
from test_framework.authproxy import AuthServiceProxy

import tempfile
import time
import shutil
import subprocess

class Daemon():
    """
    A class for representing a bitcoind or elementsd node.

    Wraps the process management, creation and deletion of datadirs, and
    RPC connectivity, into a simple object that will clean itself up on
    exit. The `cleanup_on_exit` parameter can be set to False to prevent
    the node from deleting its datadir on restart (and can be set by
    passing --no-cleanup to the main program).
    """

    def __init__(self, name, daemon, path, conf_path, cleanup_on_exit = True):
        self.name = name
        self.daemon = daemon
        self.conf_path = path
        self.path = path
        self.cleanup_on_exit = cleanup_on_exit
        self.conf_path = conf_path
        self.datadir_path = None
        self.proc = None
        self.rpc = None

        # Parse config
        self.config = {}
        with open(self.conf_path, encoding="utf8") as f:
            for line in f:
                if len(line) == 0 or line[0] == "#" or len(line.split("=")) != 2:
                    continue
                self.config[line.split("=")[0]] = line.split("=")[1].strip()

    def shutdown(self):
        if self.proc is not None:
            print ("Shutting down %s" % self.name)
            self.proc.terminate()
            # FIXME determine why we need 30+ seconds to shut down with a tiny regtest chain
            self.proc.wait(120)
            self.proc = None

        if self.datadir_path is not None:
            if self.cleanup_on_exit:
                shutil.rmtree(self.datadir_path)
            else:
                print ("Leaving %s datadir at %s." % (self.name, self.datadir_path))

    def start(self, ext_args = None, keep_datadir = False):
        if keep_datadir and self.datadir_path is not None:
            temp = self.datadir_path
            self.datadir_path = None
            self.shutdown()
            self.datadir_path = temp
        else:
            self.shutdown()
            # Create datadir and copy config into place
            self.datadir_path = tempfile.mkdtemp()
            shutil.copyfile(self.conf_path, self.datadir_path + '/' + self.daemon + '.conf')
            print("%s datadir: %s" % (self.name, self.datadir_path))

        # Start process
        print ("Starting %s" % self.name)
        if ext_args is None:
            ext_args = []
        self.proc = subprocess.Popen([self.path, "-datadir=" + self.datadir_path] + ext_args)
        self.rpc = AuthServiceProxy("http://" + self.config["rpcuser"] + ":" + self.config["rpcpassword"] + "@127.0.0.1:" + self.config["rpcport"])

        # Give daemon a moment to start up
        time.sleep(1)

    def connect_to(self, other):
        self.addnode("localhost:%s" % other.config['port'], "onetry")

    def restart(self, ext_args = None, keep_datadir = False):
        self.start(ext_args, keep_datadir)

    def __del__(self):
        self.shutdown()

    def __getattr__(self, name):
        """Dispatches any unrecognised messages to the RPC connection or a CLI instance."""
        return self.rpc.__getattr__(name)

    def __getitem__(self, key):
        """Dispatches any keys to the underlying config file"""
        return self.config[key]

def sync_all(nodes, timeout_sec = 10):
    stop_time = time.time() + timeout_sec
    while time.time() <= stop_time:
        best_hash = [x.getbestblockhash() for x in nodes]
        if best_hash.count(best_hash[0]) == len(nodes):
            break
        time.sleep(1)
    while time.time() <= stop_time:
        pool = [set(x.getrawmempool()) for x in nodes]
        if pool.count(pool[0]) == len(nodes):
            return
        time.sleep(1)
    raise Exception("Nodes cannot sync blocks or mempool!")

