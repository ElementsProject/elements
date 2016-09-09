##Building A New Sidechain with Elements

This is a basic step-by-step guide to building your own sidechain and setting up a fedpeg. It has been tested on a 1-of-1 (local machine) and a 2-of-2 (separate machines).

####Elements
Please look over the [Elements Project](https://github.com/ElementsProject/elements) if you haven't already. Also read [Alpha README](https://github.com/ElementsProject/elements/blob/alpha/alpha-README.md) for building dependencies and to follow along. The instructions for building the dependencies are pretty cut and clear, however, the building of a new fedpeg isn't as detailed. Keep the Elements Project's Alpha-README open in a separate tab for reference.

####Resources
If you have questions or need assistance, there are multiple resources to help you. The Freenode IRC channel is #sidechains-dev, and the Elements [Slack #technical channel](https://sidechains.slack.com) are great places to ask questions and promote conversation regarding sidechains. 

####Prerequisites
1. Linux. Building with Windows is possible - publish a guide if you know how as there isn't one publicly available! :)
2. All dependencies for Elements-Alpha. [Build Notes](https://github.com/bitcoin/bitcoin/blob/master/doc/build-unix.md)

####Build
Try to follow this order to avoid unneccessary recompilations. This is an extension of the instructions to "Run a fedpeg operator" in the Element's alpha README.

Edit your `.bashrc`. We'll come back to this file later:
```shell
RPC_USER=your_username_here
RPC_PASS=your_super_random_long_password_here
export RPC_USER
export RPC_PASS
```

Confirm your RPC credentials are found using `echo $RPC_USER` and `echo $RPC_PASS` in your terminal.

Build bitcoin (mainchain):
```shell
git clone https://github.com/ElementsProject/elements
cd elements
git checkout mainchain
./autogen.sh && ./configure && make
mv src/bitcoin{d,-cli,-tx} ../
```

Run testnet. **Note:** We need to have a full transaction index of the testnet blockchain. If this is your first time doing so, replace `-txindex` with `-reindex`. Every time you run the daemon after the initial reindexing, will be run with `-txindex` (running `-reindex` again will rescan the entire testnet blockchain, and this process could take hours depending on the machine/connection). If this is your first time indexing the testnet's transactions, you have to reindex:
```shell
./bitcoind -rpcuser=$RPC_USER -rpcpassword=$RPC_PASS -testnet -reindex -daemon
```

If you've already indexed testnet:
```shell
./bitcoind -rpcuser=$RPC_USER -rpcpassword=$RPC_PASS -testnet -txindex -daemon
```

Checkout:
```shell
git checkout alpha 
```

With bitcoin testnet, generate an address and obtain the private/public key.
```
./bitcoin-cli -testnet getnewaddress 
//returns some address
./bitcoin-cli -testnet dumpprivkey [address]
//returns private key. Save this - we'll need it later for .bashrc file
./bitcoin-cli -testnet validateaddress [address]
//returns JSON object. Copy the public key.
```

####C++
You should be on your sidechain branch (alpha). This is the part where we uniquely create your sidechain with the public keys of each functionary/blocksigner. Open `src/chainparams.cpp` and edit the public keys, ports, and seeds. [Line 132](https://github.com/ElementsProject/elements/blob/alpha/src/chainparams.cpp#L132) has the public keys for each functionary/blocksigner: 
```c++
scriptDestination = CScript() << OP_5 << ParseHex("027d5d62861df77fc9a37dbe901a579d686d1423be5f56d6fc50bb9de3480871d1") << ParseHex("03b41ea6ba73b94c901fdd43e782aaf70016cc124b72a086e77f6e9f4f942ca9bb") << ParseHex("02be643c3350bade7c96f6f28d1750af2ef507bc1f08dd38f82749214ab90d9037") << ParseHex("021df31471281d4478df85bfce08a10aab82601dca949a79950f8ddf7002bd915a") << ParseHex("0320ea4fcf77b63e89094e681a5bd50355900bf961c10c9c82876cb3238979c0ed") << ParseHex("021c4c92c8380659eb567b497b936b274424662909e1ffebc603672ed8433f4aa1") << ParseHex("027841250cfadc06c603da8bc58f6cd91e62f369826c8718eb6bd114601dd0c5ac") << OP_7 << OP_CHECKMULTISIG;
```
The first OP is the number of sigs required and the second OP is the total number of sigs. For simplicity, let's replace the current 5-of-7 multisig with a 1-of-1. Change to: 
```c++
scriptDestination = CScript() << OP_1 << ParseHex("[paste public key we just generated]") << OP_1 << OP_CHECKMULTISIG;
```

Replace the public keys for scriptAlert on [L96](https://github.com/ElementsProject/elements/blob/alpha/src/chainparams.cpp#L96).

[L139](https://github.com/ElementsProject/elements/blob/alpha/src/chainparams.cpp#L139) has the DNS seeds. If you have more than 1 functionary/blocksigner, you'll need to create a DNS of your own in order to communicate. Replace the current 5 seeds with the seeds of your signers. Also delete the testnet seed on [L198](https://github.com/ElementsProject/elements/blob/alpha/src/chainparams.cpp#L198). If you're creating a local 1-of-1 sidechain on your machine that won't be communicating on any port, you don't need to create any seeds or configure the protocol port. If the majority of signers are within the local network (i.e. on the same router), there's no need for a DNS seed, but it's still recommended.

Still in `src/chainparams.cpp`, change the testnet port number on [L182](https://github.com/ElementsProject/elements/blob/alpha/src/chainparams.cpp#L182) - this is the unique channel of communication for your sidechain so don't just increase/decrease it by one. This is one of two ports we'll change. Call this one the protocol port.

You need to duplicate what you did on L132 of `src/chainparams.cpp` on [L1451](https://github.com/ElementsProject/elements/blob/alpha/src/script/interpreter.cpp#L1451) of `src/script/interpreter.cpp`. 
Replace this line 
```c++
CScript scriptDestination(CScript() << OP_5 << ParseHex("0269992fb441ae56968e5b77d46a3e53b69f136444ae65a94041fc937bdb28d933") << ParseHex("021df31471281d4478df85bfce08a     10aab82601dca949a79950f8ddf7002bd915a") << ParseHex("02174c82021492c2c6dfcbfa4187d10d38bed06afb7fdcd72c880179fddd641ea1") << ParseHex("033f96e43d72c33327b6a4631ccaa6ea07f0b106c88b9dc71c9000bb6044d5e88     a") << ParseHex("0313d8748790f2a86fb524579b46ce3c68fedd58d2a738716249a9f7d5458a15c2") << ParseHex("030b632eeb079eb83648886122a04c7bf6d98ab5dfb94cf353ee3e9382a4c2fab0") << ParseHex("02fb54a7fcaa73c307c     fd70f3fa66a2e4247a71858ca731396343ad30c7c4009ce") << OP_7 << OP_CHECKMULTISIG);
```
with 

```c++
CScript scriptDestination(CScript() << OP_1 << ParseHex("[paste public key we just generated]") << OP_1 << OP_CHECKMULTISIG); 
```

Open `src/chainparamsbase.cpp`, change the port on [L43](https://github.com/ElementsProject/elements/blob/alpha/src/chainparamsbase.cpp#L43). This is the RPC port - keep it different from the protocol port (i.e. Elements-alpha's ports are 4241 and 4242). On L44 of the same file, you can change the name of the data directory for your sidechain (where your blocks, .dat files, etc. will be stored). 

At this point, you can compile your sidechain in the same way we compiled the mainchain earlier. There are a few help/console string messages you can change in `main.cpp, init.cpp, bitcoind.cpp`, but it's not necessary for basic functional purposes. 

```shell
./autogen.sh && ./configure && make
```

If there's a error in your compilation, go back to the file the compilation failed on and fix the error. Make sure to run `make clean` before compilating again. You'll only need to recompile your sidechain branch, not the bitcoin testnet `mainchain` branch.

Upon successful compilation:
```shell
mv src/alpha{d,-cli,-tx} ../
./alphad -rpcuser=$RPC_USER -rpcpassword=$RPC_PASS -testnet -rpcconnect=127.0.0.1 -rpcconnectport=18332 -tracksidechain=all -txindex -blindtrust=false -daemon
```

Use `./alpha-cli` to make RPC calls. Ex: `./alpha-cli -testnet getbalance`.

If the `getpeerinfo` RPC returns empty, and you're expecting to find peers, try manually adding them: `./alpha-cli -testnet addnode "Peer's IP address" "add"`.

####Python

Once your sidechain server is running, we can edit the Python files with your unique details. 

Inside `contrib/fedpeg/constants.py`, change the port number on [L9](https://github.com/TomMcCabe/elements/blob/patch/contrib/fedpeg/constants.py#L9) to the port number you specified above inside of your [src/chainparamsbase.cpp](https://github.com/ElementsProject/elements/blob/alpha/src/chainparamsbase.cpp#L43). You do NOT change the `bitcoin_url` port. 

We need to create a unique `redeem_script` and `redeem_script_address` for your sidechain. To do this, take the public key(s) in `chainparmas.cpp` and use the `createmultisig` RPC, which will return an address and a redeem script. Adjust [L12-L13](https://github.com/TomMcCabe/elements/blob/patch/contrib/fedpeg/constants.py#L12) in `constants.py` with the values given by the following RPC command:

```shell
./alpha-cli -testnet createmultisig [sigs_required] "[\"public key\", ...]" 
```

You can test this by decoding the redeem script (`alpha-cli -testnet decodescript [redeem script])`, which will return a JSON object with the public keys, signatures required and P2SH address. 

Replace the `nodes` with the network addresses (i.e. IPs) of your sidechain's blocksigners/functionaries. Add your network address to `my_node`.

Open the `.bashrc` file we edited earlier and add this to the bottom: 

```shell
BLOCKSIGNING_PRIV_KEY=private key generated earlier - associated to the public key in chainparams.cpp --- in plain text. (i.e. KEY=123)
FUNCTIONARY_PRIV_KEY=some separate generated private key
export BLOCKSIGNING_PRIV_KEY
export FUNCTIONARY_PRIV_KEY
```

Also be sure to import both private keys into your sidechain wallet using the RPC command (`blocksign.py` and `withdraw_watch.py` will do this as well): 

```shell
./alpha-cli -testnet importprivkey [private key]
```

The default sidechain blocktimes are set at 60 seconds. You can adjust the time on [L58](https://github.com/ElementsProject/elements/blob/alpha/contrib/fedpeg/blocksign.py#L58) of `contrib/fedpeg/blocksign.py`. Be sure to change the port number in [blocksign.py](https://github.com/ElementsProject/elements/blob/alpha/contrib/fedpeg/blocksign.py#L14) if you have multiple functionaries/blocksigners.

From here, you can follow [Step 6](https://github.com/ElementsProject/elements/blob/alpha/alpha-README.md#to-move-money-into-elements-alpha) of the Elements-Alpha README to move money into the sidechain. After the "claim-on-sidechain" part, run `blocksign.py` to run the blocksigning script(remember you can shorten block times):
```shell
./contrib/fedpeg/blocksign.py
```

When sidechain tokens are ready to be withdrawn, follow the [Alpha guide to move money out of the sidechain](https://github.com/ElementsProject/elements/blob/alpha/alpha-README.md#to-move-money-back-out-of-elements-alpha). The `send-to-mainchain` will create the sidechain transaction to move money from the sidechain wallet and authorize the 'unlocking' of the mainchain coins. 

Run `contrib/fedpeg/withdraw_watch.py` to claim the mainchain coins. Running `withdraw_watch.py` can take some time as it scans blocks on the mainchain. If you want to track the progress of the script, add `print(height)` after [withdraw_watch.py:486](https://github.com/ElementsProject/elements/blob/alpha/contrib/fedpeg/withdrawwatch.py#L486) which will print the block currently being scanned. Additionally, you can edit the starting block to be scanned on [line 593](https://github.com/ElementsProject/elements/blob/alpha/contrib/fedpeg/withdrawwatch.py#L593) - the default value of 447000 was the testnet block count when Elements began, therefore you can edit the value to be the testnet block count when you began your sidechain. You'll notice [Line 598](https://github.com/ElementsProject/elements/blob/alpha/contrib/fedpeg/withdrawwatch.py#L598) is commented out in our patch from earlier because we imported the functionary private key earlier.
