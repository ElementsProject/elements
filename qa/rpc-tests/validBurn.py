#!/usr/bin/env python3
from test_framework.test_framework import BitcoinTestFramework
from test_framework.util import *
#===============================================================================
# Test 1 : Normal Configuration Without Procedural Error
#===============================================================================
def test_validBurn_1(node):
  #=============================================================================
  # Create Address
  #=============================================================================
  addr0 = node.getnewaddress()
  #=============================================================================
  # Create Inputs & Outputs
  #=============================================================================
  unspent = node.listunspent()
  #
  freezetx = node.getrawtransaction(unspent[0]["txid"], True)
  #
  txid = unspent[0]["txid"]
  vout = str(freezetx["vout"][0]["n"])
  asset = freezetx["vout"][0]["asset"]
  amount = freezetx["vout"][0]["value"]
  #=============================================================================
  # Create Transaction Burned & Signed Transaction
  #=============================================================================
  burntx = node.createrawburn(txid, vout, asset, amount)
  signtx = node.signrawtransaction(burntx["hex"])
  #=============================================================================
  # Send Transaction and try if is valid or not valid
  #=============================================================================
  try:
    sendtx = node.sendrawtransaction(signtx["hex"])
    return True
  except:
    return False
#===============================================================================
# Test 2 :
#===============================================================================
def test_validBurn_2(node):
  #=============================================================================
  # Create Address
  #=============================================================================
  addr0 = node.getnewaddress()
  #=============================================================================
  # Create Inputs & Outputs
  #=============================================================================
  unspent = node.listunspent()
  #
  freezetx = node.getrawtransaction(unspent[0]["txid"], True)
  #
  txid = ""
  vout = str(freezetx["vout"][0]["n"])
  asset = freezetx["vout"][0]["asset"]
  amount = freezetx["vout"][0]["value"]
  #=============================================================================
  # Create Transaction Burned & Signed Transaction
  #=============================================================================
  burntx = node.createrawburn(txid, vout, asset, amount)
  signtx = node.signrawtransaction(burntx["hex"])
  #=============================================================================
  # Send Transaction and try if is valid or not valid
  #=============================================================================
  try:
    sendtx = node.sendrawtransaction(signtx["hex"])
    return False
  except:
    return True
#===============================================================================
# Test 3 :
#===============================================================================
def test_validBurn_3(node):
  #=============================================================================
  # Create Address
  #=============================================================================
  addr0 = node.getnewaddress()
  #=============================================================================
  # Create Inputs & Outputs
  #=============================================================================
  unspent = node.listunspent()
  #
  freezetx = node.getrawtransaction(unspent[0]["txid"], True)
  #
  txid = unspent[0]["txid"]
  vout = ""
  asset = freezetx["vout"][0]["asset"]
  amount = freezetx["vout"][0]["value"]
  #=============================================================================
  # Create Transaction Burned & Signed Transaction
  #=============================================================================
  burntx = node.createrawburn(txid, vout, asset, amount)
  signtx = node.signrawtransaction(burntx["hex"])
  #=============================================================================
  # Send Transaction and try if is valid or not valid
  #=============================================================================
  try:
    sendtx = node.sendrawtransaction(signtx["hex"])
    return True
  except:
    return False
#===============================================================================
# Test 4 :
#===============================================================================
def test_validBurn_4(node):
  #=============================================================================
  # Create Address
  #=============================================================================
  addr0 = node.getnewaddress()
  #=============================================================================
  # Create Inputs & Outputs
  #=============================================================================
  unspent = node.listunspent()
  #
  freezetx = node.getrawtransaction(unspent[0]["txid"], True)
  #
  txid = unspent[0]["txid"]
  vout = str(freezetx["vout"][0]["n"])
  asset = ""
  amount = freezetx["vout"][0]["value"]
  #=============================================================================
  # Create Transaction Burned & Signed Transaction
  #=============================================================================
  burntx = node.createrawburn(txid, vout, asset, amount)
  signtx = node.signrawtransaction(burntx["hex"])
  #=============================================================================
  # Send Transaction and try if is valid or not valid
  #=============================================================================
  try:
    sendtx = node.sendrawtransaction(signtx["hex"])
    return False
  except:
    return True

class validBurnTest (BitcoinTestFramework):
  def __init__(self):
    super().__init__()
    self.setup_clean_chain = True
    self.num_nodes = 4
    self.extra_args = [['-usehd={:d}'.format(i % 2 == 0), '-keypool=100']
                       for i in range(self.num_nodes)]
    self.extra_args[0].append("-txindex")
    self.extra_args[0].append("-burnlist=1")

  def setup_network(self, split=False):
    self.nodes = start_nodes(self.num_nodes, self.options.tmpdir,
                             self.extra_args[:self.num_nodes])
    connect_nodes_bi(self.nodes, 0, 1)
    connect_nodes_bi(self.nodes, 1, 2)
    connect_nodes_bi(self.nodes, 1, 3)
    connect_nodes_bi(self.nodes, 2, 3)
    self.is_network_split = False
    self.sync_all()

  def run_test(self):
    self.nodes[0].generate(101)
    self.sync_all()
    failed = False
    #===========================================================================
    # Test : 1
    #===========================================================================
    if test_validBurn_1(self.nodes[0]) == True:
      print("Test 1 :\033[1;32;40m OK\033[0m")
    else:
      failed = True
      print("Test 1 :\033[1;31;40m KO\033[0m")
    #===========================================================================
    # Test : 2
    #===========================================================================
    if test_validBurn_2(self.nodes[0]) == True:
      print("Test 2 :\033[1;32;40m OK\033[0m")
    else:
      failed = True
      print("Test 2 :\033[1;31;40m KO\033[0m")
    #===========================================================================
    # Test : 3
    #===========================================================================
    if test_validBurn_3(self.nodes[0]) == True:
      print("Test 3 :\033[1;32;40m OK\033[0m")
    else:
      failed = True
      print("Test 3 :\033[1;31;40m KO\033[0m")
    #===========================================================================
    # Test : 4
    #===========================================================================
    if test_validBurn_4(self.nodes[0]) == True:
      print("Test 4 :\033[1;32;40m OK\033[0m")
    else:
      failed = True
      print("Test 4 :\033[1;31;40m KO\033[0m")
    #===========================================================================
    # End
    #===========================================================================
    assert failed == False
    print("End.")
#===============================================================================
# Main, Entry Point
#===============================================================================
if __name__ == '__main__':
  validBurnTest().main()
