#!/usr/bin/env python3
from test_framework.test_framework import BitcoinTestFramework
from test_framework.util import *
#===============================================================================
# Test 1 : Normal Configuration Without Procedural Error
#===============================================================================
def test_validBurn_1(node):
  #create asset to send
  issue = node.issueasset('10','0')
  node.generate(10)
  tx = node.getrawtransaction(issue["txid"],1)
  for vout in tx["vout"]:
    if vout["asset"] == issue["asset"]:
      n = vout["n"]
  #=============================================================================
  # Create Address
  #=============================================================================
  addr0 = "2dZRkPX3hrPtuBrmMkbGtxTxsuYYgAaFrXZ" # Addr Null
  addr1 = "2dwjJKzmgQqZFcHuA4xpmHXpSMUUUUx3Uvp"
  #=============================================================================
  # Add address to FreezeList
  #=============================================================================
  node.addtofreezelist(addr1)
  #=============================================================================
  # Create Inputs & Outputs
  #=============================================================================
  # Make Inputs
  inputs = [{
    "txid": issue["txid"],
    "vout": n,
    "nValue": Decimal(10.0)
  }]
  # Make Outputs
  outputs = {
    addr0 : 0,
    addr1 : 10,
  }
  #assets
  assets = {
    addr0 : issue["asset"],
    addr1 : issue["asset"]
  }
  #=============================================================================
  # Create Transaction & Signed Transaction
  #=============================================================================
  tx = node.createrawtransaction(inputs, outputs,0,assets);
  txd = node.decoderawtransaction(tx)
  for vout in txd["vout"]:
    if vout["asset"] == issue["asset"] and vout["value"] > 0:
      n = vout["n"]
  signedtx = node.signrawtransaction(tx)
  sendtx = node.sendrawtransaction(signedtx["hex"])
  node.generate(10)

  #burn outputs
  burntx = node.createrawburn(sendtx, str(n), issue["asset"], '10')
  signtx = node.signrawtransaction(burntx["hex"])

  txid = node.testmempoolaccept(signtx["hex"])
  print(txid)

  if txid["allowed"] == 0:
    return True
  return False
#===============================================================================
# Test 2 :
#===============================================================================
def test_validBurn_2(node):
  #create asset to send
  issue = node.issueasset('10','0')
  tx = node.getrawtransaction(issue["txid"],1)
  for vout in tx["vout"]:
    if vout["asset"] == issue["asset"]:
      n = vout["n"]
  node.generate(10)
  #=============================================================================
  # Create Address
  #=============================================================================
  addr0 = "2dZRkPX3hrPtuBrmMkbGtxTxsuYYgAaFrXZ" # Addr Null
  addr1 = "2dwjJKzmgQqZFcHuA4xpmHXpSMUUUUx3Uvp"
  #=============================================================================
  # Add address to FreezeList
  #=============================================================================
  node.addtofreezelist(addr1)
  #=============================================================================
  # Create Inputs & Outputs
  #=============================================================================
  # Make Inputs
  inputs = [{
    "txid": issue["txid"],
    "vout": n,
    "nValue": Decimal(10.0)
  }]
  # Make Outputs
  outputs = {
    addr0 : 0,
    addr1 : 10,
  }
  #assets
  assets = {
    addr0 : issue["asset"],
    addr1 : issue["asset"]
  }
  #=============================================================================
  # Create Transaction & Signed Transaction
  #=============================================================================
  tx = node.createrawtransaction(inputs, outputs,0,assets);
  txd = node.decoderawtransaction(tx)
  for vout in txd["vout"]:
    if vout["asset"] == issue["asset"] and vout["value"] > 0:
      n = vout["n"]
  signedtx = node.signrawtransaction(tx)
  sendtx = node.sendrawtransaction(signedtx["hex"])
  node.generate(10)

  #burn outputs
  node.addtoburnlist(addr1)
  burntx = node.createrawburn(sendtx, str(n), issue["asset"], '10')
  signtx = node.signrawtransaction(burntx["hex"])

  txid = node.testmempoolaccept(signtx["hex"])
  print(txid)

  if txid["allowed"] == 0:
    return False
  return True

#===============================================================================
# Test 3 :
#===============================================================================
def test_validBurn_3(node):
  #create asset to send
  issue = node.issueasset('10','0')
  node.generate(10)
  tx = node.getrawtransaction(issue["txid"],1)
  for vout in tx["vout"]:
    if vout["asset"] == issue["asset"]:
      n = vout["n"]

  burntx = node.createrawburn(issue["txid"], str(n), issue["asset"], '10')
  signtx = node.signrawtransaction(burntx["hex"])

  txid = node.testmempoolaccept(signtx["hex"])

  if txid["allowed"] == 0:
    return True
  return False

class validBurnTest (BitcoinTestFramework):
  def __init__(self):
    super().__init__()
    self.setup_clean_chain = True
    self.num_nodes = 4
    self.extra_args = [['-usehd={:d}'.format(i % 2 == 0), '-keypool=100']
                       for i in range(self.num_nodes)]
    self.extra_args[0].append("-txindex")
    self.extra_args[0].append("-burnlist=1")
    self.extra_args[0].append("-freezelist=1")

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
    # End
    #===========================================================================
    assert failed == False
    print("End.")
#===============================================================================
# Main, Entry Point
#===============================================================================
if __name__ == '__main__':
  validBurnTest().main()
