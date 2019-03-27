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
  address = node.getnewaddress()
  #=============================================================================
  # Create Inputs & Outputs
  #=============================================================================
  unspent = node.listunspent()
  fee = Decimal('1')
  asset = "b2e15d0d7a0c94e4e2ce0fe6e8691b9e451377f6e46e8045a86f7c4b5d4f0f23"
  genesis = "867da0e138b1014173844ee0e4d557ff8a2463b14fcaeab18f6a63aa7c7e1d05"
  # Make Inputs
  inputs = {
    "txid": unspent[0]["txid"],
    "vout": unspent[0]["vout"],
    "asset": asset
  }
  # Make Outputs
  outputs = {
    "address": address,
    "decayConst": 10,
    "endBlockHeight": 20000,
    "fee": 1,
    "genesisBlockHash": genesis,
    "startBlockHeight": 10,
    "tickets": 10
  }
  #=============================================================================
  # Create Raw Request
  #=============================================================================
  try:
    tx = node.createrawrequesttx(inputs, outputs)
    signedtx = node.signrawtransaction(tx)
    #===========================================================================
    # Send Transaction and try if is valid or not valid
    #===========================================================================
    txid = node.testmempoolaccept(signedtx["hex"])
    if txid["allowed"] == 0:
      return False
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
  address = node.getnewaddress()
  #=============================================================================
  # Create Inputs & Outputs
  #=============================================================================
  unspent = node.listunspent()
  fee = Decimal('1')
  asset = "b2e15d0d7a0c94e4e2ce0fe6e8691b9e451377f6e46e8045a86f7c4b5d4f0f23"
  genesis = "867da0e138b1014173844ee0e4d557ff8a2463b14fcaeab18f6a63aa7c7e1d05"
  # Make Inputs
  inputs = {
    "txid": unspent[0]["txid"],
    "vout": unspent[0]["vout"],
    "asset": asset
  }
  # Make Outputs
  outputs = {
    # "address": address,
    "decayConst": 10,
    "endBlockHeight": 20000,
    "fee": 1,
    "genesisBlockHash": genesis,
    "startBlockHeight": 10000,
    "tickets": 10
  }
  #=============================================================================
  # Create Raw Request
  #=============================================================================
  try:
    tx = node.createrawrequesttx(inputs, outputs)
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
  address = node.getnewaddress()
  #=============================================================================
  # Create Inputs & Outputs
  #=============================================================================
  unspent = node.listunspent()
  fee = Decimal('1')
  asset = "b2e15d0d7a0c94e4e2ce0fe6e8691b9e451377f6e46e8045a86f7c4b5d4f0f23"
  genesis = "867da0e138b1014173844ee0e4d557ff8a2463b14fcaeab18f6a63aa7c7e1d05"
  # Make Inputs
  inputs = {
    "txid": unspent[0]["txid"],
    "vout": unspent[0]["vout"],
    "asset": asset
  }
  # Make Outputs
  outputs = {
    "address": address,
    # "decayConst": 10,
    "endBlockHeight": 20000,
    "fee": 1,
    "genesisBlockHash": genesis,
    "startBlockHeight": 10000,
    "tickets": 10
  }
  #=============================================================================
  # Create Raw Request
  #=============================================================================
  try:
    tx = node.createrawrequesttx(inputs, outputs)
    return False
  except:
    return True
#===============================================================================
# Test 4 :
#===============================================================================
def test_validBurn_4(node):
  #=============================================================================
  # Create Address
  #=============================================================================
  address = node.getnewaddress()
  #=============================================================================
  # Create Inputs & Outputs
  #=============================================================================
  unspent = node.listunspent()
  fee = Decimal('1')
  asset = "b2e15d0d7a0c94e4e2ce0fe6e8691b9e451377f6e46e8045a86f7c4b5d4f0f23"
  genesis = "867da0e138b1014173844ee0e4d557ff8a2463b14fcaeab18f6a63aa7c7e1d05"
  # Make Inputs
  inputs = {
    "txid": unspent[0]["txid"],
    "vout": unspent[0]["vout"],
    "asset": asset
  }
  # Make Outputs
  outputs = {
    "address": address,
    "decayConst": 10,
    # "endBlockHeight": 20000,
    "fee": 1,
    "genesisBlockHash": genesis,
    "startBlockHeight": 10000,
    "tickets": 10
  }
  #=============================================================================
  # Create Raw Request
  #=============================================================================
  try:
    tx = node.createrawrequesttx(inputs, outputs)
    return False
  except:
    return True
#===============================================================================
# Test 5 :
#===============================================================================
def test_validBurn_5(node):
  #=============================================================================
  # Create Address
  #=============================================================================
  address = node.getnewaddress()
  #=============================================================================
  # Create Inputs & Outputs
  #=============================================================================
  unspent = node.listunspent()
  fee = Decimal('1')
  asset = "b2e15d0d7a0c94e4e2ce0fe6e8691b9e451377f6e46e8045a86f7c4b5d4f0f23"
  genesis = "867da0e138b1014173844ee0e4d557ff8a2463b14fcaeab18f6a63aa7c7e1d05"
  # Make Inputs
  inputs = {
    "txid": unspent[0]["txid"],
    "vout": unspent[0]["vout"],
    "asset": asset
  }
  # Make Outputs
  outputs = {
    "address": address,
    "decayConst": 10,
    "endBlockHeight": 20000,
    # "fee": 1,
    "genesisBlockHash": genesis,
    "startBlockHeight": 10000,
    "tickets": 10
  }
  #=============================================================================
  # Create Raw Request
  #=============================================================================
  try:
    tx = node.createrawrequesttx(inputs, outputs)
    return False
  except:
    return True

#===============================================================================
# Test 6 :
#===============================================================================
def test_validBurn_6(node):
  #=============================================================================
  # Create Address
  #=============================================================================
  address = node.getnewaddress()
  #=============================================================================
  # Create Inputs & Outputs
  #=============================================================================
  unspent = node.listunspent()
  fee = Decimal('1')
  asset = "b2e15d0d7a0c94e4e2ce0fe6e8691b9e451377f6e46e8045a86f7c4b5d4f0f23"
  genesis = "867da0e138b1014173844ee0e4d557ff8a2463b14fcaeab18f6a63aa7c7e1d05"
  # Make Inputs
  inputs = {
    "txid": unspent[0]["txid"],
    "vout": unspent[0]["vout"],
    "asset": asset
  }
  # Make Outputs
  outputs = {
    "address": address,
    "decayConst": 10,
    "endBlockHeight": 20000,
    "fee": 1,
    # "genesisBlockHash": genesis,
    "startBlockHeight": 10000,
    "tickets": 10
  }
  #=============================================================================
  # Create Raw Request
  #=============================================================================
  try:
    tx = node.createrawrequesttx(inputs, outputs)
    return False
  except:
    return True

#===============================================================================
# Test 7 :
#===============================================================================
def test_validBurn_7(node):
  #=============================================================================
  # Create Address
  #=============================================================================
  address = node.getnewaddress()
  #=============================================================================
  # Create Inputs & Outputs
  #=============================================================================
  unspent = node.listunspent()
  fee = Decimal('1')
  asset = "b2e15d0d7a0c94e4e2ce0fe6e8691b9e451377f6e46e8045a86f7c4b5d4f0f23"
  genesis = "867da0e138b1014173844ee0e4d557ff8a2463b14fcaeab18f6a63aa7c7e1d05"
  # Make Inputs
  inputs = {
    "txid": unspent[0]["txid"],
    "vout": unspent[0]["vout"],
    "asset": asset
  }
  # Make Outputs
  outputs = {
    "address": address,
    "decayConst": 10,
    "endBlockHeight": 20000,
    "fee": 1,
    "genesisBlockHash": genesis,
    # "startBlockHeight": 10000,
    "tickets": 10
  }
  #=============================================================================
  # Create Raw Request
  #=============================================================================
  try:
    tx = node.createrawrequesttx(inputs, outputs)
    return False
  except:
    return True

#===============================================================================
# Test 8 :
#===============================================================================
def test_validBurn_8(node):
  #=============================================================================
  # Create Address
  #=============================================================================
  address = node.getnewaddress()
  #=============================================================================
  # Create Inputs & Outputs
  #=============================================================================
  unspent = node.listunspent()
  fee = Decimal('1')
  asset = "b2e15d0d7a0c94e4e2ce0fe6e8691b9e451377f6e46e8045a86f7c4b5d4f0f23"
  genesis = "867da0e138b1014173844ee0e4d557ff8a2463b14fcaeab18f6a63aa7c7e1d05"
  # Make Inputs
  inputs = {
    "txid": unspent[0]["txid"],
    "vout": unspent[0]["vout"],
    "asset": asset
  }
  # Make Outputs
  outputs = {
    "address": address,
    "decayConst": 10,
    "endBlockHeight": 20000,
    "fee": 1,
    "genesisBlockHash": genesis,
    "startBlockHeight": 10000,
    # "tickets": 10
  }
  #=============================================================================
  # Create Raw Request
  #=============================================================================
  try:
    tx = node.createrawrequesttx(inputs, outputs)
    return False
  except:
    return True

class CreateRawRequestTx(BitcoinTestFramework):
  def __init__(self):
    super().__init__()
    self.setup_clean_chain = True
    self.num_nodes = 4
    self.extra_args = [['-usehd={:d}'.format(i % 2 == 0), '-keypool=100']
                       for i in range(self.num_nodes)]

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
    # Test : 5
    #===========================================================================
    if test_validBurn_5(self.nodes[0]) == True:
      print("Test 5 :\033[1;32;40m OK\033[0m")
    else:
      failed = True
      print("Test 5 :\033[1;31;40m KO\033[0m")
    #===========================================================================
    # Test : 6
    #===========================================================================
    if test_validBurn_6(self.nodes[0]) == True:
      print("Test 6 :\033[1;32;40m OK\033[0m")
    else:
      failed = True
      print("Test 6 :\033[1;31;40m KO\033[0m")
    #===========================================================================
    # Test : 7
    #===========================================================================
    if test_validBurn_7(self.nodes[0]) == True:
      print("Test 7 :\033[1;32;40m OK\033[0m")
    else:
      failed = True
      print("Test 7 :\033[1;31;40m KO\033[0m")
    #===========================================================================
    # Test : 8
    #===========================================================================
    if test_validBurn_1(self.nodes[0]) == True:
      print("Test 8 :\033[1;32;40m OK\033[0m")
    else:
      failed = True
      print("Test 8 :\033[1;31;40m KO\033[0m")
    #===========================================================================
    # End
    #===========================================================================
    assert failed == False
    print("End.")
#===============================================================================
# Main, Entry Point
#===============================================================================
if __name__ == '__main__':
  CreateRawRequestTx().main()
