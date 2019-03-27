#!/usr/bin/env python3
from test_framework.test_framework import BitcoinTestFramework
from test_framework.util import *
#===============================================================================
# Test 1 : Normal Configuration Without Procedural Error
#===============================================================================
def test_redemption_1(node):
  #=============================================================================
  # Create Address
  #=============================================================================
  addr0 = "2dZRkPX3hrPtuBrmMkbGtxTxsuYYgAaFrXZ" # Addr Null
  addr1 = "2dwjJKzmgQqZFcHuA4xpmHXpSMUUUUx3Uvp"
  addr2 = "2dtN5tRLLxRcAJqKawoY5ZpVLEaEdDtsvEY"
  addr3 = "2dwqZcvKQWetnzMnnKmqr1wv6SJF8Vb6UQH"
  #=============================================================================
  # Add address to FreezeList
  #=============================================================================
  node.addtofreezelist(addr1)
  node.addtofreezelist(addr2)
  node.addtofreezelist(addr3)
  #=============================================================================
  # Create Inputs & Outputs
  #=============================================================================
  unspent = node.listunspent()
  fee = Decimal('0.0001')
  # Make Inputs
  inputs = [{
    "txid": unspent[0]["txid"],
    "vout": unspent[0]["vout"],
    "nValue": unspent[0]["amount"]
  }]
  # Make Outputs
  outputs = {
    addr0 : 1,
    addr1 : 1,
    addr2 : 1,
    addr3 : unspent[0]["amount"] - 3 - fee,
    "fee": fee
  }
  #=============================================================================
  # Create Transaction & Signed Transaction
  #=============================================================================
  tx = node.createrawtransaction(inputs, outputs);
  signedtx = node.signrawtransaction(tx)
  #=============================================================================
  # Send Transaction and try if is valid or not valid
  #=============================================================================
  txid = node.testmempoolaccept(signedtx["hex"])

  print(txid)

  if txid["allowed"] == 0:
    print(txid)
    return False
  return True
#===============================================================================
# Test 2 : Test With an Address not Listed in FreezeList
#===============================================================================
def test_redemption_2(node):
  #=============================================================================
  # Create Address
  #=============================================================================
  addr0 = "2dZRkPX3hrPtuBrmMkbGtxTxsuYYgAaFrXZ" # Addr Null
  addr1 = "2du9ZTgWwKNrNEbXKTaxY2CqHsKu54F4nDf"
  addr2 = "2dmEnSShq8JcLAcCdgc1zgEg44rghCZQbXK"
  addr3 = "2dfajcWR4zb7prgHRP4Scfa7ikxNGa79Vh6"
  #=============================================================================
  # Add address to FreezeList
  #=============================================================================
  node.addtofreezelist(addr1)
  node.addtofreezelist(addr2)
  #=============================================================================
  # Create Inputs & Outputs
  #=============================================================================
  unspent = node.listunspent()
  fee = Decimal('0.0001')
  # Make Inputs
  inputs = [{
    "txid": unspent[0]["txid"],
    "vout": unspent[0]["vout"],
    "nValue": unspent[0]["amount"]
  }]
  # Make Outputs
  outputs = {
    addr0 : 1,
    addr1 : 1,
    addr2 : 1,
    addr3 : unspent[0]["amount"] - 3 - fee,
    "fee": fee
  }
  #=============================================================================
  # Create Transaction & Signed Transaction
  #=============================================================================
  tx = node.createrawtransaction(inputs, outputs);
  signedtx = node.signrawtransaction(tx)
  #=============================================================================
  # Send Transaction and try if is valid or not valid
  #=============================================================================
  txid = node.testmempoolaccept(signedtx["hex"])
  if txid["allowed"] == 0:
    return True
  return False
#===============================================================================
# Test 3 : Test With no Address Listed in FreezeList
#===============================================================================
def test_redemption_3(node):
  #=============================================================================
  # Create Address
  #=============================================================================
  addr0 = "2dZRkPX3hrPtuBrmMkbGtxTxsuYYgAaFrXZ" # Addr Null
  addr1 = "2dk3USoFAUz8yiuxufPhBnUugtNhDSC988Z"
  addr2 = "2dbHX1sthNLQqACH18vxP9uUonwXsPeSHyY"
  addr3 = "2dbqyNEgAmQrXKHNX6fm1rJrZt9NnrZcayE"
  #=============================================================================
  # Create Inputs & Outputs
  #=============================================================================
  unspent = node.listunspent()
  fee = Decimal('0.0001')
  # Make Inputs
  inputs = [{
    "txid": unspent[0]["txid"],
    "vout": unspent[0]["vout"],
    "nValue": unspent[0]["amount"]
  }]
  # Make Outputs
  outputs = {
    addr0 : 1,
    addr1 : 1,
    addr2 : 1,
    addr3 : unspent[0]["amount"] - 3 - fee,
    "fee": fee
  }
  #=============================================================================
  # Create Transaction & Signed Transaction
  #=============================================================================
  tx = node.createrawtransaction(inputs, outputs);
  signedtx = node.signrawtransaction(tx)
  #=============================================================================
  # Send Transaction and try if is valid or not valid
  #=============================================================================
  txid = node.testmempoolaccept(signedtx["hex"])
  if txid["allowed"] == 0:
    return True
  return False
#===============================================================================
# Test 4 : Just Test With not Null Addresses
#===============================================================================
def test_redemption_4(node):
  #=============================================================================
  # Create Address
  #=============================================================================
  addr0 = "2dh4kopixia2H58uQgj3noMynGnanCcyCFU"
  addr1 = "2duGaMQy25zARWizum5XCJ3dgStyQv4xQZm"
  addr2 = "2dnu443uW56gFp6vPsWsMxXmxBDgYs6u5fR"
  addr3 = "2dr5w5UZyDoeW5Xgd2cioartw7WZjUuJA38"
  #=============================================================================
  # Create Inputs & Outputs
  #=============================================================================
  unspent = node.listunspent()
  fee = Decimal('0.0001')
  # Make Inputs
  inputs = [{
    "txid": unspent[0]["txid"],
    "vout": unspent[0]["vout"],
    "nValue": unspent[0]["amount"]
  }]
  # Make Outputs
  outputs = {
    addr0 : 1,
    addr1 : 1,
    addr2 : 1,
    addr3 : unspent[0]["amount"] - 3 - fee,
    "fee": fee
  }
  #=============================================================================
  # Create Transaction & Signed Transaction
  #=============================================================================
  tx = node.createrawtransaction(inputs, outputs);
  signedtx = node.signrawtransaction(tx)
  #=============================================================================
  # Send Transaction and try if is valid or not valid
  #=============================================================================
  txid = node.testmempoolaccept(signedtx["hex"])
  if txid["allowed"] == 0:
    print(txid)
    return False
  return True
#===============================================================================
# Test 5 : Test With a Null Address that is not at the Top of the List
#===============================================================================
def test_redemption_5(node):
  #=============================================================================
  # Create Address
  #=============================================================================
  addr0 = "2djXzQZjFzMU878ZoaRYd6gk1MjifVuh44p"
  addr1 = "2dZRkPX3hrPtuBrmMkbGtxTxsuYYgAaFrXZ" # Addr Null
  addr2 = "2dfsxgRhHzuW6kuUrNP7bTaHTfAMgzYHKPU"
  addr3 = "2deXJt7QcKAwtFyToCnog252RP8FdVCaXMC"
  #=============================================================================
  # Create Inputs & Outputs
  #=============================================================================
  unspent = node.listunspent()
  fee = Decimal('0.0001')
  # Make Inputs
  inputs = [{
    "txid": unspent[0]["txid"],
    "vout": unspent[0]["vout"],
    "nValue": unspent[0]["amount"]
  }]
  # Make Outputs
  outputs = {
    addr0 : 1,
    addr1 : 1,
    addr2 : 1,
    addr3 : unspent[0]["amount"] - 3 - fee,
    "fee": fee
  }
  #=============================================================================
  # Create Transaction & Signed Transaction
  #=============================================================================
  tx = node.createrawtransaction(inputs, outputs);
  signedtx = node.signrawtransaction(tx)
  #=============================================================================
  # Send Transaction and try if is valid or not valid
  #=============================================================================
  txid = node.testmempoolaccept(signedtx["hex"])
  if txid["allowed"] == 0:
    return True
  return False
#===============================================================================
# Test 6 : Test With a Single Null Address in the List
#===============================================================================
def test_redemption_6(node):
  #=============================================================================
  # Create Address
  #=============================================================================
  addr0 = "2dZRkPX3hrPtuBrmMkbGtxTxsuYYgAaFrXZ" # Addr Null
  #=============================================================================
  # Create Inputs & Outputs
  #=============================================================================
  unspent = node.listunspent()
  fee = Decimal('0.0001')
  # Make Inputs
  inputs = [{
    "txid": unspent[0]["txid"],
    "vout": unspent[0]["vout"],
    "nValue": unspent[0]["amount"]
  }]
  # Make Outputs
  outputs = {
    addr0 : unspent[0]["amount"] - fee,
    "fee": fee
  }
  #=============================================================================
  # Create Transaction & Signed Transaction
  #=============================================================================
  tx = node.createrawtransaction(inputs, outputs);
  signedtx = node.signrawtransaction(tx)
  #=============================================================================
  # Send Transaction and try if is valid or not valid
  #=============================================================================
  txid = node.testmempoolaccept(signedtx["hex"])
  if txid["allowed"] == 0:
    return True
  print(txid)
  return False
#===============================================================================
# Test 7 : Test With Several Null Addresses in the List
#===============================================================================
def test_redemption_7(node):
  #=============================================================================
  # Create Address
  #=============================================================================
  addr0 = "2dZRkPX3hrPtuBrmMkbGtxTxsuYYgAaFrXZ" # Addr Null
  addr1 = "2dcDRR6iK553L5svftC8GccfrhtoRQ5rx1W"
  addr2 = "2dZRkPX3hrPtuBrmMkbGtxTxsuYYgAaFrXZ" # Addr Null
  addr3 = "2dxhnrM8Fa9RB1eCfgK2FW5rDH3DJsZ2Mvn"
  #=============================================================================
  # Add address to FreezeList
  #=============================================================================
  node.addtofreezelist(addr1)
  node.addtofreezelist(addr3)
  #=============================================================================
  # Create Inputs & Outputs
  #=============================================================================
  unspent = node.listunspent()
  fee = Decimal('0.0001')
  # Make Inputs
  inputs = [{
    "txid": unspent[0]["txid"],
    "vout": unspent[0]["vout"],
    "nValue": unspent[0]["amount"]
  }]
  # Make Outputs
  outputs = {
    addr0 : 1,
    addr1 : 1,
    addr2 : 1,
    addr3 : unspent[0]["amount"] - 3 - fee,
    "fee": fee
  }
  #=============================================================================
  # Create Transaction & Signed Transaction
  #=============================================================================
  tx = node.createrawtransaction(inputs, outputs);
  signedtx = node.signrawtransaction(tx)
  #=============================================================================
  # Send Transaction and try if is valid or not valid
  #=============================================================================
  txid = node.testmempoolaccept(signedtx["hex"])
  if txid["allowed"] == 0:
    print(txid)
    return False
  return True

class RedemptionTest (BitcoinTestFramework):
  def __init__(self):
    super().__init__()
    self.setup_clean_chain = True
    self.num_nodes = 4
    self.extra_args = [['-usehd={:d}'.format(i % 2 == 0), '-keypool=100']
                       for i in range(self.num_nodes)]
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
    if test_redemption_1(self.nodes[0]) == True:
      print("Test 1 :\033[1;32;40m OK\033[0m")
    else:
      failed = True
      print("Test 1 :\033[1;31;40m KO\033[0m")
    #===========================================================================
    # Test : 2
    #===========================================================================
    if test_redemption_2(self.nodes[0]) == True:
      print("Test 2 :\033[1;32;40m OK\033[0m")
    else:
      failed = True
      print("Test 2 :\033[1;31;40m KO\033[0m")
    #===========================================================================
    # Test : 3
    #===========================================================================
    if test_redemption_3(self.nodes[0]) == True:
      print("Test 3 :\033[1;32;40m OK\033[0m")
    else:
      failed = True
      print("Test 3 :\033[1;31;40m KO\033[0m")
    #===========================================================================
    # Test : 4
    #===========================================================================
    if test_redemption_4(self.nodes[0]) == True:
      print("Test 4 :\033[1;32;40m OK\033[0m")
    else:
      failed = True
      print("Test 4 :\033[1;31;40m KO\033[0m")
    #===========================================================================
    # Test : 5
    #===========================================================================
    if test_redemption_5(self.nodes[0]) == True:
      print("Test 5 :\033[1;32;40m OK\033[0m")
    else:
      failed = True
      print("Test 5 :\033[1;31;40m KO\033[0m")
    #===========================================================================
    # Test : 6
    #===========================================================================
    if test_redemption_6(self.nodes[0]) == True:
      print("Test 6 :\033[1;32;40m OK\033[0m")
    else:
      failed = True
      print("Test 6 :\033[1;31;40m KO\033[0m")
    #===========================================================================
    # Test : 7
    #===========================================================================
    if test_redemption_7(self.nodes[0]) == True:
      print("Test 7 :\033[1;32;40m OK\033[0m")
    else:
      failed = True
      print("Test 7 :\033[1;31;40m KO\033[0m")
    #===========================================================================
    # End
    #===========================================================================
    assert failed == False
    print("End.")
#===============================================================================
# Main, Entry Point
#===============================================================================
if __name__ == '__main__':
  RedemptionTest().main()
