See https://github.com/bitcoin/bitcoin/blob/master/doc/build-unix.md
for notes on dependencies that must be installed before beginning.

### To run alphad:

1\. Download/build bitcoind/alphad
```bash
  git clone https://github.com/ElementsProject/elements
  cd elements
  git checkout mainchain
  ./autogen.sh && ./configure && make
  mv src/bitcoin{d,-cli,-tx} ../
  git checkout alpha
  ./autogen.sh && ./configure && make
  mv src/alpha{d,-cli,-tx} ../
  cd ..
```
2\. Run bitcoind/alphad
```bash
  RPC_USER=user
  RPC_PASS=pass
  ./bitcoind -rpcuser=$RPC_USER -rpcpassword=$RPC_PASS -testnet -txindex -daemon
  ./alphad -rpcuser=$RPC_USER -rpcpassword=$RPC_PASS -testnet -rpcconnect=127.0.0.1 -rpcconnectport=18332 -tracksidechain=all -txindex -blindtrust=true -daemon
```
  Note that once bitcoind finishes syncing, you can set -blindtrust=false to check that transfers to Elements Alpha are from confirmed bitcoin blocks.

### To move money into Elements Alpha:

1\. See 1 and 2 in "To run alphad"  
2\. Download secp256k1:
```bash
  git clone https://github.com/bitcoin/secp256k1
  cd secp256k1
  ./autogen.sh && ./configure --with-bignum=no && make
  make DESTDIR=`pwd`/install install
  cd ..
```
3\. Download contracthashtool
```bash
  git clone https://github.com/blockstream/contracthashtool
  cd contracthashtool
  make CXXFLAGS="-I../secp256k1/install/usr/local/include -L../secp256k1/install/usr/local/lib -static"
  cd ..
```
4\. Download python-bitcoinrpc
```bash
  git clone https://github.com/jgarzik/python-bitcoinrpc
```
5\. Edit contrib/fedpeg/constants.py (replace `user:pass` with your RPC username and password):
```python
  # VARIOUS SETTINGS...
  sidechain_url = "http://user:pass@127.0.0.1:4241"
  bitcoin_url = "http://user:pass@127.0.0.1:18332"
```
6\. Use sidechain-manipulation.py:
```bash
  [matt@2ca87f82dd9a bitcoin]$ cd elements
  [matt@2ca87f82dd9a bitcoin]$ ./contrib/sidechain-manipulation.py generate-one-of-one-multisig sidechain-wallet
  One-of-one address: 22E8NxAdeYCatCFXFeLUbhfzBxUioGxP3dk9VH849exka9umWLkxzRmFFEwsLKR1pjPeE8UZRkVEQ7uab
  P2SH address: 2NCs5ufweTL8VHKNT6wrZMTkrnnmpZCy99j
  [matt@2ca87f82dd9a bitcoin]$ ./contrib/sidechain-manipulation.py send-to-sidechain 2NCs5ufweTL8VHKNT6wrZMTkrnnmpZCy99j 1
  Sending 1 to 2N3zXjbwdTcPsJiy8sUK9FhWJhqQCxA8Jjr...
  (nonce: 94ffbf32c1f1c0d3089b27c98fd991d5)
  Sent tx with id bf01b88710b6023125379510ebd84b373bee88217c80739a1144e5e92b4ee2d0

  --- 10 testnet blocks later ---

  [matt@2ca87f82dd9a bitcoin]$ ./contrib/sidechain-manipulation.py claim-on-sidechain 2NCs5ufweTL8VHKNT6wrZMTkrnnmpZCy99j 94ffbf32c1f1c0d3089b27c98fd991d5 bf01b88710b6023125379510ebd84b373bee88217c80739a1144e5e92b4ee2d0
  Redeeming from utxo 0377d218c36f5ee90244e660c387002296f3e4d5cac8fac8530b07e4d3241ccf:0 (value 21000000, refund 20999999)
  Success!
  Resulting txid: eabe26aba6286e1ee439baedeb75094ec0bcdaf54ed9481d9d2183e8a6424755

  --- 144 sidechain blocks later ---
  [matt@2ca87f82dd9a bitcoin]$ ./contrib/sidechain-manipulation.py spend-from-claim eabe26aba6286e1ee439baedeb75094ec0bcdaf54ed9481d9d2183e8a6424755 22E8NxAdeYCatCFXFeLUbhfzBxUioGxP3dk9VH849exka9umWLkxzRmFFEwsLKR1pjPeE8UZRkVEQ7uab
  Submitting tx to mempool...
  Success!
```

### To move money back out of Elements Alpha:

1\. See 1-5 of above.  
2\. Use sidechain-manipulation.py:
```bash
  [matt@2ca87f82dd9a bitcoin]$ cd elements
  [matt@2ca87f82dd9a bitcoin]$ ./contrib/sidechain-manipulation.py generate-one-of-one-multisig mainchain-wallet
  One-of-one address: mm8UW9YsjeHoVhXbHG4hEFKJt52P5iB7Vi
  P2SH address: 2MzqiCCUwtKKEV9Kxiyvk8ZuNCFKbcbneva
  [matt@2ca87f82dd9a bitcoin]$ ./contrib/sidechain-manipulation.py send-to-mainchain 2MzqiCCUwtKKEV9Kxiyvk8ZuNCFKbcbneva 1
```

### To run a fedpeg operator (for your own sidechain):
  1. See 1 and 2 in "To run alphad" (Do not forget to append -blindtrust=false to the alphad command args once bitcoin syncs!)
  2. See 2-5 of "To move money into Elements Alpha"
 Note that the bitcoind/sidechaind wallets must be EMPTY of keys/transactions except for those created automatically by fedpeg scripts
  3. Install python ZeroMQ.
  4. Ensure your clock is reasonably accurate (within a second should suffice)
  5. Edit bitcoin/contrib/fedpeg/constants.py with the neccessary information
  6. As a daemon/in screen/etc, run both bitcoin/contrib/fedpeg/withdrawwatch.py and bitcoin/contrib/fedpeg/blocksign.py

