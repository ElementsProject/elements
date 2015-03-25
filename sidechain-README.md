See https://github.com/bitcoin/bitcoin/blob/master/doc/build-unix.md
for notes on dependencies that must be installed before beginning.

To run sidechaind:
	1. Download/build bitcoind/sidechaind
	```bash
	git clone https://github.com/bitcoin/bitcoin
	cd bitcoin
	git checkout bitcoinchain2
	./autogen.sh && ./configure && make
	mv src/bitcoin{d,-cli} ../
	git checkout sidechain-alpha-1
	./autogen.sh && ./configure && make
	mv src/bitcoind ../sidechaind && mv src/bitcoin-cli ../sidechain-cli
	cd ..
	```
	2. Run bitcoind/sidechaind
	```bash
	RPC_USER=user
	RPC_PASS=pass
	./bitcoind -rpcuser=$RPC_USER -rpcpassword=$RPC_PASS -testnet -txindex -daemon
	# Wait for chain sync to complete
	PCT="0.00"; while [ "${PCT::1}" != "1" -a "$PCT" != "0.99" -a "$PCT" != "0.98" ]; do PCT=`./bitcoin-cli -rpcuser=$RPC_USER -rpcpassword=$RPC_PASS -testnet getblockchaininfo | grep verificationprogress | awk '{ print substr($3, 0, 4) }'`; echo "Chain sync at $PCT"; sleep 30; done
	./sidechaind -rpcuser=$RPC_USER -rpcpassword=$RPC_PASS -testnet -rpcconnect=127.0.0.1 -rpcconnectport=18332 -tracksidechain=all -txindex -daemon
	```

To move money into the sidechain:
	1. Download secp256k1:
	```bash
	git clone https://github.com/bitcoin/secp256k1
	cd secp256k1
	./autogen.sh && ./configure --with-bignum=no && make
	make DESTDIR=`pwd`/install install
	cd ..
	```
	2. Download contracthashtool
	```bash
	git clone https://github.com/blockstream/contracthashtool
	cd contracthashtool
	make CXXFLAGS="-I../secp256k1/install/usr/local/include -L../secp256k1/install/usr/local/lib -static"
	cd ..
	```
	3. Download python-bitcoinrpc
	```bash
	git clone https://github.com/jgarzik/python-bitcoinrpc
	```
	4. Use sidechain-manipulation.py:
	```bash
	[matt@2ca87f82dd9a bitcoin]$ cd bitcoin
	[matt@2ca87f82dd9a bitcoin]$ ./contrib/sidechain-manipulation.py generate-one-of-one-multisig sidechain-wallet
	One-of-one address: mwrm4vAmj6yyVnmbZk2bsr396orwzkRvHv
	P2SH address: 2N6uBifUoJrir8UhF6uqq8MsE1QQZKnK28k
	Redeem script: 512102c62d23b0146077503f6233802e8d1089c9f211ffef561055f847bca8c6ef4b0d51ae
	[matt@2ca87f82dd9a bitcoin]$ ./contrib/sidechain-manipulation.py send-to-sidechain 2N6uBifUoJrir8UhF6uqq8MsE1QQZKnK28k 0.00005
	Sending 0.00005 to 2Mu2Cog6oNqgnNmtceMaYAaNrRKmPNxjkw8...
	(nonce: 948165328cb7815fb8f86aa305b73a02)
	Sent tx with id d4eb16a2100fcd32c66fc18f4a3ac840f88baa60b1556cbf98980359ec2e1324

	--- 10 testnet blocks later ---

	[matt@2ca87f82dd9a bitcoin]$ ./contrib/sidechain-manipulation.py claim-on-sidechain 2N6uBifUoJrir8UhF6uqq8MsE1QQZKnK28k 948165328cb7815fb8f86aa305b73a02 d4eb16a2100fcd32c66fc18f4a3ac840f88baa60b1556cbf98980359ec2e1324
	Redeeming from utxo 6a103184c8874f31ddd35289662452fa33b036dded5db11e7f959cd280d03312:0 (value 0.001, refund 0)
	Success!
	Resulting txid: e532f7f7fc1e23e61f51e535ac6be26ce7ac3a64ca7bc37e1ea58d74cac8484c

	--- 144 sidechain blocks later ---
	[matt@2ca87f82dd9a bitcoin]$ ./contrib/sidechain-manipulation.py spend-from-claim e532f7f7fc1e23e61f51e535ac6be26ce7ac3a64ca7bc37e1ea58d74cac8484c mwrm4vAmj6yyVnmbZk2bsr396orwzkRvHv
	Submitting tx to mempool...
	Success!
	```

To move money back out of the sidechain:
	1. See 1-3 of above.
	4. Use sidechain-manipulation.py:
	```bash
	[matt@2ca87f82dd9a bitcoin]$ cd bitcoin
	[matt@2ca87f82dd9a bitcoin]$ ./contrib/sidechain-manipulation.py generate-one-of-one-multisig mainchain-wallet
	One-of-one address: myFANdHdFUsRovMRJqXKzJ7v9Wp4BxyrJV
	P2SH address: 2N5AK9uGMQZxTzEfafNqyC2SPmVWkvN7Pvs
	Redeem script: 512103639f23f7356a4215611d083174be4846b1b2ee8894bec43151eb9d480d9689b151ae
	[matt@2ca87f82dd9a bitcoin]$ ./contrib/sidechain-manipulation.py send-to-mainchain 2N5AK9uGMQZxTzEfafNqyC2SPmVWkvN7Pvs 0.00005

To run a fedpeg operator:
	1. See 1 and 2 in "To run sidechaind" (APPEND -blindtrust=false TO THE SIDECHAIND COMMAND ARGS!)
	2. See 1-3 of "To move money into the sidechain"
	   Note that the bitcoind/sidechaind wallets must be EMPTY of keys/transactions except for those created automatically by fedpeg scripts
	3. Install python ZeroMQ.
	4. Ensure your clock is reasonably accurate (within a second should suffice)
	5. Edit bitcoin/contrib/fedpeg/constants.py with the neccessary information
	6. As a daemon/in screen/etc, run both bitcoin/contrib/fedpeg/withdrawwatch.py and bitcoin/contrib/fedpeg/blocksign.py
