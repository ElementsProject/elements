#!/usr/bin/env python3

import os
import subprocess 
import json
import argparse

def sign_block(datadir):
    """
    Gets a new blocks hex, generates a signature for that block,
    then submits the signed block to the running oceand
    """
    bc=["./ocean-cli", "-regtest"]
    if datadir is not None:
        bc.append("-datadir=" + datadir)
    new_block = subprocess.check_output(bc + ["getnewblockhex"]).strip('\n')
    blocksig = subprocess.check_output(bc + ["signblock", new_block]).strip('\n')
    signed_block = subprocess.check_output(bc + ["combineblocksigs", new_block, '["' + blocksig + '"]'])
    signed_block_json = json.loads(signed_block)
    signed_block_hex = signed_block_json['hex']
    subprocess.check_output(bc + ['submitblock', signed_block_hex])

def generate_n_blocks(n,datadir):
    """
    Generates n blocks and places them into the given datadir
    """
    for i in range(0,n):
        sign_block(datadir)

if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument('--num')
    parser.add_argument("--datadir")
    num_blocks=100
    args = vars(parser.parse_args())
    datadir = args['datadir']
    if args['num'] != None:
        num_blocks=int(args['num'])
    generate_n_blocks(num_blocks,datadir)
