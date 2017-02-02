import os
import subprocess 
import json
import argparse

def sign_block(datadir):
    bc=["./elements-cli", "-datadir=" + datadir]
    new_block = subprocess.check_output(bc + ["getnewblockhex"]).strip('\n')
    blocksig = subprocess.check_output(bc + ["signblock", new_block]).strip('\n')
    signed_block = subprocess.check_output(bc + ["combineblocksigs", new_block, '["' + blocksig + '"]']) 
    signed_block_json = json.loads(signed_block)
    signed_block_hex = signed_block_json['hex'] 
    subprocess.check_output(bc + ['submitblock', signed_block_hex])

def generate_n_blocks(n,datadir): 
    for i in range(0,n): 
        sign_block(datadir)

if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument('--num')
    parser.add_argument("--datadir")
    datadir="~/.bitcoin/elements/"
    default_num_blocks=100
    args = vars(parser.parse_args())
    if args['datadir'] != None:
        datadir = args['datadir']
    if args['num'] != None: 
        num_blocks=int(args['num'])
    generate_n_blocks(num_blocks,datadir)
