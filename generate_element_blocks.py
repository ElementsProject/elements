import os
import subprocess 
import json
bc=["./elements-cli", "-datadir=/tmp/elementsdatadir/"]

def sign_block():
    new_block = subprocess.check_output(bc + ["getnewblockhex"]).strip('\n')
    blocksig = subprocess.check_output(bc + ["signblock", new_block]).strip('\n')
    signed_block = subprocess.check_output(bc + ["combineblocksigs", new_block, '["' + blocksig + '"]']) 
    signed_block_json = json.loads(signed_block)
    signed_block_hex = signed_block_json['hex'] 
    subprocess.check_output(bc + ['submitblock', signed_block_hex])

def generate_n_blocks(n): 
    for i in range(0,n): 
        sign_block()

generate_n_blocks(100)
