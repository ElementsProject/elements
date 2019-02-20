Run Ocean node with Docker
-------------------

## Requirements

Docker engine release: 18.02.0 or latest
docker-compose: 1.20.0 or latest

## Download docker-compose.yml from commerceblock/ocean/contrib/docker/docker-compose.yml

```
cd ~
curl -O https://raw.githubusercontent.com/commerceblock/ocean/master/contrib/docker/docker-compose.yml
```

## Download and read terms and conditions

```
curl -O https://raw.githubusercontent.com/commerceblock/ocean/master/doc/terms-and-conditions/ocean_main/latest.txt
```

## Download image and start

`docker-compose -p ocean up -d`

## Check status

`docker-compose -p ocean ps`

### Output
```
    Name                  Command               State                         Ports
---------------------------------------------------------------------------------------------------------
ocean_node_1   /docker-entrypoint.sh elem ...   Up      0.0.0.0:32768->18332/tcp, 0.0.0.0:32769->7042/tcp

```

## Check logs and see if node is synching

`docker-compose -p ocean logs --follow`

Hit ctrl+c to stop following

## Check if connected to CommerceBlock testnet

`docker-compose -p ocean exec node ocean-cli -rpcport=18332 -rpcuser=ocean -rpcpassword=oceanpass getpeerinfo`

Should see: "testnet.commerceblock.com:7043"

## Check block count

`docker-compose -p ocean exec node ocean-cli -rpcport=18332 -rpcuser=ocean -rpcpassword=oceanpass getblockcount`

Once synched, block count should be the same as in: https://cbtexplorer.com

## Data persistence

`mkdir ~/ocean_full_node`
`mkdir -p ~/ocean_full_node/terms-and-conditions/ocean_main`
`cp latest.txt ~/ocean_full_node/terms-and-conditions/ocean_main/`

edit: docker-compose.yml, adding:
```
    image: commerceblock/ocean:087f1aab8
    volumes:
      - /home/your_username/ocean_full_node:/home/bitcoin/.bitcoin
```

## Dig deeper

As root
`docker-compose -p ocean exec node bash`
As bitcoin
`docker-compose -p ocean exec -u bitcoin node bash`
Then: ocean-cli / ocean-tx available from within inside of container.

Note: if running as root, need to specify: -datadir=/home/bitcoin/.bitcoin

## Execute shell commands

`docker-compose -p ocean exec node ip a`

## Scale containers
Up
`docker-compose -p ocean scale node=2`
Down
`docker-compose -p ocean scale node=1`

## Stop

`docker-compose -p ocean stop`

## Remove stack

`docker-compose -p ocean rm -f`
