Docker setup
-------------------

## Requirements

Docker engine release: 18.02.0+
docker-compose: 1.20.0+

## Build and start

`docker-compose -p elements up -d`

## Check status

`docker-compose -p elements ps`

### Output
```
     Name                    Command               State                       Ports                     
---------------------------------------------------------------------------------------------------------
elements_node_1   /docker-entrypoint.sh elem ...   Up      0.0.0.0:32769->7042/tcp, 0.0.0.0:32768->8332/tcp

```

## Jump into container

As root
`docker-compose -p elements exec node bash`
As bitcoin
`docker-compose -p elements exec -u bitcoin node bash`
Then: elements-cli / elements-tx available from within inside of container.

Note: if running as root, need to specify: -datadir=/home/bitcoin/.bitcoin

## Execute shell commands

`docker-compose -p elements exec node ip a`

## Use elements CLI from outside container

```
docker-compose -p elements exec -u bitcoin node elements-cli getinfo
docker-compose -p elements exec -u bitcoin node elements-cli getwalletinfo
```

## Stop

`docker-compose -p elements stop`

## Remove stack

`docker-compose -p elements rm -f`

## Modify startup parameters

### Edit: docker-compose.yml file

```
      elementsd
        -printtoconsole
        -rpcuser=${BITCOIN_RPC_USER:-username}
        -rpcpassword=${BITCOIN_RPC_PASSWORD:-password}
```

## Use your configuration file

### Create elements.conf
```
regtest=1
testnet=0
daemon=1
txindex=1
```

### Modify docker-compose.yml to
```
    volumes:
      - /home/bitcoin
      - ./elements.conf:/elements.conf
    command: >
      elementsd
        -printtoconsole
        -rpcuser=${BITCOIN_RPC_USER:-username}
        -rpcpassword=${BITCOIN_RPC_PASSWORD:-password}
        -conf=/elements.conf
```

### Start with

`docker-compose -p elements up -d`

## Check container logs

```
docker-compose -p elements logs

docker-compose -p elements exec -u bitcoin node \
    tail -f /home/bitcoin/.bitcoin/elementsregtest/debug.log
```

## Scale containers

`docker-compose -p elements scale node=2`

### Output
```
docker-compose -p elements ps
     Name                    Command               State                        Ports                      
-----------------------------------------------------------------------------------------------------------
elements_node_1   /docker-entrypoint.sh elem ...   Up      0.0.0.0:32769->7042/tcp, 0.0.0.0:32768->8332/tcp
elements_node_2   /docker-entrypoint.sh elem ...   Up      0.0.0.0:32771->7042/tcp, 0.0.0.0:32770->8332/tcp
```
