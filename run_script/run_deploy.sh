

#!/bin/bash

# deploy prod
TAG=Greeter
PROD_URL=https://rpc.ankr.com/polygon
PROD_SECRET=
PROD_URL=$PROD_URL PROD_SECRET=$PROD_SECRET npx hardhat deploy --network prod --tags $TAG --reset
