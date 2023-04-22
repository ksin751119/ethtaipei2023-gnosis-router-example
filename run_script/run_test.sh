#!/bin/bash
URL=https://rpc.gnosischain.com
FORK_URL=$URL npx hardhat test --network hardhat ./test/Router.test.ts
