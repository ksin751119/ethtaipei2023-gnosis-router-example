import { Wallet, BigNumber } from 'ethers';
import { ethers, deployments } from 'hardhat';
import { ROUTER, AGWXDAI_TOKEN, AGAVE_WETH_GATEWAY } from './utils/constants';
import { ether, simpleEncode } from './utils/utils';

interface IParam {
  LogicBatch: ILogicBatch;
}

interface ILogic {
  to: string;
  data: string;
  inputs: IInput[];
  wrapMode: number;
  approveTo: string;
  callback: string;
}

interface IInput {
  token: string;
  amountBps: BigNumber;
  amountOrOffset: BigNumber;
}

interface ILogicBatch {
  logics: ILogic[];
  deadline: BigNumber;
}

describe('Router', function () {
  let user: Wallet;
  let router: any;
  let aToken: any;

  const setupTest = deployments.createFixture(async ({ deployments, ethers }, options) => {
    await deployments.fixture(''); // ensure you start from a fresh deployments
    [user] = await (ethers as any).getSigners();

    router = await ethers.getContractAt('Router', ROUTER);
    aToken = await ethers.getContractAt('IERC20', AGWXDAI_TOKEN);
  });

  // `beforeEach` will run before each test, re-deploying the contract every
  // time. It receives a callback, which can be async.
  beforeEach(async function () {
    // setupTest will use the evm_snapshot to reset environment for speed up testing
    await setupTest();
  });

  describe('router', function () {
    it('swap xdai to AGAVE though router', async function () {
      // Build supply xDAI Agave protocol
      const agaveSupplyData = simpleEncode('depositETH(address,uint16)', [user.address, 0]);
      const logic: ILogic = {
        to: AGAVE_WETH_GATEWAY, // WETHGateway
        data: agaveSupplyData,
        inputs: [
          {
            token: '0xEeeeeEeeeEeEeeEeEeEeeEEEeeeeEeeeeeeeEEeE',
            amountBps: ethers.constants.MaxUint256,
            amountOrOffset: ether('1'),
          },
        ],
        wrapMode: 0,
        approveTo: ethers.constants.AddressZero,
        callback: ethers.constants.AddressZero,
      };

      const routerTx = await router.execute([logic], [], 0, {
        value: ether('1'),
      });
      await routerTx.wait();
      console.log((await aToken.balanceOf(user.address)).toString());
    });
  });
});
