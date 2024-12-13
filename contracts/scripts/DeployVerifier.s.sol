// SPDX-License-Identifier: MIT
pragma solidity >=0.8.24;

import {Script} from "forge-std/Script.sol";
import {console} from "forge-std/console.sol";
import {StoreSwitch} from "@latticexyz/store/src/StoreSwitch.sol";

import {IWorld} from "../codegen/world/IWorld.sol";
import {Halo2Verifier} from "../Halo2Verifier.sol";
import {IVerifier, NPC} from "../NPC.sol";

contract DeployVerifier is Script {
    function run() external {
        uint256 deployerPrivateKey = vm.envUint("PRIVATE_KEY");
        vm.startBroadcast(deployerPrivateKey);
        IVerifier verifier = new Halo2Verifier();
        console.log(address(verifier));
        vm.stopBroadcast();
    }
}
