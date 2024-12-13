import { useClient } from "wagmi";
import { chainId, worldAbi } from "./common";
import {
  getContract,
  Address,
  encodeDeployData,
  pad,
  concatHex,
  toHex,
} from "viem";
import { useSync } from "./mud/useSync";
import { useQuery } from "@tanstack/react-query";
import {
  useSessionClient,
  useEntryKitConfig,
} from "@latticexyz/entrykit/internal";
import { observer } from "@latticexyz/explorer/observer";
import npcContract from "../out/NPC.sol/NPC.json";
import { getAction } from "viem/utils";
import { sendUserOperation } from "viem/account-abstraction";

export function useWorldContract() {
  const { worldAddress } = useEntryKitConfig();
  const { waitForTransaction } = useSync();
  const client = useClient({ chainId });
  const { data: sessionClient } = useSessionClient();

  const deployNPC = async (target: Address) => {
    if (!sessionClient) {
      throw new Error("No session client");
    }
    console.log("deploying npc", {
      chain: sessionClient.chain ?? null,
      account: sessionClient.account,
      data: encodeDeployData({
        abi: npcContract.abi,
        args: [
          worldAddress,
          "0x75afe612b0b6963f407aaBFbBc1096c1587456d9",
          target,
        ],
        bytecode: npcContract.bytecode.object as `0x${string}`,
      }),
      gas: 10_000_000n,
    });

    const bytecode = encodeDeployData({
      abi: npcContract.abi,
      args: [
        worldAddress,
        "0x75afe612b0b6963f407aaBFbBc1096c1587456d9",
        target,
      ],
      bytecode: npcContract.bytecode.object as `0x${string}`,
    });

    const hash = await getAction(
      sessionClient,
      sendUserOperation,
      "sendUserOperation"
    )({
      calls: [
        {
          to: "0x4e59b44847b379578588920ca78fbf26c0b4956c",
          data: concatHex([pad(toHex(Date.now())), bytecode]),
        },
      ],
    });
    console.log("deployed npc", hash);
  };

  const { data: worldContract } = useQuery({
    queryKey: ["worldContract", worldAddress, client?.uid, sessionClient?.uid],
    queryFn: () => {
      if (!client || !sessionClient) {
        throw new Error("Not connected.");
      }

      return getContract({
        abi: worldAbi,
        address: worldAddress,
        client: {
          public: client,
          wallet: sessionClient.extend(observer()),
        },
      });
    },
    staleTime: Infinity,
    refetchOnMount: false,
    refetchOnReconnect: false,
    refetchOnWindowFocus: false,
  });

  return worldContract && waitForTransaction
    ? {
      worldContract,
      waitForTransaction,
      deployNPC,
    }
    : {};
}
