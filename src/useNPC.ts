import { useState, useEffect } from "react";
import { Direction, chainId, enums } from "./common";
import {
  genWitness,
  prove,
  deserialize
} from '@ezkljs/engine/web'
import { getContract, Address } from "viem";
import ezklURL from '@ezkljs/engine/web/ezkl_bg.wasm?url'
import {
  useSessionClient,
} from "@latticexyz/entrykit/internal";
import npcAbi from "../out/NPC.sol/NPC.abi.json";
import { useClient } from "wagmi";

export type NPCState = [playerX: number, playerY: number, hunterX: number, hunterY: number];

delete WebAssembly.instantiateStreaming;

function readUploadedFileAsBuffer(file: File) {
  return new Promise<Uint8ClampedArray>((resolve, reject) => {
    const reader = new FileReader()

    reader.onload = (event) => {
      if (event.target && event.target.result instanceof ArrayBuffer) {
        resolve(new Uint8ClampedArray(event.target.result))
      } else {
        reject(new Error('Failed to read file'))
      }
    }

    reader.onerror = (error) => {
      reject(new Error('File could not be read: ' + error))
    }
    reader.readAsArrayBuffer(file)
  })
}

type FileMapping = {
  [key: string]: File
}

type FileSerMapping = {
  [key: string]: Uint8ClampedArray
}

async function convertFilesToFilesSer<T extends FileMapping>(
  files: T,
): Promise<FileSerMapping> {
  const fileReadPromises = Object.entries(files).map(async ([key, file]) => {
    const fileContent = await readUploadedFileAsBuffer(file)
    return { key, fileContent }
  })

  const fileContents = await Promise.all(fileReadPromises)

  const filesSer: FileSerMapping = {}
  for (const { key, fileContent } of fileContents) {
    filesSer[key] = fileContent
  }

  return filesSer
}

// TODO: not sure what are params reused across proving calls
type EZKLState = any;

type MoveResult = {
  direction: Direction;
  proof: Uint8Array;
}

// TODO: ezkl prover should compute the next move with a proof.
async function computeMove(npcState: NPCState, ezState: EZKLState): Promise<MoveResult> {
  // 
  // Fetch the files from public folder
  // Names of the sample files in the public directory
  const sampleFileNames: { [key: string]: string } = {
    pk: 'pk.key',
    compiled_onnx: 'network.compiled',
    srs: 'kzg.params',
  }

  // Helper function to fetch and create a file object from a public URL
  const fetchAndCreateFile = async (
    path: string,
    filename: string,
  ): Promise<File> => {
    // no cors mode is required to fetch files from public folder
    const response = await fetch(path)
    const blob = await response.blob()
    return new File([blob], filename, { type: blob.type })
  }

  // Fetch each sample file and create a File object
  const filePromises = Object.entries(sampleFileNames).map(([key, filename]) =>
    fetchAndCreateFile(`https://raw.githubusercontent.com/zkonduit/hunter-npc/main/samples/${filename}`, filename),
  )

  // Wait for all files to be fetched and created
  const files = await Promise.all(filePromises) as [File, File, File]

  const start = Date.now();
  // convert the npcState to a json object of type `{"input_data": [[6, 6, 3, 9]]}` and then convert to file format
  const npcStateJson = JSON.stringify({ "input_data": [npcState] });
  const npcStateFile = new File([npcStateJson], 'input.json', { type: 'application/json' });

  let genWitnessFileObject = {
    compiled_onnx: files[1],
    input: npcStateFile
  }

  let result = await convertFilesToFilesSer(genWitnessFileObject)

  console.log(result);

  let output
  if (result['compiled_onnx'] && result['input']) {
    output = genWitness(result['compiled_onnx'], result['input']);
  } else {
    throw new Error('Required files are missing');
  }

  console.log(output);

  let witness = deserialize(output)

  // Now that we have the witness we can generate the proof.
  const witnessFile = new File([JSON.stringify(witness)], 'witness.json', { type: 'application/json' });

  let genProofFileObject = {
    data: witnessFile,
    pk: files[0],
    model: files[1],
    srs: files[2]
  }

  result = await convertFilesToFilesSer(genProofFileObject)

  if (result['data'] && result['pk'] && result['model'] && result['srs']) {
    output = prove(
      result['data'],
      result['pk'],
      result['model'],
      result['srs'],
    )
  } else {
    throw new Error('Required proof files are missing');
  }

  let proofData = deserialize(output)

  console.log(proofData);

  const direction = Number(proofData.instances[0][4][1]);

  const end = Date.now();
  console.log(`Execution time: ${end - start} ms`);


  return {
    direction,
    proof: proofData.hex_proof
  }
}

export function useNPC() {
  const [ezkl, setEzkl] = useState<EZKLState>(null);
  useEffect(() => {
    async function initializeResources() {
      // Initialize the WASM module
      try {
        const engine = await import('@ezkljs/engine/web/ezkl.js')
        setEzkl(engine)
        await (engine as any).default(ezklURL, new WebAssembly.Memory({ initial: 20, maximum: 65536, shared: true }))
        // For human readable wasm debug errors call this function
        engine.init_panic_hook()

        console.log('ezkl engine loaded');
      } catch (e) {
        console.log(e);
      }
    }
    initializeResources()
  }, []);
  const { data: sessionClient } = useSessionClient();
  const client = useClient({ chainId });

  const getNpcContract = (addr: Address) => {
    return getContract({
      address: addr,
      abi: npcAbi,
      client: {
        public: client,
        wallet: sessionClient,
      },
    });
  }

  return {
    move: (state: NPCState, npcAddr: Address) => {
      if (ezkl) {
        console.log("computing move", state);
        computeMove(state, ezkl)
          .then(result => {
            console.log(result)

            const npcContract = getNpcContract(npcAddr);

            return npcContract.write.move([result.proof, result.direction]);
          })
          .then(result => {
            console.log("sent move tx", result);
          })
          .catch(console.error);
      } else {
        console.error("EZKL was not initialized");
      }
    }
  }
}
