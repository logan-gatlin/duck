import { readFileSync } from "fs";
import { join, dirname } from "path";
import { fileURLToPath } from "url";

const root = dirname(fileURLToPath(import.meta.url));
const wasmPath = join(root, "build", "main.wasm");
const wasmBytes = readFileSync(wasmPath);

const env = {
  log: function (i) {
    console.log(i);
  },
};

WebAssembly.instantiate(wasmBytes, { env }).then(({ instance }) => {
  if (typeof instance.exports._start === "function") {
    instance.exports._start();
  }
});
