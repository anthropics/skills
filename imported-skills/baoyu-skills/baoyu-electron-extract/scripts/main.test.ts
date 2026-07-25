import assert from "node:assert/strict";
import { mkdir, mkdtemp, readFile, rm, writeFile } from "node:fs/promises";
import os from "node:os";
import path from "node:path";
import test from "node:test";

import { normalizeSourcePath, restoreFromMap } from "./main.ts";

test("normalizes Vite source map paths into readable project paths", () => {
  const extractedRoot = path.join(os.tmpdir(), "app", "extracted");
  const mapPath = path.join(extractedRoot, ".vite", "main", "index.js.map");

  assert.equal(
    normalizeSourcePath(
      "../../src/main/agent/claude-agent.ts",
      mapPath,
      extractedRoot,
      undefined
    ),
    "src/main/agent/claude-agent.ts"
  );

  assert.equal(
    normalizeSourcePath(
      "../../../shared/src/lib/prompt-classification.ts",
      mapPath,
      extractedRoot,
      undefined
    ),
    "shared/src/lib/prompt-classification.ts"
  );

  assert.equal(
    normalizeSourcePath(
      "./src/renderer/app.tsx",
      mapPath,
      extractedRoot,
      "webpack://moss/"
    ),
    "moss/src/renderer/app.tsx"
  );
});

test("restores source map sources without hashing usable relative paths", async () => {
  const root = await mkdtemp(path.join(os.tmpdir(), "baoyu-electron-extract-"));
  try {
    const extractedRoot = path.join(root, "extracted");
    const restoredRoot = path.join(root, "restored");
    const mapDir = path.join(extractedRoot, ".vite", "main");
    const mapPath = path.join(mapDir, "index.js.map");
    await mkdir(mapDir, { recursive: true });
    await writeFile(
      mapPath,
      JSON.stringify({
        version: 3,
        file: "index.js",
        sources: [
          "../../src/main.ts",
          "../../src/common/ipcChannels.ts",
          "../../../shared/src/lib/prompt-classification.ts",
          "webpack://moss/./src/renderer/app.tsx",
          "../../../../node_modules/pkg/index.js",
          "..\\..\\node_modules\\windows-pkg\\index.js",
          "webpack/runtime/chunk loading",
        ],
        sourcesContent: [
          "export const main = true;\n",
          "export const ipc = true;\n",
          "export const shared = true;\n",
          "export const renderer = true;\n",
          "module.exports = {};\n",
          "module.exports = {};\n",
          "runtime();\n",
        ],
      }),
      "utf8"
    );

    const warnings: string[] = [];
    const restored = restoreFromMap(
      mapPath,
      extractedRoot,
      restoredRoot,
      warnings
    );

    assert.equal(restored, 4);
    assert.deepEqual(warnings, []);
    assert.equal(
      await readFile(path.join(restoredRoot, "src", "main.ts"), "utf8"),
      "export const main = true;\n"
    );
    assert.equal(
      await readFile(
        path.join(restoredRoot, "src", "common", "ipcChannels.ts"),
        "utf8"
      ),
      "export const ipc = true;\n"
    );
    assert.equal(
      await readFile(
        path.join(
          restoredRoot,
          "shared",
          "src",
          "lib",
          "prompt-classification.ts"
        ),
        "utf8"
      ),
      "export const shared = true;\n"
    );
    assert.equal(
      await readFile(
        path.join(restoredRoot, "moss", "src", "renderer", "app.tsx"),
        "utf8"
      ),
      "export const renderer = true;\n"
    );
  } finally {
    await rm(root, { recursive: true, force: true });
  }
});
