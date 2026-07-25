import assert from "node:assert/strict";
import fs from "node:fs/promises";
import os from "node:os";
import path from "node:path";
import { execFile } from "node:child_process";
import { promisify } from "node:util";
import test from "node:test";

const execFileAsync = promisify(execFile);
const repoRoot = path.resolve(import.meta.dirname, "..", "..", "..");
const scriptPath = path.join(repoRoot, "skills", "baoyu-image-gen", "scripts", "build-batch.ts");

async function makeFixture(): Promise<{
  root: string;
  outlinePath: string;
  promptsDir: string;
  outputPath: string;
}> {
  const root = await fs.mkdtemp(path.join(os.tmpdir(), "baoyu-image-gen-build-batch-"));
  const outlinePath = path.join(root, "outline.md");
  const promptsDir = path.join(root, "prompts");
  const outputPath = path.join(root, "batch.json");

  await fs.mkdir(promptsDir, { recursive: true });
  await fs.writeFile(
    outlinePath,
    `## Illustration 1
**Position**: demo
**Purpose**: demo
**Visual Content**: demo
**Filename**: 01-demo.png
`,
  );
  await fs.writeFile(path.join(promptsDir, "01-demo.md"), "A demo prompt\n");

  return { root, outlinePath, promptsDir, outputPath };
}

async function runBuildBatch(args: string[]): Promise<void> {
  await execFileAsync(process.execPath, ["--import", "tsx", scriptPath, ...args], {
    cwd: repoRoot,
  });
}

test("build-batch omits default model so baoyu-image-gen can resolve env or EXTEND defaults", async () => {
  const fixture = await makeFixture();

  await runBuildBatch([
    "--outline",
    fixture.outlinePath,
    "--prompts",
    fixture.promptsDir,
    "--output",
    fixture.outputPath,
  ]);

  const batch = JSON.parse(await fs.readFile(fixture.outputPath, "utf8")) as {
    tasks: Array<Record<string, unknown>>;
  };

  assert.equal(batch.tasks.length, 1);
  assert.equal(batch.tasks[0]?.provider, "replicate");
  assert.equal(Object.hasOwn(batch.tasks[0]!, "model"), false);
});

test("build-batch preserves explicit model overrides", async () => {
  const fixture = await makeFixture();

  await runBuildBatch([
    "--outline",
    fixture.outlinePath,
    "--prompts",
    fixture.promptsDir,
    "--output",
    fixture.outputPath,
    "--model",
    "acme/custom-model",
  ]);

  const batch = JSON.parse(await fs.readFile(fixture.outputPath, "utf8")) as {
    tasks: Array<Record<string, unknown>>;
  };

  assert.equal(batch.tasks[0]?.model, "acme/custom-model");
});

test("build-batch propagates direct-usage references from prompt frontmatter", async () => {
  const fixture = await makeFixture();

  await fs.writeFile(
    path.join(fixture.promptsDir, "01-demo.md"),
    `---
illustration_id: 01
type: infographic
references:
  - ref_id: 01
    filename: 01-ref-brand.png
    usage: direct
  - ref_id: 02
    filename: 02-ref-style.png
    usage: style
---

A demo prompt
`,
  );

  await runBuildBatch([
    "--outline",
    fixture.outlinePath,
    "--prompts",
    fixture.promptsDir,
    "--output",
    fixture.outputPath,
  ]);

  const batch = JSON.parse(await fs.readFile(fixture.outputPath, "utf8")) as {
    tasks: Array<Record<string, unknown>>;
  };

  assert.deepEqual(batch.tasks[0]?.ref, ["references/01-ref-brand.png"]);
});

test("build-batch omits ref field when no direct references exist", async () => {
  const fixture = await makeFixture();

  await fs.writeFile(
    path.join(fixture.promptsDir, "01-demo.md"),
    `---
illustration_id: 01
references:
  - ref_id: 01
    filename: 01-ref-palette.png
    usage: palette
---

A demo prompt
`,
  );

  await runBuildBatch([
    "--outline",
    fixture.outlinePath,
    "--prompts",
    fixture.promptsDir,
    "--output",
    fixture.outputPath,
  ]);

  const batch = JSON.parse(await fs.readFile(fixture.outputPath, "utf8")) as {
    tasks: Array<Record<string, unknown>>;
  };

  assert.equal(Object.hasOwn(batch.tasks[0]!, "ref"), false);
});

test("build-batch honors --refs-dir override", async () => {
  const fixture = await makeFixture();

  await fs.writeFile(
    path.join(fixture.promptsDir, "01-demo.md"),
    `---
illustration_id: 01
references:
  - ref_id: 01
    filename: brand.png
    usage: direct
---

A demo prompt
`,
  );

  await runBuildBatch([
    "--outline",
    fixture.outlinePath,
    "--prompts",
    fixture.promptsDir,
    "--output",
    fixture.outputPath,
    "--refs-dir",
    "refs",
  ]);

  const batch = JSON.parse(await fs.readFile(fixture.outputPath, "utf8")) as {
    tasks: Array<Record<string, unknown>>;
  };

  assert.deepEqual(batch.tasks[0]?.ref, ["refs/brand.png"]);
});
