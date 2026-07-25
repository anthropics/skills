import { stat, readdir } from "node:fs/promises";
import { homedir } from "node:os";
import path from "node:path";
import { GenError } from "./types.ts";
import type { ToolCall } from "./types.ts";
import { hasImageGenInvocation } from "./parser.ts";

const PNG_MAGIC = Buffer.from([0x89, 0x50, 0x4e, 0x47, 0x0d, 0x0a, 0x1a, 0x0a]);

export function codexHome(): string {
  return process.env.CODEX_HOME ?? path.join(homedir(), ".codex");
}

export async function verifyImageGenWasInvoked(threadId: string | null): Promise<{ ok: boolean; reason?: string }> {
  if (!threadId) return { ok: false, reason: "no thread id" };
  const dir = path.join(codexHome(), "generated_images", threadId);
  try {
    const entries = await readdir(dir);
    const pngs = entries.filter((e) => e.toLowerCase().endsWith(".png"));
    if (pngs.length === 0) return { ok: false, reason: `no PNG in ${dir}` };
    return { ok: true };
  } catch (e: any) {
    return { ok: false, reason: `cannot read ${dir}: ${e?.code ?? e?.message}` };
  }
}

// Real evidence that image_gen ran in THIS thread. Codex's image_gen tool does
// not surface as a stream item, so a successful run shows only reasoning/shell/
// agent_message — `dirHasImage` (a PNG in this thread's generated_images dir) is
// what proves it. The stream check is kept as a forward-compatible signal in
// case a future Codex version emits the item. The #185 shortcut (copying an
// unrelated history image, which lives under a different thread id) yields
// neither, so it is correctly rejected.
export function hasImageGenEvidence(toolCalls: ToolCall[], dirHasImage: boolean): boolean {
  return dirHasImage || hasImageGenInvocation(toolCalls);
}

export async function verifyOutput(outputPath: string): Promise<{ bytes: number }> {
  let s;
  try {
    s = await stat(outputPath);
  } catch {
    throw new GenError("output_missing", `Output file not created: ${outputPath}`);
  }
  if (s.size < 1000) {
    throw new GenError("invalid_png", `Output file too small (${s.size} bytes)`);
  }
  const file = Bun.file(outputPath);
  const head = new Uint8Array(await file.slice(0, 8).arrayBuffer());
  for (let i = 0; i < PNG_MAGIC.length; i++) {
    if (head[i] !== PNG_MAGIC[i]) {
      throw new GenError("invalid_png", `Output is not a valid PNG (magic mismatch)`);
    }
  }
  return { bytes: s.size };
}
