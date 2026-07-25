import { spawnSync } from "node:child_process";
import process from "node:process";

export function applyAutocorrect(filePath: string): boolean {
  const npxCmd = process.platform === "win32" ? "npx.cmd" : "npx";
  const result = spawnSync(npxCmd, ["autocorrect-node", "--fix", filePath], {
    stdio: "inherit",
  });
  return result.status === 0;
}
