import assert from "node:assert/strict";
import fs from "node:fs";
import path from "node:path";
import test from "node:test";
import { fileURLToPath } from "node:url";

const __filename = fileURLToPath(import.meta.url);
const __dirname = path.dirname(__filename);
const clipboardScript = fs.readFileSync(path.join(__dirname, "copy-to-clipboard.ts"), "utf8");

test("macOS image clipboard copy avoids Swift AppKit JIT", () => {
  assert.match(clipboardScript, /copyImageMacWithOsascript/);
  assert.doesNotMatch(clipboardScript, /await runCommand\('swift', \[swiftPath, 'image', imagePath\]\)/);
});

test("macOS image clipboard copy converts WebP to PNG before AppleScript", () => {
  assert.match(clipboardScript, /convertWebpMacToPng/);
  assert.match(clipboardScript, /path\.extname\(imagePath\)\.toLowerCase\(\) === '\.webp'/);
  assert.match(clipboardScript, /await copyImageMacWithOsascript\(pngPath\)/);
});
