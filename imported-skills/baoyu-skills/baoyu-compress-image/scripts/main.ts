#!/usr/bin/env bun
import { existsSync, statSync, readdirSync, unlinkSync, renameSync } from "fs";
import { basename, dirname, extname, join, resolve } from "path";
import { spawn } from "child_process";

type Compressor = "sips" | "cwebp" | "imagemagick" | "sharp";
type Format = "webp" | "png" | "jpeg";

interface Options {
  input: string;
  output?: string;
  format: Format;
  quality: number;
  keep: boolean;
  recursive: boolean;
  json: boolean;
}

interface Result {
  input: string;
  output: string;
  inputSize: number;
  outputSize: number;
  ratio: number;
  compressor: Compressor;
}

const SUPPORTED_EXTS = [".png", ".jpg", ".jpeg", ".webp", ".gif", ".tiff"];

async function commandExists(cmd: string): Promise<boolean> {
  try {
    const proc = spawn("which", [cmd], { stdio: "pipe" });
    return new Promise((res) => {
      proc.on("close", (code) => res(code === 0));
      proc.on("error", () => res(false));
    });
  } catch {
    return false;
  }
}

async function detectCompressor(format: Format): Promise<Compressor> {
  if (format === "webp") {
    if (await commandExists("cwebp")) return "cwebp";
    if (await commandExists("convert")) return "imagemagick";
    return "sharp";
  }
  if (process.platform === "darwin") return "sips";
  if (await commandExists("convert")) return "imagemagick";
  return "sharp";
}

function runCmd(cmd: string, args: string[]): Promise<{ code: number; stderr: string }> {
  return new Promise((res) => {
    const proc = spawn(cmd, args, { stdio: ["ignore", "ignore", "pipe"] });
    let stderr = "";
    proc.stderr?.on("data", (d) => (stderr += d.toString()));
    proc.on("close", (code) => res({ code: code ?? 1, stderr }));
    proc.on("error", (e) => res({ code: 1, stderr: e.message }));
  });
}

async function compressWithSips(input: string, output: string, format: Format, quality: number): Promise<void> {
  const fmt = format === "jpeg" ? "jpeg" : format;
  const args = ["-s", "format", fmt, "-s", "formatOptions", String(quality), input, "--out", output];
  const { code, stderr } = await runCmd("sips", args);
  if (code !== 0) throw new Error(`sips failed: ${stderr}`);
}

async function compressWithCwebp(input: string, output: string, quality: number): Promise<void> {
  const args = ["-q", String(quality), input, "-o", output];
  const { code, stderr } = await runCmd("cwebp", args);
  if (code !== 0) throw new Error(`cwebp failed: ${stderr}`);
}

async function compressWithImagemagick(input: string, output: string, quality: number): Promise<void> {
  const args = [input, "-quality", String(quality), output];
  const { code, stderr } = await runCmd("convert", args);
  if (code !== 0) throw new Error(`convert failed: ${stderr}`);
}

async function compressWithSharp(input: string, output: string, format: Format, quality: number): Promise<void> {
  const sharp = (await import("sharp")).default;
  let pipeline = sharp(input);
  if (format === "webp") pipeline = pipeline.webp({ quality });
  else if (format === "png") pipeline = pipeline.png({ quality });
  else if (format === "jpeg") pipeline = pipeline.jpeg({ quality });
  await pipeline.toFile(output);
}

async function compress(
  compressor: Compressor,
  input: string,
  output: string,
  format: Format,
  quality: number
): Promise<void> {
  switch (compressor) {
    case "sips":
      await compressWithSips(input, output, format, quality);
      break;
    case "cwebp":
      if (format !== "webp") {
        await compressWithSharp(input, output, format, quality);
      } else {
        await compressWithCwebp(input, output, quality);
      }
      break;
    case "imagemagick":
      await compressWithImagemagick(input, output, quality);
      break;
    case "sharp":
      await compressWithSharp(input, output, format, quality);
      break;
  }
}

function getOutputPath(input: string, format: Format, keep: boolean, customOutput?: string): string {
  if (customOutput) return resolve(customOutput);
  const dir = dirname(input);
  const base = basename(input, extname(input));
  const ext = format === "jpeg" ? ".jpg" : `.${format}`;
  if (keep && extname(input).toLowerCase() === ext) {
    return join(dir, `${base}-compressed${ext}`);
  }
  return join(dir, `${base}${ext}`);
}

function formatSize(bytes: number): string {
  if (bytes < 1024) return `${bytes}B`;
  if (bytes < 1024 * 1024) return `${Math.round(bytes / 1024)}KB`;
  return `${(bytes / (1024 * 1024)).toFixed(1)}MB`;
}

async function processFile(
  compressor: Compressor,
  input: string,
  opts: Options
): Promise<Result> {
  const absInput = resolve(input);
  const inputSize = statSync(absInput).size;
  const output = getOutputPath(absInput, opts.format, opts.keep, opts.output);
  const tempOutput = output + ".tmp";

  await compress(compressor, absInput, tempOutput, opts.format, opts.quality);

  const outputSize = statSync(tempOutput).size;

  if (!opts.keep && absInput !== output) {
    const ext = extname(absInput);
    const base = absInput.slice(0, -ext.length);
    renameSync(absInput, `${base}_original${ext}`);
  }
  renameSync(tempOutput, output);

  return {
    input: absInput,
    output,
    inputSize,
    outputSize,
    ratio: outputSize / inputSize,
    compressor,
  };
}

function collectFiles(dir: string, recursive: boolean): string[] {
  const files: string[] = [];
  const entries = readdirSync(dir, { withFileTypes: true });
  for (const entry of entries) {
    const full = join(dir, entry.name);
    if (entry.isDirectory() && recursive) {
      files.push(...collectFiles(full, recursive));
    } else if (entry.isFile() && SUPPORTED_EXTS.includes(extname(entry.name).toLowerCase())) {
      files.push(full);
    }
  }
  return files;
}

function printHelp() {
  console.log(`Usage: bun main.ts <input> [options]

Options:
  -o, --output <path>   Output path
  -f, --format <fmt>    Output format: webp, png, jpeg (default: webp)
  -q, --quality <n>     Quality 0-100 (default: 80)
  -k, --keep            Keep original file
  -r, --recursive       Process directories recursively
      --json            JSON output
  -h, --help            Show help`);
}

function parseArgs(args: string[]): Options | null {
  const opts: Options = {
    input: "",
    format: "webp",
    quality: 80,
    keep: false,
    recursive: false,
    json: false,
  };

  for (let i = 0; i < args.length; i++) {
    const arg = args[i];
    if (arg === "-h" || arg === "--help") {
      printHelp();
      process.exit(0);
    } else if (arg === "-o" || arg === "--output") {
      opts.output = args[++i];
    } else if (arg === "-f" || arg === "--format") {
      const fmt = args[++i]?.toLowerCase();
      if (fmt === "webp" || fmt === "png" || fmt === "jpeg" || fmt === "jpg") {
        opts.format = fmt === "jpg" ? "jpeg" : (fmt as Format);
      } else {
        console.error(`Invalid format: ${fmt}`);
        return null;
      }
    } else if (arg === "-q" || arg === "--quality") {
      const q = parseInt(args[++i], 10);
      if (isNaN(q) || q < 0 || q > 100) {
        console.error(`Invalid quality: ${args[i]}`);
        return null;
      }
      opts.quality = q;
    } else if (arg === "-k" || arg === "--keep") {
      opts.keep = true;
    } else if (arg === "-r" || arg === "--recursive") {
      opts.recursive = true;
    } else if (arg === "--json") {
      opts.json = true;
    } else if (!arg.startsWith("-") && !opts.input) {
      opts.input = arg;
    }
  }

  if (!opts.input) {
    console.error("Error: Input file or directory required");
    printHelp();
    return null;
  }

  return opts;
}

async function main() {
  const args = process.argv.slice(2);
  const opts = parseArgs(args);
  if (!opts) process.exit(1);

  const input = resolve(opts.input);
  if (!existsSync(input)) {
    console.error(`Error: ${input} not found`);
    process.exit(1);
  }

  const compressor = await detectCompressor(opts.format);
  const isDir = statSync(input).isDirectory();

  if (isDir) {
    const files = collectFiles(input, opts.recursive);
    if (files.length === 0) {
      console.error("No supported images found");
      process.exit(1);
    }

    const results: Result[] = [];
    for (const file of files) {
      try {
        const r = await processFile(compressor, file, { ...opts, output: undefined });
        results.push(r);
        if (!opts.json) {
          const reduction = Math.round((1 - r.ratio) * 100);
          console.log(`${r.input} → ${r.output} (${formatSize(r.inputSize)} → ${formatSize(r.outputSize)}, ${reduction}% reduction)`);
        }
      } catch (e) {
        if (!opts.json) console.error(`Error processing ${file}: ${(e as Error).message}`);
      }
    }

    if (opts.json) {
      const totalInput = results.reduce((s, r) => s + r.inputSize, 0);
      const totalOutput = results.reduce((s, r) => s + r.outputSize, 0);
      console.log(
        JSON.stringify({
          files: results,
          summary: {
            totalFiles: results.length,
            totalInputSize: totalInput,
            totalOutputSize: totalOutput,
            ratio: totalInput > 0 ? totalOutput / totalInput : 0,
            compressor,
          },
        }, null, 2)
      );
    } else {
      const totalInput = results.reduce((s, r) => s + r.inputSize, 0);
      const totalOutput = results.reduce((s, r) => s + r.outputSize, 0);
      const reduction = Math.round((1 - totalOutput / totalInput) * 100);
      console.log(`\nProcessed ${results.length} files: ${formatSize(totalInput)} → ${formatSize(totalOutput)} (${reduction}% reduction)`);
    }
  } else {
    try {
      const r = await processFile(compressor, input, opts);
      if (opts.json) {
        console.log(JSON.stringify(r, null, 2));
      } else {
        const reduction = Math.round((1 - r.ratio) * 100);
        console.log(`${r.input} → ${r.output} (${formatSize(r.inputSize)} → ${formatSize(r.outputSize)}, ${reduction}% reduction)`);
      }
    } catch (e) {
      console.error(`Error: ${(e as Error).message}`);
      process.exit(1);
    }
  }
}

main();
