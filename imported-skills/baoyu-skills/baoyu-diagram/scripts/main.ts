#!/usr/bin/env bun
import { existsSync, readFileSync, mkdirSync } from "fs";
import { basename, dirname, extname, join, resolve } from "path";

interface Options {
  input: string;
  output?: string;
  scale: number;
  json: boolean;
}

function parseViewBox(svg: string): { width: number; height: number } | null {
  const vb = svg.match(/viewBox\s*=\s*"([^"]+)"/);
  if (vb) {
    const parts = vb[1].split(/[\s,]+/).map(Number);
    if (parts.length >= 4 && parts[2] > 0 && parts[3] > 0) return { width: parts[2], height: parts[3] };
  }
  const w = svg.match(/\bwidth\s*=\s*"(\d+(?:\.\d+)?)"/);
  const h = svg.match(/\bheight\s*=\s*"(\d+(?:\.\d+)?)"/);
  if (w && h) return { width: Number(w[1]), height: Number(h[1]) };
  return null;
}

function getOutputPath(input: string, scale: number, custom?: string): string {
  if (custom) return resolve(custom);
  const dir = dirname(input);
  const base = basename(input, extname(input));
  const suffix = scale === 1 ? "" : `@${scale}x`;
  return join(dir, `${base}${suffix}.png`);
}

async function convert(input: string, opts: Options): Promise<{ output: string; width: number; height: number }> {
  const svg = readFileSync(input);
  const svgStr = svg.toString("utf-8");
  const dims = parseViewBox(svgStr);
  if (!dims) throw new Error("Cannot determine SVG dimensions from viewBox or width/height attributes");

  const width = Math.round(dims.width * opts.scale);
  const height = Math.round(dims.height * opts.scale);

  const sharp = (await import("sharp")).default;
  const output = getOutputPath(input, opts.scale, opts.output);
  mkdirSync(dirname(output), { recursive: true });

  await sharp(svg, { density: 72 * opts.scale })
    .resize(width, height)
    .png()
    .toFile(output);

  return { output, width, height };
}

function printHelp() {
  console.log(`Usage: bun main.ts <input.svg> [options]

Convert SVG to @2x PNG.

Options:
  -o, --output <path>   Output path (default: <input>@2x.png)
  -s, --scale <n>       Scale factor (default: 2)
      --json            JSON output
  -h, --help            Show help`);
}

function parseArgs(args: string[]): Options | null {
  const opts: Options = { input: "", scale: 2, json: false };
  for (let i = 0; i < args.length; i++) {
    const arg = args[i];
    if (arg === "-h" || arg === "--help") { printHelp(); process.exit(0); }
    else if (arg === "-o" || arg === "--output") opts.output = args[++i];
    else if (arg === "-s" || arg === "--scale") {
      const s = Number(args[++i]);
      if (isNaN(s) || s <= 0) { console.error(`Invalid scale: ${args[i]}`); return null; }
      opts.scale = s;
    } else if (arg === "--json") opts.json = true;
    else if (!arg.startsWith("-") && !opts.input) opts.input = arg;
  }
  if (!opts.input) { console.error("Error: Input SVG file required"); printHelp(); return null; }
  return opts;
}

async function main() {
  const opts = parseArgs(process.argv.slice(2));
  if (!opts) process.exit(1);

  const input = resolve(opts.input);
  if (!existsSync(input)) { console.error(`Error: ${input} not found`); process.exit(1); }
  if (extname(input).toLowerCase() !== ".svg") { console.error("Error: Input must be an SVG file"); process.exit(1); }

  try {
    const r = await convert(input, opts);
    if (opts.json) console.log(JSON.stringify({ input, ...r }, null, 2));
    else console.log(`${input} → ${r.output} (${r.width}×${r.height})`);
  } catch (e) {
    console.error(`Error: ${(e as Error).message}`);
    process.exit(1);
  }
}

main();
