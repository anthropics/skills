#!/usr/bin/env bun
import path from "node:path"
import process from "node:process"
import { runChunkCli } from "./chunk.js"

function formatScriptCommand(fallback: string): string {
  const raw = process.argv[1]
  const displayPath = raw
    ? (() => {
        const relative = path.relative(process.cwd(), raw)
        return relative && !relative.startsWith("..") ? relative : raw
      })()
    : fallback

  const quotedPath = displayPath.includes(" ")
    ? `"${displayPath.replace(/"/g, '\\"')}"`
    : displayPath

  return `npx -y bun ${quotedPath}`
}

function printUsage(exitCode: number): never {
  const cmd = formatScriptCommand("scripts/main.ts")
  console.log(`Baoyu Translate CLI

Usage:
  ${cmd} <file> [--max-words 5000] [--output-dir <dir>]
  ${cmd} chunk <file> [--max-words 5000] [--output-dir <dir>]

Commands:
  chunk              Split markdown into chunks

Options:
  --max-words <n>    Maximum words per chunk (default: 5000)
  --output-dir <dir> Write chunks into <dir>/chunks/
  -h, --help         Show help
`)
  process.exit(exitCode)
}

const args = process.argv.slice(2)

if (args.length === 0) {
  printUsage(1)
}

if (args[0] === "-h" || args[0] === "--help") {
  printUsage(0)
}

if (args[0] === "chunk") {
  process.exit(runChunkCli(args.slice(1), `${formatScriptCommand("scripts/main.ts")} chunk`))
}

process.exit(runChunkCli(args, formatScriptCommand("scripts/main.ts")))
