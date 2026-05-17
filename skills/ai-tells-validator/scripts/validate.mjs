#!/usr/bin/env node
// CLI: validate stdin (or a file) against the AI-tells rule set. Pre-
// fetches the Wikipedia signs-of-AI-writing article so the catalog stays
// current. Exit code is 0 when clean, 1 when tells fire, 2 on infra fail.

import { readFileSync } from 'node:fs'
import { fetchWiki, describeFreshness } from '../lib/wikiFetch.mjs'
import { parseSignsArticle } from '../lib/wikiParser.mjs'
import { buildRules, findAiTells, summarizeRules, wordCount } from '../lib/validator.mjs'

const args = parseArgs(process.argv.slice(2))

if (args.help) {
  process.stdout.write(USAGE)
  process.exit(0)
}

main().catch((err) => {
  console.error(err.message ?? err)
  process.exit(2)
})

async function main() {
  // 1. Fetch the source. The skill description says "always prefetch" —
  //    that's the default; --cache-ok lets CI opt out.
  let text, meta
  try {
    ;({ text, meta } = await fetchWiki({
      source: args.source,
      fresh: args.fresh,
      cacheOk: args.cacheOk,
    }))
  } catch (err) {
    console.error(`[validate] could not fetch source catalog: ${err.message}`)
    process.exit(2)
  }
  const { words: wikiWords, phrases: wikiPhrases } = parseSignsArticle(text)

  // 2. Read input.
  const input = await readInput(args.file)
  if (!input) {
    console.error('[validate] no input — pass via stdin or --file <path>')
    process.exit(2)
  }

  // 3. Build rules + validate.
  const rules = buildRules({
    wikiWords,
    wikiPhrases,
    allow: args.allow,
    maxEmDashes: args.maxEmDashes,
  })
  const tells = findAiTells(input, rules)

  // 4. Emit JSON report.
  const report = {
    ok: tells.length === 0,
    tells,
    word_count: wordCount(input),
    source: {
      url: args.source ?? 'https://en.wikipedia.org/wiki/Wikipedia:Signs_of_AI_writing',
      freshness: describeFreshness(meta),
      rule_summary: summarizeRules(rules),
    },
  }
  process.stdout.write(JSON.stringify(report, null, 2) + '\n')
  process.exit(report.ok ? 0 : 1)
}

async function readInput(filePath) {
  if (filePath) {
    return readFileSync(filePath, 'utf-8')
  }
  // Read stdin to EOF.
  if (process.stdin.isTTY) return null
  const chunks = []
  for await (const chunk of process.stdin) chunks.push(chunk)
  return Buffer.concat(chunks).toString('utf-8').trim() ? Buffer.concat(chunks).toString('utf-8') : null
}

function parseArgs(argv) {
  const out = {
    fresh: false,
    cacheOk: false,
    source: undefined,
    file: undefined,
    allow: [],
    maxEmDashes: 1,
    help: false,
  }
  for (let i = 0; i < argv.length; i++) {
    const a = argv[i]
    switch (a) {
      case '--fresh': out.fresh = true; break
      case '--cache-ok': out.cacheOk = true; break
      case '--source': out.source = argv[++i]; break
      case '--file': out.file = argv[++i]; break
      case '--allow': out.allow = (argv[++i] ?? '').split(',').map((s) => s.trim()).filter(Boolean); break
      case '--max-em-dashes': out.maxEmDashes = Number(argv[++i]); break
      case '-h':
      case '--help': out.help = true; break
      default:
        if (a.startsWith('-')) {
          console.error(`[validate] unknown flag: ${a}`)
          process.exit(2)
        }
    }
  }
  return out
}

const USAGE = `ai-tells-validate — flag AI-sounding text against the live Wikipedia catalog.

Usage:
  ai-tells-validate [flags] < input.txt
  ai-tells-validate --file draft.md

Flags:
  --fresh                 Force refetch of the source catalog (default: 1h cache).
  --cache-ok              Use cached catalog only; skip network.
  --source <url>          Override source URL.
  --file <path>           Read input from a file instead of stdin.
  --allow <tag,tag,...>   Suppress specific tell tags.
  --max-em-dashes <n>     Cap em-dashes per message (default 1).
  -h, --help              Show this message.

Exit codes:
  0  Clean.
  1  Tells found.
  2  Infrastructure error (network, parse, etc).
`
