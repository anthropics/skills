#!/usr/bin/env node
// CLI: rewrite stdin until the AI-tells validator passes. Shells out to
// `claude -p` with the freshest banned list in the system prompt and
// retries up to 3 times when findings remain. Cleaned text → stdout;
// rewrite report → stderr.

import { readFileSync } from 'node:fs'
import { spawn } from 'node:child_process'
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
  let wikiText, meta
  try {
    ;({ text: wikiText, meta } = await fetchWiki({
      source: args.source, fresh: args.fresh, cacheOk: args.cacheOk,
    }))
  } catch (err) {
    console.error(`[rewrite] could not fetch source catalog: ${err.message}`)
    process.exit(2)
  }
  const { words: wikiWords, phrases: wikiPhrases } = parseSignsArticle(wikiText)
  const rules = buildRules({
    wikiWords, wikiPhrases, allow: args.allow, maxEmDashes: args.maxEmDashes,
  })

  const original = await readInput(args.file)
  if (!original) {
    console.error('[rewrite] no input — pass via stdin or --file <path>')
    process.exit(2)
  }

  const reports = []
  let attempt = 0
  let current = original

  while (attempt < args.maxRetries + 1) {
    const tells = findAiTells(current, rules)
    if (tells.length === 0) {
      reports.push({ attempt, ok: true, tells: [], word_count: wordCount(current) })
      break
    }
    reports.push({ attempt, ok: false, tells, word_count: wordCount(current) })
    if (attempt === args.maxRetries) break

    // Send to Claude with the findings as feedback.
    const systemPrompt = buildSystemPrompt(rules)
    const userPrompt = buildUserPrompt({
      voice: args.voice,
      original: attempt === 0 ? original : current,
      previousFindings: tells,
    })
    try {
      current = await callClaudeRewrite(systemPrompt, userPrompt, args.model)
    } catch (err) {
      console.error(`[rewrite] claude call failed on attempt ${attempt + 1}: ${err.message}`)
      process.exit(2)
    }
    attempt += 1
  }

  // Final state — if we still have tells, we return original + exit 2.
  // Better to let the human see the offending draft than silently ship.
  const finalReport = reports[reports.length - 1]
  const finalText = finalReport?.ok ? current : original

  process.stdout.write(finalText.replace(/\n*$/, '\n'))

  process.stderr.write(JSON.stringify({
    ok: finalReport?.ok ?? false,
    attempts: reports.length,
    final_tells: finalReport?.tells ?? [],
    source: {
      url: args.source ?? 'https://en.wikipedia.org/wiki/Wikipedia:Signs_of_AI_writing',
      freshness: describeFreshness(meta),
      rule_summary: summarizeRules(rules),
    },
    history: reports.map((r) => ({ attempt: r.attempt, tells: r.tells.length })),
  }, null, 2) + '\n')

  process.exit(finalReport?.ok ? 0 : 2)
}

function buildSystemPrompt(rules) {
  // We don't dump every banned word into the prompt (the list is large
  // and most rules are obvious from the patterns). Give Claude the rules
  // it can derive everything else from, plus a few category exemplars.
  const sampleWords = [...rules.words].slice(0, 20).join(', ')
  return [
    'You are rewriting a draft to eliminate every "AI-sounding" tell from it. The reader is a senior operator who will reject the message if any single tell fires.',
    '',
    'Hard rules:',
    `  - Banned vocabulary (sample, full list enforced post-hoc by validator): ${sampleWords}, etc.`,
    '  - Banned phrases: "I hope this email finds you well", "circling back", "just checking in", "in conclusion", "it is important to note", "plays a vital/crucial/pivotal role", "in today\'s fast-paced ___", "value proposition", "best practices", "looking forward to hearing", and similar canned email tropes.',
    '  - Banned patterns:',
    '    - Negative parallelism: "Not just X, but Y" / "Not X, but Y". Never.',
    '    - Contracted siblings: "aren\'t X — they\'re Y" / "isn\'t X, it\'s Y". Never.',
    '    - Rule-of-three adjective lists ("clear, sourced, and trustworthy"). Never.',
    '    - Participle tails (", ensuring X" / ", driving Y" / ", reinforcing Z"). Never.',
    '    - "Whether you\'re X or Y…" / "Excited to ___". Never.',
    `    - Em-dashes: at most ${rules.maxEmDashes} per message.`,
    '    - Three-hyphen thematic breaks (---). Never in body copy.',
    '    - Smart/curly quotes: straight quotes only.',
    '',
    'Preserve the author\'s intent, voice (if specified), and core argument. Do not pad with new content. Do not editorialize. Output only the rewritten text.',
    '',
    'Do not include any preamble or explanation. Output the rewritten text and nothing else.',
  ].join('\n')
}

function buildUserPrompt({ voice, original, previousFindings }) {
  const lines = ['# Original draft', '', original, '']
  if (voice) lines.push('# Author voice / constraints', '', voice, '')
  if (previousFindings.length > 0) {
    lines.push('# Validator findings to eliminate')
    lines.push('')
    for (const f of previousFindings.slice(0, 16)) {
      lines.push(`  - ${f.tag}: ${f.quote}`)
    }
    lines.push('')
  }
  lines.push('# Task')
  lines.push('')
  lines.push('Rewrite the draft above so that every listed finding is gone. Keep the message length similar. Output only the rewritten text.')
  return lines.join('\n')
}

function callClaudeRewrite(systemPrompt, userText, model) {
  return new Promise((resolve, reject) => {
    const child = spawn('claude', [
      '-p',
      '--output-format', 'json',
      '--tools', '',
      '--no-session-persistence',
      '--disable-slash-commands',
      '--model', model,
      '--system-prompt', systemPrompt,
    ], { stdio: ['pipe', 'pipe', 'pipe'] })
    let stdout = ''
    let stderr = ''
    child.stdout.on('data', (d) => { stdout += d.toString() })
    child.stderr.on('data', (d) => { stderr += d.toString() })
    child.on('error', reject)
    child.on('close', (code) => {
      if (code !== 0) return reject(new Error(`claude exit ${code}: ${stderr.slice(0, 300)}`))
      try {
        const env = JSON.parse(stdout)
        if (env.is_error) return reject(new Error(`claude error: ${env.result?.slice(0, 200) ?? 'unknown'}`))
        resolve((env.result ?? '').trim())
      } catch (err) {
        reject(new Error(`parse envelope failed: ${err.message}`))
      }
    })
    child.stdin.write(userText)
    child.stdin.end()
  })
}

async function readInput(filePath) {
  if (filePath) return readFileSync(filePath, 'utf-8')
  if (process.stdin.isTTY) return null
  const chunks = []
  for await (const chunk of process.stdin) chunks.push(chunk)
  return Buffer.concat(chunks).toString('utf-8')
}

function parseArgs(argv) {
  const out = {
    fresh: false, cacheOk: false, source: undefined, file: undefined,
    allow: [], maxEmDashes: 1, maxRetries: 3, model: 'sonnet',
    voice: undefined, help: false,
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
      case '--max-retries': out.maxRetries = Number(argv[++i]); break
      case '--model': out.model = argv[++i]; break
      case '--voice': out.voice = argv[++i]; break
      case '-h':
      case '--help': out.help = true; break
      default:
        if (a.startsWith('-')) {
          console.error(`[rewrite] unknown flag: ${a}`)
          process.exit(2)
        }
    }
  }
  return out
}

const USAGE = `ai-tells-rewrite — rewrite a draft until it passes the validator.

Usage:
  ai-tells-rewrite [flags] < draft.txt > clean.txt
  ai-tells-rewrite --file draft.md > clean.md

Flags:
  --fresh                  Force refetch of the source catalog.
  --cache-ok               Use cached catalog only; skip network.
  --source <url>           Override source URL.
  --file <path>            Read input from a file.
  --allow <tag,tag,...>    Suppress specific tell tags.
  --max-em-dashes <n>      Cap em-dashes per message (default 1).
  --max-retries <n>        Retry attempts (default 3).
  --model <alias>          Claude model alias (default 'sonnet').
  --voice <constraint>     One-line voice / brand constraint for the rewrite.
  -h, --help               Show this message.

Output:
  stdout — the rewritten text (or original if rewrite failed).
  stderr — JSON report (attempts, tells eliminated, source freshness).

Exit codes:
  0  Clean rewrite shipped to stdout.
  1  (Not used; rewrite either succeeds or fails entirely.)
  2  Infrastructure error OR still failing after max retries.
`
