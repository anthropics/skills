#!/usr/bin/env node
// Build, edit, recalculate, check and show .xlsx workbooks with the xlcalc engine. See ../SKILL.md.
import { readFile } from 'node:fs/promises'
import { ensureLocale, Failure, loadEngine } from './lib/engine.mjs'
import { readInput, writeWorkbook } from './lib/io.mjs'
import { buildReport, findBadFormats, ref, usedRange } from './lib/report.mjs'

const USAGE = `usage:
  node xl.mjs build  <spec.json|spec.mjs> <out.xlsx>         new workbook from a BookInput spec
  node xl.mjs edit   <file.xlsx> <ops.json|ops.mjs> [--out f] change a workbook, keeping charts and everything else
  node xl.mjs recalc <file.xlsx> [--out f]                   store formula values (e.g. after openpyxl saved the file)
  node xl.mjs check  <file.xlsx>                             report problems, write nothing
  node xl.mjs show   <file.xlsx> [--sheet S] [--range A1:H40] [--formulas] [--json]
options: --clock 2026-01-31T00:00:00Z pins TODAY/NOW/RAND`

// Batched into one applyChanges call. setLayout runs on its own: AutoFit (`fit`) reads values the batch has not calculated yet.
const SESSION_OPS = new Set(['setCells', 'replaceCells', 'clearCells', 'patchCells', 'setNames', 'setStyles'])

function parseArgs(argv) {
  const flags = {}
  const pos = []
  for (let i = 0; i < argv.length; i++) {
    const a = argv[i]
    if (a === '--formulas' || a === '--json') flags[a.slice(2)] = true
    else if (a.startsWith('--')) {
      const [k, v] = a.includes('=') ? a.slice(2).split(/=(.*)/s) : [a.slice(2), argv[++i]]
      if (v === undefined) throw new Failure(`${a} needs a value`)
      flags[k] = v
    } else pos.push(a)
  }
  return { pos, flags }
}

function sessionOptions(flags, cached) {
  const opts = {}
  if (flags.clock) opts.clock = { now: flags.clock, seed: 1 }
  if (cached) Object.assign(opts, { cached, unknownFunctions: 'held' })
  return opts
}

function wrapInput(engine, fn) {
  try {
    return fn()
  } catch (e) {
    if (e instanceof engine.core.InputError) throw new Failure(`invalid workbook: ${e.message}`)
    throw e
  }
}

async function open(engine, file, flags) {
  let original
  try {
    original = await readFile(file)
  } catch (e) {
    throw new Failure(`could not read ${file}: ${e.message}`)
  }
  let read
  try {
    read = await engine.keep.openKept(original)
  } catch (e) {
    throw new Failure(`could not open ${file} as a workbook: ${e.message}`)
  }
  await ensureLocale(engine, read.book)
  const session = wrapInput(engine, () => engine.core.createSession(read.book, sessionOptions(flags, read.cached)))
  return { original, read, session }
}

async function writeOver(engine, original, snapshot, target) {
  let written
  try {
    written = await engine.keep.writeKept(original, snapshot, { writeValues: true, values: 'preserve' })
  } catch (e) {
    if (e instanceof engine.keep.KeptRefusal) throw new Failure(`writeKept refused (${e.code}): ${e.message}`, { refusal: e.code })
    if (e instanceof engine.core.InputError) throw new Failure(`could not write: ${e.message}`)
    throw e
  }
  const unchanged = written.data === original || Buffer.compare(Buffer.from(written.data), original) === 0
  if (!unchanged) await writeWorkbook(target, written.data)
  return { issues: written.issues, unchanged }
}

function applyOps(session, ops) {
  if (!Array.isArray(ops)) throw new Failure('ops must be an array (or a module exporting a function of the session)')
  let batch = []
  const flush = () => {
    if (batch.length) session.applyChanges(batch)
    batch = []
  }
  ops.forEach((op, i) => {
    if (SESSION_OPS.has(op.op)) return void batch.push(op)
    flush()
    let r
    if (op.op === 'setLayout') r = session.setLayout(op.edits)
    else if (op.op === 'setCellText') r = session.setCellText(op.sheet, op.cell, op.text)
    else if (op.op === 'setCellTexts') r = session.setCellTexts(op.entries)
    else if (op.op === 'fillCellText') r = session.fillCellText(op.sheet, op.range, op.text)
    else if (op.op === 'pasteText') r = session.pasteText(op.sheet, op.cell, op.text)
    else r = session.editStructure(op)
    if (r && r.ok === false) throw new Failure(`op #${i} (${op.op}) refused: ${r.code}${r.message ? `: ${r.message}` : ''}`, { op })
  })
  flush()
}

async function build(engine, [specPath, out], flags) {
  if (!specPath || !out) throw new Failure(USAGE)
  const book = await readInput(specPath, { engine: engine.core })
  await ensureLocale(engine, book)
  const bad = findBadFormats(engine, book)
  if (bad.length) throw new Failure('number formats Excel would refuse to open; nothing written', { problems: bad })
  const session = wrapInput(engine, () => engine.core.createSession(book, sessionOptions(flags)))
  const { data, issues } = await engine.xlsx.writeXlsx(session.getSnapshot(), { values: 'preserve' })
  await writeWorkbook(out, data)
  return buildReport(engine, { action: 'build', file: out, written: true, session, book: session.getBook(), writeIssues: issues })
}

async function edit(engine, [file, opsPath], flags) {
  if (!file || !opsPath) throw new Failure(USAGE)
  const { original, read, session } = await open(engine, file, flags)
  const ops = await readInput(opsPath, session, engine.core)
  if (ops !== undefined) wrapInput(engine, () => applyOps(session, ops))
  const target = flags.out || file
  const w = await writeOver(engine, original, session.getSnapshot(), target)
  return buildReport(engine, { action: 'edit', file: target, written: !w.unchanged, session, book: session.getBook(), readIssues: read.issues, writeIssues: w.issues })
}

async function recalc(engine, [file], flags) {
  if (!file) throw new Failure(USAGE)
  const { original, read, session } = await open(engine, file, flags)
  const target = flags.out || file
  const w = await writeOver(engine, original, session.getSnapshot(), target)
  return buildReport(engine, { action: 'recalc', file: target, written: !w.unchanged, session, book: session.getBook(), readIssues: read.issues, writeIssues: w.issues })
}

async function check(engine, [file], flags) {
  if (!file) throw new Failure(USAGE)
  const { read, session } = await open(engine, file, flags)
  return buildReport(engine, { action: 'check', file, written: false, session, book: session.getBook(), readIssues: read.issues, cached: read.cached })
}

function clip(text, n) {
  const s = String(text ?? '').replace(/\s+/g, ' ')
  return s.length > n ? `${s.slice(0, n - 1)}…` : s
}

async function show(engine, [file], flags) {
  if (!file) throw new Failure(USAGE)
  const { session } = await open(engine, file, flags)
  const names = flags.sheet ? [flags.sheet] : session.getBook().sheets.map((s) => s.name)
  const out = []
  const json = {}
  for (const name of names) {
    const used = usedRange(session, name)
    let range = flags.range
    if (!range && used) {
      const [, col, row] = used.match(/:([A-Z]+)(\d+)$/)
      const lastCol = col.length > 1 || col > 'L' ? 'L' : col
      range = `A1:${lastCol}${Math.min(Number(row), 40)}`
    }
    out.push(`== ${name}  used ${used || '(empty)'}${range && range !== used ? `  showing ${range}` : ''}`)
    if (!range) continue
    const cells = session.getCells(name, range)
    json[name] = cells
    const rows = new Map()
    for (const [addr, c] of Object.entries(cells)) {
      const [, col, row] = addr.match(/^([A-Z]+)(\d+)$/)
      if (!rows.has(+row)) rows.set(+row, [])
      const shown = c.text !== undefined ? c.text : c.value && typeof c.value === 'object' ? engine.core.errorText(c.value.error) : c.value
      rows.get(+row).push(`${addr}=${clip(shown, 24)}`)
    }
    for (const [, line] of [...rows].sort((a, b) => a[0] - b[0])) out.push('  ' + line.join(' | '))
    if (flags.formulas) {
      for (const [addr, c] of Object.entries(cells)) {
        if (c.formula !== undefined) out.push(`  ${ref(name, addr)}: =${c.formula}${c.spill ? `  (spills ${c.spill})` : ''}`)
      }
    }
  }
  if (flags.json) return json
  return out.join('\n')
}

const COMMANDS = { build, edit, recalc, check, show }

async function main() {
  const [cmd, ...rest] = process.argv.slice(2)
  if (!COMMANDS[cmd]) {
    console.error(USAGE)
    process.exit(1)
  }
  const { pos, flags } = parseArgs(rest)
  const engine = await loadEngine()
  const result = await COMMANDS[cmd](engine, pos, flags)
  if (typeof result === 'string') {
    console.log(result)
    return
  }
  console.log(JSON.stringify(result, null, 2))
  if (result && result.status === 'problems') process.exitCode = 2
}

main().catch((e) => {
  if (e instanceof Failure) {
    console.log(JSON.stringify({ error: e.message, ...e.extra }, null, 2))
    process.exit(e.exitCode)
  }
  console.log(JSON.stringify({ error: `unexpected: ${e.stack || e.message}` }, null, 2))
  process.exit(1)
})
