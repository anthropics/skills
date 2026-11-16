const LIST = 30

export function ref(sheet, cell) {
  const name = /^[A-Za-z_][A-Za-z0-9_.]*$/.test(sheet) ? sheet : `'${sheet.replace(/'/g, "''")}'`
  return `${name}!${cell}`
}

function capped(list) {
  return list.length > LIST ? { cells: list.slice(0, LIST), more: list.length - LIST } : { cells: list }
}

function columnName(n) {
  let s = ''
  for (; n > 0; n = Math.floor((n - 1) / 26)) s = String.fromCharCode(65 + ((n - 1) % 26)) + s
  return s
}

export function usedRange(session, sheet) {
  const { rows, columns } = session.getUsedRange(sheet)
  return rows && columns ? `A1:${columnName(columns)}${rows}` : null
}

// What Excel would show differently from what the engine computed, or would refuse: these block a clean status.
const READ_PROBLEMS = {
  noPrefix: 'stored without its _xlfn. prefix: Excel shows #NAME? (FILTER and SORT: Excel does not open the file). Re-entering the same text through `edit` does not help (the file\'s formula is kept); fix the source: write the formula with xlcalc, or in openpyxl as "=_xlfn.XLOOKUP(...)" (FILTER and SORT take "_xlfn._xlws."), then recalc.',
  userFunction: 'a macro or add-in function: the engine cannot calculate it, and Excel needs that add-in.',
  formula: 'a formula the engine cannot parse; Excel probably cannot either.',
  externalLink: 'a reference to another workbook the file has no stored values for.',
  part: 'a damaged or missing part of the file.',
}
const WRITE_PROBLEMS = {
  formula: 'a formula the writer could not store as a formula (Excel would refuse it); its value was written instead.',
  textLength: 'text over Excel\'s 32,767 characters, truncated.',
  noCachedValues: 'formulas written without a value: the engine could not answer them.',
}

function badFormats(book, formatRefused) {
  const found = new Map()
  const check = (fmt, where) => {
    if (typeof fmt !== 'string' || !formatRefused(fmt)) return
    if (!found.has(fmt)) found.set(fmt, [])
    found.get(fmt).push(where)
  }
  for (const sheet of book.sheets) {
    for (const [cell, c] of Object.entries(sheet.cells || {})) check(c.numberFormat, ref(sheet.name, cell))
    for (const look of sheet.looks || []) check(look.numberFormat, ref(sheet.name, look.range))
    for (const [col, c] of Object.entries(sheet.columns || {})) check(c.numberFormat, `${sheet.name} column ${col}`)
    for (const [row, r] of Object.entries(sheet.rows || {})) check(r.numberFormat, `${sheet.name} row ${row}`)
    for (const rule of sheet.conditionalFormats || []) check(rule.style?.numberFormat, `${sheet.name} conditional format ${rule.ranges?.join(' ')}`)
  }
  return [...found].map(([format, where]) => ({
    kind: 'numberFormat',
    format,
    note: 'Excel does not open a file with this format code; put literal text in quotes (0 "kg").',
    ...capped(where),
  }))
}

export function findBadFormats(engine, book) {
  return badFormats(book, engine.core.formatRefused)
}

function groupIssues(issues, table) {
  const problems = []
  const notes = new Map()
  for (const issue of issues || []) {
    const where = issue.sheet ? (issue.cells || []).map((c) => ref(issue.sheet, c)) : []
    if (table[issue.code]) {
      problems.push({ kind: issue.code, ...(issue.fn ? { fn: issue.fn } : {}), note: table[issue.code], ...(where.length ? capped(where) : {}), detail: issue.message })
      continue
    }
    const n = notes.get(issue.code) || { code: issue.code, count: 0, message: issue.message, sheets: new Set() }
    n.count++
    if (issue.sheet) n.sheets.add(issue.sheet)
    notes.set(issue.code, n)
  }
  return { problems, notes: [...notes.values()].map((n) => ({ code: n.code, count: n.count, message: n.message, ...(n.sheets.size ? { sheets: [...n.sheets] } : {}) })) }
}

function errorProblems(engine, session) {
  const { diagnostics } = session.getResult()
  const problems = []
  const origins = new Map()
  const cycles = []
  const held = []
  for (const d of diagnostics) {
    if (d.kind === 'name') {
      problems.push({ kind: 'name', name: d.name, ...(d.scope ? { scope: d.scope } : {}), reason: d.reason, dropped: d.dropped })
      continue
    }
    const here = ref(d.sheet, d.cell)
    if (d.error === 'CYCLE') {
      cycles.push(here)
      continue
    }
    if (d.fromFile) {
      held.push(here)
      continue
    }
    const issue = session.getCellIssue(d.sheet, d.cell)
    const o = issue?.origin || d
    const key = ref(o.sheet, o.cell)
    if (!origins.has(key)) origins.set(key, { dependents: [] })
    const entry = origins.get(key)
    if (key === here) Object.assign(entry, { error: engine.core.errorText(d.error), reason: d.reason, ...(d.fn ? { fn: d.fn } : {}), ...(d.check ? { check: d.check } : {}) })
    else entry.dependents.push(here)
  }
  for (const [cell, e] of origins) {
    const dep = capped(e.dependents)
    problems.push({ kind: 'error', cell, error: e.error, reason: e.reason, ...(e.fn ? { fn: e.fn } : {}), ...(e.check ? { check: e.check } : {}), dependents: e.dependents.length, ...(e.dependents.length ? { dependent_cells: dep.cells } : {}) })
  }
  if (cycles.length) problems.push({ kind: 'cycle', note: 'circular reference: these formulas are not calculated and keep their old value (0 for new ones). Break the cycle, or set the workbook\'s `iteration` if it is intended.', ...capped(cycles) })
  if (held.length) problems.push({ kind: 'notCalculated', note: 'functions the engine does not know: the cells keep the value stored in the file, and Excel recalculates them on open.', ...capped(held) })
  return problems
}

function staleValues(engine, session, cached) {
  if (!cached) return null
  const result = session.getResult()
  const differ = []
  cached.sheets.forEach((sheet, i) => {
    for (const [cell, c] of Object.entries(sheet.cells)) {
      const now = result.sheets[i]?.cells[cell]
      if (now && c.value !== undefined && c.value !== null && !engine.core.sameValue(c.value, now.value)) differ.push(ref(sheet.name, cell))
    }
  })
  return differ.length ? { code: 'staleValues', count: differ.length, message: 'formula values stored in the file differ from the engine\'s: the file was saved before its inputs changed, or the engine differs from Excel here', ...capped(differ) } : null
}

export function buildReport(engine, { action, file, written, session, book, readIssues, writeIssues, cached, extraProblems = [], extraNotes = [] }) {
  const read = groupIssues(readIssues, READ_PROBLEMS)
  const write = groupIssues(writeIssues, WRITE_PROBLEMS)
  const problems = [...extraProblems, ...errorProblems(engine, session), ...findBadFormats(engine, book), ...read.problems, ...write.problems]
  const notes = [...extraNotes, ...read.notes, ...write.notes]
  if (book.externalBooks?.length) {
    notes.push({ code: 'externalBooks', count: book.externalBooks.length, message: 'formulas read other workbooks: calculated from the values stored in this file, as Excel does without updating links (criteria functions such as SUMIF over a link give #VALUE!, as in Excel)' })
  }
  const stale = action === 'check' ? staleValues(engine, session, cached) : null
  if (stale) notes.push(stale)
  const sheets = session.getBook().sheets.map((s) => ({
    name: s.name,
    used: usedRange(session, s.name),
    formulas: Object.values(s.cells).filter((c) => c.formula !== undefined).length,
    ...(s.hidden ? { hidden: s.hidden } : {}),
  }))
  return {
    status: problems.length ? 'problems' : 'clean',
    action,
    file,
    written,
    xlcalc: engine.version,
    formulas: sheets.reduce((n, s) => n + s.formulas, 0),
    sheets,
    problems,
    notes,
  }
}
