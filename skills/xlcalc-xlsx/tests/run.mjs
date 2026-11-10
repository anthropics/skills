// node tests/run.mjs (from the skill directory) — needs python3 with openpyxl, and `npm install --prefix scripts`.
import { execFileSync, spawnSync } from 'node:child_process'
import { chmodSync, mkdtempSync, statSync, writeFileSync, copyFileSync } from 'node:fs'
import { tmpdir } from 'node:os'
import { dirname, join } from 'node:path'
import { fileURLToPath } from 'node:url'

const here = dirname(fileURLToPath(import.meta.url))
const XL = join(here, '..', 'scripts', 'xl.mjs')
const dir = mkdtempSync(join(tmpdir(), 'xl-skill-'))
execFileSync('python3', [join(here, 'fixtures.py'), dir])
const f = (name) => join(dir, name)

function xl(...args) {
  const r = spawnSync('node', [XL, ...args], { encoding: 'utf8' })
  let out
  try { out = JSON.parse(r.stdout) } catch { out = r.stdout }
  return { code: r.status, out }
}
const kinds = (rep) => rep.problems.map((p) => p.kind)
let failed = 0
function t(name, fn) {
  try { fn(); console.log(`ok   ${name}`) } catch (e) { failed++; console.log(`FAIL ${name}: ${e.message}`) }
}
function ok(cond, msg) { if (!cond) throw new Error(msg) }
function pyValues(file, cells) {
  return JSON.parse(execFileSync('python3', ['-c', `
import json,sys
from openpyxl import load_workbook
ws=load_workbook(sys.argv[1],data_only=True).active
print(json.dumps([ws[c].value for c in sys.argv[2:]]))`, file, ...cells], { encoding: 'utf8' }))
}

t('recalc: missing _xlfn. prefix is a problem, not success', () => {
  const { code, out } = xl('recalc', f('noprefix.xlsx'))
  ok(code === 2 && kinds(out).includes('noPrefix'), JSON.stringify(out.problems))
})
t('recalc: circular reference is a problem', () => {
  const { out } = xl('recalc', f('cycle.xlsx'))
  ok(kinds(out).includes('cycle'), JSON.stringify(out.problems))
})
t('check: format Excel refuses to open is a problem', () => {
  const { out } = xl('check', f('badformat.xlsx'))
  ok(out.problems.some((p) => p.kind === 'numberFormat' && p.format === '0 kg'), JSON.stringify(out.problems))
})
t('recalc: errors grouped by origin with reason', () => {
  const { out } = xl('recalc', f('errors.xlsx'))
  const e = out.problems.filter((p) => p.kind === 'error')
  ok(e.length === 1 && e[0].cell === 'S!B1' && e[0].dependents === 2 && /division by zero/.test(e[0].reason), JSON.stringify(e))
})
t('recalc: clean file is clean, values readable by openpyxl, mode kept', () => {
  chmodSync(f('clean.xlsx'), 0o600)
  const { code, out } = xl('recalc', f('clean.xlsx'))
  ok(code === 0 && out.status === 'clean' && out.written, JSON.stringify(out))
  ok(pyValues(f('clean.xlsx'), ['A3'])[0] === 3, 'A3 not stored')
  ok((statSync(f('clean.xlsx')).mode & 0o777) === 0o600, 'mode changed')
})
t('recalc: second run leaves the file alone', () => {
  const { out } = xl('recalc', f('clean.xlsx'))
  ok(out.written === false, JSON.stringify(out))
})
t('build: prefixes and spills written, values stored', () => {
  writeFileSync(f('spec.json'), JSON.stringify({ sheets: [{ name: 'S', cells: {
    A1: { value: 'North' }, A2: { value: 'South' }, A3: { value: 'North' },
    B1: { value: 120 }, B2: { value: 80 }, B3: { value: 45 },
    D1: { formula: 'UNIQUE(A1:A3)' }, E1: { formula: 'SUMIFS(B:B,A:A,D1#)' }, F1: { formula: 'XLOOKUP("South",A1:A3,B1:B3)' },
  } }] }))
  const { code, out } = xl('build', f('spec.json'), f('built.xlsx'))
  ok(code === 0, JSON.stringify(out))
  const xml = execFileSync('unzip', ['-p', f('built.xlsx'), 'xl/worksheets/sheet1.xml'], { encoding: 'utf8' })
  ok(xml.includes('_xlfn.XLOOKUP') && xml.includes('_xlfn.UNIQUE') && xml.includes('cm="1"'), 'prefix or spill metadata missing')
  ok(JSON.stringify(pyValues(f('built.xlsx'), ['E1', 'E2', 'F1'])) === '[165,80,80]', 'values')
})
t('build: refused number format stops the write', () => {
  writeFileSync(f('bad.json'), JSON.stringify({ sheets: [{ name: 'S', cells: { A1: { value: 1, numberFormat: '0 kg' } } }] }))
  const { code, out } = xl('build', f('bad.json'), f('bad.xlsx'))
  ok(code === 1 && out.problems?.[0]?.format === '0 kg', JSON.stringify(out))
})
t('edit: chart template from openpyxl filled by xlcalc keeps the chart and spills', () => {
  copyFileSync(f('template.xlsx'), f('filled.xlsx'))
  const edits = [['A2', 'North'], ['B2', 120], ['A3', 'South'], ['B3', 80], ['A4', 'North'], ['B4', 45]]
    .map(([cell, value]) => ({ sheet: 'S', cell, input: { value } }))
    .concat([{ sheet: 'S', cell: 'D2', input: { formula: 'UNIQUE(A2:A4)' } }])
  writeFileSync(f('ops.json'), JSON.stringify([{ op: 'setCells', edits }, { op: 'insertRows', sheet: 'S', row: 1 }]))
  const { code, out } = xl('edit', f('filled.xlsx'), f('ops.json'))
  ok(code === 0, JSON.stringify(out))
  const list = execFileSync('unzip', ['-l', f('filled.xlsx')], { encoding: 'utf8' })
  ok(list.includes('xl/charts/chart1.xml'), 'chart lost')
  const chart = execFileSync('unzip', ['-p', f('filled.xlsx'), 'xl/charts/chart1.xml'], { encoding: 'utf8' })
  ok(chart.includes('$B$3:$B$5'), 'chart series did not follow the inserted row')
  ok(JSON.stringify(pyValues(f('filled.xlsx'), ['D3', 'D4'])) === '["North","South"]', 'spill values')
})
t('edit: refused structure op writes nothing', () => {
  writeFileSync(f('ops2.json'), JSON.stringify([{ op: 'deleteSheet', sheet: 'S' }]))
  const { code, out } = xl('edit', f('clean.xlsx'), f('ops2.json'))
  ok(code === 1 && /last_sheet/.test(out.error), JSON.stringify(out))
})
t('edit: fill, AutoFit and insert in one ops list', () => {
  writeFileSync(f('ops3.json'), JSON.stringify([
    { op: 'fillCellText', sheet: 'S', range: 'G1:G3', text: '=B1*2' },
    { op: 'setLayout', edits: [{ sheet: 'S', columns: 'A', fit: true }] },
    { op: 'insertRows', sheet: 'S', row: 2 },
  ]))
  const { code, out } = xl('edit', f('built.xlsx'), f('ops3.json'), '--out', f('built2.xlsx'))
  ok(code === 0, JSON.stringify(out))
  ok(JSON.stringify(pyValues(f('built2.xlsx'), ['G1', 'G3', 'G4'])) === '[240,160,90]', 'filled values')
})
t('show: prints values', () => {
  const r = spawnSync('node', [XL, 'show', f('built.xlsx'), '--formulas'], { encoding: 'utf8' })
  ok(r.stdout.includes('E1=165') && r.stdout.includes("S!D1: =UNIQUE"), r.stdout)
})

console.log(failed ? `\n${failed} failed (files in ${dir})` : '\nall passed')
process.exit(failed ? 1 : 0)
