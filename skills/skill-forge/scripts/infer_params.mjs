/* infer_params.mjs — 一次录制就判出「哪些值是变量」（省一遍录制；两遍 diff 仍是最终口径）
 *
 * 用法：
 *   node scripts/infer_params.mjs --rec recordings/xxx.rec.json            # 只看结论
 *   node scripts/infer_params.mjs --rec ... --out 参数判定.csv             # 写成表，给人核对
 *   node scripts/infer_params.mjs --rec ... --json                         # 机器读
 *
 * 退出码：0 正常（有「待确认」也算正常，那是要人看的清单）/ 4 文件读不了
 */
import fs from 'node:fs';
import path from 'node:path';
import { fileURLToPath } from 'node:url';
import { inferRecording, toCsvText } from './lib-infer.mjs';

const ROOT = path.resolve(path.dirname(fileURLToPath(import.meta.url)), '..');
const arg = (k, d) => { const i = process.argv.indexOf('--' + k); return i >= 0 ? process.argv[i + 1] : d; };
const flag = k => process.argv.includes('--' + k);

const recFile = arg('rec');
if (!recFile) { console.error('用法：node scripts/infer_params.mjs --rec <录制.rec.json> [--out 参数判定.csv] [--json]'); process.exit(4); }
const full = path.isAbsolute(recFile) ? recFile : path.join(ROOT, recFile);
if (!fs.existsSync(full)) { console.error(`找不到录制文件：${full}`); process.exit(4); }

let rec;
try { rec = JSON.parse(fs.readFileSync(full, 'utf8')); }
catch (e) { console.error(`录制文件不是合法 JSON：${String(e.message || e)}`); process.exit(4); }

const { rows, summary } = inferRecording(rec);

if (flag('json')) {
  console.log(JSON.stringify({ file: path.basename(full), rows, summary }, null, 1));
  process.exit(0);
}

console.log(`录制：${path.basename(full)} · 填值步骤 ${summary.总填值步骤} 个`);
if (!rows.length) { console.log('没有填值步骤（纯点击/下载链路）——不存在变量判定问题。'); process.exit(0); }

console.log('\n步骤 | 字段 | 当次的值 | 判定 | 类型 | 置信度');
for (const r of rows) {
  console.log(`${r.步骤} | ${r.字段 || '(无标签)'} | ${r.当次的值} | ${r.判定} | ${r.类型} | ${r.置信度}`);
}
console.log('\n理由：');
for (const r of rows) console.log(`  第${r.步骤}步：${r.理由}`);

console.log(`\n小结：变量 ${summary.变量} · 常量 ${summary.常量} · 待确认 ${summary.待确认}`);
if (summary.要人看的.length) {
  console.log('要人看一眼的：');
  for (const s of summary.要人看的) console.log('  · ' + s);
}
console.log('\n口径提醒：这是「提示」，不是定论。最硬的判法是同一操作录两遍跑 diffrec（不一致=变量）。');

const out = arg('out');
if (out) {
  const p = path.isAbsolute(out) ? out : path.join(ROOT, out);
  fs.mkdirSync(path.dirname(p), { recursive: true });
  fs.writeFileSync(p, '\uFEFF' + toCsvText(rows), 'utf8');
  console.log(`已写：${p}`);
}
