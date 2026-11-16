/* manage.mjs — 工厂台账管理：状态 / 标失败 / 记跑通 / 清旧包
 * 用法：
 *   node scripts/manage.mjs status
 *   node scripts/manage.mjs fail    --link X [--phenomenon "元素找不到"] [--http 401] [--exit 3] [--rows 0] [--rootcause …] [--fix …]
 *                                   # 不给 --rootcause 时按现象自动归因，并用人话告诉下一步、要不要重录
 *   node scripts/manage.mjs heal    [--link X] [--n 10]   # 看自愈记录：哪条链路的哪一步、靠哪级定位救回来的
 *   node scripts/manage.mjs pass    --link X            # 真跑通才许记
 *   node scripts/manage.mjs clean   [--days 7]          # 清超期产物（zip/recordings/evidence），台账与日志永远留
 *   node scripts/manage.mjs clean --all --yes           # 换机/转岗前清空全部产物（不可恢复，必须 --yes）
 *   node scripts/manage.mjs drop --rec recordings/x.rec.json --seq "3,4"   # 误点过滤：删掉这几步并重排序号（原文件改名留底）
 * 闭环规则：失败 ≥3 次 → 提示整条重录（record → analyze → 核对 → build），这就是"网页改版自动升级"的人工起点
 */
import path from 'node:path';
import fs from 'node:fs';
import { fileURLToPath } from 'node:url';
import { diagnose } from './lib-diagnose.mjs';

const ROOT = path.resolve(path.dirname(fileURLToPath(import.meta.url)), '..');
const LEDGER = path.join(ROOT, '台账.csv');
const arg = (k, d) => { const i = process.argv.indexOf('--' + k); return i >= 0 ? process.argv[i + 1] : d; };
const flag = (k) => process.argv.includes('--' + k);

function load() {
  if (!fs.existsSync(LEDGER)) return [['链路', '版本', '状态', '最后变动', 'zip', '失败次数', '备注']];
  return fs.readFileSync(LEDGER, 'utf8').replace(/^﻿/, '').split(/\r?\n/).filter(l => l.trim()).map(l => l.split(','));
}
function save(rows) {
  fs.writeFileSync(LEDGER, rows.map(r => r.join(',')).join('\r\n') + '\r\n', 'utf8');
}
function findRow(rows, link) {
  const i = rows.findIndex(r => r[0] === link);
  if (i < 0) { console.error(`台账里没有链路「${link}」（先跑 build_skill.mjs 生成）`); process.exit(1); }
  return i;
}

const cmd = process.argv[2];

/* 误点过滤：把录制里点错的那几步删掉，序号重排，原文件留 .bak（事后可查） */
if (cmd === 'drop') {
  const rec = arg('rec', '');
  const seqs = String(arg('seq', '')).split(',').map(s => Number(String(s).trim())).filter(n => n > 0);
  if (!rec || !seqs.length) {
    console.error('用法：node scripts/manage.mjs drop --rec recordings/x.rec.json --seq "3,4"');
    process.exit(2);
  }
  const file = path.isAbsolute(rec) ? rec : path.join(ROOT, rec);
  const data = JSON.parse(fs.readFileSync(file, 'utf8'));
  const before = (data.actions || []).length;
  const dropped = [];
  const src = data.actions || [];
  /* 被剔除的步如果写了备注，别把用户的规则一起删掉：挪到前面最近一个保留的步上 */
  const moved = [];
  src.forEach((a, i) => {
    const no = Number(a.seq || i + 1);
    if (!seqs.includes(no) || !a.note) return;
    for (let k = i - 1; k >= 0; k--) {
      const pv = src[k];
      if (seqs.includes(Number(pv.seq || k + 1))) continue;
      pv.note = (pv.note ? pv.note + '；' : '') + a.note;
      moved.push(`第${no}步的备注挪到第${Number(pv.seq || k + 1)}步`);
      return;
    }
  });
  const kept = src.filter((a, i) => {
    const no = Number(a.seq || i + 1);
    if (seqs.includes(no)) { dropped.push(`${no}.${a.type} ${a.text || a.label || ''}`.trim()); return false; }
    return true;
  });
  if (!dropped.length) { console.log(`这 ${seqs.join(',')} 步不存在（当前共 ${before} 步），文件没动`); process.exit(0); }
  kept.forEach((a, i) => { a.seq = i + 1; });
  data.actions = kept;
  data.meta = Object.assign({}, data.meta, { dropLog: [...((data.meta && data.meta.dropLog) || []), { at: new Date().toISOString(), dropped }] });
  fs.copyFileSync(file, file + '.bak');
  fs.writeFileSync(file, JSON.stringify(data, null, 1), 'utf8');
  console.log(`✓ 已剔除 ${dropped.length} 步（${before} → ${kept.length}），原文件留底：${path.basename(file)}.bak`);
  for (const d of dropped) console.log(`  - ${d}`);
  for (const m of moved) console.log(`  · ${m}`);
  process.exit(0);
}
const stamp = new Date(Date.now() - new Date().getTimezoneOffset() * 60000).toISOString().slice(0, 16).replace('T', ' ');

if (cmd === 'status') {
  const rows = load();
  console.log(rows.map(r => r.join(' | ')).join('\n'));
  const broken = rows.slice(1).filter(r => r[2] === 'broken');
  if (broken.length) console.log(`\n⚠ ${broken.length} 条 broken，处理顺序：重录(record.mjs) → 分析(analyze.py) → 核对 → 重新生成(build_skill.mjs)`);
  process.exit(0);
}

if (cmd === 'heal') {
  /* 自愈记录：run.mjs 每次靠降级定位救回一步就往这里写一行。
     用途：判「该不该标 broken」之前先看一眼——能被自愈救回来的，说明只是小改版，不必重录。 */
  const file = path.join(ROOT, 'logs', '自愈.log');
  if (!fs.existsSync(file)) { console.log('还没有自愈记录（要么没遇到过定位失效，要么还没跑过新版 run.mjs）'); process.exit(0); }
  const link = arg('link');
  const n = Number(arg('n', '10'));
  const rows = fs.readFileSync(file, 'utf8').split(/\r?\n/).filter(Boolean)
    .map(l => l.split('\t')).filter(c => !link || c[1] === link);
  if (!rows.length) { console.log(`没有属于「${link || '任何链路'}」的自愈记录`); process.exit(0); }
  console.log('时间\t链路\t步骤\t动作\t命中级别\t新定位');
  for (const c of rows.slice(-n)) console.log(c.join('\t'));
  const byLevel = {};
  for (const c of rows) byLevel[c[4]] = (byLevel[c[4]] || 0) + 1;
  console.log(`\n共 ${rows.length} 次自愈；按级别：` + Object.entries(byLevel).map(([k, v]) => `${k}=${v}`).join(' · '));
  console.log('看到 L4_text/L5_css 占比高 = 对方页面 id 在变，建议整条重录一次拿到更稳的定位。');
  process.exit(0);
}

if (cmd === 'fail') {
  const link = arg('link');
  const rows = load();
  const i = findRow(rows, link);
  rows[i][2] = 'broken';
  rows[i][3] = stamp;
  rows[i][5] = String(Number(rows[i][5] || 0) + 1);
  /* 根因能自动归就自动归（同一套规则见 lib-diagnose.mjs）；人给了就用人给的 */
  const d = diagnose({ err: arg('phenomenon', ''), http: arg('http', ''), exit: arg('exit', ''), rows: arg('rows'), link });
  const rootCause = arg('rootcause', '') || (d ? `${d.what}（${d.id}）` : '');
  rows[i][6] = [arg('phenomenon', ''), rootCause, arg('fix', '')].filter(Boolean).join('；').replace(/,/g, '，').slice(0, 200);
  save(rows);
  fs.mkdirSync(path.join(ROOT, 'logs'), { recursive: true });
  fs.appendFileSync(path.join(ROOT, 'logs', '失败台账.log'), `${stamp}\t${link}\t${arg('phenomenon', '')}\t${rootCause}\n`, 'utf8');
  console.log(`已记失败（第 ${rows[i][5]} 次）：${link}`);
  if (d) {
    console.log(`  人话：${d.human}`);
    console.log(`  下一步：${d.next}`);
    console.log(`  要不要重录：${d.redo}`);
  } else if (!arg('rootcause')) {
    console.log('  根因没认出来：补 --http/--exit/--phenomenon 再记一次，或手填 --rootcause');
  }
  if (Number(rows[i][5]) >= 3) console.log('≥3 次：这条链路该整条重录升级了——node scripts/record.mjs --url <入口> --name ' + link);
  const healFile = path.join(ROOT, 'logs', '自愈.log');
  if (fs.existsSync(healFile)) {
    const hs = fs.readFileSync(healFile, 'utf8').split(/\r?\n/).filter(Boolean).filter(l => l.split('\t')[1] === link);
    if (hs.length) console.log(`  自愈记录：这条链路累计 ${hs.length} 次靠降级定位救回（看明细：node scripts/manage.mjs heal --link ${link}）。先加 --heal 跑一次把定位库修好，再决定要不要重录。`);
  }
  process.exit(0);
}

if (cmd === 'pass') {
  const link = arg('link');
  const rows = load();
  const i = findRow(rows, link);
  rows[i][2] = 'verified';
  rows[i][3] = stamp;
  save(rows);
  console.log(`已记跑通：${link}（下次 build_skill 会升版本号）`);
  process.exit(0);
}

if (cmd === 'clean') {
  /* 清理产物：默认只清超期（-days，默认 7 天）；--all 清全部，必须再带 --yes
   * 清的范围：zip/（出包）、recordings/（录制）、evidence/（证据/截图）——这三处最可能带页面数据
   * 不清的：logs/（失败台账、自愈记录要留痕）、台账.csv（版本历史永远留）、配置/（人写的）
   */
  const days = Number(arg('days', '7'));
  const all = flag('all');
  if (all && !flag('yes')) {
    console.error('--all 会把 recordings/ evidence/ zip/ 全部删掉（可能含页面数据，删了不可恢复）。\n确认要清就加 --yes：node scripts/manage.mjs clean --all --yes');
    process.exit(4);
  }
  const cut = all ? Infinity : Date.now() - days * 86400000;
  const dirs = ['zip', 'recordings', 'evidence'];
  let removed = 0, bytes = 0;
  for (const d of dirs) {
    const dir = path.join(ROOT, d);
    if (!fs.existsSync(dir)) continue;
    for (const f of fs.readdirSync(dir)) {
      const p = path.join(dir, f);
      const st = fs.statSync(p);
      if (st.isFile() && st.mtimeMs < cut) {
        bytes += st.size; fs.unlinkSync(p); removed++;
        console.log(`删 ${d}/${f}（${all ? '全部' : '超过 ' + days + ' 天'}，${(st.size / 1024).toFixed(0)} KB）`);
      }
    }
  }
  console.log(removed ? `清理完成：删 ${removed} 个文件，释放 ${(bytes / 1048576).toFixed(1)} MB` : (all ? '没有可清的产物' : `没有超过 ${days} 天的产物`));
  console.log('logs/ 与 台账.csv 不动——失败留痕与版本历史要保留');
  process.exit(0);
}

console.error('用法：node scripts/manage.mjs status | fail --link X [--phenomenon …] | pass --link X | clean [--days 7] | clean --all --yes');
process.exit(1);
