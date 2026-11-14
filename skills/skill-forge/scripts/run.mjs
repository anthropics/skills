/* run.mjs — 链路执行器（工厂自用；build_skill.mjs 会把同一份复制进子技能包）
 * 一轮 = 回放定位库（导航/点击/填值）→ 等下载 → 按映射字典组装 TSV → 贴进路由表指定的在线表格 → 回读复核
 * 用法：
 *   node run.mjs --config <链路配置目录> [--source 新导出文件] [--route 某账户] [--dry] [--mode bg|watch] [--heal]
 * 退出码：0 全过 / 2 复核不过 / 3 浏览器或页面失败 / 4 配置缺东西
 * 定位失效时自动逐级降级重试（L1→L6）：命中哪级就报哪级；加 --heal 才把新定位回写 定位库.csv
 * 安检三条（不可退让）：
 *   1. 贴之前必须 --dry 或人工看过一次预览（真贴要 --go）
 *   2. 唯一键列在源表里必须无重复，有重复整轮停
 *   3. 贴完回读，键值在目标页找得到的行数 == 源行数，少一行都算失败
 */
import path from 'node:path';
import fs from 'node:fs';
import { fileURLToPath } from 'node:url';
import { ensureChrome, Cdp, watchDownloads, sleep } from './lib-cdp.mjs';
import { readTable, toNum } from './lib-tableread.mjs';
import { levelCandidates, attemptJs, firstHit, healRecord, healLogLine, applyHeal, csvCell } from './lib-heal.mjs';

const ROOT = path.resolve(path.dirname(fileURLToPath(import.meta.url)), '..');
const arg = (k, d) => { const i = process.argv.indexOf('--' + k); return i >= 0 ? process.argv[i + 1] : d; };
const flag = k => process.argv.includes('--' + k);

function parseCsvLine(line) {
  const out = [];
  let cur = '', inQ = false;
  for (let i = 0; i < line.length; i++) {
    const c = line[i];
    if (inQ) {
      if (c === '"' && line[i + 1] === '"') { cur += '"'; i++; }
      else if (c === '"') inQ = false;
      else cur += c;
    } else if (c === '"') inQ = true;
    else if (c === ',') { out.push(cur); cur = ''; }
    else cur += c;
  }
  out.push(cur);
  return out.map(s => s.trim());
}

function loadCsv(file) {
  if (!fs.existsSync(file)) return [];
  const lines = fs.readFileSync(file, 'utf8').replace(/^﻿/, '').split(/\r?\n/).filter(l => l.trim() && !l.startsWith('#'));
  if (!lines.length) return [];
  const header = parseCsvLine(lines[0]);
  return lines.slice(1).map(l => { const c = parseCsvLine(l); const r = {}; header.forEach((h, i) => r[h] = c[i] ?? ''); return r; });
}

console.error('自检：数据归属=自己的后台｜权限=账号内可见｜频率=人工级（一次一请求）｜平台协议=你确认过吗（不确定就先问，别默认可以）');
const configDir = arg('config');
if (!configDir) { console.error('用法：node run.mjs --config <链路配置目录> [--source 文件] [--dry|--go] [--route 账户]'); process.exit(4); }
const DRY = !flag('go'); // 默认预览，真跑必须带 --go（安检第 1 条）

const mappings = loadCsv(path.join(configDir, '映射字典.csv')).filter(m => m['状态'] === '已确认');
const keyCols = (loadCsv(path.join(configDir, '唯一键.csv'))[0]?.['列名'] || '').split(',').map(s => s.trim()).filter(Boolean);
const routes = loadCsv(path.join(configDir, '路由表.csv')).filter(r => r['启用'] !== '否');
const steps = loadCsv(path.join(configDir, '定位库.csv'));
if (!mappings.length || !keyCols.length) { console.error('配置没就绪：映射字典（已确认行）和唯一键都不能为空'); process.exit(4); }
if (!steps.length) { console.error('配置缺 定位库.csv（录制生成的步骤定位）'); process.exit(4); }

const routeFilter = arg('route');
const activeRoutes = routeFilter ? routes.filter(r => r['账户'] === routeFilter) : routes;
if (!activeRoutes.length && !DRY) { console.error('路由表里没有可用的行（--route 过滤后为空）'); process.exit(4); }

/* ---- 源表：--source 给文件；链路自己会下载时，真跑（--go）用刚下的文件当源 ---- */
let sourcePath = arg('source');
const selfDownload = steps.some(s => s['动作'] === 'download');
if (!sourcePath && !selfDownload) {
  console.error('缺 --source：本轮要贴的导出表路径（或链路里得有 download 步，真跑时自动用下载的文件）');
  process.exit(4);
}
function loadSource(p) {
  let t;
  try { t = readTable(p); } catch (e) { console.error(String(e.message || e)); process.exit(4); }
  const seen = new Set(), dups = []; // 安检第 2 条：唯一键无重复
  for (const r of t.rows) {
    const k = keyCols.map(c => r[c]).join('|');
    if (seen.has(k)) dups.push(k); else seen.add(k);
  }
  if (dups.length) { console.error(`唯一键重复 ${dups.length} 条（如 ${dups[0]}）——源表不对，整轮停`); process.exit(2); }
  return t;
}
let table = sourcePath ? loadSource(sourcePath) : null;

/* ---- 组装粘贴块：按映射字典逐列取值/算值 ---- */
function computeCell(row, m) {
  if (m['依据'] === '公式' && m['公式/分列规则']) {
    const fm = m['公式/分列规则'].match(/^\(?([^÷×+\−]+?)\s*÷\s*([^)×]+?)\)?(?:\s*×\s*100)?$/);
    if (fm) {
      const a = toNum(row[fm[1].trim()]), b = toNum(row[fm[2].trim()]);
      if (a === null || b === null || b === 0) return '';
      const v = a / b * (m['公式/分列规则'].includes('× 100') ? 100 : 1);
      return String(Math.round(v * 100) / 100);
    }
    const am = m['公式/分列规则'].match(/^([^×]+?)\s*×\s*(.+)$/);
    if (am) { const a = toNum(row[am[1].trim()]), b = toNum(row[am[2].trim()]); return a === null || b === null ? '' : String(Math.round(a * b * 100) / 100); }
  }
  if (m['依据'] === '分列' && m['公式/分列规则']) {
    const sm = m['公式/分列规则'].match(/按"(.)"分列取第(1|2|末)段/);
    if (sm) {
      const segs = String(row[m['源列']] ?? '').split(sm[1]).filter(s => s.trim() !== '');
      const idx = sm[2] === '末' ? segs.length - 1 : Number(sm[2]) - 1;
      return (segs[idx] ?? '').trim();
    }
  }
  return String(row[m['源列']] ?? '');
}
function buildPaste(t) {
  const rows = t.rows.map(r => mappings.map(m => computeCell(r, m)));
  return { rows, tsv: rows.map(r => r.join('\t')).join('\n') };
}

if (DRY) {
  if (!table) { console.error('预览要 --source：自动下载只在真跑（--go）发生，预览先用手头的导出表对一眼映射'); process.exit(4); }
  const { rows: pasteRows } = buildPaste(table);
  console.log(`源表：${table.name} · ${table.rows.length} 行 × ${mappings.length} 列 · 唯一键=${keyCols.join('+')}`);
  console.log(`映射（已确认 ${mappings.length} 条）：`);
  for (const m of mappings) console.log(`  ${m['源列']} → ${m['目标表格']} / ${m['目标列']} ${m['依据'] === '公式' || m['依据'] === '分列' ? '（' + m['公式/分列规则'] + '）' : ''}`);
  console.log('\n—— 预览（前 5 行）——');
  console.log(mappings.map(m => m['目标列']).join('\t'));
  pasteRows.slice(0, 5).forEach(r => console.log(r.join('\t')));
  console.log(`\n[预览模式] 没动浏览器、没贴任何东西。确认无误后加 --go 真跑。`);
  process.exit(0);
}

/* ---- 真跑：回放 → 下载 → 粘贴 → 回读 ---- */
const port = Number(arg('port', '18801'));
const mode = arg('mode', 'bg');
let cdp;
try {
  await ensureChrome({ port, mode });
  const entryUrl = steps[0]['页面'];
  cdp = await Cdp.attach({ port, url: entryUrl });
  await cdp.enableSession();
} catch (e) {
  console.error(`[浏览器失败] ${String(e.message || e)}\n→ 检查 Chrome 是否装了/端口 ${port} 是否被占（可 --port 换）`);
  process.exit(3);
}
const dl = watchDownloads(cdp, path.join(ROOT, 'downloads', String(Date.now())));
await cdp.send('Page.navigate', { url: steps[0]['页面'] });
await sleep(4000);
await cdp.injectFile(path.join(ROOT, 'assets', 'act.js'));

let failedStep = '';
const HEAL = flag('heal');                       // 只报告不动库；给 --heal 才回写定位库
const linkName = path.basename(configDir);
const stamp = () => new Date(Date.now() - new Date().getTimezoneOffset() * 60000).toISOString().slice(0, 19).replace('T', ' ');
let healed = 0;
for (const s of steps) {
  const act = s['动作'];
  if (act === 'nav' || !s['best定位']) continue;
  const cands = levelCandidates(s);
  const { hit, result, misses, tried } = await firstHit(cands, c =>
    cdp.evalJs(attemptJs(c.sel, act, s['值']), { awaitPromise: false }).catch(e => ({ found: false, err: String(e) })));
  if (!hit) {
    failedStep = `找不到：${s['标签'] || s['best定位']}（这条定位的 ${tried} 级全试过：${misses.join(' / ')}）`;
    break;
  }
  if (hit.index > 0) {
    healed++;
    const rec = healRecord(linkName, s, hit, stamp());
    fs.mkdirSync(path.join(ROOT, 'logs'), { recursive: true });
    fs.appendFileSync(path.join(ROOT, 'logs', '自愈.log'), healLogLine(rec) + '\n', 'utf8');
    let tail = '（只报告：加 --heal 才回写定位库）';
    if (HEAL) {
      const libFile = path.join(configDir, '定位库.csv');
      try {
        const { text, changed } = applyHeal(fs.readFileSync(libFile, 'utf8'), s, hit.sel);
        if (changed) {
          fs.writeFileSync(libFile, text, 'utf8');
          const recFile = path.join(configDir, '自愈记录.csv');
          if (!fs.existsSync(recFile)) fs.writeFileSync(recFile, Object.keys(rec).join(',') + '\r\n', 'utf8');
          fs.appendFileSync(recFile, Object.values(rec).map(csvCell).join(',') + '\r\n', 'utf8');
          s['best定位'] = hit.sel;
          tail = `已回写定位库（改 ${changed} 行）`;
        } else { tail = '定位库没找到这一步，没回写'; }
      } catch (e) { tail = '回写失败：' + String(e.message || e); }
    }
    console.log(`[自愈] 第${rec.步骤}步「${s['标签'] || act}」原定位失效 → 用 ${rec.命中级别} 点到（试了 ${rec.试了几级} 级）${tail}`);
  }
  if (result && result.ok && String(result.ok).startsWith('error:')) {
    failedStep = `点到了但动作失败：${result.ok}`;
    break;
  }
  await sleep(600);
  // 等可能的下载
  if (act === 'download' || (result && result.ok === 'ok')) await sleep(500);
}
if (healed) console.log(`[自愈] 本轮共 ${healed} 步靠降级定位救回${HEAL ? '，已写入 自愈记录.csv' : '（真改版前建议加 --heal 跑一次，把库修好）'}`);
if (failedStep) {
  console.error(`[页面失败] ${failedStep}\n→ 六种定位都试过还找不到 = 真改版。跑：node scripts/manage.mjs fail --link <链路名> --phenomenon "${failedStep}" 标 broken，然后整条重录。`);
  cdp.close();
  process.exit(3);
}

let downloaded = null;
if (selfDownload) {
  await dl.waitAll(120000).catch(() => {});
  const done = dl.files.filter(f => f.done);
  if (!done.length) {
    console.error('链路该下载导出表，但一个文件都没等到——导出按钮或页面多半变了');
    cdp.close();
    process.exit(3);
  }
  downloaded = path.join(dl.dir, done[0].filename);
  console.log(`下载完成：${downloaded}`);
}
if (!table) table = loadSource(downloaded);
console.log(`源表：${table.name} · ${table.rows.length} 行 × ${mappings.length} 列 · 唯一键=${keyCols.join('+')}`);
const { tsv: pasteTsv } = buildPaste(table);

/* ---- 逐路由粘贴 + 回读 ---- */
let verifyFail = 0;
for (const route of activeRoutes) {
  const url = route['目标表格URL'];
  if (!url) { console.log(`[跳过] 路由 ${route['账户']}：目标表格URL 没填（在路由表.csv 里补）`); verifyFail++; continue; }
  await cdp.send('Page.navigate', { url }).catch(() => {});
  await sleep(5000);
  await cdp.injectFile(path.join(ROOT, 'assets', 'act.js'));
  const anchor = route['落点best'] || '';
  const pasteRes = anchor
    ? await cdp.evalJs(`window.__ACT.pasteInto(${JSON.stringify(anchor)}, ${JSON.stringify(pasteTsv)})`, { awaitPromise: false })
    : await cdp.evalJs(`window.__ACT.pasteText(${JSON.stringify(pasteTsv)})`, { awaitPromise: false });
  if (String(pasteRes).includes('not-found') || String(pasteRes).includes('no-element')) {
    console.error(`[贴失败] ${route['账户']} → ${pasteRes}`); verifyFail++; continue;
  }
  await sleep(3000);
  const body = await cdp.evalJs('window.__ACT.bodyText()', { awaitPromise: false });
  const missing = [];
  for (const r of table.rows) {
    const k = keyCols.map(c => String(r[c])).join('|');
    const hit = keyCols.every(c => String(body).includes(String(r[c])));
    if (!hit) missing.push(k);
  }
  if (missing.length) {
    console.error(`[复核不过] ${route['账户']}：${missing.length}/${table.rows.length} 行的键值在目标页找不到（如 ${missing[0]}）`);
    verifyFail += missing.length;
  } else {
    console.log(`[复核通过] ${route['账户']}：${table.rows.length} 行键值全部在目标页见到`);
  }
}
cdp.close();
if (verifyFail) { console.error(`\n完成但有 ${verifyFail} 项失败——按口径这轮算没跑通，别报成功`); process.exit(2); }
console.log(`\n✓ 全链路通过（${activeRoutes.length} 条路由）${downloaded ? ' · 下载=' + downloaded : ''}`);
console.log('');
console.log('产物：recordings/ + evidence/ 里可能有本次页面数据（账号/投放/金额）');
console.log('  用完就清：node scripts/manage.mjs clean --days 0');
console.log('  要留存：先加密（7z a -p -mhe=on），密码别和文件放一起');
