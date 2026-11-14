/* build_skill.mjs — 把定稿的配置生成一个独立子技能包
 * 用法：
 *   UI 版（点击回放）：node scripts/build_skill.mjs --link <名> --config <草稿目录>
 *   接口版（直调接口）：node scripts/build_skill.mjs --link <名> --config <探查目录> --type api [--force]
 * UI 版前提：目录里有 链路就绪.json（人工核对过映射）；接口版前提：探查报告判定「能接口化」（用户确认过）
 * 产物：produced/<链路>/ 自包含包，zip/ 里出包，台账登记一行
 */
import path from 'node:path';
import fs from 'node:fs';
import { fileURLToPath } from 'node:url';
import { zipDir, listEntries } from './lib-zip.mjs';
import { readTrigger, triggerSection, missingTriggerNotice } from './lib-trigger.mjs';
import { manualText } from './lib-manual.mjs';
import { parseCsv } from './lib-heal.mjs';
import { toFarmScript } from './lib-farm.mjs';

const ROOT = path.resolve(path.dirname(fileURLToPath(import.meta.url)), '..');
const arg = (k, d) => { const i = process.argv.indexOf('--' + k); return i >= 0 ? process.argv[i + 1] : d; };
const flag = k => process.argv.includes('--' + k);

const link = arg('link');
const configDir = arg('config');
const type = String(arg('type', 'ui')).toLowerCase();
if (!link || !configDir) { console.error('用法：node scripts/build_skill.mjs --link <名> --config <目录> [--type ui|api] [--force]'); process.exit(1); }

const outDir = path.join(ROOT, 'produced', link);

/* ---- 需求访谈产物（触发.json）：没有它，产物只是一条「重复路径」 ----
 * 默认：警告 + 在子技能顶部插待办（不静默放过）；--require-trigger：直接拒绝生成 */
const trig = readTrigger(configDir, link, ROOT);
if (!trig && flag('require-trigger')) {
  console.error(`拒绝生成：没问过需求（缺 触发.json）。先跑 node scripts/interview.mjs --link ${link}`);
  process.exit(1);
}
if (!trig) {
  console.warn('⚠️ 没找到 触发.json：这条链路只有「怎么点」，没有「什么时候跑/参数哪来/跑完给谁」。');
  console.warn(`   建议先跑：node scripts/interview.mjs --link ${link}`);
}
const trigBlock = trig ? triggerSection(trig.data) : missingTriggerNotice(link);

/* ---------------- 接口版 ---------------- */
if (type === 'api') {
  const draftFile = ['接口配置草稿.json', '接口.json'].map(f => path.join(configDir, f)).find(fs.existsSync);
  if (!draftFile) { console.error('接口版要 接口配置草稿.json（先跑 scripts/probe.mjs 探查）'); process.exit(1); }
  const draft = JSON.parse(fs.readFileSync(draftFile, 'utf8'));
  if (!/能接口化/.test(draft.verdict || '') && !flag('force')) {
    console.error(`探查结论不是「能接口化」（${draft.verdict || '未判定'}）：先给用户看报告确认；确实要生成加 --force`);
    process.exit(1);
  }

  /* ---- 二次录制判定（可选但强烈建议）：参数和 body 模板从「两次数据」来，不从「理解」来 ---- */
  const vFile = arg('verdict-from');
  let vd = null;
  if (vFile) {
    const vp = path.resolve(vFile);
    if (!fs.existsSync(vp)) { console.error(`找不到参数判定文件：${vp}（先跑 scripts/diffrec.mjs）`); process.exit(1); }
    vd = JSON.parse(fs.readFileSync(vp, 'utf8'));
    if (vd.actionsSame === false) console.warn('⚠️ 两次录制动作不一致（见对比报告），参数判定要打折看');
  }
  const reqUrl = String(draft.request?.url || '');
  const baseKey = (() => { try { const u = new URL(reqUrl); return `${String(draft.request?.method || 'GET').toUpperCase()} ${u.host}${u.pathname}`; } catch { return ''; } })();

  const method = String(draft.request?.method || 'GET').toUpperCase();
  /* 模板来源优先级：diffrec 判出的模板 > probe 草稿的 bodyTemplate > 标明来自录制的 body 原文 */
  const bodyTemplate = (vd?.bodyTemplates?.[baseKey]?.template)
    || draft.request?.bodyTemplate
    || (draft.request?.bodySource === 'recording' ? draft.request?.body : '')
    || '';
  const urlTemplate = (vd?.urlTemplates?.[baseKey]) || reqUrl;
  const params = { ...(draft.params || {}), ...(vd?.params || {}) };

  /* 铁律：请求体模板替换法 —— 有 body 的接口，模板必须来自录制原文，不许凭理解重写 */
  const needBody = !['GET', 'HEAD', 'OPTIONS'].includes(method);
  if (needBody && draft.request?.body && !bodyTemplate) {
    console.error('拒绝生成：接口有 body，但拿不到「录制原文」模板（bodySource 不是 recording、也没有 diffrec 模板）。先跑 diffrec 出模板 —— 不许手写 body，少个字段就静默少数据');
    process.exit(1);
  }
  const placeholders = [...new Set([...String(bodyTemplate).matchAll(/\{\{(\w+)\}\}/g)].map(m => m[1]))];
  const missing = placeholders.filter(k => params[k] == null || params[k] === '');
  if (missing.length) {
    console.error(`拒绝生成：body 模板里的变量没有默认值：${missing.join('、')}（先跑 diffrec，或 --param ${missing[0]}=...）`);
    process.exit(1);
  }
  /* 查询参数只取真出现在 URL 里的，避免把 body 专用参数塞进 query */
  const queryKeys = (() => { try { return [...new URL(reqUrl).searchParams.keys()]; } catch { return []; } })();

  fs.rmSync(outDir, { recursive: true, force: true });
  fs.mkdirSync(path.join(outDir, '配置'), { recursive: true });
  fs.mkdirSync(path.join(outDir, 'scripts'), { recursive: true });
  fs.copyFileSync(path.join(ROOT, 'scripts', 'api_run.mjs'), path.join(outDir, 'scripts', 'api_run.mjs'));
  /* lib-guard.mjs 必须随包：api_run.mjs 顶部静态 import 它，写闸门靠它把关 */
  for (const f of ['lib-cdp.mjs', 'lib-guard.mjs']) fs.copyFileSync(path.join(ROOT, 'scripts', f), path.join(outDir, 'scripts', f));

  const fieldCount = Number(arg('expect-fields', String((draft.fields || []).length || 0)));
  const apiCfg = {
    name: link,
    request: {
      method,
      url: urlTemplate,
      bodyTemplate,
      bodyMode: bodyTemplate ? 'template' : 'none',
      headers: draft.request?.headers || {}
    },
    dataPath: draft.dataPath || null,
    fields: draft.fields || [],
    params,
    queryParams: queryKeys,
    requiredParams: draft.requiredParams || [],
    校验: {
      minRows: Number(arg('min-rows', '1')),
      requiredFields: (draft.fields || []).slice(0, 1),
      fieldCount
    },
    port: Number(arg('port', '18802')),
    sourceRecording: draft.sourceRecording || '',
    verdictFrom: vd ? path.basename(vFile) : ''
  };
  fs.writeFileSync(path.join(outDir, '配置', '接口.json'), JSON.stringify(apiCfg, null, 1), 'utf8');

  const host = new URL(apiCfg.request.url).host;
  const tpl = fs.readFileSync(path.join(ROOT, 'templates', 'child.api.SKILL.md'), 'utf8');
  fs.writeFileSync(path.join(outDir, 'SKILL.md'), tpl
    .replace(/{{链接名}}/g, link)
    .replace(/{{host}}/g, host)
    .replace(/{{method}}/g, apiCfg.request.method)
    .replace(/{{url}}/g, apiCfg.request.url)
    .replace(/{{dataPath}}/g, apiCfg.dataPath || '（自动找第一个对象数组）')
    .replace(/{{fields}}/g, (apiCfg.fields || []).join('、') || '（自动）')
    .replace(/{{minRows}}/g, String(apiCfg.校验.minRows))
    .replace(/{{required}}/g, apiCfg.校验.requiredFields.length ? `；必需字段 ${apiCfg.校验.requiredFields.join('、')}` : '')
    .replace(/{{port}}/g, String(apiCfg.port))
    .replace(/{{configSample}}/g, JSON.stringify(apiCfg, null, 1).replace(/</g, '‹'))
    .replace('## 怎么跑', trigBlock + '\n## 怎么跑'), 'utf8');
  if (trig) fs.copyFileSync(trig.file, path.join(outDir, '配置', '触发.json'));
  fs.writeFileSync(path.join(outDir, '一键跑.md'),
    '# 一键跑（命令速查）\n\n先预览（只渲染请求，不碰浏览器）：\n    node scripts/api_run.mjs --config 配置\n\n预览没问题再真跑：\n    node scripts/api_run.mjs --config 配置 --go\n\n导出 CSV：\n    node scripts/api_run.mjs --config 配置 --go --out 结果.csv\n', 'utf8');

  const ledFile = path.join(ROOT, '台账.csv');
  const led = fs.existsSync(ledFile) ? fs.readFileSync(ledFile, 'utf8').split(/\r?\n/).filter(l => l.trim()) : ['链路,版本,状态,最后变动,zip,失败次数,备注'];
  const row = led.findIndex(l => l.startsWith(link + ','));
  const prevVer = row >= 0 ? (Number(String(led[row].split(',')[1] || '').replace(/^v/, '')) || 0) : 0;
  const version = String(prevVer + 1);
  const stamp = new Date(Date.now() - new Date().getTimezoneOffset() * 60000).toISOString().slice(0, 16).replace('T', ' ');
  /* 说明书：接口版也给一份，人看的是「干什么/什么时候跑/怎么算成功」（先写，再打包） */
  fs.writeFileSync(path.join(outDir, '说明书.md'), manualText({
    link, type: 'api', steps: [], trigger: trig ? trig.data : null, mappings: [], version: `v${version}`
  }), 'utf8');
  const zipInfo = zipDir(outDir, link, path.join(ROOT, 'zip', `${link}_v${version}_${stamp.slice(0, 10).replace(/-/g, '')}.zip`));
  const line = `${link},${version},已生成(api),${stamp},${path.basename(zipInfo.path)},0,type=api`;
  if (row >= 0) led[row] = line; else led.push(line);
  fs.writeFileSync(ledFile, led.join('\r\n') + '\r\n', 'utf8');

  const chk = listEntries(zipInfo.path);
  console.log(`✓ 接口版子技能已生成：${outDir}`);
  console.log(`  接口：${apiCfg.request.method} ${apiCfg.request.url.slice(0, 100)}`);
  console.log(`  触发：${trig ? (trig.data.触发?.说明 || trig.data.用途) : '⚠️ 没问过需求（只有路径）'}`);
  console.log(`  校验：行数 ≥ ${apiCfg.校验.minRows}，字段数 = ${apiCfg.校验.fieldCount}，必需字段 ${apiCfg.校验.requiredFields.join('、') || '无'}`);
  console.log(`  包：${zipInfo.path}（${zipInfo.files} 个文件，回读 ${chk.length} 条）`);
  console.log(`  先预览：node produced/${link}/scripts/api_run.mjs --config produced/${link}/配置`);
  process.exit(0);
}

/* ---------------- UI 版 ---------------- */
if (!fs.existsSync(path.join(configDir, '链路就绪.json'))) {
  console.error('配置没定稿（缺 链路就绪.json）：先跑 analyze.py --confirm 走完人工核对');
  process.exit(1);
}

/* 子包 = 同款结构，run.mjs 按 scripts/.. 找 assets，原样搬就能跑 */
fs.rmSync(outDir, { recursive: true, force: true });
fs.mkdirSync(path.join(outDir, '配置'), { recursive: true });
fs.mkdirSync(path.join(outDir, 'scripts'), { recursive: true });
fs.copyFileSync(path.join(ROOT, 'scripts', 'run.mjs'), path.join(outDir, 'scripts', 'run.mjs'));
/* lib-heal.mjs 必须随包：run.mjs 顶部静态 import 它，缺了子包一跑就 module not found */
for (const f of ['lib-cdp.mjs', 'lib-tableread.mjs', 'lib-heal.mjs']) fs.copyFileSync(path.join(ROOT, 'scripts', f), path.join(outDir, 'scripts', f));
fs.mkdirSync(path.join(outDir, 'assets'), { recursive: true });
fs.copyFileSync(path.join(ROOT, 'assets', 'act.js'), path.join(outDir, 'assets', 'act.js'));
for (const f of fs.readdirSync(configDir)) fs.copyFileSync(path.join(configDir, f), path.join(outDir, '配置', f));

/* 子包 SKILL.md：直给接手 AI/同事的执行规程 */
const tpl = fs.readFileSync(path.join(ROOT, 'templates', 'child.SKILL.md'), 'utf8');
const mappingRows = fs.readFileSync(path.join(outDir, '配置', '映射字典.csv'), 'utf8').split(/\r?\n/).filter(l => l.trim());
fs.writeFileSync(path.join(outDir, 'SKILL.md'),
  tpl.replace(/{{链接名}}/g, link).replace('{{映射表}}', mappingRows.slice(0, 12).join('\n').replace(/</g, '‹'))
     .replace('## 怎么跑', trigBlock + '\n## 怎么跑'), 'utf8');
if (trig) fs.copyFileSync(trig.file, path.join(outDir, '配置', '触发.json'));
fs.copyFileSync(path.join(ROOT, 'templates', '一键跑.md'), path.join(outDir, '一键跑.md'));

/* 台账：一链路一行，重跑覆盖同名行。口径：每次生成 = 版本 +1、失败次数清零（新包新账，
   历史失败在 logs/失败台账.log 里永远可查）——重录升级和普通重生成走同一条规则，不搞分支 */
const ledgerFile = path.join(ROOT, '台账.csv');
const ledger = fs.existsSync(ledgerFile)
  ? fs.readFileSync(ledgerFile, 'utf8').split(/\r?\n/).filter(l => l.trim())
  : ['链路,版本,状态,最后变动,zip,失败次数,备注'];
const row = ledger.findIndex(l => l.startsWith(link + ','));
const prevVer = row >= 0 ? (Number(String(ledger[row].split(',')[1] || '').replace(/^v/, '')) || 0) : 0;
const version = String(prevVer + 1);
const stamp = new Date(Date.now() - new Date().getTimezoneOffset() * 60000).toISOString().slice(0, 16).replace('T', ' ');
/* 说明书（UI 版）：步骤直接来自 定位库.csv，和脚本同序号；映射交给人工核对过的 映射字典 */
const libCsv = path.join(outDir, '配置', '定位库.csv');
const mapCsv = path.join(outDir, '配置', '映射字典.csv');
const libSteps = fs.existsSync(libCsv) ? parseCsv(fs.readFileSync(libCsv, 'utf8')).rows : [];
const mapRows = fs.existsSync(mapCsv) ? parseCsv(fs.readFileSync(mapCsv, 'utf8')).rows : [];
fs.writeFileSync(path.join(outDir, '说明书.md'), manualText({
  link, type: 'ui', steps: libSteps, trigger: trig ? trig.data : null, mappings: mapRows, version: `v${version}`
}), 'utf8');
/* 农场脚本（2026-11-14）：纯点击链路顺手翻一份 browser-farm 挂机脚本——触发.json 里问过的
 * 「什么时候跑」只有农场能兑现（loop/watch 常驻引擎）。有填值/粘贴步的链路不出，不交付半截脚本 */
const farm = toFarmScript(libSteps, { name: link, triggerNote: trig ? (trig.data.触发?.说明 || trig.data.用途 || '') : '' });
if (farm.ok) {
  fs.writeFileSync(path.join(outDir, '农场脚本.json'), JSON.stringify(farm.script, null, 2), 'utf8');
} else {
  console.log(`  农场脚本：不出——${farm.why}`);
}
const zipInfo = zipDir(outDir, link, path.join(ROOT, 'zip', `${link}_v${version}_${stamp.slice(0, 10).replace(/-/g, '')}.zip`));
const line = `${link},${version},已生成,${stamp},${path.basename(zipInfo.path)},0,`;
if (row >= 0) ledger[row] = line; else ledger.push(line);
fs.writeFileSync(ledgerFile, ledger.join('\r\n') + '\r\n', 'utf8');

const check = listEntries(zipInfo.path);
console.log(`✓ 子技能已生成：${outDir}`);
console.log(`  触发：${trig ? (trig.data.触发?.说明 || trig.data.用途) : '⚠️ 没问过需求（只有路径）'}`);
if (farm.ok) console.log(`  农场：农场脚本.json 已出（${farm.script.steps.length} 步）——交 POST /script/new 挂机跑`);
console.log(`  包：${zipInfo.path}（${zipInfo.files} 个文件，回读验证 ${check.length} 条）`);
console.log(`  下一步：真实跑一轮 node produced/${link}/scripts/run.mjs --config 配置 --go`);
console.log(`  跑通后：node scripts/manage.mjs pass --link ${link}（记 verified，下次生成自动升版）`);
