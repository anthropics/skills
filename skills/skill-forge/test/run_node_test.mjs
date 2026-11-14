/* run_node_test.mjs — Node 侧自测：表格读取（csv+xlsx）+ zip 打包回读
 * 用法：node test/run_node_test.mjs   （xlsx 样例由 python 测试生成，没有就现场造一个最小合法包）
 */
import fs from 'node:fs';
import http from 'node:http';
import path from 'node:path';
import { fileURLToPath } from 'node:url';
import { readCsv, readXlsx, toNum } from '../scripts/lib-tableread.mjs';
import { zipStore, listEntries } from '../scripts/lib-zip.mjs';

const HERE = path.dirname(fileURLToPath(import.meta.url));
const FIX = path.join(HERE, '_fixture');
fs.mkdirSync(FIX, { recursive: true });
const checks = [];
const ok = (name, cond) => { checks.push([name, cond]); console.log((cond ? '✓ ' : '✗ ') + name); };

/* 1) csv 读取（utf-8-sig） */
const csvPath = path.join(FIX, '源表.csv');
if (fs.existsSync(csvPath)) {
  const t = readCsv(csvPath);
  ok('csv 表头', t.headers.join(',') === '日期,视频id,名称,消耗,展示次数');
  ok('csv 行数=4', t.rows.length === 4);
  ok('数字口径', toNum('1,200.50') === 1200.5);
} else {
  ok('csv（跳过：先跑 python 测试生成样例）', true);
}

/* 2) 最小 xlsx 现场造一个再读（inlineStr 写法） */
const xlsxPath = path.join(FIX, 'mini.xlsx');
if (!fs.existsSync(xlsxPath)) {
  // 最简结构：只放我们两个解析器都认的部件（不给 Excel 打开用，给解析器用）
  const entries = [
    ['[Content_Types].xml', '<?xml version="1.0"?><Types/>'],
    ['xl/workbook.xml', '<?xml version="1.0"?><workbook><sheets><sheet name="数据"/></sheets></workbook>'],
    ['xl/worksheets/sheet1.xml',
      '<?xml version="1.0"?><worksheet><sheetData>' +
      '<row><c r="A1" t="inlineStr"><is><t>日期</t></is></c><c r="B1" t="inlineStr"><is><t>消耗</t></is></c></row>' +
      '<row><c r="A2" t="inlineStr"><is><t>2026-10-30</t></is></c><c r="B2"><v>1200.5</v></c></row>' +
      '</sheetData></worksheet>']
  ];
  // 复用 zipStore 打出合法 zip 结构
  const { zipStore: zs } = await import('../scripts/lib-zip.mjs');
  zs(entries.map(([name, data]) => ({ name, data: Buffer.from(data, 'utf8') })), xlsxPath);
}
const xt = readXlsx(xlsxPath);
ok('xlsx 表头', xt.headers.join(',') === '日期,消耗');
ok('xlsx 数值单元格', xt.rows[0]['消耗'] === '1200.5');

/* 3) zip 打包 → 回读验证条目名 */
const zipPath = path.join(FIX, 'roundtrip.zip');
zipStore([
  { name: 'skill-forge/SKILL.md', data: Buffer.from('# 测试中文条目名', 'utf8') },
  { name: 'skill-forge/配置/映射字典.csv', data: Buffer.from('源列,目标列\n消耗,花费\n', 'utf8') }
], zipPath);
const names = listEntries(zipPath);
ok('zip 回读 2 条', names.length === 2);
ok('zip 条目用 / 分隔且无反斜杠', names.every(n => !n.includes('\\')));
ok('zip 中文条目名读回一致', names.includes('skill-forge/配置/映射字典.csv'));

/* 4) 大 zip（超过 64KB EOCD 搜索窗）回读——tail 变子视图后偏移重复加的坑 */
const bigPath = path.join(FIX, 'big.zip');
zipStore([
  { name: 'a/big.bin', data: Buffer.alloc(70000, 7) },
  { name: 'a/明细.csv', data: Buffer.from('日期,消耗\n2026-10-31,1200.50\n', 'utf8') }
], bigPath);
const bigNames = listEntries(bigPath);
ok('大zip（>64KB 窗口）回读 2 条', bigNames.length === 2 && bigNames.includes('a/明细.csv'));

/* 5) 农场感知（2026-11-14）：假农场总管上验 档位识别/收尾豁免/写前快照——不碰真 9300 */
const { farmSlotOf, closeChromeSmart, farmPreWriteSnapshot } = await import('../scripts/lib-cdp.mjs');
const { toFarmScript, stepToFarm } = await import('../scripts/lib-farm.mjs');
const FARM_SLOT_PORT = 19999; // 只存在于假农场 /slots 里的口
const fakeState = { fail: false, snapshot: null };
const fakeFarm = http.createServer((req, res) => {
  if (req.url === '/health') { res.writeHead(200, { 'Content-Type': 'application/json' }); return res.end('{"ok":true}'); }
  if (req.url === '/slots') {
    res.writeHead(200, { 'Content-Type': 'application/json' });
    return res.end(JSON.stringify({ ok: true, slots: [{ id: '01', note: '测试-主号', port: FARM_SLOT_PORT, alive: true }] }));
  }
  if (req.method === 'POST' && req.url === '/slot/01/snapshot') {
    let d = ''; req.on('data', c => d += c); req.on('end', () => {
      fakeState.snapshot = JSON.parse(d);
      if (fakeState.fail) { res.writeHead(500, { 'Content-Type': 'application/json' }); return res.end('{"ok":false,"error":"沙盒满了"}'); }
      res.writeHead(200, { 'Content-Type': 'application/json' }); res.end('{"ok":true,"name":"x"}');
    });
    return;
  }
  res.writeHead(404); res.end('{}');
});
await new Promise(r => fakeFarm.listen(0, '127.0.0.1', r));
process.env.SF_FARM_PORT = String(fakeFarm.address().port); // 指到假农场，绝不动真 9300
ok('farmSlotOf 认出场档位', (await farmSlotOf(FARM_SLOT_PORT) || {}).id === '01');
ok('farmSlotOf 非场口返回 null', (await farmSlotOf(18877)) === null);
const smartLogs = [];
const smartR = await closeChromeSmart(FARM_SLOT_PORT, { log: m => smartLogs.push(m) });
ok('closeChromeSmart 农场档不关（打豁免日志）', smartR.skipped === 'farm-slot' && smartLogs.some(l => l.includes('不关')));
const snapR = await farmPreWriteSnapshot(FARM_SLOT_PORT, '写前快照 api测试 POST');
ok('写前快照真打到农场（名字带前缀）', snapR && snapR.slot.id === '01' && /^写前快照/.test(fakeState.snapshot?.name || ''), fakeState.snapshot);
fakeState.fail = true;
let snapThrew = false; try { await farmPreWriteSnapshot(FARM_SLOT_PORT, 'x'); } catch { snapThrew = true; }
ok('快照失败抛错（api_run 据此拦写）', snapThrew);
fakeState.fail = false;
delete process.env.SF_FARM_PORT;
fakeFarm.close();

/* 6) 定位库→农场脚本 翻译器 */
const clickChain = [
  { '步骤': '1', '动作': 'nav', '页面': 'https://x.example.com/list' },
  { '步骤': '2', '动作': 'click', '标签': '导出', 'best定位': '#exp', 'L1_id': '#exp', 'L2_testid': '', 'L4_text': '导出报表', 'L5_css': 'button.btn [non-unique:3]', 'L6_nth_path': 'div > button:nth-of-type(2)', '页面': 'https://x.example.com/list' },
  { '步骤': '3', '动作': 'download', 'best定位': 'a[href="/e.csv"]', '页面': 'https://x.example.com/list' },
];
const farmOk = toFarmScript(clickChain, { name: '纯点击链' });
ok('纯点击链路出农场脚本（nav 不占步）', farmOk.ok && farmOk.script.steps.length === 2, farmOk.why || farmOk.script?.steps?.length);
ok('locs 六级直译（id→text→css→nth，non-unique 剥掉）',
  JSON.stringify(farmOk.script.steps[0].locs) === JSON.stringify(['#exp', 'text=导出报表', 'path=button.btn', 'path=div > button:nth-of-type(2)']),
  farmOk.script.steps[0].locs);
ok('css 形态 best 走 path=', farmOk.script.steps[1].locs[0] === 'path=a[href="/e.csv"]', farmOk.script.steps[1].locs);
ok('每步带 href（farm 自动开回录制页）', farmOk.script.steps.every(s => s.href === 'https://x.example.com/list'));
const farmBlocked = toFarmScript([{ '步骤': '1', '动作': 'fill', 'best定位': '#d' }, ...clickChain.slice(1)], { name: '带填值' });
ok('有填值步整份不出（不出半截脚本）', farmBlocked.ok === false && /fill/.test(farmBlocked.why || ''), farmBlocked.why);
ok('裸文本 best 翻成 text=', (stepToFarm({ '动作': 'click', 'best定位': '下载报表' }).step || {}).selector === 'text=下载报表');
ok('L3 role 形态翻成 text=', (stepToFarm({ '动作': 'click', 'L3_role': 'button[name="提交"]' }).step || {}).locs[0] === 'text=提交');

const bad = checks.filter(([, c]) => !c).map(([n]) => n);
if (bad.length) { console.error('\nnode test 失败：' + bad.join('；')); process.exit(1); }
console.log(`\nnode test 全过（${checks.length}/${checks.length}）`);
