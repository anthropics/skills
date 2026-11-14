/* run_forge_v2_test.mjs — 2026-11-06 新增四项的回归测试（零网络、零浏览器）
 * 覆盖：① 二次录制 diff ② body 模板替换 ③ 字段数校验 ④ 独立登录通道参数校验
 * 跑法：node test/run_forge_v2_test.mjs
 */
import { execFileSync } from 'node:child_process';
import path from 'node:path';
import fs from 'node:fs';
import { fileURLToPath, pathToFileURL } from 'node:url';

const ROOT = path.resolve(path.dirname(fileURLToPath(import.meta.url)), '..');
const NODE = process.execPath;
const tmp = path.join(ROOT, 'test', '_out');
fs.rmSync(tmp, { recursive: true, force: true });
fs.mkdirSync(tmp, { recursive: true });

let pass = 0, fail = 0;
const ok = (name, cond, extra = '') => {
  if (cond) { pass++; console.log(`✓ ${name}`); }
  else { fail++; console.log(`✗ ${name} ${extra}`); }
};
const run = (args, opts = {}) => {
  try {
    const out = execFileSync(NODE, args, { cwd: ROOT, encoding: 'utf8', stdio: ['ignore', 'pipe', 'pipe'], ...opts });
    return { code: 0, out };
  } catch (e) {
    return { code: e.status ?? -1, out: `${e.stdout || ''}${e.stderr || ''}` };
  }
};

/* Python 解析：打包副本里可能没有 PATH 上的 python，探不到就 SKIP（不算挂） */
const PY_CANDS = [process.env.SF_PY, 'python', 'python3'].filter(Boolean);
const PY = (() => {
  for (const c of PY_CANDS) {
    try { execFileSync(c, ['-c', 'print(1)'], { stdio: 'ignore' }); return c; } catch { /* 下一个 */ }
  }
  return null;
})();
const runPy = (args) => {
  try {
    const out = execFileSync(PY, args, { cwd: ROOT, encoding: 'utf8', stdio: ['ignore', 'pipe', 'pipe'] });
    return { code: 0, out };
  } catch (e) {
    return { code: e.status ?? -1, out: `${e.stdout || ''}${e.stderr || ''}` };
  }
};

/* ---------- ① 二次录制 diff ---------- */
const a = 'test/_fixture/rec_a.rec.json', b = 'test/_fixture/rec_b.rec.json';
const d1 = run(['scripts/diffrec.mjs', '--a', a, '--b', b, '--out', path.join('test', '_out', 'ev'), '--name', 't']);
ok('diffrec 退出 0', d1.code === 0, d1.out.slice(-300));
const diffDirs = fs.existsSync(path.join(ROOT, 'test/_out/ev'))
  ? fs.readdirSync(path.join(ROOT, 'test/_out/ev')) : [];
const diffDir = diffDirs[0] ? path.join(ROOT, 'test/_out/ev', diffDirs[0]) : '';
const verdict = diffDir && fs.existsSync(path.join(diffDir, '参数判定.json'))
  ? JSON.parse(fs.readFileSync(path.join(diffDir, '参数判定.json'), 'utf8')) : null;
ok('diffrec 产出参数判定.json', !!verdict);
ok('变量定出 4 个（start/end/start_date/end_date）',
  verdict && ['start', 'end', 'start_date', 'end_date'].every(k => verdict.varKeys.includes(k)),
  verdict && JSON.stringify(verdict.varKeys));
ok('常量没被误判成变量（aavid/page/size 不在变量里）',
  verdict && !['aavid', 'page', 'size', 'metrics'].some(k => verdict.varKeys.includes(k)));
const tpl = verdict?.bodyTemplates?.['POST demo.example.com/api/report/sum']?.template || '';
ok('body 模板来自原文（保留 aavid 和 metrics）', tpl.includes('7000000000000001') && tpl.includes('"metrics":["cost"]'), tpl);
ok('body 模板把日期换成占位符', tpl.includes('{{start_date}}') && tpl.includes('{{end_date}}'));
ok('只出现一次的请求被单独列出', verdict?.onlyInB?.some(x => x.includes('/api/track/ping')));

/* ---------- ②③ build_skill：模板 + 字段数 ---------- */
const ledger = path.join(ROOT, '台账.csv');
const ledgerBak = fs.existsSync(ledger) ? fs.readFileSync(ledger) : null;
const bres = run(['scripts/build_skill.mjs', '--link', '_t_v2', '--config', 'test/draft', '--type', 'api',
  '--verdict-from', path.join(diffDir, '参数判定.json')]);
ok('build_skill 用 --verdict-from 生成成功', bres.code === 0, bres.out.slice(-300));
const cfgPath = path.join(ROOT, 'produced', '_t_v2', '配置', '接口.json');
const cfg = fs.existsSync(cfgPath) ? JSON.parse(fs.readFileSync(cfgPath, 'utf8')) : null;
ok('配置里有 bodyTemplate 且是模板形态', !!cfg?.request?.bodyTemplate && cfg.request.bodyMode === 'template');
ok('配置字段数 = 探查字段数（1）', cfg?.校验?.fieldCount === 1, String(cfg?.校验?.fieldCount));
ok('body 专用参数不进 queryParams', Array.isArray(cfg?.queryParams) && cfg.queryParams.length === 0);

/* ---------- ② api_run --dry：模板替换 ---------- */
const dry = run(['produced/_t_v2/scripts/api_run.mjs', '--config', 'produced/_t_v2/配置',
  '--param', 'start_date=2026-11-06', '--param', 'end_date=2026-11-06', '--dry']);
ok('api_run --dry 退出 0', dry.code === 0, dry.out.slice(-300));
let dryJson = null;
try { dryJson = JSON.parse(dry.out); } catch {}
ok('--dry 打印了渲染后的 body', !!dryJson?.body);
ok('日期变量被替换成传入值', dryJson?.body?.includes('2026-11-06'), dryJson?.body);
ok('模板里没有残留 {{ }}', dryJson?.body && !dryJson.body.includes('{{'));
ok('未参与替换的字段原样保留', dryJson?.body?.includes('"aavid":"7000000000000001"') && dryJson?.body?.includes('"metrics":["cost"]'));

/* ---------- ② 负例：模板变量缺值 → exit 4 ---------- */
const badCfg = path.join(ROOT, 'test/_out/badcfg');
fs.mkdirSync(badCfg, { recursive: true });
const c2 = JSON.parse(JSON.stringify(cfg));
delete c2.params.start_date;
fs.writeFileSync(path.join(badCfg, '接口.json'), JSON.stringify(c2));
const bad = run(['produced/_t_v2/scripts/api_run.mjs', '--config', path.join('test', '_out', 'badcfg'), '--dry']);
ok('缺参数时拒绝执行（exit 4）', bad.code === 4, `exit=${bad.code}`);
ok('错误信息点名缺哪个变量', bad.out.includes('start_date'));

/* ---------- ② 负例：有 body 但没模板 → 拒绝生成 ---------- */
const noTplDir = path.join(ROOT, 'test/_out/notpl');
fs.mkdirSync(noTplDir, { recursive: true });
const d3 = JSON.parse(fs.readFileSync(path.join(ROOT, 'test/draft/接口配置草稿.json'), 'utf8'));
delete d3.request.bodyTemplate;
delete d3.request.bodySource;   // 模拟「手写 body」：既不是录制原文，也没标来源
fs.writeFileSync(path.join(noTplDir, '接口配置草稿.json'), JSON.stringify(d3));
const b3 = run(['scripts/build_skill.mjs', '--link', '_t_notpl', '--config', path.join('test', '_out', 'notpl'), '--type', 'api']);
ok('拿不到原文模板时拒绝生成', b3.code !== 0, `exit=${b3.code}`);

/* ---------- ④ login.mjs 参数校验（不联网、不开浏览器） ---------- */
const l1 = run(['scripts/login.mjs']);
ok('login 缺 --url 退出 4', l1.code === 4, `exit=${l1.code}`);
const l2 = run(['scripts/login.mjs', '--url', 'https://demo.example.com/login']);
ok('login 缺账密退出 4 并提示环境变量', l2.code === 4 && l2.out.includes('SF_USER'), l2.out.slice(-200));

/* ---------- ⑤ 需求访谈：把「一条路径」问成「有规则的自动化」 ---------- */
const ivA = run(['scripts/interview.mjs', '--link', '_t_iv', '--answers', 'test/_fixture/answers_event.json', '--out', 'test/_out/iv']);
ok('interview 事件型 exit 0', ivA.code === 0, ivA.out.slice(-200));
const ivAJ = JSON.parse(fs.readFileSync(path.join(ROOT, 'test/_out/iv/触发.json'), 'utf8'));
ok('触发方式=event 且条件被原样记住', ivAJ.触发?.方式 === 'event' && /90%/.test(ivAJ.触发?.条件 || ''), ivAJ.触发?.条件);
ok('写操作必须带上限与确认方式', ivAJ.写操作?.是否写 === true && /500/.test(ivAJ.写操作?.上限与确认 || ''), JSON.stringify(ivAJ.写操作));
ok('参数来源被拆成「名字+来自哪」', (ivAJ.参数来源 || []).length === 3 && ivAJ.参数来源.every(p => p.name && p.from));
ok('产出形态可多选（在线表格 + 本地文件）', (ivAJ.产出?.形态 || []).includes('在线表格') && (ivAJ.产出?.形态 || []).includes('本地文件'), JSON.stringify(ivAJ.产出?.形态));
ok('选「在线表格」自动带出映射说明（下载表列头↔目标表列头）', /列头/.test(ivAJ.产出?.映射 || ''), ivAJ.产出?.映射);

const ivB = run(['scripts/interview.mjs', '--link', '_t_iv2', '--answers', 'test/_fixture/answers_cron.json', '--out', 'test/_out/iv2']);
const ivBJ = JSON.parse(fs.readFileSync(path.join(ROOT, 'test/_out/iv2/触发.json'), 'utf8'));
ok('定时型的 cron 表达式原样保留', ivB.code === 0 && ivBJ.触发?.方式 === 'cron' && ivBJ.触发?.表达式 === '0 9 * * *', ivBJ.触发?.表达式);

const ivC = run(['scripts/interview.mjs', '--link', '_t_iv3', '--answers', 'test/_fixture/answers_bad.json', '--out', 'test/_out/iv3']);
ok('答案糊了也不硬拦（exit 0，按用户口径「只问不固化」）', ivC.code === 0, `exit=${ivC.code}`);
ok('但要说清缺哪几样，不许当没问过', /待确认/.test(ivC.out) && /阈值/.test(ivC.out) && /上限|频率/.test(ivC.out), ivC.out.slice(-260));
const ivCJ = JSON.parse(fs.readFileSync(path.join(ROOT, 'test/_out/iv3/触发.json'), 'utf8'));
ok('待确认项写进 触发.json（后人能看到还欠什么）', Array.isArray(ivCJ.待确认) && ivCJ.待确认.length >= 2, JSON.stringify(ivCJ.待确认));
ok('没答的产出写成「待确认」，不编一个假的', /待确认/.test(JSON.stringify(ivCJ.产出)), JSON.stringify(ivCJ.产出));
const ivD = run(['scripts/interview.mjs', '--link', '_t_iv4', '--answers', 'test/_fixture/answers_bad.json', '--out', 'test/_out/iv4', '--strict']);
ok('--strict 时才有硬拦（想强制问全的人可选）', ivD.code === 1, `exit=${ivD.code}`);

/* ---------- ⑤ build_skill 把「什么时候跑」写进子技能 ---------- */
const ivCfg = path.join(ROOT, 'test/_out/iv');
fs.copyFileSync(path.join(ROOT, 'test/draft/接口配置草稿.json'), path.join(ivCfg, '接口配置草稿.json'));
const bsIv = run(['scripts/build_skill.mjs', '--link', '_t_iv', '--config', 'test/_out/iv', '--type', 'api', '--force', '--require-trigger']);
ok('build_skill --require-trigger 有访谈产物时生成成功', bsIv.code === 0, bsIv.out.slice(-300));
const childMd = fs.readFileSync(path.join(ROOT, 'produced/_t_iv/SKILL.md'), 'utf8');
ok('子技能 SKILL.md 里写进了「什么时候跑」段', childMd.includes('## 什么时候跑') && childMd.includes('90%'));
ok('触发.json 跟着子包一起交付', fs.existsSync(path.join(ROOT, 'produced/_t_iv/配置/触发.json')));

const noTrig = path.join(ROOT, 'test/_out/notrig');
fs.mkdirSync(noTrig, { recursive: true });
fs.copyFileSync(path.join(ROOT, 'test/draft/接口配置草稿.json'), path.join(noTrig, '接口配置草稿.json'));
const bsNo = run(['scripts/build_skill.mjs', '--link', '_t_notrig', '--config', 'test/_out/notrig', '--type', 'api', '--force', '--require-trigger']);
ok('没问过需求时 --require-trigger 拒绝生成', bsNo.code === 1 && /interview/.test(bsNo.out), `exit=${bsNo.code}`);
const bsWarn = run(['scripts/build_skill.mjs', '--link', '_t_notrig2', '--config', 'test/_out/notrig', '--type', 'api', '--force']);
const warnMd = fs.readFileSync(path.join(ROOT, 'produced/_t_notrig2/SKILL.md'), 'utf8');
ok('不加 --require-trigger 时：照生成但顶部插了「还没问需求」待办', bsWarn.code === 0 && warnMd.includes('还没问过需求'));

/* ---------- ⑥ 失败用人话：diagnose ---------- */
const d401 = run(['scripts/diagnose.mjs', '--http', '401', '--link', '_t_x']);
ok('401 → 说「登录过期」而不是报错码', /登录/.test(d401.out) && /不要/.test(d401.out), d401.out.slice(0, 200));
const dSel = run(['scripts/diagnose.mjs', '--err', 'Timeout waiting for selector .export-btn', '--exit', '3']);
ok('点不到元素 → 说「网站改版、要重录」', /重录/.test(dSel.out) && /按钮/.test(dSel.out), dSel.out.slice(0, 200));
const dEmpty = run(['scripts/diagnose.mjs', '--rows', '0']);
ok('拿到 0 行 → 先怀疑参数而不是重录', /参数/.test(dEmpty.out) && !/要不要重录：要/.test(dEmpty.out), dEmpty.out.slice(0, 200));
const dCap = run(['scripts/diagnose.mjs', '--err', '请完成滑块验证']);
ok('验证码 → 明说机器过不去、别重录', /验证码/.test(dCap.out) && /不要/.test(dCap.out));
const dUnk = run(['scripts/diagnose.mjs']);
ok('什么信息都没给 → 不硬猜，列该补的信息', /认不出来/.test(dUnk.out), dUnk.out.slice(0, 120));

/* ---------- ⑦ 浏览器之外：下载下来的表，得看得见（localview） ---------- */
if (PY) {
  /* mini.xlsx 不进包（平台禁二进制），由 run_node_test.mjs 现场生成；没跑过就 SKIP 这一条，不算失败 */
  if (fs.existsSync(path.join(ROOT, 'test/_fixture/mini.xlsx'))) {
    const lv1 = runPy(['scripts/localview.py', '--file', 'test/_fixture/mini.xlsx']);
    ok('localview 能读 xlsx（行数 + 列名）', lv1.code === 0 && /日期/.test(lv1.out) && /数据 1 行/.test(lv1.out), lv1.out.slice(0, 200));
  } else {
    console.log('· localview xlsx 测试 SKIP（mini.xlsx 未生成：先跑 node test/run_node_test.mjs）');
  }
  const lv2 = runPy(['scripts/localview.py', '--file', 'test/_fixture/源表.csv', '--rows', '2']);
  ok('localview 能读 csv 并给出列名', lv2.code === 0 && /消耗/.test(lv2.out), lv2.out.slice(0, 200));
  const lv3 = runPy(['scripts/localview.py', '--file', 'no_such_file.xlsx']);
  ok('文件不存在 → exit 4，不假装读到了', lv3.code === 4, `exit=${lv3.code}`);
  const lv4 = runPy(['scripts/localview.py', '--file', 'test/_fixture/fixture.rec.json']);
  ok('localview 也能读 json（键/摘要）', lv4.code === 0 && /键/.test(lv4.out), lv4.out.slice(0, 160));
} else {
  console.log('· localview 测试 SKIP（本机没探到 python）');
}

/* ---------- ⑧ 失败自愈：逐级降级 + 只回写命中那一步 ---------- */
const heal = await import(pathToFileURL(path.join(ROOT, 'scripts/lib-heal.mjs')).href);
{
  const step = { '步骤': '2', '动作': 'click', 'best定位': '#gone', 'L1_id': '#new-id', 'L2_testid': '', 'L3_role': '', 'L4_text': '确定', 'L5_css': 'a.btn', 'L6_nth_path': 'body > a' };
  const cands = heal.levelCandidates(step);
  ok('自愈候选：原定位在最前，然后按 L1→L6 排', cands[0].sel === '#gone' && cands[1].level === 'L1_id' && cands[cands.length - 1].level === 'L6_nth_path');
  ok('自愈候选：空级别和重复不占位', cands.filter(c => c.sel === '').length === 0 && new Set(cands.map(c => c.sel)).size === cands.length);
  const hit = await heal.firstHit(cands, async (c) => ({ found: c.sel === '确定' }));
  ok('逐级降级：原定位失效后由 L4_text 命中', hit.hit && hit.hit.level === 'L4_text' && hit.misses.length === 2, JSON.stringify(hit.misses));
  const none = await heal.firstHit(cands, async () => ({ found: false }));
  ok('六级别全找不到 → 不硬猜（hit=null）', none.hit === null && none.tried === cands.length);

  const lib = '步骤,动作,标签,值,best定位,L1_id,L4_text,页面\r\n1,fill,日期,2026-10-30,#date-start,#date-start,,u\r\n2,click,导出,,a[href="/export.csv"],,,u\r\n';
  const r = heal.applyHeal(lib, { '步骤': '2' }, 'button.export');
  ok('回写：只改命中那一步，其他行不动', r.changed === 1 && /button\.export/.test(r.text) && /#date-start/.test(r.text));
  ok('回写：找不到对应步骤时 changed=0（不瞎改）', heal.applyHeal(lib, { '步骤': '9' }, 'x').changed === 0);
}

/* ---------- ⑨ 单遍判参：一条录制就能给出变量提示 ---------- */
{
  const rec = JSON.parse(fs.readFileSync(path.join(ROOT, 'test/_fixture/fixture.rec.json'), 'utf8'));
  const ip = run(['scripts/infer_params.mjs', '--rec', 'test/_fixture/fixture.rec.json', '--json']);
  ok('infer --json 能判出日期是变量', ip.code === 0 && /"判定": "变量"/.test(ip.out) && /日期/.test(ip.out), ip.out.slice(0, 200));

  const fake = path.join(tmp, 'fake.rec.json');
  fs.writeFileSync(fake, JSON.stringify({
    meta: { name: 'fake' },
    actions: [
      { seq: 1, type: 'fill', label: '账户', value: 'ACC-20261030-XYZ', url: 'https://x.example.com/p?a=ACC-20261030-XYZ' },
      { seq: 2, type: 'fill', label: '备注', value: '固定口令', url: 'https://x.example.com/p' },
      { seq: 3, type: 'fill', label: '预算', value: '3000', url: 'https://x.example.com/p' },
      { seq: 4, type: 'click', label: '确定', value: '', url: 'https://x.example.com/p' }
    ],
    network: [{ respBody: '{"code":0,"data":{"budget":3000}}' }]
  }), 'utf8');
  const fp = run(['scripts/infer_params.mjs', '--rec', fake, '--out', path.join('test/_out', '参数判定.csv')]);
  ok('infer：URL 带出的值 → 变量', /ACC-20261030-XYZ/.test(fp.out) && /页面带出|单号/.test(fp.out));
  ok('infer：接口响应里出现的值 → 变量', /接口带出/.test(fp.out));
  ok('infer：看不出规律的值 → 常量/待确认，不硬判变量', /固定口令/.test(fp.out));
  ok('infer 落表：参数判定.csv 有判定列', fs.existsSync(path.join(ROOT, 'test/_out', '参数判定.csv')) && /判定/.test(fs.readFileSync(path.join(ROOT, 'test/_out', '参数判定.csv'), 'utf8')));
  ok('infer 文案：明说「这是提示，不是定论」', /提示.*不是定论/.test(fp.out));
  const clickOnly = path.join(tmp, 'clicks.rec.json');
  fs.writeFileSync(clickOnly, JSON.stringify({ meta: { name: 'c' }, actions: [{ seq: 1, type: 'click', label: '导出', value: '' }], network: [] }), 'utf8');
  const cp = run(['scripts/infer_params.mjs', '--rec', clickOnly]);
  ok('infer 纯点击链路：明说没有变量判定问题', cp.code === 0 && /没有填值步骤/.test(cp.out), cp.out.slice(0, 120));
}

/* ---------- ⑩ 子包说明书：人看得懂 + 步骤和定位库同序号 ---------- */
{
  const man = await import(pathToFileURL(path.join(ROOT, 'scripts/lib-manual.mjs')).href);
  const txt = man.manualText({
    link: '_t_man', type: 'ui', version: 'v3',
    steps: [{ '步骤': '1', '动作': 'fill', '标签': '日期', '值': '2026-10-30', '页面': 'https://a.example.com/l' }],
    trigger: { 用途: '每天拉一次投放数据', 触发: { 方式: 'cron', 说明: '每天 9 点' }, 产出: { 形态: ['本地文件'], 位置与接收方: '投放群' }, 成功判据: '行数≥1 且日期=昨天', 失败处理: '重试2次', 录制备注: [{ seq: 1, text: '只处理当天的' }] },
    mappings: []
  });
  ok('说明书：写明干什么/什么时候跑/怎么算成功', /每天拉一次投放数据/.test(txt) && /每天 9 点/.test(txt) && /行数≥1 且日期=昨天/.test(txt));
  ok('说明书：步骤表和定位库同序号', /\| 1 \| 填值 \| 日期 \| 2026-10-30 \|/.test(txt));
  ok('说明书：写清改版怎么办（自愈 + 重录）', /降级重试/.test(txt) && /--heal/.test(txt) && /真改版/.test(txt));
  ok('说明书：口述备注原话带进去', /只处理当天的/.test(txt));
  ok('说明书：没问过的项写「待确认」，不编', man.manualText({ link: 'x', type: 'ui', steps: [], trigger: null }).includes('待确认'));
}

/* ---------- ⑪ 口述备注：录制里的原话带进访谈 ---------- */
{
  const recN = path.join(tmp, 'notes.rec.json');
  fs.writeFileSync(recN, JSON.stringify({ meta: { name: 'n' }, actions: [], notes: [{ seq: 2, at: '10:20:30', text: '只处理当前文件夹' }] }), 'utf8');
  const iv = run(['scripts/interview.mjs', '--link', '_t_note', '--rec', recN, '--answers', 'test/_fixture/answers_cron.json', '--out', path.join(tmp, 'cfg_note')]);
  ok('访谈：录制备注会打出来', /只处理当前文件夹/.test(iv.out), iv.out.slice(0, 200));
  const tj = path.join(tmp, 'cfg_note', '触发.json');
  ok('访谈：录制备注写进 触发.json', fs.existsSync(tj) && /只处理当前文件夹/.test(fs.readFileSync(tj, 'utf8')));
}


/* ---------- 写接口闸门（合规：非 GET 必须 --allow-write） ---------- */
{
  const g = await import(pathToFileURL(path.join(ROOT, 'scripts/lib-guard.mjs')).href);
  ok('闸门：POST/PUT/PATCH/DELETE 判定为写', ['post','Put','patch','DELETE'].every(m => g.isWrite(m)));
  ok('闸门：GET/HEAD/OPTIONS 判定为读', ['get','head','OPTIONS',''].every(m => !g.isWrite(m)));
  const g1 = g.writeGate({ method: 'POST' });
  ok('闸门：POST 无 --allow-write 拒跑（exit 4）', g1.ok === false && g1.code === 4 && /--allow-write/.test(g1.msg));
  const g2 = g.writeGate({ method: 'POST', allowWrite: true, ack: '上限=单账户预算+200元｜批准=组长张三 11-07' });
  ok('闸门：POST 带 --allow-write + --ack 放行', g2.ok === true);
  const g2b = g.writeGate({ method: 'POST', allowWrite: true });
  ok('闸门：只有 --allow-write 没有 --ack 仍拒跑（exit 5）', g2b.ok === false && g2b.code === 5 && /上限/.test(g2b.msg));
  ok('闸门：--ack 写不清（缺上限/批准）也拒跑', g.writeGate({ method: 'POST', allowWrite: true, ack: '知道了' }).ok === false);
  ok('闸门：GET 不需要开关', g.writeGate({ method: 'GET' }).ok === true && g.writeGate({ method: 'GET', allowWrite: false }).ok === true);

  const gcfg = path.join(tmp, 'cfg_write');
  fs.mkdirSync(gcfg, { recursive: true });
  fs.copyFileSync(path.join(ROOT, 'test/draft/接口配置草稿.json'), path.join(gcfg, '接口.json'));
  const r1 = run(['scripts/api_run.mjs', '--config', gcfg]);
  ok('闸门 CLI：POST 配置不加 --allow-write 直接拒跑', r1.code === 4 && /--allow-write/.test(r1.out), r1.out.slice(0, 160));
  const r1b = run(['scripts/api_run.mjs', '--config', gcfg, '--go', '--allow-write']);
  ok('闸门 CLI：加了 --allow-write 但没 --ack 仍拒跑（exit 5）', r1b.code === 5 && /批准/.test(r1b.out), r1b.out.slice(0, 160));
  const r2 = run(['scripts/api_run.mjs', '--config', gcfg, '--dry']);
  ok('自检：api_run 带四项自检（走 stderr，不污染 JSON）', fs.readFileSync(path.join(ROOT, 'scripts/api_run.mjs'), 'utf8').includes('自检：数据归属'));
  {
    const md = fs.readFileSync(path.join(ROOT, 'SKILL.md'), 'utf8');
    ok('文档：有安装前确认清单（8 项打勾）', md.includes('安装前确认清单') && md.includes('缺一项别装'));
    ok('文档：有零依赖声明', md.includes('零外部 npm / pip 包依赖') && md.includes('没有** `package.json`'));
    ok('文档：terminal 权限逐条说明', md.includes('到底能跑什么') && md.includes('不执行任意用户命令'));
    {
    const r = run(['scripts/manage.mjs', 'clean', '--all']);
    ok('清理：--all 不带 --yes 拒跑（exit 4）', r.code === 4 && /--yes/.test(r.out), r.out.slice(0, 120));
    const r0 = run(['scripts/manage.mjs', 'clean']);
    ok('清理：默认清理能跑通（exit 0）', r0.code === 0 && /台账|清理/.test(r0.out), r0.out.slice(0, 120));
    const md2 = fs.readFileSync(path.join(ROOT, 'SKILL.md'), 'utf8');
    ok('文档：逐个列出 15 个脚本白名单', (md2.match(/`(record|evidence|probe|diffrec|infer_params|interview|build_skill|run|api_run|login|manage|diagnose)\.mjs`/g) || []).length >= 12);
    {
    const md3 = fs.readFileSync(path.join(ROOT, 'SKILL.md'), 'utf8');
    ok('文档：风险须知含「复制内容」风险 + 关闭方式', md3.includes('会记录你「复制」的页面文本') && md3.includes('--no-copy-text'));
    ok('文档：含人工审批四环节', md3.includes('人工审批建议') && md3.includes('写操作确认.log'));
    {
    const rec = fs.readFileSync(path.join(ROOT, 'scripts/record.mjs'), 'utf8');
    const rn = fs.readFileSync(path.join(ROOT, 'scripts/run.mjs'), 'utf8');
    ok('提醒：record.mjs 跑完提示清理命令', rec.includes('用完就清') && rec.includes('clean --days 0'));
    ok('提醒：run.mjs 跑完提示清理命令', rn.includes('用完就清') && rn.includes('clean --days 0'));
    ok('提醒：两处都提到加密留存', rec.includes('7z a -p -mhe=on') && rn.includes('7z a -p -mhe=on'));
  }
  {
    const md4 = fs.readFileSync(path.join(ROOT, 'SKILL.md'), 'utf8');
    ok('权限：frontmatter why 写清 powershell 只是固定模板', /why:[^\n]*remote-debugging-port/.test(md4));
    ok('审计：frontmatter 有 audit 字段（写操作日志 append-only）', /audit:[^\n]*append-only/.test(md4));
    ok('风险等级：风险须知 5 条都标 🟡', (md4.match(/\d\. \u{1F7E1}/gu) || []).length >= 5);
    ok('凭证：写明禁止用环境变量/.env 存账密', md4.includes('不要把账密写进环境变量'));
  }
  ok('文档：含安装前置条件章节', md3.includes('安装前置条件'));
    ok('版本号：语义化 1.0.20 + build 时间戳', /^version: \d+\.\d+\.\d+$/m.test(md3) && /^build: "\d{14}"$/m.test(md3));
    ok('录制：--no-copy-text 已实现脱敏', fs.readFileSync(path.join(ROOT, 'assets/recorder.js'), 'utf8').includes('redactCopy'));
  }
  ok('文档：有数据管理 5 条 + 必要性说明', md2.includes('数据管理（使用中必须守的 5 条）') && md2.includes('为什么必须读登录态'));
  }
  ok('文档：写操作三道关写清 --ack', md.includes('--ack') && md.includes('写操作确认.log'));
  }
  ok('自检：--dry 的 stdout 仍是纯 JSON', (() => { try { JSON.parse(r2.out); return true; } catch { return false; } })());
  ok('自检：run.mjs 也带同一行', fs.readFileSync(path.join(ROOT, 'scripts/run.mjs'), 'utf8').includes('自检：数据归属'));
  ok('闸门 CLI：--dry 预览不受影响', r2.code === 0 && /POST/.test(r2.out), r2.out.slice(0, 160));
}


/* ---------- 子包 lib 完整性（曾经漏拷 guard/heal，import 直接崩） ---------- */
{
  const libsOf = src => [...fs.readFileSync(src, 'utf8').matchAll(/from '\.\/lib-([\w.-]+)'/g)].map(m => m[1]);
  const apiLibs = libsOf(path.join(ROOT, 'scripts', 'api_run.mjs'));
  const uiLibs = libsOf(path.join(ROOT, 'scripts', 'run.mjs'));
  ok('子包（api 版）依赖库齐全', apiLibs.length > 0 && apiLibs.every(f => fs.existsSync(path.join(ROOT, 'produced/_t_v2/scripts/lib-' + f))), apiLibs.join(','));
  ok('子包（api 版）带写接口闸门 guard.mjs', fs.existsSync(path.join(ROOT, 'produced/_t_v2/scripts/lib-guard.mjs')));
  const uib = run(['scripts/build_skill.mjs', '--link', '_t_lib', '--config', 'test/草稿']);
  ok('子包（ui 版）能生成', uib.code === 0, uib.out.slice(-200));
  ok('子包（ui 版）依赖库齐全（含自愈 heal.mjs）', uiLibs.every(f => fs.existsSync(path.join(ROOT, 'produced/_t_lib/scripts/lib-' + f))), uiLibs.join(','));
  ok('草稿链路有填值步 → 不出农场脚本（不出半截）', !fs.existsSync(path.join(ROOT, 'produced/_t_lib/农场脚本.json')) && /农场脚本：不出/.test(uib.out), uib.out.match(/农场脚本：.*/)?.[0] || '(没打原因)');
}

/* ---------- ⑩b UI 版出包 → 农场脚本.json（2026-11-14 纯点击链路） ---------- */
{
  const fu = path.join(ROOT, 'test/_out/farmui');
  fs.mkdirSync(fu, { recursive: true });
  fs.writeFileSync(path.join(fu, '链路就绪.json'), JSON.stringify({ link: '_t_farm', ok: true }, null, 1));
  fs.writeFileSync(path.join(fu, '映射字典.csv'), '源列,目标列,依据\n消耗,花费,直接\n');
  fs.writeFileSync(path.join(fu, '定位库.csv'),
    '步骤,动作,标签,值,best定位,L1_id,L4_text,L5_css,页面\r\n' +
    '1,nav,,,https://demo.example.com/list,,,https://demo.example.com/list\r\n' +
    '2,click,导出,,#exp,#exp,导出报表,button.btn,https://demo.example.com/list\r\n' +
    '3,download,,,"a[href=""/e.csv""]",,,,https://demo.example.com/list\r\n');
  const fb = run(['scripts/build_skill.mjs', '--link', '_t_farm', '--config', 'test/_out/farmui']);
  ok('纯点击链路 UI 版出包成功', fb.code === 0, fb.out.slice(-200));
  const farmFile = path.join(ROOT, 'produced/_t_farm/农场脚本.json');
  ok('农场脚本.json 跟着子包交付', fs.existsSync(farmFile));
  const farmSc = fs.existsSync(farmFile) ? JSON.parse(fs.readFileSync(farmFile, 'utf8')) : null;
  ok('农场脚本步数=2（nav 不占步）', farmSc && farmSc.steps.length === 2, farmSc && farmSc.steps.length);
  ok('农场脚本 locs 直译（#id→text→css；css best 走 path=）',
    farmSc && JSON.stringify(farmSc.steps[0].locs) === JSON.stringify(['#exp', 'text=导出报表', 'path=button.btn'])
      && farmSc.steps[1].selector === 'path=a[href="/e.csv"]',
    farmSc && JSON.stringify(farmSc.steps.map(s => s.locs)));
  ok('农场脚本步带 href（farm 自动开回）', farmSc && farmSc.steps.every(s => s.href === 'https://demo.example.com/list'));
}

/* ---------- 收尾：清掉测试产物 + 还原台账（测试不许在台账留假链路） ---------- */
if (ledgerBak) fs.writeFileSync(ledger, ledgerBak);
fs.rmSync(path.join(ROOT, 'produced', '_t_v2'), { recursive: true, force: true });
fs.rmSync(path.join(ROOT, 'produced', '_t_notpl'), { recursive: true, force: true });
for (const d of ['_t_iv', '_t_notrig', '_t_notrig2', '_t_lib', '_t_farm']) fs.rmSync(path.join(ROOT, 'produced', d), { recursive: true, force: true });
const zips = fs.existsSync(path.join(ROOT, 'zip')) ? fs.readdirSync(path.join(ROOT, 'zip')).filter(f => f.startsWith('_t_')) : [];
for (const z of zips) fs.rmSync(path.join(ROOT, 'zip', z), { force: true });
fs.rmSync(path.join(ROOT, 'test', '_out'), { recursive: true, force: true });

console.log(`\nforge v2 test：${pass} 过 / ${fail} 挂`);
process.exit(fail ? 1 : 0);
