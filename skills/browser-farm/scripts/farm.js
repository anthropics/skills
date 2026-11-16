// 浏览器农场命令行：用法见 README.md。总管没起会自动拉起。
'use strict';
const http = require('http');
const fs = require('fs');
const path = require('path');
const readline = require('readline');
const { spawn } = require('child_process');
const scripter = require('./scripter');

const PORT = Number(process.env.FARM_PORT || 9300);
const SUPERVISOR = path.join(__dirname, 'supervisor.js');

function api(method, p, body) {
  return new Promise((resolve, reject) => {
    const data = body ? JSON.stringify(body) : null;
    const req = http.request({
      host: '127.0.0.1', port: PORT, path: p, method,
      headers: data ? { 'Content-Type': 'application/json', 'Content-Length': Buffer.byteLength(data) } : {},
      timeout: 120000, // eval/快照可能慢
    }, res => {
      let d = '';
      res.on('data', c => d += c);
      res.on('end', () => { try { resolve(JSON.parse(d)); } catch (e) { reject(new Error('总管回话不是 JSON: ' + d.slice(0, 200))); } });
    });
    req.on('timeout', () => req.destroy(new Error('请求超时（2 分钟）')));
    req.on('error', reject);
    if (data) req.write(data);
    req.end();
  });
}

async function ensureDaemon() {
  try { return await api('GET', '/health'); } catch (e) {}
  // 拉起常驻总管（脱离本进程，不随 CLI 退出）
  const child = spawn(process.execPath, [SUPERVISOR], {
    detached: true, stdio: 'ignore', windowsHide: true,
    env: process.env,
  });
  child.unref();
  for (let i = 0; i < 20; i++) {
    await new Promise(r => setTimeout(r, 300));
    try { return await api('GET', '/health'); } catch (e) {}
  }
  throw new Error('总管起不来，手动跑一下看报错: node ' + SUPERVISOR);
}

function out(res) {
  console.log(JSON.stringify(res, null, 2));
  if (!res || res.ok === false) process.exit(1);
}

function die(msg) { console.error(msg); process.exit(1); }
function argFlag(name) { return process.argv.includes(name); }
function argVal(name, def) {
  const i = process.argv.indexOf(name);
  return i >= 0 && i + 1 < process.argv.length ? process.argv[i + 1] : def;
}
function ask(q) {
  const rl = readline.createInterface({ input: process.stdin, output: process.stdout });
  return new Promise(r => rl.question(q, a => { rl.close(); r(a.trim()); }));
}

async function main() {
  const [, , cmd, a, b, c] = process.argv;
  if (!cmd) die([
    '用法: node farm.js <命令>',
    '  slots                      看全部档位+死活',
    '  add "备注"                 登记新档位（自动分配端口）',
    '  start <id> [--eff]         无窗口启动（--eff=效率模式：再拦广告/埋点域名+禁远端字体，最省）',
    '  login <id>                 有窗口启动（扫码/验证码用，完事后 stop 再 start）',
    '  stop <id> | restart <id>    停（连档上的脚本一起）| 重启（脚本靠重连窗活着穿过）',
    '  open <id> <url>            开一页，返回 targetId',
    '  eval <id> [--target tid] "代码" | --file xx.js',
    '  structured <id> [--target tid]   当前页结构化数据一把抓（og/json-ld/meta/description）',
    '  status <id>                档位详情+页面列表',
    '  snap <id> <名> | restore <id> <名>',
    '  remove <id> [--wipe]       移除登记（--wipe 连数据目录一起删）',
    '  sniff <id> start|stop      抓包：start 开录页面背后的接口，stop 出清单',
    '  replay <id> <url> [--method M] [--data D] [--header k:v]  带档位登录态脱离浏览器重放',
    '  record <id> [--name 名字] [--agent]  录制点击路径（窗口右下角常驻条开录/停，Ctrl+C 也收）；--agent=不存脚本，存 agent-notes/ 笔记',
    '  forge <id[,id..]> <forge脚本名> [参数..]  forge(record-to-skill) 挂档位口跑：免登录录制/探查/纯接口（--forge-dir 指 forge 目录）',
    '  forge-rec <脚本id | 笔记.md>   农场录制产物转 forge 的 rec.json，喂它的 evidence/probe/build 管线',
    '  build <id>                     数据触发向导（消费≥300点暂停这种）',
    '  runscript <脚本id> [档位id] [--loop N] [--once] [--dry]   后台执行（关终端也跑；档位没给用绑定的）',
    '  stopscript <脚本id> | scripts | showscript <脚本id>',
    '  delscript <脚本id>   删脚本（跑着不给删，先 stopscript）',
    '  newscript <名字> <步骤.json>   写脚本（agent 用）：json 交农场校验落盘，跟录的同待遇（可带 bindSlot/desc）',
    '  bind <脚本id> <档位id|-> [一句话说明]   绑定/解绑 skill 到档位（绑了启动不用再选档，- = 解绑）',
    '  export [文件] | import <文件>   配置搬家：档位登记+全部脚本（登录态不跟走，另一台各档登一次）',
    '  fixchrome                  Chrome 门卫：清占默认目录的无头残留（桌面 Chrome 点不开就跑它）',
  ].join('\n'));
  await ensureDaemon();
  if (cmd === 'slots') return out(await api('GET', '/slots'));
  if (cmd === 'status') return out(await api('GET', '/slot/' + a));
  if (cmd === 'add') return out(await api('POST', '/slots/add', { note: a || '' }));
  if (cmd === 'start') return out(await api('POST', '/slot/' + a + '/start', argFlag('--eff') ? { mode: 'eff' } : {}));
  if (cmd === 'login') {
    if (a) { try { await api('POST', '/slot/' + a + '/stop', {}); } catch (e) {} }
    return out(await api('POST', '/slot/' + a + '/start', { mode: 'headful' }));
  }
  if (cmd === 'stop') return out(await api('POST', '/slot/' + a + '/halt', {})); // halt：连档上跑着的脚本一起真停（看护在，纯 stop 会被脚本拉活回来）
  if (cmd === 'restart') return out(await api('POST', '/slot/' + a + '/restart', {}));
  if (cmd === 'open') return out(await api('POST', '/slot/' + a + '/open', { url: b }));
  if (cmd === 'snap') return out(await api('POST', '/slot/' + a + '/snapshot', { name: b }));
  if (cmd === 'restore') return out(await api('POST', '/slot/' + a + '/restore', { name: b }));
  if (cmd === 'remove') return out(await api('POST', '/slot/' + a + '/remove', { wipe: process.argv.includes('--wipe') }));
  if (cmd === 'sniff') {
    if (!a) die('sniff 要档位 id 和动作: sniff 01 start / sniff 01 stop');
    return out(await api('POST', '/slot/' + a + '/sniff', { action: b || 'start' }));
  }
  if (cmd === 'replay') {
    if (!a || !b) die('replay 要档位 id 和 url: replay 01 https://... [--method POST --data xx]');
    const args = process.argv.slice(4);
    const req = { url: b, method: 'GET', headers: {} };
    for (let i = 0; i < args.length; i++) {
      if (args[i] === '--method') req.method = args[++i];
      else if (args[i] === '--data') req.data = args[++i];
      else if (args[i] === '--header') { const kv = args[++i].split(':'); req.headers[kv[0].trim()] = kv.slice(1).join(':').trim(); }
    }
    return out(await api('POST', '/slot/' + a + '/replay', req));
  }
  if (cmd === 'scripts') {
    const r = await api('GET', '/scripts');
    if (!r.scripts.length) { console.log('还没有脚本：record 录路径 / build 建数据触发'); return; }
    for (const s of r.scripts) {
      const desc = s.type === 'watch'
        ? '盯「' + s.watch.rowText + '」' + s.watch.columnHeader + ' ' + (s.watch.op || '>=') + ' ' + s.watch.value + ' → 点「' + s.watch.clickText + '」'
        : s.steps.length + ' 步循环' + ((s.steps || []).some(x => x && x.href) ? '·自动开页' : '') + '（' + s.steps.map(x => x.text || x.selector).join('→').slice(0, 36) + '）';
      const run = r.runs[s.id];
      console.log('  ' + s.id + '  [' + (s.type === 'watch' ? '数据触发' : '路径循环') + '] ' + s.name + (s.bindSlot ? ' [绑档' + s.bindSlot + ']' : '') + '  ' + (s.desc || desc) + (run ? '\n      ▶ ' + run.state + (run.lastMsg ? ' | ' + run.lastMsg : '') : ''));
    }
    return;
  }
  if (cmd === 'showscript') {
    if (!a) die('showscript 要脚本 id');
    return out(scripter.loadScript(a));
  }
  if (cmd === 'record') {
    if (!a) die('record 要档位 id');
    const name = argVal('--name') || await ask('这个脚本叫什么：') || '未命名';
    const asAgent = argFlag('--agent'); // 停止时不建脚本，存 agent-notes/ 的 md 笔记给 agent 读
    const startedAt = Date.now();
    let r;
    try { r = await api('POST', '/slot/' + a + '/record', { action: 'start', name }); }
    catch (e) { return die('开录失败: ' + e.message); }
    if (!r.ok) return die(r.error || '开录失败');
    console.log('录制中：去档 ' + a + ' 的窗口里点（新开标签页也录）；窗口右下角「■ 停止并保存」，或这里 Ctrl+C。');
    let stopped = false;
    process.on('SIGINT', async () => {
      if (stopped) return; stopped = true;
      console.log('\n收到 Ctrl+C，停止并保存…');
      try {
        const st = await api('POST', '/slot/' + a + '/record', { action: 'stop', asAgent });
        if (st.ok && st.agentNote) console.log('收工：共录到 ' + st.count + ' 步 → Agent 笔记 ' + st.agentNote);
        else if (st.ok) console.log('收工：共录到 ' + st.count + ' 步 → 脚本 ' + st.script.id + ' ' + st.script.name);
        else console.log(st.error || '没保存上');
      } catch (e) { console.log('停止失败: ' + e.message); }
      process.exit(0);
    });
    // 轮询打计数；录制被别处收了（窗口条/GUI 停的）就按 lastRec 收尾
    let seen = 0;
    for (;;) {
      await new Promise(rr => setTimeout(rr, 1000));
      let s;
      try { s = await api('GET', '/slots'); } catch (e) { continue; }
      if (s.recording && s.recording.count > seen) { seen = s.recording.count; console.log('  已录 ' + seen + ' 下'); }
      if (!s.recording) {
        const lr = s.lastRec;
        if (lr && lr.at >= startedAt - 2000 && lr.aborted) {
          console.log('档 ' + a + ' 的浏览器关了，录制中止没保存（已录 ' + lr.count + ' 步）');
          process.exit(0);
        }
        if (lr && lr.at >= startedAt - 2000 && lr.discarded) {
          console.log('窗口里点了「不存」：丢弃 ' + lr.count + ' 步，没保存');
          process.exit(0);
        }
        if (lr && lr.at >= startedAt - 2000 && lr.agentNote) {
          console.log('窗口里点了「存Agent」：共 ' + lr.count + ' 步 → 笔记 agent-notes/' + lr.agentNote);
          process.exit(0);
        }
        if (lr && lr.at >= startedAt - 2000 && lr.scriptId) {
          console.log('窗口里点了「停止并保存」：共 ' + lr.count + ' 步 → 脚本 ' + lr.scriptId + ' ' + lr.name);
          console.log('试跑: node farm.js runscript ' + lr.scriptId + ' ' + a + ' --dry');
          console.log('真跑: node farm.js runscript ' + lr.scriptId + ' ' + a + ' [--loop 3]');
        } else {
          console.log('录制结束：一步没录到，没保存');
        }
        process.exit(0);
      }
    }
  }
  if (cmd === 'build') {
    if (!a) die('build 要档位 id');
    const info = await api('GET', '/slot/' + a);
    if (!info.alive) { await api('POST', '/slot/' + a + '/start', {}); }
    console.log('建数据触发脚本（例：计划A 消费 ≥ 300 → 点那行的「暂停」）\n');
    const rowText = await ask('① 行识别文字（如 计划A）: ');
    const columnHeader = await ask('② 看哪一列（表头名，如 消费）: ');
    const value = Number(await ask('③ 阈值（如 300）: '));
    const opc = await ask('④ 怎么比 1=达到及以上 2=严格大于 3=小于等于 4=小于 [1]: ');
    const opMap = { '1': '>=', '2': '>', '3': '<=', '4': '<' };
    const clickText = await ask('⑤ 达标后点行里哪个按钮（如 暂停）: ');
    const sec = Number(await ask('⑥ 多久查一次秒 [10]: ') || 10);
    const w = { mode: 'cell', rowText, columnHeader, op: opMap[opc] || '>=', value, clickText, intervalMs: sec * 1000, cooldownMs: 3000 };
    const sc = {
      id: scripter.nextId(), name: rowText + columnHeader + (opMap[opc] || '>=') + value + '点' + clickText,
      type: 'watch', watch: w, clickJitter: 0.4, created: new Date().toISOString(),
    };
    // 存之前先在档位上试跑一次，盯得住才存
    try {
      const cdp = await scripter.attachPage(info.port);
      const ev = await cdp.send('Runtime.evaluate', { expression: scripter.cellWatchExpr(w), returnByValue: true });
      const r = ev.result.value || {};
      if (r.hit) console.log('试跑 ✓ 现在就达标: num=' + r.num + '，会点「' + r.text + '」');
      else if (r.num !== undefined) console.log('试跑 ✓ 盯得住: 当前列值 ' + r.num + '（未达 ' + w.op + ' ' + w.value + '）');
      else console.log('试跑 ✗ 盯不住: ' + (r.why || '页面里没找到'));
      cdp.close();
    } catch (e) { console.log('试跑没做成: ' + e.message); }
    console.log('已存 ' + scripter.saveScript(sc));
    console.log('跑: node farm.js runscript ' + sc.id + ' ' + a + '（挂总管后台，关终端也盯）');
    return;
  }
  if (cmd === 'runscript') {
    const scId = a;
    if (!scId) die('runscript 要 脚本id [档位id（脚本没绑定时必须给）]');
    scripter.loadScript(scId); // 早炸：脚本不存在马上报
    let slotId = b;
    if (!slotId) { // 档位没给：用脚本绑定的档
      const sc = scripter.loadScript(scId);
      if (!sc.bindSlot) die('这个脚本没绑档位：runscript ' + scId + ' 档位id，或先 bind ' + scId + ' 档位id');
      slotId = sc.bindSlot;
      console.log('（用绑定的档 ' + slotId + '）');
    }
    if (argFlag('--dry')) {
      const info = await api('GET', '/slot/' + slotId);
      const sc = scripter.loadScript(scId);
      await scripter.runScript(sc, {
        port: info.port,
        loop: argVal('--loop') !== undefined ? Number(argVal('--loop')) : undefined,
        once: argFlag('--once'), dry: true,
        onLog: m => console.log(m),
      }, () => false);
      return;
    }
    const r = await api('POST', '/script/' + scId + '/start', {
      slot: slotId,
      loop: argVal('--loop') !== undefined ? Number(argVal('--loop')) : undefined,
      once: argFlag('--once'),
    });
    console.log('已在总管后台起跑（关终端也继续）: ' + JSON.stringify(r));
    console.log('看状态: node farm.js scripts   停: node farm.js stopscript ' + scId);
    return;
  }
  if (cmd === 'stopscript') {
    if (!a) die('stopscript 要脚本 id');
    return out(await api('POST', '/script/' + a + '/stop', {}));
  }
  if (cmd === 'delscript') {
    if (!a) die('delscript 要脚本 id');
    return out(await api('POST', '/script/' + a + '/delete', {}));
  }
  if (cmd === 'newscript') {
    if (!a || !b) die('newscript 要名字和 json 文件: newscript "点名下 Zip" steps.json');
    let sc;
    try { sc = JSON.parse(fs.readFileSync(path.resolve(b), 'utf8')); }
    catch (e) { return die('步骤文件读不了（要 utf-8 的 json）: ' + e.message); }
    if (!sc || typeof sc !== 'object') return die('步骤文件内容要是 json 对象');
    return out(await api('POST', '/script/new', { ...sc, name: a || sc.name }));
  }
  if (cmd === 'bind') {
    if (!a || !b) die('bind 要 脚本id 档位id（- = 解绑）[一句话说明]: bind 01 03 "下载资源站包"');
    const body = b === '-' || b === 'none' ? { slot: '' } : { slot: b };
    if (c) body.desc = c;
    return out(await api('POST', '/script/' + a + '/bind', body));
  }
  if (cmd === 'fixchrome') {
    const r = await api('POST', '/chrome/fix', {});
    if (!r.ok) return die(r.error || '门卫没跑成');
    if (r.killed && r.killed.length) {
      console.log('清掉 ' + r.killed.length + ' 个占着 Chrome 默认目录的无头残留（PID: ' + r.killed.join(', ') + '）。');
      console.log('现在点 Chrome 图标应该就能开窗了（还不开再跑一次）。');
    } else {
      console.log('没发现占默认目录的无头残留，Chrome 目录是干净的（扫过 ' + r.found + ' 个 Chrome 进程）。');
    }
    return;
  }
  if (cmd === 'export') {
    const r = await api('GET', '/config/export');
    const file = path.resolve(a || ('farm-config-' + new Date().toISOString().slice(0, 10) + '.json'));
    fs.writeFileSync(file, JSON.stringify(r.payload, null, 2));
    console.log('已导出 ' + r.summary + ' → ' + file);
    console.log('另一台电脑: node farm.js import "' + path.basename(file) + '"');
    return;
  }
  if (cmd === 'import') {
    if (!a) die('import 要配置文件路径（farm.js export 出来的 json）');
    let data;
    try { data = JSON.parse(fs.readFileSync(path.resolve(a), 'utf8')); }
    catch (e) { return die('配置文件读不了: ' + e.message); }
    return out(await api('POST', '/config/import', data));
  }
  if (cmd === 'eval') {
    let target = null, code = null;
    const args = process.argv.slice(3);
    for (let i = 0; i < args.length; i++) {
      if (args[i] === '--target') target = args[++i];
      else if (args[i] === '--file') code = fs.readFileSync(args[++i], 'utf8');
      else code = args[i];
    }
    if (!a) die('eval 要档位 id');
    if (code === null) die('eval 要代码（参数或 --file）');
    return out(await api('POST', '/slot/' + a + '/eval', { code, targetId: target }));
  }
  if (cmd === 'structured') {
    if (!a) die('structured 要档位 id（在当前页上抓 og/json-ld/meta，先 open 到目标页）');
    return out(await api('POST', '/slot/' + a + '/structured', argFlag('--target') ? { targetId: argVal('--target') } : {}));
  }

  // ---- forge 桥：forge(record-to-skill) 的脚本挂到档位口上跑——免登录录制/探查/纯接口 ----
  // 档口和 --keep-open 是桥的产权：口按档位分配，收尾不杀档（forge 默认收尾按端口关浏览器，会把农场档害了）
  if (cmd === 'forge') {
    if (!a) die('用法: node farm.js forge <档位id[,档位id...]> <forge脚本名> [参数...]；forge 目录用 --forge-dir <路径> 或环境变量 FARM_FORGE_DIR 指定');
    const forgeDir = argVal('--forge-dir') || process.env.FARM_FORGE_DIR;
    if (!forgeDir) die('不知道 forge 装在哪：--forge-dir <路径>（forge 技能目录，里面有 scripts/），或设环境变量 FARM_FORGE_DIR');
    const pass = [];
    const raw = process.argv.slice(4);
    for (let i = 0; i < raw.length; i++) { if (raw[i] === '--forge-dir') { i++; continue; } pass.push(raw[i]); } // 桥自用参数不透传给 forge
    const scriptName = pass[0];
    if (!scriptName) die('要指 forge 脚本名：record / api_run / probe / evidence / build_skill / run / login / diffrec / infer_params / interview / manage / diagnose');
    const scriptPath = path.join(path.resolve(forgeDir), 'scripts', scriptName.replace(/\.mjs$/, '') + '.mjs');
    if (!fs.existsSync(scriptPath)) die('forge 里没有这个脚本: ' + scriptPath);
    if (pass.includes('--port')) die('档口由桥按档位分配，别自己传 --port');
    const forgeArgs = pass.slice(1).filter(x => x !== '--keep-open');
    forgeArgs.push('--keep-open'); // 焊死：跑完档留给农场管，不许 forge 收尾杀档
    await ensureDaemon();
    process.on('SIGINT', () => {}); // Ctrl+C 给 forge 自己接（它会存半场收工），桥只管等它退
    for (const sid of a.split(',').map(x => x.trim()).filter(Boolean)) {
      const s0 = (await api('GET', '/slots')).slots.find(x => x.id === sid);
      if (!s0) die('没有这个档位: ' + sid);
      if (!s0.alive) { await api('POST', '/slot/' + sid + '/start', {}); console.log('档 ' + sid + ' 没活着，已拉起'); }
      if (/^record/.test(scriptName) && (await api('GET', '/slot/' + sid)).mode !== 'headful') {
        await api('POST', '/slot/' + sid + '/stop', {}); // 录制要看得见的窗口：切有窗（登录态不丢）
        await api('POST', '/slot/' + sid + '/start', { mode: 'headful' });
        console.log('档 ' + sid + ' 已切有窗口（录制要点得着）');
      }
      const s = (await api('GET', '/slots')).slots.find(x => x.id === sid);
      console.log('\n[' + sid + '] forge ' + path.basename(scriptPath) + ' ' + forgeArgs.join(' ') + ' --port ' + s.port + ' --keep-open');
      const code = await new Promise(resolve => {
        const ch = spawn(process.execPath, [scriptPath, ...forgeArgs, '--port', String(s.port)], { stdio: 'inherit' });
        ch.on('exit', resolve);
      });
      console.log('[' + sid + '] 退出码 ' + code + (code ? '（看上面 forge 的输出找原因）' : '，档位留给农场管（空闲自动停，start 秒回）'));
      if (code) process.exitCode = code;
    }
    return;
  }

  // ---- forge-rec：农场录制产物（脚本 id / 存Agent笔记 md）→ forge 的 rec.json ----
  if (cmd === 'forge-rec') {
    if (!a) die('用法: node farm.js forge-rec <脚本id | agent-notes/笔记.md 路径>');
    let steps, apis, name;
    if (/^\d+$/.test(a)) {
      const sc = scripter.loadScript(a); // 本地读（跟总管同一个 FARM_HOME），脚本里 steps+apis 都全
      steps = sc.steps; apis = sc.apis || []; name = sc.name;
    } else {
      const md = fs.readFileSync(path.resolve(a), 'utf8');
      const jm = md.match(/```json\r?\n([\s\S]*?)```/);
      if (!jm) die('这文件里没找到原始 steps JSON（要存Agent笔记的 md）');
      steps = JSON.parse(jm[1]);
      apis = []; // 笔记里的接口表没有请求体，探查 POST 时要回脚本或重录——够打分用
      const row = /^\|\s*(GET|POST|PUT|DELETE|HEAD|OPTIONS)\s*\|\s*(\d+|\?)\s*\|\s*(\d+)\s*\|\s*(\S+)\s*\|/gm;
      let m; while ((m = row.exec(md))) apis.push({ method: m[1], status: m[2] === '?' ? null : Number(m[2]), count: Number(m[3]), url: m[4], tsUTC: '', postData: null });
      name = (md.match(/^#\s*录制笔记：(.+)$/m) || [])[1] || 'farm-rec';
    }
    if (!Array.isArray(steps) || !steps.length) die('这份里一步都没有，转不了');
    const rec = scripter.toForgeRec(steps, apis, name, null);
    const outDir = path.join(process.env.FARM_HOME || __dirname, 'forge-out');
    fs.mkdirSync(outDir, { recursive: true });
    const safe = String(name).replace(/[\\/:*?"<>|\s]+/g, '').slice(0, 40) || 'farm-rec';
    const file = path.join(outDir, safe + '_' + Date.now() + '.rec.json');
    fs.writeFileSync(file, JSON.stringify(rec, null, 1), 'utf8');
    console.log('已转 forge 录制: ' + file + '（' + rec.actions.length + ' 步 / ' + rec.network.length + ' 条接口）');
    console.log('下一步打分: node <forge>/scripts/evidence.mjs --recording "' + file + '"');
    console.log('下一步探查(挂档口免登录): node farm.js forge 01 probe --recording "' + file + '"');
    return;
  }

  die('不认识的命令: ' + cmd);
}
main().catch(e => die(e.message));
