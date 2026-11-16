// 人用的菜单控制台（双击 启动农场.bat 进来）。全部操作转手给 farm.js，
// 自己不碰 HTTP 和 Chrome——菜单坏了 agent 用法也不受影响。agent 直接用命令行，见 README.md。
'use strict';
const { spawnSync } = require('child_process');
const path = require('path');
const readline = require('readline');

const FARM = path.join(__dirname, 'farm.js');

// 调 farm.js 并把输出原样带回来
function run(args) {
  const r = spawnSync(process.execPath, [FARM, ...args], { encoding: 'utf8' });
  let out = (r.stdout || '').trim();
  if (r.stderr && r.stderr.trim()) out += '\n[stderr] ' + r.stderr.trim();
  return out || '(无输出)';
}

// 档位一行一条给人看；解析不了就原样倒 JSON 出来，不吞
function showSlots() {
  const raw = run(['slots']);
  try {
    const res = JSON.parse(raw.replace(/\[stderr\][\s\S]*$/, ''));
    if (!res.slots || !res.slots.length) {
      console.log('  还没有档位。菜单选 2 登记一个，或让 agent 跑: node farm.js add "备注"');
      return;
    }
    console.log('  编号  端口   状态    备注');
    for (const s of res.slots) {
      console.log('  ' + String(s.id).padEnd(4) + ' ' + String(s.port).padEnd(6) + ' ' + (s.alive ? '运行中' : '已停  ') + '  ' + (s.note || ''));
    }
  } catch (e) {
    console.log(raw);
  }
}

// 不用 rl.question：它对快速到达的多行输入会丢行（管道必丢，手快连按也会）。
// 自己排队列：先到的行存着，ask 来了直接取。
const rl = readline.createInterface({ input: process.stdin, output: process.stdout });
const pendingLines = [];
let lineWaiter = null;
rl.on('line', l => {
  const t = l.trim();
  if (lineWaiter) { const w = lineWaiter; lineWaiter = null; w(t); }
  else pendingLines.push(t);
});
rl.on('close', () => process.exit(0)); // 输入流关了（关窗口/Ctrl+C）直接走，不留半截菜单

function ask(prompt) {
  return new Promise(r => {
    process.stdout.write(prompt);
    if (pendingLines.length) return r(pendingLines.shift());
    lineWaiter = r;
  });
}

async function menu() {
  while (true) {
    console.log('\n════════ 浏览器农场控制台 ════════');
    console.log(' 1. 看全部档位');
    console.log(' 2. 登记新档位');
    console.log(' 3. 启动档位（无窗口干活）');
    console.log(' 4. 登录档位（弹真窗口，扫码/输验证码）');
    console.log(' 7. 效率启动档位（无窗口+拦广告域名，最省）');
    console.log(' 5. 停止档位');
    console.log(' 6. 档位详情（含打开的页面）');
    console.log(' 0. 退出（总管和档位留后台，agent 照常能用）');
    const c = await ask('选: ');
    try {
      if (c === '0') break;
      if (c === '1') { showSlots(); continue; }
      if (c === '2') {
        const note = await ask('备注（写账号名，回车=不写）: ');
        console.log(run(['add', note || '']));
        showSlots();
        continue;
      }
      const id = await ask('档位编号（如 01，直接回车=取消）: ');
      if (!id) continue;
      if (c === '3') { console.log(run(['start', id])); showSlots(); }
      else if (c === '7') { console.log(run(['start', id, '--eff'])); showSlots(); }
      else if (c === '4') {
        console.log(run(['login', id]));
        console.log('提示: 登完关掉弹出的浏览器窗口 → 回这里选 5 停止 → 再选 3 启动，就切回无窗口干活模式。');
      }
      else if (c === '5') { console.log(run(['stop', id])); showSlots(); }
      else if (c === '6') console.log(run(['status', id]));
      else console.log('没这个选项: ' + c);
    } catch (e) {
      console.log('出错了（不影响后台总管）: ' + e.message);
    }
  }
  console.log('再见。');
  process.exit(0);
}
menu();
