/* login.mjs — 独立账密登录通道（无人值守的前提）
 * 为什么需要它：
 *   只靠「复用你已经登录的浏览器」= 永远离不开人；机器重启/cookie 过期，链路就死。
 *   这里给这个站点开一个**专属 user-data-dir**（profile），用账密登一次，登录态就存在这个目录里，
 *   以后 api_run / run 都带 --profile 指同一个目录，就能无人值守跑。
 *
 * 用法：
 *   set SF_USER=你的账号 & set SF_PASS=你的密码        （推荐：密码走环境变量，不进命令行历史）
 *   node scripts/login.mjs --url https://xxx.com/login --profile chrome_profile_xxx \
 *        [--user %SF_USER%] [--pass %SF_PASS%] [--port 18803] \
 *        [--user-sel "#username"] [--pass-sel "input[type=password]"] [--submit-sel "button[type=submit]"] \
 *        [--success-url /home] [--success-sel ".user-avatar"] [--timeout 90] [--bg] [--save 配置/登录.json]
 *
 * 铁律：
 *   - 密码只从环境变量/参数读，**绝不写盘**；保存的登录.json 只存 profile 路径 + 选择器 + 校验方式
 *   - 登录成功必须有证据（URL 到了 success-url 或 success-sel 出现），否则 exit 2，不许假装成功
 * 退出码：0 成功 / 2 登录没成功 / 3 浏览器或页面失败 / 4 参数有问题
 */
import path from 'node:path';
import fs from 'node:fs';
import { ensureChrome, Cdp, sleep, closeChromeByPort } from './lib-cdp.mjs';

const arg = (k, d) => { const i = process.argv.indexOf('--' + k); return i >= 0 ? process.argv[i + 1] : d; };
const flag = k => process.argv.includes('--' + k);

const url = arg('url');
const port = Number(arg('port', '18803'));
const profileArg = arg('profile', `chrome_profile_${new URL(url || 'http://x').host.replace(/[^\w.-]/g, '_')}`);
const profile = path.resolve(profileArg);
const user = arg('user', process.env.SF_USER || '');
const pass = arg('pass', process.env.SF_PASS || '');
const timeout = Number(arg('timeout', '90')) * 1000;

if (!url) { console.error('缺 --url（登录页地址）'); process.exit(4); }
if (!user || !pass) {
  console.error('缺账号或密码：设环境变量 SF_USER / SF_PASS（推荐），或 --user / --pass（会进命令行历史，不推荐）');
  process.exit(4);
}
if (!fs.existsSync(profile)) fs.mkdirSync(profile, { recursive: true });

const host = new URL(url).host;

/* 候选选择器：没指定就按常见形态试，命中哪个用哪个 */
const USER_CANDS = [arg('user-sel'), '#username', '#userName', 'input[name="username"]', 'input[name="userName"]',
  'input[name="account"]', 'input[name="loginName"]', 'input[type="text"]', 'input[type="tel"]', 'input[type="email"]'];
const PASS_CANDS = [arg('pass-sel'), 'input[type="password"]', 'input[name="password"]', '#password'];
const SUB_CANDS = [arg('submit-sel'), 'button[type="submit"]', '.login-btn', '.btn-login', '#loginBtn',
  'button:has-text("登录")', 'button:has-text("登 录")', 'input[type="submit"]'];

async function pick(cdp, cands, label) {
  for (const s of cands.filter(Boolean)) {
    const ok = await cdp.evalJs(`(() => { const e = document.querySelector(${JSON.stringify(s)});
      if (!e) return false; const r = e.getBoundingClientRect();
      return r.width > 0 && r.height > 0 && !e.disabled; })()`);
    if (ok) return s;
  }
  /* 兜底：按可见文本找按钮 */
  if (label === 'submit') {
    for (const t of ['登录', '登 录', '立即登录', 'Sign in', 'Log in']) {
      const hit = await cdp.evalJs(`(() => {
        const bs = [...document.querySelectorAll('button,a,[role=button]')].filter(b => b.offsetParent &&
          (b.textContent || '').trim().replace(/\\s+/g, '') === ${JSON.stringify(t.replace(/\s+/g, ''))});
        return bs.length ? true : false; })()`);
      if (hit) return `text=${t}`;
    }
  }
  return '';
}

async function typeInto(cdp, sel, text, label) {
  const focused = await cdp.evalJs(`(() => {
    const e = document.querySelector(${JSON.stringify(sel)});
    if (!e) return 'no-el';
    e.scrollIntoView({ block: 'center' });
    e.focus(); e.click();
    if (e.setSelectionRange) try { e.setSelectionRange(0, (e.value || '').length); } catch {}
    return document.activeElement === e || document.activeElement?.closest?.('label') ? 'ok' : 'not-focused';
  })()`);
  if (focused === 'no-el') throw new Error(`找不到${label}输入框：${sel}`);
  await cdp.send('Input.insertText', { text });
  await sleep(120);
  const got = await cdp.evalJs(`(() => { const e = document.querySelector(${JSON.stringify(sel)}); return e ? String(e.value || '').length : -1; })()`);
  if (got <= 0) throw new Error(`${label}没输进去（长度为 0）：${sel}`);
  return got;
}

async function pressEnter(cdp) {
  for (const type of ['keyDown', 'keyUp']) {
    await cdp.send('Input.dispatchKeyEvent', { type, key: 'Enter', code: 'Enter', windowsVirtualKeyCode: 13, nativeVirtualKeyCode: 13 });
  }
}

const log = (...a) => console.log('[login]', ...a);

try {
  log(`浏览器：port=${port} profile=${profile}（专属目录，登录态存这里）`);
  await ensureChrome({ port, profile, mode: flag('bg') ? 'bg' : 'watch' });
  log(`打开登录页：${url}`);
  /* Chrome 刚起来时第一个标签的 ws 常常还没就绪，Page.enable 会超时 —— 重试几次，别当成登录失败 */
  let cdp = null, lastErr = '';
  for (let i = 1; i <= 5; i++) {
    try {
      cdp = await Cdp.attach({ port, url, urlPart: host || 'about:blank' });
      await cdp.enableSession();
      break;
    } catch (e) {
      lastErr = e.message;
      try { cdp?.close(); } catch {}
      cdp = null;
      log(`调试口还没就绪（第 ${i}/5 次）：${e.message}，1.5s 后重试`);
      await sleep(1500);
    }
  }
  if (!cdp) throw new Error(`连不上调试口 ${port}：${lastErr}`);
  await cdp.send('Page.navigate', { url });
  /* 等 DOM 可用（不依赖 load 事件，单页面应用常常 load 了也还没渲染完） */
  for (let i = 0; i < 60; i++) {
    await sleep(500);
    const ready = await cdp.evalJs(`(() => document.readyState !== 'loading' && !!document.body)()`).catch(() => false);
    if (ready) break;
  }

  const userSel = await pick(cdp, USER_CANDS, 'user');
  const passSel = await pick(cdp, PASS_CANDS, 'pass');
  const subSel = await pick(cdp, SUB_CANDS, 'submit');
  if (!userSel) throw new Error('找不到账号输入框：用 --user-sel 指定（F12 复制 selector）');
  if (!passSel) throw new Error('找不到密码输入框：用 --pass-sel 指定');
  log(`选择器：账号=${userSel} 密码=${passSel} 提交=${subSel || '（回车提交）'}`);

  await typeInto(cdp, userSel, user, '账号');
  await typeInto(cdp, passSel, pass, '密码');
  log('已填入账号密码（密码不回显、不落盘）');

  const urlBefore = await cdp.evalJs('location.href');
  if (subSel) {
    if (String(subSel).startsWith('text=')) {
      const t = subSel.slice(5);
      await cdp.evalJs(`(() => {
        const bs = [...document.querySelectorAll('button,a,[role=button]')].filter(b => b.offsetParent &&
          (b.textContent || '').trim().replace(/\\s+/g, '') === ${JSON.stringify(t.replace(/\s+/g, ''))});
        if (bs[0]) { bs[0].click(); return true; } return false; })()`);
    } else {
      await cdp.evalJs(`(() => { const e = document.querySelector(${JSON.stringify(subSel)}); if (!e) return false; e.click(); return true; })()`);
    }
    log('已点提交');
  } else {
    await pressEnter(cdp);
    log('已回车提交');
  }

  /* 成功判定：URL 变化 / success-url / success-sel；同时盯错误提示，错就早退 */
  const successUrl = arg('success-url', '');
  const successSel = arg('success-sel', '');
  const ERR_SEL = '.error, .login-error, #err, #error, .el-message--error, .ant-message-error, [class*="error-tip"], [class*="err-msg"], [id*="err-msg"]';
  let verified = '', errText = '', lastUrl = '';
  const t0 = Date.now();
  while (Date.now() - t0 < timeout) {
    await sleep(1000);
    const st = await cdp.evalJs(`(() => ({
      url: location.href,
      ready: document.readyState,
      succ: ${JSON.stringify(successSel)} ? !!document.querySelector(${JSON.stringify(successSel)}) : false,
      err: (() => { const e = document.querySelector(${JSON.stringify(ERR_SEL)}); return e && e.offsetParent ? (e.textContent || '').trim().slice(0, 120) : ''; })()
    }))()`).catch(() => null);
    if (!st) continue;
    lastUrl = st.url;
    if (st.err) { errText = st.err; break; }
    if (successSel && st.succ) { verified = `success-sel 出现：${successSel}`; break; }
    if (successUrl && st.url.includes(successUrl)) { verified = `URL 到达：${successUrl}`; break; }
    if (!successUrl && !successSel && st.url !== urlBefore && !st.url.includes('/login')) { verified = `URL 已离开登录页：${st.url.slice(0, 120)}`; break; }
  }

  if (!verified) {
    console.error(`✗ 登录没成功${errText ? `：${errText}` : ''}`);
    console.error(`  当前停在：${lastUrl || '(取不到)'}`);
    console.error('  排查：① 选择器对不对 ② 有没有验证码/短信（有的话这条路走不通，得换扫码或 API token）③ 账号权限');
    if (successSel || successUrl) console.error('  再跑一次可直接加 --success-sel / --success-url 精确判定');
    if (!process.argv.includes('--keep-open')) { try { closeChromeByPort(port, { log: () => {} }); } catch { /* ignore */ } }
    process.exit(2);
  }

  /* 落盘：只存 profile + 选择器 + 判定方式；账号打码，密码不存 */
  const saveTo = arg('save', '配置/登录.json');
  const savePath = path.resolve(saveTo);
  fs.mkdirSync(path.dirname(savePath), { recursive: true });
  const mask = user.length <= 2 ? '*'.repeat(user.length) : user.slice(0, 2) + '*'.repeat(Math.max(2, user.length - 2));
  const info = {
    站点: host, 登录页: url, profile: profile.replace(/\\/g, '/'),
    选择器: { user: userSel, pass: passSel, submit: subSel || '(Enter)' },
    校验: { successUrl, successSel }, 账号: mask,
    verifiedAt: new Date().toISOString(), verifiedBy: verified,
    用法: `node scripts/api_run.mjs --config 配置 --profile "${profile.replace(/\\/g, '/')}" --bg`
  };
  fs.writeFileSync(savePath, JSON.stringify(info, null, 1), 'utf8');

  log(`✓ 登录成功（${verified}）`);
  log(`  登录态已存在：${profile.replace(/\\/g, '/')}`);
  log(`  回执：${savePath}`);
  log(`  下一步：api_run 带 --profile "${profile.replace(/\\/g, '/')}" --bg 即可无人值守`);
  cdp.close();
  /* 收尾：登录态已落进 profile，浏览器当场关（--keep-open 才留） */
  if (!process.argv.includes('--keep-open') && process.env.KEEP_BROWSER !== '1') closeChromeByPort(port);
} catch (e) {
  console.error(`✗ 登录流程出错：${e.message}`);
  try { if (!process.argv.includes('--keep-open')) closeChromeByPort(port, { log: () => {} }); } catch { /* ignore */ }
  process.exit(3);
}
