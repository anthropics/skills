/* interview.mjs — 需求访谈：把「一条录好的路径」问成「一个真能用的自动化」
 *
 * 为什么必须有这一步：录一条「加预算」只会得到「点哪几下」。
 * 什么时候加、加多少、谁批、跑完给谁、失败了找谁 —— 这些录制看不出来，必须问人。
 *
 * 设计原则（2026-11-06 用户定）：**只负责问清楚，不拿模板卡人**。
 *   · 答不上来 / 答得糊 → 记进「待确认」，不拦着往下走（人当时可能真不知道）；
 *   · 但「待确认」会一路跟到子技能 SKILL.md 里，谁接手都看得见还欠什么；
 *   · 想强制问全再生成，加 --strict（不填就 exit 1）—— 默认不强制。
 *
 * 用法：
 *   交互：node scripts/interview.mjs --link <链路名> [--out <配置目录>] [--type api|ui] [--strict]
 *   非交互：node scripts/interview.mjs --link <名> --answers answers.json [--out <配置目录>]
 *   带录制备注：任何方式都可加 --rec recordings/xxx.rec.json（录制时你口述的话会自动带出来，并存进 触发.json）
 * 产物：<out>/触发.json
 * 退出码：0 完成（可能有待确认项）；1 --strict 下仍有待确认；4 参数/文件问题
 */
import fs from 'node:fs';
import path from 'node:path';
import readline from 'node:readline/promises';
import { fileURLToPath } from 'node:url';
import { triggerSection } from './lib-trigger.mjs';

const ROOT = path.resolve(path.dirname(fileURLToPath(import.meta.url)), '..');
const arg = (k, d) => { const i = process.argv.indexOf('--' + k); return i >= 0 ? process.argv[i + 1] : d; };
const flag = k => process.argv.includes('--' + k);

const link = arg('link');
if (!link) { console.error('用法：node scripts/interview.mjs --link <链路名> [--answers answers.json] [--out 目录] [--strict]'); process.exit(4); }
const type = String(arg('type', 'api')).toLowerCase();
const outDir = path.resolve(arg('out') || path.join(ROOT, 'produced', link, '配置'));
const answersFile = arg('answers');
const strict = flag('strict');

const PURPOSE = {
  cron: '定时跑（每天/每周固定时间取数或写报表）',
  event: '事件触发（指标到阈值才动，例如消耗到日预算 90% 才加预算）',
  manual: '人工按需（谁要用谁点，跑完给人看）',
  once: '一次性（就这一次，跑完拉倒）'
};
const OUT_KIND = ['本地文件', '在线表格', '接口回填', '页面回读', '只给人看'];

/* 只问，不卡：每题的 check 返回问题描述 → 记为「待确认」，而不是拒绝 */
const QUESTIONS = [
  {
    key: 'purpose', q: '这条链路什么时候跑？', opts: Object.entries(PURPOSE).map(([k, v]) => `${k}=${v}`),
    check: v => PURPOSE[v] ? null : `用途没定清（可选 ${Object.keys(PURPOSE).join(' / ')}）`
  },
  {
    key: 'cron', q: '定时表达式（cron 5 段，例 0 9 * * * = 每天 9:00）', when: a => a.purpose === 'cron',
    check: v => /^(\S+\s+){4}\S+$/.test(String(v || '').trim()) ? null : '定时时间还没写成 cron（5 段）'
  },
  {
    key: 'event', q: '触发条件：什么指标、到什么阈值、多久查一次、一次最多动多少、超限谁批（一句话）',
    when: a => a.purpose === 'event',
    check: v => (String(v || '').trim().length >= 8 ? null : '触发条件还没写清（缺指标/阈值/频率/上限/审批中的一些）')
  },
  {
    key: 'triggerNote', q: '什么时候跑（一句话，给人看）', when: a => a.purpose === 'manual' || a.purpose === 'once',
    check: v => (String(v || '').trim() ? null : '还没写清谁在什么时候跑')
  },
  {
    key: 'paramsSource', q: '参数从哪来（例：accountId=固定值, date=每次人工给, 预算值=从上级表读）',
    check: v => (String(v || '').trim() ? null : '参数来源没写（不知道参数从哪来，重放就是条死路径）')
  },
  {
    key: 'outputKind', q: `跑完东西去哪（可多选，逗号隔开）：${OUT_KIND.join(' / ')}`,
    check: v => (String(v || '').trim() ? null : '产出形态没定（本地文件？在线表格？接口回填？还是只给人看？）')
  },
  {
    key: 'output', q: '落在哪、给谁用（例：下载表格→粘贴到「投放日报」在线表，给投放负责人；或 data/xxx_YYYYMMDD.csv）',
    check: v => (String(v || '').trim() ? null : '产出位置和接收方还没写')
  },
  {
    key: 'success', q: '机器怎么判断这次跑成功（行数下限 / 回执号 / 页面提示 / 字段数，至少一项）',
    check: v => (String(v || '').trim() ? null : '成功判据没写（只看「没报错」等于没判据）')
  },
  {
    key: 'onFail', q: '失败找谁、重试几次、怎么通知（例：链路负责人 / 重试 2 次 / IM 通知）',
    check: v => (String(v || '').trim() ? null : '失败升级路径没写')
  },
  {
    key: 'write', q: '这条链路会改东西吗（加预算/提交/发布都算写操作）？y / n',
    check: v => (/^[yn]$/i.test(String(v || '').trim()) ? null : '还没确认是不是写操作（这决定要不要人工确认）')
  },
  {
    key: 'writeLimit', q: '写操作的上限与确认方式（例：单账号日累计≤500元；超限先问投放负责人；先 DryRun）',
    when: a => /^y$/i.test(String(a.write || '')),
    check: v => (String(v || '').trim() ? null : '写操作上限还没定（这条不补，别让它自动跑）')
  }
];

function parseParams(raw) {
  return String(raw || '').split(/[,，;；]/).map(s => s.trim()).filter(Boolean).map(s => {
    const i = s.indexOf('=');
    return i > 0 ? { name: s.slice(0, i).trim(), from: s.slice(i + 1).trim() } : { name: s, from: '（未写来源）' };
  });
}

function parseKinds(raw) {
  const list = String(raw || '').split(/[,，/、;；]/).map(s => s.trim()).filter(Boolean);
  return list.map(k => OUT_KIND.find(x => x === k) || OUT_KIND.find(x => k.includes(x)) || `其他:${k}`);
}

function buildTrigger(a, pending) {
  const kinds = parseKinds(a.outputKind);
  const t = {
    链路: link,
    类型: type,
    用途: PURPOSE[a.purpose] || '待确认',
    触发: {},
    参数来源: parseParams(a.paramsSource),
    产出: { 形态: kinds.length ? kinds : ['待确认'], 位置与接收方: a.output || '待确认' },
    成功判据: a.success || '待确认',
    失败处理: a.onFail || '待确认',
    写操作: /^y$/i.test(String(a.write || ''))
      ? { 是否写: true, 上限与确认: a.writeLimit || '待确认' }
      : (/^n$/i.test(String(a.write || '')) ? { 是否写: false } : { 是否写: '待确认' }),
    待确认: pending,
    问于: new Date().toISOString().slice(0, 16).replace('T', ' ')
  };
  if (a.purpose === 'cron') {
    t.触发 = { 方式: 'cron', 表达式: String(a.cron || '').trim(), 说明: a.cron ? `按 cron ${String(a.cron).trim()} 定时跑` : '待确认' };
  } else if (a.purpose === 'event') {
    t.触发 = { 方式: 'event', 条件: a.event || '待确认', 说明: a.event || '待确认' };
  } else if (a.purpose === 'manual' || a.purpose === 'once') {
    t.触发 = { 方式: a.purpose, 说明: a.triggerNote || '待确认' };
  } else {
    t.触发 = { 方式: '待确认', 说明: '待确认' };
  }
  /* 在线表格形态：映射关系不用人写，录到的下载表 + 目标表列头就能对出来 */
  if (kinds.includes('在线表格')) {
    t.产出.映射 = '列头自动对（下载表列头 ↔ 目标表列头；用 analyze.py / tableread.mjs，人工只核对一眼）';
  }
  return t;
}

/* ---------------- 录制时口述的备注：自动带出来，不用再问一遍 ---------------- */
const recFile = arg('rec');
let recNotes = [];
if (recFile) {
  const p = path.resolve(recFile);
  if (fs.existsSync(p)) {
    try {
      const rec = JSON.parse(fs.readFileSync(p, 'utf8'));
      recNotes = (rec.notes || []).map(n => ({ 第几步后: n.seq, 时间: n.at || '', 原话: n.text }));
      if (recNotes.length) {
        console.log(`\n录制里你自己说的 ${recNotes.length} 句（已带进访谈，不用重复说）：`);
        for (const n of recNotes) console.log(`  · 第${n.第几步后}步后：${n.原话}`);
      }
    } catch (e) { console.error(`录制文件读不了（跳过备注）：${String(e.message || e)}`); }
  } else { console.error(`找不到录制文件，跳过备注：${p}`); }
}

/* ---------------- 取答案：文件 or 交互 ---------------- */
let answers = {};
if (answersFile) {
  const p = path.resolve(answersFile);
  if (!fs.existsSync(p)) { console.error(`找不到答案文件：${p}`); process.exit(4); }
  answers = JSON.parse(fs.readFileSync(p, 'utf8'));
} else {
  if (!process.stdin.isTTY) {
    console.error('非交互环境：请用 --answers answers.json（或先把问题问完再跑）');
    process.exit(4);
  }
  const rl = readline.createInterface({ input: process.stdin, output: process.stdout });
  console.log(`\n需求访谈：${link}\n（不知道就直接回车 → 记为「待确认」，不拦你；以后想起来再补）\n`);
  for (const Q of QUESTIONS) {
    if (Q.when && !Q.when(answers)) continue;
    const hint = Q.opts ? `\n  ${Q.opts.join('\n  ')}\n` : '';
    const v = (await rl.question(`${Q.q}${hint}> `)).trim();
    if (v) answers[Q.key] = v;
  }
  await rl.close();
}

/* ---------------- 校验：缺的进「待确认」，不硬拦 ---------------- */
const pending = [];
for (const Q of QUESTIONS) {
  if (Q.when && !Q.when(answers)) continue;
  const msg = Q.check(answers[Q.key]);
  if (msg) pending.push({ 项: Q.q, 说明: msg });
}

const trigger = buildTrigger(answers, pending);
if (recNotes.length) {
  trigger.录制备注 = recNotes;
  trigger.录制备注提示 = '录制时用户口述的原话，写需求时优先按这个理解；和答案冲突时以答案为准（答案是他后来想清楚的）';
}
fs.mkdirSync(outDir, { recursive: true });
const outFile = path.join(outDir, '触发.json');
fs.writeFileSync(outFile, JSON.stringify(trigger, null, 1), 'utf8');

console.log(`\n✓ 需求已落盘：${outFile}`);
console.log('\n以下是会写进子技能 SKILL.md 的段落：\n');
console.log(triggerSection(trigger));

if (pending.length) {
  console.log(`还有 ${pending.length} 项待确认（不拦着生成，但会写进子技能里提醒后人）：`);
  for (const p of pending) console.log(`  · ${p.项} —— ${p.说明}`);
  console.log('（想先补齐再生成：把这几项填进 answers.json 再跑一次；或加 --strict 强制问全）');
  if (strict) {
    console.error('\n--strict：仍有待确认项，按约定不生成。');
    process.exit(1);
  }
}
if (trigger.写操作.是否写 === true) {
  console.log('⚠️ 这是写操作链路：真提交前必须人工确认，且先跑 --dry / -DryRun。');
}
console.log(`\n下一步：node scripts/build_skill.mjs --link ${link} --config "${path.dirname(outFile)}" --type ${type}`);
if (flag('json')) console.log('\n' + JSON.stringify(trigger));
