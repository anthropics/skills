#!/usr/bin/env node
// kb-bot 全库校验：结构/字段/verified/链接/INDEX 双向/ASCII 名。零依赖，Node 内置模块。
// 用法：node tools/check-kb.js（任意位置可跑，包根自动定位）
'use strict';
const fs = require('fs');
const path = require('path');

const ROOT = path.resolve(__dirname, '..');
const KB = path.join(ROOT, 'kb');
let pass = 0, fail = 0;
const lines = [];
function ok(name, cond, detail) {
  if (cond) { pass++; lines.push('  PASS ' + name); }
  else { fail++; lines.push('  FAIL ' + name + (detail ? ' — ' + detail : '')); }
}
function walk(dir, fn) {
  for (const e of fs.readdirSync(dir, { withFileTypes: true })) {
    const p = path.join(dir, e.name);
    fn(p, e.isDirectory());
    if (e.isDirectory()) walk(p, fn);
  }
}
function parseFront(text) {
  const m = text.match(/^---\r?\n([\s\S]*?)\r?\n---/);
  if (!m) return null;
  const fm = {};
  for (const line of m[1].split(/\r?\n/)) {
    const kv = line.match(/^([A-Za-z_]+):\s*(.*)$/);
    if (kv) fm[kv[1]] = kv[2].trim();
  }
  return fm;
}
const today = new Date().toISOString().slice(0, 10);

// —— skill 与 agent ——
const skillPath = path.join(ROOT, 'SKILL.md');
const skillExists = fs.existsSync(skillPath);
ok('SKILL.md 存在', skillExists);
let skillFm = null;
if (skillExists) {
  skillFm = parseFront(fs.readFileSync(skillPath, 'utf8'));
  ok('SKILL 前置元数据有 name+description', !!(skillFm && skillFm.name && skillFm.description));
  ok('SKILL name = kb-bot', skillFm.name === 'kb-bot');
}
const agentPath = path.join(ROOT, 'agents', 'kb-bot.md');
const agentExists = fs.existsSync(agentPath);
ok('agents/kb-bot.md 存在', agentExists);
if (agentExists) {
  const afm = parseFront(fs.readFileSync(agentPath, 'utf8'));
  ok('agent 前置元数据有 name+description+tools', !!(afm && afm.name && afm.description && afm.tools));
  ok('agent name = kb-bot', afm.name === 'kb-bot');
}

// —— 领域与 INDEX（空库合法：库跟着问题长，装包从零开始）——
const domains = fs.existsSync(KB)
  ? fs.readdirSync(KB, { withFileTypes: true }).filter(d => d.isDirectory()).map(d => d.name)
  : [];
const noIndex = domains.filter(d => !fs.existsSync(path.join(KB, d, 'INDEX.md')));
ok('每个领域都有 INDEX.md', noIndex.length === 0, '缺：' + noIndex.join(', '));

// —— 节点 ——
const nodes = [];
for (const d of domains) {
  const dir = path.join(KB, d);
  for (const f of fs.readdirSync(dir)) {
    if (f === 'INDEX.md' || f === 'log.md' || !f.endsWith('.md')) continue;
    const text = fs.readFileSync(path.join(dir, f), 'utf8');
    nodes.push({ domain: d, slug: f.replace(/\.md$/, ''), file: f, fm: parseFront(text), text });
  }
}
const emptyDomains = domains.filter(d => !nodes.some(n => n.domain === d));
ok('每个领域至少 1 节点', emptyDomains.length === 0, '空域：' + emptyDomains.join(', '));
ok('节点全有前置元数据', nodes.every(n => n.fm), nodes.filter(n => !n.fm).map(n => n.slug).join(','));

function collect(key, pred, detail) {
  const hits = nodes.filter(n => n.fm && !pred(n));
  ok(key, hits.length === 0, hits.map(n => n.slug + (detail ? '(' + detail(n) + ')' : '')).join(','));
}
collect('节点全有 title', n => !!n.fm.title);
collect('tier 全在 slow/medium/fast', n => ['slow', 'medium', 'fast'].includes(n.fm.tier), n => n.fm.tier);
collect('verified 全是合法日期', n => /^\d{4}-\d{2}-\d{2}$/.test(n.fm.verified || ''), n => n.fm.verified);
collect('verified 全不晚于今天', n => (n.fm.verified || '9999') <= today, n => n.fm.verified);
collect('src 全非空', n => !!n.fm.src);
collect('节点全有结论段', n => n.text.includes('**结论**'));
collect('fast 节点全有菜谱段', n => n.fm.tier !== 'fast' || n.text.includes('**菜谱**'));
collect('fast 节点全有上次快照', n => n.fm.tier !== 'fast' || n.text.includes('**上次快照**'));

// —— [[链接]] 可解析（同域）——
const broken = [];
for (const n of nodes) {
  for (const m of n.text.matchAll(/\[\[([a-z0-9-]+)\]\]/g)) {
    if (!fs.existsSync(path.join(KB, n.domain, m[1] + '.md'))) broken.push(n.domain + '/' + n.slug + ' -> [[' + m[1] + ']]');
  }
}
ok('正文 [[链接]] 全可解析', broken.length === 0, broken.join(' '));

// —— INDEX 双向 ——
const notIndexed = [], deadIndex = [];
for (const d of domains) {
  const itext = fs.readFileSync(path.join(KB, d, 'INDEX.md'), 'utf8');
  ok('INDEX(' + d + ') 含三档图例', /slow/.test(itext) && /fast/.test(itext));
  const listed = new Set([...itext.matchAll(/\]\(([a-z0-9-]+\.md)\)/g)].map(m => m[1]));
  for (const n of nodes.filter(n => n.domain === d)) if (!listed.has(n.file)) notIndexed.push(d + '/' + n.slug);
  for (const f of listed) if (!fs.existsSync(path.join(KB, d, f))) deadIndex.push(d + ' INDEX -> ' + f);
}
ok('节点全登记进 INDEX', notIndexed.length === 0, notIndexed.join(','));
ok('INDEX 链接目标全存在', deadIndex.length === 0, deadIndex.join(','));

// —— 操作日志 ——
const noLog = domains.filter(d => !fs.existsSync(path.join(KB, d, 'log.md')));
ok('每个领域都有 log.md', noLog.length === 0, '缺：' + noLog.join(', '));
const badLog = [];
for (const d of domains) {
  const lp = path.join(KB, d, 'log.md');
  if (!fs.existsSync(lp)) continue;
  for (const line of fs.readFileSync(lp, 'utf8').split(/\r?\n/)) {
    if (!line.trim() || line.startsWith('#')) continue;
    if (!/^- \d{4}-\d{2}-\d{2} \| [+\-!~]/.test(line)) badLog.push(d + ': ' + line.slice(0, 40));
  }
}
ok('log 行全为「日期 | 动作 | 说明」格式', badLog.length === 0, badLog.join(' ; '));

// —— ASCII 文件名 ——
const nonAscii = [];
walk(ROOT, p => {
  const name = path.basename(p);
  if (!/^[\x20-\x7E]+$/.test(name)) nonAscii.push(name);
});
ok('包内文件/目录名全 ASCII', nonAscii.length === 0, nonAscii.join(', '));

console.log(lines.join('\n'));
console.log('\n' + (pass + fail) + ' 项断言：' + pass + ' 过 / ' + fail + ' 挂');
process.exit(fail ? 1 : 0);
