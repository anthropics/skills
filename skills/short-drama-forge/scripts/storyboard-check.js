#!/usr/bin/env node
// 分镜表机器核数：预算 vs 实测，逐项输出。零依赖。
// 用法: node storyboard-check.js <分镜表.md路径>
// 退出码: 0=全过 1=有FAIL 2=用法/文件错误
'use strict';
const fs = require('fs');
const path = require('path');

const file = process.argv[2];
if (!file) { console.error('用法: node storyboard-check.js <分镜表.md路径>'); process.exit(2); }
if (!fs.existsSync(file)) { console.error('文件不存在: ' + file); process.exit(2); }

const text = fs.readFileSync(file, 'utf8');
const lines = text.split(/\r?\n/);

// ---------- 解析表头预算 ----------
const headLine = lines.find(l => l.includes('目标时长') && l.includes('节拍数')) || '';
const durMatch = headLine.match(/目标时长(\d+)秒/);
const beatMatch = headLine.match(/节拍数(\d+)/);
const cutBudgetMatch = headLine.match(/微切预算≈?(\d+)/);
const targetDur = durMatch ? parseInt(durMatch[1], 10) : null;
const declaredBeats = beatMatch ? parseInt(beatMatch[1], 10) : null;

// ---------- 解析主表 ----------
const rows = []; // {no, dur, visual, dialog}
const cutRows = []; // {pair, rel, bridge}
for (const l of lines) {
  let m = l.match(/^\|\s*(\d+)\s*\|([^|]*)\|([^|]*)\|/);
  if (m) {
    const no = parseInt(m[1], 10);
    if (!rows.some(r => r.no === no)) {
      const dur = m[2].trim();
      const visual = l.split('|')[3] || ''; // 第3列=画面描述
      const cells = l.split('|');
      rows.push({
        no, durRaw: dur,
        dur: parseFloat(dur) || null,
        visual: (cells[3] || '').trim(),
        dialog: (cells[6] || '').trim(), // 第6列=对白·旁白
        raw: l,
      });
      continue;
    }
  }
  m = l.match(/^\|\s*(\d+)\s*→\s*(\d+)\s*\|([^|]*)\|([^|]*)\|/);
  if (m) cutRows.push({ pair: m[1] + '→' + m[2], rel: (m[3] || '').trim(), bridge: (m[4] || '').trim() });
}

const results = [];
let fail = 0, warn = 0;
function pass(msg) { results.push('[PASS] ' + msg); }
function failMsg(msg) { results.push('[FAIL] ' + msg); fail++; }
function warnMsg(msg) { results.push('[警] ' + msg); warn++; }

if (rows.length === 0) { console.error('没解析到分镜行（检查表格格式：| 镜号 | 时长 | …）'); process.exit(2); }

// ---------- 检查 ----------
// 1 镜号连续
const nos = rows.map(r => r.no).sort((a, b) => a - b);
const gaps = [];
for (let i = 1; i < nos.length; i++) if (nos[i] !== nos[i - 1] + 1) gaps.push(nos[i - 1] + '→' + nos[i]);
gaps.length === 0 ? pass('镜号连续：1-' + nos[nos.length - 1]) : failMsg('镜号断裂：' + gaps.join('、'));

// 2 节拍数 表头 vs 实测
if (declaredBeats !== null) {
  declaredBeats === rows.length
    ? pass('节拍数：表头' + declaredBeats + ' = 实测' + rows.length)
    : failMsg('节拍数：表头' + declaredBeats + ' ≠ 实测' + rows.length);
} else warnMsg('表头没写节拍数，跳过对账');

// 3 时长
const durs = rows.filter(r => r.dur !== null);
const noDur = rows.length - durs.length;
if (noDur > 0) warnMsg(noDur + '镜时长列读不出数字');
const total = durs.reduce((a, r) => a + r.dur, 0);
if (targetDur !== null) {
  const dev = ((total - targetDur) / targetDur * 100).toFixed(1);
  Math.abs(total - targetDur) <= targetDur * 0.1
    ? pass('总时长：' + total + 's / 目标' + targetDur + 's（' + dev + '%，±10%内）')
    : failMsg('总时长：' + total + 's / 目标' + targetDur + 's（' + dev + '%，超±10%）');
}
const avg = durs.length ? total / durs.length : 0;
avg <= 4.5 ? pass('平均镜长：' + avg.toFixed(1) + 's ≤4.5s') : failMsg('平均镜长：' + avg.toFixed(1) + 's >4.5s');
const long = durs.filter(r => r.dur > 8);
long.length === 0 ? pass('无>8s长镜') : failMsg('>8s长镜须拆：镜' + long.map(r => r.no + '(' + r.dur + 's)').join('、'));

// 4 承接句
const BRIDGE_TYPES = /动作接|视线接|声桥|物件接|位置接|视觉回声/;
const noLink = [];
const noType = [];
rows.forEach(r => {
  if (r.no === 1) return; // 首镜无上镜
  if (!r.visual.startsWith('接上镜：')) noLink.push(r.no);
  else {
    const first = r.visual.slice(0, r.visual.indexOf('。') > 0 ? r.visual.indexOf('。') : 60);
    if (!BRIDGE_TYPES.test(first)) noType.push(r.no);
  }
});
noLink.length === 0 ? pass('承接句：镜2起全部「接上镜：」开头') : failMsg('缺承接句（未以「接上镜：」开头）：镜' + noLink.join('、'));
noType.length === 0 ? pass('承接句五型：首句均含类型标记') : warnMsg('承接句首句无五型关键词（动作/视线/声桥/物件/位置/视觉回声）：镜' + noType.join('、'));

// 5 功能标注 + 角度组
const noFunc = rows.filter(r => !r.visual.includes('〔功能：')).map(r => r.no);
noFunc.length === 0 ? pass('功能标注：每镜都有〔功能：〕') : failMsg('缺〔功能：〕标注：镜' + noFunc.join('、'));
const noAngle = rows.filter(r => !r.visual.includes('①')).map(r => r.no);
noAngle.length === 0 ? pass('角度组：每镜都有①微切标记') : warnMsg('缺①角度组标记：镜' + noAngle.join('、'));

// 6 微切预算对账（①②③④⑤计数）
const microCount = (text.match(/[①②③④⑤]/g) || []).length;
if (cutBudgetMatch) {
  const budget = parseInt(cutBudgetMatch[1], 10);
  Math.abs(microCount - budget) <= budget * 0.3
    ? pass('微切标记数：' + microCount + ' / 预算' + budget + '（±30%内）')
    : warnMsg('微切标记数：' + microCount + ' / 预算' + budget + '，偏差>30%');
}

// 7 台词≤20字（只查「?:名字：」式口语台词；旁白/字卡/舞台指示不查）
const PUNCT = /[\s，。！？、；：…—·？！,.!?;:"'“”‘’（）()《》「」【】\[\]-]/g;
const longDialogs = [];
rows.forEach(r => {
  const parts = r.dialog.split(/[／/]/).map(s => s.trim()).filter(Boolean);
  parts.forEach(p => {
    if (!/^[??]:/.test(p)) return; // 只查台词
    const idx = p.indexOf('：');
    if (idx < 0) return;
    const speech = p.slice(idx + 1).replace(PUNCT, '');
    if (speech.length > 20) longDialogs.push('镜' + r.no + '「' + p.slice(idx + 1, idx + 21) + '…」（' + speech.length + '字）');
  });
});
longDialogs.length === 0 ? pass('台词单句≤20字：全过') : failMsg('台词超20字：' + longDialogs.join('；'));

// 8 无对白镜三锚点
const noAnchor = rows.filter(r => r.dialog.includes('无对白') && !r.dialog.includes('三锚点')).map(r => r.no);
noAnchor.length === 0 ? pass('无对白镜三锚点：全过') : failMsg('无对白镜缺三锚点标注：镜' + noAnchor.join('、'));

// 9 切点清单
if (rows.length > 1) {
  const expect = rows.length - 1;
  cutRows.length === expect
    ? pass('切点清单：' + cutRows.length + '行 = 镜数-1')
    : failMsg('切点清单：' + cutRows.length + '行 ≠ 镜数-1（' + expect + '）');
  const JUMP = /时间跳|场景跳/;
  const BRIDGE_MARK = /声桥|空镜|定场|字卡|环境声|白闪|视觉锚/;
  const badJump = cutRows.filter(c => JUMP.test(c.rel) && !BRIDGE_MARK.test(c.bridge)).map(c => c.pair);
  badJump.length === 0 ? pass('时间跳/场景跳切点显式桥接：全过') : failMsg('时间跳/场景跳切点缺桥接标记：' + badJump.join('、'));
} else pass('单镜表，跳过切点对账');

// ---------- 输出 ----------
console.log('== 分镜表核数：' + path.basename(file) + ' ==');
results.forEach(r => console.log(r));
console.log('汇总：' + (results.length - fail - warn) + '过 / ' + warn + '警 / ' + fail + '不过');
process.exit(fail > 0 ? 1 : 0);
