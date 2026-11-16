#!/usr/bin/env node
// skill 机器安检：frontmatter/死链/孤儿/双源/体积/脚本语法/模糊纪律词。零依赖。
// 用法: node skill-audit.js <被检skill目录>
// 退出码: 0=无FAIL 1=有FAIL 2=用法/目录错误
'use strict';
const fs = require('fs');
const path = require('path');
const { spawnSync } = require('child_process');

const dir = process.argv[2];
if (!dir) { console.error('用法: node skill-audit.js <被检skill目录>'); process.exit(2); }
if (!fs.existsSync(dir) || !fs.statSync(dir).isDirectory()) { console.error('目录不存在: ' + dir); process.exit(2); }
const root = path.resolve(dir);

const skillPath = path.join(root, 'SKILL.md');
if (!fs.existsSync(skillPath)) { console.error('[FAIL] SKILL.md 不存在'); process.exit(1); }
const skill = fs.readFileSync(skillPath, 'utf8');
const dirName = path.basename(root);

let fail = 0, warn = 0, info = 0;
const out = [];
const pass = m => out.push('[PASS] ' + m);
const warnM = m => { out.push('[警] ' + m); warn++; };
const failM = m => { out.push('[FAIL] ' + m); fail++; };

// ---------- 1 frontmatter ----------
const fm = skill.match(/^---\r?\n([\s\S]*?)\r?\n---/);
if (!fm) failM('没有 frontmatter（--- 块）');
else {
  const body = fm[1];
  const nameM = body.match(/^name:\s*(\S+)/m);
  const descM = body.match(/^description:\s*([\s\S]*?)(?=\n[a-z_]+:|\s*$)/m);
  const verM = body.match(/^version:\s*(\S+)/m);
  if (!nameM) failM('frontmatter 缺 name');
  else {
    if (!/^[a-z0-9]+(-[a-z0-9]+)*$/.test(nameM[1])) failM('name 非 kebab-case: ' + nameM[1]);
    else if (nameM[1] !== dirName) warnM('name(' + nameM[1] + ') ≠ 目录名(' + dirName + ')');
    else pass('name 规范且与目录名一致: ' + nameM[1]);
  }
  if (!descM || !descM[1].trim()) failM('缺 description');
  else {
    const dlen = descM[1].trim().length;
    if (dlen > 1024) failM('description ' + dlen + ' 字符 > 1024 硬限');
    else pass('description ' + dlen + '/1024 字符');
    if (/rontmatter|如下|见下/.test(descM[1])) warnM('description 含元话（「frontmatter」「如下」类）');
  }
  if (!verM) warnM('缺 version（版本链追溯需要）'); else pass('version: ' + verM[1]);
}

// ---------- 2 死链 ----------
const refPaths = new Set();
for (const m of skill.matchAll(/(references\/[^\s`<>|)+（】：,，。；]+?\.(?:md|txt|json)|(?:templates|scripts)\/[^\s`<>|)+（】：,，。；]+?\.(?:md|js|py|json|ps1))/g)) refPaths.add(m[1]);
const literalPaths = [...refPaths].filter(r => !/[*?]/.test(r)); // 含通配符的是命名规则不是文件引用
const missing = literalPaths.filter(r => !fs.existsSync(path.join(root, r)));
missing.length ? failM('死链（SKILL.md 引用但文件不存在）：' + missing.join('、')) : pass('SKILL.md 引用 ' + literalPaths.length + ' 个文件全部存在');

// ---------- 3 孤儿文件 ----------
const subDirs = ['references', 'templates', 'scripts'];
const orphans = [];
for (const sd of subDirs) {
  const p = path.join(root, sd);
  if (!fs.existsSync(p)) continue;
  for (const f of fs.readdirSync(p)) if (/\.(md|js|py|json|ps1)$/.test(f) && !skill.includes(sd + '/' + f)) orphans.push(sd + '/' + f);
}
orphans.length ? warnM('孤儿文件（存在但 SKILL.md 没索引，agent 可能永远读不到）：' + orphans.join('、')) : pass('无孤儿文件');

// ---------- 4 双源（SKILL.md 与 references 重复行）----------
const norm = l => l.trim().replace(/\s+/g, ' ');
const skillLines = new Set(skill.split(/\r?\n/).map(norm).filter(l => l.length >= 16));
const dupSources = [];
for (const sd of ['references']) {
  const p = path.join(root, sd);
  if (!fs.existsSync(p)) continue;
  for (const f of fs.readdirSync(p)) {
    if (!f.endsWith('.md')) continue;
    const refText = fs.readFileSync(path.join(p, f), 'utf8');
    let hit = null;
    for (const l of refText.split(/\r?\n/)) {
      if (skillLines.has(norm(l))) { hit = norm(l).slice(0, 40); break; }
    }
    if (hit) dupSources.push(f + '（如「' + hit + '…」）');
  }
}
dupSources.length ? warnM('疑似双源（SKILL.md 与 references 有整行重复，改一处漏一处）：' + dupSources.slice(0, 5).join('、')) : pass('无双源重复行');

// ---------- 5 体积 ----------
// 按字符数判胖瘦：中文 1 字符=3 字节，按字节判会把 5000 字的中文路由器误报成超限
const size = Buffer.byteLength(skill, 'utf8');
const chars = skill.length;
if (chars > 8000) warnM('SKILL.md ' + chars + ' 字符 > 8000，路由器过肥（细节应下沉 references）');
else if (chars < 600) warnM('SKILL.md ' + chars + ' 字符过薄，可能缺路由/纪律/边界');
else pass('SKILL.md ' + chars + ' 字符 / ' + (size / 1024).toFixed(1) + 'KB（路由器体量正常）');

// ---------- 6 脚本语法 ----------
const scriptsDir = path.join(root, 'scripts');
if (fs.existsSync(scriptsDir)) {
  const jsFiles = fs.readdirSync(scriptsDir).filter(f => f.endsWith('.js'));
  for (const f of jsFiles) {
    const r = spawnSync('node', ['--check', path.join(scriptsDir, f)], { encoding: 'utf8' });
    if (r.status === 0) pass('scripts/' + f + ' 语法OK'); else failM('scripts/' + f + ' 语法错误: ' + String(r.stderr).split('\n')[0]);
  }
}

// ---------- 7 模糊纪律词粗检（可触线启发式）----------
const vagueLines = skill.split(/\r?\n/).filter(l => /(尽量|适当地|注意|避免|酌情|必要时)/.test(l) && !/\d/.test(l));
vagueLines.length ? warnM('模糊纪律词（无数字上限，可触线不合格候选）' + vagueLines.length + ' 行，如「' + norm(vagueLines[0]).slice(0, 40) + '…」——人检时逐条改写成「上限+到顶动作」') : pass('无裸模糊纪律词');

// ---------- 8 自检清单存在性 ----------
skill.includes('自检') ? (info++, out.push('[信息] 含自检清单节（人检验证据制是否落地）')) : warnM('无自检清单节');

// ---------- 输出 ----------
console.log('== skill 机器安检：' + dirName + ' ==');
out.forEach(l => console.log(l));
console.log('汇总：' + (out.length - fail - warn - info) + '过 / ' + warn + '警 / ' + fail + '不过（机检只覆盖确定性项，八维语义评审见 references/audit-rubric.md）');
process.exit(fail > 0 ? 1 : 0);
