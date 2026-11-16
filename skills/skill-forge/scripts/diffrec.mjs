/* diffrec.mjs — 二次录制对比：同一操作录两遍，逐层 diff 定「常量 / 变量」
 * 用法：
 *   node scripts/diffrec.mjs --a recordings/链路_1.rec.json --b recordings/链路_2.rec.json [--out evidence] [--name 链路名]
 * 产出：
 *   evidence/diff_<名>_<时间>/对比报告.md      ← 人看：哪些参数变、哪些写死
 *   evidence/diff_<名>_<时间>/参数判定.json    ← 机读：直接喂 build_skill --verdict-from
 * 为什么要有这一步：
 *   probe --minimize 是「删参数试」= 猜；二次录制是「看两次数据自己说话」= 证。
 *   两次一样 = 常量（写死）；两次不同 = 变量（必须参数化）。不用猜。
 * 判定口径（写死，防自由发挥）：
 *   - 只出现在一份录制里的请求 → 标「条件性/不稳定」，不当作数据源
 *   - query / body 里两次值不同 → 变量；相同 → 常量
 *   - 返回字段集合不同 → 数据源不稳定，先查参数；行数不同属正常（换日期/账户）
 */
import path from 'node:path';
import fs from 'node:fs';
import { fileURLToPath } from 'node:url';

const ROOT = path.resolve(path.dirname(fileURLToPath(import.meta.url)), '..');
const arg = (k, d) => { const i = process.argv.indexOf('--' + k); return i >= 0 ? process.argv[i + 1] : d; };

const aFile = arg('a'), bFile = arg('b');
if (!aFile || !bFile) {
  console.error('用法：node scripts/diffrec.mjs --a <第一次.rec.json> --b <第二次.rec.json> [--out evidence] [--name 名]');
  process.exit(1);
}
for (const f of [aFile, bFile]) if (!fs.existsSync(f)) { console.error(`找不到录制文件：${f}`); process.exit(1); }

const A = JSON.parse(fs.readFileSync(aFile, 'utf8'));
const B = JSON.parse(fs.readFileSync(bFile, 'utf8'));
const name = arg('name') || A.meta?.name || path.basename(aFile).replace(/_\d+\.rec\.json$/, '');
const stamp = new Date().toISOString().slice(0, 19).replace(/[-:T]/g, '');
const outDir = path.resolve(ROOT, arg('out', 'evidence'), `diff_${name}_${stamp}`);
fs.mkdirSync(outDir, { recursive: true });

/* ---------- 工具 ---------- */
const norm = u => { try { const x = new URL(u); return { host: x.host, path: x.pathname, sp: x.searchParams }; } catch { return null; } };
const keyOf = (r, seen) => {
  const n = norm(r.url); if (!n) return null;
  const base = `${String(r.method || 'GET').toUpperCase()} ${n.host}${n.path}`;
  const c = (seen.get(base) || 0) + 1; seen.set(base, c);
  return { base, key: c === 1 ? base : `${base}#${c}`, n };
};
const flat = (o, pre = '', out = {}, d = 0) => {
  if (d > 2 || o == null) return out;
  if (typeof o !== 'object') { out[pre] = o; return out; }
  if (Array.isArray(o)) { out[pre] = `[${o.length}项]`; return out; }
  for (const [k, v] of Object.entries(o)) flat(v, pre ? `${pre}.${k}` : k, out, d + 1);
  return out;
};
function parseBody(s) {
  if (!s) return null;
  try {
    const j = JSON.parse(s);
    if (j && typeof j === 'object') return { type: 'json', obj: j };
  } catch { /* 不是 JSON */ }
  if (/^[^=&\s]+=[^&]*(\s*&\s*[^=&\s]+=[^&]*)*$/.test(s)) {
    const o = {};
    for (const kv of s.split('&')) { const [k, ...v] = kv.split('='); o[decodeURIComponent(k)] = decodeURIComponent(v.join('=')); }
    return { type: 'form', obj: o };
  }
  return { type: 'raw', obj: null, raw: s };
}
const jstr = v => (typeof v === 'string' ? v : JSON.stringify(v));

/* ---------- 动作序列 ---------- */
const actKey = a => `${a.type}|${a.locator?.best || a.locator?.L4_text || a.text || ''}`;
const actA = (A.actions || []).map(actKey), actB = (B.actions || []).map(actKey);
const actedSame = actA.length === actB.length && actA.every((k, i) => k === actB[i]);
const actDiff = [];
for (let i = 0; i < Math.max(actA.length, actB.length); i++) {
  if (actA[i] !== actB[i]) actDiff.push({ 第几步: i + 1, 第一次: actA[i] || '（无）', 第二次: actB[i] || '（无）' });
}

/* ---------- 请求配对 ---------- */
const seenA = new Map(), seenB = new Map();
const mapA = new Map(), mapB = new Map();
for (const r of A.network || []) { const k = keyOf(r, seenA); if (k) mapA.set(k.key, { ...r, _n: k.n, _base: k.base }); }
for (const r of B.network || []) { const k = keyOf(r, seenB); if (k) mapB.set(k.key, { ...r, _n: k.n, _base: k.base }); }

const matched = [], onlyA = [], onlyB = [];
for (const [k, ra] of mapA) {
  const rb = mapB.get(k);
  if (!rb) { onlyA.push(ra); continue; }
  matched.push([ra, rb]);
}
for (const [k, rb] of mapB) if (!mapA.has(k)) onlyB.push(rb);

/* ---------- 逐条对比 ---------- */
const details = [];
const paramBag = {};      // 变量 → 两次的值
const constBag = {};      // 常量（可直接写死）
const bodyTemplates = {}; // key → 模板（来自 A 原文，只把变量位换占位符）

for (const [ra, rb] of matched) {
  const qa = ra._n.sp, qb = rb._n.sp;
  const keys = [...new Set([...qa.keys(), ...qb.keys()])];
  const varQ = {}, constQ = {};
  for (const k of keys) {
    const va = qa.get(k), vb = qb.get(k);
    if (va === vb) constQ[k] = va; else { varQ[k] = [va, vb]; paramBag[k] = va ?? vb; }
  }

  const ha = ra.headers || {}, hb = rb.headers || {};
  const hKeys = [...new Set([...Object.keys(ha), ...Object.keys(hb)])].filter(k => k.toLowerCase() !== 'content-type');
  const varH = {}, constH = {};
  for (const k of hKeys) { if (ha[k] === hb[k]) constH[k] = ha[k]; else varH[k] = [ha[k], hb[k]]; }

  const pa = parseBody(ra.body), pb = parseBody(rb.body);
  let varBody = {}, constBody = {}, bodyType = pa?.type || pb?.type || 'none', rawSame = true;
  if (pa && pb) {
    if (pa.type === 'raw' || pb.type === 'raw') {
      rawSame = ra.body === rb.body;
    } else {
      const fa = flat(pa.obj), fb = flat(pb.obj);
      for (const k of new Set([...Object.keys(fa), ...Object.keys(fb)])) {
        const va = fa[k], vb = fb[k];
        if (jstr(va) === jstr(vb)) constBody[k] = va; else { varBody[k] = [va, vb]; paramBag[k] = va ?? vb; }
      }
    }
  }

  /* 模板：结构整段来自 A 的原文，只把变量叶子换成 {{k}}（不手写、不重构） */
  let bodyTemplate = '';
  if (pa && pa.type === 'json' && Object.keys(varBody).length) {
    const clone = JSON.parse(JSON.stringify(pa.obj));
    for (const dotted of Object.keys(varBody)) {
      const segs = dotted.split('.');
      let cur = clone;
      for (let i = 0; i < segs.length - 1 && cur; i++) cur = cur[segs[i]];
      if (cur && segs.length) cur[segs[segs.length - 1]] = `{{${segs[segs.length - 1]}}}`;
    }
    bodyTemplate = JSON.stringify(clone);
  } else if (pa && pa.type === 'form' && Object.keys(varBody).length) {
    bodyTemplate = ra.body.replace(/(^|&)([^=&]+)=([^&]*)/g, (m, pre, k, v) => {
      return varBody[k] ? `${pre}${k}={{${k}}}` : m;
    });
  } else if (pa && pa.type === 'raw' && !rawSame) {
    bodyTemplate = ra.body; // 原样，自己不会改；模板替换法对它不适用，如实标注
  }
  if (bodyTemplate) bodyTemplates[ra._base] = { type: bodyType, template: bodyTemplate };

  /* URL 模板：变量位换 ${k} */
  const u = new URL(ra.url);
  for (const k of Object.keys(varQ)) if (u.searchParams.has(k)) u.searchParams.set(k, `\${${k}}`);
  const urlTemplate = decodeURIComponent(u.toString()).replace(/%24%7B/gi, '${').replace(/%7D/gi, '}');

  details.push({
    key: ra._base,
    method: String(ra.method || 'GET').toUpperCase(),
    statusA: ra.status, statusB: rb.status,
    rows: [ra.rows ?? null, rb.rows ?? null],
    fieldsSame: jstr(ra.fields) === jstr(rb.fields),
    fieldsA: ra.fields || [], fieldsB: rb.fields || [],
    constQuery: constQ, varQuery: varQ,
    constHeaders: constH, varHeaders: varH,
    bodyType, constBody, varBody,
    bodySame: pa && pb ? (pa.type === 'raw' ? rawSame : jstr(flat(pa.obj)) === jstr(flat(pb.obj))) : true,
    urlTemplate, bodyTemplate
  });
}

/* ---------- 结论 ---------- */
const varKeys = Object.keys(paramBag);
const stable = details.filter(d => d.rows[0] != null && d.fieldsSame);
const verdict = varKeys.length
  ? `定出 ${varKeys.length} 个变量（${varKeys.join('、')}）：这些必须参数化；其余写死`
  : '两次录制没抓到任何变量：要么操作完全一样（正常），要么第二次没走同一条路 → 先看「只出现一次」的请求';

const md = `# 二次录制对比：${name}

- 第一次：\`${path.basename(aFile)}\`（${(A.meta?.finishedAt || '').slice(0, 19).replace('T', ' ')}）
- 第二次：\`${path.basename(bFile)}\`（${(B.meta?.finishedAt || '').slice(0, 19).replace('T', ' ')}）
- 动作 ${(A.actions || []).length} / ${(B.actions || []).length} 条；请求 ${(A.network || []).length} / ${(B.network || []).length} 条

> 口径：两次一样 = 常量（写死）｜两次不同 = 变量（必须参数化）。**这是看数据，不是猜。**

## 一、动作序列

${actedSame ? '✅ 两次动作完全一致（同一条链路，可比）' : `⚠️ 动作不一致（${actDiff.length} 处），下面的参数判定要打折看——先确认两次走的是同一条路\n\n| 第几步 | 第一次 | 第二次 |\n|---|---|---|\n${actDiff.slice(0, 10).map(d => `| ${d.第几步} | \`${String(d.第一次).slice(0, 60)}\` | \`${String(d.第二次).slice(0, 60)}\` |`).join('\n')}`}

## 二、变量 / 常量总表

${varKeys.length ? `| 变量 | 第一次 | 第二次 |\n|---|---|---|\n${varKeys.map(k => `| **${k}** | \`${String(paramBag[k]).slice(0, 60)}\` | \`${String((details.flatMap(d => d.varQuery[k] || d.varBody[k] || [])[1]) ?? '').slice(0, 60)}\` |`).join('\n')}` : '（没抓到变量）'}

${Object.keys(constBag).length ? '' : ''}
需要写死的常量（两次一致）：见每节「常量」。

## 三、逐接口对比

${details.length ? details.map((d, i) => `### ${i + 1}. \`${d.method} ${d.key.split(' ')[1]}\`

| 项 | 第一次 | 第二次 |
|---|---|---|
| 状态 | ${d.statusA ?? '—'} | ${d.statusB ?? '—'} |
| 行数 | ${d.rows[0] ?? '—'} | ${d.rows[1] ?? '—'} |
| 字段集 | ${d.fieldsA.length} 个 | ${d.fieldsB.length} 个 ${d.fieldsSame ? '✅ 一致' : '⚠️ 不一致'} |

- 变量 query：${Object.keys(d.varQuery).length ? Object.entries(d.varQuery).map(([k, v]) => `\`${k}=${v[0]}\` → \`${k}=${v[1]}\``).join('，') : '无'}
- 常量 query：${Object.keys(d.constQuery).length ? Object.entries(d.constQuery).map(([k, v]) => `\`${k}=${v}\``).join('，') : '无'}
- 变量 body：${Object.keys(d.varBody).length ? Object.entries(d.varBody).map(([k, v]) => `\`${k}: ${JSON.stringify(v[0])}\` → \`${JSON.stringify(v[1])}\``).join('，') : '无'}
- body 是否同：${d.bodySame ? '✅ 同' : '⚠️ 不同'}
- URL 模板：\`${d.urlTemplate.slice(0, 220)}\`
${d.bodyTemplate ? `- body 模板（原文结构，变量位 \`{{k}}\`）：\n\n\`\`\`\n${d.bodyTemplate.slice(0, 500)}\n\`\`\`` : ''}`).join('\n\n') : '（两次都没抓到 XHR/Fetch）'}

## 四、只出现一次的请求（别当数据源）

${onlyA.length || onlyB.length ? `| 只在第一次 | 只在第二次 |\n|---|---|\n${Array.from({ length: Math.max(onlyA.length, onlyB.length) }, (_, i) => `| ${onlyA[i] ? `\`${onlyA[i].method} ${onlyA[i]._base.split(' ')[1]}\`` : '—'} | ${onlyB[i] ? `\`${onlyB[i].method} ${onlyB[i]._base.split(' ')[1]}\`` : '—'} |`).join('\n')}\n\n这些多半是埋点/轮询/条件加载，**不能当稳定数据源**。` : '✅ 两次请求集合一致'}

## 五、结论

**${verdict}**

下一步：
1. 把「变量」写进 \`配置/接口.json\` 的 \`params\`，常量写死；
2. body 用上面的模板整段拷（只换 \`{{k}}\`），**不要凭理解重写**；
3. \`node scripts/build_skill.mjs --link <名> --config <探查目录> --type api --verdict-from 参数判定.json\`
`;

fs.writeFileSync(path.join(outDir, '对比报告.md'), md, 'utf8');

const verdictJson = {
  name, a: path.basename(aFile), b: path.basename(bFile),
  generatedAt: new Date().toISOString(),
  actionsSame: actedSame,
  params: paramBag,                      // 变量 → 第一次的值（做默认值）
  varKeys, constants: { query: details[0]?.constQuery || {}, headers: details[0]?.constHeaders || {}, body: details[0]?.constBody || {} },
  bodyTemplates,                         // base → {type, template}
  urlTemplates: Object.fromEntries(details.map(d => [d.key, d.urlTemplate])),
  requests: details.map(d => ({
    key: d.key, method: d.method, varQuery: d.varQuery, constQuery: d.constQuery,
    varBody: d.varBody, bodyType: d.bodyType, fieldsSame: d.fieldsSame,
    fields: d.fieldsA, rows: d.rows, bodyTemplate: d.bodyTemplate
  })),
  onlyInA: onlyA.map(r => `${r.method} ${r._base.split(' ')[1]}`),
  onlyInB: onlyB.map(r => `${r.method} ${r._base.split(' ')[1]}`)
};
fs.writeFileSync(path.join(outDir, '参数判定.json'), JSON.stringify(verdictJson, null, 1), 'utf8');

console.log(`✓ 二次录制对比 → ${outDir}`);
console.log(`  动作：${actedSame ? '两次一致' : `⚠️ 有 ${actDiff.length} 处不同`}`);
console.log(`  配上的请求：${matched.length} 条；只在一次里：${onlyA.length + onlyB.length} 条`);
console.log(`  变量：${varKeys.length ? varKeys.join('、') : '（没抓到）'}`);
console.log(`  报告：${path.join(outDir, '对比报告.md')}`);
console.log(`  机读：${path.join(outDir, '参数判定.json')}（喂 build_skill --verdict-from）`);
