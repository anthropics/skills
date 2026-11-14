/* tableread.mjs — Node 零依赖读表：csv（utf-8/utf-8-sig）+ xlsx（zip+inflate+极简XML）
 * 限制：gbk 编码的 csv 读不了（Node 原生不支持 gbk），遇到会明确报错——导出请用 xlsx 或另存 utf-8。
 * 解析口径与 analyze.py 对齐：返回 { name, headers, rows }，rows 是对象数组。
 */
import fs from 'node:fs';
import zlib from 'node:zlib';

export function readCsv(path) {
  const buf = fs.readFileSync(path);
  let text = buf.toString('utf8');
  if (text.charCodeAt(0) === 0xfeff) text = text.slice(1);
  if (text.includes('�')) {
    throw new Error(`${path}：含非 UTF-8 字节（多半是 gbk 编码的 csv）。请用 xlsx 导出，或另存为 UTF-8`);
  }
  const lines = text.split(/\r?\n/).filter(l => l.trim() !== '');
  if (!lines.length) throw new Error(`${path}：空文件`);
  // 拆分走状态机：正则全局匹配会在逗号处吐零长串，表头就混进空列了
  const splitLine = l => {
    const out = [];
    let cur = '', inQ = false;
    for (let i = 0; i < l.length; i++) {
      const ch = l[i];
      if (ch === '"') {
        if (inQ && l[i + 1] === '"') { cur += '"'; i++; } else inQ = !inQ;
      } else if (ch === ',' && !inQ) { out.push(cur); cur = ''; }
      else cur += ch;
    }
    out.push(cur);
    return out;
  };
  const headers = splitLine(lines[0]).map(h => h.trim());
  const rows = lines.slice(1).map(l => {
    const cells = splitLine(l);
    const r = {};
    headers.forEach((h, i) => { r[h] = (cells[i] ?? '').trim(); });
    return r;
  });
  return { name: path.split(/[\\/]/).pop(), headers, rows };
}

/* ---- 极简 zip 读取（只服务 xlsx：中心目录 → 偏移 → inflateRaw） ---- */

function zipEntries(buf) {
  // EOCD 在末尾 64KB 里找 0x06054b50
  const tail = buf.subarray(Math.max(0, buf.length - 65557));
  let eocd = -1;
  for (let i = tail.length - 22; i >= 0; i--) {
    if (tail.readUInt32LE(i) === 0x06054b50) { eocd = i; break; }
  }
  if (eocd < 0) throw new Error('不是合法 zip/xlsx（找不到目录尾）');
  const count = tail.readUInt16LE(eocd + 10);
  let p = tail.readUInt32LE(eocd + 16); // cdStart 是绝对偏移（大文件时 tail 是子视图，别重复加窗口偏移）
  const files = new Map();
  for (let i = 0; i < count; i++) {
    if (buf.readUInt32LE(p) !== 0x02014b50) break;
    const method = buf.readUInt16LE(p + 10);
    const crc = buf.readUInt32LE(p + 16);
    const compSize = buf.readUInt32LE(p + 20);
    const nameLen = buf.readUInt16LE(p + 28), extraLen = buf.readUInt16LE(p + 30), cmtLen = buf.readUInt16LE(p + 32);
    const lho = buf.readUInt32LE(p + 42);
    const name = buf.subarray(p + 46, p + 46 + nameLen).toString('utf8');
    files.set(name, { method, crc, compSize, lho, name });
    p += 46 + nameLen + extraLen + cmtLen;
  }
  return files;
}

function inflateEntry(buf, e) {
  const nameLen = buf.readUInt16LE(e.lho + 26), extraLen = buf.readUInt16LE(e.lho + 28);
  const start = e.lho + 30 + nameLen + extraLen;
  const raw = buf.subarray(start, start + e.compSize);
  return e.method === 0 ? Buffer.from(raw) : zlib.inflateRawSync(raw);
}

/* ---- xlsx：sharedStrings + 第一张有数据的 sheet ---- */

export function readXlsx(path) {
  const buf = fs.readFileSync(path);
  const files = zipEntries(buf);
  const shared = [];
  if (files.has('xl/sharedStrings.xml')) {
    const xml = inflateEntry(buf, files.get('xl/sharedStrings.xml')).toString('utf8');
    for (const m of xml.matchAll(/<si>([\s\S]*?)<\/si>/g)) {
      shared.push([...m[1].matchAll(/<t[^>]*>([\s\S]*?)<\/t>/g)].map(t => t[1]).join(''));
    }
  }
  const sharedXml = files.has('xl/workbook.xml') ? inflateEntry(buf, files.get('xl/workbook.xml')).toString('utf8') : '';
  const sheetNames = [...sharedXml.matchAll(/<sheet[^>]*name="([^"]*)"/g)].map(m => m[1]);
  for (let idx = 1; idx <= (sheetNames.length || 1); idx++) {
    const fn = `xl/worksheets/sheet${idx}.xml`;
    if (!files.has(fn)) continue;
    const xml = inflateEntry(buf, files.get(fn)).toString('utf8');
    const rows = [];
    for (const rm of xml.matchAll(/<row[^>]*>([\s\S]*?)<\/row>/g)) {
      const cells = [];
      // 单元格两种形态分开抓：自闭合 <c r="A1"/> 和带体的 <c …><v>x</v> 或 <is><t>x</t></is></c>
      for (const cm of rm[1].matchAll(/<c\b([^>]*)\/>|<c\b([^>]*)>([\s\S]*?)<\/c>/g)) {
        const attrs = cm[1] !== undefined ? cm[1] : cm[2];
        const body = cm[1] !== undefined ? '' : cm[3];
        const v = (body.match(/<v>([\s\S]*?)<\/v>/) || [])[1] ?? '';
        const isS = /t="s"/.test(attrs), isInline = /t="inlineStr"/.test(attrs);
        const inline = isInline ? [...body.matchAll(/<t[^>]*>([\s\S]*?)<\/t>/g)].map(t => t[1]).join('') : '';
        cells.push(isS ? (shared[Number(v)] ?? '') : isInline ? inline : v);
      }
      if (cells.some(c => String(c).trim() !== '')) rows.push(cells);
    }
    if (rows.length < 2) continue;
    const headers = rows[0].map(h => String(h).trim());
    const data = rows.slice(1).map(r => {
      const o = {};
      headers.forEach((h, i) => { o[h] = (r[i] ?? '').trim(); });
      return o;
    });
    return { name: sheetNames[idx - 1] ?? path, headers, rows: data };
  }
  throw new Error(`${path}：xlsx 里没读到数据行`);
}

export function readTable(path) {
  return path.toLowerCase().endsWith('.xlsx') ? readXlsx(path) : readCsv(path);
}

/* 数字口径与 analyze.py 一致：去千分位/货币符后转 float */
export function toNum(v) {
  const s = String(v ?? '').replace(/[,，￥¥ "']/g, '').replace(/%$/, '');
  if (s === '') return null;
  const n = Number(s);
  return Number.isFinite(n) ? n : null;
}
