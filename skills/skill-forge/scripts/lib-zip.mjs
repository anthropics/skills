/* zip.mjs — 零依赖 zip 打包器（STORE 不压缩）+ 开包验证
 * 为什么不用 Compress-Archive：PowerShell 5.1 写的 zip 条目用 \ 分隔，上传平台拒收（全局坑）。
 * 规矩：条目名一律 / 分隔、不带 .. 、置 UTF-8 位（0x0800）；打完必须 listEntries 回读验证。
 */
import fs from 'node:fs';
import path from 'node:path';

const CRC_TABLE = (() => {
  const t = new Uint32Array(256);
  for (let n = 0; n < 256; n++) {
    let c = n;
    for (let k = 0; k < 8; k++) c = c & 1 ? 0xedb88320 ^ (c >>> 1) : c >>> 1;
    t[n] = c >>> 0;
  }
  return t;
})();

function crc32(buf) {
  let c = 0xffffffff;
  for (let i = 0; i < buf.length; i++) c = CRC_TABLE[(c ^ buf[i]) & 0xff] ^ (c >>> 8);
  return (c ^ 0xffffffff) >>> 0;
}

function dosTime(d) {
  const time = ((d.getHours() << 11) | (d.getMinutes() << 5) | (d.getSeconds() >> 1)) & 0xffff;
  const date = (((d.getFullYear() - 1980) << 9) | ((d.getMonth() + 1) << 5) | d.getDate()) & 0xffff;
  return { time, date };
}

export function zipStore(entries, outPath) {
  const now = new Date();
  const { time, date } = dosTime(now);
  const chunks = [], central = [];
  let offset = 0;
  for (const e of entries) {
    if (e.name.includes('\\')) throw new Error(`条目名含反斜杠（禁）：${e.name}`);
    if (e.name.startsWith('/') || e.name.split('/').includes('..')) throw new Error(`条目名不合法：${e.name}`);
    const name = Buffer.from(e.name, 'utf8');
    const data = Buffer.isBuffer(e.data) ? e.data : Buffer.from(e.data);
    const crc = crc32(data);
    const local = Buffer.alloc(30);
    local.writeUInt32LE(0x04034b50, 0);
    local.writeUInt16LE(20, 4);            // version needed
    local.writeUInt16LE(0x0800, 6);        // UTF-8 名字位
    local.writeUInt16LE(0, 8);             // STORE
    local.writeUInt16LE(time, 10); local.writeUInt16LE(date, 12);
    local.writeUInt32LE(crc, 14);
    local.writeUInt32LE(data.length, 18); local.writeUInt32LE(data.length, 22);
    local.writeUInt16LE(name.length, 26);
    chunks.push(local, name, data);

    const cd = Buffer.alloc(46);
    cd.writeUInt32LE(0x02014b50, 0);
    cd.writeUInt16LE(20, 4); cd.writeUInt16LE(20, 6);
    cd.writeUInt16LE(0x0800, 8); cd.writeUInt16LE(0, 10);
    cd.writeUInt16LE(time, 12); cd.writeUInt16LE(date, 14);
    cd.writeUInt32LE(crc, 16);
    cd.writeUInt32LE(data.length, 20); cd.writeUInt32LE(data.length, 24);
    cd.writeUInt16LE(name.length, 28);
    cd.writeUInt32LE(offset, 42);
    central.push(cd, name);
    offset += 30 + name.length + data.length;
  }
  const cdStart = offset;
  const cdBuf = Buffer.concat(central);
  const eocd = Buffer.alloc(22);
  eocd.writeUInt32LE(0x06054b50, 0);
  eocd.writeUInt16LE(entries.length, 8);
  eocd.writeUInt16LE(entries.length, 10);
  eocd.writeUInt32LE(cdBuf.length, 12);
  eocd.writeUInt32LE(cdStart, 16);
  fs.mkdirSync(path.dirname(outPath), { recursive: true });
  fs.writeFileSync(outPath, Buffer.concat([...chunks, cdBuf, eocd]));
  return outPath;
}

/* 开包验证：读中心目录，返回条目名列表（发布前必须跑，防打包器坑） */
export function listEntries(zipPath) {
  const buf = fs.readFileSync(zipPath);
  const tail = buf.subarray(Math.max(0, buf.length - 65557));
  let eocd = -1;
  for (let i = tail.length - 22; i >= 0; i--) {
    if (tail.readUInt32LE(i) === 0x06054b50) { eocd = i; break; }
  }
  if (eocd < 0) throw new Error(`${zipPath}：不是合法 zip`);
  const count = tail.readUInt16LE(eocd + 10);
  let p = tail.readUInt32LE(eocd + 16); // cdStart 本身就是文件内绝对偏移，别再加 tail 窗口偏移
  const names = [];
  for (let i = 0; i < count; i++) {
    if (buf.readUInt32LE(p) !== 0x02014b50) break;
    const nameLen = buf.readUInt16LE(p + 28), extraLen = buf.readUInt16LE(p + 30), cmtLen = buf.readUInt16LE(p + 32);
    names.push(buf.subarray(p + 46, p + 46 + nameLen).toString('utf8'));
    p += 46 + nameLen + extraLen + cmtLen;
  }
  return names;
}

/* 打包一个目录（保持相对结构，顶层包一层 dirName），并回读验证 */
export function zipDir(dirPath, dirName, outPath) {
  const entries = [];
  const walk = (abs, rel) => {
    for (const f of fs.readdirSync(abs, { withFileTypes: true })) {
      const childAbs = `${abs}/${f.name}`, childRel = rel ? `${rel}/${f.name}` : f.name;
      if (f.isDirectory()) walk(childAbs, childRel);
      else entries.push({ name: `${dirName}/${childRel}`, data: fs.readFileSync(childAbs) });
    }
  };
  walk(dirPath, '');
  zipStore(entries, outPath);
  const got = listEntries(outPath);
  if (got.length !== entries.length) throw new Error(`打包验证失败：写入 ${entries.length} 条，读回 ${got.length} 条`);
  for (const n of got) {
    if (n.includes('\\') || n.startsWith('/')) throw new Error(`条目名违规：${n}`);
  }
  return { path: outPath, files: entries.length };
}
