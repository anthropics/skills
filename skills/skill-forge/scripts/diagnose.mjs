/* diagnose.mjs — 失败用人话说：把退出码 / 报错 / 返回码，翻成「哪坏了 + 下一步干啥 + 要不要重录」
 *
 * 用法：
 *   node scripts/diagnose.mjs --err "Timeout waiting for selector .export-btn" --exit 3
 *   node scripts/diagnose.mjs --http 401
 *   node scripts/diagnose.mjs --rows 0 --link 日报
 * 退出码：0 已给出结论（不管好坏）；4 参数不对
 * 归因规则只有一份：scripts/lib-diagnose.mjs（manage.mjs fail 用的是同一份）
 */
import { diagnose } from './lib-diagnose.mjs';

const arg = (k, d) => { const i = process.argv.indexOf('--' + k); return i >= 0 ? process.argv[i + 1] : d; };
const err = String(arg('err', ''));
const http = String(arg('http', ''));
const exit = String(arg('exit', ''));
const rows = arg('rows');
const fields = arg('fields');
const stage = String(arg('stage', ''));
const link = arg('link', '');

const shown = [err && `报错「${err}」`, http && `HTTP ${http}`, exit && `退出码 ${exit}`, rows != null && `行数 ${rows}`]
  .filter(Boolean).join('；');

const r = diagnose({ err, http, exit, rows, fields, stage });
if (link) console.log(`链路：${link}`);
console.log(`现象：${shown || '（没给任何现象）'}`);

if (!r) {
  console.log('原因：认不出来。别硬猜 —— 补一条信息再问：');
  console.log('  · 重放停在哪个页面/哪一步（截图或浮标流水）');
  console.log('  · 接口返回码和返回体前 200 字');
  console.log('  · 退出码（0/1/2/3/4）');
  console.log('要不要重录：先别重录，信息不全重录也是白录');
  process.exit(0);
}

console.log(`人话：${r.human}`);
console.log(`哪坏了：${r.what}`);
console.log(`为什么：${r.why}`);
console.log(`下一步：${r.next}`);
console.log(`要不要重录：${r.redo}`);
console.log(`（归因码 ${r.id}）`);
process.exit(0);
