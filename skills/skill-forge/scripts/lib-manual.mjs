/* lib-manual.mjs — 给子技能生成「说明书」：人看得懂，模型也读得懂
 *
 * 为什么要有这份：
 *   子包里只有脚本时，换个人接手只会看到一堆 .mjs；网页一改版，没人知道当初为什么这么点。
 *   说明书补的是「意图和判据」——脚本负责照做，说明书写清楚：干什么、什么时候跑、给什么、算不算成功、坏了怎么办。
 *   （对标 BrowserBC 的「转写成技能卡」：我们不放弃确定性脚本，但把说明书一起交付。）
 *
 * 口径：
 *   1) 只写录制 + 访谈里真实存在的东西，不编步骤、不编判据。
 *   2) 缺的项写「待确认」，不写好看的空话。
 *   3) 步骤表和 定位库.csv 一一对应（同序号），改脚本不改说明书 = 骗人。
 */

const t = (v, d = '待确认') => {
  if (v == null || v === '') return d;
  if (Array.isArray(v)) return v.length ? v.join('、') : d;
  return String(v);
};

export function manualText({ link, type, steps = [], trigger = null, mappings = [], version = '' }) {
  const trg = trigger || {};
  const 触发 = trg.触发 || {};
  const 产出 = trg.产出 || {};
  const 备注 = trg.录制备注 || [];

  const stepRows = steps.filter(s => s['动作'] && s['动作'] !== 'nav');
  const stepTable = stepRows.length
    ? ['| # | 做什么 | 找哪个元素 | 给什么值 | 页面 |', '|---|---|---|---|---|']
      .concat(stepRows.map(s => `| ${t(s['步骤'])} | ${actName(s['动作'])} | ${t(s['标签'] || s['best定位'])} | ${t(s['值'], '—')} | ${shortUrl(s['页面'])} |`))
      .join('\n')
    : '（这条链路没有可回放的点击步骤，看 scripts/ 里的接口脚本）';

  const mapRows = (mappings || []).filter(m => m['状态'] === '已确认');
  const mapTable = mapRows.length
    ? ['| 源列 | 落到哪 | 规则 |', '|---|---|---|']
      .concat(mapRows.map(m => `| ${t(m['源列'])} | ${t(m['目标表格'])} / ${t(m['目标列'])} | ${t(m['公式/分列规则'] || m['依据'], '直接取')} |`)).join('\n')
    : '（不用粘贴，或映射还没确认）';

  const noteBlock = 备注.length
    ? 备注.map(n => `- 第 ${n.seq ?? n.第几步后 ?? '?'} 步之后：「${n.text || n.原话}」`).join('\n')
    : '（录制时没口述备注——下次录制可以在浮标里说一句，省得后面靠回忆）';

  return `# ${link} · 使用说明书

> 这份是**给人看的**：脚本在 \`scripts/\`，说明书回答「为什么、什么时候、算不算成功」。
> 生成版本：${version || '未标'}　｜　类型：${type === 'api' ? '接口直调（快、稳，不走页面）' : '界面回放（照录制点）'}

## 一、这条链路干什么

${t(trg.用途, '（用途还没问清，见 触发.json 的「待确认」）')}

## 二、什么时候跑

- 方式：${t(触发.方式)}
- 说明：${t(触发.说明 || 触发.条件 || 触发.表达式)}

## 三、一步一步（和 定位库.csv 同序号）

${stepTable}

## 四、每次要给什么

${(trg.参数来源 && trg.参数来源.length)
    ? trg.参数来源.map(p => `- **${t(p.name || p.名)}**：${t(p.from || p.来源)}`).join('\n')
    : '- 待确认（跑之前至少要知道：换日期/换账户/换文件，分别从哪里来）'}

> 判变量的硬口径：同一操作录两遍跑 \`diffrec.mjs\`，不一致的才是变量。
> 只有一遍时可以用 \`infer_params.mjs\` 出提示清单，但那是提示，要人核对。

## 五、跑完落在哪、给谁

- 形态：${t(产出.形态)}
- 位置与接收方：${t(产出.位置与接收方)}
${mapTable === '（不用粘贴，或映射还没确认）' ? '' : '\n映射（下载表 → 目标表）：\n\n' + mapTable + '\n'}

## 六、怎么算跑成功

${t(trg.成功判据, '待确认——没有判据就等于没跑通，别报成功')}

## 七、页面改版了怎么办

1. 脚本会先**逐级降级重试**（L1_id → L2_testid → L3_role → L4_text → L5_css → L6_nth_path），命中哪级会打印 \`[自愈]\`。
2. 想让新定位自动写回定位库：跑的时候加 \`--heal\`。之后就不用再管这一步。
3. 六种定位全找不到 = 真改版，不是小改：用 \`manage.mjs fail\` 标 broken，然后整条重录。

## 八、出问题怎么办

先跑 \`node scripts/diagnose.mjs --err "现象"\`（或看失败时自动打的那五行：现象 / 人话 / 哪坏了 / 下一步 / 要不要重录）。
常见：登录掉线 → 重新登；验证码 → 人工过一次；字段多了少了 → 重出映射，别硬跑。

## 九、录制时你自己说的话（原话，别丢）

${noteBlock}

## 十、失败处理

${t(trg.失败处理)}

${trg.待确认 && trg.待确认.length ? `## 十一、还欠什么（接手的人先补这些）\n\n${trg.待确认.map(p => `- ${t(p.项)}：${t(p.说明)}`).join('\n')}\n` : ''}`;
}

function actName(a) {
  return ({ click: '点一下', fill: '填值', paste: '粘贴数据', copy: '复制', download: '下载文件', select: '选择', upload: '上传', nav: '打开页面' })[a] || a;
}
function shortUrl(u) {
  const s = String(u || '');
  try { const x = new URL(s); return x.host + (x.pathname === '/' ? '' : x.pathname).slice(0, 40); } catch (e) { return s.slice(0, 40) || '—'; }
}
