/* trigger.mjs — 「什么时候跑」这段的唯一生成处
 * interview.mjs 用它打印，build_skill.mjs 用它写进子技能 SKILL.md —— 一处口径，不许两边各写一份
 * 逻辑：能答的都写实；没答上来的不编，统一列在「还欠确认」里，让接手的人知道边界在哪 */
import fs from 'node:fs';
import path from 'node:path';

export function triggerSection(t) {
  const L = [];
  L.push('## 什么时候跑（录制后问过用户，按这个跑，别自己改）');
  L.push('');
  L.push(`- **用途**：${t.用途 || '待确认'}`);
  if (t.触发?.方式 === 'cron') {
    L.push(`- **触发**：定时 —— \`${t.触发.表达式 || '待确认'}\`${t.触发.说明 && t.触发.说明 !== '待确认' ? `（${t.触发.说明}）` : ''}`);
  } else if (t.触发?.方式 === 'event') {
    L.push(`- **触发**：事件 —— ${t.触发.条件 || '待确认'}`);
    L.push('- **注意**：事件触发要看住「多久查一次」和「一次最多动多少」，别做成无限自动执行');
  } else {
    L.push(`- **触发**：${t.触发?.说明 || '待确认'}`);
  }

  const out = t.产出;
  if (out && typeof out === 'object') {
    const kinds = (out.形态 || []).join(' + ') || '待确认';
    L.push(`- **产出形态**：${kinds}`);
    L.push(`- **落在哪、给谁**：${out.位置与接收方 || '待确认'}`);
    if (out.映射) L.push(`- **映射**：${out.映射}`);
  } else {
    L.push(`- **产出**：${out || '待确认'}`);
  }

  L.push(`- **参数从哪来**：${(t.参数来源 || []).map(p => `${p.name}（${p.from}）`).join('、') || '待确认'}`);
  L.push(`- **怎么算成功**：${t.成功判据 || '待确认'}`);
  L.push(`- **失败怎么办**：${t.失败处理 || '待确认'}`);

  if (t.写操作?.是否写 === true) {
    const limit = t.写操作.上限与确认 || '待确认';
    L.push(`- **⚠️ 会改数据**：${limit} —— 真提交前必须问人，先 DryRun`);
  } else if (t.写操作?.是否写 === '待确认') {
    L.push('- **⚠️ 还没确认会不会改数据**：先按「会改」对待，跑之前问一句');
  } else {
    L.push('- **只读**：不改任何数据');
  }

  if (Array.isArray(t.待确认) && t.待确认.length) {
    L.push('');
    L.push('### 还欠确认（问的时候没答上来，别当成已定）');
    L.push('');
    for (const p of t.待确认) L.push(`- ${p.项} —— ${p.说明}`);
    L.push('');
    L.push('补齐方式：`node scripts/interview.mjs --link <链路名>` 再问一遍，然后重新生成。');
  }
  return L.join('\n') + '\n';
}

/** 读需求访谈产物；没有就返回 null（调用方决定是拒绝还是打警告） */
export function readTrigger(cfgDir, link, root) {
  const cands = [
    path.join(cfgDir, '触发.json'),
    path.join(root, 'produced', link, '配置', '触发.json')
  ];
  const f = cands.find(p => fs.existsSync(p));
  if (!f) return null;
  try {
    return { file: f, data: JSON.parse(fs.readFileSync(f, 'utf8')) };
  } catch {
    return null;
  }
}

/** 没问过需求时，子技能顶部插一条显眼待办（不是静默放过） */
export function missingTriggerNotice(link) {
  return [
    '## ⚠️ 这条链路还没问过需求',
    '',
    '现在它只是「录下来的点击顺序」——什么时候跑、参数从哪来、跑完给谁、失败找谁都没定，',
    '照着跑只能算重复一遍人工操作，不算自动化。',
    '',
    `补法：\`node scripts/interview.mjs --link ${link}\`，答完再重新生成一次。`,
    ''
  ].join('\n');
}
