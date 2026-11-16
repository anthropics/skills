/* lib-guard.mjs — 写接口闸门（合规用，纯函数，无副作用）
 *
 * 为什么有这一层：
 *   录制回放里有两种接口——「读」（GET/HEAD/OPTIONS，拉列表出报表）
 *   和「写」（POST/PUT/PATCH/DELETE，建计划/改预算/提交表单）。
 *   写接口一旦误跑，动的是后台真实数据（广告计划、预算、订单），
 *   所以默认不放开：必须先 --dry 核对，再显式加 --allow-write 才执行。
 *
 * 口径（全库唯一）：WRITE_METHODS 里的方法一律要 --allow-write；
 *   别的（含 GET/HEAD/OPTIONS、空）一律按读处理，不需要开关。
 *
 * 二次确认（安检要求）：--allow-write 只是"我知道这是写接口"，
 *   还必须有 --ack "上限=…｜批准=…" 说明"改多少、谁批的"，两条都要，
 *   缺一条都不跑。确认原文写进 logs/写操作确认.log 留痕。
 */

export const WRITE_METHODS = ['POST', 'PUT', 'PATCH', 'DELETE'];

/** 归一化方法名（空/小写都当 GET） */
export function normMethod(method) {
  const m = String(method ?? '').trim().toUpperCase();
  return m || 'GET';
}

/** 是不是写接口 */
export function isWrite(method) {
  return WRITE_METHODS.includes(normMethod(method));
}

/**
 * 写接口闸门：返回 { ok, code, msg }
 *   ok=true  可以执行
 *   ok=false 必须停下（调用方 print msg 后 exit code，默认 4）
 */
export function writeGate({ method, allowWrite = false, ack = '' } = {}) {
  const m = normMethod(method);
  if (!isWrite(m)) return { ok: true, code: 0, msg: '' };
  if (allowWrite) {
    const a = String(ack || '').trim();
    const bad = a.length < 10 || !a.includes('上限') || !a.includes('批准');
    if (!bad) return { ok: true, code: 0, msg: '' };
    return {
      ok: false,
      code: 5,
      msg: [
        `接口是 ${m}（写接口），已加 --allow-write，但没写清"改多少、谁批的"，本次仍不执行。`,
        '  写之前必须说清两件事，写进 --ack：',
        '  node scripts/api_run.mjs --config <配置> --go --allow-write --ack "上限=<影响范围/数值>｜批准=<谁批的>"',
        '  例如：--ack "上限=单账户预算+200元｜批准=组长 11-07"',
        '  这条会写进 logs/写操作确认.log 留痕，出事能查。'
      ].join('\n')
    };
  }
  return {
    ok: false,
    code: 4,
    msg: [
      `接口是 ${m}（写接口），没加 --allow-write，本次不执行。`,
      '  写接口会动后台真实数据（建计划/改预算/提交表单），先确认清楚：',
      '  ① 先跑 --dry 看 URL 和 BODY 对不对：node scripts/api_run.mjs --config <配置> --dry',
      '  ② 确认无误、确实要写，再执行：node scripts/api_run.mjs --config <配置> --go --allow-write',
      '  ③ 只想拉数据不要写：把配置里的 request.method 改回 GET'
    ].join('\n')
  };
}
