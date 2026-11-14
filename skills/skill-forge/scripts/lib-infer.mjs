/* lib-infer.mjs — 单遍判参：一次录制就猜出「哪些值是每次要换的变量」
 *
 * 背景：以前只有「同一操作录两遍 → diffrec 比差异」这一条路才知道哪个是变量，
 *       代价是每条链路录两遍。绝大多数值其实一眼能判：日期、单号、金额、接口带出来的值。
 *
 * 口径（先说清楚，免得把噪声当规律）：
 *   1) 只做「提示」，不做「定论」。判成变量也要人去核对一眼；判成常量的也可能要改。
 *   2) 每条都给理由 + 置信度，不写「AI 认为」。置信度 < 0.8 的必须人看。
 *   3) 两遍 diff 仍然是最硬的口径：两遍不一致 = 变量，这个不需要猜。
 *      所以本工具的输出只是「省一遍录制」的入场券，diffrec 保留，随时可复核。
 *   4) 不联网、不调模型，纯规则。
 */

/* 日期 / 单号 / 金额 / 数字 的形态判断 */
const RE = {
  isoDate: /^\d{4}-\d{2}-\d{2}([ T]\d{2}:\d{2}(:\d{2})?)?$/,
  slashDate: /^\d{4}\/\d{1,2}\/\d{1,2}$/,
  cnDate: /^\d{1,2}月\d{1,2}日$|^\d{4}年\d{1,2}月\d{1,2}日$/,
  compactDate: /^(20\d{2})(0[1-9]|1[0-2])(0[1-9]|[12]\d|3[01])$/,
  dateRange: /^\d{4}-\d{2}-\d{2}\s*(~|至|—|-)\s*\d{4}-\d{2}-\d{2}$/,
  longDigits: /^\d{8,}$/,
  mixedId: /^(?=.*\d)[A-Za-z0-9_-]{10,}$/,
  number: /^-?\d+(\.\d+)?$/,
  percent: /^\d+(\.\d+)?%$/
};

const FIELD_HINT = {
  date: /日期|时间|起始|截止|开始|结束|统计|周期|date|time/i,
  amount: /预算|金额|出价|消耗|价格|费用|收入|成本|单价|bid|amount|budget|cost/i,
  count: /数量|条数|笔数|个数|件数|count|num/i,
  name: /账户|名称|品牌|客户|店铺|项目|计划|单元|name|account/i
};

function textOf(v) { return String(v ?? '').trim(); }

/* 这个值是不是出现在接口响应里（= 页面数据带出来的，不是人手敲的） */
function inNetwork(network, value) {
  if (!value || String(value).length < 4) return false;
  const v = String(value);
  for (const r of network || []) {
    const body = [r.respBody, r.body, r.response, r.text].filter(Boolean).join(' ');
    if (body && body.includes(v)) return true;
  }
  return false;
}

/* 这个值是不是出现在动作自己的页面 URL 里（= 页面参数带出来的） */
function inUrl(url, value) {
  const v = textOf(value);
  if (!v || v.length < 2) return false;
  try { return decodeURIComponent(String(url || '')).includes(v); } catch (e) { return String(url || '').includes(v); }
}

export function inferAction(a, network) {
  const raw = textOf(a.value);
  const label = textOf(a.label);
  const type = textOf(a.type);
  const base = { 步骤: String(a.seq ?? ''), 动作: type, 字段: label, 当次的值: raw.slice(0, 40) };

  if (!raw) return { ...base, 判定: '空', 类型: '空值', 置信度: '0.9', 理由: '这一步没填值（纯点击/下载），不存在变量' };
  if (type === 'paste') return { ...base, 判定: '数据块', 类型: '整块粘贴', 置信度: '0.9', 理由: '粘贴的是整块数据，由源表决定，不用判变量' };
  if (type === 'download') return { ...base, 判定: '不适用', 类型: '下载', 置信度: '0.9', 理由: '下载动作没有输入值' };

  const hits = [];

  if (inUrl(a.url, raw)) hits.push({ 判定: '变量', 类型: '页面带出', 置信度: 0.85, 理由: '这个值出现在本页 URL 参数里 = 从上一页/筛选条件带过来的，不是人手敲的' });
  if (inNetwork(network, raw)) hits.push({ 判定: '变量', 类型: '接口带出', 置信度: 0.8, 理由: '这个值出现在某次接口响应里 = 页面数据回填的，换账户/换日期会变' });

  if (RE.dateRange.test(raw) || RE.isoDate.test(raw) || RE.slashDate.test(raw) || RE.cnDate.test(raw) || RE.compactDate.test(raw)) {
    hits.push({ 判定: '变量', 类型: '日期', 置信度: 0.9, 理由: '值本身是日期格式' + (FIELD_HINT.date.test(label) ? '，字段名也是日期口径' : '') });
  } else if (RE.longDigits.test(raw) || RE.mixedId.test(raw)) {
    hits.push({ 判定: '变量', 类型: '单号/ID', 置信度: 0.75, 理由: '长数字/字母数字混合，像订单号、计划 ID、账户 ID' });
  } else if ((RE.number.test(raw) || RE.percent.test(raw)) && FIELD_HINT.amount.test(label)) {
    hits.push({ 判定: '变量', 类型: '金额/数值', 置信度: 0.7, 理由: '字段名是金额/预算类，数值每次可能不同' });
  } else if (RE.number.test(raw) && FIELD_HINT.count.test(label)) {
    hits.push({ 判定: '变量', 类型: '数量', 置信度: 0.65, 理由: '字段名是数量类' });
  }

  if (!hits.length) {
    if (FIELD_HINT.name.test(label) && raw.length <= 20) {
      return { ...base, 判定: '待确认', 类型: '名称类', 置信度: '0.4', 理由: '看着像账户/品牌/计划名：如果只跑一个账户就是常量，跑多账户就是变量——要人定' };
    }
    return { ...base, 判定: '常量', 类型: '固定值', 置信度: '0.6', 理由: '没命中日期/单号/金额/接口特征；按常量处理，换数据时用 diffrec 复核一次' };
  }

  hits.sort((x, y) => y.置信度 - x.置信度);
  const top = hits[0];
  return { ...base, 判定: top.判定, 类型: top.类型, 置信度: String(top.置信度), 理由: top.理由 + (hits.length > 1 ? `（另有 ${hits.length - 1} 条旁证）` : '') };
}

export function inferRecording(rec) {
  const actions = (rec && rec.actions) || [];
  const network = (rec && rec.network) || [];
  const rows = actions.filter(a => a.type === 'fill' || a.type === 'select' || a.type === 'upload')
    .map(a => inferAction(a, network));
  const vars = rows.filter(r => r.判定 === '变量');
  const unsure = rows.filter(r => r.判定 === '待确认' || Number(r.置信度) < 0.8);
  const summary = {
    总填值步骤: rows.length,
    变量: vars.length,
    常量: rows.filter(r => r.判定 === '常量').length,
    待确认: unsure.length,
    要人看的: unsure.map(r => `第${r.步骤}步「${r.字段}」= ${r.当次的值}（${r.类型}，${r.置信度}）`)
  };
  return { rows, summary };
}

export function toCsvText(rows) {
  const header = ['步骤', '动作', '字段', '当次的值', '判定', '类型', '置信度', '理由'];
  const q = (v) => { const s = String(v ?? ''); return /[",\r\n]/.test(s) ? '"' + s.replace(/"/g, '""') + '"' : s; };
  return [header.join(',')].concat(rows.map(r => header.map(h => q(r[h])).join(','))).join('\r\n') + '\r\n';
}
