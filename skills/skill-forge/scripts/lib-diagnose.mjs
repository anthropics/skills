/* diagnose.mjs（lib）— 失败归因的唯一定义处：退出码/报错/HTTP → 人话 + 下一步 + 要不要重录
 * 被两个地方用：scripts/diagnose.mjs（命令行解释）、scripts/manage.mjs fail（记失败时自动归因）
 * 铁律：只按「看到的东西」归因；认不出来就说认不出来，并列出该补哪条信息，绝不硬猜。 */

export function diagnose({ err = '', http = '', exit = '', rows = null, fields = null, stage = '' } = {}) {
  const httpS = String(http || '');
  const exitS = String(exit || '');
  const text = `${err} ${httpS} ${stage}`.toLowerCase();
  const hit = RULES.find(r => r.hit({ text, http: httpS, exit: exitS, rows, fields }));
  return hit ? { ...hit } : null;
}

/* 规则表：命中即给「人话 + 下一步 + 要不要重录」。顺序 = 优先级（越具体越靠前）。 */
const RULES = [
  {
    id: 'CAPTCHA',
    hit: ({ text, http, exit, rows, fields }) => /captcha|验证码|人机|滑块|verify/.test(text),
    what: '页面弹了验证码/人机校验，脚本点不过去',
    why: '不是脚本写错，是站点在拦自动化',
    next: '改走扫码登录：node scripts/login.mjs --profile <档案目录> --manual；或换有登录态的档案跑',
    redo: '不要（重录也一样被拦）',
    human: '这页现在要验证码，机器过不去，得你手动登一次。'
  },
  {
    id: 'LOGIN',
    hit: ({ text, http, exit, rows, fields }) => /^(401|403)$/.test(http) || /401|403|unauthorized|forbidden|未登录|登录失效|请重新登录|token/.test(text),
    what: '登录态失效（站点把你当未登录）',
    why: 'Cookie/token 过期，通常是隔夜或换了档案',
    next: '重登一次再跑：node scripts/login.mjs --profile <档案目录>（或人工登录同一档案）；不用改脚本',
    redo: '不要',
    human: '登录过期了，重新登一次就好，脚本没坏。'
  },
  {
    id: 'RATE',
    hit: ({ text, http, exit, rows, fields }) => /^(429|503)$/.test(http) || /429|rate.?limit|too many|限流|请求过频/.test(text),
    what: '请求太频被限流',
    why: '并发/频率超了站点阈值',
    next: '降频重试：加 --delay 500，或把批量拆两批；同一天别反复重跑',
    redo: '不要',
    human: '站点限流了，等几分钟、放慢一点再跑。'
  },
  {
    id: 'SEL',
    hit: ({ text, http, exit, rows, fields }) => /^(3)$/.test(exit) || /not found|找不到|no node|queryselector|选择器|selector|元素|定位|click/.test(text),
    what: '点不到页面上的元素（按钮/输入框/表格不见了）',
    why: '页面改版、弹窗挡住、或入口换了位置',
    next: '先按浮标/截图看重放停在哪个页面；确认改版就重录这条链路（旧版保留 7 天）',
    redo: '要（确认页面变了就重录）',
    human: '页面上那个按钮找不到了，多半是网站改版了，要重录一遍。'
  },
  {
    id: 'FIELDS',
    hit: ({ text, http, exit, rows, fields }) => fields != null && /字段|field/.test(text) || /字段数|fieldCount|字段缺失/.test(text),
    what: '字段数/字段名和配置对不上（接口可能加了或少了列）',
    why: '接口改版最常见：加了新字段或改了字段名',
    next: '先 --dry 看原始返回；只多不少 → 更新 配置/接口.json 的 fields；少了 → 重录并重跑 diffrec',
    redo: '字段变少/改名才要',
    human: '回来的数据列变了，要么是网站加了新列（好办），要么是改版（要重录）。'
  },
  {
    id: 'EMPTY',
    hit: ({ text, http, exit, rows, fields }) => rows != null && Number(rows) === 0 || /行数为\s*0|empty|没有数据|无数据/.test(text),
    what: '接口通了但一条数据都没拿到',
    why: '多半是参数不对（日期/账号/筛选条件），不是脚本坏',
    next: '用 --dry 打印真实 URL 和 body，和浏览器 F12 里的请求逐字对一遍（日期格式、账号 id 最常错）',
    redo: '参数都对还没数据，才考虑重录',
    human: '连上了但捞回来是空的，先看是不是日期或账号参数填错了。'
  },
  {
    id: 'TIMEOUT',
    hit: ({ text, http, exit, rows, fields }) => /timeout|timed out|超时|etimedout|navigation/.test(text),
    what: '等页面/等接口超时',
    why: '站点慢、网络抖，或页面卡在某个加载中',
    next: '加大超时（--timeout 60000）重试一次；连续 3 次同一步超时才当改版处理',
    redo: '连续 3 次才考虑',
    human: '这次是等太久超时了，通常是网络或网站慢，重跑一次多半就好。'
  },
  {
    id: 'SERVER',
    hit: ({ text, http, exit, rows, fields }) => /^(500|502|504)$/.test(http) || /50[024]|internal server error|bad gateway/.test(text),
    what: '是网站自己出错了（不是我们脚本的问题）',
    why: '后端异常或维护',
    next: '过 10 分钟再跑；持续报 5xx 就找系统方，别反复重录',
    redo: '不要',
    human: '是网站那边出错了，跟我们脚本无关，等会儿再跑。'
  },
  {
    id: 'FS',
    hit: ({ text, http, exit, rows, fields }) => /enoent|eacces|ebusy|文件|目录|磁盘|权限|permission denied/.test(text),
    what: '文件写不进去/读不到（路径或占用）',
    why: '路径不对、文件正被 Excel 打开、或没权限',
    next: '关掉正打开该文件的 Excel/WPS；确认目录存在；换到有写权限的路径',
    redo: '不要',
    human: '表格写不进去，多半是文件正开着，关掉重跑即可。'
  }
];

