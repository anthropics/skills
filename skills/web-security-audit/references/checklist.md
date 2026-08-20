# Web 安全审计核查清单

> 配套 `web-security-audit` skill 使用。审计时按需加载：白盒逐类核查（第一节）、负面测试三件套（第二节）、黑盒行为核查（第三节）、报告模板（第四节）、常见陷阱（第五节）。

## 一、白盒核查项（逐类静态核查，每项给出"存在/不存在 + 证据行号"）

### 1. SQL 注入
- [ ] 所有动态 SQL 是否参数化（prepare + 绑定）？无字符串拼接（`${}`、`+`、concat）？
- [ ] ORDER BY / 表名 / 列名等不可参数化位置是否走白名单？
- [ ] LIKE 通配符用户输入是否转义？
- [ ] **注意：参数化 ≠ 参数合法**——`LIMIT ?` 绑定 `'` 会在 SQLite 层抛错 → catch 兜底 500（需类型校验 + 回 400）。

### 2. XSS
- [ ] Markdown 渲染：`marked` v12+ 无内置 sanitize → 必须 `DOMPurify.sanitize()` 后注入；
- [ ] 所有 `innerHTML` / `insertAdjacentHTML` 注入点是否消毒或转义？
- [ ] 存储型：文章正文、评论、设置项（`site_name` / `about_content` / `hero_*`）的渲染路径；
- [ ] 属性注入：值是否可能突破 `style=""`（如 `hero_bg` 应校验字符集）；
- [ ] SVG 上传（SVG 可含脚本，经 `<object>` 或直接打开执行）是否禁传；
- [ ] CSP 是否设置 `object-src 'none'` 封死 SVG 执行。

### 3. 认证与会话
- [ ] 默认口令/硬编码口令（init 脚本、README、测试代码）；
- [ ] 口令哈希强度（PBKDF2 ≥100k / bcrypt / scrypt）；
- [ ] token 存储：localStorage（XSS 可盗）vs HttpOnly Cookie（后者必须配 CSRF 防护）；
- [ ] token 过期与登出撤销；
- [ ] 强制改密标志（`force_change_pwd`）是否覆盖存量用户（**新增列默认 NULL 不会触发**——存量库要设值）；
- [ ] 登录错误信息是否统一（防用户枚举）；
- [ ] 登录限流（次数/窗口/429，注意锁定 IP 影响自身）。

### 4. 越权 / IDOR
- [ ] 资源改/删操作是否校验归属（作者/角色），还是"仅登录即可操作任意 ID"；
- [ ] 管理员接口是否仅 admin 角色可用（角色校验中间件）。

### 5. CSRF
- [ ] 是否用 Cookie 会话？是 → 需 CSRF Token / SameSite=Strict|Lax；
- [ ] Bearer token（localStorage）+ 无 Cookie 会话 → 天然免疫，标注即可。

### 6. 文件上传
- [ ] 扩展名白名单（禁 exe/html/svg/php）；
- [ ] MIME 校验 + 内容嗅探（不能只看 Content-Type）；
- [ ] 文件名随机化、存储路径不可执行、无目录穿越；
- [ ] 上传接口是否 authRequired。

### 7. 路径遍历与敏感文件
- [ ] 静态服务根目录只指向 `public/`（serve-static 默认防 `../`，但要验证）；
- [ ] 数据库 / 源码 / `.env` / `.git` / 备份文件是否可下载；
- [ ] SPA 兜底路由是否把带扩展名路径也回 200（见第二节第 3 条）。

### 8. SSRF
- [ ] URL 抓取/代理功能是否过滤内网（127.0.0.1、10.x、172.16-31.x、192.168.x、169.254.169.254 云元数据）。

### 9. 信息泄露
- [ ] 错误页是否回显堆栈/SQL（应统一 `{"error":"..."}` 通用消息）；
- [ ] `x-powered-by` / `server` 版本头（建议 `app.disable('x-powered-by')`）；
- [ ] 前端注释、调试开关、测试路由是否残留。

### 10. 依赖漏洞
- [ ] 主要依赖是否有已知 CVE（marked、multer、express、node 版本等）——记录版本号与排期。

## 二、负面行为测试三件套（必做）

### 1. 公开接口畸形输入
```bash
BASE=https://target
# 对每个公开参数依次替换：' | 1 OR 1=1 | ' OR 1=1-- | -1 | 0 | 999999999999 | 超长串
curl -s -o /dev/null -w "%{http_code}\n" "$BASE/api/articles?limit='"
curl -s -o /dev/null -w "%{http_code}\n" "$BASE/api/articles?limit=1%20OR%201=1"
curl -s -G -o /dev/null -w "%{http_code}\n" --data-urlencode "q=' OR 1=1--" "$BASE/api/articles"
# 判定：400/422 = 健康；500 = 缺参数校验（查响应体是否泄露 SQL/堆栈）；200+正常数据 = 参数被忽略（可接受但标注）
```

### 2. 敏感路径 + content-type 校验（关键：必须看 content-type，不能只看状态码）
```bash
for p in /db/blog.db /data/blog.db /blog.db /backup/blog.db /server.js /db/init.js \
         /package.json /config.json /.git/HEAD /.git/config /.env /.DS_Store /public/uploads/; do
  printf "%-20s " "$p"
  curl -s -D - -o /dev/null -L "$BASE$p" | grep -iE "^(HTTP/2|content-type)" | tr '\n' ' '; echo
done
# 判定：
#   404                  = 无泄露
#   200 + text/html      = SPA 兜底假象（非真泄露，但兜底过宽需修）
#   200 + 真实 MIME      = 真泄露（Critical：源码/数据库可下载）
```

### 3. 未知路径 404 语义
```bash
curl -s -o /dev/null -w "%{http_code}\n" "$BASE/does-not-exist-xyz"      # SPA 路由可 200
curl -s -o /dev/null -w "%{http_code}\n" "$BASE/does-not-exist-xyz.js"   # 带扩展名必须 404
curl -s -o /dev/null -w "%{http_code}\n" --path-as-is "$BASE/%2e%2e/%2e%2e/server.js"  # 目录遍历应 400/403
```

## 三、黑盒行为核查项

- [ ] 安全响应头：CSP / `X-Frame-Options: DENY` / `nosniff` / `Referrer-Policy` / HSTS / `Permissions-Policy`；
- [ ] HTTP → HTTPS 301；
- [ ] 受保护 API 未授权 → 401（`/api/auth/check` 等）；
- [ ] 写接口未授权 → 401（upload / PUT / DELETE）；
- [ ] 默认口令**单次**探测（先告知用户）；
- [ ] 不存在资源 ID → 404（而非 500/200）。

## 四、报告模板

```
# <项目> 安全审计报告（白盒+黑盒）
- 目标 / 时间 / 方式（授权 · 非破坏性）
## 结论总览（分级表：Critical/High/Medium/Low/Info + 数量）
## 直接回答用户核心问题（如"有没有后门""会不会被爆库"）
## 风险明细（每项：现象 / 影响 / 修复代码 / 验证方法 / 是否已修）
## 已验证生效的安全项
## 黑盒未覆盖项声明
```

## 五、常见陷阱（本 skill 沉淀来源，均已实测踩过）

1. **参数化 ≠ 参数合法**：`LIMIT ?` 绑定 `'` → SQLite 抛错 → 500。公开接口畸形输入必须断言 400 而非 500。
2. **SPA 兜底假象**：`app.get('*')` 兜底把 `/db/blog.db`、`/server.js` 全变 200 + index.html——扫描器误判泄露。判定必须看 content-type；修复：带扩展名路径交回 404。
3. **白盒漏"行为侧"问题**：只测正向冒烟会漏畸形输入/未知路径——负面测试必须与正向并列（2026-08-20 线上黑盒才抓到两处 Medium 的教训）。
4. **init 脚本删库重建**：库存在应 `process.exit(1)` 中止，仅 `FORCE_DB_RESET=1` 才重建，防手动跑清空生产。
5. **生产库新增列必须自愈迁移**：server 启动时幂等 `ALTER TABLE ... ADD COLUMN`（捕获 duplicate 忽略），否则 `git pull` 后热路径 `SELECT` 新列 → `no such column` 全站崩溃。
6. **登录限流测试会锁出口 IP**：15 分钟 5 次失败 → 429，可能影响用户自己访问后台；权衡或提前告知。
7. **错误响应**：500 必须回统一 `{"error":"查询失败"}`，绝不回显 SQL 错误/堆栈。
