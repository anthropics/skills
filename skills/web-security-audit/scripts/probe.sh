#!/usr/bin/env bash
# Web 安全审计 · 负面行为测试探测脚本（非破坏性）
# 用法: ./probe.sh <https://target>
# 依赖: curl
# 所有请求均为无害验证性请求：不注入真实 payload 落地数据、不爆破、不写操作。
set -u
BASE="${1:?用法: probe.sh <https://target>}"
echo "=== [1/3] 公开接口畸形输入（断言 400/422；500=缺参数校验，需查响应体是否泄露） ==="
probe_inject() {
  local url="$1"
  for payload in "'" "1%20OR%201=1" "'%20OR%201=1--" "-1" "0" "999999999999" "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"; do
    code=$(curl -s -o /dev/null -w "%{http_code}" --max-time 15 "${url}${payload}")
    printf "  %-70s -> %s\n" "${url}${payload}" "$code"
  done
}
# 按目标项目实际公开接口调整（示例：/api/articles?limit= 与 ?page=）
probe_inject "$BASE/api/articles?limit="
probe_inject "$BASE/api/articles?page="

echo "=== [2/3] 敏感路径 + content-type 校验（text/html=SPA 兜底假象；真实 MIME=真泄露 Critical） ==="
for p in /db/blog.db /data/blog.db /blog.db /backup/blog.db /server.js /db/init.js \
         /package.json /config.json /.git/HEAD /.git/config /.env /.DS_Store /public/uploads/; do
  hdr=$(curl -s -D - -o /dev/null -L --max-time 15 "$BASE$p")
  code=$(echo "$hdr" | grep -iE "^HTTP/" | tail -1 | awk '{print $2}')
  ct=$(echo "$hdr" | grep -i "^content-type" | tail -1 | tr -d '\r' | cut -d' ' -f2-)
  printf "  %-20s -> %s  %s\n" "$p" "${code:-000}" "$ct"
done

echo "=== [3/3] 未知路径 404 语义（带扩展名必须 404；目录遍历应 400/403） ==="
printf "  %-50s -> %s\n" "/does-not-exist-xyz" "$(curl -s -o /dev/null -w '%{http_code}' --max-time 15 "$BASE/does-not-exist-xyz")"
printf "  %-50s -> %s\n" "/does-not-exist-xyz.js" "$(curl -s -o /dev/null -w '%{http_code}' --max-time 15 "$BASE/does-not-exist-xyz.js")"
printf "  %-50s -> %s\n" "/%2e%2e/%2e%2e/server.js" "$(curl -s -o /dev/null -w '%{http_code}' --max-time 15 --path-as-is "$BASE/%2e%2e/%2e%2e/server.js")"

echo "=== 完成（全部为非破坏性验证请求） ==="
