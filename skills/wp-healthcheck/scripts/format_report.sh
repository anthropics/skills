#!/usr/bin/env bash
# format_report.sh — render the diagnostic findings as a Markdown report.
# 使い方: format_report.sh <work_dir> <base_url>
#
# 期待入力: work_dir/findings.tsv （check_wp.sh が生成）
#   1列目: 項目キー（例: wp_version, ssl_cert）
#   2列目: ステータス（OK / WARNING / CRITICAL / UNKNOWN）
#   3列目: 一行サマリ
#   4列目: 詳細（パイプ `|` 区切りで複数行可）

set -euo pipefail

WORK_DIR="${1:-}"
BASE_URL="${2:-}"

if [ -z "$WORK_DIR" ] || [ -z "$BASE_URL" ]; then
  echo "Usage: $0 <work_dir> <base_url>" >&2
  exit 2
fi

FINDINGS="$WORK_DIR/findings.tsv"
if [ ! -f "$FINDINGS" ]; then
  echo "Error: $FINDINGS not found." >&2
  exit 1
fi

# ステータス別カウント
COUNT_OK=$(awk -F'\t' '$2=="OK"{c++} END{print c+0}' "$FINDINGS")
COUNT_WARN=$(awk -F'\t' '$2=="WARNING"{c++} END{print c+0}' "$FINDINGS")
COUNT_CRIT=$(awk -F'\t' '$2=="CRITICAL"{c++} END{print c+0}' "$FINDINGS")
COUNT_UNK=$(awk -F'\t' '$2=="UNKNOWN"{c++} END{print c+0}' "$FINDINGS")

# 全体評価
if [ "$COUNT_CRIT" -gt 0 ]; then
  OVERALL="Action required"
elif [ "$COUNT_WARN" -gt 0 ]; then
  OVERALL="Attention recommended"
elif [ "$COUNT_OK" -eq 0 ] && [ "$COUNT_UNK" -gt 0 ]; then
  # OK が0件で UNKNOWN ばかり = 観測自体ができていない
  OVERALL="Could not assess (site unreachable or non-responsive)"
else
  OVERALL="Healthy on observable surfaces"
fi

NOW_UTC=$(date -u '+%Y-%m-%d %H:%M:%S UTC')

# 項目キー → 表示名のマッピング（bash 3.2 互換のため case で実装）
label_for_key() {
  case "$1" in
    wp_version)       echo "WordPress version" ;;
    theme)            echo "Active theme" ;;
    ssl_cert)         echo "SSL / TLS certificate" ;;
    sec_headers)      echo "Security headers" ;;
    robots_sitemap)   echo "robots.txt and sitemap" ;;
    response_time)    echo "Top page response time" ;;
    api_surface)      echo "Public API surface" ;;
    plugins)          echo "Plugin fingerprints" ;;
    *)                echo "$1" ;;
  esac
}

# レポート出力
cat <<EOF
# WordPress Healthcheck Report

- Target: ${BASE_URL}
- Generated: ${NOW_UTC}
- Skill: wp-healthcheck (Phase 1, standalone external probe)

## Summary

- Overall: **${OVERALL}**
- OK: ${COUNT_OK} / WARNING: ${COUNT_WARN} / CRITICAL: ${COUNT_CRIT} / UNKNOWN: ${COUNT_UNK}

| Item | Status | Summary |
|---|---|---|
EOF

# テーブル行
while IFS=$'\t' read -r key status summary _detail; do
  label=$(label_for_key "$key")
  echo "| ${label} | ${status} | ${summary} |"
done < "$FINDINGS"

cat <<'EOF'

## Findings (detail)

EOF

# 詳細セクション
while IFS=$'\t' read -r key status summary detail; do
  label=$(label_for_key "$key")
  echo "### ${label} — ${status}"
  echo ""
  echo "${summary}"
  echo ""
  if [ -n "$detail" ]; then
    # detail内は `|` を改行に変換
    echo "$detail" | tr '|' '\n' | while IFS= read -r line; do
      [ -n "$line" ] && echo "- ${line}"
    done
    echo ""
  fi
done < "$FINDINGS"

cat <<'EOF'
## Limitations

This report is built **only from publicly accessible information** (HTML, headers, well-known
endpoints, TLS certificate). It cannot:

- Determine actual installed plugin versions (only slugs visible in HTML).
- See plugins that are active only in the WordPress admin (SEO, cache, backup, security
  managers). Front-end-invisible plugins leave no fingerprint in public HTML, so the
  detected plugin count is a **lower bound**, not a complete inventory.
- Inspect database, wp-config.php, or admin-only state.
- Detect exploited backdoors or compromised content not exposed on the front page.

For an internal audit (file integrity, cron schedule, user roles, transient state, full
plugin inventory), use a dedicated WordPress maintenance plugin that runs inside the site.

## References

See `references/checklist.md` in the skill directory for the full judgement criteria.
EOF
