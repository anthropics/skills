#!/usr/bin/env bash
# 加载集群 profile。被其他脚本 source。
#
#   . "$(dirname "$0")/_common.sh"
#   load_cluster "$CLUSTER"        # 空则自动选择
#
# 自动选择规则：clusters/ 下只有一个非模板 profile 时用它，否则要求显式指定。

REPO_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
CLUSTER_DIR="$REPO_ROOT/clusters"

die() { printf '错误: %s\n' "$1" >&2; exit 1; }
info() { printf '  %s\n' "$1"; }

list_clusters() {
    find "$CLUSTER_DIR" -maxdepth 1 -name '*.conf' ! -name '_*' -exec basename {} .conf \; 2>/dev/null | sort
}

refresh_live_node_count() {
    [ "${SCNET_HPC_LIVE_NODE_COUNT:-yes}" != "no" ] || return 0
    [ "${SCHEDULER:-slurm}" = "slurm" ] || return 0
    [ -n "${CLUSTER_ID:-}" ] || return 0
    [ -n "${PARTITION:-}" ] || return 0

    local live
    live=$(ssh -o BatchMode=yes -o ConnectTimeout=10 -o ServerAliveInterval=15 -o ServerAliveCountMax=2 \
        "$CLUSTER_ID" "scontrol show partition ${PARTITION}" 2>/dev/null \
        | tr ' ' '\n' | sed -n 's/^TotalNodes=//p' | head -1)

    if [[ "$live" =~ ^[0-9]+$ ]] && [ "$live" -gt 0 ]; then
        NODE_COUNT="$live"
        NODE_COUNT_SOURCE="live"
    else
        NODE_COUNT_SOURCE="${NODE_COUNT_SOURCE:-profile/cache}"
    fi
}

load_cluster() {
    local want="${1:-}"
    local available
    available=$(list_clusters)

    [ -n "$available" ] || die "clusters/ 下没有可用的 profile。
从模板新建一个：
  cp $CLUSTER_DIR/_template.conf $CLUSTER_DIR/<集群短名>.conf"

    if [ -z "$want" ]; then
        local count
        count=$(printf '%s\n' "$available" | grep -c .)
        if [ "$count" -eq 1 ]; then
            want="$available"
        else
            die "有多个集群 profile，请用 --cluster <名> 指定：
$(printf '%s\n' "$available" | sed 's/^/  /')"
        fi
    fi

    local conf="$CLUSTER_DIR/$want.conf"
    [ -f "$conf" ] || die "找不到 profile: $conf
可用的：
$(printf '%s\n' "$available" | sed 's/^/  /')"

    # shellcheck disable=SC1090
    . "$conf"

    [ -n "${CLUSTER_ID:-}" ] || die "$conf 里 CLUSTER_ID 为空"
    : "${SSH_PORT:=22}"
    : "${HOME_BASE:=/public/home}"

    # SSH_HOST/SSH_PORT 应以 profile 为准。这里只作为兼容回退：
    # 旧 profile 漏填时，从本机 ~/.ssh/config 动态补全，避免脚本直接失败。
    if [ -z "${SSH_HOST:-}" ]; then
        SSH_HOST="$(ssh -G "$CLUSTER_ID" 2>/dev/null | awk '/^hostname /{print $2; exit}')"
    fi
    if [ -z "${SSH_PORT:-}" ]; then
        SSH_PORT="$(ssh -G "$CLUSTER_ID" 2>/dev/null | awk '/^port /{print $2; exit}')"
    fi
    REMOTE_USER_DETECTED="$(ssh -G "$CLUSTER_ID" 2>/dev/null | awk '/^user /{print $2; exit}')"
    : "${REMOTE_USER_DETECTED:=}"

    # 用于设置新连接的新集群仍需明确的 SSH_HOST/SSH_PORT；已有本机 ssh 别名时
    # 这里会从 ssh -G 补齐。若仍为空，给一个可操作的错误。
    [ -n "$SSH_HOST" ] || die "$conf 里 SSH_HOST 为空，且 ssh -G ${CLUSTER_ID} 也解析不到 HostName；请先配置 ~/.ssh/config 或补 profile。"

    CLUSTER_CONF="$conf"
    CLUSTER_AUTO_CONF="$CLUSTER_DIR/.cache/$want.auto.conf"
    if [ "${SCNET_HPC_USE_AUTO:-yes}" != "no" ] && [ -f "$CLUSTER_AUTO_CONF" ]; then
        # shellcheck disable=SC1090
        . "$CLUSTER_AUTO_CONF"
    fi

    refresh_live_node_count
}

# 从参数里摘出 --cluster <名>，剩下的放进 REST[]
parse_cluster_arg() {
    CLUSTER=""
    REST=()
    while [ $# -gt 0 ]; do
        case "$1" in
            --cluster)
                [ $# -ge 2 ] || die "--cluster 缺少参数"
                CLUSTER="$2"
                shift 2
                ;;
            --cluster=*) CLUSTER="${1#*=}"; shift ;;
            *) REST+=("$1"); shift ;;
        esac
    done
    if [ -n "$CLUSTER" ]; then
        [[ "$CLUSTER" =~ ^[A-Za-z0-9][A-Za-z0-9._-]*$ ]] \
            || die "集群短名包含不安全字符"
    fi
}
