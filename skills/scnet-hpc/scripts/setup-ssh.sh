#!/usr/bin/env bash
# 在一台新的个人电脑（macOS / Linux）上配置到超算集群的 SSH 连接。
#
#   ./setup-ssh.sh [--cluster <集群短名>] <私钥文件> [用户名]
#
# 集群参数从 clusters/<集群短名>.conf 读取。只有一个 profile 时可省略 --cluster。
# 幂等：重复运行只补齐缺失项，不覆盖已有的正确配置。

set -euo pipefail

. "$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)/_common.sh"

parse_cluster_arg "$@"
set -- "${REST[@]+${REST[@]}}"

KEY_SRC="${1:-}"
USER_NAME="${2:-}"

if [ -z "$KEY_SRC" ]; then
    cat >&2 <<EOF
用法: $0 [--cluster <集群短名>] <私钥文件> [用户名]

私钥从超算平台控制台下载。

可用的集群 profile：
$(list_clusters | sed 's/^/  /')
EOF
    exit 1
fi

SCNET_HPC_LIVE_NODE_COUNT=no
load_cluster "$CLUSTER"
unset SCNET_HPC_LIVE_NODE_COUNT

[ -f "$KEY_SRC" ] || die "找不到私钥文件: $KEY_SRC"
grep -q "BEGIN.*PRIVATE KEY" "$KEY_SRC" \
    || die "$KEY_SRC 看起来不是私钥（没有 'BEGIN ... PRIVATE KEY' 头）"

KEY_DST="$HOME/.ssh/id_rsa_${CLUSTER_ID}"
SSH_CONFIG="$HOME/.ssh/config"
SOCKET_DIR="$HOME/.ssh/sockets"

# 从文件名推断用户名，形如 <用户名>_<主机标识>_RsaKeyExpireTime_<日期>.txt
if [ -z "$USER_NAME" ] && [ -n "${KEY_NAME_MARKER:-}" ]; then
    base=$(basename "$KEY_SRC")
    case "$base" in
        *"$KEY_NAME_MARKER"*) USER_NAME="${base%%"$KEY_NAME_MARKER"*}" ;;
    esac
fi
[ -n "$USER_NAME" ] || die "无法从文件名推断用户名，请作为最后一个参数传入"

echo "==> 集群: ${CLUSTER_ID} (${CLUSTER_DESC:-$SSH_HOST})"
echo "==> 用户名: ${USER_NAME}"

# ---------------------------------------------------------------- 私钥
echo "==> 安装私钥"
mkdir -p "$HOME/.ssh"
chmod 700 "$HOME/.ssh"

if [ -f "$KEY_DST" ] && ! cmp -s "$KEY_SRC" "$KEY_DST"; then
    backup="$KEY_DST.bak.$(date +%Y%m%d%H%M%S)"
    cp "$KEY_DST" "$backup"
    info "已存在不同的私钥，备份到 $(basename "$backup")"
fi

# 源和目标可能是同一个文件（重复运行时），cp 会报错
if [ "$(cd "$(dirname "$KEY_SRC")" && pwd)/$(basename "$KEY_SRC")" != "$KEY_DST" ]; then
    cp "$KEY_SRC" "$KEY_DST"
fi
chmod 600 "$KEY_DST"

# macOS 的下载文件带隔离属性，会让某些工具拒绝读取
if [ "$(uname -s)" = "Darwin" ]; then
    xattr -c "$KEY_DST" 2>/dev/null || true
fi
info "$KEY_DST (600)"

if ssh-keygen -y -f "$KEY_DST" > "$KEY_DST.pub" 2>/dev/null; then
    chmod 644 "$KEY_DST.pub"
    info "$(ssh-keygen -lf "$KEY_DST" 2>/dev/null | awk '{print $1, $2, $4}')"
else
    rm -f "$KEY_DST.pub"
    info "私钥有 passphrase，跳过公钥推导"
fi

# ---------------------------------------------------------------- config
echo "==> 配置 ~/.ssh/config"
mkdir -p "$SOCKET_DIR"
chmod 700 "$SOCKET_DIR"
touch "$SSH_CONFIG"
chmod 600 "$SSH_CONFIG"

# Host 行可能列多个别名（"Host a b"），按词比对而不是用正则拼
if awk -v alias="$CLUSTER_ID" '
        $1 == "Host" { for (i = 2; i <= NF; i++) if ($i == alias) { found = 1; exit } }
        END { exit(found ? 0 : 1) }
    ' "$SSH_CONFIG"; then
    info "已存在 Host ${CLUSTER_ID}，跳过（如需重配请先手工删除该段）"
else
    # macOS 的 ssh-agent 能存进 Keychain；Linux 上这两个选项不被识别
    keychain_opts=""
    if [ "$(uname -s)" = "Darwin" ]; then
        keychain_opts="
  UseKeychain yes
  AddKeysToAgent yes"
    fi

    hostkey_opt=""
    if [ "${NEEDS_UPDATE_HOSTKEYS_NO:-no}" = "yes" ]; then
        hostkey_opt="
  # 该平台对主机密钥轮换扩展返回错误签名，关掉以消除告警噪音
  # （首次记录的主机密钥仍在正常校验，不影响安全性）
  UpdateHostKeys no"
    fi

    cat >> "$SSH_CONFIG" <<EOF

Host ${CLUSTER_ID} ${SSH_HOST}
  HostName ${SSH_HOST}
  User ${USER_NAME}
  Port ${SSH_PORT}
  IdentityFile ${KEY_DST}
  IdentitiesOnly yes${keychain_opts}
  # 长连接：复用同一条 TCP/认证通道，后续命令从 ~2s 降到 ~0.5s
  ControlMaster auto
  ControlPath ${SOCKET_DIR}/%r@%h-%p
  ControlPersist 10m
  # 保活：防止空闲会话被中间网关静默切断
  ServerAliveInterval 60
  ServerAliveCountMax 3
  TCPKeepAlive yes${hostkey_opt}
EOF
    info "已追加 Host ${CLUSTER_ID}"
fi

# ---------------------------------------------------------------- 验证
echo "==> 测试连接"
if out=$(ssh -o BatchMode=yes -o ConnectTimeout=20 \
             -o StrictHostKeyChecking=accept-new \
             "$CLUSTER_ID" 'echo OK; hostname; whoami' 2>&1); then
    printf '%s\n' "$out" | sed 's/^/  /'
    echo
    echo "完成。用法：ssh ${CLUSTER_ID}"
else
    printf '%s\n' "$out" | sed 's/^/  /'
    echo
    die "连接失败。检查：私钥是否过期、本机 IP 是否在平台白名单内、端口 ${SSH_PORT} 是否可达"
fi
