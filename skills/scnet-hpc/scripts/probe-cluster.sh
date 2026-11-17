#!/usr/bin/env bash
# 探测一个已能 SSH 登录的集群，输出可直接保存为 profile 的内容。
#
#   ./probe-cluster.sh <ssh别名或host> [集群短名] > ../clusters/<集群短名>.conf
#
# 新增集群时先手工能 ssh 上去，再跑这个脚本自动填大部分字段。
# 探测不到的项留空并注释说明，不猜。

set -euo pipefail

TARGET="${1:-}"
NAME="${2:-$TARGET}"

[ -n "$TARGET" ] || { echo "用法: $0 <ssh别名或host> [集群短名]" >&2; exit 1; }

r() { ssh -o BatchMode=yes -o ConnectTimeout=15 "$TARGET" "$1" 2>/dev/null || true; }

echo "==> 探测 $TARGET ..." >&2

# 先确认能连上，否则后面全是空值
probe_ok=$(r 'echo yes')
[ "$probe_ok" = "yes" ] || { echo "错误: 无法通过 ssh 连接 $TARGET" >&2; exit 1; }

USER_REMOTE=$(r 'whoami')
LOGIN_HOST=$(r 'hostname')
HOME_REAL=$(r 'echo $HOME')
HOME_BASE_V=$(dirname "$HOME_REAL")

# ---- 调度器 ----
SCHED="unknown"
r 'command -v sbatch'  >/dev/null && [ -n "$(r 'command -v sbatch')" ]  && SCHED="slurm"
[ "$SCHED" = "unknown" ] && [ -n "$(r 'command -v qsub')" ] && SCHED="pbs"

PART=""; DEFMEM=""; MAXWALL=""; MINGRES=""; GRESTYPE=""
NODECNT=""; CPUS_N=""; NODEMEM=""

if [ "$SCHED" = "slurm" ]; then
    # 取第一个 up 状态的分区
    PART=$(r "sinfo -h -o '%P %a' | awk '\$2==\"up\"{print \$1; exit}'" | tr -d '*')

    if [ -n "$PART" ]; then
        SCON=$(r "scontrol show partition $PART")
        DEFMEM=$(printf '%s' "$SCON" | tr ' ' '\n' | sed -n 's/^DefMemPerCPU=//p' | head -1)
        MAXWALL=$(printf '%s' "$SCON" | tr ' ' '\n' | sed -n 's/^MaxTime=//p' | head -1)
        NODECNT=$(printf '%s' "$SCON" | tr ' ' '\n' | sed -n 's/^TotalNodes=//p' | head -1)

        # QOS 的 MinTRES（如 gres/dcu=1）—— 决定是否强制申请加速器
        QOSN=$(printf '%s' "$SCON" | tr ' ' '\n' | sed -n 's/^QoS=//p' | head -1)
        if [ -n "$QOSN" ] && [ "$QOSN" != "N/A" ]; then
            MINTRES=$(r "sacctmgr -nP show qos where name=$QOSN format=MinTRES")
            # gres/dcu=1 -> dcu:1
            MINGRES=$(printf '%s' "$MINTRES" | sed -n 's|.*gres/\([a-z]*\)=\([0-9]*\).*|\1:\2|p')
        fi

        # 节点规格取第一台
        NODEINFO=$(r "sinfo -h -p $PART -o '%c|%m|%G' | head -1")
        CPUS_N=$(printf '%s' "$NODEINFO" | cut -d'|' -f1)
        NODEMEM=$(printf '%s' "$NODEINFO" | cut -d'|' -f2 | awk '{printf "%d", $1/1024}')
        # gres 形如 dcu:Hygon:8(S:0-7) 或 gpu:a100:4
        # 先砍掉括号里的 socket 映射，再取最后一段数字，否则会抓到 "0-7"
        GRESRAW=$(printf '%s' "$NODEINFO" | cut -d'|' -f3)
        GRESBASE=${GRESRAW%%(*}
        GRESTYPE=$(printf '%s' "$GRESBASE" | cut -d: -f1)
        ACCEL_N=$(printf '%s' "$GRESBASE" | awk -F: '{print $NF}' | tr -dc '0-9')
    fi
fi

CPU_MODEL_V=$(r "lscpu | sed -n 's/^Model name:[[:space:]]*//p' | head -1")

# ---- 网络（登录节点）----
# 超时给足 15s 并重试：某些站点首包慢，单次探测会误判成不可达
net_ok=""; net_bad=""
for h in pypi.org pypi.tuna.tsinghua.edu.cn modelscope.cn huggingface.co github.com; do
    reachable="no"
    for _ in 1 2; do
        code=$(r "timeout 15 curl -sI https://$h -o /dev/null -w '%{http_code}'")
        case "$code" in 2*|3*) reachable="yes"; break ;; esac
    done
    if [ "$reachable" = "yes" ]; then
        net_ok="$net_ok $h"
    else
        net_bad="$net_bad $h"
    fi
done

# ---- 登录节点能否 import torch ----
torch_login=$(r 'python3 -c "import torch" 2>&1 | tail -1')
missing_lib=$(printf '%s' "$torch_login" | sed -n 's/^ImportError: \([^:]*\.so[^:]*\).*/\1/p')

QUOTA=$(r "df -BG $HOME_REAL 2>/dev/null | awk 'NR==2{gsub(/[^0-9]/,\"\",\$2); print \$2}'")

echo "==> 完成，输出 profile" >&2

cat <<EOF
# ${NAME} —— 自动探测于 $(date +%Y-%m-%d)
# 探测源: ssh ${TARGET} (登录节点 ${LOGIN_HOST})
# 留空的项表示未能自动探测，请手工确认后填写。

# ---- 连接 ----
CLUSTER_ID="${NAME}"
CLUSTER_DESC=""
SSH_HOST="$(ssh -G "$TARGET" 2>/dev/null | awk '/^hostname /{print $2}')"
SSH_PORT="$(ssh -G "$TARGET" 2>/dev/null | awk '/^port /{print $2}')"
HOME_BASE="${HOME_BASE_V}"

KEY_NAME_MARKER=""
NEEDS_UPDATE_HOSTKEYS_NO="no"

# ---- 调度器 ----
SCHEDULER="${SCHED}"
PARTITION="${PART}"
DEF_MEM_PER_CPU="${DEFMEM}"
MIN_GRES="${MINGRES}"
GRES_TYPE="${GRESTYPE}"
MAX_WALLTIME="${MAXWALL}"

# ---- 硬件 ----
ACCEL_NAME=""
ACCEL_ARCH=""
ACCEL_PER_NODE="${ACCEL_N:-}"
ACCEL_MEM_GB=""
CPUS_PER_NODE="${CPUS_N}"
CPU_MODEL="${CPU_MODEL_V}"
NODE_MEM_GB="${NODEMEM}"
NODE_COUNT="${NODECNT}"
LOGIN_NODES="${LOGIN_HOST}"
HOME_QUOTA_GB="${QUOTA}"

# ---- 软件栈 ----
TOOLCHAIN=""
TOOLCHAIN_VERSION=""
TOOLCHAIN_PATH=""
MODULE_LOADS=""
DEFAULT_VENV=""

# ---- 网络 ----
NET_OK="$(echo "$net_ok" | sed 's/^ //')"
NET_BLOCKED="$(echo "$net_bad" | sed 's/^ //')"
PIP_INDEX="https://pypi.tuna.tsinghua.edu.cn/simple"
COMPUTE_NODE_OFFLINE="yes"
TMP_SHARED="no"

# ---- 已知问题 ----
LOGIN_NODE_MISSING_LIBS="${missing_lib}"
KNOWN_LIMITATIONS=""

# 探测时登录节点 import torch 的结果（供参考）：
#   ${torch_login:-（无输出，可能已可用）}
#
# 还需手工确认的：
#   - ACCEL_NAME / ACCEL_ARCH：在计算节点跑
#       srun -p ${PART} ${MINGRES:+--gres=$MINGRES} --time=00:05:00 rocminfo | grep gfx
#     或 nvidia-smi --query-gpu=name --format=csv
#   - MODULE_LOADS：module avail 里挑编译器和加速器 SDK
#   - KNOWN_LIMITATIONS：跑一次能力探针（见 references/troubleshooting.md）
EOF
