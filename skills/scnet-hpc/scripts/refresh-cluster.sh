#!/usr/bin/env bash
# 动态刷新 clusters/.cache/<集群>.auto.conf。
#
# 用法：
#   ./refresh-cluster.sh [--cluster <集群短名>] [--compute] [--dry-run]
#
# 默认只做登录节点上的只读探测；--compute 会提交一个 1 卡、4 核、10 分钟的小作业，
# 到计算节点实测加速器、Triton、FP8、外网等能力。生成的缓存会覆盖 profile 的同名字段。

set -euo pipefail

. "$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)/_common.sh"

parse_cluster_arg "$@"
set -- "${REST[@]+${REST[@]}}"

COMPUTE=no
DRY_RUN=no

while [ $# -gt 0 ]; do
    case "$1" in
        --compute|-c) COMPUTE=yes; shift ;;
        --dry-run|-n) DRY_RUN=yes; shift ;;
        -h|--help) sed -n '2,14p' "$0" | sed 's/^# \?//'; exit 0 ;;
        *) die "未知参数: $1" ;;
    esac
done

load_cluster "$CLUSTER"

r() {
    ssh -o BatchMode=yes -o ConnectTimeout=15 -o ServerAliveInterval=15 -o ServerAliveCountMax=3 \
        "$CLUSTER_ID" "$1" 2>/dev/null || true
}

probe_value() {
    local key="$1"
    printf '%s\n' "${COMPUTE_OUT:-}" | awk -F= -v k="$key" '$1 == k { sub(/^[^=]+=/,""); print; exit }'
}

add_known_limit() {
    local item="$1"
    [ -n "$item" ] || return 0
    case "$item" in
        *Triton*)
            if printf '%s' "$KNOWN_LIMITS_NEW" | grep -q 'Triton'; then return 0; fi
            ;;
        *FP8*)
            if printf '%s' "$KNOWN_LIMITS_NEW" | grep -q 'FP8'; then return 0; fi
            ;;
        *BF16*)
            if printf '%s' "$KNOWN_LIMITS_NEW" | grep -q 'BF16'; then return 0; fi
            ;;
        *bitsandbytes*)
            if printf '%s' "$KNOWN_LIMITS_NEW" | grep -q 'bitsandbytes'; then return 0; fi
            ;;
    esac
    KNOWN_LIMITS_NEW="${KNOWN_LIMITS_NEW:+${KNOWN_LIMITS_NEW}；}${item}"
}

info "==> 动态探测 ${CLUSTER_ID} (${CLUSTER_DESC:-$SSH_HOST})"
probe_ok=$(r 'echo yes')
[ "$probe_ok" = "yes" ] || die "无法通过 ssh 连接 ${CLUSTER_ID}"

# ---- 连接和登录节点基础信息 ----
DETECTED_HOST="$(ssh -G "$CLUSTER_ID" 2>/dev/null | awk '/^hostname /{print $2; exit}')"
DETECTED_PORT="$(ssh -G "$CLUSTER_ID" 2>/dev/null | awk '/^port /{print $2; exit}')"
DETECTED_USER="$(ssh -G "$CLUSTER_ID" 2>/dev/null | awk '/^user /{print $2; exit}')"
LOGIN_HOST=$(r 'hostname')
REMOTE_HOME=$(r 'echo $HOME')
HOME_BASE_NEW=$(dirname "$REMOTE_HOME")
CPU_MODEL_NEW=$(r "lscpu | sed -n 's/^Model name:[[:space:]]*//p' | head -1")
QUOTA_NEW=$(r "df -BG $REMOTE_HOME 2>/dev/null | awk 'NR==2{gsub(/[^0-9]/,\"\",\$2); print \$2}'")

# ---- 调度器 ----
SCHED_NEW="unknown"
if [ -n "$(r 'command -v sbatch')" ]; then
    SCHED_NEW="slurm"
elif [ -n "$(r 'command -v qsub')" ]; then
    SCHED_NEW="pbs"
fi

PART_NEW=""
DEFMEM_NEW=""
MAXWALL_NEW=""
MINGRES_NEW=""
GRESTYPE_NEW=""
NODECNT_NEW=""
CPUS_NEW=""
NODEMEM_NEW=""
ACCEL_NEW=""

if [ "$SCHED_NEW" = "slurm" ]; then
    # 优先沿用 profile 现有分区，只在它已经不再 up 时才改选第一个 up 分区。
    if [ -n "${PARTITION:-}" ]; then
        PART_STATE=$(r "sinfo -h -p ${PARTITION} -o '%a' | head -1")
        [ "$PART_STATE" = "up" ] && PART_NEW="$PARTITION"
    fi
    if [ -z "$PART_NEW" ]; then
        PART_NEW=$(r "sinfo -h -o '%P %a' | awk '\$2==\"up\"{print \$1; exit}'" | tr -d '*')
    fi

    if [ -n "$PART_NEW" ]; then
        SCON=$(r "scontrol show partition $PART_NEW")
        DEFMEM_NEW=$(printf '%s' "$SCON" | tr ' ' '\n' | sed -n 's/^DefMemPerCPU=//p' | head -1)
        MAXWALL_NEW=$(printf '%s' "$SCON" | tr ' ' '\n' | sed -n 's/^MaxTime=//p' | head -1)
        NODECNT_NEW=$(printf '%s' "$SCON" | tr ' ' '\n' | sed -n 's/^TotalNodes=//p' | head -1)

        QOS_NEW=$(printf '%s' "$SCON" | tr ' ' '\n' | sed -n 's/^QoS=//p' | head -1)
        if [ -n "$QOS_NEW" ] && [ "$QOS_NEW" != "N/A" ]; then
            MINTRES=$(r "sacctmgr -nP show qos where name=$QOS_NEW format=MinTRES")
            MINGRES_NEW=$(printf '%s' "$MINTRES" | sed -n 's|.*gres/\([a-z]*\)=\([0-9]*\).*|\1:\2|p')
        fi

        NODEINFO=$(r "sinfo -h -p $PART_NEW -o '%c|%m|%G' | head -1")
        CPUS_NEW=$(printf '%s' "$NODEINFO" | cut -d'|' -f1)
        NODEMEM_NEW=$(printf '%s' "$NODEINFO" | cut -d'|' -f2 | awk '{printf "%d", $1/1024}')
        GRESRAW=$(printf '%s' "$NODEINFO" | cut -d'|' -f3)
        GRESBASE=${GRESRAW%%(*}
        GRESTYPE_NEW=$(printf '%s' "$GRESBASE" | cut -d: -f1)
        ACCEL_NEW=$(printf '%s' "$GRESBASE" | awk -F: '{print $NF}' | tr -dc '0-9')
    fi
fi

# ---- 登录节点网络 ----
NET_OK_NEW=""
NET_BLOCKED_NEW=""
for h in pypi.org pypi.tuna.tsinghua.edu.cn modelscope.cn huggingface.co github.com; do
    reachable=no
    for _ in 1 2; do
        code=$(r "timeout 15 curl -sI https://$h -o /dev/null -w '%{http_code}'")
        case "$code" in
            2*|3*) reachable=yes; break ;;
        esac
    done
    if [ "$reachable" = yes ]; then
        NET_OK_NEW="${NET_OK_NEW:+$NET_OK_NEW }$h"
    else
        NET_BLOCKED_NEW="${NET_BLOCKED_NEW:+$NET_BLOCKED_NEW }$h"
    fi
done

# ---- 登录节点 torch 缺库 ----
torch_login=$(r 'python3 -c "import torch" 2>&1 | tail -1')
MISSING_LIB_NEW=$(printf '%s' "$torch_login" | sed -n 's/^ImportError: \([^:]*\.so[^:]*\).*/\1/p')

# ---- module 候选（只记录，不自动覆盖 MODULE_LOADS）----
MODULE_CANDIDATES_NEW=$(r "bash -lc 'module avail 2>&1' | awk '/compiler\\/(dtk|rocm)/{print}' | sort -u | head -30")

# ---- 计算节点能力（可选）----
COMPUTE_OUT=""
ACCEL_NAME_NEW=""
ACCEL_ARCH_NEW=""
ACCEL_MEM_NEW=""
COMPUTE_OFFLINE_NEW=""
KNOWN_LIMITS_NEW=""

if [ "$COMPUTE" = yes ] && [ "$DRY_RUN" = no ]; then
    info "==> 提交计算节点小探针（约 1 卡、4 核、10 分钟）"
    COMPUTE_OUT="$( { "$REPO_ROOT/scripts/run-compute-probe.sh" --cluster "$CLUSTER_ID"; } 2>&1 )" || true
    if ! printf '%s\n' "$COMPUTE_OUT" | grep -q '^PROBE_'; then
        info "计算节点探针未产生有效 PROBE 输出："
        printf '%s\n' "$COMPUTE_OUT" | sed 's/^/    /' >&2
        COMPUTE_OUT=""
    fi
fi

if [ "$COMPUTE" = yes ] && [ -n "$COMPUTE_OUT" ]; then
    CUDA_AVAILABLE=$(probe_value PROBE_CUDA_AVAILABLE)
    ACCEL_NAME_NEW=$(probe_value PROBE_DEVICE_NAME)
    case "$ACCEL_NAME_NEW" in
        BW|BW1000) ACCEL_NAME_NEW="海光 BW1000 DCU" ;;
    esac
    ACCEL_ARCH_NEW=$(probe_value PROBE_ARCH)

    MEM_MIB=$(probe_value PROBE_MEM_MIB)
    if [[ "$MEM_MIB" =~ ^[0-9]+$ ]]; then
        ACCEL_MEM_NEW=$(( (MEM_MIB + 1023) / 1024 ))
    fi

    case "$(probe_value PROBE_NET_PYPI)" in
        OFFLINE) COMPUTE_OFFLINE_NEW=yes ;;
        ONLINE) COMPUTE_OFFLINE_NEW=no ;;
    esac

    if [ "$CUDA_AVAILABLE" = "0" ]; then
        KNOWN_LIMITS_NEW="torch.cuda 不可用"
    fi

    DTYPES=$(probe_value PROBE_DTYPES)
    case ",$DTYPES," in
        *,bfloat16,*) ;;
        *) KNOWN_LIMITS_NEW="${KNOWN_LIMITS_NEW:+${KNOWN_LIMITS_NEW}；}无 BF16 数据类型支持" ;;
    esac

    SCALED=$(probe_value PROBE_SCALED_MM)
    case "$SCALED" in
        ERR:*) KNOWN_LIMITS_NEW="${KNOWN_LIMITS_NEW:+${KNOWN_LIMITS_NEW}；}硬件 FP8 torch._scaled_mm 不可用（${SCALED}）" ;;
    esac

    TRITON=$(probe_value PROBE_TRITON)
    case "$TRITON" in
        ERR:*) KNOWN_LIMITS_NEW="${KNOWN_LIMITS_NEW:+${KNOWN_LIMITS_NEW}；}Triton 不可用（${TRITON}）" ;;
    esac

    BNB=$(probe_value PROBE_BITSANDBYTES)
    case "$BNB" in
        IMPORT_ERR:*) KNOWN_LIMITS_NEW="${KNOWN_LIMITS_NEW:+${KNOWN_LIMITS_NEW}；}bitsandbytes 导入失败（${BNB}）" ;;
    esac

    # 保留 profile 中已有的人工验证结论，并将动态结果置于前面。
    if [ -n "${KNOWN_LIMITATIONS:-}" ]; then
        OLD_IFS="$IFS"
        IFS='；'
        for item in $KNOWN_LIMITATIONS; do
            add_known_limit "$item"
        done
        IFS="$OLD_IFS"
    fi
elif [ "$COMPUTE" = yes ]; then
    info "计算节点探针没有返回结果，保留 profile 中的加速器和限制信息。"
fi

build_cache() {
    echo "# 由 scripts/refresh-cluster.sh 自动生成于 $(date '+%Y-%m-%d %H:%M:%S')"
    echo "# 登录节点: ${LOGIN_HOST:-未探测}"
    echo "# 这是动态探测缓存，会覆盖 profile 中的同名字段；删除本文件即可回退到纯 profile。"
    printf 'SSH_HOST=%q\n' "${DETECTED_HOST:-$SSH_HOST}"
    printf 'SSH_PORT=%q\n' "${DETECTED_PORT:-$SSH_PORT}"
    printf 'REMOTE_USER_DETECTED=%q\n' "${DETECTED_USER:-${REMOTE_USER_DETECTED:-}}"
    printf 'HOME_BASE=%q\n' "${HOME_BASE_NEW:-$HOME_BASE}"
    printf 'SCHEDULER=%q\n' "${SCHED_NEW:-${SCHEDULER:-}}"
    printf 'PARTITION=%q\n' "${PART_NEW:-${PARTITION:-}}"
    printf 'DEF_MEM_PER_CPU=%q\n' "${DEFMEM_NEW:-${DEF_MEM_PER_CPU:-}}"
    printf 'MIN_GRES=%q\n' "${MINGRES_NEW:-${MIN_GRES:-}}"
    printf 'GRES_TYPE=%q\n' "${GRESTYPE_NEW:-${GRES_TYPE:-}}"
    printf 'MAX_WALLTIME=%q\n' "${MAXWALL_NEW:-${MAX_WALLTIME:-}}"
    printf 'CPUS_PER_NODE=%q\n' "${CPUS_NEW:-${CPUS_PER_NODE:-}}"
    printf 'NODE_MEM_GB=%q\n' "${NODEMEM_NEW:-${NODE_MEM_GB:-}}"
    printf 'NODE_COUNT=%q\n' "${NODECNT_NEW:-${NODE_COUNT:-}}"
    printf 'ACCEL_PER_NODE=%q\n' "${ACCEL_NEW:-${ACCEL_PER_NODE:-}}"
    printf 'CPU_MODEL=%q\n' "${CPU_MODEL_NEW:-${CPU_MODEL:-}}"
    printf 'LOGIN_NODES=%q\n' "${LOGIN_HOST:-${LOGIN_NODES:-}}"
    printf 'HOME_QUOTA_GB=%q\n' "${QUOTA_NEW:-${HOME_QUOTA_GB:-}}"
    printf 'NET_OK=%q\n' "${NET_OK_NEW:-${NET_OK:-}}"
    printf 'NET_BLOCKED=%q\n' "${NET_BLOCKED_NEW:-${NET_BLOCKED:-}}"
    printf 'LOGIN_NODE_MISSING_LIBS=%q\n' "${MISSING_LIB_NEW:-${LOGIN_NODE_MISSING_LIBS:-}}"
    printf 'MODULE_CANDIDATES=%q\n' "${MODULE_CANDIDATES_NEW:-}"

    if [ "$COMPUTE" = yes ]; then
        printf 'ACCEL_NAME=%q\n' "${ACCEL_NAME_NEW:-${ACCEL_NAME:-}}"
        printf 'ACCEL_ARCH=%q\n' "${ACCEL_ARCH_NEW:-${ACCEL_ARCH:-}}"
        printf 'ACCEL_MEM_GB=%q\n' "${ACCEL_MEM_NEW:-${ACCEL_MEM_GB:-}}"
        printf 'COMPUTE_NODE_OFFLINE=%q\n' "${COMPUTE_OFFLINE_NEW:-${COMPUTE_NODE_OFFLINE:-}}"
        printf 'KNOWN_LIMITATIONS=%q\n' "${KNOWN_LIMITS_NEW:-${KNOWN_LIMITATIONS:-}}"
    else
        printf 'COMPUTE_NODE_OFFLINE=%q\n' "${COMPUTE_NODE_OFFLINE:-}"
        printf 'KNOWN_LIMITATIONS=%q\n' "${KNOWN_LIMITATIONS:-}"
    fi
}

mkdir -p "$CLUSTER_DIR/.cache"
if [ "$DRY_RUN" = yes ]; then
    info "==> dry-run，不写缓存"
    build_cache
else
    AUTO_TMP="$CLUSTER_AUTO_CONF.tmp.$$"
    build_cache > "$AUTO_TMP"
    mv "$AUTO_TMP" "$CLUSTER_AUTO_CONF"
    info "==> 已写入 $CLUSTER_AUTO_CONF"

    if [ "$COMPUTE" = yes ] && [ -n "$COMPUTE_OUT" ]; then
        PROBE_LOG="$CLUSTER_DIR/.cache/${CLUSTER_ID}.probe.log"
        printf '%s\n' "$COMPUTE_OUT" > "$PROBE_LOG"
        info "==> 原始探针输出已保存 $PROBE_LOG"
    fi
fi
