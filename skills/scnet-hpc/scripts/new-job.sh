#!/usr/bin/env bash
# 生成一个符合目标集群所有约束的作业脚本骨架。
#
#   ./new-job.sh [--cluster <集群短名>] [--cpu-only] [--partition <分区>] \
#     <作业名> [加速器数] [cpu数] [时长]
#
# 内存按 cpus × DEF_MEM_PER_CPU 自动取安全值，避免手算出错。

set -euo pipefail

. "$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)/_common.sh"

parse_cluster_arg "$@"
set -- "${REST[@]+${REST[@]}}"

# --user <名>：远端用户名与本地不同时指定（日志路径需要真实用户名）
REMOTE_USER=""
REFRESH=no
USE_AUTO=yes
CPU_ONLY=no
PARTITION_OVERRIDE=""
ARGS=()
while [ $# -gt 0 ]; do
    case "$1" in
        --user) [ $# -ge 2 ] || die "--user 缺少参数"; REMOTE_USER="$2"; shift 2 ;;
        --user=*) REMOTE_USER="${1#*=}"; shift ;;
        --partition) [ $# -ge 2 ] || die "--partition 缺少参数"; PARTITION_OVERRIDE="$2"; shift 2 ;;
        --partition=*) PARTITION_OVERRIDE="${1#*=}"; shift ;;
        --cpu-only) CPU_ONLY=yes; shift ;;
        --refresh) REFRESH=yes; shift ;;
        --no-auto) USE_AUTO=no; shift ;;
        *) ARGS+=("$1"); shift ;;
    esac
done
set -- "${ARGS[@]+${ARGS[@]}}"

NAME="${1:-}"
ACCEL="${2:-1}"
CPUS="${3:-8}"
TIME="${4:-00:20:00}"

if [ -z "$NAME" ]; then
    cat >&2 <<EOF
用法: $0 [--cluster <集群短名>] [--user <远端用户名>] [--cpu-only]
       [--partition <分区>] [--refresh|--no-auto] <作业名> [加速器数] [cpu数] [时长]

例子:
  $0 probe                    # 1 卡, 8 核, 20 分钟（探针）
  $0 infer 8 32 01:30:00      # 8 卡, 32 核, 1.5 小时（大模型）
  $0 --cpu-only build 0 32 01:00:00  # 使用 profile 的 CPU 分区，不申请加速器

可用集群: $(list_clusters | tr '\n' ' ')
EOF
    exit 1
fi

[[ "$NAME" =~ ^[A-Za-z0-9][A-Za-z0-9._-]{0,63}$ ]] \
    || die "作业名只允许 1-64 个字母、数字、点、下划线或连字符，且必须以字母或数字开头"
[[ "$ACCEL" =~ ^[0-9]+$ ]] || die "加速器数必须是非负整数"
[[ "$CPUS" =~ ^[1-9][0-9]*$ ]] || die "CPU 数必须是正整数"
[[ "$TIME" =~ ^([0-9]+-)?[0-9]{1,2}:[0-9]{2}:[0-9]{2}$ ]] \
    || die "时长格式应为 HH:MM:SS 或 D-HH:MM:SS"
if [ -n "$REMOTE_USER" ]; then
    [[ "$REMOTE_USER" =~ ^[A-Za-z0-9._-]+$ ]] || die "远端用户名包含不安全字符"
fi
if [ -n "$PARTITION_OVERRIDE" ]; then
    [[ "$PARTITION_OVERRIDE" =~ ^[A-Za-z0-9._-]+$ ]] || die "分区名包含不安全字符"
fi

if [ "$REFRESH" = yes ]; then
    "$REPO_ROOT/scripts/refresh-cluster.sh" --cluster "${CLUSTER:-}"
fi

export SCNET_HPC_USE_AUTO="$USE_AUTO"
load_cluster "$CLUSTER"

[ "${SCHEDULER:-slurm}" = "slurm" ] \
    || die "暂只支持 slurm，${CLUSTER_ID} 用的是 ${SCHEDULER}"

if [ "$CPU_ONLY" = yes ]; then
    [ -n "${PARTITION_CPU:-}" ] \
        || die "${CLUSTER_ID} profile 未定义 PARTITION_CPU，不能使用 --cpu-only"
    EFFECTIVE_PARTITION="${PARTITION_OVERRIDE:-$PARTITION_CPU}"
    ACCEL=0
    [ -n "${DEF_MEM_PER_CPU_CPU:-}" ] && DEF_MEM_PER_CPU="$DEF_MEM_PER_CPU_CPU"
else
    EFFECTIVE_PARTITION="${PARTITION_OVERRIDE:-${PARTITION:-}}"
fi
[ -n "$EFFECTIVE_PARTITION" ] || die "目标分区为空，请补 profile 或使用 --partition"

# 内存上限 = cpus × DEF_MEM_PER_CPU，留 1GB 余量避免边界抖动
if [ -n "${DEF_MEM_PER_CPU:-}" ]; then
    MEM_MB=$(( CPUS * DEF_MEM_PER_CPU ))
    MEM_GB=$(( MEM_MB / 1024 ))
    [ "$MEM_GB" -gt 1 ] && MEM_GB=$(( MEM_GB - 1 ))
    MEM_LINE="#SBATCH --mem=${MEM_GB}gb"
    MEM_NOTE="${MEM_GB}gb（上限 $(( MEM_MB / 1024 )).$(( MEM_MB % 1024 * 100 / 1024 ))gb）"
else
    MEM_LINE="# DEF_MEM_PER_CPU 未在 profile 中设置，未生成 --mem"
    MEM_NOTE="未设置"
fi

# QOS 强制申请加速器时必须写 --gres
GRES_LINE=""
if [ "$CPU_ONLY" != yes ] && [ -n "${GRES_TYPE:-}" ] && [ "$ACCEL" -gt 0 ]; then
    GRES_LINE="#SBATCH --gres=${GRES_TYPE}:${ACCEL}"
    [ -n "${MIN_GRES:-}" ] && GRES_LINE="$GRES_LINE          # 必须：QOS 要求最少 ${MIN_GRES}"
fi
if [ "$CPU_ONLY" != yes ] && [ -n "${MIN_GRES:-}" ] && [ "$ACCEL" -eq 0 ]; then
    die "默认/指定分区要求至少 ${MIN_GRES}；请申请加速器或使用 --cpu-only"
fi

# 远端用户名。#SBATCH 是注释行，Slurm 不做变量展开 —— 日志路径里写 $USER
# 会被当成字面量目录名，作业以 exit 53 失败且不产生日志。所以这里必须展开成
# 真实用户名。默认取本地用户名，不同时用 --user 覆盖。
REMOTE_USER="${REMOTE_USER:-${REMOTE_USER_DETECTED:-$(whoami)}}"
[[ "$REMOTE_USER" =~ ^[A-Za-z0-9._-]+$ ]] || die "探测到的远端用户名包含不安全字符，请用 --user 显式指定"
HOME_DIR="${HOME_BASE}/${REMOTE_USER}"

# 脚本体（非 #SBATCH 行）里可以正常用 $USER
MODULES=""
[ -n "${MODULE_LOADS:-}" ] && MODULES="module load ${MODULE_LOADS}"
VENV_LINE=""
[ -n "${DEFAULT_VENV:-}" ] && VENV_LINE="source ${HOME_DIR}/${DEFAULT_VENV}/bin/activate"

OFFLINE_LINES=""
if [ "${COMPUTE_NODE_OFFLINE:-yes}" = "yes" ]; then
    OFFLINE_LINES="# 计算节点无外网：让 Hub 请求立刻失败，而不是等 httpx 超时
export HF_HUB_OFFLINE=1
export TRANSFORMERS_OFFLINE=1"
fi

OUT="${NAME}.slurm"
[ -e "$OUT" ] && die "$OUT 已存在"

cat > "$OUT" <<EOF
#!/bin/bash -l
# 目标集群: ${CLUSTER_ID} (${CLUSTER_DESC:-$SSH_HOST})
#
# 使用 "bash -l"，因为部分集群仅在 login
# shell 中定义 module 函数。普通 "#!/bin/bash" 可能使 module load 静默失败，作业仍
# 返回 0，但 ROCM_PATH 未设置且能力工具无输出。该行为已在昆山集群观测。
#SBATCH --job-name=${NAME}
#SBATCH --partition=${EFFECTIVE_PARTITION}
${GRES_LINE}
#SBATCH --nodes=1
#SBATCH --ntasks-per-node=1
#SBATCH --cpus-per-task=${CPUS}
${MEM_LINE}
#SBATCH --time=${TIME}
#SBATCH --output=${HOME_DIR}/scripts/logs/${NAME}_%j.log
#SBATCH --error=${HOME_DIR}/scripts/logs/${NAME}_%j.err

module purge
${MODULES}
${VENV_LINE}

# 集群测试/作业的临时文件统一放共享家目录，不使用节点本地 /tmp。
JOB_TMPDIR="${HOME_DIR}/.scnet-hpc/tmp/\${SLURM_JOB_ID:-manual-\$\$}"
mkdir -p "\$JOB_TMPDIR"
export TMPDIR="\$JOB_TMPDIR"
export TMP="\$JOB_TMPDIR"
export TEMP="\$JOB_TMPDIR"

${OFFLINE_LINES}

echo "### node=\$(hostname) jobid=\$SLURM_JOB_ID"
date +"%Y-%m-%d %H:%M:%S"

python3 - <<'PYEOF'
import torch
print("torch", torch.__version__, "|", torch.cuda.get_device_name(0),
      "| devices", torch.cuda.device_count())

# TODO: 在这里写你的代码
PYEOF

rc=\$?
echo "### python exit=\$rc"
date +"%Y-%m-%d %H:%M:%S"
# 传播工作负载退出码，避免调度器状态掩盖 Python 失败
exit \$rc
EOF

chmod +x "$OUT"

# 清掉 profile 缺项造成的空行
sed -i.bak '/^$/N;/^\n$/D' "$OUT" 2>/dev/null && rm -f "$OUT.bak"

echo "已生成 $OUT"
echo "  集群=${CLUSTER_ID}  ${GRES_TYPE:-加速器}=${ACCEL}  CPU=${CPUS}  内存=${MEM_NOTE}  时长=${TIME}"
echo "  分区=${EFFECTIVE_PARTITION}  模式=$([ "$CPU_ONLY" = yes ] && echo CPU || echo accelerator)  节点数=${NODE_COUNT:-未探测}（来源：${NODE_COUNT_SOURCE:-profile/cache}）"
echo "  日志目录=${HOME_DIR}/scripts/logs（用户名 ${REMOTE_USER}，不对请加 --user）"
echo
echo "上传并提交："
echo "  scp $OUT ${CLUSTER_ID}:${HOME_DIR}/scripts/"
echo "  ssh ${CLUSTER_ID} 'mkdir -p ${HOME_DIR}/scripts/logs && sbatch --test-only ${HOME_DIR}/scripts/$OUT'"
echo
echo "要求：logs 目录必须先存在；否则作业会以 exit 53 失败且不产生日志。"
