---
name: scnet-hpc
description: Configure and operate SCNet HPC clusters through SSH and Slurm, including profile-based resource requests, job submission and diagnosis, environment preparation, and accelerator compatibility checks. Use for SCNet access, Slurm CPU/DCU jobs, Hygon DCU/DTK, offline compute nodes, or adding and verifying cluster profiles. Treat other accelerator platforms as unverified until tested on their target compute nodes.
---

# SCNet HPC

Operate SCNet clusters from repository profiles and target-cluster evidence. The included
accelerator guidance is validated primarily for Hygon DCU/DTK and `gfx9xx`; do not transfer
those capability conclusions to other accelerator stacks. The repository scripts support Linux
and macOS natively. On Windows, use WSL2; native Windows execution is not supported.

## 中文说明

本技能用于通过 SSH 和 Slurm 操作 SCNet 超算集群，覆盖基于 profile 的资源申请、作业生成与诊断、环境准备，以及加速器兼容性验证。Linux 和 macOS 可直接运行仓库脚本；Windows 不提供原生脚本入口，建议使用 WSL2。官方 SCNet 客户端支持 Windows 10 及以上、macOS 12 Monterey 及以上（ARM/x86），下载地址见 [SCNet 客户端下载页](https://www.scnet.cn/ui/mall/client/download)。

## Source of truth

- Read `clusters/<cluster>.conf` before reporting connection, partition, memory, hardware,
  module, network, or known-limit information.
- Treat `clusters/.cache/<cluster>.auto.conf` as optional, time-sensitive probe data that
  overrides matching profile fields.
- Verify dynamic scheduler state on the target cluster when the task depends on current
  availability, limits, or node count.
- Do not infer one cluster's parameters from another cluster.

List available profiles with:

```bash
ls clusters/*.conf
```

If more than one profile exists, require an explicit cluster selection before generating a
job, changing SSH configuration, submitting work, or installing software.

## Route the task

Read only the references required for the current operation:

| Operation | Reference |
|---|---|
| Configure or repair SSH access | `references/setup.md` |
| Prepare Python, modules, virtual environments, or offline dependencies | `references/environment.md` |
| Diagnose Slurm, runtime, library, network, or accelerator failures | `references/troubleshooting.md` |
| Add or refresh a cluster profile | `references/adding-cluster.md` |
| Work with Hygon DCU, DTK, HIP libraries, profiling, migration, or containers | `references/hygon-dcu-development.md` |
| Evaluate software compatibility or prepare a public compatibility report | `references/software-compatibility.md` |
| Provide English operating instructions | `references/quickstart-en.md` |

Cluster parameters always come from the selected profile, including when an example in a
reference uses different values.

## Execution boundaries

- Read-only inspection and local script generation do not authorize SSH configuration changes,
  dependency installation, job submission, job cancellation, or remote file deletion.
- Before a remote mutation, resolve the target cluster, command, paths, and expected effect.
- A compute-node probe consumes scheduler resources. Run it only when the user requests
  submission or verification that requires compute-node evidence.
- Preserve existing SSH configuration. `scripts/setup-ssh.sh` adds a missing host entry and
  backs up a conflicting destination key; it does not rewrite an existing host block.
- Do not place credentials, usernames, internal hosts, node names, job IDs, private mirrors, or
  absolute home paths in committed profiles or public reports.

## Operational invariants

1. **Scheduler constraints are profile-specific.** If `MIN_GRES` is non-empty, request at least
   that accelerator resource unless an independent CPU partition is selected.
2. **Memory requests follow the partition limit.** When `DEF_MEM_PER_CPU` is defined, keep
   requested memory within `cpus-per-task × DEF_MEM_PER_CPU`. Use `scripts/new-job.sh` to
   calculate a conservative value.
3. **Framework validation belongs on compute nodes.** A login node may lack accelerator
   libraries even after modules are loaded. Use `srun`, `sbatch`, or the compute probe for
   imports, kernels, collectives, and accelerator capabilities.
4. **Offline nodes require staged dependencies.** When `COMPUTE_NODE_OFFLINE=yes`, download or
   build dependencies on a networked node and disable runtime downloads in the job.
5. **Test files use shared storage.** Create per-job temporary directories under
   `$HOME/.scnet-hpc/tmp/$SLURM_JOB_ID`; do not depend on `/tmp` being shared across nodes.
6. **Job exit status must propagate.** Capture the workload return code and terminate the batch
   script with `exit "$rc"`. Evaluate both accounting state and job logs.
7. **Compatibility claims require target-node evidence.** Package resolution or import success
   alone is insufficient for native extensions and accelerator software. Validate the relevant
   ABI, import, kernel, functional, and end-to-end layers.

## Repository tools

| Tool | Purpose |
|---|---|
| `scripts/setup-ssh.sh` | Install a supplied key and add an SSH host entry |
| `scripts/new-job.sh` | Generate a profile-aware Slurm script |
| `scripts/probe-cluster.sh` | Produce an initial profile from read-only login-node probes |
| `scripts/refresh-cluster.sh` | Refresh dynamic profile fields; compute probing is opt-in |
| `scripts/run-compute-probe.sh` | Submit a minimal accelerator capability probe |

Use `scripts/new-job.sh --cluster <name> ...` for routine job generation. Validate the generated
script with `sbatch --test-only` before submission when the target cluster supports it.

## Evidence and reporting

Distinguish:

- profile values;
- live scheduler observations;
- login-node observations;
- compute-node observations;
- conclusions inferred from those observations.

For failures, report the failing command, relevant log excerpt, scheduler state and exit code,
target profile, and the next bounded diagnostic action. For compatibility results, state the
software and toolchain versions, accelerator architecture, validation layer reached, and
untested boundaries.
