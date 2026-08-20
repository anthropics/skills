# SCNet HPC English Quick Start

This guide covers the common workflow for SCNet clusters. Current repository profiles focus
mainly on Hygon DCU/DTK systems. Always read the target profile before using a partition,
memory value, accelerator type, module, or home-directory path.

The repository scripts support Linux and macOS natively. On Windows, use WSL2; native Windows
execution and Git Bash are not fully validated. This is separate from the official SCNet desktop
client, which supports Windows 10+ and macOS 12 Monterey+.

## 1. Inspect the available profiles

```bash
ls clusters/*.conf
sed -n '1,220p' clusters/<cluster>.conf
```

Check at least `PARTITION`, `PARTITION_CPU`, `GRES_TYPE`, `MIN_GRES`,
`DEF_MEM_PER_CPU`, `MODULE_LOADS`, `COMPUTE_NODE_OFFLINE`, and
`KNOWN_LIMITATIONS`.

## 2. Install the skill

```bash
git clone https://github.com/lql341/scnet-hpc.git
cd scnet-hpc
./scripts/install.sh
```

The repository is designed to be shared by Codex, Claude Code, and OpenCode. Installation
paths depend on the local agent layout; `install.sh --link` is useful when developing the
skill from a shared source directory.

## 3. Configure SSH

Download the private key from the SCNet console, then run:

```bash
./scripts/setup-ssh.sh --cluster <cluster> <private-key-file> <username>
ssh <cluster>
```

The script installs the key under `~/.ssh`, adds an SSH config entry, and tests the
connection. Do not commit private keys, usernames, internal node names, or personal paths.

## 4. Generate a Slurm job

Accelerator job:

```bash
./scripts/new-job.sh --cluster <cluster> myjob 1 8 00:20:00
```

CPU-only job, when the profile defines `PARTITION_CPU`:

```bash
./scripts/new-job.sh --cluster <cluster> --cpu-only build 0 32 01:00:00
```

Explicit partition override:

```bash
./scripts/new-job.sh --cluster <cluster> --partition <partition> probe 1 8 00:10:00
```

The generator calculates a safe memory request from the profile, adds GRES only when
needed, configures a shared temporary directory, enables offline mode when appropriate,
and propagates the program exit code.

Create the remote log directory before submission:

```bash
ssh <cluster> 'mkdir -p ~/scripts/logs'
```

Upload the generated script and validate the request before queueing it:

```bash
scp myjob.slurm <cluster>:~/scripts/
ssh <cluster> 'sbatch --test-only ~/scripts/myjob.slurm'
ssh <cluster> 'sbatch ~/scripts/myjob.slurm'
```

## 5. Monitor and debug

```bash
squeue -u "$USER"
squeue -j <job-id> --start
sacct -j <job-id> --format=JobID,State%14,ExitCode,Elapsed,MaxRSS -P
scancel <job-id>
```

Do not trust `COMPLETED` alone. Read both stdout and stderr, and make sure the job script
ends with the real program exit code.

For short experiments, request an interactive allocation with `srun`. Use the partition,
GRES type, CPU count, and memory limit from the target profile.

## 6. SCNet environment rules

- Login nodes are for source management, dependency preparation, file operations, and
  scheduler commands. Whether package indexes and model sites are reachable is cluster-specific.
- Compute nodes are often offline. Download dependencies, models, and kernels before the job.
- A DCU partition may require at least one accelerator even for a CPU-oriented command.
- Memory limits may be tied to `cpus-per-task × DefMemPerCPU`.
- Do not use system `/tmp` for files that must be shared across login and compute nodes.
- Loading a module on a login node does not prove that the runtime works on a compute node.
- Hygon DCU software capabilities depend on the exact DTK, driver, framework, and `gfx` target.

## 7. Refresh and probe a cluster

```bash
./scripts/refresh-cluster.sh --cluster <cluster> --dry-run
./scripts/refresh-cluster.sh --cluster <cluster>
./scripts/refresh-cluster.sh --cluster <cluster> --compute
```

The default refresh performs read-only login-node checks. `--compute` submits a small Slurm
job to test the accelerator runtime and therefore consumes cluster resources.

For detailed diagnostics, see the Chinese references:

- `references/setup.md`
- `references/environment.md`
- `references/troubleshooting.md`
- `references/software-compatibility.md`
- `references/hygon-dcu-development.md`
