# 连接配置详解

集群的主机名、端口等参数来自 `clusters/<集群短名>.conf`。
本文用 `<集群>`、`<主机名>`、`<端口>` 表示从 profile 读出的值。

## 手工配置

```bash
# 1. 装私钥
mkdir -p ~/.ssh && chmod 700 ~/.ssh
cp <下载的私钥> ~/.ssh/id_rsa_<集群>
chmod 600 ~/.ssh/id_rsa_<集群>

# macOS：清除下载文件的隔离属性，否则某些工具拒绝读取
xattr -c ~/.ssh/id_rsa_<集群>

# 2. 建 socket 目录（长连接用）
mkdir -p ~/.ssh/sockets && chmod 700 ~/.ssh/sockets

# 3. 追加下面的段到 ~/.ssh/config，然后 chmod 600 ~/.ssh/config
```

```
Host <集群> <主机名>
  HostName <主机名>
  User <你的用户名>
  Port <端口>
  IdentityFile ~/.ssh/id_rsa_<集群>
  IdentitiesOnly yes
  # 以下两行仅 macOS 支持，Linux 上会报 unknown option
  UseKeychain yes
  AddKeysToAgent yes
  # 长连接
  ControlMaster auto
  ControlPath ~/.ssh/sockets/%r@%h-%p
  ControlPersist 10m
  # 保活
  ServerAliveInterval 60
  ServerAliveCountMax 3
  TCPKeepAlive yes
  # 仅当 profile 里 NEEDS_UPDATE_HOSTKEYS_NO=yes 时才加这行
  UpdateHostKeys no
```

## SSH 选项说明

**`ControlPersist 10m` 而非 `yes`**：永久驻留的 master 在笔记本休眠或换网络后会
变成失效 socket，可能留下需要清理的失效 socket。10 分钟覆盖一次交互操作的节奏，又能自然回收。
实测复用后单条命令从约 2 秒降到 0.57 秒。

**`ServerAliveInterval 60`**：应用层心跳，防止空闲 SSH 会话被中间网关静默切断。
用于保持长时间空闲会话。`TCPKeepAlive` 是 TCP 层的，两者互补。

**`UpdateHostKeys no`**：部分平台的服务端对主机密钥轮换扩展返回错误签名：

```
client_global_hostkeys_prove_confirm: server gave bad signature for RSA key 0
```

该设置仅禁用服务端主机密钥轮换扩展；首次主机密钥仍按正常流程校验。仅在出现该告警且 profile 标记 `NEEDS_UPDATE_HOSTKEYS_NO=yes` 的集群上使用。

**`IdentitiesOnly yes`**：只用指定的私钥。ssh-agent 里密钥多时，避免因尝试次数
过多被服务端拒绝。

## macOS 与 Linux 差异

| 项 | macOS | Linux |
|---|---|---|
| `UseKeychain` / `AddKeysToAgent` | 支持 | **不支持**，报 unknown option |
| 下载文件隔离属性 | 需 `xattr -c` | 无此概念 |
| `sed -i` | 需 `sed -i ''`（BSD sed） | `sed -i`（GNU sed） |

`setup-ssh.sh` 检测 `uname -s` 自动处理前两项。

## 长连接管理

```bash
ssh -O check <集群>     # 查看 master 状态
ssh -O exit <集群>      # 手工断开（网络切换后卡住时用）
```

## 密钥有效期

超算平台的私钥通常有有效期，文件名里就带，例如
`<用户名>_<主机>_RsaKeyExpireTime_2026-10-29_12-51-40.txt` 表示 2026-10-29 过期。
到期前从控制台重新下载并重跑 setup 脚本。

profile 里的 `KEY_NAME_MARKER` 就是用来从这种文件名里提取用户名的；公开
`scnet-hpc` profile 使用 `_<CLUSTER_HOST>_` 占位符，所以安装时通常需要显式传
用户名，或在本地私有 profile 中补齐真实标记。

查看密钥指纹：

```bash
ssh-keygen -lf ~/.ssh/id_rsa_<集群>
```

## 加 passphrase（可选）

```bash
ssh-keygen -p -f ~/.ssh/id_rsa_<集群>
```

配合 macOS 的 `UseKeychain yes` + `AddKeysToAgent yes`，只需首次输入一次。

## 常见连接失败

| 现象 | 原因 |
|---|---|
| `Permission denied (publickey)` | 私钥过期，或本机 IP 不在平台白名单 |
| `Connection timed out` | 端口被本地网络阻断（超算常用非 22 端口）|
| `Bad owner or permissions on config` | `chmod 600 ~/.ssh/config` |
| `WARNING: UNPROTECTED PRIVATE KEY` | `chmod 600 ~/.ssh/id_rsa_<集群>` |
| 首次连接等待主机指纹确认 | 在等确认主机指纹，加 `-o StrictHostKeyChecking=accept-new` |

多数超算平台有 **IP 白名单**，换网络（家里/公司/热点）后可能连不上，
需要去控制台加当前 IP。

## 在脚本里调用

```bash
ssh -o BatchMode=yes <集群> '<命令>'
```

`BatchMode=yes` 让认证失败立刻返回，而不是卡在密码提示上等输入。写自动化脚本时
应启用，以避免自动化流程等待交互输入。

## 文件传输

```bash
scp local.py <集群>:/public/home/$USER/scripts/
scp <集群>:/public/home/$USER/scripts/logs/job_123.log .
rsync -avz --progress ./dir/ <集群>:/public/home/$USER/dir/   # 大量文件
```

上述命令复用 SSH profile 中的连接参数。
