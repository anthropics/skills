# Shanghai Cluster (openmerlin-shanghai-001) 问题与解决

## 集群架构

| 层级 | 节点 | 位置 | 架构 | 规格 |
|------|------|------|------|------|
| 云上 | master-01/02/03 | 华为云 ECS | x86_64 | 4C8G, Ubuntu 22.04 |
| 云下 | lab-worker-01/02/03/04 | 实验室 | aarch64 | 384C/1.5TB, 8× Ascend950DT, openEuler 24.03 |
| 服务 | admin123 (192.168.13.107) | 实验室 | x86_64 | 56C/251G, Ubuntu 22.04 |

**网络**：管理面 10.254.1.0/24（云上eth1）+ 192.168.8.0/21（云下enp34s0f1），服务面 10.254.9.0/24（云上eth0），数据面 178.27.0.0/18（云下data0）。

**ELB**：管理面 `115.175.0.82:6443`（内网 `10.254.1.33`，白名单模式），服务面 `10.254.9.147:6443`。

---

## 一、K8s 集群初始化

### 1.1 Cilium cluster-pool CIDR 与 kubeadm CIDR 不一致

**现象**：Pod 实际分配 IP 为 `10.0.x.x`，而非 kubeadm init 时指定的 `10.244.0.0/16`。

**根因**：Cilium 默认使用 `cluster-pool-ipv4-cidr: 10.0.0.0/8`，kubeadm 的 `--pod-network-cidr` 只用于 kube-proxy 和 CoreDNS 默认配置，Cilium 自己的 IPAM 不受其影响。

**解决**：将 `ipv4-native-routing-cidr` 设为 `10.0.0.0/8` 与实际 Pod IP 段对齐。后续所有涉及 Pod CIDR 的配置（masquerade、routing）也必须使用 `10.0.0.0/8`。

### 1.2 Flannel CNI 残留冲突

**现象**：CoreDNS pod 创建立即失败，日志 `plugin type="flannel" failed: open /run/flannel/subnet.env: no such file or directory`。

**根因**：旧集群的 flannel CNI 配置文件 `/etc/cni/net.d/*.conf` 未被 kubeadm reset 清理。kubelet 在 Cilium 写入自己的 CNI 配置之前，先读到了 flannel 的配置。

**解决**：删除 `/etc/cni/net.d/*` 下所有文件，重启 kubelet。

---

## 二、证书与 ELB

### 2.1 证书不含 ELB IP 导致 TLS 验证失败

**现象**：`kubeadm join 10.254.9.147:6443` 报 `x509: certificate is valid for 10.96.0.1, 10.254.1.187, not 10.254.9.147`。

**根因**：`kubeadm init` 时 control-plane-endpoint 设为 `10.254.1.187:6443`，证书仅包含该 IP。后续新增的 ELB IP 不在 SAN 中。

**解决**：更新 kubeadm-config ConfigMap，将期望的所有 IP 加入 `apiServer.certSANs` 列表，然后在三台 master 上重新生成证书并重启 API server。

最终 certSANs：`10.254.1.187, 10.254.1.232, 10.254.1.25, 10.254.9.49, 10.254.9.229, 10.254.9.85, 10.254.9.147, 115.175.0.82`

### 2.2 证书重新生成后丢失老 SAN 导致 API server CrashLoop

**现象**：为新 ELB 重新生成证书后，API server 全部 CrashLoopBackOff。kubectl 报 `certificate is valid for ..., not 10.254.1.187`。

**根因**：`kubeadm init phase certs apiserver` 不自动合并已有 SAN，仅根据 ConfigMap 中的列表重新生成。某次只写入新增 IP 而未保留原有 IP，导致 API server 实际监听的 `10.254.1.187` 被移除。

**解决**：每次修改证书前确保 `certSANs` 列表包含**所有**需要访问 API server 的 IP 地址（管理面、服务面、ELB 两侧）。修改后必须分发证书到所有 master 并重启 API server。

### 2.3 cluster-info 和 kube-proxy ConfigMap 指向老地址

**现象**：lab 节点 `kubeadm join` 时尝试连接 `10.254.1.187:6443`（不通），lab 节点上的 kube-proxy 日志也显示连接该地址超时。

**根因**：`kube-public/cluster-info` ConfigMap 和 `kube-system/kube-proxy` ConfigMap 中硬编码了 kubeadm init 时的 server 地址，ELB 添加后未同步更新。

**解决**：更新两个 ConfigMap 的 server 地址为 ELB `10.254.9.147:6443`。

---

## 三、Lab 节点系统差异

### 3.1 OpenEuler 无 systemd-resolved

**现象**：Pod sandbox 创建失败，kubelet 日志 `open /run/systemd/resolve/resolv.conf: no such file or directory`。

**根因**：OpenEuler 24.03 不使用 systemd-resolved，`/run/systemd/resolve/` 目录不存在。kubelet 默认配置引用该路径。

**解决**：`mkdir -p /run/systemd/resolve && ln -sf /etc/resolv.conf /run/systemd/resolve/resolv.conf`

### 3.2 containerd v1.6 配置格式差异

**现象**：将 master 节点（v2.x）的 containerd 配置直接复制到 lab 后，containerd 启动失败或 mirror 不生效。

**根因**：OpenEuler 自带 containerd v1.6，使用旧版 config 格式。关键差异：
- Registry mirror 用 `[plugins."io.containerd.grpc.v1.cri".registry.mirrors]` 而非 v2.x 的 `certs.d` 目录
- `sandbox_image` 用双引号 `sandbox_image = "..."`，sed 替换需注意引号匹配
- `SystemdCgroup = true` 写死在小节内，不在顶层

**解决**：使用 `containerd config default` 生成 v1.6 默认配置，手动添加 mirror 和 sandbox 修改。

### 3.3 Lab 节点无外网直连

**现象**：`yum install kubeadm` 失败，`Could not resolve host: mirrors.aliyun.com`

**根因**：lab 节点虽能通过公网 DNS 解析域名，但到某些 CDN 的实际 TCP 连接不通，导致包下载失败。

**解决**：从有外网的 master-01 下载 aarch64 RPM 包，通过 scp 传到 lab 节点，本地 `rpm -ivh` 安装。用 `--nodeps` 跳过 kubernetes-cni 依赖（Cilium 自带 CNI 插件，不需要 k8s 自带的）。

### 3.4 两节点 hostname 相同导致相互覆盖

**现象**：两台 lab 节点加入集群后，`kubectl get nodes` 只显示一个 `localhost.localdomain`。

**根因**：两台节点的初始 hostname 都是 `localhost.localdomain`。K8s 以 hostname 作为节点唯一标识，后者加入时覆盖前者。

**解决**：加入集群前先设置唯一 hostname（`lab-worker-01`、`lab-worker-02`）。

---

## 四、Pod 网络与 DNS（核心难点）

DNS 问题涉及三条链路的三个断裂点：

```
Pod (10.0.x.x)
  → CoreDNS ClusterIP (10.96.0.10)     [断裂点1]
  → CoreDNS pod → forward → 上游DNS     [断裂点2]
  → 上游DNS回复 → 回不到 Pod             [断裂点3]
```

### 4.1 断裂点1：Cilium kube-proxy replacement 不工作

**现象**：Pod 内无法访问 K8s Service IP（如 `10.96.0.1:443`）。CoreDNS kubernetes 插件卡在 `Still waiting on: kubernetes`，无法初始化。

**根因**：Cilium 以 `kube-proxy-replacement: true` 安装，但 BPF 级别的 Service 路由未正确生效。

**解决**：关闭 kube-proxy replacement，回退到 kube-proxy iptables 模式。验证：Pod 内 `curl https://10.96.0.1:443` 返回 `ok` 即表示修复。

### 4.2 断裂点2：CoreDNS 转发到不可达上游 DNS

**现象**：Pod DNS 查询到达 CoreDNS 后，CoreDNS 向上游转发超时，返回 SERVFAIL。

**根因**：迭代修正了 3 次——
1. 初始 `forward . 114.114.114.114 8.8.8.8`：lab 节点到 114 公网不通（ICMP 被过滤）
2. 改为 `forward . 178.27.1.100 114.114.114.114`：178.27.1.100 可达（数据面 DNS），但回包路由不通（见 4.3）
3. 最终恢复 `forward . /etc/resolv.conf`：CoreDNS 使用节点自身 DNS 配置，等 4.3 修好后自然恢复

**最终方案**：lab 节点的 `/etc/resolv.conf` 中 DNS 顺序调整为 `114.114.114.114` 在前、`178.27.1.100` 在后。114 作为公网 DNS 从 pod 网络经 SNAT 后可通。

### 4.3 断裂点3：回包路由不通（Cilium masquerade 不覆盖）

**现象**：在 host 上 `nslookup api.github.com <coredns-pod-ip>` 成功，但 Pod 内同样的查询超时。CoreDNS 能发出 UDP 请求，但收不到回复。

**根因**：数据面网络（178.27.0.0/18）没有 Pod 网段（10.0.0.0/8）的路由。CoreDNS pod 用其 Pod IP (10.0.x.x) 发出 DNS 请求，回包到 178.27.0.0/18 段后找不到回程路由。

Cilium iptables masquerade 规则中存在 `oifname != "cilium_*"` 条件——当出流量走 `cilium_host` 接口时，条件不满足，SNAT 被跳过。Pod 流量以原始 Pod IP 发出，回包自然丢失。

从 nftables 规则可见：
```
oifname != "cilium_*" ip saddr 10.0.4.0/24 ip daddr != 10.0.0.0/8 masquerade
```
`cilium_host` 作为出接口时匹配 `cilium_*` 前缀，被 `!=` 排除；但 pod 到外部主机的流量不走物理网卡，走 `cilium_host`，于是 SNAT 被跳过。

**解决**：启用 Cilium BPF masquerade（`enable-bpf-masquerade: "true"`），BPF 层面的 SNAT 不依赖 iptables 的接口匹配逻辑，对所有出 pod 流量生效。

**注意事项**：BPF masquerade 依赖 `enable-node-port: "true"`，必须同时配置，否则 Cilium agent 启动即 CrashLoop（报 `BPF masquerade requires NodePort`）。两个配置需同时写入 ConfigMap 后再重启 Cilium agent。

### 4.4 Pod DNS 临时 workaround

在 DNS 完全修复之前，对关键 Pod（ARC controller、listener、runner）临时使用 `dnsPolicy: None` + 直接指定公网 DNS `114.114.114.114`，绕过 CoreDNS 的转发链路。DNS 修复后应移除该 workaround。

### 4.5 CoreDNS pod 卡在 0/1 Ready

**现象**：CoreDNS pod 长时间 `0/1 Running`，readiness probe 503。

**根因**：CoreDNS kubernetes 插件启动时需连接 API server（`10.96.0.1:443`）初始化。如果 Cilium 未完全就绪，Service IP 路由不通，插件进入等待循环，不处理任何 DNS 查询。

**解决**：等 Cilium agent 全部 Ready 后，重启 CoreDNS pod。

---

## 五、Lab 节点时钟偏差

### 5.1 时钟快 8 小时导致 Runner 无限循环创建

**现象**：
- Runner pod 日志：`The token is not valid until 07/16/2026 21:43:24. Current server time is 07/16/2026 13:43:09`
- Runner 行为：启动 → 注册 JIT → 创建 session 失败 → 退出 → listener 检测 runner 消失 → 创建新 runner → 再次失败 → 无限循环
- GitHub 侧：job 永远 QUEUED

**根因**：lab 节点（openEuler 24.03）系统时钟比实际时间快 8 小时（显示 `Fri Jul 17 05:43 CST` 而实际为 `Fri Jul 16 21:43 CST`）。GitHub JIT token 的 `nbf`（not-before）claim 基于实际 UTC 时间签发，但 runner 用容器内错误的时间做校验——token 的生效时间看起来在未来，因此被拒绝。

**解决**：从 master-01 获取正确时间戳，用 `date -s` 同步 lab 节点时钟。

**遗留**：需配置 NTP 服务永久修复（`chronyd` 或 `ntpdate` + cron），否则重启后时钟可能再次漂移。

---

## 六、镜像拉取

### 6.1 registry.k8s.io 不可达

**解决**：所有节点 containerd 配置阿里云镜像代理 `registry.k8s.io → registry.aliyuncs.com/google_containers`。lab 节点（containerd v1.6）在 `[plugins."io.containerd.grpc.v1.cri".registry.mirrors]` 段配置。

### 6.2 quay.io S3 CDN 不可达

**现象**：Cilium 镜像 `quay.io/cilium/*` 拉取超时，报 `TLS handshake timeout` 到 `cdn01.quay.io`。

**解决**：Docker Hub 镜像走 `docker.m.daocloud.io` 代理。quay.io 镜像通过从已部署节点 `ctr images export/import` 传输。

### 6.3 daocloud /v2/ 返回 401（误判）

**现象**：`curl https://docker.m.daocloud.io/v2/` 返回 HTTP 401。

**根因**：这是 Docker Registry API 的标准认证流程——对 `/v2/` 的首次请求返回 401 + Bearer challenge，containerd/crictl 会自动完成后续 token 交换。**不是认证失败**，尝试 pull 即可验证。

---

## 七、GitHub Actions Runner

### 7.1 Runner 无限循环（由时钟偏差引起）

见 5.1。时钟修复后循环自停。

### 7.2 Listener hostNetwork 端口冲突

**现象**：Listener pod Pending，scheduler 报 `0/5 nodes are available: 3 node(s) didn't have free ports for the requested pod ports`

**根因**：ARC Helm 模板默认给 listener 容器加了 hostPort 8080（metrics）。搭配 hostNetwork 使用时，同一节点只能运行一个 listener。多个 scale set 时冲突。

**解决**：DNS 和 Service 路由修复后，去掉 listener 的 hostNetwork 和 dnsPolicy override，恢复独立 pod 网络栈，端口冲突消失。

### 7.3 Scale set ID 变化导致 job 孤儿

**现象**：多次 `helm uninstall` + `helm install` 后，GitHub job 状态永远 QUEUED，listener 显示 `count=0`。

**根因**：每次重装向 GitHub Actions 注册新的 scale set ID。此前 PR 触发的 job 已绑定到旧 scale set ID，GitHub 不会自动迁移到新 scale set。新 scale set 看不到任何 assigned job。

**解决**：确认配置正确后只安装一次，不再卸载。新 job 由新 PR 触发，会绑定到当前有效的 scale set ID。生产环境依赖 ArgoCD GitOps 管理后不存在手动卸载场景。

### 7.4 maxRunners=0 意外锁死

**现象**：EphemeralRunnerSet replicas=0，listener 收到 assigned job 但不创建 runner。

**根因**：手动 `kubectl patch` 设了 maxRunners=0 以停止无限创建循环，但该字段不在 Helm values 中，后续 `helm upgrade` 无法恢复。Controller 读取的是 AutoscalingRunnerSet 资源中的值，不随 Helm 更新。

**解决**：直接 kubectl patch 将 maxRunners 设为期望值。

### 7.5 values.yaml 与已有 A3 配置对齐

**要求**：PR 中 values.yaml 必须与已有 A3 runner 配置完全一致，仅修改标签。

**根因**：多轮手动编辑引入格式偏差（缩进不一致、bucket 数组格式不同、空格缺失），导致 yamllint 和代码审查反复要求修改。

**解决**：终极方案——直接从 `linux-aarch64-a3-8/values.yaml` 复制，仅做 3 处替换：`a3-8→950dt-n`、`ascend-1980→ascend-950dt`、`gy-005→shanghai-001`。其余一字不改。

---

## 八、Ascend NPU

### 8.1 Ascend Docker Runtime 版本与 Device Plugin 不匹配

**现象**：NPU 容器启动失败 `ascend-docker-runtime did not terminate successfully: exit status 1`，日志 `dcmi init failed, error code: -8255`。

**根因**：Runtime v7.0.RC1 仅支持 DCMIv1 API，而 Device Plugin v26.1.0.beta.2 使用 DCMIv2 API。Ascend950DT 需要 v26.x Runtime。

**解决**：升级 Runtime 到 v26.1.0.beta.2。**踩坑**：installer 会校验文件名，必须包含 `aarch64` 字符串，不能重命名。

### 8.2 资源名不一致

**现象**：Volcano 调度报 `Unschedulable: huawei.com/ascend-a5 not found`。

**根因**：ConfigMap 中定义了 `huawei.com/ascend-a5` 作为资源名，但 Ascend Device Plugin 在节点上实际注册的资源名为 `huawei.com/npu`。

**解决**：所有 ConfigMap 和 values.yaml 中的资源名统一改为 `huawei.com/npu`。

### 8.3 presetVirtualDevice=false 导致 Device Plugin 崩溃

**现象**：Device Plugin CrashLoop，日志 `only 310p, 910a2 and 910a3 support presetVirtualDevice false`。

**根因**：Ascend950DT 只支持静态虚拟化（presetVirtualDevice=true），动态 vNPU 仅限 310P/910A2/910A3 系列。

**解决**：保持 `presetVirtualDevice=true`。配置 vnpu.cfg `dev0:0-7` 实现 1×8 卡虚拟设备。

### 8.4 Volcano NPU 插件无默认 handler

**现象**：NPU job 调度失败 `validNPUJob failed: no policy handler registered`。

**根因**：Volcano NPU 插件需要 Pod annotation 指定调度策略，950DT 没有预配置的默认 handler。

**解决**：ConfigMap 中 PodTemplate 添加 annotation `huawei.com/schedule_policy: chip1-node8`。

### 8.5 liburma.so.0 共享库缺失

**现象**：workflow 容器 Started 后 300s FailedPostStartHook，日志 `liburma.so.0: cannot open shared object file`。

**根因**：Ascend950DT 的 `npu-smi` 依赖 `umdk-urma-lib` 包中的 `liburma.so.0`，该库安装在宿主机的 `/usr/lib64` 路径下。workflow pod 默认只挂载了 `/usr/local/Ascend/driver`，未挂载 `/usr/lib64`。

**解决**：ConfigMap 添加 hostPath volume：`/usr/lib64` → 容器 `/usr/lib64`。

---

## 九、Volcano 调度器

### 9.1 Volcano 镜像拉取与部署

**现象**：阿里云 registry 没有 Volcano ARM64 镜像，docker.io 直连不稳定。

**解决**：通过 `docker.m.daocloud.io/volcanosh/` 代理拉取 4 个镜像（controller-manager、scheduler、webhook-manager、agent），tag 为 `docker.io/volcanosh/*`。

### 9.2 Master 节点资源紧张

**现象**：master 只有 4C8G，Volcano 默认资源请求（5.5C/15G）超过可用资源。

**解决**：下调 Volcano 各组件资源请求到适配 4C8G。用 buildah 构建 amd64 版本镜像供 master 节点使用，避免跨架构拉取。

---

## 十、Service 管理

### 10.1 Admin123 服务节点

新增 x86 节点 `192.168.13.107` 作为专用服务节点，从 master 迁出非控制面服务：resource-api、ARC controller、listeners、secrets-manager、imagepullsecret-patcher、nginx-pypi-cache。

**配置要点**：
- DNS 顺序：`114.114.114.114` 在前优先，`178.27.1.100` 在后
- containerd mirror：daocloud + aliyuncs
- 无 storage provisioner：PVC 改为 hostPath

### 10.2 Weight NFS 新节点不可见

**现象**：后加入的 lab-03/04 上报 `FailedMount: /mnt/weight/vllm-ascend is not a directory`。

**根因**：lab-01/02 有 `/mnt/weight` NFS 挂载，但 03/04 只有 `/mnt/share` 共享 NFS。

**解决**：ConfigMap 中将 weight 路径从 `/mnt/weight/vllm-ascend` 改为 `/mnt/share/vllm-ascend/weight`（所有节点均有此共享 NFS），并设置 `type: DirectoryOrCreate`。

---

## 十一、Summary of Learned Patterns

| 排查模式 | 适用场景 |
|----------|----------|
| DNS 链路分段验证（Pod→CoreDNS→上游→回包） | 任何 Pod 内网络不通 |
| 证书 SAN 列表必须完整 | 添加新入口 IP |
| 时钟偏差 → JIT token 校验失败 | Runner 无限循环 |
| Helm 重装 → scale set ID 变化 | GitHub job 永远 queued |
| 镜像 401 = 正常认证流程 | 误判为镜像仓库故障 |
| OpenEuler 与 Ubuntu 系统差异 | 路径、containerd 版本 |
| 云下节点无外网 | 镜像预拉 + scp 传输 |

---

## 待完成

| # | 事项 |
|---|------|
| 1 | ArgoCD 注册集群 + PR 合入，纳入 GitOps |
| 2 | lab 节点 NTP 永久配置 |
| 3 | CoreDNS 转发回包路由永久修复（去掉 dnsPolicy workaround） |
| 4 | Volcano + Device Plugin + NodeD 完整部署 |
