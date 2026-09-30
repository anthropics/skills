# Ascend CI — Critical 告警清单

> 数据来源：`ascend-ci-deployment/monitoring/config-for-infra-cn4-x86-common-cluster/`
> 的 `prometheus-rules.yaml`（38 条规则）+ `alertmanager-config-secret.yaml`（路由）。
> 本文档仅收录 **severity: critical** 的 35 条告警；3 条 warning 级
> （`AlertDeliverySLOBreach`、`NPUSmallJobWaitTooLong`、`NPUNodeIdleTooLong`）不在本文范围。
>
> 部署集群：CN4 监控集群（`infra-monitoring` namespace），经 remote-write /
> Pushgateway 汇聚 11 个业务集群指标统一判定。

## 通知路由说明（Alertmanager）

| 路由 | 收件人 | 命中规则 | 重复提醒 |
|------|--------|---------|---------|
| `*ProbeStale` | zhangyang-email | 拨测停推类 | 24h（首次即时） |
| `SharedDisk.*` | zhangyang-email | 共享盘水位类 | 4h（首次即时） |
| `RunnerUpdateAvailable` / `RunnerVersionExpiring` | zhangyang-email | runner 版本类 | 4h（首次即时） |
| `NPU8Card.*` / `NPUQueue.*` | yinyulin-email | NPU 排队类 | 默认 30m |
| `NPUMetricTotal*Missing` | datastat-email | NPU 指标漏报类 | 默认 30m |
| 开源组集群（hk-001/guiyang-001~005/cn12-001/ascend-mind-third-ci） | dev-email | 其余 critical，双发 | 默认 30m |
| 其余 critical（默认路由） | zhangyang-email | 兜底 | 默认 30m |

- `guiyang-006` 全量进黑洞不外发。
- 主题带 `[SEVERITY][cluster] AlertName`，`send_resolved: true`（恢复发 RESOLVED）。
- 默认路由根：`group_by: [cluster, alertname]`，`group_wait 10s / group_interval 30m / repeat_interval 30m`。

---

## 一、GitHub / 连通性拨测类(责任人：张扬；许广跃）

| 告警名 | 触发条件 | for | 通知路由 |
|--------|---------|-----|---------|
| GitHubProxyUnreachable | 国内集群走 git 代理 clone 失败（`cluster!="hk-001"`）。⚠️ 名称/label `path="gh-proxy"` 为历史遗留，2026-08-20 起（c67fd173）拨测实际目标 = **git-cdn**（`git-cdn-service.git-cdn.svc.cluster.local:8000`） | 10m | 按集群（dev-email / 默认） |
| GitHubDirectUnreachable | hk-001 直连 GitHub clone 失败 | 10m | dev-email（hk-001） |
| GitHubUnreachable | 直连 + 代理（git-cdn）两条路径均失败（escalation） | 10m | 按集群 |
| GitHubProbeMissing | `github_probe_success{path="any"}` 全集群消失（Pushgateway/CronJob 挂） | 10m | zhangyang-email（cluster=center） |
| GitHubStatusOutage | GitHub 官方状态页事故等级 major/critical（indicator≥2） | 10m | 按集群 |
| GitHubStatusComponentDegraded | 状态页任一分项 degraded/partial_outage/major_outage | 5m | 按集群 |
| GitHubStatusProbeStale | 状态页拨测停推（`push_time_seconds{job=github_status}`>900s） | 5m | zhangyang-email（*ProbeStale，24h） |
| GitHubStatusPageUnreachable | 所有集群都拉不到状态页（`max(github_status_check_ok)==0`） | 10m | zhangyang-email（cluster=center） |
| GitHubStatusIncidentOpen | 状态页有未解决 incident（indicator=none 也兜底） | 10m | 按集群 |

## 二、Runner / CI 执行类

| 告警名 | 触发条件 | for | 通知路由 |
|--------|---------|-----|---------|
| RunnerCrashLooping | 10m 内 >10 个生命周期 <30s 的 runner pod（崩溃循环，正常基线 ≤2） | 5m | 按集群 |
| RunnerPodPendingTooLong | 单个 runner pod 未调度（`node=""`）>1800s | 5m | 按集群 |
| RunnerImagePullFailed | CI namespace 容器 ImagePullBackOff/ErrImagePull/CrashLoopBackOff | 10m | 按集群 |
| RunnerInvalidImageName | CI namespace 容器 InvalidImageName（须人工改名，不自愈） | 5m | 按集群 |
| ListenerCrashLooping | arc-systems listener 15m 内重建 >8 次（~2 分钟一次） | 5m | 按集群 |
| WorkflowRunTooLong | `-workflow` pod 纯执行时长 >2.5h | 5m | 按集群 |
| RunnerUpdateAvailable | actions/runner 落后于 GitHub 最新 release | 10m | zhangyang-email（4h） |
| RunnerVersionExpiring | 距 GitHub 30 天强制升级截止不足 5 天 | 10m | zhangyang-email（4h） |

## 三、NPU 资源类（掉卡 / 排队 / 指标漏报）

| 告警名 | 触发条件 | for | 通知路由 |
|--------|---------|-----|---------|
| NPUCardDropped | 节点 NPU `capacity - allocatable > 0`（掉卡） | 20m | 按集群 |
| NPU8CardJobWaitTooLong | 8 卡 NPU 任务排队 >10m（`ci_job_max_wait_seconds{npu_cards=8}`） | 5m | yinyulin-email |
| NPU8CardJobQueueStorm | ≥5 个 8 卡任务同时排队（`ci_job_pending_count{npu_cards=8}>=5`） | 5m | yinyulin-email |
| NPUQueueProbeStale | 排队拨测停推（`push_time_seconds{npu_queue_monitor}`>900s） | 5m | yinyulin-email |
| NPUMetricTotalUsedCountMissing | `custom_npu_total_used_count` 逐节点漏报 / 全局缺失（absent 兜底） | 5m | datastat-email |
| NPUMetricTotalMissing | `custom_npu_total` 逐节点漏报 / 全局缺失（exporter 掉线） | 5m | datastat-email |

## 四、存储 / 证书 / 成本 / 安全类

| 告警名 | 触发条件 | for | 通知路由 |
|--------|---------|-----|---------|
| SharedDiskHighUsage | SFS Turbo 共享存储用量 >90% | 5m | zhangyang-email（SharedDisk.*，4h） |
| SharedDiskMountFailed | 共享盘挂载探测失败（`shared_disk_mount_ok==0`，水位失明） | 5m | zhangyang-email（SharedDisk.*，4h） |
| SfsTurboDiskProbeStale | SFS 盘拨测停推（`push_time_seconds{sfs_turbo_disk}`>2700s，容忍丢 3 轮） | 5m | zhangyang-email（*ProbeStale，24h） |
| CertExpiring | TLS 证书 <30 天到期（`cert_expiry_days<30`） | 1h | 按集群 |
| CertProbeFailed | 探测不到端点证书（`cert_probe_ok==0`） | 10m | 按集群 |
| CloudAccountLowBalance | 华为云余额 <¥1000（BSS 可达才报，避免 -1 误报） | 10m | 按集群 |
| CloudAccountUnreachable | 华为云 BSS API 不可达 | 10m | 按集群 |
| SAExcessiveClusterAdmin | cluster-admin 绑定 SA >10 个 | 5m | 按集群 |
| SAAuditAPIUnreachable | SA 审计 CronJob 无法访问 K8s API | 5m | 按集群 |

## 五、基础设施服务 / 拨测自诊断

| 告警名 | 触发条件 | for | 通知路由 |
|--------|---------|-----|---------|
| NginxPodDown | nginx 系 namespace pod NotReady 或 ImagePull/CrashLoop | 10m | 按集群 |
| InfraServiceCrashLooping | vault / smart-git-proxy / git-cdn 容器崩溃循环或拉取失败 | 10m | 按集群 |
| ProbeStale | 任一拨测指标超期未更新（github/sfs/balance/sa/cert/runner 兜底总检） | 5m | zhangyang-email（*ProbeStale，24h） |

---

统计：critical 共 **35 条**（连通性 9 + Runner/CI 8 + NPU 6 + 存储/证书/成本/安全 9 + 基础设施/自诊断 3）。
