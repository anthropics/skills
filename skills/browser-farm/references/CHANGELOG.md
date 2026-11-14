# Changelog

## 0.1.23（2026-11-14）forge 桥

- `forge` 命令：forge(record-to-skill) 的脚本挂到档位口跑——免登录录制/探查/纯接口执行（档口与 `--keep-open` 桥焊死，forge 收尾不杀档；record 自动切有窗；多档顺序跑=多账号）
- `forge-rec` 命令：农场脚本/存Agent笔记转 forge 的 rec.json，直接进它的 evidence→probe→build 管线
- 与 forge 零耦合：不用改 forge 任何代码，两边各管各的版本

## 0.1.22（2026-11-14）存 Agent 笔记

- 录制收工第三条出口：窗口录制条蓝色「存Agent」/ GUI「停止存Agent笔记」/ CLI `record --agent`——不建脚本，落 `agent-notes/` 一份 agent 直接读的 md（步骤表+录制期间抓到的接口+原始 steps JSON）
- 老的存脚本 / 不存 / 继续录行为不变

## 0.1.21（2026-11-13）首个公开版

与内部版 v0.1.21 同源。本文件只记录公开线的变更。

- 效率模式（`start --eff` / GUI「效率跑」）：广告/埋点域名 DNS 层拦截（`blocklist.txt` 清单）、禁远端字体、禁视频自动播、磁盘缓存 8MB、关 DoH；看护/eval/快照自动拉回保持跑法
- `structured`：当前页 og / json-ld / meta / canonical 一把抓（CLI + HTTP）
- `/slots` 与档位详情带 `mode`，GUI 徽章显示「运行中·效率」
- 全部基础能力见 README（账号档/登录保持/快照回滚/录制回放/盯表触发/抓包重放/Chrome 门卫/配置搬家）
