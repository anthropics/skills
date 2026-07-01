# OpenSpec 映射

当用户需要 ECL bundle 之外的 OpenSpec 兼容输出时使用此参考。

## 映射

- `00-overview.md` + `05-constraint-ledger.md` + `10-a-preprocess.md` -> `proposal.md`
- `30-c-requirements.md` + `20-b-divergence.md` 中保留的方案 -> `specs/<change>/spec.md`
- `40-d-critique.md` + `50-e-closure.md` + `70-g-red-blue.md` + `95-execution-manifest.md` -> `design.md`
- `95-execution-manifest.md` + `96-code-batches.md` + `90-code-handoff.md` 实现单元 -> `tasks.md`

## 规则

- 仅在审批门关闭且 A-H 加 J 收敛后才导出。
- 反映冻结路径，而非已丢弃的替代方案。
- 保留相同的约束、成功语义和验收规则。
- 将 `tasks.md` 视为依赖感知的执行视图，而非单元名称的平面转储。
- 当 ECL bundle 有批次顺序、验证检查点和完成信号时，`tasks.md` 应将其暴露出来。
- 如果 `code_ready=false`，导出的 OpenSpec 包也必须传达编码尚未就绪。
