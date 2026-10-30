# DataEase V2 Chart Skill：开启 BI 可视化的“口令直达”时代

数据可视化（BI）系统的核心职责是将海量碎片化数据转化为直观的业务洞察，从而辅助决策。然而，传统的 BI 系统通常采用“由人驱动”的模式：复杂的数据集关联、繁琐指标拖拽、多次图表微调，均增加了数据消费的门槛。

2026年4月，Cordys 开源项目组正式发布 **DataEase V2 Chart Skill**。借助该技能，DataEase 用户可以实现从“手动绘图”到“口令制图”的跨越式转变。该技能将 DataEase V2 的底层 API 能力封装为 AI 可直接调用的模块，用户只需通过自然语言交互，即可自动完成数据集探索、图表配置及仪表板部署。

## 一、DataEase V2 Chart Skill 的功能

DataEase V2 Chart Skill 严格遵循 DataEase V2 架构设计，专注于为大模型提供高质量、强语义的可视化能力。其核心功能矩阵包括：

* **全量数据资产自动探索**：AI 助理能自动检索 DataEase 中的数据集树状结构，并深入穿透至字段层级，识别字段名称（Dimension/Measure）与类型，彻底解决“找不到数”的痛点。
* **多图表看板智能平铺**：支持单指令生成包含柱状图、折线图、饼图等多个组件的综合看板。内置智能布局算法，能够根据图表数量自动计算最佳显示比例与排列位置。
* **动态字段清洗与映射**：内置强大的正则与递归替换引擎。AI 会自动识别并移除模板中残留的演示文案，将真实的业务字段名精准映射至 xAxis、yAxis、标签及提示框中，确保数据展示的准确性。
* **即时发布与多端预览**：图表创建后自动触发发布状态更新，并返回唯一的预览 URL。用户无需登录后台，即可在移动端或 PC 端即时查看最新的分析结果。

## 二、DataEase V2 Chart Skill 的安装方法

DataEase V2 Chart Skill 的部署过程极其简便，支持手动配置或通过 AI 自动化引导完成。以下是以 OpenClaw 为例的安装流程：

### 1. 快速安装

通过与 OpenClaw 对话，一键克隆技能库：

```bash
git clone https://github.com/zevin-cloud/dataease-v2-chart-skill ~/.openclaw/workspace/skills/dataease-chart-skill
```

<img width="1910" height="873" alt="image" src="https://github.com/user-attachments/assets/7ab6e92c-c066-4946-9744-d227e57ceae7" />

### 2. 安全配置与对接

用户可以通过直接在 OpenClaw 对话框中告知具体的配置信息，由 OpenClaw 自动完成：

```text
DATAEASE_ACCESS_KEY=你的AccessKey
DATAEASE_SECRET_KEY=你的SecretKey
DATAEASE_BASE_URL=https://你的域名:20000/de2api
```
<img width="1910" height="873" alt="image" src="https://github.com/user-attachments/assets/b11dfa65-c0f9-4746-a8b4-0cd21e2d9f29" />


## 三、DataEase V2 Chart Skill 的使用场景

配置完成后，用户无需再次登录 DataEase，直接在 OpenClaw 对话框通过自然语言下达指令，即可方便地调取所需的业务数据。

### 1. 查询数据集与字段

AI 将自动列出所有数据集 ID，并穿透展示维度与指标字段。

```bash
python3 scripts/inspect_data.py --list-datasets
python3 scripts/inspect_data.py --dataset "数据集名称"
```

### 2. 部署图表看板

直接用自然语言描述需求，AI 会自动转换为对应的部署指令。

* **单图表**: “帮我用销售数据集创建一个柱状图，展示各门店的销售额”
* **多图表**: “帮我分析下电商数据集，我想看平台访问、转化阶段和产品分布”
<img width="1910" height="873" alt="a04c0bed-bc05-4274-82db-cec989429213" src="https://github.com/user-attachments/assets/1a8ba71f-64b2-46d2-953e-091ffbf105b0" />
<img width="1910" height="873" alt="bbad4c11-f6dd-48b9-a19a-8bf8845eadb9" src="https://github.com/user-attachments/assets/bc402970-df20-427c-828c-15f9eab98b76" />
<img width="1910" height="873" alt="75fdb202-c71d-43b1-ab35-bcad735e4bbd" src="https://github.com/user-attachments/assets/b432410e-b2a7-48ae-ab0a-868382401014" />
<img width="1910" height="873" alt="66276c60-1148-4282-8843-aebcae85d78b" src="https://github.com/user-attachments/assets/d20e0d21-7255-4efb-9a87-72db1a046590" />
<img width="1910" height="873" alt="4a9ca2aa-826a-4ae7-a014-8a5a06cc3ec1" src="https://github.com/user-attachments/assets/c86d2036-0014-4907-a0bb-f595b7835e67" />





## 四、总结

通过对 DataEase V2 底层接口的深度封装，DataEase V2 Chart Skill 实现了从“复杂拖拽”到“口令直达”的信息穿透。极大地提升了企业数据的流动性与决策效率。

---
