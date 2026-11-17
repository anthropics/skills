# DataEase V2 ChatBI 工具使用手册

本工具集成了 DataEase V2 的 API 能力，通过 AI 驱动的方式，帮助用户快速将数据资产转化为可视化图表和看板。

## 1. 核心功能概览

*   **自动数据探索**：自动识别数据集结构、字段名称及数据类型。
*   **单图表部署**：支持快速创建柱状图、折线图、饼图和明细表。
*   **多图表看板**：支持在一个仪表板中自动布局多个不同类型的图表。
*   **字段动态清洗**：自动剔除模板硬编码，确保图表字段与数据集完全匹配。

## 2. 快速开始

### 2.1 环境配置
在项目根目录创建 `.env` 文件，并配置以下凭据：
```env
DATAEASE_ACCESS_KEY=你的AK
DATAEASE_SECRET_KEY=你的SK
DATAEASE_BASE_URL=https://de.example.com:20000/de2api
```

### 2.2 验证连接
运行以下命令检查是否能正常获取数据集：
```bash
python3 scripts/inspect_data.py --list-datasets
```

## 3. 使用手册

### 3.1 数据探索
在创建图表前，建议先查询数据集字段：
```bash
# 查询特定数据集字段
python3 scripts/inspect_data.py --dataset "数据集名称或ID"
```

### 3.2 部署单图表
```bash
python3 scripts/deploy.py <类型> <标题> <数据集> <维度字段> <指标字段>
```
*   **类型**: `bar`, `line`, `pie`, `table_info`
*   **示例**: `python3 scripts/deploy.py bar '销售周报' '销售数据集' '门店' '成交额'`

### 3.3 部署多图表看板
```bash
python3 scripts/multi_deploy.py <看板标题> '<JSON配置>'
```
*   **JSON示例**: 
    ```json
    [
      {"type":"bar", "title":"门店分布", "dataset_name":"ds1", "x_axis":["门店"], "y_axis":["额度"]},
      {"type":"line", "title":"增长趋势", "dataset_name":"ds1", "x_axis":["日期"], "y_axis":["额度"]}
    ]
    ```

## 4. AI 协作最佳实践 (OpenClaw)

在 OpenClaw 等 AI 终端中使用时，您可以直接用自然语言下令：

*   **初级指令**: “帮我分析一下‘电商数据集’。” (AI 会自动查询字段并给出看板建议)
*   **进阶指令**: “用‘销售记录’数据集做一个看板，左边放门店对比柱状图，右边放日期趋势图。”
*   **提示**: AI 现在遵循“执行优先”原则，它会默默为您完成所有技术细节，直接返回最终的预览链接。

---
*注：生成的仪表板默认处于“已发布”状态，您可以直接点击返回的 URL 进行查看。*
