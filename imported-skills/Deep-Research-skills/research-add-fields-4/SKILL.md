---
name: research-add-fields
user-invocable: true
description: 向现有调研outline补充字段定义。
allowed-tools: Bash, Read, Write, Glob, WebSearch, Task, AskUserQuestion
---

# Research Add Fields - 补充调研字段

## 触发方式
`/research-add-fields`

## 执行流程

### Step 1: 自动定位Fields文件
在当前工作目录查找 `*/fields.yaml` 文件，自动读取现有fields定义。

### Step 2: 获取补充来源
询问用户选择：
- **A. 用户直接输入**：用户提供字段名称和描述
- **B. Web Search搜索**：启动web-search-agent搜索该领域常用字段

### Step 3: 展示并确认
- 展示建议的新字段列表
- 用户确认哪些字段需要添加
- 用户指定字段分类和detail_level

### Step 4: 保存更新
将确认的字段追加到fields.yaml，保存文件。

## 输出
更新后的 `{topic}/fields.yaml` 文件（原地修改，需用户确认）
