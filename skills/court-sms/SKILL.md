---
name: court-sms
description: Process Chinese court SMS notifications (法院短信). Triggers when message contains court name + case number + delivery platform link (zxfw.court.gov.cn / sd.gdems.com / jysd.10102368.com). Parses SMS, downloads legal documents to ~/Desktop/文书下载/{case_number}/, extracts key dates from summons/court notices. Optional: write hearing dates to Feishu bitable.
---

# 法院短信识别与文书下载

## 核心原则（强制执行）

1. **触发即调用**：消息含法院名称 + 案号 + 送达平台链接（zxfw.court.gov.cn / sd.gdems.com / jysd.10102368.com）→ 立即调用本 skill，不绕路
2. **下载到桌面**：所有文件下载到 `~/Desktop/文书下载/{案号}/`，不放到案件目录
3. **原样保存，同名去重**：保留 API 返回的原始文件名，不删除、不整理、不合并。如同名文件已存在，追加 `_2`、`_3` 后缀防止覆盖
4. **只提取关键文书**：仅对传票和开庭/出庭通知书提取关键信息，其他文书不读不总结

## 功能概述

处理法院短信的完整流程：**粘贴短信 → 解析内容 → 下载文书 → 原样保存到桌面 → 仅提取传票/开庭通知关键日期 → 可选写入飞书**。

支持两种触发方式：

**方式一：粘贴短信原文**

```text
收到法院短信，内容如下：
【xx市人民法院】张三，您好！您有（2025）苏0981民初1234号案件文书送达，请点击链接查收：https://zxfw.court.gov.cn/zxfw/#/pagesAjkj/app/wssd/index?qdbh=DEMO1&sdbh=DEMO2&sdsin=DEMO3
```

**方式二：直接发送送达链接**

用户直接粘贴送达 URL，跳过短信文本解析，直接从 URL 提取 `qdbh`、`sdbh`、`sdsin` 参数。

```text
https://zxfw.court.gov.cn/zxfw/#/pagesAjkj/app/wssd/index?qdbh=xxx&sdbh=xxx&sdsin=xxx
```

## 短信类型分类

| 类型 | 特征 | 含下载链接 | 处理方式 |
| --- | --- | --- | --- |
| 文书送达 | 含送达平台链接 + 案号 | 是 | 下载文书并归档 |
| 立案通知 | 含"已立案"等关键词 | 可能有 | 展示解析结果 |
| 信息通知 | 无链接，纯信息 | 否 | 展示解析结果 |

**支持的送达平台**：`zxfw.court.gov.cn`（全国）、`sd.gdems.com`（广东）、`jysd.10102368.com`（集约送达）。详见 `references/sms-patterns.json`。

## 依赖

| 依赖 | 用途 | 安装方式 |
|------|------|----------|
| Python 3.9+ | 运行下载脚本 | 系统自带 |
| `requests` | HTTP 请求 | `pip install requests` |
| `pdftotext` | PDF 文本提取（仅飞书功能需要） | `brew install poppler` |

---

## 工作流（五步）

### 第一步：输入解析

1. 读取 `${CLAUDE_SKILL_DIR}/references/sms-patterns.json` 作为解析参考
2. **判断输入类型**：
   - **完整短信**：包含法院签名（如 `【xx法院】`）+ 正文 + 链接 → 完整解析流程
   - **纯链接**：用户直接发送送达 URL → 跳过短信文本解析，直接从 URL 提取参数，进入第三步下载
3. 对用户粘贴的短信文本进行分析（纯链接输入跳过此步）：

**a) 短信分类**：根据关键词判断类型
- 文书送达：包含 zxfw.court.gov.cn 链接
- 立案通知：包含"已立案"、"立案通知"等
- 信息通知：其他

**b) 案号提取**：使用正则 `[（(〔[]\d{4}[）)〕]]` 匹配标准案号格式

标准案号格式示例：
- `（2025）苏0981民初1234号`
- `(2024)粤0604执保5678号`
- `〔2025〕京0105民初901号`

**c) 当事人提取**：从短信文本初步识别，最终以文书内容为准
- **注意**：短信中的称呼（如"张三，您好"）仅为短信接收人，不作为案件当事人
- 公司名称：`xx有限责任公司`、`xx有限公司`、`xx股份有限公司`
- 诉讼对峙：`A与B`、`A诉B`、`原告A 被告B`
- 角色前缀：`原告：xxx`、`被告：xxx` 等

**d) 下载链接提取**：识别短信中的送达平台链接并提取参数

| 平台 | 域名 | 下载方式 | 提取参数 |
|------|------|----------|----------|
| 全国法院统一送达平台 | `zxfw.court.gov.cn` | API 直连 | qdbh, sdbh, sdsin |
| 广东法院电子送达 | `sd.gdems.com` | 浏览器自动化 | 路径中的送达标识码 |
| 集约送达平台 | `jysd.10102368.com` | 浏览器自动化 | key |

**输出格式**（向用户展示）：

```text
📋 短信解析结果：
- 类型：文书送达
- 案号：（2025）苏0981民初1234号
- 当事人：张三、xx有限公司
- 下载链接：已提取（zxfw.court.gov.cn）
```

### 第二步：确定下载目录

固定下载到桌面：`~/Desktop/文书下载/{案号}/`

- `{案号}` 使用短信中提取的案号
- 目录不存在则自动创建
- **不扫描案件目录，不询问用户，直接使用此固定路径**

### 第三步：文书下载

> **直接调用 Python 脚本**，单次进程调用，30 秒内完成全部下载。

#### 执行命令

```bash
python3 "${CLAUDE_SKILL_DIR}/scripts/download_sms_docs.py" "<完整短信原文>"
```

脚本自动完成：解析 URL → 提取参数 → 调用 API → 批量下载 → 输出 JSON 结果。

**输出 JSON 包含**：`output_dir`（下载目录）、`files`（文件列表）、`case_number`（案号）、`court`（法院）、`document_types`（文书类型列表）。

#### 失败兜底

脚本失败时（网络问题/API 不可用），降级方案：

```bash
qdbh="<从URL提取>"; sdbh="<从URL提取>"; sdsin="<从URL提取>"
resp=$(curl -s -X POST "https://zxfw.court.gov.cn/yzw/yzw-zxfw-sdfw/api/v1/sdfw/getWsListBySdbhNew" \
  -H "Content-Type: application/json" \
  -d "{\"qdbh\":\"$qdbh\",\"sdbh\":\"$sdbh\",\"sdsin\":\"$sdsin\"}")
echo "$resp" | python3 -c "
import json, sys, os, urllib.request
data = json.loads(sys.stdin.read())
outdir = os.path.expanduser('~/Desktop/文书下载/') + data['data'][0].get('c_fymc','')[:6] if data.get('data') else 'temp'
os.makedirs(outdir, exist_ok=True)
for d in data['data']:
    name = d['c_wsmc'] + '.' + d['c_wjgs']
    urllib.request.urlretrieve(d['wjlj'], outdir + '/' + name)
    print(f'OK: {name}')
"
```

### 第四步：保存到桌面

1. **确定目标目录**：`~/Desktop/文书下载/{案号}/`
2. **保存文件**：将临时目录中的所有文件（PDF + MP4 等）复制到目标目录
3. **同名处理**：保留 API 返回的原始文件名；如同名文件已存在，追加 `_2`、`_3` 后缀（检测文件大小，大小相同则为真重复跳过，大小不同则为同名异内容保留）
4. **不做任何删减**：不删除文件、不重命名、不整理子目录、不合并 PDF

### 第五步：关键文书提取

> **仅提取传票和开庭/出庭通知书**，其他文书（举证通知、判决书、裁定书等）不读取、不总结。

#### 文书类型识别

| 文书类型 | 识别关键词 | 必须提取的信息 |
|---------|-----------|---------------|
| **传票** | 标题含"传票" | 开庭时间、地点、法庭、案号、案由 |
| **开庭通知书/出庭通知书** | 标题含"开庭通知"或"出庭通知" | 开庭/宣判时间、地点、法庭、案号 |

#### 提取方式

1. 扫描目标目录文件名，找到标题含"传票"或"开庭通知"或"出庭通知"的 PDF
2. 用 `pdftotext` 提取文本（前 500 字符即可）
3. 正则匹配日期时间、地点、案号等信息
4. 向用户展示关键日期信息

#### 向用户汇报

```text
📅 关键日期信息已提取：

┌─────────────────────────────────────────────────────────────┐
│ 案号：（2025）浙0105刑初789号                                │
│ 法院：某市某区人民法院                                       │
│ 当事人：王某某                                              │
├─────────────────────────────────────────────────────────────┤
│ ⚠️  2025-06-15 09:30  —  开庭审理  —  第三审判庭            │
└─────────────────────────────────────────────────────────────┘
```

---

## 可选：飞书多维表格集成

如需将开庭信息自动写入飞书多维表格，安装 `lark-cli`（`npm install -g @larksuiteoapi/lark-cli`）并配置。

写入飞书时，使用字段名（中文）而非 field_id，单选字段用选项名（"高"/"中"/"低"），日期时间字段传毫秒时间戳：

```bash
APP_TOKEN="<YOUR_APP_TOKEN>"
TABLE_ID="<YOUR_TABLE_ID>"
timestamp=$(date -j -f "%Y-%m-%d %H:%M" "2025-06-15 09:30" "+%s")000

lark-cli api POST "/open-apis/bitable/v1/apps/${APP_TOKEN}/tables/${TABLE_ID}/records" \
  --as user \
  --data '{
    "fields": {
      "事项": "开庭审理（2025）苏0102民初5678号",
      "任务内容": "某市某区人民法院 - 原告张三与被告李四劳务合同纠纷",
      "开始时间": '"$timestamp"',
      "地点": "第三审判庭",
      "来源": "法院短信",
      "优先级": "高"
    }
  }'
```

---

## 常见法院短信格式参考

### 文书送达短信

```text
【xx市人民法院】张三，您好！您有（2025）苏0981民初1234号案件文书送达，
请点击链接查收：
https://zxfw.court.gov.cn/zxfw/#/pagesAjkj/app/wssd/index?qdbh=DEMO1&sdbh=DEMO2&sdsin=DEMO3
如非本人操作请联系法院。
```

### 立案通知短信

```text
【xx市xx区人民法院】您好，您提交的立案材料已审核通过。
案号：（2025）京0105民初54321号
请及时缴纳诉讼费用。
```

### 开庭提醒短信

```text
【xx市xx区人民法院】提醒：您有（2025）苏0508民初567号案件，
定于2025年3月15日上午9:30在第3法庭开庭，请准时到庭。
```

## 故障排除

| 问题 | 解决方案 |
| --- | --- |
| 短信无法识别类型 | 展示原文，请用户确认类型后继续 |
| 案号提取失败 | 手动输入案号 |
| 当事人识别不准 | 提示用户确认/修正当事人列表 |
| 下载超时 | 检查网络连接，尝试重新执行 |
| 下载文件损坏 | 清理临时目录，重新尝试下载 |
| 桌面目录创建失败 | 检查磁盘空间和权限 |
