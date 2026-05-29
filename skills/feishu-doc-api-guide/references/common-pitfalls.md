# 飞书文档 API 常见陷阱与解决方案

基于实战经验总结的飞书文档 API 使用注意事项。

## 1. 缺少 document_revision_id 查询参数

### 问题
使用块创建 API 时返回错误：
```json
{"code": 1770001, "msg": "invalid param"}
```

### 原因
URL 缺少必需的 `document_revision_id` 查询参数。

### 解决方案
✅ **正确的 URL 格式：**
```
https://open.feishu.cn/open-apis/docx/v1/documents/{doc_id}/blocks/{block_id}/children?document_revision_id={revision_id}
```

❌ **错误的 URL 格式：**
```
https://open.feishu.cn/open-apis/docx/v1/documents/{doc_id}/blocks/{block_id}/children
```

### 获取 revision_id
```python
url = f"https://open.feishu.cn/open-apis/docx/v1/documents/{doc_id}"
response = requests.get(url, headers={"Authorization": f"Bearer {token}"})
revision_id = response.json()["data"]["document"]["revision_id"]
```

## 2. block_type 与字段不匹配

### 问题
文本块使用错误的字段名导致 API 返回 invalid param。

### 原因
飞书 API 文档示例可能不清晰，`block_type: 2` 对应的是 `text` 字段，而不是 `heading1`。

### 正确的映射关系
```python
# ✅ 正确：block_type 2 使用 text 字段
{
    "block_type": 2,
    "text": {
        "elements": [{"text_run": {"content": "内容"}}],
        "style": {}
    }
}

# ✅ 正确：block_type 3 使用 heading3 字段
{
    "block_type": 3,
    "heading3": {
        "elements": [{"text_run": {"content": "标题"}}],
        "style": {}
    }
}

# ❌ 错误：block_type 2 不能使用 heading1
{
    "block_type": 2,
    "heading1": {  # 这是错的！
        "elements": [{"text_run": {"content": "标题"}}],
        "style": {}
    }
}
```

## 3. 缺少 style 字段

### 问题
即使使用正确的 block_type 和字段名，仍然返回 invalid param。

### 原因
`text`、`bullet`、`ordered` 等对象必须包含 `style: {}` 字段，即使为空。

### 解决方案
✅ **始终包含 style 字段：**
```python
{
    "block_type": 2,
    "text": {
        "elements": [{"text_run": {"content": "内容"}}],
        "style": {}  # 必须包含，即使为空
    }
}
```

## 4. bullet 列表不稳定

### 问题
使用 `block_type: 26` (bullet) 创建项目符号列表时可能失败。

### 观察
- 在某些情况下可以成功
- 在某些情况下返回 invalid param
- 具体原因不明，可能与文档状态或其他因素有关

### 替代方案
✅ **使用文本块 + Unicode 项目符号：**
```python
# 推荐：使用文本块模拟列表
{
    "block_type": 2,
    "text": {
        "elements": [{"text_run": {"content": "• 列表项内容"}}],
        "style": {}
    }
}
```

## 5. 批量添加块的限制

### 问题
一次性添加太多块可能导致失败或超时。

### 最佳实践
- **小批量添加**：每次 5-10 个块
- **添加延迟**：批次之间延迟 0.5-1 秒
- **更新 revision_id**：每次添加后使用返回的新 revision_id

```python
revision_id = get_revision_id(token, doc_id)

for batch in batches:
    revision_id = add_blocks(token, doc_id, batch, revision_id)
    time.sleep(0.5)  # 延迟避免频率限制
```

## 6. 权限问题

### 问题
API 返回 403 或 400 错误，提示无权限。

### 检查清单
1. **应用权限范围**：确认已开通以下权限
   - `docx:document` - 查看、评论、编辑和管理云文档
   - `docx:document:readonly` - 查看云文档
   - `drive:drive` - 查看、下载、上传、编辑云空间中的文件

2. **发布应用版本**：
   - 在飞书开放平台 → 版本管理与发布
   - 创建并发布应用版本

3. **启用应用**：
   - 在飞书管理后台 → 工作台 → 应用管理
   - 确认应用已启用并设置可用范围

## 7. 文档链接格式

### 正确的文档链接格式
```
https://feishu.cn/docx/{document_id}
```

### 从 API URL 获取 document_id
API URL 中的最后一段就是 document_id：
```
https://open.feishu.cn/open-apis/docx/v1/documents/S2PmdhIhroLphZxs8GlcFfDan4u
                                                      ↑
                                                  document_id
```

## 8. 频率限制

### 限制
- **应用级别**：单个应用每秒最多 3 次调用
- **文档级别**：单个文档每秒最多 3 次并发编辑操作

### 处理方法
```python
import time

def add_with_retry(writer, doc_id, blocks, max_retries=3):
    for attempt in range(max_retries):
        try:
            return writer.add_blocks(doc_id, blocks)
        except Exception as e:
            if "429" in str(e) and attempt < max_retries - 1:
                wait_time = 2 ** attempt  # 指数退避
                time.sleep(wait_time)
            else:
                raise
```

## 快速参考

### 最小可行示例
```python
import requests

# 1. 获取 token
token_response = requests.post(
    "https://open.feishu.cn/open-apis/auth/v3/tenant_access_token/internal",
    json={"app_id": APP_ID, "app_secret": APP_SECRET}
)
token = token_response.json()["tenant_access_token"]

# 2. 获取 revision_id
doc_response = requests.get(
    f"https://open.feishu.cn/open-apis/docx/v1/documents/{DOC_ID}",
    headers={"Authorization": f"Bearer {token}"}
)
revision = doc_response.json()["data"]["document"]["revision_id"]

# 3. 添加内容（注意 URL 中的 revision_id 参数）
blocks = [{
    "block_type": 2,
    "text": {
        "elements": [{"text_run": {"content": "Hello World"}}],
        "style": {}
    }
}]

add_response = requests.post(
    f"https://open.feishu.cn/open-apis/docx/v1/documents/{DOC_ID}/blocks/{DOC_ID}/children?document_revision_id={revision}",
    headers={"Authorization": f"Bearer {token}", "Content-Type": "application/json"},
    json={"children": blocks}
)
new_revision = add_response.json()["data"]["document_revision_id"]
```

### 调试技巧

1. **检查完整的错误响应**
```python
result = response.json()
print(json.dumps(result, indent=2, ensure_ascii=False))
```

2. **验证 token 有效性**
```python
# 测试 token 是否有效
doc_url = f"https://open.feishu.cn/open-apis/docx/v1/documents/{doc_id}"
response = requests.get(doc_url, headers={"Authorization": f"Bearer {token}"})
print(response.json())
```

3. **使用浏览器查看官方文档示例**
访问飞书开放平台文档并使用浏览器开发者工具查看实际的请求格式：
```
https://open.feishu.cn/document/server-docs/docs/docs/docx-v1/document-block/create
```
