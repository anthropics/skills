---
name: webapp-testing
description: 使用 Playwright 与本地 Web 应用进行交互和测试的工具包。支持前端功能验证、UI 行为调试、浏览器截图捕获和浏览器日志查看。
license: Complete terms in LICENSE.txt
---

# Web 应用测试

要测试本地 Web 应用，请编写原生 Python Playwright 脚本。

**可用辅助脚本**：
- `scripts/with_server.py` - 管理服务器生命周期（支持多服务器）

**请务必先使用 `--help` 运行脚本**以查看用法。在尝试运行脚本并确认确实需要自定义方案之前，请勿阅读源代码。这些脚本可能非常大，会占用大量上下文窗口空间。它们的设计初衷是作为黑盒脚本直接调用，而非读取到上下文窗口中。

## 决策树：选择方法

```
用户任务 → 是否为静态 HTML？
    ├─ 是 → 直接读取 HTML 文件以识别选择器
    │         ├─ 成功 → 使用选择器编写 Playwright 脚本
    │         └─ 失败/不完整 → 按动态应用处理（见下方）
    │
    └─ 否（动态 Web 应用）→ 服务器是否已运行？
        ├─ 否 → 运行：python scripts/with_server.py --help
        │        然后使用辅助脚本 + 编写简化的 Playwright 脚本
        │
        └─ 是 → 先侦察后操作：
            1. 导航并等待 networkidle
            2. 截图或检查 DOM
            3. 从渲染状态中识别选择器
            4. 使用发现的选择器执行操作
```

## 示例：使用 with_server.py

要启动服务器，先运行 `--help`，然后使用辅助脚本：

**单服务器：**
```bash
python scripts/with_server.py --server "npm run dev" --port 5173 -- python your_automation.py
```

**多服务器（例如后端 + 前端）：**
```bash
python scripts/with_server.py \
  --server "cd backend && python server.py" --port 3000 \
  --server "cd frontend && npm run dev" --port 5173 \
  -- python your_automation.py
```

编写自动化脚本时，只需包含 Playwright 逻辑（服务器由辅助脚本自动管理）：
```python
from playwright.sync_api import sync_playwright

with sync_playwright() as p:
    browser = p.chromium.launch(headless=True) # 始终以无头模式启动 chromium
    page = browser.new_page()
    page.goto('http://localhost:5173') # 服务器已运行并就绪
    page.wait_for_load_state('networkidle') # 关键：等待 JS 执行完毕
    # ... 你的自动化逻辑
    browser.close()
```

## 先侦察后操作模式

1. **检查渲染后的 DOM**：
   ```python
   page.screenshot(path='/tmp/inspect.png', full_page=True)
   content = page.content()
   page.locator('button').all()
   ```

2. **从检查结果中识别选择器**

3. **使用发现的选择器执行操作**

## 常见陷阱

❌ **不要**在动态应用中未等待 `networkidle` 就检查 DOM
✅ **应该**在检查前先等待 `page.wait_for_load_state('networkidle')`

## 最佳实践

- **将内置脚本作为黑盒使用** - 执行任务时，先考虑 `scripts/` 中是否有可用的脚本。这些脚本可靠地处理常见的复杂工作流，而不会占用上下文窗口。使用 `--help` 查看用法，然后直接调用。
- 使用 `sync_playwright()` 编写同步脚本
- 完成后务必关闭浏览器
- 使用描述性选择器：`text=`、`role=`、CSS 选择器或 ID
- 添加适当的等待：`page.wait_for_selector()` 或 `page.wait_for_timeout()`

## 参考文件

- **examples/** - 展示常见模式的示例：
  - `element_discovery.py` - 发现页面上的按钮、链接和输入框
  - `static_html_automation.py` - 使用 file:// URL 访问本地 HTML
  - `console_logging.py` - 在自动化过程中捕获控制台日志
