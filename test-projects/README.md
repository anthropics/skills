# 🧪 Web App Testing 实战指南

## 📋 项目结构

```
test-projects/
├── todo-app/
│   └── index.html              # 待测试的 Web 应用
├── test_1_element_discovery.py  # 测试 1: 元素发现
├── test_2_add_todos.py          # 测试 2: 添加待办事项
├── test_3_complete_delete.py    # 测试 3: 完成和删除
├── test_4_console_logs.py       # 测试 4: 控制台日志
├── test_5_e2e.py                # 测试 5: 端到端测试
├── run_all_tests.py             # 运行所有测试
└── test-outputs/                # 测试输出目录（自动创建）
    ├── *.png                    # 截图
    ├── *.txt                    # 日志和报告
    └── summary.txt              # 测试总结
```

## 🚀 快速开始

### 步骤 1: 安装 Playwright

```bash
pip install playwright
playwright install chromium
```

### 步骤 2: 运行单个测试

```bash
# 测试 1: 元素发现
python test_1_element_discovery.py

# 测试 2: 添加待办事项
python test_2_add_todos.py

# 测试 3: 完成和删除
python test_3_complete_delete.py

# 测试 4: 控制台日志
python test_4_console_logs.py

# 测试 5: 端到端测试
python test_5_e2e.py
```

### 步骤 3: 运行所有测试

```bash
python run_all_tests.py
```

## 📖 测试说明

### 测试 1: 元素发现
探索页面上的所有可交互元素
- 发现输入框
- 发现按钮
- 发现列表
- 发现统计元素

**输出**: `test-outputs/01_initial_state.png`

### 测试 2: 添加待办事项
验证添加功能
- 添加单个任务
- 使用回车键添加
- 批量添加多个任务
- 验证统计更新

**输出**: `test-outputs/02_*.png`

### 测试 3: 完成和删除
验证任务操作功能
- 标记任务完成
- 取消完成状态
- 标记所有完成
- 删除单个任务
- 清空列表

**输出**: `test-outputs/03_*.png`

### 测试 4: 控制台日志
捕获浏览器控制台输出
- 监听所有控制台消息
- 分析日志类型
- 保存日志到文件

**输出**: `test-outputs/console_logs.txt`

### 测试 5: 端到端测试
完整用户流程测试
- 页面加载验证
- 添加任务
- 完成任务
- 修改任务
- 边界情况
- 生成测试报告

**输出**: `test-outputs/test_report.txt`

## 🎯 Playwright 常用命令

### 导航
```python
page.goto('url')              # 导航到 URL
page.wait_for_load_state('networkidle')  # 等待网络空闲
page.reload()                 # 重新加载
page.go_back()                # 后退
page.go_forward()             # 前进
```

### 元素选择器
```python
page.locator('button')                    # CSS 选择器
page.locator('text=Submit')               # 文本选择器
page.locator('[data-testid="submit"]')   # 属性选择器
page.get_by_text('Submit')                # 按文本获取
page.get_by_role('button', name='Submit') # 按角色获取
```

### 元素操作
```python
page.click('selector')                    # 点击
page.fill('selector', 'value')            # 填写输入
page.select_option('selector', 'value')   # 选择选项
page.check('selector')                    # 勾选复选框
page.uncheck('selector')                  # 取消勾选
```

### 等待
```python
page.wait_for_selector('selector')        # 等待元素出现
page.wait_for_timeout(1000)               # 等待固定时间
page.wait_for_load_state('domcontentloaded')  # 等待 DOM 加载
page.wait_for_load_state('networkidle')   # 等待网络空闲
```

### 信息获取
```python
page.inner_text('selector')               # 获取文本
page.get_attribute('selector', 'href')    # 获取属性
page.is_visible('selector')               # 检查可见性
page.screenshot(path='screenshot.png')    # 截图
page.content()                            # 获取 HTML
```

## 💡 最佳实践

### 1. 使用 data-testid 属性
```html
<!-- 推荐 -->
<button data-testid="submit-button">提交</button>

<!-- 不推荐（可能变化） -->
<button class="btn btn-primary">提交</button>
```

### 2. 等待策略
```python
# 好的做法
page.wait_for_selector('[data-testid="result"]')

# 避免固定等待（除非必要）
page.wait_for_timeout(5000)  # 不推荐
```

### 3. 选择器优先级
```
1. data-testid 属性（最稳定）
2. 文本选择器（text=...）
3. ID 选择器（#id）
4. CSS 类选择器（.class）
5. CSS 组合选择器（div > span.button）
```

### 4. 测试隔离
```python
# 每个测试独立运行
def test_scenario():
    browser = p.chromium.launch()
    try:
        # 测试代码
        pass
    finally:
        browser.close()  # 确保清理
```

## 🔧 调试技巧

### 1. 使用截图
```python
page.screenshot(path='debug.png', full_page=True)
```

### 2. 慢速模式
```python
browser = p.chromium.launch(
    headless=True,
    slow_mo=1000  # 每个操作延迟 1 秒
)
```

### 3. 非无头模式（调试时）
```python
browser = p.chromium.launch(headless=False)  # 可以看到浏览器
```

### 4. 查看页面内容
```python
print(page.content())  # 打印 HTML
print(page.inner_text('body'))  # 打印所有文本
```

## 📊 测试报告示例

运行 `python run_all_tests.py` 后，查看 `test-outputs/summary.txt`：

```
======================================================================
测试总结报告
======================================================================

时间: 2025-01-15 14:30:00
通过: 5/5
通过率: 100.0%

✅ 元素发现测试
✅ 添加待办事项测试
✅ 完成和删除测试
✅ 控制台日志测试
✅ 端到端测试
```

## 🎓 进阶主题

### 1. 页面对象模式 (POM)
```python
class TodoPage:
    def __init__(self, page):
        self.page = page
        self.input = page.locator('[data-testid="todo-input"]')
        self.add_btn = page.locator('[data-testid="add-button"]')
        self.list = page.locator('[data-testid="todo-list"]')

    def add_todo(self, text):
        self.input.fill(text)
        self.add_btn.click()
```

### 2. 参数化测试
```python
test_data = [
    ('任务1', '任务2'),
    ('测试A', '测试B'),
]

for task1, task2 in test_data:
    test_adding_two_tasks(task1, task2)
```

### 3. 并行测试
```python
from concurrent.futures import ThreadPoolExecutor

def run_test(test_file):
    subprocess.run(['python', test_file])

with ThreadPoolExecutor(max_workers=3) as executor:
    executor.map(run_test, TEST_FILES)
```

## 📚 参考资源

- [Playwright Python 文档](https://playwright.dev/python/)
- [选择器最佳实践](https://playwright.dev/python/docs/selectors)
- [调试指南](https://playwright.dev/python/docs/debug)

---

**提示**: 所有测试都是独立的，可以按任何顺序运行。输出文件会保存在 `test-outputs/` 目录中。
