"""
测试 1: 元素发现
探索待办事项应用的所有可交互元素
"""
from playwright.sync_api import sync_playwright
import os

# 获取 HTML 文件路径
html_path = os.path.abspath('todo-app/index.html')
file_url = f'file://{html_path}'

print("=" * 60)
print("测试 1: 元素发现")
print("=" * 60)
print(f"目标: {file_url}\n")

with sync_playwright() as p:
    # 启动浏览器
    browser = p.chromium.launch(headless=True)
    page = browser.new_page(viewport={'width': 1400, 'height': 900})

    # 导航到页面
    print("📂 正在加载页面...")
    page.goto(file_url)

    # 等待页面完全加载
    page.wait_for_load_state('domcontentloaded')
    print("✅ 页面加载完成\n")

    # ============ 发现输入框 ============
    print("🔍 发现输入框:")
    inputs = page.locator('input').all()
    for i, inp in enumerate(inputs):
        inp_type = inp.get_attribute('type') or 'text'
        inp_id = inp.get_attribute('id') or inp.get_attribute('data-testid') or '[unnamed]'
        placeholder = inp.get_attribute('placeholder') or ''
        is_visible = inp.is_visible()
        print(f"  [{i}] 类型={inp_type}, ID={inp_id}, 占位符='{placeholder}', 可见={is_visible}")

    # ============ 发现按钮 ============
    print("\n🔍 发现按钮:")
    buttons = page.locator('button').all()
    for i, btn in enumerate(buttons):
        text = btn.inner_text().strip()
        test_id = btn.get_attribute('data-testid') or '[none]'
        is_visible = btn.is_visible()
        print(f"  [{i}] 文本='{text}', data-testid={test_id}, 可见={is_visible}")

    # ============ 发现列表 ============
    print("\n🔍 发现列表:")
    todo_list = page.locator('[data-testid="todo-list"]')
    count = todo_list.locator('li').count()
    print(f"  当前待办事项数量: {count}")

    # ============ 发现统计元素 ============
    print("\n🔍 发现统计元素:")
    stats = page.locator('[class^="stat-value"]').all()
    for stat in stats:
        test_id = stat.get_attribute('data-testid') or '[none]'
        text = stat.inner_text()
        print(f"  - {test_id}: {text}")

    # ============ 截图 ============
    screenshot_path = 'test-outputs/01_initial_state.png'
    os.makedirs('test-outputs', exist_ok=True)
    page.screenshot(path=screenshot_path, full_page=True)
    print(f"\n📸 初始状态截图已保存: {screenshot_path}")

    # ============ 获取页面内容 ============
    print("\n📄 页面内容预览:")
    content = page.content()
    print(f"  HTML 大小: {len(content)} 字符")

    browser.close()

print("\n" + "=" * 60)
print("✅ 测试 1 完成！")
print("=" * 60)
