"""
测试 2: 添加待办事项功能
验证用户可以添加新的待办事项
"""
from playwright.sync_api import sync_playwright
import os

html_path = os.path.abspath('todo-app/index.html')
file_url = f'file://{html_path}'

print("=" * 60)
print("测试 2: 添加待办事项")
print("=" * 60)

with sync_playwright() as p:
    browser = p.chromium.launch(headless=True)
    page = browser.new_page(viewport={'width': 1400, 'height': 900})

    page.goto(file_url)
    page.wait_for_load_state('domcontentloaded')

    # 初始截图
    os.makedirs('test-outputs', exist_ok=True)
    page.screenshot(path='test-outputs/02_before_add.png', full_page=True)

    # 获取初始统计
    initial_total = page.locator('[data-testid="total-count"]').inner_text()
    print(f"📊 初始待办数量: {initial_total}")

    # ============ 测试 1: 添加单个待办事项 ============
    print("\n➕ 测试 1: 添加单个待办事项")

    # 填写输入框
    page.fill('[data-testid="todo-input"]', '学习 Playwright')
    print("  ✍️  已填写: '学习 Playwright'")

    # 点击添加按钮
    page.click('[data-testid="add-button"]')
    print("  🖱️  已点击添加按钮")

    # 等待更新
    page.wait_for_timeout(500)

    # 验证添加成功
    new_total = page.locator('[data-testid="total-count"]').inner_text()
    print(f"  ✅ 待办数量: {initial_total} → {new_total}")

    # 截图
    page.screenshot(path='test-outputs/02_after_first_add.png', full_page=True)
    print("  📸 截图已保存")

    # ============ 测试 2: 使用回车键添加 ============
    print("\n➕ 测试 2: 使用回车键添加")

    page.fill('[data-testid="todo-input"]', '编写测试脚本')
    page.press('[data-testid="todo-input"]', 'Enter')
    print("  ⌨️  已按回车键添加: '编写测试脚本'")

    page.wait_for_timeout(500)

    # ============ 测试 3: 批量添加 ============
    print("\n➕ 测试 3: 批量添加多个待办事项")

    tasks = [
        '运行自动化测试',
        '查看测试报告',
        '修复发现的问题'
    ]

    for task in tasks:
        page.fill('[data-testid="todo-input"]', task)
        page.click('[data-testid="add-button"]')
        page.wait_for_timeout(300)
        print(f"  ✅ 已添加: {task}")

    # 最终统计
    final_total = page.locator('[data-testid="total-count"]').inner_text()
    final_completed = page.locator('[data-testid="completed-count"]').inner_text()
    final_pending = page.locator('[data-testid="pending-count"]').inner_text()

    print(f"\n📊 最终统计:")
    print(f"  总计: {final_total}")
    print(f"  已完成: {final_completed}")
    print(f"  待完成: {final_pending}")

    # 验证所有任务都显示在列表中
    todo_count = page.locator('[data-testid="todo-list"] li').count()
    print(f"\n✅ 列表中的任务数: {todo_count}")

    # 最终截图
    page.screenshot(path='test-outputs/02_after_all_adds.png', full_page=True)
    print("📸 最终截图已保存: test-outputs/02_after_all_adds.png")

    browser.close()

print("\n" + "=" * 60)
print("✅ 测试 2 完成！")
print("=" * 60)
