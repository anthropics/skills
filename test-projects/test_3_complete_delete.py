"""
测试 3: 完成和删除待办事项
验证用户可以标记完成和删除待办事项
"""
from playwright.sync_api import sync_playwright
import os

html_path = os.path.abspath('todo-app/index.html')
file_url = f'file://{html_path}'

print("=" * 60)
print("测试 3: 完成和删除待办事项")
print("=" * 60)

with sync_playwright() as p:
    browser = p.chromium.launch(headless=True)
    page = browser.new_page(viewport={'width': 1400, 'height': 900})

    page.goto(file_url)
    page.wait_for_load_state('domcontentloaded')

    os.makedirs('test-outputs', exist_ok=True)

    # ============ 准备测试数据 ============
    print("\n📝 准备测试数据...")

    test_tasks = ['任务A', '任务B', '任务C']
    for task in test_tasks:
        page.fill('[data-testid="todo-input"]', task)
        page.click('[data-testid="add-button"]')
        page.wait_for_timeout(200)

    print(f"✅ 已添加 {len(test_tasks)} 个测试任务")

    page.screenshot(path='test-outputs/03_initial_tasks.png', full_page=True)
    print("📸 初始状态截图已保存")

    # ============ 测试 1: 标记完成 ============
    print("\n✅ 测试 1: 标记任务为完成")

    # 获取第一个复选框
    first_checkbox = page.locator('.todo-checkbox').first
    first_checkbox.check()
    print("  ☑️  已勾选第一个任务")

    page.wait_for_timeout(500)

    # 验证统计更新
    completed_count = page.locator('[data-testid="completed-count"]').inner_text()
    print(f"  📊 已完成数量: {completed_count}")

    page.screenshot(path='test-outputs/03_after_complete.png', full_page=True)
    print("  📸 截图已保存")

    # ============ 测试 2: 取消完成 ============
    print("\n↩️  测试 2: 取消完成状态")

    first_checkbox.uncheck()
    print("  ☐ 已取消勾选")

    page.wait_for_timeout(500)

    completed_count = page.locator('[data-testid="completed-count"]').inner_text()
    print(f"  📊 已完成数量: {completed_count}")

    # ============ 测试 3: 标记所有任务为完成 ============
    print("\n✅ 测试 3: 标记所有任务为完成")

    checkboxes = page.locator('.todo-checkbox').all()
    print(f"  找到 {len(checkboxes)} 个复选框")

    for i, checkbox in enumerate(checkboxes):
        checkbox.check()
        print(f"  ☑️  已勾选任务 {i + 1}")
        page.wait_for_timeout(200)

    page.screenshot(path='test-outputs/03_all_completed.png', full_page=True)
    print("  📸 全部完成截图已保存")

    # 验证统计
    final_completed = page.locator('[data-testid="completed-count"]').inner_text()
    final_pending = page.locator('[data-testid="pending-count"]').inner_text()
    print(f"  📊 已完成: {final_completed}, 待完成: {final_pending}")

    # ============ 测试 4: 删除任务 ============
    print("\n🗑️  测试 4: 删除任务")

    # 获取删除前的数量
    before_count = page.locator('[data-testid="todo-list"] li').count()
    print(f"  删除前任务数: {before_count}")

    # 点击第一个删除按钮
    first_delete_btn = page.locator('.delete-btn').first
    first_delete_btn.click()
    print("  🖱️  已点击第一个删除按钮")

    page.wait_for_timeout(500)

    # 验证删除成功
    after_count = page.locator('[data-testid="todo-list"] li').count()
    print(f"  删除后任务数: {after_count}")
    print(f"  ✅ 成功删除 1 个任务")

    page.screenshot(path='test-outputs/03_after_delete.png', full_page=True)
    print("  📸 删除后截图已保存")

    # ============ 测试 5: 删除所有任务 ============
    print("\n🗑️  测试 5: 删除所有任务")

    delete_buttons = page.locator('.delete-btn').all()
    print(f"  找到 {len(delete_buttons)} 个删除按钮")

    for i in range(len(delete_buttons)):
        # 重新获取删除按钮（因为 DOM 会变化）
        current_btn = page.locator('.delete-btn').first
        current_btn.click()
        page.wait_for_timeout(200)
        remaining = page.locator('[data-testid="todo-list"] li').count()
        print(f"  删除任务 {i + 1}, 剩余 {remaining} 个")

    # 验证列表为空
    final_count = page.locator('[data-testid="todo-list"] li').count()
    print(f"\n  ✅ 列表为空: {final_count == 0}")

    page.screenshot(path='test-outputs/03_empty_list.png', full_page=True)
    print("  📸 空列表截图已保存")

    browser.close()

print("\n" + "=" * 60)
print("✅ 测试 3 完成！")
print("=" * 60)
