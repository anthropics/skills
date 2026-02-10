"""
测试 5: 完整端到端测试
模拟真实用户使用待办事项应用的完整流程
"""
from playwright.sync_api import sync_playwright
import os
from datetime import datetime

html_path = os.path.abspath('todo-app/index.html')
file_url = f'file://{html_path}'

print("=" * 60)
print("测试 5: 完整端到端测试")
print("=" * 60)

# 测试结果记录
test_results = []

def log_test_result(test_name, passed, details=""):
    """记录测试结果"""
    result = {
        'name': test_name,
        'passed': passed,
        'details': details
    }
    test_results.append(result)
    status = "✅ 通过" if passed else "❌ 失败"
    print(f"{status} - {test_name}")
    if details:
        print(f"    详情: {details}")

with sync_playwright() as p:
    browser = p.chromium.launch(headless=True)
    page = browser.new_page(viewport={'width': 1400, 'height': 900})

    os.makedirs('test-outputs', exist_ok=True)

    print("\n" + "=" * 60)
    print("开始测试场景...")
    print("=" * 60 + "\n")

    # ============ 场景 1: 页面加载 ============
    print("📂 场景 1: 页面加载")
    page.goto(file_url)
    page.wait_for_load_state('domcontentloaded')

    # 验证页面标题
    title = page.title()
    log_test_result("页面标题正确", title == "待办事项应用", f"实际标题: {title}")

    # 验证关键元素存在
    has_input = page.locator('[data-testid="todo-input"]').count() > 0
    log_test_result("输入框存在", has_input)

    has_add_btn = page.locator('[data-testid="add-button"]').count() > 0
    log_test_result("添加按钮存在", has_add_btn)

    has_list = page.locator('[data-testid="todo-list"]').count() > 0
    log_test_result("待办列表存在", has_list)

    page.screenshot(path='test-outputs/05_scenario_1_loaded.png')

    # ============ 场景 2: 添加任务 ============
    print("\n➕ 场景 2: 添加任务")

    # 添加多个任务
    tasks_to_add = [
        '完成项目文档',
        '代码审查',
        '团队会议',
        '修复 Bug #123'
    ]

    for task in tasks_to_add:
        page.fill('[data-testid="todo-input"]', task)
        page.click('[data-testid="add-button"]')
        page.wait_for_timeout(300)

    # 验证任务数量
    total_count = page.locator('[data-testid="total-count"]').inner_text()
    log_test_result("任务数量正确", total_count == str(len(tasks_to_add)),
                   f"预期: {len(tasks_to_add)}, 实际: {total_count}")

    # 验证任务在列表中
    first_task_text = page.locator('.todo-text').first.inner_text()
    log_test_result("第一个任务正确", first_task_text == tasks_to_add[0],
                   f"预期: {tasks_to_add[0]}, 实际: {first_task_text}")

    page.screenshot(path='test-outputs/05_scenario_2_added.png')

    # ============ 场景 3: 完成任务 ============
    print("\n✅ 场景 3: 完成任务")

    # 完成前两个任务
    checkboxes = page.locator('.todo-checkbox').all()
    for i in range(min(2, len(checkboxes))):
        checkboxes[i].check()
        page.wait_for_timeout(200)

    # 验证完成数量
    completed_count = page.locator('[data-testid="completed-count"]').inner_text()
    log_test_result("完成数量正确", completed_count == '2',
                   f"预期: 2, 实际: {completed_count}")

    # 验证待完成数量
    pending_count = page.locator('[data-testid="pending-count"]').inner_text()
    expected_pending = len(tasks_to_add) - 2
    log_test_result("待完成数量正确", pending_count == str(expected_pending),
                   f"预期: {expected_pending}, 实际: {pending_count}")

    page.screenshot(path='test-outputs/05_scenario_3_completed.png')

    # ============ 场景 4: 编辑功能（通过删除和重新添加）=-----------
    print("\n✏️  场景 4: 修改任务")

    # 删除一个任务
    initial_total = page.locator('[data-testid="total-count"]').inner_text()
    page.locator('.delete-btn').first.click()
    page.wait_for_timeout(300)

    new_total = page.locator('[data-testid="total-count"]').inner_text()
    log_test_result("删除成功", int(new_total) == int(initial_total) - 1,
                   f"删除前: {initial_total}, 删除后: {new_total}")

    # 添加新任务
    page.fill('[data-testid="todo-input"]', '部署到生产环境')
    page.click('[data-testid="add-button"]')
    page.wait_for_timeout(300)

    page.screenshot(path='test-outputs/05_scenario_4_modified.png')

    # ============ 场景 5: 边界情况测试 ============
    print("\n🧪 场景 5: 边界情况测试")

    # 测试空输入
    page.fill('[data-testid="todo-input"]', '')
    page.click('[data-testid="add-button"]')
    page.wait_for_timeout(300)

    total_after_empty = page.locator('[data-testid="total-count"]').inner_text()
    total_before_empty = new_total
    log_test_result("空输入不添加任务", total_after_empty == total_before_empty,
                   f"数量保持: {total_after_empty}")

    # 测试超长输入
    long_text = "A" * 200
    page.fill('[data-testid="todo-input"]', long_text)
    page.click('[data-testid="add-button"]')
    page.wait_for_timeout(300)

    long_text_added = page.locator('.todo-text').last.inner_text()
    log_test_result("超长文本可以添加", long_text == long_text_added,
                   f"长度: {len(long_text_added)}")

    page.screenshot(path='test-outputs/05_scenario_5_edge_cases.png')

    # ============ 场景 6: 清空所有 ============
    print("\n🗑️  场景 6: 清空所有任务")

    # 删除所有任务
    while page.locator('.delete-btn').count() > 0:
        page.locator('.delete-btn').first.click()
        page.wait_for_timeout(200)

    final_total = page.locator('[data-testid="total-count"]').inner_text()
    final_completed = page.locator('[data-testid="completed-count"]').inner_text()

    log_test_result("列表已清空", final_total == '0' and final_completed == '0',
                   f"总计: {final_total}, 已完成: {final_completed}")

    page.screenshot(path='test-outputs/05_scenario_6_cleared.png')

    browser.close()

    # ============ 生成测试报告 ============
    print("\n" + "=" * 60)
    print("测试报告")
    print("=" * 60)

    passed = sum(1 for r in test_results if r['passed'])
    failed = sum(1 for r in test_results if not r['passed'])
    total = len(test_results)

    print(f"\n总测试数: {total}")
    print(f"通过: {passed} ✅")
    print(f"失败: {failed} ❌")
    print(f"通过率: {passed/total*100:.1f}%")

    # 保存详细报告
    report_file = 'test-outputs/test_report.txt'
    with open(report_file, 'w', encoding='utf-8') as f:
        f.write("=" * 60 + "\n")
        f.write("端到端测试报告\n")
        f.write("=" * 60 + "\n\n")
        f.write(f"时间: {datetime.now().strftime('%Y-%m-%d %H:%M:%S')}\n")
        f.write(f"总测试数: {total}\n")
        f.write(f"通过: {passed}\n")
        f.write(f"失败: {failed}\n")
        f.write(f"通过率: {passed/total*100:.1f}%\n\n")
        f.write("=" * 60 + "\n")
        f.write("详细结果\n")
        f.write("=" * 60 + "\n\n")

        for i, result in enumerate(test_results, 1):
            status = "✅ 通过" if result['passed'] else "❌ 失败"
            f.write(f"{i}. {status} - {result['name']}\n")
            if result['details']:
                f.write(f"   详情: {result['details']}\n")
            f.write("\n")

    print(f"\n📄 详细报告已保存: {report_file}")

print("\n" + "=" * 60)
print("✅ 测试 5 完成！")
print("=" * 60)
