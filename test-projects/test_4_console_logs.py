"""
测试 4: 控制台日志捕获
捕获和分析浏览器控制台输出
"""
from playwright.sync_api import sync_playwright
import os

html_path = os.path.abspath('todo-app/index.html')
file_url = f'file://{html_path}'

print("=" * 60)
print("测试 4: 控制台日志捕获")
print("=" * 60)

console_logs = []

def handle_console_message(msg):
    """处理控制台消息"""
    log_entry = {
        'type': msg.type,
        'text': msg.text
    }
    console_logs.append(log_entry)
    print(f"🔔 [控制台] [{msg.type}] {msg.text}")

with sync_playwright() as p:
    browser = p.chromium.launch(headless=True)
    page = browser.new_page(viewport={'width': 1400, 'height': 900})

    # 注册控制台监听器
    page.on("console", handle_console_message)

    print("\n📂 正在加载页面...")
    page.goto(file_url)
    page.wait_for_load_state('domcontentloaded')
    print("✅ 页面加载完成")

    # 执行各种操作以触发控制台日志
    print("\n🔧 执行操作...")

    # 添加任务
    page.fill('[data-testid="todo-input"]', '测试控制台日志')
    page.click('[data-testid="add-button"]')
    page.wait_for_timeout(500)

    # 标记完成
    page.locator('.todo-checkbox').first.check()
    page.wait_for_timeout(500)

    # 删除任务
    page.locator('.delete-btn').first.click()
    page.wait_for_timeout(500)

    print(f"\n📊 共捕获 {len(console_logs)} 条控制台消息")

    # 分析日志
    print("\n📈 日志统计:")
    log_types = {}
    for log in console_logs:
        log_type = log['type']
        log_types[log_type] = log_types.get(log_type, 0) + 1

    for log_type, count in log_types.items():
        print(f"  {log_type}: {count} 条")

    # 保存日志到文件
    os.makedirs('test-outputs', exist_ok=True)
    log_file = 'test-outputs/console_logs.txt'

    with open(log_file, 'w', encoding='utf-8') as f:
        f.write("浏览器控制台日志\n")
        f.write("=" * 60 + "\n\n")
        for i, log in enumerate(console_logs, 1):
            f.write(f"[{i}] [{log['type']}] {log['text']}\n")

    print(f"\n💾 日志已保存到: {log_file}")

    browser.close()

print("\n" + "=" * 60)
print("✅ 测试 4 完成！")
print("=" * 60)
