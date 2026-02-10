"""
运行所有测试的脚本
一键执行所有测试用例
"""
import subprocess
import os
import sys
from datetime import datetime

# 测试脚本列表
TESTS = [
    ('test_1_element_discovery.py', '元素发现测试'),
    ('test_2_add_todos.py', '添加待办事项测试'),
    ('test_3_complete_delete.py', '完成和删除测试'),
    ('test_4_console_logs.py', '控制台日志测试'),
    ('test_5_e2e.py', '端到端测试'),
]

def run_test(test_file, test_name):
    """运行单个测试"""
    print("\n" + "=" * 70)
    print(f"🧪 运行: {test_name}")
    print("=" * 70)

    try:
        result = subprocess.run(
            [sys.executable, test_file],
            capture_output=False,
            text=True
        )
        return result.returncode == 0
    except Exception as e:
        print(f"❌ 运行测试时出错: {e}")
        return False

def main():
    print("=" * 70)
    print("🚀 待办事项应用 - 自动化测试套件")
    print("=" * 70)
    print(f"⏰ 开始时间: {datetime.now().strftime('%Y-%m-%d %H:%M:%S')}")

    # 创建输出目录
    os.makedirs('test-outputs', exist_ok=True)

    # 运行所有测试
    results = []
    for test_file, test_name in TESTS:
        passed = run_test(test_file, test_name)
        results.append((test_name, passed))

    # 生成总结报告
    print("\n" + "=" * 70)
    print("📊 测试总结")
    print("=" * 70)

    passed_count = sum(1 for _, passed in results if passed)
    total_count = len(results)

    for test_name, passed in results:
        status = "✅ 通过" if passed else "❌ 失败"
        print(f"{status} - {test_name}")

    print(f"\n通过率: {passed_count}/{total_count} ({passed_count/total_count*100:.1f}%)")
    print(f"⏰ 结束时间: {datetime.now().strftime('%Y-%m-%d %H:%M:%S')}")
    print("=" * 70)

    # 保存总结到文件
    with open('test-outputs/summary.txt', 'w', encoding='utf-8') as f:
        f.write("=" * 70 + "\n")
        f.write("测试总结报告\n")
        f.write("=" * 70 + "\n\n")
        f.write(f"时间: {datetime.now().strftime('%Y-%m-%d %H:%M:%S')}\n")
        f.write(f"通过: {passed_count}/{total_count}\n")
        f.write(f"通过率: {passed_count/total_count*100:.1f}%\n\n")

        for test_name, passed in results:
            status = "✅" if passed else "❌"
            f.write(f"{status} {test_name}\n")

    print(f"\n📄 总结报告已保存: test-outputs/summary.txt")

if __name__ == '__main__':
    main()
