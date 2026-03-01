"""
scheduler.py - Windows 定时任务管理器
用于注册/删除/查看盘后自动采集任务

用法：
  python scheduler.py --install     # 安装所有定时任务
  python scheduler.py --uninstall   # 删除所有定时任务
  python scheduler.py --status      # 查看任务状态
  python scheduler.py --run-now     # 立即手动运行全套采集+报告
"""
import subprocess
import sys
import os
from datetime import date

# 脚本目录（自动检测）
SCRIPTS_DIR = os.path.dirname(os.path.abspath(__file__))
PYTHON_EXE = sys.executable  # 使用当前 Python 环境

# 任务定义：(任务名, 脚本文件, 运行时间HH:MM)
TASKS = [
    ("ETF_PostMarket_MarketData",  "fetch_market_data.py",  "15:30"),
    ("ETF_PostMarket_FundFlow",    "fetch_fund_flow.py",     "16:00"),
    ("ETF_PostMarket_ETFShares",   "fetch_etf_shares.py",    "17:00"),
    ("ETF_PostMarket_GenReport",   "generate_report.py",     "18:00"),
]

# 只在工作日运行（周一到周五）
WEEKDAYS = "MON,TUE,WED,THU,FRI"


def run_command(cmd: list, description: str) -> bool:
    """执行命令并返回是否成功"""
    print(f"  → {description}...")
    result = subprocess.run(cmd, capture_output=True, text=True, shell=True)
    if result.returncode == 0:
        print(f"    ✅ 成功")
        return True
    else:
        print(f"    ❌ 失败: {result.stderr.strip()}")
        return False


def install_tasks():
    """使用 Windows 任务计划程序注册所有定时任务"""
    print("\n📅 安装 Windows 定时任务...\n")
    print(f"Python 路径: {PYTHON_EXE}")
    print(f"脚本目录: {SCRIPTS_DIR}\n")

    success_count = 0
    for task_name, script_file, run_time in TASKS:
        script_path = os.path.join(SCRIPTS_DIR, script_file)
        hour, minute = run_time.split(":")

        # schtasks 命令：创建每日工作日定时任务
        cmd = [
            "schtasks", "/Create",
            "/TN", task_name,
            "/TR", f'"{PYTHON_EXE}" "{script_path}"',
            "/SC", "WEEKLY",
            "/D", WEEKDAYS,
            "/ST", run_time,
            "/F",   # 强制覆盖已有任务
            "/RL", "HIGHEST",  # 最高权限运行
        ]

        description = f"{task_name} → 每个工作日 {run_time} 自动运行 {script_file}"
        if run_command(cmd, description):
            success_count += 1

    print(f"\n✅ 已成功安装 {success_count}/{len(TASKS)} 个定时任务")
    print("\n💡 任务说明:")
    for task_name, script_file, run_time in TASKS:
        print(f"  {run_time}  {task_name:<35} → {script_file}")

    print("\n📋 管理任务：")
    print("  查看任务: taskschd.msc （Windows 任务计划程序）")
    print("  查看状态: python scheduler.py --status")
    print("  删除任务: python scheduler.py --uninstall")


def uninstall_tasks():
    """删除所有已注册的定时任务"""
    print("\n🗑️ 删除定时任务...\n")

    for task_name, _, _ in TASKS:
        cmd = ["schtasks", "/Delete", "/TN", task_name, "/F"]
        run_command(cmd, f"删除任务: {task_name}")

    print("\n✅ 定时任务已全部删除")


def check_status():
    """查看所有定时任务状态"""
    print("\n📊 定时任务状态:\n")

    for task_name, script_file, run_time in TASKS:
        cmd = ["schtasks", "/Query", "/TN", task_name, "/FO", "LIST"]
        result = subprocess.run(cmd, capture_output=True, text=True, shell=True)

        if result.returncode == 0:
            # 解析状态
            lines = result.stdout.strip().split("\n")
            status_line = next((l for l in lines if "状态" in l or "Status" in l), "")
            next_run = next((l for l in lines if "下次运行" in l or "Next Run" in l), "")
            print(f"  ✅ {task_name}")
            print(f"     脚本: {script_file} | 计划时间: {run_time}")
            if status_line:
                print(f"     {status_line.strip()}")
            if next_run:
                print(f"     {next_run.strip()}")
        else:
            print(f"  ❌ {task_name} — 未找到或未安装")
        print()


def run_now():
    """立即运行完整数据采集+报告生成"""
    print("\n🚀 立即运行盘后数据采集套件...\n")

    today = date.today().strftime("%Y-%m-%d")
    print(f"📅 日期: {today}")
    print(f"🐍 Python: {PYTHON_EXE}")
    print(f"📂 目录: {SCRIPTS_DIR}\n")

    generate_script = os.path.join(SCRIPTS_DIR, "generate_report.py")
    result = subprocess.run(
        [PYTHON_EXE, generate_script, "--force"],
        cwd=SCRIPTS_DIR,
        text=True
    )

    if result.returncode == 0:
        print("\n✅ 全套数据采集完成！")
        print(f"📄 报告路径: {SCRIPTS_DIR}\\output\\{today}\\review_{today}.md")
    else:
        print("\n❌ 运行失败，请检查以上错误信息")


def print_help():
    print("""
📅 ETF盘后自动化调度器

用法：
  python scheduler.py --install     安装 Windows 定时任务（每个工作日自动运行）
  python scheduler.py --uninstall   删除所有定时任务
  python scheduler.py --status      查看任务状态
  python scheduler.py --run-now     立即手动运行完整采集+生成报告

定时任务计划：
  15:30  fetch_market_data.py   → 采集大盘行情/涨跌停数据
  16:00  fetch_fund_flow.py     → 采集主力资金净流向
  17:00  fetch_etf_shares.py    → 采集ETF份额变化
  18:00  generate_report.py     → 汇总生成 Markdown 复盘报告

报告输出目录：
  scripts/output/YYYY-MM-DD/review_YYYY-MM-DD.md
    """)


if __name__ == "__main__":
    args = sys.argv[1:]

    if not args or "--help" in args:
        print_help()
    elif "--install" in args:
        install_tasks()
    elif "--uninstall" in args:
        uninstall_tasks()
    elif "--status" in args:
        check_status()
    elif "--run-now" in args:
        run_now()
    else:
        print(f"❌ 未知参数: {args}")
        print_help()
