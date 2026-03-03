#!/usr/bin/env python3
"""
截图任务脚本
"""
import time
import base64
from pathlib import Path
from selenium import webdriver
from selenium.webdriver.chrome.options import Options
from selenium.webdriver.chrome.service import Service

def take_screenshot(url, output_path, wait_seconds=4):
    """
    访问URL并截图保存
    
    Args:
        url: 目标网址
        output_path: 输出文件路径
        wait_seconds: 等待页面加载的秒数
    """
    # 配置 Chrome 选项
    chrome_options = Options()
    chrome_options.add_argument('--headless')
    chrome_options.add_argument('--no-sandbox')
    chrome_options.add_argument('--disable-dev-shm-usage')
    chrome_options.add_argument('--window-size=1920,1080')
    chrome_options.add_argument('--disable-gpu')
    chrome_options.add_argument('--disable-blink-features=AutomationControlled')
    chrome_options.add_argument('user-agent=Mozilla/5.0 (Macintosh; Intel Mac OS X 10_15_7) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/120.0.0.0 Safari/537.36')
    
    driver = None
    try:
        # 初始化浏览器
        driver = webdriver.Chrome(options=chrome_options)
        
        # 访问网页
        print(f"正在访问: {url}")
        driver.get(url)
        
        # 等待页面加载
        print(f"等待 {wait_seconds} 秒...")
        time.sleep(wait_seconds)
        
        # 确保输出目录存在
        output_file = Path(output_path)
        output_file.parent.mkdir(parents=True, exist_ok=True)
        
        # 截图
        print(f"正在截图...")
        driver.save_screenshot(str(output_file))
        
        # 检查文件大小
        file_size = output_file.stat().st_size
        print(f"✓ 截图已保存: {output_path}")
        print(f"  文件大小: {file_size:,} 字节 ({file_size/1024:.2f} KB)")
        
        return True, file_size
        
    except Exception as e:
        print(f"✗ 错误: {e}")
        return False, 0
        
    finally:
        if driver:
            driver.quit()

def main():
    """主函数"""
    tasks = [
        {
            "url": "https://pixso.cn/designskills/top-ai-ui-design-tools-2026/",
            "output": "/Users/a./Downloads/skills/industry-dynamics-trends/assets/images/2026-03-ai-for-design/08-pixso.png",
            "wait": 4
        },
        {
            "url": "https://www.aihub.cn/tools/uxbot/",
            "output": "/Users/a./Downloads/skills/industry-dynamics-trends/assets/images/2026-03-ai-for-design/09-uxbot.png",
            "wait": 4
        }
    ]
    
    results = []
    
    for i, task in enumerate(tasks, 1):
        print(f"\n{'='*60}")
        print(f"任务 {i}/{len(tasks)}")
        print(f"{'='*60}")
        
        success, size = take_screenshot(
            task["url"],
            task["output"],
            task["wait"]
        )
        
        results.append({
            "task": i,
            "url": task["url"],
            "output": task["output"],
            "success": success,
            "size": size
        })
    
    # 打印总结
    print(f"\n{'='*60}")
    print("任务完成总结")
    print(f"{'='*60}")
    
    for result in results:
        status = "✓ 成功" if result["success"] else "✗ 失败"
        print(f"\n任务 {result['task']}: {status}")
        print(f"  URL: {result['url']}")
        print(f"  文件: {result['output']}")
        if result["success"]:
            print(f"  大小: {result['size']:,} 字节 ({result['size']/1024:.2f} KB)")

if __name__ == "__main__":
    main()
