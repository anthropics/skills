#!/usr/bin/env node
/**
 * 截图任务脚本
 */
const fs = require('fs');
const path = require('path');

async function takeScreenshot(url, outputPath, waitSeconds = 4) {
    let browser;
    try {
        // 动态导入 puppeteer
        const puppeteer = await import('puppeteer');
        
        console.log(`正在访问: ${url}`);
        
        // 启动浏览器
        browser = await puppeteer.default.launch({
            headless: 'new',
            args: [
                '--no-sandbox',
                '--disable-setuid-sandbox',
                '--disable-dev-shm-usage',
                '--disable-gpu'
            ]
        });
        
        const page = await browser.newPage();
        
        // 设置视口大小
        await page.setViewport({ width: 1920, height: 1080 });
        
        // 访问网页
        await page.goto(url, { waitUntil: 'networkidle2', timeout: 30000 });
        
        // 等待指定时间
        console.log(`等待 ${waitSeconds} 秒...`);
        await new Promise(resolve => setTimeout(resolve, waitSeconds * 1000));
        
        // 确保输出目录存在
        const outputDir = path.dirname(outputPath);
        if (!fs.existsSync(outputDir)) {
            fs.mkdirSync(outputDir, { recursive: true });
        }
        
        // 截图
        console.log(`正在截图...`);
        await page.screenshot({ path: outputPath, fullPage: true });
        
        // 检查文件大小
        const stats = fs.statSync(outputPath);
        const fileSize = stats.size;
        console.log(`✓ 截图已保存: ${outputPath}`);
        console.log(`  文件大小: ${fileSize.toLocaleString()} 字节 (${(fileSize/1024).toFixed(2)} KB)`);
        
        return { success: true, size: fileSize };
        
    } catch (error) {
        console.error(`✗ 错误: ${error.message}`);
        return { success: false, size: 0 };
    } finally {
        if (browser) {
            await browser.close();
        }
    }
}

async function main() {
    const tasks = [
        {
            url: "https://pixso.cn/designskills/top-ai-ui-design-tools-2026/",
            output: "/Users/a./Downloads/skills/industry-dynamics-trends/assets/images/2026-03-ai-for-design/08-pixso.png",
            wait: 4
        },
        {
            url: "https://www.aihub.cn/tools/uxbot/",
            output: "/Users/a./Downloads/skills/industry-dynamics-trends/assets/images/2026-03-ai-for-design/09-uxbot.png",
            wait: 4
        }
    ];
    
    const results = [];
    
    for (let i = 0; i < tasks.length; i++) {
        const task = tasks[i];
        console.log(`\n${'='.repeat(60)}`);
        console.log(`任务 ${i + 1}/${tasks.length}`);
        console.log(`${'='.repeat(60)}`);
        
        const result = await takeScreenshot(task.url, task.output, task.wait);
        
        results.push({
            task: i + 1,
            url: task.url,
            output: task.output,
            success: result.success,
            size: result.size
        });
    }
    
    // 打印总结
    console.log(`\n${'='.repeat(60)}`);
    console.log('任务完成总结');
    console.log(`${'='.repeat(60)}`);
    
    for (const result of results) {
        const status = result.success ? '✓ 成功' : '✗ 失败';
        console.log(`\n任务 ${result.task}: ${status}`);
        console.log(`  URL: ${result.url}`);
        console.log(`  文件: ${result.output}`);
        if (result.success) {
            console.log(`  大小: ${result.size.toLocaleString()} 字节 (${(result.size/1024).toFixed(2)} KB)`);
        }
    }
}

main().catch(console.error);
