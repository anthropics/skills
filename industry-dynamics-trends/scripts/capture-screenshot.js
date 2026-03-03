const puppeteer = require('puppeteer');
const fs = require('fs');
const path = require('path');

async function captureScreenshot() {
    console.log('启动浏览器...');
    const browser = await puppeteer.launch({
        headless: true,
        args: ['--no-sandbox', '--disable-setuid-sandbox']
    });
    
    const page = await browser.newPage();
    await page.setViewport({ width: 1920, height: 1080 });
    
    console.log('导航到 https://konva.app/...');
    await page.goto('https://konva.app/', { 
        waitUntil: 'networkidle2',
        timeout: 30000 
    });
    
    console.log('等待 3 秒让页面完全加载...');
    await new Promise(resolve => setTimeout(resolve, 3000));
    
    const outputPath = path.join(__dirname, '..', 'assets', 'images', '2026-03-ai-for-design', '07-konva.png');
    const outputDir = path.dirname(outputPath);
    
    // 确保目录存在
    if (!fs.existsSync(outputDir)) {
        fs.mkdirSync(outputDir, { recursive: true });
        console.log(`创建目录: ${outputDir}`);
    }
    
    console.log(`截取页面截图并保存到 ${outputPath}...`);
    await page.screenshot({ 
        path: outputPath,
        fullPage: false 
    });
    
    await browser.close();
    
    // 检查文件并获取大小
    if (fs.existsSync(outputPath)) {
        const stats = fs.statSync(outputPath);
        console.log('\n✓ 截图已成功保存！');
        console.log(`文件路径: ${outputPath}`);
        console.log(`文件大小: ${stats.size.toLocaleString()} 字节 (${(stats.size/1024).toFixed(2)} KB)`);
    } else {
        console.log('✗ 文件保存失败');
        process.exit(1);
    }
}

captureScreenshot().catch(error => {
    console.error('错误:', error);
    process.exit(1);
});
