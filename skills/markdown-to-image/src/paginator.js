import puppeteer from 'puppeteer';
import fs from 'fs/promises';
import path from 'path';

/**
 * 分页算法：将长文本按照卡片高度智能分割
 * @param {string} text - 要分页的文本
 * @param {object} browser - Puppeteer browser 实例
 * @param {string} templatePath - 模板文件路径
 * @param {object} theme - 主题配置
 * @returns {Promise<string[]>} 分页后的文本数组
 */
export async function paginateContent(text, browser, templatePath, theme) {
  const page = await browser.newPage();
  await page.setViewport({ width: 1440, height: 2400 });

  // 读取模板
  const template = await fs.readFile(templatePath, 'utf-8');
  const html = template
    .replace('{{background}}', theme.background)
    .replace('{{textColor}}', theme.text)
    .replace('{{content}}', '');

  await page.setContent(html);

  // 最大高度（卡片 2400 - 上下 padding 各 130 = 2140，再留安全边距）
  const maxHeight = 2100;

  // 按句子分割文本（保留分隔符）
  const sentences = text.split(/([。！？\n]+)/);
  const pages = [];
  let currentPage = '';

  for (let i = 0; i < sentences.length; i++) {
    const sentence = sentences[i];
    const testContent = currentPage + sentence;

    // 更新页面内容
    await page.evaluate((content) => {
      const element = document.querySelector('.content-text');
      if (element) element.textContent = content;
    }, testContent);

    // 测量高度
    const height = await page.evaluate(() => {
      const element = document.querySelector('.content-text');
      return element ? element.scrollHeight : 0;
    });

    if (height > maxHeight && currentPage) {
      // 超出高度，保存当前页，开始新页
      pages.push(currentPage.trim());
      currentPage = sentence;
    } else {
      currentPage = testContent;
    }
  }

  // 添加最后一页
  if (currentPage.trim()) {
    pages.push(currentPage.trim());
  }

  await page.close();
  return pages;
}

/**
 * 计算标题字体大小（根据长度自动缩放）
 * @param {string} title - 标题文本
 * @returns {number} 字体大小（px）
 */
export function calculateTitleFontSize(title) {
  const length = title.length;
  if (length <= 6) return 140;
  if (length <= 10) return 120;
  if (length <= 15) return 100;
  if (length <= 25) return 80;
  return 64;
}
