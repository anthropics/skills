import puppeteer from 'puppeteer';
import fs from 'fs/promises';
import path from 'path';
import { fileURLToPath } from 'url';
import { paginateContent, calculateTitleFontSize } from './paginator.js';
import { themes } from './themes.js';
import { parseMarkdown } from './markdown-parser.js';

const __filename = fileURLToPath(import.meta.url);
const __dirname = path.dirname(__filename);

const MERMAID_JS_PATH = path.join(__dirname, '..', 'node_modules', 'mermaid', 'dist', 'mermaid.min.js');

/**
 * 生成卡片图片
 * @param {object} options - 配置选项
 * @param {string} options.title - 标题文本
 * @param {string} options.content - 正文内容
 * @param {string} options.theme - 主题名称
 * @param {string} options.outputDir - 输出目录
 * @returns {Promise<string[]>} 生成的图片路径数组
 */
export async function generateCards(options) {
  const { title, content, theme: themeName = 'white', outputDir = 'output' } = options;

  // 验证主题
  const theme = themes[themeName];
  if (!theme) {
    throw new Error(`未知主题: ${themeName}。可用主题: ${Object.keys(themes).join(', ')}`);
  }

  // 确保输出目录存在
  const outputPath = path.resolve(process.cwd(), outputDir);
  await fs.mkdir(outputPath, { recursive: true });

  // 启动浏览器
  console.log('🚀 启动浏览器...');
  const browser = await puppeteer.launch({
    headless: true,
    args: ['--no-sandbox', '--disable-setuid-sandbox']
  });

  const generatedFiles = [];

  try {
    // 生成标题卡
    if (title) {
      console.log('📝 生成标题卡...');
      const titlePath = await generateTitleCard(browser, title, theme, outputPath);
      generatedFiles.push(titlePath);
    }

    // 生成内容卡
    if (content) {
      console.log('📄 分析内容并分页...');
      const templatePath = path.join(__dirname, 'templates', 'content-card.html');
      const pages = await paginateContent(content, browser, templatePath, theme);

      console.log(`📚 共 ${pages.length} 页内容`);

      for (let i = 0; i < pages.length; i++) {
        console.log(`   生成第 ${i + 1}/${pages.length} 页...`);
        const contentPath = await generateContentCard(browser, pages[i], theme, outputPath, i + 1);
        generatedFiles.push(contentPath);
      }
    }
  } finally {
    await browser.close();
  }
}

/**
 * 生成标题卡
 */
async function generateTitleCard(browser, title, theme, outputPath, filenameBase = null) {
  const page = await browser.newPage();
  await page.setViewport({ width: 1440, height: 2400 });

  const fontSize = calculateTitleFontSize(title);

  const templatePath = path.join(__dirname, 'templates', 'title-card.html');
  const template = await fs.readFile(templatePath, 'utf-8');
  const bg = theme.tokens?.background || '#ffffff';
  const fg = theme.tokens?.textPrimary || '#000000';
  const fontFamily = theme.typography?.fontCJK || "'PingFang SC', 'Microsoft YaHei', 'Hiragino Sans GB', sans-serif";
  const html = template
    .replace('{{background}}', bg)
    .replace('{{textColor}}', fg)
    .replace('{{fontSize}}', fontSize)
    .replace('{{fontFamily}}', fontFamily)
    .replace('{{title}}', title);

  await page.setContent(html, { waitUntil: 'load', timeout: 120000 });
  await page.evaluateHandle('document.fonts.ready');

  const filename = filenameBase ? `${filenameBase}.png` : `title-${Date.now()}.png`;
  const filepath = path.join(outputPath, filename);

  await page.screenshot({
    path: filepath,
    type: 'png'
  });

  await page.close();
  return filepath;
}

/**
 * 生成内容卡
 */
async function generateContentCard(browser, content, theme, outputPath, pageNumber) {
  const page = await browser.newPage();
  await page.setViewport({ width: 1440, height: 2400 });

  // 读取并渲染模板
  const templatePath = path.join(__dirname, 'templates', 'content-card.html');
  const template = await fs.readFile(templatePath, 'utf-8');
  const html = template
    .replace('{{background}}', theme.background)
    .replace('{{textColor}}', theme.text)
    .replace('{{content}}', content);

  await page.setContent(html);

  // 截图
  const timestamp = Date.now();
  const filename = `content-${timestamp}-page${pageNumber}.png`;
  const filepath = path.join(outputPath, filename);

  await page.screenshot({
    path: filepath,
    type: 'png'
  });

  await page.close();
  return filepath;
}

function generateCardName(mdContent) {
  const headingMatch = mdContent.match(/^#{1,3}\s+(.+)/m);
  if (headingMatch) {
    return headingMatch[1].replace(/[^\u4e00-\u9fa5a-zA-Z0-9\s]/g, '').trim().slice(0, 12);
  }
  const text = mdContent.replace(/\s+/g, '').slice(0, 8);
  return text || 'card';
}

export async function generateCardsFromMarkdown(options) {
  const { mdFile, theme: themeName = 'white', outputDir = null, cardName: passedName, pageFormat = 'total', coverTitle = null } = options;

  const theme = themes[themeName];
  if (!theme) {
    throw new Error(`未知主题: ${themeName}。可用主题: ${Object.keys(themes).join(', ')}`);
  }

  console.log('📖 解析 Markdown 文件...');
  const blocks = await parseMarkdown(mdFile);
  console.log(`   发现 ${blocks.length} 个内容块`);

  let cardName = passedName;

  if (!cardName) {
    const mdContent = await fs.readFile(mdFile, 'utf8');
    cardName = generateCardName(mdContent);
    console.log(`   📝 自动命名: "${cardName}"`);
  }

  for (const block of blocks) {
    if (block.type === 'image') {
      const imageBuffer = await fs.readFile(block.content);
      block.base64 = `data:image/png;base64,${imageBuffer.toString('base64')}`;
    }
  }

  const resolvedOutputDir = outputDir || path.join(process.env.HOME, 'Downloads', cardName);
  const outputPath = path.resolve(process.cwd(), resolvedOutputDir);
  await fs.rm(outputPath, { recursive: true, force: true });
  await fs.mkdir(outputPath, { recursive: true });

  console.log('🚀 启动浏览器...');
  const browser = await puppeteer.launch({
    headless: true,
    executablePath: '/Applications/Google Chrome.app/Contents/MacOS/Google Chrome',
    args: ['--no-sandbox', '--disable-setuid-sandbox']
  });

  const generatedFiles = [];

  try {
    if (coverTitle) {
      console.log('🖼️  生成封面标题卡...');
      const coverPath = await generateTitleCard(browser, coverTitle, theme, outputPath, `${cardName}-00`);
      generatedFiles.unshift(coverPath);
    }

    console.log('🎨 生成图文混排卡片...');
    const cards = await generateMixedContentCards(browser, blocks, theme, outputPath, cardName, pageFormat);
    generatedFiles.push(...cards);

    console.log(`✅ 完成！共生成 ${generatedFiles.length} 张卡片`);
    return generatedFiles;
  } finally {
    await browser.close();
  }
}

async function generateMixedContentCards(browser, blocks, theme, outputPath, cardName, pageFormat = 'total') {
  const page = await browser.newPage();
  await page.setViewport({ width: 1440, height: 2400 });
  await page.setDefaultNavigationTimeout(120000);

  const templatePath = path.join(__dirname, 'templates', 'mixed-content-card.html');
  let template = await fs.readFile(templatePath, 'utf-8');

  const tokens = theme.tokens;
  const spacing = theme.spacing;
  const fontCJK = theme.typography?.fontCJK || "'SF Pro Text', 'PingFang SC', sans-serif";
  const fontHeading = theme.typography?.fontHeading || "'SF Pro Display', serif";

  template = template
    .replace(/{{backgroundColor}}/g, tokens.background)
    .replace(/{{textColor}}/g, tokens.textPrimary)
    .replace(/{{textPrimary}}/g, tokens.textPrimary)
    .replace(/{{textSecondary}}/g, tokens.textSecondary)
    .replace(/{{textTertiary}}/g, tokens.textTertiary)
    .replace(/{{accentColor}}/g, tokens.accent)
    .replace(/{{accentColorMuted}}/g, tokens.accentMuted)
    .replace(/{{backgroundElevated}}/g, tokens.backgroundElevated)
    .replace(/{{borderColor}}/g, tokens.border)
    .replace(/{{codeBackground}}/g, tokens.codeBackground)
    .replace(/{{padding}}/g, String(spacing.padding))
    .replace(/{{paddingSide}}/g, String(spacing.padding))
    .replace(/{{gap}}/g, String(spacing.gap))
    .replace(/{{fontSize}}/g, '38px')
    .replace(/{{lineHeight}}/g, '1.65')
    .replace(/{{paragraphGap}}/g, '28px')
    .replace(/{{codeFontSize}}/g, '32px')
    .replace(/{{codeRadius}}/g, String(theme.radius.code))
    .replace(/{{imageRadius}}/g, String(theme.radius.image))
    .replace(/{{fontFamily}}/g, fontCJK)
    .replace(/{{fontHeading}}/g, fontHeading)
    .replace(/{{pageNumber}}/g, '{{pageNumber}}');

  const hasMermaid = blocks.some(b => b.isMermaid);
  const maxHeight = 2060;
  const pageGroups = fixLonelyHeadingPages(fixOrphanHeadings(await paginateBlocks(page, template, blocks, maxHeight, hasMermaid)));
  const totalPages = pageGroups.length;

  const generatedFiles = [];
  for (let i = 0; i < pageGroups.length; i++) {
    const filepath = await renderMixedContentCard(page, template, pageGroups[i], theme, outputPath, i + 1, cardName, totalPages, pageFormat, hasMermaid);
    generatedFiles.push(filepath);
  }

  await page.close();
  return generatedFiles;
}

async function paginateBlocks(page, template, blocks, maxHeight, hasMermaid = false) {
  const emptyHtml = template
    .replace('{{content}}', '<div id="measure-root"></div>')
    .replace(/{{pageNumber}}/g, '1')
    .replace(/{{totalPages}}/g, '1')
    .replace(/{{pageFormat}}/g, 'default');
  await page.setContent(emptyHtml, { waitUntil: 'load', timeout: 120000 });
  await page.evaluateHandle('document.fonts.ready');

  if (hasMermaid) {
    await page.addScriptTag({ path: MERMAID_JS_PATH });
    await page.evaluate(() => {
      mermaid.initialize({
        startOnLoad: false,
        theme: 'neutral',
        securityLevel: 'loose',
        fontSize: 32,
        flowchart: { useMaxWidth: true, htmlLabels: true }
      });
    });
  }

  async function runMermaidAndFixSize(selector) {
    await page.evaluate(async (sel) => {
      const nodes = document.querySelectorAll(sel);
      if (!nodes.length) return;
      await mermaid.run({ nodes });

      // Content area width = card width minus horizontal padding (120px * 2)
      const contentWidth = 1200;

      nodes.forEach(el => {
        el.style.cssText = 'width: 100%; max-width: 100%; display: block;';
        const svg = el.querySelector('svg');
        if (!svg) return;

        // Read natural dimensions from viewBox (most reliable source)
        const vb = svg.viewBox && svg.viewBox.baseVal;
        const naturalW = (vb && vb.width) || parseFloat(svg.getAttribute('width')) || 800;
        const naturalH = (vb && vb.height) || parseFloat(svg.getAttribute('height')) || 400;

        const scale = contentWidth / naturalW;
        svg.removeAttribute('style');
        svg.setAttribute('width', String(contentWidth));
        svg.setAttribute('height', String(Math.ceil(naturalH * scale)));
        svg.style.display = 'block';
        svg.style.maxWidth = '100%';
      });
    }, selector);
  }

  function blockToHtml(block) {
    if (block.type === 'html') return `<div class="html-block">${block.content}</div>`;
    if (block.type === 'image') return `<div class="image-block"><img src="${block.base64}" alt="${block.alt || ''}" /></div>`;
    return '';
  }

  async function measureWithExtra(extraHtml, isMermaid = false) {
    await page.evaluate((html) => {
      const root = document.getElementById('measure-root');
      const probe = document.createElement('div');
      probe.id = '__measure-probe__';
      probe.innerHTML = html;
      root.appendChild(probe);
    }, extraHtml);
    if (isMermaid && hasMermaid) {
      await runMermaidAndFixSize('#__measure-probe__ .mermaid');
    }
    const h = await page.evaluate(() => {
      const root = document.getElementById('measure-root');
      const probe = document.getElementById('__measure-probe__');
      const h = root.scrollHeight;
      root.removeChild(probe);
      return h;
    });
    return h;
  }

  async function commitBlock(html, isMermaid = false) {
    await page.evaluate((html) => {
      const root = document.getElementById('measure-root');
      root.insertAdjacentHTML('beforeend', html);
      return root.scrollHeight;
    }, html);
    if (isMermaid && hasMermaid) {
      await runMermaidAndFixSize('.mermaid:not([data-processed])');
    }
    return page.evaluate(() => document.getElementById('measure-root').scrollHeight);
  }

  async function resetPage() {
    await page.evaluate(() => {
      document.getElementById('measure-root').innerHTML = '';
    });
  }

  const measureBlocksFn = async (blocks) => {
    const html = blocks.map(blockToHtml).join('');
    return page.evaluate((html) => {
      const root = document.getElementById('measure-root');
      const saved = root.innerHTML;
      root.innerHTML = html;
      const h = root.scrollHeight;
      root.innerHTML = saved;
      return h;
    }, html);
  };

  const pageGroups = [];
  let currentPageBlocks = [];
  let remainingBlocks = [...blocks];

  while (remainingBlocks.length > 0) {
    let block = remainingBlocks.shift();

    if (block.type === 'html' && block.isAtomic && block.content.includes('<pre>')) {
      block = await handleOversizedCodeBlock(page, template, block, maxHeight, measureBlocksFn);
    }

    const testHeight = await measureWithExtra(blockToHtml(block), block.isMermaid);

    if (testHeight <= maxHeight) {
      currentPageBlocks.push(block);
      await commitBlock(blockToHtml(block), block.isMermaid);
    } else if (currentPageBlocks.length === 0) {
      if (block.type === 'html' && !block.isAtomic) {
        const { fit, overflow } = await splitTextBlock(page, template, [], block, maxHeight, measureBlocksFn);
        if (fit) {
          pageGroups.push([fit]);
        } else {
          pageGroups.push([block]);
        }
        if (overflow) remainingBlocks.unshift(overflow);
      } else if (block.tableRows && block.tableRows.length > 1) {
        const chunks = await splitTableBlock(page, block, maxHeight, measureBlocksFn, []);
        remainingBlocks.unshift(...chunks);
      } else if (block.listItems && block.listItems.length > 1) {
        const chunks = await splitListBlock(page, block, maxHeight, measureBlocksFn, []);
        remainingBlocks.unshift(...chunks);
      } else {
        pageGroups.push([block]);
      }
      await resetPage();
    } else {
      if (block.type === 'html' && !block.isAtomic) {
        const { fit, overflow } = await splitTextBlock(page, template, currentPageBlocks, block, maxHeight, measureBlocksFn);
        if (fit) currentPageBlocks.push(fit);
        pageGroups.push([...currentPageBlocks]);
        if (overflow) remainingBlocks.unshift(overflow);
      } else if (block.tableRows && block.tableRows.length > 1) {
        // Has prior content: try to fill remaining space, then overflow to next pages
        // Pass measureWithExtra so Mermaid-rendered height is used for the first chunk measurement
        const chunks = await splitTableBlock(page, block, maxHeight, measureBlocksFn, currentPageBlocks, measureWithExtra);
        if (chunks.length === 0) {
          pageGroups.push([...currentPageBlocks]);
          currentPageBlocks = [];
          remainingBlocks.unshift(block);
        } else {
          if (chunks.length > 0) currentPageBlocks.push(chunks[0]);
          pageGroups.push([...currentPageBlocks]);
          currentPageBlocks = [];
          await resetPage();
          if (chunks.length > 1) remainingBlocks.unshift(...chunks.slice(1));
        }
      } else if (block.listItems && block.listItems.length > 1) {
        const chunks = await splitListBlock(page, block, maxHeight, measureBlocksFn, currentPageBlocks, measureWithExtra);
        if (chunks.length === 0) {
          pageGroups.push([...currentPageBlocks]);
          currentPageBlocks = [];
          remainingBlocks.unshift(block);
        } else {
          if (chunks.length > 0) currentPageBlocks.push(chunks[0]);
          pageGroups.push([...currentPageBlocks]);
          currentPageBlocks = [];
          await resetPage();
          if (chunks.length > 1) remainingBlocks.unshift(...chunks.slice(1));
        }
      } else {
        pageGroups.push([...currentPageBlocks]);
        remainingBlocks.unshift(block);
      }
      currentPageBlocks = [];
      await resetPage();
    }
  }

  if (currentPageBlocks.length > 0) {
    pageGroups.push([...currentPageBlocks]);
  }

  return pageGroups;
}

async function handleOversizedCodeBlock(page, template, block, maxHeight, measureFn) {
  const measure = measureFn || ((blocks) => measureContentHeight(page, template, blocks));
  const originalHeight = await measure([block]);

  if (originalHeight <= maxHeight) return block;

  console.warn(`⚠️  代码块过长（${originalHeight}px > ${maxHeight}px），自动缩小字体`);
  return { ...block, content: block.content.replace(/<pre>/, '<pre class="oversized">') };
}

async function splitTextBlock(page, template, currentPageBlocks, htmlBlock, maxHeight, measureFn) {
  const measure = measureFn || ((blocks) => measureContentHeight(page, template, blocks));

  if (htmlBlock.isAtomic) return { fit: null, overflow: htmlBlock };

  const textContent = htmlBlock.content.replace(/<[^>]+>/g, '');
  let low = 1, high = textContent.length, bestFit = 0;

  while (low <= high) {
    const mid = Math.floor((low + high) / 2);
    const testHtml = htmlBlock.content.replace(/(<p>)(.*?)(<\/p>)/, `$1${textContent.substring(0, mid)}$3`);
    const testHeight = await measure([...currentPageBlocks, { ...htmlBlock, content: testHtml }]);
    if (testHeight <= maxHeight) { bestFit = mid; low = mid + 1; }
    else high = mid - 1;
  }

  if (bestFit === 0) return { fit: null, overflow: htmlBlock };
  if (bestFit >= textContent.length) return { fit: htmlBlock, overflow: null };

  let splitPoint = bestFit;
  const searchRange = textContent.substring(Math.max(0, bestFit - 50), bestFit);
  const breakPoints = /[。！？\n]/g;
  let lastBreak = -1, match;
  while ((match = breakPoints.exec(searchRange)) !== null) lastBreak = match.index;
  if (lastBreak >= 0) splitPoint = Math.max(0, bestFit - 50) + lastBreak + 1;

  const fitText = textContent.substring(0, splitPoint).trim();
  const overflowText = textContent.substring(splitPoint).trim();

  return {
    fit: fitText ? { ...htmlBlock, content: htmlBlock.content.replace(/(<p>)(.*?)(<\/p>)/, `$1${fitText}$3`) } : null,
    overflow: overflowText ? { ...htmlBlock, content: htmlBlock.content.replace(/(<p>)(.*?)(<\/p>)/, `$1${overflowText}$3`) } : null
  };
}

function isHeadingBlock(block) {
  return block.type === 'html' && /^\s*<h[1-6][\s>]/.test(block.content);
}

function fixOrphanHeadings(pageGroups) {
  for (let i = 0; i < pageGroups.length - 1; i++) {
    const group = pageGroups[i];
    let trailingHeadings = 0;
    for (let j = group.length - 1; j >= 0; j--) {
      if (isHeadingBlock(group[j])) trailingHeadings++;
      else break;
    }
    // Only move headings if they're not the entire page
    if (trailingHeadings > 0 && trailingHeadings < group.length) {
      const orphans = group.splice(group.length - trailingHeadings, trailingHeadings);
      pageGroups[i + 1].unshift(...orphans);
    }
  }
  return pageGroups;
}

function fixLonelyHeadingPages(pageGroups) {
  for (let i = 0; i < pageGroups.length - 1; i++) {
    const group = pageGroups[i];
    if (group.length > 0 && group.every(b => isHeadingBlock(b))) {
      const nextGroup = pageGroups[i + 1];
      if (nextGroup.length > 0) {
        group.push(nextGroup.shift());
        if (nextGroup.length === 0) {
          pageGroups.splice(i + 1, 1);
          i--;
        }
      }
    }
  }
  return pageGroups;
}

async function splitTableBlock(page, block, maxHeight, measureFn, priorBlocks = [], measureExtra = null) {
  const { tableHeader, tableRows } = block;

  const buildTableHtml = (rows) => {
    let html = '<table><thead><tr>';
    tableHeader.forEach(cell => { html += `<th>${cell}</th>`; });
    html += '</tr></thead><tbody>';
    rows.forEach(row => {
      html += '<tr>';
      row.forEach(cell => { html += `<td>${cell}</td>`; });
      html += '</tr>';
    });
    html += '</tbody></table>';
    return html;
  };

  const makeBlock = (rows) => ({
    ...block,
    content: buildTableHtml(rows),
    tableRows: rows,
    isAtomic: true
  });

  const hasInitialPrior = priorBlocks.length > 0;
  const chunks = [];
  let i = 0;
  let currentPrior = priorBlocks;
  const TABLE_BUFFER = 150;

  while (i < tableRows.length) {
    let lo = 1, hi = tableRows.length - i, best = 0;
    const threshold = maxHeight - TABLE_BUFFER;

    while (lo <= hi) {
      const mid = Math.floor((lo + hi) / 2);
      // For the first chunk with prior content, use measureExtra so already-rendered Mermaid
      // heights are reflected correctly (measureBlocksFn replaces innerHTML, losing Mermaid SVGs)
      let h;
      if (i === 0 && hasInitialPrior && measureExtra) {
        h = await measureExtra(`<div class="html-block">${buildTableHtml(tableRows.slice(i, i + mid))}</div>`, false);
      } else {
        h = await measureFn([...currentPrior, makeBlock(tableRows.slice(i, i + mid))]);
      }
      if (h <= threshold) { best = mid; lo = mid + 1; }
      else hi = mid - 1;
    }

    if (best === 0) {
      if (i === 0 && hasInitialPrior) {
        // Nothing fits alongside prior content — signal caller to flush page first
        return [];
      }
      best = 1; // fresh page: force at least one row to avoid infinite loop
    }

    chunks.push(makeBlock(tableRows.slice(i, i + best)));
    i += best;
    currentPrior = [];
  }

  return chunks;
}

async function splitListBlock(page, block, maxHeight, measureFn, priorBlocks = [], measureExtra = null) {
  const { listTag, listItems } = block;

  const makeBlock = (items) => ({
    ...block,
    content: `<${listTag}>${items.join('')}</${listTag}>`,
    listItems: items,
    isAtomic: true
  });

  const hasInitialPrior = priorBlocks.length > 0;
  const chunks = [];
  let i = 0;
  let currentPrior = priorBlocks;
  const LIST_BUFFER = 60;

  while (i < listItems.length) {
    let lo = 1, hi = listItems.length - i, best = 0;
    const threshold = maxHeight - LIST_BUFFER;

    while (lo <= hi) {
      const mid = Math.floor((lo + hi) / 2);
      let h;
      if (i === 0 && hasInitialPrior && measureExtra) {
        h = await measureExtra(`<div class="html-block"><${listTag}>${listItems.slice(i, i + mid).join('')}</${listTag}></div>`, false);
      } else {
        h = await measureFn([...currentPrior, makeBlock(listItems.slice(i, i + mid))]);
      }
      if (h <= threshold) { best = mid; lo = mid + 1; }
      else hi = mid - 1;
    }

    if (best === 0) {
      if (i === 0 && hasInitialPrior) return [];
      best = 1;
    }

    chunks.push(makeBlock(listItems.slice(i, i + best)));
    i += best;
    currentPrior = [];
  }

  return chunks;
}

async function measureContentHeight(page, template, blocks) {
  let contentHtml = '';

  for (const block of blocks) {
    if (block.type === 'html') {
      contentHtml += `<div class="html-block">${block.content}</div>`;
    } else if (block.type === 'image') {
      contentHtml += `<div class="image-block"><img src="${block.base64}" alt="${block.alt || ''}" /></div>`;
    }
  }

  const testHtml = template.replace('{{content}}', contentHtml).replace('{{pageNumber}}', '1');
  await page.setContent(testHtml, { waitUntil: 'domcontentloaded', timeout: 120000 });

  // 获取 content-wrapper 的实际高度
  const height = await page.evaluate(() => {
    const wrapper = document.querySelector('.content-wrapper');
    return wrapper ? wrapper.scrollHeight : 0;
  });

  return height;
}

/**
 * 渲染单个图文混排卡片
 */
async function renderMixedContentCard(page, template, blocks, theme, outputPath, pageNumber, cardName = 'card', totalPages = 1, pageFormat = 'default', hasMermaid = false) {
  // 构建 HTML 内容
  let contentHtml = '';

  for (const block of blocks) {
    if (block.type === 'html') {
      contentHtml += `<div class="html-block">${block.content}</div>`;
    } else if (block.type === 'image') {
      contentHtml += `<div class="image-block"><img src="${block.base64}" alt="${block.alt || ''}" /></div>`;
    }
  }

  const html = template.replace('{{content}}', contentHtml).replace(/{{pageNumber}}/g, String(pageNumber).padStart(2, '0')).replace(/{{totalPages}}/g, String(totalPages).padStart(2, '0')).replace(/{{pageFormat}}/g, pageFormat);
  await page.setContent(html, { waitUntil: 'load', timeout: 120000 });
  await page.evaluateHandle('document.fonts.ready');

  const pagHasMermaid = hasMermaid && blocks.some(b => b.isMermaid);
  if (pagHasMermaid) {
    await page.addScriptTag({ path: MERMAID_JS_PATH });
    await page.evaluate(() => {
      mermaid.initialize({
        startOnLoad: false,
        theme: 'neutral',
        securityLevel: 'loose',
        fontSize: 32,
        flowchart: { useMaxWidth: true, htmlLabels: true }
      });
    });
    await page.evaluate(async () => {
      const nodes = document.querySelectorAll('.mermaid');
      await mermaid.run({ nodes });

      const contentWidth = 1200;
      nodes.forEach(el => {
        el.style.cssText = 'width: 100%; max-width: 100%; display: block;';
        const svg = el.querySelector('svg');
        if (!svg) return;
        const vb = svg.viewBox && svg.viewBox.baseVal;
        const naturalW = (vb && vb.width) || parseFloat(svg.getAttribute('width')) || 800;
        const naturalH = (vb && vb.height) || parseFloat(svg.getAttribute('height')) || 400;
        const scale = contentWidth / naturalW;
        svg.removeAttribute('style');
        svg.setAttribute('width', String(contentWidth));
        svg.setAttribute('height', String(Math.ceil(naturalH * scale)));
        svg.style.display = 'block';
        svg.style.maxWidth = '100%';
      });
    });
    await page.waitForFunction(
      () => [...document.querySelectorAll('.mermaid')].every(el => el.querySelector('svg')),
      { timeout: 15000 }
    );
  }

  // 截图
  const filename = `${cardName}-${String(pageNumber).padStart(2, '0')}.png`;
  const filepath = path.join(outputPath, filename);

  await page.screenshot({
    path: filepath,
    type: 'png'
  });

  return filepath;
}
