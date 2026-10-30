import { marked } from 'marked';
import path from 'path';
import fs from 'fs';
import https from 'https';
import http from 'http';
import { fileURLToPath } from 'url';

const __filename = fileURLToPath(import.meta.url);
const __dirname = path.dirname(__filename);

/**
 * 下载远程图片到临时目录
 * @param {string} url - 图片 URL
 * @returns {Promise<string|null>} - 本地文件路径，如果跳过则返回 null
 */
async function downloadImage(url) {
  const tempDir = path.join(__dirname, '..', '.temp-images');

  // 确保临时目录存在
  if (!fs.existsSync(tempDir)) {
    fs.mkdirSync(tempDir, { recursive: true });
  }

  // 检查是否为 GIF 或其他动图格式，直接跳过
  const urlLower = url.toLowerCase();
  if (urlLower.endsWith('.gif') || urlLower.includes('.gif?')) {
    console.log(`   ⏭️  跳过动图: ${url}`);
    return null;
  }

  // 生成本地文件名
  const urlObj = new URL(url);
  const filename = path.basename(urlObj.pathname) || `image-${Date.now()}.png`;
  const localPath = path.join(tempDir, filename);

  // 如果已经下载过，直接返回
  if (fs.existsSync(localPath)) {
    return localPath;
  }

  // 下载图片
  return new Promise((resolve, reject) => {
    const protocol = url.startsWith('https') ? https : http;

    protocol.get(url, (response) => {
      if (response.statusCode === 200) {
        const fileStream = fs.createWriteStream(localPath);
        response.pipe(fileStream);

        fileStream.on('finish', () => {
          fileStream.close();
          resolve(localPath);
        });

        fileStream.on('error', (err) => {
          fs.unlink(localPath, () => {});
          reject(err);
        });
      } else {
        reject(new Error(`下载图片失败: ${url} (状态码: ${response.statusCode})`));
      }
    }).on('error', (err) => {
      reject(new Error(`下载图片失败: ${url} (${err.message})`));
    });
  });
}

/**
 * 清理 Markdown 格式标记（用于直接输入文字场景）
 */
function cleanMarkdownFormatting(text) {
  return text
    // 移除加粗标记
    .replace(/\*\*(.+?)\*\*/g, '$1')
    // 移除斜体标记
    .replace(/\*(.+?)\*/g, '$1')
    .replace(/_(.+?)_/g, '$1')
    // 移除行内代码标记
    .replace(/`(.+?)`/g, '$1')
    // 移除链接，保留文字
    .replace(/\[([^\]]+)\]\([^)]+\)/g, '$1')
    .trim();
}

/**
 * 将 Markdown token 转换为 HTML（用于 Markdown 文件场景）
 */
function tokenToHtml(token) {
  switch (token.type) {
    case 'paragraph':
      return `<p>${marked.parseInline(token.text)}</p>`;

    case 'heading':
      return `<h${token.depth}>${marked.parseInline(token.text)}</h${token.depth}>`;

    case 'code':
      // 不使用语法高亮，只添加基础样式
      const escapedCode = token.text
        .replace(/&/g, '&amp;')
        .replace(/</g, '&lt;')
        .replace(/>/g, '&gt;');
      return `<pre><code class="language-${token.lang || 'plaintext'}">${escapedCode}</code></pre>`;

    case 'list':
      const tag = token.ordered ? 'ol' : 'ul';
      const items = token.items.map(item =>
        `<li>${marked.parseInline(item.text)}</li>`
      ).join('');
      return `<${tag}>${items}</${tag}>`;

    case 'blockquote':
      return `<blockquote>${marked.parse(token.text)}</blockquote>`;

    case 'table':
      // 构建表格 HTML
      let tableHtml = '<table><thead><tr>';

      // 表头
      token.header.forEach(cell => {
        tableHtml += `<th>${marked.parseInline(cell.text)}</th>`;
      });
      tableHtml += '</tr></thead><tbody>';

      // 表格行
      token.rows.forEach(row => {
        tableHtml += '<tr>';
        row.forEach(cell => {
          tableHtml += `<td>${marked.parseInline(cell.text)}</td>`;
        });
        tableHtml += '</tr>';
      });

      tableHtml += '</tbody></table>';
      return tableHtml;

    default:
      return '';
  }
}

/**
 * 解析 Markdown 文件，提取文字和图片
 * @param {string} mdFilePath - Markdown 文件路径
 * @returns {Array} - 内容块数组，每个块包含 type 和 content
 */
export async function parseMarkdown(mdFilePath) {
  const mdContent = fs.readFileSync(mdFilePath, 'utf-8');
  const mdDir = path.dirname(mdFilePath);

  // 解析 Markdown
  const tokens = marked.lexer(mdContent);
  const blocks = [];
  const seenContent = new Set(); // 用于去重

  for (const token of tokens) {
    if (token.type === 'paragraph' || token.type === 'text') {
      // 检查段落中是否包含图片
      const imageRegex = /!\[([^\]]*)\]\(([^)]+)\)/g;
      let lastIndex = 0;
      let match;
      let hasImage = false;

      while ((match = imageRegex.exec(token.text)) !== null) {
        hasImage = true;

        // 添加图片前的文字（转为 HTML）
        if (match.index > lastIndex) {
          const textBefore = token.text.substring(lastIndex, match.index).trim();
          if (textBefore && !seenContent.has(textBefore)) {
            const htmlContent = `<p>${marked.parseInline(textBefore)}</p>`;
            blocks.push({
              type: 'html',
              content: htmlContent,
              isAtomic: false
            });
            seenContent.add(textBefore);
          }
        }

        // 添加图片
        const imagePath = match[2];
        let absolutePath;

        // 判断是否为远程 URL
        if (imagePath.startsWith('http://') || imagePath.startsWith('https://')) {
          try {
            console.log(`   下载远程图片: ${imagePath}`);
            absolutePath = await downloadImage(imagePath);

            // 如果返回 null（如 GIF 被跳过），则跳过此图片
            if (!absolutePath) {
              lastIndex = imageRegex.lastIndex;
              continue;
            }
          } catch (err) {
            console.warn(`   ⚠️  跳过图片（下载失败）: ${imagePath}`);
            console.warn(`      ${err.message}`);
            lastIndex = imageRegex.lastIndex;
            continue;
          }
        } else {
          // 本地路径
          absolutePath = path.isAbsolute(imagePath)
            ? imagePath
            : path.resolve(mdDir, imagePath);

          // 检查文件是否存在
          if (!fs.existsSync(absolutePath)) {
            console.warn(`   ⚠️  跳过图片（文件不存在）: ${absolutePath}`);
            lastIndex = imageRegex.lastIndex;
            continue;
          }
        }

        if (!seenContent.has(absolutePath)) {
          blocks.push({
            type: 'image',
            content: absolutePath,
            alt: match[1]
          });
          seenContent.add(absolutePath);
        }

        lastIndex = imageRegex.lastIndex;
      }

      // 添加剩余文字或整段文字（如果没有图片）
      if (lastIndex < token.text.length || !hasImage) {
        const textContent = hasImage ? token.text.substring(lastIndex).trim() : token.text.trim();
        if (textContent && !seenContent.has(textContent)) {
          const htmlContent = `<p>${marked.parseInline(textContent)}</p>`;
          blocks.push({
            type: 'html',
            content: htmlContent,
            isAtomic: false
          });
          seenContent.add(textContent);
        }
      }
    } else if (token.type === 'heading') {
      const headingText = token.text.trim();
      if (headingText && !seenContent.has(headingText)) {
        const htmlContent = tokenToHtml(token);
        blocks.push({
          type: 'html',
          content: htmlContent,
          isAtomic: false
        });
        seenContent.add(headingText);
      }
    } else if (token.type === 'list') {
      const listKey = JSON.stringify(token.items);
      if (!seenContent.has(listKey)) {
        const listTag = token.ordered ? 'ol' : 'ul';
        const itemHtmls = token.items.map(item => `<li>${marked.parseInline(item.text)}</li>`);
        const htmlContent = `<${listTag}>${itemHtmls.join('')}</${listTag}>`;
        blocks.push({
          type: 'html',
          content: htmlContent,
          isAtomic: true,
          listTag,
          listItems: itemHtmls
        });
        seenContent.add(listKey);
      }
    } else if (token.type === 'code') {
      const codeKey = token.text;
      if (!seenContent.has(codeKey)) {
        if (token.lang === 'mermaid') {
          blocks.push({
            type: 'html',
            content: `<div class="mermaid-block"><div class="mermaid">${token.text}</div></div>`,
            isAtomic: true,
            isMermaid: true
          });
        } else {
          const htmlContent = tokenToHtml(token);
          blocks.push({
            type: 'html',
            content: htmlContent,
            isAtomic: true
          });
        }
        seenContent.add(codeKey);
      }
    } else if (token.type === 'blockquote') {
      // 引用块作为原子单元
      const quoteKey = token.text;
      if (!seenContent.has(quoteKey)) {
        const htmlContent = tokenToHtml(token);
        blocks.push({
          type: 'html',
          content: htmlContent,
          isAtomic: true
        });
        seenContent.add(quoteKey);
      }
    } else if (token.type === 'table') {
      const tableKey = JSON.stringify(token.header) + JSON.stringify(token.rows);
      if (!seenContent.has(tableKey)) {
        const htmlContent = tokenToHtml(token);
        // Store raw header/rows so the paginator can split the table across pages
        const headerCells = token.header.map(cell => marked.parseInline(cell.text));
        const rowCells = token.rows.map(row => row.map(cell => marked.parseInline(cell.text)));
        blocks.push({
          type: 'html',
          content: htmlContent,
          isAtomic: true,
          tableHeader: headerCells,
          tableRows: rowCells
        });
        seenContent.add(tableKey);
      }
    }
  }

  return blocks;
}
