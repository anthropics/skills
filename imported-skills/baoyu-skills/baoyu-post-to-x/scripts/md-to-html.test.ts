import assert from 'node:assert/strict';
import fs from 'node:fs/promises';
import os from 'node:os';
import path from 'node:path';
import test from 'node:test';

import { parseMarkdown } from './md-to-html.ts';

async function makeTempDir(prefix: string): Promise<string> {
  return fs.mkdtemp(path.join(os.tmpdir(), prefix));
}

test('parseMarkdown preserves mixed markdown and Obsidian wikilink image order', async (t) => {
  const root = await makeTempDir('x-md-to-html-wikilinks-');
  t.after(() => fs.rm(root, { recursive: true, force: true }));

  const articleDir = path.join(root, 'article');
  const attachmentsDir = path.join(articleDir, 'Attachments');
  const tempDir = path.join(root, 'tmp');
  await fs.mkdir(attachmentsDir, { recursive: true });
  await fs.mkdir(tempDir, { recursive: true });
  await fs.writeFile(path.join(articleDir, 'a.png'), 'a');
  await fs.writeFile(path.join(articleDir, 'b.jpg'), 'b');
  await fs.writeFile(path.join(attachmentsDir, 'c.webp'), 'c');

  const markdownPath = path.join(articleDir, 'post.md');
  await fs.writeFile(
    markdownPath,
    [
      '# Title',
      '',
      '![[a.png]]',
      '',
      '![B alt](b.jpg)',
      '',
      '![[c.webp|C alt]]',
      '',
      '![[note]]',
    ].join('\n'),
  );

  const result = await parseMarkdown(markdownPath, { tempDir });

  assert.deepEqual(
    result.contentImages.map(({ placeholder, originalPath, alt, localPath }) => ({
      placeholder,
      originalPath,
      alt,
      localPath,
    })),
    [
      {
        placeholder: 'XIMGPH_1',
        originalPath: 'a.png',
        alt: '',
        localPath: path.join(articleDir, 'a.png'),
      },
      {
        placeholder: 'XIMGPH_2',
        originalPath: 'b.jpg',
        alt: 'B alt',
        localPath: path.join(articleDir, 'b.jpg'),
      },
      {
        placeholder: 'XIMGPH_3',
        originalPath: 'c.webp',
        alt: 'C alt',
        localPath: path.join(attachmentsDir, 'c.webp'),
      },
    ],
  );
  assert.match(result.html, /XIMGPH_1[\s\S]*XIMGPH_2[\s\S]*XIMGPH_3/);
  assert.match(result.html, /!\[\[note\]\]/);
});

test('parseMarkdown resolves encoded spaces and literal percent image paths', async (t) => {
  const root = await makeTempDir('baoyu-post-to-x-images-');
  t.after(() => fs.rm(root, { recursive: true, force: true }));

  const articlePath = path.join(root, 'article.md');
  const tempDir = path.join(root, 'tmp');
  await fs.mkdir(tempDir, { recursive: true });
  await fs.writeFile(path.join(root, 'Pasted image.png'), 'png');
  await fs.writeFile(path.join(root, '100%.png'), 'png');
  await fs.writeFile(
    articlePath,
    [
      '# Title',
      '',
      '![encoded](Pasted%20image.png)',
      '',
      '![literal](100%.png)',
    ].join('\n'),
  );

  const result = await parseMarkdown(articlePath, { tempDir });

  assert.equal(result.contentImages[0]?.localPath, path.join(root, 'Pasted image.png'));
  assert.equal(result.contentImages[1]?.localPath, path.join(root, '100%.png'));
});

test('parseMarkdown renders CJK-adjacent bold and italics (no literal asterisks)', async (t) => {
  const root = await makeTempDir('x-md-to-html-cjk-bold-');
  t.after(() => fs.rm(root, { recursive: true, force: true }));

  const markdownPath = path.join(root, 'post.md');
  const tempDir = path.join(root, 'tmp');
  await fs.mkdir(tempDir, { recursive: true });
  await fs.writeFile(
    markdownPath,
    [
      '# 标题',
      '',
      '分工在变细。**国际大厂卷基础设施，中文项目卷场景落地。**这其实是生态成熟的表现。',
      '',
      '半角场景 **Top 10 里平均有 8 个** 项目。',
      '',
      '斜体 *数据来源 GitHub* 收尾。',
      '',
      '参考 **[docs][d]** 了解更多。',
      '',
      '[d]: https://example.com',
    ].join('\n'),
  );

  const result = await parseMarkdown(markdownPath, { tempDir });

  // Bold directly adjacent to CJK (closing ** followed by CJK) must render.
  assert.match(result.html, /<strong>国际大厂卷基础设施，中文项目卷场景落地。<\/strong>/);
  assert.match(result.html, /<strong>Top 10 里平均有 8 个<\/strong>/);
  // Italics.
  assert.match(result.html, /<em>数据来源 GitHub<\/em>/);
  // Reference-style links inside emphasis must render as links, not plain text.
  assert.match(result.html, /<strong><a href="https:\/\/example\.com" rel="noopener noreferrer nofollow">docs<\/a><\/strong>/);
  // No literal emphasis delimiters should leak into the output.
  assert.doesNotMatch(result.html, /\*\*/);
  assert.doesNotMatch(result.html, /(?<!\*)\*(?!\*)[^*\n]+\*(?!\*)/);
});

test('parseMarkdown does not decode author-written literal HTML entities into tags', async (t) => {
  const root = await makeTempDir('x-md-to-html-entities-');
  t.after(() => fs.rm(root, { recursive: true, force: true }));

  const markdownPath = path.join(root, 'post.md');
  const tempDir = path.join(root, 'tmp');
  await fs.mkdir(tempDir, { recursive: true });
  await fs.writeFile(
    markdownPath,
    [
      '# 标题',
      '',
      '正文中写 &#x3C;b&#x3E;literal&#x3C;/b&#x3E; 想显示字面标签。**加粗**收尾。',
      '',
      '代码里写 `&#x3C;b&#x3E;` 同样保留。',
    ].join('\n'),
  );

  const result = await parseMarkdown(markdownPath, { tempDir });

  // CJK-adjacent bold still renders.
  assert.match(result.html, /<strong>加粗<\/strong>/);
  // Author-written literal entities must NOT be decoded into real tags.
  assert.doesNotMatch(result.html, /<b>literal<\/b>/);
  assert.match(result.html, /&lt;b&gt;literal&lt;\/b&gt;/);
});
