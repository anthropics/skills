#!/usr/bin/env node

import { Command } from 'commander';
import chalk from 'chalk';
import path from 'path';
import { generateCards, generateCardsFromMarkdown } from './generator.js';
import { themes } from './themes.js';

const program = new Command();

program
  .name('text-to-card')
  .description('将文本转换为精美的图片卡片')
  .version('1.0.0')
  .option('-t, --title <text>', '标题文本')
  .option('-c, --content <text>', '正文内容')
  .option('-m, --markdown <file>', 'Markdown 文件路径（支持图文混排）')
  .option('--theme <name>', `主题名称 (${Object.keys(themes).join(', ')})`, 'white')
  .option('-o, --output <dir>', '输出目录（默认 ~/Downloads/<卡片名>/）')
  .option('-n, --name <text>', '卡片名称前缀（默认从文件内容智能提取）')
  .option('--page-format <style>', '页码格式: default(01), total(01/12), brackets((1/12))', 'total')
  .action(async (options) => {
    try {
      const cardName = options.name || null;

      if (options.markdown) {
        const files = await generateCardsFromMarkdown({
          mdFile: options.markdown,
          theme: options.theme,
          outputDir: options.output || null,
          cardName: cardName,
          pageFormat: options.pageFormat,
          coverTitle: options.title || null
        });

        console.log(chalk.green('\n✨ 生成的文件:'));
        files.forEach(file => {
          console.log(chalk.gray(`   ${file}`));
        });
        console.log();
        return;
      }

      if (!options.title && !options.content) {
        console.error(chalk.red('❌ 错误: 必须提供 --title、--content 或 --markdown'));
        process.exit(1);
      }

      console.log(chalk.cyan('\n📋 配置信息:'));
      if (options.title) console.log(`   标题: ${options.title}`);
      if (options.content) console.log(`   内容: ${options.content.substring(0, 50)}${options.content.length > 50 ? '...' : ''}`);
      console.log(`   主题: ${themes[options.theme]?.name || options.theme}`);
      console.log(`   输出: ${options.output}\n`);

      const files = await generateCards({
        title: options.title,
        content: options.content,
        theme: options.theme,
        outputDir: options.output
      });

      console.log(chalk.green('\n✨ 生成的文件:'));
      files.forEach(file => {
        console.log(chalk.gray(`   ${file}`));
      });
      console.log();

    } catch (error) {
      console.error(chalk.red(`\n❌ 错误: ${error.message}\n`));
      process.exit(1);
    }
  });

program.parse();