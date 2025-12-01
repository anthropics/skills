/**
 * Mermaid to Image - Mermaid構文をPNG/SVG画像に変換
 * 複数の変換方法をサポート（mermaid-cli, Kroki API）
 */

const fs = require('fs');
const path = require('path');
const { execSync, exec } = require('child_process');
const https = require('https');
const zlib = require('zlib');

// ====================
// デザインシステム定数
// ====================
const JONY_IVE_CONFIG = {
  theme: 'base',
  themeVariables: {
    primaryColor: '#F5F5F5',
    primaryTextColor: '#333333',
    primaryBorderColor: '#CCCCCC',
    secondaryColor: '#5B7B94',
    tertiaryColor: '#E0E0E0',
    lineColor: '#666666',
    textColor: '#333333',
    mainBkg: '#FFFFFF',
    nodeBorder: '#CCCCCC',
    clusterBkg: '#F5F5F5',
    clusterBorder: '#E0E0E0',
    titleColor: '#333333',
    edgeLabelBackground: '#FFFFFF',
    fontFamily: 'Meiryo, "Hiragino Sans", sans-serif',
    fontSize: '14px'
  }
};

const DEFAULT_CONFIG = {
  theme: 'default'
};

// ====================
// コマンドライン引数解析
// ====================
function parseArgs() {
  const args = process.argv.slice(2);
  const config = {
    input: null,
    output: '/mnt/user-data/outputs/diagram.png',
    format: 'png',
    theme: 'jony-ive',
    width: 800,
    height: 600,
    backgroundColor: 'white'
  };

  for (let i = 0; i < args.length; i++) {
    switch (args[i]) {
      case '--input': config.input = args[++i]; break;
      case '--output': config.output = args[++i]; break;
      case '--format': config.format = args[++i]; break;
      case '--theme': config.theme = args[++i]; break;
      case '--width': config.width = parseInt(args[++i]); break;
      case '--height': config.height = parseInt(args[++i]); break;
      case '--bg': config.backgroundColor = args[++i]; break;
    }
  }
  return config;
}

// ====================
// HTML出力（ブラウザでレンダリング）
// ====================
function generateMermaidHtml(mermaidCode, config) {
  const themeConfig = config.theme === 'jony-ive' ? JONY_IVE_CONFIG : DEFAULT_CONFIG;
  
  return `<!DOCTYPE html>
<html lang="ja">
<head>
    <meta charset="UTF-8">
    <meta name="viewport" content="width=device-width, initial-scale=1.0">
    <title>Mermaid Diagram</title>
    <script src="https://cdn.jsdelivr.net/npm/mermaid/dist/mermaid.min.js"></script>
    <style>
        body {
            font-family: 'Meiryo', 'Hiragino Sans', sans-serif;
            margin: 0;
            padding: 40px;
            background: ${config.backgroundColor || 'white'};
            display: flex;
            justify-content: center;
            align-items: flex-start;
            min-height: 100vh;
        }
        .mermaid {
            max-width: 100%;
        }
        .download-btn {
            position: fixed;
            top: 20px;
            right: 20px;
            padding: 10px 20px;
            background: #5B7B94;
            color: white;
            border: none;
            border-radius: 4px;
            cursor: pointer;
            font-family: inherit;
        }
        .download-btn:hover {
            background: #4a6a83;
        }
    </style>
</head>
<body>
    <button class="download-btn" onclick="downloadSvg()">SVGダウンロード</button>
    <div class="mermaid">
${mermaidCode}
    </div>
    <script>
        mermaid.initialize(${JSON.stringify(themeConfig)});
        
        function downloadSvg() {
            const svg = document.querySelector('.mermaid svg');
            if (svg) {
                const svgData = new XMLSerializer().serializeToString(svg);
                const blob = new Blob([svgData], {type: 'image/svg+xml'});
                const url = URL.createObjectURL(blob);
                const a = document.createElement('a');
                a.href = url;
                a.download = 'diagram.svg';
                a.click();
                URL.revokeObjectURL(url);
            }
        }
    </script>
</body>
</html>`;
}

// ====================
// Mermaid CLI変換
// ====================
async function convertWithMermaidCli(mermaidCode, outputPath, config) {
  const tempMmdFile = '/tmp/temp_diagram.mmd';
  const tempConfigFile = '/tmp/mermaid_config.json';

  // Mermaidコードをファイルに書き出し
  fs.writeFileSync(tempMmdFile, mermaidCode, 'utf-8');

  // 設定ファイル作成
  const mermaidConfig = config.theme === 'jony-ive' ? JONY_IVE_CONFIG : DEFAULT_CONFIG;
  fs.writeFileSync(tempConfigFile, JSON.stringify(mermaidConfig), 'utf-8');

  try {
    // mermaid-cliで変換
    const cmd = `mmdc -i "${tempMmdFile}" -o "${outputPath}" -c "${tempConfigFile}" -b ${config.backgroundColor}`;
    execSync(cmd, { encoding: 'utf-8', timeout: 30000 });
    
    // クリーンアップ
    fs.unlinkSync(tempMmdFile);
    fs.unlinkSync(tempConfigFile);
    
    return true;
  } catch (e) {
    console.warn('⚠️ mermaid-cli変換失敗、Kroki APIにフォールバック...');
    return false;
  }
}

// ====================
// Kroki API変換（フォールバック）
// ====================
function encodeForKroki(mermaidCode) {
  // Kroki用にBase64エンコード（deflate圧縮）
  const compressed = zlib.deflateSync(mermaidCode);
  return compressed.toString('base64')
    .replace(/\+/g, '-')
    .replace(/\//g, '_');
}

async function convertWithKroki(mermaidCode, outputPath, config) {
  return new Promise((resolve, reject) => {
    const encoded = encodeForKroki(mermaidCode);
    const format = config.format === 'png' ? 'png' : 'svg';
    const url = `https://kroki.io/mermaid/${format}/${encoded}`;

    https.get(url, (response) => {
      if (response.statusCode !== 200) {
        reject(new Error(`Kroki API error: ${response.statusCode}`));
        return;
      }

      const chunks = [];
      response.on('data', (chunk) => chunks.push(chunk));
      response.on('end', () => {
        const buffer = Buffer.concat(chunks);
        fs.writeFileSync(outputPath, buffer);
        resolve(true);
      });
    }).on('error', reject);
  });
}

// ====================
// Puppeteerベース変換（高品質）
// ====================
async function convertWithPuppeteer(mermaidCode, outputPath, config) {
  try {
    const puppeteer = require('puppeteer');
    
    const browser = await puppeteer.launch({
      headless: 'new',
      args: ['--no-sandbox', '--disable-setuid-sandbox']
    });
    
    const page = await browser.newPage();
    await page.setViewport({ width: config.width, height: config.height });

    const themeConfig = config.theme === 'jony-ive' ? JONY_IVE_CONFIG : DEFAULT_CONFIG;
    
    const html = `
    <!DOCTYPE html>
    <html>
    <head>
      <script src="https://cdn.jsdelivr.net/npm/mermaid/dist/mermaid.min.js"></script>
      <style>
        body { margin: 0; padding: 20px; background: ${config.backgroundColor}; }
        #diagram { display: flex; justify-content: center; }
      </style>
    </head>
    <body>
      <div id="diagram" class="mermaid">
${mermaidCode}
      </div>
      <script>
        mermaid.initialize(${JSON.stringify(themeConfig)});
      </script>
    </body>
    </html>`;

    await page.setContent(html);
    await page.waitForSelector('.mermaid svg', { timeout: 10000 });
    
    const element = await page.$('#diagram');
    
    if (config.format === 'svg') {
      const svgContent = await page.evaluate(() => {
        return document.querySelector('.mermaid svg').outerHTML;
      });
      fs.writeFileSync(outputPath, svgContent, 'utf-8');
    } else {
      await element.screenshot({ path: outputPath, type: 'png' });
    }
    
    await browser.close();
    return true;
  } catch (e) {
    console.warn('⚠️ Puppeteer変換失敗:', e.message);
    return false;
  }
}

// ====================
// メイン変換関数
// ====================
async function convertMermaidToImage(mermaidInput, outputPath, config) {
  let mermaidCode;

  // 入力がファイルパスかコードか判定
  if (fs.existsSync(mermaidInput)) {
    mermaidCode = fs.readFileSync(mermaidInput, 'utf-8');
    console.log(`📄 Mermaidファイル読み込み: ${mermaidInput}`);
  } else {
    mermaidCode = mermaidInput;
  }

  console.log('🎨 Mermaid → 画像変換中...');
  console.log(`   出力形式: ${config.format.toUpperCase()}`);
  console.log(`   テーマ: ${config.theme}`);

  // 出力ディレクトリ確保
  const outputDir = path.dirname(outputPath);
  if (!fs.existsSync(outputDir)) {
    fs.mkdirSync(outputDir, { recursive: true });
  }

  // HTML形式の場合は直接出力
  if (config.format === 'html') {
    const html = generateMermaidHtml(mermaidCode, config);
    fs.writeFileSync(outputPath, html, 'utf-8');
    console.log(`✅ HTML出力完了: ${outputPath}`);
    return outputPath;
  }

  // 変換方法を順番に試行
  let success = false;

  // 1. mermaid-cli
  success = await convertWithMermaidCli(mermaidCode, outputPath, config);
  
  // 2. Kroki API（フォールバック）
  if (!success) {
    try {
      await convertWithKroki(mermaidCode, outputPath, config);
      success = true;
      console.log('✅ Kroki APIで変換成功');
    } catch (e) {
      console.warn('⚠️ Kroki API変換失敗:', e.message);
    }
  }

  // 3. Puppeteer（最終手段）
  if (!success) {
    success = await convertWithPuppeteer(mermaidCode, outputPath, config);
  }

  // 4. HTML出力（最終フォールバック）
  if (!success) {
    console.log('📝 PNG/SVG変換失敗、HTML形式で出力します...');
    const htmlPath = outputPath.replace(/\.(png|svg)$/, '.html');
    const html = generateMermaidHtml(mermaidCode, config);
    fs.writeFileSync(htmlPath, html, 'utf-8');
    console.log(`✅ HTML出力完了: ${htmlPath}`);
    console.log('   ブラウザで開くと図が表示されます。SVGダウンロードボタンも利用可能です。');
    return htmlPath;
  }

  if (success) {
    console.log(`✅ 変換完了: ${outputPath}`);
    return outputPath;
  }
}

// ====================
// CLI実行
// ====================
if (require.main === module) {
  const config = parseArgs();

  if (!config.input) {
    console.log('使用方法: node mermaid_to_image.js --input <ファイルまたはコード> [オプション]');
    console.log('');
    console.log('オプション:');
    console.log('  --input <file|code>  Mermaidファイルまたはコード');
    console.log('  --output <file>      出力ファイル（デフォルト: diagram.png）');
    console.log('  --format <png|svg>   出力形式（デフォルト: png）');
    console.log('  --theme <name>       テーマ（default/jony-ive）');
    console.log('  --width <px>         幅（デフォルト: 800）');
    console.log('  --height <px>        高さ（デフォルト: 600）');
    console.log('  --bg <color>         背景色（デフォルト: white）');
    process.exit(1);
  }

  convertMermaidToImage(config.input, config.output, config)
    .then(() => console.log('完了'))
    .catch(err => {
      console.error('❌ エラー:', err.message);
      process.exit(1);
    });
}

module.exports = { convertMermaidToImage, generateMermaidHtml, JONY_IVE_CONFIG };
