/**
 * Generate Diagram - テキスト説明からMermaid図を生成
 * テキスト解析 + Mermaid構文生成 + 画像変換
 */

const fs = require('fs');
const path = require('path');
const { convertMermaidToImage, JONY_IVE_CONFIG } = require('./mermaid_to_image.js');

// ====================
// コマンドライン引数解析
// ====================
function parseArgs() {
  const args = process.argv.slice(2);
  const config = {
    type: 'flowchart',
    input: null,
    output: '/mnt/user-data/outputs/diagram.png',
    format: 'png',
    direction: 'TD',
    theme: 'jony-ive',
    title: '',
    mermaidOnly: false  // Mermaidコードのみ出力
  };

  for (let i = 0; i < args.length; i++) {
    switch (args[i]) {
      case '--type': config.type = args[++i]; break;
      case '--input': config.input = args[++i]; break;
      case '--output': config.output = args[++i]; break;
      case '--format': config.format = args[++i]; break;
      case '--direction': config.direction = args[++i]; break;
      case '--theme': config.theme = args[++i]; break;
      case '--title': config.title = args[++i]; break;
      case '--mermaid-only': config.mermaidOnly = true; break;
    }
  }
  return config;
}

// ====================
// テキスト解析・パターンマッチング
// ====================

/**
 * 矢印パターンを検出して分割
 */
function parseArrowSequence(text) {
  // 様々な矢印パターンに対応
  const arrowPatterns = [
    /\s*[→➡︎➔⇒]\s*/g,
    /\s*->\s*/g,
    /\s*=>\s*/g,
    /\s*-->\s*/g
  ];

  let steps = [text];
  for (const pattern of arrowPatterns) {
    if (pattern.test(text)) {
      steps = text.split(pattern).map(s => s.trim()).filter(s => s);
      break;
    }
  }
  return steps;
}

/**
 * 箇条書きを検出してステップ抽出
 */
function parseBulletList(text) {
  const lines = text.split('\n');
  const steps = [];
  
  for (const line of lines) {
    const trimmed = line.trim();
    // 箇条書きパターン
    const bulletMatch = trimmed.match(/^[\-\*•・]\s*(.+)$/);
    const numMatch = trimmed.match(/^(\d+)[\.）\)]\s*(.+)$/);
    
    if (bulletMatch) {
      steps.push(bulletMatch[1]);
    } else if (numMatch) {
      steps.push(numMatch[2]);
    } else if (trimmed && !trimmed.includes(':')) {
      steps.push(trimmed);
    }
  }
  
  return steps;
}

/**
 * 条件分岐を検出
 */
function detectConditionals(text) {
  const conditionals = [];
  
  // 条件パターン
  const patterns = [
    /(.+)の場合[はに](.+)/g,
    /もし(.+)なら(.+)/g,
    /(.+)かどうか/g,
    /(.+)[?？](.+):(.+)/g,  // 三項演算子風
  ];

  for (const pattern of patterns) {
    let match;
    while ((match = pattern.exec(text)) !== null) {
      conditionals.push({
        condition: match[1],
        yes: match[2] || 'Yes',
        no: match[3] || 'No'
      });
    }
  }

  return conditionals;
}

/**
 * スイムレーン（部門）を検出
 */
function detectSwimlanes(text) {
  const swimlanes = {};
  const lines = text.split('\n');
  
  // パターン: 「部門名: 処理」または「部門名が処理」
  for (const line of lines) {
    const colonMatch = line.match(/^(.+?)[：:]\s*(.+)$/);
    const gaMatch = line.match(/^(.+?)が\s*(.+)$/);
    
    if (colonMatch) {
      const [, dept, actionsStr] = colonMatch;
      if (!swimlanes[dept]) swimlanes[dept] = [];
      // カンマ区切りで複数アクションを分割
      const actions = actionsStr.split(/[,、→]/).map(a => a.trim()).filter(a => a);
      swimlanes[dept].push(...actions);
    } else if (gaMatch) {
      const [, dept, actionsStr] = gaMatch;
      if (!swimlanes[dept]) swimlanes[dept] = [];
      const actions = actionsStr.split(/[,、→]/).map(a => a.trim()).filter(a => a);
      swimlanes[dept].push(...actions);
    }
  }

  return Object.keys(swimlanes).length > 1 ? swimlanes : null;
}

// ====================
// Mermaid構文生成
// ====================

/**
 * フローチャート生成
 */
function generateFlowchart(steps, config) {
  const direction = config.direction || 'TD';
  let mermaid = `flowchart ${direction}\n`;
  
  // ノードID生成用
  const nodeId = (i) => String.fromCharCode(65 + i); // A, B, C...
  
  for (let i = 0; i < steps.length; i++) {
    const step = steps[i].trim();
    const id = nodeId(i);
    
    // 開始・終了判定
    const isStart = i === 0;
    const isEnd = i === steps.length - 1;
    
    // 条件判断キーワード
    const isDecision = /判断|確認|チェック|可否|[?？]/.test(step);
    
    // ノード形状決定
    let nodeShape;
    if (isStart || isEnd) {
      nodeShape = `([${step}])`;  // 角丸（開始/終了）
    } else if (isDecision) {
      nodeShape = `{${step}}`;    // ひし形（判断）
    } else {
      nodeShape = `[${step}]`;    // 四角形（処理）
    }
    
    mermaid += `    ${id}${nodeShape}\n`;
  }
  
  // 接続線
  mermaid += '\n';
  for (let i = 0; i < steps.length - 1; i++) {
    mermaid += `    ${nodeId(i)} --> ${nodeId(i + 1)}\n`;
  }
  
  // スタイル適用
  mermaid += '\n';
  mermaid += `    classDef default fill:#fff,stroke:#CCC,stroke-width:1px\n`;
  mermaid += `    classDef startEnd fill:#5B7B94,color:#fff,stroke:#333\n`;
  mermaid += `    classDef decision fill:#F5F5F5,stroke:#666,stroke-width:2px\n`;
  
  // スタイル割り当て
  const startEndNodes = [nodeId(0), nodeId(steps.length - 1)].join(',');
  mermaid += `    class ${startEndNodes} startEnd\n`;
  
  return mermaid;
}

/**
 * シーケンス図生成
 */
function generateSequence(participants, interactions) {
  let mermaid = 'sequenceDiagram\n';
  
  // 参加者定義
  for (const p of participants) {
    const alias = p.alias || p.name.charAt(0).toUpperCase();
    mermaid += `    participant ${alias} as ${p.name}\n`;
  }
  
  mermaid += '\n';
  
  // インタラクション
  for (const interaction of interactions) {
    const arrow = interaction.async ? '-->>' : '->>';
    mermaid += `    ${interaction.from}${arrow}${interaction.to}: ${interaction.message}\n`;
  }
  
  return mermaid;
}

/**
 * スイムレーン図生成
 */
function generateSwimlane(swimlanes, config) {
  // スイムレーンは横方向（LR）が見やすい
  const direction = 'LR';
  let mermaid = `flowchart ${direction}\n`;
  
  let nodeCounter = 0;
  const nodeId = () => `N${nodeCounter++}`;
  const deptNodes = {};
  
  // 各部門のサブグラフ
  for (const [dept, actions] of Object.entries(swimlanes)) {
    mermaid += `    subgraph ${dept}\n`;
    deptNodes[dept] = [];
    
    for (const action of actions) {
      const id = nodeId();
      mermaid += `        ${id}[${action}]\n`;
      deptNodes[dept].push(id);
    }
    
    // 部門内の接続
    const nodes = deptNodes[dept];
    for (let i = 0; i < nodes.length - 1; i++) {
      mermaid += `        ${nodes[i]} --> ${nodes[i + 1]}\n`;
    }
    
    mermaid += `    end\n`;
  }
  
  // 部門間の接続（最後のノード → 次の部門の最初のノード）
  mermaid += '\n';
  const depts = Object.keys(swimlanes);
  for (let i = 0; i < depts.length - 1; i++) {
    const currentDeptNodes = deptNodes[depts[i]];
    const nextDeptNodes = deptNodes[depts[i + 1]];
    if (currentDeptNodes.length > 0 && nextDeptNodes.length > 0) {
      mermaid += `    ${currentDeptNodes[currentDeptNodes.length - 1]} --> ${nextDeptNodes[0]}\n`;
    }
  }

  // スタイル
  mermaid += '\n    classDef default fill:#fff,stroke:#CCC,stroke-width:1px\n';
  
  return mermaid;
}

/**
 * 状態遷移図生成
 */
function generateStateDiagram(states, transitions) {
  let mermaid = 'stateDiagram-v2\n';
  
  // 状態定義と遷移
  for (const transition of transitions) {
    if (transition.from === 'start') {
      mermaid += `    [*] --> ${transition.to}\n`;
    } else if (transition.to === 'end') {
      mermaid += `    ${transition.from} --> [*]\n`;
    } else {
      const label = transition.label ? `: ${transition.label}` : '';
      mermaid += `    ${transition.from} --> ${transition.to}${label}\n`;
    }
  }
  
  return mermaid;
}

// ====================
// テキストから自動判定・生成
// ====================

function autoGenerateMermaid(text, config) {
  console.log('🔍 テキスト解析中...');
  
  // 1. スイムレーン検出
  const swimlanes = detectSwimlanes(text);
  if (swimlanes && config.type === 'auto' || config.type === 'swimlane') {
    console.log('   → スイムレーン図として生成');
    return generateSwimlane(swimlanes, config);
  }
  
  // 2. 矢印シーケンス検出
  const arrowSteps = parseArrowSequence(text);
  if (arrowSteps.length > 1) {
    console.log(`   → フローチャートとして生成（${arrowSteps.length}ステップ）`);
    return generateFlowchart(arrowSteps, config);
  }
  
  // 3. 箇条書き検出
  const bulletSteps = parseBulletList(text);
  if (bulletSteps.length > 1) {
    console.log(`   → フローチャートとして生成（${bulletSteps.length}ステップ）`);
    return generateFlowchart(bulletSteps, config);
  }
  
  // 4. 単純なテキスト（カンマ区切り等）
  const simpleSteps = text.split(/[,、]/g).map(s => s.trim()).filter(s => s);
  if (simpleSteps.length > 1) {
    console.log(`   → フローチャートとして生成（${simpleSteps.length}ステップ）`);
    return generateFlowchart(simpleSteps, config);
  }
  
  // フォールバック：単一ノード
  console.log('   → 単一ノードとして生成');
  return `flowchart ${config.direction || 'TD'}\n    A[${text}]\n`;
}

// ====================
// メイン処理
// ====================

async function main() {
  const config = parseArgs();

  if (!config.input) {
    console.log('使用方法: node generate_diagram.js --input <テキストまたはファイル> [オプション]');
    console.log('');
    console.log('オプション:');
    console.log('  --type <type>        図表タイプ（flowchart/sequence/swimlane/state/auto）');
    console.log('  --input <text|file>  テキスト説明またはファイルパス');
    console.log('  --output <file>      出力ファイル');
    console.log('  --format <png|svg>   出力形式');
    console.log('  --direction <dir>    フロー方向（TD/LR/RL/BT）');
    console.log('  --theme <theme>      テーマ（default/jony-ive）');
    console.log('  --mermaid-only       Mermaidコードのみ出力（画像生成しない）');
    process.exit(1);
  }

  console.log('📊 ダイアグラム生成を開始...');
  console.log(`   タイプ: ${config.type}`);

  // 入力テキスト取得
  let inputText;
  if (fs.existsSync(config.input)) {
    inputText = fs.readFileSync(config.input, 'utf-8');
    console.log(`   入力ファイル: ${config.input}`);
  } else {
    inputText = config.input;
    console.log(`   入力テキスト: ${inputText.substring(0, 50)}...`);
  }

  // Mermaid構文生成
  let mermaidCode;
  
  if (inputText.trim().startsWith('flowchart') || 
      inputText.trim().startsWith('sequenceDiagram') ||
      inputText.trim().startsWith('stateDiagram') ||
      inputText.trim().startsWith('erDiagram') ||
      inputText.trim().startsWith('gantt')) {
    // 既にMermaid構文の場合はそのまま使用
    console.log('   → Mermaid構文として認識');
    mermaidCode = inputText;
  } else {
    // テキストからMermaid生成
    mermaidCode = autoGenerateMermaid(inputText, config);
  }

  console.log('\n生成されたMermaid構文:');
  console.log('---');
  console.log(mermaidCode);
  console.log('---\n');

  // Mermaidのみ出力モード
  if (config.mermaidOnly) {
    const mmdPath = config.output.replace(/\.(png|svg)$/, '.mmd');
    fs.writeFileSync(mmdPath, mermaidCode, 'utf-8');
    console.log(`✅ Mermaidファイル出力: ${mmdPath}`);
    return;
  }

  // 画像変換
  await convertMermaidToImage(mermaidCode, config.output, {
    format: config.format,
    theme: config.theme
  });
}

main().catch(err => {
  console.error('❌ エラー:', err.message);
  process.exit(1);
});

module.exports = {
  generateFlowchart,
  generateSequence,
  generateSwimlane,
  generateStateDiagram,
  autoGenerateMermaid
};
