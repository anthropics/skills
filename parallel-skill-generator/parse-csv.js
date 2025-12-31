// CSV解析とスキル情報の構造化

/**
 * スキルリクエストの型定義
 * @typedef {Object} SkillRequest
 * @property {string} name - 記入者名
 * @property {string} department - 部門/チーム
 * @property {string} profession - 職業/役職
 * @property {string} painPoint - ペインポイント
 * @property {string} task - 解決したいタスク
 * @property {string} skillName - 希望するスキル名
 * @property {string} outputFormat - 出力形式の希望
 * @property {string} priority - 優先度
 * @property {string} notes - 備考
 */

/**
 * スキル名を自動生成
 * @param {string} task - タスクの説明
 * @returns {string} 生成されたスキル名
 */
function generateSkillName(task) {
  // キーワードベースでスキル名を生成
  const patterns = {
    '自動作成': 'generator',
    '自動生成': 'generator',
    '計算': 'calculator',
    '分析': 'analyzer',
    'チェック': 'checker',
    '比較': 'comparator',
    '集計': 'aggregator',
    '変換': 'converter',
    '更新': 'updater',
    '仕訳': 'categorizer'
  };
  
  let baseName = 'skill';
  let suffix = 'tool';
  
  // タスクからキーワードを抽出
  for (const [keyword, suf] of Object.entries(patterns)) {
    if (task.includes(keyword)) {
      suffix = suf;
      break;
    }
  }
  
  // タスクの最初の名詞を抽出（簡易版）
  const nouns = task.match(/[^\s、。！？]+(?:書|表|データ|情報|申告|保険|契約|規則|レポート)/g);
  if (nouns && nouns[0]) {
    baseName = nouns[0].replace(/[のをが]/, '');
  }
  
  return `${baseName}-${suffix}`.toLowerCase().replace(/[^\w-]/g, '');
}

/**
 * CSV内容を解析してスキルリクエストの配列を返す
 * @param {string} csvContent - CSV文字列
 * @returns {SkillRequest[]} スキルリクエストの配列
 */
function parseSkillRequests(csvContent) {
  const lines = csvContent.split('\n');
  const headers = lines[0].split(',').map(h => h.trim());
  
  const skills = [];
  
  for (let i = 1; i < lines.length; i++) {
    const line = lines[i].trim();
    if (!line) continue;
    
    // CSVの簡易パーサー（カンマ区切り、引用符未対応）
    const values = line.split(',').map(v => v.trim());
    
    // 必須フィールドのチェック
    if (!values[0] || !values[2] || !values[3] || !values[4]) {
      console.warn(`行${i + 1}はスキップされました（必須項目が不足）`);
      continue;
    }
    
    const skillRequest = {
      name: values[0],
      department: values[1] || '',
      profession: values[2],
      painPoint: values[3],
      task: values[4],
      skillName: values[5] || generateSkillName(values[4]),
      outputFormat: values[6] || 'Text',
      priority: values[7] || '中',
      notes: values[8] || ''
    };
    
    skills.push(skillRequest);
  }
  
  return skills;
}

/**
 * スキルリクエストを優先度でグループ化
 * @param {SkillRequest[]} skills - スキルリクエストの配列
 * @returns {Object} 優先度別にグループ化されたオブジェクト
 */
function groupByPriority(skills) {
  const groups = {
    '高': [],
    '中': [],
    '低': []
  };
  
  skills.forEach(skill => {
    const priority = skill.priority || '中';
    if (groups[priority]) {
      groups[priority].push(skill);
    } else {
      groups['中'].push(skill);
    }
  });
  
  return groups;
}

/**
 * スキルリクエストを職業でグループ化
 * @param {SkillRequest[]} skills - スキルリクエストの配列
 * @returns {Object} 職業別にグループ化されたオブジェクト
 */
function groupByProfession(skills) {
  const groups = {};
  
  skills.forEach(skill => {
    const profession = skill.profession;
    if (!groups[profession]) {
      groups[profession] = [];
    }
    groups[profession].push(skill);
  });
  
  return groups;
}

// エクスポート
if (typeof module !== 'undefined' && module.exports) {
  module.exports = {
    parseSkillRequests,
    generateSkillName,
    groupByPriority,
    groupByProfession
  };
}