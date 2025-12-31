# 並列スキル生成ワークフロー

## 概要
このドキュメントは、Claude Codeの並列実行機能を最大限活用してスキルを生成するワークフローを説明します。

## Claude Codeの並列実行パターン

### 1. 複数ツールの同時実行
Claude Codeは一度に複数のツールを呼び出すことができます：

```
// 同時に複数のディレクトリを作成
<複数のBashツール呼び出し>
- mkdir skill-1
- mkdir skill-2
- mkdir skill-3
...（最大10個まで同時実行可能）
```

### 2. 複数ファイルの同時作成
```
// 同時に複数のSKILL.mdを作成
<複数のWriteツール呼び出し>
- Write skill-1/SKILL.md
- Write skill-2/SKILL.md
- Write skill-3/SKILL.md
...（最大10個まで同時実行可能）
```

### 3. 複数ファイルの同時読み取り
```
// 検証のため複数ファイルを同時に読む
<複数のReadツール呼び出し>
- Read skill-1/SKILL.md
- Read skill-2/SKILL.md
- Read skill-3/SKILL.md
```

## ワークフローステップ

### Step 1: CSVデータの準備と解析
```javascript
// 1. CSVファイルを読み込む
const csvContent = await readFile('professional_skill_requests.csv');

// 2. スキル情報を解析
const skills = parseSkillRequests(csvContent);

// 3. バッチに分割（10個ずつ）
const batches = [];
for (let i = 0; i < skills.length; i += 10) {
  batches.push(skills.slice(i, i + 10));
}
```

### Step 2: ディレクトリの並列作成
```javascript
// 各バッチに対して並列実行
for (const batch of batches) {
  // Claude Codeで同時に最大10個のmkdirコマンドを実行
  const mkdirCommands = batch.map(skill => 
    `mkdir -p /path/to/${skill.skillName}`
  );
  
  // 並列実行
  await executeParallelBash(mkdirCommands);
}
```

### Step 3: SKILL.mdファイルの並列生成
```javascript
// スキルファイルの内容を生成
function generateSkillContent(skill) {
  return `# ${skill.skillName}

## スキル概要
${skill.profession}の${skill.task}を自動化するスキル

## 背景
${skill.name}さん（${skill.profession}）から以下の課題が報告されました：
- ${skill.painPoint}

## 主な機能
1. ${skill.task}の自動化
2. ${skill.outputFormat}形式での出力
3. エラーチェックと検証機能

## ワークフロー
[詳細なワークフローをここに記載]

## 期待される効果
- 作業時間の大幅短縮
- ヒューマンエラーの削減
- 業務効率の向上

## 注意事項
${skill.notes}
`;
}

// 並列でファイル作成
for (const batch of batches) {
  const writeOperations = batch.map(skill => ({
    path: `/path/to/${skill.skillName}/SKILL.md`,
    content: generateSkillContent(skill)
  }));
  
  // 最大10個のファイルを同時に作成
  await executeParallelWrite(writeOperations);
}
```

### Step 4: 検証とレポート生成
```javascript
// 作成されたスキルの検証
const verificationResults = [];

for (const batch of batches) {
  // 並列でファイルの存在確認
  const readOperations = batch.map(skill => 
    `/path/to/${skill.skillName}/SKILL.md`
  );
  
  const results = await executeParallelRead(readOperations);
  verificationResults.push(...results);
}

// レポート生成
const report = generateReport(skills, verificationResults);
```

## 実行例

### 基本的な使い方
```
「professional_skill_requests.csvから並列でスキルを作成してください」
```

### 高優先度のみ処理
```
「CSVから優先度が「高」のスキルのみを並列で作成してください」
```

### 特定の職業のみ処理
```
「税理士のスキルのみを並列で作成してください」
```

## パフォーマンス最適化のヒント

### 1. バッチサイズの調整
- 10個以下: 1バッチで処理
- 11-30個: 3バッチに分割
- 31個以上: 適切なバッチサイズで分割

### 2. エラーハンドリング
```javascript
// エラーが発生しても他のスキル作成は継続
const results = await Promise.allSettled(writeOperations);
const failures = results.filter(r => r.status === 'rejected');
```

### 3. プログレス表示
```javascript
console.log(`バッチ ${currentBatch}/${totalBatches} を処理中...`);
console.log(`進捗: ${completed}/${total} (${Math.round(completed/total*100)}%)`);
```

## 実装時の注意点

1. **ファイルシステムの制限**
   - 同時に作成できるファイル数に注意
   - ディスクI/Oの負荷を考慮

2. **メモリ使用量**
   - 大量のスキル情報を扱う場合はメモリに注意
   - 必要に応じてストリーミング処理を検討

3. **エラーリカバリ**
   - 部分的な失敗に対応できるよう設計
   - 失敗したスキルのリトライ機能

## 拡張可能性

### 将来的な機能追加
1. **依存関係の管理**
   - スキル間の依存関係を考慮した順序制御

2. **テンプレートエンジン**
   - より高度なスキルテンプレートのサポート

3. **自動テスト**
   - 生成されたスキルの自動検証

4. **バージョン管理**
   - スキルの更新履歴管理