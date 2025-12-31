# parallel-skill-generator

## スキル概要
Claude Codeの並列処理機能を最大限活用し、CSVファイルから複数のAgent Skillsを同時並行で高速生成するスキル

## 背景
skill-batch-creatorはシーケンシャルな処理であったため、大量のスキル作成に時間がかかっていました。Claude Codeの強力な並列処理機能を使うことで、複数のスキルを同時に作成し、処理時間を大幅に短縮できます。

## 主な機能
1. **並列CSV処理**: 複数行のスキルリクエストを同時に解析
2. **パラレルディレクトリ作成**: 複数のスキルフォルダを一括作成
3. **同時SKILL.md生成**: 複数のSKILL.mdファイルを並行して作成
4. **バッチバリデーション**: 作成前の一括検証
5. **プログレスレポート**: リアルタイムな進捗状況の報告

## ワークフロー

### 1. CSV読み込みと解析
```
「CSVファイル /path/to/requests.csv から並列でAgent Skillsを作成してください」
```

### 2. バッチ処理の準備
- CSVの全行を一度に読み込み
- スキル情報を配列に格納
- 重複チェックと検証

### 3. 並列実行フェーズ

#### Phase 1: ディレクトリの一括作成
Claude Codeの複数ツール同時実行機能を使用：
```
- 全スキルのディレクトリを1回のコマンドで作成
- 例: 9個のスキルなら9個のディレクトリを同時作成
```

#### Phase 2: SKILL.mdの並列生成
複数のWriteツールを同時に呼び出し：
```
- 各スキルのSKILL.mdを同時に作成
- テンプレートエンジンを使用して高速生成
```

#### Phase 3: 検証と最適化
並列でファイルの存在確認と内容検証：
```
- 全ファイルの作成確認
- 内容の整合性チェック
- エラー時の自動リトライ
```

## 技術的な実装

### CSVパーサー関数
```typescript
function parseSkillRequests(csvContent: string): SkillRequest[] {
  const lines = csvContent.split('\n');
  const headers = lines[0].split(',');
  
  return lines.slice(1)
    .filter(line => line.trim())
    .map(line => {
      const values = line.split(',');
      return {
        name: values[0],
        department: values[1],
        profession: values[2],
        painPoint: values[3],
        task: values[4],
        skillName: values[5] || generateSkillName(values[4]),
        outputFormat: values[6],
        priority: values[7],
        notes: values[8]
      };
    });
}
```

### 並列実行戦略
```typescript
// バッチサイズの最適化（Claude Codeは最大10個の同時ツール実行が可能）
const BATCH_SIZE = 10;

function executeBatch(skills: SkillRequest[]) {
  const batches = chunk(skills, BATCH_SIZE);
  
  for (const batch of batches) {
    // 同時にディレクトリ作成
    parallelCreateDirectories(batch);
    
    // 同時にSKILL.md作成
    parallelCreateSkillFiles(batch);
  }
}
```

## 利用例

### 基本的な使用方法
```
「Docs/professional_skill_requests.csvを使って並列でスキルを作成してください」
```

### 高度な使用方法
```
「優先度が「高」のスキルだけを並列で作成し、
作成時間を計測してレポートを出してください」
```

## パフォーマンス比較

### シーケンシャル処理（従来）
- 9個のスキル作成: 約3-5分
- 1スキルあたり: 20-30秒

### パラレル処理（本スキル）
- 9個のスキル作成: 約30-45秒
- 処理速度: 5-10倍高速

## ベストプラクティス

1. **CSVフォーマットの確認**
   - 必須項目が全て埋まっているか確認
   - 文字コードはUTF-8を使用

2. **バッチサイズの調整**
   - 10個以下: 1バッチで処理
   - 11-50個: 複数バッチに分割
   - 50個以上: プログレスバーを表示

3. **エラーハンドリング**
   - 個別のスキル作成失敗は全体を止めない
   - 失敗したスキルのリストを最後に表示

## 出力構造
```
output-directory/
├── skill-1/
│   └── SKILL.md
├── skill-2/
│   └── SKILL.md
├── ...
└── generation-report.md  # 生成レポート
```

## 注意事項
- Claude Codeの並列実行は最大10個まで同時実行可能
- 大量のファイルI/O操作時はシステムリソースに注意
- ネットワークドライブでは並列処理の効果が低下する可能性

## 今後の拡張予定
1. スキルテンプレートのカスタマイズ機能
2. 依存関係を持つスキルの順次・並列ハイブリッド処理
3. 生成後の自動テスト実行
4. スキルのバージョン管理機能