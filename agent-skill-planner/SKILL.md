---
name: agent-skill-planner
description: Interactive analyzer for Agent Skill planning. Use when users want to create a new Agent Skill and need help defining its purpose, scope, and structure. Guides users through atomic task decomposition, 1-skill-1-purpose validation, and YAML specification generation. Bridges user requirements to skill-creator by producing structured planning output. Trigger on requests like "create a skill for...", "I want to make a skill that...", "help me design an Agent Skill", or any task that requires skill requirement analysis before implementation.
---

# Agent Skill Planner

Interactive requirement analyzer that helps users define optimal Agent Skills through structured dialogue and atomic task decomposition.

## Purpose

Transform vague user requests into well-defined, single-purpose Agent Skill specifications that follow the **1 Skill = 1 Purpose** principle. Output structured YAML that can be passed directly to `skill-creator`.

## Core Principles

### 1 Skill = 1 Purpose
- Each skill must serve exactly ONE specific purpose
- Multiple purposes require multiple skills
- Clear boundaries prevent scope creep

### Atomic Task Decomposition
- Break requests into smallest indivisible tasks
- Each atomic task = single action with single output
- Identify which tasks deserve skill-ification vs simple prompts

### Trigger Clarity
- Use concrete verbs and specific file formats
- Avoid ambiguous language in descriptions
- Define clear do/don't boundaries

### Repeatability Threshold
- Prioritize tasks repeated 5+ times OR expected 10+ future uses
- One-off tasks don't warrant skills

## Dialogue Flow

### Phase 1: Initial Understanding (1-2 exchanges)

Ask targeted questions to understand:

1. **Core objective**: "What problem are you trying to solve?"
2. **Frequency**: "How often will this be used?"
3. **Output format**: "What should the final result look like?"
4. **Trigger context**: "What would a user say to activate this skill?"

**Example:**
```
User: "動画の内容を分析してレポートを作るスキルが欲しい"

Claude: "いくつか確認させてください:
1. 動画の種類は?(セミナー録画、製品デモ、インタビューなど)
2. レポートの形式は?(Markdown、Word、PowerPoint?)
3. 月に何回くらい使う想定ですか?
4. 分析内容は?(要約、文字起こし、キーポイント抽出?)"
```

**Response strategy:**
- Ask 3-5 specific questions maximum per exchange
- Focus on disambiguation, not exhaustive details
- Use examples to clarify ambiguous terms

### Phase 2: Task Decomposition (2-3 exchanges)

Present atomic task breakdown and validate with user:

1. **Show decomposition**: List all atomic tasks identified
2. **Confirm understanding**: "Is this breakdown correct?"
3. **Identify skill candidates**: Mark which tasks should be skills vs prompts
4. **Check for hidden complexity**: "Are there edge cases I'm missing?"

**Example:**
```
Claude: "依頼内容を分解すると、以下のタスクが必要そうです:

Atomic Tasks:
1. 動画ファイルから音声を抽出
2. 音声を文字起こし(日本語認識)
3. 文字起こしテキストを構造化(話者分離、タイムスタンプ)
4. 内容を要約・分析
5. 指定形式(Word/Markdown)でレポート生成

Skill化が必要なのは:
- タスク3-5(繰り返し使う構造化パターン)

Skill化不要:
- タスク1-2(既存ツールで十分)

この分解で合っていますか?他に必要な処理はありますか?"
```

**Validation checklist:**
- [ ] All tasks are truly atomic (cannot be subdivided further)
- [ ] No overlapping purposes between tasks
- [ ] Clear input/output for each task
- [ ] Skill vs prompt classification justified

### Phase 3: Boundary Definition (1-2 exchanges)

Clarify skill scope and constraints:

1. **Split evaluation**: Does this need multiple skills?
2. **Trigger precision**: What exact phrases should activate it?
3. **Constraint identification**: What should this skill NOT do?
4. **Success criteria**: How do we know it worked?

**Example:**
```
Claude: "スキルの境界を確認します:

このスキルは:
✓ 日本語の文字起こしテキストを構造化
✓ ビジネスコンテキストに沿った要約生成
✓ Word/Markdown形式でレポート出力

このスキルは NOT:
✗ 動画ファイルの直接処理(前処理として別ツール使用)
✗ リアルタイム分析
✗ 動画編集機能

分割の必要性:
現状は単一目的(文字起こし→レポート化)なので1スキルで適切。
ただし、将来的に「動画編集」機能を追加したい場合は別スキル化を推奨。

この境界定義で問題ありませんか?"
```

### Phase 4: YAML Specification (Final output)

Generate complete YAML specification:

```yaml
goal: "<最終的に達成したいこと(1文)>"

atomic_tasks:
  - "<最小タスク1>"
  - "<最小タスク2>"
  - "<最小タスク3>"

should_be_skill:
  - "<Skill化すべきタスク>"
  - "<理由: 繰り返し利用、複雑な構造化が必要、など>"

skill_name: "lowercase-kebab-case-name"

description_draft: |
  <Claude trigger用の明確な説明>
  
  必須要素:
  - 何をするスキルか(能力)
  - いつ使うべきか(シナリオ)
  - 何をしないか(境界)
  - トリガーとなる具体的なフレーズ例
  - 対応するファイル形式や入力タイプ

instructions_outline: |
  # <Skill Name>
  
  ## Purpose
  <単一目的の明確な定義>
  
  ## Workflow
  1. <ステップ1>
  2. <ステップ2>
  3. <ステップ3>
  
  ## Input Requirements
  - <必要な入力1>
  - <必要な入力2>
  
  ## Output Specification
  - <出力形式>
  - <品質基準>
  
  ## Constraints & Boundaries
  - DO: <すること>
  - DO NOT: <しないこと>
  
  ## Examples
  <具体的な使用例>

skill_split_evaluation: |
  <さらに分割が必要かどうかの評価>
  
  判断基準:
  - 目的が2つ以上混在していないか?
  - トリガーが曖昧になっていないか?
  - 1つのスキルが複数のドメインをカバーしすぎていないか?
  
  推奨: <分割不要/2つに分割すべき/など>

repeatability_score: "<使用頻度の評価: 低/中/高>"

next_steps: |
  このYAML仕様を `skill-creator` スキルに渡して、
  実際のSKILL.mdファイルを生成できます。
  
  続けて作成しますか?
```

## Dialogue Strategies

### When User is Vague

**Don't:** Accept vague requirements and produce ambiguous specs
**Do:** Ask specific clarifying questions with examples

```
User: "なんでもできるAIアシスタントスキルを作りたい"

Claude: "「なんでもできる」は複数目的の混在を示しています。
具体的にどのような作業を自動化したいですか?

例えば:
- 文書作成の自動化?
- データ分析のサポート?
- コード生成?
- 会議議事録の作成?

1つ選んで、その具体例を教えてください。"
```

### When Scope is Too Broad

**Don't:** Force everything into one skill
**Do:** Propose skill split with clear rationale

```
Claude: "この要件には3つの異なる目的が含まれています:

1. PDFからデータ抽出
2. データ分析と可視化
3. レポート生成

推奨: 3つの独立したスキルに分割
- pdf-data-extractor (目的1)
- data-analyzer (目的2)
- report-generator (目的3)

理由: 各目的で使用頻度とトリガーが異なるため。

全て1つにまとめますか?それとも分割しますか?"
```

### When User Accepts Decomposition

**Don't:** Immediately generate YAML
**Do:** Confirm all details before final output

```
Claude: "了解しました。最終確認です:

Skill Name: pdf-table-extractor
Purpose: PDFの表データを構造化Excelに変換
Trigger: 「PDFから表を抽出」「PDFテーブルをExcel化」
Output: .xlsx形式
Frequency: 週2-3回

この仕様でYAML生成に進みますか?
修正したい点があれば教えてください。"
```

## Anti-Patterns to Avoid

### ❌ Accepting Multiple Purposes
```yaml
# BAD
skill_name: document-processor
description: Process any document type and generate any output format
```

### ✅ Single Clear Purpose
```yaml
# GOOD
skill_name: docx-to-markdown
description: Convert Word documents to Markdown format with formatting preservation
```

### ❌ Vague Triggers
```yaml
# BAD
description: Help with data tasks
```

### ✅ Specific Triggers
```yaml
# GOOD
description: Extract tables from PDF files and convert to Excel format. Use when user uploads PDF and requests table extraction, data conversion to spreadsheet, or structured data export.
```

### ❌ Scope Creep in Instructions
```markdown
# BAD
This skill processes documents, analyzes data, generates reports, 
and creates presentations.
```

### ✅ Focused Scope
```markdown
# GOOD
This skill converts DOCX files to Markdown while preserving:
- Headings and hierarchy
- Lists and tables
- Basic formatting (bold, italic)
```

## Special Considerations

### Japanese Business Context

When working with Japanese business requirements:

1. **Clarify document types**: 稟議書、議事録、報告書 have different structures
2. **Confirm language**: 日本語のみ or 日英対応?
3. **Check formality**: ビジネス文書 requires specific tone and format
4. **Validate output format**: Word, Excel, PowerPoint have different usage contexts in Japanese business

### Integration with Existing Skills

Before creating new skill, check if existing skills can handle the task:

```
Claude: "この要件は既存の `docx` スキルで対応できそうです。
新しいスキルを作る前に、既存スキルで試してみますか?

もし既存スキルで不足している機能があれば、
それを明確にしてから新規作成を検討しましょう。"
```

### Skill vs MCP Server Decision

Guide users on when to build MCP server instead of skill:

**Use Skill when:**
- Workflow/process documentation needed
- Requires Claude's reasoning at each step
- Frequent variation in execution

**Use MCP Server when:**
- External API integration required
- Real-time data access needed
- Authentication/credentials involved

## Output Quality Checklist

Before generating final YAML, verify:

- [ ] Goal statement is one clear sentence
- [ ] All atomic tasks are truly indivisible
- [ ] Skill name follows lowercase-kebab-case
- [ ] Description includes concrete triggers and file formats
- [ ] Instructions outline follows standard structure
- [ ] Split evaluation provides clear reasoning
- [ ] Repeatability justifies skill creation (5+ uses)
- [ ] No multiple purposes混在
- [ ] Clear DO/DON'T boundaries defined

## Handoff to skill-creator

After generating YAML specification:

```
このYAML仕様が確定したら、次のステップで `skill-creator` スキルを使って
実際のSKILL.mdファイルを生成できます。

続けて実装まで進めますか?それとも仕様の調整が必要ですか?
```

If user approves, pass the YAML to skill-creator and assist with implementation.

## Example Complete Flow

```
User: "業務日報を音声入力で作るスキルが欲しい"

Claude: "確認させてください:
1. 日報のフォーマットは決まっていますか?
2. 音声入力後、どのファイル形式で保存?
3. 週何回くらい使いますか?"

User: "5列のExcelフォーマット、週5回使う"

Claude: "タスク分解:
1. 音声をテキスト化
2. テキストから項目抽出(日付、作業内容、課題など)
3. Excel形式で出力
4. Google Driveに保存

Skill化すべきは2-4です。1は既存機能で対応可能。
この分解で合っていますか?"

User: "OK"

Claude: "境界確認:
✓ 5列固定フォーマット(日付、報告者、作業内容、課題、次回予定)
✓ Excel出力のみ
✗ 日報の分析機能は含まない
✗ 勤怠管理は含まない

分割不要: 単一目的(音声→日報Excel化)

この仕様でYAML生成しますか?"

User: "はい"

Claude: [YAML output]
```

## Iteration & Refinement

After user tests the generated skill:

1. **Collect feedback**: "実際に使ってみてどうでしたか?"
2. **Identify gaps**: "想定外の入力や状況はありましたか?"
3. **Propose updates**: "XXを追加すると改善できそうです"
4. **Regenerate YAML**: Update specification based on learnings

Remember: Good skills emerge through iteration. First version doesn't need to be perfect.
