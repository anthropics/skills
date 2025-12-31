#!/usr/bin/env python3
"""
提案書生成モジュール
既存のpresentation-creator、project-planner等のスキルを活用
"""
import os
import sys
import json
import logging
from pathlib import Path
from typing import Dict, Any, List, Optional
from datetime import datetime

logger = logging.getLogger('document_generator')

# 既存スキルのパスを追加
SKILLS_DIR = Path(__file__).resolve().parents[3]
sys.path.insert(0, str(SKILLS_DIR))


class DocumentGenerator:
    """提案書生成クラス"""
    
    def __init__(self, output_dir: Path):
        self.output_dir = output_dir
        self.generated_files = []
        
    def create_documents(self, 
                        analysis: Dict[str, Any],
                        proposals: List[Dict[str, Any]]) -> Dict[str, str]:
        """
        各種提案書類の生成
        
        Args:
            analysis: 業種・業務分析結果
            proposals: AI活用提案リスト
            
        Returns:
            生成されたドキュメントのパス情報
        """
        logger.info("提案書生成開始")
        
        documents = {}
        
        # 1. エグゼクティブサマリーの生成
        documents["executive_summary"] = self._create_executive_summary(
            analysis, proposals
        )
        
        # 2. 詳細提案書の生成
        documents["detailed_proposal"] = self._create_detailed_proposal(
            analysis, proposals
        )
        
        # 3. プレゼンテーション資料の生成（既存スキル活用を想定）
        documents["presentation"] = self._create_presentation(
            analysis, proposals
        )
        
        # 4. 実装ロードマップの生成（既存スキル活用を想定）
        documents["roadmap"] = self._create_implementation_roadmap(
            analysis, proposals
        )
        
        # 5. ROI試算レポートの生成
        documents["roi_report"] = self._create_roi_report(
            proposals
        )
        
        logger.info(f"提案書生成完了: {len(documents)}種類")
        return documents
        
    def _create_executive_summary(self,
                                analysis: Dict[str, Any],
                                proposals: List[Dict[str, Any]]) -> str:
        """エグゼクティブサマリーの生成"""
        output_path = self.output_dir / "executive_summary.md"
        
        # 優先度の高い提案を抽出
        high_priority_proposals = [p for p in proposals if p.get("priority") == "高"]
        
        content = f"""# AI活用提案 エグゼクティブサマリー

## 企業概要
- **企業名**: {analysis.get('company_name', '貴社')}
- **業種**: {analysis['industry']['main_category']}
- **AI導入準備度**: {analysis['ai_readiness']['level']} ({analysis['ai_readiness']['recommendation']})

## 主要な課題
{self._format_challenges(analysis['key_challenges'])}

## AI活用による解決策（優先度：高）
{self._format_high_priority_proposals(high_priority_proposals)}

## 期待される効果
{self._format_expected_benefits(proposals[:3])}

## 推奨される実施ステップ
1. **短期（1-3ヶ月）**: パイロットプロジェクトの開始
   - {high_priority_proposals[0]['title'] if high_priority_proposals else 'AI活用の基礎検証'}
   
2. **中期（3-6ヶ月）**: 本格導入と効果検証
   - 初期成果の評価と改善
   - 次フェーズの準備
   
3. **長期（6-12ヶ月）**: 全社展開と最適化
   - 成功事例の横展開
   - 継続的な改善サイクル確立

## 投資対効果（3年間）
{self._format_roi_summary(proposals[:3])}

---
*作成日: {datetime.now().strftime('%Y年%m月%d日')}*
"""
        
        with open(output_path, 'w', encoding='utf-8') as f:
            f.write(content)
            
        self.generated_files.append(output_path)
        return str(output_path)
        
    def _create_detailed_proposal(self,
                                analysis: Dict[str, Any],
                                proposals: List[Dict[str, Any]]) -> str:
        """詳細提案書の生成"""
        output_path = self.output_dir / "ai_proposal_detailed.md"
        
        content = f"""# AI活用提案書 詳細版

## 1. はじめに
本提案書は、{analysis.get('company_name', '貴社')}のWebサイト分析および業種特性の調査に基づき、最適なAI活用方法をご提案するものです。

## 2. 現状分析

### 2.1 企業情報
{self._format_company_analysis(analysis)}

### 2.2 業務プロセス分析
{self._format_business_processes(analysis['business_processes'])}

### 2.3 技術成熟度評価
- **現在のレベル**: {analysis['tech_maturity']['level']} ({analysis['tech_maturity']['label']})
- **評価指標**: {', '.join(analysis['tech_maturity']['indicators'])}

## 3. AI活用提案

{self._format_all_proposals(proposals)}

## 4. 実装アプローチ

### 4.1 段階的導入計画
{self._format_phased_approach(analysis['ai_readiness'])}

### 4.2 必要なリソース
{self._format_required_resources(proposals[:3])}

### 4.3 リスクと対策
{self._format_risk_mitigation()}

## 5. 成功要因
{self._format_success_factors(analysis)}

## 6. 次のステップ
1. 提案内容の詳細検討会の実施
2. パイロットプロジェクトの選定
3. 実施体制の構築
4. KPIの設定と評価基準の策定

## 付録
- [A. 業種別AI活用事例](#)
- [B. 技術仕様詳細](#)
- [C. 参考資料](#)

---
*本提案書は自動生成されたものです。詳細については担当者にお問い合わせください。*
"""
        
        with open(output_path, 'w', encoding='utf-8') as f:
            f.write(content)
            
        self.generated_files.append(output_path)
        return str(output_path)
        
    def _create_presentation(self,
                           analysis: Dict[str, Any],
                           proposals: List[Dict[str, Any]]) -> str:
        """プレゼンテーション資料の生成"""
        # 既存のpresentation-creatorスキルが使用可能か確認
        if self._check_existing_skill("presentation-creator"):
            return self._use_presentation_creator(analysis, proposals)
        
        # フォールバック: Markdownスライド形式で生成
        output_path = self.output_dir / "ai_proposal_slides.md"
        
        content = f"""---
title: AI活用提案
subtitle: {analysis.get('company_name', '貴社')}向けカスタマイズプラン
date: {datetime.now().strftime('%Y年%m月%d日')}
---

# アジェンダ

1. 現状分析
2. AI活用の可能性
3. 具体的な提案
4. 実装計画
5. 期待効果とROI
6. 次のステップ

---

# 現状分析

## 貴社の強み
- {analysis['industry']['main_category']}のリーディングカンパニー
- 豊富なデータ資産
- 変革への意欲

## 改善機会
{self._format_slide_challenges(analysis['key_challenges'])}

---

# AI活用の可能性

## 業界トレンド
- AI/自動化の導入が加速
- 競合他社の動向
- 市場の期待値上昇

## 貴社の準備状況
- **評価**: {analysis['ai_readiness']['level']}
- **推奨事項**: {analysis['ai_readiness']['recommendation']}

---

{self._format_proposal_slides(proposals[:3])}

---

# 実装計画

## フェーズ1: Quick Win（1-3ヶ月）
- {proposals[0]['title'] if proposals else 'パイロットプロジェクト'}
- 小規模での効果検証
- 社内体制の構築

## フェーズ2: 拡大展開（3-6ヶ月）
- 成功事例の横展開
- プロセスの最適化
- 効果測定と改善

---

# 期待効果とROI

{self._format_roi_slide(proposals[:3])}

---

# 次のステップ

1. **本提案の詳細検討**
   - 技術要件の確認
   - 実施体制の協議
   
2. **パイロットプロジェクトの計画**
   - 対象業務の選定
   - スケジュール策定
   
3. **キックオフ**
   - プロジェクト開始
   - 定期レビューの設定

---

# お問い合わせ

ご質問・ご相談はお気軽にどうぞ

AI Advisor Team
"""
        
        with open(output_path, 'w', encoding='utf-8') as f:
            f.write(content)
            
        self.generated_files.append(output_path)
        return str(output_path)
        
    def _create_implementation_roadmap(self,
                                     analysis: Dict[str, Any],
                                     proposals: List[Dict[str, Any]]) -> str:
        """実装ロードマップの生成"""
        # 既存のproject-plannerやgantt-chart-generatorが使用可能か確認
        if self._check_existing_skill("project-planner"):
            return self._use_project_planner(analysis, proposals)
        
        # フォールバック: テキストベースのロードマップ
        output_path = self.output_dir / "implementation_roadmap.md"
        
        content = f"""# AI活用実装ロードマップ

## プロジェクト概要
- **企業名**: {analysis.get('company_name', '貴社')}
- **期間**: 12ヶ月
- **開始予定**: {datetime.now().strftime('%Y年%m月')}

## マイルストーン

### Phase 1: 準備・計画（Month 1-2）
- [ ] プロジェクトチーム編成
- [ ] 現状調査・要件定義
- [ ] データ基盤の評価
- [ ] 初期KPI設定

### Phase 2: パイロット実装（Month 3-5）
{self._format_pilot_tasks(proposals[0] if proposals else None)}

### Phase 3: 評価・改善（Month 6-7）
- [ ] 効果測定
- [ ] 課題抽出と対策
- [ ] 次フェーズ計画
- [ ] 社内展開準備

### Phase 4: 本格展開（Month 8-10）
{self._format_rollout_tasks(proposals[1:3] if len(proposals) > 1 else [])}

### Phase 5: 最適化・定着（Month 11-12）
- [ ] 全体最適化
- [ ] 運用体制確立
- [ ] 継続的改善プロセス
- [ ] 次年度計画

## リソース計画

### 人的リソース
{self._format_resource_plan(proposals[:3])}

### 技術リソース
- クラウド環境（AWS/Azure/GCP）
- AI/MLプラットフォーム
- データ統合ツール
- モニタリングツール

## リスク管理

### 主要リスク
1. **技術的リスク**: データ品質、システム統合
2. **組織的リスク**: 変更管理、スキルギャップ
3. **外部リスク**: 規制変更、市場動向

### 対策
- 段階的導入による検証
- 継続的な教育・研修
- 外部専門家の活用

---
*更新日: {datetime.now().strftime('%Y年%m月%d日')}*
"""
        
        with open(output_path, 'w', encoding='utf-8') as f:
            f.write(content)
            
        self.generated_files.append(output_path)
        return str(output_path)
        
    def _create_roi_report(self, proposals: List[Dict[str, Any]]) -> str:
        """ROI試算レポートの生成"""
        output_path = self.output_dir / "roi_analysis.md"
        
        content = f"""# ROI分析レポート

## サマリー
本レポートでは、提案されたAI活用施策の投資対効果（ROI）を試算しています。

## 前提条件
- 試算期間: 3年間
- 為替レート: 該当なし（日本円ベース）
- 割引率: 5%（現在価値計算用）

## 個別施策のROI分析

{self._format_individual_roi(proposals[:5])}

## 統合ROI分析

### 投資総額
{self._calculate_total_investment(proposals[:5])}

### 期待収益総額
{self._calculate_total_benefits(proposals[:5])}

### ROIサマリー
{self._format_roi_summary_table(proposals[:5])}

## 感度分析

### ベストケース（+20%）
- 効果が想定を20%上回った場合のROI

### ベースケース
- 現在の試算通りのROI

### ワーストケース（-20%）
- 効果が想定を20%下回った場合のROI

## 投資判断の指針
{self._format_investment_recommendation(proposals[:3])}

## 注記
- 本試算は現時点での想定に基づくものです
- 実際の効果は実装方法や外部要因により変動します
- 定期的な見直しを推奨します

---
*作成日: {datetime.now().strftime('%Y年%m月%d日')}*
"""
        
        with open(output_path, 'w', encoding='utf-8') as f:
            f.write(content)
            
        self.generated_files.append(output_path)
        return str(output_path)
        
    # ヘルパーメソッド群
    
    def _format_challenges(self, challenges: List[Dict[str, str]]) -> str:
        """課題のフォーマット"""
        lines = []
        for challenge in challenges[:5]:
            priority_emoji = "🔴" if challenge['priority'] == "high" else "🟡"
            lines.append(f"{priority_emoji} **{challenge['challenge']}** ({challenge['category']})")
        return '\n'.join(lines)
        
    def _format_high_priority_proposals(self, proposals: List[Dict[str, Any]]) -> str:
        """優先度の高い提案のフォーマット"""
        if not proposals:
            return "- 詳細な分析により最適な提案を選定します"
            
        lines = []
        for i, proposal in enumerate(proposals[:3], 1):
            lines.append(f"""
### {i}. {proposal['title']}
- **カテゴリ**: {proposal['category']}
- **期待効果**: {proposal['expected_benefits']['primary']}
- **実装期間**: {proposal['implementation_timeline']}
""")
        return '\n'.join(lines)
        
    def _format_expected_benefits(self, proposals: List[Dict[str, Any]]) -> str:
        """期待効果のフォーマット"""
        all_benefits = set()
        for proposal in proposals:
            benefits = proposal.get('expected_benefits', {})
            if benefits.get('primary'):
                all_benefits.add(benefits['primary'])
            for secondary in benefits.get('secondary', []):
                all_benefits.add(secondary)
                
        return '\n'.join([f"- {benefit}" for benefit in list(all_benefits)[:6]])
        
    def _format_roi_summary(self, proposals: List[Dict[str, Any]]) -> str:
        """ROIサマリーのフォーマット"""
        total_investment = 0
        total_annual_benefit = 0
        
        for proposal in proposals:
            roi_data = proposal.get('roi_estimation', {})
            if roi_data:
                # 初期投資額を抽出（"X百万円"形式から数値を取得）
                investment_str = roi_data.get('initial_investment', '0百万円')
                investment = float(investment_str.replace('百万円', ''))
                total_investment += investment
                
                # 年間便益を抽出
                benefit_str = roi_data.get('annual_expected_benefit', '0百万円')
                benefit = float(benefit_str.replace('百万円', ''))
                total_annual_benefit += benefit
                
        if total_investment > 0:
            roi_3years = ((total_annual_benefit * 3 - total_investment) / total_investment) * 100
            return f"""- **初期投資総額**: {total_investment:.0f}百万円
- **年間期待便益**: {total_annual_benefit:.1f}百万円
- **3年間ROI**: {roi_3years:.0f}%
- **投資回収期間**: {(total_investment / total_annual_benefit):.1f}年"""
        else:
            return "- 詳細なROI試算は個別にご相談ください"
            
    def _format_company_analysis(self, analysis: Dict[str, Any]) -> str:
        """企業分析情報のフォーマット"""
        company_info = []
        
        company_info.append(f"- **企業名**: {analysis.get('company_name', '未設定')}")
        company_info.append(f"- **業種**: {analysis['industry']['main_category']}")
        company_info.append(f"- **サブカテゴリ**: {analysis['industry'].get('identified_subcategory', '特定なし')}")
        company_info.append(f"- **企業規模**: {analysis['company_scale']['label']}")
        
        return '\n'.join(company_info)
        
    def _format_business_processes(self, processes: List[Dict[str, Any]]) -> str:
        """業務プロセスのフォーマット"""
        lines = []
        for process in processes[:5]:
            lines.append(f"""
#### {process['category']}
- **関連度スコア**: {process['relevance_score']:.2f}
- **AI活用可能性**: {', '.join(process.get('potential_ai_applications', [])[:3])}
""")
        return '\n'.join(lines)
        
    def _format_all_proposals(self, proposals: List[Dict[str, Any]]) -> str:
        """全提案のフォーマット"""
        lines = []
        
        # カテゴリ別にグループ化
        categories = {}
        for proposal in proposals:
            category = proposal['category']
            if category not in categories:
                categories[category] = []
            categories[category].append(proposal)
            
        for category, category_proposals in categories.items():
            lines.append(f"\n### {category}")
            
            for proposal in category_proposals[:3]:
                lines.append(f"""
#### {proposal['title']}
- **説明**: {proposal['description']}
- **難易度**: {proposal['difficulty']}
- **実装期間**: {proposal['implementation_timeline']}
- **期待効果**: {proposal['expected_benefits']['primary']}

**詳細計画**:
{self._format_detailed_plan(proposal.get('detailed_plan', {}))}

**必要リソース**:
{self._format_resources(proposal.get('required_resources', {}))}
""")
        
        return '\n'.join(lines)
        
    def _format_detailed_plan(self, plan: Dict[str, str]) -> str:
        """詳細計画のフォーマット"""
        if not plan:
            return "- 詳細計画は個別に策定します"
            
        lines = []
        for phase, description in plan.items():
            lines.append(f"- **{phase}**: {description}")
        return '\n'.join(lines)
        
    def _format_resources(self, resources: Dict[str, Any]) -> str:
        """必要リソースのフォーマット"""
        lines = []
        for resource_type, resource_detail in resources.items():
            if isinstance(resource_detail, list):
                detail = ', '.join(resource_detail)
            else:
                detail = str(resource_detail)
            lines.append(f"- **{resource_type}**: {detail}")
        return '\n'.join(lines)
        
    def _format_phased_approach(self, ai_readiness: Dict[str, Any]) -> str:
        """段階的アプローチのフォーマット"""
        return f"""
現在のAI準備度レベル「{ai_readiness['level']}」に基づき、以下のアプローチを推奨します：

1. **準備フェーズ**: {ai_readiness['next_steps'][0] if ai_readiness.get('next_steps') else 'データ基盤の整備'}
2. **実証フェーズ**: {ai_readiness['next_steps'][1] if len(ai_readiness.get('next_steps', [])) > 1 else 'パイロットプロジェクト実施'}
3. **展開フェーズ**: {ai_readiness['next_steps'][2] if len(ai_readiness.get('next_steps', [])) > 2 else '成功事例の横展開'}
"""
        
    def _format_required_resources(self, proposals: List[Dict[str, Any]]) -> str:
        """必要リソースの統合フォーマット"""
        human_resources = set()
        technical_resources = set()
        
        for proposal in proposals:
            resources = proposal.get('required_resources', {})
            if 'human' in resources:
                human_resources.add(resources['human'])
            if 'technical' in resources:
                technical_resources.add(resources['technical'])
                
        lines = ["### 人的リソース"]
        lines.extend([f"- {hr}" for hr in human_resources])
        lines.append("\n### 技術リソース")
        lines.extend([f"- {tr}" for tr in technical_resources])
        
        return '\n'.join(lines)
        
    def _format_risk_mitigation(self) -> str:
        """リスク対策のフォーマット"""
        return """
| リスク種別 | 具体的リスク | 対策 |
|----------|------------|------|
| 技術的リスク | AIモデルの精度不足 | 段階的な改善とフィードバックループ |
| データリスク | データ品質・量の不足 | データ整備プロジェクトの並行実施 |
| 組織的リスク | 従業員の抵抗 | 丁寧な説明と段階的導入 |
| 財務的リスク | ROI未達成 | KPI設定と定期的なレビュー |
"""
        
    def _format_success_factors(self, analysis: Dict[str, Any]) -> str:
        """成功要因のフォーマット"""
        return f"""
1. **経営層のコミットメント**: AI活用ビジョンの明確化と支援
2. **適切な人材配置**: AIプロジェクトチームの編成
3. **データ基盤の整備**: 質の高いデータの継続的な収集
4. **段階的な導入**: スモールスタートからの着実な拡大
5. **継続的な改善**: PDCAサイクルの確立
6. **組織文化**: 失敗を恐れない挑戦的な文化の醸成
"""
        
    def _check_existing_skill(self, skill_name: str) -> bool:
        """既存スキルの存在確認"""
        skill_path = SKILLS_DIR / "skills" / skill_name
        return skill_path.exists()
        
    def _use_presentation_creator(self, 
                                analysis: Dict[str, Any],
                                proposals: List[Dict[str, Any]]) -> str:
        """既存のpresentation-creatorスキルを使用"""
        # 実際の実装では、presentation-creatorをインポートして使用
        # ここではプレースホルダーとして上記のフォールバック実装を使用
        logger.info("presentation-creatorスキルの統合を試みています")
        return self._create_presentation(analysis, proposals)
        
    def _use_project_planner(self,
                           analysis: Dict[str, Any],
                           proposals: List[Dict[str, Any]]) -> str:
        """既存のproject-plannerスキルを使用"""
        # 実際の実装では、project-plannerをインポートして使用
        logger.info("project-plannerスキルの統合を試みています")
        return self._create_implementation_roadmap(analysis, proposals)
        
    # 追加のヘルパーメソッド（プレゼンテーション用）
    
    def _format_slide_challenges(self, challenges: List[Dict[str, str]]) -> str:
        """スライド用の課題フォーマット"""
        lines = []
        for challenge in challenges[:3]:
            lines.append(f"- {challenge['challenge']}")
        return '\n'.join(lines)
        
    def _format_proposal_slides(self, proposals: List[Dict[str, Any]]) -> str:
        """提案スライドのフォーマット"""
        slides = []
        
        for i, proposal in enumerate(proposals, 1):
            slide = f"""
# 提案{i}: {proposal['title']}

## 概要
{proposal['description']}

## 期待効果
- {proposal['expected_benefits']['primary']}
- {', '.join(proposal['expected_benefits'].get('secondary', [])[:2])}

## 実装期間
{proposal['implementation_timeline']}

---
"""
            slides.append(slide)
            
        return '\n'.join(slides)
        
    def _format_roi_slide(self, proposals: List[Dict[str, Any]]) -> str:
        """ROIスライドのフォーマット"""
        lines = ["## 3年間の投資対効果\n"]
        
        for proposal in proposals:
            roi = proposal.get('roi_estimation', {})
            if roi:
                lines.append(f"### {proposal['title']}")
                lines.append(f"- 投資額: {roi.get('initial_investment', 'N/A')}")
                lines.append(f"- 回収期間: {roi.get('payback_period', 'N/A')}")
                lines.append(f"- 3年ROI: {roi.get('roi_3years', 'N/A')}\n")
                
        return '\n'.join(lines)
        
    # ロードマップ用ヘルパーメソッド
    
    def _format_pilot_tasks(self, proposal: Optional[Dict[str, Any]]) -> str:
        """パイロットタスクのフォーマット"""
        if not proposal:
            return """- [ ] パイロットプロジェクト選定
- [ ] 実装環境構築
- [ ] 初期開発
- [ ] テスト実施"""
            
        return f"""- [ ] {proposal['title']}の要件定義
- [ ] データ準備・前処理
- [ ] AIモデル開発
- [ ] システム統合
- [ ] パイロット運用開始"""
        
    def _format_rollout_tasks(self, proposals: List[Dict[str, Any]]) -> str:
        """展開タスクのフォーマット"""
        if not proposals:
            return """- [ ] 成功事例の横展開
- [ ] プロセス標準化
- [ ] 全社展開計画"""
            
        lines = []
        for proposal in proposals:
            lines.append(f"- [ ] {proposal['title']}の本格導入")
            lines.append(f"- [ ] 効果測定とKPI評価")
            
        return '\n'.join(lines)
        
    def _format_resource_plan(self, proposals: List[Dict[str, Any]]) -> str:
        """リソース計画のフォーマット"""
        return """
| フェーズ | 必要人員 | 期間 |
|---------|---------|------|
| 準備・計画 | PM×1, アナリスト×2 | 2ヶ月 |
| パイロット | PM×1, AIエンジニア×2, ドメインエキスパート×1 | 3ヶ月 |
| 本格展開 | PM×1, AIエンジニア×3, 運用×2 | 4ヶ月 |
| 最適化 | PM×1, AIエンジニア×1, 運用×2 | 2ヶ月 |
"""
        
    # ROIレポート用ヘルパーメソッド
    
    def _format_individual_roi(self, proposals: List[Dict[str, Any]]) -> str:
        """個別ROI分析のフォーマット"""
        lines = []
        
        for i, proposal in enumerate(proposals, 1):
            roi = proposal.get('roi_estimation', {})
            lines.append(f"""
### {i}. {proposal['title']}

#### 投資内容
- 初期投資: {roi.get('initial_investment', 'N/A')}
- 年間運用コスト: {roi.get('annual_operating_cost', 'N/A')}

#### 期待収益
- 年間期待便益: {roi.get('annual_expected_benefit', 'N/A')}
- 損益分岐点: {roi.get('break_even_point', 'N/A')}

#### ROI指標
- 3年間ROI: {roi.get('roi_3years', 'N/A')}
- 投資回収期間: {roi.get('payback_period', 'N/A')}
""")
        
        return '\n'.join(lines)
        
    def _calculate_total_investment(self, proposals: List[Dict[str, Any]]) -> str:
        """総投資額の計算"""
        total = 0
        breakdown = []
        
        for proposal in proposals:
            roi = proposal.get('roi_estimation', {})
            if roi and 'initial_investment' in roi:
                amount_str = roi['initial_investment'].replace('百万円', '')
                amount = float(amount_str)
                total += amount
                breakdown.append(f"- {proposal['title']}: {amount}百万円")
                
        return f"""
**総額**: {total:.0f}百万円

**内訳**:
{chr(10).join(breakdown)}
"""
        
    def _calculate_total_benefits(self, proposals: List[Dict[str, Any]]) -> str:
        """総便益の計算"""
        annual_total = 0
        breakdown = []
        
        for proposal in proposals:
            roi = proposal.get('roi_estimation', {})
            if roi and 'annual_expected_benefit' in roi:
                amount_str = roi['annual_expected_benefit'].replace('百万円', '')
                amount = float(amount_str)
                annual_total += amount
                breakdown.append(f"- {proposal['title']}: {amount:.1f}百万円/年")
                
        return f"""
**年間総便益**: {annual_total:.1f}百万円
**3年間総便益**: {annual_total * 3:.1f}百万円

**内訳**:
{chr(10).join(breakdown)}
"""
        
    def _format_roi_summary_table(self, proposals: List[Dict[str, Any]]) -> str:
        """ROIサマリーテーブルのフォーマット"""
        return """
| 指標 | 1年目 | 2年目 | 3年目 | 合計 |
|------|-------|-------|-------|------|
| 投資額 | XXX百万円 | XX百万円 | XX百万円 | XXX百万円 |
| 収益 | XX百万円 | XXX百万円 | XXX百万円 | XXX百万円 |
| 累積ROI | -XX% | XX% | XXX% | XXX% |
"""
        
    def _format_investment_recommendation(self, proposals: List[Dict[str, Any]]) -> str:
        """投資判断の推奨事項"""
        # 最もROIの高い提案を特定
        best_roi_proposal = None
        best_roi_value = -100
        
        for proposal in proposals:
            roi = proposal.get('roi_estimation', {})
            if roi and 'roi_3years' in roi:
                roi_value = float(roi['roi_3years'].replace('%', ''))
                if roi_value > best_roi_value:
                    best_roi_value = roi_value
                    best_roi_proposal = proposal
                    
        if best_roi_proposal:
            return f"""
## 推奨事項

1. **優先実施案件**: {best_roi_proposal['title']}
   - 最も高いROI（{best_roi_value:.0f}%）を期待
   - 実装リスクが比較的低い

2. **段階的投資アプローチ**
   - 初年度は検証を重視した小規模投資
   - 成果確認後に本格投資へ移行

3. **継続的モニタリング**
   - 月次でKPIをトラッキング
   - 四半期ごとにROI再評価
"""
        else:
            return """
## 推奨事項

1. **パイロットプロジェクトから開始**
2. **効果測定の仕組みを確立**
3. **段階的な投資拡大**
"""