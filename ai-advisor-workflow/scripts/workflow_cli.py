#!/usr/bin/env python3
"""
AI Advisor Workflow CLI with Trigger Words
トリガーワードを使った対話型インターフェース
"""
import os
import sys
import json
from pathlib import Path
from datetime import datetime
import logging
from typing import Optional, Dict, Any, List

# パス設定
sys.path.insert(0, str(Path(__file__).parent))

from main import AIAdvisorWorkflow
from trigger_words import TriggerWordProcessor, TriggerType, create_workflow_command

logging.basicConfig(level=logging.INFO)
logger = logging.getLogger('workflow_cli')


class WorkflowCLI:
    """対話型ワークフローCLI"""
    
    def __init__(self):
        self.processor = TriggerWordProcessor()
        self.workflow = None
        self.history = []
        
    def run(self):
        """メインループ"""
        self._show_welcome()
        
        while True:
            try:
                user_input = input("\n🤖 > ").strip()
                
                if not user_input:
                    continue
                    
                # 終了コマンド
                if user_input.lower() in ["exit", "quit", "終了", "bye"]:
                    print("\n👋 またお会いしましょう！")
                    break
                    
                # ヘルプコマンド
                if user_input.lower() in ["help", "?", "ヘルプ", "使い方"]:
                    self._show_help()
                    continue
                    
                # 履歴表示
                if user_input.lower() in ["history", "履歴"]:
                    self._show_history()
                    continue
                    
                # トリガー処理
                self._process_input(user_input)
                
            except KeyboardInterrupt:
                print("\n\n👋 終了します。")
                break
            except Exception as e:
                logger.error(f"エラー発生: {e}")
                print(f"\n❌ エラーが発生しました: {e}")
                print("もう一度お試しください。")
                
    def _show_welcome(self):
        """ウェルカムメッセージ"""
        print("""
╔═══════════════════════════════════════════════════════╗
║     🚀 AI Advisor Workflow - Interactive CLI 🚀       ║
╠═══════════════════════════════════════════════════════╣
║  クライアントのWebサイトを分析し、                    ║
║  AI活用提案とAgentSkillsを自動生成します。           ║
╚═══════════════════════════════════════════════════════╝

💡 使い方の例:
  • "https://example.com を分析して"
  • "株式会社〇〇のAI活用提案書を作成"
  • "ざっくりとサイトをチェック"
  
📌 コマンド: help, history, exit
""")
        
    def _show_help(self):
        """ヘルプ表示"""
        print("""
📚 使い方ガイド

【基本的な使い方】
1. URLを含めて分析依頼
   例: "https://example.com を分析して提案書を作成"

2. 会社名から分析
   例: "株式会社サンプルのホームページを調査"

3. 複数URLを指定
   例: "https://example.com と https://example.com/services を分析"

【トリガーワード】
• 分析系: 分析して、調査して、調べて、チェックして
• 提案系: 提案書作成、提案を作って、proposal
• スキル系: スキル生成、AgentSkill作成、実装して
• クイック: ざっくり、簡単に、さっと見て

【オプション】
• スキル不要: スキル生成をスキップ
• ROI不要: ROI計算をスキップ
• 効率化重視: 業務効率化に特化した提案

【便利なコマンド】
• help / ? : このヘルプを表示
• history : 実行履歴を表示
• exit / quit : 終了
""")
        
    def _show_history(self):
        """実行履歴表示"""
        if not self.history:
            print("\n📋 実行履歴はまだありません。")
            return
            
        print("\n📋 実行履歴:")
        for i, item in enumerate(self.history[-10:], 1):  # 最新10件
            print(f"\n{i}. {item['timestamp']}")
            print(f"   入力: {item['input']}")
            print(f"   結果: {item['status']}")
            if item.get('output_dir'):
                print(f"   出力: {item['output_dir']}")
                
    def _process_input(self, user_input: str):
        """ユーザー入力を処理"""
        # トリガー解析
        match = self.processor.process(user_input)
        
        if not match:
            print("\n🤔 申し訳ありません、理解できませんでした。")
            print("💡 ヒント: URLや「分析して」「提案書作成」などのキーワードを含めてください。")
            self._suggest_similar_commands(user_input)
            return
            
        # 確認メッセージ
        print(f"\n✅ 理解しました！")
        print(f"📊 実行内容: {self._get_action_description(match.trigger_type)}")
        if match.urls:
            print(f"🔗 対象URL: {', '.join(match.urls[:3])}")
            if len(match.urls) > 3:
                print(f"   他 {len(match.urls) - 3} 件")
        else:
            print("⚠️  URLが指定されていません。サンプルデータで実行します。")
            
        # 実行確認
        confirm = input("\n実行しますか？ (Y/n): ").strip().lower()
        if confirm == 'n':
            print("キャンセルしました。")
            return
            
        # ワークフロー実行
        self._execute_workflow(match, user_input)
        
    def _execute_workflow(self, match, user_input: str):
        """ワークフローを実行"""
        print("\n⏳ 処理を開始します...")
        
        # 出力ディレクトリ作成
        timestamp = datetime.now().strftime('%Y%m%d_%H%M%S')
        output_dir = f"./output/{match.trigger_type.value}_{timestamp}"
        
        try:
            # ワークフローインスタンス作成
            if not self.workflow:
                self.workflow = AIAdvisorWorkflow()
                
            # 設定の適用
            config = self._create_config_from_match(match)
            self.workflow.config.update(config)
            
            # URLが空の場合はサンプルを使用
            urls = match.urls if match.urls else ["https://example.com"]
            
            # 実行
            result = self.workflow.execute(
                client_urls=urls,
                output_dir=output_dir,
                generate_skills=match.options.get('generate_skills', True)
            )
            
            # 結果表示
            self._show_results(result, match)
            
            # 履歴に追加
            self.history.append({
                'timestamp': datetime.now().strftime('%Y-%m-%d %H:%M:%S'),
                'input': user_input,
                'status': 'success',
                'output_dir': output_dir,
                'trigger_type': match.trigger_type.value
            })
            
        except Exception as e:
            logger.error(f"ワークフロー実行エラー: {e}")
            print(f"\n❌ 実行中にエラーが発生しました: {e}")
            
            # エラーも履歴に記録
            self.history.append({
                'timestamp': datetime.now().strftime('%Y-%m-%d %H:%M:%S'),
                'input': user_input,
                'status': 'error',
                'error': str(e)
            })
            
    def _create_config_from_match(self, match) -> Dict[str, Any]:
        """マッチ結果から設定を作成"""
        config = {}
        
        # クイックモードの設定
        if match.options.get('quick_mode'):
            config['web_extractor'] = {
                'max_pages': 10,
                'follow_links': False,
                'timeout': 15
            }
            
        # カテゴリ制限
        if match.options.get('proposal_categories'):
            config['proposal'] = {
                'categories': match.options['proposal_categories']
            }
            
        # ROI設定
        if 'include_roi' in match.options:
            config.setdefault('proposal', {})['include_roi_calculation'] = match.options['include_roi']
            
        return config
        
    def _show_results(self, result: Dict[str, Any], match):
        """実行結果を表示"""
        print("\n" + "="*50)
        print("✨ 実行完了！")
        print("="*50)
        
        # 企業情報
        print(f"\n🏢 企業情報:")
        print(f"  • 企業名: {result['industry_analysis']['company_name']}")
        print(f"  • 業種: {result['industry_analysis']['industry']['main_category']}")
        print(f"  • AI準備度: {result['industry_analysis']['ai_readiness']['level']}")
        
        # 提案サマリー
        if result.get('proposals'):
            print(f"\n💡 AI活用提案 (上位3件):")
            for i, proposal in enumerate(result['proposals'][:3], 1):
                print(f"\n  {i}. {proposal['title']}")
                print(f"     カテゴリ: {proposal['category']}")
                print(f"     期待効果: {proposal['expected_benefits']['primary']}")
                if 'roi_estimation' in proposal:
                    print(f"     ROI: {proposal['roi_estimation']['roi_3years']}")
                    
        # 生成物
        print(f"\n📁 生成されたファイル:")
        print(f"  • 出力先: {result['output_directory']}")
        
        if result.get('documents'):
            print(f"\n  📄 ドキュメント:")
            for doc_type, doc_path in result['documents'].items():
                print(f"     • {self._get_doc_name(doc_type)}: {Path(doc_path).name}")
                
        if result.get('generated_skills'):
            print(f"\n  🛠️  AgentSkills ({len(result['generated_skills'])}個):")
            for skill in result['generated_skills'][:3]:
                print(f"     • {skill['name']}")
                
        # 次のアクション提案
        print("\n💭 次のアクション:")
        print(f"  1. 提案書を確認: {result['output_directory']}/proposal/")
        if result.get('generated_skills'):
            print(f"  2. スキルをテスト: {result['output_directory']}/generated_skills/")
        print("  3. 別の企業を分析: 新しいURLを入力してください")
        
    def _get_action_description(self, trigger_type: TriggerType) -> str:
        """アクションの説明を取得"""
        descriptions = {
            TriggerType.ANALYZE: "Webサイトの詳細分析",
            TriggerType.QUICK_CHECK: "クイックチェック（簡易分析）",
            TriggerType.PROPOSAL: "AI活用提案書の作成",
            TriggerType.SKILL_GEN: "AgentSkillsの生成",
            TriggerType.FULL_WORKFLOW: "フルワークフロー（分析→提案→スキル生成）"
        }
        return descriptions.get(trigger_type, "カスタム処理")
        
    def _get_doc_name(self, doc_type: str) -> str:
        """ドキュメントタイプの日本語名"""
        names = {
            'executive_summary': 'エグゼクティブサマリー',
            'detailed_proposal': '詳細提案書',
            'presentation': 'プレゼンテーション',
            'roadmap': '実装ロードマップ',
            'roi_report': 'ROI分析レポート'
        }
        return names.get(doc_type, doc_type)
        
    def _suggest_similar_commands(self, user_input: str):
        """類似コマンドの提案"""
        suggestions = [
            "https://example.com を分析して",
            "AI活用提案書を作成",
            "ざっくりサイトをチェック",
            "株式会社〇〇のスキルを生成"
        ]
        
        print("\n💡 こんな感じで試してみてください:")
        for suggestion in suggestions[:3]:
            print(f"   • {suggestion}")


def main():
    """メインエントリーポイント"""
    cli = WorkflowCLI()
    cli.run()


if __name__ == "__main__":
    main()