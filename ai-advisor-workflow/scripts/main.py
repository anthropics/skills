#!/usr/bin/env python3
"""
AI Advisor Workflow - メインコントローラー
既存のAgentSkillsを統合して、HP分析から提案書作成、スキル生成まで実行
"""
import os
import sys
import json
from pathlib import Path
from datetime import datetime
from typing import Dict, List, Any, Optional
import logging

# 既存スキルのインポートパス設定
SKILLS_DIR = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(SKILLS_DIR))

# ログ設定
logging.basicConfig(
    level=logging.INFO,
    format='%(asctime)s - %(name)s - %(levelname)s - %(message)s'
)
logger = logging.getLogger('ai_advisor_workflow')


class AIAdvisorWorkflow:
    """AI活用提案ワークフローの統合管理クラス"""
    
    def __init__(self, config: Optional[Dict[str, Any]] = None):
        """
        初期化
        
        Args:
            config: ワークフロー設定
        """
        self.config = config or self._load_default_config()
        self.results = {}
        self.output_dir = None
        
    def _load_default_config(self) -> Dict[str, Any]:
        """デフォルト設定の読み込み"""
        return {
            "web_extractor": {
                "timeout": 30,
                "max_pages": 50,
                "follow_links": True
            },
            "analysis": {
                "industry_classification": True,
                "business_process_extraction": True,
                "competitor_analysis": False
            },
            "proposal": {
                "categories": [
                    "業務効率化",
                    "顧客体験向上",
                    "データ分析・意思決定支援",
                    "新規事業・サービス開発"
                ],
                "max_proposals_per_category": 3,
                "include_roi_calculation": True
            },
            "skill_generation": {
                "generate_tests": True,
                "include_documentation": True,
                "template_style": "standard"
            }
        }
        
    def execute(self, 
                client_url: str,
                output_dir: str = "./output",
                generate_skills: bool = True) -> Dict[str, Any]:
        """
        ワークフロー全体の実行
        
        Args:
            client_url: クライアントのWebサイトURL
            output_dir: 出力ディレクトリ
            generate_skills: AgentSkillsを生成するかどうか
            
        Returns:
            実行結果の辞書
        """
        try:
            logger.info(f"AI Advisor Workflow開始: {client_url}")
            
            # 出力ディレクトリの準備
            self._prepare_output_directory(output_dir)
            
            # Step 1: HP情報収集
            logger.info("Step 1: HP情報収集開始")
            web_data = self._extract_web_content(client_url)
            
            # Step 2: 業種・業務分析
            logger.info("Step 2: 業種・業務分析開始")
            analysis_result = self._analyze_business(web_data)
            
            # Step 3: AI活用提案生成
            logger.info("Step 3: AI活用提案生成開始")
            proposals = self._generate_ai_proposals(analysis_result)
            
            # Step 4: 提案書作成
            logger.info("Step 4: 提案書作成開始")
            documents = self._create_proposal_documents(
                analysis_result, 
                proposals
            )
            
            # Step 5: AgentSkills生成（オプション）
            generated_skills = []
            if generate_skills:
                logger.info("Step 5: AgentSkills生成開始")
                generated_skills = self._generate_agent_skills(proposals)
            
            # 結果のまとめ
            self.results = {
                "status": "success",
                "client_url": client_url,
                "timestamp": datetime.now().isoformat(),
                "web_data_summary": self._summarize_web_data(web_data),
                "industry_analysis": analysis_result,
                "proposals": proposals,
                "documents": documents,
                "generated_skills": generated_skills,
                "output_directory": str(self.output_dir)
            }
            
            # 結果の保存
            self._save_results()
            
            logger.info("AI Advisor Workflow完了")
            return self.results
            
        except Exception as e:
            logger.error(f"ワークフロー実行エラー: {str(e)}")
            raise
            
    def _prepare_output_directory(self, output_dir: str):
        """出力ディレクトリの準備"""
        self.output_dir = Path(output_dir).resolve()
        
        # サブディレクトリの作成
        subdirs = [
            "proposal",
            "generated_skills",
            "reports",
            "assets"
        ]
        
        for subdir in subdirs:
            (self.output_dir / subdir).mkdir(parents=True, exist_ok=True)
            
    def _extract_web_content(self, url: str) -> Dict[str, Any]:
        """
        Webコンテンツの抽出
        web-content-extractorスキルを活用
        """
        try:
            # ここで実際のweb-content-extractorを呼び出す
            # 現在はモックデータを返す
            from .hp_analyzer import HPAnalyzer
            
            analyzer = HPAnalyzer()
            return analyzer.extract_content(url, self.config["web_extractor"])
            
        except Exception as e:
            logger.error(f"Web情報抽出エラー: {str(e)}")
            # フォールバックとしてシンプルな抽出を実行
            return self._simple_web_extract(url)
            
    def _simple_web_extract(self, url: str) -> Dict[str, Any]:
        """シンプルなWeb情報抽出（フォールバック）"""
        return {
            "url": url,
            "title": "サンプル企業",
            "description": "サンプル企業の説明",
            "content": {
                "company_overview": "ITソリューションを提供する企業",
                "services": ["システム開発", "コンサルティング"],
                "industry": "情報通信業"
            },
            "extracted_at": datetime.now().isoformat()
        }
        
    def _analyze_business(self, web_data: Dict[str, Any]) -> Dict[str, Any]:
        """
        業種・業務分析
        """
        from .business_analyzer import BusinessAnalyzer
        
        analyzer = BusinessAnalyzer()
        return analyzer.analyze(web_data, self.config["analysis"])
        
    def _generate_ai_proposals(self, analysis: Dict[str, Any]) -> List[Dict[str, Any]]:
        """
        AI活用提案の生成
        """
        from .ai_proposal_engine import AIProposalEngine
        
        engine = AIProposalEngine()
        return engine.generate_proposals(analysis, self.config["proposal"])
        
    def _create_proposal_documents(self, 
                                 analysis: Dict[str, Any],
                                 proposals: List[Dict[str, Any]]) -> Dict[str, str]:
        """
        提案書の作成
        presentation-creatorなど既存スキルを活用
        """
        from .document_generator import DocumentGenerator
        
        generator = DocumentGenerator(self.output_dir / "proposal")
        return generator.create_documents(analysis, proposals)
        
    def _generate_agent_skills(self, proposals: List[Dict[str, Any]]) -> List[Dict[str, Any]]:
        """
        AgentSkillsの自動生成
        skill-creation-guideを活用
        """
        from .skill_generator import SkillGenerator
        
        generator = SkillGenerator(
            self.output_dir / "generated_skills",
            self.config["skill_generation"]
        )
        return generator.generate_skills_from_proposals(proposals)
        
    def _summarize_web_data(self, web_data: Dict[str, Any]) -> Dict[str, Any]:
        """Web情報のサマリー作成"""
        return {
            "url": web_data.get("url", ""),
            "title": web_data.get("title", ""),
            "industry": web_data.get("content", {}).get("industry", "不明"),
            "services": web_data.get("content", {}).get("services", []),
            "pages_analyzed": len(web_data.get("pages", []))
        }
        
    def _save_results(self):
        """実行結果の保存"""
        results_file = self.output_dir / "reports" / "workflow_results.json"
        with open(results_file, 'w', encoding='utf-8') as f:
            json.dump(self.results, f, ensure_ascii=False, indent=2)
            
        logger.info(f"結果を保存しました: {results_file}")


def main():
    """CLIエントリーポイント"""
    import argparse
    
    parser = argparse.ArgumentParser(
        description="AI Advisor Workflow - AI活用提案自動生成システム"
    )
    parser.add_argument(
        "url",
        help="分析対象のWebサイトURL"
    )
    parser.add_argument(
        "--output",
        default="./output",
        help="出力ディレクトリ (デフォルト: ./output)"
    )
    parser.add_argument(
        "--no-skills",
        action="store_true",
        help="AgentSkillsの生成をスキップ"
    )
    parser.add_argument(
        "--config",
        help="設定ファイルのパス"
    )
    
    args = parser.parse_args()
    
    # 設定の読み込み
    config = None
    if args.config:
        with open(args.config, 'r', encoding='utf-8') as f:
            config = json.load(f)
    
    # ワークフローの実行
    workflow = AIAdvisorWorkflow(config)
    results = workflow.execute(
        client_url=args.url,
        output_dir=args.output,
        generate_skills=not args.no_skills
    )
    
    # 結果の表示
    print("\n=== AI Advisor Workflow 実行完了 ===")
    print(f"出力ディレクトリ: {results['output_directory']}")
    print(f"生成された提案数: {len(results['proposals'])}")
    if results['generated_skills']:
        print(f"生成されたスキル数: {len(results['generated_skills'])}")
    

if __name__ == "__main__":
    main()