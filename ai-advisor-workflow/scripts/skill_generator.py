#!/usr/bin/env python3
"""
AgentSkills自動生成モジュール
スタメンSkillsをベースに、クライアント向けにカスタマイズしたスキルを生成
プールされたスキルも参考にして最適化
"""
import os
import sys
import json
import logging
from pathlib import Path
from typing import Dict, Any, List, Optional, Tuple
from datetime import datetime
import shutil
import re

logger = logging.getLogger('skill_generator')

# 既存スキルのパスを追加
SKILLS_DIR = Path(__file__).resolve().parents[3]
sys.path.insert(0, str(SKILLS_DIR))


class SkillGenerator:
    """AgentSkills自動生成クラス"""
    
    def __init__(self, output_dir: Path, config: Dict[str, Any]):
        self.output_dir = output_dir
        self.config = config
        self.generated_skills = []
        
        # スタメンSkills（既存の汎用スキル）
        self.starter_skills_dir = SKILLS_DIR / "skills"
        
        # プールSkills（クライアント向けカスタムスキル）
        self.pool_skills_dir = SKILLS_DIR / "client-skills-pool"
        self.pool_skills_dir.mkdir(exist_ok=True)
        
        # スキルテンプレート
        self.skill_templates = self._load_skill_templates()
        
    def generate_skills_from_proposals(self, 
                                     proposals: List[Dict[str, Any]]) -> List[Dict[str, Any]]:
        """
        AI活用提案からAgentSkillsを生成
        
        Args:
            proposals: AI活用提案リスト
            
        Returns:
            生成されたスキル情報のリスト
        """
        logger.info(f"AgentSkills生成開始: {len(proposals)}件の提案から生成")
        
        for proposal in proposals[:5]:  # 上位5提案に対してスキル生成
            if proposal.get("priority") == "高" or proposal.get("priority_score", 0) > 5:
                skill_info = self._generate_skill_for_proposal(proposal)
                if skill_info:
                    self.generated_skills.append(skill_info)
                    
        # 生成したスキルをプールに追加
        self._add_skills_to_pool()
        
        logger.info(f"AgentSkills生成完了: {len(self.generated_skills)}個のスキル")
        return self.generated_skills
        
    def _generate_skill_for_proposal(self, proposal: Dict[str, Any]) -> Optional[Dict[str, Any]]:
        """
        個別の提案に対するスキル生成
        
        Args:
            proposal: AI活用提案
            
        Returns:
            生成されたスキル情報
        """
        try:
            # 1. 提案内容を分析してスキルタイプを決定
            skill_type = self._determine_skill_type(proposal)
            
            # 2. スタメンSkillsから最も適したベーススキルを選択
            base_skill = self._select_base_skill(proposal, skill_type)
            
            # 3. プールから類似のカスタムスキルを検索
            similar_skills = self._find_similar_pool_skills(proposal)
            
            # 4. スキルをカスタマイズ
            customized_skill = self._customize_skill(
                proposal, 
                base_skill, 
                similar_skills
            )
            
            # 5. スキルファイルを生成
            skill_path = self._create_skill_files(customized_skill)
            
            return {
                "name": customized_skill["name"],
                "path": str(skill_path),
                "base_skill": base_skill["name"] if base_skill else "original",
                "proposal_title": proposal["title"],
                "skill_type": skill_type,
                "pool_candidate": True,  # プール候補
                "starter_candidate": self._evaluate_for_starter(customized_skill)
            }
            
        except Exception as e:
            logger.error(f"スキル生成エラー: {str(e)}")
            return None
            
    def _determine_skill_type(self, proposal: Dict[str, Any]) -> str:
        """提案内容からスキルタイプを決定"""
        category = proposal.get("category", "")
        title = proposal.get("title", "").lower()
        description = proposal.get("description", "").lower()
        
        # キーワードマッチングでタイプ判定
        type_keywords = {
            "automation": ["自動化", "automation", "効率化", "省力化"],
            "analysis": ["分析", "analysis", "レポート", "可視化"],
            "integration": ["連携", "integration", "統合", "api"],
            "communication": ["チャット", "bot", "対話", "カスタマー"],
            "prediction": ["予測", "prediction", "予知", "需要"],
            "optimization": ["最適化", "optimization", "改善"],
            "document": ["文書", "document", "生成", "作成"]
        }
        
        for skill_type, keywords in type_keywords.items():
            if any(keyword in title or keyword in description for keyword in keywords):
                return skill_type
                
        return "general"
        
    def _select_base_skill(self, 
                         proposal: Dict[str, Any], 
                         skill_type: str) -> Optional[Dict[str, Any]]:
        """
        スタメンSkillsから最適なベーススキルを選択
        """
        # スタメンスキルを検索
        starter_skills = self._load_starter_skills()
        
        # スコアリングして最適なスキルを選択
        best_skill = None
        best_score = 0
        
        for skill in starter_skills:
            score = self._calculate_skill_relevance_score(skill, proposal, skill_type)
            if score > best_score:
                best_score = score
                best_skill = skill
                
        logger.info(f"ベーススキル選択: {best_skill['name'] if best_skill else 'None'} (スコア: {best_score})")
        return best_skill
        
    def _load_starter_skills(self) -> List[Dict[str, Any]]:
        """スタメンスキルの読み込み"""
        starter_skills = []
        
        for skill_dir in self.starter_skills_dir.iterdir():
            if skill_dir.is_dir() and (skill_dir / "SKILL.md").exists():
                skill_info = self._parse_skill_metadata(skill_dir)
                if skill_info:
                    skill_info["path"] = skill_dir
                    starter_skills.append(skill_info)
                    
        return starter_skills
        
    def _parse_skill_metadata(self, skill_dir: Path) -> Optional[Dict[str, Any]]:
        """SKILL.mdからメタデータを抽出"""
        skill_md_path = skill_dir / "SKILL.md"
        
        try:
            with open(skill_md_path, 'r', encoding='utf-8') as f:
                content = f.read()
                
            # YAMLフロントマターの抽出
            yaml_match = re.match(r'^---\n(.*?)\n---', content, re.DOTALL)
            if yaml_match:
                import yaml
                metadata = yaml.safe_load(yaml_match.group(1))
                return metadata
            else:
                # フロントマターがない場合は基本情報を抽出
                return {
                    "name": skill_dir.name,
                    "description": self._extract_description_from_md(content),
                    "tags": []
                }
                
        except Exception as e:
            logger.warning(f"スキルメタデータ読み込みエラー: {skill_dir.name} - {str(e)}")
            return None
            
    def _extract_description_from_md(self, content: str) -> str:
        """Markdownから説明を抽出"""
        lines = content.split('\n')
        for i, line in enumerate(lines):
            if line.startswith('## 概要') or line.startswith('## Overview'):
                # 次の空行までを説明として取得
                description_lines = []
                for j in range(i + 1, len(lines)):
                    if lines[j].strip() == '':
                        break
                    description_lines.append(lines[j])
                return ' '.join(description_lines)
        return ""
        
    def _calculate_skill_relevance_score(self,
                                       skill: Dict[str, Any],
                                       proposal: Dict[str, Any],
                                       skill_type: str) -> float:
        """スキルと提案の関連性スコアを計算"""
        score = 0.0
        
        # タグマッチング
        skill_tags = [tag.lower() for tag in skill.get("tags", [])]
        proposal_keywords = self._extract_proposal_keywords(proposal)
        
        for keyword in proposal_keywords:
            if keyword in skill_tags:
                score += 2.0
                
        # 説明文の類似度（簡易版）
        skill_desc = skill.get("description", "").lower()
        proposal_desc = proposal.get("description", "").lower()
        
        common_words = set(skill_desc.split()) & set(proposal_desc.split())
        if common_words:
            score += len(common_words) * 0.5
            
        # スキルタイプの一致
        if skill_type in skill.get("name", "").lower():
            score += 3.0
            
        return score
        
    def _extract_proposal_keywords(self, proposal: Dict[str, Any]) -> List[str]:
        """提案からキーワードを抽出"""
        keywords = []
        
        # カテゴリから
        category_keywords = {
            "業務効率化": ["automation", "効率化", "自動化"],
            "顧客体験向上": ["customer", "ux", "体験"],
            "データ分析": ["analysis", "data", "分析"],
            "新規事業": ["innovation", "new", "新規"]
        }
        
        category = proposal.get("category", "")
        if category in category_keywords:
            keywords.extend(category_keywords[category])
            
        # タイトルから重要語を抽出
        title_words = proposal.get("title", "").lower().split()
        keywords.extend([w for w in title_words if len(w) > 3])
        
        return keywords
        
    def _find_similar_pool_skills(self, proposal: Dict[str, Any]) -> List[Dict[str, Any]]:
        """プールから類似のカスタムスキルを検索"""
        similar_skills = []
        
        if not self.pool_skills_dir.exists():
            return similar_skills
            
        # プール内のスキルを検索
        for skill_dir in self.pool_skills_dir.iterdir():
            if skill_dir.is_dir() and (skill_dir / "SKILL.md").exists():
                pool_skill = self._parse_skill_metadata(skill_dir)
                if pool_skill:
                    # 業種や用途が類似しているか判定
                    if self._is_similar_skill(pool_skill, proposal):
                        pool_skill["path"] = skill_dir
                        similar_skills.append(pool_skill)
                        
        return similar_skills[:3]  # 最大3つまで
        
    def _is_similar_skill(self, skill: Dict[str, Any], proposal: Dict[str, Any]) -> bool:
        """スキルと提案の類似性判定"""
        # タグの共通性をチェック
        skill_tags = set(skill.get("tags", []))
        proposal_keywords = set(self._extract_proposal_keywords(proposal))
        
        common_tags = skill_tags & proposal_keywords
        return len(common_tags) >= 2
        
    def _customize_skill(self,
                        proposal: Dict[str, Any],
                        base_skill: Optional[Dict[str, Any]],
                        similar_skills: List[Dict[str, Any]]) -> Dict[str, Any]:
        """
        スキルのカスタマイズ
        """
        # スキル名の生成
        skill_name = self._generate_skill_name(proposal)
        
        # 基本構造
        customized_skill = {
            "name": skill_name,
            "version": "1.0.0",
            "description": f"{proposal['title']}を実現するAgentSkill",
            "author": "AI Advisor System (Auto-generated)",
            "tags": self._generate_skill_tags(proposal),
            "base_skill": base_skill["name"] if base_skill else None,
            "proposal": proposal,
            "scripts": {},
            "references": [],
            "dependencies": []
        }
        
        # ベーススキルがある場合は構造を継承
        if base_skill:
            customized_skill["dependencies"] = base_skill.get("dependencies", [])
            # スクリプトのテンプレートも参考に
            if base_skill.get("path"):
                customized_skill["base_scripts_path"] = base_skill["path"] / "scripts"
                
        # 類似スキルからの学習
        if similar_skills:
            # 共通のタグや依存関係を追加
            for similar in similar_skills:
                customized_skill["tags"].extend(similar.get("tags", []))
                customized_skill["dependencies"].extend(similar.get("dependencies", []))
                
        # 重複除去
        customized_skill["tags"] = list(set(customized_skill["tags"]))
        customized_skill["dependencies"] = list(set(customized_skill["dependencies"]))
        
        # スクリプトの生成
        customized_skill["scripts"] = self._generate_skill_scripts(
            customized_skill, 
            proposal
        )
        
        return customized_skill
        
    def _generate_skill_name(self, proposal: Dict[str, Any]) -> str:
        """スキル名の生成"""
        # 提案タイトルからスキル名を生成
        title = proposal.get("title", "Custom Skill")
        
        # 日本語を英語に変換（簡易版）
        name_mappings = {
            "自動化": "automation",
            "分析": "analysis",
            "最適化": "optimization",
            "生成": "generator",
            "支援": "assistant",
            "管理": "manager",
            "予測": "predictor",
            "チャット": "chatbot",
            "レポート": "reporter"
        }
        
        name = title.lower()
        for jp, en in name_mappings.items():
            name = name.replace(jp, en)
            
        # 特殊文字を除去してケバブケースに
        name = re.sub(r'[^\w\s-]', '', name)
        name = re.sub(r'[-\s]+', '-', name)
        
        # AIプレフィックスを追加
        if not name.startswith("ai-"):
            name = f"ai-{name}"
            
        return name[:50]  # 最大50文字
        
    def _generate_skill_tags(self, proposal: Dict[str, Any]) -> List[str]:
        """スキルのタグ生成"""
        tags = ["auto-generated", "ai-advisor"]
        
        # カテゴリタグ
        category_tags = {
            "業務効率化": ["automation", "efficiency"],
            "顧客体験向上": ["customer-experience", "ux"],
            "データ分析": ["analytics", "data-analysis"],
            "新規事業": ["innovation", "new-business"]
        }
        
        category = proposal.get("category", "")
        if category in category_tags:
            tags.extend(category_tags[category])
            
        # 提案固有のタグ
        tags.extend(self._extract_proposal_keywords(proposal)[:3])
        
        return tags
        
    def _generate_skill_scripts(self,
                              skill: Dict[str, Any],
                              proposal: Dict[str, Any]) -> Dict[str, str]:
        """スキルのスクリプト生成"""
        scripts = {}
        
        # メインスクリプト
        scripts["main.py"] = self._generate_main_script(skill, proposal)
        
        # 設定スクリプト
        scripts["config.py"] = self._generate_config_script(skill)
        
        # ユーティリティスクリプト
        scripts["utils.py"] = self._generate_utils_script(skill)
        
        # requirements.txt
        scripts["requirements.txt"] = self._generate_requirements(skill)
        
        # __init__.py
        scripts["__init__.py"] = f'from .main import {self._to_class_name(skill["name"])}'
        
        return scripts
        
    def _generate_main_script(self, skill: Dict[str, Any], proposal: Dict[str, Any]) -> str:
        """メインスクリプトの生成"""
        class_name = self._to_class_name(skill["name"])
        
        # ベーススキルがある場合はその構造を参考に
        if skill.get("base_scripts_path"):
            base_main_path = skill["base_scripts_path"] / "main.py"
            if base_main_path.exists():
                # ベースコードを読み込んで改変
                return self._adapt_base_script(base_main_path, skill, proposal)
                
        # ベースがない場合はテンプレートから生成
        return f'''#!/usr/bin/env python3
"""
{skill["name"]} - {skill["description"]}
Auto-generated by AI Advisor System
Based on proposal: {proposal["title"]}
"""
import os
import logging
from typing import Dict, Any, List, Optional
from datetime import datetime

# ロギング設定
logging.basicConfig(level=logging.INFO)
logger = logging.getLogger(__name__)


class {class_name}:
    """
    {proposal["description"]}
    
    このスキルは以下の機能を提供します：
    - {proposal.get("expected_benefits", {}).get("primary", "業務効率の向上")}
    - 自動化による作業時間の削減
    - エラー率の低減
    """
    
    def __init__(self, config: Optional[Dict[str, Any]] = None):
        """
        初期化
        
        Args:
            config: 設定パラメータ
        """
        self.config = config or self._get_default_config()
        self.results = {{}}
        logger.info(f"{skill['name']} initialized")
        
    def _get_default_config(self) -> Dict[str, Any]:
        """デフォルト設定の取得"""
        return {{
            "mode": "production",
            "timeout": 300,
            "retry_count": 3,
            "output_format": "json"
        }}
        
    def execute(self, **kwargs) -> Dict[str, Any]:
        """
        メイン実行メソッド
        
        Args:
            **kwargs: 実行パラメータ
            
        Returns:
            実行結果
        """
        try:
            logger.info("Execution started")
            
            # 入力検証
            self._validate_input(kwargs)
            
            # メイン処理
            result = self._process(kwargs)
            
            # 結果の整形
            self.results = self._format_result(result)
            
            logger.info("Execution completed successfully")
            return self.results
            
        except Exception as e:
            logger.error(f"Execution failed: {{str(e)}}")
            raise
            
    def _validate_input(self, params: Dict[str, Any]):
        """入力パラメータの検証"""
        required_params = ["input_data"]  # 必須パラメータ
        
        for param in required_params:
            if param not in params:
                raise ValueError(f"Required parameter '{{param}}' is missing")
                
    def _process(self, params: Dict[str, Any]) -> Dict[str, Any]:
        """
        メイン処理ロジック
        
        このメソッドをカスタマイズして、
        具体的な処理を実装してください
        """
        input_data = params["input_data"]
        
        # ここに具体的な処理を実装
        # 例: データ処理、AI推論、外部API呼び出しなど
        
        processed_data = {{
            "status": "success",
            "processed_at": datetime.now().isoformat(),
            "data": input_data  # 実際の処理結果に置き換える
        }}
        
        return processed_data
        
    def _format_result(self, result: Dict[str, Any]) -> Dict[str, Any]:
        """結果の整形"""
        return {{
            "skill": skill["name"],
            "version": skill["version"],
            "timestamp": datetime.now().isoformat(),
            "result": result,
            "metadata": {{
                "proposal": "{proposal['title']}",
                "category": "{proposal['category']}",
                "expected_benefit": "{proposal.get('expected_benefits', {}).get('primary', '')}"
            }}
        }}


def main():
    """CLIエントリーポイント"""
    import argparse
    
    parser = argparse.ArgumentParser(
        description="{skill['description']}"
    )
    parser.add_argument(
        "input_file",
        help="入力データファイル"
    )
    parser.add_argument(
        "--output",
        default="output.json",
        help="出力ファイル (デフォルト: output.json)"
    )
    parser.add_argument(
        "--config",
        help="設定ファイル"
    )
    
    args = parser.parse_args()
    
    # 設定の読み込み
    config = None
    if args.config:
        import json
        with open(args.config, 'r') as f:
            config = json.load(f)
    
    # スキルの実行
    skill = {class_name}(config)
    
    # 入力データの読み込み
    with open(args.input_file, 'r') as f:
        input_data = json.load(f)
    
    # 実行
    result = skill.execute(input_data=input_data)
    
    # 結果の保存
    with open(args.output, 'w') as f:
        json.dump(result, f, indent=2, ensure_ascii=False)
    
    print(f"Result saved to {{args.output}}")


if __name__ == "__main__":
    main()
'''
        
    def _to_class_name(self, skill_name: str) -> str:
        """スキル名をクラス名に変換"""
        # ai-customer-support -> AiCustomerSupport
        parts = skill_name.split('-')
        return ''.join(part.capitalize() for part in parts)
        
    def _adapt_base_script(self, 
                         base_script_path: Path,
                         skill: Dict[str, Any],
                         proposal: Dict[str, Any]) -> str:
        """ベーススクリプトを改変"""
        # ベースコードを読み込み
        with open(base_script_path, 'r', encoding='utf-8') as f:
            base_code = f.read()
            
        # クラス名とドキュメントを置換
        old_class_name = self._extract_class_name(base_code)
        new_class_name = self._to_class_name(skill["name"])
        
        if old_class_name:
            base_code = base_code.replace(old_class_name, new_class_name)
            
        # ドキュメント文字列を更新
        base_code = self._update_docstrings(base_code, skill, proposal)
        
        return base_code
        
    def _extract_class_name(self, code: str) -> Optional[str]:
        """コードからクラス名を抽出"""
        class_match = re.search(r'class\s+(\w+)\s*\(', code)
        if class_match:
            return class_match.group(1)
        return None
        
    def _update_docstrings(self, code: str, skill: Dict[str, Any], proposal: Dict[str, Any]) -> str:
        """ドキュメント文字列を更新"""
        # モジュールドキュメントを更新
        module_doc = f'''"""
{skill["name"]} - {skill["description"]}
Auto-generated by AI Advisor System
Based on proposal: {proposal["title"]}
Original base skill: {skill.get("base_skill", "None")}
"""'''
        
        # 最初のドキュメント文字列を置換
        code = re.sub(r'^""".*?"""', module_doc, code, count=1, flags=re.DOTALL)
        
        return code
        
    def _generate_config_script(self, skill: Dict[str, Any]) -> str:
        """設定スクリプトの生成"""
        return f'''"""
Configuration for {skill["name"]}
"""
import os
from typing import Dict, Any

# 環境変数からの設定読み込み
ENV = os.getenv("SKILL_ENV", "production")

# 基本設定
BASE_CONFIG = {{
    "name": "{skill['name']}",
    "version": "{skill['version']}",
    "environment": ENV,
    "log_level": "INFO" if ENV == "production" else "DEBUG"
}}

# 環境別設定
ENVIRONMENTS = {{
    "development": {{
        "debug": True,
        "cache_enabled": False,
        "timeout": 60
    }},
    "staging": {{
        "debug": False,
        "cache_enabled": True,
        "timeout": 180
    }},
    "production": {{
        "debug": False,
        "cache_enabled": True,
        "timeout": 300
    }}
}}


def get_config() -> Dict[str, Any]:
    """現在の環境に応じた設定を取得"""
    config = BASE_CONFIG.copy()
    config.update(ENVIRONMENTS.get(ENV, ENVIRONMENTS["production"]))
    return config
'''
        
    def _generate_utils_script(self, skill: Dict[str, Any]) -> str:
        """ユーティリティスクリプトの生成"""
        return f'''"""
Utility functions for {skill["name"]}
"""
import json
import logging
from datetime import datetime
from typing import Dict, Any, List, Optional
from pathlib import Path

logger = logging.getLogger(__name__)


def load_json_file(file_path: str) -> Dict[str, Any]:
    """JSONファイルの読み込み"""
    try:
        with open(file_path, 'r', encoding='utf-8') as f:
            return json.load(f)
    except Exception as e:
        logger.error(f"Failed to load JSON file: {{file_path}} - {{str(e)}}")
        raise


def save_json_file(data: Dict[str, Any], file_path: str):
    """JSONファイルの保存"""
    try:
        Path(file_path).parent.mkdir(parents=True, exist_ok=True)
        with open(file_path, 'w', encoding='utf-8') as f:
            json.dump(data, f, indent=2, ensure_ascii=False)
        logger.info(f"Data saved to {{file_path}}")
    except Exception as e:
        logger.error(f"Failed to save JSON file: {{file_path}} - {{str(e)}}")
        raise


def validate_required_fields(data: Dict[str, Any], required_fields: List[str]):
    """必須フィールドの検証"""
    missing_fields = []
    for field in required_fields:
        if field not in data or data[field] is None:
            missing_fields.append(field)
    
    if missing_fields:
        raise ValueError(f"Missing required fields: {{', '.join(missing_fields)}}")


def format_timestamp(dt: Optional[datetime] = None) -> str:
    """タイムスタンプのフォーマット"""
    if dt is None:
        dt = datetime.now()
    return dt.isoformat()


def safe_get(data: Dict[str, Any], path: str, default: Any = None) -> Any:
    """
    ネストされた辞書から安全に値を取得
    
    Args:
        data: 辞書データ
        path: ドット区切りのパス (e.g., "user.profile.name")
        default: デフォルト値
        
    Returns:
        取得した値またはデフォルト値
    """
    try:
        keys = path.split('.')
        value = data
        for key in keys:
            value = value[key]
        return value
    except (KeyError, TypeError):
        return default


def chunk_list(lst: List[Any], chunk_size: int) -> List[List[Any]]:
    """リストを指定サイズのチャンクに分割"""
    return [lst[i:i + chunk_size] for i in range(0, len(lst), chunk_size)]
'''
        
    def _generate_requirements(self, skill: Dict[str, Any]) -> str:
        """requirements.txtの生成"""
        # 基本的な依存関係
        base_requirements = [
            "requests>=2.28.0",
            "pandas>=1.5.0",
            "numpy>=1.23.0",
            "pyyaml>=6.0",
            "python-dotenv>=0.20.0"
        ]
        
        # スキルの依存関係から追加
        dependencies = skill.get("dependencies", [])
        
        # カテゴリ別の追加依存関係
        category_deps = {
            "data-analysis": ["matplotlib>=3.6.0", "seaborn>=0.12.0"],
            "web-scraping": ["beautifulsoup4>=4.11.0", "selenium>=4.0.0"],
            "nlp": ["transformers>=4.25.0", "torch>=1.13.0"],
            "api": ["fastapi>=0.90.0", "uvicorn>=0.20.0"]
        }
        
        # タグから関連する依存関係を追加
        all_deps = set(base_requirements)
        for tag in skill.get("tags", []):
            if tag in category_deps:
                all_deps.update(category_deps[tag])
                
        # カスタム依存関係を追加
        all_deps.update(dependencies)
        
        return '\n'.join(sorted(all_deps))
        
    def _create_skill_files(self, skill: Dict[str, Any]) -> Path:
        """スキルファイルの作成"""
        skill_dir = self.output_dir / skill["name"]
        skill_dir.mkdir(parents=True, exist_ok=True)
        
        # ディレクトリ構造の作成
        (skill_dir / "scripts").mkdir(exist_ok=True)
        (skill_dir / "references").mkdir(exist_ok=True)
        (skill_dir / "assets").mkdir(exist_ok=True)
        
        # SKILL.mdの作成
        self._create_skill_md(skill_dir, skill)
        
        # スクリプトファイルの作成
        for script_name, script_content in skill["scripts"].items():
            if script_name == "requirements.txt":
                script_path = skill_dir / script_name
            else:
                script_path = skill_dir / "scripts" / script_name
                
            with open(script_path, 'w', encoding='utf-8') as f:
                f.write(script_content)
                
        # README.mdの作成
        self._create_readme(skill_dir, skill)
        
        logger.info(f"Skill files created at: {skill_dir}")
        return skill_dir
        
    def _create_skill_md(self, skill_dir: Path, skill: Dict[str, Any]):
        """SKILL.mdファイルの作成"""
        proposal = skill["proposal"]
        
        content = f"""---
name: {skill["name"]}
version: {skill["version"]}
description: {skill["description"]}
author: {skill["author"]}
tags: {json.dumps(skill["tags"])}
dependencies: {json.dumps(skill.get("dependencies", []))}
base_skill: {skill.get("base_skill", "None")}
created_at: {datetime.now().isoformat()}
---

# {skill["name"]}

## 概要
{skill["description"]}

このスキルは、「{proposal['title']}」の提案に基づいて自動生成されました。

## 主な機能
- {proposal.get('expected_benefits', {}).get('primary', 'プロセスの自動化と効率化')}
- エラー率の削減と品質向上
- リアルタイムモニタリングとレポート生成

## 使用方法

### Pythonライブラリとして使用
```python
from {skill["name"].replace("-", "_")}.scripts.main import {self._to_class_name(skill["name"])}

# スキルのインスタンス化
skill = {self._to_class_name(skill["name"])}()

# 実行
result = skill.execute(
    input_data={{"key": "value"}}
)

print(result)
```

### CLIとして使用
```bash
python -m {skill["name"].replace("-", "_")}.scripts.main input.json --output result.json
```

## 設定
設定は環境変数または設定ファイルで指定できます。

### 環境変数
- `SKILL_ENV`: 実行環境 (development/staging/production)
- `LOG_LEVEL`: ログレベル (DEBUG/INFO/WARNING/ERROR)

### 設定ファイル
`config.json`で詳細な設定が可能です。

## 期待される効果
{self._format_expected_benefits_md(proposal)}

## 技術仕様
- **カテゴリ**: {proposal['category']}
- **実装難易度**: {proposal.get('difficulty', 'medium')}
- **推定実装期間**: {proposal.get('implementation_timeline', '2-3ヶ月')}

## ベーススキル
{f"このスキルは `{skill.get('base_skill')}` をベースに作成されています。" if skill.get('base_skill') else "このスキルは新規に作成されました。"}

## 注意事項
- このスキルは自動生成されたものです。本番環境での使用前に十分なテストを行ってください。
- 必要に応じてコードをカスタマイズしてください。

## ライセンス
[プロジェクトのライセンスに準拠]
"""
        
        with open(skill_dir / "SKILL.md", 'w', encoding='utf-8') as f:
            f.write(content)
            
    def _format_expected_benefits_md(self, proposal: Dict[str, Any]) -> str:
        """期待効果のMarkdownフォーマット"""
        benefits = proposal.get('expected_benefits', {})
        lines = []
        
        if benefits.get('primary'):
            lines.append(f"- **主要効果**: {benefits['primary']}")
            
        if benefits.get('secondary'):
            lines.append("- **副次的効果**:")
            for benefit in benefits['secondary']:
                lines.append(f"  - {benefit}")
                
        return '\n'.join(lines) if lines else "- 業務効率の向上"
        
    def _create_readme(self, skill_dir: Path, skill: Dict[str, Any]):
        """README.mdの作成"""
        content = f"""# {skill["name"]}

{skill["description"]}

## クイックスタート

### インストール
```bash
pip install -r requirements.txt
```

### 基本的な使用方法
```python
from scripts.main import {self._to_class_name(skill["name"])}

skill = {self._to_class_name(skill["name"])}()
result = skill.execute(input_data={{"example": "data"}})
```

## ドキュメント
詳細なドキュメントは [SKILL.md](SKILL.md) を参照してください。

## ライセンス
[プロジェクトのライセンスに準拠]
"""
        
        with open(skill_dir / "README.md", 'w', encoding='utf-8') as f:
            f.write(content)
            
    def _add_skills_to_pool(self):
        """生成したスキルをプールに追加"""
        for skill_info in self.generated_skills:
            if skill_info["pool_candidate"]:
                # プールディレクトリにコピー
                source_path = Path(skill_info["path"])
                pool_path = self.pool_skills_dir / skill_info["name"]
                
                if pool_path.exists():
                    shutil.rmtree(pool_path)
                shutil.copytree(source_path, pool_path)
                
                # メタデータを追加
                metadata_path = pool_path / "pool_metadata.json"
                metadata = {
                    "added_date": datetime.now().isoformat(),
                    "proposal_title": skill_info["proposal_title"],
                    "base_skill": skill_info["base_skill"],
                    "skill_type": skill_info["skill_type"],
                    "usage_count": 0,
                    "rating": 0,
                    "starter_candidate": skill_info["starter_candidate"]
                }
                
                with open(metadata_path, 'w', encoding='utf-8') as f:
                    json.dump(metadata, f, indent=2)
                    
                logger.info(f"Skill added to pool: {skill_info['name']}")
                
    def _evaluate_for_starter(self, skill: Dict[str, Any]) -> bool:
        """スタメン候補として評価"""
        # 評価基準
        # - 汎用性が高い
        # - 複数の業種で使える
        # - 実装がシンプル
        
        generic_tags = ["automation", "analysis", "reporting", "integration"]
        skill_tags = skill.get("tags", [])
        
        generic_score = sum(1 for tag in generic_tags if tag in skill_tags)
        
        return generic_score >= 2
        
    def _load_skill_templates(self) -> Dict[str, str]:
        """スキルテンプレートの読み込み"""
        templates = {}
        
        # 基本的なテンプレートを定義
        # 実際の実装では外部ファイルから読み込むことも可能
        templates["automation"] = "automation_template.py"
        templates["analysis"] = "analysis_template.py"
        templates["integration"] = "integration_template.py"
        
        return templates