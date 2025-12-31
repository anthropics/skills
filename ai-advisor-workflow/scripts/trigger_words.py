#!/usr/bin/env python3
"""
AI Advisor Workflow トリガーワード管理
特定のキーワードやフレーズでワークフローを起動する機能
"""
import re
from typing import Dict, List, Optional, Tuple, Any
from dataclasses import dataclass
from enum import Enum


class TriggerType(Enum):
    """トリガータイプの定義"""
    ANALYZE = "analyze"           # 分析実行
    QUICK_CHECK = "quick_check"   # 簡易チェック
    PROPOSAL = "proposal"         # 提案書生成
    SKILL_GEN = "skill_gen"      # スキル生成
    FULL_WORKFLOW = "full"       # フルワークフロー


@dataclass
class TriggerMatch:
    """トリガーマッチ結果"""
    trigger_type: TriggerType
    confidence: float
    urls: List[str]
    options: Dict[str, Any]
    matched_phrase: str


class TriggerWordProcessor:
    """トリガーワード処理クラス"""
    
    def __init__(self):
        # トリガーワード定義
        self.triggers = {
            TriggerType.ANALYZE: {
                "keywords": [
                    "分析して", "調査して", "調べて", "analyze", "research",
                    "見て", "確認して", "チェックして", "check"
                ],
                "patterns": [
                    r"(.+?)の(HP|ホームページ|サイト|ウェブ)を?(分析|調査|調べ|見)",
                    r"(分析|調査|analyze|check)\s*(.+)",
                    r"(.+?)について(調べ|分析|調査)"
                ]
            },
            TriggerType.PROPOSAL: {
                "keywords": [
                    "提案書", "提案を", "proposal", "プロポーザル",
                    "提案して", "提案作成", "提案書作って"
                ],
                "patterns": [
                    r"(.+?)の?(AI活用)?提案書?を?(作成|作って|生成)",
                    r"(提案|proposal).*(作成|create|generate)",
                    r"(.+?)向けの?提案"
                ]
            },
            TriggerType.SKILL_GEN: {
                "keywords": [
                    "スキル作成", "skill", "AgentSkill", "スキル生成",
                    "実装", "コード生成"
                ],
                "patterns": [
                    r"(.+?)の?スキルを?(作成|生成|作って)",
                    r"(skill|AgentSkill).*(generate|create|作成)",
                    r"(.+?)を?実装"
                ]
            },
            TriggerType.FULL_WORKFLOW: {
                "keywords": [
                    "フルワークフロー", "全部", "すべて", "full workflow",
                    "分析から提案まで", "最初から最後まで", "一連の流れ"
                ],
                "patterns": [
                    r"(.+?)の?(フル|全部|すべて)",
                    r"(全体|一連)の?(ワークフロー|流れ)",
                    r"分析から.*(提案|スキル)まで"
                ]
            },
            TriggerType.QUICK_CHECK: {
                "keywords": [
                    "ざっくり", "簡単に", "クイック", "quick", "概要",
                    "さっと", "軽く"
                ],
                "patterns": [
                    r"(ざっくり|簡単に|さっと).*(見|チェック|分析)",
                    r"(quick|クイック).*(check|チェック)",
                    r"(.+?)の?概要"
                ]
            }
        }
        
        # URL抽出パターン
        self.url_pattern = re.compile(
            r'https?://(?:www\.)?[-a-zA-Z0-9@:%._\+~#=]{1,256}\.[a-zA-Z0-9()]{1,6}\b(?:[-a-zA-Z0-9()@:%_\+.~#?&/=]*)'
        )
        
        # 会社名からURL推測のパターン
        self.company_patterns = [
            (r'(.+?)株式会社', lambda x: f"https://{x}.co.jp"),
            (r'株式会社(.+)', lambda x: f"https://{x}.co.jp"),
            (r'(.+?)(会社|コーポレーション|corp|inc)', lambda x: f"https://{x}.com"),
            (r'(.+?)商店', lambda x: f"https://{x}.jp")
        ]
        
    def process(self, input_text: str) -> Optional[TriggerMatch]:
        """
        入力テキストを処理してトリガーマッチを返す
        
        Args:
            input_text: ユーザー入力テキスト
            
        Returns:
            トリガーマッチ結果
        """
        # テキストの正規化
        normalized_text = self._normalize_text(input_text)
        
        # URL抽出
        urls = self._extract_urls(input_text)
        
        # トリガータイプの判定
        trigger_type, confidence, matched_phrase = self._identify_trigger_type(normalized_text)
        
        if not trigger_type:
            return None
            
        # URLが見つからない場合、会社名から推測
        if not urls:
            urls = self._infer_urls_from_text(input_text)
            
        # オプションの抽出
        options = self._extract_options(input_text, trigger_type)
        
        return TriggerMatch(
            trigger_type=trigger_type,
            confidence=confidence,
            urls=urls,
            options=options,
            matched_phrase=matched_phrase
        )
        
    def _normalize_text(self, text: str) -> str:
        """テキストの正規化"""
        # 全角を半角に
        text = text.replace('　', ' ')
        # 複数スペースを単一に
        text = re.sub(r'\s+', ' ', text)
        # 小文字化
        return text.lower().strip()
        
    def _extract_urls(self, text: str) -> List[str]:
        """URLの抽出"""
        urls = self.url_pattern.findall(text)
        
        # 重複を除去して順序を保持
        seen = set()
        unique_urls = []
        for url in urls:
            if url not in seen:
                seen.add(url)
                unique_urls.append(url)
                
        return unique_urls
        
    def _identify_trigger_type(self, text: str) -> Tuple[Optional[TriggerType], float, str]:
        """トリガータイプの識別"""
        best_match = None
        best_confidence = 0.0
        best_phrase = ""
        
        for trigger_type, config in self.triggers.items():
            # キーワードマッチング
            keyword_score = 0
            for keyword in config["keywords"]:
                if keyword in text:
                    keyword_score += 1
                    
            # パターンマッチング
            pattern_score = 0
            matched_phrase = ""
            for pattern in config["patterns"]:
                match = re.search(pattern, text)
                if match:
                    pattern_score += 2  # パターンマッチはより重要
                    matched_phrase = match.group(0)
                    break
                    
            # 総合スコア計算
            total_score = keyword_score + pattern_score
            confidence = min(total_score / 3.0, 1.0)  # 正規化
            
            if confidence > best_confidence:
                best_match = trigger_type
                best_confidence = confidence
                best_phrase = matched_phrase or text[:50]
                
        # 閾値チェック
        if best_confidence >= 0.3:
            return best_match, best_confidence, best_phrase
            
        return None, 0.0, ""
        
    def _infer_urls_from_text(self, text: str) -> List[str]:
        """テキストから会社名を抽出してURLを推測"""
        urls = []
        
        for pattern, url_generator in self.company_patterns:
            match = re.search(pattern, text)
            if match:
                company_name = match.group(1).strip()
                # 特殊文字を除去
                company_name = re.sub(r'[^\w\s-]', '', company_name)
                company_name = company_name.replace(' ', '').lower()
                
                if company_name:
                    # 複数のURL候補を生成
                    urls.extend([
                        url_generator(company_name),
                        f"https://www.{company_name}.com",
                        f"https://www.{company_name}.jp",
                        f"https://{company_name}.co.jp"
                    ])
                    break
                    
        # 重複除去
        return list(dict.fromkeys(urls))[:4]  # 最大4つまで
        
    def _extract_options(self, text: str, trigger_type: TriggerType) -> Dict[str, Any]:
        """オプションの抽出"""
        options = {
            "generate_skills": True,
            "include_roi": True,
            "quick_mode": False,
            "language": "ja"
        }
        
        # クイックモードの判定
        if trigger_type == TriggerType.QUICK_CHECK:
            options["quick_mode"] = True
            options["generate_skills"] = False
            
        # スキル生成の判定
        if "スキル不要" in text or "no skills" in text:
            options["generate_skills"] = False
            
        # ROI計算の判定
        if "ROI不要" in text or "no roi" in text:
            options["include_roi"] = False
            
        # 言語設定
        if "english" in text or "英語" in text:
            options["language"] = "en"
            
        # カテゴリ指定
        categories = []
        if "効率化" in text:
            categories.append("業務効率化")
        if "顧客" in text or "カスタマー" in text:
            categories.append("顧客体験向上")
        if "分析" in text or "データ" in text:
            categories.append("データ分析・意思決定支援")
        if "新規" in text or "イノベーション" in text:
            categories.append("新規事業・サービス開発")
            
        if categories:
            options["proposal_categories"] = categories
            
        return options
        
    def get_usage_examples(self) -> List[Dict[str, str]]:
        """使用例を取得"""
        return [
            {
                "input": "https://example.com を分析して、AI活用提案を作成してください",
                "description": "URLを指定してフルワークフロー実行"
            },
            {
                "input": "株式会社サンプルのホームページを調査して",
                "description": "会社名からURL推測して分析"
            },
            {
                "input": "ざっくりhttps://example.comをチェックして",
                "description": "クイックチェックモード"
            },
            {
                "input": "効率化に特化した提案書を作成 https://example.com",
                "description": "カテゴリを限定した提案"
            },
            {
                "input": "https://example.com https://example.com/services を分析してスキルまで生成",
                "description": "複数URL指定でスキル生成まで実行"
            },
            {
                "input": "スキル不要でhttps://example.comの提案書だけ作って",
                "description": "提案書のみ生成（スキル生成スキップ）"
            }
        ]


def create_workflow_command(trigger_match: TriggerMatch) -> Dict[str, Any]:
    """
    トリガーマッチからワークフローコマンドを生成
    
    Args:
        trigger_match: トリガーマッチ結果
        
    Returns:
        ワークフロー実行用のコマンド設定
    """
    command = {
        "urls": trigger_match.urls,
        "workflow_type": trigger_match.trigger_type.value,
        "options": trigger_match.options,
        "confidence": trigger_match.confidence
    }
    
    # ワークフロータイプに応じた設定
    if trigger_match.trigger_type == TriggerType.QUICK_CHECK:
        command["options"]["max_pages"] = 10
        command["options"]["follow_links"] = False
        command["options"]["generate_skills"] = False
        
    elif trigger_match.trigger_type == TriggerType.PROPOSAL:
        command["options"]["generate_skills"] = False
        command["options"]["focus"] = "proposal"
        
    elif trigger_match.trigger_type == TriggerType.SKILL_GEN:
        command["options"]["focus"] = "skills"
        
    return command


# CLI用のメイン関数
def main():
    """トリガーワードのテストとデモ"""
    import json
    
    processor = TriggerWordProcessor()
    
    print("=== AI Advisor Workflow トリガーワード ===\n")
    print("使用例:")
    for example in processor.get_usage_examples():
        print(f"- 「{example['input']}」")
        print(f"  → {example['description']}\n")
        
    print("\n入力待機中... (終了: exit または quit)\n")
    
    while True:
        try:
            user_input = input(">>> ").strip()
            
            if user_input.lower() in ["exit", "quit", "終了"]:
                print("終了します。")
                break
                
            if not user_input:
                continue
                
            # トリガー処理
            match = processor.process(user_input)
            
            if match:
                print(f"\n✅ トリガー検出!")
                print(f"  タイプ: {match.trigger_type.value}")
                print(f"  信頼度: {match.confidence:.0%}")
                print(f"  URL: {match.urls}")
                print(f"  オプション: {json.dumps(match.options, ensure_ascii=False, indent=2)}")
                
                # ワークフローコマンド生成
                command = create_workflow_command(match)
                print(f"\n実行コマンド:")
                print(json.dumps(command, ensure_ascii=False, indent=2))
            else:
                print("\n❌ トリガーワードが検出されませんでした。")
                print("ヒント: 「分析して」「提案書作成」「スキル生成」などを含めてください。")
                
        except KeyboardInterrupt:
            print("\n\n終了します。")
            break
        except Exception as e:
            print(f"\nエラー: {e}")


if __name__ == "__main__":
    main()