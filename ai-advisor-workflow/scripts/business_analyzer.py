#!/usr/bin/env python3
"""
業種・業務分析モジュール
抽出されたWeb情報から業種特性と業務内容を分析
"""
import logging
from typing import Dict, Any, List, Optional
from datetime import datetime
import re

logger = logging.getLogger('business_analyzer')


class BusinessAnalyzer:
    """業種・業務内容分析クラス"""
    
    def __init__(self):
        # 業種分類マスタ（日本標準産業分類を参考）
        self.industry_master = {
            "情報通信業": {
                "keywords": ["IT", "システム", "ソフトウェア", "Web", "アプリ", "データ", "クラウド", "AI"],
                "sub_categories": ["ソフトウェア業", "情報処理サービス業", "インターネット関連"],
                "common_challenges": [
                    "開発効率の向上",
                    "品質管理の強化",
                    "セキュリティ対策",
                    "人材不足への対応"
                ]
            },
            "製造業": {
                "keywords": ["製造", "生産", "工場", "製品", "品質", "機械", "部品", "組立"],
                "sub_categories": ["機械製造業", "電子部品製造業", "食品製造業", "化学工業"],
                "common_challenges": [
                    "生産効率の向上",
                    "品質管理の自動化",
                    "在庫最適化",
                    "予防保全"
                ]
            },
            "小売業": {
                "keywords": ["販売", "店舗", "商品", "顧客", "EC", "通販", "ショップ"],
                "sub_categories": ["総合小売業", "専門小売業", "無店舗小売業"],
                "common_challenges": [
                    "顧客体験の向上",
                    "在庫管理の最適化",
                    "需要予測の精度向上",
                    "オムニチャネル対応"
                ]
            },
            "サービス業": {
                "keywords": ["サービス", "コンサル", "支援", "代行", "管理", "運営"],
                "sub_categories": ["専門サービス業", "技術サービス業", "生活関連サービス業"],
                "common_challenges": [
                    "サービス品質の標準化",
                    "顧客満足度向上",
                    "業務効率化",
                    "人材育成"
                ]
            },
            "医療・福祉": {
                "keywords": ["医療", "病院", "クリニック", "介護", "福祉", "健康", "診療"],
                "sub_categories": ["医療業", "保健衛生", "社会保険・福祉・介護事業"],
                "common_challenges": [
                    "医療サービスの質向上",
                    "業務負荷の軽減",
                    "患者満足度向上",
                    "コンプライアンス対応"
                ]
            }
        }
        
        # 業務プロセステンプレート
        self.business_process_templates = {
            "営業・マーケティング": ["リード獲得", "顧客管理", "提案作成", "契約管理"],
            "人事・労務": ["採用管理", "勤怠管理", "評価管理", "教育研修"],
            "経理・財務": ["請求管理", "支払管理", "予算管理", "決算処理"],
            "カスタマーサポート": ["問い合わせ対応", "クレーム処理", "FAQ管理", "顧客満足度調査"],
            "製造・生産": ["生産計画", "品質管理", "在庫管理", "設備保全"],
            "研究開発": ["研究管理", "特許管理", "プロジェクト管理", "技術文書管理"]
        }
        
    def analyze(self, web_data: Dict[str, Any], config: Dict[str, Any]) -> Dict[str, Any]:
        """
        業種・業務内容の分析
        
        Args:
            web_data: Web抽出データ
            config: 分析設定
            
        Returns:
            分析結果
        """
        logger.info("業種・業務分析開始")
        
        # 業種の特定
        industry_info = self._identify_industry(web_data)
        
        # 業務プロセスの抽出
        business_processes = self._extract_business_processes(web_data, industry_info)
        
        # 企業規模の推定
        company_scale = self._estimate_company_scale(web_data)
        
        # 技術成熟度の評価
        tech_maturity = self._assess_tech_maturity(web_data)
        
        # 競合分析（設定による）
        competitor_analysis = None
        if config.get("competitor_analysis", False):
            competitor_analysis = self._analyze_competitors(industry_info)
        
        # 分析結果のまとめ
        analysis_result = {
            "company_name": self._extract_company_name(web_data),
            "industry": industry_info,
            "business_processes": business_processes,
            "company_scale": company_scale,
            "tech_maturity": tech_maturity,
            "key_challenges": self._identify_key_challenges(
                industry_info, 
                business_processes, 
                tech_maturity
            ),
            "ai_readiness": self._assess_ai_readiness(tech_maturity, company_scale),
            "analysis_timestamp": datetime.now().isoformat()
        }
        
        if competitor_analysis:
            analysis_result["competitor_analysis"] = competitor_analysis
            
        logger.info("業種・業務分析完了")
        return analysis_result
        
    def _identify_industry(self, web_data: Dict[str, Any]) -> Dict[str, Any]:
        """業種の特定"""
        content = web_data.get("content", {})
        services = content.get("services", [])
        overview = content.get("company_overview", {})
        
        # 全テキストを結合して分析
        all_text = ' '.join([
            web_data.get("title", ""),
            web_data.get("description", ""),
            ' '.join(services),
            str(overview.get("business", ""))
        ]).lower()
        
        # 各業種のスコアリング
        industry_scores = {}
        for industry, info in self.industry_master.items():
            score = sum(1 for keyword in info["keywords"] if keyword.lower() in all_text)
            if score > 0:
                industry_scores[industry] = score
                
        # 最高スコアの業種を選択
        if industry_scores:
            main_industry = max(industry_scores, key=industry_scores.get)
            industry_info = self.industry_master[main_industry].copy()
            industry_info["main_category"] = main_industry
            industry_info["confidence_score"] = industry_scores[main_industry] / len(self.industry_master[main_industry]["keywords"])
        else:
            # デフォルト業種
            main_industry = "サービス業"
            industry_info = self.industry_master[main_industry].copy()
            industry_info["main_category"] = main_industry
            industry_info["confidence_score"] = 0.3
            
        # サブカテゴリの特定
        industry_info["identified_subcategory"] = self._identify_subcategory(
            all_text, 
            industry_info["sub_categories"]
        )
        
        return industry_info
        
    def _identify_subcategory(self, text: str, subcategories: List[str]) -> Optional[str]:
        """サブカテゴリの特定"""
        for subcategory in subcategories:
            if subcategory.replace("業", "").lower() in text:
                return subcategory
        return subcategories[0] if subcategories else None
        
    def _extract_business_processes(self, 
                                  web_data: Dict[str, Any], 
                                  industry_info: Dict[str, Any]) -> List[Dict[str, Any]]:
        """業務プロセスの抽出"""
        services = web_data.get("content", {}).get("services", [])
        pages = web_data.get("pages", [])
        
        # ページコンテンツからプロセス関連キーワードを抽出
        all_content = ' '.join([
            ' '.join(services),
            ' '.join([p.get("content_summary", "") for p in pages])
        ])
        
        identified_processes = []
        
        for process_category, keywords in self.business_process_templates.items():
            relevance_score = 0
            found_keywords = []
            
            for keyword in keywords:
                if keyword in all_content:
                    relevance_score += 1
                    found_keywords.append(keyword)
                    
            if relevance_score > 0:
                identified_processes.append({
                    "category": process_category,
                    "relevance_score": relevance_score / len(keywords),
                    "identified_keywords": found_keywords,
                    "potential_ai_applications": self._get_ai_applications(process_category)
                })
                
        # 業種特有のプロセスを追加
        industry_specific_processes = self._get_industry_specific_processes(
            industry_info["main_category"]
        )
        identified_processes.extend(industry_specific_processes)
        
        # 関連度でソート
        identified_processes.sort(key=lambda x: x["relevance_score"], reverse=True)
        
        return identified_processes[:6]  # 上位6プロセスを返す
        
    def _get_ai_applications(self, process_category: str) -> List[str]:
        """プロセスカテゴリ別のAI活用例"""
        ai_applications = {
            "営業・マーケティング": [
                "リード スコアリング",
                "顧客セグメンテーション",
                "需要予測"
            ],
            "人事・労務": [
                "採用候補者スクリーニング",
                "従業員エンゲージメント分析",
                "スキルマッチング"
            ],
            "経理・財務": [
                "請求書自動処理",
                "異常検知",
                "キャッシュフロー予測"
            ],
            "カスタマーサポート": [
                "チャットボット対応",
                "感情分析",
                "FAQ自動生成"
            ],
            "製造・生産": [
                "品質検査自動化",
                "予知保全",
                "生産最適化"
            ],
            "研究開発": [
                "特許分析",
                "技術トレンド予測",
                "実験データ分析"
            ]
        }
        
        return ai_applications.get(process_category, ["プロセス自動化", "データ分析", "予測モデル構築"])
        
    def _get_industry_specific_processes(self, industry: str) -> List[Dict[str, Any]]:
        """業種特有のプロセス"""
        industry_processes = {
            "情報通信業": [
                {"category": "開発・運用", "relevance_score": 0.8, "identified_keywords": ["開発", "運用"]}
            ],
            "製造業": [
                {"category": "品質管理", "relevance_score": 0.8, "identified_keywords": ["品質", "検査"]}
            ],
            "小売業": [
                {"category": "在庫管理", "relevance_score": 0.8, "identified_keywords": ["在庫", "商品"]}
            ],
            "医療・福祉": [
                {"category": "診療支援", "relevance_score": 0.8, "identified_keywords": ["診療", "患者"]}
            ]
        }
        
        processes = industry_processes.get(industry, [])
        for process in processes:
            process["potential_ai_applications"] = self._get_ai_applications(process["category"])
            
        return processes
        
    def _estimate_company_scale(self, web_data: Dict[str, Any]) -> Dict[str, str]:
        """企業規模の推定"""
        content_text = str(web_data.get("content", {})).lower()
        
        # 規模を示すキーワードの検索
        scale_indicators = {
            "large": ["大企業", "上場", "グローバル", "global", "1000名以上", "billion"],
            "medium": ["中堅", "中企業", "100名", "200名", "300名", "全国展開"],
            "small": ["中小", "小規模", "ベンチャー", "スタートアップ", "startup", "10名", "20名"]
        }
        
        for scale, keywords in scale_indicators.items():
            if any(keyword in content_text for keyword in keywords):
                return {
                    "scale": scale,
                    "label": {"large": "大企業", "medium": "中堅企業", "small": "中小企業"}[scale]
                }
                
        # デフォルト
        return {"scale": "medium", "label": "中堅企業"}
        
    def _assess_tech_maturity(self, web_data: Dict[str, Any]) -> Dict[str, Any]:
        """技術成熟度の評価"""
        content_text = str(web_data).lower()
        
        # 技術関連キーワードのチェック
        tech_indicators = {
            "advanced": ["ai", "機械学習", "iot", "blockchain", "自動化", "デジタル"],
            "intermediate": ["システム", "データベース", "クラウド", "api", "セキュリティ"],
            "basic": ["ホームページ", "メール", "エクセル", "手作業"]
        }
        
        scores = {}
        for level, keywords in tech_indicators.items():
            scores[level] = sum(1 for keyword in keywords if keyword in content_text)
            
        # 最高スコアのレベルを選択
        if scores["advanced"] > 0:
            maturity_level = "advanced"
        elif scores["intermediate"] > scores["basic"]:
            maturity_level = "intermediate"
        else:
            maturity_level = "basic"
            
        return {
            "level": maturity_level,
            "label": {
                "advanced": "先進的",
                "intermediate": "中程度",
                "basic": "基礎的"
            }[maturity_level],
            "indicators": [k for k, v in scores.items() if v > 0]
        }
        
    def _identify_key_challenges(self, 
                               industry_info: Dict[str, Any],
                               business_processes: List[Dict[str, Any]],
                               tech_maturity: Dict[str, Any]) -> List[Dict[str, str]]:
        """主要課題の特定"""
        challenges = []
        
        # 業種共通の課題
        common_challenges = industry_info.get("common_challenges", [])
        for challenge in common_challenges[:3]:  # 上位3つ
            challenges.append({
                "challenge": challenge,
                "priority": "high",
                "category": "業種特有"
            })
            
        # 技術成熟度に基づく課題
        if tech_maturity["level"] == "basic":
            challenges.append({
                "challenge": "デジタル化の推進",
                "priority": "high",
                "category": "技術基盤"
            })
        elif tech_maturity["level"] == "intermediate":
            challenges.append({
                "challenge": "データ活用の高度化",
                "priority": "medium",
                "category": "技術基盤"
            })
            
        # プロセス別の課題
        for process in business_processes[:2]:  # 上位2プロセス
            challenges.append({
                "challenge": f"{process['category']}の効率化",
                "priority": "medium",
                "category": "業務プロセス"
            })
            
        return challenges
        
    def _assess_ai_readiness(self, 
                           tech_maturity: Dict[str, Any],
                           company_scale: Dict[str, str]) -> Dict[str, Any]:
        """AI導入準備度の評価"""
        # スコアリング
        readiness_score = 0
        
        # 技術成熟度によるスコア
        maturity_scores = {"advanced": 3, "intermediate": 2, "basic": 1}
        readiness_score += maturity_scores.get(tech_maturity["level"], 1)
        
        # 企業規模によるスコア
        scale_scores = {"large": 3, "medium": 2, "small": 1}
        readiness_score += scale_scores.get(company_scale["scale"], 1)
        
        # 準備度レベルの判定
        if readiness_score >= 5:
            readiness_level = "high"
            recommendation = "本格的なAI導入プロジェクトの推進が可能"
        elif readiness_score >= 3:
            readiness_level = "medium"
            recommendation = "パイロットプロジェクトから開始を推奨"
        else:
            readiness_level = "low"
            recommendation = "まずは基盤整備とPoC（概念実証）から開始"
            
        return {
            "level": readiness_level,
            "score": readiness_score,
            "recommendation": recommendation,
            "next_steps": self._get_readiness_next_steps(readiness_level)
        }
        
    def _get_readiness_next_steps(self, readiness_level: str) -> List[str]:
        """準備度に応じた次のステップ"""
        steps = {
            "high": [
                "AI戦略の策定",
                "大規模プロジェクトの企画",
                "専門チームの組成"
            ],
            "medium": [
                "パイロットプロジェクトの選定",
                "データ基盤の整備",
                "AI人材の育成"
            ],
            "low": [
                "AI基礎知識の習得",
                "小規模PoCの実施",
                "データ収集体制の構築"
            ]
        }
        
        return steps.get(readiness_level, [])
        
    def _analyze_competitors(self, industry_info: Dict[str, Any]) -> Dict[str, Any]:
        """競合分析（簡易版）"""
        # 実際の実装では外部APIやデータベースを使用
        return {
            "analysis_note": "詳細な競合分析には追加の市場調査が必要です",
            "industry_trends": [
                "AI/自動化の導入加速",
                "DXへの投資増加",
                "顧客体験の重視"
            ],
            "competitive_factors": [
                "技術力",
                "サービス品質",
                "価格競争力"
            ]
        }
        
    def _extract_company_name(self, web_data: Dict[str, Any]) -> str:
        """会社名の抽出"""
        # タイトルから抽出を試みる
        title = web_data.get("title", "")
        if title:
            # 一般的なパターンから会社名を抽出
            patterns = [
                r'株式会社[\s]*([^\s|｜|\-|－]+)',
                r'([^\s|｜|\-|－]+)[\s]*株式会社',
                r'^([^|｜\-－]+?)[\s]*[|｜\-－]'
            ]
            
            for pattern in patterns:
                match = re.search(pattern, title)
                if match:
                    return match.group(1).strip()
                    
        # company_overviewから取得
        company_info = web_data.get("content", {}).get("company_overview", {})
        if company_info.get("name"):
            return company_info["name"]
            
        return "不明"