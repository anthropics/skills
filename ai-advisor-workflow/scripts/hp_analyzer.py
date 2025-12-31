#!/usr/bin/env python3
"""
HP分析モジュール - 既存のweb-content-extractorとweb-test-automationを活用
"""
import os
import sys
import json
import logging
from pathlib import Path
from typing import Dict, Any, List, Optional
from urllib.parse import urlparse, urljoin
import requests
from bs4 import BeautifulSoup
import re

logger = logging.getLogger('hp_analyzer')

# 既存スキルのパスを追加
SKILLS_DIR = Path(__file__).resolve().parents[3]
sys.path.insert(0, str(SKILLS_DIR))


class HPAnalyzer:
    """Webサイト分析クラス"""
    
    def __init__(self):
        self.visited_urls = set()
        self.extracted_data = {
            "pages": [],
            "company_info": {},
            "services": [],
            "products": [],
            "contact_info": {},
            "additional_resources": {},  # 追加リソース情報
            "departments": [],  # 部門・事業部情報
            "case_studies": []  # 事例・実績
        }
        
    def extract_content_multi(self, urls: List[str], config: Dict[str, Any]) -> Dict[str, Any]:
        """
        複数のWebサイトから情報を抽出
        
        Args:
            urls: 対象URLリスト
            config: 抽出設定
            
        Returns:
            抽出されたコンテンツ
        """
        try:
            # メインURLと追加URLを分離
            main_url = urls[0]
            additional_urls = urls[1:] if len(urls) > 1 else []
            
            logger.info(f"メインURL: {main_url}")
            if additional_urls:
                logger.info(f"追加URL: {len(additional_urls)}件")
            
            # 既存のweb-content-extractorがあれば使用
            if self._check_existing_skill("web-content-extractor"):
                return self._use_web_content_extractor_multi(urls, config)
            
            # フォールバック: 独自実装
            return self._extract_with_beautifulsoup_multi(urls, config)
            
        except Exception as e:
            logger.error(f"コンテンツ抽出エラー: {str(e)}")
            return self._get_default_content_multi(urls)
            
    def _check_existing_skill(self, skill_name: str) -> bool:
        """既存スキルの存在確認"""
        skill_path = SKILLS_DIR / "skills" / skill_name
        return skill_path.exists()
        
    def _use_web_content_extractor_multi(self, urls: List[str], config: Dict[str, Any]) -> Dict[str, Any]:
        """既存のweb-content-extractorを使用（複数URL対応）"""
        try:
            # web-content-extractorのインポートを試みる
            from web_content_extractor.scripts.main import WebContentExtractor
            
            extractor = WebContentExtractor(config)
            
            # 各URLを処理
            all_results = []
            for url in urls:
                result = extractor.extract(url)
                all_results.append(result)
            
            # 結果を統合して統一フォーマットに変換
            return self._normalize_extractor_results_multi(all_results, urls)
            
        except ImportError:
            logger.warning("web-content-extractorのインポートに失敗")
            return self._extract_with_beautifulsoup_multi(urls, config)
            
    def _extract_with_beautifulsoup_multi(self, urls: List[str], config: Dict[str, Any]) -> Dict[str, Any]:
        """BeautifulSoupを使用した複数URL抽出実装"""
        logger.info(f"BeautifulSoupで{len(urls)}件のURLを抽出開始")
        
        # メインURLの処理
        main_url = urls[0]
        main_content = self._fetch_page(main_url)
        if not main_content:
            return self._get_default_content_multi(urls)
            
        # メインページの解析
        self._parse_main_page(main_url, main_content)
        
        # 追加URLの処理
        for url in urls[1:]:
            logger.info(f"追加URL処理: {url}")
            content = self._fetch_page(url)
            if content:
                self._parse_additional_resource(url, content)
        
        # 関連ページのクロール（設定に応じて）
        if config.get("follow_links", True):
            max_pages_per_url = config.get("max_pages", 10) // max(len(urls), 1)
            for url in urls:
                self._crawl_related_pages(url, max_pages_per_url)
                
        # 結果の整形
        return self._format_extraction_result_multi(urls)
        
    def _fetch_page(self, url: str) -> Optional[str]:
        """ページコンテンツの取得"""
        try:
            headers = {
                'User-Agent': 'Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36'
            }
            response = requests.get(url, headers=headers, timeout=30)
            response.raise_for_status()
            return response.text
        except Exception as e:
            logger.error(f"ページ取得エラー ({url}): {str(e)}")
            return None
            
    def _parse_main_page(self, url: str, html_content: str):
        """メインページの解析"""
        soup = BeautifulSoup(html_content, 'html.parser')
        
        # タイトルと説明の抽出
        title = soup.find('title')
        self.extracted_data["title"] = title.text.strip() if title else ""
        
        meta_desc = soup.find('meta', attrs={'name': 'description'})
        self.extracted_data["description"] = meta_desc.get('content', '') if meta_desc else ""
        
        # 会社情報の抽出
        self._extract_company_info(soup)
        
        # サービス・製品情報の抽出
        self._extract_services_and_products(soup)
        
        # 連絡先情報の抽出
        self._extract_contact_info(soup)
        
        # 事例・実績の抽出
        self._extract_case_studies(soup)
        
        # ページデータの保存
        self.extracted_data["pages"].append({
            "url": url,
            "title": self.extracted_data["title"],
            "content_summary": self._summarize_content(soup),
            "page_type": "main"
        })
        
    def _extract_company_info(self, soup: BeautifulSoup):
        """会社情報の抽出"""
        # 会社概要を含むセクションを探す
        company_sections = soup.find_all(['div', 'section'], 
                                       class_=re.compile(r'(company|about|overview)', re.I))
        
        for section in company_sections:
            text = section.get_text(strip=True)
            
            # 会社名
            if not self.extracted_data["company_info"].get("name"):
                name_match = re.search(r'(株式会社|会社名|Company)[\s:：]*([^\n]+)', text)
                if name_match:
                    self.extracted_data["company_info"]["name"] = name_match.group(2).strip()
                    
            # 設立年
            year_match = re.search(r'(設立|創業)[\s:：]*(\d{4}年)', text)
            if year_match:
                self.extracted_data["company_info"]["established"] = year_match.group(2)
                
            # 事業内容
            if "事業内容" in text or "Business" in text:
                self.extracted_data["company_info"]["business"] = self._extract_list_items(section)
                
    def _extract_services_and_products(self, soup: BeautifulSoup):
        """サービス・製品情報の抽出"""
        # サービス/製品セクションを探す
        service_keywords = ['service', 'product', 'solution', 'サービス', '製品', 'ソリューション']
        
        for keyword in service_keywords:
            sections = soup.find_all(['div', 'section'], 
                                   class_=re.compile(keyword, re.I))
            
            for section in sections:
                items = self._extract_list_items(section)
                if items:
                    self.extracted_data["services"].extend(items)
                    
        # 重複削除
        self.extracted_data["services"] = list(set(self.extracted_data["services"]))
        
    def _extract_contact_info(self, soup: BeautifulSoup):
        """連絡先情報の抽出"""
        # メールアドレス
        email_pattern = r'[a-zA-Z0-9._%+-]+@[a-zA-Z0-9.-]+\.[a-zA-Z]{2,}'
        emails = re.findall(email_pattern, str(soup))
        if emails:
            self.extracted_data["contact_info"]["email"] = emails[0]
            
        # 電話番号
        phone_pattern = r'(?:TEL|Tel|電話|Phone)[\s:：]*([0-9\-\(\)]+)'
        phone_match = re.search(phone_pattern, str(soup))
        if phone_match:
            self.extracted_data["contact_info"]["phone"] = phone_match.group(1)
            
    def _extract_list_items(self, element) -> List[str]:
        """リスト項目の抽出"""
        items = []
        
        # ul/ol リストを探す
        lists = element.find_all(['ul', 'ol'])
        for lst in lists:
            items.extend([li.get_text(strip=True) for li in lst.find_all('li')])
            
        # h3/h4などの見出しも収集
        headers = element.find_all(['h3', 'h4', 'h5'])
        items.extend([h.get_text(strip=True) for h in headers])
        
        return [item for item in items if len(item) > 2]  # 短すぎる項目は除外
        
    def _summarize_content(self, soup: BeautifulSoup) -> str:
        """コンテンツのサマリー作成"""
        # 主要なテキストコンテンツを抽出
        main_content = soup.find(['main', 'article']) or soup.find('body')
        if not main_content:
            return ""
            
        text = main_content.get_text(separator=' ', strip=True)
        # 最初の500文字を返す
        return text[:500] + "..." if len(text) > 500 else text
        
    def _crawl_related_pages(self, base_url: str, max_pages: int):
        """関連ページのクロール"""
        self.visited_urls.add(base_url)
        to_visit = self._get_internal_links(base_url)
        
        pages_crawled = 1
        while to_visit and pages_crawled < max_pages:
            url = to_visit.pop(0)
            if url in self.visited_urls:
                continue
                
            logger.info(f"クロール中: {url}")
            content = self._fetch_page(url)
            if content:
                self._parse_page(url, content)
                self.visited_urls.add(url)
                pages_crawled += 1
                
                # 新しいリンクを追加
                new_links = self._get_internal_links(url)
                to_visit.extend([link for link in new_links if link not in self.visited_urls])
                
    def _get_internal_links(self, url: str) -> List[str]:
        """内部リンクの取得"""
        content = self._fetch_page(url)
        if not content:
            return []
            
        soup = BeautifulSoup(content, 'html.parser')
        parsed_url = urlparse(url)
        base_domain = f"{parsed_url.scheme}://{parsed_url.netloc}"
        
        links = []
        for a in soup.find_all('a', href=True):
            href = a['href']
            full_url = urljoin(url, href)
            
            # 同一ドメインのリンクのみ
            if full_url.startswith(base_domain):
                links.append(full_url)
                
        return list(set(links))[:20]  # 最大20リンクまで
        
    def _parse_page(self, url: str, content: str):
        """個別ページの解析"""
        soup = BeautifulSoup(content, 'html.parser')
        title = soup.find('title')
        
        self.extracted_data["pages"].append({
            "url": url,
            "title": title.text.strip() if title else "",
            "content_summary": self._summarize_content(soup)
        })
        
    def _parse_additional_resource(self, url: str, content: str):
        """追加リソースの解析"""
        soup = BeautifulSoup(content, 'html.parser')
        
        # URLの種別を判定
        url_lower = url.lower()
        page_type = "general"
        
        if "product" in url_lower or "製品" in url_lower:
            page_type = "product"
            self._extract_product_details(soup)
        elif "service" in url_lower or "サービス" in url_lower:
            page_type = "service"
            self._extract_service_details(soup)
        elif "about" in url_lower or "会社" in url_lower:
            page_type = "about"
            self._extract_detailed_company_info(soup)
        elif "case" in url_lower or "事例" in url_lower:
            page_type = "case_study"
            self._extract_case_studies(soup)
        elif "recruit" in url_lower or "採用" in url_lower:
            page_type = "recruitment"
            self._extract_recruitment_info(soup)
        
        # ページ情報を保存
        self.extracted_data["pages"].append({
            "url": url,
            "title": soup.find('title').text.strip() if soup.find('title') else "",
            "content_summary": self._summarize_content(soup),
            "page_type": page_type
        })
        
        # 追加リソース情報を記録
        if page_type not in self.extracted_data["additional_resources"]:
            self.extracted_data["additional_resources"][page_type] = []
        self.extracted_data["additional_resources"][page_type].append(url)
    
    def _extract_product_details(self, soup: BeautifulSoup):
        """製品詳細の抽出"""
        products = self._extract_list_items(soup)
        self.extracted_data["products"].extend(products)
        
    def _extract_service_details(self, soup: BeautifulSoup):
        """サービス詳細の抽出"""
        services = self._extract_list_items(soup)
        self.extracted_data["services"].extend(services)
        
    def _extract_detailed_company_info(self, soup: BeautifulSoup):
        """詳細な会社情報の抽出"""
        # 部門情報
        departments = soup.find_all(['div', 'section'], 
                                  class_=re.compile(r'(department|部門|事業)', re.I))
        for dept in departments:
            dept_info = self._extract_list_items(dept)
            if dept_info:
                self.extracted_data["departments"].extend(dept_info)
                
    def _extract_recruitment_info(self, soup: BeautifulSoup):
        """採用情報の抽出（組織文化の理解に役立つ）"""
        if "culture" not in self.extracted_data["company_info"]:
            self.extracted_data["company_info"]["culture"] = []
            
        culture_keywords = ["社風", "ビジョン", "ミッション", "価値観", "culture", "vision"]
        for keyword in culture_keywords:
            elements = soup.find_all(text=re.compile(keyword, re.I))
            for elem in elements:
                parent = elem.parent
                if parent:
                    text = parent.get_text(strip=True)
                    if len(text) > 20:
                        self.extracted_data["company_info"]["culture"].append(text[:200])
                        
    def _extract_case_studies(self, soup: BeautifulSoup):
        """事例・実績の抽出"""
        case_sections = soup.find_all(['div', 'section', 'article'], 
                                    class_=re.compile(r'(case|事例|実績)', re.I))
        
        for section in case_sections:
            case_info = {
                "title": "",
                "industry": "",
                "challenge": "",
                "solution": "",
                "result": ""
            }
            
            # タイトル抽出
            title = section.find(['h2', 'h3', 'h4'])
            if title:
                case_info["title"] = title.get_text(strip=True)
                
            # 内容から情報抽出
            text = section.get_text()
            
            # 業種・課題・解決策・結果を抽出
            patterns = {
                "industry": r"業種[・:]　*(.*?)。",
                "challenge": r"課題[・:]　*(.*?)。",
                "solution": r"解決[・:]　*(.*?)。",
                "result": r"結果[・:]　*(.*?)。"
            }
            
            for key, pattern in patterns.items():
                match = re.search(pattern, text)
                if match:
                    case_info[key] = match.group(1)
                    
            if case_info["title"] or case_info["challenge"]:
                self.extracted_data["case_studies"].append(case_info)
    
    def _format_extraction_result_multi(self, urls: List[str]) -> Dict[str, Any]:
        """複数URL抽出結果のフォーマット"""
        # 業種の推定
        industry = self._estimate_industry()
        
        # サービスと製品の統合・重複除去
        all_services = list(set(self.extracted_data["services"] + self.extracted_data["products"]))
        
        return {
            "urls": urls,
            "main_url": urls[0],
            "title": self.extracted_data.get("title", ""),
            "description": self.extracted_data.get("description", ""),
            "content": {
                "company_overview": self.extracted_data["company_info"],
                "services": all_services[:20],  # 上位20件
                "departments": self.extracted_data["departments"][:10],
                "industry": industry,
                "contact": self.extracted_data["contact_info"],
                "case_studies": self.extracted_data["case_studies"][:10]
            },
            "pages": self.extracted_data["pages"][:50],  # 上位50ページ
            "pages_analyzed": len(self.extracted_data["pages"]),
            "additional_resources": self.extracted_data["additional_resources"],
            "extracted_at": self._get_timestamp()
        }
        
    def _estimate_industry(self) -> str:
        """業種の推定"""
        # サービス内容から業種を推定
        services_text = ' '.join(self.extracted_data["services"]).lower()
        
        industry_keywords = {
            "情報通信業": ["システム", "ソフトウェア", "IT", "web", "アプリ"],
            "製造業": ["製造", "生産", "工場", "製品開発"],
            "小売業": ["販売", "店舗", "EC", "通販"],
            "サービス業": ["サービス", "コンサルティング", "支援"],
            "医療・福祉": ["医療", "病院", "介護", "福祉"],
            "教育": ["教育", "学習", "研修", "スクール"]
        }
        
        for industry, keywords in industry_keywords.items():
            if any(keyword in services_text for keyword in keywords):
                return industry
                
        return "その他"
        
    def _normalize_extractor_results_multi(self, results: List[Dict[str, Any]], urls: List[str]) -> Dict[str, Any]:
        """既存extractorの結果を統一フォーマットに変換（複数URL対応）"""
        # メイン結果から基本情報を取得
        main_result = results[0] if results else {}
        
        # 全結果からページとサービス情報を統合
        all_pages = []
        all_services = []
        for result in results:
            all_pages.extend(result.get("pages", []))
            content = result.get("content", {})
            if isinstance(content, dict) and "services" in content:
                all_services.extend(content["services"])
        
        return {
            "urls": urls,
            "main_url": urls[0] if urls else "",
            "title": main_result.get("title", ""),
            "description": main_result.get("meta_description", ""),
            "content": {
                "company_overview": main_result.get("content", {}).get("company_overview", {}),
                "services": list(set(all_services))[:20],
                "departments": [],
                "industry": main_result.get("content", {}).get("industry", "不明"),
                "contact": main_result.get("content", {}).get("contact", {}),
                "case_studies": []
            },
            "pages": all_pages[:50],
            "pages_analyzed": len(all_pages),
            "additional_resources": {},
            "extracted_at": self._get_timestamp()
        }
        
    def _get_default_content_multi(self, urls: List[str]) -> Dict[str, Any]:
        """デフォルトコンテンツ（エラー時）"""
        return {
            "urls": urls,
            "main_url": urls[0] if urls else "",
            "title": "Unknown Company",
            "description": "",
            "content": {
                "company_overview": {"name": "不明", "business": ["情報取得失敗"]},
                "services": ["Webサイトから情報を取得できませんでした"],
                "departments": [],
                "industry": "不明",
                "contact": {},
                "case_studies": []
            },
            "pages": [],
            "pages_analyzed": 0,
            "additional_resources": {},
            "extracted_at": self._get_timestamp(),
            "error": True
        }
        
    def _get_timestamp(self) -> str:
        """現在のタイムスタンプ取得"""
        from datetime import datetime
        return datetime.now().isoformat()