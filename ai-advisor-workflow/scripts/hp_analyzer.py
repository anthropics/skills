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
            "contact_info": {}
        }
        
    def extract_content(self, url: str, config: Dict[str, Any]) -> Dict[str, Any]:
        """
        Webサイトから情報を抽出
        
        Args:
            url: 対象URL
            config: 抽出設定
            
        Returns:
            抽出されたコンテンツ
        """
        try:
            # 既存のweb-content-extractorがあれば使用
            if self._check_existing_skill("web-content-extractor"):
                return self._use_web_content_extractor(url, config)
            
            # フォールバック: 独自実装
            return self._extract_with_beautifulsoup(url, config)
            
        except Exception as e:
            logger.error(f"コンテンツ抽出エラー: {str(e)}")
            return self._get_default_content(url)
            
    def _check_existing_skill(self, skill_name: str) -> bool:
        """既存スキルの存在確認"""
        skill_path = SKILLS_DIR / "skills" / skill_name
        return skill_path.exists()
        
    def _use_web_content_extractor(self, url: str, config: Dict[str, Any]) -> Dict[str, Any]:
        """既存のweb-content-extractorを使用"""
        try:
            # web-content-extractorのインポートを試みる
            from web_content_extractor.scripts.main import WebContentExtractor
            
            extractor = WebContentExtractor(config)
            result = extractor.extract(url)
            
            # 結果を統一フォーマットに変換
            return self._normalize_extractor_result(result)
            
        except ImportError:
            logger.warning("web-content-extractorのインポートに失敗")
            return self._extract_with_beautifulsoup(url, config)
            
    def _extract_with_beautifulsoup(self, url: str, config: Dict[str, Any]) -> Dict[str, Any]:
        """BeautifulSoupを使用した独自抽出実装"""
        logger.info(f"BeautifulSoupで抽出開始: {url}")
        
        # メインページの取得
        main_content = self._fetch_page(url)
        if not main_content:
            return self._get_default_content(url)
            
        # メインページの解析
        self._parse_main_page(url, main_content)
        
        # 関連ページのクロール（設定に応じて）
        if config.get("follow_links", True):
            self._crawl_related_pages(url, config.get("max_pages", 10))
            
        # 結果の整形
        return self._format_extraction_result(url)
        
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
        
        # ページデータの保存
        self.extracted_data["pages"].append({
            "url": url,
            "title": self.extracted_data["title"],
            "content_summary": self._summarize_content(soup)
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
        
    def _format_extraction_result(self, url: str) -> Dict[str, Any]:
        """抽出結果のフォーマット"""
        # 業種の推定
        industry = self._estimate_industry()
        
        return {
            "url": url,
            "title": self.extracted_data.get("title", ""),
            "description": self.extracted_data.get("description", ""),
            "content": {
                "company_overview": self.extracted_data["company_info"],
                "services": self.extracted_data["services"][:10],  # 上位10件
                "industry": industry,
                "contact": self.extracted_data["contact_info"]
            },
            "pages": self.extracted_data["pages"][:20],  # 上位20ページ
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
        
    def _normalize_extractor_result(self, result: Dict[str, Any]) -> Dict[str, Any]:
        """既存extractorの結果を統一フォーマットに変換"""
        return {
            "url": result.get("url", ""),
            "title": result.get("title", ""),
            "description": result.get("meta_description", ""),
            "content": result.get("content", {}),
            "pages": result.get("pages", []),
            "extracted_at": self._get_timestamp()
        }
        
    def _get_default_content(self, url: str) -> Dict[str, Any]:
        """デフォルトコンテンツ（エラー時）"""
        return {
            "url": url,
            "title": "Unknown Company",
            "description": "",
            "content": {
                "company_overview": {"name": "不明", "business": ["情報取得失敗"]},
                "services": ["Webサイトから情報を取得できませんでした"],
                "industry": "不明",
                "contact": {}
            },
            "pages": [],
            "extracted_at": self._get_timestamp(),
            "error": True
        }
        
    def _get_timestamp(self) -> str:
        """現在のタイムスタンプ取得"""
        from datetime import datetime
        return datetime.now().isoformat()