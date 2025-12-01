#!/usr/bin/env python3
"""
株式会社けんけん マスタートリガー実装
v3.3 - パラレル実行対応版
"""

import json
import os
from datetime import datetime
from typing import Dict, List, Optional, Tuple
import concurrent.futures
import sys

class WorkflowTrigger:
    """ワークフローのマスタートリガー管理クラス"""
    
    def __init__(self):
        self.triggers = {
            "起きろ": self.contract_phase,
            "月締め": self.execution_phase,
            "フル実行": self.full_execution,
        }
        self.parallel_triggers = {
            "起きろ×": self.contract_phase_parallel,
            "月締め×": self.execution_phase_parallel,
            "フル実行×": self.full_execution_parallel,
        }
        self.output_dir = "outputs"
        
    def detect_trigger(self, input_text: str) -> Tuple[str, Optional[int]]:
        """トリガーの検出と並列数の抽出"""
        input_lower = input_text.lower()
        
        # パラレル実行の検出
        for trigger, func in self.parallel_triggers.items():
            if trigger in input_text:
                # 並列数を抽出（例: 起きろ×3 → 3）
                try:
                    parts = input_text.split("×")
                    if len(parts) > 1:
                        parallel_count = int(parts[1].strip().split()[0])
                        return trigger, parallel_count
                except:
                    pass
                    
        # 単一実行の検出
        for trigger, func in self.triggers.items():
            if trigger in input_text:
                return trigger, 1
                
        return None, 0
    
    def contract_phase(self, company_info: Dict) -> Dict:
        """契約フェーズの実行（単一企業）"""
        print(f"\n🔥 契約フェーズを開始: {company_info['name']}")
        
        results = {
            "company": company_info['name'],
            "phase": "契約",
            "steps": []
        }
        
        # Step 0: 補助金確認
        print("📍 Step 0: 補助金確認中...")
        subsidy_info = self._check_subsidies(company_info)
        results["steps"].append({
            "step": 0,
            "name": "補助金確認",
            "status": "完了",
            "output": subsidy_info
        })
        
        # Step 1: 見積書作成
        print("📍 Step 1: 見積書作成中...")
        quotation_files = self._create_quotation(company_info, subsidy_info)
        results["steps"].append({
            "step": 1,
            "name": "見積書作成",
            "status": "完了",
            "files": quotation_files
        })
        
        # Step 2: NDA作成
        print("📍 Step 2: NDA作成中...")
        nda_file = self._create_nda(company_info)
        results["steps"].append({
            "step": 2,
            "name": "NDA作成",
            "status": "完了",
            "files": [nda_file]
        })
        
        # Step 3: 業務委託契約書作成
        print("📍 Step 3: 業務委託契約書作成中...")
        contract_file = self._create_contract(company_info)
        results["steps"].append({
            "step": 3,
            "name": "契約書作成",
            "status": "完了",
            "files": [contract_file]
        })
        
        # Step 4: WBS/ガントチャート作成
        print("📍 Step 4: WBS/ガントチャート作成中...")
        gantt_file = self._create_gantt(company_info)
        results["steps"].append({
            "step": 4,
            "name": "WBS作成",
            "status": "完了",
            "files": [gantt_file]
        })
        
        print(f"✅ 契約フェーズ完了: {company_info['name']}")
        return results
    
    def execution_phase(self, company_info: Dict) -> Dict:
        """実行フェーズの実行（単一企業）"""
        print(f"\n🔥 実行フェーズを開始: {company_info['name']}")
        
        results = {
            "company": company_info['name'],
            "phase": "実行",
            "steps": []
        }
        
        # Step 5: 日報集計
        print("📍 Step 5: 日報データ確認・集計中...")
        daily_report_summary = self._aggregate_daily_reports(company_info)
        results["steps"].append({
            "step": 5,
            "name": "日報集計",
            "status": "完了",
            "output": daily_report_summary
        })
        
        # Step 6: 月次レポート作成
        print("📍 Step 6: 月次レポート作成中...")
        monthly_report_file = self._create_monthly_report(company_info, daily_report_summary)
        results["steps"].append({
            "step": 6,
            "name": "月次レポート",
            "status": "完了",
            "files": [monthly_report_file]
        })
        
        # Step 7: 請求書作成
        print("📍 Step 7: 請求書作成中...")
        invoice_files = self._create_invoice(company_info)
        results["steps"].append({
            "step": 7,
            "name": "請求書作成",
            "status": "完了",
            "files": invoice_files
        })
        
        print(f"✅ 実行フェーズ完了: {company_info['name']}")
        return results
    
    def full_execution(self, company_info: Dict) -> Dict:
        """フル実行（契約＋実行フェーズ）"""
        print(f"\n🔥 フル実行を開始: {company_info['name']}")
        
        # 契約フェーズ
        contract_results = self.contract_phase(company_info)
        
        # 実行フェーズ
        execution_results = self.execution_phase(company_info)
        
        # 結果をマージ
        return {
            "company": company_info['name'],
            "phase": "フル実行",
            "contract_phase": contract_results,
            "execution_phase": execution_results
        }
    
    def contract_phase_parallel(self, companies: List[Dict]) -> List[Dict]:
        """契約フェーズの並列実行"""
        print(f"\n🔥 契約フェーズ並列実行: {len(companies)}社")
        
        with concurrent.futures.ThreadPoolExecutor(max_workers=10) as executor:
            futures = [executor.submit(self.contract_phase, company) for company in companies]
            results = [future.result() for future in concurrent.futures.as_completed(futures)]
        
        self._save_batch_summary("契約", results)
        return results
    
    def execution_phase_parallel(self, companies: List[Dict]) -> List[Dict]:
        """実行フェーズの並列実行"""
        print(f"\n🔥 実行フェーズ並列実行: {len(companies)}社")
        
        with concurrent.futures.ThreadPoolExecutor(max_workers=20) as executor:
            futures = [executor.submit(self.execution_phase, company) for company in companies]
            results = [future.result() for future in concurrent.futures.as_completed(futures)]
        
        self._save_batch_summary("実行", results)
        return results
    
    def full_execution_parallel(self, companies: List[Dict]) -> List[Dict]:
        """フル実行の並列実行"""
        print(f"\n🔥 フル実行並列実行: {len(companies)}社")
        
        with concurrent.futures.ThreadPoolExecutor(max_workers=5) as executor:
            futures = [executor.submit(self.full_execution, company) for company in companies]
            results = [future.result() for future in concurrent.futures.as_completed(futures)]
        
        self._save_batch_summary("フル実行", results)
        return results
    
    # === スキル呼び出しのモック関数 ===
    # 実際の実装では、各スキルのAPIやスクリプトを呼び出す
    
    def _check_subsidies(self, company_info: Dict) -> Dict:
        """補助金確認（jgrants-mcp）"""
        # TODO: 実際のjgrants-mcp呼び出し
        return {
            "subsidies": [
                {
                    "name": "IT導入補助金2025",
                    "amount": "最大450万円",
                    "rate": "2/3",
                    "deadline": "2026-03-31"
                }
            ]
        }
    
    def _create_quotation(self, company_info: Dict, subsidy_info: Dict) -> List[str]:
        """見積書作成（billing-documents）"""
        # TODO: 実際のbilling-documentsスキル呼び出し
        date_str = datetime.now().strftime("%Y%m%d")
        return [
            f"quotation_{company_info['name']}_{date_str}.xlsx",
            f"quotation_{company_info['name']}_{date_str}.pdf"
        ]
    
    def _create_nda(self, company_info: Dict) -> str:
        """NDA作成（nda-generator）"""
        # TODO: 実際のnda-generatorスキル呼び出し
        date_str = datetime.now().strftime("%Y%m%d")
        return f"nda_{company_info['name']}_{date_str}.docx"
    
    def _create_contract(self, company_info: Dict) -> str:
        """契約書作成（consulting-contract-generator）"""
        # TODO: 実際のconsulting-contract-generatorスキル呼び出し
        date_str = datetime.now().strftime("%Y%m%d")
        return f"contract_{company_info['name']}_{date_str}.docx"
    
    def _create_gantt(self, company_info: Dict) -> str:
        """ガントチャート作成（gantt-chart-generator）"""
        # TODO: 実際のgantt-chart-generatorスキル呼び出し
        date_str = datetime.now().strftime("%Y%m%d")
        return f"gantt_{company_info['name']}_{date_str}.xlsx"
    
    def _aggregate_daily_reports(self, company_info: Dict) -> Dict:
        """日報集計（daily-report-voice）"""
        # TODO: 実際のdaily-report-voiceスキル呼び出し
        return {
            "total_days": 20,
            "total_hours": 160,
            "main_activities": ["開発", "打ち合わせ", "レビュー"]
        }
    
    def _create_monthly_report(self, company_info: Dict, daily_summary: Dict) -> str:
        """月次レポート作成（monthly-report-generator）"""
        # TODO: 実際のmonthly-report-generatorスキル呼び出し
        month_str = datetime.now().strftime("%Y%m")
        return f"monthly_report_{company_info['name']}_{month_str}.docx"
    
    def _create_invoice(self, company_info: Dict) -> List[str]:
        """請求書作成（billing-documents）"""
        # TODO: 実際のbilling-documentsスキル呼び出し
        month_str = datetime.now().strftime("%Y%m")
        return [
            f"invoice_{company_info['name']}_{month_str}.xlsx",
            f"invoice_{company_info['name']}_{month_str}.pdf"
        ]
    
    def _save_batch_summary(self, phase: str, results: List[Dict]):
        """バッチ処理のサマリー保存"""
        date_str = datetime.now().strftime("%Y%m%d_%H%M%S")
        summary_file = f"{self.output_dir}/summary_batch_{phase}_{date_str}.json"
        
        os.makedirs(self.output_dir, exist_ok=True)
        
        with open(summary_file, 'w', encoding='utf-8') as f:
            json.dump({
                "phase": phase,
                "timestamp": datetime.now().isoformat(),
                "total_companies": len(results),
                "results": results
            }, f, ensure_ascii=False, indent=2)
        
        print(f"\n📊 処理サマリーを保存: {summary_file}")


def main():
    """メイン実行関数"""
    trigger = WorkflowTrigger()
    
    # コマンドライン引数またはインタラクティブ入力
    if len(sys.argv) > 1:
        command = " ".join(sys.argv[1:])
    else:
        print("🤖 株式会社けんけん ワークフロートリガー v3.3")
        print("📝 使用可能なトリガー:")
        print("   - 起きろ（契約フェーズ）")
        print("   - 月締め（実行フェーズ）")
        print("   - フル実行（全フェーズ）")
        print("   - 起きろ×3（3社並列）")
        print("   - 月締め×5（5社並列）")
        print("   - フル実行×2（2社並列）")
        command = input("\n👉 トリガーを入力: ")
    
    # トリガー検出
    trigger_type, count = trigger.detect_trigger(command)
    
    if not trigger_type:
        print("❌ 有効なトリガーが見つかりません")
        return
    
    # TODO: 実際の実装では、ここで企業情報を収集
    # 今回はサンプルデータを使用
    
    if count > 1:
        # パラレル実行
        print(f"\n🚀 {count}社分の情報を収集します...")
        companies = []
        for i in range(count):
            companies.append({
                "name": f"企業{i+1}",
                "business": "IT導入支援",
                "amount": 200000 + (i * 50000),
                "period": "3ヶ月"
            })
        
        # パラレル実行
        if "起きろ" in trigger_type:
            trigger.contract_phase_parallel(companies)
        elif "月締め" in trigger_type:
            trigger.execution_phase_parallel(companies)
        elif "フル実行" in trigger_type:
            trigger.full_execution_parallel(companies)
    else:
        # 単一実行
        company = {
            "name": "合同会社大吉",
            "business": "生成AIアドバイザリー",
            "amount": 300000,
            "period": "3ヶ月"
        }
        
        if trigger_type == "起きろ":
            trigger.contract_phase(company)
        elif trigger_type == "月締め":
            trigger.execution_phase(company)
        elif trigger_type == "フル実行":
            trigger.full_execution(company)
    
    print("\n✨ 処理が完了しました！")


if __name__ == "__main__":
    main()