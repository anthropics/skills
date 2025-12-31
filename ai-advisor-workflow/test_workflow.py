#!/usr/bin/env python3
"""
AI Advisor Workflow テストスクリプト
実際のURLまたはサンプルデータでワークフローをテスト
"""
import sys
from pathlib import Path
sys.path.insert(0, str(Path(__file__).parent))

from scripts.main import AIAdvisorWorkflow
import json
from datetime import datetime


def test_with_sample_data():
    """サンプルデータでのテスト"""
    print("=== AI Advisor Workflow サンプル実行 ===\n")
    
    # サンプルURL（実際のURLに置き換え可能）
    sample_urls = [
        "https://example-company.com",
        "https://example-company.com/services",
        "https://example-company.com/products", 
        "https://example-company.com/about"
    ]
    
    # 出力ディレクトリ
    output_dir = f"./output/test_{datetime.now().strftime('%Y%m%d_%H%M%S')}"
    
    print(f"分析対象URL:")
    for url in sample_urls:
        print(f"  - {url}")
    print(f"\n出力ディレクトリ: {output_dir}")
    print("\n処理を開始します...")
    
    try:
        # ワークフローの実行
        workflow = AIAdvisorWorkflow()
        result = workflow.execute(
            client_urls=sample_urls,
            output_dir=output_dir,
            generate_skills=True
        )
        
        # 結果の表示
        print("\n=== 実行結果 ===")
        print(f"ステータス: {result['status']}")
        print(f"分析URL数: {len(result['client_urls'])}")
        print(f"業種: {result['industry_analysis']['industry']['main_category']}")
        print(f"AI準備度: {result['industry_analysis']['ai_readiness']['level']}")
        print(f"生成提案数: {len(result['proposals'])}")
        print(f"生成スキル数: {len(result['generated_skills'])}")
        
        # 主要な提案を表示
        print("\n=== 優先度の高いAI活用提案 ===")
        high_priority_proposals = [p for p in result['proposals'] if p.get('priority') == '高']
        for i, proposal in enumerate(high_priority_proposals[:3], 1):
            print(f"\n{i}. {proposal['title']}")
            print(f"   カテゴリ: {proposal['category']}")
            print(f"   期待効果: {proposal['expected_benefits']['primary']}")
            if 'roi_estimation' in proposal:
                print(f"   ROI（3年）: {proposal['roi_estimation']['roi_3years']}")
        
        # 生成されたドキュメント
        print("\n=== 生成されたドキュメント ===")
        for doc_type, doc_path in result['documents'].items():
            print(f"- {doc_type}: {doc_path}")
        
        # 生成されたスキル
        if result['generated_skills']:
            print("\n=== 生成されたAgentSkills ===")
            for skill in result['generated_skills']:
                print(f"- {skill['name']}")
                print(f"  ベース: {skill['base_skill']}")
                print(f"  タイプ: {skill['skill_type']}")
                print(f"  パス: {skill['path']}")
        
        print(f"\n✅ ワークフローが正常に完了しました。")
        print(f"詳細は {output_dir} をご確認ください。")
        
    except Exception as e:
        print(f"\n❌ エラーが発生しました: {str(e)}")
        import traceback
        traceback.print_exc()


def test_with_real_url(url: str):
    """実際のURLでのテスト"""
    print(f"=== 実URLでのテスト: {url} ===\n")
    
    output_dir = f"./output/real_{datetime.now().strftime('%Y%m%d_%H%M%S')}"
    
    try:
        workflow = AIAdvisorWorkflow()
        result = workflow.execute(
            client_urls=url,
            output_dir=output_dir,
            generate_skills=True
        )
        
        print(f"✅ 分析完了: {result['industry_analysis']['company_name']}")
        print(f"業種: {result['industry_analysis']['industry']['main_category']}")
        print(f"出力: {output_dir}")
        
    except Exception as e:
        print(f"❌ エラー: {str(e)}")


def create_sample_config():
    """サンプル設定ファイルの作成"""
    config = {
        "web_extractor": {
            "timeout": 30,
            "max_pages": 20,
            "follow_links": True
        },
        "analysis": {
            "industry_classification": True,
            "business_process_extraction": True,
            "competitor_analysis": False
        },
        "proposal": {
            "categories": ["業務効率化", "顧客体験向上"],
            "max_proposals_per_category": 2,
            "include_roi_calculation": True
        },
        "skill_generation": {
            "generate_tests": True,
            "include_documentation": True
        }
    }
    
    config_path = Path("./sample_config.json")
    with open(config_path, 'w', encoding='utf-8') as f:
        json.dump(config, f, indent=2, ensure_ascii=False)
    
    print(f"サンプル設定ファイルを作成しました: {config_path}")
    return str(config_path)


if __name__ == "__main__":
    import argparse
    
    parser = argparse.ArgumentParser(description="AI Advisor Workflow テスト")
    parser.add_argument(
        "--url",
        help="テストに使用する実際のURL"
    )
    parser.add_argument(
        "--create-config",
        action="store_true",
        help="サンプル設定ファイルを作成"
    )
    
    args = parser.parse_args()
    
    if args.create_config:
        create_sample_config()
    elif args.url:
        test_with_real_url(args.url)
    else:
        test_with_sample_data()