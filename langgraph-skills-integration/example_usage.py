"""
使用示例 - 演示如何使用 LangGraph + DeepSeek + Skills 系统
"""
import os
from langgraph_agent import SkillAgent


def example_1_pdf_operations():
    """示例 1: PDF 操作"""
    print("\n" + "="*70)
    print("示例 1: PDF 操作")
    print("="*70)
    
    agent = SkillAgent(
        skills_path="../",
        deepseek_api_key=os.getenv("DEEPSEEK_API_KEY", "your-api-key")
    )
    
    # PDF 合并
    query = "我有两个 PDF 文件 doc1.pdf 和 doc2.pdf，帮我合并成一个文件"
    result = agent.run(query)
    print(f"\n结果: {result}")


def example_2_gif_creation():
    """示例 2: GIF 创建"""
    print("\n" + "="*70)
    print("示例 2: Slack GIF 创建")
    print("="*70)
    
    agent = SkillAgent(
        skills_path="../",
        deepseek_api_key=os.getenv("DEEPSEEK_API_KEY", "your-api-key")
    )
    
    # 创建动画 GIF
    query = "创建一个 Slack emoji GIF，显示一个心形图标脉动的效果"
    result = agent.run(query)
    print(f"\n结果: {result}")


def example_3_document_processing():
    """示例 3: 文档处理"""
    print("\n" + "="*70)
    print("示例 3: 文档处理")
    print("="*70)
    
    agent = SkillAgent(
        skills_path="../",
        deepseek_api_key=os.getenv("DEEPSEEK_API_KEY", "your-api-key")
    )
    
    # DOCX 操作
    query = "从 Word 文档中提取所有表格数据并保存为 Excel"
    result = agent.run(query)
    print(f"\n结果: {result}")


def example_4_custom_workflow():
    """示例 4: 自定义工作流"""
    print("\n" + "="*70)
    print("示例 4: 自定义工作流 - 组合多个技能")
    print("="*70)
    
    agent = SkillAgent(
        skills_path="../",
        deepseek_api_key=os.getenv("DEEPSEEK_API_KEY", "your-api-key")
    )
    
    # 复杂任务：处理多个文档
    query = """
    帮我完成以下任务：
    1. 从 report.pdf 中提取所有表格
    2. 将表格数据保存为 Excel
    3. 为这个报告创建一个封面页的 PDF
    """
    result = agent.run(query)
    print(f"\n结果: {result}")


def example_5_skill_discovery():
    """示例 5: 技能发现和查询"""
    print("\n" + "="*70)
    print("示例 5: 技能发现")
    print("="*70)
    
    from skill_discovery import SkillDiscovery
    
    # 发现所有技能
    discovery = SkillDiscovery("../")
    skills = discovery.discover_all_skills()
    
    print(f"\n发现 {len(skills)} 个技能:")
    for name, skill in skills.items():
        print(f"\n• {name}")
        print(f"  描述: {skill.description}")
        if skill.has_scripts:
            print(f"  包含脚本: ✓")
        if skill.has_references:
            print(f"  包含参考: ✓")
        if skill.has_assets:
            print(f"  包含资源: ✓")
    
    # 搜索特定技能
    print("\n" + "-"*70)
    print("搜索 'pdf' 相关技能:")
    pdf_skills = discovery.search_skills("pdf")
    for skill in pdf_skills:
        print(f"  - {skill.name}: {skill.description}")


def example_6_direct_skill_usage():
    """示例 6: 直接使用技能内容"""
    print("\n" + "="*70)
    print("示例 6: 直接加载和使用技能")
    print("="*70)
    
    from skill_discovery import SkillDiscovery
    from skill_loader import SkillLoader
    
    # 发现和加载
    discovery = SkillDiscovery("../")
    skills = discovery.discover_all_skills()
    
    if "pdf" in skills:
        loader = SkillLoader("../")
        pdf_skill = loader.load_skill(skills["pdf"])
        
        print(f"\n技能: {pdf_skill.metadata.name}")
        print(f"描述: {pdf_skill.metadata.description}")
        
        # 获取可用脚本
        if pdf_skill.scripts:
            print(f"\n可用脚本 ({len(pdf_skill.scripts)}):")
            for script_name in pdf_skill.scripts.keys():
                print(f"  - {script_name}")
        
        # 获取参考文档
        if pdf_skill.references:
            print(f"\n可用参考文档 ({len(pdf_skill.references)}):")
            for ref_name in pdf_skill.references.keys():
                print(f"  - {ref_name}")
        
        # 格式化上下文（供 LLM 使用）
        context = loader.format_skill_context(pdf_skill)
        print(f"\n上下文长度: {len(context)} 字符")
        print(f"前 200 字符预览:\n{context[:200]}...")


def example_7_error_handling():
    """示例 7: 错误处理"""
    print("\n" + "="*70)
    print("示例 7: 错误处理和回退")
    print("="*70)
    
    agent = SkillAgent(
        skills_path="../",
        deepseek_api_key=os.getenv("DEEPSEEK_API_KEY", "your-api-key")
    )
    
    # 尝试一个可能没有对应技能的请求
    query = "帮我预测明天的股票价格"
    result = agent.run(query)
    print(f"\n结果: {result}")


def main():
    """运行所有示例"""
    examples = [
        ("技能发现", example_5_skill_discovery),
        ("直接技能使用", example_6_direct_skill_usage),
        # 以下示例需要有效的 DeepSeek API 密钥
        # ("PDF 操作", example_1_pdf_operations),
        # ("GIF 创建", example_2_gif_creation),
        # ("文档处理", example_3_document_processing),
        # ("自定义工作流", example_4_custom_workflow),
        # ("错误处理", example_7_error_handling),
    ]
    
    print("\n" + "="*70)
    print("LangGraph + DeepSeek + Skills 集成示例")
    print("="*70)
    
    for name, func in examples:
        try:
            func()
        except Exception as e:
            print(f"\n❌ {name} 示例失败: {e}")
    
    print("\n" + "="*70)
    print("示例运行完成")
    print("="*70)


if __name__ == "__main__":
    # 检查 API 密钥
    if not os.getenv("DEEPSEEK_API_KEY"):
        print("⚠️  警告: 未设置 DEEPSEEK_API_KEY 环境变量")
        print("某些示例需要有效的 API 密钥才能运行")
        print("设置方法: export DEEPSEEK_API_KEY='your-api-key'")
        print()
    
    main()