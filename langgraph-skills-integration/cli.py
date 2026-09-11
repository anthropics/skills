#!/usr/bin/env python3
"""
命令行工具 - 快速使用 Skills Agent
"""
import sys
import argparse
from pathlib import Path
from langgraph_agent import SkillAgent
from skill_discovery import SkillDiscovery
from config import config


def list_skills(args):
    """列出所有可用技能"""
    print("\n🔍 扫描技能仓库...")
    discovery = SkillDiscovery(args.skills_path)
    skills = discovery.discover_all_skills()
    
    print(f"\n发现 {len(skills)} 个技能:\n")
    for name, skill in skills.items():
        print(f"📦 {name}")
        print(f"   {skill.description}")
        
        indicators = []
        if skill.has_scripts:
            indicators.append("📜 scripts")
        if skill.has_references:
            indicators.append("📚 references")
        if skill.has_assets:
            indicators.append("🎨 assets")
        
        if indicators:
            print(f"   包含: {', '.join(indicators)}")
        print()


def search_skills(args):
    """搜索技能"""
    print(f"\n🔎 搜索: '{args.query}'")
    discovery = SkillDiscovery(args.skills_path)
    discovery.discover_all_skills()
    
    results = discovery.search_skills(args.query)
    
    if results:
        print(f"\n找到 {len(results)} 个匹配的技能:\n")
        for skill in results:
            print(f"📦 {skill.name}")
            print(f"   {skill.description}\n")
    else:
        print("\n未找到匹配的技能")


def run_agent(args):
    """运行 Agent 处理查询"""
    if not args.api_key and not config.deepseek.api_key:
        print("❌ 错误: 需要 DeepSeek API 密钥")
        print("使用 --api-key 参数或设置 DEEPSEEK_API_KEY 环境变量")
        sys.exit(1)
    
    api_key = args.api_key or config.deepseek.api_key
    
    print("\n🤖 初始化 Agent...")
    agent = SkillAgent(
        skills_path=args.skills_path,
        deepseek_api_key=api_key
    )
    
    # 如果提供了查询，直接执行
    if args.query:
        result = agent.run(args.query)
        print(f"\n{'='*60}")
        print("结果:")
        print(f"{'='*60}")
        print(result)
        print(f"{'='*60}\n")
    else:
        # 交互式模式
        print("\n💬 交互式模式 (输入 'exit' 或 'quit' 退出)")
        print(f"{'='*60}\n")
        
        while True:
            try:
                query = input("👤 你: ").strip()
                
                if query.lower() in ['exit', 'quit', 'q']:
                    print("\n👋 再见!")
                    break
                
                if not query:
                    continue
                
                print()
                result = agent.run(query)
                print(f"\n🤖 Agent: {result}\n")
                print(f"{'-'*60}\n")
                
            except KeyboardInterrupt:
                print("\n\n👋 再见!")
                break
            except Exception as e:
                print(f"\n❌ 错误: {e}\n")


def show_config(args):
    """显示当前配置"""
    config.display()


def validate_setup(args):
    """验证系统设置"""
    print("\n🔧 验证系统设置...\n")
    
    errors = []
    warnings = []
    
    # 检查 Skills 路径
    skills_path = Path(args.skills_path)
    if not skills_path.exists():
        errors.append(f"Skills 路径不存在: {skills_path}")
    else:
        print(f"✅ Skills 路径: {skills_path.absolute()}")
    
    # 检查 API 密钥
    if not config.deepseek.api_key:
        warnings.append("DeepSeek API 密钥未设置")
    else:
        print(f"✅ API 密钥: 已设置")
    
    # 检查依赖
    try:
        import langgraph
        print(f"✅ LangGraph: {langgraph.__version__}")
    except ImportError:
        errors.append("LangGraph 未安装")
    
    try:
        import openai
        print(f"✅ OpenAI: {openai.__version__}")
    except ImportError:
        errors.append("OpenAI 包未安装")
    
    try:
        import yaml
        print(f"✅ PyYAML: 已安装")
    except ImportError:
        errors.append("PyYAML 未安装")
    
    # 扫描技能
    if skills_path.exists():
        try:
            discovery = SkillDiscovery(str(skills_path))
            skills = discovery.discover_all_skills()
            print(f"✅ 发现技能: {len(skills)} 个")
        except Exception as e:
            errors.append(f"技能扫描失败: {e}")
    
    # 显示结果
    if errors:
        print(f"\n❌ 发现 {len(errors)} 个错误:")
        for error in errors:
            print(f"   • {error}")
    
    if warnings:
        print(f"\n⚠️  {len(warnings)} 个警告:")
        for warning in warnings:
            print(f"   • {warning}")
    
    if not errors and not warnings:
        print("\n✅ 所有检查通过!")
    
    print()


def main():
    """主函数"""
    parser = argparse.ArgumentParser(
        description="LangGraph + DeepSeek + Skills 命令行工具",
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog="""
示例:
  # 列出所有技能
  %(prog)s list
  
  # 搜索技能
  %(prog)s search pdf
  
  # 运行查询
  %(prog)s run "帮我合并两个 PDF"
  
  # 交互式模式
  %(prog)s run --interactive
  
  # 验证设置
  %(prog)s validate
        """
    )
    
    parser.add_argument(
        '--skills-path',
        default='../',
        help='Skills 仓库路径 (默认: ../)'
    )
    
    parser.add_argument(
        '--api-key',
        help='DeepSeek API 密钥'
    )
    
    subparsers = parser.add_subparsers(dest='command', help='命令')
    
    # list 命令
    list_parser = subparsers.add_parser('list', help='列出所有技能')
    list_parser.set_defaults(func=list_skills)
    
    # search 命令
    search_parser = subparsers.add_parser('search', help='搜索技能')
    search_parser.add_argument('query', help='搜索查询')
    search_parser.set_defaults(func=search_skills)
    
    # run 命令
    run_parser = subparsers.add_parser('run', help='运行 Agent')
    run_parser.add_argument('query', nargs='?', help='用户查询')
    run_parser.add_argument('-i', '--interactive', action='store_true',
                           help='交互式模式')
    run_parser.set_defaults(func=run_agent)
    
    # config 命令
    config_parser = subparsers.add_parser('config', help='显示配置')
    config_parser.set_defaults(func=show_config)
    
    # validate 命令
    validate_parser = subparsers.add_parser('validate', help='验证系统设置')
    validate_parser.set_defaults(func=validate_setup)
    
    # 解析参数
    args = parser.parse_args()
    
    if not args.command:
        parser.print_help()
        sys.exit(1)
    
    # 执行命令
    try:
        args.func(args)
    except Exception as e:
        print(f"\n❌ 错误: {e}")
        sys.exit(1)


if __name__ == "__main__":
    main()