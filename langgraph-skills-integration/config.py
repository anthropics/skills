"""
配置文件 - 管理系统配置
"""
import os
from dataclasses import dataclass
from typing import Optional
from pathlib import Path


@dataclass
class SkillsConfig:
    """技能系统配置"""
    # Skills 仓库路径
    skills_root: str = "../"
    
    # 缓存设置
    enable_cache: bool = True
    cache_ttl: int = 3600  # 缓存过期时间（秒）
    
    # 技能发现设置
    auto_discover: bool = True
    scan_interval: int = 300  # 自动扫描间隔（秒）
    
    # 技能加载设置
    max_skill_size: int = 10 * 1024 * 1024  # 最大技能大小 (10MB)
    load_references_by_default: bool = False


@dataclass
class DeepSeekConfig:
    """DeepSeek LLM 配置"""
    # API 设置
    api_key: str = ""
    base_url: str = "https://api.deepseek.com/v1"
    
    # 模型选择
    chat_model: str = "deepseek-chat"
    code_model: str = "deepseek-coder"
    
    # 推理参数
    temperature: float = 0.7
    max_tokens: int = 2000
    
    # 超时设置
    timeout: int = 60  # 秒
    
    # 重试设置
    max_retries: int = 3
    retry_delay: int = 1  # 秒


@dataclass
class AgentConfig:
    """Agent 配置"""
    # 执行设置
    max_execution_time: int = 300  # 最大执行时间（秒）
    enable_code_execution: bool = True
    sandbox_mode: bool = True  # 沙箱模式
    
    # 工作流设置
    max_workflow_steps: int = 10
    enable_parallel_execution: bool = False
    
    # 日志设置
    log_level: str = "INFO"
    log_file: Optional[str] = None
    
    # 错误处理
    max_retry_attempts: int = 2
    fallback_to_general_llm: bool = True


class Config:
    """主配置类"""
    
    def __init__(self):
        # 加载环境变量
        self._load_from_env()
        
        # 子配置
        self.skills = SkillsConfig()
        self.deepseek = DeepSeekConfig()
        self.agent = AgentConfig()
    
    def _load_from_env(self):
        """从环境变量加载配置"""
        # DeepSeek API 密钥
        api_key = os.getenv("DEEPSEEK_API_KEY")
        if api_key:
            self.deepseek.api_key = api_key
        
        # Skills 路径
        skills_path = os.getenv("SKILLS_PATH")
        if skills_path:
            self.skills.skills_root = skills_path
        
        # 日志级别
        log_level = os.getenv("LOG_LEVEL")
        if log_level:
            self.agent.log_level = log_level
    
    def validate(self) -> bool:
        """验证配置"""
        errors = []
        
        # 检查 API 密钥
        if not self.deepseek.api_key:
            errors.append("DeepSeek API 密钥未设置")
        
        # 检查 skills 路径
        if not Path(self.skills.skills_root).exists():
            errors.append(f"Skills 路径不存在: {self.skills.skills_root}")
        
        if errors:
            print("配置验证失败:")
            for error in errors:
                print(f"  ❌ {error}")
            return False
        
        return True
    
    def display(self):
        """显示当前配置"""
        print("\n" + "="*60)
        print("当前配置")
        print("="*60)
        
        print("\n📁 Skills 配置:")
        print(f"  路径: {self.skills.skills_root}")
        print(f"  缓存: {'启用' if self.skills.enable_cache else '禁用'}")
        print(f"  自动发现: {'启用' if self.skills.auto_discover else '禁用'}")
        
        print("\n🤖 DeepSeek 配置:")
        print(f"  API Key: {'已设置' if self.deepseek.api_key else '未设置'}")
        print(f"  基础 URL: {self.deepseek.base_url}")
        print(f"  聊天模型: {self.deepseek.chat_model}")
        print(f"  代码模型: {self.deepseek.code_model}")
        print(f"  温度: {self.deepseek.temperature}")
        
        print("\n⚙️  Agent 配置:")
        print(f"  代码执行: {'启用' if self.agent.enable_code_execution else '禁用'}")
        print(f"  沙箱模式: {'启用' if self.agent.sandbox_mode else '禁用'}")
        print(f"  最大步骤: {self.agent.max_workflow_steps}")
        print(f"  日志级别: {self.agent.log_level}")
        
        print("="*60 + "\n")


# 全局配置实例
config = Config()


# 使用示例
if __name__ == "__main__":
    # 显示配置
    config.display()
    
    # 验证配置
    if config.validate():
        print("✅ 配置验证通过")
    else:
        print("❌ 配置验证失败")
    
    # 修改配置
    config.deepseek.temperature = 0.5
    config.agent.max_workflow_steps = 20
    
    print("\n修改后的配置:")
    config.display()