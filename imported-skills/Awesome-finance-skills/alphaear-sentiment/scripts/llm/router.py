import os
from typing import Optional, List, Dict, Any, Union
from agno.models.base import Model
from loguru import logger
from dotenv import load_dotenv
from .llm.factory import get_model
from utils.llm.capability import ModelCapabilityRegistry

# 确保在初始化前加载环境变量
load_dotenv()

class ModelRouter:
    """
    模型路由管理器
    
    功能：
    1. 管理“推理/写作模型” (Reasoning Model) 和“工具调用模型” (Tool Model)。
    2. 根据任务需求自动选择合适的模型。
    """
    
    def __init__(self):
        # 默认从环境变量读取
        self.reasoning_provider = os.getenv("REASONING_MODEL_PROVIDER", os.getenv("LLM_PROVIDER", "openai"))
        self.reasoning_id = os.getenv("REASONING_MODEL_ID", os.getenv("LLM_MODEL", "gpt-4o"))
        self.reasoning_host = os.getenv("REASONING_MODEL_HOST", os.getenv("LLM_HOST"))
        
        self.tool_provider = os.getenv("TOOL_MODEL_PROVIDER", self.reasoning_provider)
        self.tool_id = os.getenv("TOOL_MODEL_ID", self.reasoning_id)
        self.tool_host = os.getenv("TOOL_MODEL_HOST", self.reasoning_host)
        
        self._reasoning_model = None
        self._tool_model = None
        
        logger.info(f"🤖 ModelRouter initialized: Reasoning={self.reasoning_id} ({self.reasoning_host or 'default'}), Tool={self.tool_id} ({self.tool_host or 'default'})")

    def get_reasoning_model(self, **kwargs) -> Model:
        if not self._reasoning_model:
            # 优先使用路由配置的 host
            if self.reasoning_host and "host" not in kwargs:
                kwargs["host"] = self.reasoning_host
            self._reasoning_model = get_model(self.reasoning_provider, self.reasoning_id, **kwargs)
        return self._reasoning_model

    def get_tool_model(self, **kwargs) -> Model:
        if not self._tool_model:
            # 优先使用路由配置的 host
            if self.tool_host and "host" not in kwargs:
                kwargs["host"] = self.tool_host
                
            # 检查 tool_model 是否真的支持 tool call
            caps = ModelCapabilityRegistry.get_capabilities(self.tool_provider, self.tool_id, **kwargs)
            if not caps["supports_tool_call"]:
                logger.warning(f"⚠️ Configured tool model {self.tool_id} might not support native tool calls! Consider using ReAct mode or a different model.")
            
            self._tool_model = get_model(self.tool_provider, self.tool_id, **kwargs)
        return self._tool_model

    def get_model_for_agent(self, has_tools: bool = False, **kwargs) -> Model:
        """
        根据 Agent 是否包含工具来返回合适的模型。
        """
        if has_tools:
            return self.get_tool_model(**kwargs)
        return self.get_reasoning_model(**kwargs)

# 全局单例
router = ModelRouter()
