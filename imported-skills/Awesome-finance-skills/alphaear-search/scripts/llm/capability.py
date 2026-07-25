import os
from typing import Optional, List, Dict, Any
from agno.agent import Agent
from agno.models.base import Model
from loguru import logger
from .factory import get_model

def test_tool_call_support(model: Model) -> bool:
    """
    测试模型是否支持原生的 Tool Call (Function Calling)。
    通过尝试执行一个简单的加法工具来验证。
    """
    def get_current_weather(location: str):
        """获取指定地点的天气"""
        return f"{location} 的天气是晴天，25度。"

    test_agent = Agent(
        model=model,
        tools=[get_current_weather],
        instructions="请调用工具查询北京的天气，并直接返回工具的输出结果。"
    )

    try:
        # 运行一个简单的任务，观察是否触发了 tool_call
        response = test_agent.run("北京天气怎么样？")
        
        # 检查 response 中是否包含 tool_calls
        # Agno 的 RunResponse 对象通常包含 messages，我们可以检查最后几条消息
        has_tool_call = False
        for msg in response.messages:
            if hasattr(msg, 'tool_calls') and msg.tool_calls:
                has_tool_call = True
                break
        
        if has_tool_call:
            logger.info(f"✅ Model {model.id} supports native tool calling.")
            return True
        else:
            # 如果没有 tool_calls 但返回了正确答案，可能是模型通过纯文本模拟了工具调用（ReAct）
            # 或者根本没用工具。对于原生支持的判断，我们坚持要求有 tool_calls 结构。
            logger.warning(f"⚠️ Model {model.id} did NOT use native tool calling structure.")
            return False
            
    except Exception as e:
        logger.error(f"❌ Error testing tool call for {model.id}: {e}")
        return False

class ModelCapabilityRegistry:
    """
    模型能力注册表，用于缓存和管理不同模型的能力测试结果。
    """
    _cache = {}

    @classmethod
    def get_capabilities(cls, provider: str, model_id: str, **kwargs) -> Dict[str, bool]:
        key = f"{provider}:{model_id}"
        if key not in cls._cache:
            logger.info(f"🔍 Testing capabilities for {key}...")
            model = get_model(provider, model_id, **kwargs)
            supports_tool_call = test_tool_call_support(model)
            cls._cache[key] = {
                "supports_tool_call": supports_tool_call
            }
        return cls._cache[key]

if __name__ == "__main__":
    # 简单测试脚本
    from dotenv import load_dotenv
    load_dotenv()
    
    # 测试当前配置的模型
    p = os.getenv("LLM_PROVIDER", "ust")
    m = os.getenv("LLM_MODEL", "Qwen")
    
    print(f"Testing {p}/{m}...")
    res = ModelCapabilityRegistry.get_capabilities(p, m)
    print(f"Result: {res}")
