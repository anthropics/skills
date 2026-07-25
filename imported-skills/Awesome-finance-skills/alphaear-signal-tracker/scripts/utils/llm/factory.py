import os
from agno.models.openai import OpenAIChat
from agno.models.ollama import Ollama
from agno.models.dashscope import DashScope
from agno.models.deepseek import DeepSeek
from agno.models.openrouter import OpenRouter

def get_model(model_provider: str, model_id: str, **kwargs):
    """
    Factory to get the appropriate LLM model.
    
    Args:
        model_provider: "openai", "ollama", "deepseek"
        model_id: The specific model ID (e.g., "gpt-4o", "llama3", "deepseek-chat")
        **kwargs: Additional arguments for the model constructor
    """
    if model_provider == "openai":
        return OpenAIChat(id=model_id, **kwargs)
    
    elif model_provider == "ollama":
        return Ollama(id=model_id, **kwargs)
    
    elif model_provider == "deepseek":
        # DeepSeek is OpenAI compatible
        api_key = os.getenv("DEEPSEEK_API_KEY")
        if not api_key:
            print("Warning: DEEPSEEK_API_KEY not set.")
        
        return DeepSeek(
            id=model_id,
            api_key=api_key,
            **kwargs
        )
    elif model_provider == "dashscope":
        api_key = os.getenv("DASHSCOPE_API_KEY")
        if not api_key:
            print("Warning: DASHSCOPE_API_KEY not set.")
        
        return DashScope(
            id=model_id,
            base_url="https://dashscope.aliyuncs.com/compatible-mode/v1",
            api_key=api_key,
            **kwargs
        )
    elif model_provider == 'openrouter':
        api_key = os.getenv("OPENROUTER_API_KEY")
        if not api_key:
            print('Warning: OPENROUTER_API_KEY not set.')
        
        return OpenRouter(
            id=model_id,
            api_key=api_key,
            **kwargs
        )

    elif model_provider == 'zai':
        api_key = os.getenv("ZAI_KEY_API")
        if not api_key:
            print('Warning: ZAI_KEY_API not set.')

        # role_map to ensure compatibility.
        default_role_map = {
            "system": "system",
            "user": "user",
            "assistant": "assistant",
            "tool": "tool",
            "model": "assistant",
        }

        # Allow callers to override role_map via kwargs, otherwise use default
        role_map = kwargs.pop("role_map", default_role_map)
        
        return OpenAIChat(
            id=model_id,
            base_url="https://api.z.ai/api/paas/v4",
            api_key=api_key,
            timeout=60,
            role_map=role_map,
            extra_body={"enable_thinking": False}, # TODO: one more setting for thinking
            **kwargs
        )
    
    elif model_provider == 'ust':
        api_key = os.getenv("UST_KEY_API")
        if not api_key:
            print('Warning: UST_KEY_API not set.')
        
        # Some UST-compatible endpoints expect the standard OpenAI role names
        # (e.g. "system", "user", "assistant") rather than Agno's default
        # mapping which maps "system" -> "developer". Provide an explicit
        # role_map to ensure compatibility.
        default_role_map = {
            "system": "system",
            "user": "user",
            "assistant": "assistant",
            "tool": "tool",
            "model": "assistant",
        }

        # Allow callers to override role_map via kwargs, otherwise use default
        role_map = kwargs.pop("role_map", default_role_map)

        return OpenAIChat(
            id=model_id,
            api_key=api_key,
            base_url=os.getenv("UST_URL"),
            role_map=role_map,
            extra_body={"enable_thinking": False}, # TODO: one more setting for thinking
            **kwargs
        )
    
    else:
        raise ValueError(f"Unknown model provider: {model_provider}")

