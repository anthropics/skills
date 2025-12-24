"""
ModelScope API 技能 - 提供对 ModelScope 平台 API 的便捷访问

功能包括：
- 文本生成（支持 OpenAI 兼容接口）
- 图像生成（异步处理）
- 支持流式响应
- 支持 LoRA 模型
"""

import os
import json
import time
import requests
from typing import Dict, List, Optional, Union, Iterator, Any
from io import BytesIO
from PIL import Image


class ModelScopeAPI:
    """ModelScope API 客户端类"""

    def __init__(self, api_key: Optional[str] = None, base_url: str = "https://api-inference.modelscope.cn/"):
        """
        初始化 ModelScope API 客户端

        Args:
            api_key: ModelScope API Token，如果不提供则从环境变量 MODELSCOPE_API_KEY 获取
            base_url: API 基础 URL
        """
        self.api_key = api_key or os.getenv("MODELSCOPE_API_KEY")
        if not self.api_key:
            raise ValueError("必须提供 API Key 或设置 MODELSCOPE_API_KEY 环境变量")

        self.base_url = base_url.rstrip("/")
        self.common_headers = {
            "Authorization": f"Bearer {self.api_key}",
            "Content-Type": "application/json",
        }

        # 检查依赖
        try:
            import openai
            self.openai_client = openai.OpenAI(
                base_url=f"{self.base_url}/v1",
                api_key=self.api_key
            )
        except ImportError:
            self.openai_client = None

    def chat_completion(self,
                       model: str,
                       messages: List[Dict[str, str]],
                       stream: bool = False,
                       temperature: float = 0.7,
                       max_tokens: int = 1000,
                       **kwargs) -> Any:
        """
        调用文本生成接口（OpenAI 兼容）

        Args:
            model: ModelScope 模型 ID
            messages: 消息列表，格式为 [{"role": "user", "content": "..."}]
            stream: 是否使用流式响应
            temperature: 温度参数（0-1）
            max_tokens: 最大 token 数
            **kwargs: 其他参数

        Returns:
            流式响应迭代器或完整响应对象
        """
        if not self.openai_client:
            raise ImportError("需要安装 openai 包：pip install openai")

        try:
            response = self.openai_client.chat.completions.create(
                model=model,
                messages=messages,
                stream=stream,
                temperature=temperature,
                max_tokens=max_tokens,
                **kwargs
            )
            return response
        except Exception as e:
            raise Exception(f"文本生成请求失败: {str(e)}")

    def generate_image(self,
                      model: str,
                      prompt: str,
                      loras: Optional[Union[str, Dict[str, float]]] = None,
                      output_path: str = "generated_image.jpg",
                      check_interval: int = 5) -> str:
        """
        生成图像（异步处理）

        Args:
            model: ModelScope 图像生成模型 ID
            prompt: 图像描述文本
            loras: LoRA 配置，可以是字符串（单个 LoRA）或字典（多个 LoRA）
            output_path: 输出图像路径
            check_interval: 状态检查间隔（秒）

        Returns:
            输出图像路径
        """
        # 准备请求数据
        data = {
            "model": model,
            "prompt": prompt
        }

        # 添加 LoRA 配置
        if loras:
            data["loras"] = loras

        # 发起异步生成请求
        try:
            response = requests.post(
                f"{self.base_url}/v1/images/generations",
                headers={**self.common_headers, "X-ModelScope-Async-Mode": "true"},
                data=json.dumps(data, ensure_ascii=False).encode('utf-8')
            )
            response.raise_for_status()
            task_id = response.json()["task_id"]
        except Exception as e:
            raise Exception(f"图像生成请求失败: {str(e)}")

        # 轮询任务状态
        while True:
            try:
                result = requests.get(
                    f"{self.base_url}/v1/tasks/{task_id}",
                    headers={**self.common_headers, "X-ModelScope-Task-Type": "image_generation"},
                )
                result.raise_for_status()
                data = result.json()

                if data["task_status"] == "SUCCEED":
                    # 下载并保存图像
                    image_url = data["output_images"][0]
                    image_response = requests.get(image_url)
                    image_response.raise_for_status()

                    # 保存图像
                    os.makedirs(os.path.dirname(output_path) if os.path.dirname(output_path) else ".", exist_ok=True)
                    image = Image.open(BytesIO(image_response.content))
                    image.save(output_path)

                    print(f"图像生成成功，保存到: {output_path}")
                    return output_path

                elif data["task_status"] == "FAILED":
                    error_msg = data.get("error_message", "未知错误")
                    raise Exception(f"图像生成失败: {error_msg}")

                time.sleep(check_interval)

            except requests.exceptions.RequestException as e:
                raise Exception(f"检查任务状态时出错: {str(e)}")

    def batch_generate_images(self,
                             model: str,
                             prompts: List[str],
                             output_dir: str = "batch_images",
                             loras: Optional[Union[str, Dict[str, float]]] = None) -> List[str]:
        """
        批量生成图像

        Args:
            model: ModelScope 图像生成模型 ID
            prompts: 图像描述文本列表
            output_dir: 输出目录
            loras: LoRA 配置

        Returns:
            生成的图像路径列表
        """
        os.makedirs(output_dir, exist_ok=True)
        image_paths = []

        for i, prompt in enumerate(prompts):
            output_path = os.path.join(output_dir, f"image_{i+1}.jpg")
            try:
                path = self.generate_image(
                    model=model,
                    prompt=prompt,
                    loras=loras,
                    output_path=output_path
                )
                image_paths.append(path)
            except Exception as e:
                print(f"生成第 {i+1} 张图像失败: {str(e)}")
                continue

        return image_paths

    def get_model_info(self, model_id: str) -> Dict[str, Any]:
        """
        获取模型信息（示例方法，实际 API 可能需要调整）

        Args:
            model_id: 模型 ID

        Returns:
            模型信息字典
        """
        # 这里可以根据实际 API 实现获取模型信息的功能
        return {
            "model_id": model_id,
            "description": f"ModelScope model: {model_id}",
            "type": "text_generation"  # 或 "image_generation"
        }

    def validate_lora_weights(self, loras: Dict[str, float]) -> bool:
        """
        验证多个 LoRA 的权重是否有效（总和为 1.0）

        Args:
            loras: LoRA 配置字典

        Returns:
            是否有效
        """
        if not isinstance(loras, dict):
            return False

        total_weight = sum(loras.values())
        return abs(total_weight - 1.0) < 0.001


# 快捷函数
def chat_with_model(prompt: str,
                   model: str = "Qwen/Qwen3-VL-235B-A22B-Instruct",
                   api_key: Optional[str] = None,
                   stream: bool = True,
                   **kwargs) -> Union[str, Iterator[str]]:
    """
    快速文本生成函数

    Args:
        prompt: 输入提示
        model: 模型 ID
        api_key: API Key
        stream: 是否流式输出
        **kwargs: 其他参数

    Returns:
        生成的文本或文本迭代器
    """
    api = ModelScopeAPI(api_key=api_key)
    messages = [{"role": "user", "content": prompt}]

    response = api.chat_completion(
        model=model,
        messages=messages,
        stream=stream,
        **kwargs
    )

    if stream:
        def text_generator():
            for chunk in response:
                if chunk.choices:
                    content = chunk.choices[0].delta.content
                    if content:
                        yield content
        return text_generator()
    else:
        return response.choices[0].message.content


def generate_image_from_text(prompt: str,
                           model: str = "Tongyi-MAI/Z-Image-Turbo",
                           output_path: str = "generated_image.jpg",
                           api_key: Optional[str] = None,
                           **kwargs) -> str:
    """
    快速图像生成函数

    Args:
        prompt: 图像描述
        model: 模型 ID
        output_path: 输出路径
        api_key: API Key
        **kwargs: 其他参数

    Returns:
        图像路径
    """
    api = ModelScopeAPI(api_key=api_key)
    return api.generate_image(
        model=model,
        prompt=prompt,
        output_path=output_path,
        **kwargs
    )


# 示例用法
if __name__ == "__main__":
    # 示例 1: 文本生成
    print("=== 文本生成示例 ===")
    api = ModelScopeAPI()

    # 流式输出
    response = api.chat_completion(
        model="Qwen/Qwen3-VL-235B-A22B-Instruct",
        messages=[{"role": "user", "content": "请介绍一下人工智能"}],
        stream=True
    )

    for chunk in response:
        if chunk.choices:
            content = chunk.choices[0].delta.content
            if content:
                print(content, end='', flush=True)
    print("\n")

    # 示例 2: 图像生成
    print("=== 图像生成示例 ===")
    try:
        image_path = api.generate_image(
            model="Tongyi-MAI/Z-Image-Turbo",
            prompt="A cute robot in cyberpunk style",
            output_path="example_robot.jpg"
        )
        print(f"图像已生成: {image_path}")
    except Exception as e:
        print(f"图像生成失败: {e}")

    # 示例 3: 使用快捷函数
    print("\n=== 快捷函数示例 ===")
    # 文本生成
    for text_chunk in chat_with_model("用一句话描述春天"):
        print(text_chunk, end='', flush=True)
    print("\n")