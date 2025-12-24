"""
ModelScope API 使用示例

本文件包含了 ModelScope API 技能的各种使用示例
"""

from modelscope_api import ModelScopeAPI, chat_with_model, generate_image_from_text


def example_1_basic_chat():
    """基础文本聊天示例"""
    print("=== 示例 1: 基础文本聊天 ===")

    # 初始化 API
    api = ModelScopeAPI(api_key="your-api-key")

    # 发送消息
    messages = [
        {"role": "user", "content": "你好，请介绍一下自己"}
    ]

    # 非流式响应
    response = api.chat_completion(
        model="Qwen/Qwen3-VL-235B-A22B-Instruct",
        messages=messages,
        stream=False
    )

    print("模型回复:", response.choices[0].message.content)
    print()


def example_2_streaming_chat():
    """流式文本聊天示例"""
    print("=== 示例 2: 流式文本聊天 ===")

    api = ModelScopeAPI()

    messages = [
        {"role": "user", "content": "请写一首关于春天的短诗"}
    ]

    # 流式响应
    response = api.chat_completion(
        model="Qwen/Qwen3-VL-235B-A22B-Instruct",
        messages=messages,
        stream=True
    )

    print("模型回复: ", end="")
    for chunk in response:
        if chunk.choices:
            content = chunk.choices[0].delta.content
            if content:
                print(content, end='', flush=True)
    print("\n")


def example_3_image_generation():
    """基础图像生成示例"""
    print("=== 示例 3: 基础图像生成 ===")

    api = ModelScopeAPI()

    try:
        # 生成图像
        image_path = api.generate_image(
            model="Tongyi-MAI/Z-Image-Turbo",
            prompt="一只可爱的橘猫坐在樱花树下",
            output_path="cute_cat.jpg"
        )
        print(f"图像已保存到: {image_path}")
    except Exception as e:
        print(f"图像生成失败: {e}")
    print()


def example_4_image_with_lora():
    """使用 LoRA 的图像生成示例"""
    print("=== 示例 4: 使用 LoRA 的图像生成 ===")

    api = ModelScopeAPI()

    try:
        # 使用单个 LoRA
        image_path = api.generate_image(
            model="Tongyi-MAI/Z-Image-Turbo",
            prompt="A beautiful landscape",
            loras="lora-repo-id",
            output_path="landscape_with_lora.jpg"
        )
        print(f"带 LoRA 的图像已保存到: {image_path}")
    except Exception as e:
        print(f"图像生成失败: {e}")
    print()


def example_5_multiple_loras():
    """使用多个 LoRA 的图像生成示例"""
    print("=== 示例 5: 使用多个 LoRA 的图像生成 ===")

    api = ModelScopeAPI()

    try:
        # 使用多个 LoRA（权重总和必须为 1.0）
        image_path = api.generate_image(
            model="Tongyi-MAI/Z-Image-Turbo",
            prompt="A cyberpunk style cityscape",
            loras={"lora1": 0.6, "lora2": 0.4},  # 权重总和为 1.0
            output_path="cyberpunk_city.jpg"
        )
        print(f"带多个 LoRA 的图像已保存到: {image_path}")
    except Exception as e:
        print(f"图像生成失败: {e}")
    print()


def example_6_batch_image_generation():
    """批量图像生成示例"""
    print("=== 示例 6: 批量图像生成 ===")

    api = ModelScopeAPI()

    # 批量生成提示词
    prompts = [
        "A serene Japanese garden in autumn",
        "A futuristic spaceship in deep space",
        "A cozy cabin in the snowy mountains",
        "A vibrant coral reef underwater scene"
    ]

    try:
        image_paths = api.batch_generate_images(
            model="Tongyi-MAI/Z-Image-Turbo",
            prompts=prompts,
            output_dir="batch_images"
        )
        print(f"批量生成完成，共生成 {len(image_paths)} 张图像")
        for path in image_paths:
            print(f" - {path}")
    except Exception as e:
        print(f"批量生成失败: {e}")
    print()


def example_7_quick_chat_function():
    """使用快捷聊天函数"""
    print("=== 示例 7: 使用快捷聊天函数 ===")

    # 流式输出
    print("流式输出: ", end="")
    for text_chunk in chat_with_model("用一句话描述人工智能"):
        print(text_chunk, end='', flush=True)
    print("\n")

    # 非流式输出
    response = chat_with_model("什么是机器学习？", stream=False)
    print("非流式输出:", response)
    print()


def example_8_quick_image_function():
    """使用快捷图像生成函数"""
    print("=== 示例 8: 使用快捷图像生成函数 ===")

    try:
        image_path = generate_image_from_text(
            prompt="A magical forest with glowing mushrooms",
            output_path="magical_forest.jpg"
        )
        print(f"图像已生成: {image_path}")
    except Exception as e:
        print(f"图像生成失败: {e}")
    print()


def example_9_advanced_chat_parameters():
    """高级聊天参数示例"""
    print("=== 示例 9: 高级聊天参数 ===")

    api = ModelScopeAPI()

    messages = [
        {"role": "system", "content": "你是一个专业的编程助手"},
        {"role": "user", "content": "请解释 Python 中的装饰器"}
    ]

    # 使用高级参数
    response = api.chat_completion(
        model="Qwen/Qwen3-VL-235B-A22B-Instruct",
        messages=messages,
        stream=False,
        temperature=0.3,  # 降低随机性
        max_tokens=500,
        top_p=0.9
    )

    print("模型回复:", response.choices[0].message.content)
    print()


def example_10_error_handling():
    """错误处理示例"""
    print("=== 示例 10: 错误处理 ===")

    try:
        # 使用无效的 API Key
        api = ModelScopeAPI(api_key="invalid-key")

        response = api.chat_completion(
            model="Qwen/Qwen3-VL-235B-A22B-Instruct",
            messages=[{"role": "user", "content": "Hello"}],
            stream=False
        )
    except Exception as e:
        print(f"捕获到错误: {type(e).__name__}: {e}")

    # 验证 LoRA 权重
    api = ModelScopeAPI()

    # 有效的权重
    valid_loras = {"lora1": 0.5, "lora2": 0.3, "lora3": 0.2}
    print(f"LoRA 权重 {valid_loras} 有效: {api.validate_lora_weights(valid_loras)}")

    # 无效的权重
    invalid_loras = {"lora1": 0.6, "lora2": 0.3, "lora3": 0.3}
    print(f"LoRA 权重 {invalid_loras} 有效: {api.validate_lora_weights(invalid_loras)}")
    print()


def run_all_examples():
    """运行所有示例"""
    examples = [
        example_1_basic_chat,
        example_2_streaming_chat,
        example_3_image_generation,
        example_4_image_with_lora,
        example_5_multiple_loras,
        example_6_batch_image_generation,
        example_7_quick_chat_function,
        example_8_quick_image_function,
        example_9_advanced_chat_parameters,
        example_10_error_handling
    ]

    print("开始运行 ModelScope API 示例...\n")

    for example in examples:
        try:
            example()
        except Exception as e:
            print(f"示例 {example.__name__} 运行失败: {e}\n")

    print("所有示例运行完成！")


if __name__ == "__main__":
    # 运行单个示例
    # example_1_basic_chat()

    # 运行所有示例
    run_all_examples()