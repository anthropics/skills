import requests
import time
import json
import os
from PIL import Image
from io import BytesIO

# 尝试从 .env 文件加载环境变量
try:
    from dotenv import load_dotenv
    # 尝试加载 .env 文件（如果存在）
    if os.path.exists('.env'):
        load_dotenv('.env')
    else:
        # 尝试从技能目录加载 .env 文件
        skill_dir = os.path.dirname(os.path.abspath(__file__))
        env_path = os.path.join(skill_dir, '.env')
        if os.path.exists(env_path):
            load_dotenv(env_path)
except ImportError:
    # 如果没有安装 python-dotenv，只使用系统环境变量
    pass

class ModelScopeImageGenerator:
    def __init__(self):
        self.base_url = 'https://api-inference.modelscope.cn/'
        self.api_key = os.getenv('MODELSCOPE_API_KEY')

        if not self.api_key:
            skill_dir = os.path.dirname(os.path.abspath(__file__))
            env_example_path = os.path.join(skill_dir, '.env.example')
            error_msg = f"请设置 MODELSCOPE_API_KEY 环境变量或创建 .env 文件\n示例文件位置: {env_example_path}"
            raise ValueError(error_msg)

        self.common_headers = {
            "Authorization": f"Bearer {self.api_key}",
            "Content-Type": "application/json",
        }

    def generate_image(self, prompt, output_path="result_image.jpg", model="Tongyi-MAI/Z-Image-Turbo"):
        """
        生成单张图像

        Args:
            prompt (str): 图像生成提示词
            output_path (str): 输出文件路径
            model (str): 使用的模型ID

        Returns:
            str: 成功时返回输出文件路径，失败时返回None
        """
        try:
            # 提交图像生成任务
            response = requests.post(
                f"{self.base_url}v1/images/generations",
                headers={**self.common_headers, "X-ModelScope-Async-Mode": "true"},
                data=json.dumps({
                    "model": model,
                    "prompt": prompt
                }, ensure_ascii=False).encode('utf-8')
            )
            response.raise_for_status()
            task_id = response.json()["task_id"]

            # 轮询检查任务状态
            while True:
                result = requests.get(
                    f"{self.base_url}v1/tasks/{task_id}",
                    headers={**self.common_headers, "X-ModelScope-Task-Type": "image_generation"},
                )
                result.raise_for_status()
                data = result.json()

                if data["task_status"] == "SUCCEED":
                    image_url = data["output_images"][0]
                    image_response = requests.get(image_url)
                    image_response.raise_for_status()

                    image = Image.open(BytesIO(image_response.content))
                    image.save(output_path)
                    print(f"图像已保存到: {output_path}")
                    return output_path

                elif data["task_status"] == "FAILED":
                    print(f"图像生成失败: {data.get('error_message', 'Unknown error')}")
                    return None

                time.sleep(5)  # 等待5秒后再次检查

        except Exception as e:
            print(f"生成图像时发生错误: {e}")
            return None

    def generate_images_sequentially(self, prompts, output_dir):
        """
        顺序生成多张图像（考虑API限流）

        Args:
            prompts (list): 提示词列表，每个元素可以是字符串或包含描述的字典
            output_dir (str): 输出目录的绝对路径（必需参数）

        Returns:
            list: 成功生成的图像文件路径列表
        """
        import os

        # 验证输出目录必须是绝对路径
        if not os.path.isabs(output_dir):
            raise ValueError("output_dir 必须是绝对路径")

        # 创建输出目录（如果不存在）
        os.makedirs(output_dir, exist_ok=True)

        generated_images = []

        for i, prompt_info in enumerate(prompts):
            if isinstance(prompt_info, dict):
                prompt = prompt_info["prompt"]
                description = prompt_info.get("description", f"提示词 {i+1}")
            else:
                prompt = prompt_info
                description = f"提示词 {i+1}"

            print(f"正在生成第 {i+1}/{len(prompts)} 张图像: {description}")

            # 构建输出文件名
            safe_description = "".join(c for c in description if c.isalnum() or c in " _-").rstrip()
            output_path = os.path.join(output_dir, f"{safe_description}.jpg")

            # 生成图像
            result = self.generate_image(prompt, output_path)
            if result:
                generated_images.append(result)

            # 在生成下一张之前等待，避免触发限流
            if i < len(prompts) - 1:  # 不是最后一张
                print("等待10秒以避免API限流...")
                time.sleep(10)

        return generated_images

# 使用示例
if __name__ == "__main__":
    generator = ModelScopeImageGenerator()

    # 单张图像生成示例
    # result = generator.generate_image("A golden cat", "/absolute/path/to/cat_image.jpg")

    # 多张图像顺序生成示例（必须指定绝对路径）
    # prompts = [
    #     {"prompt": "A golden cat sitting on a windowsill", "description": "金色猫咪"},
    #     {"prompt": "A futuristic city at night with neon lights", "description": "未来城市"}
    # ]
    # results = generator.generate_images_sequentially(prompts, "/absolute/path/to/output/directory")