"""
DeepSeek LLM 集成 - 处理推理和技能匹配
"""
from typing import List, Dict, Optional, Any
from openai import OpenAI
from skill_discovery import SkillMetadata


class DeepSeekLLM:
    """DeepSeek LLM 包装器"""
    
    def __init__(self, api_key: str, base_url: str = "https://api.deepseek.com/v1"):
        """
        初始化 DeepSeek 客户端
        
        Args:
            api_key: DeepSeek API 密钥
            base_url: API 基础 URL
        """
        self.client = OpenAI(
            api_key=api_key,
            base_url=base_url
        )
        self.model = "deepseek-chat"  # 或 "deepseek-coder" 用于代码生成
    
    def chat(self, messages: List[Dict[str, str]], 
             temperature: float = 0.7,
             max_tokens: int = 2000) -> str:
        """
        发送聊天请求
        
        Args:
            messages: 消息列表
            temperature: 温度参数
            max_tokens: 最大 token 数
            
        Returns:
            模型响应
        """
        try:
            response = self.client.chat.completions.create(
                model=self.model,
                messages=messages,
                temperature=temperature,
                max_tokens=max_tokens
            )
            return response.choices[0].message.content
        except Exception as e:
            return f"错误: {str(e)}"
    
    def select_skill(self, user_query: str, 
                    available_skills: Dict[str, SkillMetadata]) -> Optional[str]:
        """
        根据用户查询选择最合适的技能
        
        Args:
            user_query: 用户查询
            available_skills: 可用技能字典
            
        Returns:
            选中的技能名称或 None
        """
        # 构建技能列表描述
        skills_desc = "\n".join([
            f"{i+1}. {name}: {skill.description}"
            for i, (name, skill) in enumerate(available_skills.items())
        ])
        
        prompt = f"""分析用户查询并选择最合适的技能。

可用技能:
{skills_desc}

用户查询: {user_query}

请分析用户的意图，并返回最适合处理此查询的技能名称。
如果没有合适的技能，返回 "none"。
只返回技能名称，不要有其他解释。"""

        messages = [
            {"role": "system", "content": "你是一个智能助手，负责根据用户需求选择合适的技能。"},
            {"role": "user", "content": prompt}
        ]
        
        response = self.chat(messages, temperature=0.3)
        response = response.strip().lower()
        
        # 检查返回的技能名称是否有效
        if response in available_skills:
            return response
        elif response == "none":
            return None
        else:
            # 尝试模糊匹配
            for skill_name in available_skills.keys():
                if skill_name in response or response in skill_name:
                    return skill_name
            return None
    
    def understand_intent(self, user_query: str, 
                         skill_context: str) -> Dict[str, Any]:
        """
        理解用户意图并提取关键信息
        
        Args:
            user_query: 用户查询
            skill_context: 技能上下文
            
        Returns:
            包含意图分析的字典
        """
        prompt = f"""分析用户查询，基于以下技能上下文理解用户的具体需求。

技能上下文:
{skill_context[:2000]}  # 限制长度

用户查询: {user_query}

请分析并返回 JSON 格式的结果，包含:
1. intent: 用户的主要意图
2. parameters: 需要的参数和值
3. steps: 建议的执行步骤
4. scripts_needed: 需要使用的脚本列表
5. references_needed: 需要查阅的参考文档列表"""

        messages = [
            {"role": "system", "content": "你是一个智能助手，负责理解用户意图。请以 JSON 格式返回分析结果。"},
            {"role": "user", "content": prompt}
        ]
        
        response = self.chat(messages, temperature=0.3)
        
        # 尝试解析 JSON
        try:
            import json
            # 提取 JSON 部分
            if "```json" in response:
                json_str = response.split("```json")[1].split("```")[0]
            elif "{" in response:
                json_str = response[response.find("{"):response.rfind("}")+1]
            else:
                json_str = response
            
            return json.loads(json_str)
        except:
            # 如果解析失败，返回文本
            return {
                "intent": "unknown",
                "raw_response": response
            }
    
    def generate_code(self, task_description: str, 
                     skill_context: str,
                     language: str = "python") -> str:
        """
        生成代码
        
        Args:
            task_description: 任务描述
            skill_context: 技能上下文
            language: 编程语言
            
        Returns:
            生成的代码
        """
        prompt = f"""基于以下技能说明，编写 {language} 代码来完成任务。

技能说明:
{skill_context[:3000]}  # 限制长度

任务: {task_description}

请编写完整、可执行的代码。只返回代码，不要有额外的解释。"""

        messages = [
            {"role": "system", "content": f"你是一个专业的 {language} 程序员。只返回代码，使用 markdown 代码块格式。"},
            {"role": "user", "content": prompt}
        ]
        
        # 使用 deepseek-coder 模型
        original_model = self.model
        self.model = "deepseek-coder"
        
        response = self.chat(messages, temperature=0.2, max_tokens=4000)
        
        # 恢复原模型
        self.model = original_model
        
        # 提取代码块
        if "```" in response:
            code_blocks = response.split("```")
            for i, block in enumerate(code_blocks):
                if i % 2 == 1:  # 奇数索引是代码块
                    # 移除语言标识
                    lines = block.split("\n")
                    if lines[0].strip() in ["python", "py", "javascript", "js", "bash", "sh"]:
                        return "\n".join(lines[1:])
                    return block
        
        return response
    
    def plan_workflow(self, user_query: str, 
                     available_skills: Dict[str, SkillMetadata]) -> List[Dict[str, Any]]:
        """
        规划多步骤工作流
        
        Args:
            user_query: 用户查询
            available_skills: 可用技能
            
        Returns:
            工作流步骤列表
        """
        skills_desc = "\n".join([
            f"- {name}: {skill.description}"
            for name, skill in available_skills.items()
        ])
        
        prompt = f"""分析用户查询，规划完成任务所需的步骤。

可用技能:
{skills_desc}

用户查询: {user_query}

请规划详细的执行步骤，以 JSON 数组格式返回，每个步骤包含:
- step_number: 步骤编号
- description: 步骤描述
- skill_needed: 需要的技能名称 (如果需要)
- action: 具体动作
- dependencies: 依赖的前置步骤编号列表"""

        messages = [
            {"role": "system", "content": "你是一个任务规划专家。请以 JSON 格式返回工作流计划。"},
            {"role": "user", "content": prompt}
        ]
        
        response = self.chat(messages, temperature=0.3)
        
        # 尝试解析 JSON
        try:
            import json
            if "```json" in response:
                json_str = response.split("```json")[1].split("```")[0]
            elif "[" in response:
                json_str = response[response.find("["):response.rfind("]")+1]
            else:
                json_str = response
            
            return json.loads(json_str)
        except:
            # 返回单步骤
            return [{
                "step_number": 1,
                "description": user_query,
                "skill_needed": None,
                "action": "execute",
                "dependencies": []
            }]


# 使用示例
if __name__ == "__main__":
    # 初始化 DeepSeek
    llm = DeepSeekLLM(api_key="your-api-key")
    
    # 测试对话
    messages = [
        {"role": "user", "content": "你好，请介绍一下自己"}
    ]
    response = llm.chat(messages)
    print(response)