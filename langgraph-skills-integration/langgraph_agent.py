"""
LangGraph Agent - 使用状态图协调技能执行
"""
from typing import TypedDict, Annotated, List, Dict, Any, Optional
from langgraph.graph import StateGraph, END
from langgraph.graph.message import add_messages
from langchain_core.messages import BaseMessage, HumanMessage, AIMessage, SystemMessage
import subprocess
import os

from skill_discovery import SkillDiscovery, SkillMetadata
from skill_loader import SkillLoader, SkillContent
from deepseek_integration import DeepSeekLLM


class AgentState(TypedDict):
    """Agent 状态定义"""
    # 消息历史
    messages: Annotated[List[BaseMessage], add_messages]
    # 用户原始查询
    user_query: str
    # 发现的所有技能
    available_skills: Dict[str, SkillMetadata]
    # 选中的技能
    selected_skill: Optional[str]
    # 加载的技能内容
    skill_content: Optional[SkillContent]
    # 意图分析结果
    intent_analysis: Optional[Dict[str, Any]]
    # 生成的代码
    generated_code: Optional[str]
    # 执行结果
    execution_result: Optional[str]
    # 工作流步骤
    workflow_steps: List[Dict[str, Any]]
    # 当前步骤
    current_step: int
    # 是否完成
    is_complete: bool
    # 错误信息
    error: Optional[str]


class SkillAgent:
    """基于 LangGraph 的技能 Agent"""
    
    def __init__(self, skills_path: str, deepseek_api_key: str, 
                 deepseek_base_url: str = "https://api.deepseek.com/v1"):
        """
        初始化 Agent
        
        Args:
            skills_path: skills 仓库路径
            deepseek_api_key: DeepSeek API 密钥
            deepseek_base_url: DeepSeek API 基础 URL
        """
        self.skills_path = skills_path
        self.discovery = SkillDiscovery(skills_path)
        self.loader = SkillLoader(skills_path)
        self.llm = DeepSeekLLM(deepseek_api_key, deepseek_base_url)
        
        # 构建状态图
        self.graph = self._build_graph()
        self.app = self.graph.compile()
    
    def _build_graph(self) -> StateGraph:
        """构建 LangGraph 状态图"""
        workflow = StateGraph(AgentState)
        
        # 添加节点
        workflow.add_node("discover_skills", self._discover_skills)
        workflow.add_node("select_skill", self._select_skill)
        workflow.add_node("load_skill", self._load_skill)
        workflow.add_node("analyze_intent", self._analyze_intent)
        workflow.add_node("generate_code", self._generate_code)
        workflow.add_node("execute_code", self._execute_code)
        workflow.add_node("handle_error", self._handle_error)
        workflow.add_node("finalize", self._finalize)
        
        # 定义流程
        workflow.set_entry_point("discover_skills")
        
        # discover_skills -> select_skill
        workflow.add_edge("discover_skills", "select_skill")
        
        # select_skill -> load_skill 或 finalize (没有找到合适技能)
        workflow.add_conditional_edges(
            "select_skill",
            lambda state: "load_skill" if state["selected_skill"] else "finalize"
        )
        
        # load_skill -> analyze_intent
        workflow.add_edge("load_skill", "analyze_intent")
        
        # analyze_intent -> generate_code
        workflow.add_edge("analyze_intent", "generate_code")
        
        # generate_code -> execute_code
        workflow.add_edge("generate_code", "execute_code")
        
        # execute_code -> finalize 或 handle_error
        workflow.add_conditional_edges(
            "execute_code",
            lambda state: "finalize" if not state["error"] else "handle_error"
        )
        
        # handle_error -> finalize
        workflow.add_edge("handle_error", "finalize")
        
        # finalize -> END
        workflow.add_edge("finalize", END)
        
        return workflow
    
    def _discover_skills(self, state: AgentState) -> AgentState:
        """节点: 发现所有可用技能"""
        print("🔍 发现技能...")
        skills = self.discovery.discover_all_skills()
        state["available_skills"] = skills
        
        # 添加系统消息
        system_msg = SystemMessage(
            content=f"发现 {len(skills)} 个可用技能: {', '.join(skills.keys())}"
        )
        state["messages"].append(system_msg)
        
        return state
    
    def _select_skill(self, state: AgentState) -> AgentState:
        """节点: 选择最合适的技能"""
        print("🎯 选择技能...")
        
        selected = self.llm.select_skill(
            state["user_query"],
            state["available_skills"]
        )
        
        state["selected_skill"] = selected
        
        if selected:
            msg = AIMessage(content=f"选择技能: {selected}")
            print(f"✓ 选择技能: {selected}")
        else:
            msg = AIMessage(content="未找到合适的技能处理此请求")
            print("✗ 未找到合适的技能")
        
        state["messages"].append(msg)
        return state
    
    def _load_skill(self, state: AgentState) -> AgentState:
        """节点: 加载技能内容"""
        print("📥 加载技能内容...")
        
        skill_name = state["selected_skill"]
        if not skill_name:
            return state
        
        skill_metadata = state["available_skills"][skill_name]
        skill_content = self.loader.load_skill(skill_metadata)
        state["skill_content"] = skill_content
        
        msg = AIMessage(content=f"已加载技能: {skill_name}")
        state["messages"].append(msg)
        print(f"✓ 已加载技能: {skill_name}")
        
        return state
    
    def _analyze_intent(self, state: AgentState) -> AgentState:
        """节点: 分析用户意图"""
        print("🧠 分析用户意图...")
        
        skill_content = state["skill_content"]
        context = self.loader.format_skill_context(skill_content)
        
        intent = self.llm.understand_intent(
            state["user_query"],
            context
        )
        
        state["intent_analysis"] = intent
        
        msg = AIMessage(content=f"意图分析完成: {intent.get('intent', 'unknown')}")
        state["messages"].append(msg)
        print(f"✓ 意图: {intent.get('intent', 'unknown')}")
        
        return state
    
    def _generate_code(self, state: AgentState) -> AgentState:
        """节点: 生成代码"""
        print("💻 生成代码...")
        
        skill_content = state["skill_content"]
        context = self.loader.format_skill_context(skill_content)
        
        # 检查是否需要加载参考文档
        intent = state["intent_analysis"]
        if intent and "references_needed" in intent:
            refs = intent["references_needed"]
            context = self.loader.format_skill_context(
                skill_content,
                include_references=True,
                reference_names=refs
            )
        
        code = self.llm.generate_code(
            state["user_query"],
            context
        )
        
        state["generated_code"] = code
        
        msg = AIMessage(content="代码生成完成")
        state["messages"].append(msg)
        print("✓ 代码生成完成")
        
        return state
    
    def _execute_code(self, state: AgentState) -> AgentState:
        """节点: 执行代码"""
        print("🚀 执行代码...")
        
        code = state["generated_code"]
        if not code:
            state["error"] = "没有代码可执行"
            return state
        
        # 保存代码到临时文件
        temp_file = "/tmp/skill_execution.py"
        try:
            with open(temp_file, "w") as f:
                f.write(code)
            
            # 执行代码
            result = subprocess.run(
                ["python", temp_file],
                capture_output=True,
                text=True,
                timeout=30,
                cwd=os.path.dirname(self.skills_path)
            )
            
            if result.returncode == 0:
                state["execution_result"] = result.stdout
                msg = AIMessage(content=f"执行成功:\n{result.stdout}")
                print("✓ 执行成功")
            else:
                state["error"] = result.stderr
                msg = AIMessage(content=f"执行失败:\n{result.stderr}")
                print(f"✗ 执行失败: {result.stderr}")
            
            state["messages"].append(msg)
            
        except Exception as e:
            state["error"] = str(e)
            msg = AIMessage(content=f"执行错误: {e}")
            state["messages"].append(msg)
            print(f"✗ 执行错误: {e}")
        
        return state
    
    def _handle_error(self, state: AgentState) -> AgentState:
        """节点: 处理错误"""
        print("⚠️ 处理错误...")
        
        error = state["error"]
        msg = AIMessage(content=f"遇到错误，正在尝试修复: {error}")
        state["messages"].append(msg)
        
        # 这里可以添加错误恢复逻辑
        # 例如：重新生成代码、尝试其他技能等
        
        return state
    
    def _finalize(self, state: AgentState) -> AgentState:
        """节点: 完成任务"""
        print("✅ 任务完成")
        
        state["is_complete"] = True
        
        # 生成最终响应
        if state["execution_result"]:
            final_msg = AIMessage(
                content=f"任务完成！\n\n结果:\n{state['execution_result']}"
            )
        elif state["error"]:
            final_msg = AIMessage(
                content=f"任务失败: {state['error']}"
            )
        elif not state["selected_skill"]:
            final_msg = AIMessage(
                content="未找到合适的技能处理此请求。请尝试更具体的描述。"
            )
        else:
            final_msg = AIMessage(content="任务处理完成")
        
        state["messages"].append(final_msg)
        
        return state
    
    def run(self, user_query: str) -> str:
        """
        运行 Agent 处理用户查询
        
        Args:
            user_query: 用户查询
            
        Returns:
            处理结果
        """
        print(f"\n{'='*60}")
        print(f"用户查询: {user_query}")
        print(f"{'='*60}\n")
        
        # 初始化状态
        initial_state: AgentState = {
            "messages": [HumanMessage(content=user_query)],
            "user_query": user_query,
            "available_skills": {},
            "selected_skill": None,
            "skill_content": None,
            "intent_analysis": None,
            "generated_code": None,
            "execution_result": None,
            "workflow_steps": [],
            "current_step": 0,
            "is_complete": False,
            "error": None
        }
        
        # 运行状态图
        final_state = self.app.invoke(initial_state)
        
        # 返回最终消息
        if final_state["messages"]:
            return final_state["messages"][-1].content
        return "处理完成"
    
    def get_state_history(self) -> List[Dict]:
        """获取状态历史（用于调试）"""
        return []


# 使用示例
if __name__ == "__main__":
    # 初始化 Agent
    agent = SkillAgent(
        skills_path="../",  # skills 仓库路径
        deepseek_api_key="your-api-key"
    )
    
    # 测试查询
    queries = [
        "帮我合并两个 PDF 文件",
        "创建一个 Slack GIF，显示一个弹跳的笑脸",
        "分析这个 Excel 文件的数据"
    ]
    
    for query in queries:
        result = agent.run(query)
        print(f"\n最终结果:\n{result}\n")
        print("-" * 60)