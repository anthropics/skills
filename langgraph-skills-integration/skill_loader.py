"""
技能加载器 - 按需加载技能内容和资源
"""
from pathlib import Path
from typing import Dict, List, Optional, Any
from dataclasses import dataclass
from skill_discovery import SkillMetadata


@dataclass
class SkillContent:
    """完整的技能内容"""
    metadata: SkillMetadata
    markdown_body: str
    scripts: Dict[str, str] = None  # 脚本名称 -> 脚本路径
    references: Dict[str, str] = None  # 参考文件名 -> 文件路径
    assets: Dict[str, str] = None  # 资源文件名 -> 文件路径


class SkillLoader:
    """技能加载器 - 实现渐进式加载"""
    
    def __init__(self, skills_root: str):
        """
        初始化技能加载器
        
        Args:
            skills_root: skills 仓库的根目录路径
        """
        self.skills_root = Path(skills_root)
        self._cache: Dict[str, SkillContent] = {}
    
    def load_skill(self, metadata: SkillMetadata) -> SkillContent:
        """
        加载完整的技能内容
        
        Args:
            metadata: 技能元数据
            
        Returns:
            完整的技能内容
        """
        # 检查缓存
        if metadata.name in self._cache:
            return self._cache[metadata.name]
        
        skill_path = Path(metadata.skill_path)
        
        # 1. 读取 SKILL.md 的 Markdown 正文
        markdown_body = self._load_markdown_body(skill_path / "SKILL.md")
        
        # 2. 索引 scripts/
        scripts = self._index_directory(skill_path / "scripts") if metadata.has_scripts else {}
        
        # 3. 索引 references/
        references = self._index_directory(skill_path / "references") if metadata.has_references else {}
        
        # 4. 索引 assets/
        assets = self._index_directory(skill_path / "assets") if metadata.has_assets else {}
        
        # 创建 SkillContent
        content = SkillContent(
            metadata=metadata,
            markdown_body=markdown_body,
            scripts=scripts,
            references=references,
            assets=assets
        )
        
        # 缓存
        self._cache[metadata.name] = content
        
        return content
    
    def _load_markdown_body(self, skill_md_path: Path) -> str:
        """
        加载 SKILL.md 的 Markdown 正文（不含 YAML frontmatter）
        
        Args:
            skill_md_path: SKILL.md 文件路径
            
        Returns:
            Markdown 正文内容
        """
        try:
            with open(skill_md_path, 'r', encoding='utf-8') as f:
                content = f.read()
            
            # 跳过 YAML frontmatter
            if content.startswith('---'):
                parts = content.split('---', 2)
                if len(parts) >= 3:
                    return parts[2].strip()
            
            return content
        except Exception as e:
            print(f"读取 {skill_md_path} 时出错: {e}")
            return ""
    
    def _index_directory(self, directory: Path) -> Dict[str, str]:
        """
        索引目录中的文件
        
        Args:
            directory: 目录路径
            
        Returns:
            文件名到完整路径的映射
        """
        if not directory.exists():
            return {}
        
        files = {}
        for file_path in directory.rglob('*'):
            if file_path.is_file() and not file_path.name.startswith('.'):
                # 使用相对于目录的路径作为键
                relative_path = file_path.relative_to(directory)
                files[str(relative_path)] = str(file_path)
        
        return files
    
    def load_reference(self, skill_name: str, reference_name: str) -> Optional[str]:
        """
        加载特定的参考文件内容
        
        Args:
            skill_name: 技能名称
            reference_name: 参考文件名
            
        Returns:
            文件内容或 None
        """
        if skill_name not in self._cache:
            return None
        
        skill = self._cache[skill_name]
        if not skill.references or reference_name not in skill.references:
            return None
        
        try:
            with open(skill.references[reference_name], 'r', encoding='utf-8') as f:
                return f.read()
        except Exception as e:
            print(f"读取参考文件 {reference_name} 时出错: {e}")
            return None
    
    def get_script_path(self, skill_name: str, script_name: str) -> Optional[str]:
        """
        获取脚本的完整路径
        
        Args:
            skill_name: 技能名称
            script_name: 脚本名称
            
        Returns:
            脚本的完整路径或 None
        """
        if skill_name not in self._cache:
            return None
        
        skill = self._cache[skill_name]
        return skill.scripts.get(script_name) if skill.scripts else None
    
    def format_skill_context(self, skill_content: SkillContent, 
                            include_references: bool = False,
                            reference_names: List[str] = None) -> str:
        """
        格式化技能上下文（用于提供给 LLM）
        
        Args:
            skill_content: 技能内容
            include_references: 是否包含参考文件
            reference_names: 要包含的特定参考文件列表
            
        Returns:
            格式化的上下文字符串
        """
        context = f"# 技能: {skill_content.metadata.name}\n\n"
        context += f"描述: {skill_content.metadata.description}\n\n"
        context += "## 技能说明\n\n"
        context += skill_content.markdown_body + "\n\n"
        
        # 可用资源
        if skill_content.scripts:
            context += "## 可用脚本\n"
            for script in skill_content.scripts.keys():
                context += f"- {script}\n"
            context += "\n"
        
        if skill_content.references:
            context += "## 可用参考文档\n"
            for ref in skill_content.references.keys():
                context += f"- {ref}\n"
            context += "\n"
        
        if skill_content.assets:
            context += "## 可用资源文件\n"
            for asset in skill_content.assets.keys():
                context += f"- {asset}\n"
            context += "\n"
        
        # 包含特定参考文件的内容
        if include_references and reference_names:
            context += "## 参考文档内容\n\n"
            for ref_name in reference_names:
                ref_content = self.load_reference(
                    skill_content.metadata.name, 
                    ref_name
                )
                if ref_content:
                    context += f"### {ref_name}\n\n"
                    context += ref_content + "\n\n"
        
        return context
    
    def clear_cache(self):
        """清除缓存"""
        self._cache.clear()


# 使用示例
if __name__ == "__main__":
    from skill_discovery import SkillDiscovery
    
    # 发现和加载技能
    discovery = SkillDiscovery("../")
    skills = discovery.discover_all_skills()
    
    # 加载一个技能
    loader = SkillLoader("../")
    if "pdf" in skills:
        pdf_skill = loader.load_skill(skills["pdf"])
        print(f"加载技能: {pdf_skill.metadata.name}")
        print(f"脚本数量: {len(pdf_skill.scripts) if pdf_skill.scripts else 0}")
        print(f"参考文档数量: {len(pdf_skill.references) if pdf_skill.references else 0}")
        
        # 格式化上下文
        context = loader.format_skill_context(pdf_skill)
        print(f"\n上下文长度: {len(context)} 字符")