"""
技能发现器 - 扫描和索引 Skills 仓库
"""
import os
import yaml
from pathlib import Path
from typing import Dict, List, Optional
from dataclasses import dataclass, asdict


@dataclass
class SkillMetadata:
    """技能元数据"""
    name: str
    description: str
    license: Optional[str] = None
    allowed_tools: Optional[List[str]] = None
    metadata: Optional[Dict] = None
    skill_path: str = ""
    has_scripts: bool = False
    has_references: bool = False
    has_assets: bool = False


class SkillDiscovery:
    """技能发现和索引系统"""
    
    def __init__(self, skills_root: str):
        """
        初始化技能发现器
        
        Args:
            skills_root: skills 仓库的根目录路径
        """
        self.skills_root = Path(skills_root)
        self.skills_index: Dict[str, SkillMetadata] = {}
        
    def discover_all_skills(self) -> Dict[str, SkillMetadata]:
        """
        发现所有技能
        
        Returns:
            技能名称到元数据的映射
        """
        if not self.skills_root.exists():
            raise ValueError(f"Skills 目录不存在: {self.skills_root}")
        
        # 遍历所有子目录
        for item in self.skills_root.iterdir():
            if item.is_dir() and not item.name.startswith('.'):
                skill_md = item / "SKILL.md"
                if skill_md.exists():
                    metadata = self._parse_skill_md(skill_md, item)
                    if metadata:
                        self.skills_index[metadata.name] = metadata
        
        return self.skills_index
    
    def _parse_skill_md(self, skill_md_path: Path, skill_dir: Path) -> Optional[SkillMetadata]:
        """
        解析 SKILL.md 文件的 YAML frontmatter
        
        Args:
            skill_md_path: SKILL.md 文件路径
            skill_dir: 技能目录路径
            
        Returns:
            技能元数据或 None
        """
        try:
            with open(skill_md_path, 'r', encoding='utf-8') as f:
                content = f.read()
            
            # 解析 YAML frontmatter
            if content.startswith('---'):
                parts = content.split('---', 2)
                if len(parts) >= 3:
                    yaml_content = parts[1]
                    frontmatter = yaml.safe_load(yaml_content)
                    
                    # 检查必需字段
                    if 'name' not in frontmatter or 'description' not in frontmatter:
                        print(f"警告: {skill_md_path} 缺少必需字段")
                        return None
                    
                    # 检查子目录
                    has_scripts = (skill_dir / "scripts").exists()
                    has_references = (skill_dir / "references").exists()
                    has_assets = (skill_dir / "assets").exists()
                    
                    return SkillMetadata(
                        name=frontmatter['name'],
                        description=frontmatter['description'],
                        license=frontmatter.get('license'),
                        allowed_tools=frontmatter.get('allowed-tools'),
                        metadata=frontmatter.get('metadata'),
                        skill_path=str(skill_dir),
                        has_scripts=has_scripts,
                        has_references=has_references,
                        has_assets=has_assets
                    )
        except Exception as e:
            print(f"解析 {skill_md_path} 时出错: {e}")
            return None
    
    def search_skills(self, query: str) -> List[SkillMetadata]:
        """
        根据查询搜索技能（简单的关键词匹配）
        
        Args:
            query: 搜索查询
            
        Returns:
            匹配的技能列表
        """
        query_lower = query.lower()
        results = []
        
        for skill in self.skills_index.values():
            # 在名称和描述中搜索
            if (query_lower in skill.name.lower() or 
                query_lower in skill.description.lower()):
                results.append(skill)
        
        return results
    
    def get_skill_by_name(self, name: str) -> Optional[SkillMetadata]:
        """
        根据名称获取技能
        
        Args:
            name: 技能名称
            
        Returns:
            技能元数据或 None
        """
        return self.skills_index.get(name)
    
    def get_all_skill_names(self) -> List[str]:
        """获取所有技能名称"""
        return list(self.skills_index.keys())
    
    def get_skills_summary(self) -> str:
        """
        获取所有技能的摘要（用于提供给 LLM）
        
        Returns:
            格式化的技能摘要
        """
        summary = "可用技能列表:\n\n"
        for name, skill in self.skills_index.items():
            summary += f"• {name}: {skill.description}\n"
        return summary
    
    def export_index(self) -> Dict:
        """导出技能索引为字典格式"""
        return {
            name: asdict(skill) 
            for name, skill in self.skills_index.items()
        }


# 使用示例
if __name__ == "__main__":
    # 发现技能
    discovery = SkillDiscovery("../")  # 指向 skills 仓库根目录
    skills = discovery.discover_all_skills()
    
    print(f"发现 {len(skills)} 个技能:\n")
    print(discovery.get_skills_summary())
    
    # 搜索示例
    pdf_skills = discovery.search_skills("pdf")
    print(f"\n与 'pdf' 相关的技能: {[s.name for s in pdf_skills]}")