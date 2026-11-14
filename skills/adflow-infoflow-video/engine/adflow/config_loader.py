"""
全局配置加载器
- 从 config.yaml 读取配置
- 环境变量覆盖（> config.yaml）
- 提供 Config 单例供整个应用使用
"""

import copy
import os
from pathlib import Path
from typing import Any

from ruamel.yaml import YAML

# save() 时剔除的敏感键（密钥只走 os.environ，禁止落盘 config.yaml）
_SENSITIVE_KEYS = frozenset({"api_key", "access_token", "secret", "password", "token"})

# round-trip 模式：load/save 保留注释（中文注释 + 键内联注释）
_yaml_rt = YAML()
_yaml_rt.preserve_quotes = True
_yaml_rt.width = 4096


class Config:
    """全局配置单例"""

    _instance: "Config | None" = None
    _data: dict[str, Any] = {}
    _config_path: str = ""

    def __new__(cls) -> "Config":
        if cls._instance is None:
            cls._instance = super().__new__(cls)
        return cls._instance

    def __init__(self) -> None:
        # 首次实例化时自动加载配置（脚本/CLI 无需手动 load）
        if not self._data:
            self.load()

    def load(self, config_path: str | None = None) -> None:
        """加载配置文件（最多调用一次）"""
        if self._data:
            return  # 已加载，跳过

        if config_path is None:
            # 默认：adflow 包同级的 config.yaml
            config_path = str(Path(__file__).parent.parent / "config.yaml")

        self._config_path = config_path
        with open(config_path, "r", encoding="utf-8") as f:
            self._data = _yaml_rt.load(f) or {}

        # 加载 .env 文件
        self._load_dotenv()

        # 环境变量覆盖（最高优先级）
        if api_key := os.environ.get("DASHSCOPE_API_KEY"):
            self._data.setdefault("llm", {})["api_key"] = api_key

    @staticmethod
    def _load_dotenv() -> None:
        """加载项目 .env 文件到 os.environ"""
        env_path = Path(__file__).parent.parent / ".env"
        if not env_path.exists():
            return
        try:
            with open(env_path, "r", encoding="utf-8") as f:
                for line in f:
                    line = line.strip()
                    if not line or line.startswith("#") or "=" not in line:
                        continue
                    key, _, value = line.partition("=")
                    key = key.strip()
                    value = value.strip().strip('"').strip("'")
                    if key and value and key not in os.environ:
                        os.environ[key] = value
        except Exception:
            pass  # .env 加载失败不阻塞启动

    @staticmethod
    def save_env(updates: dict[str, str]) -> None:
        """把 key=value 写回 .env 并同步 os.environ（设置页保存 API Key 用）

        只更新给了非空值的键；没提到的键原样保留。
        """
        env_path = Path(__file__).parent.parent / ".env"
        lines: list[str] = []
        if env_path.exists():
            try:
                with open(env_path, "r", encoding="utf-8") as f:
                    lines = f.read().splitlines()
            except Exception:
                lines = []
        remaining = {k: v for k, v in updates.items() if v}
        out: list[str] = []
        seen: set[str] = set()
        for line in lines:
            stripped = line.strip()
            key = stripped.partition("=")[0].strip() if "=" in stripped else ""
            if key in remaining:
                out.append(f"{key}={remaining[key]}")
                os.environ[key] = remaining[key]
                seen.add(key)
            else:
                out.append(line)
        for key, val in remaining.items():
            if key not in seen:
                out.append(f"{key}={val}")
                os.environ[key] = val
        try:
            with open(env_path, "w", encoding="utf-8") as f:
                f.write("\n".join(out) + "\n")
        except Exception:
            pass  # 写失败只影响持久化，本次运行仍用 os.environ

    def get(self, key_path: str, default: Any = None) -> Any:
        """通过点分隔路径获取配置值，如 get("editing.subtitle.font")"""
        keys = key_path.split(".")
        node = self._data
        for k in keys:
            if isinstance(node, dict):
                node = node.get(k)
            else:
                return default
            if node is None:
                return default
        return node

    def save(self) -> None:
        """保存当前配置到 config.yaml（保留注释，剔除敏感键，密钥只走 os.environ）"""
        if not self._config_path:
            return
        data = copy.deepcopy(self._data)
        self._strip_sensitive_inplace(data)
        with open(self._config_path, "w", encoding="utf-8") as f:
            _yaml_rt.dump(data, f)

    @classmethod
    def _strip_sensitive_inplace(cls, node: Any) -> None:
        """就地剔除敏感键（api_key/access_token 等），保留 ruamel 注释结构"""
        if isinstance(node, dict):
            for k in list(node.keys()):
                if k in _SENSITIVE_KEYS:
                    del node[k]
                else:
                    cls._strip_sensitive_inplace(node[k])
        elif isinstance(node, list):
            for v in node:
                cls._strip_sensitive_inplace(v)

    def set(self, key_path: str, value: Any) -> None:
        """通过点分隔路径设置配置值，如 set(\"editing.subtitle.font\", \"xxx.ttf\")"""
        keys = key_path.split(".")
        node = self._data
        for k in keys[:-1]:
            node = node.setdefault(k, {})
        node[keys[-1]] = value

    @property
    def db_path(self) -> str:
        return self._resolve_path(self.get("paths.db_path", "./data/adflow.db"))

    @property
    def materials_dir(self) -> str:
        return self._resolve_path(self.get("paths.materials_dir", "./materials"))

    @property
    def output_dir(self) -> str:
        return self._resolve_path(self.get("paths.output_dir", "./output"))

    @property
    def bgm_dir(self) -> str:
        return self._resolve_path(self.get("paths.bgm_dir", "./bgm_library"))

    @property
    def log_dir(self) -> str:
        return self._resolve_path(self.get("paths.log_dir", "./data/logs"))

    @property
    def llm_model(self) -> str:
        return self.get("llm.model", "qwen-max")

    @property
    def llm_max_tokens(self) -> int:
        return self.get("llm.max_tokens", 4096)

    @property
    def llm_temperature(self) -> float:
        return self.get("llm.temperature", 0.7)

    @property
    def llm_api_key(self) -> str:
        return self.get("llm.api_key", "")

    @property
    def llm_base_url(self) -> str:
        return self.get("llm.base_url", "https://dashscope.aliyuncs.com/compatible-mode/v1")

    @property
    def tts_voice(self) -> str:
        return self.get("tts.voice", "longxiaoxia")

    @property
    def tts_config(self) -> dict:
        return self.get("tts", {})

    @property
    def tts_speech_rate(self) -> float:
        return self.get("tts.speech_rate", 1.0)

    @property
    def tts_volume(self) -> int:
        return self.get("tts.volume", 50)

    @property
    def color_grade_config(self) -> dict:
        return self.get("color_grade", {})

    @property
    def diversity_config(self) -> dict:
        return self.get("diversity", {})

    @property
    def editing_config(self) -> dict:
        return self.get("editing", {})

    @property
    def platform_config(self) -> dict:
        return self.get("platform_defaults", {})

    def platform_default(self, platform: str) -> dict:
        return self.get(f"platform_defaults.{platform}", {})

    def _resolve_path(self, path: str) -> str:
        """相对路径 → 基于项目根目录的绝对路径"""
        if os.path.isabs(path):
            return path
        root = Path(__file__).parent.parent
        return str((root / path).resolve())

    def ensure_dirs(self) -> None:
        """确保所有配置的目录存在"""
        for d in [self.db_path, self.materials_dir, self.output_dir,
                  self.bgm_dir, self.log_dir]:
            parent = os.path.dirname(d)
            if parent:
                os.makedirs(parent, exist_ok=True)
            if not os.path.splitext(d)[1]:  # 无后缀 → 目录
                os.makedirs(d, exist_ok=True)


# 全局实例
config = Config()
