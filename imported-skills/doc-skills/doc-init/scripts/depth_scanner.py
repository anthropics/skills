#!/usr/bin/env python3
"""
doc-init 深度知识提取脚本。

读取 project_inventory.py 输出的 inventory JSON，按检测到的语言栈
用正则机械提取以下模式（不做业务判断）：
  - 状态枚举（status_patterns）
  - 并发控制（concurrency_patterns）
  - 事件/消息（event_patterns）
  - 框架组件注册（framework_components）
  - 软删除标记（soft_delete_patterns）
  - 幂等标记（idempotency_patterns）
  - 可运行项目元数据（runnable_project）
  - 热点文件（hot_files）

用法：
  python3 depth_scanner.py --root <project_root> --inventory <inventory.json> --output <depth_scan.json>
"""

from __future__ import annotations

import argparse
import json
import os
import re
import subprocess
import time
import warnings
from datetime import datetime, timezone
from pathlib import Path
from typing import Any

# ---------------------------------------------------------------------------
# 跳过目录（与 project_inventory.py 保持一致）
# ---------------------------------------------------------------------------
IGNORE_DIRS = {
    ".git",
    ".idea",
    ".vscode",
    ".claude",
    ".agents",
    ".codex",
    ".codegraph",
    ".gradle",
    ".mvn",
    ".venv",
    "venv",
    "env",
    "__pycache__",
    "node_modules",
    "target",
    "build",
    "dist",
    "out",
    ".next",
    ".nuxt",
    "coverage",
    ".pytest_cache",
    "vendor",
}

# 大文件只读前 N 行
LARGE_FILE_LINE_LIMIT = 500
LARGE_FILE_BYTE_LIMIT = 100 * 1024  # 100 KB

# 每类结果最多收录数量，防止输出过大
RESULT_LIMIT = 200

# 总运行时间上限（秒）
TIMEOUT_SECONDS = 30

# ---------------------------------------------------------------------------
# 多语言正则模式配置
# ---------------------------------------------------------------------------

# 每个语言族的模式字典，key 对应输出字段名
# value 是 (compiled_pattern, 用途说明)
LANG_PATTERNS: dict[str, dict[str, list[tuple[re.Pattern[str], str]]]] = {
    "java_kotlin": {
        "status": [
            (re.compile(r"enum\s+\w*(?:Status|State)\w*", re.I), "Java/Kotlin 状态枚举"),
        ],
        "concurrency": [
            (re.compile(r"@Version\b"), "JPA/Hibernate 乐观锁 @Version"),
            (re.compile(r"synchronized\s*\(|ReentrantLock|StampedLock"), "Java 显式锁"),
        ],
        "event": [
            (re.compile(r"class\s+\w+Event\b"), "事件类定义"),
            (re.compile(r"@(?:EventListener|TransactionalEventListener)\b"), "Spring 事件监听"),
            (re.compile(r"publishEvent\s*\(|applicationEventPublisher\.publish", re.I), "Spring 事件发布"),
            (re.compile(r"@(?:RabbitListener|KafkaListener)\b"), "MQ 监听注解"),
        ],
        "component": [
            (re.compile(r'@LiteflowComponent\s*\('), "LiteFlow 组件注册"),
            (re.compile(r'@(?:Component|Service|Controller|RestController)\s*\(\s*(?:value\s*=\s*)?["\']'), "Spring 具名 Bean"),
            (re.compile(r"@Scheduled\b"), "Spring 定时任务"),
        ],
        "idempotency": [
            (re.compile(r"idempotent|dedup|idempotentId|timingIdempotentId", re.I), "幂等字段/标记"),
        ],
        "soft_delete": [
            (re.compile(r"biz_status|is_deleted|deleted_at|isDeleted", re.I), "软删除字段"),
            (re.compile(r"\.ne\s*\(.*?DELETED", re.I), "MyBatis-Plus ne(DELETED) 查询"),
        ],
        "sharding": [
            (re.compile(r"BusinessContextHolder|ShardingContext", re.I), "分表上下文持有"),
            (re.compile(r"@TableName\s*\("), "MyBatis-Plus @TableName"),
        ],
    },
    "python": {
        "status": [
            (re.compile(r"class\s+\w*(?:Status|State)\s*[\w(,\s]*(?:Enum|IntEnum)\b"), "Python 状态枚举"),
            (re.compile(r"STATUS_CHOICES\s*="), "Django choices 模式"),
        ],
        "concurrency": [
            (re.compile(r"version_id|_version\b|select_for_update\s*\("), "Python ORM 乐观锁"),
        ],
        "event": [
            (re.compile(r"signal\.\w+\.connect|@receiver\s*\("), "Django signal"),
            (re.compile(r"celery\.task|@app\.task|@shared_task"), "Celery 任务"),
            (re.compile(r"publish_event|event_bus\.publish", re.I), "事件总线发布"),
        ],
        "component": [
            (re.compile(r"@app\.route\s*\(|@router\."), "Flask/FastAPI 路由"),
            (re.compile(r"@dramatiq\.actor|@celery\.task"), "Dramatiq/Celery Actor"),
        ],
        "idempotency": [
            (re.compile(r"idempotency_key|get_or_create\s*\(", re.I), "幂等 key / get_or_create"),
            (re.compile(r"ON CONFLICT", re.I), "SQL ON CONFLICT 幂等"),
        ],
        "soft_delete": [
            (re.compile(r"is_deleted|deleted_at|SoftDeletable"), "Python 软删除字段"),
            (re.compile(r"objects\.filter.*\.exclude.*deleted", re.I), "Django 软删除查询"),
        ],
        "sharding": [
            (re.compile(r"tenant_id|schema_name|connection\.set_schema", re.I), "多租户/分库路由"),
        ],
    },
    "typescript_javascript": {
        "status": [
            (re.compile(r"enum\s+\w*Status\b"), "TS 状态枚举"),
            (re.compile(r"type\s+\w*Status\s*=|Status\s*=\s*\{"), "TS 联合类型/对象状态"),
        ],
        "concurrency": [
            (re.compile(r"@VersionColumn\(\)|version.*:\s*number", re.I), "TypeORM 乐观锁"),
            (re.compile(r"optimisticLock|_version\b", re.I), "乐观锁标记"),
        ],
        "event": [
            (re.compile(r"EventEmitter|\.emit\s*\(|\.on\s*\("), "Node.js EventEmitter"),
            (re.compile(r"@OnEvent\s*\(|pubSub\.publish|eventBus\.emit", re.I), "事件发布/订阅"),
        ],
        "component": [
            (re.compile(r"@(?:Controller|Injectable|Module)\s*\("), "NestJS 装饰器"),
            (re.compile(r'app\.(?:get|post|put|delete|patch)\s*\(|router\.(?:get|post|put)'), "Express/Koa 路由"),
        ],
        "idempotency": [
            (re.compile(r"idempotencyKey|idempotent|upsert\s*\(", re.I), "幂等 key / upsert"),
            (re.compile(r"ON CONFLICT", re.I), "SQL ON CONFLICT"),
        ],
        "soft_delete": [
            (re.compile(r"deletedAt|isDeleted|@DeleteDateColumn", re.I), "TS 软删除字段"),
            (re.compile(r"withDeleted\s*\(\)", re.I), "TypeORM withDeleted"),
        ],
        "sharding": [
            (re.compile(r"tenantId|cls\.schema|setSchema|multiTenancy", re.I), "多租户/分库路由"),
        ],
    },
    "go": {
        "status": [
            (re.compile(r"Status\w+\s+(?:int|string)|State\w+\s+(?:int|string)"), "Go 状态常量类型"),
            (re.compile(r"iota.*(?:Status|State)", re.I), "Go iota 状态枚举"),
            (re.compile(r"type\s+\w*Status\s+(?:int|string)\b"), "Go 命名状态类型"),
        ],
        "concurrency": [
            (re.compile(r"version\s+(?:int|int64)|Version\s+(?:int|int64)"), "Go 版本号乐观锁"),
            (re.compile(r"sync\.Mutex|sync\.RWMutex|atomic\."), "Go 同步原语"),
            (re.compile(r"\.CAS\s*\(|compare_and_swap", re.I), "CAS 操作"),
        ],
        "event": [
            (re.compile(r"chan\s+\w*Event"), "Go channel 事件"),
            (re.compile(r"\.Publish\s*\(|\.Subscribe\s*\("), "发布/订阅调用"),
            (re.compile(r"nats\.Conn|amqp\.Channel"), "NATS/AMQP"),
        ],
        "component": [
            (re.compile(r"func\s+init\s*\(\s*\)"), "Go init 注册"),
            (re.compile(r"http\.Handle\s*\(|mux\.Handle\s*\("), "Go HTTP 路由"),
            (re.compile(r'gin\.(?:GET|POST|PUT|DELETE)\s*\(|echo\.(?:GET|POST)'), "Gin/Echo 路由"),
        ],
        "idempotency": [
            (re.compile(r"idempotent|SetNX\s*\(|setnx\b", re.I), "Redis SetNX 幂等"),
            (re.compile(r"InsertOrUpdate|UPSERT\b", re.I), "Upsert 幂等"),
        ],
        "soft_delete": [
            (re.compile(r"deleted_at|IsDeleted|gorm\.DeletedAt"), "GORM 软删除"),
            (re.compile(r"Unscoped\s*\(\)"), "GORM Unscoped"),
        ],
        "sharding": [
            (re.compile(r"context\.Value\s*\(|WithValue.*tenant", re.I), "context 分片路由"),
            (re.compile(r"shardKey|partition\b", re.I), "分片键"),
        ],
    },
    "csharp_dotnet": {
        "status": [
            (re.compile(r"enum\s+\w*(?:Status|State)\b"), "C# 状态枚举"),
            (re.compile(r"\[Flags\]\s*\n\s*enum\b"), "C# Flags 枚举"),
        ],
        "concurrency": [
            (re.compile(r"\[ConcurrencyCheck\]|\[Timestamp\]|IsRowVersion\s*\("), "EF Core 并发标记"),
            (re.compile(r"Interlocked\.|Monitor\.Enter|SemaphoreSlim"), ".NET 并发原语"),
        ],
        "event": [
            (re.compile(r"INotification\b|IMediator\b"), "MediatR 事件/命令"),
            (re.compile(r"\.Publish\s*\(|DomainEvent\b|EventHandler\b"), "领域事件"),
        ],
        "component": [
            (re.compile(r"\[(?:ApiController|HttpGet|HttpPost|HttpPut|HttpDelete)\]"), "ASP.NET Controller"),
            (re.compile(r"services\.Add|builder\.Services\.Add"), ".NET DI 注册"),
        ],
        "idempotency": [
            (re.compile(r"IdempotencyKey|idempotent", re.I), "幂等 key"),
            (re.compile(r"MERGE\s+INTO|ExecuteUpdateOrInsert", re.I), "Upsert 语句"),
        ],
        "soft_delete": [
            (re.compile(r"IsDeleted|DeletedAt|ISoftDelete\b"), "C# 软删除接口/字段"),
            (re.compile(r"HasQueryFilter.*!.*[Ii]s[Dd]eleted"), "EF Core 全局过滤"),
        ],
        "sharding": [
            (re.compile(r"ITenantProvider|TenantId|UseDatabasePerTenant", re.I), "多租户路由"),
            (re.compile(r"IMultiTenantDbContext"), "多租户 DbContext"),
        ],
    },
}

# 语言标签 → 模式族映射（来自 project_inventory.py 的 language 字段）
LANG_TO_PATTERN_KEY: dict[str, str] = {
    "Java": "java_kotlin",
    "Kotlin": "java_kotlin",
    "Python": "python",
    "TypeScript": "typescript_javascript",
    "JavaScript": "typescript_javascript",
    "Go": "go",
    "C#/.NET": "csharp_dotnet",
    "F#/.NET": "csharp_dotnet",
}

# 文件扩展名 → 语言标签
EXT_TO_LANG: dict[str, str] = {
    ".java": "Java",
    ".kt": "Kotlin",
    ".kts": "Kotlin",
    ".py": "Python",
    ".ts": "TypeScript",
    ".tsx": "TypeScript",
    ".js": "JavaScript",
    ".jsx": "JavaScript",
    ".go": "Go",
    ".cs": "C#/.NET",
    ".fs": "F#/.NET",
}


# ---------------------------------------------------------------------------
# 状态枚举值提取（Java/Kotlin/Go/C#/Python/TS 通用）
# ---------------------------------------------------------------------------

# 匹配枚举块 { ... }，只取前 2000 字符避免跨块匹配
_ENUM_BODY_RE = re.compile(r"\{([^{}]{0,2000})\}", re.S)
# 枚举值：全大写下划线 或 SCREAMING_SNAKE + 可选括号
_ENUM_VALUE_RE = re.compile(r"\b([A-Z][A-Z0-9_]{1,40})\b")


def extract_enum_values(text: str, start: int) -> list[str]:
    """从 start 位置之后提取枚举值列表（最多取前 20 个全大写成员）。"""
    fragment = text[start : start + 2000]
    m = _ENUM_BODY_RE.search(fragment)
    if not m:
        return []
    body = m.group(1)
    values = _ENUM_VALUE_RE.findall(body)
    # 过滤掉 Java 关键字等噪声
    stop_words = {"NULL", "TRUE", "FALSE", "VOID", "INT", "LONG", "STRING", "BYTE"}
    return [v for v in values if v not in stop_words][:20]


# ---------------------------------------------------------------------------
# 文件迭代
# ---------------------------------------------------------------------------

def iter_source_files(root: Path, active_exts: set[str]) -> list[Path]:
    """遍历源码文件，跳过忽略目录，只返回 active_exts 中的扩展名。"""
    result: list[Path] = []
    for current, dirs, names in os.walk(root):
        dirs[:] = sorted(d for d in dirs if d not in IGNORE_DIRS and not d.startswith(".cache"))
        for name in sorted(names):
            ext = Path(name).suffix.lower()
            if ext in active_exts:
                result.append(Path(current) / name)
    return result


def read_file_lines(path: Path) -> list[str]:
    """读取文件，大文件只读前 LARGE_FILE_LINE_LIMIT 行。"""
    try:
        size = path.stat().st_size
        if size > LARGE_FILE_BYTE_LIMIT:
            with path.open("r", encoding="utf-8", errors="ignore") as fh:
                return [fh.readline() for _ in range(LARGE_FILE_LINE_LIMIT)]
        return path.read_text(encoding="utf-8", errors="ignore").splitlines(keepends=True)
    except OSError as e:
        warnings.warn(f"跳过文件 {path}: {e}")
        return []


def read_file_text(path: Path) -> str:
    return "".join(read_file_lines(path))


def rel(path: Path, root: Path) -> str:
    return path.relative_to(root).as_posix()


# ---------------------------------------------------------------------------
# 各类模式扫描
# ---------------------------------------------------------------------------

def scan_status_patterns(
    path: Path, root: Path, text: str, lang_key: str, results: list[dict[str, Any]]
) -> None:
    if len(results) >= RESULT_LIMIT:
        return
    patterns = LANG_PATTERNS.get(lang_key, {}).get("status", [])
    for pattern, _ in patterns:
        for m in pattern.finditer(text):
            values = extract_enum_values(text, m.end())
            results.append({
                "file": rel(path, root),
                "name": m.group(0).strip(),
                "values": values,
                "type": "enum",
            })
            if len(results) >= RESULT_LIMIT:
                return


def scan_concurrency_patterns(
    path: Path, root: Path, text: str, lang_key: str, results: list[dict[str, Any]]
) -> None:
    if len(results) >= RESULT_LIMIT:
        return
    patterns = LANG_PATTERNS.get(lang_key, {}).get("concurrency", [])
    # 提取 @Version 前后的字段名（Java 场景）
    field_re = re.compile(r"(?:private|protected|public|var|val)\s+\S+\s+(\w+)\s*;")
    for pattern, signal in patterns:
        for m in pattern.finditer(text):
            # 尝试提取临近字段名
            nearby = text[m.start(): m.start() + 200]
            fm = field_re.search(nearby)
            field = fm.group(1) if fm else ""
            results.append({
                "file": rel(path, root),
                "type": "optimistic_lock" if "Version" in signal or "version" in signal else "lock",
                "field": field,
                "signal": m.group(0).strip()[:80],
            })
            if len(results) >= RESULT_LIMIT:
                return


def scan_event_patterns(
    path: Path, root: Path, text: str, lang_key: str, publishers: list[dict[str, Any]]
) -> None:
    if len(publishers) >= RESULT_LIMIT:
        return
    patterns = LANG_PATTERNS.get(lang_key, {}).get("event", [])
    # 提取事件类名（简单：从 class XxxEvent 或 publishEvent(new XxxEvent)）
    event_name_re = re.compile(r"(?:class\s+(\w+Event\b)|publish\w*\s*\(\s*(?:new\s+)?(\w+Event)\b)", re.I)
    for pattern, _ in patterns:
        for m in pattern.finditer(text):
            en_match = event_name_re.search(text[max(0, m.start()-50): m.end()+100])
            event_name = ""
            if en_match:
                event_name = en_match.group(1) or en_match.group(2) or ""
            publishers.append({
                "publisher_file": rel(path, root),
                "event_name": event_name,
                "subscriber_file": "",  # 跨文件关联留空，由 LLM 阶段补充
                "signal": m.group(0).strip()[:80],
            })
            if len(publishers) >= RESULT_LIMIT:
                return


def scan_framework_components(
    path: Path, root: Path, text: str, lang_key: str, results: list[dict[str, Any]]
) -> None:
    if len(results) >= RESULT_LIMIT:
        return
    patterns = LANG_PATTERNS.get(lang_key, {}).get("component", [])
    # LiteFlow 组件 ID 提取
    liteflow_id_re = re.compile(r'@LiteflowComponent\s*\(\s*(?:id\s*=\s*)?["\']([^"\']+)["\'](?:\s*,\s*name\s*=\s*["\']([^"\']+)["\'])?')
    for pattern, comp_type in patterns:
        for m in pattern.finditer(text):
            comp_id = ""
            comp_name = ""
            if "LiteFlow" in comp_type or "liteflow" in comp_type.lower():
                lm = liteflow_id_re.search(text[m.start(): m.start() + 200])
                if lm:
                    comp_id = lm.group(1) or ""
                    comp_name = lm.group(2) or ""
            results.append({
                "file": rel(path, root),
                "type": "liteflow_component" if comp_id else comp_type.lower().replace(" ", "_"),
                "id": comp_id,
                "name": comp_name,
                "signal": m.group(0).strip()[:80],
            })
            if len(results) >= RESULT_LIMIT:
                return


def scan_soft_delete(
    path: Path, root: Path, text: str, lang_key: str, results: list[dict[str, Any]]
) -> None:
    if len(results) >= RESULT_LIMIT:
        return
    patterns = LANG_PATTERNS.get(lang_key, {}).get("soft_delete", [])
    for pattern, _ in patterns:
        if pattern.search(text):
            # 提取第一个匹配的字段名
            m = pattern.search(text)
            results.append({
                "file": rel(path, root),
                "field": m.group(0).strip()[:60] if m else "",
                "signal": m.group(0).strip()[:80] if m else "",
            })
            return  # 每个文件只记录一次


def scan_idempotency(
    path: Path, root: Path, text: str, lang_key: str, results: list[dict[str, Any]]
) -> None:
    if len(results) >= RESULT_LIMIT:
        return
    patterns = LANG_PATTERNS.get(lang_key, {}).get("idempotency", [])
    for pattern, _ in patterns:
        m = pattern.search(text)
        if m:
            results.append({
                "file": rel(path, root),
                "key_field": m.group(0).strip()[:60],
                "signal": m.group(0).strip()[:80],
            })
            return  # 每个文件只记录一次


# ---------------------------------------------------------------------------
# 可运行项目检测
# ---------------------------------------------------------------------------

def _is_ignored_path(path: Path) -> bool:
    """检查路径是否包含应跳过的目录段。"""
    for part in path.parts:
        if part in IGNORE_DIRS:
            return True
    return False


def _rglob_filtered(base: Path, pattern: str) -> list[Path]:
    """rglob 变体，自动跳过 IGNORE_DIRS 中的子树。"""
    return [p for p in base.rglob(pattern) if not _is_ignored_path(p)]


def detect_runnable_project(root: Path) -> dict[str, Any]:
    """检测项目类型、端口、启动命令、日志路径。"""
    result: dict[str, Any] = {
        "type": "unknown",
        "ports": [],
        "start_commands": [],
        "log_paths": [],
    }

    def read_text_safe(p: Path) -> str:
        try:
            return p.read_text(encoding="utf-8", errors="ignore")[:50000]
        except OSError:
            return ""

    # Spring Boot
    for pom in _rglob_filtered(root, "pom.xml"):
        if pom.stat().st_size == 0:
            continue
        text = read_text_safe(pom)
        if "spring-boot-maven-plugin" in text or "spring-boot-starter" in text:
            result["type"] = "spring-boot"
            module_dir = pom.parent
            # 端口：扫描 application*.properties / application*.yml（跳过 target/）
            for prop_path in _rglob_filtered(module_dir, "application*.properties"):
                prop_text = read_text_safe(prop_path)
                m = re.search(r"server\.port\s*=\s*(\d+)", prop_text)
                if m:
                    result["ports"].append({
                        "module": rel(module_dir, root),
                        "port": m.group(1),
                        "source": rel(prop_path, root),
                    })
            for yml_path in _rglob_filtered(module_dir, "application*.yml"):
                yml_text = read_text_safe(yml_path)
                m = re.search(r"port\s*:\s*(\d+)", yml_text)
                if m:
                    result["ports"].append({
                        "module": rel(module_dir, root),
                        "port": m.group(1),
                        "source": rel(yml_path, root),
                    })
            # 启动命令：用 host 模块相对路径
            module_rel = rel(module_dir, root)
            result["start_commands"].append(f"mvn spring-boot:run -pl {module_rel}")
            # 日志路径：只取 src/main 同层的 logs 目录
            for log_dir in _rglob_filtered(module_dir, "logs"):
                if log_dir.is_dir() and not _is_ignored_path(log_dir):
                    result["log_paths"].append(rel(log_dir, root) + "/*.log")
        # 只检测第一个匹配的
        if result["type"] != "unknown":
            break

    # Django
    if result["type"] == "unknown":
        if (root / "manage.py").exists() and any(_rglob_filtered(root, "settings.py")):
            result["type"] = "django"
            result["start_commands"].append("python manage.py runserver")
            for settings in _rglob_filtered(root, "settings.py"):
                text = read_text_safe(settings)
                m = re.search(r"(?:PORT|DJANGO_PORT)\s*=\s*(\d+)", text)
                if m:
                    result["ports"].append({"module": ".", "port": m.group(1), "source": rel(settings, root)})

    # Express / NestJS
    if result["type"] == "unknown":
        pkg = root / "package.json"
        if pkg.exists():
            text = read_text_safe(pkg)
            if '"express"' in text or '"@nestjs/core"' in text or '"fastify"' in text:
                result["type"] = "express"
                result["start_commands"].append("npm start")
                # 扫描 .env 或源码中的 listen(
                for env_file in [root / ".env", root / ".env.local"]:
                    if env_file.exists():
                        env_text = read_text_safe(env_file)
                        m = re.search(r"PORT\s*=\s*(\d+)", env_text)
                        if m:
                            result["ports"].append({"module": ".", "port": m.group(1), "source": rel(env_file, root)})

    # Docker
    if result["type"] == "unknown":
        docker_files = list(root.glob("Dockerfile")) + list(root.glob("docker-compose*.yml"))
        if docker_files:
            result["type"] = "docker"
            for df in docker_files:
                text = read_text_safe(df)
                for m in re.finditer(r"EXPOSE\s+(\d+)", text):
                    result["ports"].append({"module": ".", "port": m.group(1), "source": rel(df, root)})
                for m in re.finditer(r'"(\d+):\d+"', text):
                    result["ports"].append({"module": ".", "port": m.group(1), "source": rel(df, root)})

    # Go
    if result["type"] == "unknown":
        if (root / "go.mod").exists():
            for main_go in _rglob_filtered(root, "main.go"):
                text = read_text_safe(main_go)
                if "http.ListenAndServe" in text or "gin.Default" in text or "echo.New" in text:
                    result["type"] = "go-server"
                    result["start_commands"].append("go run ./...")
                    m = re.search(r'ListenAndServe\s*\(\s*"[^"]*:(\d+)', text)
                    if m:
                        result["ports"].append({"module": rel(main_go.parent, root), "port": m.group(1), "source": rel(main_go, root)})
                    break

    # .NET
    if result["type"] == "unknown":
        csproj_files = list(_rglob_filtered(root, "*.csproj"))
        for csproj in csproj_files:
            text = read_text_safe(csproj)
            if "Microsoft.NET.Sdk.Web" in text:
                result["type"] = "dotnet"
                result["start_commands"].append(f"dotnet run --project {rel(csproj.parent, root)}")
                break

    # library / cli / unknown
    if result["type"] == "unknown":
        if (root / "setup.py").exists() or (root / "pyproject.toml").exists():
            result["type"] = "library"
        elif any(_rglob_filtered(root, "*.py")):
            # 检测 CLI
            for py in list(_rglob_filtered(root, "*.py"))[:50]:
                text = read_text_safe(py)
                if "argparse.ArgumentParser" in text or "click.command" in text:
                    result["type"] = "cli"
                    break

    # 去重端口
    seen_ports: set[str] = set()
    unique_ports = []
    for p in result["ports"]:
        key = f"{p.get('module')}:{p.get('port')}"
        if key not in seen_ports:
            seen_ports.add(key)
            unique_ports.append(p)
    result["ports"] = unique_ports[:30]

    return result


# ---------------------------------------------------------------------------
# 热点文件
# ---------------------------------------------------------------------------

def get_hot_files(root: Path) -> list[dict[str, Any]]:
    """通过 git log 获取修改次数最多的前 20 个文件。"""
    if not (root / ".git").exists():
        return []
    try:
        proc = subprocess.run(
            ["git", "-C", str(root), "log", "--format=", "--name-only"],
            capture_output=True,
            text=True,
            timeout=10,
        )
        if proc.returncode != 0:
            return []
        counter: dict[str, int] = {}
        for line in proc.stdout.splitlines():
            line = line.strip()
            if line:
                counter[line] = counter.get(line, 0) + 1
        return [
            {"file": f, "commit_count": c}
            for f, c in sorted(counter.items(), key=lambda x: -x[1])[:20]
        ]
    except (subprocess.TimeoutExpired, FileNotFoundError):
        return []


# ---------------------------------------------------------------------------
# 可运行项目类型检测
# ---------------------------------------------------------------------------

def detect_runnable_project(root: Path) -> dict[str, Any]:
    """检测项目可运行类型、端口、启动命令和日志路径。"""
    result: dict[str, Any] = {"type": "unknown", "ports": [], "start_commands": [], "log_paths": []}

    # Spring Boot
    for pom in root.rglob("pom.xml"):
        try:
            text = pom.read_text(encoding="utf-8", errors="ignore")[:8000]
            if "spring-boot-maven-plugin" in text:
                result["type"] = "spring-boot"
                module = str(pom.parent.relative_to(root))
                result["start_commands"].append(f"mvn spring-boot:run -pl {module}")
                for prop_file in pom.parent.rglob("application*.properties"):
                    try:
                        for line in prop_file.read_text(encoding="utf-8", errors="ignore").splitlines():
                            if "server.port" in line and "=" in line:
                                port = line.split("=", 1)[1].strip()
                                result["ports"].append({"module": module, "port": port, "source": str(prop_file.relative_to(root))})
                    except OSError:
                        pass
                for yml_file in pom.parent.rglob("application*.yml"):
                    try:
                        for line in yml_file.read_text(encoding="utf-8", errors="ignore").splitlines():
                            if "port:" in line:
                                port = line.split("port:", 1)[1].strip()
                                if port.isdigit():
                                    result["ports"].append({"module": module, "port": port, "source": str(yml_file.relative_to(root))})
                    except OSError:
                        pass
                for log_cfg in pom.parent.rglob("logback*.xml"):
                    result["log_paths"].append(str(log_cfg.relative_to(root)))
                break
        except OSError:
            continue

    if result["type"] != "unknown":
        return result

    # Django
    if (root / "manage.py").exists() and any(root.rglob("settings.py")):
        result["type"] = "django"
        result["start_commands"].append("python manage.py runserver")
        return result

    # Express / NestJS
    pkg_json = root / "package.json"
    if pkg_json.exists():
        try:
            pkg = json.loads(pkg_json.read_text(encoding="utf-8"))
            deps = {**pkg.get("dependencies", {}), **pkg.get("devDependencies", {})}
            if "express" in deps or "@nestjs/core" in deps:
                result["type"] = "express"
                scripts = pkg.get("scripts", {})
                for key in ("start", "dev", "serve"):
                    if key in scripts:
                        result["start_commands"].append(f"npm run {key}")
                return result
        except (json.JSONDecodeError, OSError):
            pass

    # Docker
    if (root / "Dockerfile").exists() or (root / "docker-compose.yml").exists() or (root / "docker-compose.yaml").exists():
        result["type"] = "docker"
        if (root / "docker-compose.yml").exists():
            result["start_commands"].append("docker-compose up")
        elif (root / "docker-compose.yaml").exists():
            result["start_commands"].append("docker-compose up")
        return result

    # Go server
    for main_go in root.rglob("main.go"):
        try:
            text = main_go.read_text(encoding="utf-8", errors="ignore")[:5000]
            if "ListenAndServe" in text or "gin." in text or "mux." in text or "fiber." in text:
                result["type"] = "go-server"
                result["start_commands"].append(f"go run {main_go.relative_to(root)}")
                return result
        except OSError:
            continue

    # .NET Web
    for csproj in root.rglob("*.csproj"):
        try:
            text = csproj.read_text(encoding="utf-8", errors="ignore")[:3000]
            if "Microsoft.NET.Sdk.Web" in text:
                result["type"] = "dotnet"
                result["start_commands"].append("dotnet run")
                return result
        except OSError:
            continue

    # Library / CLI detection
    if (root / "setup.py").exists() or (root / "pyproject.toml").exists():
        result["type"] = "library"
    elif pkg_json.exists():
        result["type"] = "library"

    return result


# ---------------------------------------------------------------------------
# 实体字段提取（entity_fields）
# ---------------------------------------------------------------------------

# 各语言栈的实体标记和字段提取正则
_ENTITY_MARKERS: dict[str, list[re.Pattern[str]]] = {
    "java_kotlin": [
        re.compile(r'@TableName\s*\(\s*["\']([^"\']+)'),  # MyBatis-Plus
        re.compile(r'@Entity\b'),  # JPA
        re.compile(r'@Table\s*\(\s*name\s*=\s*["\']([^"\']+)'),  # JPA @Table
    ],
    "python": [
        re.compile(r'class\s+\w+\(.*?models\.Model\)', re.I),  # Django
        re.compile(r'__tablename__\s*=\s*["\']([^"\']+)'),  # SQLAlchemy
    ],
    "typescript_javascript": [
        re.compile(r'@Entity\s*\('),  # TypeORM
        re.compile(r'model\s+\w+\s*\{'),  # Prisma schema
    ],
    "go": [
        re.compile(r'TableName\s*\(\s*\)\s*string\s*\{'),  # GORM TableName()
        re.compile(r'`.*?gorm:".*?column:'),  # GORM struct tag
    ],
    "csharp_dotnet": [
        re.compile(r'\[Table\s*\(\s*["\']([^"\']+)'),  # EF [Table]
        re.compile(r'DbSet<\w+>\s+\w+\s*\{'),  # EF DbContext
    ],
}

# Java 字段提取：捕获类型、字段名、以及可能的注解
_JAVA_FIELD_RE = re.compile(
    r'(?:(?:@\w+(?:\([^)]*\))?)\s*)*'  # 可能的注解
    r'(?:private|protected|public)?\s+'
    r'([\w<>,?\s]+?)\s+'  # 类型
    r'(\w+)\s*[;=]',  # 字段名
)
_JAVA_TABLEFIELD_RE = re.compile(r'@TableField\s*\(\s*(?:value\s*=\s*)?["\']([^"\']+)')
_JAVA_VERSION_RE = re.compile(r'@Version\b')
_JAVA_TABLELOGIC_RE = re.compile(r'@TableLogic\b')


def scan_entity_fields(path: Path, root: Path, text: str, lang_key: str,
                       results: list[dict[str, Any]]) -> None:
    """提取实体类的字段列表，包含字段名、类型、注解标记。"""
    if len(results) >= RESULT_LIMIT:
        return

    markers = _ENTITY_MARKERS.get(lang_key, [])
    if not markers:
        return

    is_entity = False
    table_name = ""
    for marker in markers:
        m = marker.search(text)
        if m:
            is_entity = True
            if m.lastindex and m.lastindex >= 1:
                table_name = m.group(1)
            break

    if not is_entity:
        return

    # 提取类名
    class_match = re.search(r'(?:public\s+)?class\s+(\w+)', text)
    class_name = class_match.group(1) if class_match else path.stem

    if lang_key == "java_kotlin":
        fields: list[dict[str, str]] = []
        for line in text.splitlines():
            line_stripped = line.strip()
            # 跳过方法定义和注释
            if line_stripped.startswith("//") or line_stripped.startswith("/*") or line_stripped.startswith("*"):
                continue
            if "(" in line_stripped and ")" in line_stripped and not line_stripped.endswith(";"):
                continue

            fm = _JAVA_FIELD_RE.search(line_stripped)
            if fm:
                field_type = fm.group(1).strip()
                field_name = fm.group(2).strip()
                # 过滤常量和序列化字段
                if field_name.isupper() or field_name == "serialVersionUID":
                    continue
                # 检查特殊注解
                annotations: list[str] = []
                # 向上看 3 行寻找注解
                line_idx = text.find(line_stripped)
                context = text[max(0, line_idx - 200):line_idx]
                if _JAVA_VERSION_RE.search(context):
                    annotations.append("@Version")
                if _JAVA_TABLELOGIC_RE.search(context):
                    annotations.append("@TableLogic")
                col_match = _JAVA_TABLEFIELD_RE.search(context)
                col_name = col_match.group(1) if col_match else ""

                fields.append({
                    "name": field_name,
                    "type": field_type,
                    "column": col_name,
                    "annotations": annotations,
                })

        if fields:
            results.append({
                "file": str(path.relative_to(root)),
                "class": class_name,
                "table": table_name,
                "fields": fields[:50],  # 限制每个实体最多 50 个字段
            })


# ---------------------------------------------------------------------------
# JSON 字段模式检测（json_field_patterns）
# ---------------------------------------------------------------------------

_JSON_PARSE_PATTERNS: dict[str, list[tuple[re.Pattern[str], str]]] = {
    "java_kotlin": [
        (re.compile(r'JSON\.parse(?:Object|Array)\s*\(\s*\w+\.get(\w+)\s*\(\s*\)\s*,\s*(\w+)\.class'), "Fastjson parseObject"),
        (re.compile(r'objectMapper\.readValue\s*\(\s*\w+\.get(\w+)\s*\(\s*\)\s*,\s*(\w+)\.class'), "Jackson readValue"),
        (re.compile(r'typeHandler\s*=\s*JacksonTypeHandler\.class'), "MyBatis-Plus JacksonTypeHandler"),
        (re.compile(r'@TableField\s*\([^)]*typeHandler\s*=\s*(\w+)TypeHandler'), "自定义 TypeHandler"),
    ],
    "python": [
        (re.compile(r'json\.loads\s*\(\s*(?:self|instance|obj)\.(\w+)'), "json.loads 字段解析"),
        (re.compile(r'JSONField\s*\('), "Django JSONField"),
    ],
    "typescript_javascript": [
        (re.compile(r'JSON\.parse\s*\(\s*\w+\.(\w+)'), "JSON.parse 字段解析"),
        (re.compile(r"type:\s*['\"]jsonb?['\"]"), "TypeORM jsonb 列"),
    ],
    "go": [
        (re.compile(r'json\.Unmarshal\s*\(\s*\[\]byte\s*\(\s*\w+\.(\w+)'), "json.Unmarshal 字段"),
        (re.compile(r'`[^`]*gorm:"[^"]*type:jsonb?[^"]*"'), "GORM jsonb tag"),
    ],
    "csharp_dotnet": [
        (re.compile(r'JsonSerializer\.Deserialize<(\w+)>\s*\(\s*\w+\.(\w+)'), "System.Text.Json 反序列化"),
        (re.compile(r'\[Column\s*\(\s*TypeName\s*=\s*["\']jsonb?["\']'), "EF jsonb Column"),
    ],
}


def scan_json_field_patterns(path: Path, root: Path, text: str, lang_key: str,
                             results: list[dict[str, Any]]) -> None:
    """检测 JSON 字段解析模式（String 存 JSON 并反序列化为 DTO 的字段）。"""
    if len(results) >= RESULT_LIMIT:
        return

    patterns = _JSON_PARSE_PATTERNS.get(lang_key, [])
    for pat, desc in patterns:
        for m in pat.finditer(text):
            results.append({
                "file": str(path.relative_to(root)),
                "match": m.group(0)[:120],
                "pattern_type": desc,
                "line": text[:m.start()].count("\n") + 1,
            })
            if len(results) >= RESULT_LIMIT:
                return


# ---------------------------------------------------------------------------
# 主流程
# ---------------------------------------------------------------------------

def run_scan(root: Path, inventory: dict[str, Any]) -> dict[str, Any]:
    start_time = time.monotonic()

    # 从 inventory 提取语言栈（使用原始语言标签，不是内部 key）
    language_stack: list[str] = [item["language"] for item in inventory.get("languages", [])]

    # 确定本次扫描激活的模式族和文件扩展名
    active_lang_keys: set[str] = set()
    active_exts: set[str] = set()
    for lang in language_stack:
        key = LANG_TO_PATTERN_KEY.get(lang)
        if key:
            active_lang_keys.add(key)
    for ext, lang in EXT_TO_LANG.items():
        if LANG_TO_PATTERN_KEY.get(lang) in active_lang_keys:
            active_exts.add(ext)

    # 如果 inventory 为空（直接运行不带 inventory），扫描所有已知扩展名
    if not active_exts:
        active_exts = set(EXT_TO_LANG.keys())
        active_lang_keys = set(LANG_PATTERNS.keys())

    # language_stack 最终输出用原始标签（不是内部 key）
    if not language_stack:
        language_stack = sorted(
            {lang for lang, key in LANG_TO_PATTERN_KEY.items() if key in active_lang_keys}
        )

    files = iter_source_files(root, active_exts)

    status_patterns: list[dict[str, Any]] = []
    concurrency_patterns: list[dict[str, Any]] = []
    event_patterns: list[dict[str, Any]] = []
    framework_components: list[dict[str, Any]] = []
    soft_delete_patterns: list[dict[str, Any]] = []
    idempotency_patterns: list[dict[str, Any]] = []
    entity_fields: list[dict[str, Any]] = []
    json_field_patterns: list[dict[str, Any]] = []

    for path in files:
        # 超时保护
        if time.monotonic() - start_time > TIMEOUT_SECONDS:
            break

        ext = path.suffix.lower()
        lang = EXT_TO_LANG.get(ext, "")
        lang_key = LANG_TO_PATTERN_KEY.get(lang, "")
        if not lang_key:
            continue

        text = read_file_text(path)
        if not text:
            continue

        scan_status_patterns(path, root, text, lang_key, status_patterns)
        scan_concurrency_patterns(path, root, text, lang_key, concurrency_patterns)
        scan_event_patterns(path, root, text, lang_key, event_patterns)
        scan_framework_components(path, root, text, lang_key, framework_components)
        scan_soft_delete(path, root, text, lang_key, soft_delete_patterns)
        scan_idempotency(path, root, text, lang_key, idempotency_patterns)
        scan_entity_fields(path, root, text, lang_key, entity_fields)
        scan_json_field_patterns(path, root, text, lang_key, json_field_patterns)

    runnable_project = detect_runnable_project(root)
    hot_files = get_hot_files(root)

    return {
        "scan_timestamp": datetime.now(timezone.utc).isoformat(),
        "language_stack": language_stack or list(active_lang_keys),
        "status_patterns": status_patterns,
        "concurrency_patterns": concurrency_patterns,
        "event_patterns": event_patterns,
        "framework_components": framework_components,
        "soft_delete_patterns": soft_delete_patterns,
        "idempotency_patterns": idempotency_patterns,
        "entity_fields": entity_fields,
        "json_field_patterns": json_field_patterns,
        "runnable_project": runnable_project,
        "hot_files": hot_files,
    }


def main() -> int:
    parser = argparse.ArgumentParser(description="doc-init 深度知识提取（语言模式扫描）")
    parser.add_argument("--root", default=".", help="项目根目录")
    parser.add_argument("--inventory", help="project_inventory.py 输出的 JSON 文件路径；缺省仅按文件扩展名推断")
    parser.add_argument("--output", help="输出 JSON 文件；缺省打印到 stdout")
    args = parser.parse_args()

    root = Path(args.root).expanduser().resolve()
    if not root.exists() or not root.is_dir():
        print(f"错误：项目根目录不存在或不是目录：{root}")
        return 2

    inventory: dict[str, Any] = {}
    if args.inventory:
        inv_path = Path(args.inventory).expanduser()
        if inv_path.exists():
            try:
                inventory = json.loads(inv_path.read_text(encoding="utf-8"))
            except (json.JSONDecodeError, OSError) as e:
                print(f"警告：无法读取 inventory 文件 {inv_path}: {e}，将按文件扩展名推断")

    data = run_scan(root, inventory)
    text = json.dumps(data, ensure_ascii=False, indent=2)
    if args.output:
        Path(args.output).expanduser().write_text(text + "\n", encoding="utf-8")
    else:
        print(text)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
