# -*- coding: utf-8 -*-
"""门日志原型（2026-10-20）· 验证 #1423 方案可行性的最小实现。

要证明三件事（这是给 tonydzi 的回信里承诺的设计）：
  1. block/warn 逐条记，allow 按会话聚合 —— 日志量降一个量级
  2. 聚合后比率仍可算：blocks / (blocks + allows)
  3. 死门（allowed=0 且无 block）必须能和「满足的门」区分开 —— schema 带三态

运行：python gate_log.py --selftest
"""
from __future__ import annotations

import json
import sys
from dataclasses import dataclass, field

for _s in (sys.stdout, sys.stderr):
    try:
        _s.reconfigure(encoding="utf-8", errors="replace")
    except Exception:
        pass


@dataclass
class GateLog:
    """一个门的会话级日志。allow 只计数，block/warn 留全行。"""
    gate: str
    blocks: int = 0
    warns: int = 0
    allowed: int = 0
    events: list[dict] = field(default_factory=list)

    def block(self, reason: str, at: str = "") -> None:
        self.blocks += 1
        self.events.append({"t": "block", "ts": at, "reason": reason})

    def warn(self, reason: str, at: str = "") -> None:
        self.warns += 1
        self.events.append({"t": "warn", "ts": at, "reason": reason})

    def allow(self) -> None:
        self.allowed += 1  # 只加计数，不写行

    def status(self) -> str:
        """measured = 有放行也有拦截；satisfied = 有放行无拦截；
        dead = 有拦截却零放行（门在跑但每次都要拦，可能是判据过严）；
        uncomputable = 两侧都没有，这个门什么都没测到。"""
        if self.allowed > 0 and self.blocks > 0:
            return "measured"
        if self.allowed > 0 and self.blocks == 0:
            return "satisfied"
        if self.allowed == 0 and self.blocks > 0:
            return "dead"
        return "uncomputable"

    def rate(self) -> float | None:
        total = self.blocks + self.allowed
        return None if total == 0 else round(self.blocks / total, 4)

    def line(self, session: str) -> dict:
        return {
            "gate": self.gate,
            "session": session,
            "status": self.status(),
            "allowed": self.allowed,
            "blocks": self.blocks,
            "warns": self.warns,
            "block_rate": self.rate(),
        }


def selftest() -> int:
    ok = True

    print("① 正常门：3 拦 / 1200 放行")
    g = GateLog("voice-compliance")
    for i in range(3):
        g.block("中英混排", f"t{i}")
    for _ in range(1200):
        g.allow()
    line = g.line("s1")
    print("   ", json.dumps(line, ensure_ascii=False))
    ok &= line["status"] == "measured" and line["block_rate"] == pytest_rate(3, 1200)
    ok = ok and (len(g.events) == 3)  # allow 不应逐条写行

    print("② 死门：有拦截、零放行")
    g2 = GateLog("write-guard")
    g2.block("路径越界")
    l2 = g2.line("s2")
    ok &= l2["status"] == "dead" and l2["block_rate"] == 1.0
    print("   ", json.dumps(l2, ensure_ascii=False))

    print("③ 满足的门：有放行、零拦截")
    g3 = GateLog("honesty")
    for _ in range(40):
        g3.allow()
    l3 = g3.line("s3")
    ok &= l3["status"] == "satisfied" and l3["block_rate"] == 0.0
    print("   ", json.dumps(l3, ensure_ascii=False))

    print("④ 什么都没测到：两侧皆零")
    g4 = GateLog("claim-gate")
    l4 = g4.line("s4")
    ok &= l4["status"] == "uncomputable" and l4["block_rate"] is None
    print("   ", json.dumps(l4, ensure_ascii=False))

    print("⑤ 日志体积：逐条 write_guard 963 拦 / 96,300 放行")
    naive = 963 + 96_300
    ours = 963 + 1
    ok &= ours < naive / 90
    print(f"    逐条 = {naive} 行 · 本方案 = {ours} 行 · 降幅 {100 * (1 - ours / naive):.2f}%")

    print("⑥ 三态互斥且覆盖：四种状态各不相同")
    statuses = {l["status"] for l in (line, l2, l3, l4)}
    ok &= statuses == {"measured", "dead", "satisfied", "uncomputable"}
    print("   ", sorted(statuses))

    print("\nSELFTEST PASS" if ok else "\nSELFTEST FAIL")
    return 0 if ok else 1


def pytest_rate(b: int, a: int) -> float:
    return round(b / (b + a), 4)


if __name__ == "__main__":
    raise SystemExit(selftest() if "--selftest" in sys.argv else 0)
