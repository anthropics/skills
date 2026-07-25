# Claude Code를 위한 Academic Research Skills

[![Version](https://img.shields.io/badge/version-v3.16.0-blue)](https://github.com/Imbad0202/academic-research-skills/releases/tag/v3.16.0)
[![DOI](https://img.shields.io/badge/DOI-10.5281%2Fzenodo.20696614-blue)](https://doi.org/10.5281/zenodo.20696614)
[![License: CC BY-NC 4.0](https://img.shields.io/badge/license-CC%20BY--NC%204.0-lightgrey)](https://creativecommons.org/licenses/by-nc/4.0/)
[![Sponsor](https://img.shields.io/badge/sponsor-Buy%20Me%20a%20Coffee-orange?logo=buy-me-a-coffee)](https://buymeacoffee.com/crucify020v)

[English](README.md) | [简体中文版](README.zh-CN.md) | [繁體中文版](README.zh-TW.md) | [日本語版](README.ja-JP.md)

학술 연구를 위한 Claude Code 통합 스킬 모음으로, 연구 설계부터 논문 작성·검토·출판 준비까지의 전체 워크플로를 지원합니다.

**30초 만에 설치**(Claude Code CLI / VS Code / JetBrains, v3.7.0+):

```text
/plugin marketplace add Imbad0202/academic-research-skills
/plugin install academic-research-skills
```

그런 다음 `/ars-plan`을 실행해 소크라테스식 대화로 논문 구조를 짜보거나, 사전 요건과 전통적인 심볼릭 링크 방식을 보려면 [빠른 설치](#빠른-설치)로 이동하세요.

> **AI는 부조종사이지 조종사가 아닙니다.** 이 도구는 논문을 대신 써 주지 않습니다. 참고문헌 탐색, 인용 형식 정리, 데이터 검증, 논리적 일관성 점검과 같은 반복적이고 소모적인 작업을 지원하여, 실제로 사람의 판단이 필요한 부분 — 질문 정의, 방법 선택, 데이터가 의미하는 바의 해석, 그리고 "나는 ~라고 주장한다" 다음에 오는 문장을 쓰는 일 — 에 집중할 수 있게 합니다.
>
> 휴머나이저(humanizer)와 달리, 이 도구는 AI를 사용했다는 사실을 숨기도록 돕지 않습니다. 더 잘 쓰도록 돕습니다. Style Calibration은 과거 작업에서 사용자의 문체를 학습합니다. Writing Quality Check는 기계가 생성한 듯한 느낌을 주는 패턴을 잡아냅니다. 목표는 품질이지 부정행위가 아닙니다.

### 왜 완전 자동화가 아니라 인간 참여형(human-in-the-loop)인가?

Lu et al. (2026, *Nature* 651:914-919)은 **The AI Scientist**를 만들었습니다 — 최상위 ML 학회의 블라인드 동료 심사를 통과해 논문을 게재한 최초의 완전 자율 AI 연구 시스템입니다(ICLR 2025 workshop, 점수 6.33/10 vs workshop 평균 4.87). 이들의 Limitations 절은 완전 자율 AI 연구 파이프라인이 물려받는 실패 양상을 열거합니다: 구현 버그, 환각된 결과, 지름길 의존, 버그를 통찰로 재포장, 방법론 날조, 프레임 고착, 인용 환각.

ARS는 **AI의 지원을 받는 인간 연구자가 인간이나 AI가 단독으로 연구할 때보다 이러한 실패 양상을 더 효과적으로 줄일 수 있다**는 전제에서 설계되었습니다. Stage 2.5와 Stage 4.5 무결성 게이트는 7개 모드의 차단형 체크리스트를 실행합니다. 자세한 내용은 [`academic-pipeline/references/ai_research_failure_modes.md`](academic-pipeline/references/ai_research_failure_modes.md)를 참조하세요. 또한 리뷰어는 사용자가 제공한 골드셋에 대해 자신의 FNR/FPR을 측정하는 옵트인 calibration 모드를 제공합니다.

[**Zhao et al.**](https://arxiv.org/abs/2605.07723) (2026-05)은 arXiv, bioRxiv, SSRN, PMC의 250만 편 논문에 걸친 1억 1,100만 건의 참고문헌을 대규모로 점검했습니다. 이들의 보수적 추정치는 2025년 한 해에만 146,932건의 환각된 인용이며, 2024년 중반에 변곡점이 관찰되었습니다. bioRxiv-to-PMC 쌍에 대해서는 85.3%의 preprint-to-published 지속성을 보고합니다. 이 논문은 "인용된 참고문헌이 실제로는 뒷받침하지 않는 주장을 지지하기 위해 배치된 진짜 인용"을 미해결 과제로 기술합니다. ARS v3.7.1은 출처 provenance를 위한 trust-chain frontmatter를 추가했고, v3.7.3은 향후 주장 수준 감사를 위한 locator 인프라(3계층 인용 앵커)를 추가하고 인용 시점에 참고용 위험 신호를 표시합니다(ARS는 이 주장-충실성 격차를 내부적으로 "L3"로 라벨링합니다. 이는 ARS 용어이며 논문의 용어가 아닙니다). v3.7.x는 Zhao et al.의 코퍼스 규모 발견에 동기를 두며, ARS 자체에 대한 코퍼스 규모 평가는 향후 과제로 남아 있습니다.

v3.8은 L3 격차의 나머지 절반을 메웁니다. v3.7.3은 모든 인용이 locator 앵커를 갖도록 했고, v3.8은 각 앵커에 대해 인용된 출처를 가져와 주장이 실제로 뒷받침되는지 판단하는 옵트인 감사 패스(`ARS_CLAIM_AUDIT=1`)를 추가합니다. 다섯 개의 새로운 HIGH-WARN 클래스(claim-not-supported, negative-constraint-violation, fabricated-reference, anchorless, constraint-violation-uncited)의 출력을 formatter terminal hard gate가 거부합니다. 캘리브레이션은 FNR<0.15 + FPR<0.10 합격 임계값을 갖는 20개 항목으로 구성된 골드셋으로 제공됩니다. 단계적 활성화 계획은 v3.8 명세 §5에 따라 캘리브레이션 후 증거가 나올 때까지 보류됩니다.

v3.3은 [**PaperOrchestra**](https://arxiv.org/abs/2604.05018) (Song, Song, Pfister & Yoon, 2026, Google)에서 영감을 받았습니다: Semantic Scholar API 검증, anti-leakage 프로토콜, VLM 그림 검증, 점수 궤적 추적.

---

## 아키텍처 & 파이프라인

**👉 [docs/ARCHITECTURE.md](docs/ARCHITECTURE.md)** — 전체 파이프라인 개요: 흐름도, 단계별 매트릭스, 데이터 접근 흐름, 스킬 의존성 그래프, 품질 게이트, 모드 목록.

아키텍처 문서는 기존의 상세한 파이프라인 설명을 대체합니다. *어떤 단계에서 무엇이 실행되는지*에 관한 모든 내용이 이제 한 곳에 있습니다.

## 빠른 설치

**사전 요건**

- [Claude Code](https://docs.claude.com/en/docs/claude-code/setup) (최신 버전. 플러그인 패키징은 최근 버전을 요구합니다)
- `ANTHROPIC_API_KEY`를 export하거나, 첫 `claude` 실행 시 설정
- *선택:* DOCX용 Pandoc, APA 7.0 PDF용 tectonic + Source Han Serif TC (Markdown 출력은 둘 다 없어도 동작)
- *선택(실제 Python):* 핵심 스킬(research / write / review)은 Python이 필요 없습니다 — 프롬프트 기반입니다. **실제 Python 인터프리터**는 다음에만 필요합니다: `PreToolUse` write-scope guard(선택적 서브에이전트 하드닝 — 실제 Python을 찾지 못하면 오류 없이 no-op으로 처리되고 guard는 비활성화됩니다. 핵심 스킬은 영향받지 않습니다), 그리고 Python 프로세스를 호출하는 몇 가지 옵트인 기능(revision-patch 모드, submission-package verifier, `/ars-cache-invalidate` / `/ars-mark-read` / `/ars-unmark-read` 명령). Windows에서는 `python3`가 실제 Python이 아니라 동작하지 않는 Microsoft Store placeholder인 경우가 많으니, 런처가 실제 인터프리터를 찾을 수 있도록 python.org에서(또는 `winget`으로) Python을 설치하세요. guard 런처는 POSIX 셸 스크립트이고 `hooks.json`이 이를 `bash`로 호출하므로, Windows에서는 **Git Bash**(Git for Windows에 번들됨)가 필요합니다. Git Bash가 있으면 실제 Python이 없어도 오류 없이 기능이 비활성화됩니다(guard는 조용히 no-op으로 처리됩니다). Git Bash가 없으면 Claude Code는 PowerShell로 폴백하는데, PowerShell은 `.sh` 런처를 전혀 실행할 수 없습니다: guard는 비활성화되고 `PreToolUse` 훅은 호출마다 조용히 no-op하는 대신 오류를 로깅합니다(허용된 기능 저하 — guard는 선택적이며 절대 쓰기를 막지 않지만, Git Bash 설치 전까지는 훅 오류 로그가 발생할 수 있습니다).

**플러그인 설치(v3.7.0+, 권장):**

```text
/plugin marketplace add Imbad0202/academic-research-skills
/plugin install academic-research-skills
```

**동작 확인:** `/ars-plan`을 실행하고 작업 중인 논문을 설명하세요 — ARS가 소크라테스식 대화를 시작해 논문의 장 구조를 함께 그려 줍니다. 단발성 테스트를 원하면 `/ars-lit-review "your topic"`을 시도하세요.

**👉 [docs/SETUP.md](docs/SETUP.md)** — 전체 가이드: Claude Code 설치, API 키 설정, DOCX/PDF용 선택적 Pandoc/tectonic, 교차 모델 검증(`ARS_CROSS_MODEL`), 여섯 가지 설치 방법(Plugin, project skills, global skills, claude.ai Project, repo-cloned, Claude Science 가져오기).

**Claude Science를 사용하시나요?** 네 개의 스킬을 바로 가져올 수 있습니다: **Skills → Import from GitHub**에서 `https://github.com/Imbad0202/academic-research-skills`를 붙여넣고 **Preview** → **Import 4 skills**(이 저장소 v3.14.0+ 필요 — 가져오기 도구는 marketplace manifest에 명시된 스킬 경로를 읽습니다). 가져오기는 특정 시점의 스냅샷입니다: ARS 업데이트 후에는 다시 가져오세요. 가져온 스킬은 ARS 방법론(연구/작성/리뷰 프로토콜)을 담습니다. Claude Code 전용 메커니즘 — slash commands, hooks, 서브에이전트 오케스트레이션 — 은 이전되지 않습니다. 자세한 내용은 [docs/SETUP.md](docs/SETUP.md) Method 5를 참조하세요.

**Codex CLI를 사용하시나요?** 대신 자매 배포판을 설치하세요: [`Imbad0202/academic-research-skills-codex`](https://github.com/Imbad0202/academic-research-skills-codex) — 동일한 워크플로 콘텐츠를, `ars-*` 별칭을 갖는 단일 `$academic-research-suite` 스킬로 Codex 네이티브 패키징한 것입니다.

## 성능 & 비용

**👉 [docs/PERFORMANCE.md](docs/PERFORMANCE.md)** — 모드별 토큰 예산, 전체 파이프라인 추정치(15,000 단어 논문 기준 약 $4–6), 권장 Claude Code 설정(Auto 모드. Agent Team 선택).

## 가이드 & 글

- [Academic Writing Shouldn't Be a Solo Act](https://open.substack.com/pub/edwardwu223235/p/academic-writing-shouldnt-be-a-solo?r=4dczl&utm_medium=ios) — 전체 파이프라인 워크스루(영어)
- [學術寫作不該是一個人的事：一套開源 AI 協作工具如何改變研究者的工作流](https://open.substack.com/pub/edwardwu223235/p/ai?r=4dczl&utm_medium=ios) — 完整使用指南（繁體中文）

---

## 한눈에 보는 기능

- **Deep Research** — 소크라테스식 가이드 모드, PRISMA 체계적 문헌고찰, 의도 감지, 대화 건강도 모니터링, 선택적 교차 모델 DA, Semantic Scholar API 검증을 갖춘 13개 에이전트 연구팀.
- **Academic Paper** — Style Calibration, Writing Quality Check, LaTeX 하드닝, 시각화, 수정 코칭, 인용 변환, anti-leakage 프로토콜, VLM 그림 검증을 갖춘 12개 에이전트 논문 작성.
- **Academic Paper Reviewer** — 0–100 품질 루브릭(EIC + 동적 리뷰어 3명 + Devil's Advocate), 양보 임계값 프로토콜, 공격 강도 보존, 선택적 교차 모델 DA 비평 / 캘리브레이션, R&R 추적 매트릭스, 읽기 전용 제약을 갖춘 7개 에이전트 다관점 동료 심사.
- **Academic Pipeline** — 적응형 체크포인트, 주장 검증, Material Passport, 선택적 `repro_lock`, 선택적 교차 모델 무결성 검증, 대화 중 강화, 점수 궤적 추적을 갖춘 10단계 파이프라인 오케스트레이터.
- **Data Access Level Metadata** (v3.3.2+) — 모든 스킬이 `data_access_level`(`raw` / `redacted` / `verified_only`)을 선언하며, `scripts/check_data_access_level.py`로 강제됩니다. Anthropic의 automated-w2s-researcher (2026)에서 패턴을 차용했습니다. 자세한 내용은 [`shared/ground_truth_isolation_pattern.md`](shared/ground_truth_isolation_pattern.md)를 참조하세요.
- **Task Type Annotation** (v3.3.2+) — 모든 스킬이 `task_type`(`open-ended` 또는 `outcome-gradable`)을 선언합니다. 현재 모든 ARS 스킬은 `open-ended`입니다.
- **Benchmark Report Schema** (v3.3.5+) — 정직한 벤치마크 비교를 위한 JSON Schema와 린트입니다. 자세한 내용은 [`shared/benchmark_report_pattern.md`](shared/benchmark_report_pattern.md)를 참조하세요.
- **Artifact Reproducibility Lockfile** (v3.3.5+) — Material Passport의 선택적 `repro_lock` 하위 블록. **재현 보장이 아니라 구성 문서화입니다** — LLM 출력은 바이트 단위로 재현 가능하지 않습니다. 자세한 내용은 [`shared/artifact_reproducibility_pattern.md`](shared/artifact_reproducibility_pattern.md)를 참조하세요.
- **Experiment Provenance Intake** (#260) — Material Passport의 선택적 `experiment_provenance[]`는 연구자가 **외부에서** 실행한 실험을 기록하며(ARS는 절대 실험을 실행하지 않습니다), 원고의 주장은 `claim_intent_manifest.planned_experiment_ids[]`를 통해 이에 연결됩니다. 무결성 게이트(Stage 2.5/4.5)는 실험 기반 각 주장을 선언된 provenance와 대조해 검증합니다 — `ALIGNED` / `OVERSTATED` / `NOT_SUPPORTED_BY_PROVENANCE` / `PROVENANCE_INSUFFICIENT` — **실험 자체가 옳았는지는 판단하지 않습니다**. fail-closed `experiment_intake_declaration`은 "실험을 실행했는가?"를 명시적인 Stage 1 결정으로 만듭니다(문헌 전용 실행조차 `no_experiments_declared`를 선언). 자세한 내용은 [`shared/handoff_schemas.md`](shared/handoff_schemas.md)의 §"Experiment Provenance Intake (#260)"를 참조하세요.

---

## 쇼케이스: 실제 파이프라인 출력

실제 10단계 파이프라인 실행에서 나온 완전한 산출물 — 동료 심사 보고서, 무결성 검증 보고서, 최종 논문 — 을 확인하세요:

**[모든 파이프라인 산출물 둘러보기 →](examples/showcase/)**

| 산출물 | 설명 |
|---|---|
| [Final Paper (EN)](examples/showcase/full_paper_apa7.pdf) | APA 7.0 형식, LaTeX 컴파일 |
| [Final Paper (ZH)](examples/showcase/full_paper_zh_apa7.pdf) | 중국어 버전, APA 7.0 |
| [Integrity Report — Pre-Review](examples/showcase/integrity_report_stage2.5.pdf) | Stage 2.5: 날조된 참고문헌 15건 + 통계 오류 3건 적발 |
| [Integrity Report — Final](examples/showcase/integrity_report_stage4.5.pdf) | Stage 4.5: 회귀 없음 확인 |
| [Peer Review Round 1](examples/showcase/stage3_review_report.pdf) | EIC + 리뷰어 3명 + Devil's Advocate |
| [Re-Review](examples/showcase/stage3prime_rereview_report.pdf) | 수정 후 검증 |
| [Peer Review Round 2](examples/showcase/stage3_review_report_r2.pdf) | 후속 심사 |
| [Response to Reviewers](examples/showcase/response_to_reviewers_r2.pdf) | 항목별 저자 응답 |
| [Post-Publication Audit Report](examples/showcase/post_publication_audit_2026-03-09.pdf) | 독립적 전체 참고문헌 감사: 3회의 무결성 점검이 놓친 21/68 문제 발견 |

---

## 동반 도구: Experiment Agent

연구가 글쓰기 전에 실험(코드 또는 인간 대상 연구)을 수행해야 한다면, [Experiment Agent](https://github.com/Imbad0202/experiment-agent) 스킬이 ARS Stage 1(RESEARCH)과 Stage 2(WRITE) 사이의 공백을 메웁니다.

```
ARS Stage 1 RESEARCH  →  RQ Brief + Methodology Blueprint
        ↓
  experiment-agent     →  run/manage experiments → validate results
        ↓
ARS Stage 2 WRITE     →  write paper with verified experiment results
```

**무엇을 하는가**: 실시간 모니터링과 함께 코드 실험(Python, R 등)을 실행하고, IRB 윤리 체크리스트로 인간 대상 연구 프로토콜을 관리하며, 11종 오류(fallacy) 감지로 통계를 해석하고, 재현성을 검증합니다.

**함께 사용하는 방법**: Stage 1 이후 ARS 파이프라인을 일시 중지하고, 별도의 experiment-agent 세션에서 실험을 실행한 다음, 결과를(Material Passport와 함께) ARS Stage 2로 다시 가져옵니다. ARS는 어떤 수정도 필요하지 않습니다. 설정 방법은 [experiment-agent README](https://github.com/Imbad0202/experiment-agent)를 참고하세요.

**Stage 1 intake 선언 (#260)**: Stage 1에서 ARS는 해당 실행이 실험 기반 주장을 포함할지 감지하고 Material Passport에 fail-closed `experiment_intake_declaration`을 설정합니다. 외부에서 실험을 실행했다면 연구자는 실험당 하나의 `experiment_provenance[]` 항목(`experiment_id`, 중첩된 `repro_lock`, `planned_vs_executed[]`, `negative_results[]`, `known_limitations[]`)을 입력하고 선언은 `experiments_declared`로 설정됩니다. 그렇지 않으면 `no_experiments_declared`로 설정됩니다. 이 선언은 **#260 이후 모든 passport에서 필수**입니다 — 실험을 전혀 다루지 않는 실행도 `no_experiments_declared`를 선언하므로, 잊힌 provenance 블록 때문에 무결성 게이트가 조용히 우회될 수 없습니다. `experiment_id`는 이 intake 시점에 고정되며, 작성자는 이후 `planned_experiment_ids[]`를 통해 이를 참조합니다.

**교육 측 동반 도구**: [Teaching Skills](https://github.com/YujxZJCN/teaching-skills)는 ARS 아키텍처(스킬 앙상블, 공유 계약, 단계별 게이트, Course Passport)를 학술 생활의 교육 측면에 적용합니다 — 강좌 설계 → 수업 → 평가 → 전달 → 성찰. 이것의 `sotl` 모드는 수업 탐구 프로젝트를 출판 단계를 위해 ARS deep-research / academic-paper로 넘깁니다.

---

## 사용법

### 빠른 시작

```
# 전체 연구 파이프라인 시작
You: "I want to write a research paper on AI's impact on higher education QA"

# 소크라테스식 가이던스로 시작
You: "Guide my research on AI in educational evaluation"

# 가이드된 플래닝으로 논문 작성
You: "Guide me through writing a paper on demographic decline"

# 기존 논문 검토
You: "Review this paper" (그런 다음 논문을 제공)

# 파이프라인 상태 확인
You: "status"
```

### 개별 스킬

#### Deep Research (8개 모드)

```
"Research the impact of AI on higher education"       → full 모드
"Give me a quick brief on X"                          → quick 모드
"Do a systematic review on X with PRISMA"             → systematic-review 모드
"Guide my research on X"                              → socratic 모드 (guided)
"Fact-check these claims"                             → fact-check 모드
"Do a literature review on X"                         → lit-review 모드
"Compare these papers in WHY/HOW/WHAT format"         → three-way-scan 모드
"Review this paper's research quality"                → review 모드
```

#### Academic Paper (11개 모드)

```
"Write a paper on X"                                  → full 모드
"Guide me through writing a paper"                    → plan 모드 (guided)
"Build a paper outline"                               → outline-only 모드
"I have a draft, here are reviewer comments"          → revision 모드
"Parse these reviewer comments into a roadmap"        → revision-coach 모드
"Write an abstract for this paper"                    → abstract-only 모드
"Turn this into a literature review paper"            → lit-review 모드
"Convert to LaTeX" / "Convert citations to IEEE"      → format-convert 모드
"Check citations"                                     → citation-check 모드
"Generate an AI disclosure statement for NeurIPS"     → disclosure 모드
"Audit my rebuttal draft against the reviews"         → rebuttal-audit 모드
```

#### Academic Paper Reviewer (6개 모드)

```
"Review this paper"                                   → full 모드 (EIC + R1/R2/R3 + Devil's Advocate)
"Quick assessment of this paper"                      → quick 모드
"Guide me to improve this paper"                      → guided 모드
"Check the methodology"                               → methodology-focus 모드
"Verify the revisions"                                → re-review 모드
"Calibrate this reviewer against my gold set"         → calibration 모드
```

#### Academic Pipeline (오케스트레이터)

```
"I want to write a complete research paper"           → Stage 1부터 full 파이프라인
"I already have a paper, review it"                   → Stage 2.5 중간 진입 (무결성 먼저)
"I received reviewer comments"                        → Stage 4 중간 진입
```

> 파이프라인은 **Stage 6: Process Summary**로 끝납니다 — 6차원 협업 품질 평가(1–100 점수)와 함께 논문 작성 과정 기록을 자동 생성합니다.

### 지원 언어

- **번체중국어**(繁體中文) — 사용자가 중국어로 작성할 때 기본값
- **영어** — 사용자가 영어로 작성할 때 기본값
- 학술 논문용 이중언어 초록(중국어 + 영어)

> **다른 언어를 사용하시나요?** Socratic 모드(deep-research)와 Plan 모드(academic-paper)는 **의도 기반 활성화**를 사용합니다 — 특정 키워드가 아니라 요청의 의미를 감지합니다. 즉, 수정 없이 **어떤 언어에서도** 동작합니다.
>
> 다만, 일반적인 `Trigger Keywords` 섹션(스킬이 애초에 활성화되는지를 결정함)은 여전히 영어와 번체중국어 키워드를 나열합니다. 사용하는 언어에서 스킬이 안정적으로 활성화되지 않는다면, 각 `SKILL.md` 파일의 `### Trigger Keywords` 섹션에 해당 언어의 키워드를 추가해 매칭 신뢰도를 높일 수 있습니다.

### 지원 인용 형식

- APA 7.0 (기본값, 중국어 인용 규칙 포함)
- Chicago (Notes & Author-Date)
- MLA
- IEEE
- Vancouver

### 지원 논문 구조

- IMRaD (실증 연구)
- 주제별 문헌고찰(Thematic Literature Review)
- 이론 분석(Theoretical Analysis)
- 사례 연구(Case Study)
- 정책 브리프(Policy Brief)
- 학회 논문(Conference Paper)

---

## 스킬 상세

에이전트별 책임과 단계별 산출물은 이제 [`docs/ARCHITECTURE.md`](docs/ARCHITECTURE.md)에 있습니다. 릴리스 메타데이터를 한 곳에 유지하기 위해 버전 번호는 여기에 고정합니다.

### Deep Research (v2.11.0)

13개 에이전트 연구팀. 모드: full, quick, review, lit-review, three-way-scan, fact-check, socratic, systematic-review. 전체 에이전트 명단과 산출물: ARCHITECTURE.md §3 참조.

### Academic Paper (v3.2.0)

12개 에이전트 논문 작성 파이프라인. 모드: full, plan, outline-only, revision, revision-coach, abstract-only, lit-review, format-convert, citation-check, disclosure, rebuttal-audit. 출력: MD + DOCX (가능한 경우 Pandoc 경유) + LaTeX (APA 7.0 `apa7` class / IEEE / Chicago) → tectonic 경유 PDF. 전체 에이전트 명단과 단계별 책임: ARCHITECTURE.md §3 참조.

### Academic Paper Reviewer (v1.10.0)

**0-100 품질 루브릭**을 갖춘 7개 에이전트 다관점 심사. 모드: full, re-review, quick, methodology-focus, guided, calibration. **결정 매핑:** ≥80 Accept, 65-79 Minor Revision, 50-64 Major Revision, <50 Reject. 1차 심사팀 대 좁은 re-review 팀 경계: ARCHITECTURE.md §3 Stage 3 / Stage 3' 참조.

### Academic Pipeline (v3.16.0)

무결성 검증, 2단계 심사, 소크라테스식 코칭, 협업 평가를 갖춘 10단계 오케스트레이터. 파이프라인 보장: 모든 단계는 사용자 확인 체크포인트를 요구하며, 무결성 검증(Stage 2.5 + 4.5)은 건너뛸 수 없고, R&R Traceability Matrix(Schema 11)는 저자의 수정 주장을 독립적으로 검증합니다. v3.4는 Stage 2.5 / 4.5에 Compliance Agent(PRISMA-trAIce + RAISE)를 추가했습니다. v3.5는 모든 FULL/SLIM 체크포인트와 파이프라인 완료 시점에 **Collaboration Depth Observer**(`collaboration_depth_agent`, 자문 전용 — 절대 차단하지 않음)를 추가합니다. 필수(MANDATORY) 무결성 게이트(2.5 / 4.5)는 컴플라이언스 점검이 희석되지 않도록 observer를 명시적으로 건너뜁니다. Wang & Zhang (2026), IJETHE 23:11에 기반합니다. 에이전트·산출물·게이트를 포함한 단계별 매트릭스: ARCHITECTURE.md §3 참조.

---

## v3.0 최적화: AI의 구조적 한계에 대해 우리가 발견한 것

### 무슨 일이 있었나

고등교육의 AI에 대한 성찰 글을 쓰기 위해 ARS를 사용하던 중, 어떤 프롬프트 엔지니어링으로도 고칠 수 없는 세 가지 구조적 문제에 부딪혔습니다:

1. **프레임 고착(Frame-lock)**: AI에게 자기 논제에 대한 devil's advocate 토론을 시켰습니다. 실제로 그렇게 했습니다 — 네 라운드, 매번 더 정교해졌습니다. 하지만 모든 라운드는 내가 설정한 프레임 안에 머물렀습니다. DA는 논증을 공격했을 뿐 전제를 공격한 적이 없습니다. "우리가 애초에 올바른 질문을 논의하고 있는가?"를 묻지 않았습니다. 이는 v2.7 스트레스 테스트에서 31% 인용 오류율을 일으킨 것과 같은 패턴입니다: 검증하는 AI와 생성하는 AI가 동일한 인지 프레임을 공유합니다.

2. **반박에 대한 아첨(Sycophancy under pushback)**: DA의 공격에 이의를 제기할 때마다 너무 빨리 양보했습니다. 자신이 제기한 지적을 충분한 근거 없이 지나치게 쉽게 철회했습니다. 모델의 학습은 대화의 화합을 보상하므로 — "사용자가 반박했다"가 공격이 틀렸다는 증거로 취급되었지만, 사실은 사용자가 끈질겼다는 의미일 뿐인 경우가 많았습니다.

3. **의도 오인식(Intent misdetection)**: Socratic Mentor는 내가 아직 탐색 중인데도 계속 수렴해 산출물을 만들려 했습니다("정리해 드릴까요?"). "사용자가 깊은 철학적 논의를 원한다"와 "사용자가 RQ 브리프를 원한다"를 구분하지 못했습니다. 둘 다 참여처럼 보이지만 정반대의 AI 행동이 필요합니다.

### 우리가 바꾼 것 (v3.0)

**Devil's Advocate — 양보 임계값 프로토콜**(`deep-research` + `academic-paper-reviewer`)
- DA는 이제 응답 전에 모든 반박을 1-5 척도로 채점해야 합니다
- 양보는 점수 ≥4(반박이 증거와 함께 핵심 공격을 직접 다룸)에서만 허용됩니다
- 점수 ≤3: 입장을 유지하고 원래 공격을 다시 진술합니다
- 안티-아첨 규칙: 연속 양보 금지, 양보율 추적, 각 체크포인트 후 프레임 고착 감지

**Socratic Mentor — 의도 감지 계층**(`deep-research`)
- 대화 시작과 매 3턴마다 사용자 의도를 탐색형 대 목표지향형으로 분류합니다
- 탐색형 모드: 자동 수렴 비활성화, 최대 라운드를 60으로 상향, "요약해 드릴까요?" 프롬프트 금지
- 목표지향형 모드: 표준 수렴 동작
- 조기 종료 방지 규칙: 탐색형 모드에서는 사용자가 중단 시점을 결정합니다

**Socratic Mentor — 대화 건강도 지표**(`deep-research`)
- 매 5턴마다 세 차원(지속적 동의, 갈등 회피, 조기 수렴)에 대해 조용히 자기 평가합니다
- 동의 패턴이 감지되면 도전적 질문을 자동 주입합니다
- 사용자에게 보이지 않음(게이밍 방지). 단, 사후 세션 검토용 로그는 제공됩니다

### 왜 중요한가

이 최적화들은 AI의 구조적 한계를 해결하지 못합니다 — 한계를 가시화하고 관리 가능하게 만들 뿐입니다. DA는 충분히 강하게 밀어붙이면 결국 양보합니다. Socratic Mentor는 여전히 약간의 수렴 편향을 가집니다. 하지만 이제 아첨을 늦추고, DA가 양보를 정당화하도록 강제하며, Mentor가 사용자가 준비되기 전에 마무리하지 못하게 하는 명시적 체크포인트가 있습니다.

더 깊은 교훈: AI 리터러시는 AI를 도구로 사용하는 법을 배우거나, 윤리 규칙을 따르거나, AI 위험을 두려워하는 것이 아닙니다. AI와 충분히 깊이 관여해 그 구조적 한계를 — 그리고 그 과정에서 자신의 사고 한계를 — 스스로 발견하는 것입니다.

---

## 라이선스

이 저작물은 [CC-BY-NC 4.0](https://creativecommons.org/licenses/by-nc/4.0/) 하에 라이선스됩니다.

**다음을 자유롭게 할 수 있습니다:**
- 공유 — 자료를 복사하고 재배포
- 각색 — 자료를 리믹스, 변형, 기반으로 제작

**다음 조건 하에서:**
- **저작자 표시(Attribution)** — 적절한 출처를 표기해야 합니다
- **비영리(NonCommercial)** — 자료를 상업적 목적으로 사용할 수 없습니다

**저작자 표시 형식:**
```
Based on Academic Research Skills by Cheng-I Wu
https://github.com/Imbad0202/academic-research-skills
```

---

## 기여자

**Cheng-I Wu** (吳政宜) — 저자 및 메인테이너

**[aspi6246](https://github.com/aspi6246)** — 기여자. v3.1 최적화는 [Claude-Code-Skills-for-Academics](https://github.com/aspi6246/Claude-Code-Skills-for-Academics)의 패턴에서 영감을 받았습니다: 읽기 전용 제약 패턴, 일급(first-class) 설계로서의 안티패턴 성문화, 인지 프레임워크 접근(절차가 아니라 "어떻게 생각할지" 교육), 그리고 lean 스킬 크기 철학.

**[mchesbro1](https://github.com/mchesbro1)** — 기여자. `academic-paper-reviewer/references/top_journals_by_field.md`를 위한 IS Basket of 8 저널을 최초로 제안하고 초안을 작성했습니다([Issue #5](https://github.com/Imbad0202/academic-research-skills/issues/5)).

**[cloudenochcsis](https://github.com/cloudenochcsis)** — 기여자. IS 절을 *Basket of 8*에서 전체 *Senior Scholars' Basket of 11*로 확장 — *Decision Support Systems*, *Information & Management*, *Information and Organization*을 추가했습니다([Issue #7](https://github.com/Imbad0202/academic-research-skills/issues/7), [PR #8](https://github.com/Imbad0202/academic-research-skills/pull/8)). 출처: [AIS Senior Scholars' List of Premier Journals](https://aisnet.org/research/seniorscholarsbasket/).

**[eltociear](https://github.com/eltociear)** (Ikko Eltociear Ashimine) — 기여자. 일본어 README([`README.ja-JP.md`](README.ja-JP.md))를 번역했습니다([PR #161](https://github.com/Imbad0202/academic-research-skills/pull/161)).

**[xpfo-go](https://github.com/xpfo-go)** (xpfo) — 기여자. 간체중국어 README([`README.zh-CN.md`](README.zh-CN.md))를 번역했습니다([PR #181](https://github.com/Imbad0202/academic-research-skills/pull/181)).

**[devCharlotte](https://github.com/devCharlotte)** — 기여자. 한국어 README([`README.ko-KR.md`](README.ko-KR.md))를 번역했습니다([PR #469](https://github.com/Imbad0202/academic-research-skills/pull/469)).

**[Yaobin29](https://github.com/Yaobin29)** — 기여자. [PR #433](https://github.com/Imbad0202/academic-research-skills/pull/433)에서 리뷰어 응답 도구를 제안했습니다. `deep-research three-way-scan` 모드와 `academic-paper rebuttal-audit` 모드(해당 PR의 `audit` 개념을 발전시킨 기능)가 v3.12.1에서 정식으로 통합되었습니다.

---

## 변경 이력

### v3.16.0 (2026-07-12) — 모델 계층화, 크로스모델 게이트 강화, WP 어드바이저리 정밀화

> **추가:** 옵트인 모델 계층화(#517) — 새 `ARS_MODEL_TIERING` 스위치에 두 방향(`economy`: 13개 실행형 에이전트를 세션 모델보다 한 단계 아래로 파견, 하한은 Opus급; `quality-boost`: 무결성 게이트와 최종 리뷰 표면의 판단형 에이전트를 프런티어 단계로 상향); 미설정 시 기존 동작과 바이트 동일하며, 동결된 39개 에이전트 분류는 새 매니페스트 + lint로 고정. 크로스모델 게이트 강화(#518) — 위험 계층화 샘플링(HIGH-IMPACT 참고문헌은 두 게이트에서 100% 검증), 두 비가역 결정 지점(설계 동결 + 최종 편집 결정)의 블라인드 불일치 점검, 검증 모델 id 상태 허용 목록, 승격 베이크오프 프로토콜; 한때 계획됐던 범용 6번째 리뷰어는 연기가 아니라 폐기. GPT-5.6 Sol을 잠정 크로스모델 검증자로 등재하고 명시적 reasoning-effort 제어 추가(#515). devCharlotte 님이 제안한 한국어 트리거 키워드 + 라우팅 경계 픽스처(#452/#509). 논문 작성 측에 CARS 서론 수사 + 제목 설계 레퍼런스(#500). **변경:** WP 연구질문 어드바이저리를 명사 치환 테스트로 20개 셸 표 밖까지 일반화(#501)하고 장식형 제목 셸을 잡도록 면제 조항을 정밀화(#505) — held-out 누락률 0.34–0.38 → 0.094, 오발화 0/16 유지; 리뷰어 캘리브레이션 프로토콜에 LLM 심사의 관대화 방향 기재(FARS 앵커, #484); OpenAlex API 키 인증 + 예산 인지 429 처리 + arXiv ToU 정렬 백오프(#495/#496). **문서:** THIRD_PARTY.md 커뮤니티 디렉터리(#497/#498). `academic-pipeline`은 스위트를 따라 v3.16.0으로, 나머지 세 스킬 버전은 변경 없습니다.

### v3.15.0 (2026-07-04) — 릴리스 게이트 강화, 프롬프트 부채 정리 2차, 드리프트 방지 잠금

> 릴리스 규율과 품질 위생 중심의 릴리스로, 스킬 동작 변경은 없습니다. **추가:** 세 가지 CI 게이트 — CHANGELOG-covers-merges 태그 전 게이트(#483), version-consistency invariant 9-11 및 태그 시점 재실행 게이트(#487), SessionStart 안내 목록을 실제 16개 명령 목록에 고정하는 command-invariants 게이트(#486) — 그리고 두 가지 드리프트 방지 잠금: Phase Boundary enforcement 문장을 23개 Bucket A 에이전트 블록 전체에 축자 고정하고, SETUP 크로스모델 예시를 상호 및 정준 모델 표에 고정(#491 → #492). **변경:** 프롬프트 부채 정리 2차는 1차에서 미뤄진 17개 에이전트를 정밀 감사(#489 → #490): 두 socratic_mentor의 실제 동작하는 자기모순(만료된 "15라운드 중단 권고" 규칙 vs 문서화된 일반적 20-30라운드) 수정, 저장소 전체 29곳의 만료된 enforcement 상태 문장 수정, 7개 에이전트의 few-shot 및 중복 프로세스 스캐폴드 정리 — 4개 배치 병렬 감사 + 독립 codex 크로스모델 챌린지로 검증. 감사 보고서는 `audits/` 아래. **수정:** DOI 배지를 shields.io에서 제공(#482). `academic-pipeline`은 스위트를 따라 v3.15.0으로, 나머지 세 스킬 버전은 변경 없습니다.

### v3.14.0 (2026-07-02) — Claude Science importability, eval-comment rendering, prompt-debt retirement

> 이식성과 다듬기에 초점을 둔 릴리스로, 스킬 동작 변경은 없습니다. **추가:** Claude Science 가져오기 지원 — marketplace manifest가 스킬 경로를 명시적으로 선언하여, symlink된 `skills/` 디렉터리를 탐색할 수 없는 GitHub API 기반 가져오기 도구(Claude Science "Import from GitHub", Windows 체크아웃)에서도 네 개의 스킬이 모두 인식됩니다. Claude Science에서 엔드투엔드로 검증되었으며 README + SETUP에 가져오기 가이드가 추가되었습니다(#480). eval-harness PR 코멘트는 원시 JSON 전체 붙여넣기 대신 한 줄 판정 + 태스크별 테이블 + `<details>`로 접힌 JSON으로 렌더링됩니다 — 표시 계층만의 변경으로, 게이트 로직은 바이트 단위로 동일합니다(#479). **변경:** 2026-07 harness-retirement 감사에 따라 네 개의 작성 계열 에이전트에서 만료된 writing-harness 스캐폴드를 제거(#476/#477 → #478, 프롬프트 순 −111줄); PR이 새 최상위 디렉터리를 추가할 때 platform-ports 정책을 안내하는 remind-don't-block 방식의 Platform Port Reminder 추가(#473). **문서:** devCharlotte의 네이티브 검수 한국어 README(#469/#471); GitHub Copilot repository instructions(#465); Skip Permissions 대신 auto permission mode 권장(#464). `[Unreleased]`에 누적된 16개 백로그 항목(코드는 모두 v3.13.0 태그 이전에 반영됨 — diff/patch revision mode #390, submission-package verifier #394, eval gold sets #215/#216 등)이 버전 기록으로 통합되었습니다. 자세한 내용은 `CHANGELOG.md`를 참조하세요. `academic-pipeline`은 스위트와 함께 v3.14.0으로, 나머지 세 스킬 버전은 변경 없습니다.

### v3.13.0 (2026-06-18) — Hook portability, provider-agnostic verification, guard correctness

> 설치/런타임 표면을 견고하게 만들고 교차 모델 도달 범위를 확장한 마이너 릴리스. **수정:** git-clone + symlink 설치 레이아웃에서 write-scope guard가 더 이상 사용자 본인의 `CLAUDE.md`를 잘못 차단하지 않음(#459, #448/#449의 잔여 절반을 마무리 — `CLAUDE.md`는 문서이지 load-bearing 강제 파일이 아니므로 infra-protected 목록에서 제외되며, 모든 load-bearing 파일은 보호 유지); 0-byte Microsoft Store `python3` 스텁을 거부하고 훅 로그를 스팸하지 않는 크로스플랫폼 `hooks/run_guard.sh` 런처를 통한 Windows Python 훅 이식성 + Python 부재 시 우아한 degradation(#454); `draft_writer` dual-phase static union 문서화 + POSIX-safe Windows 경로 매칭(#451). **추가:** grounded first-party OpenAI(절대 조용히 다운그레이드되지 않음)와 더불어 OpenAI 호환 엔드포인트(MiMo, DeepSeek, self-hosted)를 수용하는 provider-agnostic 교차 모델 검증(#455); 옵트인 Socratic 인접 프레이밍 프로브(STORM에서 차용한 관점 확장, `ARS_SOCRATIC_ADJACENT_PROBE=1`, 기본 OFF, 프로즈 계층 전용 — `deep-research` 2.10.0 → 2.11.0)(#461). `academic-pipeline`은 스위트를 v3.13.0으로 추적하며, `academic-paper`와 `academic-paper-reviewer`는 변경 없음. 이슈별 상세는 `CHANGELOG.md` 참조.

### v3.12.1 (2026-06-15) — Reviewer-response triage modes (PR #433 integration)

> ARS의 모드 기반 아키텍처에 따라 외부 기여 중 진정으로 새로운 부분을 기존 스킬의 모드로 접어 넣은 패치 릴리스. **새 모드:** `deep-research` `three-way-scan` — `quick`과 `lit-review` 사이의 경량 WHY/HOW/WHAT 논문 비교 분류로, 논문별 후보 목록 + 교차 논문 종합 제공(`deep-research` 2.9.4 → 2.10.0); `academic-paper` `rebuttal-audit` — 저자의 기존 반박/응답 초안을 리뷰어 의견에 대해 점검하는 독립형 자문 QA(의견별 커버리지 표 + 격차 목록 + 톤/증거/오독 위험 플래그)로, 아무것도 생성하지 않으며 독립 실행 시 Schema 11 / Material Passport 쓰기 / `ready_to_submit`을 명시적으로 억제(뮤테이션 커버리지를 갖춘 `check_rebuttal_audit_guard()` 린트로 강제); 더불어 `revision-coach`의 범위를 반박/이견 자세 및 비저널 범위로 확장, 그리고 `/ars-3w` + `/ars-rebuttal-audit` 슬래시 명령. 입력 형태로 라우팅: 리뷰어 의견 AND 초안 → `rebuttal-audit`; 의견만 → `revision-coach`. [@Yaobin29](https://github.com/Yaobin29)의 [PR #433](https://github.com/Imbad0202/academic-research-skills/pull/433)에서 통합. 스위트 모드 수 25 → 27(여전히 4개 스킬). 이슈별 상세는 `CHANGELOG.md` 참조.

### v3.12.0 (2026-06-08) — Kong auto-research feature track: experiment provenance, figure fidelity, cross-paper contradiction, partial-evidence decomposition

> Kong et al. (2026, arXiv:2605.18661) auto-research 기능 트랙과 partial-evidence-trap 분해 작업을 각각 독립적으로 검토·머지해 내놓은 마이너 릴리스. **새 기능:** Experiment Provenance Intake + claim→experiment 정렬 — 실험 기반 주장을 위한 schema-first 증거 원장 계층으로, intake와 정렬만 수행(연구자가 외부에서 실험을 실행하며 ARS는 절대 실행하지 않음)(#260); 캡션의 해석이 데이터로부터 따라 나오는지 그리고 원고가 그 산출물을 자신이 뒷받침하는 주장에 대해 인용하는지 점검하는 Figure/Table Fidelity Gate(#261); 평가된 논문 쌍을 연구자 확인을 위해 열거 가능하게 만드는 구조화된 Cross-Paper Contradiction 인벤토리(#262); 그리고 citation judge(#213)와 editorial synthesizer(#214) 양쪽에서 판단 전 하위 주장 분해로, 두 계층 모두에서 §F.3.2 partial-evidence trap을 닫음. **가이던스 + 해석 계층:** 보고서 생성 리뷰어 전반의 concise-output + pressure-stable 경계 강화(#274); same-family / rubric-aware 캘리브레이션 인식론 노트(#273); 검색된 콘텐츠 instruction/data 경계를 상시 원칙으로 명시(#367). **네거티브 범위:** Kong META(#255)는 ARS가 수행하지 않는 다섯 가지 자율 메커니즘을 열거한 "Rejected mechanisms" 절을 `POSITIONING.md`에 두고, 더불어 두 개의 Tier D 설계 교훈 문서로 마무리. **릴리스 규율 린트:** version-consistency invariants 5–7(#357)과 ARCHITECTURE 컴포넌트 버전 단속(#345). 더불어 교차 모델 grounding guards(#346 / #349 / #351), citation-gate 캐시 키 및 rationale 경계(#359 / #360 / #361), 평가 골드셋(#250), ACL/EMNLP disclosure 재근거화(#242) 전반의 정확성 수정. 새 스키마, manifest 필드, 모든 invariant는 추가적이며 하위 호환됩니다. `academic-pipeline`은 스위트를 v3.12.0으로 추적하며, 나머지 세 스킬 버전은 변경 없음. 이슈별 상세는 `CHANGELOG.md` 참조.

### v3.11.1 (2026-06-06) — Post-ship correctness, hardening & provenance rollup

> v3.11.0 이후 드러난 출시 후 수정을 각각 독립적으로 검토·머지해 모은 패치 릴리스: 무결성 검증 + collaboration-depth 경로로의 교차 모델 consent-gate 확장(#322), 항목별 OpenAlex + Crossref 백필 병렬화(#138), 그리고 citation-existence gate, v3.10 정책 계층, 평가 하니스, 도메인 증거 프로파일, #310 보안 경계 엣지 케이스 전반의 정확성/하드닝 수정 7건(#323 / #327 / #328 / #329 / #331 / #332 / #333) — P1 수정 2건 포함(#327 no-handoff 경로의 도메인 프로파일 활성화, #328 평가 하니스의 클래스별 임계값 게이트). 새 기능 없음, breaking 스키마 변경 없음. 이슈별 상세는 `CHANGELOG.md` 참조.

### v3.11.0 (2026-06-04) — Deterministic citation verification gate (#182)

> LLM 동료 심사와 독립적으로 실행되는 **결정론적 citation-existence 검증 게이트**를 추가. 인용된 모든 참고문헌이 최대 네 개의 서지 인덱스 — Semantic Scholar + OpenAlex + Crossref + 새로운 **arXiv resolver**(`scripts/arxiv_client.py`, API 키 불필요) — 에 대해 교차 점검되며, 인용별 `lookup_verified` 상태(`{true, false, unresolvable}`)가 통합 요약에 기록됩니다. 따라서 입증 가능하게 가짜인 DOI/arXiv ID를 가진 날조된 인용은 리뷰어 에이전트가 알아채길 바라는 대신 lookup으로 잡힙니다. 이 게이트는 **v3.10 `terminal_policies` 옵트인 모델을 상속**합니다: 감지는 항상 실행되지만, `lookup_verified == false` 행은 사용자가 `terminal_policies.citation_existence == strict`를 옵트인할 때**에만** terminal입니다 — 기본 동작은 참고용이며 `/ars-mark-read`로 확인 처리 가능합니다. `false`는 **ID-keyed unmatched**(정확한 DOI/arXiv lookup이 입증 가능하게 실패)로 좁혀져, 정당하게 비색인된 인문학 / 비영어 / 지역 인용은 `unresolvable`로 남아 절대 차단하지 않습니다(문서화된 precision-over-recall 트레이드오프). 영속 SQLite 검증 캐시(`~/.cache/ars/verification.db`, 90-day TTL)와 `/ars-cache-invalidate` 명령, 독립형 `verification_gate` API + `verify_passport.py` CLI, 그리고 v3.9.0 contamination triangulation 매트릭스의 4-인덱스 확장(k=0..4, 모두 참고용)을 제공합니다. `academic-pipeline`은 스위트를 v3.11.0으로 추적하며, 나머지 세 스킬 버전은 변경 없음. 명세: `docs/design/2026-05-21-v3.10-182-promote-citation-gate-spec.md` (§0 amendment + C-V6).

### v3.10.0 (2026-06-01) — Triangulation policy layer, Kong survey adoptions, eval harness, scoped-write guard

> 다음을 묶은 마이너 릴리스: 옵트인 contamination-triangulation **terminal policy layer**(#127 — 기본 인용 동작은 v3.9.0과 바이트 동등); **Kong et al. 2026 서베이 채택** — Rebuttal Commitment Ledger(#256/#266/#268/#269)와 분야 상대적 도메인 증거 프로파일(#259); **v3.10 측정 인프라** — 일반화된 평가 골드셋 + ranking-lift CI 게이트(#184); **scoped-write guard MVP**(#134) — 23개 단일 단계 에이전트를 자신의 단계 디렉터리에 가두고 Bash를 거부하는 결정론적 `PreToolUse` 훅(이들은 대신 Grep/Glob 및 구조화된 편집 도구를 사용); `/ars-mark-read` 플러그인 명령(#190)과 도착 즉시 깨진 버그 수정(#195); 간체중국어 README(#185); 그리고 CI 하드닝(#156/#155). Commitment-Ledger 및 도메인 프로파일 추가로 `academic-paper` → v3.2.0, `academic-paper-reviewer` → v1.10.0; `academic-pipeline`은 스위트를 v3.10.0으로 추적. strict 정책 모드를 옵트인하지 않는 한 기본 스킬 동작은 변경되지 않으며, 유일하게 기본 ON인 변경은 #134 guard로, 사용자 대상 출력이 아니라 가둬진 서브에이전트를 제약합니다.

### v3.9.4.2 (2026-05-19) — post-ship hotfix for PR #149 CI discipline gates (codex post-ship)

> PR #149(7개 CI discipline 게이트)의 Codex 출시 후 검토에서 4개 P2 발견이 드러났고, v3.9.4.2는 4개 중 3개를 하드닝. F1: `harness-retirement-monthly.yml`이 `GH_REPO`를 추가해 예약 실행이 `gh issue create`를 위한 repo 컨텍스트를 갖도록 함. F2: `release-cooldown.yml`이 `PREV_TAG` 조회를 `v*` 태그로 필터링해 비릴리스 태그가 cooldown을 우회할 수 없게 함. F3: `release-cooldown.yml`이 annotated tag subject도 읽고 `hot-fix` 철자를 수용(v3.9.2가 이전에 false-negative hotfix였음). PR #157 후속: `[skip-cooldown]` 오버라이드를 이제 커밋 메시지 AND annotated tag 메시지 양쪽에서 읽음(self-bootstrapping 수정 — 이 태그의 cooldown 우회가 F2+F3가 end-to-end로 동작함을 입증). F4(test-count-monotonic 하드닝)는 기존 `scripts/` 패키지 문제를 드러내 되돌려졌고, #154로 추적(PR #158로 수정 완료) + 재시도 #155. #152 종료. 후속: #155, #156.

### v3.9.4.1 (2026-05-19) — post-ship hotfix for v3.9.4 temporal verification (#135 codex post-ship)

> v3.9.4의 Codex 출시 후 검토가 태스크별 서브에이전트 리뷰어가 놓친 실제 버그 4개를 잡음. 핫픽스가 4개 모두에 패치: (1) `audit()`이 이제 `citation_provenance`를 P2와 P4로 전달 — ref slug가 `confidence: low` 또는 `conflict`일 때 검증기는 타임라인 날짜를 ground truth로 사용하는 대신 `TEMPORAL-METADATA-MISSING`을 발행(spec §3.4 first-party safety check가 깨져 있었음). (2) `_date_to_interval`이 `YYYY-MM`(Crossref 월 정밀도)과 `YYYY-MM-DD..YYYY-MM-DD`(구간)을 포함한 모든 schema-valid 날짜 형태를 파싱; v3.9.4는 이들에서 조용히 `ValueError`가 나며 점검을 건너뜀. (3) P4가 이제 ref 마커가 없을 때 직접 날짜 캡처를 바인딩 — "The 2026 policy enabled the 2020 rollout" 같은 문장이 실제로 트리거됨. (4) `citation_provenance.schema.json` `confidence:high` allOf가 이제 non-null에 더해 존재(`then.required`)를 요구해 누락 속성 우회를 닫음. 1561 passed(v3.9.4 베이스라인 대비 +12 새 테스트, 0 회귀). ARCHITECTURE.md를 현재 상태에 맞춤(v3.8.0에서 stale였음).

### v3.9.4 (2026-05-18) — #135 temporal verification layer (advisory)

> 5개 시간적 실패 양상(P1 retrospective arithmetic, P2 anachronistic citation, P3 comparator unmaterialized, P4 causal inversion, P5 deictic present)을 다루는 Phase 4 → 5 경계의 결정론적 자문 검증기. 새 Phase 2 형제 `timeline_extraction_agent`가 `phase2_investigation/timeline.yaml` + `phase2_investigation/citation_provenance.yaml`을 소유. 검증기 스크립트 `scripts/temporal_integrity_audit.py`가 5개 패스를 결정론적으로 실행. M3 Temporal Integrity Iron Rule을 `report_compiler_agent` + `draft_writer_agent`에 추가. M6-minimal: Crossref `issued` + pdftotext가 first-party 검증을 커버. M7-minimal: 날짜 provenance + comparator materialization. M5-stub: 사용자 선언 `version_family_id`만. `literature_corpus_entry`, `claim_audit_result`, `claim_intent_manifest` 변경 없음. `bibliography_agent` 미변경(F2 invariant). 새 sidecar 스키마 3개. 커버리지 추정: 베이스라인 55-70% / M7 minimal 시 65-75%. 1549 passed(+44 새 테스트, 0 회귀).

### v3.9.3 (2026-05-18) — #128 housekeeping (shared client utilities + dedup resolvers)

> v3.9.0 `/simplify` 검토 백로그에서 나온 순수 리팩터 + 잠복 버그 1건 수정. `scripts/_text_similarity.py`(3-way 클라이언트 dedup: normalize / similarity / threshold / retry 상수) + `scripts/_passport_yaml.py`(2-way 마이그레이션 도구 dedup: ruamel.yaml round-trip 구성) + private `_resolve_by_doi_then_title` 헬퍼(2-way resolver 본문 dedup, §3.4 / §3.5 API 표면 보존)를 추출. OpenAlex + Crossref 전반의 throttle 측정을 `time.monotonic`으로 표준화(이전 `time.time`, NTP-unsafe), Semantic Scholar와 정렬. 5개 모듈 수준 cross-import 전부에 dual-path import 인프라(sibling-first, namespace-package fallback)를 적용해 `SemanticScholarUnavailable`의 클래스 동일성을 보존하고 잠복 깨진 `import scripts.X` 경로 2개를 보너스 수정. 1505 passed(+23 새, 0 회귀). #128 §4(OA + CR 항목별 병렬화)는 #138로 이월.

### v3.9.2 (2026-05-18) — #133 phase boundary hot-fix

> #133 종료(핫픽스 계층). 장기 아키텍처 수정은 #134의 v3.10 active conductor로 추적. 추가: CLAUDE.md의 라우팅 명확화 게이트(교차 단계 자료 → 조용한 디스패치 대신 a-d 옵션으로 명확화), 22개 단일 단계 에이전트가 프롬프트 hard fence(`## Phase Boundary (v3.9.2)`)를 받음, 16개 multi-phase / phase-orthogonal / cross-phase-meta 에이전트는 의도적으로 fence하지 않음(정직한 프레이밍 — 프로즈 플라시보는 거짓 강제 환상을 만듦), 자문 검증기 `scripts/check_pipeline_integrity.py`가 #133 패턴을 사후 감지. 교차 모델 스팟체크를 갖춘 행동 스모크 테스트(100% Opus 4.7, ≥75% Sonnet + GPT-5.5).

### v3.9.1 (2026-05-18) — #129 + #130 client hardening

> v3.9.0 핫픽스. OpenAlex / Crossref 응답 읽기 실패를 `*Unavailable`로 래핑(#129); `check_claim_audit_consistency`를 비문자열 `manifest_id`에 대해 보호(#130). 스펙 변경 없음.

### v3.9.0 (2026-05-17) — #102 cross-index triangulation measurement

> #102 종료. v3.7.3은 단일 인덱스(Semantic Scholar) contamination 감지를 도입했고, v3.9.0은 이를 **자문 증거로만** 3-인덱스 triangulation(S2 + OpenAlex + Crossref)으로 확장. `contamination_signals`에 두 개의 새 선택적 boolean(`openalex_unmatched`, `crossref_unmatched`); 수동 입력 not-rule도 대칭으로 확장. Finalizer가 (현재의 `*_unmatched` 필드에 대한 k=0/1/2/3) 4단계 자문 매트릭스를 추가하며 v3.7.3 레거시 `CONTAMINATED-UNMATCHED`를 k=1/k_max=1 S2-only 케이스용으로 보존. Formatter 패스스루 allowlist를 3 → 9 접미사로 확장; 거부 규칙 1-10은 R-L3-2-E에 따라 미변경. 정책 계층(strict 모드, hard-block tier, `venue_type` / `triangulation_policy`)은 spec §2.3에 따라 v3.10으로 보류. k=3 마커는 `CONTAMINATED-TRIANGULATION-UNMATCHED`(추론된 원인이 아니라 관측 가능한 것을 기술). 새 firm rule 3개: R-L3-2-C(k는 현재 필드에 대해 계산), R-L3-2-D(API 추론 분류 없음), R-L3-2-E(거부 목록 미변경; 패스스루 allowlist 확장).

**마이그레이션:** v3.7.3 코퍼스 — `python scripts/migrate_literature_corpus_to_v3_9_0.py PATH`를 실행해 새 두 필드를 백필. v3.7.3 이전 코퍼스 — 먼저 `migrate_literature_corpus_to_v3_7_3.py`를 실행한 다음 v3.9.0 마이그레이션(spec §3.7에 따라 데이지 체인; v3.9.0 도구는 이미 `contamination_signals.semantic_scholar_unmatched`를 가진 항목에만 작용).

### v3.8.2 (2026-05-17) — #118 uncited audit_tool_failure surface

> #118 종료. `ARS_CLAIM_AUDIT=1` uncited constraint-judging 경로는 `JudgeInvocationError` 시 `{"judgment": "NOT_VIOLATED"}`를 조용히 대체해, 일시적 judge 장애 시 HIGH-WARN constraint 점검을 억제했습니다. v3.8.2는 그 실패를 MED-WARN 자문 tier의 전용 `uncited_audit_failures[]` 집계로 라우팅하며, cited 경로 INV-14 행을 미러링하되 `claim_audit_result.ref_slug`가 필수이고 uncited 경로에는 바인딩할 ref가 없으므로 전용 스키마를 사용합니다. #118 이슈 본문의 option-1..4 트레이드오프는 option 2(새 집계)로 귀결 — option 4(re-raise 후 중단)는 불안정한 judge 엔드포인트에서의 감사 커버리지 손실로 기각.

- **새 `uncited_audit_failure.schema.json` 집계**(spec §3.6). constraint judge가 `JudgeInvocationError`를 일으킨 uncited 문장 × manifest 쌍당 한 항목. cited-path INV-14와 동일한 fault-class enum(`judge_timeout` / `judge_api_error` / `judge_parse_error` / `cache_corruption` / `retrieval_api_error` / `retrieval_timeout` / `retrieval_network_error`). `rule_version: D4-c-v1-uaf-v1`.
- **UAF-INV-1..UAF-INV-6 린트**(spec §6 rule 4d). `finding_id` 고유성, scoped_manifest_id 교차 배열 무결성, manifest_claim_id가 non-null일 때 (M, C) 쌍 무결성, (sentence, manifest)별 dedup, rationale fault_class 접두사, `constraint_violations[]`에 대한 교차 집계 배타성.
- **Finalizer §5 MED-WARN 자문 행**: 주석 `[CLAIM-AUDIT-TOOL-FAILURE-UNCITED — <fault-class>]`, 게이트 통과(retry-next-pass remediation). Formatter REFUSE 목록 미변경 — UAF는 참고용.
- **파이프라인 통합**(`scripts/claim_audit_pipeline.py`): 1211-1224 행의 swallow 지점 제거; `JudgeInvocationError`가 이제 UAF 행을 발행하고 다음 (sentence, manifest) 쌍으로 `continue`. 가짜 NOT_VIOLATED가 `constraint_violations[]`에 도달하지 않음.
- **테스트**: 새 18개(스키마/린트 TSUAFUncitedAuditFailureInvariants 15 + 파이프라인 통합 TP23UncitedJudgeOutageEmitsUAF 3). 베이스라인 694 → 712 테스트, 0 회귀.
- **에이전트 문서**(`academic-pipeline/agents/claim_ref_alignment_audit_agent.md`): Output emission 표가 일곱 번째 행 추가; Error handling 표가 3개 표면에서 uncited-path UAF 행과 함께 4개 표면으로 확장.

### v3.8.0 (2026-05-16) — L3 Claim-Faithfulness Locator + Audit (paired milestone)

> v3.7.3 + v3.8이 L3(claim-faithfulness) 격차를 end-to-end로 닫음. v3.7.3은 locator 인프라를 도입 — 모든 인용이 3계층 앵커를 가져 향후 감사가 인용된 구절을 가져올 수 있음. v3.8은 그 앵커를 소비하는 감사 패스를 도입해, 인용된 출처가 주장을 뒷받침하는지 판단하고 formatter terminal hard gate에서 HIGH-WARN 위반 출력을 거부. 이 릴리스는 v3.7.0 이후 누적된 audit-trail로 배포된 기능 PR 5개(#104 / #105 / #108 / #111 / #115)도 묶음.

- **#103 — `claim_ref_alignment_audit_agent`**(v3.8 PR #121). 옵트인(`ARS_CLAIM_AUDIT=1`, 기본 OFF) Stage 4→5 감사 에이전트. 샘플링된 모든 인용을 검색된 발췌에 대해 판단; `claim_audit_results[]` + `claim_intent_manifests[]` + `claim_drifts[]` + `uncited_assertions[]` + `constraint_violations[]` 집계를 발행. 8행 finalizer 매트릭스가 HIGH-WARN 클래스(CLAIM-NOT-SUPPORTED / NEGATIVE-CONSTRAINT-VIOLATION / FABRICATED-REFERENCE / ANCHORLESS / CONSTRAINT-VIOLATION-UNCITED)를 formatter REFUSE 규칙 6-10으로 라우팅. 캘리브레이션 러너가 20개 항목으로 구성된 골드셋과 함께 제공(T-C1 FNR<0.15 + FPR<0.10, T-C2 per-class, T-C3 shape integrity). dual-track 검토 8라운드(R1 codex + Gemini-3.1-pro-preview, Gemini 쿼터 소진 후 R2-R8 codex-only); 궤적 R1 4P1+2P2 → R8 0P1+4P2 ship gate.
- **v3.7.3 — Three-Layer Citation Emission + contamination signals**(PR #98). `synthesis_agent` / `draft_writer_agent` / `report_compiler_agent`가 `## Three-Layer Citation Emission (v3.7.3)` H2를 획득. 모든 `<!--ref:slug-->`가 `<!--anchor:<kind>:<value>-->`를 가지며 `<kind> ∈ {quote, page, section, paragraph, none}`(quote 앵커는 25단어로 제한, URL 인코딩). `pipeline_orchestrator_agent` finalizer가 precedence-zero NO-LOCATOR 점검을 갖는 5-cell이 됨. `formatter_agent`가 `[UNVERIFIED CITATION — NO QUOTE OR PAGE LOCATOR]`에 대한 명시적 hard-gate 거부를 추가. `literature_corpus_entry.schema.json`이 선택적 `contamination_signals: { preprint_post_llm_inflection, semantic_scholar_unmatched }` 객체를 추가. `bibliography_agent`가 ingest 시 두 신호를 계산. 11라운드 검토 궤적(Codex×10 + Gemini 교차 모델×1)이 22개 발견을 종료. 명세: `docs/design/2026-05-12-ars-v3.7.3-claim-faithfulness-and-contaminated-source-spec.md`. 외부 동기: Zhao et al. arXiv:2605.07723 (2026-05).
- **#108 — AI disclosure policy-anchor renderer**(audit-trail로 2026-05-14 릴리스). 기존 venue-track renderer와 더불어 PRISMA-trAIce / ICMJE / Nature / IEEE policy-anchor disclosure 경로를 추가.
- **#111 — systematic-review → academic-paper 핸드오프 시 `slr_lineage` 발행**(2026-05-15). Schema 9 선택적 boolean `slr_lineage` 필드; 생산자 `pipeline_orchestrator_agent`가 모든 핸드오프 전환에서 기록; 소비자 `disclosure` 모드가 §4.3 G2 invariant track gate에 따라 `--policy-anchor=prisma-trAIce`를 디스패치.
- **#104 — README 동기: Zhao et al. 코퍼스 규모 증거 앵커**(2026-05-15). README + `README.zh-TW.md` 동기 절이 v3.7.x 라인을 Zhao et al.의 146,932 환각 인용 발견에 견주어 프레이밍.
- **#105 — v3.7.3 contamination_signals 백필 마이그레이션 도구**(2026-05-15). `scripts/migrate_literature_corpus_to_v3_7_3.py`가 v3.7.3 이전 passport 전반에서 두 contamination 신호를 소급 계산.
- **#115 — Semantic Scholar 클라이언트 성숙도**(2026-05-15). `scripts/semantic_scholar_client.py`가 1-req/s throttle(`S2_API_KEY` 감지 시 0.1s로 하락), URLError 시 outage latch, 그리고 장기 교차 passport 배치용 `reset_outage_latch()`를 추가.

### v3.7.0 (2026-05-05) — Claude Code Plugin Packaging

> 플러그인 패키징 업그레이드: ARS가 이제 `/plugin marketplace add Imbad0202/academic-research-skills` + `/plugin install academic-research-skills`로 Claude Code CLI / VS Code / JetBrains에 한 줄로 설치됩니다. 전통적인 `git clone` + `~/.claude/skills/` 경로로 연결하는 방식도 계속 동작합니다 — 두 트랙 모두 일급입니다.

- **플러그인 manifest + marketplace 메타데이터**(Phase 1, PR #68). `.claude-plugin/plugin.json`이 스위트를 선언(`skills/` 디렉터리에서 상대 symlink로 자동 발견되는 4개 스킬). `.claude-plugin/marketplace.json`이 플러그인을 등록해 단일 GitHub 호스팅 엔드포인트가 marketplace 목록과 플러그인 소스를 모두 제공. README + `README.zh-TW.md` + `docs/SETUP.md`가 dual-track 설치 지침을 담음.
- **10개 슬래시 명령**(`commands/ars-*.md`, Phase 2.1, PR #69)이 `MODE_REGISTRY.md` 항목을 `/ars-<mode>` 트리거에 매핑. 모델 라우팅은 각 명령의 frontmatter에 고정 — `full`과 `revision-coach`에는 `opus`(아키텍처 / 검토 해석 깊이), 나머지 8개에는 `sonnet`. 프로젝트 정책에 따라 Haiku 없음.
- **3개 플러그인 탑재 에이전트**(`agents/*_agent.md`, Phase 2.1, PR #69)는 `deep-research/agents/`의 v3.6.7-하드닝된 다운스트림 에이전트에 대한 상대 symlink: `synthesis_agent`, `research_architect_agent`, `report_compiler_agent`. `scripts/check_v3_6_7_pattern_protection.py` hard-pinned 경로와 INV-3 manifest-confined Clause 1 invariant를 온전히 유지하기 위해 언더스코어 파일명 보존. Symlink(복사본 아님)는 단일 진실 원천을 보존하고 v3.6.7 §6 inversion sweep + INV-1/2/3 린트가 닫는 Pattern C3 공격 표면을 방지. (#413에서 실제 바이트 동일 복사본으로 구체화 — 상대 symlink는 `core.symlinks` 없는 Windows 체크아웃과 zip-download 설치를 깨뜨림; 단일 소스 보장은 `scripts/check_agents_mirror_sync.py` 바이트 동등 CI 린트로 이동.)
- **`model: inherit`**를 그 세 소스 에이전트 frontmatter에 추가. opus 세션이 ARS full 파이프라인을 실행할 때 (상한에 걸리는 대신) opus 에이전트를 유지하도록 `sonnet` 고정 대신 inherit 선택. 사용자의 `~/.claude/hooks/warn-agent-no-model.sh` PreToolUse 훅이 디스패치 경계에서 Haiku를 차단하므로 `inherit`은 이미 Haiku 없는 모델로 해석됨.
- **SessionStart announce 훅**(`hooks/hooks.json` + `scripts/announce-ars-loaded.sh`, Phase 2.2, PR #70). 플러그인 로드 시 훅이 10개 슬래시 명령, 3개 플러그인 에이전트, 토큰 예산 포인터를 LLM의 첫 턴에 `additionalContext`로 주입. `startup`과 `clear` 소스 값은 전체 announce를, `resume`과 `compact`는 컨텍스트 소모를 피하려 한 줄 ack를 받음. Bash 3.2 호환 — `brew install bash` 요구 없이 macOS 기본 `/bin/bash`에서 실행.
- **Phase 2.2 범위 축소**: `SubagentStop → run_codex_audit.sh` codex 감사 훅은 계약 격차(SubagentStop 페이로드가 stage/deliverable 정보를 담지 않아 wrapper가 필수 인자를 절반 추론해야 함)와 invoker-class 경계(`run_codex_audit.sh` 4–7행이 same-session in-LLM 호출을 금지; PostToolUse는 생산 세션 내부에서 발화) 때문에 v3.7.0에서 범위 제외. 실제 감사 훅 통합은 ARS가 stage/deliverable 전파 계약을 갖추는 향후 릴리스로 보류. `docs/design/2026-04-30-ars-v3.7.0-plugin-packaging-roadmap.md` Update note 2026-05-05 (Phase 2.2 scope reduction) 참조.
- **`docs/PERFORMANCE.md` + `.zh-TW.md`**가 inherit 의미론과 현재 3-에이전트 범위 경계를 설명하는 "v3.7.0 Plugin agents and model routing" 하위 절을 획득.
- **세 PR에 걸친 Codex 검토 체인**: 인라인 반복 8라운드 + PR 수준 신규 3라운드, 모두 머지 전 0 P0/P1/P2 발견으로 수렴. Phase 2.2 신규 PR 검토가 인라인 라운드가 놓친 P2 하나(따옴표 없는 `${CLAUDE_PLUGIN_ROOT}`가 공백 포함 설치 경로를 깨뜨림)를 잡음 — 구현 검토(인라인)와 계약 검토(신규) 분리의 가치를 확인.
- **변경되지 않은 것**: 네 개 스킬 디렉터리, 25개 모드 전부, 에이전트 프롬프트, 스키마 파일, 린트 계약. 플러그인 패키징은 새 최상위 표면(`commands/`, `agents/`, `hooks/`, `.claude-plugin/`, `skills/` symlink 디렉터리, 3개 플러그인 에이전트 `model: inherit` frontmatter 추가)만 추가. 기존 4.3k clone-install 사용자에게는 breaking 변경 없음.

### v3.6.8 (2026-05-03) — Generator-Evaluator Contract Gate (v3.6.6 spec ship)

> 명명 참고: 이 릴리스는 **v3.6.6 generator-evaluator contract** 스펙과 구현을 릴리스합니다. v3.6.6 작업은 프로젝트 순서 때문에 v3.6.7 이후에 도착했으며, 설계 문서는 계약 게이트 버전에 대해 v3.6.6 내부 명명을 유지하되, 스위트 릴리스는 CHANGELOG를 단조롭게 유지하기 위해 v3.6.8로 태깅됩니다.

- **Schema 13.1**(`shared/sprint_contract.schema.json`)이 Schema 13을 두 개의 새 `mode` enum 값(`writer_full` + `evaluator_full`), 두 개의 새 선택적 최상위 필드(`pre_commitment_artifacts` writer 전용, `disagreement_handling` evaluator 전용), 그리고 reviewer- / writer- / evaluator-조건부 게이트를 강제하는 12개 `allOf` 분기로 확장. 기존 reviewer 계약은 Schema 13.1 하에서 바이트 동등하게 검증됨(§3.6 zero-touch promise).
- **두 개의 새로 탑재된 계약 템플릿** `shared/contracts/writer/full.json`(D1–D7, F1/F4/F2/F3/F0)과 `shared/contracts/evaluator/full.json`(D1–D5, F1/F2/F3/F6/F4/F5/F0). 스펙 브랜치의 설계 시점 산출물에서 Schema 13.1 업그레이드와 원자적으로 live 출시 상태로 승격.
- **2단계 오케스트레이션** `academic-paper full` 내부: Phase 4가 Phase 4a(writer paper-blind pre-commitment) + Phase 4b(writer paper-visible drafting + self-scoring)로 분할; Phase 6이 Phase 6a(evaluator paper-blind pre-commitment) + Phase 6b(evaluator paper-visible scoring + decision)로 분할. Phase 번호가 붙은 `<phase4a_output>` / `<phase6a_output>` 데이터 구분자가 v3.6.2 reviewer 패턴을 미러링. 린트 수 요약: writer 3+4 / evaluator 5+5 / reviewer 5+6 (reviewer는 zero-touch 유지).
- **`academic-paper` SKILL + 에이전트 파일**이 축어적 `## v3.6.6 Generator-Evaluator Contract Protocol` 블록을 획득(SKILL.md 101행 + `draft_writer_agent.md` 47행 + `peer_reviewer_agent.md` 57행). SKILL.md는 v3.6.7+용 graceful-degradation + cross-session resume forward notes를 담는 새 `## Known limitations` 절도 추가.
- **검증기 확장**: `scripts/check_sprint_contract.py` SC-* mode-gating 감사(SC-5 + SC-11 reviewer 전용; SC-9는 세 mode 패밀리 전반으로 확장). 새 17개 테스트가 검증기 유닛 테스트 수를 54에서 71로 증가(positive + schema-branch negative 5 + §3.6 reviewer 회귀 2 + mode-gating 6).
- **Manifest CI 린트**: `scripts/check_v3_6_6_ab_manifest.py`가 `tests/fixtures/v3.6.6-ab/manifest.yaml`에 대해 §6.2 manifest 스키마 + §6.5 git-tracked invariant를 강제. `.github/workflows/spec-consistency.yml`이 기존 reviewer 루프와 더불어 writer + evaluator 템플릿 디렉터리를 순회하도록 sprint contract 검증 루프를 확장하고, 새 manifest CI 린트를 실행.
- **A/B 증거 픽스처 스텁** `tests/fixtures/v3.6.6-ab/`(30 파일): manifest + README + paper-A 입력/베이스라인 6 + paper-C 입력/베이스라인 1 + Stage 3 reviewer 발췌 + codex-judge 베이스라인 placeholder 6. 실제 픽스처 데이터는 구현 작업이 완전히 완료되기 전 후속 커밋에서 채워짐.

### v3.6.7 (2026-04-30) — Downstream-Agent Pattern Protection (Step 1+2)

- **세 다운스트림 에이전트가 문서화된 17개 환각/드리프트 패턴 중 13개에 대해 하드닝**: `synthesis_agent`(A1–A5 narrative 측), `research_architect_agent`의 survey-designer 모드(B1–B5 instrument 측), `report_compiler_agent`의 abstract-only 모드(C1–C3 publication 측). 각 에이전트 프롬프트가 이제 `PATTERN PROTECTION (v3.6.7)` 블록을 담음.
- **`shared/references/`의 참조 파일 4개**: `irb_terminology_glossary.md`, `psychometric_terminology_glossary.md`, `protected_hedging_phrases.md`, `word_count_conventions.md`. 참조 파일은 에이전트 프롬프트가 경로로 인용하는 운영 계약을 담음.
- **교차 모델 감사 프롬프트 템플릿** `shared/templates/codex_audit_multifile_template.md`로, 7개 감사 차원과 `report_compiler_agent` 번들용 필수 3부 Section 4(f) 점검. 어느 하위 점검이라도 실패하면 P1 발견.
- **정적 린트 + 29-테스트 뮤테이션 스위트**: `scripts/check_v3_6_7_pattern_protection.py`가 protection-clause 존재와 obligation-phrase 형태를 강제; `scripts/test_check_v3_6_7_pattern_protection.py`가 codex 검토 증거를 보존해 향후 checker 회귀가 CI에 드러나도록. 둘 다 `.github/workflows/spec-consistency.yml`에 연결.
- **Codex 검토 이력**: `gpt-5.5` + `xhigh` 교차 모델 검토 7라운드가 P1+P2 발견 0으로 SHIP-OK 도달. Step 6(orchestrator runtime hooks)과 Step 8(synthetic eval case)은 후속 PR에서 출시.

### v3.6.5 (2026-04-27) — Material Passport `literature_corpus[]` Consumer Integration

- **두 개의 Phase 1 문헌 소비자** 연결: `deep-research/agents/bibliography_agent.md`와 `academic-paper/agents/literature_strategist_agent.md`. passport가 비어 있지 않은 `literature_corpus[]`를 담을 때 둘 다 동일한 5단계 **corpus-first, search-fills-gap** 흐름과 동일한 네 Iron Rule(Same criteria / No silent skip / No corpus mutation / Graceful fallback on parse failure)을 따름.
- **Search Strategy 보고서의 PRE-SCREENED 재현성 블록**: 포함/제외/건너뜀 corpus 항목을 열거하며, F3 zero-hit 노트와 `obtained_via` / `obtained_at`의 부분 선언 주위를 구성하는 F4a–F4f provenance 보고. `final_included = pre_screened_included[] ∪ external_included[]`는 중립 유지 — bibliography 항목이나 literature matrix 행에 provenance 태그 없음.
- **소비자 프로토콜 참조** `academic-pipeline/references/literature_corpus_consumers.md`로, 정규 PRE-SCREENED 템플릿, BAD/GOOD 예시, 네 Iron Rule, 소비자별 읽기 지침 포함.
- **CI 린트** `scripts/check_corpus_consumer_protocol.py`가 manifest 기반 소비자 목록(`scripts/corpus_consumer_manifest.json`)으로 9개 프로토콜 invariant를 강제.
- **Schema 9 단서 폐기**: `shared/handoff_schemas.md`가 v3.6.4 "Consumer-side integration deferred to v3.6.5+" 단서를 폐기; 소비자 프로토콜로의 backpointer로 대체.
- 존재 기반, 스키마 변경 없음, 새 env 플래그 없음. 파싱 실패는 `[CORPUS PARSE FAILURE]` 표면과 함께 external-DB-only 흐름으로 폴백. `citation_compliance_agent` corpus 통합은 보류(목표 버전 TBD, post-v3.8).
- breaking 변경 없음.

### v3.6.4 (2026-04-25) — Material Passport `literature_corpus[]` Input Port

- **`literature_corpus[]` 필드**가 사용자 소유 문헌을 위한 선택적 입력 포트로 Schema 9에 추가. 각 항목은 `shared/contracts/passport/literature_corpus_entry.schema.json`을 따름(CSL-JSON authors, year, title, source_pointer + private 선택적 `abstract` / `user_notes`).
- **언어 중립 어댑터 계약** `academic-pipeline/references/adapters/overview.md`: 사용자 코퍼스 소스를 읽는 모든 프로그램(어떤 언어든)이 적합한 `passport.yaml` + `rejection_log.yaml`을 생성 가능. Fail-soft 항목 수준 오류, fail-loud 어댑터 수준 오류, 결정론적 순서.
- **세 개의 참조 Python 어댑터** `scripts/adapters/` 하위: `folder_scan.py`(PDF 파일시스템), `zotero.py`(Better BibTeX JSON export), `obsidian.py`(vault frontmatter). 시작점일 뿐이며, 사용자는 비참조 소스용 자체 어댑터를 작성하도록 기대됨.
- **Rejection log 계약** `shared/contracts/passport/rejection_log.schema.json`으로, 범주적 이유 값의 닫힌 enum; 항상 발행(거부 없으면 빈 값).
- **CI 게이트**: `scripts/check_literature_corpus_schema.py`가 스키마 + 어댑터 예시를 검증; `scripts/sync_adapter_docs.py --check`가 schema→docs 드리프트를 방지; 새 `pytest.yml` 워크플로가 경로 필터 트리거로 `scripts/adapters/tests/`를 실행.
- **v3.6.4에서는 입력 포트만**: v3.6.4는 소비자 통합 없이 스키마와 어댑터 계약을 출시. `bibliography_agent`와 `literature_strategist_agent`는 v3.6.5에서 연결됨.
- breaking 변경 없음.

### v3.6.3 (2026-04-23) — Opt-in Passport Reset Boundary

- **옵트인 passport reset boundary**(`ARS_PASSPORT_RESET=1`). 모든 FULL 체크포인트를 컨텍스트 리셋 경계로 승격. 새 `resume_from_passport=<hash>` 모드로 사용자가 Material Passport 원장만으로 새 Claude Code 세션에서 재개 가능. 플래그 ON인 `systematic-review` 모드는 모든 FULL 체크포인트에서 리셋을 필수로 만듦; 다른 모드는 리셋을 플래그 게이트된 기본값으로 취급. 플래그 OFF는 v3.6.3 이전 동작을 바이트 단위로 보존.
- Schema 9가 두 항목 종류(`kind: boundary` + `kind: resume`)를 갖는 append-only `reset_boundary[]` 원장을 획득. 해시는 self-reference 안전을 위한 정규 placeholder와 함께 JSON Canonical Form + SHA-256 사용. 선택적 `pending_decision`이 MANDATORY 분기 선택을 처리.
- 새 `scripts/check_passport_reset_contract.py` CI 린트: 플래그를 언급하는 모든 곳은 권위 있는 프로토콜 문서로의 포인터를 같은 위치에 두어야 함.
- 프로토콜 문서: `academic-pipeline/references/passport_as_reset_boundary.md`.
- `docs/PERFORMANCE.md`가 장기 세션 가이던스로 업데이트.
- breaking 변경 없음. 플래그 기본값은 OFF.

### v3.6.2 (2026-04-23) — Reviewer Sprint Contract Hard Gate

v3.6.2는 Schema 13 sprint contract와, 리뷰어가 논문을 읽기 전에 채점 계획을 미리 약속하도록 강제하는 hard-gate 오케스트레이션을 도입합니다. Reviewer-only 첫 테스트 케이스; writer/evaluator는 v3.6.4로 보류. CHANGELOG 참조.

- **Schema 13 sprint contract**로 `panel_size`, `acceptance_dimensions`, `failure_conditions`(`severity` 우선순위 + panel-relative `cross_reviewer_quantifier` 포함), `measurement_procedure`, 선택적 `override_ladder`, 경계 지어진 `agent_amendments`. 검증기: `scripts/check_sprint_contract.py`.
- **2단계 호출 hard gate.** 리뷰어가 paper-content-blind Phase 1 + paper-visible Phase 2를 실행; Phase 1 출력은 self-injection 표면을 좁히기 위해 `<phase1_output>...</phase1_output>` 데이터 구분자로 감싸짐.
- **Synthesizer 3단계 기계적 프로토콜.** 교차 리뷰어 매트릭스 구축 → panel-relative quantifier + 인식된 표현 어휘로 각 `failure_condition` 평가 → `severity`로 우선순위 해소. Forbidden-ops 목록이 `editorial_synthesizer_agent`에 명시.
- **두 reviewer 템플릿 제공**(`shared/contracts/reviewer/full.json` panel 5; `shared/contracts/reviewer/methodology_focus.json` panel 2). `reviewer_re_review`, `reviewer_calibration`, `reviewer_guided`는 스키마 enum에 예약되어 있으나 v3.6.2에서는 계약 템플릿 없이 출시; v3.6.2 이전 동작 유지. `reviewer_quick`은 enum에서 완전히 제외.
- `academic-paper-reviewer` SKILL 버전: `1.8.1 → 1.9.0`. `academic-pipeline` SKILL 버전: `3.5.1 → 3.6.2`(suite-version invariant). 스위트 버전 `3.6.2`로 상향.
- spec [`docs/design/2026-04-23-ars-v3.6.2-sprint-contract-design.md`](docs/design/2026-04-23-ars-v3.6.2-sprint-contract-design.md)와 프로토콜 [`academic-paper-reviewer/references/sprint_contract_protocol.md`](academic-paper-reviewer/references/sprint_contract_protocol.md) 참조.

### v3.5.1 (2026-04-22) — Opt-in Socratic Reading-Check Probe

v3.5.1은 Socratic Mentor에 옵트인 정직성 프로브(`ARS_SOCRATIC_READING_PROBE=1`)를 추가합니다. 기본 off. CHANGELOG 참조.

- **옵트인 reading-check probe**: `ARS_SOCRATIC_READING_PROBE=1`이 설정되면, 사용자가 특정 논문을 인용한 목표지향형 세션에서 Socratic Mentor가 일회성 정직성 프로브를 발화. 거절은 페널티 없이 로깅됨. 결과는 Research Plan Summary와 Stage 6 AI Self-Reflection Report로 흐름. 새 에이전트 없음, 스키마 변경 없음.
- `deep-research` SKILL 버전: `2.9.0 → 2.9.1`. `academic-pipeline` SKILL 버전: `3.5.0 → 3.5.1`. 스위트 버전 `3.5.1`로 상향.

### v3.5.0 (2026-04-21) — Collaboration Depth Observer

- **새 에이전트**: `academic-pipeline`의 `collaboration_depth_agent`(Agent Team이 3에서 4로 증가). 모든 FULL/SLIM 체크포인트와 파이프라인 완료 시 호출; 4차원 루브릭에 대해 사용자-AI 협업을 채점. **자문 전용 — 진행을 절대 차단하지 않음.** MANDATORY 체크포인트(Stage 2.5 / 4.5 무결성 게이트)는 observer를 호출하지 않음.
- **새 루브릭**: [`shared/collaboration_depth_rubric.md`](shared/collaboration_depth_rubric.md) v1.0. 차원: Delegation Intensity, Cognitive Vigilance, Cognitive Reallocation, Zone Classification(Zone 1 / Zone 2 / Zone 3). Wang, S., & Zhang, H. (2026). "Pedagogical partnerships with generative AI in higher education: how dual cognitive pathways paradoxically enable transformative learning." *International Journal of Educational Technology in Higher Education*, 23:11. DOI [10.1186/s41239-026-00585-x](https://doi.org/10.1186/s41239-026-00585-x)에 기반.
- **교차 모델 발산은 평균이 아니라 플래그**: `ARS_CROSS_MODEL`이 설정되면 observer가 두 모델 모두에서 실행; 차원 불일치 > 2점은 조용히 평활화되지 않고 보고됨. 비용 트레이드오프용 `ARS_CROSS_MODEL_SAMPLE_INTERVAL` 탈출구.
- **Short-stage guard**: 사용자 턴이 5 미만인 단계는 full-model observer 디스패치 대신 정적 `insufficient_evidence` 블록을 주입.
- **안티-아첨 규율**: 점수 ≥ 7은 특정 대화 턴 인용을 요구; Zone 3은 재감사를 트리거; motivational framing 없음.
- `academic-pipeline` SKILL 버전: `3.3.0 → 3.4.0`. 스위트 버전 `3.5.0`으로 상향. 새 린트 `scripts/check_collaboration_depth_rubric.py` + 10개 테스트.

### v3.4.0 (2026-04-20) — Compliance Agent + Schema 12

- **Compliance Agent**(shared): PRISMA-trAIce 17개 항목(SR 모드만) + RAISE 4 원칙 + 8-role 매트릭스를 실행하는 단일 mode-aware 에이전트. 기존 Stage 2.5 / 4.5 Integrity Gate에 연결; tier 기반 차단(Mandatory → block, HR → warn, R/O → info). 비-SR 항목은 principles-only, warn-only로 실행.
- **Schema 12 compliance_report**가 `compliance_history[]`(append-only)를 통해 Material Passport에 추가.
- **3라운드 사용자 오버라이드 사다리**가 `disclosure_addendum`을 원고에 자동 주입. 감지 회피 불가능.
- **투명한 보고를 갖춘 캘리브레이션**, hard FNR/FPR 게이트 없음 — `task_type: open-ended`와 self-consistent.
- **상류 freshness CI**가 PRISMA-trAIce 드리프트를 경고(non-blocking).
- **장기 세션 문서**: cross-session resume 메커니즘으로서의 Material Passport.

### v3.3.6 (2026-04-15) — README Streamlining + ARCHITECTURE doc

- `docs/ARCHITECTURE.md`를 파이프라인 구조(흐름, 매트릭스, 데이터 접근, 의존성 그래프, 품질 게이트, 모드)의 단일 진실 원천으로 추가. PR #18을 통해 main에 머지.
- `docs/SETUP.md`(사전 요건, API 키, Pandoc/tectonic, 교차 모델 검증, 설치 방법)와 `docs/PERFORMANCE.md`(토큰 예산, 권장 Claude Code 설정)를 추가. README는 인라인 대신 둘 모두로 링크.
- README 간소화: ASCII 파이프라인 다이어그램과 16개 핵심 기능 목록 제거(ARCHITECTURE.md로 대체); Skill Details 절은 이제 버전 번호를 고정하고 에이전트별 명단은 ARCHITECTURE.md §3을 가리킴.
- 참고: 어떤 스킬에도 기능 변경 없음. 순수 문서 재구성. 스위트 버전 `3.3.6`으로 상향.

### v3.3.5 (2026-04-15)
- `benchmark_report.schema.json` + Material Passport의 선택적 `repro_lock` 블록 추가. 둘 다 패턴 문서, 린트, 예시와 함께 제공. 최초의 공식 Python dev dep manifest(`requirements-dev.txt`).

### v3.3.4 (2026-04-15) — README Changelog Sync Patch

- `README.md`와 `README.zh-TW.md`의 임베디드 changelog 절을 동기화해 누락된 `v3.3.3`과 `v3.3.2` 릴리스 요약을 포함.
- `scripts/check_spec_consistency.py`를 확장해 향후 README changelog 드리프트가 CI를 실패시키도록 함.
### v3.3.3 (2026-04-15) — Release Prep + Lint Hardening

- SKILL frontmatter 린팅 하드닝: 닫는 `---` fence가 누락되면 유효한 YAML로 잘못 파싱되지 않고 명확하게 실패합니다.
- 유효한 YAML이지만 매핑이 아닌 것으로 파싱되는 frontmatter가 이제 충돌 대신 읽기 쉬운 오류를 보고.
- 두 README의 post-publication audit report 깨진 showcase 링크 수정.
- 죽은 링크가 CI를 실패시키도록 README 상대 링크 검증을 spec consistency 점검에 추가.
- 문서 전반의 DOCX 출력 계약 정렬: 직접 `.docx` 생성은 Pandoc 의존이며, 폴백으로 Markdown + 변환 지침.
- `v3.3.3` 릴리스 준비: 스위트 버전 상향, `academic-paper` -> v3.0.2, `academic-pipeline` -> v3.2.2.

### v3.3.2 (2026-04-15) — Data Access Levels + Task Type Metadata

- 모든 최상위 `SKILL.md` 파일에 강제 어휘를 갖는 `metadata.data_access_level` 추가: `raw`, `redacted`, `verified_only`.
- 모든 최상위 `SKILL.md` 파일에 강제 어휘를 갖는 `metadata.task_type` 추가: `open-ended`, `outcome-gradable`.
- 두 메타데이터 필드에 대한 린트 스크립트와 유닛 테스트 추가, GitHub Actions spec consistency 워크플로에 연결.
- `shared/ground_truth_isolation_pattern.md` 추가, `shared/handoff_schemas.md`에서 새 어휘를 링크.

### v3.3.1 (2026-04-14) — Spec Consistency Patch

- README, `.claude/CLAUDE.md`, `MODE_REGISTRY.md`, `SKILL.md` 파일을 현재 모드 수와 게시된 스킬 버전에 동기화.
- 교차 모델 표현 수정: 무결성 샘플 점검과 독립 DA 비평은 오늘날 구현됨; sixth-reviewer 동료 심사는 계획 단계로 유지.
- SLIM 체크포인트도 명시적 사용자 확인을 기다리도록 적응형 체크포인트 의미론 명확화.
- Stage 2.5와 Stage 4.5 무결성 게이트가 건너뛸 수 없음을 재확인.
- 향후 드리프트를 잡기 위한 경량 spec consistency 점검과 GitHub Actions 워크플로 추가.

### v3.3 (2026-04-09) — PaperOrchestra-Inspired Enhancements

[PaperOrchestra](https://arxiv.org/abs/2604.05018) (Song, Song, Pfister & Yoon, 2026, Google)의 기법을 통합.

- **Semantic Scholar API Verification** — S2 API를 통한 Tier 0 프로그래밍 방식 참고문헌 존재 점검. Levenshtein >= 0.70 제목 매칭, DOI 불일치 감지, S2 ID를 통한 bibliography 중복 제거. API 사용 불가 시 우아한 degradation.
- **Anti-Leakage Protocol** — Knowledge Isolation Directive가 LLM 파라메트릭 메모리보다 세션 자료를 우선. 누락 콘텐츠를 메모리에서 채우는 대신 `[MATERIAL GAP]`로 플래그. Mode 5/6 실패 위험 감소.
- **VLM Figure Verification**(선택) — vision 가능 LLM으로 렌더링된 그림의 폐루프 검증. 10점 체크리스트, 최대 2회 정제 반복.
- **Score Trajectory Protocol** — 수정 라운드 전반의 차원별 루브릭 점수 델타 추적(7차원). 회귀(delta < -3) 감지 및 필수 체크포인트 트리거.
- **Stage 2 Parallelization** — outline 완료 후 시각화와 논증 구축을 병렬 실행 가능.
- 새 버전: deep-research v2.8, academic-paper v3.0, academic-pipeline v3.2

### v3.2 (2026-04-09) — Lu 2026 Nature Integration

Lu et al. (2026, *Nature* 651:914-919) — 블라인드 동료 심사를 통과한 최초의 end-to-end 자율 AI 연구 시스템 — 의 통찰을 통합.

- **7-mode AI Research Failure Mode Checklist** — 의심되는 구현 버그, 환각된 결과, 지름길 의존, 버그를 통찰로, 방법론 날조, 프레임 고착에 대해 Stage 2.5/4.5에서 파이프라인을 차단. 기존 5종 인용 환각 분류를 확장.
- **Reviewer Calibration Mode**(academic-paper-reviewer v1.8) — 사용자 제공 골드셋에 대한 옵트인 FNR/FPR/balanced-accuracy 측정. 5× ensembling, 교차 모델 기본 ON, 세션 범위 신뢰도 공개.
- **Disclosure Mode**(academic-paper v2.9) — venue별 AI 사용 명시문 생성기. v1은 ICLR, NeurIPS, Nature, Science, ACL, EMNLP 커버.
- **Early-Stopping Criterion**(academic-pipeline v3.1) — 파이프라인 시작 시 수렴 점검 + 예산 투명성.
- **Fidelity-Originality Mode Spectrum** — Lu 2026 Fig 1c에 따라 3개 스킬 전반의 모든 모드를 분류.
- 새 버전: academic-paper v2.9, academic-paper-reviewer v1.8, academic-pipeline v3.1

### v3.1.1 (2026-04-09) — IS Senior Scholars' Basket of 11

외부 기여: [@mchesbro1](https://github.com/mchesbro1)이 IS Basket of 8 저널을 최초로 제안하고 초안 작성([Issue #5](https://github.com/Imbad0202/academic-research-skills/issues/5)); [@cloudenochcsis](https://github.com/cloudenochcsis)가 이를 전체 Senior Scholars' Basket of 11로 확장([Issue #7](https://github.com/Imbad0202/academic-research-skills/issues/7), [PR #8](https://github.com/Imbad0202/academic-research-skills/pull/8)). `academic-paper-reviewer/references/top_journals_by_field.md` Section 7을 업데이트해 *Decision Support Systems*, *Information & Management*, *Information and Organization*을 추가. 출처: [AIS Senior Scholars' List of Premier Journals](https://aisnet.org/research/seniorscholarsbasket/).

### v3.1 (2026-04-06) — Anti-Context-Rot + Cognitive Frameworks + Lean Size

[aspi6246/Claude-Code-Skills-for-Academics](https://github.com/aspi6246/Claude-Code-Skills-for-Academics)의 패턴에서 영감을 받음.

**Wave 1: Anti-Context-Rot Anchors**
- 4개 스킬 전반의 명시적 안티패턴 29개("Why It Fails" + "Correct Behavior"를 갖는 표 형식, 스킬당 7-8개)
- 긴 대화에서도 위반되어선 안 되는 핵심 규칙에 대한 IRON RULE 마커 22개
- academic-paper-reviewer의 읽기 전용 제약(리뷰어는 원고를 수정할 수 없음)

**Wave 2: Traceability + Cognitive Frameworks + Reinforcement**
- R&R Traceability Matrix(Schema 11): re-review 출력에 "Author's Claim"과 "Verified?" 열을 추가해 수정 주장의 독립 검증을 가능하게 함
- 에이전트에게 "무엇을 할지"가 아니라 "어떻게 생각할지"를 가르치는 인지 프레임워크 참조 파일 3개:
  - `argumentation_reasoning_framework.md` — Toulmin model, Bradford Hill 인과 추론, inference to best explanation, 인식론적 상태 분류
  - `review_quality_thinking.md` — 세 렌즈(internal validity, external validity, contribution), 흔한 리뷰어 함정, 캘리브레이션 질문
  - `writing_judgment_framework.md` — clarity test, reader's journey, 분야별 voice, 수정 결정 매트릭스
- 대화 중 강화 프로토콜: 모든 파이프라인 전환에서 단계별 IRON RULE + 안티패턴 리마인더
- 모든 FULL 체크포인트에서 자기 점검 질문(인용 무결성, 아첨적 양보, 품질 궤적, 범위 규율, 완결성)

**Wave 3: Lean Skill Size**
- 상세 프로토콜을 `references/` 파일로 추출해 SKILL.md 총 크기를 142KB에서 85KB로 축소(−40%)
- 약 15개의 새 참조 파일 생성(re-review 프로토콜, guided 모드, systematic review, process summary, external review 등)
- 모든 IRON RULE 마커는 SKILL.md에 보존; 상세 콘텐츠는 온디맨드 로드
- 새 버전: deep-research v2.7, academic-paper v2.8, academic-paper-reviewer v1.7, academic-pipeline v3.0

### v3.0 (2026-04-03) — Anti-Sycophancy + Intent Detection + Dialogue Health
- **Devil's Advocate Concession Threshold**(deep-research + academic-paper-reviewer): DA는 응답 전 반박을 1-5로 채점해야 함. 양보는 ≥4에서만. 연속 양보 없음. 양보율 추적. 각 체크포인트 후 프레임 고착 감지.
- **Attack Intensity Preservation**(academic-paper-reviewer): DA는 반박에 약해지지 않음. 명시적 deflection 감지를 갖는 반박 평가 프로토콜. 안티-아첨 규칙이 끈질긴 반박을 유효한 증거로 취급하지 못하게 함.
- **Intent Detection Layer**(deep-research socratic): 사용자 의도를 탐색형 대 목표지향형으로 분류. 탐색형 모드는 자동 수렴 비활성화, 최대 라운드 상향, 조기 종료 금지. 매 3턴마다 재평가.
- **Dialogue Health Indicator**(deep-research socratic): 매 5턴마다 지속적 동의, 갈등 회피, 조기 수렴에 대한 조용한 자기 점검. 동의 패턴 감지 시 도전 자동 주입.
- **Cross-Model Verification Protocol**(shared, 선택): 무결성 검증 샘플 교차 점검과 독립 DA 비평에 GPT-5.4 Pro 또는 Gemini 3.1 Pro 사용. Sixth-reviewer 동료 심사는 계획 단계로 아직 미구현. `ARS_CROSS_MODEL` env var 설정으로 활성화 — 없으면 모든 것이 이전처럼 동작. 전체 설정 가이드, API 패턴, 비용 추정은 `shared/cross_model_verification.md` 참조.
- **AI Self-Reflection Report**(academic-pipeline Stage 6): 파이프라인 후 AI 행동 패턴 자기 평가 — DA 양보율, 체크포인트 건너뜀률, health 경보, 아첨 위험 등급(LOW/MEDIUM/HIGH), 프레임 고착 사건, 수렴 패턴 분석. 아이러니 단서 포함: "이 자기 성찰은 아첨적이었을 수 있는 바로 그 AI가 생성한 것이다."
- 기원: DA가 너무 빨리 양보하고, Socratic Mentor가 조기 수렴을 시도했으며, 전체 토론이 인간이 설정한 프레임에 갇혔던 4라운드 변증법 실험을 통해 발견.
- 버전: deep-research v2.5, academic-paper-reviewer v1.5, academic-pipeline v2.8

### v2.9.1 (2026-04-03) — Skill Metadata
- 4개 SKILL.md frontmatter 전부에 `status: active`와 `related_skills` 교차 참조 추가.
- `deep-research` ↔ `academic-paper` ↔ `academic-paper-reviewer` ↔ `academic-pipeline` 전반의 스킬 발견 도구와 교차 스킬 내비게이션을 가능하게 함.

### v2.9 (2026-03-27) — Style Calibration + Writing Quality Check
- **Style Calibration**(academic-paper intake Step 10, 선택): 과거 논문 3편 이상을 제공하면 파이프라인이 사용자의 문체 — 문장 리듬, 어휘 선호, 인용 통합 방식 — 를 학습. 초안 작성 중 soft guide로 적용; 분야 관례가 항상 우선. 우선순위 체계: 분야 규범(hard) > 저널 관례(strong) > 개인 문체(soft). `shared/style_calibration_protocol.md` 참조
- **Writing Quality Check**(`academic-paper/references/writing_quality_check.md`): 초안 자기 검토 중 적용되는 글쓰기 품질 체크리스트. 5개 범주: AI 고빈도 용어 경고(25개 용어), 구두점 패턴 제어(em dash ≤3), throat-clearing opener 감지, 구조 패턴 경고(Rule of Three, 균일한 단락, 동의어 순환), burstiness 점검(문장 길이 변화). 이는 좋은 글쓰기 규칙이지 감지 회피가 아님
- **Style Profile**이 academic-pipeline Material Passport(`shared/handoff_schemas.md`의 Schema 10)를 통해 전달됨
- **deep-research** report compiler도 두 기능을 선택적으로 소비
- 버전: academic-paper v2.5, deep-research v2.4, academic-pipeline v2.7

### v2.8 (2026-03-22) — SCR Loop Phase 1: State-Challenge-Reflect
- **Socratic Mentor Agent**(deep-research + academic-paper): SCR(State-Challenge-Reflect) 프로토콜 통합
  - **Commitment Gates**: 각 계층/챕터 전환에서 증거 제시 전 사용자 예측 수집
  - **Certainty-Triggered Contradiction**: 고신뢰 언어("obviously", "clearly") 감지 후 반론 도입
  - **Adaptive Intensity**: commitment 정확도 추적, 도전 빈도 동적 조정
  - **Self-Calibration Signal (S5)**: 대화 전반에 걸친 사용자의 self-calibration 성장을 추적하는 새 수렴 신호
  - **SCR Switch**: 사용자가 "skip the predictions"로 비활성화하거나 "turn predictions back on"으로 대화 중 재활성화 가능; 소크라테스식 질문은 정상 지속
- `deep-research/references/socratic_questioning_framework.md`: SCR 단계를 소크라테스식 기능에 매핑하는 SCR Overlay Protocol
- `CHANGELOG.md` 추가

### v2.7 (2026-03-09) — Integrity Verification v2.0: Anti-Hallucination Overhaul
- **integrity_verification_agent v2.0**: Anti-Hallucination Mandate(AI 메모리 검증 없음), gray-zone 분류 제거(VERIFIED/NOT_FOUND/MISMATCH만), 모든 참고문헌에 대한 필수 WebSearch 감사 추적, Stage 4.5 신선한 독립 검증, Gray-Zone Prevention Rule
- **Known Hallucination Patterns**: GPTZero × NeurIPS 2025 연구에서 나온 5종 분류(TF/PAC/IH/PH/SH), 5개 복합 기만 패턴, 실세계 사례 연구, 문헌 통계
- **Post-publication audit**: 전체 68개 참고문헌의 완전한 WebSearch 검증이 3회의 무결성 점검을 통과한 21개 문제(31% 오류율)를 발견 — 외부 검증의 필요성을 입증
- **논문 수정**: 날조된 참고문헌 4개 제거, 저자 오류 6개 수정, 메타데이터 오류 7개 수정, 형식 문제 2개 수정

### v2.6.2 (2026-03-09) — Intent-Based Mode Activation
- **deep-research**: Socratic 모드가 이제 키워드 매칭 대신 **의도 기반 활성화**를 사용. 어떤 언어에서도 동작 — 특정 문자열 매칭이 아니라 의미(예: "사용자가 가이드된 사고를 원함")를 감지.
- **academic-paper**: Plan 모드가 이제 **의도 기반 활성화**를 사용. "사용자가 시작 방법을 모름" 또는 "사용자가 단계별 가이드를 원함" 같은 의도 신호를 어떤 언어에서도 감지.
- 두 모드 모두 이제 **기본 규칙**을 가짐: 의도가 모호할 때 `full`보다 `socratic`/`plan`을 선호 — 먼저 안내하는 편이 더 안전.
- 2계층 아키텍처: Layer 1(스킬 활성화)은 매칭 신뢰도를 위해 이중언어 키워드 사용; Layer 2(모드 라우팅)는 언어 무관 의도 신호 사용.

### v2.6.1 (2026-03-09) — Bilingual Trigger Keywords
- **deep-research**: 일반 활성화와 Socratic 모드를 위한 번체중국어 트리거 키워드 추가.
- **academic-paper**: 번체중국어 트리거 키워드와 Plan Mode 트리거 절 추가.
- 두 모드 선택 가이드 모두 이제 이중언어 예시와 중국어 특유의 오선택 시나리오 포함.

### v2.6 / v2.4 / v1.4 (2026-03-08) — 15+ Improvements
- **deep-research v2.3**: 새 systematic-review / PRISMA 모드(7번째); 새 에이전트 3개(risk_of_bias, meta_analysis, monitoring); PRISMA 프로토콜/보고서 템플릿; Socratic 수렴 기준(4 신호 + auto-end); Quick Mode Selection Guide
- **academic-paper v2.4**: 새 에이전트 2개(visualization, revision_coach); 4가지 상태 유형을 갖는 수정 추적 템플릿; 인용 형식 변환(APA↔Chicago↔MLA↔IEEE↔Vancouver); 통계 시각화 표준; Socratic 수렴 기준; 수정 복구 예시; **LaTeX 출력 하드닝** — 필수 `apa7` document class, 텍스트 justification 수정(`ragged2e` + `etoolbox`), 표 열 너비 공식, 이중언어 초록 centering, 표준화된 폰트 스택(Times New Roman + Source Han Serif TC VF + Courier New), tectonic 경유 PDF만
- **academic-paper-reviewer v1.4**: 0-100 점수와 행동 지표를 갖는 품질 루브릭; 결정 매핑(≥80 Accept, 65-79 Minor, 50-64 Major, <50 Reject); Quick Mode Selection Guide
- **academic-pipeline v2.6**: 적응형 체크포인트 시스템(FULL/SLIM/MANDATORY); 무결성 점검의 Phase E Claim Verification; 중간 진입 provenance용 Material Passport; 교차 스킬 mode advisor(14 시나리오); 팀 협업 프로토콜; 향상된 핸드오프 스키마(9 스키마); 무결성 실패 복구 예시

### v2.4 / v1.3 (2026-03-08)
- **academic-pipeline v2.4**: 새 Stage 6 PROCESS SUMMARY — 구조화된 논문 작성 과정 기록 자동 생성(MD → LaTeX → PDF, 이중언어); 필수 마지막 챕터: 6차원을 1–100으로 채점하는 **Collaboration Quality Evaluation**(Direction Setting, Intellectual Contribution, Quality Gatekeeping, Iteration Discipline, Delegation Efficiency, Meta-Learning), 정직한 피드백, 개선 권고; 파이프라인이 9에서 10단계로 확장

### v2.3 / v1.3 (2026-03-08)
- **academic-pipeline v2.3**: Stage 5 FINALIZE가 이제 형식 스타일(APA 7.0 / Chicago / IEEE)을 물음; PDF는 `tectonic`을 통해 LaTeX에서 컴파일되어야 함(HTML-to-PDF 금지); APA 7.0은 이중언어 CJK 지원을 위한 XeCJK와 함께 `apa7` document class(`man` 모드) 사용; 폰트 스택: Times New Roman + Source Han Serif TC VF + Courier New

### v2.2 / v1.3 (2025-03-05)
- **Cross-Agent Quality Alignment**: 모든 에이전트 전반의 통일된 정의(peer-reviewed, currency rule, CRITICAL severity, source tier)
- **deep-research v2.2**: synthesis 안티패턴, Socratic auto-end 조건, DOI+WebSearch 검증, 향상된 윤리 무결성 점검, mode transition 매트릭스
- **academic-paper v2.2**: 4단계 논증 채점, 표절 스크리닝, 새 실패 경로 2개(F11 Desk-Reject Recovery, F12 Conference-to-Journal), Plan→Full 모드 변환
- **academic-paper-reviewer v1.3**: DA 대 R3 역할 경계, CRITICAL 발견 기준, 합의 분류(4/3/SPLIT/DA-CRITICAL), 신뢰도 점수 가중, Asian & Regional Journals 참조
- **academic-pipeline v2.2**: 체크포인트 확인 의미론, mode switching 매트릭스, 실패 폴백 매트릭스, 상태 소유권 프로토콜, 자료 버전 관리

### v2.0.1 (2026-03)
- **4개 SKILL.md 간소화**(-371행, -16.5%): 교차 스킬 중복 제거, 인라인 템플릿 → 파일 참조, 중복 라우팅 표, 중복 모드 선택 절
- academic-paper와 academic-pipeline 간 수정 루프 상한 모순 수정

### v2.0 (2026-02)
- **academic-pipeline v2.0**: 5→9단계, 필수 무결성 검증, 2단계 심사, 소크라테스식 수정 코칭, 재현성 보장
- **academic-paper-reviewer v1.1**: +Devil's Advocate Reviewer(7번째 에이전트), +re-review 모드(검증), +사후 심사 소크라테스식 코칭
- 새 에이전트: `integrity_verification_agent` — 감사 추적을 갖는 100% 참고문헌/데이터 검증
- 새 에이전트: `devils_advocate_reviewer_agent` — 8차원 논제 도전자
- 출력 순서: MD → 가능한 경우 Pandoc 경유 DOCX(아니면 지침) → LaTeX 질문 → 확인 → PDF

### v1.0 (2026-02)
- 최초 릴리스
- deep-research v2.0 (10 에이전트, socratic 포함 6 모드)
- academic-paper v2.0 (10 에이전트, plan 포함 8 모드)
- academic-paper-reviewer v1.0 (6 에이전트, guided 포함 4 모드)
- academic-pipeline v1.0 (오케스트레이터)
