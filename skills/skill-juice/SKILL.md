---
name: skill-juice
description: Use when you want to learn from a skill's design — understand why it works, extract reusable patterns, and apply insights to your own projects. Trigger on "analyze this skill", "learn from this", "what can I learn", "how does this skill work", "juicify", "스킬 분석", "이 스킬에서 배울 점".
disable-model-invocation: true
argument-hint: "<skill-path|skill-name|URL> [quick|deep]"
---

# Skill Juice — 스킬을 갈아서 주스로 만들어 마시다

스킬이나 플러그인을 입력받아, 그 안에 녹아있는 시스템적 사고와 논리 흐름, 엔지니어링 테크닉 및 인사이트를 추출한다.

**Language**: 항상 사용자의 언어로 응답하고 juice note를 작성한다.

## 왜 Skill Juice인가?

시중의 스킬을 "설치 → 사용"으로 끝내면 기능만 빌려 쓰는 것이다. AI Native한 역량을 키우려면, 잘 만들어진 스킬을 **갈아서 주스로 만들어** — 왜 이렇게 설계했는지, 어떤 사고 패턴이 깔려있는지, 어떤 엔지니어링 판단을 내렸는지 — 한 방울도 남기지 않고 흡수해야 한다.

거인의 어깨에 올라타되, 거인이 어떻게 만들어졌는지를 이해하는 것이 목적이다.

## 실행 플로우

### Step 0: 인자 파싱

`$ARGUMENTS`에서 두 가지를 추출한다:
- **대상**: 스킬 경로, 스킬 이름, 또는 URL
- **깊이**: `quick` 또는 `deep` (기본값: `deep`)

예시:
```
/skill-juice skill-creator quick
/skill-juice ~/.claude/skills/work-juice deep
/skill-juice https://github.com/someone/skill-repo
/skill-juice postmortem-writing
```

### Step 1: 대상 스킬 접근

대상 유형에 따라 스킬 파일을 읽는다:

- **로컬 경로**: Read로 SKILL.md + 디렉토리 내 지원 파일 전체 확인
- **스킬 이름**: 아래 경로를 순서대로 탐색
  1. `~/.claude/skills/{name}/SKILL.md`
  2. `.claude/skills/{name}/SKILL.md`
  3. `~/.claude/plugins/cache/*/skills/{name}/SKILL.md` (플러그인)
  4. `~/.claude/plugins/marketplaces/*/skills/{name}/SKILL.md` (마켓플레이스)
- **URL**: WebFetch로 가져오기. GitHub URL이면 raw content 경로로 변환.

**대상이 모호할 때**: 스킬 이름이 일반 단어와 겹치거나(예: "vague", "loop"), 여러 경로에서 동명 스킬이 발견될 경우, 곧바로 하나를 선택하지 않는다. 발견된 후보를 옵션으로 제시한다:

```
다음 스킬이 발견되었습니다:
1. ~/.claude/skills/vague/SKILL.md — (설명)
2. .claude/plugins/.../clarify/skills/vague/SKILL.md — (설명)

어떤 스킬을 분석할까요?
```

후보가 1개뿐이면 확인 없이 진행한다. 스킬을 찾지 못하면 사용자에게 알리고 경로 확인을 요청한다.

### Step 2: 스킬 구조 파악

SKILL.md를 읽고 전체 구조를 파악한다:
- frontmatter 필드 (name, description, tools, model, context 등)
- 본문 섹션 구조
- 지원 파일 목록 (scripts/, references/, assets/)
- 전체 줄 수 및 규모

deep 모드에서는 지원 파일도 모두 읽는다.

### Step 3: 6렌즈 분석

#### quick 모드 (3개 렌즈)

| 렌즈 | 뽑아내는 것 |
|------|------------|
| **설계 철학** | 이 스킬이 전제하는 세계관, 핵심 원칙, 해결하려는 근본 문제 |
| **핵심 테크닉** | 재사용 가능한 구체적 엔지니어링 기법 2~3개 |
| **내 작업에 적용** | 현재 프로젝트/작업에 즉시 적용 가능한 인사이트 |

#### deep 모드 (6개 렌즈)

| 렌즈 | 뽑아내는 것 |
|------|------------|
| **설계 철학** | 이 스킬이 전제하는 세계관, 핵심 원칙, 해결하려는 근본 문제 |
| **시스템적 사고** | 구조적 패턴, 피드백 루프, 분리 원칙, 계층 설계 |
| **엔지니어링 테크닉** | 재사용 가능한 구체적 기법. DRY, 비동기 활용, 데이터 흐름 등 |
| **프롬프트 설계** | LLM에게 지시하는 방식의 패턴. Why 설명, Theory of Mind, 출력 형식 제어 등 |
| **사용자 경험** | 사용자와의 상호작용 설계. 입력 유연성, 피드백 루프, 에러 처리 |
| **내 작업에 적용** | 현재 프로젝트/작업에 적용 가능한 구체적 인사이트. 이미 가진 스킬과의 비교 |

### Step 4: Juice Note 작성 및 저장

juice note를 `docs/juice-notes/YYYY-MM-DD-{스킬이름}.md`에 저장한다.
해당 폴더가 없으면 생성한다.

### Step 5: 세션 출력

세션에는 핵심 요약만 출력한다:
- 스킬 한 줄 요약
- 가장 인상적인 테크닉 1~2개
- 내 작업에 즉시 적용 가능한 인사이트 1개
- 저장된 juice note 파일 경로

전문은 MD 파일을 참조하도록 안내한다.

## Juice Note 구조

### quick 모드

```markdown
# {스킬이름} — Juice Note (Quick)

## 스킬 개요
- 이름: {name}
- 목적: (한 줄)
- 규모: {줄 수}줄, 지원 파일 {N}개

---

## 설계 철학
(이 스킬의 핵심 전제와 원칙)

## 핵심 테크닉
(재사용 가능한 기법 2~3개, 각각 한 문단)

## 내 작업에 적용
(현재 맥락에서 즉시 적용 가능한 인사이트)
```

### deep 모드

```markdown
# {스킬이름} — Juice Note (Deep)

## 스킬 개요
- 이름: {name}
- 목적: (한 줄)
- 규모: {줄 수}줄, 지원 파일 {N}개
- frontmatter: (주요 필드 나열)
- 구조: (섹션 목차)

---

## 1. 설계 철학
(세계관, 핵심 원칙, 근본 문제)

## 2. 시스템적 사고
(구조적 패턴, 피드백 루프, 분리 원칙)

## 3. 엔지니어링 테크닉
(재사용 가능한 기법, 각각 제목 + 설명 + 원문 인용)

## 4. 프롬프트 설계
(LLM 지시 패턴, 출력 제어, Theory of Mind 활용)

## 5. 사용자 경험
(입력 유연성, 피드백 루프, 에러 처리)

## 6. 내 작업에 적용
(구체적 적용 인사이트, 기존 스킬과의 비교)
```

## Juicing 원칙

- **기능이 아닌 사고를 뽑아낸다**: "이 스킬은 리포트를 생성한다"가 아니라 "왜 이 순서로 생성하는가"를 파악한다.
- **원문을 인용한다**: 인사이트의 근거가 되는 스킬 원문을 `>` 인용으로 포함한다.
- **일반화한다**: 이 스킬에만 해당하는 것이 아니라, 다른 스킬/시스템에도 적용 가능한 패턴으로 정리한다.
- **"내 작업에 적용"은 구체적으로**: "참고할 만하다" 수준이 아니라, "work-juice 스킬의 Step 2에 이 패턴을 적용하면 ~" 수준으로 구체적으로 쓴다.
