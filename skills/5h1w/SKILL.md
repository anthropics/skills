---
name: 5h1w
description: >
  Gather missing context from user requests using the 5W1H framework (Who, What, When, Where, Why,
  How) before implementation. Use this skill when: (1) a user explicitly invokes /5h1w, (2) after
  internal 5W1H analysis, 2 or more dimensions are missing — present structured choices via
  AskUserQuestion. Do NOT trigger when only 0-1 dimensions are missing — just ask inline or proceed.
  Designed for non-developer vibe coders but adapts language to any skill level.
---

# 5W1H Context Gatherer

사용자의 요청을 5W1H 6가지 관점으로 내부 분석하여, 빠진 정보가 2개 이상이면 선택형 UI로 수집한다.

## Trigger rules

1. `/5h1w` 명시적 호출 → 항상 발동
2. 자동 발동 조건:
   - 내부적으로 5W1H 분석 수행 (사용자에게 분석 과정을 보여주지 않는다)
   - **빠진 항목 2개 이상** → AskUserQuestion으로 구조화된 질문
   - **빠진 항목 1개** → 인라인으로 간단히 질문
   - **빠진 항목 0개** → 바로 작업 시작

## Language adaptation

사용자의 기술 수준에 맞춰 소통한다:
- 사용자가 일상 언어를 쓰면 → 기술 용어 없이 쉬운 말로 질문
- 사용자가 개발 용어를 쓰면 → 같은 수준으로 질문
- 판단이 안 되면 → 쉬운 쪽으로 기본 설정

## Workflow

### 1. 내부 분석 (사용자에게 보여주지 않음)

메시지에서 6가지 정보를 찾는다:

| 관점 | 질문 | 찾을 정보 |
|------|------|----------|
| **Who** | 누가 쓰는가? | 이 기능을 쓸 사람, 영향받는 사람 |
| **What** | 무엇을 만들/고칠 것인가? | 원하는 결과물, 해결할 문제 |
| **When** | 언제 작동하는가? | 작동 시점, 조건, 마감기한 |
| **Where** | 어디에 적용하는가? | 화면, 페이지, 위치, 범위 |
| **Why** | 왜 필요한가? | 이유, 배경, 목적 |
| **How** | 어떤 방식으로? | 원하는 동작 방식, 디자인, 느낌 |

각 관점을 평가한다:
- **있음**: 메시지에 명확히 드러남
- **추론 가능**: 프로젝트 코드나 맥락에서 파악 가능
- **없음**: 알 수 없어서 질문이 필요

### 2. 빠진 항목 수에 따라 분기

**0개 없음** → 바로 작업 시작.

**1개 없음** → 인라인으로 간단히 질문. 프레임워크나 구조화 불필요.
예: "무슨 색으로 바꿀까요?"

**2개 이상 없음** → `AskUserQuestion`으로 선택형 UI 제공:

**AskUserQuestion 규칙:**
- 빠진 항목별로 2-4개 선택지를 만들어 한 번에 질문한다 (최대 4개 질문)
- **header에 5W1H 태그를 사용한다** — `"Why(왜)"`, `"How(어떻게)"`, `"Where(어디)"` 등. 사용자가 선택 UI를 통해 5W1H 프레임워크를 자연스럽게 체험한다
- 추천 옵션은 첫 번째에 배치하고 label 끝에 `(추천)` 표기
- 여러 개 고를 수 있는 항목은 `multiSelect: true` 사용 (예: 필요한 페이지, 기능 목록)
- 단일 선택 항목은 `multiSelect: false` (예: 분위기, 목적)
- label은 짧고 명확하게 (1-5단어), description에 부연 설명
- 사용자는 항상 "Other"로 직접 입력 가능하므로 모든 경우를 커버할 필요 없음
- 구체적 비교가 필요하면 `preview` 필드로 ASCII 목업이나 코드 예시를 보여준다

**header 매핑 규칙:**
| 빠진 관점 | header 형식 |
|----------|------------|
| Who | `Who(누가)` |
| What | `What(무엇)` |
| When | `When(언제)` |
| Where | `Where(어디)` |
| Why | `Why(왜)` |
| How | `How(어떻게)` |

**텍스트 질문으로 전환하는 경우:**
- 자유 서술이 필요한 항목일 때 (예: 버그 상황 설명)

**What이 극도로 모호한 경우:**
- What이 너무 모호해서 나머지 질문의 선택지를 구성할 수 없으면, What과 Why만 먼저 질문한다

### 3. 작업 시작

선택 완료 후, 바로 작업을 시작한다.
- `/5h1w`로 명시적 호출된 경우에만 5W1H Brief를 출력한다
- 자동 발동된 경우에는 Brief 없이 바로 작업에 들어간다

5W1H Brief 형식 (`/5h1w` 호출 시에만):
```
## 5W1H Brief
- **누가(Who)**: ...
- **무엇을(What)**: ...
- **언제(When)**: ...
- **어디서(Where)**: ...
- **왜(Why)**: ...
- **어떻게(How)**: ...
```

## Priority rules

- **What**(무엇)과 **Why**(왜)는 항상 필수 — 절대 생략하지 않는다
- **Where**(어디)는 프로젝트 구조에서 대부분 파악 가능
- **How**(어떻게)는 작업하면서 결정해도 된다
- **Who**(누가)와 **When**(언제)은 단순 작업에서는 해당 없을 수 있다
- 오류/버그 상황: **What**(기대 vs 실제 동작), **When**(언제 발생), **Where**(어떤 화면)이 핵심

## Examples

See [references/examples.md](references/examples.md) for scenario-specific 5W1H analysis patterns.
