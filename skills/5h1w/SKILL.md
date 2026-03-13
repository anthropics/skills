---
name: 5h1w
description: >
  Analyze user requests through the 5W1H framework (Who, What, When, Where, Why, How) to ensure
  complete context before implementation. Use this skill when: (1) a user starts a new task, feature
  request, or bug report, (2) a user explicitly invokes /5h1w, (3) a request feels ambiguous or
  underspecified. Automatically parse the initial message, identify which 5W1H elements are present
  vs missing, and ask targeted follow-up questions only for gaps — never re-ask what's already clear.
---

# 5W1H Context Analyzer

사용자의 요청을 5W1H 6가지 관점으로 분석하여, 빠진 정보를 파악하고 보충 질문한 뒤 작업을 시작한다.

## Language adaptation

사용자의 기술 수준에 맞춰 소통한다:
- 사용자가 일상 언어를 쓰면 → 기술 용어 없이 쉬운 말로 질문
- 사용자가 개발 용어를 쓰면 → 같은 수준으로 질문
- 판단이 안 되면 → 쉬운 쪽으로 기본 설정

## Workflow

### 1. 사용자 메시지 분석

메시지에서 6가지 정보를 찾는다:

| 관점 | 질문 | 찾을 정보 |
|------|------|----------|
| **Who** | 누가 쓰는가? | 이 기능을 쓸 사람, 영향받는 사람 |
| **What** | 무엇을 만들/고칠 것인가? | 원하는 결과물, 해결할 문제 |
| **When** | 언제 작동하는가? | 작동 시점, 조건, 마감기한 |
| **Where** | 어디에 적용하는가? | 화면, 페이지, 위치, 범위 |
| **Why** | 왜 필요한가? | 이유, 배경, 목적 |
| **How** | 어떤 방식으로? | 원하는 동작 방식, 디자인, 느낌 |

### 2. 완성도 평가

각 관점을 평가한다:
- **있음**: 메시지에 명확히 드러남
- **추론 가능**: 프로젝트 코드나 맥락에서 파악 가능
- **없음**: 알 수 없어서 질문이 필요

### 3. 빠진 것만 질문 (AskUserQuestion 사용)

6가지 모두 파악되면 바로 작업 시작 — 불필요한 질문 금지.

빠진 정보가 있으면 `AskUserQuestion` 도구로 선택형 UI를 제공한다:

**AskUserQuestion 규칙:**
- 빠진 항목별로 2-4개 선택지를 만들어 한 번에 질문한다 (최대 4개 질문)
- 추천 옵션은 첫 번째에 배치하고 label 끝에 `(추천)` 표기
- 여러 개 고를 수 있는 항목은 `multiSelect: true` 사용 (예: 필요한 페이지, 기능 목록)
- 단일 선택 항목은 `multiSelect: false` (예: 분위기, 목적)
- header는 12자 이내 한국어 라벨 (예: "목적", "분위기", "페이지")
- label은 짧고 명확하게 (1-5단어), description에 부연 설명
- 사용자는 항상 "Other"로 직접 입력 가능하므로 모든 경우를 커버할 필요 없음
- 구체적 비교가 필요하면 `preview` 필드로 ASCII 목업이나 코드 예시를 보여준다

**텍스트 질문으로 전환하는 경우:**
- 빠진 항목이 1개뿐이고 선택지로 나누기 어려울 때
- 자유 서술이 필요한 항목일 때 (예: 버그 상황 설명)

### 4. 정리 후 작업 시작

모든 정보를 모은 후, 간단한 정리를 보여주고 작업을 시작한다:

```
## 5W1H Brief
- **누가(Who)**: ...
- **무엇을(What)**: ...
- **언제(When)**: ...
- **어디서(Where)**: ...
- **왜(Why)**: ...
- **어떻게(How)**: ...
```

이 정리가 작업의 기준이 된다. 작업 중 판단이 필요하면 여기로 돌아온다.

## Priority rules

- **What**(무엇)과 **Why**(왜)는 항상 필수 — 절대 생략하지 않는다
- **Where**(어디)는 프로젝트 구조에서 대부분 파악 가능
- **How**(어떻게)는 작업하면서 결정해도 된다
- **Who**(누가)와 **When**(언제)은 단순 작업에서는 해당 없을 수 있다
- 오류/버그 상황: **What**(기대 vs 실제 동작), **When**(언제 발생), **Where**(어떤 화면)이 핵심

## Interaction style

- 간결하게. 질문은 한 번에 모아서 한다.
- 가능하면 답을 제안한다: "로그인 화면에 넣을까요, 메인 화면에 넣을까요?"
- 이미 충분하면 정리만 짧게 보여주고 바로 작업한다.
- 사용자가 이미 말한 내용을 반복하지 않는다.

## Examples

See [references/examples.md](references/examples.md) for scenario-specific 5W1H analysis patterns.
