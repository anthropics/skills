# 5W1H Examples

빠진 항목 수에 따라 동작이 달라지는 것이 핵심. 분석 과정은 사용자에게 보여주지 않는다.
header에는 5W1H 태그를 사용하여 프레임워크를 자연스럽게 노출한다.

---

## 1. 빠진 항목 3개 — AskUserQuestion 발동

**User message**: "회원가입 페이지 만들어줘"

**내부 분석** (사용자에게 비공개):
- Who: 추론 가능 (신규 사용자)
- What: 있음 (회원가입 페이지)
- When: 추론 가능 (비로그인 시)
- Where: **없음** — 어떤 경로?
- Why: **없음** — 이메일? 소셜? 둘 다?
- How: **없음** — 어떤 정보를 받을지

→ 3개 없음 → AskUserQuestion 발동:
```json
[
  {
    "question": "어떤 방식으로 가입하나요?",
    "header": "Why(왜)",
    "multiSelect": true,
    "options": [
      {"label": "이메일+비밀번호", "description": "이메일과 비밀번호로 직접 가입 (추천)"},
      {"label": "카카오 로그인", "description": "카카오 계정으로 간편 가입"},
      {"label": "네이버 로그인", "description": "네이버 계정으로 간편 가입"},
      {"label": "구글 로그인", "description": "구글 계정으로 간편 가입"}
    ]
  },
  {
    "question": "가입 시 어떤 정보를 받나요?",
    "header": "How(어떻게)",
    "multiSelect": true,
    "options": [
      {"label": "이름 + 이메일", "description": "기본 정보만 (추천)"},
      {"label": "전화번호", "description": "연락처 추가 수집"},
      {"label": "주소", "description": "배송지 미리 입력"},
      {"label": "프로필 사진", "description": "사진 업로드 포함"}
    ]
  },
  {
    "question": "가입 완료 후 어디로 이동하나요?",
    "header": "Where(어디)",
    "multiSelect": false,
    "options": [
      {"label": "메인 화면", "description": "바로 서비스 이용 시작 (추천)"},
      {"label": "환영 페이지", "description": "가입 축하 + 서비스 안내"},
      {"label": "프로필 설정", "description": "추가 정보 입력 화면"}
    ]
  }
]
```

---

## 2. 빠진 항목 3개 (버그) — 텍스트 질문 발동

**User message**: "버튼 누르면 아무것도 안 돼요"

**내부 분석**:
- What: 부분 (어떤 버튼인지 불명)
- When: **없음** (항상? 가끔?)
- Where: **없음** (어떤 화면?)
- How: **없음** (기대 동작이 뭔지)

→ 3개 없음이지만 버그 상황은 자유 서술이 필요 → 텍스트 질문:
> 문제 확인을 위해:
> 1. **Where(어디)**: 어떤 화면의 어떤 버튼인가요? (예: "발행" 버튼, "저장" 버튼 등)
> 2. **How(어떻게)**: 버튼을 눌렀을 때 원래 어떻게 되어야 하나요?
> 3. **When(언제)**: 항상 안 되나요, 아니면 가끔만 그런가요?

---

## 3. 빠진 항목 2개 — AskUserQuestion 발동

**User message**: "메인 화면 좀 예쁘게 바꿔줘"

**내부 분석**:
- What: 부분 (디자인 개선 — 범위 불명확)
- Where: 있음 (메인 화면)
- Why: 있음 (마음에 안 듦)
- How: **없음** (어떤 느낌?)
- What 세부: **없음** (어떤 부분?)

→ 2개 없음 → AskUserQuestion 발동:
```json
[
  {
    "question": "어떤 느낌을 원하나요?",
    "header": "How(어떻게)",
    "multiSelect": false,
    "options": [
      {"label": "깔끔/미니멀", "description": "여백 많고 정돈된 느낌"},
      {"label": "컬러풀/활기찬", "description": "밝고 다채로운 색상"},
      {"label": "전문적/신뢰감", "description": "비즈니스 느낌, 차분한 톤"}
    ]
  },
  {
    "question": "어떤 부분이 특히 아쉬운가요?",
    "header": "What(무엇)",
    "multiSelect": true,
    "options": [
      {"label": "색상/톤", "description": "전체적인 색감이 아쉬움"},
      {"label": "레이아웃", "description": "요소 배치, 구조가 아쉬움"},
      {"label": "글꼴/텍스트", "description": "글자 크기, 서체가 아쉬움"},
      {"label": "전체 분위기", "description": "전반적으로 바꾸고 싶음"}
    ]
  }
]
```

---

## 4. 빠진 항목 1개 — 인라인 질문 (5W1H 미발동)

**User message**: "api.ts 파일이 너무 커졌어. 정리 좀 해줘"

**내부 분석**:
- What: 있음, Where: 있음, Why: 있음
- How: **없음** (분리 기준)

→ 1개 없음 → 인라인으로 간단히 질문:
> 도메인별(auth, content, publish 등)로 나눌까요, 다른 기준이 있나요?

---

## 5. 빠진 항목 0개 — 바로 작업 시작 (5W1H 미발동)

**User message**: "블로그 글 목록 화면에서 각 글마다 조회수를 보여주고 싶어요. 오른쪽에 작은 숫자로 표시해주면 돼요. 지금은 조회수가 안 보여서 어떤 글이 인기 있는지 모르겠어요."

**내부 분석**: 6가지 모두 충분

→ 0개 없음 → 질문 없이 바로 작업 시작.

---

## 6. 빠진 항목 0개 — 단순 요청 (5W1H 미발동)

**User message**: "버튼 색 빨간색으로 바꿔줘"

**내부 분석**: What(색 변경), How(빨간색), Where(버튼) 모두 있음

→ 0개 없음 → 바로 작업.
