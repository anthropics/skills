# 5W1H Examples

초보자와 개발자 양쪽 시나리오를 포함한다. 사용자의 언어 수준에 맞춰 소통하는 것이 핵심.

---

## 1. Beginner — 기능 요청

**User message**: "회원가입 페이지 만들어줘"

**Analysis**:
| 관점 | 상태 | 파악된 내용 |
|------|------|------------|
| Who | 추론 가능 | 서비스에 가입하려는 신규 사용자 |
| What | 있음 | 회원가입 페이지 |
| When | 추론 가능 | 비로그인 상태에서 접근 |
| Where | 없음 | 어떤 경로? 기존 로그인 페이지 옆? |
| Why | 없음 | 이메일 가입? 소셜 로그인? 둘 다? |
| How | 없음 | 어떤 정보를 받을지 (이름, 이메일, 비밀번호 등) |

**Follow-up** (AskUserQuestion):
```json
[
  {
    "question": "어떤 방식으로 가입하나요?",
    "header": "가입 방식",
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
    "header": "입력 정보",
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
    "header": "가입 후",
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

## 2. Beginner — 오류/문제 신고

**User message**: "버튼 누르면 아무것도 안 돼요"

**Analysis**:
| 관점 | 상태 | 파악된 내용 |
|------|------|------------|
| Who | 추론 가능 | 서비스 사용자 |
| What | 부분 | 버튼이 동작하지 않음 — 어떤 버튼인지 불명 |
| When | 없음 | 항상? 특정 상황에서만? |
| Where | 없음 | 어떤 화면의 어떤 버튼? |
| Why | 해당 없음 | 버그이므로 이유 불필요 |
| How | 없음 | 기대 동작이 무엇인지 |

**Follow-up** (텍스트 질문 — 버그는 자유 서술이 필요하므로 AskUserQuestion보다 텍스트가 적합):
> 문제 확인을 위해:
> 1. **어떤 화면**의 **어떤 버튼**인가요? (예: "발행" 버튼, "저장" 버튼 등)
> 2. 버튼을 눌렀을 때 **원래 어떻게 되어야** 하나요?
> 3. **항상** 안 되나요, 아니면 **가끔**만 그런가요?

---

## 3. Beginner — 디자인/변경 요청

**User message**: "메인 화면 좀 예쁘게 바꿔줘"

**Analysis**:
| 관점 | 상태 | 파악된 내용 |
|------|------|------------|
| Who | 추론 가능 | 방문자/사용자 |
| What | 부분 | 메인 화면 디자인 개선 — 범위 불명확 |
| When | 해당 없음 | 즉시 |
| Where | 있음 | 메인 화면 |
| Why | 있음 | 현재 디자인이 마음에 안 듦 |
| How | 없음 | 어떤 느낌/스타일을 원하는지 |

**Follow-up** (AskUserQuestion):
```json
[
  {
    "question": "어떤 느낌을 원하나요?",
    "header": "분위기",
    "multiSelect": false,
    "options": [
      {"label": "깔끔/미니멀", "description": "여백 많고 정돈된 느낌"},
      {"label": "컬러풀/활기찬", "description": "밝고 다채로운 색상"},
      {"label": "전문적/신뢰감", "description": "비즈니스 느낌, 차분한 톤"}
    ]
  },
  {
    "question": "어떤 부분이 특히 아쉬운가요?",
    "header": "개선 대상",
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

## 4. Developer — 리팩토링

**User message**: "api.ts 파일이 너무 커졌어. 정리 좀 해줘"

**Analysis**:
| 관점 | 상태 | 파악된 내용 |
|------|------|------------|
| Who | 해당 없음 | 코드 품질 작업 |
| What | 있음 | api.ts 파일 분리/정리 |
| When | 해당 없음 | 즉시 |
| Where | 있음 | `frontend/src/lib/api.ts` |
| Why | 있음 | 파일이 너무 큼 (유지보수 어려움) |
| How | 없음 | 분리 기준이 필요 |

**Follow-up** (AskUserQuestion):
```json
[
  {
    "question": "어떤 기준으로 파일을 나눌까요?",
    "header": "분리 기준",
    "multiSelect": false,
    "options": [
      {"label": "도메인별", "description": "auth, content, publish, agent 등 기능 영역별로 분리 (추천)"},
      {"label": "역할별", "description": "queries, mutations, subscriptions 등 데이터 흐름별로 분리"},
      {"label": "레이어별", "description": "API 호출, 데이터 변환, 타입 정의를 각각 분리"}
    ]
  }
]
```

---

## 5. Complete request — 추가 질문 불필요

**User message**: "블로그 글 목록 화면에서 각 글마다 조회수를 보여주고 싶어요. 오른쪽에 작은 숫자로 표시해주면 돼요. 지금은 조회수가 안 보여서 어떤 글이 인기 있는지 모르겠어요."

**Analysis**:
| 관점 | 상태 | 파악된 내용 |
|------|------|------------|
| Who | 추론 가능 | 블로그 관리자 (대시보드 사용자) |
| What | 있음 | 글 목록에 조회수 표시 |
| When | 추론 가능 | 글 목록 화면 진입 시 |
| Where | 있음 | 블로그 글 목록 화면, 각 글 오른쪽 |
| Why | 있음 | 인기 글 파악을 위해 |
| How | 있음 | 오른쪽에 작은 숫자로 |

**Action**: 모든 요소 충분 → 바로 작업 시작. Brief만 간단히 출력.
