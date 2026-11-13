# ai-skills

Claude Code용 스킬을 모아 관리하는 저장소입니다. 저장소를 클론해 Claude Code를 실행하면 `.claude/skills/` 아래의 스킬이 자동으로 로드됩니다.

## 포함된 스킬

| 스킬 | 출처 | 라이선스 |
|---|---|---|
| `frontend-design` | [anthropics/skills](https://github.com/anthropics/skills) | Apache License 2.0 |
| Superpowers 스킬 15개 (아래 표) | [obra/superpowers](https://github.com/obra/superpowers) v7.0.2 | MIT |

### frontend-design

새 UI를 만들거나 기존 UI를 다시 디자인할 때, 템플릿 같은 결과 대신 주제에 맞는 뚜렷한 디자인을 만들도록 Claude를 안내합니다. 방향 잡기, 서체·색·레이아웃·모션 선택, 흔한 AI 디자인 패턴 피하기, 계획 → 구현 → 자체 점검 순서, UI 문구 작성 원칙을 다룹니다.

### Superpowers

브레인스토밍 → 계획 → TDD 구현 → 리뷰 → 마무리로 이어지는 개발 흐름을 스킬로 묶은 모음입니다.

| 스킬 | 하는 일 |
|---|---|
| `using-superpowers` | 다른 스킬을 언제 쓰는지 알려 주는 입문 스킬 |
| `brainstorming` | 구현 전에 질문으로 요구사항과 설계를 다듬음 |
| `writing-plans` | 설계를 작은 작업 단위의 구현 계획으로 작성 |
| `executing-plans` | 계획을 단계별로 실행하고 체크포인트에서 점검 |
| `subagent-driven-development` | 작업마다 서브에이전트에 맡기고 리뷰하며 진행 |
| `dispatching-parallel-agents` | 서로 독립적인 작업을 병렬 에이전트로 처리 |
| `test-driven-development` | 실패하는 테스트 → 구현 → 리팩터링 순서 강제 |
| `systematic-debugging` | 원인 추적 중심의 4단계 디버깅 |
| `verification-before-completion` | 완료라고 말하기 전에 실제로 확인 |
| `requesting-code-review` | 코드 리뷰 요청 |
| `receiving-code-review` | 받은 리뷰를 검증하며 반영 |
| `using-git-worktrees` | 격리된 git worktree에서 작업 |
| `finishing-a-development-branch` | 머지·PR·정리 중 선택해 브랜치 마무리 |
| `writing-skills` | 새 스킬을 만들고 테스트 |
| `diagnosing-superpowers` | Superpowers가 기대대로 동작하지 않을 때 세션을 진단 |

#### 원본과 다른 점

- 원본은 Claude Code 플러그인이라 스킬 이름에 `superpowers:` 접두어가 붙습니다(예: `superpowers:brainstorming`). 여기서는 프로젝트 스킬로 넣었으므로 본문의 `superpowers:` 접두어를 지웠습니다.
- 원본 플러그인은 세션이 시작될 때 `using-superpowers` 내용을 자동으로 넣어 주는 SessionStart 훅이 있습니다. 이 저장소에는 훅을 넣지 않았으므로, 스킬은 설명(description)에 맞는 요청이 들어올 때 불립니다. 원본과 똑같이 쓰려면 아래의 플러그인 설치 방법을 쓰세요.

## 사용법

### 이 저장소에서 사용

```
로그인 기능을 만들고 싶어. brainstorming 스킬부터 시작해줘.
```

`/brainstorming`, `/frontend-design`처럼 직접 호출할 수도 있습니다.

### 다른 프로젝트나 모든 프로젝트에서 사용

필요한 스킬 폴더를 통째로 복사합니다. 폴더 안의 `LICENSE.txt`도 함께 복사하세요. Superpowers 스킬은 서로를 참조하므로 한꺼번에 복사하는 것을 권합니다.

```bash
# 특정 프로젝트
cp -r .claude/skills/* /path/to/project/.claude/skills/

# 내 모든 프로젝트
cp -r .claude/skills/* ~/.claude/skills/
```

### Superpowers를 원본 플러그인으로 설치

세션 시작 훅까지 포함해 원본 그대로 쓰려면 Claude Code에서 다음을 실행합니다. 이 경우 위의 복사본과 중복되므로 둘 중 하나만 쓰세요.

```
/plugin marketplace add obra/superpowers-marketplace
/plugin install superpowers@superpowers-marketplace
```

### Claude.ai

스킬 폴더를 zip으로 묶어 [Using skills in Claude](https://support.claude.com/en/articles/12512180-using-skills-in-claude)의 안내대로 업로드합니다.

## 라이선스

각 스킬 폴더의 `LICENSE.txt`를 따릅니다. 스킬을 복사하거나 배포할 때 이 파일을 함께 유지하세요.

- `frontend-design`: Apache License 2.0
- Superpowers 스킬: MIT License, Copyright (c) 2025 Jesse Vincent
