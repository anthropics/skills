# frontend-design

Claude Code용 `frontend-design` 스킬 하나만 관리하는 저장소입니다.

## 용도

새 UI를 만들거나 기존 UI를 다시 디자인할 때, 어디서나 볼 수 있는 템플릿 같은 결과 대신 주제에 맞는 뚜렷한 디자인을 만들도록 Claude를 안내합니다. 스킬이 다루는 내용은 다음과 같습니다.

- 주제와 대상 사용자에 맞춘 방향 잡기
- 서체, 색, 레이아웃, 모션을 의도적으로 고르기
- 자주 보이는 AI 생성 디자인 패턴 피하기
- 디자인 계획을 세우고 브리프와 대조한 뒤 구현하고 스스로 점검하는 순서
- 카피와 UI 문구 작성 원칙

## 구성

```
.claude/skills/frontend-design/
├── SKILL.md      # 스킬 지침과 메타데이터
└── LICENSE.txt   # Apache License 2.0
```

`SKILL.md`는 다른 파일이나 외부 의존성 없이 단독으로 동작합니다.

## 사용법

### 이 저장소에서 사용

저장소를 클론해 Claude Code를 실행하면 `.claude/skills/` 아래의 스킬이 자동으로 로드됩니다. UI 제작이나 디자인 작업을 요청하면 Claude가 필요할 때 스킬을 적용합니다. `/frontend-design`으로 직접 호출할 수도 있습니다.

```
랜딩 페이지를 만들어줘. frontend-design 스킬을 사용해줘.
```

### 다른 프로젝트나 모든 프로젝트에서 사용

폴더를 통째로 복사합니다. `LICENSE.txt`도 함께 복사하세요.

```bash
# 특정 프로젝트
cp -r .claude/skills/frontend-design /path/to/project/.claude/skills/

# 내 모든 프로젝트
cp -r .claude/skills/frontend-design ~/.claude/skills/
```

### Claude.ai

`frontend-design` 폴더를 zip으로 묶어 [Using skills in Claude](https://support.claude.com/en/articles/12512180-using-skills-in-claude)의 안내대로 업로드합니다.

## 라이선스

Apache License 2.0이며 전문은 [`LICENSE.txt`](./.claude/skills/frontend-design/LICENSE.txt)에 있습니다. 스킬을 복사하거나 배포할 때 이 파일을 함께 유지하세요. 이 스킬은 [anthropics/skills](https://github.com/anthropics/skills)의 `frontend-design` 스킬에서 가져왔습니다.
