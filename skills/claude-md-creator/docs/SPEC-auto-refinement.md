# claude-md-creator Auto-Refinement SPEC

## 1. 개요

autoresearch의 "자동 반복 실험 → 메트릭 비교 → 개선 유지/폐기" 패턴을 차용하여, claude-md-creator 스킬의 Python 스크립트 로직(claim 추출, 코드베이스 검증 등)을 실제 GitHub 레포들에 대해 대규모로 테스트하고, 실패 모드를 자동 감지/수정하는 완전 자동화 파이프라인.

### 목적

**스킬 로직 개선**에 집중. CLAUDE.md 생성 품질이 아닌, `extract_claims.py`의 precision/recall과 `verify_coherence.py`의 정확도를 다양한 레포에서 테스트하여 패턴 매칭/검증 로직을 정교하게 다듬는 것이 핵심.

### 핵심 아이디어: autoresearch 매핑

| autoresearch | claude-md-creator Auto-Refinement |
|---|---|
| `train.py` (수정 대상) | `scripts/*.py` — extract_claims.py, verify_coherence.py 등 |
| `prepare.py` (고정) | 테스트 하네스 + golden set (고정) |
| `val_bpb` (메트릭) | 실패 모드 점수 (6가지 실패 감지 메트릭) |
| `program.md` (가이드) | 수정 가이드 문서 (실패 모드 + 코드 구조 + 금지 사항) |
| 5분 고정 예산 | N회 고정 반복 |
| git baseline 비교 | golden set 회귀 테스트 |

## 2. 배경

- **문제**: claude-md-creator의 claim 추출/검증 로직이 특정 프로젝트 유형(주로 Node/Next.js)에 편향되어 있을 수 있음. 다른 생태계(Rust, Go, Ruby 등)에서 추출 실패, 과적합, 검증 에러 등이 발생할 가능성이 높음.
- **접근**: 실제 내용의 적합성 검증(Ground Truth)은 평가하기 너무 어려우므로, **실패 모드 감지**에 집중 — 0점/과소 추출/과다 추출/스크립트 에러/과적합 등 명확한 이상 징후만 탐지.
- **영감**: karpathy/autoresearch — 고정 예산 실험 + 단일 메트릭(val_bpb) + keep/discard 반복으로 자율적 개선.

## 3. 요구사항

### 기능적 요구사항

#### FR1: 테스트 레포 자동 수집
- GitHub Search API로 `filename:CLAUDE.md` 검색
- 필터링 기준: 스타 수, 언어 분포, 레포 크기
- 20-30개 레포 풀 구성 (다양한 생태계 커버)
- shallow clone (depth=1)으로 디스크 최소화
- 레포 목록을 JSON으로 캐싱하여 재사용

#### FR2: 실패 모드 자동 감지 (6가지)

| # | 실패 모드 | 감지 조건 | 심각도 |
|---|-----------|----------|--------|
| 1 | **추출 실패** | `len(claims) == 0` | CRITICAL |
| 2 | **과소 추출** | `claim_count / non_empty_lines < threshold` | HIGH |
| 3 | **과다 추출 (과적합)** | `(vague + generic) / total > 0.5` | HIGH |
| 4 | **스크립트 런타임 에러** | Python exception / non-zero exit code | CRITICAL |
| 5 | **Coherence 0점** | `coherence_score == 0` (모든 claim stale) | HIGH |
| 6 | **Coherence 100점 과신** | `coherence_score == 100` AND `unverifiable > 50%` | MEDIUM |

#### FR3: 자동 수정 루프
- Claude가 `scripts/*.py`만 수정 (에이전트 지시문, SKILL.md 등은 고정)
- 실패 리포트를 분석하여 패턴/정규식/검증 로직 수정
- 수정 후 golden set 회귀 테스트 통과 확인
- 통과 시 keep, 실패 시 git revert (discard)

#### FR4: 회귀 방지 (Golden Set)
- 5-10개 레포를 golden set으로 지정
- 매 반복마다 golden set 전체 통과 필수
- 새 레포에서 실패를 고치고 golden set도 통과하면 → keep + 해당 레포를 golden set에 추가 검토
- golden set이 점진적으로 확장되어 기준선이 올라감

#### FR5: 결과 출력
- 반복별 JSON 로그: `iterations/<N>/result.json`
- 최종 HTML 리포트: 반복 진행 경과 + 개선 사항 시각화
- 터미널 실시간 요약 (진행률, 현재 점수, keep/discard 상태)

#### FR6: Claude Code 스킬로 구현
- `/auto-refine` 또는 유사한 스킬 커맨드로 실행
- Claude Code 세션에서 인터랙티브하게 동작
- 기존 claude-md-creator 스킬 디렉토리 내에 서브 모듈로 구성

### 비기능적 요구사항

- **NFR1**: 한 반복(iteration)당 실행 시간 < 5분 (스크립트 실행만, clone 제외)
- **NFR2**: 로컬 디스크 사용량 < 2GB (shallow clone + 완료 후 cleanup)
- **NFR3**: GitHub API rate limit 준수 (인증된 요청 5000/h)
- **NFR4**: 수정된 스크립트가 기존 인터페이스(입출력 형식)를 유지해야 함

## 4. 기술 설계

### 아키텍처

```
┌─────────────────────────────────────────────────────────┐
│                    Auto-Refinement Loop                   │
│                                                           │
│  ┌──────────┐   ┌──────────┐   ┌──────────┐   ┌───────┐ │
│  │ 1. Collect│──→│ 2. Test  │──→│ 3. Analyze│──→│4. Fix │ │
│  │   Repos   │   │  Scripts │   │ Failures  │   │Scripts│ │
│  └──────────┘   └──────────┘   └──────────┘   └───┬───┘ │
│       ↑                                            │     │
│       │         ┌──────────┐   ┌──────────┐        │     │
│       │         │6. Decide │←──│5. Regress │←───────┘     │
│       └─────────│keep/disc.│   │   Test    │              │
│                 └──────────┘   └──────────┘              │
└─────────────────────────────────────────────────────────┘
```

#### 컴포넌트 구성

```
skills/claude-md-creator/
├── auto-refine/
│   ├── SKILL.md                    # /auto-refine 스킬 정의
│   ├── program.md                  # Claude 수정 가이드 (실패 모드 + 코드 구조 + 금지 사항)
│   ├── harness/
│   │   ├── collect_repos.py        # GitHub API로 CLAUDE.md 있는 레포 수집
│   │   ├── run_test.py             # 단일 레포에 대해 scripts 실행 + 실패 감지
│   │   ├── run_suite.py            # 전체 레포 셋 테스트 + 결과 집계
│   │   └── regression_check.py     # golden set 회귀 테스트
│   ├── config/
│   │   ├── golden_set.json         # golden set 레포 목록 + 기대 결과
│   │   ├── repo_pool.json          # 전체 테스트 레포 풀 (캐싱)
│   │   └── thresholds.json         # 실패 모드 임계값 설정
│   ├── results/
│   │   ├── iterations/             # 반복별 결과 JSON
│   │   └── report.html             # 최종 HTML 리포트
│   └── agents/
│       └── script_modifier.md      # Claude에게 수정 방향을 지시하는 에이전트 정의
```

### 데이터 흐름

#### 1단계: 레포 수집 (`collect_repos.py`)
```
GitHub Search API ("filename:CLAUDE.md")
  → 필터 (stars > 10, 최근 6개월 활동, 다양한 언어)
  → repo_pool.json (owner, name, language, stars, clone_url)
  → 매 반복에서 10개 랜덤 선택 + golden set(5개) = 15개 테스트
```

#### 2단계: 테스트 실행 (`run_test.py`)
```
각 레포에 대해:
  1. shallow clone → /tmp/auto-refine/<repo>/
  2. CLAUDE.md + .claude/rules/ 파일 위치 확인
  3. extract_claims.py 실행 → claims.json
  4. verify_coherence.py 실행 → coherence_report.json
  5. 실패 모드 6가지 체크 → test_result.json
  6. cleanup (clone 삭제)
```

#### 3단계: 실패 분석 (`run_suite.py`)
```
전체 레포 결과 집계:
  - 레포별 실패 모드 발생 여부
  - 생태계별 성공률 (Node: 90%, Python: 70%, Rust: 40% ...)
  - claim type 분포 균형도
  - 전체 점수 = (성공 레포 수 / 전체 레포 수) × 100
```

#### 4단계: 스크립트 수정 (Claude + `program.md`)
```
실패 리포트 + program.md → Claude가 scripts/*.py 수정
  - 실패한 레포의 CLAUDE.md 패턴 분석
  - 누락된 정규식/키워드 추가
  - 과적합 필터 강화
  - 새 생태계 지원 추가
```

#### 5단계: 회귀 테스트 (`regression_check.py`)
```
수정된 scripts로 golden set 전체 재실행
  - 모든 golden set 레포가 이전과 동일하거나 더 나은 결과
  - 어떤 golden set 레포든 악화 → FAIL → git revert
```

#### 6단계: Keep/Discard 결정
```
회귀 테스트 통과:
  - git commit "auto-refine: iteration N - fix {failure_type} for {ecosystem}"
  - 새로 성공한 레포를 golden set 추가 후보에 기록
  - 다음 반복 진행

회귀 테스트 실패:
  - git revert
  - 실패 원인 로그 기록
  - 다음 반복에서 다른 접근 시도
```

### 테스트 레포 선정 기준

#### GitHub Search 쿼리
```
filename:CLAUDE.md path:/
```

#### 필터링 조건
- stars >= 10 (최소 활용 검증)
- 최근 6개월 내 커밋 활동 (활성 프로젝트)
- CLAUDE.md 크기 >= 500 bytes (최소 내용 보장)
- 레포 크기 < 500MB (clone 시간/디스크 절약)

#### 생태계 다양성 보장 (목표 분포)
| 언어/생태계 | 목표 비율 | 최소 레포 수 |
|------------|----------|-------------|
| JavaScript/TypeScript (Node) | 30% | 6개 |
| Python | 25% | 5개 |
| Rust | 15% | 3개 |
| Go | 15% | 3개 |
| 기타 (Ruby, Java, PHP 등) | 15% | 3개 |

## 5. 엣지 케이스

### EC1: CLAUDE.md 구조가 극단적인 경우
- **빈 CLAUDE.md** (파일은 존재하지만 내용 없음): 추출 실패로 감지되지만, 스크립트가 graceful하게 처리해야 함
- **초대형 CLAUDE.md** (1000줄+): 추출 시간이 길어지거나 메모리 문제 가능. 타임아웃 설정 필요
- **비표준 Markdown**: HTML 혼용, 탭 기반 들여쓰기, 비ASCII 문자 등

### EC2: 레포 접근 문제
- **private 레포**: Search API에 나타나지 않으므로 자동 필터링됨
- **clone 실패**: 네트워크 에러, 인증 문제 → skip + 로그 기록
- **CLAUDE.md 경로 변형**: `.claude/CLAUDE.md`, `docs/CLAUDE.md` 등 비표준 경로

### EC3: 수정 루프 관련
- **Claude 수정이 항상 discard되는 교착 상태**: N회 연속 discard 시 경고 + 실패 패턴을 program.md에 추가하여 다른 접근 유도
- **수정이 한 레포만 고치고 다른 레포를 망가뜨리는 반복**: golden set이 방지하지만, golden set 외 레포 간 충돌은 감지 못함
- **스크립트 인터페이스 변경**: 입출력 JSON 스키마가 바뀌면 다운스트림(aggregate, report) 스크립트도 깨짐 → program.md에서 인터페이스 변경 금지 명시

### EC4: GitHub API 제약
- **Rate limit**: 인증 5000/h, 비인증 60/h → 인증 토큰 필수
- **Search 결과 편향**: 인기 레포 위주로 검색됨 → stars 범위를 구간별로 분리 수집
- **일시적 API 오류**: 재시도 로직 (exponential backoff)

## 6. 트레이드오프 기록

### TD1: 실패 모드 감지 vs Ground Truth 평가
- **선택**: 실패 모드 감지 (정답 없이 이상 징후만 탐지)
- **대안**: 수동 라벨링으로 precision/recall 측정
- **배제 이유**: 수동 라벨링 비용이 너무 높고, 실제 내용 적합성을 사람이 판단하기도 주관적
- **향후 개선**: 실패 모드 기반으로 충분히 안정화되면, 소규모 golden claim set으로 precision/recall 측정 추가 검토

### TD2: Python 스크립트만 수정 vs 에이전트 지시문도 수정
- **선택**: Python 스크립트만 수정
- **대안**: agents/*.md도 함께 수정 허용
- **배제 이유**: 에이전트 지시문 변경의 영향을 정량화하기 어려움 (스크립트는 deterministic, 에이전트는 non-deterministic)
- **향후 개선**: 스크립트 안정화 후 에이전트 지시문 A/B 테스트 별도 파이프라인 구축 가능

### TD3: Golden Set 회귀 vs 전체 점수 합산
- **선택**: Golden Set 회귀 테스트 (어떤 golden set 레포도 악화 불가)
- **대안**: 전체 레포 점수 합산이 이전보다 높으면 keep
- **배제 이유**: 전체 합산은 개별 레포 회귀를 허용하여, 특정 생태계가 점점 악화될 위험
- **향후 개선**: golden set 크기가 충분히 커지면 (15개+) 전체 합산 방식으로 전환 검토

### TD4: 완전 자동 vs 반자동 수정
- **선택**: 완전 자동 (Claude가 수정 + 테스트 + keep/discard)
- **대안**: Claude 제안 → 사람 승인 → 적용
- **배제 이유**: 자동화 속도가 핵심 가치. git revert 안전장치가 있으므로 리스크 관리 가능
- **향후 개선**: 큰 구조 변경이 필요할 때만 사람 개입 (코드 줄 수 변경 > threshold 시 pause)

### TD5: 로컬 실행 vs CI/CD
- **선택**: 로컬 머신
- **대안**: GitHub Actions, Docker
- **배제 이유**: 초기 개발/디버깅이 로컬에서 훨씬 빠름. Python 스크립트만 실행하므로 환경 격리 불필요
- **향후 개선**: 안정화 후 GitHub Actions로 이관하여 야간 자동 실행 가능

## 7. 구현 체크리스트

### Phase 0: 기반 구축
- [ ] `auto-refine/` 디렉토리 구조 생성
- [ ] `program.md` 작성 (실패 모드 정의 + 코드 구조 설명 + 금지 사항)
- [ ] `thresholds.json` 초기값 설정 (과소/과다 추출 임계값 등)

### Phase 1: 레포 수집기
- [ ] `collect_repos.py` 구현 (GitHub Search API + 필터링)
- [ ] 생태계별 다양성 보장 로직
- [ ] `repo_pool.json` 캐싱/갱신 메커니즘
- [ ] 초기 golden set 수동 선정 (5개: Node, Python, Rust, Go, 기타 각 1개)

### Phase 2: 테스트 하네스
- [ ] `run_test.py` 구현 (단일 레포 테스트 + 6가지 실패 모드 감지)
- [ ] `run_suite.py` 구현 (전체 레포 셋 테스트 + 결과 집계)
- [ ] `regression_check.py` 구현 (golden set 회귀 테스트)
- [ ] JSON 결과 스키마 정의

### Phase 3: 자동 수정 루프
- [ ] `/auto-refine` 스킬 SKILL.md 작성
- [ ] `script_modifier.md` 에이전트 정의 (수정 전략 + 제약 사항)
- [ ] 반복 루프 구현 (테스트 → 분석 → 수정 → 회귀 → keep/discard)
- [ ] git commit/revert 자동화
- [ ] 종료 조건 구현 (N회 고정 반복)

### Phase 4: 결과 리포팅
- [ ] 반복별 JSON 로그 저장 (`iterations/<N>/result.json`)
- [ ] HTML 리포트 생성 (반복 진행 경과 + 개선 시각화)
- [ ] 터미널 실시간 요약 출력

### Phase 5: 통합 테스트
- [ ] 전체 파이프라인 end-to-end 테스트 (3회 반복)
- [ ] 교착 상태 감지/복구 테스트
- [ ] golden set 확장 프로세스 검증

## 8. 실행 예시

```bash
# Claude Code 세션에서:
/auto-refine --iterations 10 --golden-set config/golden_set.json

# 또는 기본값으로:
/auto-refine
```

### 예상 출력 (터미널)
```
🔄 Auto-Refinement Loop - claude-md-creator
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

📦 Repo pool: 25 repos (6 Node, 5 Python, 3 Rust, 3 Go, 3 Ruby, 5 other)
🏅 Golden set: 5 repos (all passing)

Iteration 1/10
├── Testing 15 repos (10 random + 5 golden)...
├── Failures: 3 repos (2 CRITICAL, 1 HIGH)
│   ├── rust-analyzer: CRITICAL - extract_claims runtime error (TOML parsing)
│   ├── servo: HIGH - coherence 0% (Rust ecosystem unsupported)
│   └── django-ninja: HIGH - under-extraction (4 claims from 120-line CLAUDE.md)
├── Fixing scripts...
│   └── verify_coherence.py: Added Cargo.toml dependency parser
├── Regression test: ✅ PASS (5/5 golden repos OK)
├── Decision: ✅ KEEP
└── Score: 80% → 87% (+7%)

Iteration 2/10
├── Testing 15 repos (10 random + 5 golden)...
...
```
