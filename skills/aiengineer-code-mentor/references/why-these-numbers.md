# 매직넘버의 출처와 근거

> ML 코드에서 자주 보이는 "마법의 숫자"들. 왜 이 값인지 설명합니다.

---

## 42의-출처

### 왜 시드가 42인가?

```python
torch.manual_seed(42)
np.random.seed(42)
random.seed(42)
```

**출처**: Douglas Adams의 소설 "은하수를 여행하는 히치하이커를 위한 안내서"
- "삶, 우주, 그리고 모든 것에 대한 궁극적인 질문의 답" = 42
- 프로그래머 문화에서 관례로 정착

**기술적 의미**:
- 시드 값 자체는 아무 숫자나 가능 (0, 1, 123 등)
- 42인 이유는 순전히 관례 (기능적 차이 없음)
- 중요한 건 **고정**이지, 숫자가 아님

---

## ImageNet-정규화값

### 왜 이 숫자들인가?

```python
mean = [0.485, 0.456, 0.406]  # RGB
std = [0.229, 0.224, 0.225]   # RGB
```

**출처**: ImageNet 데이터셋 (120만장 이미지) 전체의 통계값
- R 채널 평균: 0.485, 표준편차: 0.229
- G 채널 평균: 0.456, 표준편차: 0.224
- B 채널 평균: 0.406, 표준편차: 0.225

**계산 과정**:
```python
# 이론적으로 이렇게 계산됨 (실제로 돌리면 며칠 걸림)
all_images = load_all_imagenet()  # 120만장
mean = all_images.mean(dim=[0, 2, 3])  # 채널별 평균
std = all_images.std(dim=[0, 2, 3])    # 채널별 표준편차
```

**언제 이 값을 쓰나?**
- Pretrained 모델 사용 시: 반드시 동일 값 사용
- 자체 데이터로 처음부터 학습 시: 자체 통계 계산 권장

---

## colsample_bytree=0.8의 원리

### 왜 0.8인가?

**배경: 배깅(Bagging)의 핵심 아이디어**
앙상블은 다양한 모델의 평균이 단일 모델보다 나음.
"다양성"을 확보하려면 각 트리가 다른 관점으로 학습해야 함.

**피처 샘플링이 다양성을 만드는 메커니즘**:
1. 트리 A: 피처 [f1, f2, f3, ...80개] 사용
2. 트리 B: 피처 [f2, f4, f5, ...다른 80개] 사용
3. 결과: 트리 A와 B의 예측이 다름 → 상관관계 ↓ → 앙상블 효과 ↑

**0.8인 이유**:
- Random Forest 관례: sqrt(n_features) ≈ 피처의 30-40%
- Boosting에서는 더 보수적: 70-90% 사용이 일반적
- 0.8 = 80%는 "충분한 정보 유지 + 적절한 랜덤성"의 경험적 균형점
- XGBoost/LightGBM 튜닝 가이드에서 0.7-0.9 범위 권장

**튜닝 방향**:
| 값 | 효과 |
|-----|------|
| 0.5 | 랜덤성 ↑, 과적합 방지 ↑, 성능 불안정 가능 |
| 0.8 | 균형점 (기본값) |
| 1.0 | 모든 피처 사용, 트리 다양성 ↓ |

---

## num_leaves=31의 출처

### 왜 31인가?

**계산**:
- 31 = 2^5 - 1
- 깊이 5의 완전 이진 트리 = 최대 32개 리프
- LightGBM 기본값 = 31 (1개 적음)

**왜 2^5인가?**
- XGBoost 기본 max_depth=6
- LightGBM은 더 보수적으로 max_depth=5 수준 상정
- 과적합 방지를 위한 안전 마진

**언제 바꾸나?**
| 상황 | 권장값 |
|------|--------|
| 데이터 복잡 | 63, 127 (2^6-1, 2^7-1) |
| 과적합 심함 | 15, 7 |
| 데이터 적음 | 15 이하 |

**규칙**: num_leaves를 2배로 → 학습 데이터도 2배 이상 필요

---

## 딥러닝 매직넘버

### 1e-4 (학습률)

**출처**: Adam 논문 (Kingma & Ba, 2014)
- 논문 권장값: 0.001 (1e-3)
- Fine-tuning 시: 1e-4 ~ 1e-5 (더 작게)
- Pretrained 모델 건드리지 않으려면 작은 lr 필요

### 768 (BERT hidden size)

**출처**: BERT 논문 (Devlin et al., 2018)
- 계산: 12 heads × 64 dim = 768
- Attention head 수와 head dimension의 곱
- GPT-2도 동일 (768)

### 0.1 (Dropout)

**출처**: Dropout 논문 (Srivastava et al., 2014)
- 기본 권장값: 0.5 (원 논문)
- Transformer 이후: 0.1이 표준
- BERT, GPT 모두 0.1 사용

### 3×3 (Conv kernel)

**출처**: VGGNet 논문 (Simonyan & Zisserman, 2014)
- 발견: 3×3 두 개 쌓기 = 5×5 하나와 동일 receptive field
- 하지만 파라미터 수: 3×3×2 = 18 < 5×5 = 25
- 결론: 작은 필터 여러 개가 효율적

### 0.9 (Adam beta1)

**출처**: Adam 논문 기본값
- beta1=0.9: 모멘텀 계수
- beta2=0.999: RMSprop 계수
- epsilon=1e-8: 수치 안정성

### 1e-5 / 1e-6 (weight decay)

**출처**: AdamW 논문 (Loshchilov & Hutter, 2017)
- BERT fine-tuning: 1e-5
- 일반 학습: 1e-4 ~ 1e-6

### 512 / 1024 / 2048 (max sequence length)

**출처**: Transformer 논문
- 512: BERT 기본
- 1024: GPT-2 기본
- 2048+: 최신 모델 (GPT-3, Llama)
- 2의 거듭제곱: 메모리 정렬 효율

### warmup_steps=10000

**출처**: Transformer 논문 (Vaswani et al., 2017)
- 왜?: 초기에 lr 너무 크면 학습 불안정
- 방법: 0에서 시작해서 점진적 증가
- 10000 steps = 논문에서 경험적으로 찾은 값

---

## 트리 모델 매직넘버

### max_depth=6 (XGBoost)

**출처**: XGBoost 기본값
- 왜 6?: 2^6 = 64개 리프까지 허용
- 경험칙: 깊이 6이면 대부분 문제 커버
- 과적합 방지와 성능의 균형점

### n_estimators=100

**출처**: 관례적 시작점
- sklearn RandomForest 기본값: 100
- XGBoost/LightGBM: 명시적 지정 필요
- 100에서 시작해서 early stopping으로 최적화

### subsample=0.8

**출처**: Stochastic Gradient Boosting (Friedman, 1999)
- 행(샘플) 랜덤 샘플링
- colsample_bytree와 유사한 원리
- 0.8 = 80% 샘플 사용

### min_child_weight=1 (XGBoost)

**출처**: XGBoost 기본값
- 리프 노드의 최소 가중치 합
- 작을수록 분할 자유로움 → 과적합 위험
- 불균형 데이터: 증가 권장 (10+)

### learning_rate=0.1 (트리)

**출처**: 관례
- Boosting에서 각 트리 기여도
- 작을수록 안정적, 느림
- 규칙: lr 절반 → n_estimators 2배

### reg_lambda=1 (L2 정규화)

**출처**: XGBoost 기본값
- 가중치에 L2 페널티
- 1.0이면 적당한 정규화
- 과적합 심하면 증가 (10, 100)

### scale_pos_weight

**출처**: 불균형 데이터 처리
- 계산: negative_samples / positive_samples
- 예: 1000:10 → scale_pos_weight=100
- positive 클래스에 가중치 부여
