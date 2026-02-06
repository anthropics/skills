# 알고리즘 내부 동작

> "왜 이렇게 작동하는가?"에 대한 깊은 이해를 위한 문서

---

## Leaf-wise 트리의 복잡도 제어

### Level-wise vs Leaf-wise 비교

```
[Level-wise (XGBoost 기본)]          [Leaf-wise (LightGBM)]
       Root                                 Root
      /    \                               /    \
     O      O     ← 같은 레벨 전부        O      O
    / \    / \       먼저 확장           / \
   O   O  O   O                        O   O    ← 손실 감소 최대인
                                          / \      리프만 확장
                                         O   O
```

**Level-wise (XGBoost)**:
- 같은 깊이의 모든 노드를 동시에 확장
- 균형 잡힌 트리 → 과적합 자연 방지
- 단점: 불필요한 분할도 수행 → 느림

**Leaf-wise (LightGBM)**:
- 손실 감소가 가장 큰 리프만 선택적으로 확장
- 불균형 트리 → 과적합 위험 ↑
- 장점: 필요한 분할만 → 빠름

### 왜 max_depth=-1인데 num_leaves로 제어하나?

Level-wise는 깊이=5면 모든 노드가 깊이 5까지 균등하게 자람.
Leaf-wise는 손실 감소가 큰 리프만 선택적으로 자라서 깊이가 불균형.

따라서:
- `max_depth=-1`: "깊이로 제한 안 함" (leaf-wise에선 의미 약함)
- `num_leaves=31`: "리프 최대 31개" (실제 복잡도 직접 제어)
- 관계: `num_leaves ≤ 2^max_depth` 이어야 일관성 유지
- 31 = 2^5 - 1: max_depth=5 수준의 복잡도를 리프 수로 표현

---

## Leaf-wise의 트레이드오프

### 왜 더 빠른가?

```python
# Level-wise: 모든 노드 확장
for node in all_nodes_at_depth(d):
    if can_split(node):
        split(node)  # 불필요한 분할 포함

# Leaf-wise: 최적 노드만 확장
best_leaf = max(leaves, key=loss_reduction)
split(best_leaf)  # 효율적
```

- Level-wise: 모든 노드 확장 (불필요한 분할 포함)
- Leaf-wise: 손실 감소 최대 노드만 확장 (효율적)
- 같은 리프 수 도달까지 연산량 ↓

### 왜 과적합 위험이 높은가?

- **탐욕적(Greedy) 선택**: 현재 손실 감소만 보고 분할
- 학습 데이터의 노이즈도 "손실 감소"로 인식 → 학습해버림
- **불균형 트리**: 특정 영역만 과도하게 깊어짐

### 해결책

| 방법 | 파라미터 | 효과 |
|------|---------|------|
| 리프 수 제한 | `num_leaves=15` | 복잡도 직접 제어 |
| 최소 샘플 수 | `min_data_in_leaf=20` | 작은 리프 방지 |
| L2 정규화 | `lambda=1.0` | 가중치 크기 제한 |
| L1 정규화 | `alpha=0.1` | 희소성 유도 |

---

## 추론-모드-동작

### model.eval()이 하는 일

```python
model.eval()  # 추론 모드 활성화
```

**내부적으로 변경되는 것**:

| 레이어 | train() 모드 | eval() 모드 |
|--------|-------------|-------------|
| **Dropout** | 랜덤하게 뉴런 비활성화 | 모든 뉴런 활성화 (확률로 스케일) |
| **BatchNorm** | 현재 배치 통계 사용 | 저장된 running 통계 사용 |
| **LayerNorm** | 동일 | 동일 |

**Dropout 동작 상세**:
```python
# train() 모드
x = x * (random_mask)  # 일부 0으로

# eval() 모드
x = x * (1 - p)  # 전체에 (1-dropout_rate) 곱함
```

**왜 eval() 안 하면 문제?**
- 같은 입력 → 다른 출력 (Dropout 랜덤)
- 프로덕션에서 예측 불안정
- 디버깅 지옥

### torch.no_grad()가 하는 일

```python
with torch.no_grad():
    output = model(x)
```

**내부적으로 변경되는 것**:
- `requires_grad=False`로 모든 연산 처리
- Gradient 계산 그래프 생성 안 함
- 메모리 사용량 대폭 감소 (중간 결과 저장 안 함)

**eval()과 no_grad() 차이**:
| | eval() | no_grad() |
|---|--------|-----------|
| 목적 | 레이어 동작 변경 | 메모리 절약 |
| Dropout 영향 | O | X |
| BatchNorm 영향 | O | X |
| Gradient 계산 | 여전히 함 | 안 함 |

**둘 다 필요한 이유**:
```python
model.eval()         # Dropout, BatchNorm 동작 변경
with torch.no_grad():  # 메모리 절약
    output = model(x)
```
- 하나만 하면 불완전!

---

## device-관리

### 왜 .to(device)를 매번 해야 하나?

```python
device = torch.device('cuda' if torch.cuda.is_available() else 'cpu')
model.to(device)
x = x.to(device)
```

**내부 원리**:
- PyTorch 텐서는 메모리 위치를 가짐 (CPU RAM vs GPU VRAM)
- 연산은 **같은 장치**의 텐서끼리만 가능
- 모델 파라미터도 텐서 → 장치 위치 있음

**흔한 실수**:
```python
# 에러: 모델은 GPU, 데이터는 CPU
model.to('cuda')
output = model(x)  # RuntimeError: expected device cuda but got cpu

# 해결
x = x.to('cuda')
output = model(x)  # OK
```

**DataLoader에서 자동화**:
```python
for batch in dataloader:
    x, y = batch
    x, y = x.to(device), y.to(device)  # 매 배치마다 필요
```

### pin_memory와 non_blocking

```python
DataLoader(..., pin_memory=True)
x = x.to(device, non_blocking=True)
```

**pin_memory**:
- CPU 메모리를 "고정" → GPU 전송 빨라짐
- 페이지 스왑 방지

**non_blocking**:
- 비동기 전송 (CPU-GPU 병렬 작업)
- 다음 배치 준비하는 동안 현재 배치 처리

---

## 옵티마이저 내부

### SGD 동작

```python
# 의사 코드
for param in model.parameters():
    param.data -= lr * param.grad
```

- 고정 학습률
- 모든 파라미터에 동일하게 적용
- 단점: 희소한 피처에 불리

### Adam 동작

```python
# 의사 코드 (간소화)
m = beta1 * m + (1 - beta1) * grad       # 모멘텀 (1차 모멘트)
v = beta2 * v + (1 - beta2) * grad**2    # RMSprop (2차 모멘트)
m_hat = m / (1 - beta1**t)               # 편향 보정
v_hat = v / (1 - beta2**t)               # 편향 보정
param -= lr * m_hat / (sqrt(v_hat) + eps)
```

**왜 Adam인가?**
| | SGD | Adam |
|---|-----|------|
| 학습률 | 고정 | 적응적 (파라미터별) |
| 튜닝 | lr 민감 | lr 덜 민감 |
| 수렴 속도 | 느림 | 빠름 |
| 최종 성능 | 때때로 더 좋음 | 일반적으로 좋음 |

### AdamW vs Adam

```python
# Adam (L2 regularization)
grad = grad + weight_decay * param
param -= lr * adam_update(grad)

# AdamW (Decoupled weight decay)
param -= lr * adam_update(grad)
param -= lr * weight_decay * param  # 분리됨
```

**차이점**:
- Adam: weight decay가 gradient에 포함 → 적응적 lr에 영향
- AdamW: weight decay가 분리됨 → 더 일관된 정규화

**권장**:
- Transformer: AdamW
- CNN: 둘 다 OK

---

## 정규화 레이어 내부

### BatchNorm 동작

```python
# 학습 시
mean = x.mean(dim=0)  # 배치 평균
var = x.var(dim=0)    # 배치 분산
x_norm = (x - mean) / sqrt(var + eps)
out = gamma * x_norm + beta  # 학습 가능한 파라미터

# running 통계 업데이트 (eval 때 사용)
running_mean = momentum * running_mean + (1 - momentum) * mean
running_var = momentum * running_var + (1 - momentum) * var
```

**왜 필요한가?**
- 내부 공변량 이동(Internal Covariate Shift) 감소
- 각 레이어 입력 분포 안정화
- 더 높은 lr 사용 가능

### LayerNorm vs BatchNorm

| | BatchNorm | LayerNorm |
|---|-----------|-----------|
| 정규화 축 | 배치 (dim=0) | 피처 (dim=-1) |
| 배치 크기 의존 | O | X |
| 주 사용처 | CNN | Transformer |
| eval 동작 | running 통계 | 현재 입력 통계 |

**Transformer에서 LayerNorm 쓰는 이유**:
- 시퀀스 길이가 가변적
- 배치 크기 작을 수 있음
- 배치 간 독립성 보장
