# 파라미터 간 상호작용

> 파라미터는 혼자 작동하지 않는다. 함께 조정해야 할 파라미터 쌍을 이해합니다.

---

## DataLoader-병렬화

### num_workers, pin_memory, prefetch_factor 관계

```python
DataLoader(
    dataset,
    batch_size=32,
    num_workers=4,      # CPU 워커 수
    pin_memory=True,    # GPU 전송 최적화
    prefetch_factor=2,  # 워커당 미리 로드할 배치 수
)
```

**상호작용**:

| 파라미터 | 역할 | 다른 파라미터와 관계 |
|---------|------|---------------------|
| `num_workers` | 데이터 로딩 병렬화 | CPU 코어 수 고려, 너무 많으면 오버헤드 |
| `pin_memory` | GPU 전송 속도 ↑ | `num_workers > 0`일 때만 효과 |
| `prefetch_factor` | 버퍼 크기 | `num_workers × prefetch_factor` = 대기 배치 수 |

**권장 설정**:
```python
# GPU 학습 시
num_workers = min(4, cpu_count())  # 4개면 충분
pin_memory = True
prefetch_factor = 2  # 기본값

# CPU만 있을 때
num_workers = 0  # 멀티프로세싱 비활성화
pin_memory = False
```

**Windows 주의사항**:
```python
if __name__ == '__main__':  # 필수!
    loader = DataLoader(..., num_workers=4)
```

---

## learning_rate ↔ n_estimators

### 트리 앙상블에서의 관계

```python
# 조합 1: 빠른 학습
model = LGBMClassifier(learning_rate=0.1, n_estimators=100)

# 조합 2: 안정적 학습 (결과 비슷)
model = LGBMClassifier(learning_rate=0.05, n_estimators=200)

# 조합 3: 더 안정적 (결과 비슷)
model = LGBMClassifier(learning_rate=0.01, n_estimators=1000)
```

**핵심 관계**:
```
learning_rate × n_estimators ≈ 상수
```

| learning_rate | n_estimators | 학습 시간 | 안정성 |
|---------------|--------------|-----------|--------|
| 0.1 | 100 | 빠름 | 불안정 가능 |
| 0.05 | 200 | 보통 | 보통 |
| 0.01 | 1000 | 느림 | 안정적 |

**튜닝 전략**:
1. `n_estimators=10000` (큰 값) 고정
2. `early_stopping_rounds=50` 설정
3. `learning_rate`만 조정 (0.01 ~ 0.1)
4. Early stopping이 최적 n_estimators 찾아줌

---

## num_leaves ↔ max_depth

### LightGBM에서의 관계

**규칙**:
```
num_leaves ≤ 2^max_depth
```

```python
# 일관된 설정
model = LGBMClassifier(
    num_leaves=31,     # 2^5 - 1
    max_depth=5,       # 일치
)

# 불일치 (권장하지 않음)
model = LGBMClassifier(
    num_leaves=31,     # 2^5 - 1
    max_depth=3,       # 2^3 = 8 < 31 → 실제로 8개 리프만 사용
)
```

**왜 둘 다 있나?**
- `num_leaves`: 복잡도의 주 제어 (LightGBM 권장)
- `max_depth`: 보조 제어, 극단적 불균형 방지

**튜닝 전략**:
| 데이터 크기 | num_leaves | max_depth |
|-------------|------------|-----------|
| 작음 (<10K) | 15-31 | 5-7 |
| 보통 (10K-100K) | 31-63 | 7-10 |
| 큼 (>100K) | 63-127 | 10-15 |

---

## colsample_bytree ↔ subsample

### 열 vs 행 랜덤성

```python
model = XGBClassifier(
    colsample_bytree=0.8,  # 피처(열) 80% 샘플링
    subsample=0.8,         # 샘플(행) 80% 샘플링
)
```

**차이점**:

| 파라미터 | 샘플링 대상 | 효과 |
|---------|------------|------|
| `colsample_bytree` | 피처 (열) | 트리 간 다양성 ↑ |
| `subsample` | 샘플 (행) | 과적합 방지, 노이즈 감소 |

**함께 조정하는 이유**:
- 둘 다 정규화 효과
- 하나만 낮추면 효과 제한적
- 둘 다 0.8이면 실제로 64% 데이터만 사용

**튜닝 조합**:
| colsample | subsample | 용도 |
|-----------|-----------|------|
| 0.8 | 0.8 | 기본 (균형) |
| 0.6 | 0.8 | 피처 많을 때 |
| 0.8 | 0.6 | 샘플 많을 때 |
| 0.6 | 0.6 | 과적합 심할 때 |

---

## batch_size ↔ learning_rate

### 딥러닝에서의 Linear Scaling Rule

**규칙** (He et al., 2017 - ImageNet 학습):
```
batch_size 2배 → learning_rate 2배
```

```python
# 조합 1
batch_size = 32
lr = 0.001

# 조합 2 (동등)
batch_size = 64
lr = 0.002

# 조합 3 (동등)
batch_size = 256
lr = 0.008
```

**왜 이런 관계?**
- 큰 배치 = 더 정확한 gradient 추정
- 정확한 gradient = 더 큰 step 가능
- 작은 배치 = 노이즈 있는 gradient = 작은 step 필요

**주의사항**:
| 상황 | 권장 |
|------|------|
| batch_size 2배 | lr 1.5~2배 (선형보다 약간 보수적) |
| batch_size 매우 큼 (>1024) | warmup 필수 |
| batch_size 너무 작음 (<8) | 정규화 효과 사라질 수 있음 |

**Gradient Accumulation**:
```python
# 메모리 부족 시 큰 배치 효과
accumulation_steps = 4
for i, batch in enumerate(loader):  # batch_size=32
    loss = model(batch) / accumulation_steps
    loss.backward()
    if (i + 1) % accumulation_steps == 0:
        optimizer.step()  # 효과적 batch_size = 32 × 4 = 128
        optimizer.zero_grad()
```

---

## dropout ↔ weight_decay

### 정규화 중복 주의

```python
# 둘 다 정규화 효과
model = nn.Sequential(
    nn.Linear(100, 50),
    nn.Dropout(0.5),  # 정규화 1
    nn.ReLU(),
)
optimizer = AdamW(model.parameters(), weight_decay=0.01)  # 정규화 2
```

**상호작용**:

| dropout | weight_decay | 효과 |
|---------|--------------|------|
| 0.5 | 0.01 | 정규화 과다 → 과소적합 위험 |
| 0.3 | 0.01 | 균형 |
| 0.1 | 0.01 | 가벼운 정규화 |
| 0.0 | 0.1 | weight_decay만으로 정규화 |

**권장 조합**:
| 모델 유형 | dropout | weight_decay |
|-----------|---------|--------------|
| Transformer | 0.1 | 0.01 |
| CNN | 0.25-0.5 | 1e-4 |
| 작은 MLP | 0.5 | 1e-5 |

**언제 둘 다 끄나?**
- 데이터가 매우 많을 때
- 모델이 이미 충분히 작을 때
- 언더피팅 문제가 있을 때

---

## 추가 상호작용

### momentum ↔ learning_rate (SGD)

```python
# SGD with momentum
optimizer = SGD(model.parameters(), lr=0.1, momentum=0.9)
```

| momentum | lr | 효과 |
|----------|-----|------|
| 0.9 | 0.1 | 표준 설정 |
| 0.9 | 0.01 | 안정적이지만 느림 |
| 0.99 | 0.01 | 높은 모멘텀 보상 |

### warmup_steps ↔ learning_rate

```python
# Warmup scheduler
scheduler = get_linear_schedule_with_warmup(
    optimizer,
    num_warmup_steps=1000,
    num_training_steps=10000,
)
```

| max_lr | warmup_steps | 권장 |
|--------|--------------|------|
| 1e-4 | 100-500 | 작은 lr은 짧은 warmup |
| 1e-3 | 1000-2000 | 큰 lr은 긴 warmup |
| 1e-2 | 2000-5000 | 매우 큰 lr은 매우 긴 warmup |

### early_stopping_patience ↔ learning_rate

| learning_rate | patience | 이유 |
|---------------|----------|------|
| 0.1 | 5-10 | 빠른 수렴 → 짧은 patience |
| 0.01 | 10-20 | 느린 수렴 → 긴 patience |
| 0.001 | 20-50 | 매우 느린 수렴 → 매우 긴 patience |
