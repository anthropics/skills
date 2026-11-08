# ML 파이프라인 핵심 개념

데이터 유형과 무관하게 공통으로 적용되는 ML 개념.

## 데이터 분할

### Train / Validation / Test

```
Train (60-80%): 모델 학습
Val (10-20%):   하이퍼파라미터 튜닝, 조기 종료 판단
Test (10-20%):  최종 성능 평가 (한 번만 사용)
```

### 왜 세 개로 나누나?
- Train으로 학습 → val로 성능 확인 → 하이퍼파라미터 조정
- 이 과정에서 val에 간접적으로 과적합됨
- Test는 마지막에 한 번만 → 실제 성능의 공정한 추정

### Cross-Validation
```python
# 데이터가 적을 때 유용
# K-Fold: K개로 나눠 K번 학습/검증
# 각 fold가 한 번씩 validation 역할
```
- 장점: 모든 데이터를 학습/검증에 활용
- 단점: K배 학습 시간

## 손실 함수 (Loss Function)

### 회귀
| Loss | 수식 | 특성 |
|------|------|------|
| MSE | (y-ŷ)² | 큰 오차에 민감, 미분 가능 |
| MAE | \|y-ŷ\| | 이상치에 강건, 0에서 미분 불가 |
| Huber | MSE + MAE 조합 | 절충안 |

### 분류
| Loss | 용도 |
|------|------|
| CrossEntropy | 다중 클래스 |
| BCELoss | 이진 분류 (시그모이드 출력) |
| BCEWithLogitsLoss | 이진 분류 (raw logit 출력) |

### Loss vs Metric
- **Loss**: 학습에 사용, 미분 가능해야 함
- **Metric**: 평가에 사용, 해석 용이해야 함
- 예: CrossEntropy로 학습, Accuracy로 평가

## 옵티마이저

### 주요 옵티마이저

```
SGD: 기본, 모멘텀 추가 권장
Adam: 적응적 학습률, 대부분 상황에서 무난
AdamW: Adam + weight decay 분리, transformer에 권장
```

### Learning Rate

```
너무 크면: 발산, loss가 튐
너무 작으면: 수렴 느림, local minimum에 갇힘
```

### Learning Rate Scheduler
```python
# 왜 필요?
# 처음: 큰 보폭으로 빠르게 탐색
# 나중: 작은 보폭으로 미세 조정

# 자주 쓰이는 스케줄러
StepLR: n epoch마다 lr *= gamma
CosineAnnealing: 코사인 형태로 감소
ReduceLROnPlateau: val loss 정체 시 감소
```

## 과적합 방지

### 증상
- Train loss ↓, Val loss ↑
- Train accuracy >> Val accuracy

### 대응 방법

| 방법 | 설명 |
|------|------|
| **데이터 증강** | 학습 데이터 다양성 증가 |
| **Dropout** | 학습 중 랜덤하게 뉴런 비활성화 |
| **Weight Decay (L2)** | 가중치 크기에 페널티 |
| **Early Stopping** | Val loss가 나빠지면 학습 중단 |
| **모델 단순화** | 층 수/뉴런 수 감소 |
| **배치 정규화** | 내부 공변량 이동 감소 |

### Early Stopping 구현
```python
best_val_loss = float('inf')
patience_counter = 0
patience = 5  # 5 epoch 동안 개선 없으면 종료

for epoch in range(max_epochs):
    train_loss = train()
    val_loss = validate()
    
    if val_loss < best_val_loss:
        best_val_loss = val_loss
        patience_counter = 0
        save_model()  # 최고 성능 모델 저장
    else:
        patience_counter += 1
        if patience_counter >= patience:
            break
```

## 배치 처리

### Batch Size 영향
```
작은 배치:
- 노이즈 있는 gradient → 일반화에 도움될 수 있음
- GPU 활용도 낮음
- 학습 느림

큰 배치:
- 안정적인 gradient
- GPU 활용도 높음
- 같은 성능에 더 큰 lr 필요
- 메모리 한계
```

### Gradient Accumulation
```python
# 메모리 부족할 때 큰 배치 효과
accumulation_steps = 4  # 실제 배치 32 → 효과적 배치 128

for i, batch in enumerate(loader):
    loss = model(batch) / accumulation_steps
    loss.backward()
    
    if (i + 1) % accumulation_steps == 0:
        optimizer.step()
        optimizer.zero_grad()
```

## 평가 지표

### 분류

| 지표 | 언제 사용 |
|------|----------|
| Accuracy | 클래스 균형할 때 |
| Precision | 거짓 양성 비용 클 때 (스팸 필터) |
| Recall | 거짓 음성 비용 클 때 (암 진단) |
| F1 | Precision-Recall 균형 |
| AUC-ROC | 임계값 독립적 평가 |

### 불균형 데이터 주의
```
99% 정상, 1% 이상 데이터에서
"전부 정상"으로 예측하면 Accuracy 99%
→ Accuracy만 보면 안됨
→ F1, AUC, 또는 클래스별 metrics 확인
```

## 모델 저장/로드

### PyTorch
```python
# 모델 전체 저장 (비권장)
torch.save(model, 'model.pt')

# state_dict만 저장 (권장)
torch.save(model.state_dict(), 'model_weights.pt')

# 로드
model = MyModel()
model.load_state_dict(torch.load('model_weights.pt'))
model.eval()  # 추론 모드
```

### Checkpoint (학습 재개용)
```python
checkpoint = {
    'epoch': epoch,
    'model_state_dict': model.state_dict(),
    'optimizer_state_dict': optimizer.state_dict(),
    'loss': loss,
}
torch.save(checkpoint, 'checkpoint.pt')
```

## 재현성 (Reproducibility)

```python
import random
import numpy as np
import torch

def set_seed(seed=42):
    random.seed(seed)
    np.random.seed(seed)
    torch.manual_seed(seed)
    torch.cuda.manual_seed_all(seed)
    torch.backends.cudnn.deterministic = True
    torch.backends.cudnn.benchmark = False
```

### 완전한 재현이 어려운 이유
- GPU 연산의 비결정성
- 멀티스레딩
- 라이브러리 버전 차이

## 디버깅 팁

### 학습이 안될 때 체크리스트
1. **데이터 확인**: 라벨이 맞는지, 전처리가 제대로 됐는지
2. **작은 데이터로 과적합**: 10개 샘플로 loss 0 가능한지
3. **Learning rate**: 너무 크거나 작은지
4. **Gradient 확인**: NaN이나 0인지
5. **Loss 함수**: 문제 유형에 맞는지

### 로그 출력 예시
```python
for epoch in range(epochs):
    for batch_idx, (data, target) in enumerate(loader):
        # 학습 로직
        
        if batch_idx % 100 == 0:
            print(f'Epoch {epoch}, Batch {batch_idx}, Loss: {loss.item():.4f}')
    
    # 에폭 끝날 때
    print(f'Epoch {epoch}: Train Loss {train_loss:.4f}, Val Loss {val_loss:.4f}')
```
