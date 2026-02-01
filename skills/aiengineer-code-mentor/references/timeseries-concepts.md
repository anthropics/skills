# 시계열 데이터 핵심 개념

시계열 관련 코드 설명 시 참조.

## 시계열 데이터 특성

### 일반 데이터와의 차이
- **순서가 중요**: 셔플하면 안됨
- **시간 의존성**: 과거가 미래에 영향
- **자기상관**: 인접 시점 값이 유사한 경향

### 데이터 분할 주의사항
```
❌ 잘못된 분할 (랜덤 셔플)
train: [t1, t5, t3, t8, t2]
test:  [t4, t6, t7]
→ 미래 데이터로 과거 예측하는 누수 발생

✅ 올바른 분할 (시간 순서 유지)
train: [t1, t2, t3, t4, t5]
val:   [t6, t7]
test:  [t8, t9, t10]
```

## 전처리

### 정규화 방식

| 방식 | 설명 | 사용 시점 |
|------|------|----------|
| Min-Max | (x - min) / (max - min) | 범위가 고정된 경우 |
| Standard | (x - mean) / std | 일반적인 경우 |
| Robust | (x - median) / IQR | 이상치가 많을 때 |

### 핵심 주의사항
```python
# ❌ 전체 데이터로 스케일러 fit
scaler.fit(all_data)

# ✅ train 데이터로만 fit, test에는 transform만
scaler.fit(train_data)
train_scaled = scaler.transform(train_data)
test_scaled = scaler.transform(test_data)
```
→ test 통계가 학습에 반영되면 데이터 누수

### 결측치 처리
- **Forward fill**: 이전 값으로 채움 (가장 흔함)
- **Interpolation**: 선형/다항식 보간
- **삭제**: 결측 구간이 길면 해당 시퀀스 제외

## 시퀀스 구성

### Sliding Window
```python
# 입력: 과거 n개 시점
# 출력: 다음 1개 (또는 m개) 시점
window_size = 10
for i in range(len(data) - window_size):
    X.append(data[i:i+window_size])
    y.append(data[i+window_size])
```

### Window Size 선택
- 너무 작으면: 패턴 학습 부족
- 너무 크면: 노이즈 포함, 메모리 부담
- 도메인 지식 활용 (예: 일주일 주기면 7일 이상)

### Multi-step 예측
```
Single-step: X[t-n:t] → y[t+1]
Multi-step:  X[t-n:t] → y[t+1:t+m]
```

## 모델 선택

### 전통 모델 vs 딥러닝

| 모델 | 장점 | 단점 |
|------|------|------|
| ARIMA | 해석 가능, 적은 데이터 OK | 비선형 패턴 못잡음 |
| Prophet | 트렌드/계절성 자동 분리 | 복잡한 패턴 한계 |
| LSTM/GRU | 장기 의존성 학습 | 데이터 많이 필요 |
| Transformer | 병렬화, 긴 시퀀스 | 매우 많은 데이터 필요 |
| 1D CNN | 빠름, 로컬 패턴 | 장기 의존성 약함 |

### LSTM/GRU 이해

```
왜 RNN이 아닌 LSTM/GRU?
- 기본 RNN은 긴 시퀀스에서 기울기 소실
- LSTM: forget/input/output 게이트로 장기 기억 유지
- GRU: LSTM 간소화, 파라미터 적음, 비슷한 성능
```

### 주요 파라미터
- **hidden_size**: 은닉 상태 차원. 클수록 복잡한 패턴, 과적합 위험
- **num_layers**: 층 수. 깊을수록 추상적 특징
- **bidirectional**: 양방향. 예측에는 부적합 (미래 정보 사용)
- **dropout**: 층 사이에 적용, 마지막 층엔 안함

## 평가 지표

### 회귀 (연속값 예측)
```python
MAE  = mean(|y - ŷ|)        # 직관적, 이상치에 덜 민감
MSE  = mean((y - ŷ)²)       # 큰 오차 강하게 페널티
RMSE = sqrt(MSE)            # 원래 단위로 해석 가능
MAPE = mean(|y - ŷ|/|y|)    # 퍼센트, y=0이면 문제
```

### 분류 (이벤트 예측)
- 시계열 분류: 전체 시퀀스 → 하나의 라벨
- Accuracy, F1, AUC 등 일반 분류 지표 사용

### 주의사항
- 단순 baseline과 비교 (예: "어제와 같음" 예측)
- 시계열은 자기상관 있어서 naive baseline도 꽤 좋음

## 흔한 실수

### 미래 정보 누수
```python
# ❌ 전체 데이터로 정규화 후 분할
normalized = (data - data.mean()) / data.std()
train, test = split(normalized)

# ✅ 분할 후 train으로만 정규화
train, test = split(data)
mean, std = train.mean(), train.std()
train_norm = (train - mean) / std
test_norm = (test - mean) / std
```

### 계절성 무시
- 주기적 패턴이 있으면 그 주기 이상의 데이터 필요
- 연간 패턴이면 최소 2년 데이터 권장

### 시간 특성 미활용
```python
# 유용한 시간 특성
df['hour'] = df['timestamp'].dt.hour
df['dayofweek'] = df['timestamp'].dt.dayofweek
df['month'] = df['timestamp'].dt.month
df['is_weekend'] = df['dayofweek'].isin([5, 6])
```

### 정상성 가정 위반
- 많은 모델이 정상성(stationary) 가정
- 트렌드/계절성 제거 후 모델링
- 또는 차분(differencing) 적용
