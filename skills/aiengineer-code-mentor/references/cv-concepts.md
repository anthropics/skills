# 컴퓨터 비전 핵심 개념

이미지/영상 관련 코드 설명 시 참조.

## 이미지 데이터 기초

### 이미지 표현
- **픽셀값**: 0-255 (8bit) 또는 0-1 (정규화 후)
- **채널**: RGB(3), Grayscale(1), RGBA(4)
- **축 순서**: 
  - NumPy/OpenCV: (H, W, C) - Height, Width, Channel
  - PyTorch: (C, H, W) - Channel first
  - TensorFlow: (H, W, C) - Channel last (기본)

### 왜 정규화하나?
```python
# 0-255 → 0-1
image = image / 255.0
```
- 신경망 가중치 초기화가 보통 작은 값(-1~1)으로 됨
- 큰 입력값(0-255)은 gradient exploding 위험
- 정규화로 학습 안정성 확보

## 데이터 증강 (Augmentation)

### 왜 필요한가?
- 데이터 부족 문제 완화
- 모델이 위치/각도/밝기 변화에 강건해짐
- **핵심**: 라벨이 변하지 않는 변환만 사용

### 주요 기법과 사용 시점

| 기법 | 설명 | 주의사항 |
|------|------|----------|
| RandomHorizontalFlip | 좌우 반전 | 좌우 구분 중요하면 안됨 (예: 글자 인식) |
| RandomRotation | 회전 | 각도가 의미 있으면 안됨 (예: 숫자 6과 9) |
| RandomCrop | 일부 영역 자르기 | 핵심 객체가 잘릴 수 있음 |
| ColorJitter | 밝기/대비/채도 변경 | 색상이 중요한 task에선 주의 |
| RandomErasing/Cutout | 일부 영역 가리기 | 부분 가림에 강건해짐 |

### 증강은 언제 적용?
- **학습 시에만**: 매 epoch마다 다른 변환 적용
- **검증/테스트 시**: 증강 안 함 (공정한 평가를 위해)

## CNN 구조 이해

### Convolution Layer
```
왜 Convolution인가?
- Fully Connected는 이미지 크기에 비례해 파라미터 폭발
- Conv는 작은 필터를 슬라이딩 → 파라미터 효율적
- 위치 불변성: 고양이가 어디 있든 감지 가능
```

### 주요 파라미터
- **kernel_size**: 필터 크기. 3×3이 표준 (큰 receptive field는 여러 층으로)
- **stride**: 필터 이동 간격. 2면 출력 크기 절반
- **padding**: 테두리 처리. 'same'이면 출력 크기 유지
- **channels**: 입력/출력 채널 수. 깊어질수록 채널 증가가 일반적

### Pooling Layer
```
왜 Pooling인가?
- 다운샘플링으로 계산량 감소
- 작은 위치 변화에 불변성 부여
- Max Pooling: 가장 강한 특징 선택
- Average Pooling: 전체적인 특징 평균
```

## 전이 학습 (Transfer Learning)

### 왜 사용하나?
- ImageNet 100만장으로 학습된 특징 추출기 재활용
- 적은 데이터로도 좋은 성능
- 학습 시간 단축

### 전략 선택

| 상황 | 전략 |
|------|------|
| 데이터 적음 + 도메인 유사 | Feature extraction (마지막 층만 학습) |
| 데이터 많음 + 도메인 유사 | Fine-tuning (전체 또는 뒷부분 학습) |
| 데이터 적음 + 도메인 다름 | Fine-tuning (앞부분만, 낮은 lr) |
| 데이터 많음 + 도메인 다름 | 처음부터 학습 고려 |

### ImageNet 정규화 값의 의미
```python
mean = [0.485, 0.456, 0.406]  # RGB 채널별 평균
std = [0.229, 0.224, 0.225]   # RGB 채널별 표준편차
```
- ImageNet 전체 이미지에서 계산된 값
- 사전학습 모델 사용 시 동일하게 적용 필요
- 자체 데이터로 처음부터 학습하면 자체 통계 사용

## 객체 탐지 (Object Detection)

### 주요 개념
- **Bounding Box**: [x, y, width, height] 또는 [x1, y1, x2, y2]
- **IoU (Intersection over Union)**: 두 박스 겹침 정도. 0.5 이상이면 보통 정답으로 인정
- **NMS (Non-Maximum Suppression)**: 중복 박스 제거

### Two-stage vs One-stage
- **Two-stage (R-CNN 계열)**: Region 제안 → 분류. 정확하지만 느림
- **One-stage (YOLO, SSD)**: 한 번에 탐지. 빠르지만 작은 객체에 약함

## 영상 처리

### 영상 = 이미지의 시퀀스
- 추가 차원: (T, C, H, W) 또는 (Batch, T, C, H, W)
- T = 시간축 (프레임 수)

### 영상 특화 기법
- **3D Convolution**: 시공간 특징 동시 추출
- **Optical Flow**: 프레임 간 움직임 벡터
- **Temporal Pooling**: 시간 축 집계

### 메모리 주의
- 영상은 메모리 많이 사용
- 프레임 샘플링, 해상도 축소 고려
- batch_size 작게 시작

## 흔한 실수와 디버깅

### 이미지 로딩 관련
```python
# OpenCV는 BGR, PIL은 RGB
# cv2.imread() → BGR
# PIL.Image.open() → RGB
# cv2.cvtColor(img, cv2.COLOR_BGR2RGB) 로 변환
```

### 차원 불일치
```python
# 배치 차원 추가 필요할 때
image = image.unsqueeze(0)  # (C,H,W) → (1,C,H,W)
```

### 데이터 누수
- 증강이 test set에 적용되면 안됨
- train/val 분리 전 셔플하면 시계열에서 누수
