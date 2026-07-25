# Computer Vision Architectures

Comprehensive guide to CNN and Vision Transformer architectures for object detection, segmentation, and image classification.

## Table of Contents

- [Backbone Architectures](#backbone-architectures)
- [Detection Architectures](#detection-architectures)
- [Segmentation Architectures](#segmentation-architectures)
- [Vision Transformers](#vision-transformers)
- [Feature Pyramid Networks](#feature-pyramid-networks)
- [Architecture Selection](#architecture-selection)

---

## Backbone Architectures

Backbone networks extract feature representations from images. The choice of backbone affects both accuracy and inference speed.

### ResNet Family

ResNet introduced residual connections that enable training of very deep networks.

| Variant | Params | GFLOPs | Top-1 Acc | Use Case |
|---------|--------|--------|-----------|----------|
| ResNet-18 | 11.7M | 1.8 | 69.8% | Edge, mobile |
| ResNet-34 | 21.8M | 3.7 | 73.3% | Balanced |
| ResNet-50 | 25.6M | 4.1 | 76.1% | Standard backbone |
| ResNet-101 | 44.5M | 7.8 | 77.4% | High accuracy |
| ResNet-152 | 60.2M | 11.6 | 78.3% | Maximum accuracy |

**Residual Block Architecture:**

```
Input
  |
  +---> Conv 1x1 (reduce channels)
  |         |
  |     Conv 3x3
  |         |
  |     Conv 1x1 (expand channels)
  |         |
  +-----> Add <----+
            |
         ReLU
            |
         Output
```

**When to use ResNet:**
- Standard detection/segmentation tasks
- When pretrained weights are important
- Moderate compute budget
- Well-understood, stable architecture

### EfficientNet Family

EfficientNet uses compound scaling to balance depth, width, and resolution.

| Variant | Params | GFLOPs | Top-1 Acc | Relative Speed |
|---------|--------|--------|-----------|----------------|
| EfficientNet-B0 | 5.3M | 0.4 | 77.1% | 1x |
| EfficientNet-B1 | 7.8M | 0.7 | 79.1% | 0.7x |
| EfficientNet-B2 | 9.2M | 1.0 | 80.1% | 0.6x |
| EfficientNet-B3 | 12M | 1.8 | 81.6% | 0.4x |
| EfficientNet-B4 | 19M | 4.2 | 82.9% | 0.25x |
| EfficientNet-B5 | 30M | 9.9 | 83.6% | 0.15x |
| EfficientNet-B6 | 43M | 19 | 84.0% | 0.1x |
| EfficientNet-B7 | 66M | 37 | 84.3% | 0.05x |

**Key innovations:**
- Mobile Inverted Bottleneck (MBConv) blocks
- Squeeze-and-Excitation attention
- Compound scaling coefficients
- Swish activation function

**When to use EfficientNet:**
- Mobile and edge deployment
- When parameter efficiency matters
- Classification tasks
- Limited compute resources

### ConvNeXt

ConvNeXt modernizes ResNet with techniques from Vision Transformers.

| Variant | Params | GFLOPs | Top-1 Acc |
|---------|--------|--------|-----------|
| ConvNeXt-T | 29M | 4.5 | 82.1% |
| ConvNeXt-S | 50M | 8.7 | 83.1% |
| ConvNeXt-B | 89M | 15.4 | 83.8% |
| ConvNeXt-L | 198M | 34.4 | 84.3% |
| ConvNeXt-XL | 350M | 60.9 | 84.7% |

**Key design choices:**
- 7x7 depthwise convolutions (like ViT patch size)
- Layer normalization instead of batch norm
- GELU activation
- Fewer but wider stages
- Inverted bottleneck design

**ConvNeXt Block:**

```
Input
  |
  +---> DWConv 7x7
  |         |
  |     LayerNorm
  |         |
  |     Linear (4x channels)
  |         |
  |     GELU
  |         |
  |     Linear (1x channels)
  |         |
  +-----> Add <----+
            |
         Output
```

### CSPNet (Cross Stage Partial)

CSPNet is the backbone design used in YOLO v4-v8.

**Key features:**
- Gradient flow optimization
- Reduced computation while maintaining accuracy
- Cross-stage partial connections
- Optimized for real-time detection

**CSP Block:**

```
Input
  |
  +----> Split ----+
  |                |
  |            Conv Block
  |                |
  |            Conv Block
  |                |
  +----> Concat <--+
            |
         Output
```

---

## Detection Architectures

### Two-Stage Detectors

Two-stage detectors first propose regions, then classify and refine them.

#### Faster R-CNN

Architecture:
1. **Backbone**: Feature extraction (ResNet, etc.)
2. **RPN (Region Proposal Network)**: Generate object proposals
3. **RoI Pooling/Align**: Extract fixed-size features
4. **Classification Head**: Classify and refine boxes

```
Image → Backbone → Feature Map
                      |
                      +→ RPN → Proposals
                      |           |
                      +→ RoI Align ← +
                            |
                      FC Layers
                            |
                    Class + BBox
```

**RPN Details:**
- Sliding window over feature map
- Anchor boxes at each position (3 scales × 3 ratios = 9)
- Predicts objectness score and box refinement
- NMS to reduce proposals (typically 300-2000)

**Performance characteristics:**
- mAP@50:95: ~40-42 (COCO, R50-FPN)
- Inference: ~50-100ms per image
- Better localization than single-stage
- Slower but more accurate

#### Cascade R-CNN

Multi-stage refinement with increasing IoU thresholds.

```
Stage 1 (IoU 0.5) → Stage 2 (IoU 0.6) → Stage 3 (IoU 0.7)
```

**Benefits:**
- Progressive refinement
- Better high-IoU predictions
- +3-4 mAP over Faster R-CNN
- Minimal additional cost per stage

### Single-Stage Detectors

Single-stage detectors predict boxes and classes in one pass.

#### YOLO Family

**YOLOv8 Architecture:**

```
Input Image
     |
  Backbone (CSPDarknet)
     |
  +--+--+--+
  |  |  |  |
 P3 P4 P5 (multi-scale features)
  |  |  |
  Neck (PANet + C2f)
  |  |  |
  Head (Decoupled)
     |
 Boxes + Classes
```

**Key YOLOv8 innovations:**
- C2f module (faster CSP variant)
- Anchor-free detection head
- Decoupled classification/regression heads
- Task-aligned assigner (TAL)
- Distribution focal loss (DFL)

**YOLO variant comparison:**

| Model | Size (px) | Params | mAP@50:95 | Speed (ms) |
|-------|-----------|--------|-----------|------------|
| YOLOv5n | 640 | 1.9M | 28.0 | 1.2 |
| YOLOv5s | 640 | 7.2M | 37.4 | 1.8 |
| YOLOv5m | 640 | 21.2M | 45.4 | 3.5 |
| YOLOv8n | 640 | 3.2M | 37.3 | 1.2 |
| YOLOv8s | 640 | 11.2M | 44.9 | 2.1 |
| YOLOv8m | 640 | 25.9M | 50.2 | 4.2 |
| YOLOv8l | 640 | 43.7M | 52.9 | 6.8 |
| YOLOv8x | 640 | 68.2M | 53.9 | 10.1 |

#### SSD (Single Shot Detector)

Multi-scale detection with default boxes.

**Architecture:**
- VGG16 or MobileNet backbone
- Additional convolution layers for multi-scale
- Default boxes at each scale
- Direct classification and regression

**When to use SSD:**
- Edge deployment (SSD-MobileNet)
- When YOLO alternatives needed
- Simple architecture requirements

#### RetinaNet

Focal loss to handle class imbalance.

**Key innovation:**
```python
FL(p_t) = -α_t * (1 - p_t)^γ * log(p_t)
```

Where:
- γ (focusing parameter) = 2 typically
- α (class weight) = 0.25 for background

**Benefits:**
- Handles extreme foreground-background imbalance
- Matches two-stage accuracy
- Single-stage speed

---

## Segmentation Architectures

### Instance Segmentation

#### Mask R-CNN

Extends Faster R-CNN with mask prediction branch.

```
RoI Features → FC Layers → Class + BBox
      |
      +→ Conv Layers → Mask (28×28 per class)
```

**Key details:**
- RoI Align (bilinear interpolation, no quantization)
- Per-class binary mask prediction
- Decoupled mask and classification
- 14×14 or 28×28 mask resolution

**Performance:**
- mAP (box): ~39 on COCO
- mAP (mask): ~35 on COCO
- Inference: ~100-200ms

#### YOLACT / YOLACT++

Real-time instance segmentation.

**Approach:**
1. Generate prototype masks (global)
2. Predict mask coefficients per instance
3. Linear combination: mask = Σ(coefficients × prototypes)

**Benefits:**
- Real-time (~30 FPS)
- Simpler than Mask R-CNN
- Global prototypes capture spatial info

#### YOLOv8-Seg

Adds segmentation head to YOLOv8.

**Performance:**
- mAP (box): 44.6
- mAP (mask): 36.8
- Speed: 4.5ms

### Semantic Segmentation

#### DeepLabV3+

Atrous convolutions for multi-scale context.

**Key components:**
1. **ASPP (Atrous Spatial Pyramid Pooling)**
   - Parallel atrous convolutions at different rates
   - Captures multi-scale context
   - Rates: 6, 12, 18 typically

2. **Encoder-Decoder**
   - Encoder: Backbone + ASPP
   - Decoder: Upsample with skip connections

```
Image → Backbone → ASPP → Decoder → Segmentation
              ↘    ↗
          Low-level features
```

**Performance:**
- mIoU: 89.0 on Cityscapes
- Inference: ~25ms (ResNet-50)

#### SegFormer

Transformer-based semantic segmentation.

**Architecture:**
1. **Hierarchical Transformer Encoder**
   - Multi-scale feature maps
   - Efficient self-attention
   - Overlapping patch embedding

2. **MLP Decoder**
   - Simple MLP aggregation
   - No complex decoders needed

**Benefits:**
- No positional encoding needed
- Efficient attention mechanism
- Strong multi-scale features

### Promptable Segmentation

#### SAM (Segment Anything Model)

Zero-shot segmentation with prompts.

**Architecture:**
1. **Image Encoder**: ViT-H (632M params)
2. **Prompt Encoder**: Points, boxes, masks, text
3. **Mask Decoder**: Lightweight transformer

**Prompts supported:**
- Points (foreground/background)
- Bounding boxes
- Rough masks
- Text (via CLIP integration)

**Usage patterns:**
```python
# Point prompt
masks = sam.predict(image, point_coords=[[500, 375]], point_labels=[1])

# Box prompt
masks = sam.predict(image, box=[100, 100, 400, 400])

# Multiple points
masks = sam.predict(image, point_coords=[[500, 375], [200, 300]],
                   point_labels=[1, 0])  # 1=foreground, 0=background
```

---

## Vision Transformers

### ViT (Vision Transformer)

Original vision transformer architecture.

**Architecture:**

```
Image → Patch Embedding → [CLS] + Position Embedding
                              ↓
                    Transformer Encoder ×L
                              ↓
                         [CLS] token
                              ↓
                     Classification Head
```

**Key details:**
- Patch size: 16×16 or 14×14 typically
- Position embeddings: Learned 1D
- [CLS] token for classification
- Standard transformer encoder blocks

**Variants:**

| Model | Patch | Layers | Hidden | Heads | Params |
|-------|-------|--------|--------|-------|--------|
| ViT-Ti | 16 | 12 | 192 | 3 | 5.7M |
| ViT-S | 16 | 12 | 384 | 6 | 22M |
| ViT-B | 16 | 12 | 768 | 12 | 86M |
| ViT-L | 16 | 24 | 1024 | 16 | 304M |
| ViT-H | 14 | 32 | 1280 | 16 | 632M |

### DeiT (Data-efficient Image Transformers)

Training ViT without massive datasets.

**Key innovations:**
- Knowledge distillation from CNN teachers
- Strong data augmentation
- Regularization (stochastic depth, label smoothing)
- Distillation token (learns from teacher)

**Training recipe:**
- RandAugment
- Mixup (α=0.8)
- CutMix (α=1.0)
- Random erasing (p=0.25)
- Stochastic depth (p=0.1)

### Swin Transformer

Hierarchical transformer with shifted windows.

**Key innovations:**
1. **Shifted Window Attention**
   - Local attention within windows
   - Cross-window connection via shifting
   - O(n) complexity vs O(n²) for global attention

2. **Hierarchical Feature Maps**
   - Patch merging between stages
   - Similar to CNN feature pyramids
   - Direct use in detection/segmentation

**Architecture:**

```
Stage 1: 56×56, 96-dim   → Patch Merge
Stage 2: 28×28, 192-dim  → Patch Merge
Stage 3: 14×14, 384-dim  → Patch Merge
Stage 4: 7×7, 768-dim
```

**Variants:**

| Model | Params | GFLOPs | Top-1 |
|-------|--------|--------|-------|
| Swin-T | 29M | 4.5 | 81.3% |
| Swin-S | 50M | 8.7 | 83.0% |
| Swin-B | 88M | 15.4 | 83.5% |
| Swin-L | 197M | 34.5 | 84.5% |

---

## Feature Pyramid Networks

FPN variants for multi-scale detection.

### Original FPN

Top-down pathway with lateral connections.

```
P5 ← C5 (1/32)
 ↓
P4 ← C4 + Upsample(P5) (1/16)
 ↓
P3 ← C3 + Upsample(P4) (1/8)
 ↓
P2 ← C2 + Upsample(P3) (1/4)
```

### PANet (Path Aggregation Network)

Bottom-up augmentation after FPN.

```
FPN top-down → Bottom-up augmentation
P2 → N2 ↘
P3 → N3 → N3 ↘
P4 → N4 → N4 → N4 ↘
P5 → N5 → N5 → N5 → N5
```

**Benefits:**
- Shorter path from low-level to high-level
- Better localization signals
- +1-2 mAP improvement

### BiFPN (Bidirectional FPN)

Weighted bidirectional feature fusion.

**Key innovations:**
- Learnable fusion weights
- Bidirectional cross-scale connections
- Repeated blocks for iterative refinement

**Fusion formula:**
```
O = Σ(w_i × I_i) / (ε + Σ w_i)
```

Where weights are learned via fast normalized fusion.

### NAS-FPN

Neural architecture search for FPN design.

**Searched on COCO:**
- 7 fusion cells
- Optimized connection patterns
- 3-4 mAP improvement over FPN

---

## Architecture Selection

### Decision Matrix

| Requirement | Recommended | Alternative |
|-------------|-------------|-------------|
| Real-time (>30 FPS) | YOLOv8s | RT-DETR-S |
| Edge (<4GB RAM) | YOLOv8n | MobileNetV3-SSD |
| High accuracy | DINO, Cascade R-CNN | YOLOv8x |
| Instance segmentation | Mask R-CNN | YOLOv8-seg |
| Semantic segmentation | SegFormer | DeepLabV3+ |
| Zero-shot | SAM | CLIP+segmentation |
| Small objects | YOLO+SAHI | Cascade R-CNN |
| Video real-time | YOLOv8 + ByteTrack | YOLOX + SORT |

### Training Data Requirements

| Architecture | Minimum Images | Recommended |
|--------------|----------------|-------------|
| YOLO (fine-tune) | 100-500 | 1,000-5,000 |
| YOLO (from scratch) | 5,000+ | 10,000+ |
| Faster R-CNN | 1,000+ | 5,000+ |
| DETR/DINO | 10,000+ | 50,000+ |
| ViT backbone | 10,000+ | 100,000+ |
| SAM (fine-tune) | 100-1,000 | 5,000+ |

### Compute Requirements

| Architecture | Training GPU | Inference GPU |
|--------------|--------------|---------------|
| YOLOv8n | 4GB VRAM | 2GB VRAM |
| YOLOv8m | 8GB VRAM | 4GB VRAM |
| YOLOv8x | 16GB VRAM | 8GB VRAM |
| Faster R-CNN R50 | 8GB VRAM | 4GB VRAM |
| Mask R-CNN R101 | 16GB VRAM | 8GB VRAM |
| DINO-4scale | 32GB VRAM | 16GB VRAM |
| SAM ViT-H | 32GB VRAM | 8GB VRAM |

---

## Code Examples

### Load Pretrained Backbone (timm)

```python
import timm

# List available models
print(timm.list_models('*resnet*'))

# Load pretrained
backbone = timm.create_model('resnet50', pretrained=True, features_only=True)

# Get feature maps
features = backbone(torch.randn(1, 3, 224, 224))
for f in features:
    print(f.shape)
# torch.Size([1, 64, 56, 56])
# torch.Size([1, 256, 56, 56])
# torch.Size([1, 512, 28, 28])
# torch.Size([1, 1024, 14, 14])
# torch.Size([1, 2048, 7, 7])
```

### Custom Detection Backbone

```python
import torch.nn as nn
from torchvision.models import resnet50
from torchvision.ops import FeaturePyramidNetwork

class DetectionBackbone(nn.Module):
    def __init__(self):
        super().__init__()
        backbone = resnet50(pretrained=True)

        self.layer1 = nn.Sequential(backbone.conv1, backbone.bn1,
                                     backbone.relu, backbone.maxpool,
                                     backbone.layer1)
        self.layer2 = backbone.layer2
        self.layer3 = backbone.layer3
        self.layer4 = backbone.layer4

        self.fpn = FeaturePyramidNetwork(
            in_channels_list=[256, 512, 1024, 2048],
            out_channels=256
        )

    def forward(self, x):
        c1 = self.layer1(x)
        c2 = self.layer2(c1)
        c3 = self.layer3(c2)
        c4 = self.layer4(c3)

        features = {'feat0': c1, 'feat1': c2, 'feat2': c3, 'feat3': c4}
        pyramid = self.fpn(features)
        return pyramid
```

### Vision Transformer with Detection Head

```python
import timm

# Swin Transformer for detection
swin = timm.create_model('swin_base_patch4_window7_224',
                          pretrained=True,
                          features_only=True,
                          out_indices=[0, 1, 2, 3])

# Get multi-scale features
x = torch.randn(1, 3, 224, 224)
features = swin(x)
for i, f in enumerate(features):
    print(f"Stage {i}: {f.shape}")
# Stage 0: torch.Size([1, 128, 56, 56])
# Stage 1: torch.Size([1, 256, 28, 28])
# Stage 2: torch.Size([1, 512, 14, 14])
# Stage 3: torch.Size([1, 1024, 7, 7])
```

---

## Resources

- [torchvision models](https://pytorch.org/vision/stable/models.html)
- [timm library](https://github.com/huggingface/pytorch-image-models)
- [Detectron2 Model Zoo](https://github.com/facebookresearch/detectron2/blob/main/MODEL_ZOO.md)
- [MMDetection Model Zoo](https://github.com/open-mmlab/mmdetection/blob/main/docs/en/model_zoo.md)
- [Ultralytics YOLOv8](https://docs.ultralytics.com/)
