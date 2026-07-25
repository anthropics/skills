# Object Detection Optimization

Comprehensive guide to optimizing object detection models for accuracy and inference speed.

## Table of Contents

- [Non-Maximum Suppression](#non-maximum-suppression)
- [Anchor Design and Optimization](#anchor-design-and-optimization)
- [Loss Functions](#loss-functions)
- [Training Strategies](#training-strategies)
- [Data Augmentation](#data-augmentation)
- [Model Optimization Techniques](#model-optimization-techniques)
- [Hyperparameter Tuning](#hyperparameter-tuning)

---

## Non-Maximum Suppression

NMS removes redundant overlapping detections to produce final predictions.

### Standard NMS

Basic algorithm:
1. Sort boxes by confidence score
2. Select highest confidence box
3. Remove boxes with IoU > threshold
4. Repeat until no boxes remain

```python
def nms(boxes, scores, iou_threshold=0.5):
    """
    boxes: (N, 4) in format [x1, y1, x2, y2]
    scores: (N,)
    """
    order = scores.argsort()[::-1]
    keep = []

    while len(order) > 0:
        i = order[0]
        keep.append(i)

        if len(order) == 1:
            break

        # Calculate IoU with remaining boxes
        ious = compute_iou(boxes[i], boxes[order[1:]])

        # Keep boxes with IoU <= threshold
        mask = ious <= iou_threshold
        order = order[1:][mask]

    return keep
```

**Parameters:**
- `iou_threshold`: 0.5-0.7 typical (lower = more suppression)
- `score_threshold`: 0.25-0.5 (filter low-confidence first)

### Soft-NMS

Reduces scores instead of removing boxes entirely.

**Formula:**
```
score = score * exp(-IoU^2 / sigma)
```

**Benefits:**
- Better for overlapping objects
- +1-2% mAP improvement
- Slightly slower than hard NMS

```python
def soft_nms(boxes, scores, sigma=0.5, score_threshold=0.001):
    """Gaussian penalty soft-NMS"""
    order = scores.argsort()[::-1]
    keep = []

    while len(order) > 0:
        i = order[0]
        keep.append(i)

        if len(order) == 1:
            break

        ious = compute_iou(boxes[i], boxes[order[1:]])

        # Gaussian penalty
        weights = np.exp(-ious**2 / sigma)
        scores[order[1:]] *= weights

        # Re-sort by updated scores
        mask = scores[order[1:]] > score_threshold
        order = order[1:][mask]
        order = order[scores[order].argsort()[::-1]]

    return keep
```

### DIoU-NMS

Uses Distance-IoU instead of standard IoU.

**Formula:**
```
DIoU = IoU - (d^2 / c^2)
```

Where:
- d = center distance between boxes
- c = diagonal of smallest enclosing box

**Benefits:**
- Better for occluded objects
- Penalizes distant boxes less
- Works well with DIoU loss

### Batched NMS

NMS per class (prevents cross-class suppression).

```python
def batched_nms(boxes, scores, classes, iou_threshold):
    """Per-class NMS"""
    # Offset boxes by class ID to prevent cross-class suppression
    max_coordinate = boxes.max()
    offsets = classes * (max_coordinate + 1)
    boxes_for_nms = boxes + offsets[:, None]

    keep = torchvision.ops.nms(boxes_for_nms, scores, iou_threshold)
    return keep
```

### NMS-Free Detection (DETR-style)

Transformer-based detectors eliminate NMS.

**How DETR avoids NMS:**
- Object queries are learned embeddings
- Bipartite matching in training
- Each query outputs exactly one detection
- Set-based loss enforces uniqueness

**Benefits:**
- End-to-end differentiable
- No hand-crafted post-processing
- Better for complex scenes

---

## Anchor Design and Optimization

### Anchor-Based Detection

Traditional detectors use predefined anchor boxes.

**Anchor parameters:**
- Scales: [32, 64, 128, 256, 512] pixels
- Ratios: [0.5, 1.0, 2.0] (height/width)
- Stride: Feature map stride (8, 16, 32)

**Anchor assignment:**
- Positive: IoU > 0.7 with ground truth
- Negative: IoU < 0.3 with all ground truths
- Ignored: 0.3 < IoU < 0.7

### K-Means Anchor Clustering

Optimize anchors for your dataset.

```python
import numpy as np
from sklearn.cluster import KMeans

def optimize_anchors(annotations, num_anchors=9, image_size=640):
    """
    annotations: list of (width, height) for each bounding box
    """
    # Normalize to input size
    boxes = np.array(annotations)
    boxes = boxes / boxes.max() * image_size

    # K-means clustering
    kmeans = KMeans(n_clusters=num_anchors, random_state=42)
    kmeans.fit(boxes)

    # Get anchor sizes
    anchors = kmeans.cluster_centers_

    # Sort by area
    areas = anchors[:, 0] * anchors[:, 1]
    anchors = anchors[np.argsort(areas)]

    # Calculate mean IoU with ground truth
    mean_iou = calculate_anchor_fit(boxes, anchors)
    print(f"Optimized anchors (mean IoU: {mean_iou:.3f}):")
    print(anchors.astype(int))

    return anchors

def calculate_anchor_fit(boxes, anchors):
    """Calculate how well anchors fit the boxes"""
    ious = []
    for box in boxes:
        box_area = box[0] * box[1]
        anchor_areas = anchors[:, 0] * anchors[:, 1]
        intersections = np.minimum(box[0], anchors[:, 0]) * \
                       np.minimum(box[1], anchors[:, 1])
        unions = box_area + anchor_areas - intersections
        max_iou = (intersections / unions).max()
        ious.append(max_iou)
    return np.mean(ious)
```

### Anchor-Free Detection

Modern detectors predict boxes without anchors.

**FCOS-style (center-based):**
- Predict (l, t, r, b) distances from center
- Centerness score for quality
- Multi-scale assignment

**YOLO v8 style:**
- Predict (x, y, w, h) directly
- Task-aligned assigner
- Distribution focal loss for regression

**Benefits of anchor-free:**
- No hyperparameter tuning for anchors
- Simpler architecture
- Better generalization

### Anchor Assignment Strategies

**ATSS (Adaptive Training Sample Selection):**
1. For each GT, select k closest anchors per level
2. Calculate IoU for selected anchors
3. IoU threshold = mean + std of IoUs
4. Assign positives where IoU > threshold

**TAL (Task-Aligned Assigner - YOLO v8):**
```
score = cls_score^alpha * IoU^beta
```

Where alpha=0.5, beta=6.0 (weights classification and localization)

---

## Loss Functions

### Classification Losses

#### Cross-Entropy Loss

Standard multi-class classification:
```python
loss = -log(p_correct_class)
```

#### Focal Loss

Handles class imbalance by down-weighting easy examples.

```python
def focal_loss(pred, target, gamma=2.0, alpha=0.25):
    """
    pred: (N, num_classes) predicted probabilities
    target: (N,) ground truth class indices
    """
    ce_loss = F.cross_entropy(pred, target, reduction='none')
    pt = torch.exp(-ce_loss)  # probability of correct class

    # Focal term: (1 - pt)^gamma
    focal_term = (1 - pt) ** gamma

    # Alpha weighting
    alpha_t = alpha * target + (1 - alpha) * (1 - target)

    loss = alpha_t * focal_term * ce_loss
    return loss.mean()
```

**Hyperparameters:**
- gamma: 2.0 typical, higher = more focus on hard examples
- alpha: 0.25 for foreground class weight

#### Quality Focal Loss (QFL)

Combines classification with IoU quality.

```python
def quality_focal_loss(pred, target, beta=2.0):
    """
    target: IoU values (0-1) instead of binary
    """
    ce = F.binary_cross_entropy(pred, target, reduction='none')
    focal_weight = torch.abs(pred - target) ** beta
    loss = focal_weight * ce
    return loss.mean()
```

### Regression Losses

#### Smooth L1 Loss

```python
def smooth_l1_loss(pred, target, beta=1.0):
    diff = torch.abs(pred - target)
    loss = torch.where(
        diff < beta,
        0.5 * diff ** 2 / beta,
        diff - 0.5 * beta
    )
    return loss.mean()
```

#### IoU-Based Losses

**IoU Loss:**
```
L_IoU = 1 - IoU
```

**GIoU (Generalized IoU):**
```
GIoU = IoU - (C - U) / C
L_GIoU = 1 - GIoU
```

Where C = area of smallest enclosing box, U = union area.

**DIoU (Distance IoU):**
```
DIoU = IoU - d^2 / c^2
L_DIoU = 1 - DIoU
```

Where d = center distance, c = diagonal of enclosing box.

**CIoU (Complete IoU):**
```
CIoU = IoU - d^2 / c^2 - alpha*v
v = (4/pi^2) * (arctan(w_gt/h_gt) - arctan(w/h))^2
alpha = v / (1 - IoU + v)
L_CIoU = 1 - CIoU
```

**Comparison:**

| Loss | Handles | Best For |
|------|---------|----------|
| L1/L2 | Basic regression | Simple tasks |
| IoU | Overlap | Standard detection |
| GIoU | Non-overlapping | Distant boxes |
| DIoU | Center distance | Faster convergence |
| CIoU | Aspect ratio | Best accuracy |

```python
def ciou_loss(pred_boxes, target_boxes):
    """
    pred_boxes, target_boxes: (N, 4) as [x1, y1, x2, y2]
    """
    # Standard IoU
    inter = compute_intersection(pred_boxes, target_boxes)
    union = compute_union(pred_boxes, target_boxes)
    iou = inter / (union + 1e-7)

    # Enclosing box diagonal
    enclose_x1 = torch.min(pred_boxes[:, 0], target_boxes[:, 0])
    enclose_y1 = torch.min(pred_boxes[:, 1], target_boxes[:, 1])
    enclose_x2 = torch.max(pred_boxes[:, 2], target_boxes[:, 2])
    enclose_y2 = torch.max(pred_boxes[:, 3], target_boxes[:, 3])
    c_sq = (enclose_x2 - enclose_x1)**2 + (enclose_y2 - enclose_y1)**2

    # Center distance
    pred_cx = (pred_boxes[:, 0] + pred_boxes[:, 2]) / 2
    pred_cy = (pred_boxes[:, 1] + pred_boxes[:, 3]) / 2
    target_cx = (target_boxes[:, 0] + target_boxes[:, 2]) / 2
    target_cy = (target_boxes[:, 1] + target_boxes[:, 3]) / 2
    d_sq = (pred_cx - target_cx)**2 + (pred_cy - target_cy)**2

    # Aspect ratio term
    pred_w = pred_boxes[:, 2] - pred_boxes[:, 0]
    pred_h = pred_boxes[:, 3] - pred_boxes[:, 1]
    target_w = target_boxes[:, 2] - target_boxes[:, 0]
    target_h = target_boxes[:, 3] - target_boxes[:, 1]

    v = (4 / math.pi**2) * (
        torch.atan(target_w / target_h) - torch.atan(pred_w / pred_h)
    )**2
    alpha_term = v / (1 - iou + v + 1e-7)

    ciou = iou - d_sq / (c_sq + 1e-7) - alpha_term * v
    return 1 - ciou
```

### Distribution Focal Loss (DFL)

Used in YOLO v8 for regression.

**Concept:**
- Predict distribution over discrete positions
- Each regression target is a soft label
- Allows uncertainty estimation

```python
def dfl_loss(pred_dist, target, reg_max=16):
    """
    pred_dist: (N, reg_max) predicted distribution
    target: (N,) continuous target values (0 to reg_max)
    """
    # Convert continuous target to soft label
    target_left = target.floor().long()
    target_right = target_left + 1
    weight_right = target - target_left.float()
    weight_left = 1 - weight_right

    # Cross-entropy with soft targets
    loss_left = F.cross_entropy(pred_dist, target_left, reduction='none')
    loss_right = F.cross_entropy(pred_dist, target_right.clamp(max=reg_max-1),
                                  reduction='none')

    loss = weight_left * loss_left + weight_right * loss_right
    return loss.mean()
```

---

## Training Strategies

### Learning Rate Schedules

**Warmup:**
```python
# Linear warmup for first N epochs
if epoch < warmup_epochs:
    lr = base_lr * (epoch + 1) / warmup_epochs
```

**Cosine Annealing:**
```python
lr = lr_min + 0.5 * (lr_max - lr_min) * (1 + cos(pi * epoch / total_epochs))
```

**Step Decay:**
```python
# Reduce by factor at milestones
lr = base_lr * (0.1 ** (milestones_passed))
```

**Recommended schedule for detection:**
```python
optimizer = SGD(model.parameters(), lr=0.01, momentum=0.937, weight_decay=0.0005)

scheduler = torch.optim.lr_scheduler.CosineAnnealingLR(
    optimizer,
    T_max=total_epochs,
    eta_min=0.0001
)

# With warmup
warmup_scheduler = torch.optim.lr_scheduler.LinearLR(
    optimizer,
    start_factor=0.1,
    total_iters=warmup_epochs
)

scheduler = torch.optim.lr_scheduler.SequentialLR(
    optimizer,
    schedulers=[warmup_scheduler, scheduler],
    milestones=[warmup_epochs]
)
```

### Exponential Moving Average (EMA)

Smooths model weights for better stability.

```python
class EMA:
    def __init__(self, model, decay=0.9999):
        self.model = model
        self.decay = decay
        self.shadow = {}
        for name, param in model.named_parameters():
            if param.requires_grad:
                self.shadow[name] = param.data.clone()

    def update(self):
        for name, param in self.model.named_parameters():
            if param.requires_grad:
                self.shadow[name] = (
                    self.decay * self.shadow[name] +
                    (1 - self.decay) * param.data
                )

    def apply_shadow(self):
        for name, param in self.model.named_parameters():
            if param.requires_grad:
                param.data.copy_(self.shadow[name])
```

**Usage:**
- Update EMA after each training step
- Use EMA weights for validation/inference
- Decay: 0.9999 typical (higher = slower update)

### Multi-Scale Training

Train with varying input sizes.

```python
# Random size each batch
sizes = [480, 512, 544, 576, 608, 640, 672, 704, 736, 768]
input_size = random.choice(sizes)

# Resize batch to selected size
images = F.interpolate(images, size=input_size, mode='bilinear')
```

**Benefits:**
- Better scale invariance
- +1-2% mAP improvement
- Slower training (variable batch size)

### Gradient Accumulation

Simulate larger batch sizes.

```python
accumulation_steps = 4
optimizer.zero_grad()

for i, (images, targets) in enumerate(dataloader):
    loss = model(images, targets) / accumulation_steps
    loss.backward()

    if (i + 1) % accumulation_steps == 0:
        optimizer.step()
        optimizer.zero_grad()
```

### Mixed Precision Training

Use FP16 for speed and memory.

```python
from torch.cuda.amp import autocast, GradScaler

scaler = GradScaler()

for images, targets in dataloader:
    optimizer.zero_grad()

    with autocast():
        loss = model(images, targets)

    scaler.scale(loss).backward()
    scaler.step(optimizer)
    scaler.update()
```

**Benefits:**
- 2-3x faster training
- 50% memory reduction
- Minimal accuracy loss

---

## Data Augmentation

### Geometric Augmentations

```python
import albumentations as A

geometric = A.Compose([
    A.HorizontalFlip(p=0.5),
    A.Rotate(limit=15, p=0.3),
    A.RandomScale(scale_limit=0.2, p=0.5),
    A.Affine(translate_percent={'x': (-0.1, 0.1), 'y': (-0.1, 0.1)}, p=0.3),
], bbox_params=A.BboxParams(format='coco', label_fields=['class_labels']))
```

### Color Augmentations

```python
color = A.Compose([
    A.RandomBrightnessContrast(brightness_limit=0.2, contrast_limit=0.2, p=0.5),
    A.HueSaturationValue(hue_shift_limit=20, sat_shift_limit=30, val_shift_limit=20, p=0.5),
    A.CLAHE(clip_limit=2.0, p=0.1),
    A.GaussianBlur(blur_limit=3, p=0.1),
    A.GaussNoise(var_limit=(10, 50), p=0.1),
])
```

### Mosaic Augmentation

Combines 4 images into one (YOLO-style).

```python
def mosaic_augmentation(images, labels, input_size=640):
    """
    images: list of 4 images
    labels: list of 4 label arrays
    """
    result_image = np.zeros((input_size, input_size, 3), dtype=np.uint8)
    result_labels = []

    # Random center point
    cx = int(random.uniform(input_size * 0.25, input_size * 0.75))
    cy = int(random.uniform(input_size * 0.25, input_size * 0.75))

    positions = [
        (0, 0, cx, cy),           # top-left
        (cx, 0, input_size, cy),  # top-right
        (0, cy, cx, input_size),  # bottom-left
        (cx, cy, input_size, input_size),  # bottom-right
    ]

    for i, (x1, y1, x2, y2) in enumerate(positions):
        img = images[i]
        h, w = y2 - y1, x2 - x1

        # Resize and place
        img_resized = cv2.resize(img, (w, h))
        result_image[y1:y2, x1:x2] = img_resized

        # Transform labels
        for label in labels[i]:
            # Scale and shift bounding boxes
            new_label = transform_bbox(label, img.shape, (h, w), (x1, y1))
            result_labels.append(new_label)

    return result_image, result_labels
```

### MixUp

Blends two images and labels.

```python
def mixup(image1, labels1, image2, labels2, alpha=0.5):
    """
    alpha: mixing ratio (0.5 = equal blend)
    """
    # Blend images
    mixed_image = (alpha * image1 + (1 - alpha) * image2).astype(np.uint8)

    # Blend labels with soft weights
    labels1_weighted = [(box, cls, alpha) for box, cls in labels1]
    labels2_weighted = [(box, cls, 1-alpha) for box, cls in labels2]

    mixed_labels = labels1_weighted + labels2_weighted
    return mixed_image, mixed_labels
```

### Copy-Paste Augmentation

Paste objects from one image to another.

```python
def copy_paste(background, bg_labels, source, src_labels, src_masks):
    """
    Paste segmented objects onto background
    """
    result = background.copy()

    for mask, label in zip(src_masks, src_labels):
        # Random position
        x_offset = random.randint(0, background.shape[1] - mask.shape[1])
        y_offset = random.randint(0, background.shape[0] - mask.shape[0])

        # Paste with mask
        region = result[y_offset:y_offset+mask.shape[0],
                       x_offset:x_offset+mask.shape[1]]
        region[mask > 0] = source[mask > 0]

        # Add new label
        new_box = transform_bbox(label, x_offset, y_offset)
        bg_labels.append(new_box)

    return result, bg_labels
```

### Cutout / Random Erasing

Randomly erase patches.

```python
def cutout(image, num_holes=8, max_h_size=32, max_w_size=32):
    h, w = image.shape[:2]
    result = image.copy()

    for _ in range(num_holes):
        y = random.randint(0, h)
        x = random.randint(0, w)
        h_size = random.randint(1, max_h_size)
        w_size = random.randint(1, max_w_size)

        y1, y2 = max(0, y - h_size // 2), min(h, y + h_size // 2)
        x1, x2 = max(0, x - w_size // 2), min(w, x + w_size // 2)

        result[y1:y2, x1:x2] = 0  # or random color

    return result
```

---

## Model Optimization Techniques

### Pruning

Remove unimportant weights.

**Magnitude Pruning:**
```python
import torch.nn.utils.prune as prune

# Prune 30% of weights with smallest magnitude
for name, module in model.named_modules():
    if isinstance(module, nn.Conv2d):
        prune.l1_unstructured(module, name='weight', amount=0.3)
```

**Structured Pruning (channels):**
```python
# Prune entire channels
prune.ln_structured(module, name='weight', amount=0.3, n=2, dim=0)
```

### Knowledge Distillation

Train smaller model with larger teacher.

```python
def distillation_loss(student_logits, teacher_logits, labels,
                      temperature=4.0, alpha=0.7):
    """
    Combine soft targets from teacher with hard labels
    """
    # Soft targets
    soft_student = F.log_softmax(student_logits / temperature, dim=1)
    soft_teacher = F.softmax(teacher_logits / temperature, dim=1)
    soft_loss = F.kl_div(soft_student, soft_teacher, reduction='batchmean')
    soft_loss *= temperature ** 2  # Scale by T^2

    # Hard targets
    hard_loss = F.cross_entropy(student_logits, labels)

    # Combined loss
    return alpha * soft_loss + (1 - alpha) * hard_loss
```

### Quantization

Reduce precision for faster inference.

**Post-Training Quantization:**
```python
import torch.quantization

# Prepare model
model.set_mode('inference')
model.qconfig = torch.quantization.get_default_qconfig('fbgemm')
torch.quantization.prepare(model, inplace=True)

# Calibrate with representative data
with torch.no_grad():
    for images in calibration_loader:
        model(images)

# Convert to quantized model
torch.quantization.convert(model, inplace=True)
```

**Quantization-Aware Training:**
```python
# Insert fake quantization during training
model.train()
model.qconfig = torch.quantization.get_default_qat_qconfig('fbgemm')
model_prepared = torch.quantization.prepare_qat(model)

# Train with fake quantization
for epoch in range(num_epochs):
    train(model_prepared)

# Convert to quantized
model_quantized = torch.quantization.convert(model_prepared)
```

---

## Hyperparameter Tuning

### Key Hyperparameters

| Parameter | Range | Default | Impact |
|-----------|-------|---------|--------|
| Learning rate | 1e-4 to 1e-1 | 0.01 | Critical |
| Batch size | 4 to 64 | 16 | Memory/speed |
| Weight decay | 1e-5 to 1e-3 | 5e-4 | Regularization |
| Momentum | 0.9 to 0.99 | 0.937 | Optimization |
| Warmup epochs | 1 to 10 | 3 | Stability |
| IoU threshold (NMS) | 0.4 to 0.7 | 0.5 | Recall/precision |
| Confidence threshold | 0.1 to 0.5 | 0.25 | Detection count |
| Image size | 320 to 1280 | 640 | Accuracy/speed |

### Tuning Strategy

1. **Baseline**: Use default hyperparameters
2. **Learning rate**: Grid search [1e-3, 5e-3, 1e-2, 5e-2]
3. **Batch size**: Maximum that fits in memory
4. **Augmentation**: Start minimal, add progressively
5. **Epochs**: Train until validation loss plateaus
6. **NMS threshold**: Tune on validation set

### Automated Hyperparameter Optimization

```python
import optuna

def objective(trial):
    lr = trial.suggest_loguniform('lr', 1e-4, 1e-1)
    weight_decay = trial.suggest_loguniform('weight_decay', 1e-5, 1e-3)
    mosaic_prob = trial.suggest_uniform('mosaic_prob', 0.0, 1.0)

    model = create_model()
    train_model(model, lr=lr, weight_decay=weight_decay, mosaic_prob=mosaic_prob)
    mAP = test_model(model)

    return mAP

study = optuna.create_study(direction='maximize')
study.optimize(objective, n_trials=100)

print(f"Best params: {study.best_params}")
print(f"Best mAP: {study.best_value}")
```

---

## Detection-Specific Tips

### Small Object Detection

1. **Higher resolution**: 1280px instead of 640px
2. **SAHI (Slicing)**: Inference on overlapping tiles
3. **More FPN levels**: P2 level (1/4 scale)
4. **Anchor adjustment**: Smaller anchors for small objects
5. **Copy-paste augmentation**: Increase small object frequency

### Handling Class Imbalance

1. **Focal loss**: gamma=2.0, alpha=0.25
2. **Over-sampling**: Repeat rare class images
3. **Class weights**: Inverse frequency weighting
4. **Copy-paste**: Augment rare classes

### Improving Localization

1. **CIoU loss**: Includes aspect ratio term
2. **Cascade detection**: Progressive refinement
3. **Higher IoU threshold**: 0.6-0.7 for positive samples
4. **Deformable convolutions**: Learn spatial offsets

### Reducing False Positives

1. **Higher confidence threshold**: 0.4-0.5
2. **More negative samples**: Hard negative mining
3. **Background class weight**: Increase penalty
4. **Ensemble**: Multiple model voting

---

## Resources

- [MMDetection training configs](https://github.com/open-mmlab/mmdetection/tree/main/configs)
- [Ultralytics training tips](https://docs.ultralytics.com/guides/hyperparameter-tuning/)
- [Albumentations detection](https://albumentations.ai/docs/getting_started/bounding_boxes_augmentation/)
- [Focal Loss paper](https://arxiv.org/abs/1708.02002)
- [CIoU paper](https://arxiv.org/abs/2005.03572)
