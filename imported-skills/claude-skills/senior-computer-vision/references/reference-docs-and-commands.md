# senior-computer-vision reference

## Reference Documentation

### 1. Computer Vision Architectures

See `references/computer_vision_architectures.md` for:

- CNN backbone architectures (ResNet, EfficientNet, ConvNeXt)
- Vision Transformer variants (ViT, DeiT, Swin)
- Detection heads (anchor-based vs anchor-free)
- Feature Pyramid Networks (FPN, BiFPN, PANet)
- Neck architectures for multi-scale detection

### 2. Object Detection Optimization

See `references/object_detection_optimization.md` for:

- Non-Maximum Suppression variants (NMS, Soft-NMS, DIoU-NMS)
- Anchor optimization and anchor-free alternatives
- Loss function design (focal loss, GIoU, CIoU, DIoU)
- Training strategies (warmup, cosine annealing, EMA)
- Data augmentation for detection (mosaic, mixup, copy-paste)

### 3. Production Vision Systems

See `references/production_vision_systems.md` for:

- ONNX export and optimization
- TensorRT deployment pipeline
- Batch inference optimization
- Edge device deployment (Jetson, Intel NCS)
- Model serving with Triton
- Video processing pipelines

## Common Commands

### Ultralytics YOLO

```bash
# Training
yolo detect train data=coco.yaml model=yolov8m.pt epochs=100 imgsz=640

# Validation
yolo detect val model=best.pt data=coco.yaml

# Inference
yolo detect predict model=best.pt source=images/ save=True

# Export
yolo export model=best.pt format=onnx simplify=True dynamic=True
```

### Detectron2

```bash
# Training
python train_net.py --config-file configs/COCO-Detection/faster_rcnn_R_50_FPN_3x.yaml \
    --num-gpus 1 OUTPUT_DIR ./output

# Evaluation
python train_net.py --config-file configs/faster_rcnn.yaml --eval-only \
    MODEL.WEIGHTS output/model_final.pth

# Inference
python demo.py --config-file configs/faster_rcnn.yaml \
    --input images/*.jpg --output results/ \
    --opts MODEL.WEIGHTS output/model_final.pth
```

### MMDetection

```bash
# Training
python tools/train.py configs/faster_rcnn/faster-rcnn_r50_fpn_1x_coco.py

# Testing
python tools/test.py configs/faster_rcnn.py checkpoints/latest.pth --eval bbox

# Inference
python demo/image_demo.py demo.jpg configs/faster_rcnn.py checkpoints/latest.pth
```

### Model Optimization

```bash
# ONNX export and simplify
python -c "import torch; model = torch.load('model.pt'); torch.onnx.export(model, torch.randn(1,3,640,640), 'model.onnx', opset_version=17)"
python -m onnxsim model.onnx model_sim.onnx

# TensorRT conversion
trtexec --onnx=model.onnx --saveEngine=model.engine --fp16 --workspace=4096

# Benchmark
trtexec --loadEngine=model.engine --batch=1 --iterations=1000 --avgRuns=100
```
