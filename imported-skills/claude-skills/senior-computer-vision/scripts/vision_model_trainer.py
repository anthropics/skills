#!/usr/bin/env python3
"""
Vision Model Trainer Configuration Generator

Generates training configuration files for object detection and segmentation models.
Supports Ultralytics YOLO, Detectron2, and MMDetection frameworks.

Usage:
    python vision_model_trainer.py <data_dir> --task detection --arch yolov8m
    python vision_model_trainer.py <data_dir> --framework detectron2 --arch faster_rcnn_R_50_FPN
"""

import os
import sys
import json
import argparse
import logging
from pathlib import Path
from typing import Dict, List, Optional, Any
from datetime import datetime

logging.basicConfig(
    level=logging.INFO,
    format='%(asctime)s - %(levelname)s - %(message)s'
)
logger = logging.getLogger(__name__)


# Architecture configurations
YOLO_ARCHITECTURES = {
    'yolov8n': {'params': '3.2M', 'gflops': 8.7, 'map': 37.3},
    'yolov8s': {'params': '11.2M', 'gflops': 28.6, 'map': 44.9},
    'yolov8m': {'params': '25.9M', 'gflops': 78.9, 'map': 50.2},
    'yolov8l': {'params': '43.7M', 'gflops': 165.2, 'map': 52.9},
    'yolov8x': {'params': '68.2M', 'gflops': 257.8, 'map': 53.9},
    'yolov5n': {'params': '1.9M', 'gflops': 4.5, 'map': 28.0},
    'yolov5s': {'params': '7.2M', 'gflops': 16.5, 'map': 37.4},
    'yolov5m': {'params': '21.2M', 'gflops': 49.0, 'map': 45.4},
    'yolov5l': {'params': '46.5M', 'gflops': 109.1, 'map': 49.0},
    'yolov5x': {'params': '86.7M', 'gflops': 205.7, 'map': 50.7},
}

DETECTRON2_ARCHITECTURES = {
    'faster_rcnn_R_50_FPN': {'backbone': 'R-50-FPN', 'map': 37.9},
    'faster_rcnn_R_101_FPN': {'backbone': 'R-101-FPN', 'map': 39.4},
    'faster_rcnn_X_101_FPN': {'backbone': 'X-101-FPN', 'map': 41.0},
    'mask_rcnn_R_50_FPN': {'backbone': 'R-50-FPN', 'map': 38.6},
    'mask_rcnn_R_101_FPN': {'backbone': 'R-101-FPN', 'map': 40.0},
    'retinanet_R_50_FPN': {'backbone': 'R-50-FPN', 'map': 36.4},
    'retinanet_R_101_FPN': {'backbone': 'R-101-FPN', 'map': 37.7},
}

MMDETECTION_ARCHITECTURES = {
    'faster_rcnn_r50_fpn': {'backbone': 'ResNet50', 'map': 37.4},
    'faster_rcnn_r101_fpn': {'backbone': 'ResNet101', 'map': 39.4},
    'mask_rcnn_r50_fpn': {'backbone': 'ResNet50', 'map': 38.2},
    'yolox_s': {'backbone': 'CSPDarknet', 'map': 40.5},
    'yolox_m': {'backbone': 'CSPDarknet', 'map': 46.9},
    'yolox_l': {'backbone': 'CSPDarknet', 'map': 49.7},
    'detr_r50': {'backbone': 'ResNet50', 'map': 42.0},
    'dino_r50': {'backbone': 'ResNet50', 'map': 49.0},
}


class VisionModelTrainer:
    """Generates training configurations for vision models."""

    def __init__(self, data_dir: str, task: str = 'detection',
                 framework: str = 'ultralytics'):
        self.data_dir = Path(data_dir)
        self.task = task
        self.framework = framework
        self.config = {}

    def analyze_dataset(self) -> Dict[str, Any]:
        """Analyze dataset structure and statistics."""
        logger.info(f"Analyzing dataset at {self.data_dir}")

        analysis = {
            'path': str(self.data_dir),
            'exists': self.data_dir.exists(),
            'images': {'train': 0, 'val': 0, 'test': 0},
            'annotations': {'format': None, 'classes': []},
            'recommendations': []
        }

        if not self.data_dir.exists():
            analysis['recommendations'].append(
                f"Directory {self.data_dir} does not exist"
            )
            return analysis

        # Check for common dataset structures
        # COCO format
        if (self.data_dir / 'annotations').exists():
            analysis['annotations']['format'] = 'coco'
            for split in ['train', 'val', 'test']:
                ann_file = self.data_dir / 'annotations' / f'{split}.json'
                if ann_file.exists():
                    with open(ann_file, 'r') as f:
                        data = json.load(f)
                        analysis['images'][split] = len(data.get('images', []))
                        if not analysis['annotations']['classes']:
                            analysis['annotations']['classes'] = [
                                c['name'] for c in data.get('categories', [])
                            ]

        # YOLO format
        elif (self.data_dir / 'labels').exists():
            analysis['annotations']['format'] = 'yolo'
            for split in ['train', 'val', 'test']:
                img_dir = self.data_dir / 'images' / split
                if img_dir.exists():
                    analysis['images'][split] = len(list(img_dir.glob('*.*')))

            # Try to read classes from data.yaml
            data_yaml = self.data_dir / 'data.yaml'
            if data_yaml.exists():
                import yaml
                with open(data_yaml, 'r') as f:
                    data = yaml.safe_load(f)
                    analysis['annotations']['classes'] = data.get('names', [])

        # Generate recommendations
        total_images = sum(analysis['images'].values())
        if total_images < 100:
            analysis['recommendations'].append(
                f"Dataset has only {total_images} images. "
                "Consider collecting more data or using transfer learning."
            )
        if total_images < 1000:
            analysis['recommendations'].append(
                "Use aggressive data augmentation (mosaic, mixup) for small datasets."
            )

        num_classes = len(analysis['annotations']['classes'])
        if num_classes > 80:
            analysis['recommendations'].append(
                f"Large number of classes ({num_classes}). "
                "Consider using larger model (yolov8l/x) or longer training."
            )

        logger.info(f"Found {total_images} images, {num_classes} classes")
        return analysis

    def generate_yolo_config(self, arch: str, epochs: int = 100,
                             batch: int = 16, imgsz: int = 640,
                             **kwargs) -> Dict[str, Any]:
        """Generate Ultralytics YOLO training configuration."""
        if arch not in YOLO_ARCHITECTURES:
            available = ', '.join(YOLO_ARCHITECTURES.keys())
            raise ValueError(f"Unknown architecture: {arch}. Available: {available}")

        arch_info = YOLO_ARCHITECTURES[arch]

        config = {
            'model': f'{arch}.pt',
            'data': str(self.data_dir / 'data.yaml'),
            'epochs': epochs,
            'batch': batch,
            'imgsz': imgsz,
            'patience': 50,
            'save': True,
            'save_period': -1,
            'cache': False,
            'device': '0',
            'workers': 8,
            'project': 'runs/detect',
            'name': f'{arch}_{datetime.now().strftime("%Y%m%d_%H%M%S")}',
            'exist_ok': False,
            'pretrained': True,
            'optimizer': 'auto',
            'verbose': True,
            'seed': 0,
            'deterministic': True,
            'single_cls': False,
            'rect': False,
            'cos_lr': False,
            'close_mosaic': 10,
            'resume': False,
            'amp': True,
            'fraction': 1.0,
            'profile': False,
            'freeze': None,
            'lr0': 0.01,
            'lrf': 0.01,
            'momentum': 0.937,
            'weight_decay': 0.0005,
            'warmup_epochs': 3.0,
            'warmup_momentum': 0.8,
            'warmup_bias_lr': 0.1,
            'box': 7.5,
            'cls': 0.5,
            'dfl': 1.5,
            'pose': 12.0,
            'kobj': 1.0,
            'label_smoothing': 0.0,
            'nbs': 64,
            'hsv_h': 0.015,
            'hsv_s': 0.7,
            'hsv_v': 0.4,
            'degrees': 0.0,
            'translate': 0.1,
            'scale': 0.5,
            'shear': 0.0,
            'perspective': 0.0,
            'flipud': 0.0,
            'fliplr': 0.5,
            'bgr': 0.0,
            'mosaic': 1.0,
            'mixup': 0.0,
            'copy_paste': 0.0,
            'auto_augment': 'randaugment',
            'erasing': 0.4,
            'crop_fraction': 1.0,
        }

        # Update with user overrides
        config.update(kwargs)

        # Task-specific settings
        if self.task == 'segmentation':
            config['model'] = f'{arch}-seg.pt'
            config['overlap_mask'] = True
            config['mask_ratio'] = 4

        # Metadata
        config['_metadata'] = {
            'architecture': arch,
            'arch_info': arch_info,
            'task': self.task,
            'framework': 'ultralytics',
            'generated_at': datetime.now().isoformat()
        }

        self.config = config
        return config

    def generate_detectron2_config(self, arch: str, epochs: int = 12,
                                   batch: int = 16, **kwargs) -> Dict[str, Any]:
        """Generate Detectron2 training configuration."""
        if arch not in DETECTRON2_ARCHITECTURES:
            available = ', '.join(DETECTRON2_ARCHITECTURES.keys())
            raise ValueError(f"Unknown architecture: {arch}. Available: {available}")

        arch_info = DETECTRON2_ARCHITECTURES[arch]
        iterations = epochs * 1000  # Approximate

        config = {
            'MODEL': {
                'WEIGHTS': f'detectron2://COCO-Detection/{arch}_3x/137849458/model_final_280758.pkl',
                'ROI_HEADS': {
                    'NUM_CLASSES': len(self._get_classes()),
                    'BATCH_SIZE_PER_IMAGE': 512,
                    'POSITIVE_FRACTION': 0.25,
                    'SCORE_THRESH_TEST': 0.05,
                    'NMS_THRESH_TEST': 0.5,
                },
                'BACKBONE': {
                    'FREEZE_AT': 2
                },
                'FPN': {
                    'IN_FEATURES': ['res2', 'res3', 'res4', 'res5']
                },
                'ANCHOR_GENERATOR': {
                    'SIZES': [[32], [64], [128], [256], [512]],
                    'ASPECT_RATIOS': [[0.5, 1.0, 2.0]]
                },
                'RPN': {
                    'PRE_NMS_TOPK_TRAIN': 2000,
                    'PRE_NMS_TOPK_TEST': 1000,
                    'POST_NMS_TOPK_TRAIN': 1000,
                    'POST_NMS_TOPK_TEST': 1000,
                }
            },
            'DATASETS': {
                'TRAIN': ('custom_train',),
                'TEST': ('custom_val',),
            },
            'DATALOADER': {
                'NUM_WORKERS': 4,
                'SAMPLER_TRAIN': 'TrainingSampler',
                'FILTER_EMPTY_ANNOTATIONS': True,
            },
            'SOLVER': {
                'IMS_PER_BATCH': batch,
                'BASE_LR': 0.001,
                'STEPS': (int(iterations * 0.7), int(iterations * 0.9)),
                'MAX_ITER': iterations,
                'WARMUP_FACTOR': 1.0 / 1000,
                'WARMUP_ITERS': 1000,
                'WARMUP_METHOD': 'linear',
                'GAMMA': 0.1,
                'MOMENTUM': 0.9,
                'WEIGHT_DECAY': 0.0001,
                'WEIGHT_DECAY_NORM': 0.0,
                'CHECKPOINT_PERIOD': 5000,
                'AMP': {
                    'ENABLED': True
                }
            },
            'INPUT': {
                'MIN_SIZE_TRAIN': (640, 672, 704, 736, 768, 800),
                'MAX_SIZE_TRAIN': 1333,
                'MIN_SIZE_TEST': 800,
                'MAX_SIZE_TEST': 1333,
                'FORMAT': 'BGR',
            },
            'TEST': {
                'EVAL_PERIOD': 5000,
                'DETECTIONS_PER_IMAGE': 100,
            },
            'OUTPUT_DIR': f'./output/{arch}_{datetime.now().strftime("%Y%m%d_%H%M%S")}',
        }

        # Add mask head for instance segmentation
        if 'mask' in arch.lower():
            config['MODEL']['MASK_ON'] = True
            config['MODEL']['ROI_MASK_HEAD'] = {
                'POOLER_RESOLUTION': 14,
                'POOLER_SAMPLING_RATIO': 0,
                'POOLER_TYPE': 'ROIAlignV2'
            }

        config.update(kwargs)
        config['_metadata'] = {
            'architecture': arch,
            'arch_info': arch_info,
            'task': self.task,
            'framework': 'detectron2',
            'generated_at': datetime.now().isoformat()
        }

        self.config = config
        return config

    def generate_mmdetection_config(self, arch: str, epochs: int = 12,
                                    batch: int = 16, **kwargs) -> Dict[str, Any]:
        """Generate MMDetection training configuration."""
        if arch not in MMDETECTION_ARCHITECTURES:
            available = ', '.join(MMDETECTION_ARCHITECTURES.keys())
            raise ValueError(f"Unknown architecture: {arch}. Available: {available}")

        arch_info = MMDETECTION_ARCHITECTURES[arch]

        config = {
            '_base_': [
                f'../_base_/models/{arch}.py',
                '../_base_/datasets/coco_detection.py',
                '../_base_/schedules/schedule_1x.py',
                '../_base_/default_runtime.py'
            ],
            'model': {
                'roi_head': {
                    'bbox_head': {
                        'num_classes': len(self._get_classes())
                    }
                }
            },
            'data': {
                'samples_per_gpu': batch // 2,
                'workers_per_gpu': 4,
                'train': {
                    'type': 'CocoDataset',
                    'ann_file': str(self.data_dir / 'annotations' / 'train.json'),
                    'img_prefix': str(self.data_dir / 'images' / 'train'),
                },
                'val': {
                    'type': 'CocoDataset',
                    'ann_file': str(self.data_dir / 'annotations' / 'val.json'),
                    'img_prefix': str(self.data_dir / 'images' / 'val'),
                },
                'test': {
                    'type': 'CocoDataset',
                    'ann_file': str(self.data_dir / 'annotations' / 'val.json'),
                    'img_prefix': str(self.data_dir / 'images' / 'val'),
                }
            },
            'optimizer': {
                'type': 'SGD',
                'lr': 0.02,
                'momentum': 0.9,
                'weight_decay': 0.0001
            },
            'optimizer_config': {
                'grad_clip': {'max_norm': 35, 'norm_type': 2}
            },
            'lr_config': {
                'policy': 'step',
                'warmup': 'linear',
                'warmup_iters': 500,
                'warmup_ratio': 0.001,
                'step': [int(epochs * 0.7), int(epochs * 0.9)]
            },
            'runner': {
                'type': 'EpochBasedRunner',
                'max_epochs': epochs
            },
            'checkpoint_config': {
                'interval': 1
            },
            'log_config': {
                'interval': 50,
                'hooks': [
                    {'type': 'TextLoggerHook'},
                    {'type': 'TensorboardLoggerHook'}
                ]
            },
            'work_dir': f'./work_dirs/{arch}_{datetime.now().strftime("%Y%m%d_%H%M%S")}',
            'load_from': None,
            'resume_from': None,
            'fp16': {'loss_scale': 512.0}
        }

        config.update(kwargs)
        config['_metadata'] = {
            'architecture': arch,
            'arch_info': arch_info,
            'task': self.task,
            'framework': 'mmdetection',
            'generated_at': datetime.now().isoformat()
        }

        self.config = config
        return config

    def _get_classes(self) -> List[str]:
        """Get class names from dataset."""
        analysis = self.analyze_dataset()
        classes = analysis['annotations']['classes']
        if not classes:
            classes = ['object']  # Default fallback
        return classes

    def save_config(self, output_path: str) -> str:
        """Save configuration to file."""
        output_path = Path(output_path)
        output_path.parent.mkdir(parents=True, exist_ok=True)

        if self.framework == 'ultralytics':
            # YOLO uses YAML
            import yaml
            with open(output_path, 'w') as f:
                yaml.dump(self.config, f, default_flow_style=False, sort_keys=False)
        else:
            # Detectron2 and MMDetection use Python configs
            with open(output_path, 'w') as f:
                f.write("# Auto-generated configuration\n")
                f.write(f"# Generated at: {datetime.now().isoformat()}\n\n")
                f.write(f"config = {json.dumps(self.config, indent=2)}\n")

        logger.info(f"Configuration saved to {output_path}")
        return str(output_path)

    def generate_training_command(self) -> str:
        """Generate the training command for the framework."""
        if self.framework == 'ultralytics':
            return f"yolo detect train data={self.config.get('data', 'data.yaml')} " \
                   f"model={self.config.get('model', 'yolov8m.pt')} " \
                   f"epochs={self.config.get('epochs', 100)} " \
                   f"imgsz={self.config.get('imgsz', 640)}"
        elif self.framework == 'detectron2':
            return f"python train_net.py --config-file config.yaml --num-gpus 1"
        elif self.framework == 'mmdetection':
            return f"python tools/train.py config.py"
        return ""

    def print_summary(self):
        """Print configuration summary."""
        meta = self.config.get('_metadata', {})

        print("\n" + "=" * 60)
        print("TRAINING CONFIGURATION SUMMARY")
        print("=" * 60)
        print(f"Framework:     {meta.get('framework', 'unknown')}")
        print(f"Architecture:  {meta.get('architecture', 'unknown')}")
        print(f"Task:          {meta.get('task', 'detection')}")

        if 'arch_info' in meta:
            info = meta['arch_info']
            if 'params' in info:
                print(f"Parameters:    {info['params']}")
            if 'map' in info:
                print(f"COCO mAP:      {info['map']}")

        print("-" * 60)
        print("Training Command:")
        print(f"  {self.generate_training_command()}")
        print("=" * 60 + "\n")


def main():
    parser = argparse.ArgumentParser(
        description="Generate vision model training configurations"
    )
    parser.add_argument('data_dir', help='Path to dataset directory')
    parser.add_argument('--task', choices=['detection', 'segmentation'],
                       default='detection', help='Task type')
    parser.add_argument('--framework', choices=['ultralytics', 'detectron2', 'mmdetection'],
                       default='ultralytics', help='Training framework')
    parser.add_argument('--arch', default='yolov8m',
                       help='Model architecture')
    parser.add_argument('--epochs', type=int, default=100, help='Training epochs')
    parser.add_argument('--batch', type=int, default=16, help='Batch size')
    parser.add_argument('--imgsz', type=int, default=640, help='Image size')
    parser.add_argument('--output', '-o', help='Output config file path')
    parser.add_argument('--analyze-only', action='store_true',
                       help='Only analyze dataset, do not generate config')
    parser.add_argument('--json', action='store_true',
                       help='Output as JSON')

    args = parser.parse_args()

    trainer = VisionModelTrainer(
        data_dir=args.data_dir,
        task=args.task,
        framework=args.framework
    )

    # Analyze dataset
    analysis = trainer.analyze_dataset()

    if args.analyze_only:
        if args.json:
            print(json.dumps(analysis, indent=2))
        else:
            print("\nDataset Analysis:")
            print(f"  Path: {analysis['path']}")
            print(f"  Format: {analysis['annotations']['format']}")
            print(f"  Classes: {len(analysis['annotations']['classes'])}")
            print(f"  Images - Train: {analysis['images']['train']}, "
                  f"Val: {analysis['images']['val']}, "
                  f"Test: {analysis['images']['test']}")
            if analysis['recommendations']:
                print("\nRecommendations:")
                for rec in analysis['recommendations']:
                    print(f"  - {rec}")
        return

    # Generate configuration
    try:
        if args.framework == 'ultralytics':
            config = trainer.generate_yolo_config(
                arch=args.arch,
                epochs=args.epochs,
                batch=args.batch,
                imgsz=args.imgsz
            )
        elif args.framework == 'detectron2':
            config = trainer.generate_detectron2_config(
                arch=args.arch,
                epochs=args.epochs,
                batch=args.batch
            )
        elif args.framework == 'mmdetection':
            config = trainer.generate_mmdetection_config(
                arch=args.arch,
                epochs=args.epochs,
                batch=args.batch
            )
    except ValueError as e:
        logger.error(str(e))
        sys.exit(1)

    # Output
    if args.json:
        print(json.dumps(config, indent=2))
    else:
        trainer.print_summary()

        if args.output:
            trainer.save_config(args.output)


if __name__ == '__main__':
    main()
