# Production Vision Systems

Comprehensive guide to deploying computer vision models in production environments.

## Table of Contents

- [Model Export and Optimization](#model-export-and-optimization)
- [TensorRT Deployment](#tensorrt-deployment)
- [ONNX Runtime Deployment](#onnx-runtime-deployment)
- [Edge Device Deployment](#edge-device-deployment)
- [Model Serving](#model-serving)
- [Video Processing Pipelines](#video-processing-pipelines)
- [Monitoring and Observability](#monitoring-and-observability)
- [Scaling and Performance](#scaling-and-performance)

---

## Model Export and Optimization

### PyTorch to ONNX Export

Basic export:
```python
import torch
import torch.onnx

def export_to_onnx(model, input_shape, output_path, dynamic_batch=True):
    """
    Export PyTorch model to ONNX format.

    Args:
        model: PyTorch model
        input_shape: (C, H, W) input dimensions
        output_path: Path to save .onnx file
        dynamic_batch: Allow variable batch sizes
    """
    model.set_mode('inference')

    # Create dummy input
    dummy_input = torch.randn(1, *input_shape)

    # Dynamic axes for variable batch size
    dynamic_axes = None
    if dynamic_batch:
        dynamic_axes = {
            'input': {0: 'batch_size'},
            'output': {0: 'batch_size'}
        }

    # Export
    torch.onnx.export(
        model,
        dummy_input,
        output_path,
        export_params=True,
        opset_version=17,
        do_constant_folding=True,
        input_names=['input'],
        output_names=['output'],
        dynamic_axes=dynamic_axes
    )

    print(f"Exported to {output_path}")
    return output_path
```

### ONNX Model Optimization

Simplify and optimize ONNX graph:
```python
import onnx
from onnxsim import simplify

def optimize_onnx(input_path, output_path):
    """
    Simplify ONNX model for faster inference.
    """
    # Load model
    model = onnx.load(input_path)

    # Check validity
    onnx.checker.check_model(model)

    # Simplify
    model_simplified, check = simplify(model)

    if check:
        onnx.save(model_simplified, output_path)
        print(f"Simplified model saved to {output_path}")

        # Print size reduction
        import os
        original_size = os.path.getsize(input_path) / 1024 / 1024
        simplified_size = os.path.getsize(output_path) / 1024 / 1024
        print(f"Size: {original_size:.2f}MB -> {simplified_size:.2f}MB")
    else:
        print("Simplification failed, saving original")
        onnx.save(model, output_path)

    return output_path
```

### Model Size Analysis

```python
def analyze_model(model_path):
    """
    Analyze ONNX model structure and size.
    """
    model = onnx.load(model_path)

    # Count parameters
    total_params = 0
    param_sizes = {}

    for initializer in model.graph.initializer:
        param_count = 1
        for dim in initializer.dims:
            param_count *= dim
        total_params += param_count
        param_sizes[initializer.name] = param_count

    # Print summary
    print(f"Total parameters: {total_params:,}")
    print(f"Model size: {total_params * 4 / 1024 / 1024:.2f} MB (FP32)")
    print(f"Model size: {total_params * 2 / 1024 / 1024:.2f} MB (FP16)")
    print(f"Model size: {total_params / 1024 / 1024:.2f} MB (INT8)")

    # Top 10 largest layers
    print("\nLargest layers:")
    sorted_params = sorted(param_sizes.items(), key=lambda x: x[1], reverse=True)
    for name, size in sorted_params[:10]:
        print(f"  {name}: {size:,} params")

    return total_params
```

---

## TensorRT Deployment

### TensorRT Engine Build

```python
import tensorrt as trt

def build_tensorrt_engine(onnx_path, engine_path, precision='fp16',
                          max_batch_size=8, workspace_gb=4):
    """
    Build TensorRT engine from ONNX model.

    Args:
        onnx_path: Path to ONNX model
        engine_path: Path to save TensorRT engine
        precision: 'fp32', 'fp16', or 'int8'
        max_batch_size: Maximum batch size
        workspace_gb: GPU memory workspace in GB
    """
    logger = trt.Logger(trt.Logger.WARNING)
    builder = trt.Builder(logger)
    network = builder.create_network(
        1 << int(trt.NetworkDefinitionCreationFlag.EXPLICIT_BATCH)
    )
    parser = trt.OnnxParser(network, logger)

    # Parse ONNX
    with open(onnx_path, 'rb') as f:
        if not parser.parse(f.read()):
            for error in range(parser.num_errors):
                print(parser.get_error(error))
            raise RuntimeError("ONNX parsing failed")

    # Configure builder
    config = builder.create_builder_config()
    config.set_memory_pool_limit(trt.MemoryPoolType.WORKSPACE,
                                  workspace_gb * 1024 * 1024 * 1024)

    # Set precision
    if precision == 'fp16':
        config.set_flag(trt.BuilderFlag.FP16)
    elif precision == 'int8':
        config.set_flag(trt.BuilderFlag.INT8)
        # Requires calibrator for INT8

    # Set optimization profile for dynamic shapes
    profile = builder.create_optimization_profile()
    input_name = network.get_input(0).name
    input_shape = network.get_input(0).shape

    # Min, optimal, max batch sizes
    min_shape = (1,) + tuple(input_shape[1:])
    opt_shape = (max_batch_size // 2,) + tuple(input_shape[1:])
    max_shape = (max_batch_size,) + tuple(input_shape[1:])

    profile.set_shape(input_name, min_shape, opt_shape, max_shape)
    config.add_optimization_profile(profile)

    # Build engine
    serialized_engine = builder.build_serialized_network(network, config)

    # Save engine
    with open(engine_path, 'wb') as f:
        f.write(serialized_engine)

    print(f"TensorRT engine saved to {engine_path}")
    return engine_path
```

### TensorRT Inference

```python
import numpy as np
import pycuda.driver as cuda
import pycuda.autoinit

class TensorRTInference:
    def __init__(self, engine_path):
        """
        Load TensorRT engine and prepare for inference.
        """
        self.logger = trt.Logger(trt.Logger.WARNING)

        # Load engine
        with open(engine_path, 'rb') as f:
            engine_data = f.read()

        runtime = trt.Runtime(self.logger)
        self.engine = runtime.deserialize_cuda_engine(engine_data)
        self.context = self.engine.create_execution_context()

        # Allocate buffers
        self.inputs = []
        self.outputs = []
        self.bindings = []
        self.stream = cuda.Stream()

        for i in range(self.engine.num_io_tensors):
            name = self.engine.get_tensor_name(i)
            dtype = trt.nptype(self.engine.get_tensor_dtype(name))
            shape = self.engine.get_tensor_shape(name)
            size = trt.volume(shape)

            # Allocate host and device buffers
            host_mem = cuda.pagelocked_empty(size, dtype)
            device_mem = cuda.mem_alloc(host_mem.nbytes)

            self.bindings.append(int(device_mem))

            if self.engine.get_tensor_mode(name) == trt.TensorIOMode.INPUT:
                self.inputs.append({'host': host_mem, 'device': device_mem,
                                   'shape': shape, 'name': name})
            else:
                self.outputs.append({'host': host_mem, 'device': device_mem,
                                    'shape': shape, 'name': name})

    def infer(self, input_data):
        """
        Run inference on input data.

        Args:
            input_data: numpy array (batch, C, H, W)

        Returns:
            Output numpy array
        """
        # Copy input to host buffer
        np.copyto(self.inputs[0]['host'], input_data.ravel())

        # Transfer input to device
        cuda.memcpy_htod_async(
            self.inputs[0]['device'],
            self.inputs[0]['host'],
            self.stream
        )

        # Run inference
        self.context.execute_async_v2(
            bindings=self.bindings,
            stream_handle=self.stream.handle
        )

        # Transfer output from device
        cuda.memcpy_dtoh_async(
            self.outputs[0]['host'],
            self.outputs[0]['device'],
            self.stream
        )

        # Synchronize
        self.stream.synchronize()

        # Reshape output
        output = self.outputs[0]['host'].reshape(self.outputs[0]['shape'])
        return output
```

### INT8 Calibration

```python
class Int8Calibrator(trt.IInt8EntropyCalibrator2):
    def __init__(self, calibration_data, cache_file, batch_size=8):
        """
        INT8 calibrator for TensorRT.

        Args:
            calibration_data: List of numpy arrays
            cache_file: Path to save calibration cache
            batch_size: Calibration batch size
        """
        super().__init__()
        self.calibration_data = calibration_data
        self.cache_file = cache_file
        self.batch_size = batch_size
        self.current_index = 0

        # Allocate device buffer
        self.device_input = cuda.mem_alloc(
            calibration_data[0].nbytes * batch_size
        )

    def get_batch_size(self):
        return self.batch_size

    def get_batch(self, names):
        if self.current_index + self.batch_size > len(self.calibration_data):
            return None

        # Get batch
        batch = self.calibration_data[
            self.current_index:self.current_index + self.batch_size
        ]
        batch = np.stack(batch, axis=0)

        # Copy to device
        cuda.memcpy_htod(self.device_input, batch)
        self.current_index += self.batch_size

        return [int(self.device_input)]

    def read_calibration_cache(self):
        if os.path.exists(self.cache_file):
            with open(self.cache_file, 'rb') as f:
                return f.read()
        return None

    def write_calibration_cache(self, cache):
        with open(self.cache_file, 'wb') as f:
            f.write(cache)
```

---

## ONNX Runtime Deployment

### Basic ONNX Runtime Inference

```python
import onnxruntime as ort

class ONNXInference:
    def __init__(self, model_path, device='cuda'):
        """
        Initialize ONNX Runtime session.

        Args:
            model_path: Path to ONNX model
            device: 'cuda' or 'cpu'
        """
        # Set execution providers
        if device == 'cuda':
            providers = [
                ('CUDAExecutionProvider', {
                    'device_id': 0,
                    'arena_extend_strategy': 'kNextPowerOfTwo',
                    'gpu_mem_limit': 4 * 1024 * 1024 * 1024,  # 4GB
                    'cudnn_conv_algo_search': 'EXHAUSTIVE',
                }),
                'CPUExecutionProvider'
            ]
        else:
            providers = ['CPUExecutionProvider']

        # Session options
        sess_options = ort.SessionOptions()
        sess_options.graph_optimization_level = ort.GraphOptimizationLevel.ORT_ENABLE_ALL
        sess_options.intra_op_num_threads = 4

        # Create session
        self.session = ort.InferenceSession(
            model_path,
            sess_options=sess_options,
            providers=providers
        )

        # Get input/output info
        self.input_name = self.session.get_inputs()[0].name
        self.input_shape = self.session.get_inputs()[0].shape
        self.output_name = self.session.get_outputs()[0].name

        print(f"Loaded model: {model_path}")
        print(f"Input: {self.input_name} {self.input_shape}")
        print(f"Provider: {self.session.get_providers()[0]}")

    def infer(self, input_data):
        """
        Run inference.

        Args:
            input_data: numpy array (batch, C, H, W)

        Returns:
            Model output
        """
        outputs = self.session.run(
            [self.output_name],
            {self.input_name: input_data.astype(np.float32)}
        )
        return outputs[0]

    def benchmark(self, input_shape, num_iterations=100, warmup=10):
        """
        Benchmark inference speed.
        """
        import time

        dummy_input = np.random.randn(*input_shape).astype(np.float32)

        # Warmup
        for _ in range(warmup):
            self.infer(dummy_input)

        # Benchmark
        start = time.perf_counter()
        for _ in range(num_iterations):
            self.infer(dummy_input)
        end = time.perf_counter()

        avg_time = (end - start) / num_iterations * 1000
        fps = 1000 / avg_time * input_shape[0]

        print(f"Average latency: {avg_time:.2f}ms")
        print(f"Throughput: {fps:.1f} images/sec")

        return avg_time, fps
```

---

## Edge Device Deployment

### NVIDIA Jetson Optimization

```python
def optimize_for_jetson(model_path, output_path, jetson_model='orin'):
    """
    Optimize model for NVIDIA Jetson deployment.

    Args:
        model_path: Path to ONNX model
        output_path: Path to save optimized engine
        jetson_model: 'nano', 'xavier', 'orin'
    """
    # Jetson-specific configurations
    configs = {
        'nano': {'precision': 'fp16', 'workspace': 1, 'dla': False},
        'xavier': {'precision': 'fp16', 'workspace': 2, 'dla': True},
        'orin': {'precision': 'int8', 'workspace': 4, 'dla': True},
    }

    config = configs[jetson_model]

    # Build engine with Jetson-optimized settings
    logger = trt.Logger(trt.Logger.WARNING)
    builder = trt.Builder(logger)
    network = builder.create_network(
        1 << int(trt.NetworkDefinitionCreationFlag.EXPLICIT_BATCH)
    )
    parser = trt.OnnxParser(network, logger)

    with open(model_path, 'rb') as f:
        parser.parse(f.read())

    builder_config = builder.create_builder_config()
    builder_config.set_memory_pool_limit(
        trt.MemoryPoolType.WORKSPACE,
        config['workspace'] * 1024 * 1024 * 1024
    )

    if config['precision'] == 'fp16':
        builder_config.set_flag(trt.BuilderFlag.FP16)
    elif config['precision'] == 'int8':
        builder_config.set_flag(trt.BuilderFlag.INT8)

    # Enable DLA if supported
    if config['dla'] and builder.num_DLA_cores > 0:
        builder_config.default_device_type = trt.DeviceType.DLA
        builder_config.DLA_core = 0
        builder_config.set_flag(trt.BuilderFlag.GPU_FALLBACK)

    # Build and save
    serialized = builder.build_serialized_network(network, builder_config)
    with open(output_path, 'wb') as f:
        f.write(serialized)

    print(f"Jetson-optimized engine saved to {output_path}")
```

### OpenVINO for Intel Devices

```python
from openvino.runtime import Core

class OpenVINOInference:
    def __init__(self, model_path, device='CPU'):
        """
        Initialize OpenVINO inference.

        Args:
            model_path: Path to ONNX or OpenVINO IR model
            device: 'CPU', 'GPU', 'MYRIAD' (Intel NCS)
        """
        self.core = Core()

        # Load and compile model
        self.model = self.core.read_model(model_path)
        self.compiled = self.core.compile_model(self.model, device)

        # Get input/output info
        self.input_layer = self.compiled.input(0)
        self.output_layer = self.compiled.output(0)

        print(f"Loaded model on {device}")
        print(f"Input shape: {self.input_layer.shape}")

    def infer(self, input_data):
        """
        Run inference.
        """
        result = self.compiled([input_data])
        return result[self.output_layer]

    def benchmark(self, input_shape, num_iterations=100):
        """
        Benchmark inference speed.
        """
        import time

        dummy = np.random.randn(*input_shape).astype(np.float32)

        # Warmup
        for _ in range(10):
            self.infer(dummy)

        # Benchmark
        start = time.perf_counter()
        for _ in range(num_iterations):
            self.infer(dummy)
        elapsed = time.perf_counter() - start

        latency = elapsed / num_iterations * 1000
        print(f"Latency: {latency:.2f}ms")
        return latency


def convert_to_openvino(onnx_path, output_dir, precision='FP16'):
    """
    Convert ONNX to OpenVINO IR format.
    """
    from openvino.tools import mo

    mo.convert_model(
        onnx_path,
        output_model=f"{output_dir}/model.xml",
        compress_to_fp16=(precision == 'FP16')
    )
    print(f"Converted to OpenVINO IR at {output_dir}")
```

### CoreML for Apple Silicon

```python
import coremltools as ct

def convert_to_coreml(model_or_path, output_path, compute_units='ALL'):
    """
    Convert to CoreML for Apple devices.

    Args:
        model_or_path: PyTorch model or ONNX path
        output_path: Path to save .mlpackage
        compute_units: 'ALL', 'CPU_AND_GPU', 'CPU_AND_NE'
    """
    # Map compute units
    units_map = {
        'ALL': ct.ComputeUnit.ALL,
        'CPU_AND_GPU': ct.ComputeUnit.CPU_AND_GPU,
        'CPU_AND_NE': ct.ComputeUnit.CPU_AND_NE,  # Neural Engine
    }

    # Convert from ONNX
    if isinstance(model_or_path, str) and model_or_path.endswith('.onnx'):
        mlmodel = ct.convert(
            model_or_path,
            compute_units=units_map[compute_units],
            minimum_deployment_target=ct.target.macOS13  # or iOS16
        )
    else:
        # Convert from PyTorch
        traced = torch.jit.trace(model_or_path, torch.randn(1, 3, 640, 640))
        mlmodel = ct.convert(
            traced,
            inputs=[ct.TensorType(shape=(1, 3, 640, 640))],
            compute_units=units_map[compute_units],
        )

    mlmodel.save(output_path)
    print(f"CoreML model saved to {output_path}")
```

---

## Model Serving

### Triton Inference Server

Configuration file (`config.pbtxt`):
```protobuf
name: "yolov8"
platform: "onnxruntime_onnx"
max_batch_size: 8

input [
  {
    name: "images"
    data_type: TYPE_FP32
    dims: [ 3, 640, 640 ]
  }
]

output [
  {
    name: "output0"
    data_type: TYPE_FP32
    dims: [ 84, 8400 ]
  }
]

instance_group [
  {
    count: 2
    kind: KIND_GPU
  }
]

dynamic_batching {
  preferred_batch_size: [ 4, 8 ]
  max_queue_delay_microseconds: 100
}
```

Triton client:
```python
import tritonclient.http as httpclient

class TritonClient:
    def __init__(self, url='localhost:8000', model_name='yolov8'):
        self.client = httpclient.InferenceServerClient(url=url)
        self.model_name = model_name

        # Check model is ready
        if not self.client.is_model_ready(model_name):
            raise RuntimeError(f"Model {model_name} is not ready")

    def infer(self, images):
        """
        Send inference request to Triton.

        Args:
            images: numpy array (batch, C, H, W)
        """
        # Create input
        inputs = [
            httpclient.InferInput("images", images.shape, "FP32")
        ]
        inputs[0].set_data_from_numpy(images)

        # Create output request
        outputs = [
            httpclient.InferRequestedOutput("output0")
        ]

        # Send request
        response = self.client.infer(
            model_name=self.model_name,
            inputs=inputs,
            outputs=outputs
        )

        return response.as_numpy("output0")
```

### TorchServe Deployment

Model handler (`handler.py`):
```python
from ts.torch_handler.base_handler import BaseHandler
import torch
import cv2
import numpy as np

class YOLOHandler(BaseHandler):
    def __init__(self):
        super().__init__()
        self.input_size = 640
        self.conf_threshold = 0.25
        self.iou_threshold = 0.45

    def preprocess(self, data):
        """Preprocess input images."""
        images = []
        for row in data:
            image = row.get("data") or row.get("body")

            if isinstance(image, (bytes, bytearray)):
                image = np.frombuffer(image, dtype=np.uint8)
                image = cv2.imdecode(image, cv2.IMREAD_COLOR)

            # Resize and normalize
            image = cv2.resize(image, (self.input_size, self.input_size))
            image = image.astype(np.float32) / 255.0
            image = np.transpose(image, (2, 0, 1))
            images.append(image)

        return torch.tensor(np.stack(images))

    def inference(self, data):
        """Run model inference."""
        with torch.no_grad():
            outputs = self.model(data)
        return outputs

    def postprocess(self, outputs):
        """Postprocess model outputs."""
        results = []
        for output in outputs:
            # Apply NMS and format results
            detections = self._nms(output, self.conf_threshold, self.iou_threshold)
            results.append(detections.tolist())
        return results
```

TorchServe configuration (`config.properties`):
```properties
inference_address=http://0.0.0.0:8080
management_address=http://0.0.0.0:8081
metrics_address=http://0.0.0.0:8082
number_of_netty_threads=4
job_queue_size=100
model_store=/opt/ml/model
load_models=yolov8.mar
```

### FastAPI Serving

```python
from fastapi import FastAPI, File, UploadFile
from fastapi.responses import JSONResponse
import uvicorn
import numpy as np
import cv2

app = FastAPI(title="YOLO Detection API")

# Global model
model = None

@app.on_event("startup")
async def load_model():
    global model
    model = ONNXInference("models/yolov8m.onnx", device='cuda')

@app.post("/detect")
async def detect(file: UploadFile = File(...), conf: float = 0.25):
    """
    Detect objects in uploaded image.
    """
    # Read image
    contents = await file.read()
    nparr = np.frombuffer(contents, np.uint8)
    image = cv2.imdecode(nparr, cv2.IMREAD_COLOR)

    # Preprocess
    input_image = preprocess_image(image, 640)

    # Inference
    outputs = model.infer(input_image)

    # Postprocess
    detections = postprocess_detections(outputs, conf, 0.45)

    return JSONResponse({
        "detections": detections,
        "image_size": list(image.shape[:2])
    })

@app.get("/health")
async def health():
    return {"status": "healthy", "model_loaded": model is not None}

if __name__ == "__main__":
    uvicorn.run(app, host="0.0.0.0", port=8000)
```

---

## Video Processing Pipelines

### Real-Time Video Detection

```python
import cv2
import time
from collections import deque

class VideoDetector:
    def __init__(self, model, conf_threshold=0.25, track=True):
        self.model = model
        self.conf_threshold = conf_threshold
        self.track = track
        self.tracker = ByteTrack() if track else None
        self.fps_buffer = deque(maxlen=30)

    def process_video(self, source, output_path=None, show=True):
        """
        Process video stream with detection.

        Args:
            source: Video file path, camera index, or RTSP URL
            output_path: Path to save output video
            show: Display results in window
        """
        cap = cv2.VideoCapture(source)

        if output_path:
            fourcc = cv2.VideoWriter_fourcc(*'mp4v')
            fps = cap.get(cv2.CAP_PROP_FPS)
            width = int(cap.get(cv2.CAP_PROP_FRAME_WIDTH))
            height = int(cap.get(cv2.CAP_PROP_FRAME_HEIGHT))
            writer = cv2.VideoWriter(output_path, fourcc, fps, (width, height))

        frame_count = 0
        start_time = time.time()

        while cap.isOpened():
            ret, frame = cap.read()
            if not ret:
                break

            # Inference
            t0 = time.perf_counter()
            detections = self._detect(frame)

            # Tracking
            if self.track and len(detections) > 0:
                detections = self.tracker.update(detections)

            # Calculate FPS
            inference_time = time.perf_counter() - t0
            self.fps_buffer.append(1 / inference_time)
            avg_fps = sum(self.fps_buffer) / len(self.fps_buffer)

            # Draw results
            frame = self._draw_detections(frame, detections, avg_fps)

            # Output
            if output_path:
                writer.write(frame)

            if show:
                cv2.imshow('Detection', frame)
                if cv2.waitKey(1) == ord('q'):
                    break

            frame_count += 1

        # Cleanup
        cap.release()
        if output_path:
            writer.release()
        cv2.destroyAllWindows()

        # Print statistics
        total_time = time.time() - start_time
        print(f"Processed {frame_count} frames in {total_time:.1f}s")
        print(f"Average FPS: {frame_count / total_time:.1f}")

    def _detect(self, frame):
        """Run detection on single frame."""
        # Preprocess
        input_tensor = self._preprocess(frame)

        # Inference
        outputs = self.model.infer(input_tensor)

        # Postprocess
        detections = self._postprocess(outputs, frame.shape[:2])
        return detections

    def _preprocess(self, frame):
        """Preprocess frame for model input."""
        # Resize
        input_size = 640
        image = cv2.resize(frame, (input_size, input_size))

        # Normalize and transpose
        image = image.astype(np.float32) / 255.0
        image = np.transpose(image, (2, 0, 1))
        image = np.expand_dims(image, axis=0)

        return image

    def _draw_detections(self, frame, detections, fps):
        """Draw detections on frame."""
        for det in detections:
            x1, y1, x2, y2 = det['bbox']
            cls = det['class']
            conf = det['confidence']
            track_id = det.get('track_id', None)

            # Draw box
            color = self._get_color(cls)
            cv2.rectangle(frame, (int(x1), int(y1)), (int(x2), int(y2)), color, 2)

            # Draw label
            label = f"{cls}: {conf:.2f}"
            if track_id:
                label = f"ID:{track_id} {label}"

            cv2.putText(frame, label, (int(x1), int(y1) - 10),
                       cv2.FONT_HERSHEY_SIMPLEX, 0.5, color, 2)

        # Draw FPS
        cv2.putText(frame, f"FPS: {fps:.1f}", (10, 30),
                   cv2.FONT_HERSHEY_SIMPLEX, 1, (0, 255, 0), 2)

        return frame
```

### Batch Video Processing

```python
import concurrent.futures
from pathlib import Path

def process_videos_batch(video_paths, model, output_dir, max_workers=4):
    """
    Process multiple videos in parallel.
    """
    output_dir = Path(output_dir)
    output_dir.mkdir(parents=True, exist_ok=True)

    def process_single(video_path):
        detector = VideoDetector(model)
        output_path = output_dir / f"{Path(video_path).stem}_detected.mp4"
        detector.process_video(video_path, str(output_path), show=False)
        return output_path

    with concurrent.futures.ThreadPoolExecutor(max_workers=max_workers) as executor:
        futures = {executor.submit(process_single, vp): vp for vp in video_paths}

        for future in concurrent.futures.as_completed(futures):
            video_path = futures[future]
            try:
                output_path = future.result()
                print(f"Completed: {video_path} -> {output_path}")
            except Exception as e:
                print(f"Failed: {video_path} - {e}")
```

---

## Monitoring and Observability

### Prometheus Metrics

```python
from prometheus_client import Counter, Histogram, Gauge, start_http_server

# Define metrics
INFERENCE_COUNT = Counter(
    'model_inference_total',
    'Total number of inferences',
    ['model_name', 'status']
)

INFERENCE_LATENCY = Histogram(
    'model_inference_latency_seconds',
    'Inference latency in seconds',
    ['model_name'],
    buckets=[0.01, 0.025, 0.05, 0.1, 0.25, 0.5, 1.0]
)

GPU_MEMORY = Gauge(
    'gpu_memory_used_bytes',
    'GPU memory usage in bytes',
    ['device']
)

DETECTIONS_COUNT = Counter(
    'detections_total',
    'Total detections by class',
    ['model_name', 'class_name']
)

class MetricsWrapper:
    def __init__(self, model, model_name='yolov8'):
        self.model = model
        self.model_name = model_name

    def infer(self, input_data):
        """Inference with metrics."""
        start_time = time.perf_counter()

        try:
            result = self.model.infer(input_data)
            INFERENCE_COUNT.labels(self.model_name, 'success').inc()

            # Count detections by class
            for det in result:
                DETECTIONS_COUNT.labels(self.model_name, det['class']).inc()

            return result

        except Exception as e:
            INFERENCE_COUNT.labels(self.model_name, 'error').inc()
            raise

        finally:
            latency = time.perf_counter() - start_time
            INFERENCE_LATENCY.labels(self.model_name).observe(latency)

            # Update GPU memory
            if torch.cuda.is_available():
                memory = torch.cuda.memory_allocated()
                GPU_MEMORY.labels('cuda:0').set(memory)

# Start metrics server
start_http_server(9090)
```

### Logging Configuration

```python
import logging
import json
from datetime import datetime

class StructuredLogger:
    def __init__(self, name, level=logging.INFO):
        self.logger = logging.getLogger(name)
        self.logger.setLevel(level)

        # JSON formatter
        handler = logging.StreamHandler()
        handler.setFormatter(JsonFormatter())
        self.logger.addHandler(handler)

    def log_inference(self, model_name, latency, num_detections, input_shape):
        self.logger.info(json.dumps({
            'event': 'inference',
            'timestamp': datetime.utcnow().isoformat(),
            'model_name': model_name,
            'latency_ms': latency * 1000,
            'num_detections': num_detections,
            'input_shape': list(input_shape)
        }))

    def log_error(self, model_name, error, input_shape):
        self.logger.error(json.dumps({
            'event': 'inference_error',
            'timestamp': datetime.utcnow().isoformat(),
            'model_name': model_name,
            'error': str(error),
            'error_type': type(error).__name__,
            'input_shape': list(input_shape)
        }))

class JsonFormatter(logging.Formatter):
    def format(self, record):
        return record.getMessage()
```

---

## Scaling and Performance

### Batch Processing Optimization

```python
class BatchProcessor:
    def __init__(self, model, max_batch_size=8, max_wait_ms=100):
        self.model = model
        self.max_batch_size = max_batch_size
        self.max_wait_ms = max_wait_ms
        self.queue = []
        self.lock = threading.Lock()
        self.results = {}

    async def process(self, image, request_id):
        """Add image to batch and wait for result."""
        future = asyncio.Future()

        with self.lock:
            self.queue.append((request_id, image, future))

            if len(self.queue) >= self.max_batch_size:
                self._process_batch()

        # Wait for result with timeout
        result = await asyncio.wait_for(future, timeout=5.0)
        return result

    def _process_batch(self):
        """Process accumulated batch."""
        batch_items = self.queue[:self.max_batch_size]
        self.queue = self.queue[self.max_batch_size:]

        # Stack images
        images = np.stack([item[1] for item in batch_items])

        # Inference
        outputs = self.model.infer(images)

        # Return results
        for i, (request_id, image, future) in enumerate(batch_items):
            future.set_result(outputs[i])
```

### Multi-GPU Inference

```python
import torch.nn as nn
from torch.nn.parallel import DataParallel

class MultiGPUInference:
    def __init__(self, model, device_ids=None):
        """
        Wrap model for multi-GPU inference.

        Args:
            model: PyTorch model
            device_ids: List of GPU IDs, e.g., [0, 1, 2, 3]
        """
        if device_ids is None:
            device_ids = list(range(torch.cuda.device_count()))

        self.device = torch.device('cuda:0')
        self.model = DataParallel(model, device_ids=device_ids)
        self.model.to(self.device)
        self.model.set_mode('inference')

    def infer(self, images):
        """
        Run inference across GPUs.
        """
        with torch.no_grad():
            images = torch.from_numpy(images).to(self.device)
            outputs = self.model(images)
        return outputs.cpu().numpy()
```

### Performance Benchmarking

```python
def comprehensive_benchmark(model, input_sizes, batch_sizes, num_iterations=100):
    """
    Benchmark model across different configurations.
    """
    results = []

    for input_size in input_sizes:
        for batch_size in batch_sizes:
            # Create input
            dummy = np.random.randn(batch_size, 3, input_size, input_size).astype(np.float32)

            # Warmup
            for _ in range(10):
                model.infer(dummy)

            # Benchmark
            latencies = []
            for _ in range(num_iterations):
                start = time.perf_counter()
                model.infer(dummy)
                latencies.append(time.perf_counter() - start)

            # Calculate statistics
            latencies = np.array(latencies) * 1000  # Convert to ms
            result = {
                'input_size': input_size,
                'batch_size': batch_size,
                'mean_latency_ms': np.mean(latencies),
                'std_latency_ms': np.std(latencies),
                'p50_latency_ms': np.percentile(latencies, 50),
                'p95_latency_ms': np.percentile(latencies, 95),
                'p99_latency_ms': np.percentile(latencies, 99),
                'throughput_fps': batch_size * 1000 / np.mean(latencies)
            }
            results.append(result)

            print(f"Size: {input_size}, Batch: {batch_size}")
            print(f"  Latency: {result['mean_latency_ms']:.2f}ms (p99: {result['p99_latency_ms']:.2f}ms)")
            print(f"  Throughput: {result['throughput_fps']:.1f} FPS")

    return results
```

---

## Resources

- [TensorRT Documentation](https://docs.nvidia.com/deeplearning/tensorrt/)
- [ONNX Runtime Documentation](https://onnxruntime.ai/docs/)
- [Triton Inference Server](https://github.com/triton-inference-server/server)
- [OpenVINO Documentation](https://docs.openvino.ai/)
- [CoreML Tools](https://coremltools.readme.io/)
