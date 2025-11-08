# PyTorch Quantization Guide

Quantization reduces model size and speeds up inference by converting 32-bit floating-point weights and activations to lower-precision integers (typically 8-bit).

## Quantization Types

### 1. Dynamic Quantization (Easiest)

**When to use:** Production inference where speed is critical and you need minimal setup.

```python
import torch
import torch.quantization

# Load model
model = torch.load("model.pt")
model.eval()

# Apply dynamic quantization
quantized_model = torch.quantization.quantize_dynamic(
    model,
    {torch.nn.Linear, torch.nn.Conv2d},
    dtype=torch.qint8
)

# Use
output = quantized_model(input_data)
```

**Advantages:**
- Easy to apply (one line)
- Works with most architectures
- No training required
- Good speed improvement

**Disadvantages:**
- Activation precision not optimized
- Less accuracy improvement than static QAT
- Only weights quantized

**Performance:**
- 2-3x model size reduction
- 1.5-2x speedup on CPU
- Minimal accuracy loss (typically <1%)

### 2. Static Quantization (Better Accuracy)

**When to use:** When you need better accuracy-performance tradeoff.

```python
import torch
import torch.quantization

# Step 1: Configure quantization
model = torch.load("model.pt")
model.eval()
model.qconfig = torch.quantization.get_default_qconfig('fbgemm')

# Step 2: Insert observer modules
torch.quantization.prepare(model, inplace=True)

# Step 3: Calibrate with representative data
for data, _ in calibration_loader:
    model(data)

# Step 4: Convert to quantized model
torch.quantization.convert(model, inplace=True)

# Use
output = model(input_data)
```

**Detailed Example:**

```python
import torch
import torch.quantization
from torch.utils.data import DataLoader

def static_quantize(model, calibration_data_loader, device="cpu"):
    """Apply static quantization with calibration."""

    model = model.to(device).eval()

    # Configure for quantization
    model.qconfig = torch.quantization.get_default_qconfig('fbgemm')

    # Prepare - adds observer modules
    torch.quantization.prepare(model, inplace=True)

    # Calibration phase - measure activation ranges
    print("Calibrating...")
    with torch.no_grad():
        for batch_idx, (data, target) in enumerate(calibration_data_loader):
            data = data.to(device)
            model(data)
            if batch_idx % 100 == 0:
                print(f"  Batch {batch_idx}")

    # Convert - replace modules with quantized versions
    torch.quantization.convert(model, inplace=True)

    return model

# Usage
model = torch.load("model.pt")
calibration_loader = DataLoader(calibration_dataset, batch_size=32)
quantized = static_quantize(model, calibration_loader)
```

**Advantages:**
- Better accuracy than dynamic
- Both weights and activations quantized
- 2-4x speedup possible

**Disadvantages:**
- Requires calibration data
- More setup than dynamic
- Platform-specific (FBGEMM for CPU)

**Performance:**
- 2-4x model size reduction
- 2-3x speedup on CPU
- Better accuracy than dynamic (<0.5% loss)

### 3. Quantization-Aware Training (QAT)

**When to use:** Maximum accuracy retention with quantization, willing to retrain.

```python
import torch
import torch.quantization

# Load pretrained model
model = torch.load("model.pt")
model.train()  # Set to training mode

# Configure for QAT
model.qconfig = torch.quantization.get_default_qat_qconfig('fbgemm')

# Prepare - insert fake quantization modules
torch.quantization.prepare_qat(model, inplace=True)

# Training loop
optimizer = torch.optim.SGD(model.parameters(), lr=0.001)
loss_fn = torch.nn.CrossEntropyLoss()

for epoch in range(num_epochs):
    for data, target in train_loader:
        # Forward pass
        output = model(data)
        loss = loss_fn(output, target)

        # Backward pass
        optimizer.zero_grad()
        loss.backward()
        optimizer.step()

    print(f"Epoch {epoch+1}/{num_epochs}, Loss: {loss.item():.4f}")

# Convert to quantized model
model.eval()
torch.quantization.convert(model, inplace=True)
```

**Complete QAT Example:**

```python
def train_with_qat(model, train_loader, val_loader, num_epochs=10, device="cpu"):
    """Train model with quantization-aware training."""

    model = model.to(device).train()

    # Configure QAT
    model.qconfig = torch.quantization.get_default_qat_qconfig('fbgemm')
    torch.quantization.prepare_qat(model, inplace=True)

    optimizer = torch.optim.SGD(model.parameters(), lr=0.001)
    loss_fn = torch.nn.CrossEntropyLoss()

    for epoch in range(num_epochs):
        # Training phase
        model.train()
        total_loss = 0
        for data, target in train_loader:
            data, target = data.to(device), target.to(device)

            output = model(data)
            loss = loss_fn(output, target)

            optimizer.zero_grad()
            loss.backward()
            optimizer.step()

            total_loss += loss.item()

        # Validation phase
        model.eval()
        with torch.no_grad():
            correct = 0
            total = 0
            for data, target in val_loader:
                data, target = data.to(device), target.to(device)
                output = model(data)
                _, predicted = torch.max(output.data, 1)
                total += target.size(0)
                correct += (predicted == target).sum().item()

        accuracy = 100 * correct / total
        print(f"Epoch {epoch+1}: Loss={total_loss:.4f}, Accuracy={accuracy:.2f}%")

    # Convert to quantized model
    model.eval()
    torch.quantization.convert(model, inplace=True)

    return model
```

**Advantages:**
- Best accuracy retention (minimal loss)
- Both weights and activations optimized
- Highest speedup potential

**Disadvantages:**
- Requires retraining
- Time-consuming
- Best results with full training data

**Performance:**
- 2-4x model size reduction
- 2-4x speedup on CPU
- Minimal accuracy loss (<0.1%)

## Choosing Quantization Backend

### FBGEMM (CPU)
```python
model.qconfig = torch.quantization.get_default_qconfig('fbgemm')
```
- Best for x86 CPU
- Optimized for Intel CPUs
- Good speedup

### QNNPACK (Mobile/ARM)
```python
model.qconfig = torch.quantization.get_default_qconfig('qnnpack')
```
- Mobile and ARM processors
- Lower precision (unsigned int8)
- Best for edge devices

## Quantization Configuration Options

```python
# Different precision levels
torch.quantization.quantize_dynamic(
    model,
    {torch.nn.Linear},
    dtype=torch.qint8   # 8-bit integer
)

torch.quantization.quantize_dynamic(
    model,
    {torch.nn.Linear},
    dtype=torch.float16  # 16-bit float (not true quantization)
)

# Mixed precision - different precision for different layers
model.fc1.qconfig = torch.quantization.default_dynamic_qconfig
model.fc2.qconfig = None  # Skip quantization
```

## Validation and Testing

```python
def validate_quantized_model(original_model, quantized_model, test_loader, device="cpu"):
    """Compare original and quantized model outputs."""

    original_model.to(device).eval()
    quantized_model.to(device).eval()

    differences = []

    with torch.no_grad():
        for data, target in test_loader:
            data = data.to(device)

            # Get predictions
            orig_output = original_model(data)
            quant_output = quantized_model(data)

            # Compare
            orig_pred = orig_output.argmax(dim=1)
            quant_pred = quant_output.argmax(dim=1)

            # Calculate difference
            match = (orig_pred == quant_pred).float().mean().item()
            differences.append(match)

    avg_agreement = sum(differences) / len(differences)
    print(f"Model Agreement: {avg_agreement * 100:.2f}%")

    return avg_agreement
```

## Quantization Roadblocks and Solutions

### Problem: Accuracy Drop > 1%

**Solution 1: Use Static Quantization**
```python
# Instead of dynamic, use static with calibration
model.qconfig = torch.quantization.get_default_qconfig('fbgemm')
torch.quantization.prepare(model, inplace=True)
# Calibrate...
torch.quantization.convert(model, inplace=True)
```

**Solution 2: Use QAT**
```python
# Train with quantization awareness
model.qconfig = torch.quantization.get_default_qat_qconfig('fbgemm')
torch.quantization.prepare_qat(model, inplace=True)
# Train...
```

### Problem: Module Not Supported

```python
# Skip unsupported modules
model.custom_layer.qconfig = None
```

### Problem: Speed Not Improved

```python
# Check if using CUDA (quantization mainly benefits CPU)
# For CUDA, use torch.compile() instead
compiled_model = torch.compile(model)
```

## Performance Comparison

| Method | Size | Speed | Accuracy |
|--------|------|-------|----------|
| Original FP32 | 1.0x | 1.0x | 100% |
| Dynamic QAT | 0.25x | 1.8x | 99.2% |
| Static QAT | 0.25x | 2.3x | 99.5% |
| QAT | 0.25x | 2.3x | 99.8% |

*Typical results for image classification models on CPU*

## Best Practices

1. **Start with dynamic quantization** - easiest and works well for most cases
2. **Use calibration data that represents production** - for static quantization
3. **Validate on test set** - ensure accuracy is acceptable
4. **Test on target hardware** - quantization benefits vary by platform
5. **Combine with torch.compile()** - for maximum performance (CPU to GPU transfer)
6. **Profile before and after** - measure real impact on your hardware

## Quick Reference

```python
# 1. Dynamic Quantization (1 line)
quantized = torch.quantization.quantize_dynamic(model, {torch.nn.Linear})

# 2. Static Quantization (4 lines)
model.qconfig = torch.quantization.get_default_qconfig('fbgemm')
torch.quantization.prepare(model, inplace=True)
# Calibrate...
torch.quantization.convert(model, inplace=True)

# 3. QAT (5 lines)
model.qconfig = torch.quantization.get_default_qat_qconfig('fbgemm')
torch.quantization.prepare_qat(model, inplace=True)
# Train...
model.eval()
torch.quantization.convert(model, inplace=True)
```
