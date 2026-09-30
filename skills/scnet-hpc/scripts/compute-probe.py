#!/usr/bin/env python3
"""在目标计算节点上做一次最小能力探针。

输出统一使用 PROBE_ 前缀的 KEY=value 行，方便 refresh-cluster.sh 解析。
每个检查都独立捕获异常，单项失败不会中断后续检查。
"""

import os
import urllib.request


def emit(key, value):
    print("PROBE_{}={}".format(key, value), flush=True)


def short_error(exc, limit=180):
    text = str(exc).replace("\n", " ")
    return "{}:{}".format(type(exc).__name__, text[:limit])


try:
    import torch
    emit("TORCH_VERSION", torch.__version__)
    cuda_available = bool(torch.cuda.is_available())
    emit("CUDA_AVAILABLE", "1" if cuda_available else "0")

    if cuda_available:
        count = torch.cuda.device_count()
        emit("DEVICE_COUNT", count)

        props = torch.cuda.get_device_properties(0)
        emit("DEVICE_NAME", getattr(props, "name", "unknown").replace("\n", " "))

        arch = getattr(props, "gcnArchName", None)
        if arch is None:
            arch = "{}.{}".format(getattr(props, "major", "?"), getattr(props, "minor", "?"))
        emit("ARCH", arch)

        total_memory = getattr(props, "total_memory", 0)
        emit("MEM_MIB", int(total_memory // (1024 * 1024)))

        have_dtypes = []
        for dtype_name in ["float8_e4m3fn", "float8_e5m2", "float8_e8m0fnu", "bfloat16"]:
            if hasattr(torch, dtype_name):
                have_dtypes.append(dtype_name)
        emit("DTYPES", ",".join(have_dtypes))

        # 硬件 FP8 matmul
        try:
            if hasattr(torch, "float8_e4m3fn") and hasattr(torch, "_scaled_mm"):
                a = torch.randn(64, 128).to(torch.float8_e4m3fn).cuda()
                b = torch.randn(128, 64).to(torch.float8_e4m3fn).cuda().t().contiguous().t()
                torch._scaled_mm(
                    a,
                    b,
                    scale_a=torch.tensor(1.0).cuda(),
                    scale_b=torch.tensor(1.0).cuda(),
                    out_dtype=torch.bfloat16,
                )
                torch.cuda.synchronize()
                emit("SCALED_MM", "OK")
            else:
                emit("SCALED_MM", "SKIP:float8_e4m3fn_or_scaled_mm_missing")
        except Exception as exc:
            emit("SCALED_MM", "ERR:" + short_error(exc))

        # Triton 内核
        try:
            import triton
            import triton.language as tl

            @triton.jit
            def add_kernel(x, y, out, n, BLOCK: tl.constexpr):
                idx = tl.program_id(0) * BLOCK + tl.arange(0, BLOCK)
                mask = idx < n
                tl.store(out + idx, tl.load(x + idx, mask=mask) + tl.load(y + idx, mask=mask), mask=mask)

            n = 4096
            x = torch.randn(n, device="cuda")
            y = torch.randn(n, device="cuda")
            out = torch.empty_like(x)
            add_kernel[(triton.cdiv(n, 256),)](x, y, out, n, BLOCK=256)
            torch.cuda.synchronize()
            max_err = float((out - (x + y)).abs().max().item())
            emit("TRITON", "OK err={:.3g}".format(max_err))
        except Exception as exc:
            emit("TRITON", "ERR:" + short_error(exc, 240))

        # bitsandbytes：先看能否 import；是否真正可用仍需业务级测试
        try:
            import bitsandbytes as bnb
            emit("BITSANDBYTES", "IMPORT_OK version={}".format(getattr(bnb, "__version__", "unknown")))
        except Exception as exc:
            emit("BITSANDBYTES", "IMPORT_ERR:" + short_error(exc))
    else:
        emit("DEVICE_COUNT", 0)
except Exception as exc:
    emit("TORCH_IMPORT", "ERR:" + short_error(exc, 240))

# 计算节点外网
try:
    urllib.request.urlopen("https://pypi.org", timeout=5)
    emit("NET_PYPI", "ONLINE")
except Exception:
    emit("NET_PYPI", "OFFLINE")

# 测试任务统一使用家目录中的 TMPDIR；记录实际路径，确认规则生效。
try:
    tmp_dir = os.environ.get("TMPDIR", "")
    emit("TMPDIR", tmp_dir)
    emit("TMP_IN_HOME", "1" if tmp_dir and os.path.commonpath([os.path.expanduser("~"), tmp_dir]) == os.path.expanduser("~") else "0")
except Exception as exc:
    emit("TMPDIR", "ERR:" + short_error(exc))

print("PROBE_EXIT=0", flush=True)
