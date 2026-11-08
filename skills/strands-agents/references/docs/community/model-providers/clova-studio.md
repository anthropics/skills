# CLOVA Studio

{{ community_contribution_banner }}

!!! info "Language Support"
    This provider is only supported in Python.

[CLOVA Studio](https://www.ncloud.com/product/aiService/clovaStudio) is Naver Cloud Platform's AI service that provides large language models optimized for Korean language processing. The [`strands-clova`](https://pypi.org/project/strands-clova/) package ([GitHub](https://github.com/aidendef/strands-clova)) provides a community-maintained integration for the Strands Agents SDK, enabling seamless use of CLOVA Studio's Korean-optimized AI models.

## Installation

CLOVA Studio integration is available as a separate community package:

```bash
pip install strands-agents strands-clova
```

## Usage

After installing `strands-clova`, you can import and initialize the CLOVA Studio provider:

```python
from strands import Agent
from strands_clova import ClovaModel

model = ClovaModel(
    api_key="your-clova-api-key",  # or set CLOVA_API_KEY env var
    model="HCX-005",
    temperature=0.7,
    max_tokens=2048
)

agent = Agent(model=model)
response = await agent.invoke_async("안녕하세요! 오늘 날씨가 어떤가요?")
print(response.message)
```

## Configuration

### Environment Variables

```bash
export CLOVA_API_KEY="your-api-key"
export CLOVA_REQUEST_ID="optional-request-id"  # For request tracking
```

### Model Configuration

The supported configurations are:

|  Parameter | Description | Example | Default |
|------------|-------------|---------|---------|
| `model` | Model ID | `HCX-005` | `HCX-005` |
| `temperature` | Sampling temperature (0.0-1.0) | `0.7` | `0.7` |
| `max_tokens` | Maximum tokens to generate | `4096` | `2048` |
| `top_p` | Nucleus sampling parameter | `0.8` | `0.8` |
| `top_k` | Top-k sampling parameter | `0` | `0` |
| `repeat_penalty` | Repetition penalty | `1.1` | `1.1` |
| `stop` | Stop sequences | `["\\n\\n"]` | `[]` |

## Advanced Features

### Korean Language Optimization

CLOVA Studio excels at Korean language tasks:

```python
# Korean customer support bot
model = ClovaModel(api_key="your-api-key", temperature=0.3)
agent = Agent(
    model=model,
    system_prompt="당신은 친절한 고객 서비스 상담원입니다."
)

response = await agent.invoke_async("제품 반품 절차를 알려주세요")
```

### Bilingual Capabilities

Handle both Korean and English seamlessly:

```python
# Process Korean document and get English summary
response = await agent.invoke_async(
    "다음 한국어 문서를 영어로 요약해주세요: [문서 내용]"
)
```

## References

- [strands-clova GitHub Repository](https://github.com/aidendef/strands-clova)
- [CLOVA Studio Documentation](https://www.ncloud.com/product/aiService/clovaStudio)
- [Naver Cloud Platform](https://www.ncloud.com/)