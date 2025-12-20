#!/usr/bin/env python3
"""
Hive Image Generation - AI image generation with multiple providers.

Usage:
    python generate.py "prompt"                 # Generate with default (xAI)
    python generate.py "prompt" --provider openai  # Use DALL-E
    python generate.py "prompt" --size 1024x1024   # Specific size
    python generate.py "prompt" -o image.png    # Save to file
"""

import argparse
import json
import os
import sys
import base64
from datetime import datetime

PROVIDERS = {
    "xai": {
        "name": "xAI Aurora",
        "env": "XAI_API_KEY",
        "models": ["aurora"],
        "sizes": ["1024x1024", "1792x1024", "1024x1792"]
    },
    "openai": {
        "name": "OpenAI DALL-E",
        "env": "OPENAI_API_KEY",
        "models": ["dall-e-3", "dall-e-2"],
        "sizes": ["1024x1024", "1792x1024", "1024x1792"]
    },
    "stability": {
        "name": "Stability AI",
        "env": "STABILITY_API_KEY",
        "models": ["sdxl", "sd3"],
        "sizes": ["512x512", "768x768", "1024x1024"]
    },
    "huggingface": {
        "name": "HuggingFace",
        "env": "HUGGINGFACE_API_KEY",
        "models": ["flux", "sdxl"],
        "sizes": ["512x512", "768x768", "1024x1024"]
    }
}

def generate_image(prompt: str, provider: str = "xai", model: str = None,
                   size: str = "1024x1024", style: str = None) -> dict:
    """Generate image from prompt."""
    if provider not in PROVIDERS:
        return {"error": f"Unknown provider: {provider}", "available": list(PROVIDERS.keys())}

    provider_info = PROVIDERS[provider]

    # Check API key
    api_key = os.environ.get(provider_info["env"])
    if not api_key:
        return {
            "error": f"Missing API key: {provider_info['env']}",
            "hint": f"Set {provider_info['env']} environment variable"
        }

    # Validate size
    if size not in provider_info["sizes"]:
        return {
            "error": f"Size {size} not supported by {provider}",
            "supported": provider_info["sizes"]
        }

    # Use default model if not specified
    model = model or provider_info["models"][0]

    print(f"Generating image with {provider_info['name']}...")
    print(f"Model: {model}")
    print(f"Size: {size}")
    print(f"Prompt: {prompt[:100]}{'...' if len(prompt) > 100 else ''}")

    # Mock result (would call actual API)
    result = {
        "provider": provider,
        "model": model,
        "prompt": prompt,
        "size": size,
        "style": style,
        "timestamp": datetime.now().isoformat(),
        "image_url": f"https://placeholder.example.com/image_{provider}_{size}.png",
        "note": "This is a demonstration. Connect to actual APIs to generate real images."
    }

    return result

def format_output(result: dict, output_format: str) -> str:
    """Format result for display."""
    if output_format == "json":
        return json.dumps(result, indent=2)

    if "error" in result:
        return f"Error: {result['error']}\n{result.get('hint', '')}"

    lines = [
        f"Image Generated",
        f"Provider: {result['provider']}",
        f"Model: {result['model']}",
        f"Size: {result['size']}",
        f"Prompt: {result['prompt'][:80]}{'...' if len(result['prompt']) > 80 else ''}",
        f"URL: {result['image_url']}",
        f"",
        f"Note: {result['note']}"
    ]

    return "\n".join(lines)

def main():
    parser = argparse.ArgumentParser(
        description="Hive Image Generation - AI image creation",
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog="""
Examples:
  python generate.py "A sunset over mountains"
  python generate.py "A robot" --provider openai
  python generate.py "prompt" --size 1792x1024 --style vivid
  python generate.py "prompt" -o output.png

Providers:
  xai       - xAI Aurora (default)
  openai    - OpenAI DALL-E 3
  stability - Stability AI SDXL
  huggingface - HuggingFace models
        """
    )

    parser.add_argument("prompt", help="Image generation prompt")
    parser.add_argument("--provider", "-p", choices=list(PROVIDERS.keys()),
                       default="xai", help="Provider (default: xai)")
    parser.add_argument("--model", "-m", help="Specific model")
    parser.add_argument("--size", "-s", default="1024x1024",
                       help="Image size (default: 1024x1024)")
    parser.add_argument("--style", help="Style modifier (vivid, natural)")
    parser.add_argument("--output", "-o", help="Save image to file")
    parser.add_argument("--json", action="store_true", help="Output as JSON")

    args = parser.parse_args()

    output_format = "json" if args.json else "text"
    result = generate_image(args.prompt, args.provider, args.model, args.size, args.style)

    output = format_output(result, output_format)

    if args.output and "error" not in result:
        # In real implementation, would save actual image
        print(f"Image would be saved to: {args.output}")
        print(f"URL: {result.get('image_url')}")
    else:
        print(output)

if __name__ == "__main__":
    main()
