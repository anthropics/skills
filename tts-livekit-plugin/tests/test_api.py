"""
Test cases for MeloTTS API Server
Tests API endpoints without mocking
"""
import asyncio
import pytest
import aiohttp
from typing import AsyncGenerator


API_BASE_URL = "http://localhost:8000"


class TestAPIHealth:
    """Test API health and basic functionality"""

    @pytest.mark.asyncio
    async def test_root_endpoint(self):
        """Test that root endpoint returns health status"""
        async with aiohttp.ClientSession() as session:
            async with session.get(f"{API_BASE_URL}/") as resp:
                assert resp.status == 200
                data = await resp.json()
                assert data["status"] == "ok"
                assert "service" in data
                assert "version" in data

    @pytest.mark.asyncio
    async def test_list_voices(self):
        """Test listing available voices"""
        async with aiohttp.ClientSession() as session:
            # Test English voices
            async with session.get(f"{API_BASE_URL}/voices?language=EN") as resp:
                assert resp.status == 200
                data = await resp.json()
                assert "language" in data
                assert "voices" in data
                assert isinstance(data["voices"], list)
                assert len(data["voices"]) > 0
                # Should have EN-US, EN-BR, etc.
                assert any("EN" in voice for voice in data["voices"])


class TestSynthesis:
    """Test TTS synthesis endpoints"""

    @pytest.mark.asyncio
    async def test_synthesize_basic(self):
        """Test basic synthesis with default parameters"""
        async with aiohttp.ClientSession() as session:
            payload = {
                "text": "Hello, this is a test.",
                "language": "EN",
                "speaker": "EN-US",
                "speed": 1.0
            }

            async with session.post(
                f"{API_BASE_URL}/synthesize",
                json=payload
            ) as resp:
                assert resp.status == 200
                assert resp.headers["Content-Type"].startswith("audio/")

                # Read audio data
                audio_data = await resp.read()
                assert len(audio_data) > 0
                # WAV file should start with RIFF header
                assert audio_data[:4] == b"RIFF"

    @pytest.mark.asyncio
    async def test_synthesize_streaming(self):
        """Test streaming synthesis endpoint"""
        async with aiohttp.ClientSession() as session:
            payload = {
                "text": "This is a streaming test with multiple words.",
                "language": "EN",
                "speaker": "EN-US",
                "speed": 1.0
            }

            async with session.post(
                f"{API_BASE_URL}/synthesize/stream",
                json=payload
            ) as resp:
                assert resp.status == 200
                assert resp.headers["Content-Type"].startswith("audio/")

                # Collect chunks
                chunks = []
                async for chunk, _ in resp.content.iter_chunks():
                    if chunk:
                        chunks.append(chunk)

                assert len(chunks) > 0

                # Combine all chunks
                audio_data = b"".join(chunks)
                assert len(audio_data) > 0
                # WAV file should start with RIFF header
                assert audio_data[:4] == b"RIFF"

    @pytest.mark.asyncio
    async def test_synthesize_different_speeds(self):
        """Test synthesis with different speed settings"""
        text = "Speed test."

        async with aiohttp.ClientSession() as session:
            for speed in [0.5, 1.0, 1.5, 2.0]:
                payload = {
                    "text": text,
                    "language": "EN",
                    "speaker": "EN-US",
                    "speed": speed
                }

                async with session.post(
                    f"{API_BASE_URL}/synthesize",
                    json=payload
                ) as resp:
                    assert resp.status == 200
                    audio_data = await resp.read()
                    assert len(audio_data) > 0

    @pytest.mark.asyncio
    async def test_synthesize_different_languages(self):
        """Test synthesis with different languages"""
        test_cases = [
            ("EN", "EN-US", "Hello world"),
            ("ES", "ES", "Hola mundo"),
            ("FR", "FR", "Bonjour le monde"),
        ]

        async with aiohttp.ClientSession() as session:
            for language, speaker, text in test_cases:
                payload = {
                    "text": text,
                    "language": language,
                    "speaker": speaker,
                    "speed": 1.0
                }

                async with session.post(
                    f"{API_BASE_URL}/synthesize",
                    json=payload
                ) as resp:
                    assert resp.status == 200
                    audio_data = await resp.read()
                    assert len(audio_data) > 0


class TestValidation:
    """Test input validation"""

    @pytest.mark.asyncio
    async def test_empty_text(self):
        """Test that empty text is rejected"""
        async with aiohttp.ClientSession() as session:
            payload = {
                "text": "",
                "language": "EN"
            }

            async with session.post(
                f"{API_BASE_URL}/synthesize",
                json=payload
            ) as resp:
                assert resp.status == 422  # Validation error

    @pytest.mark.asyncio
    async def test_invalid_speed(self):
        """Test that invalid speed is rejected"""
        async with aiohttp.ClientSession() as session:
            # Speed too low
            payload = {
                "text": "Test",
                "language": "EN",
                "speed": 0.1  # Below minimum
            }

            async with session.post(
                f"{API_BASE_URL}/synthesize",
                json=payload
            ) as resp:
                assert resp.status == 422

            # Speed too high
            payload["speed"] = 5.0  # Above maximum
            async with session.post(
                f"{API_BASE_URL}/synthesize",
                json=payload
            ) as resp:
                assert resp.status == 422

    @pytest.mark.asyncio
    async def test_invalid_speaker(self):
        """Test that invalid speaker is handled"""
        async with aiohttp.ClientSession() as session:
            payload = {
                "text": "Test",
                "language": "EN",
                "speaker": "INVALID-SPEAKER"
            }

            async with session.post(
                f"{API_BASE_URL}/synthesize",
                json=payload
            ) as resp:
                assert resp.status == 400  # Bad request


class TestPerformance:
    """Test performance characteristics"""

    @pytest.mark.asyncio
    async def test_concurrent_requests(self):
        """Test handling multiple concurrent requests"""
        async with aiohttp.ClientSession() as session:
            async def make_request(text: str):
                payload = {
                    "text": text,
                    "language": "EN",
                    "speaker": "EN-US",
                    "speed": 1.0
                }
                async with session.post(
                    f"{API_BASE_URL}/synthesize",
                    json=payload
                ) as resp:
                    return resp.status, await resp.read()

            # Make 5 concurrent requests
            tasks = [
                make_request(f"Concurrent test number {i}")
                for i in range(5)
            ]

            results = await asyncio.gather(*tasks)

            # All should succeed
            for status, audio_data in results:
                assert status == 200
                assert len(audio_data) > 0


if __name__ == "__main__":
    # Run tests with pytest
    pytest.main([__file__, "-v", "-s"])
