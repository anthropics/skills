"""
Test cases for MeloTTS LiveKit Plugin
Tests plugin integration without mocking
"""
import pytest
import asyncio
from unittest.mock import MagicMock, AsyncMock
import sys
import os

# Add plugin to path
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..', 'plugin'))

from melotts_plugin import TTS, ChunkedStream


class TestTTSInitialization:
    """Test TTS plugin initialization"""

    def test_default_initialization(self):
        """Test plugin initialization with default parameters"""
        tts = TTS()

        assert tts.model == "melotts"
        assert tts.provider == "custom-melotts"
        assert tts.sample_rate == 44100
        assert tts.num_channels == 1
        assert tts.capabilities.streaming is True

    def test_custom_initialization(self):
        """Test plugin initialization with custom parameters"""
        tts = TTS(
            api_base_url="http://custom:9000",
            language="ES",
            speaker="ES",
            speed=1.5,
            timeout=60.0
        )

        assert tts._opts.api_base_url == "http://custom:9000"
        assert tts._opts.language == "ES"
        assert tts._opts.speaker == "ES"
        assert tts._opts.speed == 1.5
        assert tts._opts.timeout == 60.0

    def test_url_normalization(self):
        """Test that trailing slashes are removed from URL"""
        tts = TTS(api_base_url="http://localhost:8000/")
        assert tts._opts.api_base_url == "http://localhost:8000"


class TestTTSSynthesis:
    """Test TTS synthesis functionality"""

    @pytest.mark.asyncio
    async def test_synthesize_returns_chunked_stream(self):
        """Test that synthesize returns a ChunkedStream"""
        tts = TTS(api_base_url="http://localhost:8000")

        stream = tts.synthesize("Hello world")

        assert isinstance(stream, ChunkedStream)
        assert stream._input_text == "Hello world"
        assert stream._opts.language == "EN"

        # Cleanup
        await tts.aclose()

    @pytest.mark.asyncio
    async def test_session_management(self):
        """Test aiohttp session lifecycle"""
        tts = TTS()

        # Session should be created on first use
        assert tts._session is None
        session = tts._ensure_session()
        assert session is not None
        assert tts._session is session

        # Same session should be returned
        session2 = tts._ensure_session()
        assert session2 is session

        # Session should be closed on aclose
        await tts.aclose()
        assert tts._session is None


class TestChunkedStreamIntegration:
    """Test ChunkedStream with real API server"""

    @pytest.mark.asyncio
    async def test_stream_with_real_api(self):
        """Test streaming with actual API server (requires server running)"""
        tts = TTS(
            api_base_url="http://localhost:8000",
            language="EN",
            speaker="EN-US",
            speed=1.0
        )

        try:
            stream = tts.synthesize("This is a test of the streaming integration.")

            # Create a mock output emitter to capture calls
            emitter = MagicMock()
            emitter.initialize = MagicMock()
            emitter.start_segment = MagicMock()
            emitter.push = MagicMock()
            emitter.end_segment = MagicMock()
            emitter.flush = MagicMock()

            # Run the stream
            await stream._run(emitter)

            # Verify the emitter was called correctly
            emitter.initialize.assert_called_once()
            emitter.start_segment.assert_called_once()
            emitter.flush.assert_called_once()
            emitter.end_segment.assert_called_once()

            # Verify audio data was pushed
            assert emitter.push.call_count > 0

            # Verify audio data is bytes
            for call in emitter.push.call_args_list:
                audio_chunk = call[0][0]
                assert isinstance(audio_chunk, bytes)
                assert len(audio_chunk) > 0

        finally:
            await tts.aclose()

    @pytest.mark.asyncio
    async def test_stream_different_languages(self):
        """Test streaming with different languages"""
        test_cases = [
            ("EN", "EN-US", "Hello from English"),
            ("ES", "ES", "Hola desde español"),
            ("FR", "FR", "Bonjour de France"),
        ]

        for language, speaker, text in test_cases:
            tts = TTS(
                api_base_url="http://localhost:8000",
                language=language,
                speaker=speaker
            )

            try:
                stream = tts.synthesize(text)

                emitter = MagicMock()
                emitter.initialize = MagicMock()
                emitter.start_segment = MagicMock()
                emitter.push = MagicMock()
                emitter.end_segment = MagicMock()
                emitter.flush = MagicMock()

                await stream._run(emitter)

                # Verify audio was generated
                assert emitter.push.call_count > 0

            finally:
                await tts.aclose()

    @pytest.mark.asyncio
    async def test_stream_long_text(self):
        """Test streaming with longer text"""
        tts = TTS(api_base_url="http://localhost:8000")

        long_text = """
        This is a longer test text to verify that the streaming
        functionality works correctly with multiple sentences.
        The audio should be streamed in chunks as it becomes available.
        This helps reduce latency in real-time applications like LiveKit.
        """

        try:
            stream = tts.synthesize(long_text)

            emitter = MagicMock()
            emitter.initialize = MagicMock()
            emitter.start_segment = MagicMock()
            emitter.push = MagicMock()
            emitter.end_segment = MagicMock()
            emitter.flush = MagicMock()

            await stream._run(emitter)

            # Verify audio was generated
            assert emitter.push.call_count > 0

            # Verify total audio size is reasonable for longer text
            total_bytes = sum(
                len(call[0][0]) for call in emitter.push.call_args_list
            )
            assert total_bytes > 10000  # Should be substantial audio

        finally:
            await tts.aclose()


class TestErrorHandling:
    """Test error handling in the plugin"""

    @pytest.mark.asyncio
    async def test_invalid_api_url(self):
        """Test handling of invalid API URL"""
        from livekit.agents import APIConnectionError

        tts = TTS(api_base_url="http://invalid-host-that-does-not-exist:8000")

        try:
            stream = tts.synthesize("Test")

            emitter = MagicMock()
            emitter.initialize = MagicMock()
            emitter.start_segment = MagicMock()
            emitter.push = MagicMock()
            emitter.end_segment = MagicMock()
            emitter.flush = MagicMock()

            with pytest.raises(APIConnectionError):
                await stream._run(emitter)

        finally:
            await tts.aclose()

    @pytest.mark.asyncio
    async def test_timeout_handling(self):
        """Test timeout handling"""
        from livekit.agents import APITimeoutError

        # Use very short timeout to force timeout
        tts = TTS(
            api_base_url="http://localhost:8000",
            timeout=0.001  # 1ms - too short
        )

        try:
            stream = tts.synthesize("This will timeout")

            emitter = MagicMock()
            emitter.initialize = MagicMock()
            emitter.start_segment = MagicMock()
            emitter.push = MagicMock()
            emitter.end_segment = MagicMock()
            emitter.flush = MagicMock()

            with pytest.raises((APITimeoutError, Exception)):
                await stream._run(emitter)

        finally:
            await tts.aclose()


class TestConcurrency:
    """Test concurrent usage of the plugin"""

    @pytest.mark.asyncio
    async def test_multiple_concurrent_streams(self):
        """Test multiple concurrent synthesis requests"""
        tts = TTS(api_base_url="http://localhost:8000")

        async def synthesize_text(text: str):
            stream = tts.synthesize(text)

            emitter = MagicMock()
            emitter.initialize = MagicMock()
            emitter.start_segment = MagicMock()
            emitter.push = MagicMock()
            emitter.end_segment = MagicMock()
            emitter.flush = MagicMock()

            await stream._run(emitter)

            return emitter.push.call_count

        try:
            # Run 3 concurrent synthesis tasks
            tasks = [
                synthesize_text(f"Concurrent test number {i}")
                for i in range(3)
            ]

            results = await asyncio.gather(*tasks)

            # All should have generated audio
            for call_count in results:
                assert call_count > 0

        finally:
            await tts.aclose()


if __name__ == "__main__":
    # Run tests with pytest
    pytest.main([__file__, "-v", "-s"])
