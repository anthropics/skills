"""
Simple client to test the MeloTTS API Server
This script tests the API without LiveKit to verify it works correctly
"""
import asyncio
import aiohttp
import sys


API_BASE_URL = "http://localhost:8000"


async def test_health():
    """Test API health endpoint"""
    print("Testing health endpoint...")
    async with aiohttp.ClientSession() as session:
        async with session.get(f"{API_BASE_URL}/") as resp:
            data = await resp.json()
            print(f"✓ Health check: {data}")
            return resp.status == 200


async def test_list_voices():
    """Test listing available voices"""
    print("\nTesting voice listing...")
    async with aiohttp.ClientSession() as session:
        for lang in ["EN", "ES", "FR"]:
            async with session.get(f"{API_BASE_URL}/voices?language={lang}") as resp:
                if resp.status == 200:
                    data = await resp.json()
                    print(f"✓ {lang} voices: {data['voices']}")
                else:
                    print(f"✗ Failed to get voices for {lang}")
                    return False
    return True


async def test_synthesize(output_file: str = "test_output.wav"):
    """Test synthesis endpoint"""
    print(f"\nTesting synthesis (saving to {output_file})...")

    async with aiohttp.ClientSession() as session:
        payload = {
            "text": "Hello! This is a test of the MeloTTS API server. The quick brown fox jumps over the lazy dog.",
            "language": "EN",
            "speaker": "EN-US",
            "speed": 1.0
        }

        async with session.post(
            f"{API_BASE_URL}/synthesize",
            json=payload
        ) as resp:
            if resp.status == 200:
                audio_data = await resp.read()
                with open(output_file, "wb") as f:
                    f.write(audio_data)
                print(f"✓ Synthesis successful: {len(audio_data)} bytes saved to {output_file}")
                return True
            else:
                error = await resp.text()
                print(f"✗ Synthesis failed: {error}")
                return False


async def test_streaming(output_file: str = "test_stream_output.wav"):
    """Test streaming synthesis endpoint"""
    print(f"\nTesting streaming synthesis (saving to {output_file})...")

    async with aiohttp.ClientSession() as session:
        payload = {
            "text": "This is a streaming test. The audio should arrive in chunks.",
            "language": "EN",
            "speaker": "EN-US",
            "speed": 1.0
        }

        async with session.post(
            f"{API_BASE_URL}/synthesize/stream",
            json=payload
        ) as resp:
            if resp.status == 200:
                chunks = []
                chunk_count = 0

                async for chunk, _ in resp.content.iter_chunks():
                    if chunk:
                        chunks.append(chunk)
                        chunk_count += 1
                        print(f"  Received chunk {chunk_count}: {len(chunk)} bytes")

                audio_data = b"".join(chunks)
                with open(output_file, "wb") as f:
                    f.write(audio_data)

                print(f"✓ Streaming successful: {len(audio_data)} bytes in {chunk_count} chunks")
                print(f"  Saved to {output_file}")
                return True
            else:
                error = await resp.text()
                print(f"✗ Streaming failed: {error}")
                return False


async def test_different_languages():
    """Test synthesis with different languages"""
    print("\nTesting different languages...")

    test_cases = [
        ("EN", "EN-US", "Hello from English"),
        ("EN", "EN-BR", "Hello from Britain"),
        ("ES", "ES", "Hola desde español"),
        ("FR", "FR", "Bonjour de France"),
    ]

    async with aiohttp.ClientSession() as session:
        for lang, speaker, text in test_cases:
            payload = {
                "text": text,
                "language": lang,
                "speaker": speaker,
                "speed": 1.0
            }

            async with session.post(
                f"{API_BASE_URL}/synthesize",
                json=payload
            ) as resp:
                if resp.status == 200:
                    audio_data = await resp.read()
                    print(f"✓ {lang}-{speaker}: {len(audio_data)} bytes")
                else:
                    print(f"✗ {lang}-{speaker}: Failed")
                    return False

    return True


async def test_different_speeds():
    """Test synthesis with different speeds"""
    print("\nTesting different speeds...")

    async with aiohttp.ClientSession() as session:
        for speed in [0.5, 1.0, 1.5, 2.0]:
            payload = {
                "text": "Testing speed variation.",
                "language": "EN",
                "speaker": "EN-US",
                "speed": speed
            }

            async with session.post(
                f"{API_BASE_URL}/synthesize",
                json=payload
            ) as resp:
                if resp.status == 200:
                    audio_data = await resp.read()
                    print(f"✓ Speed {speed}x: {len(audio_data)} bytes")
                else:
                    print(f"✗ Speed {speed}x: Failed")
                    return False

    return True


async def main():
    """Run all tests"""
    print("=" * 60)
    print("MeloTTS API Server Test Suite")
    print("=" * 60)

    try:
        # Check if server is running
        async with aiohttp.ClientSession() as session:
            try:
                async with session.get(f"{API_BASE_URL}/", timeout=aiohttp.ClientTimeout(total=2)) as resp:
                    if resp.status != 200:
                        print("✗ Server is not responding correctly")
                        sys.exit(1)
            except Exception as e:
                print(f"✗ Cannot connect to server at {API_BASE_URL}")
                print(f"  Error: {e}")
                print(f"\nPlease start the server first:")
                print(f"  cd api && python server.py")
                sys.exit(1)

        # Run tests
        tests = [
            ("Health Check", test_health),
            ("List Voices", test_list_voices),
            ("Basic Synthesis", test_synthesize),
            ("Streaming Synthesis", test_streaming),
            ("Different Languages", test_different_languages),
            ("Different Speeds", test_different_speeds),
        ]

        results = []
        for name, test_func in tests:
            try:
                result = await test_func()
                results.append((name, result))
            except Exception as e:
                print(f"✗ {name} failed with exception: {e}")
                results.append((name, False))

        # Print summary
        print("\n" + "=" * 60)
        print("Test Summary")
        print("=" * 60)

        passed = sum(1 for _, result in results if result)
        total = len(results)

        for name, result in results:
            status = "✓ PASS" if result else "✗ FAIL"
            print(f"{status}: {name}")

        print(f"\nTotal: {passed}/{total} tests passed")

        if passed == total:
            print("\n✓ All tests passed!")
            sys.exit(0)
        else:
            print(f"\n✗ {total - passed} test(s) failed")
            sys.exit(1)

    except KeyboardInterrupt:
        print("\n\nTests interrupted by user")
        sys.exit(1)


if __name__ == "__main__":
    asyncio.run(main())
