"""Shared pytest fixtures and configuration."""

import pytest
from typing import Generator


@pytest.fixture
def temp_data() -> dict:
    """Fixture providing temporary test data."""
    return {
        "user_id": 1,
        "email": "test@example.com",
        "name": "Test User",
        "active": True,
    }


@pytest.fixture
def mock_config(monkeypatch) -> None:
    """Fixture for mocking environment variables."""
    monkeypatch.setenv("APP_ENV", "testing")
    monkeypatch.setenv("DATABASE_URL", "sqlite:///:memory:")
    monkeypatch.setenv("DEBUG", "true")


# Organize tests by markers
def pytest_configure(config):
    """Register custom markers."""
    config.addinivalue_line("markers", "unit: mark test as unit test")
    config.addinivalue_line("markers", "integration: mark test as integration test")
    config.addinivalue_line("markers", "e2e: mark test as end-to-end test")
    config.addinivalue_line("markers", "slow: mark test as slow")


# Example fixtures for database testing
# Uncomment and customize for your project

# @pytest.fixture
# def db_session():
#     """Database session fixture."""
#     from sqlalchemy import create_engine
#     from sqlalchemy.orm import sessionmaker
#
#     engine = create_engine("sqlite:///:memory:")
#     SessionLocal = sessionmaker(bind=engine)
#     session = SessionLocal()
#
#     yield session
#     session.close()


# Example fixtures for async testing
# @pytest.fixture
# async def async_client():
#     """Async HTTP client fixture."""
#     from httpx import AsyncClient
#     from app import app
#
#     async with AsyncClient(app=app, base_url="http://test") as client:
#         yield client
