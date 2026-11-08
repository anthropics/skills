# -*- coding: utf-8 -*-
"""
REST API integration test example (full version in SKILL history or expand as needed).

Use with: FastAPI TestClient + local DB; or for external HTTP API use requests + base_url, with fixture providing api_client/base_url.
One class per endpoint, one test_xxx per scenario; cover both positive (success codes) and negative (400/401/403/404/409).
"""

import pytest
from fastapi.testclient import TestClient
from sqlalchemy.orm import Session

# from src.models import User


# ============================================================================
# GET /api/users - List
# ============================================================================

class TestGetUsers:
    """GET /api/users example: empty list, pagination, invalid params."""

    def test_get_users_empty_returns_empty_list(self, client: TestClient):
        response = client.get("/api/users")
        assert response.status_code == 200
        assert response.json() == []

    def test_get_users_with_pagination(self, client: TestClient, db: Session):
        # Arrange: create data then request
        # response = client.get("/api/users?limit=5&offset=0")
        # assert response.status_code == 200
        # assert len(response.json()) == 5
        pass

    def test_get_users_invalid_limit_returns_400(self, client: TestClient):
        response = client.get("/api/users?limit=-1")
        assert response.status_code == 400


# ============================================================================
# GET /api/users/:id - Detail
# ============================================================================

class TestGetUserById:
    """GET /api/users/:id: success, 404, invalid ID."""

    def test_get_user_nonexistent_id_returns_404(self, client: TestClient):
        response = client.get("/api/users/99999")
        assert response.status_code == 404

    def test_get_user_invalid_id_format_returns_400(self, client: TestClient):
        response = client.get("/api/users/invalid-id")
        assert response.status_code == 400


# ============================================================================
# POST /api/users - Create
# ============================================================================

class TestCreateUser:
    """POST /api/users: 201, missing required 400, duplicate 409, no auth 401, non-admin 403."""

    def test_create_user_missing_required_field_returns_400(self, client: TestClient, admin_headers: dict):
        invalid_data = {"name": "User", "password": "password"}  # missing email
        response = client.post("/api/users", json=invalid_data, headers=admin_headers)
        assert response.status_code == 400

    def test_create_user_without_auth_returns_401(self, client: TestClient):
        response = client.post("/api/users", json={"name": "x", "email": "x@x.com", "password": "x"})
        assert response.status_code == 401


# ============================================================================
# PUT /api/users/:id, PATCH, DELETE: same pattern - success codes + 404/403/401 negative cases
# ============================================================================

class TestDeleteUser:
    """DELETE /api/users/:id: 204, 404, 401, 403."""

    def test_delete_user_nonexistent_returns_404(self, client: TestClient, admin_headers: dict):
        response = client.delete("/api/users/99999", headers=admin_headers)
        assert response.status_code == 404
