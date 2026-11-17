# -*- coding: utf-8 -*-
"""
HTTP status code test example: success and error codes to cover per endpoint.
"""

# 200 OK - GET/PUT/PATCH success
def test_returns_200_on_success(client):
    response = client.get("/api/resource")
    assert response.status_code == 200

# 201 Created - POST create success
def test_returns_201_on_create(client):
    response = client.post("/api/resource", json={})
    assert response.status_code == 201

# 204 No Content - DELETE success
def test_returns_204_on_delete(client):
    response = client.delete("/api/resource/1")
    assert response.status_code == 204

# 400 Bad Request - parameter/validation error
def test_returns_400_on_invalid_input(client):
    response = client.post("/api/resource", json={"invalid": True})
    assert response.status_code == 400

# 401 Unauthorized - unauthenticated
def test_returns_401_without_auth(client):
    response = client.get("/api/protected")
    assert response.status_code == 401

# 403 Forbidden - no permission
def test_returns_403_without_permission(client, user_token):
    response = client.delete("/api/admin/resource", headers=user_token)
    assert response.status_code == 403

# 404 Not Found - resource does not exist
def test_returns_404_for_nonexistent(client):
    response = client.get("/api/resource/99999")
    assert response.status_code == 404

# 409 Conflict - duplicate/conflict
def test_returns_409_on_duplicate(client):
    response = client.post("/api/resource", json={"duplicate": "key"})
    assert response.status_code == 409

# 422 Unprocessable Entity - semantic error
def test_returns_422_on_semantic_error(client):
    response = client.post("/api/resource", json={"bad_semantic": True})
    assert response.status_code == 422

# 500 Internal Server Error - typically triggered via mock
def test_returns_500_on_server_error(client, mock_error):
    response = client.get("/api/resource")
    assert response.status_code == 500
