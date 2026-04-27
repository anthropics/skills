# -*- coding: utf-8 -*-
"""
GraphQL API test example: queries and mutations, asserting status 200 and data structure.
"""

import pytest
from fastapi.testclient import TestClient
from sqlalchemy.orm import Session


class TestGraphQLQueries:
    """GraphQL query example."""

    def test_query_users_returns_list(self, client: TestClient, db: Session):
        # create_test_users(db, count=3)
        query = """
        query {
            users {
                id
                name
                email
            }
        }
        """
        response = client.post("/graphql", json={"query": query})
        assert response.status_code == 200
        data = response.json().get("data", {})
        assert "users" in data

    def test_query_user_by_id_returns_user(self, client: TestClient, test_user):
        query = """
        query {{
            user(id: {}) {{
                id
                name
                email
            }}
        }}
        """.format(test_user.id)
        response = client.post("/graphql", json={"query": query})
        assert response.status_code == 200
        data = response.json().get("data", {}).get("user")
        assert data is not None


class TestGraphQLMutations:
    """GraphQL mutation example."""

    def test_create_user_mutation_creates_user(self, client: TestClient, db: Session, admin_headers: dict):
        mutation = """
        mutation {
            createUser(input: {
                name: "New User",
                email: "newuser@example.com",
                password: "SecurePass123"
            }) {
                user {
                    id
                    name
                    email
                }
            }
        }
        """
        response = client.post("/graphql", json={"query": mutation}, headers=admin_headers)
        assert response.status_code == 200
        data = response.json().get("data", {}).get("createUser", {}).get("user")
        assert data is not None
        assert data.get("email") == "newuser@example.com"
