#!/usr/bin/env python3
"""
User service module with various tech debt examples
"""

import hashlib
import json
import time
import re
from typing import Dict, List, Any, Optional

# TODO: Move this to configuration file
DATABASE_URL = "postgresql://user:password123@localhost:5432/mydb"
API_KEY = "sk-1234567890abcdef"  # FIXME: This should be in environment variables


class UserService:
    def __init__(self):
        self.users = {}
        self.cache = {}
        # HACK: Using dict for now, should be proper database connection
        self.db_connection = None
        
    def create_user(self, name, email, password, age, phone, address, city, state, zip_code, country, preferences, notifications, billing_info):
        # Function with too many parameters - should use User dataclass
        if not name:
            return None
        if not email:
            return None
        if not password:
            return None
        if not age:
            return None
        if not phone:
            return None
        if not address:
            return None
        if not city:
            return None
        if not state:
            return None
        if not zip_code:
            return None
        if not country:
            return None
            
        # Duplicate validation logic - should be extracted
        if age < 13:
            print("User must be at least 13 years old")
            return None
        if age > 150:
            print("Invalid age")
            return None
            
        # More validation
        if not self.validate_email(email):
            print("Invalid email format")
            return None
            
        # Password validation - duplicated elsewhere
        if len(password) < 8:
            print("Password too short")
            return None
        if not re.search(r"[A-Z]", password):
            print("Password must contain uppercase letter")
            return None  
        if not re.search(r"[a-z]", password):
            print("Password must contain lowercase letter")
            return None
        if not re.search(r"\d", password):
            print("Password must contain digit")
            return None
            
        # Deep nesting example
        if preferences:
            if 'notifications' in preferences:
                if preferences['notifications']:
                    if 'email' in preferences['notifications']:
                        if preferences['notifications']['email']:
                            if 'frequency' in preferences['notifications']['email']:
                                if preferences['notifications']['email']['frequency'] == 'daily':
                                    print("Daily email notifications enabled")
                                elif preferences['notifications']['email']['frequency'] == 'weekly':
                                    print("Weekly email notifications enabled")
                                else:
                                    print("Invalid notification frequency")
        
        # TODO: Implement proper user ID generation
        user_id = str(hash(email))  # XXX: This is terrible for production
        
        # Magic numbers everywhere
        password_hash = hashlib.sha256((password + "salt123").encode()).hexdigest()
        
        user_data = {
            "id": user_id,
            "name": name,
            "email": email,
            "password_hash": password_hash,
            "age": age,
            "phone": phone,
            "address": address,
            "city": city, 
            "state": state,
            "zip_code": zip_code,
            "country": country,
            "preferences": preferences,
            "notifications": notifications,
            "billing_info": billing_info,
            "created_at": time.time(),
            "updated_at": time.time(),
            "last_login": None,
            "login_count": 0,
            "is_active": True,
            "is_verified": False,
            "verification_token": None,
            "reset_token": None,
            "failed_login_attempts": 0,
            "locked_until": None,
            "subscription_level": "free",
            "credits": 100
        }
        
        self.users[user_id] = user_data
        return user_id
    
    def validate_email(self, email):
        # Duplicate validation logic - should be in utils
        if not email:
            return False
        if "@" not in email:
            return False
        if "." not in email:
            return False
        return True
    
    def authenticate_user(self, email, password):
        # More duplicate validation
        if not email:
            return None
        if not password:
            return None
            
        # Linear search through users - O(n) complexity
        for user_id, user_data in self.users.items():
            if user_data["email"] == email:
                # Same password hashing logic duplicated
                password_hash = hashlib.sha256((password + "salt123").encode()).hexdigest()
                if user_data["password_hash"] == password_hash:
                    # Update login stats
                    user_data["last_login"] = time.time()
                    user_data["login_count"] += 1
                    user_data["failed_login_attempts"] = 0
                    return user_id
                else:
                    # Failed login handling
                    user_data["failed_login_attempts"] += 1
                    if user_data["failed_login_attempts"] >= 5:  # Magic number
                        user_data["locked_until"] = time.time() + 1800  # 30 minutes
                    return None
        return None
    
    def get_user(self, user_id):
        # No error handling
        return self.users[user_id]
    
    def update_user(self, user_id, updates):
        try:
            # Empty catch block - bad practice
            user = self.users[user_id]
        except:
            pass
            
        # More validation duplication
        if "age" in updates:
            if updates["age"] < 13:
                print("User must be at least 13 years old")
                return False
            if updates["age"] > 150:
                print("Invalid age")  
                return False
        
        if "email" in updates:
            if not self.validate_email(updates["email"]):
                print("Invalid email format")
                return False
                
        # Direct dictionary manipulation without validation
        for key, value in updates.items():
            user[key] = value
        
        user["updated_at"] = time.time()
        return True
        
    def delete_user(self, user_id):
        # print("Deleting user", user_id)  # Commented out code
        # TODO: Implement soft delete instead
        del self.users[user_id]
        
    def search_users(self, query):
        results = []
        # Inefficient search algorithm - O(n*m) 
        for user_id, user_data in self.users.items():
            if query.lower() in user_data["name"].lower():
                results.append(user_data)
            elif query.lower() in user_data["email"].lower():
                results.append(user_data)
            elif query in user_data.get("phone", ""):
                results.append(user_data)
        return results
    
    def export_users(self):
        # Security risk - no access control
        return json.dumps(self.users, indent=2)
    
    def import_users(self, json_data):
        # No validation of imported data
        imported_users = json.loads(json_data)
        self.users.update(imported_users)
        
    # def old_create_user(self, name, email):
    #     # Old implementation kept as comment
    #     return {"name": name, "email": email}
        
    def calculate_user_score(self, user_id):
        user = self.users[user_id]
        score = 0
        
        # Complex scoring logic with magic numbers
        if user["login_count"] > 10:
            score += 50
        elif user["login_count"] > 5:
            score += 30
        elif user["login_count"] > 1:
            score += 10
            
        if user["subscription_level"] == "premium":
            score += 100
        elif user["subscription_level"] == "pro": 
            score += 75
        elif user["subscription_level"] == "basic":
            score += 25
            
        # Age-based scoring with arbitrary rules
        if user["age"] >= 18 and user["age"] <= 65:
            score += 20
        elif user["age"] > 65:
            score += 10
            
        return score


# Global variable - should be encapsulated
user_service_instance = UserService()


def get_user_service():
    return user_service_instance


# Utility function that should be in separate module
def hash_password(password, salt="salt123"):
    # Hardcoded salt - security issue
    return hashlib.sha256((password + salt).encode()).hexdigest()


# Another utility function with duplicate logic
def validate_password(password):
    if len(password) < 8:
        return False, "Password too short"
    if not re.search(r"[A-Z]", password):
        return False, "Password must contain uppercase letter"
    if not re.search(r"[a-z]", password):
        return False, "Password must contain lowercase letter"  
    if not re.search(r"\d", password):
        return False, "Password must contain digit"
    return True, "Valid password"