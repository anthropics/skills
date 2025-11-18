# FastAPI Patterns for Modal

Common REST API patterns using FastAPI on Modal, covering request handling, validation, authentication, and responses.

## Basic FastAPI Setup

```python
import modal
from fastapi import FastAPI

app = modal.App("my-api")
web_app = FastAPI()

@web_app.get("/")
def root():
    return {"message": "Hello, World!"}

@app.function()
@modal.asgi_app()
def serve():
    return web_app
```

Access at: `https://{workspace}--my-api-serve.modal.run`

## Request Validation with Pydantic

Define request/response models for automatic validation:

```python
from pydantic import BaseModel, Field
from typing import Optional

class CreateItemRequest(BaseModel):
    name: str = Field(..., min_length=1, max_length=100)
    description: Optional[str] = None
    quantity: int = Field(..., ge=0)  # Greater than or equal to 0

class ItemResponse(BaseModel):
    id: str
    name: str
    description: Optional[str]
    quantity: int
    created_at: str

@web_app.post("/items", response_model=ItemResponse)
def create_item(request: CreateItemRequest):
    item_id = generate_id()
    # Save to volume...
    return ItemResponse(
        id=item_id,
        name=request.name,
        description=request.description,
        quantity=request.quantity,
        created_at=datetime.utcnow().isoformat()
    )
```

**Benefits:**
- Automatic request validation
- Auto-generated OpenAPI docs
- Type safety
- Clear error messages for invalid requests

## Authentication Patterns

### Bearer Token Authentication

```python
from fastapi import Security, HTTPException
from fastapi.security import HTTPBearer, HTTPAuthorizationCredentials

security = HTTPBearer()

def validate_api_key(api_key: str) -> bool:
    """Validate API key against your auth system."""
    # Example: Check against external service
    # In production, verify with your auth provider
    return api_key.startswith("valid-key-")

@web_app.get("/protected")
def protected_endpoint(credentials: HTTPAuthorizationCredentials = Security(security)):
    api_key = credentials.credentials
    
    if not validate_api_key(api_key):
        raise HTTPException(status_code=401, detail="Invalid API key")
    
    return {"message": "Authorized", "api_key": api_key}
```

**Usage:**
```bash
curl -H "Authorization: Bearer valid-key-123" \
  https://your-api.modal.run/protected
```

### Dependency Injection for Auth

```python
from fastapi import Depends

async def get_current_user(credentials: HTTPAuthorizationCredentials = Security(security)) -> str:
    """Dependency that validates and returns user ID."""
    api_key = credentials.credentials
    
    if not validate_api_key(api_key):
        raise HTTPException(status_code=401, detail="Invalid API key")
    
    # Return user ID or user object
    return extract_user_id(api_key)

@web_app.get("/me")
def get_profile(user_id: str = Depends(get_current_user)):
    """Endpoint automatically requires valid auth."""
    return {"user_id": user_id, "profile": get_user_profile(user_id)}

@web_app.post("/items")
def create_item(item: CreateItemRequest, user_id: str = Depends(get_current_user)):
    """Create item for authenticated user."""
    save_item(user_id, item)
    return {"status": "created"}
```

## Error Handling

### Custom Error Responses

```python
from fastapi import HTTPException, status

@web_app.get("/items/{item_id}")
def get_item(item_id: str):
    item = load_item(item_id)
    
    if item is None:
        raise HTTPException(
            status_code=status.HTTP_404_NOT_FOUND,
            detail=f"Item {item_id} not found"
        )
    
    return item
```

### Exception Handlers

```python
from fastapi import Request
from fastapi.responses import JSONResponse

@web_app.exception_handler(ValueError)
async def value_error_handler(request: Request, exc: ValueError):
    return JSONResponse(
        status_code=400,
        content={"error": "Invalid input", "detail": str(exc)}
    )

@web_app.exception_handler(Exception)
async def general_exception_handler(request: Request, exc: Exception):
    # Log error
    print(f"Unhandled error: {exc}")
    
    return JSONResponse(
        status_code=500,
        content={"error": "Internal server error"}
    )
```

## CRUD Operations Pattern

```python
from typing import List
from fastapi import HTTPException, status

# CREATE
@web_app.post("/items", status_code=status.HTTP_201_CREATED)
def create_item(item: CreateItemRequest, user_id: str = Depends(get_current_user)):
    item_id = generate_id()
    save_item(user_id, item_id, item.dict())
    return {"id": item_id, **item.dict()}

# READ (single)
@web_app.get("/items/{item_id}")
def get_item(item_id: str, user_id: str = Depends(get_current_user)):
    item = load_item(user_id, item_id)
    
    if not item:
        raise HTTPException(status_code=404, detail="Item not found")
    
    # Verify ownership
    if item.get("user_id") != user_id:
        raise HTTPException(status_code=403, detail="Forbidden")
    
    return item

# READ (list)
@web_app.get("/items", response_model=List[ItemResponse])
def list_items(user_id: str = Depends(get_current_user)):
    items = load_user_items(user_id)
    return items

# UPDATE
@web_app.put("/items/{item_id}")
def update_item(
    item_id: str,
    updates: CreateItemRequest,
    user_id: str = Depends(get_current_user)
):
    item = load_item(user_id, item_id)
    
    if not item:
        raise HTTPException(status_code=404, detail="Item not found")
    
    if item.get("user_id") != user_id:
        raise HTTPException(status_code=403, detail="Forbidden")
    
    updated_item = {**item, **updates.dict(exclude_unset=True)}
    save_item(user_id, item_id, updated_item)
    return updated_item

# DELETE
@web_app.delete("/items/{item_id}", status_code=status.HTTP_204_NO_CONTENT)
def delete_item(item_id: str, user_id: str = Depends(get_current_user)):
    item = load_item(user_id, item_id)
    
    if not item:
        raise HTTPException(status_code=404, detail="Item not found")
    
    if item.get("user_id") != user_id:
        raise HTTPException(status_code=403, detail="Forbidden")
    
    delete_item_from_storage(user_id, item_id)
    return None  # 204 No Content
```

## Content Negotiation

Serve different formats based on Accept header:

```python
from fastapi import Request
from fastapi.responses import HTMLResponse, JSONResponse

@web_app.get("/")
async def root(request: Request):
    accept_header = request.headers.get("accept", "")
    wants_html = "text/html" in accept_header
    
    if wants_html:
        html_content = """
        <!DOCTYPE html>
        <html>
        <head><title>My API</title></head>
        <body>
            <h1>Welcome to My API</h1>
            <p>Visit <a href="/docs">/docs</a> for API documentation</p>
        </body>
        </html>
        """
        return HTMLResponse(content=html_content)
    
    return JSONResponse(content={
        "service": "My API",
        "version": "1.0.0",
        "endpoints": {
            "/items": "Manage items",
            "/docs": "API documentation"
        }
    })
```

**Browser visits** → HTML landing page  
**curl/API clients** → JSON response

## Query Parameters

```python
from typing import Optional

@web_app.get("/items")
def list_items(
    limit: int = 10,
    offset: int = 0,
    sort_by: Optional[str] = None,
    filter_status: Optional[str] = None,
    user_id: str = Depends(get_current_user)
):
    """
    List items with pagination and filtering.
    
    - limit: Max items to return (default 10)
    - offset: Skip first N items (default 0)
    - sort_by: Field to sort by (optional)
    - filter_status: Filter by status (optional)
    """
    items = load_user_items(user_id)
    
    # Apply filters
    if filter_status:
        items = [i for i in items if i.get("status") == filter_status]
    
    # Apply sorting
    if sort_by:
        items.sort(key=lambda x: x.get(sort_by, ""))
    
    # Apply pagination
    total = len(items)
    items = items[offset:offset + limit]
    
    return {
        "items": items,
        "total": total,
        "limit": limit,
        "offset": offset
    }
```

**Usage:**
```bash
curl "https://api.modal.run/items?limit=20&offset=40&filter_status=active"
```

## Request Body with Multiple Content Types

```python
from fastapi import File, UploadFile, Form

@web_app.post("/upload")
async def upload_file(
    file: UploadFile = File(...),
    description: str = Form(None),
    user_id: str = Depends(get_current_user)
):
    """Upload file with form data."""
    content = await file.read()
    
    # Save to volume
    save_user_file(user_id, file.filename, content)
    
    return {
        "filename": file.filename,
        "size": len(content),
        "description": description
    }
```

## Response Models and Status Codes

```python
from fastapi import status

class SuccessResponse(BaseModel):
    message: str
    data: dict

class ErrorResponse(BaseModel):
    error: str
    detail: str

@web_app.post("/items", 
    status_code=status.HTTP_201_CREATED,
    response_model=SuccessResponse,
    responses={
        400: {"model": ErrorResponse, "description": "Invalid input"},
        401: {"model": ErrorResponse, "description": "Unauthorized"},
        409: {"model": ErrorResponse, "description": "Item already exists"}
    }
)
def create_item(item: CreateItemRequest, user_id: str = Depends(get_current_user)):
    """Create new item with documented responses."""
    if item_exists(user_id, item.name):
        raise HTTPException(
            status_code=409,
            detail=f"Item '{item.name}' already exists"
        )
    
    item_id = save_item(user_id, item.dict())
    
    return SuccessResponse(
        message="Item created successfully",
        data={"id": item_id}
    )
```

## Background Tasks

Execute non-blocking work after returning response:

```python
from fastapi import BackgroundTasks

def send_notification(user_id: str, message: str):
    """Send notification (slow operation)."""
    # Call external API, send email, etc.
    print(f"Sending notification to {user_id}: {message}")

@web_app.post("/items")
def create_item(
    item: CreateItemRequest,
    background_tasks: BackgroundTasks,
    user_id: str = Depends(get_current_user)
):
    """Create item and send notification in background."""
    item_id = save_item(user_id, item.dict())
    
    # Schedule background task
    background_tasks.add_task(
        send_notification,
        user_id,
        f"Item '{item.name}' created successfully"
    )
    
    # Return immediately
    return {"id": item_id, "status": "created"}
```

## CORS Configuration

Allow cross-origin requests:

```python
from fastapi.middleware.cors import CORSMiddleware

web_app.add_middleware(
    CORSMiddleware,
    allow_origins=["https://myapp.com"],  # Or ["*"] for all
    allow_credentials=True,
    allow_methods=["*"],
    allow_headers=["*"],
)
```

## Request Logging

```python
import time
from fastapi import Request

@web_app.middleware("http")
async def log_requests(request: Request, call_next):
    start_time = time.time()
    
    # Process request
    response = await call_next(request)
    
    # Log after response
    duration = time.time() - start_time
    print(f"{request.method} {request.url.path} - {response.status_code} - {duration:.3f}s")
    
    return response
```

## OpenAPI Documentation

FastAPI automatically generates `/docs` (Swagger UI) and `/redoc` (ReDoc).

**Customize:**
```python
web_app = FastAPI(
    title="My API",
    description="API for managing items",
    version="1.0.0",
    docs_url="/docs",
    redoc_url="/redoc",
    openapi_url="/openapi.json"
)
```

## Testing FastAPI on Modal

```python
from fastapi.testclient import TestClient

# In your tests
client = TestClient(web_app)

def test_create_item():
    response = client.post(
        "/items",
        json={"name": "Test", "quantity": 5},
        headers={"Authorization": "Bearer test-key"}
    )
    assert response.status_code == 201
    assert response.json()["name"] == "Test"
```

## Best Practices

**Request Validation:**
- Always use Pydantic models for requests
- Set appropriate field constraints (min_length, ge, le, regex)
- Use Optional for optional fields

**Response Models:**
- Define response models for consistency
- Document different status codes
- Return appropriate HTTP status codes

**Authentication:**
- Use dependency injection for reusable auth
- Validate on every protected endpoint
- Return 401 for auth failures, 403 for permission denials

**Error Handling:**
- Catch and handle specific exceptions
- Return clear error messages
- Log errors for debugging

**Documentation:**
- Add docstrings to endpoints
- Document query parameters
- Specify response models and status codes
