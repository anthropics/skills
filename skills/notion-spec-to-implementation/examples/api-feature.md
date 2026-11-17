# Example: API Feature Implementation

## User Request

> "Create an implementation plan for the User Profile API spec"

## Workflow Execution

### Step 1: Fetch Specification

```
Notion:notion-search
query: "User Profile API spec"
query_type: "internal"
```

Found: "User Profile API Specification" in Engineering Specs

```
Notion:notion-fetch
id: "user-profile-api-spec-page-id"
```

### Step 2: Parse Specification

**Spec Content Extracted:**

```markdown
# User Profile API Specification

## Overview
RESTful API for user profile management

## Requirements

### Functional
- FR-1: Get user profile by ID
- FR-2: Update user profile (name, bio, avatar)
- FR-3: Upload profile avatar
- FR-4: Get user's public profile (limited fields)
- FR-5: Search users by name

### Non-Functional
- NFR-1: Response time < 200ms (p95)
- NFR-2: Support 1000 concurrent users
- NFR-3: Avatar upload < 5MB
- NFR-4: GDPR compliant (data portability)

## API Endpoints

GET /api/v1/users/:id
PUT /api/v1/users/:id
POST /api/v1/users/:id/avatar
GET /api/v1/users/:id/public
GET /api/v1/users/search

## Data Model
- id (UUID)
- email (string, unique)
- name (string)
- bio (text, max 500 chars)
- avatar_url (string)
- created_at (timestamp)
- updated_at (timestamp)

## Security
- Authentication: JWT bearer token
- Authorization: Users can only update own profile
- Rate limiting: 100 req/min per user

## Acceptance Criteria
- AC-1: All endpoints return proper HTTP status codes
- AC-2: Validation errors return 400 with error details
- AC-3: Unauthorized access returns 401
- AC-4: Rate limit exceeded returns 429
- AC-5: Avatar images stored in S3
```

### Step 3: Create Implementation Plan

```
Notion:notion-create-pages

parent: { page_id: "engineering-plans-parent-id" }

pages: [{
  properties: {
    "title": "Implementation Plan: User Profile API"
  },
  content: "[Implementation plan]"
}]
```

**Implementation Plan Created:**

```markdown
# Implementation Plan: User Profile API

## Overview
Build RESTful API for user profile management with CRUD operations, avatar upload, and search functionality.

## Linked Specification
<mention-page url="...">User Profile API Specification</mention-page>

## Requirements Summary

### Functional Requirements
- ✅ Get user profile (authenticated)
- ✅ Update profile fields (name, bio)
- ✅ Upload avatar with image processing
- ✅ Public profile view (limited fields)
- ✅ User search by name

### Non-Functional Requirements
- **Performance**: < 200ms response time (p95)
- **Scalability**: 1000 concurrent users
- **Storage**: Avatar files < 5MB to S3
- **Compliance**: GDPR data portability

### Acceptance Criteria
- All endpoints with proper status codes
- Input validation with error details
- JWT authentication required
- Rate limiting enforced
- Avatars stored in S3

## Technical Approach

### Architecture
- **Framework**: Express.js (Node.js)
- **Database**: PostgreSQL
- **Storage**: AWS S3 for avatars
- **Cache**: Redis for profile data
- **Search**: PostgreSQL full-text search

### Key Design Decisions
1. **JWT Authentication**: Stateless auth, scales horizontally
2. **S3 for Avatars**: Offload storage, CDN integration ready
3. **Redis Caching**: Reduce DB load for frequently accessed profiles
4. **Rate Limiting**: Token bucket algorithm, per-user limits

## Implementation Phases

### Phase 1: Foundation (Days 1-2)
**Goal**: Set up core infrastructure

**Tasks**:
- [ ] <mention-page url="...">Setup database schema</mention-page>
- [ ] <mention-page url="...">Configure S3 bucket</mention-page>
- [ ] <mention-page url="...">Setup Redis cache</mention-page>
- [ ] <mention-page url="...">Create API scaffolding</mention-page>

**Deliverables**: Working skeleton with DB, storage, cache ready  
**Estimated effort**: 2 days

### Phase 2: Core Endpoints (Days 3-5)
**Goal**: Implement main CRUD operations

**Tasks**:
- [ ] <mention-page url="...">Implement GET user profile</mention-page>
- [ ] <mention-page url="...">Implement PUT update profile</mention-page>
- [ ] <mention-page url="...">Add input validation</mention-page>
- [ ] <mention-page url="...">Add JWT authentication middleware</mention-page>
- [ ] <mention-page url="...">Implement rate limiting</mention-page>

**Deliverables**: Working CRUD operations with auth  
**Estimated effort**: 3 days

### Phase 3: Avatar Upload (Days 6-7)
**Goal**: Avatar management with S3

**Tasks**:
- [ ] <mention-page url="...">Implement avatar upload endpoint</mention-page>
- [ ] <mention-page url="...">Add image validation (size, format)</mention-page>
- [ ] <mention-page url="...">Process and resize images</mention-page>
- [ ] <mention-page url="...">Upload to S3 with signed URLs</mention-page>

**Deliverables**: Avatar upload/update functionality  
**Estimated effort**: 2 days

### Phase 4: Search & Public Profile (Days 8-9)
**Goal**: Complete remaining features

**Tasks**:
- [ ] <mention-page url="...">Implement user search</mention-page>
- [ ] <mention-page url="...">Implement public profile endpoint</mention-page>
- [ ] <mention-page url="...">Add search indexing</mention-page>
- [ ] <mention-page url="...">Optimize search queries</mention-page>

**Deliverables**: Search and public profiles working  
**Estimated effort**: 2 days

### Phase 5: Testing & Optimization (Days 10-12)
**Goal**: Production-ready quality

**Tasks**:
- [ ] <mention-page url="...">Write unit tests</mention-page>
- [ ] <mention-page url="...">Write integration tests</mention-page>
- [ ] <mention-page url="...">Performance testing</mention-page>
- [ ] <mention-page url="...">Security audit</mention-page>
- [ ] <mention-page url="...">API documentation</mention-page>

**Deliverables**: Tested, documented, production-ready API  
**Estimated effort**: 3 days

## Dependencies

### External Dependencies
- AWS S3 bucket created ✅
- Redis instance available ✅
- PostgreSQL database provisioned ✅

### Internal Dependencies
- JWT authentication service (exists)
- User database table (exists)
- Logging infrastructure (exists)

### Blockers
None currently

## Risks & Mitigation

### Risk 1: Image Processing Performance
- **Probability**: Medium
- **Impact**: Medium
- **Mitigation**: Use background job queue for processing, return signed upload URL immediately

### Risk 2: S3 Upload Failures
- **Probability**: Low
- **Impact**: Medium
- **Mitigation**: Implement retry logic with exponential backoff, fallback to local storage temporarily

### Risk 3: Rate Limiting Complexity
- **Probability**: Low
- **Impact**: Low
- **Mitigation**: Use proven library (express-rate-limit with Redis store)

### Risk 4: Search Performance
- **Probability**: Medium
- **Impact**: Medium
- **Mitigation**: Add database indexes, consider Elasticsearch if needed later

## Timeline

| Milestone | Target Date | Status |
|-----------|-------------|--------|
| Phase 1 Complete | Oct 16 | ⏳ Planned |
| Phase 2 Complete | Oct 19 | ⏳ Planned |
| Phase 3 Complete | Oct 21 | ⏳ Planned |
| Phase 4 Complete | Oct 23 | ⏳ Planned |
| Phase 5 Complete | Oct 26 | ⏳ Planned |
| **Production Deploy** | **Oct 28** | ⏳ Planned |

**Total Duration**: 12 working days (~2.5 weeks)

## Success Criteria

### Technical Success
- [ ] All 5 endpoints implemented and working
- [ ] Response time < 200ms (p95) verified in load testing
- [ ] Handles 1000 concurrent users
- [ ] All acceptance criteria met
- [ ] Test coverage > 80%
- [ ] Security scan passed
- [ ] API documentation complete

### Business Success
- [ ] User profile updates functional
- [ ] Avatar uploads working reliably
- [ ] Search returns relevant results in < 500ms
- [ ] Zero critical bugs in first week

## Resources

### Documentation
- <mention-page url="...">User Profile API Specification</mention-page> (original spec)
- <mention-page url="...">Authentication Service Docs</mention-page>
- <mention-page url="...">AWS S3 Setup Guide</mention-page>

### Related Work
- <mention-page url="...">User Authentication API</mention-page> (similar pattern)
- <mention-page url="...">File Upload Service</mention-page> (avatar upload reference)

### External References
- Express.js best practices
- AWS S3 SDK documentation
- PostgreSQL full-text search guide

## Progress Tracking

### Phase Status
- Phase 1: ⏳ Not Started
- Phase 2: ⏳ Not Started
- Phase 3: ⏳ Not Started
- Phase 4: ⏳ Not Started
- Phase 5: ⏳ Not Started

**Overall Progress**: 0% complete

### Latest Update
*Implementation plan created on October 14, 2025*
```

### Step 4: Find Task Database

```
Notion:notion-search
query: "Tasks database"
query_type: "internal"
```

Found: "Engineering Tasks" database

### Step 5: Fetch Task Database Schema

```
Notion:notion-fetch
id: "tasks-database-id"
```

**Schema retrieved:**
- Data source: `collection://tasks-db-uuid`
- Properties: Name (title), Status (select), Priority (select), Related Tasks (relation), Story Points (number), Tags (multi_select)

### Step 6: Create Implementation Tasks

Now create tasks for Phase 1:

**Task 1: Setup database schema**

```
Notion:notion-create-pages

parent: { data_source_id: "collection://tasks-db-uuid" }

pages: [{
  properties: {
    "Name": "Setup database schema for User Profile API",
    "Status": "To Do",
    "Priority": "High",
    "Related Tasks": ["impl-plan-page-id", "spec-page-id"],
    "Story Points": 3,
    "Tags": "backend, database, api"
  },
  content: "## Context\nImplementation task for <mention-page url=\"...\">User Profile API Specification</mention-page>\n\nPart of <mention-page url=\"...\">Implementation Plan: User Profile API</mention-page> - Phase 1\n\n## Objective\nCreate database schema for user profile storage\n\n## Requirements\nBased on spec data model:\n- id (UUID, primary key)\n- email (string, unique index)\n- name (string, not null)\n- bio (text, max 500 chars)\n- avatar_url (string, nullable)\n- created_at (timestamp)\n- updated_at (timestamp)\n\n## Acceptance Criteria\n- [ ] Migration file created\n- [ ] Schema includes all required fields\n- [ ] Indexes on email (unique) and name (search)\n- [ ] Constraints validated (bio length, email format)\n- [ ] Migration tested on dev database\n- [ ] Rollback migration created\n\n## Technical Approach\n```sql\nCREATE TABLE user_profiles (\n  id UUID PRIMARY KEY DEFAULT gen_random_uuid(),\n  email VARCHAR(255) UNIQUE NOT NULL,\n  name VARCHAR(255) NOT NULL,\n  bio TEXT CHECK (length(bio) <= 500),\n  avatar_url TEXT,\n  created_at TIMESTAMP DEFAULT NOW(),\n  updated_at TIMESTAMP DEFAULT NOW()\n);\n\nCREATE INDEX idx_user_profiles_email ON user_profiles(email);\nCREATE INDEX idx_user_profiles_name ON user_profiles USING gin(to_tsvector('english', name));\n```\n\n## Dependencies\n- Blocked By: None\n- Blocks: All Phase 2 tasks\n\n## Estimated Effort\n3 story points (half day)\n"
}]
```

*[Create similar tasks for all phases - 20 tasks total]*

### Step 7: Link Plan Back to Spec

```
Notion:notion-update-page
page_id: "user-profile-api-spec-page-id"
command: "insert_content_after"
selection_with_ellipsis: "## Acceptance Criteria..."
new_str: "

---

## Implementation

**Implementation Plan**: <mention-page url=\"...\">Implementation Plan: User Profile API</mention-page>

**Implementation Tasks**: See plan for full task breakdown (20 tasks across 5 phases)

**Status**: Planning complete, ready to start implementation
"
```

## Summary Provided to User

```markdown
## Implementation Plan Created ✅

### Plan Overview
- **Feature**: User Profile API
- **Duration**: 12 days (~2.5 weeks)
- **Phases**: 5 (Foundation → Core → Avatar → Search → Testing)
- **Tasks**: 20 tasks created
- **Target Launch**: October 28, 2025

### Implementation Phases

**Phase 1: Foundation** (2 days)
- Database schema
- S3 and Redis setup
- API scaffolding

**Phase 2: Core Endpoints** (3 days)
- GET/PUT user profile
- Authentication & validation
- Rate limiting

**Phase 3: Avatar Upload** (2 days)
- Image upload & validation
- S3 integration
- Image processing

**Phase 4: Search & Public Profile** (2 days)
- User search
- Public profile endpoint

**Phase 5: Testing & Optimization** (3 days)
- Unit & integration tests
- Performance testing
- Documentation

### Key Deliverables
- 5 REST API endpoints
- Avatar upload to S3
- User search functionality
- Comprehensive tests
- API documentation

### Links Created
✅ Plan page: <mention-page url="...">Implementation Plan: User Profile API</mention-page>
✅ Spec updated with plan link
✅ 20 tasks created in task database
✅ All tasks linked to plan and spec

### Next Steps
1. Review and approve plan
2. Assign tasks to team members
3. Begin Phase 1 (Foundation)
4. Daily standups for progress tracking

**Ready to start implementation! 🚀**
```

## Key Features Demonstrated

### Spec Parsing
- Extracted requirements (functional & non-functional)
- Identified API endpoints
- Noted data model
- Captured acceptance criteria
- Understood security requirements

### Implementation Planning
- Broke into logical phases
- Sequenced work appropriately (foundation → features → testing)
- Identified dependencies
- Estimated effort per phase
- Created realistic timeline

### Task Creation
- Generated 20 specific tasks
- Each task has context, acceptance criteria, technical approach
- Tasks link to both spec and plan
- Proper dependencies noted

### Bidirectional Linking
- Plan links to spec
- Spec updated to link to plan
- Tasks link to both
- Easy navigation between all artifacts

Perfect for: Feature implementation, API development, technical projects

