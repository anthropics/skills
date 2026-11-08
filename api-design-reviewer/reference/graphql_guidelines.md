# GraphQL API Design Guidelines

Comprehensive guide for designing production-ready GraphQL APIs.

## Table of Contents
1. [Schema Design](#schema-design)
2. [Query Design](#query-design)
3. [Mutation Design](#mutation-design)
4. [Security](#security)
5. [Performance](#performance)
6. [Error Handling](#error-handling)

---

## Schema Design

### Type Naming Conventions

```graphql
# ✅ GOOD: Clear, descriptive names
type User {
  id: ID!
  email: String!
  firstName: String
  lastName: String
  createdAt: DateTime!
}

type Order {
  id: ID!
  orderNumber: String!
  total: Money!
  status: OrderStatus!
}

enum OrderStatus {
  PENDING
  PROCESSING
  SHIPPED
  DELIVERED
  CANCELLED
}

# ❌ BAD: Abbreviations, unclear names
type Usr {
  id: ID!
  em: String!
  fn: String
}
```

### Nullable vs Non-Nullable Fields

**Rule of Thumb:**
- Fields nullable by default
- Non-null only when guaranteed to exist

```graphql
type User {
  # Non-null: Always exists
  id: ID!
  email: String!
  createdAt: DateTime!

  # Nullable: May not exist
  phoneNumber: String
  bio: String
  lastLoginAt: DateTime

  # Non-null list of non-null items
  roles: [Role!]!  # List always exists, items never null

  # Nullable list of nullable items
  preferences: [Preference]  # List and items can be null
}
```

**Why default to nullable?**
- Schema evolution: Adding non-null fields breaks clients
- Partial failures: Can return partial data with errors
- Flexibility: Easier to relax (nullable → non-null) than tighten

### Connections Pattern (Pagination)

**Use Relay Connection Specification:**

```graphql
type Query {
  users(
    first: Int
    after: String
    last: Int
    before: String
    filter: UserFilter
  ): UserConnection!
}

type UserConnection {
  edges: [UserEdge!]!
  pageInfo: PageInfo!
  totalCount: Int
}

type UserEdge {
  node: User!
  cursor: String!
}

type PageInfo {
  hasNextPage: Boolean!
  hasPreviousPage: Boolean!
  startCursor: String
  endCursor: String
}

input UserFilter {
  role: Role
  status: UserStatus
  createdAfter: DateTime
}
```

**Why Connections?**
- Cursor-based pagination (stable, performant)
- Supports bidirectional pagination
- Standardized across industry
- Works well with infinite scroll

### Input Types

```graphql
# Separate input types from output types
input CreateUserInput {
  email: String!
  firstName: String!
  lastName: String!
  password: String!
}

input UpdateUserInput {
  firstName: String
  lastName: String
  bio: String
  # email NOT included (can't be changed)
}

type CreateUserPayload {
  user: User
  errors: [Error!]
}
```

**Benefits:**
- Clear separation of concerns
- Different validation rules for create vs update
- Can evolve independently

---

## Query Design

### Field Arguments

```graphql
type Query {
  # Single resource by ID
  user(id: ID!): User

  # Collection with filtering
  users(
    filter: UserFilter
    sort: UserSort
    first: Int = 20
    after: String
  ): UserConnection!

  # Search
  searchUsers(
    query: String!
    limit: Int = 20
  ): [User!]!
}

input UserFilter {
  role: Role
  status: UserStatus
  createdAfter: DateTime
  createdBefore: DateTime
}

enum UserSort {
  CREATED_AT_ASC
  CREATED_AT_DESC
  NAME_ASC
  NAME_DESC
}
```

### Query Depth Limiting

**Problem: Deeply nested queries**
```graphql
query DangerouslyDeep {
  user {
    friends {
      friends {
        friends {
          friends {
            # ... 100 levels deep
          }
        }
      }
    }
  }
}
```

**Solution: Enforce depth limit**
```javascript
import depthLimit from 'graphql-depth-limit'

const server = new ApolloServer({
  typeDefs,
  resolvers,
  validationRules: [depthLimit(7)]  # Max 7 levels deep
})
```

### Query Complexity Analysis

**Assign costs to fields:**
```javascript
const typeCostMap = {
  User: {
    complexity: 1,
    fields: {
      orders: { multipliers: ['first'], complexity: 2 }
    }
  }
}

// Query cost: 1 + (50 * 2) = 101
query {
  user {              # Cost: 1
    orders(first: 50) {  # Cost: 50 * 2 = 100
      id
    }
  }
}

// Reject if cost > budget (e.g., 1000)
```

---

## Mutation Design

### Mutation Naming

```graphql
# ✅ GOOD: Verb + Noun pattern
type Mutation {
  createUser(input: CreateUserInput!): CreateUserPayload!
  updateUser(id: ID!, input: UpdateUserInput!): UpdateUserPayload!
  deleteUser(id: ID!): DeleteUserPayload!

  publishPost(id: ID!): PublishPostPayload!
  sendEmail(input: SendEmailInput!): SendEmailPayload!
}

# ❌ BAD: Inconsistent naming
type Mutation {
  newUser(input: CreateUserInput!): User
  userUpdate(id: ID!, data: UpdateUserInput!): User
  removeUser(id: ID!): Boolean
}
```

### Mutation Payloads

**Always return payload type:**
```graphql
type CreateUserPayload {
  # The created resource
  user: User

  # Validation/business errors
  errors: [Error!]

  # Success indicator
  success: Boolean!

  # Client mutation ID (for optimistic updates)
  clientMutationId: String
}

type Error {
  message: String!
  field: String
  code: String!
}
```

**Why payload types?**
- Can return errors without throwing
- Extensible (add fields without breaking changes)
- Support client mutation IDs

### Mutation Example

```graphql
mutation CreateUser($input: CreateUserInput!) {
  createUser(input: $input) {
    user {
      id
      email
      firstName
    }
    errors {
      field
      message
      code
    }
    success
  }
}

# Variables
{
  "input": {
    "email": "alice@example.com",
    "firstName": "Alice",
    "lastName": "Smith",
    "password": "SecurePass123!"
  }
}

# Response (validation error)
{
  "data": {
    "createUser": {
      "user": null,
      "errors": [
        {
          "field": "email",
          "message": "Email already exists",
          "code": "EMAIL_DUPLICATE"
        }
      ],
      "success": false
    }
  }
}
```

---

## Security

### Authentication

```javascript
// Context with authenticated user
const server = new ApolloServer({
  context: async ({ req }) => {
    const token = req.headers.authorization?.replace('Bearer ', '')
    if (!token) return { user: null }

    try {
      const user = await verifyToken(token)
      return { user }
    } catch (error) {
      throw new AuthenticationError('Invalid token')
    }
  }
})
```

### Field-Level Authorization

```javascript
// Protect fields based on user permissions
const resolvers = {
  User: {
    // Public field
    name: (parent) => parent.name,

    // Authenticated only
    email: (parent, args, context) => {
      if (!context.user) {
        throw new ForbiddenError('Authentication required')
      }
      return parent.email
    },

    // Owner or admin only
    ssn: (parent, args, context) => {
      if (!context.user) {
        throw new ForbiddenError('Authentication required')
      }
      if (context.user.id !== parent.id && !context.user.isAdmin) {
        throw new ForbiddenError('Access denied')
      }
      return parent.ssn
    }
  }
}
```

### Query Authorization

```javascript
const resolvers = {
  Query: {
    user: async (parent, { id }, context) => {
      if (!context.user) {
        throw new AuthenticationError('Login required')
      }

      const user = await User.findById(id)

      // Check ownership or admin
      if (context.user.id !== id && !context.user.isAdmin) {
        throw new ForbiddenError('Access denied')
      }

      return user
    }
  }
}
```

### Preventing Information Disclosure

```graphql
# ❌ BAD: Reveals whether email exists
mutation Login($email: String!, $password: String!) {
  login(email: $email, password: $password) {
    token
    errors {
      message  # "Email not found" or "Incorrect password"
    }
  }
}

# ✅ GOOD: Generic error message
mutation Login($email: String!, $password: String!) {
  login(email: $email, password: $password) {
    token
    errors {
      message  # "Invalid email or password"
    }
  }
}
```

---

## Performance

### N+1 Query Problem

**Problem:**
```javascript
// ❌ BAD: N+1 queries
const resolvers = {
  Query: {
    posts: () => Post.findAll()
  },
  Post: {
    author: (post) => User.findById(post.authorId)  # Query for each post!
  }
}

// Fetches 100 posts: 1 query
// Then fetches author for each post: 100 queries
// Total: 101 queries
```

**Solution: DataLoader**
```javascript
// ✅ GOOD: Batched loading
import DataLoader from 'dataloader'

const createLoaders = () => ({
  userLoader: new DataLoader(async (userIds) => {
    const users = await User.findAll({ where: { id: userIds } })
    return userIds.map(id => users.find(user => user.id === id))
  })
})

const resolvers = {
  Query: {
    posts: () => Post.findAll()
  },
  Post: {
    author: (post, args, context) => {
      return context.loaders.userLoader.load(post.authorId)
    }
  }
}

// Batches all user IDs into single query
// Total: 2 queries (posts + users)
```

### Resolver Optimization

```javascript
// Use field selection to optimize database queries
const resolvers = {
  Query: {
    user: async (parent, { id }, context, info) => {
      // Parse requested fields from GraphQL query
      const fields = getFieldsFromInfo(info)

      // Only fetch requested fields from database
      const query = User.findById(id)

      if (fields.includes('orders')) {
        query.include('orders')
      }
      if (fields.includes('profile')) {
        query.include('profile')
      }

      return query
    }
  }
}
```

### Caching

```javascript
import { InMemoryLRUCache } from '@apollo/utils.keyvaluecache'

const server = new ApolloServer({
  cache: new InMemoryLRUCache({
    maxSize: 100_000_000, // 100 MB
    ttl: 300 // 5 minutes
  }),
  plugins: [
    responseCachePlugin()
  ]
})

// Cache specific queries
const resolvers = {
  Query: {
    publicUsers: async (parent, args, context, info) => {
      // Cache for 5 minutes
      info.cacheControl.setCacheHint({ maxAge: 300, scope: 'PUBLIC' })
      return User.findAll({ where: { isPublic: true } })
    }
  }
}
```

### Persisted Queries

```javascript
// Client sends query hash instead of full query
// Server looks up full query from hash
// Benefits:
// - Reduced bandwidth
// - Protection against malicious queries
// - Query whitelisting

const server = new ApolloServer({
  persistedQueries: {
    cache: new InMemoryLRUCache()
  }
})
```

---

## Error Handling

### Error Types

```javascript
import { ApolloError, AuthenticationError, ForbiddenError, UserInputError } from 'apollo-server'

const resolvers = {
  Mutation: {
    createUser: async (parent, { input }) => {
      // Validation error
      if (!isValidEmail(input.email)) {
        throw new UserInputError('Invalid email format', {
          invalidArgs: ['email']
        })
      }

      // Authentication error
      if (!context.user) {
        throw new AuthenticationError('Login required')
      }

      // Authorization error
      if (!context.user.isAdmin) {
        throw new ForbiddenError('Admin access required')
      }

      // Business logic error
      const existing = await User.findByEmail(input.email)
      if (existing) {
        throw new ApolloError('Email already exists', 'EMAIL_DUPLICATE')
      }

      // Unexpected error
      try {
        return await User.create(input)
      } catch (error) {
        throw new ApolloError('Failed to create user', 'INTERNAL_ERROR')
      }
    }
  }
}
```

### Error Response Format

```json
{
  "errors": [
    {
      "message": "Email already exists",
      "extensions": {
        "code": "EMAIL_DUPLICATE",
        "field": "email",
        "timestamp": "2024-11-01T10:30:00Z"
      },
      "path": ["createUser"],
      "locations": [{ "line": 2, "column": 3 }]
    }
  ],
  "data": {
    "createUser": null
  }
}
```

### Partial Success

```graphql
mutation BulkCreateUsers($inputs: [CreateUserInput!]!) {
  bulkCreateUsers(inputs: $inputs) {
    successful {
      user {
        id
        email
      }
      index
    }
    failed {
      index
      errors {
        message
        code
      }
    }
  }
}
```

---

## Schema Evolution

### Deprecation

```graphql
type User {
  id: ID!

  # Deprecated field
  name: String @deprecated(reason: "Use firstName and lastName instead")

  # New fields
  firstName: String!
  lastName: String!
}
```

### Adding Fields (Non-Breaking)

```graphql
# Before
type User {
  id: ID!
  email: String!
}

# After (non-breaking change)
type User {
  id: ID!
  email: String!
  phoneNumber: String  # New optional field
}
```

### Breaking Changes (Require New Version)

```graphql
# ❌ BREAKING: Removing field
type User {
  id: ID!
  # email: String!  <- Removed
}

# ❌ BREAKING: Changing field type
type User {
  id: Int!  # Was ID!, now Int!
}

# ❌ BREAKING: Making field non-null
type User {
  phoneNumber: String!  # Was nullable
}

# ✅ SOLUTION: Deprecate old, add new
type User {
  id: ID!
  email: String! @deprecated(reason: "Use primaryEmail")
  primaryEmail: String!
}
```

---

## Best Practices Summary

**Schema Design:**
- [ ] Use clear, descriptive type and field names
- [ ] Default to nullable fields
- [ ] Use Connections pattern for pagination
- [ ] Separate input types from output types

**Security:**
- [ ] Implement query depth limiting (max 5-7 levels)
- [ ] Implement query complexity analysis
- [ ] Field-level authorization
- [ ] Rate limiting on mutations
- [ ] Validate all inputs

**Performance:**
- [ ] Use DataLoader for batched loading
- [ ] Optimize database queries based on field selection
- [ ] Implement caching for expensive queries
- [ ] Consider persisted queries for production

**Error Handling:**
- [ ] Use appropriate error types
- [ ] Include error codes for programmatic handling
- [ ] Don't expose sensitive information in errors
- [ ] Support partial success in bulk operations

**Evolution:**
- [ ] Deprecate fields before removing
- [ ] Avoid breaking changes when possible
- [ ] Version API if breaking changes necessary
- [ ] Maintain changelog

---

## Tools

**Schema Design:**
- GraphQL Inspector (schema diff, breaking change detection)
- GraphQL Voyager (schema visualization)

**Security:**
- graphql-armor (security middleware)
- graphql-depth-limit
- graphql-query-complexity

**Performance:**
- DataLoader (batching and caching)
- Apollo Server (caching, tracing)
- GraphQL Shield (authorization layer)

**Testing:**
- GraphQL Playground
- Altair GraphQL Client
- Apollo Studio

---

**Remember:** GraphQL gives clients great flexibility, but with that comes responsibility to secure, optimize, and maintain your API properly.
