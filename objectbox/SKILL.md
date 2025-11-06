---
name: objectbox
description: This skill should be used when working with ObjectBox (version 5.0.1), an on-device NoSQL database with vector search capabilities. Use this skill for tasks involving local data persistence, vector embeddings, semantic search, HNSW indexing, RAG (Retrieval-Augmented Generation) applications, or on-device AI with Flutter/Dart, Python, Java/Kotlin, Swift, Go, or C/C++. Especially relevant for mobile, IoT, and edge computing scenarios requiring offline-first functionality and efficient vector similarity searches.
---

# ObjectBox

## Overview

ObjectBox is a high-performance, on-device NoSQL database optimized for resource-constrained devices including mobile, IoT, and embedded systems. Version 5.0.1 provides native vector database capabilities with HNSW (Hierarchical Navigable Small Worlds) indexing for efficient approximate nearest neighbor (ANN) search, making it ideal for on-device AI applications including RAG, semantic search, and similarity matching.

**Key capabilities:**
- **Ultra-fast object persistence**: 10X faster than alternatives with minimal CPU, RAM, and power consumption
- **Native vector search**: First-class support for vector embeddings with HNSW indexing
- **Offline-first**: Full functionality without network connectivity
- **Multi-platform**: Supports Dart/Flutter, Python, Java/Kotlin, Swift, Go, and C/C++
- **Data Sync**: Optional out-of-the-box synchronization across devices
- **Type-safe**: Code generation for compile-time safety and performance

## Core Capabilities

### 1. Object Database Operations

Store, query, and manage objects with a simple, type-safe API.

**Entity Definition (Dart example):**
```dart
import 'package:objectbox/objectbox.dart';

@Entity()
class Note {
  @Id()
  int id;

  String title;
  String content;

  @Property(type: PropertyType.date)
  DateTime createdAt;

  Note({
    this.id = 0,
    required this.title,
    required this.content,
    required this.createdAt,
  });
}
```

**Basic CRUD operations:**
```dart
// Initialize store (one-time setup)
final store = await openStore();
final box = store.box<Note>();

// Create
final note = Note(title: 'My Note', content: 'Content here', createdAt: DateTime.now());
final id = box.put(note);

// Read
final retrievedNote = box.get(id);
final allNotes = box.getAll();

// Update
note.content = 'Updated content';
box.put(note);

// Delete
box.remove(id);

// Close store when done
store.close();
```

### 2. Vector Search with HNSW Indexing

ObjectBox provides native vector database capabilities for AI applications using HNSW algorithm for fast approximate nearest neighbor search.

**Define entity with vector property (Dart):**
```dart
@Entity()
class Document {
  @Id()
  int id;

  String text;

  @Property(type: PropertyType.floatVector)
  @HnswIndex(dimensions: 384, distanceType: VectorDistanceType.cosine)
  List<double>? embedding;

  Document({this.id = 0, required this.text, this.embedding});
}
```

**Vector distance types available:**
1. **Euclidean** (default): Traditional distance metric, typically uses "Euclidean squared" internally
2. **Cosine**: Compares vectors by angle regardless of magnitude; range 0.0-2.0 (0.0=same direction, 1.0=orthogonal, 2.0=opposite)
3. **DotProduct**: For normalized vectors (length==1.0), equivalent to cosine but faster
4. **DotProductNonNormalized**: Custom similarity measure without normalization requirement
5. **Geospatial**: For latitude/longitude pairs (2D vectors only), uses haversine distance

**Perform vector search:**
```dart
// Query for nearest neighbors
final queryVector = [0.1, 0.2, 0.3, ...]; // Your embedding vector

final query = box.query(Document_.embedding.nearestNeighborsF32(queryVector, 10)).build();
final results = query.find();

// Get results with distance scores
final resultsWithScores = query.findWithScores();
for (var result in resultsWithScores) {
  print('ID: ${result.object.id}, Score: ${result.score}');
}

query.close();
```

**HNSW Index Configuration:**
- `dimensions`: Vector dimensionality (e.g., 384 for MiniLM, 768 for BERT, 1536 for OpenAI embeddings)
- `neighborsPerNode` (optional): Number of neighbors per node (default: 30)
- `indexingSearchCount` (optional): Search count during indexing (default: 100)
- `flags` (optional): Additional configuration flags
- `distanceType`: One of the five distance types above

### 3. Queries and Filtering

Build complex queries with type-safe query builder API.

**Basic queries:**
```dart
// Simple equality
final query = box.query(Note_.title.equals('My Note')).build();

// String operations
final query = box.query(Note_.title.contains('search term', caseSensitive: false)).build();

// Numeric comparisons
final query = box.query(Note_.createdAt.greaterThan(DateTime.now().millisecondsSinceEpoch)).build();

// Logical operators
final query = box.query(
  Note_.title.contains('important') & Note_.createdAt.greaterThan(timestamp)
).build();

// Order results
final query = box.query(Note_.title.equals('Test'))
  .order(Note_.createdAt, flags: Order.descending)
  .build();

// Limit and offset
query.limit = 20;
query.offset = 10;

final results = query.find();
query.close();
```

**Combining vector search with filters:**
```dart
// Find nearest neighbors that also match specific criteria
final query = box.query(
  Document_.embedding.nearestNeighborsF32(queryVector, 20) &
  Document_.category.equals('technical')
).build();
```

### 4. Relations

ObjectBox supports ToOne, ToMany, and many-to-many relationships.

**ToOne relationship:**
```dart
@Entity()
class Order {
  @Id()
  int id;

  final customer = ToOne<Customer>();

  Order({this.id = 0});
}

// Usage
order.customer.target = myCustomer;
box.put(order);
```

**ToMany relationship:**
```dart
@Entity()
class Customer {
  @Id()
  int id;

  String name;

  @Backlink('customer')
  final orders = ToMany<Order>();

  Customer({this.id = 0, required this.name});
}

// Usage
customer.orders.add(newOrder);
box.put(customer);
```

### 5. Transactions

Use transactions for atomic operations and improved performance.

```dart
store.runInTransaction(TxMode.write, () {
  box.put(note1);
  box.put(note2);
  box.put(note3);
  // All succeed or all fail together
});
```

### 6. Observers and Reactive Queries

Monitor database changes in real-time.

**Stream-based observation (Dart):**
```dart
// Listen to all changes in a Box
final stream = box.query().watch(triggerImmediately: true);
stream.listen((query) {
  final results = query.find();
  // Update UI with results
});

// Listen to specific query results
final query = box.query(Note_.title.contains('important')).build();
query.stream.listen((results) {
  // React to changes
});
```

## Language-Specific Setup

### Dart/Flutter

**Installation:**
```yaml
# pubspec.yaml
dependencies:
  objectbox: ^4.0.1
  objectbox_flutter_libs: any

dev_dependencies:
  build_runner: ^2.4.0
  objectbox_generator: any
```

**Generate code:**
```bash
flutter pub run build_runner build
# or watch for changes
flutter pub run build_runner watch
```

**Initialize store:**
```dart
import 'objectbox.g.dart'; // Generated code

late Store store;

Future<void> initObjectBox() async {
  store = await openStore();
}
```

See `references/dart-api.md` for complete Dart/Flutter API documentation.

### Python

**Installation:**
```bash
pip install objectbox
```

**Basic usage:**
```python
from objectbox import *

@Entity()
class Note:
    id = Id()
    title = String()
    content = String()

# Open store
ob = ObjectBox()
ob.open_store()
box = ob.box(Note)

# Use the box
note = Note(title="Example", content="Content")
box.put(note)
```

### Java/Kotlin

**Installation (Gradle):**
```gradle
plugins {
    id("io.objectbox") version "4.0.1"
}

dependencies {
    implementation("io.objectbox:objectbox-kotlin:4.0.1")
}
```

**Entity definition (Kotlin):**
```kotlin
@Entity
data class Note(
    @Id var id: Long = 0,
    var title: String = "",
    var content: String = ""
)
```

### Swift/iOS

**Installation (CocoaPods):**
```ruby
pod 'ObjectBox', '~> 2.0'
```

For detailed setup instructions for all languages, see `references/setup-installation.md`.

## Common Workflows

### RAG (Retrieval-Augmented Generation) Application

**Workflow:**
1. Define entity with text and vector embedding property
2. Generate embeddings for documents using an embedding model (e.g., sentence-transformers, OpenAI)
3. Store documents with embeddings in ObjectBox
4. For queries: generate query embedding, perform vector search, use retrieved context with LLM

**Example pattern:**
```dart
// 1. Store document with embedding
final doc = Document(
  text: 'Your document content',
  embedding: await generateEmbedding('Your document content')
);
docBox.put(doc);

// 2. Query with user question
final questionEmbedding = await generateEmbedding(userQuestion);
final query = docBox.query(
  Document_.embedding.nearestNeighborsF32(questionEmbedding, 5)
).build();
final relevantDocs = query.find();

// 3. Build context and query LLM
final context = relevantDocs.map((d) => d.text).join('\n\n');
final llmResponse = await queryLLM(userQuestion, context);
```

### Semantic Search

1. Index content with embeddings using appropriate distance metric (usually cosine)
2. For search: convert query to embedding
3. Perform nearest neighbor search
4. Optionally combine with traditional filters for hybrid search

```dart
// Hybrid search: vector similarity + metadata filtering
final query = docBox.query(
  Document_.embedding.nearestNeighborsF32(queryEmbedding, 20) &
  Document_.category.equals('technical') &
  Document_.publishDate.greaterThan(cutoffDate)
).order(Document_.publishDate, flags: Order.descending)
.build();
```

### Image Similarity Search

1. Use image embedding model (e.g., CLIP, ResNet)
2. Store image metadata with embedding vectors
3. Query with target image embedding

```dart
@Entity()
class ImageRecord {
  @Id()
  int id;

  String filePath;

  @Property(type: PropertyType.floatVector)
  @HnswIndex(dimensions: 512, distanceType: VectorDistanceType.cosine)
  List<double>? imageEmbedding;

  ImageRecord({this.id = 0, required this.filePath, this.imageEmbedding});
}
```

## Best Practices

### Vector Search Optimization

1. **Choose appropriate distance metric:**
   - Cosine: Best for semantic similarity, document comparison
   - DotProduct: Use for normalized vectors (faster than cosine)
   - Euclidean: Traditional distance metric, good for general use
   - Geospatial: Specifically for lat/long coordinates

2. **Tune HNSW parameters:**
   - Higher `neighborsPerNode` (e.g., 50-100): Better accuracy, more memory
   - Lower `neighborsPerNode` (e.g., 16-30): Faster queries, less memory
   - Default (30) is good for most use cases

3. **Normalize vectors when using DotProduct** for better similarity comparison

4. **Match dimensions to your embedding model:**
   - sentence-transformers/all-MiniLM-L6-v2: 384 dimensions
   - OpenAI text-embedding-ada-002: 1536 dimensions
   - BERT base: 768 dimensions

### Performance

1. **Use transactions** for batch operations
2. **Close queries** after use to free resources
3. **Use query streams** for reactive UI updates
4. **Prefer ToOne/ToMany relations** over manual ID management
5. **Index frequently queried properties** using `@Index()` annotation

### Data Modeling

1. **Keep entities focused**: Don't create god objects with too many properties
2. **Use relations judiciously**: ToOne is cheap, ToMany has overhead
3. **Consider denormalization** for read-heavy workloads
4. **Store vector metadata** alongside embeddings for filtering

## Troubleshooting

**Common issues:**

1. **"Store already opened" error**: Ensure only one Store instance per database directory
2. **Vector dimensions mismatch**: Verify embedding dimensions match `@HnswIndex(dimensions=...)` declaration
3. **Build runner errors**: Clean generated files with `flutter pub run build_runner clean`
4. **Platform-specific issues**: Check that objectbox_flutter_libs or native binaries are properly installed

**For platform-specific solutions, consult:**
- Dart/Flutter: `references/dart-api.md`
- Installation issues: `references/setup-installation.md`
- Vector search details: `references/vector-search.md`

## Resources

### references/

- **vector-search.md**: Comprehensive vector search documentation including HNSW algorithm details, distance functions, index configuration, and advanced query patterns
- **dart-api.md**: Complete Dart/Flutter API reference with code generation, store management, queries, and reactive patterns
- **setup-installation.md**: Detailed installation and setup instructions for all supported languages (Dart, Python, Java, Kotlin, Swift, Go, C/C++)

### scripts/

- **vector_search_example.py**: Complete Python example demonstrating RAG application with ObjectBox vector search
- **dart_rag_example.dart**: Dart/Flutter RAG implementation with sentence embeddings

---

**Official Documentation**: https://docs.objectbox.io/
**Current Version**: 5.0.1
**GitHub**: https://github.com/objectbox
