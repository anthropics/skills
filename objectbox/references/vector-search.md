# ObjectBox Vector Search Reference

This document provides comprehensive information about ObjectBox's on-device vector search capabilities, including the HNSW algorithm, distance functions, index configuration, and advanced query patterns.

## HNSW Algorithm Overview

ObjectBox implements **Hierarchical Navigable Small World (HNSW)** graphs for approximate nearest neighbor (ANN) search. HNSW is a state-of-the-art algorithm that provides:

- **Fast query performance**: Logarithmic time complexity for searches
- **High accuracy**: Near-exact nearest neighbor results
- **Scalability**: Handles millions of vectors efficiently
- **Memory efficiency**: Optimized for resource-constrained devices

### How HNSW Works

HNSW constructs a multi-layer graph structure:

1. **Bottom layer**: Contains all data points connected in a navigable small-world graph
2. **Upper layers**: Contain progressively fewer "shortcut" nodes for faster traversal
3. **Search process**: Starts from top layer, greedy searches down through layers to find nearest neighbors
4. **Trade-offs**: Balance between accuracy (more connections) and speed/memory (fewer connections)

## Vector Property Types

ObjectBox supports multiple vector property types for different use cases:

### Float32 Vectors (`PropertyType.floatVector`)

Most common type for embeddings from ML models.

```dart
@Property(type: PropertyType.floatVector)
@HnswIndex(dimensions: 384)
List<double>? embedding;
```

**Use cases:**
- Text embeddings (sentence-transformers, OpenAI, etc.)
- Image embeddings (CLIP, ResNet, etc.)
- Audio embeddings
- General-purpose semantic vectors

### Byte Vectors (`PropertyType.byteVector`)

For quantized or binary embeddings (memory-efficient).

```dart
@Property(type: PropertyType.byteVector)
@HnswIndex(dimensions: 128)
List<int>? quantizedEmbedding;
```

**Use cases:**
- Quantized embeddings for reduced memory footprint
- Binary embeddings
- Low-precision applications

## Distance Functions

ObjectBox provides five distance functions for different similarity metrics:

### 1. Euclidean Distance (Default)

**Formula**: √(Σ(ai - bi)²) — typically uses squared Euclidean internally for efficiency

**Characteristics:**
- Measures absolute distance in vector space
- Sensitive to vector magnitude
- Good general-purpose metric
- Range: [0, ∞)

**Usage:**
```dart
@HnswIndex(dimensions: 384, distanceType: VectorDistanceType.euclidean)
```

**Best for:**
- General similarity comparisons
- When vector magnitude matters
- Image embeddings with consistent scale

### 2. Cosine Similarity

**Formula**: 1 - (A·B)/(||A||·||B||)

**Characteristics:**
- Measures angle between vectors, ignoring magnitude
- Normalized comparison
- Range: [0.0, 2.0] where 0.0=same direction, 1.0=orthogonal, 2.0=opposite
- Most popular for semantic similarity

**Usage:**
```dart
@HnswIndex(dimensions: 384, distanceType: VectorDistanceType.cosine)
```

**Best for:**
- Semantic text similarity
- Document comparison
- Sentence embeddings
- When vector magnitude shouldn't affect similarity

**Example:**
```dart
// Documents with cosine similarity
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

### 3. Dot Product

**Formula**: A·B (for normalized vectors, equivalent to cosine similarity)

**Characteristics:**
- Faster than cosine similarity
- Requires normalized vectors (||v|| = 1.0)
- Returns similarity score (higher = more similar)
- Optimal when vectors are already normalized

**Usage:**
```dart
@HnswIndex(dimensions: 384, distanceType: VectorDistanceType.dotProduct)
```

**Best for:**
- Pre-normalized embeddings
- Performance-critical applications
- When you control the embedding normalization

**Important**: Ensure vectors are normalized before storage:
```dart
List<double> normalizeVector(List<double> vector) {
  final magnitude = sqrt(vector.fold<double>(0.0, (sum, v) => sum + v * v));
  return vector.map((v) => v / magnitude).toList();
}

// Use it
doc.embedding = normalizeVector(rawEmbedding);
```

### 4. Dot Product Non-Normalized

**Formula**: A·B (without normalization requirement)

**Characteristics:**
- Custom similarity measure
- Does not require vector normalization
- Not equivalent to cosine similarity
- Use with caution—results depend on vector magnitudes

**Usage:**
```dart
@HnswIndex(dimensions: 384, distanceType: VectorDistanceType.dotProductNonNormalized)
```

**Best for:**
- Specialized applications with specific requirements
- When unnormalized dot product is desired
- Custom embedding schemes

### 5. Geospatial Distance

**Formula**: Haversine distance for latitude/longitude

**Characteristics:**
- Specifically for geographic coordinates
- Requires exactly 2 dimensions
- First element: latitude (-90 to 90)
- Second element: longitude (-180 to 180)
- Returns distance in kilometers

**Usage:**
```dart
@Property(type: PropertyType.floatVector)
@HnswIndex(dimensions: 2, distanceType: VectorDistanceType.geospatial)
List<double>? coordinates; // [latitude, longitude]
```

**Example:**
```dart
@Entity()
class Location {
  @Id()
  int id;

  String name;

  @Property(type: PropertyType.floatVector)
  @HnswIndex(dimensions: 2, distanceType: VectorDistanceType.geospatial)
  List<double>? coordinates; // [lat, lng]

  Location({this.id = 0, required this.name, this.coordinates});
}

// Usage
final location = Location(
  name: 'Eiffel Tower',
  coordinates: [48.8584, 2.2945] // [latitude, longitude]
);

// Find nearby locations
final query = box.query(
  Location_.coordinates.nearestNeighborsF32([48.8566, 2.3522], 10)
).build();
```

**Best for:**
- Location-based services
- Proximity searches
- Geographic queries

## HNSW Index Configuration

### Basic Configuration

```dart
@HnswIndex(
  dimensions: 384,                              // Required
  distanceType: VectorDistanceType.cosine,      // Optional (default: euclidean)
)
```

### Advanced Configuration

```dart
@HnswIndex(
  dimensions: 384,
  distanceType: VectorDistanceType.cosine,
  neighborsPerNode: 30,        // Default: 30
  indexingSearchCount: 100,    // Default: 100
  flags: 0                     // Default: 0
)
```

### Configuration Parameters

#### dimensions (Required)

Number of dimensions in the vector. Must match embedding model output.

**Common embedding dimensions:**
- `sentence-transformers/all-MiniLM-L6-v2`: 384
- `sentence-transformers/all-mpnet-base-v2`: 768
- `BERT-base`: 768
- `OpenAI text-embedding-ada-002`: 1536
- `OpenAI text-embedding-3-small`: 1536
- `OpenAI text-embedding-3-large`: 3072
- `CLIP ViT-B/32`: 512
- `CLIP ViT-L/14`: 768

#### neighborsPerNode (Optional)

**Description**: Number of bi-directional links per node in the HNSW graph (also called M or efConstruction)

**Default**: 30

**Trade-offs:**
- **Lower values (16-30)**:
  - Faster queries
  - Less memory usage
  - Slightly lower accuracy
  - Good for resource-constrained devices

- **Higher values (50-100)**:
  - Better accuracy (closer to exact nearest neighbors)
  - Slower queries
  - More memory usage
  - Better for high-dimensional spaces

**Recommendations:**
- Mobile/IoT: 16-30
- Desktop/Server: 30-50
- High-accuracy requirements: 50-100

#### indexingSearchCount (Optional)

**Description**: Number of neighbors explored during index construction (also called efConstruction)

**Default**: 100

**Impact:**
- Higher values: Better index quality, slower indexing
- Lower values: Faster indexing, potentially lower quality
- Usually doesn't need adjustment

#### flags (Optional)

**Description**: Additional configuration flags

**Default**: 0

**Usage**: Reserved for future extensions and specialized configurations

## Vector Search Queries

### Basic Nearest Neighbor Search

```dart
// Single query
final queryVector = [0.1, 0.2, 0.3, ...]; // Your embedding

final query = box.query(
  Document_.embedding.nearestNeighborsF32(queryVector, 10)
).build();

final results = query.find();
query.close();
```

### Search with Distance Scores

```dart
final query = box.query(
  Document_.embedding.nearestNeighborsF32(queryVector, 10)
).build();

final resultsWithScores = query.findWithScores();

for (var result in resultsWithScores) {
  print('Document: ${result.object.text}');
  print('Distance: ${result.score}');
  print('---');
}

query.close();
```

### Hybrid Search: Vector + Filters

Combine vector search with traditional database filters:

```dart
// Find similar documents that also match specific criteria
final query = box.query(
  Document_.embedding.nearestNeighborsF32(queryVector, 50) &  // Vector search
  Document_.category.equals('technical') &                     // Filter 1
  Document_.publishDate.greaterThan(cutoffDate) &             // Filter 2
  Document_.language.equals('en')                              // Filter 3
).order(Document_.publishDate, flags: Order.descending)
 .build();

final results = query.find();
query.close();
```

### Multi-Vector Search

For complex scenarios, query multiple vector properties:

```dart
@Entity()
class MultiModalDoc {
  @Id()
  int id;

  String text;

  @Property(type: PropertyType.floatVector)
  @HnswIndex(dimensions: 384, distanceType: VectorDistanceType.cosine)
  List<double>? textEmbedding;

  @Property(type: PropertyType.floatVector)
  @HnswIndex(dimensions: 512, distanceType: VectorDistanceType.cosine)
  List<double>? imageEmbedding;

  MultiModalDoc({this.id = 0, required this.text, this.textEmbedding, this.imageEmbedding});
}

// Search by text or image
final textQuery = box.query(
  MultiModalDoc_.textEmbedding.nearestNeighborsF32(textQueryVector, 10)
).build();

final imageQuery = box.query(
  MultiModalDoc_.imageEmbedding.nearestNeighborsF32(imageQueryVector, 10)
).build();
```

### Pagination

```dart
final query = box.query(
  Document_.embedding.nearestNeighborsF32(queryVector, 100)
).build();

// Paginate results
query.offset = page * pageSize;
query.limit = pageSize;

final results = query.find();
query.close();
```

## Advanced Patterns

### Re-ranking

Improve result quality by combining vector search with re-ranking:

```dart
// 1. Fast vector search with larger result set
final initialQuery = box.query(
  Document_.embedding.nearestNeighborsF32(queryVector, 100)
).build();
final candidates = initialQuery.find();
initialQuery.close();

// 2. Re-rank with more expensive similarity metric or business logic
final reranked = candidates.map((doc) {
  final score = computeDetailedScore(doc, userQuery);
  return (doc: doc, score: score);
}).toList()
  ..sort((a, b) => b.score.compareTo(a.score));

// 3. Return top K
final topResults = reranked.take(10).map((r) => r.doc).toList();
```

### Query Expansion

Improve recall by generating multiple query variations:

```dart
// Generate query variations
final queries = [
  originalQuery,
  expandedQuery1,
  expandedQuery2,
];

final allResults = <Document>{};

for (final queryText in queries) {
  final embedding = await generateEmbedding(queryText);
  final query = box.query(
    Document_.embedding.nearestNeighborsF32(embedding, 20)
  ).build();

  allResults.addAll(query.find());
  query.close();
}

// Deduplicate and rank
final uniqueResults = allResults.toList();
```

### Contextual Filtering

Adjust search based on user context:

```dart
Future<List<Document>> contextualSearch(
  String query,
  UserContext context,
) async {
  final embedding = await generateEmbedding(query);

  var queryBuilder = Document_.embedding.nearestNeighborsF32(embedding, 50);

  // Add contextual filters
  if (context.language != null) {
    queryBuilder = queryBuilder & Document_.language.equals(context.language!);
  }

  if (context.categories.isNotEmpty) {
    queryBuilder = queryBuilder & Document_.category.oneOf(context.categories);
  }

  if (context.minDate != null) {
    queryBuilder = queryBuilder &
      Document_.publishDate.greaterOrEqual(context.minDate!.millisecondsSinceEpoch);
  }

  final query = box.query(queryBuilder).build();
  final results = query.find();
  query.close();

  return results;
}
```

## Performance Optimization

### Batch Operations

Use transactions for inserting multiple vectors:

```dart
store.runInTransaction(TxMode.write, () {
  for (final doc in documents) {
    box.put(doc);
  }
});
```

### Index Optimization

**Rebuild index** if search performance degrades after many updates:

```dart
// Note: Index rebuilding API may vary by platform
// Consult platform-specific documentation
```

### Memory Management

For large datasets, consider:

1. **Pagination**: Load results in batches
2. **Lazy loading**: Only load full objects when needed
3. **Clear queries**: Always close Query objects
4. **Limit vector dimensions**: Use smaller embedding models when possible

### Query Caching

Cache frequently used query embeddings:

```dart
final queryCache = <String, List<double>>{};

Future<List<Document>> cachedSearch(String query) async {
  // Check cache
  var embedding = queryCache[query];

  if (embedding == null) {
    embedding = await generateEmbedding(query);
    queryCache[query] = embedding;
  }

  final q = box.query(
    Document_.embedding.nearestNeighborsF32(embedding, 10)
  ).build();

  final results = q.find();
  q.close();

  return results;
}
```

## Embedding Model Selection

### Choosing an Embedding Model

**Factors to consider:**
1. **Dimensions**: Lower = faster, less memory; Higher = potentially better accuracy
2. **Model size**: Must run on target device
3. **Domain**: Choose models trained on similar data
4. **Language**: Ensure model supports your languages
5. **Performance**: Balance quality vs. speed

### Recommended Models

**For Mobile/Edge Devices:**
- `all-MiniLM-L6-v2` (384 dims): Fast, small, good quality
- `paraphrase-MiniLM-L3-v2` (384 dims): Very fast, tiny

**For Better Quality:**
- `all-mpnet-base-v2` (768 dims): High quality, moderate size
- `multi-qa-mpnet-base-dot-v1` (768 dims): Optimized for Q&A

**For Multilingual:**
- `paraphrase-multilingual-MiniLM-L12-v2` (384 dims)
- `distiluse-base-multilingual-cased-v2` (512 dims)

**For Images:**
- CLIP models (512-768 dims)
- ResNet embeddings (2048 dims, consider dimensionality reduction)

### Running Models On-Device

**Options:**
1. **ONNX Runtime**: Cross-platform, efficient
2. **TensorFlow Lite**: Good for mobile
3. **PyTorch Mobile**: Full PyTorch ecosystem
4. **Platform-specific**: Core ML (iOS), ML Kit (Android)

**Example with ONNX (Python):**
```python
from sentence_transformers import SentenceTransformer
import onnx

# Convert model to ONNX
model = SentenceTransformer('all-MiniLM-L6-v2')
model.save('model.onnx')

# Use in app with ONNX Runtime
# (Dart/Flutter: use onnxruntime_flutter package)
```

## Testing and Validation

### Accuracy Testing

Evaluate vector search quality:

```dart
Future<double> evaluateRecall(
  List<TestQuery> testQueries,
  int k,
) async {
  var correctRetrievals = 0;

  for (final testQuery in testQueries) {
    final query = box.query(
      Document_.embedding.nearestNeighborsF32(testQuery.embedding, k)
    ).build();

    final results = query.find();
    query.close();

    final retrievedIds = results.map((d) => d.id).toSet();
    final groundTruthIds = testQuery.relevantIds.toSet();

    final intersection = retrievedIds.intersection(groundTruthIds);
    correctRetrievals += intersection.length;
  }

  final recall = correctRetrievals / (testQueries.length * k);
  return recall;
}
```

### Performance Benchmarking

```dart
Future<void> benchmarkSearch() async {
  final queryVectors = generateRandomVectors(100, 384);

  final stopwatch = Stopwatch()..start();

  for (final queryVector in queryVectors) {
    final query = box.query(
      Document_.embedding.nearestNeighborsF32(queryVector, 10)
    ).build();
    query.find();
    query.close();
  }

  stopwatch.stop();

  final avgTime = stopwatch.elapsedMilliseconds / queryVectors.length;
  print('Average query time: ${avgTime}ms');
}
```

## Troubleshooting

### Common Issues

**1. Dimension Mismatch**
```
Error: Vector dimension mismatch
```
**Solution**: Ensure embedding dimensions match `@HnswIndex(dimensions=...)` exactly

**2. Poor Search Quality**
- Try different distance metrics (cosine often works best)
- Increase `neighborsPerNode` for better accuracy
- Verify embeddings are generated correctly
- Check if vectors need normalization (for DotProduct)

**3. Slow Performance**
- Reduce `neighborsPerNode` for faster queries
- Use smaller embedding dimensions
- Optimize query filters
- Use DotProduct instead of Cosine for normalized vectors

**4. High Memory Usage**
- Reduce `neighborsPerNode`
- Use quantized vectors (byte vectors)
- Consider dimensionality reduction
- Use pagination for large result sets

## Best Practices Summary

1. **Choose appropriate distance metric**: Cosine for semantic similarity, DotProduct for normalized vectors
2. **Match dimensions to model**: Verify embedding dimensions are correct
3. **Tune HNSW parameters**: Balance accuracy vs. performance
4. **Use hybrid search**: Combine vector search with filters
5. **Close queries**: Always close Query objects to free resources
6. **Batch operations**: Use transactions for bulk inserts
7. **Test thoroughly**: Validate search quality and performance
8. **Monitor performance**: Track query times and accuracy
9. **Consider re-ranking**: Improve results with post-processing
10. **Cache when possible**: Cache frequent query embeddings

## Additional Resources

- **ObjectBox Official Docs**: https://docs.objectbox.io/on-device-vector-search
- **HNSW Paper**: https://arxiv.org/abs/1603.09320
- **Embedding Models**: https://huggingface.co/models?pipeline_tag=sentence-similarity
- **Vector Search Best Practices**: https://www.pinecone.io/learn/vector-search/
