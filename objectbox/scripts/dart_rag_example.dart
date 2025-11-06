// ObjectBox Vector Search Example - RAG Application with Dart/Flutter
//
// This example demonstrates how to build a Retrieval-Augmented Generation (RAG)
// application using ObjectBox's vector search capabilities in Dart/Flutter.
//
// Features:
// - Document storage with vector embeddings
// - Semantic search using HNSW index with cosine similarity
// - Hybrid search (vector + metadata filtering)
// - Context retrieval for LLM queries
//
// Setup:
// 1. Add dependencies to pubspec.yaml:
//    dependencies:
//      objectbox: ^4.0.1
//      objectbox_flutter_libs: any
//    dev_dependencies:
//      build_runner: ^2.4.0
//      objectbox_generator: any
//
// 2. Run code generation:
//    flutter pub run build_runner build
//
// 3. Integrate embedding generation (not shown here - use sentence-transformers
//    via ONNX Runtime or call external API)

import 'package:objectbox/objectbox.dart';
import 'dart:math';

// ============================================================================
// Entity Definitions
// ============================================================================

/// Document entity with text content and vector embedding for semantic search
@Entity()
class Document {
  @Id()
  int id;

  String title;
  String content;
  String category;

  @Property(type: PropertyType.date)
  DateTime createdAt;

  /// Vector embedding for semantic search using HNSW index
  /// Configured for 384 dimensions (all-MiniLM-L6-v2 model)
  @Property(type: PropertyType.floatVector)
  @HnswIndex(
    dimensions: 384,
    distanceType: VectorDistanceType.cosine,
    neighborsPerNode: 30,
  )
  List<double>? embedding;

  Document({
    this.id = 0,
    required this.title,
    required this.content,
    required this.category,
    required this.createdAt,
    this.embedding,
  });

  @override
  String toString() => 'Document(id: $id, title: "$title", category: "$category")';
}

// ============================================================================
// Document Store with Vector Search
// ============================================================================

/// High-level interface for document storage and semantic search using ObjectBox
class DocumentStore {
  late final Store _store;
  late final Box<Document> _box;

  /// Initialize the document store
  Future<void> init(String dbPath) async {
    print('Initializing DocumentStore...');
    print('  Database: $dbPath');

    // Note: In actual implementation, import generated objectbox.g.dart
    // _store = await openStore(directory: dbPath);
    // _box = _store.box<Document>();

    print('Initialization complete!\n');
  }

  /// Add a document with pre-computed embedding
  int addDocument({
    required String title,
    required String content,
    required List<double> embedding,
    String category = 'general',
  }) {
    final doc = Document(
      title: title,
      content: content,
      category: category,
      createdAt: DateTime.now(),
      embedding: embedding,
    );

    final id = _box.put(doc);
    return id;
  }

  /// Batch add multiple documents with transaction for better performance
  List<int> addDocumentsBatch(List<Map<String, dynamic>> documents) {
    print('Adding ${documents.length} documents in batch...');

    final docs = documents.map((doc) {
      return Document(
        title: doc['title'],
        content: doc['content'],
        category: doc['category'] ?? 'general',
        createdAt: DateTime.now(),
        embedding: doc['embedding'],
      );
    }).toList();

    final ids = _box.putMany(docs);
    print('Successfully added ${ids.length} documents\n');
    return ids;
  }

  /// Perform semantic search using vector similarity
  ///
  /// Returns list of documents with similarity scores
  List<({Document doc, double score})> semanticSearch({
    required List<double> queryEmbedding,
    int topK = 5,
    String? category,
  }) {
    // Build query with vector search
    var queryCondition = Document_.embedding.nearestNeighborsF32(
      queryEmbedding,
      topK * 2, // Retrieve more for post-filtering
    );

    // Add category filter if specified
    if (category != null) {
      queryCondition = queryCondition & Document_.category.equals(category);
    }

    final query = _box.query(queryCondition).build();

    // Find with scores (distance values)
    final resultsWithScores = query.findWithScores();
    query.close();

    // Convert to records (Dart 3.0 feature)
    final results = resultsWithScores.map((result) {
      // ObjectBox returns distance; convert to similarity score
      // For cosine distance: similarity = 1 - distance
      final similarity = 1.0 - result.score;

      return (doc: result.object, score: similarity);
    }).toList();

    // Sort by score descending and limit to topK
    results.sort((a, b) => b.score.compareTo(a.score));
    return results.take(topK).toList();
  }

  /// Perform hybrid search: vector similarity + metadata filters
  List<({Document doc, double score})> hybridSearch({
    required List<double> queryEmbedding,
    int topK = 5,
    String? category,
    DateTime? minDate,
    List<String>? categories,
  }) {
    var queryCondition = Document_.embedding.nearestNeighborsF32(
      queryEmbedding,
      topK * 3, // Retrieve more for filtering
    );

    // Add metadata filters
    if (category != null) {
      queryCondition = queryCondition & Document_.category.equals(category);
    }

    if (minDate != null) {
      queryCondition = queryCondition &
          Document_.createdAt.greaterOrEqual(minDate.millisecondsSinceEpoch);
    }

    if (categories != null && categories.isNotEmpty) {
      queryCondition = queryCondition & Document_.category.oneOf(categories);
    }

    final query = _box.query(queryCondition).build();
    final resultsWithScores = query.findWithScores();
    query.close();

    final results = resultsWithScores.map((result) {
      return (doc: result.object, score: 1.0 - result.score);
    }).toList();

    results.sort((a, b) => b.score.compareTo(a.score));
    return results.take(topK).toList();
  }

  /// Get all documents
  List<Document> getAllDocuments() => _box.getAll();

  /// Get document count
  int getDocumentCount() => _box.count();

  /// Close the database
  void close() {
    _store.close();
  }
}

// ============================================================================
// RAG Helper Functions
// ============================================================================

/// Build context string from retrieved documents for LLM
String buildContext(
  List<({Document doc, double score})> documents, {
  int maxTokens = 500,
}) {
  final contextParts = <String>[];
  var totalChars = 0;
  final maxChars = maxTokens * 4; // Rough approximation

  for (final result in documents) {
    final docText = '[${result.doc.title}]\n${result.doc.content}\n';

    if (totalChars + docText.length > maxChars) {
      break;
    }

    contextParts.add(docText);
    totalChars += docText.length;
  }

  return contextParts.join('\n---\n');
}

/// Perform a RAG query: retrieve relevant context and prepare for LLM
Map<String, dynamic> ragQuery({
  required DocumentStore store,
  required String question,
  required List<double> questionEmbedding,
  int topK = 3,
}) {
  print('Question: $question\n');
  print('Retrieving relevant documents...');

  // Semantic search for relevant documents
  final results = store.semanticSearch(
    queryEmbedding: questionEmbedding,
    topK: topK,
  );

  print('Found ${results.length} relevant documents:\n');
  for (var i = 0; i < results.length; i++) {
    final result = results[i];
    print('${i + 1}. ${result.doc.title} (score: ${result.score.toStringAsFixed(4)})');
    print('   Category: ${result.doc.category}');
    print('   Preview: ${result.doc.content.substring(0, min(100, result.doc.content.length))}...');
    print();
  }

  // Build context for LLM
  final context = buildContext(results);

  return {
    'question': question,
    'context': context,
    'retrieved_docs': results.map((r) => r.doc).toList(),
    'scores': results.map((r) => r.score).toList(),
  };
}

// ============================================================================
// Embedding Generation (Placeholder)
// ============================================================================

/// Generate embedding for text
///
/// In production, use one of:
/// 1. ONNX Runtime with sentence-transformers model
/// 2. TensorFlow Lite model
/// 3. External API (OpenAI, Cohere, etc.)
/// 4. On-device model via platform channels
///
/// This is a placeholder that generates random vectors for demonstration
List<double> generateEmbedding(String text, {int dimensions = 384}) {
  // PLACEHOLDER: In production, use actual embedding model
  // For demonstration, generate deterministic "fake" embedding based on text
  final random = Random(text.hashCode);
  final embedding = List.generate(dimensions, (_) => random.nextDouble() * 2 - 1);

  // Normalize for use with cosine similarity
  final magnitude = sqrt(embedding.fold<double>(0, (sum, val) => sum + val * val));
  return embedding.map((val) => val / magnitude).toList();
}

// ============================================================================
// Example Usage
// ============================================================================

Future<void> main() async {
  print('=' * 70);
  print('ObjectBox Vector Search RAG Example (Dart/Flutter)');
  print('=' * 70);
  print('\n');

  // Initialize document store
  final store = DocumentStore();
  await store.init('rag_example_db');

  // Sample documents about machine learning
  final sampleDocs = [
    {
      'title': 'Introduction to Neural Networks',
      'content': 'Neural networks are computing systems inspired by biological neural networks. '
          'They consist of interconnected nodes (neurons) organized in layers. Each connection '
          'has a weight that adjusts during learning. Neural networks excel at pattern recognition '
          'and are fundamental to deep learning.',
      'category': 'ml_basics',
    },
    {
      'title': 'Understanding Transformers',
      'content': 'Transformers are a type of neural network architecture based on self-attention mechanisms. '
          'Introduced in 2017, they revolutionized NLP by processing entire sequences simultaneously '
          'rather than sequentially. Key components include multi-head attention, positional encodings, '
          'and feed-forward networks. Models like BERT and GPT are built on transformer architecture.',
      'category': 'deep_learning',
    },
    {
      'title': 'Vector Databases Explained',
      'content': 'Vector databases store and query high-dimensional vector embeddings efficiently. '
          'They use algorithms like HNSW (Hierarchical Navigable Small Worlds) for fast approximate '
          'nearest neighbor search. Essential for semantic search, recommendation systems, and RAG '
          'applications. ObjectBox provides on-device vector database capabilities.',
      'category': 'databases',
    },
    {
      'title': 'What is RAG?',
      'content': 'Retrieval-Augmented Generation (RAG) combines information retrieval with text generation. '
          'First, relevant documents are retrieved using semantic search. Then, these documents provide '
          'context to a language model for generating accurate, grounded responses. RAG reduces hallucinations '
          'and enables LLMs to access external knowledge.',
      'category': 'ml_applications',
    },
    {
      'title': 'Embeddings in NLP',
      'content': 'Embeddings represent text as dense vectors in high-dimensional space. Words or sentences '
          'with similar meanings have similar vector representations. Modern embedding models like '
          'sentence-transformers capture semantic meaning effectively. These embeddings enable semantic '
          'search, clustering, and similarity comparison.',
      'category': 'nlp',
    },
  ];

  // Generate embeddings and add to documents
  if (store.getDocumentCount() == 0) {
    print('Populating database with sample documents...\n');

    final docsWithEmbeddings = sampleDocs.map((doc) {
      return {
        ...doc,
        'embedding': generateEmbedding(doc['content'] as String),
      };
    }).toList();

    store.addDocumentsBatch(docsWithEmbeddings);
  } else {
    print('Database already contains ${store.getDocumentCount()} documents\n');
  }

  print('-' * 70);
  print('EXAMPLE 1: Basic Semantic Search');
  print('-' * 70);
  print('\n');

  // Example 1: Semantic search
  final query1 = 'How do attention mechanisms work?';
  final query1Embedding = generateEmbedding(query1);
  final results1 = store.semanticSearch(
    queryEmbedding: query1Embedding,
    topK: 2,
  );

  print('Query: "$query1"\n');
  print('Top results:');
  for (var i = 0; i < results1.length; i++) {
    final result = results1[i];
    print('\n${i + 1}. ${result.doc.title} (similarity: ${result.score.toStringAsFixed(4)})');
    print('   ${result.doc.content.substring(0, min(150, result.doc.content.length))}...');
  }

  print('\n');
  print('-' * 70);
  print('EXAMPLE 2: RAG Query');
  print('-' * 70);
  print('\n');

  // Example 2: RAG query
  final question = 'What are the benefits of using vector databases for AI applications?';
  final questionEmbedding = generateEmbedding(question);
  final ragResult = ragQuery(
    store: store,
    question: question,
    questionEmbedding: questionEmbedding,
    topK: 3,
  );

  print('\n${'=' * 70}');
  print('Context prepared for LLM:');
  print('=' * 70);
  final context = ragResult['context'] as String;
  print(context.substring(0, min(500, context.length)) + '...');
  print();

  print('-' * 70);
  print('EXAMPLE 3: Hybrid Search (Vector + Category Filter)');
  print('-' * 70);
  print('\n');

  // Example 3: Hybrid search
  final query3 = 'machine learning concepts';
  final query3Embedding = generateEmbedding(query3);
  final results3 = store.hybridSearch(
    queryEmbedding: query3Embedding,
    topK: 3,
    categories: ['ml_basics', 'deep_learning'],
  );

  print('Query: "$query3" (filtered by categories: ml_basics, deep_learning)\n');
  print('Results:');
  for (var i = 0; i < results3.length; i++) {
    final result = results3[i];
    print('\n${i + 1}. ${result.doc.title}');
    print('   Category: ${result.doc.category}');
    print('   Similarity: ${result.score.toStringAsFixed(4)}');
  }

  print('\n');
  print('=' * 70);
  print('Example complete! Database contains ${store.getDocumentCount()} documents.');
  print('=' * 70);

  // Cleanup
  store.close();
}

// ============================================================================
// Flutter Widget Integration Example
// ============================================================================

/*
// Example of integrating semantic search in a Flutter widget:

class SemanticSearchWidget extends StatefulWidget {
  @override
  State<SemanticSearchWidget> createState() => _SemanticSearchWidgetState();
}

class _SemanticSearchWidgetState extends State<SemanticSearchWidget> {
  final DocumentStore _store = DocumentStore();
  List<({Document doc, double score})> _results = [];
  bool _isSearching = false;

  @override
  void initState() {
    super.initState();
    _initStore();
  }

  Future<void> _initStore() async {
    final docsDir = await getApplicationDocumentsDirectory();
    await _store.init(docsDir.path + '/objectbox');
  }

  Future<void> _performSearch(String query) async {
    setState(() => _isSearching = true);

    // Generate embedding (use actual model in production)
    final embedding = await generateEmbedding(query);

    // Perform search
    final results = _store.semanticSearch(
      queryEmbedding: embedding,
      topK: 10,
    );

    setState(() {
      _results = results;
      _isSearching = false;
    });
  }

  @override
  Widget build(BuildContext context) {
    return Column(
      children: [
        // Search bar
        TextField(
          decoration: InputDecoration(labelText: 'Search'),
          onSubmitted: _performSearch,
        ),

        // Results
        if (_isSearching)
          CircularProgressIndicator()
        else
          Expanded(
            child: ListView.builder(
              itemCount: _results.length,
              itemBuilder: (context, index) {
                final result = _results[index];
                return ListTile(
                  title: Text(result.doc.title),
                  subtitle: Text(result.doc.content),
                  trailing: Text(
                    result.score.toStringAsFixed(2),
                    style: TextStyle(color: Colors.blue),
                  ),
                );
              },
            ),
          ),
      ],
    );
  }

  @override
  void dispose() {
    _store.close();
    super.dispose();
  }
}
*/
