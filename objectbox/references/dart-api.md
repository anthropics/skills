# ObjectBox Dart/Flutter API Reference

Complete reference for using ObjectBox in Dart and Flutter applications, including installation, code generation, entity definitions, queries, relations, and vector search.

## Installation

### pubspec.yaml

```yaml
dependencies:
  objectbox: ^4.0.1
  objectbox_flutter_libs: any  # Flutter only

dev_dependencies:
  build_runner: ^2.4.0
  objectbox_generator: any
```

### Platform Requirements

- **Flutter**: Android (API 16+), iOS (10.0+), Windows, Linux, macOS
- **Dart**: Linux, macOS, Windows (x64, arm64)
- **Minimum Dart SDK**: 2.17.0

### Install Dependencies

```bash
flutter pub get
# or for pure Dart
dart pub get
```

## Code Generation

ObjectBox uses code generation to create type-safe database access code.

### Setup Entity Files

```dart
// lib/models/note.dart
import 'package:objectbox/objectbox.dart';

@Entity()
class Note {
  @Id()
  int id;

  String title;
  String? content;

  Note({this.id = 0, required this.title, this.content});
}
```

### Generate Code

```bash
# One-time generation
flutter pub run build_runner build

# Watch mode (regenerates on file changes)
flutter pub run build_runner watch

# Clean and rebuild
flutter pub run build_runner build --delete-conflicting-outputs
```

This generates:
- `objectbox.g.dart`: Main generated file with store configuration
- `*.objectbox.g.dart`: Generated code for each entity file

### Import Generated Code

```dart
import 'objectbox.g.dart'; // Generated code
```

## Store Management

### Initialize Store

**Flutter (with directory):**
```dart
import 'package:path_provider/path_provider.dart';
import 'package:path/path.dart' as path;
import 'objectbox.g.dart';

late Store store;

Future<void> initObjectBox() async {
  // Get application documents directory
  final docsDir = await getApplicationDocumentsDirectory();
  final storePath = path.join(docsDir.path, 'objectbox');

  store = await openStore(directory: storePath);
}

// Call during app initialization
await initObjectBox();
```

**Pure Dart:**
```dart
final store = await openStore();  // Uses current directory
// or
final store = await openStore(directory: './my-db');
```

### Store Configuration

```dart
final store = await openStore(
  directory: dbPath,
  maxDBSizeInKB: 100 * 1024,  // 100MB limit
  maxReaders: 126,              // Max concurrent readers
  queriesCaseSensitiveDefault: false,
);
```

### Close Store

```dart
store.close();
```

**Important**: Close the store when your app terminates to ensure data integrity.

### Store Properties

```dart
// Check if store is closed
if (store.isClosed()) {
  print('Store is closed');
}

// Get database file path
print('DB path: ${store.directoryPath}');
```

## Entity Definitions

### Basic Entity

```dart
@Entity()
class Note {
  @Id()
  int id;  // Auto-incremented by default

  String title;
  String? content;  // Nullable field

  @Property(type: PropertyType.date)
  DateTime createdAt;

  Note({
    this.id = 0,  // 0 means not yet persisted
    required this.title,
    this.content,
    required this.createdAt,
  });
}
```

### Property Types

```dart
@Entity()
class AllTypes {
  @Id()
  int id;

  // Primitives
  int integer;
  double floatingPoint;
  bool boolean;
  String text;

  // Date and time
  @Property(type: PropertyType.date)
  DateTime timestamp;

  @Property(type: PropertyType.dateNano)
  DateTime timestampNano;

  // Lists (byte arrays)
  @Property(type: PropertyType.byteVector)
  List<int>? bytes;

  @Property(type: PropertyType.charVector)
  List<int>? chars;

  // Float vectors (for embeddings)
  @Property(type: PropertyType.floatVector)
  List<double>? embedding;

  // Nullable types
  int? nullableInt;
  String? nullableString;
  DateTime? nullableDate;

  AllTypes({
    this.id = 0,
    required this.integer,
    required this.floatingPoint,
    required this.boolean,
    required this.text,
    required this.timestamp,
    required this.timestampNano,
    this.bytes,
    this.chars,
    this.embedding,
    this.nullableInt,
    this.nullableString,
    this.nullableDate,
  });
}
```

### Property Annotations

#### @Id()

Marks the primary key property (must be `int`).

```dart
@Id()
int id;  // Auto-incremented

// Or assign manually
@Id(assignable: true)
int id;
```

#### @Property()

Customizes property behavior.

```dart
// Custom type
@Property(type: PropertyType.date)
DateTime createdAt;

// Custom database name
@Property(name: 'content_text')
String content;

// Unsigned integer
@Property(type: PropertyType.int, signed: false)
int unsignedValue;
```

#### @Transient()

Excludes property from database.

```dart
@Transient()
String computedField;  // Not stored in database
```

#### @Index()

Creates database index for faster queries.

```dart
@Index()
String email;  // Indexed for faster lookups

@Index(type: IndexType.hash)
String hashedField;

@Index(type: IndexType.value)
int sortedField;
```

#### @Unique()

Enforces unique constraint.

```dart
@Unique()
String username;  // Must be unique across all records

@Unique(onConflict: ConflictStrategy.replace)
String email;  // Replace on conflict
```

#### @HnswIndex()

Creates HNSW index for vector search.

```dart
@Property(type: PropertyType.floatVector)
@HnswIndex(
  dimensions: 384,
  distanceType: VectorDistanceType.cosine,
  neighborsPerNode: 30,
  indexingSearchCount: 100,
)
List<double>? embedding;
```

## Box Operations (CRUD)

### Get Box

```dart
final noteBox = store.box<Note>();
```

### Create (Put)

```dart
// Insert single object
final note = Note(title: 'My Note', content: 'Content', createdAt: DateTime.now());
final id = noteBox.put(note);  // Returns assigned ID
print('Inserted ID: ${note.id}');  // ID is set on the object

// Insert multiple objects
final notes = [note1, note2, note3];
final ids = noteBox.putMany(notes);
```

### Read (Get)

```dart
// Get by ID
final note = noteBox.get(1);
if (note != null) {
  print(note.title);
}

// Get multiple by IDs
final notes = noteBox.getMany([1, 2, 3]);  // Returns List<Note?>

// Get all
final allNotes = noteBox.getAll();

// Count
final count = noteBox.count();
print('Total notes: $count');

// Check if empty
if (noteBox.isEmpty()) {
  print('No notes');
}
```

### Update (Put)

ObjectBox uses `put()` for both insert and update (upsert).

```dart
// Update existing object
final note = noteBox.get(1)!;
note.title = 'Updated Title';
noteBox.put(note);  // Updates if ID exists
```

### Delete (Remove)

```dart
// Delete by ID
final removed = noteBox.remove(1);  // Returns true if deleted

// Delete multiple by IDs
final removedCount = noteBox.removeMany([1, 2, 3]);

// Delete object
noteBox.remove(note.id);

// Delete all
noteBox.removeAll();
```

### Contains

```dart
if (noteBox.contains(1)) {
  print('Note exists');
}

final existingIds = noteBox.containsMany([1, 2, 3]);  // Returns Map<int, bool>
```

## Queries

### Query Builder

```dart
// Basic query
final query = noteBox.query(Note_.title.equals('Test')).build();
final results = query.find();
query.close();  // Always close queries
```

### Query Conditions

#### Equality

```dart
// String equality
Note_.title.equals('Exact Match')
Note_.title.equals('case insensitive', caseSensitive: false)

// Numeric equality
Note_.id.equals(42)

// Null checks
Note_.content.isNull()
Note_.content.notNull()
```

#### String Operations

```dart
// Contains
Note_.title.contains('search term')
Note_.title.contains('case insensitive', caseSensitive: false)

// Starts with / Ends with
Note_.title.startsWith('prefix')
Note_.title.endsWith('suffix')

// Greater/Less than (lexicographic)
Note_.title.greaterThan('M')
Note_.title.lessThan('N')
```

#### Numeric Comparisons

```dart
Note_.id.greaterThan(10)
Note_.id.greaterOrEqual(10)
Note_.id.lessThan(100)
Note_.id.lessOrEqual(100)
Note_.id.between(10, 100)
Note_.id.oneOf([1, 5, 10, 15])
```

#### Date/Time Queries

```dart
final cutoff = DateTime.now().subtract(Duration(days: 7));
Note_.createdAt.greaterThan(cutoff.millisecondsSinceEpoch)
Note_.createdAt.between(startDate.millisecondsSinceEpoch, endDate.millisecondsSinceEpoch)
```

### Logical Operators

```dart
// AND
final query = noteBox.query(
  Note_.title.contains('important') & Note_.createdAt.greaterThan(timestamp)
).build();

// OR
final query = noteBox.query(
  Note_.title.equals('A') | Note_.title.equals('B')
).build();

// Complex combinations
final query = noteBox.query(
  (Note_.title.contains('urgent') | Note_.title.contains('important')) &
  Note_.createdAt.greaterThan(cutoffDate)
).build();
```

### Vector Search

```dart
// Nearest neighbors
final queryVector = [0.1, 0.2, 0.3, ...];  // Your embedding
final query = noteBox.query(
  Note_.embedding.nearestNeighborsF32(queryVector, 10)  // Top 10 results
).build();

// With scores
final resultsWithScores = query.findWithScores();
for (var result in resultsWithScores) {
  print('Note: ${result.object.title}, Distance: ${result.score}');
}

// Combined with filters
final query = noteBox.query(
  Note_.embedding.nearestNeighborsF32(queryVector, 20) &
  Note_.category.equals('technical')
).build();
```

### Ordering

```dart
// Ascending order (default)
final query = noteBox.query(Note_.title.notNull())
  .order(Note_.createdAt)
  .build();

// Descending order
final query = noteBox.query(Note_.title.notNull())
  .order(Note_.createdAt, flags: Order.descending)
  .build();

// Case-insensitive string ordering
final query = noteBox.query(Note_.title.notNull())
  .order(Note_.title, flags: Order.caseSensitive)
  .build();

// Multiple orderings
final query = noteBox.query(Note_.title.notNull())
  .order(Note_.category)
  .order(Note_.createdAt, flags: Order.descending)
  .build();
```

### Pagination

```dart
final query = noteBox.query().build();

// Set offset and limit
query.offset = 20;  // Skip first 20
query.limit = 10;   // Return next 10

final results = query.find();
query.close();
```

### Query Execution

```dart
// Find all matching objects
final results = query.find();

// Find first match
final first = query.findFirst();

// Find unique (throws if multiple results)
final unique = query.findUnique();

// Find with scores (for vector search)
final scored = query.findWithScores();

// Find IDs only (more efficient)
final ids = query.findIds();

// Count results
final count = query.count();
```

### Property Queries

Query for specific properties instead of full objects:

```dart
// Single property
final titles = query.property(Note_.title).find();  // List<String>

// With distinct
final uniqueTitles = query.property(Note_.title).distinct().find();

// Count distinct
final uniqueCount = query.property(Note_.title).distinct().count();
```

### Aggregation

```dart
// Count
final count = query.count();

// Sum
final totalViews = query.property(Note_.views).sum();

// Average
final avgViews = query.property(Note_.views).average();

// Min/Max
final minViews = query.property(Note_.views).min();
final maxViews = query.property(Note_.views).max();
```

### Reusing Queries

```dart
// Build query once
final query = noteBox.query(Note_.category.equals('work')).build();

// Use multiple times
final results1 = query.find();
// ... later ...
final results2 = query.find();

// Update parameters
query.offset = 10;
final results3 = query.find();

// Always close when done
query.close();
```

## Relations

### ToOne (Many-to-One)

```dart
@Entity()
class Order {
  @Id()
  int id;

  double amount;

  // Many orders belong to one customer
  final customer = ToOne<Customer>();

  Order({this.id = 0, required this.amount});
}

@Entity()
class Customer {
  @Id()
  int id;

  String name;

  Customer({this.id = 0, required this.name});
}

// Usage
final customer = Customer(name: 'Alice');
customerBox.put(customer);

final order = Order(amount: 99.99);
order.customer.target = customer;  // Set relation
orderBox.put(order);

// Access related object
final retrievedOrder = orderBox.get(order.id)!;
print('Customer: ${retrievedOrder.customer.target?.name}');

// Check if relation is set
if (order.customer.hasValue) {
  print('Has customer');
}
```

### ToMany (One-to-Many)

```dart
@Entity()
class Customer {
  @Id()
  int id;

  String name;

  // One customer has many orders
  @Backlink('customer')
  final orders = ToMany<Order>();

  Customer({this.id = 0, required this.name});
}

@Entity()
class Order {
  @Id()
  int id;

  double amount;

  final customer = ToOne<Customer>();

  Order({this.id = 0, required this.amount});
}

// Usage
final customer = Customer(name: 'Bob');

// Add orders
customer.orders.add(Order(amount: 50.00));
customer.orders.add(Order(amount: 75.00));

customerBox.put(customer);  // Saves customer and orders

// Access related objects
final retrievedCustomer = customerBox.get(customer.id)!;
print('Orders: ${retrievedCustomer.orders.length}');
for (var order in retrievedCustomer.orders) {
  print('Amount: \$${order.amount}');
}

// Modify relations
retrievedCustomer.orders.add(Order(amount: 25.00));
customerBox.put(retrievedCustomer);

// Remove from relation
retrievedCustomer.orders.removeAt(0);
```

### Many-to-Many

```dart
@Entity()
class Student {
  @Id()
  int id;

  String name;

  final courses = ToMany<Course>();

  Student({this.id = 0, required this.name});
}

@Entity()
class Course {
  @Id()
  int id;

  String title;

  @Backlink('courses')
  final students = ToMany<Student>();

  Course({this.id = 0, required this.title});
}

// Usage
final student = Student(name: 'Alice');
final course1 = Course(title: 'Math');
final course2 = Course(title: 'Physics');

student.courses.add(course1);
student.courses.add(course2);

studentBox.put(student);

// Access from other side
final retrievedCourse = courseBox.get(course1.id)!;
print('Students in ${retrievedCourse.title}:');
for (var s in retrievedCourse.students) {
  print('  ${s.name}');
}
```

### Query Relations

```dart
// Query by related object
final alicesOrders = orderBox.query(
  Order_.customer.targetEquals(aliceCustomerId)
).build().find();

// Query by related property (requires @Index on relation)
final query = orderBox.query(
  Order_.customer.targetEquals(customerId)
).build();
```

## Transactions

### Write Transaction

```dart
store.runInTransaction(TxMode.write, () {
  noteBox.put(note1);
  noteBox.put(note2);
  noteBox.put(note3);
  // All succeed or all fail together
});

// With return value
final result = store.runInTransaction(TxMode.write, () {
  noteBox.put(note);
  return 'Success';
});
```

### Read Transaction

```dart
store.runInTransaction(TxMode.read, () {
  final notes = noteBox.getAll();
  // Read operations only
});
```

### Transaction Scope

Transactions ensure:
- **Atomicity**: All operations succeed or all fail
- **Consistency**: Database remains in valid state
- **Isolation**: Concurrent transactions don't interfere
- **Durability**: Committed changes are permanent

## Reactive Queries (Streams)

### Watch Query Results

```dart
// Watch all objects
final stream = noteBox.query().watch(triggerImmediately: true);

stream.listen((query) {
  final results = query.find();
  print('Notes updated: ${results.length}');
  // Update UI
});

// Watch specific query
final stream = noteBox.query(Note_.title.contains('important'))
  .watch(triggerImmediately: false);

final subscription = stream.listen((query) {
  final results = query.find();
  // React to changes
});

// Cancel subscription
await subscription.cancel();
```

### Integration with Flutter

```dart
class NotesWidget extends StatefulWidget {
  @override
  State<NotesWidget> createState() => _NotesWidgetState();
}

class _NotesWidgetState extends State<NotesWidget> {
  late Stream<Query<Note>> _notesStream;
  late Query<Note> _query;

  @override
  void initState() {
    super.initState();
    _query = store.box<Note>().query().build();
    _notesStream = _query.watch(triggerImmediately: true);
  }

  @override
  void dispose() {
    _query.close();
    super.dispose();
  }

  @override
  Widget build(BuildContext context) {
    return StreamBuilder<Query<Note>>(
      stream: _notesStream,
      builder: (context, snapshot) {
        if (!snapshot.hasData) return CircularProgressIndicator();

        final notes = snapshot.data!.find();

        return ListView.builder(
          itemCount: notes.length,
          itemBuilder: (context, index) {
            return ListTile(
              title: Text(notes[index].title),
              subtitle: Text(notes[index].content ?? ''),
            );
          },
        );
      },
    );
  }
}
```

## Advanced Features

### Custom Converters

Convert custom types to database-supported types:

```dart
// Define enum
enum NoteCategory { work, personal, shopping }

// Converter
class NoteCategoryConverter {
  static int toDb(NoteCategory category) => category.index;
  static NoteCategory fromDb(int index) => NoteCategory.values[index];
}

// Use in entity
@Entity()
class Note {
  @Id()
  int id;

  String title;

  // Store as int, use as enum
  int _categoryIndex;

  @Transient()
  NoteCategory get category => NoteCategoryConverter.fromDb(_categoryIndex);

  set category(NoteCategory value) {
    _categoryIndex = NoteCategoryConverter.toDb(value);
  }

  Note({
    this.id = 0,
    required this.title,
    required NoteCategory category,
  }) : _categoryIndex = NoteCategoryConverter.toDb(category);
}
```

### Data Observers

Listen to all changes in a Box:

```dart
// Listen to all changes
store.box<Note>().subscribe().listen((event) {
  print('Box changed!');
  // event contains change details
});
```

### Async/Await Support

All Box operations are synchronous by design for simplicity and performance. For long-running operations, use isolates:

```dart
Future<void> processLargeDataset() async {
  // Move to background isolate
  await compute(_processInIsolate, data);
}

void _processInIsolate(Data data) {
  final store = openStore(); // Open store in isolate
  final box = store.box<Note>();

  for (var item in data.items) {
    box.put(Note(title: item.title, ...));
  }

  store.close();
}
```

## Best Practices

### Store Management

1. **Single Store Instance**: Use one Store instance per database
2. **Close on Exit**: Always close store when app terminates
3. **Lazy Initialization**: Initialize store early, reuse throughout app

### Memory Management

1. **Close Queries**: Always close Query objects after use
2. **Avoid Large Results**: Use pagination for large datasets
3. **Use Streams Wisely**: Unsubscribe from streams when not needed
4. **Clear References**: Help GC by clearing large collections

### Performance

1. **Use Transactions**: Batch write operations in transactions
2. **Index Wisely**: Add @Index() to frequently queried properties
3. **Lazy Relations**: Relations load on-demand, avoid unnecessary access
4. **Reuse Queries**: Build queries once, reuse multiple times
5. **Property Queries**: Query specific properties instead of full objects when possible

### Code Organization

```dart
// lib/models/
//   note.dart - Entity definitions
//   customer.dart
//
// lib/database/
//   objectbox.dart - Store initialization
//   repositories/ - Data access layer
//     note_repository.dart
//     customer_repository.dart

// Repository pattern
class NoteRepository {
  final Box<Note> _box;

  NoteRepository(Store store) : _box = store.box<Note>();

  List<Note> getAll() => _box.getAll();

  Note? getById(int id) => _box.get(id);

  int save(Note note) => _box.put(note);

  bool delete(int id) => _box.remove(id);

  List<Note> search(String query) {
    final q = _box.query(Note_.title.contains(query)).build();
    final results = q.find();
    q.close();
    return results;
  }
}
```

## Error Handling

```dart
try {
  final store = await openStore(directory: path);
} on ObjectBoxException catch (e) {
  print('Failed to open store: $e');
  // Handle database errors
}

try {
  noteBox.put(note);
} on UniqueViolationException catch (e) {
  print('Unique constraint violated: $e');
  // Handle unique constraint errors
}

try {
  final note = query.findUnique();
} on NonUniqueResultException catch (e) {
  print('Expected single result, got multiple: $e');
}
```

## Testing

### Setup Test Database

```dart
import 'package:test/test.dart';
import 'package:objectbox/objectbox.dart';

void main() {
  late Store store;
  late Box<Note> noteBox;

  setUp(() async {
    // Use in-memory store for tests
    store = await openStore(directory: Directory.systemTemp
      .createTempSync('test-db')
      .path);
    noteBox = store.box<Note>();
  });

  tearDown(() {
    store.close();
  });

  test('should save and retrieve note', () {
    final note = Note(title: 'Test', createdAt: DateTime.now());
    final id = noteBox.put(note);

    final retrieved = noteBox.get(id);
    expect(retrieved?.title, equals('Test'));
  });
}
```

## Migration

ObjectBox handles schema changes automatically in most cases:

- **Adding properties**: Existing objects get default values
- **Removing properties**: Data is kept but not accessible
- **Renaming**: Use `@Property(name: 'old_name')` to keep compatibility

For complex migrations, access the old data and transform programmatically.

## Platform-Specific Notes

### Flutter Web

ObjectBox is not available for Flutter Web. Consider alternatives like Hive or IndexedDB.

### Flutter Desktop

Requires native libraries. Installation is automatic on supported platforms.

### Dart Server

Fully supported. Great for backend services with embedded database needs.

## Additional Resources

- **API Docs**: https://pub.dev/documentation/objectbox/latest/
- **GitHub**: https://github.com/objectbox/objectbox-dart
- **Examples**: https://github.com/objectbox/objectbox-dart/tree/main/objectbox/example
- **Troubleshooting**: https://docs.objectbox.io/troubleshooting
