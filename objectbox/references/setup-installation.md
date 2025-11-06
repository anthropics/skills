# ObjectBox Setup and Installation Guide

Complete installation instructions for ObjectBox across all supported platforms and languages.

## Version Information

- **Current Version**: 5.0.1
- **Vector Search**: Available from version 4.0.0+
- **Minimum Requirements**: Varies by platform (see below)

## Dart/Flutter

### Requirements

- **Dart SDK**: 2.17.0 or higher
- **Flutter**: 3.0.0 or higher (for Flutter projects)
- **Platforms**:
  - Android: API level 16+ (Android 4.1+)
  - iOS: 10.0+
  - macOS: 10.15+
  - Windows: 7+ (x64)
  - Linux: x64, arm64, armv7

### Installation

#### Step 1: Add Dependencies

Add to `pubspec.yaml`:

```yaml
dependencies:
  objectbox: ^4.0.1
  objectbox_flutter_libs: any  # For Flutter only

dev_dependencies:
  build_runner: ^2.4.0
  objectbox_generator: any
```

For **pure Dart** projects (no Flutter), omit `objectbox_flutter_libs` and ensure native libraries are available on your system.

#### Step 2: Install Packages

```bash
flutter pub get
# or for pure Dart
dart pub get
```

#### Step 3: Create Entity

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

#### Step 4: Generate Code

```bash
# One-time generation
flutter pub run build_runner build

# Or use watch mode for automatic regeneration
flutter pub run build_runner watch

# If you encounter conflicts
flutter pub run build_runner build --delete-conflicting-outputs
```

This generates `objectbox.g.dart` and entity-specific `.objectbox.g.dart` files.

#### Step 5: Initialize Store

```dart
import 'package:objectbox/objectbox.dart';
import 'objectbox.g.dart'; // Generated

late Store store;

Future<void> initObjectBox() async {
  // For Flutter apps, specify directory
  if (Platform.isAndroid || Platform.isIOS) {
    final docsDir = await getApplicationDocumentsDirectory();
    store = await openStore(directory: docsDir.path + '/objectbox');
  } else {
    // For desktop or pure Dart
    store = await openStore();
  }
}

// In main()
void main() async {
  WidgetsFlutterBinding.ensureInitialized();
  await initObjectBox();
  runApp(MyApp());
}
```

### Troubleshooting Dart/Flutter

**Issue**: Build runner fails with "conflicting outputs"
```bash
flutter pub run build_runner clean
flutter pub run build_runner build --delete-conflicting-outputs
```

**Issue**: Native library not found (pure Dart)
- Download native libraries from [ObjectBox releases](https://github.com/objectbox/objectbox-c/releases)
- Place in system library path or project directory
- Set `LD_LIBRARY_PATH` (Linux/macOS) or add to PATH (Windows)

**Issue**: iOS build fails
- Ensure minimum deployment target is iOS 10.0+ in `ios/Podfile`
- Run `pod install` in the ios directory

**Issue**: Android build fails
- Ensure `minSdkVersion` is 16+ in `android/app/build.gradle`
- Clean and rebuild: `flutter clean && flutter pub get`

## Python

### Requirements

- **Python**: 3.7 or higher
- **Platforms**: Linux (x64, arm64), macOS (x64, Apple Silicon), Windows (x64)
- **Pip**: Latest version recommended

### Installation

#### Using pip

```bash
pip install objectbox
```

#### Using Poetry

```bash
poetry add objectbox
```

#### Using Conda

```bash
conda install -c conda-forge objectbox
```

### Basic Setup

```python
from objectbox import *

# Define entity
@Entity()
class Note:
    id = Id()
    title = String()
    content = String()
    created_at = Date()

# Open store
ob = ObjectBox()
ob.open_store(directory="my-database")

# Get box
note_box = ob.box(Note)

# Use it
note = Note()
note.title = "My Note"
note.content = "Content here"
note.created_at = datetime.now()

note_box.put(note)
```

### Vector Search in Python

```python
from objectbox import *
import numpy as np

@Entity()
class Document:
    id = Id()
    text = String()
    embedding = Float32Vector()  # For vector search

# Configure HNSW index in schema
# (Typically done through annotations or schema configuration)

# Create entity with embedding
doc = Document()
doc.text = "Sample document"
doc.embedding = embedding_model.encode(doc.text)  # Your embedding

doc_box.put(doc)

# Query nearest neighbors
query_vector = embedding_model.encode("search query")
results = doc_box.query().nearest_neighbors(
    Document.embedding,
    query_vector,
    max_results=10
).find()
```

### Troubleshooting Python

**Issue**: Module not found
```bash
pip install --upgrade objectbox
```

**Issue**: Platform not supported
- Ensure you're on a supported platform (Linux x64/arm64, macOS x64/arm64, Windows x64)
- Check Python version (3.7+ required)

**Issue**: Native library loading error
- Update to latest version: `pip install --upgrade objectbox`
- Check system architecture matches package

## Java/Kotlin

### Requirements

- **Java**: 8 or higher
- **Kotlin**: 1.6.0 or higher (for Kotlin projects)
- **Android**: API level 16+ (Android 4.1+)
- **Gradle**: 6.7.1 or higher

### Installation (Gradle)

#### Step 1: Add Plugin

In `build.gradle.kts` (project level):

```kotlin
plugins {
    id("io.objectbox") version "4.0.1" apply false
}
```

Or in `build.gradle` (Groovy):

```groovy
plugins {
    id 'io.objectbox' version '4.0.1' apply false
}
```

#### Step 2: Apply Plugin

In `build.gradle.kts` (app/module level):

```kotlin
plugins {
    id("io.objectbox")
}

dependencies {
    implementation("io.objectbox:objectbox-kotlin:4.0.1")
    // or for Java
    // implementation("io.objectbox:objectbox-java:4.0.1")
}
```

#### Step 3: Define Entity (Kotlin)

```kotlin
import io.objectbox.annotation.Entity
import io.objectbox.annotation.Id

@Entity
data class Note(
    @Id var id: Long = 0,
    var title: String = "",
    var content: String? = null
)
```

#### Step 4: Build Project

The ObjectBox Gradle plugin will generate code during build:

```bash
./gradlew build
```

This generates `MyObjectBox` class and entity metadata.

#### Step 5: Initialize Store

```kotlin
import io.objectbox.BoxStore

lateinit var boxStore: BoxStore

fun initObjectBox(context: Context) {
    boxStore = MyObjectBox.builder()
        .androidContext(context.applicationContext)
        .build()
}

// In Application class or Activity
class MyApp : Application() {
    override fun onCreate() {
        super.onCreate()
        initObjectBox(this)
    }
}
```

### Vector Search in Java/Kotlin

```kotlin
import io.objectbox.annotation.*

@Entity
data class Document(
    @Id var id: Long = 0,
    var text: String = "",

    @HnswIndex(dimensions = 384, distanceType = VectorDistanceType.COSINE)
    var embedding: FloatArray? = null
)

// Usage
val doc = Document(
    text = "Sample document",
    embedding = generateEmbedding("Sample document")
)

val docBox = boxStore.boxFor(Document::class.java)
docBox.put(doc)

// Query
val queryVector = generateEmbedding("search query")
val query = docBox.query(
    Document_.embedding.nearestNeighbors(queryVector, 10)
).build()

val results = query.find()
query.close()
```

### Installation (Maven)

For non-Android Java projects:

```xml
<dependencies>
    <dependency>
        <groupId>io.objectbox</groupId>
        <artifactId>objectbox-java</artifactId>
        <version>4.0.1</version>
    </dependency>
</dependencies>

<build>
    <plugins>
        <plugin>
            <groupId>io.objectbox</groupId>
            <artifactId>objectbox-maven-plugin</artifactId>
            <version>4.0.1</version>
            <executions>
                <execution>
                    <goals>
                        <goal>generate</goal>
                    </goals>
                </execution>
            </executions>
        </plugin>
    </plugins>
</build>
```

### Troubleshooting Java/Kotlin

**Issue**: Plugin version conflict
- Ensure Gradle version is 6.7.1+
- Update Android Gradle Plugin to latest stable version
- Check plugin compatibility matrix

**Issue**: Native library not found (desktop Java)
- Add platform-specific natives dependency:
```kotlin
implementation("io.objectbox:objectbox-linux:4.0.1")      // Linux
implementation("io.objectbox:objectbox-macos:4.0.1")      // macOS
implementation("io.objectbox:objectbox-windows:4.0.1")    // Windows
```

**Issue**: Code generation fails
- Clean and rebuild: `./gradlew clean build`
- Check entity annotations are correct
- Ensure entities are in correct source set

**Issue**: Android 64-bit requirement
- ObjectBox requires 64-bit support on Android
- Ensure `abiFilters` includes 64-bit architectures in `build.gradle`

## Swift (iOS/macOS)

### Requirements

- **Xcode**: 12.0 or higher
- **Swift**: 5.3 or higher
- **iOS**: 10.0+
- **macOS**: 10.15+

### Installation (CocoaPods)

#### Step 1: Create Podfile

```ruby
platform :ios, '10.0'
use_frameworks!

target 'YourApp' do
  pod 'ObjectBox', '~> 2.0'
end
```

#### Step 2: Install

```bash
pod install
```

#### Step 3: Define Entity

```swift
import ObjectBox

// Entity definition
class Note: Entity, ObjectKeyedSubscript {
    var id: Id<Note> = 0
    var title: String = ""
    var content: String = ""

    required init() {}
}

// Register entities
extension EntityInfo {
    static func registerEntities() {
        store.register(entity: Note.self)
    }
}
```

#### Step 4: Initialize Store

```swift
import ObjectBox

var store: Store!

func initObjectBox() throws {
    // Get documents directory
    let dir = try FileManager.default
        .url(for: .documentDirectory, in: .userDomainMask,
             appropriateFor: nil, create: true)
        .appendingPathComponent("ObjectBox")

    EntityInfo.registerEntities()
    store = try Store(directoryPath: dir.path)
}

// In AppDelegate or SceneDelegate
func application(_ application: UIApplication,
                 didFinishLaunchingWithOptions launchOptions: [UIApplication.LaunchOptionsKey: Any]?) -> Bool {
    try! initObjectBox()
    return true
}
```

### Installation (Swift Package Manager)

#### Step 1: Add Package

In Xcode: File → Add Packages...

```
https://github.com/objectbox/objectbox-swift.git
```

Or in `Package.swift`:

```swift
dependencies: [
    .package(url: "https://github.com/objectbox/objectbox-swift.git",
             from: "2.0.0")
]
```

#### Step 2: Import and Use

```swift
import ObjectBox

// Define and use entities as shown above
```

### Vector Search in Swift

```swift
class Document: Entity {
    var id: Id<Document> = 0
    var text: String = ""
    var embedding: [Float] = []  // Vector embedding

    required init() {}
}

// Configure HNSW index (typically in entity registration)
// Query nearest neighbors
let queryVector: [Float] = generateEmbedding("search query")
let query = try store.query(Document.self)
    .nearestNeighbors(Document.embedding, to: queryVector, maxResults: 10)
    .build()

let results = try query.find()
```

### Troubleshooting Swift

**Issue**: Build fails with linker errors
- Ensure Xcode version is 12.0+
- Clean derived data: Cmd+Shift+K
- Check minimum deployment target

**Issue**: Pod installation fails
- Update CocoaPods: `sudo gem install cocoapods`
- Clear cache: `pod cache clean --all`
- Run `pod install --repo-update`

**Issue**: Swift version mismatch
- Set Swift version in Podfile: `ENV['SWIFT_VERSION'] = '5'`
- Update Xcode to latest version

## Go

### Requirements

- **Go**: 1.16 or higher
- **Platforms**: Linux (x64, arm64), macOS (x64, arm64), Windows (x64)

### Installation

```bash
go get github.com/objectbox/objectbox-go/objectbox
```

### Setup

```go
package main

import (
    "github.com/objectbox/objectbox-go/objectbox"
)

// Define entity
type Note struct {
    ID      uint64
    Title   string
    Content string
}

func main() {
    // Create ObjectBox builder
    ob := objectbox.NewBuilder().Model(model()).Build()
    defer ob.Close()

    // Get box
    box := objectbox.BoxForType(ob, Note{})

    // Use box
    note := &Note{
        Title:   "My Note",
        Content: "Content here",
    }

    id, err := box.Put(note)
    if err != nil {
        panic(err)
    }
}
```

### Code Generation

ObjectBox Go uses code generation:

```bash
go generate ./...
```

This generates binding code for your entities.

### Troubleshooting Go

**Issue**: CGO_ENABLED required
- Ensure CGO is enabled: `export CGO_ENABLED=1`
- Install C compiler (gcc for Linux, clang for macOS)

**Issue**: Native library not found
- Download ObjectBox C library from releases
- Place in system library path
- Set library path environment variables

## C/C++

### Requirements

- **C**: C11 or higher
- **C++**: C++11 or higher
- **Platforms**: Linux (x64, arm64, armv7), macOS (x64, arm64), Windows (x64)

### Installation

#### Step 1: Download Library

Download ObjectBox C library from:
https://github.com/objectbox/objectbox-c/releases

Choose the archive for your platform (e.g., `objectbox-linux-x64.tar.gz`).

#### Step 2: Extract and Link

```bash
tar -xzf objectbox-linux-x64.tar.gz
sudo cp -r include/objectbox* /usr/local/include/
sudo cp lib/libobjectbox.so /usr/local/lib/
sudo ldconfig  # Linux only
```

#### Step 3: Use in CMake

```cmake
cmake_minimum_required(VERSION 3.10)
project(MyApp)

set(CMAKE_CXX_STANDARD 11)

find_library(OBJECTBOX_LIB objectbox)

add_executable(myapp main.cpp)
target_link_libraries(myapp ${OBJECTBOX_LIB})
```

### Basic Usage (C++)

```cpp
#include "objectbox.hpp"

using namespace obx;

// Define entity struct
struct Note {
    obx_id id;
    std::string title;
    std::string content;
};

int main() {
    // Create store
    Store store(Model());

    // Get box
    Box<Note> noteBox(store);

    // Put object
    Note note{0, "My Note", "Content"};
    noteBox.put(note);

    // Get all
    std::vector<Note> notes = noteBox.getAll();

    return 0;
}
```

### Troubleshooting C/C++

**Issue**: Library not found at runtime
- Set `LD_LIBRARY_PATH` (Linux): `export LD_LIBRARY_PATH=/path/to/lib:$LD_LIBRARY_PATH`
- Set `DYLD_LIBRARY_PATH` (macOS): `export DYLD_LIBRARY_PATH=/path/to/lib`
- Add to PATH (Windows) or place DLL in executable directory

**Issue**: Header files not found
- Ensure include path is set correctly in compiler flags
- Copy headers to system include path or specify with `-I`

## General Troubleshooting

### Database Issues

**Store already opened error**
- Ensure only one Store instance per database directory
- Close store properly before reopening
- Check for zombie processes holding lock

**Database corruption**
- ObjectBox is ACID compliant and rarely corrupts
- If corruption occurs, restore from backup
- Check disk space and permissions

**Performance issues**
- Use transactions for batch operations
- Add indexes to frequently queried properties
- Check query complexity
- Monitor database size

### Platform-Specific Issues

**iOS/macOS: Bitcode not supported**
- Disable bitcode in Xcode build settings
- ObjectBox doesn't require bitcode

**Android: ABI filters**
- ObjectBox supports: armeabi-v7a, arm64-v8a, x86, x86_64
- Include all or specific ABIs in build.gradle

**Linux: GLIBC version**
- ObjectBox requires GLIBC 2.17+ (GLIBCXX 3.4.18+)
- Update system or use compatible version

**Windows: Visual C++ Redistributable**
- Install Visual C++ Redistributable 2015-2022
- Download from Microsoft website

### Getting Help

- **Documentation**: https://docs.objectbox.io/
- **GitHub Issues**: https://github.com/objectbox/[language-binding]/issues
- **Community**: ObjectBox Forum and Discord
- **Stack Overflow**: Tag questions with `objectbox`

## Version Migration

### Upgrading from 3.x to 4.x

ObjectBox 4.0 introduced vector search. Migration is automatic:

1. Update dependency version
2. Run code generation (if applicable)
3. Rebuild project
4. Existing databases continue to work

### Schema Changes

ObjectBox handles most schema changes automatically:

- **Adding properties**: Existing objects get default values
- **Removing properties**: Data preserved but not accessible
- **Renaming**: Use UID annotations to preserve data
- **Changing types**: Requires manual migration

### Backup and Restore

```dart
// Dart example - similar patterns for other languages

// Backup
final backupFile = File('backup.obx');
await store.backup(backupFile.path);

// Restore
// 1. Close existing store
store.close();

// 2. Copy backup to database directory
await backupFile.copy(dbPath);

// 3. Reopen store
store = await openStore(directory: dbPath);
```

## Production Checklist

Before deploying to production:

- [ ] Tested on all target platforms
- [ ] Error handling implemented
- [ ] Backup strategy in place
- [ ] Indexes added to frequently queried properties
- [ ] Queries properly closed after use
- [ ] Store properly closed on app exit
- [ ] Transaction boundaries identified for batch operations
- [ ] Memory usage profiled for large datasets
- [ ] Migration strategy planned for schema changes
- [ ] Monitoring and logging in place
- [ ] Security considerations addressed (encryption, access control)

## Advanced Configuration

### Store Options

```dart
// Dart example
final store = await openStore(
  directory: dbPath,
  maxDBSizeInKB: 100 * 1024,      // 100 MB
  maxReaders: 126,                 // Max concurrent readers
  fileMode: 0o644,                 // File permissions (Unix)
  maxDataSizeInKB: 512 * 1024,    // 512 MB
  queriesCaseSensitiveDefault: false,
);
```

### Debug Mode

Enable debug logging:

```dart
// Dart
Store.debugFlags = DebugFlags.LOG_TRANSACTIONS;

// Java/Kotlin
BoxStore.setDebugFlags(DebugFlags.LOG_TRANSACTIONS_READ | DebugFlags.LOG_TRANSACTIONS_WRITE);

// Swift
Store.debugFlags = .transactionWrites
```

### Custom Database Location

Choose appropriate location based on platform:

- **Android**: `context.filesDir` or `context.cacheDir`
- **iOS**: Documents directory or Library/Application Support
- **Desktop**: User data directory or app-specific folder
- **Server**: Persistent storage location

## Next Steps

After installation:

1. Read the main SKILL.md for usage patterns
2. Explore vector search capabilities in references/vector-search.md
3. Check language-specific API docs (e.g., references/dart-api.md)
4. Review example scripts in scripts/ directory
5. Join ObjectBox community for support

## Resources

- **Official Website**: https://objectbox.io/
- **Documentation**: https://docs.objectbox.io/
- **GitHub**: https://github.com/objectbox/
- **Releases**: Check language-specific repositories for latest versions
- **Examples**: https://github.com/objectbox/[language-binding]/tree/main/examples
