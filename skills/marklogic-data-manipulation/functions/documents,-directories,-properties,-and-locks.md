# Documents, Directories, Properties, And Locks

9 functions in this category.

## xdmp:collection-locks

Returns locks of documents in a collection.

### Signature

```xquery
xdmp:collection-locks(
  $uri as xs:string*?
) as document-node()*
```

### Parameters

**`$uri`** *(optional)*
The input URI.

### Returns

`document-node()*`

### Usage Notes

Note that the locks described here are relatively heavy persistent
document locks for file system emulation through WebDAV, not relatively
light transaction locks for database consistency.

### Examples

```xquery
for $d in xdmp:collection-locks(
                     ("http://example.com/col1/",
                      "http://example.com/col2/"))
  return xdmp:node-uri($d)
  => http://example.com/bar.xml
     http://example.com/baz.xml
```

---

## xdmp:collection-properties

Returns a sequence of properties documents, one for each document in the
  specified collection(s) that has a corresponding properties document.

### Signature

```xquery
xdmp:collection-properties(
  $uri as xs:string*?
) as document-node()*
```

### Parameters

**`$uri`** *(optional)*
The URI(s) of the collection(s).

### Returns

`document-node()*`

### Examples

```xquery
xquery version "1.0-ml";
  declare namespace cpf="http://marklogic.com/cpf";

  for $d in xdmp:collection-properties(
                   ("http://example.com/col1/",
                    "http://example.com/col2/"))
  where $d/property::cpf:error
  return xdmp:node-uri($d)

  => A list of document URIs of documents that have a
     cpf:error property in their corresponding properties
     documents.  For example:

     http://example.com/bar.xml http://example.com/baz.xml
```

---

## xdmp:directory

Returns the documents from the database in a directory.  Note that these are
  database documents, not from the filesystem; if you want documents from a 
  filesystem directory, use xdmp:filesystem-directory instead.

### Signature

```xquery
xdmp:directory(
  $uri as xs:string*,
  $depth as xs:string??
) as document-node()*
```

### Parameters

**`$uri`**
The URI of the directory.  Typically, directory URIs end with a forward
    slash (/).

**`$depth`** *(optional)*
"1" for immediate children, "infinity" for all.
    If not supplied, depth is "1".

### Returns

`document-node()*`

### Examples

```xquery
for $d in xdmp:directory("http://example.com/foo/","1")
return xdmp:node-uri($d)
  => http://example.com/foo/bar.xml
     http://example.com/foo/baz.xml
```

---

## xdmp:directory-locks

Returns locks of documents in a directory.

### Signature

```xquery
xdmp:directory-locks(
  $uri as xs:string*,
  $depth as xs:string??
) as document-node()*
```

### Parameters

**`$uri`**
The URI of the directory.  Typically, directory URIs end with a forward
    slash (/).

**`$depth`** *(optional)*
"1" for immediate children, "infinity" for all.
    If not supplied, depth is "1".

### Returns

`document-node()*`

### Usage Notes

Note that the locks described here are relatively heavy persistent
document locks for file system emulation through WebDAV, not relatively
light transaction locks for database consistency.

### Examples

```xquery
for $d in xdmp:directory-locks("http://example.com/foo/","1")
  return xdmp:node-uri($d)
  => http://example.com/foo/bar.xml
     http://example.com/foo/baz.xml
```

---

## xdmp:directory-properties

Returns a sequence of properties documents, one for each document in
  the specified directory that has a corresponding properties document.

### Signature

```xquery
xdmp:directory-properties(
  $uri as xs:string*,
  $depth as xs:string??
) as document-node()*
```

### Parameters

**`$uri`**
The URI of the directory.  Typically, directory URIs end with a forward
    slash (/).

**`$depth`** *(optional)*
"1" for immediate children, "infinity" for all children.
    If not supplied, depth is "1".

### Returns

`document-node()*`

### Examples

```xquery
xdmp:directory-properties("http://example.com/dir/","1")
=> <prop:properties
            xmlns:prop="http://marklogic.com/xdmp/property">
         <prop:directory/>
     </prop:properties>

   The properties document returned has one directory element, indicating
   that there is a single directory that is an immediate child of the
   specified directory.
```

---

## xdmp:document-get-properties

Returns the property values for a document's property.  Throws
  XDMP-DOCNOTFOUND if there is no document at the specified URI.

### Signature

```xquery
xdmp:document-get-properties(
  $uri as xs:string,
  $property as xs:QName
) as element()*
```

### Parameters

**`$uri`**
The document URI.

**`$property`**
The property name. This is the QName of the top-level property element
    in the specified properties document.

### Returns

`element()*`

### Examples

```xquery
xdmp:document-get-properties(
         "http://example.com/foo.xml",
         fn:QName("http://examples.com/","priority"))
   => <priority xmlns="http://examples.com/">5</priority>
```

---

## xdmp:document-get-quality

Returns the quality of the specified document if the document exists.
  Otherwise, returns the empty sequence.

### Signature

```xquery
xdmp:document-get-quality(
  $uri as xs:string
) as xs:integer?
```

### Parameters

**`$uri`**
The URI of the document in question.

### Returns

`xs:integer?`

### Examples

```xquery
xdmp:document-get-quality("example.xml")
=> 10
```

---

## xdmp:document-locks

Returns the locks for one or more documents or directories.
  Returns the locks for all documents and directories
  in the database if no parameter is given.

### Signature

```xquery
xdmp:document-locks(
  $uri as xs:string*?
) as document-node()*
```

### Parameters

**`$uri`** *(optional)*
A document URI.

### Returns

`document-node()*`

### Usage Notes

Note that the locks described here are relatively heavy persistent
document locks for file system emulation through WebDAV, not relatively
light transaction locks for database consistency.

### Examples

#### Example 1

```xquery
xdmp:document-locks("example.xml")
=>
<?xml version="1.0" encoding="ASCII"?>
<lock:lock xmlns:lock="http://marklogic.com/xdmp/lock">
  <lock:lock-type>write</lock:lock-type>
  <lock:lock-scope>exclusive</lock:lock-scope>
  <lock:active-locks>
    <lock:active-lock>
      <lock:depth>0</lock:depth>
      <lock:owner>
        <DAV:href xmlns:DAV="DAV:">http://example.com/~user</DAV:href>
      </lock:owner>
      <lock:timeout>120</lock:timeout>
      <lock:lock-token>http://marklogic.com/xdmp/locks/1c267a036b8480c3
      </lock:lock-token>
      <lock:timestamp>1290136652</lock:timestamp>
      <sec:user-id xmlns:sec="http://marklogic.com/xdmp/security">
        893641342095093063</sec:user-id>
    </lock:active-lock>
  </lock:active-locks>
</lock:lock>
```

#### Example 2

```xquery
xquery version "1.0-ml";

(:
   The time is in epoch time, which is seconds from the start
   of 1970, so this code does a little math on the values in
   the lock document to figure out how many seconds are left
   for the lock.  Assumes a lock on /example.xml, for example
   by running the following:

xquery version "1.0-ml";
declare namespace DAV="DAV:";

xdmp:lock-acquire("/example.xml",
           "exclusive",
           "0",
           <DAV:href>http://example.com/~user</DAV:href>,
           xs:unsignedLong(120))

:)
let $lock := xdmp:document-locks("/example.xml")
let $lock-duration :=
   $lock/lock:lock/lock:active-locks/lock:active-lock/
         lock:timeout/fn:data(.)
let $current-epoch-time :=
 fn:round(
  ( fn:current-dateTime() - xs:dateTime("1970-01-01T00:00:00-00:00") )
  div xs:dayTimeDuration('PT1S') )
let $start-time :=
  $lock/lock:lock/lock:active-locks/lock:active-lock/
        lock:timestamp/fn:data(.)
let $end-time := $start-time + $lock-duration
let $seconds-left := $end-time - $current-epoch-time
return
 ($current-epoch-time, $start-time, $seconds-left)
=>
1290136837
1290136832
115
```

---

## xdmp:document-properties

Returns a sequence of properties documents, one for each of the specified
  documents that has a corresponding properties document.  If no documents
  are specified, returns a sequence of properties documents for all
  documents in the database that have a corresponding properties document.

### Signature

```xquery
xdmp:document-properties(
  $uri as xs:string*?
) as document-node()*
```

### Parameters

**`$uri`** *(optional)*
A sequence of document URIs.

### Returns

`document-node()*`

### Examples

#### Example 1

```xquery
xdmp:document-properties("/mydoc.xml")
  =>
<prop:properties xmlns:prop="http://marklogic.com/xdmp/property">
  <cpf:processing-status xmlns:cpf="http://marklogic.com/cpf">done
    </cpf:processing-status>
  <cpf:last-updated xmlns:cpf="http://marklogic.com/cpf">
    2010-05-24T16:28:11.577608-07:00</cpf:last-updated>
  <cpf:state xmlns:cpf="http://marklogic.com/cpf">
    http://marklogic.com/states/final</cpf:state>
  <prop:last-modified>2010-05-24T16:29:58-07:00</prop:last-modified>
</prop:properties>
```

#### Example 2

```xquery
xdmp:document-properties()
 => All of the document properties, for example:
    <prop:properties
          xmlns:prop="http://marklogic.com/xdmp/property">
    Property Node1
    </prop:properties>
    <prop:properties
          xmlns:prop="http://marklogic.com/xdmp/property">
    Property Node2
    </prop:properties>
    <prop:properties
          xmlns:prop="http://marklogic.com/xdmp/property">
    Property NodeN
    </prop:properties>
```

---
