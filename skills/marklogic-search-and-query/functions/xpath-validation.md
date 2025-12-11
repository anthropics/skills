# Xpath Validation

4 functions in this category.

## cts:valid-document-patch-path

Parses path expressions and resolves namespaces using the $map parameter.
 Returns true if the argument is permissible as a path for
 document PATCH.

### Signature

```xquery
cts:valid-document-patch-path(
  $string as xs:string,
  $map as map:map??
) as xs:boolean
```

### Parameters

**`$string`**
The path to be tested as a string.

**`$map`** *(optional)*
A map of namespace bindings. The keys should be namespace prefixes and the
  values should be namespace URIs. These namespace bindings will be added to
  the in-scope namespace bindings in the evaluation of the path.

### Returns

`xs:boolean`

### Examples

#### Example 1

```xquery
cts:valid-document-patch-path("/foo/bar[@baz = '1']")
  => true
```

#### Example 2

```xquery
xquery version "1.0-ml";
  let $namespaces := map:map()
  let $_ := map:put($namespaces, "ns1", "http://example.org/myns")
  return cts:valid-document-patch-path("/ns1:foo/ns1:bar[@baz = '1']",$namespaces)
  => true
```

---

## cts:valid-extract-path

Parses path expressions and resolves namespaces using the $map parameter.
 Returns true if the argument is permissible as a path for
 extract-path option in extract-document-data

### Signature

```xquery
cts:valid-extract-path(
  $string as xs:string,
  $map as map:map??
) as xs:boolean
```

### Parameters

**`$string`**
The path to be tested as a string.

**`$map`** *(optional)*
A map of namespace bindings. The keys should be namespace prefixes and the
  values should be namespace URIs. These namespace bindings will be added to
  the in-scope namespace bindings in the evaluation of the path.

### Returns

`xs:boolean`

### Examples

#### Example 1

```xquery
cts:valid-extract-path("/foo/bar[@baz = '1']")
  => true
```

#### Example 2

```xquery
xquery version "1.0-ml";
  let $namespaces := map:map()
  let $_ := map:put($namespaces, "ns1", "http://example.org/myns")
  return cts:valid-extract-path("/ns1:foo/ns1:bar[@baz = '1']",$namespaces)
  => true
```

---

## cts:valid-index-path

Parses path expressions and resolves namespaces based on the server
 run-time environment. Returns true if the argument is
 permissible as a path for indexing.

### Signature

```xquery
cts:valid-index-path(
  $string as xs:string,
  $ignorens as xs:boolean
) as xs:boolean
```

### Parameters

**`$string`**
The path to be tested as a string.

**`$ignorens`**
Ignore namespace prefix binding errors.

### Returns

`xs:boolean`

### Examples

#### Example 1

```xquery
cts:valid-index-path("/aaa:a/bbb:b[1]/ccc:c",fn:false())
  => true
```

#### Example 2

```xquery
cts:valid-index-path("/a/b[c=/a/b/d]/p",fn:true())
  => false
```

---

## cts:valid-optic-path

Parses path expressions and resolves namespaces using the $map parameter.
 Support built in functions inside path since ML 11.0.0.
 Returns true if the argument is permissible as a path for
 Optic op:xpath

### Signature

```xquery
cts:valid-optic-path(
  $string as xs:string,
  $map as map:map??
) as xs:boolean
```

### Parameters

**`$string`**
The path to be tested as a string.

**`$map`** *(optional)*
A map of namespace bindings. The keys should be namespace prefixes and the
  values should be namespace URIs. These namespace bindings will be added to
  the in-scope namespace bindings in the evaluation of the path.

### Returns

`xs:boolean`

### Examples

#### Example 1

```xquery
cts:valid-optic-path("/foo/bar[@baz = '1']")
  => true
```

#### Example 2

```xquery
xquery version "1.0-ml";
  let $namespaces := map:map()
  let $_ := map:put($namespaces, "ns1", "http://example.org/myns")
  return cts:valid-optic-path("/ns1:foo/ns1:bar[@baz = '1']",$namespaces)
  => true
```

#### Example 3

```xquery
xquery version "1.0-ml";
  cts:valid-optic-path("/foo/bar[@baz = '1']/fn:string(.)")
  => true
```

---
