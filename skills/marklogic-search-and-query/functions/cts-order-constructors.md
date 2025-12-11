# Cts:Order Constructors

7 functions in this category.

## cts:confidence-order

Creates a confidence-based ordering clause, for use as an option to
  
  cts:search.

### Signature

```xquery
cts:confidence-order(
  $options as xs:string*?
) as cts:order
```

### Parameters

**`$options`** *(optional)*
Options. 
    
      Options include:
      
        "descending"
        Results should be returned in descending order of confidence.
        "ascending"
        Results should be returned in ascending order of confidence.

### Returns

`cts:order`

### Usage Notes

Only one of "ascending" or "descending" may be specified
  in the options parameter.  If neither "ascending" nor "descending"
  is specified, then the default is "ascending".

### Examples

```xquery
cts:confidence-order("descending")
(: Returns the specified opaque cts:order object :)
```

---

## cts:document-order

Creates a document-based ordering clause, for use as an option to
  
  cts:search.

### Signature

```xquery
cts:document-order(
  $options as xs:string*?
) as cts:order
```

### Parameters

**`$options`** *(optional)*
Options.
    
      Options include:
      
        "descending"
        Results should be returned in descending order of document.
        "ascending"
        Results should be returned in ascending order of document.

### Returns

`cts:order`

### Usage Notes

Only one of "ascending" or "descending" may be specified
  in the options parameter.  If neither "ascending" nor "descending"
  is specified, then the default is "ascending".

### Examples

```xquery
cts:document-order("descending")
(: Returns the specified opaque cts:order object :)
```

---

## cts:fitness-order

Creates a fitness-based ordering clause, for use as an option to
  
  cts:search.

### Signature

```xquery
cts:fitness-order(
  $options as xs:string*?
) as cts:order
```

### Parameters

**`$options`** *(optional)*
Options.
    
      Options include:
      
        "descending"
        Return results in descending order of fitness.
        "ascending"
        Return results in ascending order of fitness.

### Returns

`cts:order`

### Usage Notes

Only one of "ascending" or "descending" may be specified
  in the options parameter.  If neither "ascending" nor "descending"
  is specified, then the default is "ascending".

### Examples

```xquery
cts:fitness-order("descending")
(: Returns the specified opaque cts:order object :)
```

---

## cts:index-order

Creates a index-based ordering clause, for use as an option to
  
  cts:search.

### Signature

```xquery
cts:index-order(
  $index as cts:reference,
  $options as xs:string*?
) as cts:order
```

### Parameters

**`$index`**
A reference to a range index.

**`$options`** *(optional)*
Options.  The default is ().
    
      Options include:
      
        "descending"
        Results should be returned in descending order of index.
        "ascending"
        Results should be returned in ascending order of index.

### Returns

`cts:order`

### Usage Notes

Only one of "ascending" or "descending" may be specified
  in the options parameter.  If neither "ascending" nor "descending"
  is specified, then the default is "ascending".

### Examples

```xquery
cts:index-order(cts:element-reference(xs:QName("TITLE")))

(: returns the following:
cts:index-order(cts:element-reference(fn:QName("","TITLE"),
  ("type=string","collation=http://marklogic.com/collation/")), "ascending")
:)
```

---

## cts:quality-order

Creates a quality-based ordering clause, for use as an option to
  
  cts:search.

### Signature

```xquery
cts:quality-order(
  $options as xs:string*?
) as cts:order
```

### Parameters

**`$options`** *(optional)*
Options.
    
      Options include:
      
        "descending"
        Results should be returned in descending order of quality.
        "ascending"
        Results should be returned in ascending order of quality.

### Returns

`cts:order`

### Usage Notes

Only one of "ascending" or "descending" may be specified
  in the options parameter.  If neither "ascending" nor "descending"
  is specified, then the default is "ascending".

### Examples

```xquery
cts:quality-order("descending")
(: Returns the specified opaque cts:order object :)
```

---

## cts:score-order

Creates a score-based ordering clause, for use as an option to
  
  cts:search.

### Signature

```xquery
cts:score-order(
  $options as xs:string*?
) as cts:order
```

### Parameters

**`$options`** *(optional)*
Options.
    
      Options include:
      
        "descending"
        Return results in descending order of score.
        "ascending"
        Return results in ascending order of score.

### Returns

`cts:order`

### Usage Notes

Only one of "ascending" or "descending" may be specified
  in the options parameter.  If neither "ascending" nor "descending"
  is specified, then the default is "ascending".

### Examples

```xquery
cts:score-order("descending")

(: Returns the specified opaque cts:order object :)
```

---

## cts:unordered

Specifies that results should be unordered, for use with
  
  cts:search.

### Returns

`cts:order`

### Examples

```xquery
cts:unordered()
(: Returns the specified opaque cts:order object :)
```

---
