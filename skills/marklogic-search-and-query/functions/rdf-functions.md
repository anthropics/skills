# Rdf Functions

2 functions in this category.

## rdf:langString

Returns an rdf:langString value with the 
   given value and language tag. The rdf:langString type extends 
   xs:string, and represents a language tagged string in RDF.
  
      This function is a built-in.

### Signature

```xquery
rdf:langString(
  $string as xs:string,
  $lang as xs:string
) as rdf:langString
```

### Parameters

**`$string`**
The lexical value.

**`$lang`**
The language.

### Returns

`rdf:langString`

### Examples

```xquery
rdf:langString("http://foo/bar", "en")
=> an rdf:langString representing "http://foo/bar" in english
```

---

## rdf:langString-language

Returns the language of an rdf:langString 
   value.
      This function is a built-in.

### Signature

```xquery
rdf:langString-language(
  $val as rdf:langString
) as xs:string
```

### Parameters

**`$val`**
The rdf:langString value.

### Returns

`xs:string`

### Examples

```xquery
rdf:langString-language(rdf:langString("http://foo/bar", "en"))
=> en
```

---
