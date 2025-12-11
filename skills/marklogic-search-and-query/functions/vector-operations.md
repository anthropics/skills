# Vector Operations

13 functions in this category.

## vec:add

Returns the sum of two vectors. The vectors must be of the same dimension.

### Signature

```xquery
vec:add(
  $vector1 as vec:vector,
  $vector2 as vec:vector
) as vec:vector
```

### Parameters

**`$vector1`**
The first addend vector.

**`$vector2`**
The second addend vector.

### Returns

`vec:vector`

### Examples

#### Example 1

```xquery
xquery version "1.0-ml";
  let $vec1 := vec:vector((3.14,1.59,2.65))
  let $vec2 := vec:vector((3.58,9.79,3.23))

  return vec:add($vec1,$vec2);

  => [ 6.72, 11.38, 5.88 ]
```

#### Example 2

```xquery
xquery version "1.0-ml";

  let $vec1 := vec:vector(fn:head(fn:doc('pronethalol.json'))/data/array-node{embedding})
  let $vec2 := vec:vector(fn:head(fn:doc('cell_renewal.json'))/data/array-node{embedding})

  return vec:add($vec1,$vec2)

  => The sum of vectors in JSON arrays named 'embedding'
      in documents 'pronethalol.json' and 'cell_renewal.json'
```

---

## vec:base64-encode

Returns the base64 encoding of the vector. Useful for compressing a
    high-dimensional float vector represented as a string into fewer characters.

### Signature

```xquery
vec:base64-encode(
  $vector1 as vec:vector
) as xs:string
```

### Parameters

**`$vector1`**
The vector to base64 encode.

### Returns

`xs:string`

### Examples

#### Example 1

```xquery
xquery version "1.0-ml";
  let $vec1 := vec:vector((3.14,1.59,2.65))
  return vec:base64-encode($vec1)

  => kuF6JKCPwuUfzcwUIAAAAA==
```

#### Example 2

```xquery
xquery version "1.0-ml";
  let $vec1 := vec:vector(xdmp:to-json(fn:doc('pronethalol.json'))/data/array-node{embedding})
  return fn:string-length(vec:base64-encode($vec1)) || " VS " || fn:string-length(fn:string($vec1))

  => 8220 VS 18229
  (: This function compressed the string representation of the 1536 dimensional float vector
     in 'pronethalol.json' at array node 'embedding'
     from 18229 characters to 8220 characters.
  :)
```

---

## vec:cosine

Returns the cosine of the angle between two vectors. The vectors must be of
    the same dimension.

### Signature

```xquery
vec:cosine(
  $vector1 as vec:vector,
  $vector2 as vec:vector
) as xs:double
```

### Parameters

**`$vector1`**
The vector from which to calculate the cosine with vector2.

**`$vector2`**
The vector from which to calculate the cosine with vector1.

### Returns

`xs:double`

### Examples

#### Example 1

```xquery
xquery version "1.0-ml";
  let $vec1 := vec:vector((3.14,1.59,2.65))
  let $vec2 := vec:vector((3.58,9.79,3.23))

  return vec:cosine($vec1,$vec2);

  => 0.73559182882309
```

#### Example 2

```xquery
xquery version "1.0-ml";

  let $vec1 := vec:vector(fn:head(fn:doc('pronethalol.json'))/data/array-node{embedding})
  let $vec2 := vec:vector(fn:head(fn:doc('cell_renewal.json'))/data/array-node{embedding})

  return vec:cosine($vec1,$vec2)

  => The cosine between vectors in JSON arrays named 'embedding'
      in documents 'pronethalol.json' and 'cell_renewal.json'
```

#### Example 3

```xquery
xquery version "1.0-ml";
import module namespace op = 'http://marklogic.com/optic'
           at 'MarkLogic/optic.xqy';
import module namespace ovec = 'http://marklogic.com/optic/expression/vec'
           at 'MarkLogic/optic/optic-vec.xqy';

(: construct a query vector from the JSON array node 'emb' in document 'embedding104576.json' :)
let $qv := vec:vector(fn:head(fn:doc('embedding104576.json'))/array-node('emb'))

let $view := op:from-view('vecs','wiki_vectors')
           =>op:bind(op:as('cosine',ovec:cosine(op:col('embedding'),$qv)))
           =>op:select((op:col('title'),op:col('text'),op:col('cosine')))
           =>op:order-by(op:desc(op:col('cosine')))
           =>op:limit(30)
           =>op:result()
return $view;

=>
(:
  Performs a linear scan of vectors in the 'embedding' column in the 'wiki_vectors' view to find the top
   30 matches to the query vector $qv
:)
```

---

## vec:cosine-distance

Returns the cosine distance between two vectors. The vectors must be of
    the same dimension.

### Signature

```xquery
vec:cosine-distance(
  $vector1 as vec:vector,
  $vector2 as vec:vector
) as xs:double
```

### Parameters

**`$vector1`**
The vector from which to calculate the cosine distance to vector2.

**`$vector2`**
The vector from which to calculate the cosine distance to vector1.

### Returns

`xs:double`

### Examples

#### Example 1

```xquery
xquery version "1.0-ml";
  let $vec1 := vec:vector((3.14,1.59,2.65))
  let $vec2 := vec:vector((3.58,9.79,3.23))

  return vec:cosine-distance($vec1,$vec2);

  => 0.26440817117691
```

#### Example 2

```xquery
xquery version "1.0-ml";

  let $vec1 := vec:vector(fn:head(fn:doc('pronethalol.json'))/data/array-node{embedding})
  let $vec2 := vec:vector(fn:head(fn:doc('cell_renewal.json'))/data/array-node{embedding})

  return vec:cosine-distance($vec1,$vec2)

  => The cosine distance between vectors in JSON arrays named 'embedding'
      in documents 'pronethalol.json' and 'cell_renewal.json'
```

#### Example 3

```xquery
xquery version "1.0-ml";
import module namespace op = 'http://marklogic.com/optic'
           at 'MarkLogic/optic.xqy';
import module namespace ovec = 'http://marklogic.com/optic/expression/vec'
            at 'MarkLogic/optic/optic-vec.xqy';
  
  (: construct a query vector from the JSON array node 'emb' in document 'embedding104576.json' :)
  let $qv := vec:vector(fn:head(fn:doc('embedding104576.json'))/array-node('emb'))

  let $view := op:from-view('vecs','wiki_vectors')
             =>op:bind(op:as('cosineDist',ovec:cosine-distance(op:col('embedding'),$qv)))
             =>op:select((op:col('title'),op:col('text'),op:col('cosineDist')))
             =>op:order-by(op:asc(op:col('cosineDist')))
             =>op:limit(30)
             =>op:result()
  return $view;

  =>
  // Performs a linear scan of vectors in the 'embedding' column in the 'wiki_vectors' view to find the top
  //  30 matches to the query vector $qv
```

---

## vec:dimension

Returns the dimension of the vector passed in.

### Signature

```xquery
vec:dimension(
  $vector1 as vec:vector
) as xs:unsignedInt
```

### Parameters

**`$vector1`**
The vector to find the dimension of.

### Returns

`xs:unsignedInt`

### Examples

```xquery
xquery version "1.0-ml";
  vec:dimension(vec:vector((3.14, 1.59, 2.65)))

  => 3
```

---

## vec:dot-product

Returns the dot product between two vectors. The vectors must be of
    the same dimension. Use this function to calculate similarity between
    vectors if you are certain they are both of magnitude 1.

### Signature

```xquery
vec:dot-product(
  $vector1 as vec:vector,
  $vector2 as vec:vector
) as xs:double
```

### Parameters

**`$vector1`**
The vector from which to calculate the dot product with vector2.

**`$vector2`**
The vector from which to calculate the dot product with vector1.

### Returns

`xs:double`

### Examples

#### Example 1

```xquery
xquery version "1.0-ml";
  let $vec1 := vec:normalize(vec:vector((3.14,1.59,2.65)))
  let $vec2 := vec:normalize(vec:vector((3.58,9.79,3.23)))

  return vec:dot-product($vec1,$vec2);

  => 0.735591769218445
```

#### Example 2

```xquery
xquery version "1.0-ml";

  let $vec1 := vec:vector(fn:head(fn:doc('pronethalol.json'))/data/array-node{embedding})
  let $vec2 := vec:vector(fn:head(fn:doc('cell_renewal.json'))/data/array-node{embedding})

  return vec:dot-product($vec1,$vec2)

  => The dot product between vectors in JSON arrays named 'embedding'
      in documents 'pronethalol.json' and 'cell_renewal.json'
    Can be used instead of vec:cosine() if you are sure the
      vectors are normalized to magnitude 1.
```

---

## vec:euclidean-distance

Returns the Euclidean distance between two vectors. The vectors must be of
    the same dimension.

### Signature

```xquery
vec:euclidean-distance(
  $vector1 as vec:vector,
  $vector2 as vec:vector
) as xs:double
```

### Parameters

**`$vector1`**
The vector from which to calculate the Euclidean distance to vector2.

**`$vector2`**
The vector from which to calculate the Euclidean distance to vector1.

### Returns

`xs:double`

### Examples

#### Example 1

```xquery
xquery version "1.0-ml";
  let $vec1 := vec:vector((3.14,1.59,2.65))
  let $vec2 := vec:vector((3.58,9.79,3.23))

  return vec:euclidean-distance($vec1,$vec2);

  => 8.23225402832031
```

#### Example 2

```xquery
xquery version "1.0-ml";

  let $vec1 := vec:vector(fn:head(fn:doc('pronethalol.json'))/data/array-node{embedding})
  let $vec2 := vec:vector(fn:head(fn:doc('cell_renewal.json'))/data/array-node{embedding})

  return vec:euclidean-distance($vec1,$vec2)

  => The Euclidean distance between vectors in JSON arrays named 'embedding'
      in documents 'pronethalol.json' and 'cell_renewal.json'
```

#### Example 3

```xquery
xquery version "1.0-ml";
import module namespace op = 'http://marklogic.com/optic'
           at 'MarkLogic/optic.xqy';
import module namespace ovec = 'http://marklogic.com/optic/expression/vec'
           at 'MarkLogic/optic/optic-vec.xqy';

(: construct a query vector from the JSON array node 'emb' in document 'embedding104576.json' :)
let $qv := vec:vector(fn:head(fn:doc('embedding104576.json'))/array-node('emb'))

let $view := op:from-view('vecs','wiki_vectors')
           =>op:bind(op:as('euclDistance',ovec:euclidean-distance(op:col('embedding'),$qv)))
           =>op:select((op:col('title'),op:col('text'),op:col('euclDistance')))
           =>op:order-by(op:asc(op:col('euclDistance')))
           =>op:limit(30)
           =>op:result()
return $view;

(: Performs a linear scan of vectors in the 'embedding' column in the 'wiki_vectors' view to find the top
   30 matches to the query vector $qv
:)
```

---

## vec:get

Returns the element at the k-th index of the vector.

### Signature

```xquery
vec:get(
  $vector1 as vec:vector,
  $k as xs:unsignedInt
) as xs:float
```

### Parameters

**`$vector1`**
The vector to grab the k-th element of.

**`$k`**
The zero-based index of vector1 to return. If k is greater than the number of elements in the vector,
      throw VEC-OUTOFBOUNDS.

### Returns

`xs:float`

### Examples

```xquery
xquery version "1.0-ml";
  let $vec1 := vec:vector((3.14,1.59,2.65))
  return vec:get($vec1, 1)

  => 1.59
```

---

## vec:magnitude

Returns the magnitude of the vector.

### Signature

```xquery
vec:magnitude(
  $vector1 as vec:vector
) as xs:float
```

### Parameters

**`$vector1`**
The vector to find the magnitude of.

### Returns

`xs:float`

### Examples

```xquery
xquery version "1.0-ml";
  let $vec1 := vec:vector((3.14,1.59,2.65))
  return vec:magnitude($vec1)

  => 4.40570116043091
```

---

## vec:normalize

Returns the vector passed in, normalized to a length of 1.

### Signature

```xquery
vec:normalize(
  $vector1 as vec:vector
) as vec:vector
```

### Parameters

**`$vector1`**
The vector to normalize.

### Returns

`vec:vector`

### Examples

```xquery
xquery version "1.0-ml";
  vec:normalize(vec:vector((3.14, 1.59, 2.65)))

  => [ 0.712713, 0.360896, 0.601493 ] (: the vector value normalized to length 1 :)
```

---

## vec:subtract

Returns the difference of two vectors. The vectors must be of the same dimension.

### Signature

```xquery
vec:subtract(
  $vector1 as vec:vector,
  $vector2 as vec:vector
) as vec:vector
```

### Parameters

**`$vector1`**
The minuend vector.

**`$vector2`**
The subtrahend vector.

### Returns

`vec:vector`

### Examples

#### Example 1

```xquery
xquery version "1.0-ml";
  let $vec1 := vec:vector((3.14,1.59,2.65))
  let $vec2 := vec:vector((3.58,9.79,3.23))

  return vec:subtract($vec1,$vec2);

  => [ -0.44, -8.2, -0.58 ]
```

#### Example 2

```xquery
xquery version "1.0-ml";

  let $vec1 := vec:vector(fn:head(fn:doc('pronethalol.json'))/data/array-node{embedding})
  let $vec2 := vec:vector(fn:head(fn:doc('cell_renewal.json'))/data/array-node{embedding})

  return vec:subtract($vec1,$vec2)

  => The difference of vectors in JSON arrays named 'embedding'
      in documents 'pronethalol.json' and 'cell_renewal.json'
```

---

## vec:subvector

Returns a subvector of the input vector, starting at the specified index, with the specified length (optional).

### Signature

```xquery
vec:subvector(
  $vector as vec:vector,
  $start as xs:unsignedInt,
  $length as xs:unsignedInt??
) as vec:vector
```

### Parameters

**`$vector`**
The input vector.

**`$start`**
The zero-based index of the input vector from which to start (inclusive).

**`$length`** *(optional)*
The length of the subvector. If not provided, returns a subvector beginning from index at start
      to the end of the input vector. If length is greater than the number of elements left in the input vector,
      throw VEC-OUTOFBOUNDS.

### Returns

`vec:vector`

### Examples

```xquery
xquery version "1.0-ml";
  let $vector := vec:vector((3.14,1.59,2.65,3.58,9.79,3.23))
  return vec:subvector($vector, 2, 3)

  => [ 2.65, 3.58, 9.79 ]
```

---

## vec:vector-score

A helper function that returns a hybrid score using a cts score and a vector distance calculation result.
  You can tune the effect of the vector distance on the score using the distanceWeight option. The ideal 
  value for distanceWeight depends on your application.

  The hybrid score is calculated using the formula:
  score = weight * annScore + (1 - weight) * ctsScore.
  - annScore is derived from the distance and distanceWeight, where a larger distanceWeight reduces the annScore for the same distance.
  - weight determines the contribution of the annScore and ctsScore to the final score. A weight of 0.5 balances both equally.
  This formula allows you to combine traditional cts scoring with vector-based distance scoring, providing a flexible way to rank results.

### Signature

```xquery
vec:vector-score(
  $score as xs:unsignedInt,
  $distance as xs:double,
  $distanceWeight as xs:double??,
  $weight as xs:double??
) as xs:unsignedLong
```

### Parameters

**`$score`**
The cts:score of the matching document.

**`$distance`**
The distance between the vector in the matching document and the query vector. Examples, the result of
    a call to ovec:cosine-distance() or ovec:euclidean-distance().

**`$distanceWeight`** *(optional)*
The weight of the vector distance on the annScore. This value is a positive
    coefficient that scales the distance. A larger distanceWeight produces a lower annScore for the same distance.
    The default value is 1.

**`$weight`** *(optional)*
The weight of the annScore in the final hybrid score. This value is a coefficient between 0 and 1, where 0 gives
    full weight to the cts score and 1 gives full weight to the annScore. The default value is 0.5.

### Returns

`xs:unsignedLong`

### Examples

```xquery
xquery version "1.0-ml";
import module namespace op = 'http://marklogic.com/optic'
           at 'MarkLogic/optic.xqy';
import module namespace ovec = 'http://marklogic.com/optic/expression/vec'
           at 'MarkLogic/optic/optic-vec.xqy';
import module namespace ofn = 'http://marklogic.com/optic/expression/fn'
           at 'MarkLogic/optic/optic-fn.xqy';

(: grab a query vector from the document below at the array node named 'emb' :)
let $qv    := vec:vector(fn:head(fn:doc('embedding104206.json'))/array-node('emb'))

(: define a word query to find relevant documents :)
let $query := cts:word-query('turtle')

(: define a view named 'from_search' that contains our search results :)
let $search   := op:from-search($query,('fragmentId','score'),'from_search')

(: join a TDE view named 'wiki_vectors' with which to calculate a hybrid score :)
let $result := op:from-view('vecs','wiki_vectors',(),op:fragment-id-col('view_frag'))
             => op:join-inner($search,op:on(op:view-col('wiki_vectors','view_frag'),op:view-col('from_search','fragmentId')))
             => op:join-doc-uri(op:col('uri'),op:fragment-id-col('view_frag'))
             => op:bind(op:as('cosDistance',ovec:cosine-distance(op:view-col('wiki_vectors','embedding'),$qv)))
             => op:bind(op:as('hybridScore',ovec:vector-score(op:col('score'), op:col('cosDistance'), 0.5, 1.0)))
             => op:select((op:col('score'),op:col('cosDistance'),op:col('hybridScore'),op:col('uri')))
             => op:order-by((op:desc(op:col('hybridScore')),op:col('uri')))
             => op:result()
return $result

=> A table with the result of scoring the document, combining the cts score with vector distance
```

---
