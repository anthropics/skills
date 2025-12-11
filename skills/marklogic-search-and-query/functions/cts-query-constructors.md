# Cts:Query Constructors

226 functions in this category.

## cts:after-query

Returns a query matching fragments committed after a specified timestamp.

### Signature

```xquery
cts:after-query(
  $timestamp as xs:unsignedLong
) as cts:after-query
```

### Parameters

**`$timestamp`**
A commit timestamp.  
    Database fragments committed after this timestamp are matched.

### Returns

`cts:after-query`

### Usage Notes

Fragment commit timestamps change not only by application transactions, but also
by system transactions from the reindexer or the rebalancer. The query
will also match fragments whose timestamps have been changed because of reindexing
and rebalancing after the given timestamp.

### Examples

```xquery
cts:uris("",(),
  cts:after-query(xdmp:wallclock-to-timestamp(
  fn:current-dateTime() - xs:dayTimeDuration("PT1H")))
)

 => URIs of fragments committed in the last one hour
```

---

## cts:after-query-timestamp

Returns the timestamp with which a specified query was constructed.

### Signature

```xquery
cts:after-query-timestamp(
  $query as cts:after-query
) as xs:unsignedLong
```

### Parameters

**`$query`**
A query.

### Returns

`xs:unsignedLong`

### Examples

```xquery
cts:after-query-timestamp(cts:after-query(
  xdmp:wallclock-to-timestamp(
  fn:current-dateTime() - xs:dayTimeDuration("PT3H")))
)

 => timestamp of the specified query
```

---

## cts:and-not-query

Returns a query specifying the set difference of
  the matches specified by two sub-queries.

### Signature

```xquery
cts:and-not-query(
  $positive-query as cts:query,
  $negative-query as cts:query
) as cts:and-not-query
```

### Parameters

**`$positive-query`**
A positive query, specifying the search results
    filtered in.

**`$negative-query`**
A negative query, specifying the search results
    to filter out.

### Returns

`cts:and-not-query`

### Usage Notes

This query construct is fragment-based, so it returns true only if the 
  specified query does not produce a match anywhere in a fragment.  
  Therefore, a search using 
  cts:and-not-query 
  is only guaranteed to be accurate if the negative query is accurate from 
  its index resolution (that is, if the unfiltered results of the 
  negative query are accurate. The accuracy of the index resolution depends
  on many factors such as the query, whether you search
  at a fragment root (that is, if the first parameter of
  cts:search 
  specifies an XPath that resolves to a fragment root),
  the index options enabled on the database, the search options, and other 
  factors.  In cases where the $negative-query parameter has false
  positive matches, the negation of the query can miss matches (have false 
  negative matches).  In these cases, searches with 
  cts:and-not-query
  can miss results, even if those searches are filtered.

### Examples

```xquery
cts:search(//PLAY,
    cts:and-not-query(
      cts:word-query("summer"),
      cts:word-query("glorious")))
  => .. sequence of 'PLAY' elements containing some
  text node with the word 'summer' BUT NOT containing
  any text node with the word 'glorious'.  This sequence
  may be (in fact is) non-empty, but certainly does not
  contain the PLAY element with:

    PLAY/TITLE =
      "The Tragedy of King Richard the Second"

  since this play contains both 'glorious' and 'summer'.
```

---

## cts:and-not-query-negative-query

Returns the negative (second parameter) query used to construct the
  specified query.

### Signature

```xquery
cts:and-not-query-negative-query(
  $query as cts:and-not-query
) as cts:query
```

### Parameters

**`$query`**
A query.

### Returns

`cts:query`

### Examples

```xquery
let $query := cts:and-not-query(
                 cts:word-query("wanted"),
                 cts:word-query("unwanted"))
return cts:and-not-query-negative-query($query)

  => cts:word-query("unwanted", ("lang=en"), 1)
```

---

## cts:and-not-query-positive-query

Returns the positive (first parameter) query used to construct the
  specified query.

### Signature

```xquery
cts:and-not-query-positive-query(
  $query as cts:and-not-query
) as cts:query
```

### Parameters

**`$query`**
A query.

### Returns

`cts:query`

### Examples

```xquery
let $query := cts:and-not-query(
                 cts:word-query("wanted"),
                 cts:word-query("unwanted"))
return cts:and-not-query-positive-query($query)

  => cts:word-query("wanted", ("lang=en"), 1)
```

---

## cts:and-query

Returns a query specifying the intersection
  of the matches specified by the sub-queries.

### Signature

```xquery
cts:and-query(
  $queries as cts:query*,
  $options as xs:string*?
) as cts:and-query
```

### Parameters

**`$queries`**
A sequence of sub-queries.

**`$options`** *(optional)*
Options to this query.  The default is ().
    
      Options include:
      
        "ordered"
        An ordered and-query, which specifies that the sub-query matches
            must occur in the order of the specified sub-queries.  For example,
            if the sub-queries are "cat" and "dog", an ordered
            query will only match fragments where both "cat" and "dog" occur,
            and where "cat" comes before "dog" in the fragment.
        "unordered"
        An unordered and-query, which specifies that the sub-query matches
        can occur in any order.

### Returns

`cts:and-query`

### Usage Notes

If the options parameter contains neither "ordered" nor "unordered",
  then the default is "unordered".
      If you specify the empty sequence for the queries parameter
  to cts:and-query, you will get a match for every document in
  the database.  For example, the following query always returns true:
        cts:contains(collection(), cts:and-query(()))
       In order to match a cts:and-query, the matches
  from each of the specified sub-queries must all occur in the same
  fragment.

### Examples

```xquery
cts:search(//PLAY,
    cts:and-query((
      cts:word-query("to be or"),
      cts:word-query("or not to be"))))
  =&gt; .. a sequence of 'PLAY' elements which are
  ancestors (or self) of some node whose text content
  contains the phrase 'to be or' AND some node
  whose text content contains the phrase 'or not to be'.
  With high probability this intersection contains only
  one 'PLAY' element, namely,

    PLAY/TITLE =
      "The Tragedy of Hamlet, Prince of Denmark".
```

---

## cts:and-query-options

Returns the options for the specified query.

### Signature

```xquery
cts:and-query-options(
  $query as cts:and-query
) as xs:string*
```

### Parameters

**`$query`**
A query.

### Returns

`xs:string*`

### Examples

```xquery
let $query :=
  cts:and-query((
    cts:word-query("to be or"),
    cts:word-query("or not to be")))
return cts:and-query-queries($query)
  => ()
```

---

## cts:and-query-queries

Returns a sequence of the queries that were used to construct the specified
  query.

### Signature

```xquery
cts:and-query-queries(
  $query as cts:and-query
) as cts:query*
```

### Parameters

**`$query`**
A query.

### Returns

`cts:query*`

### Examples

#### Example 1

```xquery
cts:and-query-queries($query)
  => ... a sequence of the queries used to
            construct this query
```

#### Example 2

```xquery
let $query :=
  cts:and-query((
    cts:word-query("to be or"),
    cts:word-query("or not to be")))
return cts:and-query-queries($query)
  => (cts:word-query("to be or", (), 1)
         cts:word-query("or not to be", (), 1))
```

---

## cts:before-query

Returns a query matching fragments committed before or at a specified timestamp.

### Signature

```xquery
cts:before-query(
  $timestamp as xs:unsignedLong
) as cts:before-query
```

### Parameters

**`$timestamp`**
A commit timestamp.  
    Database fragments committed before this timestamp are matched.

### Returns

`cts:before-query`

### Usage Notes

Fragment commit timestamps change not only by application transactions, but also
by system transactions from the reindexer or the rebalancer. The query
will also match fragments whose timestamps have been changed because of reindexing
and rebalancing before the given timestamp.

### Examples

```xquery
cts:uris("",(),
  cts:before-query(xdmp:wallclock-to-timestamp(
  fn:current-dateTime() - xs:dayTimeDuration("PT1H")))
)

 => URIs of fragments committed one hour before the current time
```

---

## cts:before-query-timestamp

Returns the timestamp with which a specified query was constructed.

### Signature

```xquery
cts:before-query-timestamp(
  $query as cts:before-query
) as xs:unsignedLong
```

### Parameters

**`$query`**
A query.

### Returns

`xs:unsignedLong`

### Examples

```xquery
cts:before-query-timestamp(cts:before-query(
  xdmp:wallclock-to-timestamp(
  fn:current-dateTime() - xs:dayTimeDuration("PT3H")))
)

 => timestamp of the specified query
```

---

## cts:boost-query

Returns a query specifying that matches to $matching-query
  should have their search relevance scores boosted if they also match
  $boosting-query.

### Signature

```xquery
cts:boost-query(
  $matching-query as cts:query,
  $boosting-query as cts:query
) as cts:boost-query
```

### Parameters

**`$matching-query`**
A sub-query that is used for match and scoring.

**`$boosting-query`**
A sub-query that is used only for boosting score.

### Returns

`cts:boost-query`

### Usage Notes

When used in a search, $boosting-query is not evaluated
  if there are no matches to $matching-query.
      When used in a search, all matches to $matching-query
  are included in the search results. $boosting-query
  only contributes to search relevances scores. Scoring is done the same
  way as for a cts:and-query.

### Examples

```xquery
cts:search(fn:collection(),
    cts:boost-query(cts:word-query("George"),
                    cts:word-query("Washington", (), 10.0)
    )
  )[1 to 10]
  => The first 10 documents containing the word "George". Those documents
     that also contain the word "Washington" have a higher relevance
     score than those elements that do not.
```

---

## cts:boost-query-boosting-query

Returns the boosting (second parameter) query used to construct the
  specified boost query.

### Signature

```xquery
cts:boost-query-boosting-query(
  $query as cts:boost-query
) as cts:query
```

### Parameters

**`$query`**
A query.

### Returns

`cts:query`

### Examples

```xquery
let $query := cts:boost-query(
                cts:word-query("wanted"),
                cts:word-query("unwanted"))
return cts:boost-query-boosting-query($query)

  => cts:word-query("unwanted", (), 1)
```

---

## cts:boost-query-matching-query

Returns the matching (first parameter) query used to construct the
  specified boost query.

### Signature

```xquery
cts:boost-query-matching-query(
  $query as cts:boost-query
) as cts:query
```

### Parameters

**`$query`**
A query.

### Returns

`cts:query`

### Examples

```xquery
let $query := cts:boost-query(
                cts:word-query("wanted"),
                cts:word-query("unwanted"))
return cts:boost-query-matching-query($query)

  => cts:word-query("wanted", (), 1)
```

---

## cts:collection-query

Match documents in at least one of the specified collections.
  It will match both documents and properties documents in the collections
  with the given URIs.

### Signature

```xquery
cts:collection-query(
  $uris as xs:string*
) as cts:collection-query
```

### Parameters

**`$uris`**
One or more collection URIs. A document matches the query if it is 
    in at least one of these collections.

### Returns

`cts:collection-query`

### Examples

```xquery
cts:search(//function,
    cts:collection-query(("reports", "analysis")))

  => .. a sequence of 'function' elements in any document in the
     collection "reports" or in the collection "analysis".
```

---

## cts:collection-query-uris

Returns the URIs used to construct the specified query.

### Signature

```xquery
cts:collection-query-uris(
  $query as cts:collection-query
) as xs:string*
```

### Parameters

**`$query`**
A query.

### Returns

`xs:string*`

### Examples

```xquery
let $query := cts:collection-query(("reports", "analysis"))
return
cts:collection-query-uris($query)
  => ("reports", "analysis")
```

---

## cts:column-range-query

Returns a 
  cts:query
  matching documents matching a TDE-view column equals to an value.  Searches with the
  cts:column-range-query
  constructor require the triple index;
  if the triple index is not configured, then an exception is thrown.

### Signature

```xquery
cts:column-range-query(
  $schema as xs:string,
  $view as xs:string,
  $column as xs:string,
  $value as xs:anyAtomicType*,
  $operator as xs:string??,
  $options as xs:string*?,
  $weight as xs:double??
) as cts:triple-range-query
```

### Parameters

**`$schema`**
The TDE schema name.

**`$view`**
The TDE view name.

**`$column`**
The TDE column name.

**`$value`**
One or more values used for querying.

**`$operator`** *(optional)*
Operator for the $value values. The default operator is "=".
    
      Operators include:
       
        "<"
        Match range index values less than $value.
        "<="
        Match range index values less than or equal to $value.
        ">"
        Match range index values greater than $value.
        ">="
        Match range index values greater than or equal to $value.
        "="
        Match range index values equal to $value.
        "!="
        Match range index values not equal to $value.

**`$options`** *(optional)*
Options to this query.  The default is ().
    
      Options include:
      
        "cached"
        Cache the results of this query in the list cache.
        "uncached"
        Do not cache the results of this query in the list cache.
        "score-function=function"
        Use the selected scoring function. The score function may be:
          
          linearUse a linear function of the difference between the
          specified query value and the matching value in the index to calculate
          a score for this range query.
          reciprocalUse a reciprocal function of the difference
          between the specified query value and the matching value in the
          index to calculate a score for this range query.
          zeroThis range query does not contribute to the
          score. This is the default.
          
        
        "slope-factor=number"
        Apply the given number as a scaling factor to the slope of the
        scoring function. The default is 1.0.

**`$weight`** *(optional)*
A weight for this query.  The default is 1.0.

### Returns

`cts:triple-range-query`

### Usage Notes

This function returns a cts:triple-range-query, and all functions which takes cts:triple-range-query as an input can be used (e.g. cts:triple-range-query-subject).

      
This type of query may only be used in unfiltered search,
i.e. cts:search
 with 'unfiltered' option, and index lookup,
e.g. cts.uris

.

      
The column parameter must be an indexed column, i.e. does not have the virtual=true or belong to a view with viewVirtual=true

### Examples

```xquery
xquery version "1.0-ml"; 
let $query:=cts:column-range-query("MySchema","MyView","value",xs:decimal(200), "<")  
return cts:uris((),(),$query)
```

---

## cts:directory-query

Returns a query matching documents in the directories with the given URIs.

### Signature

```xquery
cts:directory-query(
  $uris as xs:string*,
  $depth as xs:string??
) as cts:directory-query
```

### Parameters

**`$uris`**
One or more directory URIs.

**`$depth`** *(optional)*
"1" for immediate children, "infinity" for all.  If not supplied,
    depth is "1".

### Returns

`cts:directory-query`

### Usage Notes

The directory URI should always have a trailing slash.

### Examples

```xquery
cts:search(//function,
    cts:directory-query(("/reports/","/analysis/"),"1"))

  => .. a sequence of 'function' elements in any document
     in the directory "/reports/" or the directory "/analysis/".
```

---

## cts:directory-query-depth

Returns the depth used to construct the specified query.

### Signature

```xquery
cts:directory-query-depth(
  $query as cts:directory-query
) as xs:string
```

### Parameters

**`$query`**
A query.

### Returns

`xs:string`

### Examples

```xquery
let $query := cts:directory-query(("/reports/", "/analysis/"))
return
cts:directory-query-depth($query)
  => 1
```

---

## cts:directory-query-uris

Returns the URIs used to construct the specified query.

### Signature

```xquery
cts:directory-query-uris(
  $query as cts:directory-query
) as xs:string*
```

### Parameters

**`$query`**
A query.

### Returns

`xs:string*`

### Examples

```xquery
let $query := cts:directory-query(("/reports/", "/analysis/"))
return
cts:directory-query-uris($query)
  => ("/reports/", "/analysis/")
```

---

## cts:document-format-query

Returns a query matching documents of a given format.

### Signature

```xquery
cts:document-format-query(
  $format as xs:string
) as cts:document-format-query
```

### Parameters

**`$format`**
Case insensitve one of: "json","xml","text","binary". This will result in a XDMP-ARG exception  in case of an invalid format.

### Returns

`cts:document-format-query`

### Examples

```xquery
cts:uris((),(),cts:document-format-query("xml"))
  => .. Return all XML documents URIs.
```

---

## cts:document-format-query-format

Returns the formt used to construct the specified query.

### Signature

```xquery
cts:document-format-query-format(
  $query as cts:document-format-query
) as xs:string
```

### Parameters

**`$query`**
A query.

### Returns

`xs:string`

### Examples

```xquery
cts:document-format-query-format(cts:document-format-query("xml")) 
  => "xml"
```

---

## cts:document-fragment-query

Returns a query that matches all documents where $query matches
  any document fragment.  When searching documents, document-properties, or
  document-locks, this function provides a
  convenient way to additionally constrain the search against any document
  fragment.

### Signature

```xquery
cts:document-fragment-query(
  $query as cts:query
) as cts:document-fragment-query
```

### Parameters

**`$query`**
A query to be matched against any document fragment.

### Returns

`cts:document-fragment-query`

### Usage Notes

A document fragment query enables you to cross fragment boundaries 
in an AND query, as shown in the second example below.

### Examples

#### Example 1

```xquery
cts:search(
xdmp:document-properties(),
  cts:document-fragment-query(
    cts:word-query("hello")))

(: All properties documents whose corresponding document
 : (that is, the document at the same URI as the
 : proerties document) contain the word "hello". :)
```

#### Example 2

```xquery
xquery version "1.0-ml";
(:
 Given a document with a fragment root of <fragment>
 created as follows:

xdmp:document-insert("fragmented.xml",
   <root>
     <author>bob</author>
     <fragment>dog</fragment>
     <fragment>cat</fragment>
     <fragment>fish</fragment>
  </root>);
:)

cts:search(fn:doc("fragmented.xml"),
  cts:and-query((
    cts:document-fragment-query("bob"),
    "dog"
  ))
)

(: returns the fragmented.xml document :)
```

---

## cts:document-fragment-query-query

Returns the query used to construct the specified query.

### Signature

```xquery
cts:document-fragment-query-query(
  $query as cts:document-fragment-query
) as cts:query
```

### Parameters

**`$query`**
A query.

### Returns

`cts:query`

### Examples

```xquery
cts:document-fragment-query-query(
     cts:document-fragment-query(cts:word-query("word")))
  => cts:word-query("word", ("lang=en"), 1)
```

---

## cts:document-permission-query

Returns a query matching documents with a given permission.

### Signature

```xquery
cts:document-permission-query(
  $role as xs:string,
  $capability as xs:string
) as cts:document-permission-query
```

### Parameters

**`$role`**
The role of the permission

**`$capability`**
The capability of the permission (read, update, node-update, insert, execute)

### Returns

`cts:document-permission-query`

### Examples

```xquery
cts:uris((),(),cts:document-permission-query("admin","execute"))
=> .. Return all URIs of documents which have admin/execute permission
```

---

## cts:document-permission-query-capability

Returns the capability used to construct the specified query.

### Signature

```xquery
cts:document-permission-query-capability(
  $query as cts:document-permission-query
) as xs:string
```

### Parameters

**`$query`**
A query.

### Returns

`xs:string`

### Examples

```xquery
cts:document-permission-query-capability(cts:document-permission-query("admin","read")) 
  => "xml"
```

---

## cts:document-query

Returns a query matching documents with the given URIs.  It will match both
  documents and properties documents with the given URIs.

### Signature

```xquery
cts:document-query(
  $uris as xs:string*
) as cts:document-query
```

### Parameters

**`$uris`**
One or more document URIs.

### Returns

`cts:document-query`

### Examples

#### Example 1

```xquery
cts:search(//function,
    cts:document-query("/reports.xml"))

  => .. relevance-ordered sequence of 'function' elements
  in the document "/reports.xml".
```

#### Example 2

```xquery
cts:search(//function, cts:and-query(("repair",
  cts:document-query(("/reports.xml", "/analysis.xml")))))

  => .. relevance ordered sequence of 'function' elements in
     any document that both contains the word "repair" and is
     in either the document "/reports.xml" or in the document
     "/analysis.xml".
```

---

## cts:document-query-uris

Returns the URIs used to construct the specified query.

### Signature

```xquery
cts:document-query-uris(
  $query as cts:document-query
) as xs:string*
```

### Parameters

**`$query`**
A query.

### Returns

`xs:string*`

### Examples

```xquery
cts:document-query-uris($query)
  => ("/reports.xml", "/analysis.xml")
```

---

## cts:document-root-query

Returns a query matching documents with a given root element.

### Signature

```xquery
cts:document-root-query(
  $root as xs:QName
) as cts:document-root-query
```

### Parameters

**`$root`**
The root QName to query.

### Returns

`cts:document-root-query`

### Examples

```xquery
cts:document-root-query(xs:QName("root"))
  => Match documents with root element 'root'.
```

---

## cts:document-root-query-root

Returns the QName used to construct the specified query.

### Signature

```xquery
cts:document-root-query-root(
  $query as cts:document-root-query
) as xs:QName
```

### Parameters

**`$query`**
A query.

### Returns

`xs:QName`

### Examples

```xquery
cts:document-root-query-root(cts:document-root-query("ROOT"))
  => "ROOT""
```

---

## cts:element-attribute-pair-geospatial-query

Returns a query matching elements by name which has
  specific attributes representing latitude and longitude values for
  a point contained within the given geographic box, circle, or polygon,
  or equal to the given point. Points that lie
  between the southern boundary and the northern boundary of a box,
  travelling northwards,
  and between the western boundary and the eastern boundary of the box,
  travelling eastwards, will match.
  Points contained within the given radius of the center point of a circle will
  match, using the curved distance on the surface of the Earth.
  Points contained within the given polygon will match, using great circle arcs
  over a spherical model of the Earth as edges.  An error may result
  if the polygon is malformed in some way.
  Points equal to the a given point will match, taking into account the fact
  that longitudes converge at the poles.
  Using the geospatial query constructors requires a valid geospatial
  license key; without a valid license key, searches that include
  geospatial queries will throw an exception.

### Signature

```xquery
cts:element-attribute-pair-geospatial-query(
  $element-name as xs:QName*,
  $latitude-attribute-names as xs:QName*,
  $longitude-attribute-names as xs:QName*,
  $regions as cts:region*,
  $options as xs:string*?,
  $weight as xs:double??
) as cts:element-attribute-pair-geospatial-query
```

### Parameters

**`$element-name`**
One or more parent element QNames to match.
    When multiple QNames are specified,
    the query matches if any QName matches.

**`$latitude-attribute-names`**
One or more latitude attribute QNames to match.
    When multiple QNames are specified, the query matches
    if any QName matches; however, only the first matching latitude
    attribute in any point instance will be checked.

**`$longitude-attribute-names`**
One or more longitude attribute QNames to match.
    When multiple QNames are specified, the query matches
    if any QName matches; however, only the first matching longitude
    attribute in any point instance will be checked.

**`$regions`**
One or more geographic boxes, circles, polygons, or points. Where
    multiple regions
    are specified, the query matches if any region matches.

**`$options`** *(optional)*
Options to this query.  The default is ().
    Options include:
      
        
        "coordinate-system=string"
        Use the given coordinate system. Valid values are:
          
          wgs84The WGS84 coordinate system with degrees as the angular unit.
          wgs84/radiansThe WGS84 coordinate system with radians as the angular unit.
          wgs84/doubleThe WGS84 coordinate system at double precision with degrees as the angular unit.
          wgs84/radians/doubleThe WGS84 coordinate system at double precision with radians as the angular unit.
          etrs89The ETRS89 coordinate system.
          etrs89/doubleThe ETRS89 coordinate system at double precision.
          rawThe raw (unmapped) coordinate system.
          raw/doubleThe raw coordinate system at double precision.
          
          
          "precision=value"
          Use the coordinate system at the given precision. Allowed values:
          float and double.
        "units=value"
        Measure distance and the radii of circles in the specified units.
         Allowed values: miles (default), km,
         feet, meters.
        "boundaries-included"
        Points on boxes', circles', and polygons' boundaries are counted
        as matching.  This is the default.
        "boundaries-excluded"
        Points on boxes', circles', and polygons' boundaries are not
    counted as matching.
        "boundaries-latitude-excluded"
        Points on boxes' latitude boundaries are not counted as
    matching.
        "boundaries-longitude-excluded"
        Points on boxes' longitude boundaries are not counted as
    matching.
        "boundaries-south-excluded"
        Points on the boxes' southern boundaries are not counted as
    matching.
        "boundaries-west-excluded"
        Points on the boxes' western boundaries are not counted as
    matching.
        "boundaries-north-excluded"
        Points on the boxes' northern boundaries are not counted as
    matching.
        "boundaries-east-excluded"
        Points on the boxes' eastern boundaries are not counted as
    matching.
        "boundaries-circle-excluded"
        Points on circles' boundary are not counted as matching.
        "boundaries-endpoints-excluded"
        Points on linestrings' boundary (the endpoints) are not counted as matching.
        "cached"
        Cache the results of this query in the list cache.
        "uncached"
        Do not cache the results of this query in the list cache.
        "score-function=function"
        Use the selected scoring function. The score function may be:
          
          linearUse a linear function of the difference between the
          specified query value and the matching value in the index to calculate
          a score for this range query.
          reciprocalUse a reciprocal function of the difference
          between the specified query value and the matching value in the
          index to calculate a score for this range query.
          zeroThis range query does not contribute to the
          score. This is the default.
          
        
        "slope-factor=number"
        Apply the given number as a scaling factor to the slope of the
        scoring function. The default is 1.0.
        "synonym"
        Specifies that all of the terms in the $regions parameter are
        considered synonyms for scoring purposes.  The result is that
        occurrences of more than one of the synonyms are scored as if
        there are more occurrence of the same term (as opposed to
        having a separate term that contributes to score).

**`$weight`** *(optional)*
A weight for this query.  The default is 1.0.

### Returns

`cts:element-attribute-pair-geospatial-query`

### Usage Notes

The point value is expressed as the numerical values in the
textual content of the named attributes.

      The value of the precision option takes precedence over
 that implied by the governing coordinate system name, including the
 value of the coordinate-system option. For example, if the
 governing coordinate system is "wgs84/double" and the precision
 option is "float", then the query uses single precision.

      The point values and the boundary specifications are given in degrees
relative to the WGS84 coordinate system.  Southern latitudes and Western
longitudes take negative values.  Longitudes will be wrapped to the range
(-180,+180) and latitudes will be clipped to the range (-90,+90).

      If the northern boundary of a box is south of the southern boundary,
no points will
match. However, longitudes wrap around the globe, so that if the western
boundary is east of the eastern boundary (that is, if the value of 'w' is
greater than the value of 'e'), then the box crosses the anti-meridian.

      Special handling occurs at the poles, as all longitudes exist at latitudes
+90 and -90.

      If neither "cached" nor "uncached" is present, it specifies "cached".
      "score-function=linear" means that values that are further away from
  the bounds will score higher. "score-function=reciprocal" means that values
  that are closer to the bounds will score higher. The functions are scaled
  appropriately for different types, so that in general the default slope factor
  will provide useful results. Using a slope factor greater than 1 gives
  distinct scores over a smaller range of values, and produces generally
  higher scores.  Using a slope factor less than 1 gives distinct scores
  over a wider range of values, and produces generally lower scores.

### Examples

```xquery
(: create a document with test data :)
xdmp:document-insert("/points.xml",
<root>
  <item><point lat="10.5" long="30.0"/></item>
  <item><point lat="15.35" long="35.34"/></item>
  <item><point lat="5.11" long="40.55"/></item>
</root> );

cts:search(doc("/points.xml")//item,
  cts:element-attribute-pair-geospatial-query(xs:QName("point"),
    xs:QName("lat"), xs:QName("long"), cts:box(10.0, 35.0, 20.0, 40.0)));
(:
  returns the following node:
  <item><point lat="15.35" long="35.34"/></item>
:)

cts:search(doc("/points.xml")//item,
  cts:element-attribute-pair-geospatial-query(xs:QName("point"),
    xs:QName("lat"), xs:QName("long"), cts:box(10.0, 40.0, 20.0, 35.0)));
(:
  returns the following nodes (wrapping around the Earth):
  <item><point lat="10.5" long="30.0"/></item>
:)

cts:search(doc("/points.xml")//item,
  cts:element-attribute-pair-geospatial-query(xs:QName("point"),
    xs:QName("lat"), xs:QName("long"), cts:box(20.0, 35.0, 10.0, 40.0)))
(:
  throws an error (latitudes do not wrap)
:)
```

---

## cts:element-attribute-pair-geospatial-query-element-name

Returns the QNames used to construct the specified query.

### Signature

```xquery
cts:element-attribute-pair-geospatial-query-element-name(
  $query as cts:element-attribute-pair-geospatial-query
) as xs:QName*
```

### Parameters

**`$query`**
A query.

### Returns

`xs:QName*`

### Examples

```xquery
let $query := cts:element-attribute-pair-geospatial-query(xs:QName("point"),
     xs:QName("lat"), xs:QName("long"), cts:box(10.1, 10.2, 20.1, 20.2))
return cts:element-attribute-pair-geospatial-query-element-name($query)

=> "point" (as an xs:QName)
```

---

## cts:element-attribute-pair-geospatial-query-latitude-name

Returns the QNames used to construct the specified query.

### Signature

```xquery
cts:element-attribute-pair-geospatial-query-latitude-name(
  $query as cts:element-attribute-pair-geospatial-query
) as xs:QName*
```

### Parameters

**`$query`**
A query.

### Returns

`xs:QName*`

### Examples

```xquery
let $query := cts:element-attribute-pair-geospatial-query(xs:QName("point"),
     xs:QName("lat"), xs:QName("long"), cts:box(10.1, 10.2, 20.1, 20.2))
return cts:element-attribute-pair-geospatial-query-latitude-name($query)

=> "lat" (as an xs:QName)
```

---

## cts:element-attribute-pair-geospatial-query-longitude-name

Returns the QNames used to construct the specified query.

### Signature

```xquery
cts:element-attribute-pair-geospatial-query-longitude-name(
  $query as cts:element-attribute-pair-geospatial-query
) as xs:QName*
```

### Parameters

**`$query`**
A query.

### Returns

`xs:QName*`

### Examples

```xquery
let $query := cts:element-attribute-pair-geospatial-query(xs:QName("point"),
     xs:QName("lat"), xs:QName("long"), cts:box(10.1, 10.2, 20.1, 20.2))
return cts:element-attribute-pair-geospatial-query-longitude-name($query)

=> "long" (as an xs:QName)
```

---

## cts:element-attribute-pair-geospatial-query-options

Returns the options for the specified query.

### Signature

```xquery
cts:element-attribute-pair-geospatial-query-options(
  $query as cts:element-attribute-pair-geospatial-query
) as xs:string*
```

### Parameters

**`$query`**
A query.

### Returns

`xs:string*`

### Examples

```xquery
let $query := cts:element-attribute-pair-geospatial-query(xs:QName("point"),
     xs:QName("lat"), xs:QName("long"), cts:box(10.1, 10.2, 20.1, 20.2))
return cts:element-attribute-pair-geospatial-query-options($query)

=> coordinate-system=wgs84
```

---

## cts:element-attribute-pair-geospatial-query-region

Returns the geographical regions with which the specified query was constructed.

### Signature

```xquery
cts:element-attribute-pair-geospatial-query-region(
  $query as cts:element-attribute-pair-geospatial-query
) as cts:region*
```

### Parameters

**`$query`**
A query.

### Returns

`cts:region*`

### Examples

```xquery
let $query := cts:element-attribute-pair-geospatial-query(xs:QName("point"),
     xs:QName("lat"), xs:QName("long"), cts:box(10.1, 10.2, 20.1, 20.2))
return cts:element-attribute-pair-geospatial-query-region($query)

=> cts:box("[10.1, 10.2, 20.1, 20.2]")
```

---

## cts:element-attribute-pair-geospatial-query-weight

Returns the weight with which the specified query was constructed.

### Signature

```xquery
cts:element-attribute-pair-geospatial-query-weight(
  $query as cts:element-attribute-pair-geospatial-query
) as xs:double
```

### Parameters

**`$query`**
A query.

### Returns

`xs:double`

### Examples

```xquery
let $query := cts:element-attribute-pair-geospatial-query(xs:QName("point"),
     xs:QName("lat"), xs:QName("long"), cts:box(10.1, 10.2, 20.1, 20.2))
return cts:element-attribute-pair-geospatial-query-weight($query)

=> 1
```

---

## cts:element-attribute-range-query

Constructs a query that matches element-attributes by name with a
  range-index entry equal to a given value. An element attribute range
  index on the specified QName(s) must exist when you use this query
  in a search; if no such range index exists, the search throws an exception.

### Signature

```xquery
cts:element-attribute-range-query(
  $element-name as xs:QName*,
  $attribute-name as xs:QName*,
  $operator as xs:string,
  $value as xs:anyAtomicType*,
  $options as xs:string*?,
  $weight as xs:double??
) as cts:element-attribute-range-query
```

### Parameters

**`$element-name`**
One or more element QNames to match.
    When multiple QNames are specified,
    the query matches if any QName matches.

**`$attribute-name`**
One or more attribute QNames to match.
    When multiple QNames are specified,
    the query matches if any QName matches.

**`$operator`**
A comparison operator.
    
      Operators include:
      
        "<"
        Match range index values less than $value.
        "<="
        Match range index values less than or equal to $value.
        ">"
        Match range index values greater than $value.
        ">="
        Match range index values greater than or equal to $value.
        "="
        Match range index values equal to $value.
        "!="
        Match range index values not equal to $value.

**`$value`**
Some values to match.
    When multiple values are specified,
    the query matches if any value matches.

**`$options`** *(optional)*
Options to this query.  The default is ().
    
      Options include:
      
        "collation=URI"
        Use the range index with the collation specified by
        URI.  If not specified, then the default collation
        from the query is used. If a range index with the specified
        collation does not exist, an error is thrown.
        "cached"
        Cache the results of this query in the list cache.
        "uncached"
        Do not cache the results of this query in the list cache.
        "cached-incremental"
        When querying on a short date or dateTime range, break the
        query into sub-queries on smaller ranges, and then cache the
        results of each.  See the Usage Notes for details.
        "min-occurs=number"
        Specifies the minimum number of occurrences required. If
        fewer that this number of words occur, the fragment does not match.
        The default is 1.
        "max-occurs=number"
        Specifies the maximum number of occurrences required.  If
        more than this number of words occur, the fragment does not match.
        The default is unbounded.
        "score-function=function"
        Use the selected scoring function. The score function may be:
          
          linearUse a linear function of the difference between the
          specified query value and the matching value in the index to calculate
          a score for this range query.
          reciprocalUse a reciprocal function of the difference
          between the specified query value and the matching value in the
          index to calculate a score for this range query.
          zeroThis range query does not contribute to the
          score. This is the default.
          
        
        "slope-factor=number"
        Apply the given number as a scaling factor to the slope of the
        scoring function. The default is 1.0.
        "synonym"
        Specifies that all of the terms in the $value parameter are
        considered synonyms for scoring purposes.  The result is that
        occurrences of more than one of the synonyms are scored as if
        there are more occurrences of the same term (as opposed to
        having a separate term that contributes to score).

**`$weight`** *(optional)*
A weight for this query.  The default is 1.0.

### Returns

`cts:element-attribute-range-query`

### Usage Notes

To constrain on a range of values, combine multiple element attribute
  range queries together using
  cts:and-query
   or another
  composable query constructor.
      If neither "cached" nor "uncached" is present, it specifies "cached".
      The "cached-incremental" option can improve performance if you
   repeatedly perform range queries on date or dateTime values over a
   short range that does not vary widely over short period of time. To
   benefit, the operator should remain the same "direction" (<,<=, or >,>=) 
   across calls, the bounding date or dateTime changes slightly across calls,
   and the query runs very frequently (multiple times per minute).
   Note that using this options creates significantly more cached queries
   than the "cached" option.
  
      The "cached-incremental" option has the following restrictions and
   interactions: The "min-occurs" and "max-occurs" options will be ignored
   if you use "cached-incremental" in unfiltered search. You can only use
   "score-function=zero" with "cached-incremental". The "cached-incremental"
   option behaves like "cached" if you are not querying date or dateTime values.
  
      
    Negative "min-occurs" or "max-occurs" values will be treated as 0 and
    non-integral values will be rounded down.  An error will be raised if
    the "min-occurs" value is greater than the "max-occurs" value.
  
      "score-function=linear" means that values that are further away from
  the bounds will score higher. "score-function=reciprocal" means that values
  that are closer to the bounds will score higher. The functions are scaled
  appropriately for different types, so that in general the default slope factor
  will provide useful results. Using a slope factor greater than 1 gives distinct
  scores over a smaller range of values, and produces generally higher scores.
  Using a slope factor less than 1 gives distinct scores over a wider range of
  values, and produces generally lower scores.
  
      For queries against a dateTime index, when $value is an xs:dayTimeDuration
  or xs:yearMonthDuration, the query is executed as an age query. $value is
  subtracted from fn:current-dateTime() to create an xs:dateTime used in the query.
  If there is more than one item in $value, they must all be the same type.

### Examples

```xquery
(: create a document with test data :)
xdmp:document-insert("/attributes.xml",
<root>
  <entry sku="100">
    <product>apple</product>
  </entry>
  <entry sku="200">
    <product>orange</product>
  </entry>
  <entry sku="1000">
    <product>electric car</product>
  </entry>
</root>) ;

(:
   requires an attribute (range) index of
   type xs:int on the "sku" attribute of
   the "entry" element
:)
cts:search(doc("/attributes.xml")/root/entry,
  cts:element-attribute-range-query(
      xs:QName("entry"), xs:QName("sku"), ">=",
      500))
(:
  returns the following node:
  <entry sku="1000">
    <product>electric car</product>
  </entry>
:)
```

---

## cts:element-attribute-range-query-attribute-name

Returns the QNames used to construct the specified query.

### Signature

```xquery
cts:element-attribute-range-query-attribute-name(
  $query as cts:element-attribute-range-query
) as xs:QName*
```

### Parameters

**`$query`**
A query.

### Returns

`xs:QName*`

### Examples

```xquery
let $query := cts:element-attribute-range-query(
              xs:QName("function"),
              xs:QName("name"), ">",
              "MarkLogic Corporation")
return cts:element-attribute-range-query-attribute-name($query)

  => xs:QName("name")
```

---

## cts:element-attribute-range-query-element-name

Returns the QNames used to construct the specified query.

### Signature

```xquery
cts:element-attribute-range-query-element-name(
  $query as cts:element-attribute-range-query
) as xs:QName*
```

### Parameters

**`$query`**
A query.

### Returns

`xs:QName*`

### Examples

```xquery
let $query := cts:element-attribute-range-query(
              xs:QName("function"),
              xs:QName("name"), ">",
              "MarkLogic Corporation")
return cts:element-attribute-range-query-element-name($query)

  => xs:QName("function")
```

---

## cts:element-attribute-range-query-operator

Returns the operator used to construct the specified query.

### Signature

```xquery
cts:element-attribute-range-query-operator(
  $query as cts:element-attribute-range-query
) as xs:string
```

### Parameters

**`$query`**
A query.

### Returns

`xs:string`

### Examples

```xquery
let $query := cts:element-attribute-range-query(
              xs:QName("function"),
              xs:QName("name"), ">",
              "MarkLogic Corporation")
return cts:element-attribute-range-query-operator($query)

  => ">"
```

---

## cts:element-attribute-range-query-options

Returns the options for the specified query.

### Signature

```xquery
cts:element-attribute-range-query-options(
  $query as cts:element-attribute-range-query
) as xs:string*
```

### Parameters

**`$query`**
A query.

### Returns

`xs:string*`

### Examples

```xquery
let $query := cts:element-attribute-range-query(
              xs:QName("function"),
              xs:QName("name"), ">",
              "MarkLogic Corporation")
return cts:element-attribute-range-query-options($query)

  => "collation=http://marklogic.com/collation/"
```

---

## cts:element-attribute-range-query-value

Returns the value used to construct the specified query.

### Signature

```xquery
cts:element-attribute-range-query-value(
  $query as cts:element-attribute-range-query
) as xs:anyAtomicType*
```

### Parameters

**`$query`**
A query.

### Returns

`xs:anyAtomicType*`

### Examples

```xquery
let $query := cts:element-attribute-range-query(
              xs:QName("function"),
              xs:QName("name"), ">",
              "MarkLogic Corporation")
return cts:element-attribute-range-query-value($query)

  => MarkLogic Corporation
```

---

## cts:element-attribute-range-query-weight

Returns the weight with which the specified query was constructed.

### Signature

```xquery
cts:element-attribute-range-query-weight(
  $query as cts:element-attribute-range-query
) as xs:double
```

### Parameters

**`$query`**
A query.

### Returns

`xs:double`

### Examples

```xquery
let $query := cts:element-attribute-range-query(
              xs:QName("function"),
              xs:QName("name"), ">",
              "MarkLogic Corporation")
return cts:element-attribute-range-query-weight($query)

  => 1
```

---

## cts:element-attribute-value-query

Returns a query matching elements by name with attributes by name
  with text content equal a given phrase.

### Signature

```xquery
cts:element-attribute-value-query(
  $element-name as xs:QName*,
  $attribute-name as xs:QName*,
  $text as xs:string*,
  $options as xs:string*?,
  $weight as xs:double??
) as cts:element-attribute-value-query
```

### Parameters

**`$element-name`**
One or more element QNames to match.
    When multiple QNames are specified,
    the query matches if any QName matches.

**`$attribute-name`**
One or more attribute QNames to match.
    When multiple QNames are specified,
    the query matches if any QName matches.

**`$text`**
One or more attribute values to match.
    When multiple strings are specified,
    the query matches if any string matches.

**`$options`** *(optional)*
Options to this query.  The default is ().
    
      Options include:
      
        "case-sensitive"
        A case-sensitive query.
        "case-insensitive"
        A case-insensitive query.
        "diacritic-sensitive"
        A diacritic-sensitive query.
        "diacritic-insensitive"
        A diacritic-insensitive query.
        "punctuation-sensitive"
        A punctuation-sensitive query.
        "punctuation-insensitive"
        A punctuation-insensitive query.
        "whitespace-sensitive"
        A whitespace-sensitive query.
        "whitespace-insensitive"
        A whitespace-insensitive query.
        "stemmed"
        A stemmed query.
        "unstemmed"
        An unstemmed query.
        "wildcarded"
        A wildcarded query.
        "unwildcarded"
        An unwildcarded query.
        "exact"
        An exact match query. Shorthand for "case-sensitive",
        "diacritic-sensitive", "punctuation-sensitive",
        "whitespace-sensitive", "unstemmed", and "unwildcarded".
        
        "lang=iso639code"
        Specifies the language of the query. The iso639code
            code portion is case-insensitive, and uses the languages
            specified by
           ISO 639.
            The default is specified in the database configuration.
        "min-occurs=number"
        Specifies the minimum number of occurrences required. If
        fewer that this number of words occur, the fragment does not match.
        The default is 1.
        "max-occurs=number"
        Specifies the maximum number of occurrences required.  If
        more than this number of words occur, the fragment does not match.
        The default is unbounded.
        "synonym"
        Specifies that all of the terms in the $text parameter are
        considered synonyms for scoring purposes.  The result is that
        occurrences of more than one of the synonyms are scored as if
        there are more occurrences of the same term (as opposed to
        having a separate term that contributes to score).

**`$weight`** *(optional)*
A weight for this query.
    Higher weights move search results up in the relevance
    order.  The default is 1.0. The
    weight should be between 64 and -16.
    Weights greater than 64 will have the same effect as a
    weight of 64.
    Weights less than the absolute value of 0.0625 (between -0.0625 and
    0.0625) are rounded to 0, which means that they do not contribute to the
    score.

### Returns

`cts:element-attribute-value-query`

### Usage Notes

If neither "case-sensitive" nor "case-insensitive"
    is present, $text is used to determine case sensitivity.
    If $text contains no uppercase, it specifies "case-insensitive".
    If $text contains uppercase, it specifies "case-sensitive".
  
      
    If neither "diacritic-sensitive" nor "diacritic-insensitive"
    is present, $text is used to determine diacritic sensitivity.
    If $text contains no diacritics, it specifies "diacritic-insensitive".
    If $text contains diacritics, it specifies "diacritic-sensitive".
  
      
    If neither "punctuation-sensitive" nor "punctuation-insensitive"
    is present, $text is used to determine punctuation sensitivity.
    If $text contains no punctuation, it specifies "punctuation-insensitive".
    If $text contains punctuation, it specifies "punctuation-sensitive".
  
      
    If neither "whitespace-sensitive" nor "whitespace-insensitive"
    is present, the query is "whitespace-insensitive".
  
      
    If neither "wildcarded" nor "unwildcarded"
    is present, the database configuration and $text determine wildcarding.
    If the database has any wildcard indexes enabled ("three character
    searches", "two character searches", "one character searches",  or
    "trailing wildcard searches") and if $text contains either of the
    wildcard characters '?' or '*', it specifies "wildcarded".
    Otherwise it specifies "unwildcarded".
  
      
    If neither "stemmed" nor "unstemmed"
    is present, the database configuration determines stemming.
    If the database has "stemmed searches" enabled, it specifies "stemmed".
    Otherwise it specifies "unstemmed".
    If the query is a wildcarded query and also a phrase query
    (contains two or more terms), the wildcard terms in the query
    are unstemmed.
  
      
    When you use the "exact" option, you should also enable
    "fast case sensitive searches" and "fast diacritic sensitive searches"
    in your database configuration.
  
      
    Negative "min-occurs" or "max-occurs" values will be treated as 0 and
    non-integral values will be rounded down.  An error will be raised if
    the "min-occurs" value is greater than the "max-occurs" value.
  
      When multiple element and/or attribute QNames are specified,
  then all possible element/attribute QName combinations are used
  to select the matching values.

### Examples

#### Example 1

```xquery
cts:search(//module,
    cts:element-attribute-value-query(
      xs:QName("function"),
      xs:QName("type"),
      "MarkLogic Corporation"))

  => .. relevance-ordered sequence of 'module' element
  ancestors (or self) of 'function' elements that have
  an attribute 'type' whose value equals 'MarkLogic
  Corporation'.
```

#### Example 2

```xquery
cts:search(//module,
    cts:and-query((
      cts:element-attribute-value-query(
        xs:QName("function"),
        xs:QName("type"),
        "MarkLogic Corporation",
        (), 0.5),
      cts:element-word-query(
        xs:QName("title"),
        "faster"))))

  => .. relevance-ordered sequence of 'module' element
  ancestors (or self) of both:
   (a) 'function' elements with attribute 'type' whose
       value equals the string 'MarkLogic Corporation',
       ignoring embedded punctuation,
   AND
   (b) 'title' elements whose text content contains the
       word 'faster', with the results from (a) given
       weight 0.5, and the results from (b) given default
       weight 1.0.
```

---

## cts:element-attribute-value-query-attribute-name

Returns the attribute QNames used to construct the specified query.

### Signature

```xquery
cts:element-attribute-value-query-attribute-name(
  $query as cts:element-attribute-value-query
) as xs:QName*
```

### Parameters

**`$query`**
A query.

### Returns

`xs:QName*`

### Examples

```xquery
let $query := cts:element-attribute-value-query(
              xs:QName("function"),
              xs:QName("name"),
              "MarkLogic Corporation")
return cts:element-attribute-value-query-attribute-name($query)

  => xs:QName("name")
```

---

## cts:element-attribute-value-query-element-name

Returns the element QNames used to construct the specified query.

### Signature

```xquery
cts:element-attribute-value-query-element-name(
  $query as cts:element-attribute-value-query
) as xs:QName*
```

### Parameters

**`$query`**
A query.

### Returns

`xs:QName*`

### Examples

```xquery
let $query := cts:element-attribute-value-query(
              xs:QName("function"),
              xs:QName("name"),
              "MarkLogic Corporation")
return cts:element-attribute-value-query-element-name($query)

  => xs:QName("function")
```

---

## cts:element-attribute-value-query-options

Returns the options for the specified query.

### Signature

```xquery
cts:element-attribute-value-query-options(
  $query as cts:element-attribute-value-query
) as xs:string*
```

### Parameters

**`$query`**
A query.

### Returns

`xs:string*`

### Examples

```xquery
let $query := cts:element-attribute-value-query(
              xs:QName("function"),
              xs:QName("name"),
              "MarkLogic Corporation")
return cts:element-attribute-value-query-options($query)

  => "lang=en"
```

---

## cts:element-attribute-value-query-text

Returns the text used to construct the specified query.

### Signature

```xquery
cts:element-attribute-value-query-text(
  $query as cts:element-attribute-value-query
) as xs:string*
```

### Parameters

**`$query`**
A query.

### Returns

`xs:string*`

### Examples

```xquery
let $query := cts:element-attribute-value-query(
              xs:QName("function"),
              xs:QName("name"),
              "MarkLogic Corporation")
return cts:element-attribute-value-query-text($query)

  => MarkLogic Corporation
```

---

## cts:element-attribute-value-query-weight

Returns the weight with which the specified query was constructed.

### Signature

```xquery
cts:element-attribute-value-query-weight(
  $query as cts:element-attribute-value-query
) as xs:double
```

### Parameters

**`$query`**
A query.

### Returns

`xs:double`

### Examples

```xquery
let $query := cts:element-attribute-value-query(
              xs:QName("function"),
              xs:QName("name"),
              "MarkLogic Corporation")
return cts:element-attribute-value-query-weight($query)

  => 1
```

---

## cts:element-attribute-word-query

Returns a query matching elements by name
  with attributes by name
  with text content containing a given phrase.

### Signature

```xquery
cts:element-attribute-word-query(
  $element-name as xs:QName*,
  $attribute-name as xs:QName*,
  $text as xs:string*,
  $options as xs:string*?,
  $weight as xs:double??
) as cts:element-attribute-word-query
```

### Parameters

**`$element-name`**
One or more element QNames to match.
    When multiple QNames are specified,
    the query matches if any QName matches.

**`$attribute-name`**
One or more attribute QNames to match.
    When multiple QNames are specified,
    the query matches if any QName matches.

**`$text`**
Some words or phrases to match.
    When multiple strings are specified,
    the query matches if any string matches.

**`$options`** *(optional)*
Options to this query.  The default is ().
    
      Options include:
      
        "case-sensitive"
        A case-sensitive query.
        "case-insensitive"
        A case-insensitive query.
        "diacritic-sensitive"
        A diacritic-sensitive query.
        "diacritic-insensitive"
        A diacritic-insensitive query.
        "punctuation-sensitive"
        A punctuation-sensitive query.
        "punctuation-insensitive"
        A punctuation-insensitive query.
        "whitespace-sensitive"
        A whitespace-sensitive query.
        "whitespace-insensitive"
        A whitespace-insensitive query.
        "stemmed"
        A stemmed query.
        "unstemmed"
        An unstemmed query.
        "wildcarded"
        A wildcarded query.
        "unwildcarded"
        An unwildcarded query.
        "exact"
        An exact match query. Shorthand for "case-sensitive",
        "diacritic-sensitive", "punctuation-sensitive",
        "whitespace-sensitive", "unstemmed", and "unwildcarded".
        
        "lang=iso639code"
        Specifies the language of the query. The iso639code
            code portion is case-insensitive, and uses the languages
            specified by
           ISO 639.
            The default is specified in the database configuration.
        "min-occurs=number"
        Specifies the minimum number of occurrences required. If
        fewer that this number of words occur, the fragment does not match.
        The default is 1.
        "max-occurs=number"
        Specifies the maximum number of occurrences required.  If
        more than this number of words occur, the fragment does not match.
        The default is unbounded.
        "synonym"
        Specifies that all of the terms in the $text parameter are
        considered synonyms for scoring purposes.  The result is that
        occurrences of more than one of the synonyms are scored as if
        there are more occurrences of the same term (as opposed to
        having a separate term that contributes to score). 
        "lexicon-expand=value"
        The value is one of full,
        prefix-postfix, off, or
        heuristic (the default is heuristic).
        An option with a value of lexicon-expand=full
        specifies that wildcards are resolved by expanding the pattern to
        words in a lexicon (if there is one available), and turning into a
        series of cts:word-queries, even if this takes a long
        time to evaluate.
        An option with a value of lexicon-expand=prefix-postfix
        specifies that wildcards are resolved by expanding the pattern to the
        pre- and postfixes of the words in the word lexicon (if there is one),
        and turning the query into a series of character queries, even if it
        takes a long time to evaluate.
        An option with a value of lexicon-expand=off
        specifies that wildcards are only resolved by looking up character
        patterns in the search pattern index, not in the lexicon.
        An option with a value of lexicon-expand=heuristic,
        which is the default, specifies that wildcards are resolved by using
        a series of internal rules, such as estimating the number of lexicon
        entries that need to be scanned, seeing if the estimate crosses
        certain thresholds, and (if appropriate), using another way besides
        lexicon expansion to resolve the query.
        
 *      "lexicon-expansion-limit=number"
        Specifies the limit for lexicon expansion. This puts a restriction
  on the number of lexicon expansions that can be performed. If the limit is
  exceeded, the server may raise an error depending on whether the "limit-check"
  option is set. The default value for this option will be 4096.
        
        "limit-check"
        Specifies that an error will be raised if the lexicon expansion
  exceeds the specified limit.
        "no-limit-check"
        Specifies that error will not be raised if the lexicon expansion
  exceeds the specified limit. The server will try to resolve the wildcard.

**`$weight`** *(optional)*
A weight for this query.
    Higher weights move search results up in the relevance
    order.  The default is 1.0. The
    weight should be between 64 and -16.
    Weights greater than 64 will have the same effect as a
    weight of 64.
    Weights less than the absolute value of 0.0625 (between -0.0625 and
    0.0625) are rounded to 0, which means that they do not contribute to the
    score.

### Returns

`cts:element-attribute-word-query`

### Usage Notes

If neither "case-sensitive" nor "case-insensitive"
    is present, $text is used to determine case sensitivity.
    If $text contains no uppercase, it specifies "case-insensitive".
    If $text contains uppercase, it specifies "case-sensitive".
  
      
    If neither "diacritic-sensitive" nor "diacritic-insensitive"
    is present, $text is used to determine diacritic sensitivity.
    If $text contains no diacritics, it specifies "diacritic-insensitive".
    If $text contains diacritics, it specifies "diacritic-sensitive".
  
      
    If neither "punctuation-sensitive" nor "punctuation-insensitive"
    is present, $text is used to determine punctuation sensitivity.
    If $text contains no punctuation, it specifies "punctuation-insensitive".
    If $text contains punctuation, it specifies "punctuation-sensitive".
  
      
    If neither "whitespace-sensitive" nor "whitespace-insensitive"
    is present, the query is "whitespace-insensitive".
  
      
    If neither "wildcarded" nor "unwildcarded"
    is present, the database configuration and $text determine wildcarding.
    If the database has any wildcard indexes enabled ("three character
    searches", "two character searches", "one character searches",  or
    "trailing wildcard searches") and if $text contains either of the
    wildcard characters '?' or '*', it specifies "wildcarded".
    Otherwise it specifies "unwildcarded".
  
      
    If neither "stemmed" nor "unstemmed"
    is present, the database configuration determines stemming.
    If the database has "stemmed searches" enabled, it specifies "stemmed".
    Otherwise it specifies "unstemmed".
    If the query is a wildcarded query and also a phrase query
    (contains two or more terms), the wildcard terms in the query
    are unstemmed.
  
      
    Negative "min-occurs" or "max-occurs" values will be treated as 0 and
    non-integral values will be rounded down.  An error will be raised if
    the "min-occurs" value is greater than the "max-occurs" value.

### Examples

#### Example 1

```xquery
cts:search(//module,
    cts:element-attribute-word-query(
      xs:QName("function"),
      xs:QName("type"),
      "MarkLogic Corporation"))

  => .. relevance-ordered sequence of 'module' element
  ancestors of 'function' elements that have a 'type'
  attribute whose value contains the phrase
  'MarkLogic Corporation'.
```

#### Example 2

```xquery
cts:search(//module,
    cts:element-attribute-word-query(
      xs:QName("function"),
      xs:QName("type"),
      "MarkLogic Corporation", "case-insensitive"))

  => .. relevance-ordered sequence of 'module' element
  ancestors of 'function' elements that have a 'type'
  attribute whose value contains the phrase
  'MarkLogic Corporation', or any other case-shift,
  like 'MARKLOGIC CorpoRation'.
```

#### Example 3

```xquery
cts:search(//module,
    cts:and-query((
      cts:element-attribute-word-query(
        xs:QName("function"),
        xs:QName("type"),
        "MarkLogic Corporation",
        "punctuation-insensitive", 0.5),
      cts:element-word-query(
        xs:QName("title"),
        "faster"))))

  => .. relevance-ordered sequence of 'module' element
  ancestors of both:
  (a) 'function' elements with 'type' attribute whose value
      contains the phrase 'MarkLogic Corporation',
      ignoring embedded punctuation,
  AND
  (b) 'title' elements whose text content contains the
      term 'faster',
  with the results of the first query given weight 0.5,
  as opposed to the default 1.0 for the second query.
```

---

## cts:element-attribute-word-query-attribute-name

Returns the attribute QNames used to construct the specified query.

### Signature

```xquery
cts:element-attribute-word-query-attribute-name(
  $query as cts:element-attribute-word-query
) as xs:QName*
```

### Parameters

**`$query`**
A query.

### Returns

`xs:QName*`

### Examples

```xquery
let $query := cts:element-attribute-word-query(
              xs:QName("function"),
              xs:QName("name"),
              "MarkLogic Corporation")
return cts:element-attribute-word-query-attribute-name($query)

  => xs:QName("name")
```

---

## cts:element-attribute-word-query-element-name

Returns the element QNames used to construct the specified query.

### Signature

```xquery
cts:element-attribute-word-query-element-name(
  $query as cts:element-attribute-word-query
) as xs:QName*
```

### Parameters

**`$query`**
A query.

### Returns

`xs:QName*`

### Examples

```xquery
let $query := cts:element-attribute-word-query(
              xs:QName("function"),
              xs:QName("name"),
              "MarkLogic Corporation")
return cts:element-attribute-word-query-element-name($query)

  => xs:QName("function")
```

---

## cts:element-attribute-word-query-options

Returns the options for the specified query.

### Signature

```xquery
cts:element-attribute-word-query-options(
  $query as cts:element-attribute-word-query
) as xs:string*
```

### Parameters

**`$query`**
A query.

### Returns

`xs:string*`

### Examples

```xquery
let $query := cts:element-attribute-word-query(
              xs:QName("function"),
              xs:QName("name"),
              "MarkLogic Corporation")
return cts:element-attribute-word-query-options($query)

  => "lang=en"
```

---

## cts:element-attribute-word-query-text

Returns the text used to construct the specified query.

### Signature

```xquery
cts:element-attribute-word-query-text(
  $query as cts:element-attribute-word-query
) as xs:string*
```

### Parameters

**`$query`**
A query.

### Returns

`xs:string*`

### Examples

```xquery
let $query := cts:element-attribute-word-query(
              xs:QName("function"),
              xs:QName("name"),
              "MarkLogic Corporation")
return cts:element-attribute-word-query-text($query)

  => MarkLogic Corporation
```

---

## cts:element-attribute-word-query-weight

Returns the weight with which the specified query was constructed.

### Signature

```xquery
cts:element-attribute-word-query-weight(
  $query as cts:element-attribute-word-query
) as xs:double
```

### Parameters

**`$query`**
A query.

### Returns

`xs:double`

### Examples

```xquery
let $query := cts:element-attribute-word-query(
              xs:QName("function"),
              xs:QName("name"),
              "MarkLogic Corporation")
return cts:element-attribute-word-query-weight($query)

  => 1
```

---

## cts:element-child-geospatial-query

Returns a query matching elements by name which has
  specific element children representing latitude and longitude values for
  a point contained within the given geographic box, circle, or polygon, or
  equal to the given point.  Points that lie
  between the southern boundary and the northern boundary of a box,
  travelling northwards,
  and between the western boundary and the eastern boundary of the box,
  travelling eastwards, will match.
  Points contained within the given radius of the center point of a circle will
  match, using the curved distance on the surface of the Earth.
  Points contained within the given polygon will match, using great circle arcs
  over a spherical model of the Earth as edges.  An error may result
  if the polygon is malformed in some way.
  Points equal to the a given point will match, taking into account the fact
  that longitudes converge at the poles.
  Using the geospatial query constructors requires a valid geospatial
  license key; without a valid license key, searches that include
  geospatial queries will throw an exception.

### Signature

```xquery
cts:element-child-geospatial-query(
  $parent-element-name as xs:QName*,
  $child-element-names as xs:QName*,
  $regions as cts:region*,
  $options as xs:string*?,
  $weight as xs:double??
) as cts:element-child-geospatial-query
```

### Parameters

**`$parent-element-name`**
One or more parent element QNames to match.
    When multiple QNames are specified,
    the query matches if any QName matches.

**`$child-element-names`**
One or more child element QNames to match.
    When multiple QNames are specified, the query matches
    if any QName matches; however, only the first matching latitude
    child in any point instance will be checked.  The element must specify
    both latitude and longitude coordinates.

**`$regions`**
One or more geographic boxes, circles, polygons, or points. Where multiple
    regions are specified, the query matches if any region matches.

**`$options`** *(optional)*
Options to this query.  The default is ().
    Options include:
      
        
        "coordinate-system=string"
        Use the given coordinate system. Valid values are:
          
          wgs84The WGS84 coordinate system with degrees as the angular unit.
          wgs84/radiansThe WGS84 coordinate system with radians as the angular unit.
          wgs84/doubleThe WGS84 coordinate system at double precision with degrees as the angular unit.
          wgs84/radians/doubleThe WGS84 coordinate system at double precision with radians as the angular unit.
          etrs89The ETRS89 coordinate system.
          etrs89/doubleThe ETRS89 coordinate system at double precision.
          rawThe raw (unmapped) coordinate system.
          raw/doubleThe raw coordinate system at double precision.
          
          
          "precision=string"
          Use the coordinate system at the given precision. Allowed values:
          float (default) and double.
        "units=value"
        Measure distance and the radii of circles in the specified units.
         Allowed values: miles (default), km,
         feet, meters.
        "boundaries-included"
        Points on boxes', circles', and polygons' boundaries are counted
         as matching.  This is the default.
        "boundaries-excluded"
        Points on boxes', circles', and polygons' boundaries are not
    counted as matching.
        "boundaries-latitude-excluded"
        Points on boxes' latitude boundaries are not counted as
    matching.
        "boundaries-longitude-excluded"
        Points on boxes' longitude boundaries are not counted as
    matching.
        "boundaries-south-excluded"
        Points on the boxes' southern boundaries are not counted as
    matching.
        "boundaries-west-excluded"
        Points on the boxes' western boundaries are not counted as
    matching.
        "boundaries-north-excluded"
        Points on the boxes' northern boundaries are not counted as
    matching.
        "boundaries-east-excluded"
        Points on the boxes' eastern boundaries are not counted as
    matching.
        "boundaries-circle-excluded"
        Points on circles' boundary are not counted as matching.
        "boundaries-endpoints-excluded"
        Points on linestrings' boundary (the endpoints) are not counted as matching.
        "cached"
        Cache the results of this query in the list cache.
        "uncached"
        Do not cache the results of this query in the list cache.
        "type=long-lat-point"
        Specifies the format for the point in the data as longitude first,
        latitude second.
        "type=point"
        Specifies the format for the point in the data as latitude first,
        longitude second.  This is the default format.
        "score-function=function"
        Use the selected scoring function. The score function may be:
          
          linearUse a linear function of the difference between the
          specified query value and the matching value in the index to calculate
          a score for this range query.
          reciprocalUse a reciprocal function of the difference
          between the specified query value and the matching value in the
          index to calculate a score for this range query.
          zeroThis range query does not contribute to the
          score. This is the default.
          
        
        "slope-factor=number"
        Apply the given number as a scaling factor to the slope of the
        scoring function. The default is 1.0.
        "synonym"
        Specifies that all of the terms in the $regions parameter are
        considered synonyms for scoring purposes.  The result is that
        occurrences of more than one of the synonyms are scored as if
        there are more occurrence of the same term (as opposed to
        having a separate term that contributes to score).

**`$weight`** *(optional)*
A weight for this query.  The default is 1.0.

### Returns

`cts:element-child-geospatial-query`

### Usage Notes

The point value is expressed in the content of the element as a child
of numbers, separated by whitespace and punctuation (excluding decimal points
and sign characters).

      The value of the precision option takes precedence over
 that implied by the governing coordinate system name, including the
 value of the coordinate-system option. For example, if the
 governing coordinate system is "wgs84/double" and the precision
 option is "float", then the query uses single precision.

      Point values and boundary specifications of boxes are given in degrees
relative to the WGS84 coordinate system.  Southern latitudes and Western
longitudes take negative values.  Longitudes will be wrapped to the range
(-180,+180) and latitudes will be clipped to the range (-90,+90).

      If the northern boundary of a box is south of the southern boundary, no
points will  match. However, longitudes wrap around the globe, so that if
the western boundary is east of the eastern boundary,
then the box crosses the anti-meridian.

      Special handling occurs at the poles, as all longitudes exist at latitudes
+90 and -90.

      If neither "cached" nor "uncached" is present, it specifies "cached".
      "score-function=linear" means that values that are further away from
  the bounds will score higher. "score-function=reciprocal" means that values
  that are closer to the bounds will score higher. The functions are scaled
  appropriately for different types, so that in general the default slope factor
  will provide useful results. Using a slope factor greater than 1 gives distinct
  scores over a smaller range of values, and produces generally higher scores.
  Using a slope factor less than 1 gives distinct scores over a wider range of
  values, and produces generally lower scores.

### Examples

```xquery
(: create a document with test data :)
xdmp:document-insert("/points.xml",
<root>
  <item><point><pos>10.5 30.0</pos></point></item>
  <item><point><pos>15.35 35.34</pos></point></item>
  <item><point><pos>5.11 40.55</pos></point></item>
</root> );

cts:search(doc("/points.xml")//item,
  cts:element-child-geospatial-query(xs:QName("point"), xs:QName("pos"),
    cts:box(10.0, 35.0, 20.0, 40.0)));
(:
  returns the following node:
  <item><point><pos>15.35 35.34</pos></point></item>
:)

cts:search(doc("/points.xml")//item,
  cts:element-child-geospatial-query(xs:QName("point"), xs:QName("pos"),
    cts:box(10.0, 40.0, 20.0, 35.0)));
(:
  returns the following nodes (wrapping around the Earth):
  <item><point><pos>10.5 30.0</pos></point></item>
:)

cts:search(doc("/points.xml")//item,
  cts:element-child-geospatial-query(xs:QName("point"), xs:QName("pos"),
    cts:box(20.0, 35.0, 10.0, 40.0)))
(:
  throws an error (latitudes do not wrap)
:)
```

---

## cts:element-child-geospatial-query-child-name

Returns the QNames used to construct the specified query.

### Signature

```xquery
cts:element-child-geospatial-query-child-name(
  $query as cts:element-child-geospatial-query
) as xs:QName*
```

### Parameters

**`$query`**
A query.

### Returns

`xs:QName*`

### Examples

```xquery
let $query := cts:element-child-geospatial-query(
     xs:QName("point"), xs:QName("pos"),
     cts:box(10.1, 10.2, 20.1, 20.2))
return cts:element-child-geospatial-query-child-name($query)

=> "pos" (as an xs:QName)
```

---

## cts:element-child-geospatial-query-element-name

Returns the QNames used to construct the specified query.

### Signature

```xquery
cts:element-child-geospatial-query-element-name(
  $query as cts:element-child-geospatial-query
) as xs:QName*
```

### Parameters

**`$query`**
A query.

### Returns

`xs:QName*`

### Examples

```xquery
let $query := cts:element-child-geospatial-query(
     xs:QName("point"), xs:QName("pos"),
     cts:box(10.1, 10.2, 20.1, 20.2))
return cts:element-child-geospatial-query-element-name($query)

=> "point" (as an xs:QName)
```

---

## cts:element-child-geospatial-query-options

Returns the options for the specified query.

### Signature

```xquery
cts:element-child-geospatial-query-options(
  $query as cts:element-child-geospatial-query
) as xs:string*
```

### Parameters

**`$query`**
A query.

### Returns

`xs:string*`

### Examples

```xquery
let $query := cts:element-child-geospatial-query(
     xs:QName("point"), xs:QName("pos"),
     cts:box(10.1, 10.2, 20.1, 20.2))
return cts:element-child-geospatial-query-options($query)

=> coordinate-system=wgs84
```

---

## cts:element-child-geospatial-query-region

Returns the geographical regions with which the specified query was constructed.

### Signature

```xquery
cts:element-child-geospatial-query-region(
  $query as cts:element-child-geospatial-query
) as cts:region*
```

### Parameters

**`$query`**
A query.

### Returns

`cts:region*`

### Examples

```xquery
let $query := cts:element-child-geospatial-query(
     xs:QName("point"), xs:QName("pos"),
     cts:box(10.1, 10.2, 20.1, 20.2))
return cts:element-child-geospatial-query-region($query)

=> cts:box("[10.1, 10.2, 20.1, 20.2]")
```

---

## cts:element-child-geospatial-query-weight

Returns the weight with which the specified query was constructed.

### Signature

```xquery
cts:element-child-geospatial-query-weight(
  $query as cts:element-child-geospatial-query
) as xs:double
```

### Parameters

**`$query`**
A query.

### Returns

`xs:double`

### Examples

```xquery
let $query := cts:element-child-geospatial-query(
     xs:QName("point"), xs:QName("pos"),
     cts:box(10.1, 10.2, 20.1, 20.2))
return cts:element-child-geospatial-query-weight($query)

=> 1
```

---

## cts:element-geospatial-query

Returns a query matching elements by name whose content
  represents a point contained within the given geographic box, circle, or
  polygon, or equal to the given point. Points that lie
  between the southern boundary and the northern boundary of a box,
  travelling northwards,
  and between the western boundary and the eastern boundary of the box,
  travelling eastwards, will match.
  Points contained within the given radius of the center point of a circle will
  match, using the curved distance on the surface of the Earth.
  Points contained within the given polygon will match, using great circle arcs
  over a spherical model of the Earth as edges.  An error may result
  if the polygon is malformed in some way.
  Points equal to the a given point will match, taking into account the fact
  that longitudes converge at the poles.
  Using the geospatial query constructors requires a valid geospatial
  license key; without a valid license key, searches that include
  geospatial queries will throw an exception.

### Signature

```xquery
cts:element-geospatial-query(
  $element-name as xs:QName*,
  $regions as cts:region*,
  $options as xs:string*?,
  $weight as xs:double??
) as cts:element-geospatial-query
```

### Parameters

**`$element-name`**
One or more element QNames to match.
    When multiple QNames are specified,
    the query matches if any QName matches.

**`$regions`**
One or more geographic boxes, circles, polygons, or points. Where multiple
    regions are specified, the query matches if any region matches.

**`$options`** *(optional)*
Options to this query.  The default is ().
    Options include:
      
        
        "coordinate-system=string"
        Use the given coordinate system. Valid values are:
          
          wgs84The WGS84 coordinate system with degrees as the angular unit.
          wgs84/radiansThe WGS84 coordinate system with radians as the angular unit.
          wgs84/doubleThe WGS84 coordinate system at double precision with degrees as the angular unit.
          wgs84/radians/doubleThe WGS84 coordinate system at double precision with radians as the angular unit.
          etrs89The ETRS89 coordinate system.
          etrs89/doubleThe ETRS89 coordinate system at double precision.
          rawThe raw (unmapped) coordinate system.
          raw/doubleThe raw coordinate system at double precision.
          
          
          "precision=value"
          Use the coordinate system at the given precision. Allowed values:
          float and double.
        "units=value"
        Measure distance and the radii of circles in the specified units.
         Allowed values: miles (default), km,
         feet, meters.
        "boundaries-included"
        Points on boxes', circles', and polygons' boundaries are counted as
         matching.  This is the default.
        "boundaries-excluded"
        Points on boxes', circles', and polygons' boundaries are not
    counted as matching.
        "boundaries-latitude-excluded"
        Points on boxes' latitude boundaries are not counted as
    matching.
        "boundaries-longitude-excluded"
        Points on boxes' longitude boundaries are not counted as
    matching.
        "boundaries-south-excluded"
        Points on the boxes' southern boundaries are not counted as
    matching.
        "boundaries-west-excluded"
        Points on the boxes' western boundaries are not counted as
    matching.
        "boundaries-north-excluded"
        Points on the boxes' northern boundaries are not counted as
    matching.
        "boundaries-east-excluded"
        Points on the boxes' eastern boundaries are not counted as
    matching.
        "boundaries-circle-excluded"
        Points on circles' boundary are not counted as matching.
        "boundaries-endpoints-excluded"
        Points on linestrings' boundary (the endpoints) are not counted as matching.
        "cached"
        Cache the results of this query in the list cache.
        "uncached"
        Do not cache the results of this query in the list cache.
        "type=long-lat-point"
        Specifies the format for the point in the data as longitude first,
        latitude second.
        "type=point"
        Specifies the format for the point in the data as latitude first,
        longitude second.  This is the default format.
        "score-function=function"
        Use the selected scoring function. The score function may be:
          
          linearUse a linear function of the difference between the
          specified query value and the matching value in the index to calculate
          a score for this range query.
          reciprocalUse a reciprocal function of the difference
          between the specified query value and the matching value in the
          index to calculate a score for this range query.
          zeroThis range query does not contribute to the
          score. This is the default.
          
        
        "slope-factor=number"
        Apply the given number as a scaling factor to the slope of the
        scoring function. The default is 1.0.
        "synonym"
        Specifies that all of the terms in the $regions parameter are
        considered synonyms for scoring purposes.  The result is that
        occurrences of more than one of the synonyms are scored as if
        there are more occurrence of the same term (as opposed to
        having a separate term that contributes to score).

**`$weight`** *(optional)*
A weight for this query.  The default is 1.0.

### Returns

`cts:element-geospatial-query`

### Usage Notes

The point value is expressed in the content of the element as a pair
of numbers, separated by whitespace and punctuation (excluding decimal points
and sign characters).

      The value of the precision option takes precedence over
 that implied by the governing coordinate system name, including the
 value of the coordinate-system option. For example, if the
 governing coordinate system is "wgs84/double" and the precision
 option is "float", then the query uses single precision.

      Point and region coordinates are interpreted according to the governing
coordinate system of the query. When using a geographic coordinate system
such as wgs84 or wgs84/double the following also applies:
      
	Southern latitudes and Western longitudes take negative values.
	Longitudes are wrapped to the range (-180,+180).
	Latitudes are clipped to the range (-90,+90).
      
      If the northern boundary of a box is south of the southern boundary, no
points will match. However, longitudes wrap around the globe, so that if
the western boundary is east of the eastern boundary,
then the box crosses the anti-meridian.

      Special handling occurs at the poles, as all longitudes exist at latitudes
+90 and -90.

      If neither "cached" nor "uncached" is present, it specifies "cached".
      "score-function=linear" means that values that are further away from
  the bounds will score higher. "score-function=reciprocal" means that values
  that are closer to the bounds will score higher. The functions are scaled
  appropriately for different types, so that in general the default slope factor
  will provide useful results. Using a slope factor greater than 1 gives distinct
  scores over a smaller range of values, and produces generally higher scores.
  Using a slope factor less than 1 gives distinct scores over a wider range of
  values, and produces generally lower scores.

### Examples

```xquery
(: create a document with test data :)
xdmp:document-insert("/points.xml",
<root>
  <item><point>10.5, 30.0</point></item>
  <item><point>15.35, 35.34</point></item>
  <item><point>5.11, 40.55</point></item>
</root> );

cts:search(doc("/points.xml")//item,
  cts:element-geospatial-query(
    xs:QName("point"), cts:box(10.0, 35.0, 20.0, 40.0)));
(:
  returns the following node:
  <item><point>15.35, 35.34</point></item>
:)

cts:search(doc("/points.xml")//item,
  cts:element-geospatial-query(
    xs:QName("point"), cts:box(10.0, 40.0, 20.0, 35.0)));
(:
  returns the following nodes (wrapping around the Earth):
  <item><point>10.5, 30.0</point></item>
:)

cts:search(doc("/points.xml")//item,
  cts:element-geospatial-query(
    xs:QName("point"), cts:box(20.0, 35.0, 10.0, 40.0)))
(:
  throws an error (latitudes do not wrap)
:)
```

---

## cts:element-geospatial-query-element-name

Returns the QNames used to construct the specified query.

### Signature

```xquery
cts:element-geospatial-query-element-name(
  $query as cts:element-geospatial-query
) as xs:QName*
```

### Parameters

**`$query`**
A query.

### Returns

`xs:QName*`

### Examples

```xquery
let $query := cts:element-geospatial-query(
    xs:QName("point"), cts:box(10.1, 10.2, 20.1, 20.2))
return
cts:element-geospatial-query-element-name($query)

=> "point" (as an xs:QName)
```

---

## cts:element-geospatial-query-options

Returns the options for the specified query.

### Signature

```xquery
cts:element-geospatial-query-options(
  $query as cts:element-geospatial-query
) as xs:string*
```

### Parameters

**`$query`**
A query.

### Returns

`xs:string*`

### Examples

```xquery
let $query := cts:element-geospatial-query(
    xs:QName("point"), cts:box(10.1, 10.2, 20.1, 20.2))
return
cts:element-geospatial-query-options($query)

=> coordinate-system=wgs84
```

---

## cts:element-geospatial-query-region

Returns the geographical regions
  with which the specified query was constructed.

### Signature

```xquery
cts:element-geospatial-query-region(
  $query as cts:element-geospatial-query
) as cts:region*
```

### Parameters

**`$query`**
A query.

### Returns

`cts:region*`

### Examples

```xquery
let $query := cts:element-geospatial-query(
    xs:QName("point"), cts:box(10.1, 10.2, 20.1, 20.2))
return
cts:element-geospatial-query-region($query)

=> cts:box("[10.1, 10.2, 20.1, 20.2]")
```

---

## cts:element-geospatial-query-weight

Returns the weight with which the specified query was constructed.

### Signature

```xquery
cts:element-geospatial-query-weight(
  $query as cts:element-geospatial-query
) as xs:double
```

### Parameters

**`$query`**
A query.

### Returns

`xs:double`

### Examples

```xquery
let $query := cts:element-geospatial-query(
    xs:QName("point"), cts:box(10.1, 10.2, 20.1, 20.2))
return
cts:element-geospatial-query-weight($query)

=> 1
```

---

## cts:element-pair-geospatial-query

Returns a query matching elements by name which has
  specific element children representing latitude and longitude values for
  a point contained within the given geographic box, circle, or polygon, or
  equal to the given point.
  Points that lie
  between the southern boundary and the northern boundary of a box,
  travelling northwards,
  and between the western boundary and the eastern boundary of the box,
  travelling eastwards, will match.
  Points contained within the given radius of the center point of a circle will
  match, using the curved distance on the surface of the Earth.
  Points contained within the given polygon will match, using great circle arcs
  over a spherical model of the Earth as edges.  An error may result
  if the polygon is malformed in some way.
  Points equal to the a given point will match, taking into account the fact
  that longitudes converge at the poles.
  Using the geospatial query constructors requires a valid geospatial
  license key; without a valid license key, searches that include
  geospatial queries will throw an exception.

### Signature

```xquery
cts:element-pair-geospatial-query(
  $element-name as xs:QName*,
  $latitude-element-names as xs:QName*,
  $longitude-element-names as xs:QName*,
  $regions as cts:region*,
  $options as xs:string*?,
  $weight as xs:double??
) as cts:element-pair-geospatial-query
```

### Parameters

**`$element-name`**
One or more parent element QNames to match.
    When multiple QNames are specified,
    the query matches if any QName matches.

**`$latitude-element-names`**
One or more latitude element QNames to match.
    When multiple QNames are specified, the query matches
    if any QName matches; however, only the first matching latitude
    child in any point instance will be checked.

**`$longitude-element-names`**
One or more longitude element QNames to match.
    When multiple QNames are specified, the query matches
    if any QName matches; however, only the first matching longitude
    child in any point instance will be checked.

**`$regions`**
One or more geographic boxes, circles, polygons, or points. Where multiple
    regions are specified, the query matches if any region matches.

**`$options`** *(optional)*
Options to this query.  The default is ().
    Options include:
      
        
        "coordinate-system=string"
        Use the given coordinate system. Valid values are:
          
          wgs84The WGS84 coordinate system with degrees as the angular unit.
          wgs84/radiansThe WGS84 coordinate system with radians as the angular unit.
          wgs84/doubleThe WGS84 coordinate system at double precision with degrees as the angular unit.
          wgs84/radians/doubleThe WGS84 coordinate system at double precision with radians as the angular unit.
          etrs89The ETRS89 coordinate system.
          etrs89/doubleThe ETRS89 coordinate system at double precision.
          rawThe raw (unmapped) coordinate system.
          raw/doubleThe raw coordinate system at double precision.
          
          
          "precision=value"
          Use the coordinate system at the given precision. Allowed values:
          float and double.
        "units=value"
        Measure distance and the radii of circles in the specified units.
         Allowed values: miles (default), km,
         feet, meters.
        "boundaries-included"
        Points on boxes', circles', and polygons' boundaries are counted
        as matching.  This is the default.
        "boundaries-excluded"
        Points on boxes', circles', and polygons' boundaries are not
    counted as matching.
        "boundaries-latitude-excluded"
        Points on boxes' latitude boundaries are not counted as
    matching.
        "boundaries-longitude-excluded"
        Points on boxes' longitude boundaries are not counted as
    matching.
        "boundaries-south-excluded"
        Points on the boxes' southern boundaries are not counted as
    matching.
        "boundaries-west-excluded"
        Points on the boxes' western boundaries are not counted as
    matching.
        "boundaries-north-excluded"
        Points on the boxes' northern boundaries are not counted as
    matching.
        "boundaries-east-excluded"
        Points on the boxes' eastern boundaries are not counted as
    matching.
        "boundaries-circle-excluded"
        Points on circles' boundary are not counted as matching.
        "boundaries-endpoints-excluded"
        Points on linestrings' boundary (the endpoints) are not counted as matching.
        "cached"
        Cache the results of this query in the list cache.
        "uncached"
        Do not cache the results of this query in the list cache.
        "score-function=function"
        Use the selected scoring function. The score function may be:
          
          linearUse a linear function of the difference between the
          specified query value and the matching value in the index to calculate
          a score for this range query.
          reciprocalUse a reciprocal function of the difference
          between the specified query value and the matching value in the
          index to calculate a score for this range query.
          zeroThis range query does not contribute to the
          score. This is the default.
          
        
        "slope-factor=number"
        Apply the given number as a scaling factor to the slope of the
        scoring function. The default is 1.0.
        "synonym"
        Specifies that all of the terms in the $regions parameter are
        considered synonyms for scoring purposes.  The result is that
        occurrences of more than one of the synonyms are scored as if
        there are more occurrence of the same term (as opposed to
        having a separate term that contributes to score).

**`$weight`** *(optional)*
A weight for this query.  The default is 1.0.

### Returns

`cts:element-pair-geospatial-query`

### Usage Notes

The point value is expressed in the content of the latitude and
longitude elements (the latitude value in the latitude element, and the
longitude value in the longitude element).

      The value of the precision option takes precedence over
 that implied by the governing coordinate system name, including the
 value of the coordinate-system option. For example, if the
 governing coordinate system is "wgs84/double" and the precision
 option is "float", then the query uses single precision.

      Point values and boundary specifications of boxes are given in degrees
relative to the WGS84 coordinate system.  Southern latitudes and Western
longitudes take negative values.  Longitudes will be wrapped to the range
(-180,+180) and latitudes will be clipped to the range (-90,+90).

      If the northern boundary of a box is south of the southern boundary, no
points will  match. However, longitudes wrap around the globe, so that if
the western boundary is east of the eastern boundary,
then the box crosses the anti-meridian.

      Special handling occurs at the poles, as all longitudes exist at latitudes
+90 and -90.

      If neither "cached" nor "uncached" is present, it specifies "cached".
      "score-function=linear" means that values that are further away from
  the bounds will score higher. "score-function=reciprocal" means that values
  that are closer to the bounds will score higher. The functions are scaled
  appropriately for different types, so that in general the default slope factor
  will provide useful results. Using a slope factor greater than 1 gives
  distinct scores over a smaller range of values, and produces generally
  higher scores.  Using a slope factor less than 1 gives distinct scores
  over a wider range of values, and produces generally lower scores.

### Examples

```xquery
(: create a document with test data :)
xdmp:document-insert("/points.xml",
<root>
  <item><point><lat>10.5</lat><long>30.0</long></point></item>
  <item><point><lat>15.35</lat><long>35.34</long></point></item>
  <item><point><lat>5.11</lat><long>40.55</long></point></item>
</root> );

cts:search(doc("/points.xml")//item,
  cts:element-pair-geospatial-query(xs:QName("point"),
    xs:QName("lat"), xs:QName("long"), cts:box(10.0, 35.0, 20.0, 40.0)));
(:
  returns the following node:
  <item><point><lat>15.35</lat><long>35.34</long></point></item>
:)

cts:search(doc("/points.xml")//item,
  cts:element-pair-geospatial-query(xs:QName("point"),
    xs:QName("lat"), xs:QName("long"), cts:box(10.0, 40.0, 20.0, 35.0)));
(:
  returns the following nodes (wrapping around the Earth):
  <item><point><lat>10.5</lat><long>30.0</long></point></item>
:)

cts:search(doc("/points.xml")//item,
  cts:element-pair-geospatial-query(xs:QName("point"),
    xs:QName("lat"), xs:QName("long"), cts:box(20.0, 35.0, 10.0, 40.0)))
(:
  throws an error (latitudes do not wrap)
:)
```

---

## cts:element-pair-geospatial-query-element-name

Returns the QNames used to construct the specified query.

### Signature

```xquery
cts:element-pair-geospatial-query-element-name(
  $query as cts:element-pair-geospatial-query
) as xs:QName*
```

### Parameters

**`$query`**
A query.

### Returns

`xs:QName*`

### Examples

```xquery
let $query := cts:element-pair-geospatial-query(xs:QName("point"),
     xs:QName("lat"), xs:QName("long"), cts:box(10.1, 10.2, 20.1, 20.2))
return cts:element-pair-geospatial-query-element-name($query)

=> "point" (as an xs:QName)
```

---

## cts:element-pair-geospatial-query-latitude-name

Returns the QNames used to construct the specified query.

### Signature

```xquery
cts:element-pair-geospatial-query-latitude-name(
  $query as cts:element-pair-geospatial-query
) as xs:QName*
```

### Parameters

**`$query`**
A query.

### Returns

`xs:QName*`

### Examples

```xquery
let $query := cts:element-pair-geospatial-query(xs:QName("point"),
     xs:QName("lat"), xs:QName("long"), cts:box(10.1, 10.2, 20.1, 20.2))
return cts:element-pair-geospatial-query-latitude-name($query)

=> "lat" (as an xs:QName)
```

---

## cts:element-pair-geospatial-query-longitude-name

Returns the QNames used to construct the specified query.

### Signature

```xquery
cts:element-pair-geospatial-query-longitude-name(
  $query as cts:element-pair-geospatial-query
) as xs:QName*
```

### Parameters

**`$query`**
A query.

### Returns

`xs:QName*`

### Examples

```xquery
let $query := cts:element-pair-geospatial-query(xs:QName("point"),
     xs:QName("lat"), xs:QName("long"), cts:box(10.1, 10.2, 20.1, 20.2))
return cts:element-pair-geospatial-query-longitude-name($query)

=> "long" (as an xs:QName)
```

---

## cts:element-pair-geospatial-query-options

Returns the options for the specified query.

### Signature

```xquery
cts:element-pair-geospatial-query-options(
  $query as cts:element-pair-geospatial-query
) as xs:string*
```

### Parameters

**`$query`**
A query.

### Returns

`xs:string*`

### Examples

```xquery
let $query := cts:element-pair-geospatial-query(xs:QName("point"),
     xs:QName("lat"), xs:QName("long"), cts:box(10.1, 10.2, 20.1, 20.2))
return cts:element-pair-geospatial-query-options($query)

=> coordinate-system=wgs84
```

---

## cts:element-pair-geospatial-query-region

Returns the geographical regions with which the specified query was
  constructed.

### Signature

```xquery
cts:element-pair-geospatial-query-region(
  $query as cts:element-pair-geospatial-query
) as cts:region*
```

### Parameters

**`$query`**
A query.

### Returns

`cts:region*`

### Examples

```xquery
let $query := cts:element-pair-geospatial-query(xs:QName("point"),
     xs:QName("lat"), xs:QName("long"), cts:box(10.1, 10.2, 20.1, 20.2))
return cts:element-pair-geospatial-query-region($query)

=> cts:box("[10.1, 10.2, 20.1, 20.2]")
```

---

## cts:element-pair-geospatial-query-weight

Returns the weight with which the specified query was constructed.

### Signature

```xquery
cts:element-pair-geospatial-query-weight(
  $query as cts:element-pair-geospatial-query
) as xs:double
```

### Parameters

**`$query`**
A query.

### Returns

`xs:double`

### Examples

```xquery
let $query := cts:element-pair-geospatial-query(xs:QName("point"),
     xs:QName("lat"), xs:QName("long"), cts:box(10.1, 10.2, 20.1, 20.2))
return cts:element-pair-geospatial-query-weight($query)

=> 1
```

---

## cts:element-query

Constructs a query that matches elements by name with the content
  constrained by the query given in the second parameter.
  Searches for matches in the specified element and all of its descendants.
  If the query specified in the second parameter includes any element
  attribute sub-queries, it will search attributes on the specified element
  and attributes on any descendant elements. See the
  second example
   below).

### Signature

```xquery
cts:element-query(
  $element-name as xs:QName*,
  $query as cts:query
) as cts:element-query
```

### Parameters

**`$element-name`**
One or more element QNames to match.
    When multiple QNames are specified,
    the query matches if any QName matches.

**`$query`**
A query for the element to match.  If a string
   is entered, the string is treated as a cts:word-query of the
   specified string.

### Returns

`cts:element-query`

### Usage Notes

Enabling both the word position and element position indexes
  ("word position" and "element word position" in the database configuration
  screen of the Admin Interface) will speed up query performance for many
  queries that use 
  cts:element-query. The position indexes
  enable MarkLogic Server to eliminate many false-positive results, which can
  reduce disk I/O and processing, thereby speeding the performance of many
  queries.  The amount of benefit will vary depending on your data.
      You can query for the existence of an element by specifying an empty
  cts:and-query
   as
  the second parameter. For example, the following will match any instance
  of the specified element:
      
  
  cts:element-query(xs:QName("my-element"),
    cts:and-query( () ))

### Examples

#### Example 1

```xquery
cts:search(//module,
    cts:element-query(
      xs:QName("function"),
      "MarkLogic Corporation"))

  => .. relevance-ordered sequence of 'module' elements
  ancestors (or self) of elements with QName 'function'
  and text content containing the phrase 'MarkLogic
  Corporation'.
```

#### Example 2

```xquery
let $x := <a attr="something">hello</a>
return
cts:contains($x, cts:element-query(xs:QName("a"),
   cts:and-query((
     cts:element-attribute-word-query(xs:QName("a"),
         xs:QName("attr"), "something"),
     cts:word-query("hello")))))
(: returns true :)
```

---

## cts:element-query-element-name

Returns the QNames used to construct the specified query.

### Signature

```xquery
cts:element-query-element-name(
  $query as cts:element-query
) as xs:QName*
```

### Parameters

**`$query`**
A query.

### Returns

`xs:QName*`

### Examples

```xquery
let $query := cts:element-query(
              xs:QName("function"),
              "MarkLogic Corporation")
return cts:element-query-element-name($query)

  => xs:QName("function")
```

---

## cts:element-query-query

Returns the query used to construct the element query.

### Signature

```xquery
cts:element-query-query(
  $query as cts:element-query
) as cts:query
```

### Parameters

**`$query`**
A query.

### Returns

`cts:query`

### Examples

```xquery
let $query := cts:element-query(xs:QName("help"),
                 cts:word-query("wanted"))
return cts:element-query-query($query)

  => cts:word-query("wanted", (), 1)
```

---

## cts:element-range-query

Constructs a query that matches elements by name with range index
  entry equal to a given value. Searches that use an element range query
  require an element range index on the specified QName(s);
  if no such range index exists, then an exception is thrown.

### Signature

```xquery
cts:element-range-query(
  $element-name as xs:QName*,
  $operator as xs:string,
  $value as xs:anyAtomicType*,
  $options as xs:string*?,
  $weight as xs:double??
) as cts:element-range-query
```

### Parameters

**`$element-name`**
One or more element QNames to match.
    When multiple QNames are specified,
    the query matches if any QName matches.

**`$operator`**
A comparison operator.
    
      Operators include:
      
        "<"
        Match range index values less than $value.
        "<="
        Match range index values less than or equal to $value.
        ">"
        Match range index values greater than $value.
        ">="
        Match range index values greater than or equal to $value.
        "="
        Match range index values equal to $value.
        "!="
        Match range index values not equal to $value.

**`$value`**
One or more element values to match.
    When multiple values are specified,
    the query matches if any value matches.

**`$options`** *(optional)*
Options to this query.  The default is ().
    
      Options include:
      
        "collation=URI"
        Use the range index with the collation specified by
        URI.  If not specified, then the default collation
        from the query is used. If a range index with the specified
        collation does not exist, an error is thrown.
        "cached"
        Cache the results of this query in the list cache.
        "uncached"
        Do not cache the results of this query in the list cache.
        "cached-incremental"
        When querying on a short date or dateTime range, break the
        query into sub-queries on smaller ranges, and then cache the
        results of each.  See the Usage Notes for details.
        "min-occurs=number"
        Specifies the minimum number of occurrences required. If
        fewer that this number of words occur, the fragment does not match.
        The default is 1.
        "max-occurs=number"
        Specifies the maximum number of occurrences required.  If
        more than this number of words occur, the fragment does not match.
        The default is unbounded.
        "score-function=function"
        Use the selected scoring function. The score function may be:
          
          linearUse a linear function of the difference between the
          specified query value and the matching value in the index to calculate
          a score for this range query.
          reciprocalUse a reciprocal function of the difference
          between the specified query value and the matching value in the
          index to calculate a score for this range query.
          zeroThis range query does not contribute to the
          score. This is the default.
          
        
        "slope-factor=number"
        Apply the given number as a scaling factor to the slope of the
        scoring function. The default is 1.0.
        "synonym"
        Specifies that all of the terms in the $value parameter are
        considered synonyms for scoring purposes.  The result is that
        occurrences of more than one of the synonyms are scored as if
        there are more occurrences of the same term (as opposed to
        having a separate term that contributes to score).

**`$weight`** *(optional)*
A weight for this query.  The default is 1.0.

### Returns

`cts:element-range-query`

### Usage Notes

To constrain on a range of values, combine multiple element range
  queries together using cts:and-query
   or any of the
  composable query constructors, as in the last part of the example below.
      If neither "cached" nor "uncached" is present, it specifies "cached".
      The "cached-incremental" option can improve performance if you
   repeatedly perform range queries on date or dateTime values over a
   short range that does not vary widely over short period of time. To
   benefit, the operator should remain the same "direction" (<,<=, or >,>=) 
   across calls, the bounding date or dateTime changes slightly across calls,
   and the query runs very frequently (multiple times per minute).
   Note that using this options creates significantly more cached queries
   than the "cached" option.
  
      The "cached-incremental" option has the following restrictions and
   interactions: The "min-occurs" and "max-occurs" options will be ignored
   if you use "cached-incremental" in unfiltered search. You can only use
   "score-function=zero" with "cached-incremental". The "cached-incremental"
   option behaves like "cached" if you are not querying date or dateTime values.
  
      
    Negative "min-occurs" or "max-occurs" values will be treated as 0 and
    non-integral values will be rounded down.  An error will be raised if
    the "min-occurs" value is greater than the "max-occurs" value.
  
      "score-function=linear" means that values that are further away from
  the bounds will score higher. "score-function=reciprocal" means that values
  that are closer to the bounds will score higher. The functions are scaled
  appropriately for different types, so that in general the default slope factor
  will provide useful results. Using a slope factor greater than 1 gives distinct
  scores over a smaller range of values, and produces generally higher scores.
  Using a slope factor less than 1 gives distinct scores over a wider range of
  values, and produces generally lower scores.
  
      For queries against a dateTime index, when $value is an xs:dayTimeDuration
  or xs:yearMonthDuration, the query is executed as an age query. $value is
  subtracted from fn:current-dateTime() to create an xs:dateTime used in the query.
  If there is more than one item in $value, they must all be the same type.

### Examples

```xquery
(: create a document with test data :)
xdmp:document-insert("/dates.xml",
<root>
  <entry>
    <date>2007-01-01</date>
    <info>Some information.</info>
  </entry>
  <entry>
    <date>2006-06-23</date>
    <info>Some other information.</info>
  </entry>
  <entry>
    <date>1971-12-23</date>
    <info>Some different information.</info>
  </entry>
</root>);

(:
   requires an element (range) index of
   type xs:date on "date"
:)
cts:search(doc("/dates.xml")/root/entry,
  cts:element-range-query(xs:QName("date"), "<=",
      xs:date("2000-01-01")))
(:
  returns the following node:
  <entry>
    <date>1971-12-23</date>
    <info>Some different information.</info>
  </entry>
:)
;
(:
   requires an element (range) index of
   type xs:date on "date"
:)
cts:search(doc("/dates.xml")/root/entry,
  cts:and-query((
   cts:element-range-query(xs:QName("date"), ">",
      xs:date("2006-01-01")),
   cts:element-range-query(xs:QName("date"), "<",
      xs:date("2008-01-01")))))
(:
  returns the following 2 nodes:
  <entry>
    <date>2007-01-01</date>
    <info>Some information.</info>
  </entry>

  <entry>
    <date>2006-06-23</date>
    <info>Some other information.</info>
  </entry>
:)
```

---

## cts:element-range-query-element-name

Returns the QNames used to construct the specified query.

### Signature

```xquery
cts:element-range-query-element-name(
  $query as cts:element-range-query
) as xs:QName*
```

### Parameters

**`$query`**
A query.

### Returns

`xs:QName*`

### Examples

```xquery
let $query := cts:element-range-query(xs:QName("date"), "<=",
      xs:date("2000-01-01"))
return
cts:element-range-query-element-name($query)
  => "date" (as an xs:QName)
```

---

## cts:element-range-query-operator

Returns the operator used to construct the specified query.

### Signature

```xquery
cts:element-range-query-operator(
  $query as cts:element-range-query
) as xs:string
```

### Parameters

**`$query`**
A query.

### Returns

`xs:string`

### Examples

```xquery
let $query := cts:element-range-query(xs:QName("date"), "<=",
      xs:date("2000-01-01"))
return
cts:element-range-query-operator($query)
  =>
     <=
```

---

## cts:element-range-query-options

Returns the options for the specified query.

### Signature

```xquery
cts:element-range-query-options(
  $query as cts:element-range-query
) as xs:string*
```

### Parameters

**`$query`**
A query.

### Returns

`xs:string*`

### Examples

```xquery
let $query := cts:element-range-query(xs:QName("date"), "<=",
      xs:date("2000-01-01"))
return
cts:element-range-query-options($query)
  => ()
```

---

## cts:element-range-query-value

Returns the value used to construct the specified query.

### Signature

```xquery
cts:element-range-query-value(
  $query as cts:element-range-query
) as xs:anyAtomicType*
```

### Parameters

**`$query`**
A query.

### Returns

`xs:anyAtomicType*`

### Examples

```xquery
let $query := cts:element-range-query(xs:QName("date"), "<=",
      xs:date("2000-01-01"))
return
cts:element-range-query-value($query)
  =>
     "2000-01-01" (as an xs.date)
```

---

## cts:element-range-query-weight

Returns the weight with which the specified query was constructed.

### Signature

```xquery
cts:element-range-query-weight(
  $query as cts:element-range-query
) as xs:double
```

### Parameters

**`$query`**
A query.

### Returns

`xs:double`

### Examples

```xquery
let $query := cts:element-range-query(xs:QName("date"), "<=",
      xs:date("2000-01-01"))
return
cts:element-range-query-weight($query)
  => 1
```

---

## cts:element-value-query

Returns a query matching elements by name with text content equal a
  given phrase.  cts:element-value-query only matches against
  simple elements (that is, elements that contain only text and have no element
  children).

### Signature

```xquery
cts:element-value-query(
  $element-name as xs:QName*,
  $text as xs:string*?,
  $options as xs:string*?,
  $weight as xs:double??
) as cts:element-value-query
```

### Parameters

**`$element-name`**
One or more element QNames to match.
    When multiple QNames are specified,
    the query matches if any QName matches.

**`$text`** *(optional)*
One or more element values to match.
    When multiple strings are specified,
    the query matches if any string matches.

**`$options`** *(optional)*
Options to this query.  The default is ().
    
      Options include:
      
        "case-sensitive"
        A case-sensitive query.
        "case-insensitive"
        A case-insensitive query.
        "diacritic-sensitive"
        A diacritic-sensitive query.
        "diacritic-insensitive"
        A diacritic-insensitive query.
        "punctuation-sensitive"
        A punctuation-sensitive query.
        "punctuation-insensitive"
        A punctuation-insensitive query.
        "whitespace-sensitive"
        A whitespace-sensitive query.
        "whitespace-insensitive"
        A whitespace-insensitive query.
        "stemmed"
        A stemmed query.
        "unstemmed"
        An unstemmed query.
        "wildcarded"
        A wildcarded query.
        "unwildcarded"
        An unwildcarded query.
        "exact"
        An exact match query. Shorthand for "case-sensitive",
        "diacritic-sensitive", "punctuation-sensitive",
        "whitespace-sensitive", "unstemmed", and "unwildcarded".
        
        "lang=iso639code"
        Specifies the language of the query. The iso639code
            code portion is case-insensitive, and uses the languages
            specified by
           ISO 639.
            The default is specified in the database configuration.
        "min-occurs=number"
        Specifies the minimum number of occurrences required. If
        fewer that this number of words occur, the fragment does not match.
        The default is 1.
        "max-occurs=number"
        Specifies the maximum number of occurrences required.  If
        more than this number of words occur, the fragment does not match.
        The default is unbounded.
        "synonym"
        Specifies that all of the terms in the $text parameter are
        considered synonyms for scoring purposes.  The result is that
        occurrences of more than one of the synonyms are scored as if
        there are more occurrences of the same term (as opposed to
        having a separate term that contributes to score).

**`$weight`** *(optional)*
A weight for this query.
    Higher weights move search results up in the relevance
    order.  The default is 1.0. The
    weight should be between 64 and -16.
    Weights greater than 64 will have the same effect as a
    weight of 64.
    Weights less than the absolute value of 0.0625 (between -0.0625 and
    0.0625) are rounded to 0, which means that they do not contribute to the
    score.

### Returns

`cts:element-value-query`

### Usage Notes

If neither "case-sensitive" nor "case-insensitive"
    is present, $text is used to determine case sensitivity.
    If $text contains no uppercase, it specifies "case-insensitive".
    If $text contains uppercase, it specifies "case-sensitive".
  
      
    If neither "diacritic-sensitive" nor "diacritic-insensitive"
    is present, $text is used to determine diacritic sensitivity.
    If $text contains no diacritics, it specifies "diacritic-insensitive".
    If $text contains diacritics, it specifies "diacritic-sensitive".
  
      
    If neither "punctuation-sensitive" nor "punctuation-insensitive"
    is present, $text is used to determine punctuation sensitivity.
    If $text contains no punctuation, it specifies "punctuation-insensitive".
    If $text contains punctuation, it specifies "punctuation-sensitive".
  
      
    If neither "whitespace-sensitive" nor "whitespace-insensitive"
    is present, the query is "whitespace-insensitive".
  
      
    If neither "wildcarded" nor "unwildcarded"
    is present, the database configuration and $text determine wildcarding.
    If the database has any wildcard indexes enabled ("three character
    searches", "two character searches", "one character searches",  or
    "trailing wildcard searches") and if $text contains either of the
    wildcard characters '?' or '*', it specifies "wildcarded".
    Otherwise it specifies "unwildcarded".
  
      
    If neither "stemmed" nor "unstemmed"
    is present, the database configuration determines stemming.
    If the database has "stemmed searches" enabled, it specifies "stemmed".
    Otherwise it specifies "unstemmed".
    If the query is a wildcarded query and also a phrase query
    (contains two or more terms), the wildcard terms in the query
    are unstemmed.
  
      
    When you use the "exact" option, you should also enable
    "fast case sensitive searches" and "fast diacritic sensitive searches"
    in your database configuration.
  
      
    Negative "min-occurs" or "max-occurs" values will be treated as 0 and
    non-integral values will be rounded down.  An error will be raised if
    the "min-occurs" value is greater than the "max-occurs" value.
  
       Note that the text content for the value in a
  cts:element-value-query is treated the same as a phrase in a
  cts:word-query, where the phrase is the element value.
  Therefore, any wildcard and/or stemming rules are treated like a phrase.
  For example, if you have an element value of "hello friend" with wildcarding
  enabled for a query, a cts:element-value-query for "he*" will
  not match because the wildcard matches do not span word boundaries, but a
  cts:element-value-query for "hello *" will match.  A search
  for "*" will match, because a "*" wildcard by itself is defined to match
  the value.  Similarly, stemming rules are applied to each term, so a
  search for "hello friends" would match when stemming is enabled for the query
  because "friends" matches "friend". For an example, see the
  fourth example that follows.
       Similarly, because a "*" wildcard by itself is defined to match
  the value, the following query will match any element with the
  QName my-element, regardless of the wildcard indexes enabled in
  the database configuration:
  cts:element-value-query(xs:QName("my-element"), "*", "wildcarded")

### Examples

#### Example 1

```xquery
cts:search(//module,
    cts:element-value-query(
      xs:QName("function"),
      "MarkLogic Corporation"))

  => .. relevance-ordered sequence of 'module' element
  ancestors of 'function' elements whose text
  content equals 'MarkLogic Corporation'.
```

#### Example 2

```xquery
cts:search(//module,
    cts:element-value-query(
      xs:QName("function"),
      "MarkLogic Corporation", "case-insensitive"))

  => .. relevance-ordered sequence of 'module' element
  ancestors of 'function' elements whose text
  content equals 'MarkLogic Corporation', or any other
  case-shift like 'MARKLOGIC CorpoRation'.
```

#### Example 3

```xquery
cts:search(//module,
    cts:and-query((
      cts:element-value-query(
        xs:QName("function"),
        "MarkLogic Corporation",
        "punctuation-insensitive", 0.5),
      cts:element-value-query(
        xs:QName("title"),
        "Word Query"))))
  => .. relevance-ordered sequence of 'module' elements
  which are ancestors of both:
  (a) 'function' elements with text content equal to
      'MarkLogic Corporation', ignoring embedded
      punctuation,
  AND
  (b) 'title' elements with text content equal to
      'Word Query', with the results of the first sub-query
      query given weight 0.5, and the results of the second
      sub-query given the default weight 1.0.  As a result,
      the title phrase 'Word Query' counts more heavily
      towards the relevance score.
```

#### Example 4

```xquery
let $node := <my-node>hello friend</my-node>
return (
cts:contains($node, cts:element-value-query(xs:QName('my-node'),
      "hello friends", "stemmed")),
cts:contains($node, cts:element-value-query(xs:QName('my-node'),
      "he*", "wildcarded")),
cts:contains($node, cts:element-value-query(xs:QName('my-node'),
      "hello f*", "wildcarded"))
)

=> true
   false
   true
```

---

## cts:element-value-query-element-name

Returns the QNames used to construct the specified query.

### Signature

```xquery
cts:element-value-query-element-name(
  $query as cts:element-value-query
) as xs:QName*
```

### Parameters

**`$query`**
A query.

### Returns

`xs:QName*`

### Examples

```xquery
let $query := cts:element-value-query(
              xs:QName("function"),
              "MarkLogic Corporation")
return cts:element-value-query-element-name($query)

  => xs:QName("function")
```

---

## cts:element-value-query-options

Returns the options for the specified query.

### Signature

```xquery
cts:element-value-query-options(
  $query as cts:element-value-query
) as xs:string*
```

### Parameters

**`$query`**
A query.

### Returns

`xs:string*`

### Examples

```xquery
let $query := cts:element-value-query(
              xs:QName("function"),
              "MarkLogic Corporation")
return cts:element-value-query-options($query)

  => "lang=en"
```

---

## cts:element-value-query-text

Returns the text used to construct the specified query.

### Signature

```xquery
cts:element-value-query-text(
  $query as cts:element-value-query
) as xs:string*
```

### Parameters

**`$query`**
A query.

### Returns

`xs:string*`

### Examples

```xquery
let $query := cts:element-value-query(
              xs:QName("function"),
              "MarkLogic Corporation")
return cts:element-value-query-text($query)

  => "MarkLogic Corporation"
```

---

## cts:element-value-query-weight

Returns the weight with which the specified query was constructed.

### Signature

```xquery
cts:element-value-query-weight(
  $query as cts:element-value-query
) as xs:double
```

### Parameters

**`$query`**
A query.

### Returns

`xs:double`

### Examples

```xquery
let $query := cts:element-value-query(
              xs:QName("function"),
              "MarkLogic Corporation")
return cts:element-value-query-weight($query)

  => 1
```

---

## cts:element-word-query

Returns a query matching elements by name with text content containing
  a given phrase.  Searches only through immediate text node children of
  the specified element as well as any text node children of child elements
  defined in the Admin Interface as element-word-query-throughs
  or phrase-throughs; does not search through any other children of
  the specified element. If neither word searches nor stemmed word searches is
  enabled for the target database, an XDMP-SEARCH error is thrown.

### Signature

```xquery
cts:element-word-query(
  $element-name as xs:QName*,
  $text as xs:string*,
  $options as xs:string*?,
  $weight as xs:double??
) as cts:element-word-query
```

### Parameters

**`$element-name`**
One or more element QNames to match.
    When multiple QNames are specified,
    the query matches if any QName matches.

**`$text`**
Some words or phrases to match.
    When multiple strings are specified,
    the query matches if any string matches.

**`$options`** *(optional)*
Options to this query.  The default is ().
    
      Options include:
      
        "case-sensitive"
        A case-sensitive query.
        "case-insensitive"
        A case-insensitive query.
        "diacritic-sensitive"
        A diacritic-sensitive query.
        "diacritic-insensitive"
        A diacritic-insensitive query.
        "punctuation-sensitive"
        A punctuation-sensitive query.
        "punctuation-insensitive"
        A punctuation-insensitive query.
        "whitespace-sensitive"
        A whitespace-sensitive query.
        "whitespace-insensitive"
        A whitespace-insensitive query.
        "stemmed"
        A stemmed query.
        "unstemmed"
        An unstemmed query.
        "wildcarded"
        A wildcarded query.
        "unwildcarded"
        An unwildcarded query.
        "exact"
        An exact match query. Shorthand for "case-sensitive",
        "diacritic-sensitive", "punctuation-sensitive",
        "whitespace-sensitive", "unstemmed", and "unwildcarded".
        
        "lang=iso639code"
        Specifies the language of the query. The iso639code
            code portion is case-insensitive, and uses the languages
            specified by
           ISO 639.
            The default is specified in the database configuration.
        "distance-weight=number"
        A weight applied based on the minimum distance between matches
        of this query.  Higher weights add to the importance of
        proximity (as opposed to term matches) when the relevance order is
        calculated.
        The default value is 0.0 (no impact of proximity). The
        weight should be between 64 and -16.
        Weights greater than 64 will have the same effect as a
        weight of 64.
        This parameter has no effect if the word positions
        index is not enabled.  This parameter has no effect on searches that
        use score-simple, score-random, or score-zero (because those scoring
        algorithms do not consider term frequency, proximity is irrelevant).
        
        "min-occurs=number"
        Specifies the minimum number of occurrences required. If
        fewer that this number of words occur, the fragment does not match.
        The default is 1.
        "max-occurs=number"
        Specifies the maximum number of occurrences required.  If
        more than this number of words occur, the fragment does not match.
        The default is unbounded.
        "synonym"
        Specifies that all of the terms in the $text parameter are
        considered synonyms for scoring purposes.  The result is that
        occurrences of more than one of the synonyms are scored as if
        there are more occurrences of the same term (as opposed to
        having a separate term that contributes to score). 
        "lexicon-expand=value"
        The value is one of full,
        prefix-postfix, off, or
        heuristic (the default is heuristic).
        An option with a value of lexicon-expand=full
        specifies that wildcards are resolved by expanding the pattern to
        words in a lexicon (if there is one available), and turning into a
        series of cts:word-queries, even if this takes a long
        time to evaluate.
        An option with a value of lexicon-expand=prefix-postfix
        specifies that wildcards are resolved by expanding the pattern to the
        pre- and postfixes of the words in the word lexicon (if there is one),
        and turning the query into a series of character queries, even if it
        takes a long time to evaluate.
        An option with a value of lexicon-expand=off
        specifies that wildcards are only resolved by looking up character
        patterns in the search pattern index, not in the lexicon.
        An option with a value of lexicon-expand=heuristic,
        which is the default, specifies that wildcards are resolved by using
        a series of internal rules, such as estimating the number of lexicon
        entries that need to be scanned, seeing if the estimate crosses
        certain thresholds, and (if appropriate), using another way besides
        lexicon expansion to resolve the query.
        
       "lexicon-expansion-limit=number"
        Specifies the limit for lexicon expansion. This puts a restriction
  on the number of lexicon expansions that can be performed. If the limit is
  exceeded, the server may raise an error depending on whether the "limit-check"
  option is set. The default value for this option will be 4096.
        
        "limit-check"
        Specifies that an error will be raised if the lexicon expansion
  exceeds the specified limit.
        "no-limit-check"
        Specifies that error will not be raised if the lexicon expansion
  exceeds the specified limit. The server will try to resolve the wildcard.
  "no-limit-check" is default, if neither "limit-check" nor "no-limit-check" is explicitly
  specified.

**`$weight`** *(optional)*
A weight for this query.
    Higher weights move search results up in the relevance
    order.  The default is 1.0. The
    weight should be between 64 and -16.
    Weights greater than 64 will have the same effect as a
    weight of 64.
    Weights less than the absolute value of 0.0625 (between -0.0625 and
    0.0625) are rounded to 0, which means that they do not contribute to the
    score.

### Returns

`cts:element-word-query`

### Usage Notes

If neither "case-sensitive" nor "case-insensitive"
    is present, $text is used to determine case sensitivity.
    If $text contains no uppercase, it specifies "case-insensitive".
    If $text contains uppercase, it specifies "case-sensitive".
  
      
    If neither "diacritic-sensitive" nor "diacritic-insensitive"
    is present, $text is used to determine diacritic sensitivity.
    If $text contains no diacritics, it specifies "diacritic-insensitive".
    If $text contains diacritics, it specifies "diacritic-sensitive".
  
      
    If neither "punctuation-sensitive" nor "punctuation-insensitive"
    is present, $text is used to determine punctuation sensitivity.
    If $text contains no punctuation, it specifies "punctuation-insensitive".
    If $text contains punctuation, it specifies "punctuation-sensitive".
  
      
    If neither "whitespace-sensitive" nor "whitespace-insensitive"
    is present, the query is "whitespace-insensitive".
  
      
    If neither "wildcarded" nor "unwildcarded"
    is present, the database configuration and $text determine wildcarding.
    If the database has any wildcard indexes enabled ("three character
    searches", "two character searches", "one character searches",  or
    "trailing wildcard searches") and if $text contains either of the
    wildcard characters '?' or '*', it specifies "wildcarded".
    Otherwise it specifies "unwildcarded".
  
      
    If neither "stemmed" nor "unstemmed"
    is present, the database configuration determines stemming.
    If the database has "stemmed searches" enabled, it specifies "stemmed".
    Otherwise it specifies "unstemmed".
    If the query is a wildcarded query and also a phrase query
    (contains two or more terms), the wildcard terms in the query
    are unstemmed.
  
      
    Negative "min-occurs" or "max-occurs" values will be treated as 0 and
    non-integral values will be rounded down.  An error will be raised if
    the "min-occurs" value is greater than the "max-occurs" value.
  
      Relevance adjustment for the "distance-weight" option depends on
  the closest proximity of any two matches of the query.  For example,
  
  cts:element-word-query(xs:QName("p"),("dog","cat"),("distance-weight=10"))
  
  will adjust relevance based on the distance between the closest pair of
  matches of either "dog" or "cat" within an element named "p"
  (the pair may consist only of matches of
  "dog", only of matches of "cat", or a match of "dog" and a match of "cat").

### Examples

#### Example 1

```xquery
cts:search(//module,
    cts:element-word-query(
      xs:QName("function"),
      "MarkLogic Corporation"))

  => .. relevance-ordered sequence of 'module' elements
  ancestors (or self) of elements with QName 'function'
  and text content containing the phrase 'MarkLogic
  Corporation'.
```

#### Example 2

```xquery
cts:search(//module,
    cts:element-word-query(
      xs:QName("function"),
        "MarkLogic Corporation", "case-sensitive"))

  => .. relevance-ordered sequence of 'module' elements
  ancestors (or self) of elements with QName 'function'
  and text content containing the phrase 'MarkLogic
  Corporation', case-sensitive (so 'MarkLogic Corporation'
  matches but 'MARKLOGIC Corporation' does not).
```

#### Example 3

```xquery
cts:search(//module,
    cts:and-query((
      cts:element-word-query(
        xs:QName("function"),
        "MarkLogic Corporation",
        ("case-insensitive", "punctuation-insensitive"), 0.5),
      cts:element-word-query(
        xs:QName("title"),
        "faster"))))

  => .. relevance-ordered sequence of 'module' element
  ancestors (or self) of both:
  (a) 'function' elements with text content containing
      the phrase 'MarkLogic Corporation', ignoring embedded
      punctuation,
  AND
  (b) 'title' elements containing the word 'faster',
      with the results of the first sub-query query given
      weight 0.5, and the results of the second sub-query
      given the default weight 1.0.  As a result, the title
      term 'faster' counts more towards the relevance
      score.
```

---

## cts:element-word-query-element-name

Returns the QNames used to construct the specified query.

### Signature

```xquery
cts:element-word-query-element-name(
  $query as cts:element-word-query
) as xs:QName*
```

### Parameters

**`$query`**
A query.

### Returns

`xs:QName*`

### Examples

```xquery
let $query := cts:element-word-query(xs:QName("elem"), "choice of law")
  return
  cts:element-word-query-element-name($query)
  => xs:QName("elem")
```

---

## cts:element-word-query-options

Returns the options for the specified query.

### Signature

```xquery
cts:element-word-query-options(
  $query as cts:element-word-query
) as xs:string*
```

### Parameters

**`$query`**
A query.

### Returns

`xs:string*`

### Examples

```xquery
let $query := cts:element-word-query(xs:QName("elem"), "choice of law")
  return
  cts:element-word-query-options($query)
  => "lang=en"
```

---

## cts:element-word-query-text

Returns the text used to construct the specified query.

### Signature

```xquery
cts:element-word-query-text(
  $query as cts:element-word-query
) as xs:string*
```

### Parameters

**`$query`**
A query.

### Returns

`xs:string*`

### Examples

```xquery
let $query := cts:element-word-query(xs:QName("elem"), "choice of law")
  return
  cts:element-word-query-text($query)
  => "choice of law"
```

---

## cts:element-word-query-weight

Returns the weight with which the specified query was constructed.

### Signature

```xquery
cts:element-word-query-weight(
  $query as cts:element-word-query
) as xs:double
```

### Parameters

**`$query`**
A query.

### Returns

`xs:double`

### Examples

```xquery
let $query := cts:element-word-query(xs:QName("elem"), "choice of law")
  return
  cts:element-word-query-weight($query)
  => 1
```

---

## cts:false-query

Returns a query that matches no fragments.

### Returns

`cts:or-query`

### Examples

```xquery
cts:search(fn:doc(),cts:false-query())
  =&gt; empty sequence
```

---

## cts:field-range-query

Returns a cts:query matching fields by name with a
  range-index entry equal to a given value.  Searches with the
  cts:field-range-query
  constructor require a field range index on the specified field name(s);
  if there is no range index configured, then an exception is thrown.

### Signature

```xquery
cts:field-range-query(
  $field-name as xs:string*,
  $operator as xs:string,
  $value as xs:anyAtomicType*,
  $options as xs:string*?,
  $weight as xs:double??
) as cts:field-range-query
```

### Parameters

**`$field-name`**
One or more field names to match. When multiple field names are specified,
    the query matches if any field name matches.

**`$operator`**
A comparison operator.
    
      Operators include:
      
        "<"
        Match range index values less than $value.
        "<="
        Match range index values less than or equal to $value.
        ">"
        Match range index values greater than $value.
        ">="
        Match range index values greater than or equal to $value.
        "="
        Match range index values equal to $value.
        "!="
        Match range index values not equal to $value.

**`$value`**
One or more field values to match.
    When multiple values are specified,
    the query matches if any value matches. The value must be a type for
    which there is a range index defined.

**`$options`** *(optional)*
Options to this query.  The default is ().
    
      Options include:
      
        "collation=URI"
        Use the range index with the collation specified by
        URI.  If not specified, then the default collation
        from the query is used. If a range index with the specified
        collation does not exist, an error is thrown.
        "cached"
        Cache the results of this query in the list cache.
        "uncached"
        Do not cache the results of this query in the list cache.
        "cached-incremental"
        When querying on a short date or dateTime range, break the
        query into sub-queries on smaller ranges, and then cache the
        results of each.  See the Usage Notes for details.
        "min-occurs=number"
        Specifies the minimum number of occurrences required. If
        fewer that this number of words occur, the fragment does not match.
        The default is 1.
        "max-occurs=number"
        Specifies the maximum number of occurrences required.  If
        more than this number of words occur, the fragment does not match.
        The default is unbounded.
        "score-function=function"
        Use the selected scoring function. The score function may be:
          
          linearUse a linear function of the difference between the
          specified query value and the matching value in the index to calculate
          a score for this range query.
          reciprocalUse a reciprocal function of the difference
          between the specified query value and the matching value in the
          index to calculate a score for this range query.
          zeroThis range query does not contribute to the
          score. This is the default.
          
        
        "slope-factor=number"
        Apply the given number as a scaling factor to the slope of the
        scoring function. The default is 1.0.
        "synonym"
        Specifies that all of the terms in the $value parameter are
        considered synonyms for scoring purposes.  The result is that
        occurrences of more than one of the synonyms are scored as if
        there are more occurrences of the same term (as opposed to
        having a separate term that contributes to score).

**`$weight`** *(optional)*
A weight for this query.  The default is 1.0.

### Returns

`cts:field-range-query`

### Usage Notes

If you want to constrain on a range of values, you can combine multiple
  cts:field-range-query constructors together
  with cts:and-query or any of the other composable
  cts:query constructors.
      If neither "cached" nor "uncached" is present, it specifies "cached".
      The "cached-incremental" option can improve performance if you
   repeatedly perform range queries on date or dateTime values over a
   short range that does not vary widely over short period of time. To
   benefit, the operator should remain the same "direction" (<,<=, or >,>=) 
   across calls, the bounding date or dateTime changes slightly across calls,
   and the query runs very frequently (multiple times per minute).
   Note that using this options creates significantly more cached queries
   than the "cached" option.
  
      The "cached-incremental" option has the following restrictions and
   interactions: The "min-occurs" and "max-occurs" options will be ignored
   if you use "cached-incremental" in unfiltered search. You can only use
   "score-function=zero" with "cached-incremental". The "cached-incremental"
   option behaves like "cached" if you are not querying date or dateTime values.
  
      
    Negative "min-occurs" or "max-occurs" values will be treated as 0 and
    non-integral values will be rounded down.  An error will be raised if
    the "min-occurs" value is greater than the "max-occurs" value.
  
      "score-function=linear" means that values that are further away from
  the bounds will score higher. "score-function=reciprocal" means that values
  that are closer to the bounds will score higher. The functions are scaled
  appropriately for different types, so that in general the default slope factor
  will provide useful results. Using a slope factor greater than 1 gives
  distinct scores over a smaller range of values, and produces
  generally higher scores.  Using a slope factor less than 1 gives
  distinct scores over a wider range of values, and produces generally
  lower scores.
  
      For queries against a dateTime index, when $value is an xs:dayTimeDuration
  or xs:yearMonthDuration, the query is executed as an age query. $value is
  subtracted from fn:current-dateTime() to create an xs:dateTime used in the query.
  If there is more than one item in $value, they must all be the same type.

### Examples

```xquery
(: Requires a field that includes name and excludes mname :)
(: Insert few documents with test data :)
let $content1 :=
 <name><fname>John</fname><mname>Rob</mname><lname>Goldings</lname></name>
let $content2 :=
 <name><fname>Jim</fname><mname>Ken</mname><lname>Kurla</lname></name>
let $content3 :=
 <name><fname>Ooi</fname><mname>Ben</mname><lname>Fu</lname></name>
let $content4 :=
 <name><fname>James</fname><mname>Rick</mname><lname>Tod</lname></name>
return (
xdmp:document-insert("/aname1.xml",$content1),
xdmp:document-insert("/aname2.xml",$content2),
xdmp:document-insert("/aname3.xml",$content3),
xdmp:document-insert("/aname4.xml",$content4));

(:
   requires a field (range) index of
   type xs:string on field "aname"
:)

cts:search(doc(),cts:field-range-query("aname",">","Jim Kurla"));

(:
  returns the following:
<?xml version="1.0" encoding="UTF-8"?>
<name>
  <fname>John</fname>
  <mname>Rob</mname>
  <lname>Goldings</lname>
</name>
<?xml version="1.0" encoding="UTF-8"?>
<name>
  <fname>Ooi</fname>
  <mname>Ben</mname>
  <lname>Fu</lname>
</name>
:)

(:
   requires a field (range) index of
   type xs:string on "aname"
:)
cts:contains(doc(),cts:field-range-query("aname",">","Jim Kurla"))
(:
  returns "true".
:)
```

---

## cts:field-range-query-field-name

Returns the fieldname used to construct the specified query.

### Signature

```xquery
cts:field-range-query-field-name(
  $query as cts:field-range-query
) as xs:string*
```

### Parameters

**`$query`**
A query.

### Returns

`xs:string*`

### Examples

```xquery
let $query := cts:field-range-query("aname",">","Jim Kurla")
return
cts:field-range-query-field-name($query)
  => aname
```

---

## cts:field-range-query-operator

Returns the operator used to construct the specified query.

### Signature

```xquery
cts:field-range-query-operator(
  $query as cts:field-range-query
) as xs:string
```

### Parameters

**`$query`**
A query.

### Returns

`xs:string`

### Examples

```xquery
let $query := cts:field-range-query("aname",">","Jim Kurla")
return
cts:field-range-query-operator($query)
  => >
```

---

## cts:field-range-query-options

Returns the options for the specified query.

### Signature

```xquery
cts:field-range-query-options(
  $query as cts:field-range-query
) as xs:string*
```

### Parameters

**`$query`**
A query.

### Returns

`xs:string*`

### Examples

```xquery
let $query := cts:field-range-query("aname",">","Jim Kurla")
return
cts:field-range-query-options($query)
  => collation=http://marklogic.com/collation/
```

---

## cts:field-range-query-value

Returns the value used to construct the specified query.

### Signature

```xquery
cts:field-range-query-value(
  $query as cts:field-range-query
) as xs:anyAtomicType*
```

### Parameters

**`$query`**
A query.

### Returns

`xs:anyAtomicType*`

### Examples

```xquery
let $query := cts:field-range-query("aname",">","Jim Kurla")
return
cts:field-range-query-value($query)
  => "Jim Kurla"
```

---

## cts:field-range-query-weight

Returns the weight with which the specified query was constructed.

### Signature

```xquery
cts:field-range-query-weight(
  $query as cts:field-range-query
) as xs:double
```

### Parameters

**`$query`**
A query.

### Returns

`xs:double`

### Examples

```xquery
let $query := cts:field-range-query("aname",">","Jim Kurla")
return
cts:field-range-query-weight($query)
  => 1
```

---

## cts:field-value-query

Returns a query matching text content containing a given value in the
  specified field.  If the specified field does not exist,
  cts:field-value-query throws an exception.
  If the specified field does not have the index setting
  field value searches enabled, either for the database or
  for the specified field, then a cts:search with a
  cts:field-value-query throws an exception. A field
  is a named object that specified elements to include and exclude
  from a search, and can include score weights for any included elements.
  You create fields at the database level using the Admin Interface.  For
  details on fields, see the chapter on "Fields Database Settings" in the
  Administrator's Guide.

### Signature

```xquery
cts:field-value-query(
  $field-name as xs:string*,
  $text as xs:anyAtomicType*,
  $options as xs:string*?,
  $weight as xs:double??
) as cts:field-value-query
```

### Parameters

**`$field-name`**
One or more field names to search over. If multiple field names are
    supplied, the match can be in any of the specified fields (or-query
    semantics).

**`$text`**
The values to match. If multiple values are specified,
    the query matches if any of the values match (or-query
    semantics). For XML and metadata, the values should be strings.
    For JSON, the values can be strings, numbers or booleans to match correspondingly typed nodes.
    To match null, pass in the empty sequence.

**`$options`** *(optional)*
Options to this query.  The default is ().
    
      Options include:
      
        "case-sensitive"
        A case-sensitive query.
        "case-insensitive"
        A case-insensitive query.
        "diacritic-sensitive"
        A diacritic-sensitive query.
        "diacritic-insensitive"
        A diacritic-insensitive query.
        "punctuation-sensitive"
        A punctuation-sensitive query.
        "punctuation-insensitive"
        A punctuation-insensitive query.
        "whitespace-sensitive"
        A whitespace-sensitive query.
        "whitespace-insensitive"
        A whitespace-insensitive query.
        "stemmed"
        A stemmed query.
        "unstemmed"
        An unstemmed query.
        "wildcarded"
        A wildcarded query.
        "unwildcarded"
        An unwildcarded query.
        "exact"
        An exact match query. Shorthand for "case-sensitive",
        "diacritic-sensitive", "punctuation-sensitive",
        "whitespace-sensitive", "unstemmed", and "unwildcarded".
        
        "lang=iso639code"
        Specifies the language of the query. The iso639code
            code portion is case-insensitive, and uses the languages
            specified by
           ISO 639.
            The default is specified in the database configuration.
        "distance-weight=number"
        A weight applied based on the minimum distance between matches
        of this query.  Higher weights add to the importance of
        proximity (as opposed to term matches) when the relevance order is
        calculated.
        The default value is 0.0 (no impact of proximity). The
        weight should be between 64 and -16.
        Weights greater than 64 will have the same effect as a
        weight of 64.
        This parameter has no effect if the word positions
        index is not enabled.  This parameter has no effect on searches that
        use score-simple or score-random (because those scoring algorithms
        do not consider term frequency, proximity is irrelevant).
        
        "min-occurs=number"
        Specifies the minimum number of occurrences required. If
        fewer that this number of words occur, the fragment does not match.
        The default is 1.
        "max-occurs=number"
        Specifies the maximum number of occurrences required.  If
        more than this number of words occur, the fragment does not match.
        The default is unbounded.
        "synonym"
        Specifies that all of the terms in the $text parameter are
        considered synonyms for scoring purposes.  The result is that
        occurrences of more than one of the synonyms are scored as if
        there are more occurrences of the same term (as opposed to
        having a separate term that contributes to score). 
        "lexicon-expansion-limit=number"
        Specifies the limit for lexicon expansion. This puts a restriction
  on the number of lexicon expansions that can be performed. If the limit is
  exceeded, the server may raise an error depending on whether the "limit-check"
  option is set. The default value for this option will be 4096.
        
        "limit-check"
        Specifies that an error will be raised if the lexicon expansion
  exceeds the specified limit.
        "no-limit-check"
        Specifies that error will not be raised if the lexicon expansion
  exceeds the specified limit. The server will try to resolve the wildcard.

**`$weight`** *(optional)*
A weight for this query.
    Higher weights move search results up in the relevance
    order.  The default is 1.0. The
    weight should be between 64 and -16.
    Weights greater than 64 will have the same effect as a
    weight of 64.
    Weights less than the absolute value of 0.0625 (between -0.0625 and
    0.0625) are rounded to 0, which means that they do not contribute to the
    score.

### Returns

`cts:field-value-query`

### Usage Notes

If you use cts:near-query with
  cts:field-value-query, the distance supplied in the near query
  applies to the whole document, not just to the field.  For example, if
  you specify a near query with a distance of 3, it will return matches
  when the values are within 3 words in the whole document,
  For a code example illustrating this, see the
  second example
  
  below. 
      Values are determined based on words (tokens)of values of elements that are
  included in the field. Field values span all the included elements. They
  cannot span excluded elements (this is because MarkLogic Server breaks
  out of the field when it encounters the excluded element and start it again
  field when it encounters the next included element). Field
  values will also span included sibling elements.
      
    If neither "case-sensitive" nor "case-insensitive"
    is present, $text is used to determine case sensitivity.
    If $text contains no uppercase, it specifies "case-insensitive".
    If $text contains uppercase, it specifies "case-sensitive".
  
      
    If neither "diacritic-sensitive" nor "diacritic-insensitive"
    is present, $text is used to determine diacritic sensitivity.
    If $text contains no diacritics, it specifies "diacritic-insensitive".
    If $text contains diacritics, it specifies "diacritic-sensitive".
  
      
    If neither "punctuation-sensitive" nor "punctuation-insensitive"
    is present, $text is used to determine punctuation sensitivity.
    If $text contains no punctuation, it specifies "punctuation-insensitive".
    If $text contains punctuation, it specifies "punctuation-sensitive".
  
      
    If neither "whitespace-sensitive" nor "whitespace-insensitive"
    is present, the query is "whitespace-insensitive".
  
      
    If neither "wildcarded" nor "unwildcarded"
    is present, the database configuration and $text determine wildcarding.
    If the database has any wildcard indexes enabled ("three character
    searches", "two character searches", "one character searches",  or
    "trailing wildcard searches") and if $text contains either of the
    wildcard characters '?' or '*', it specifies "wildcarded".
    Otherwise it specifies "unwildcarded".
  
      
    If neither "stemmed" nor "unstemmed"
    is present, the database configuration determines stemming.
    If the database has "stemmed searches" enabled, it specifies "stemmed".
    Otherwise it specifies "unstemmed".
    If the query is a wildcarded query and also a phrase query
    (contains two or more terms), the wildcard terms in the query
    are unstemmed.
  
      
    When you use the "exact" option, you should also enable
    "fast case sensitive searches" and "fast diacritic sensitive searches"
    in your database configuration.
  
      
    Negative "min-occurs" or "max-occurs" values will be treated as 0 and
    non-integral values will be rounded down.  An error will be raised if
    the "min-occurs" value is greater than the "max-occurs" value.

### Examples

#### Example 1

```xquery
let $contents :=
  <Employee>
    <name>
      <fname>Jaz</fname>
      <mname>Roy</mname>
      <lname>Smith</lname>
    </name>
  </Employee>
return
cts:contains($contents,cts:field-value-query("myField","Jaz Roy Smith"))

=> false, assuming the field "myField" is defined to include element
   "name" and exclude element "mname". The field must exist in the
   database against which this query is evaluated.
```

#### Example 2

```xquery
let $contents :=
  <Employee>
    <name>
      <fname>Jaz</fname>
      <mname>Roy</mname>
      <lname>Smith</lname>
    </name>
  </Employee>
return
cts:contains($contents,cts:field-value-query("myField","Jaz Smith"))

=> true, assuming the field "myField" is defined to include element
   "name" and exclude element "mname". The field must exist in
   the database against which this query is evaluated.
```

#### Example 3

```xquery
In this query, the search is fully resolved in the index.

cts:search(
  fn:doc("/Employee/jaz.xml"),
  cts:field-value-query("myField","Jaz Smith"),
  "unfiltered")

=> Returns the doc which has field "myField" and a match
   with the value of the field.
```

---

## cts:field-value-query-field-name

Returns the names used to construct the specified
  cts:field-value-query.

### Signature

```xquery
cts:field-value-query-field-name(
  $query as cts:field-value-query
) as xs:string*
```

### Parameters

**`$query`**
A query.

### Returns

`xs:string*`

### Examples

```xquery
let $query := cts:field-value-query("myField", "choice of law")
return
cts:field-value-query-field-name($query)

=> "myField"
```

---

## cts:field-value-query-options

Returns the options for the specified
  cts:field-value-query.

### Signature

```xquery
cts:field-value-query-options(
  $query as cts:field-value-query
) as xs:string*
```

### Parameters

**`$query`**
A query.

### Returns

`xs:string*`

### Examples

```xquery
let $query := cts:field-value-query("myField", "choice of law")
return
cts:field-value-query-options($query)

=> "lang=en"
```

---

## cts:field-value-query-text

Returns the values used to construct the specified
  cts:field-value-query.

### Signature

```xquery
cts:field-value-query-text(
  $query as cts:field-value-query
) as xs:anyAtomicType*
```

### Parameters

**`$query`**
A query.

### Returns

`xs:anyAtomicType*`

### Examples

```xquery
let $query := cts:field-value-query("myField", "choice of law")
return
cts:field-value-query-text($query)

=> "choice of law"
```

---

## cts:field-value-query-weight

Returns the weight with which the specified query was constructed.

### Signature

```xquery
cts:field-value-query-weight(
  $query as cts:field-value-query
) as xs:double
```

### Parameters

**`$query`**
A query.

### Returns

`xs:double`

### Examples

```xquery
let $query := cts:field-value-query("myField", "choice of law")
return
cts:field-value-query-weight($query)

=> 1
```

---

## cts:field-word-query

Returns a query matching fields with text content containing a given
  phrase.  If the specified field does not exist, this function
  throws an exception.  A field
  is a named object that specified elements to include and exclude
  from a search, and can include score weights for any included elements.
  You create fields at the database level using the Admin Interface.  For
  details on fields, see the chapter on "Fields Database Settings" in the
  Administrator's Guide.

### Signature

```xquery
cts:field-word-query(
  $field-name as xs:string*,
  $text as xs:string*,
  $options as xs:string*?,
  $weight as xs:double??
) as cts:field-word-query
```

### Parameters

**`$field-name`**
One or more field names to search over. If multiple field names are
    supplied, the match can be in any of the specified fields (or-query
    semantics).

**`$text`**
The word or phrase to match. If multiple strings are specified,
    the query matches if any of the words or phrases match (or-query
    semantics).

**`$options`** *(optional)*
Options to this query.  The default is ().
    
      Options include:
      
        "case-sensitive"
        A case-sensitive query.
        "case-insensitive"
        A case-insensitive query.
        "diacritic-sensitive"
        A diacritic-sensitive query.
        "diacritic-insensitive"
        A diacritic-insensitive query.
        "punctuation-sensitive"
        A punctuation-sensitive query.
        "punctuation-insensitive"
        A punctuation-insensitive query.
        "whitespace-sensitive"
        A whitespace-sensitive query.
        "whitespace-insensitive"
        A whitespace-insensitive query.
        "stemmed"
        A stemmed query.
        "unstemmed"
        An unstemmed query.
        "wildcarded"
        A wildcarded query.
        "unwildcarded"
        An unwildcarded query.
        "exact"
        An exact match query. Shorthand for "case-sensitive",
        "diacritic-sensitive", "punctuation-sensitive",
        "whitespace-sensitive", "unstemmed", and "unwildcarded".
        
        "lang=iso639code"
        Specifies the language of the query. The iso639code
            code portion is case-insensitive, and uses the languages
            specified by
           ISO 639.
            The default is specified in the database configuration.
        "distance-weight=number"
        A weight applied based on the minimum distance between matches
        of this query.  Higher weights add to the importance of
        proximity (as opposed to term matches) when the relevance order is
        calculated.
        The default value is 0.0 (no impact of proximity). The
        weight should be between 64 and -16.
        Weights greater than 64 will have the same effect as a
        weight of 64.
        This parameter has no effect if the word positions
        index is not enabled.  This parameter has no effect on searches that
        use score-simple, score-random, or score-zero (because those scoring
        algorithms do not consider term frequency, proximity is irrelevant).
        
        "min-occurs=number"
        Specifies the minimum number of occurrences required. If
        fewer that this number of words occur, the fragment does not match.
        The default is 1.
        "max-occurs=number"
        Specifies the maximum number of occurrences required.  If
        more than this number of words occur, the fragment does not match.
        The default is unbounded.
        "synonym"
        Specifies that all of the terms in the $text parameter are
        considered synonyms for scoring purposes.  The result is that
        occurrences of more than one of the synonyms are scored as if
        there are more occurrences of the same term (as opposed to
        having a separate term that contributes to score). 
        "lexicon-expand=value"
        The value is one of full,
        prefix-postfix, off, or
        heuristic (the default is heuristic).
        An option with a value of lexicon-expand=full
        specifies that wildcards are resolved by expanding the pattern to
        words in a lexicon (if there is one available), and turning into a
        series of cts:word-queries, even if this takes a long
        time to evaluate.
        An option with a value of lexicon-expand=prefix-postfix
        specifies that wildcards are resolved by expanding the pattern to the
        pre- and postfixes of the words in the word lexicon (if there is one),
        and turning the query into a series of character queries, even if it
        takes a long time to evaluate.
        An option with a value of lexicon-expand=off
        specifies that wildcards are only resolved by looking up character
        patterns in the search pattern index, not in the lexicon.
        An option with a value of lexicon-expand=heuristic,
        which is the default, specifies that wildcards are resolved by using
        a series of internal rules, such as estimating the number of lexicon
        entries that need to be scanned, seeing if the estimate crosses
        certain thresholds, and (if appropriate), using another way besides
        lexicon expansion to resolve the query.
        
    "lexicon-expansion-limit=number"
    Specifies the limit for lexicon expansion. This puts a restriction
    on the number of lexicon expansions that can be performed. If the limit is
    exceeded, the server may raise an error depending on whether the "limit-check"
    option is set. The default value for this option will be 4096.
    
    "limit-check"
    Specifies that an error will be raised if the lexicon expansion
    exceeds the specified limit.
    "no-limit-check"
    Specifies that error will not be raised if the lexicon expansion
    exceeds the specified limit. The server will try to resolve the wildcard.

**`$weight`** *(optional)*
A weight for this query.
    Higher weights move search results up in the relevance
    order.  The default is 1.0. The
    weight should be between 64 and -16.
    Weights greater than 64 will have the same effect as a
    weight of 64.
    Weights less than the absolute value of 0.0625 (between -0.0625 and
    0.0625) are rounded to 0, which means that they do not contribute to the
    score.

### Returns

`cts:field-word-query`

### Usage Notes

If you use cts:near-query with
  cts:field-word-query, the distance supplied in the near query
  applies to the whole document, not just to the field.  For example, if
  you specify a near query with a distance of 3, it will return matches
  when the words or phrases are within 3 words in the whole document,
  even if some of those words are not in the specified field.  For a code
  example illustrating this, see the
  second example
  
  below. 
      Phrases are determined based on words being next to each other
  (word positions with a distance of 1) and words being in the same
  instance of the field.  Because field word positions
  are determined based on the fragment, not on the field, field phrases
  cannot span excluded elements (this is because MarkLogic Server breaks
  out of the field when it encounters the excluded element and start a new
  field when it encounters the next included element).  Similarly, field
  phrases will not span included sibling elements.  The
  second code example below
  
  illustrates this. 
      The phrase-through feature will be enabled once you include the path 
  element in the field setting. Field phrases will automatically phrase-through
  all child elements of an included element, until it encounters an explicitly 
  excluded element. The
  third example
  
  below illustrates this.
  An example of when this automatic phrase-through behavior might be
  convenient is if you create a field that includes only the element
  ABSTRACT.  Then all child elements of ABSTRACT
  are included in the field, and phrases would span all of the child
  elements (that is, phrases would "phrase-through" all the child elements).
      
    Negative "min-occurs" or "max-occurs" values will be treated as 0 and
    non-integral values will be rounded down.  An error will be raised if
    the "min-occurs" value is greater than the "max-occurs" value.

### Examples

#### Example 1

```xquery
(: Assume the database configuration includes a field named "myField"
 : on the paths /root/a/name and /root/b/name and a corresponding
 : field range index.
 :)

cts:search(fn:doc(), cts:field-word-query("myField", ("amy", "bill")))

(: Then the search matches all documents that contain either "amy" or
 : "bill" in the value of /root/a/name or /root/b/name (the field). 
 : For example, it would match this document:
 :
 :   <root><a><name>bill</name></a></root>
 :
 : But would not match this document:
 :
 :   <root><c><name>bill</name></c></root>
 :
 : By contrast, if you defined an element index on the element "name"
 : and queried using cts:element-word-query, both documents would match.
 :)
```

#### Example 2

```xquery
(: Assume the database configuration includes a field named "buzz"
 : on the path /hello/buzz, with localname "buzz" as an include and
 : localname "baz" as an exclude.
 :)

let $x :=
  <hello>word1 word2 word3
    <buzz>word4 word5</buzz>
    <baz>word6 word7 word8</baz>
    <buzz>word9 word10</buzz>
  </hello>
return (
  cts:contains($x, cts:near-query(
    (cts:field-word-query("buzz", "word5"),
     cts:field-word-query("buzz", "word9")), 3)),
  cts:contains($x, cts:near-query(
    (cts:field-word-query("buzz", "word5"),
     cts:field-word-query("buzz", "word9")), 4)),
  cts:contains($x,
    cts:field-word-query("buzz", "word5 word9")))

(:
 : Returns the sequence ("false", "true", "false").
 : The first part does not match because "word5" and "word9" do 
 : not occur within 3 words of each other; distance is calculated 
 : based on the whole node (or document if querying documents in 
 : the database), rather than on the field. The distance requirement
 : of the second near-query (4) is met, so the query matches and
 : returns true. The third query does not match because there
 : are words between "word5" and "word9", and the phrase is based
 : on the entire node, not on the field.
:)
```

#### Example 3

```xquery
(: Assume the database configuration includes a field named "buzz"
 : on the path /hello/buzz, with localname "buzz" as an include and
 : localname "baz" as an exclude.
 :)
let $x :=
<hello>
  <buzz>word1 word2
    <gads>word3 word4 word5</gads>
    <zukes>word6 word7 word8</zukes>
  word9 word10
  </buzz>
</hello>
return (
cts:contains($x,
  cts:field-word-query("buzz", "word2 word3")))

(: Returns "true" because the children of "buzz" are not excluded, 
 : and are therefore automatically phrased through.
:)
```

---

## cts:field-word-query-field-name

Returns the names used to construct the specified
  cts:field-word-query.

### Signature

```xquery
cts:field-word-query-field-name(
  $query as cts:field-word-query
) as xs:string*
```

### Parameters

**`$query`**
A query.

### Returns

`xs:string*`

### Examples

```xquery
let $query := cts:field-word-query("myField", "choice of law")
return
cts:field-word-query-field-name($query)

=> "myField"
```

---

## cts:field-word-query-options

Returns the options for the specified
  cts:field-word-query.

### Signature

```xquery
cts:field-word-query-options(
  $query as cts:field-word-query
) as xs:string*
```

### Parameters

**`$query`**
A query.

### Returns

`xs:string*`

### Examples

```xquery
let $query := cts:field-word-query("myField", "choice of law")
return
cts:field-word-query-options($query)

=> "lang=en"
```

---

## cts:field-word-query-text

Returns the text used to construct the specified
  cts:field-word-query.

### Signature

```xquery
cts:field-word-query-text(
  $query as cts:field-word-query
) as xs:string*
```

### Parameters

**`$query`**
A query.

### Returns

`xs:string*`

### Examples

```xquery
let $query := cts:field-word-query("myField", "choice of law")
return
cts:field-word-query-text($query)

=> "choice of law"
```

---

## cts:field-word-query-weight

Returns the weight with which the specified query was constructed.

### Signature

```xquery
cts:field-word-query-weight(
  $query as cts:field-word-query
) as xs:double
```

### Parameters

**`$query`**
A query.

### Returns

`xs:double`

### Examples

```xquery
let $query := cts:field-word-query("myField", "choice of law")
return
cts:field-word-query-weight($query)

=> 1
```

---

## cts:geospatial-region-query

Construct a query to match regions in documents
    that satisfy a specified relationship relative to other regions. For
    example, regions in documents that intersect with regions specified
    in the search criteria.

### Signature

```xquery
cts:geospatial-region-query(
  $geospatial-region-reference as cts:reference*,
  $operation as xs:string,
  $regions as cts:region*,
  $options as xs:string*?,
  $weight as xs:double??
) as cts:geospatial-region-query
```

### Parameters

**`$geospatial-region-reference`**
Zero or more geospatial path region index references that identify
      regions in your content. To create a reference, see
      cts:geospatial-region-path-reference.

**`$operation`**
The match operation to apply between the regions specified in the
      $geospatial-region-reference parameter and the
      regions in the $regions parameter. Allowed values:
      contains, covered-by, covers,
      disjoint, intersects, overlaps,
      within, equals, touches,
      crosses. See the Usage Notes for details.

**`$regions`**
Criteria regions to match against the regions specified in the
      $geospatial-region-reference parameter. These regions
      function as the right operand of $operation.

**`$options`** *(optional)*
Options to this query.  The default is (). Available options:
      
        
        "units=value"
        Measure distances and the radii of circles using the
         given units.
         Allowed values: miles (default), km,
         feet, and meters. This option only affects
         regions provided in the $regions parameter, not regions
         stored in documents.
        "score-function=function"
        Use the selected scoring function. The score function may be:
          
          linearUse a linear function of the difference between the
          specified query value and the matching value in the index to calculate
          a score for this range query.
          reciprocalUse a reciprocal function of the difference
          between the specified query value and the matching value in the
          index to calculate a score for this range query.
          zeroThis range query does not contribute to the
          score. This is the default.
          
        
        "slope-factor=number"
        Apply the given number as a scaling factor to the slope of the
        scoring function. The default is 1.0.
        "synonym"
        Specifies that all of the terms in the $regions parameter are
        considered synonyms for scoring purposes.  The result is that
        occurrences of more than one of the synonyms are scored as if
        there are more occurrence of the same term (as opposed to
        having a separate term that contributes to score). 
        "tolerance=distance"
        Tolerance is the largest allowable variation in geometry calculations.
        If the distance between two points is less than tolerance, then the two
        points are considered equal. For the raw coordinate system, use the units
        of the coordinates. For geographic coordinate systems, use the units
        specified by the units option.

**`$weight`** *(optional)*
A weight for this query.  The default is 1.0.

### Returns

`cts:geospatial-region-query`

### Usage Notes

This function matches regions in documents in the database satisfying
   the relationship R1 op R2, where R1 is a region in
   a database document, op is the operator provided in the
   operation parameter, and R2 is any of the regions
   provided in the regions parameter. The R1 regions
   under considerations are those in the indexes provided in the
   geospatial-region-reference parameter.
      The database configuration must include a geospatial path region index
   corresponding to each R1 region. For details, see
 Geospatial Region Queries and Indexes in the Search Developer's Guide.
      The operations are defined by the
   Dimensionally Extended
   nine-Intersection Model (DE-9IM) of spatial relations. They have the
   following semantics:
      
   
    "contains"
    R1 contains R2 if every point of R2 is also a point of
     R1, and their interiors intersect.
    "covered-by"
    R1 is covered-by R2 if every point of
     R1 is also a point of R2.
    "covers"
    R1 covers R2 if every point of R2 is also a point of
     R1.
    "disjoint"
    R1 is disjoint from R2 if they have no points
     in common.
    "intersects"
    R1 intersects R2 if the two regions have at least one point in
     common.
    "overlaps"
    R1 overlaps R2 if the two regions partially intersect -- that
     is, they have some but not all points in common -- and the intersection of
     R1 and R2 has the same dimension as R1 and
     R2.
    "within"
    R1 is within R2 if every point of R1 is also
     a point of R2, and their interiors intersect.
    "equals"
    R1 equals R2 if every point of R1 is a point of
     R2, and every point of R2 is a point of R1. That
     is, the regions are topologically equal.
    "touches"
    R1 touches R2 if they have a boundary point in common but no
     interior points in common.
    "crosses"
    R1 crosses R2 if their interiors intersect and the dimension of
     the intersection is less than that of at least one of the regions.
  
      Note: the operation covers differs from contains
   only in that covers does not distinguish between points in the
   boundary and the interior of geometries. In general, covers
   should be used in preference to contains. Similarly,
   covered-by should generally be used in preference to
   within.
      If either the geospatial-region-reference or
   regions parameter is an empty list, the query will not
   match any documents.
      The query uses the coordinate system and precision of the geospatial
   region index reference supplied in the
   geospatial-region-reference parameter. If multiple index
   references are specified and they have conflicting coordinate systems,
   an XDMP-INCONSCOORD error is thrown.

### Examples

```xquery
cts:geospatial-region-query(
  cts:geospatial-region-path-reference("//item/region"),
    "contains", cts:box(10, 20, 30, 40))
```

---

## cts:geospatial-region-query-operation

Returns the comparison operation specified when constructing the
    input query.

### Signature

```xquery
cts:geospatial-region-query-operation(
  $query as cts:geospatial-region-query
) as xs:string
```

### Parameters

**`$query`**
A geospatial region path query.

### Returns

`xs:string`

### Examples

```xquery
cts:geospatial-region-query-operation(
  cts:geospatial-region-query(
    cts:geospatial-region-path-reference("//item/region")
    "contains", cts:box(10, 20, 30, 40))
)

=> "contains"
```

---

## cts:geospatial-region-query-options

Returns the options specified when constructing the input query.

### Signature

```xquery
cts:geospatial-region-query-options(
  $query as cts:geospatial-region-query
) as xs:string*
```

### Parameters

**`$query`**
A geospatial region path query.

### Returns

`xs:string*`

### Examples

```xquery
cts:geospatial-region-query-options(
  cts:geospatial-region-query(
    cts:geospatial-region-path-reference("//item/region")
    "contains", cts:box(10, 20, 30, 40),
    ("units=km", "tolerance=0.025"))
)

=> ("units=km", "tolerance=0.025")
```

---

## cts:geospatial-region-query-reference

Returns the geospatial region path index reference(s) specified
    when constructing the input query.

### Signature

```xquery
cts:geospatial-region-query-reference(
  $query as cts:geospatial-region-query
) as cts:reference*
```

### Parameters

**`$query`**
A geospatial region path query.

### Returns

`cts:reference*`

### Examples

```xquery
cts:geospatial-region-query-reference(
  cts:geospatial-region-query(
    cts:geospatial-region-path-reference("//item/region")
    "contains", cts:box(10, 20, 30, 40))
)

=> A region path index reference of the following form:

   cts:geospatial-region-path-reference(
     "//item/region",("coordinate-system=wgs84"))
```

---

## cts:geospatial-region-query-region

Returns the region criteria specified when constructing the
    input query.

### Signature

```xquery
cts:geospatial-region-query-region(
  $query as cts:geospatial-region-query
) as cts:region*
```

### Parameters

**`$query`**
A geospatial region path query.

### Returns

`cts:region*`

### Examples

```xquery
cts:geospatial-region-query-region(
  cts:geospatial-region-query(
    cts:geospatial-region-path-reference("//item/region")
    "contains", cts:box(10, 20, 30, 40))
)

=> cts:box("[10, 20, 30, 40]")
```

---

## cts:geospatial-region-query-weight

Returns the weight specified when constructing the input query.

### Signature

```xquery
cts:geospatial-region-query-weight(
  $query as cts:geospatial-region-query
) as xs:double
```

### Parameters

**`$query`**
A geospatial region path query.

### Returns

`xs:double`

### Examples

```xquery
cts:geospatial-region-query-weight(
  cts:geospatial-region-query(
    cts:geospatial-region-path-reference("//item/region")
    "contains", cts:box(10, 20, 30, 40), (), 2.0)
)

=> 2.0
```

---

## cts:json-property-child-geospatial-query

Returns a query matching json properties by name which has
  specific children representing latitude and longitude values for
  a point contained within the given geographic box, circle, or polygon, or
  equal to the given point.  Points that lie
  between the southern boundary and the northern boundary of a box,
  travelling northwards,
  and between the western boundary and the eastern boundary of the box,
  travelling eastwards, will match.
  Points contained within the given radius of the center point of a circle will
  match, using the curved distance on the surface of the Earth.
  Points contained within the given polygon will match, using great circle arcs
  over a spherical model of the Earth as edges.  An error may result
  if the polygon is malformed in some way.
  Points equal to the a given point will match, taking into account the fact
  that longitudes converge at the poles.
  Using the geospatial query constructors requires a valid geospatial
  license key; without a valid license key, searches that include
  geospatial queries will throw an exception.

### Signature

```xquery
cts:json-property-child-geospatial-query(
  $parent-property-name as xs:string*,
  $child-property-names as xs:string*,
  $regions as cts:region*,
  $options as xs:string*?,
  $weight as xs:double??
) as cts:json-property-child-geospatial-query
```

### Parameters

**`$parent-property-name`**
One or more parent property names to match.
    When multiple names are specified,
    the query matches if any name matches.

**`$child-property-names`**
One or more child property names to match.
    When multiple names are specified, the query matches
    if any name matches; however, only the first matching latitude
    child in any point instance will be checked.  The property must specify
    both latitude and longitude coordinates.

**`$regions`**
One or more geographic boxes, circles, polygons, or points. Where multiple
    regions are specified, the query matches if any region matches.

**`$options`** *(optional)*
Options to this query.  The default is ().
    Options include:
      
        
        "coordinate-system=string"
        Use the given coordinate system. Valid values are:
          
          wgs84The WGS84 coordinate system with degrees as the angular unit.
          wgs84/radiansThe WGS84 coordinate system with radians as the angular unit.
          wgs84/doubleThe WGS84 coordinate system at double precision with degrees as the angular unit.
          wgs84/radians/doubleThe WGS84 coordinate system at double precision with radians as the angular unit.
          etrs89The ETRS89 coordinate system.
          etrs89/doubleThe ETRS89 coordinate system at double precision.
          rawThe raw (unmapped) coordinate system.
          raw/doubleThe raw coordinate system at double precision.
          
          
          "precision=string"
          Use the coordinate system at the given precision. Allowed values:
          float (default) and double.
        "units=value"
        Measure distance and the radii of circles in the specified units.
         Allowed values: miles (default), km,
         feet, meters.
        "boundaries-included"
        Points on boxes', circles', and polygons' boundaries are counted
         as matching.  This is the default.
        "boundaries-excluded"
        Points on boxes', circles', and polygons' boundaries are not
  counted as matching.
        "boundaries-latitude-excluded"
        Points on boxes' latitude boundaries are not counted as
  matching.
        "boundaries-longitude-excluded"
        Points on boxes' longitude boundaries are not counted as
  matching.
        "boundaries-south-excluded"
        Points on the boxes' southern boundaries are not counted as
  matching.
        "boundaries-west-excluded"
        Points on the boxes' western boundaries are not counted as
  matching.
        "boundaries-north-excluded"
        Points on the boxes' northern boundaries are not counted as
  matching.
        "boundaries-east-excluded"
        Points on the boxes' eastern boundaries are not counted as
  matching.
        "boundaries-circle-excluded"
        Points on circles' boundary are not counted as matching.
        "boundaries-endpoints-excluded"
        Points on linestrings' boundary (the endpoints) are not counted as matching.
        "cached"
        Cache the results of this query in the list cache.
        "uncached"
        Do not cache the results of this query in the list cache.
        "type=long-lat-point"
        Specifies the format for the point in the data as longitude first,
        latitude second.
        "type=point"
        Specifies the format for the point in the data as latitude first,
        longitude second.  This is the default format.
        "score-function=function"
        Use the selected scoring function. The score function may be:
          
          linearUse a linear function of the difference between the
          specified query value and the matching value in the index to calculate
          a score for this range query.
          reciprocalUse a reciprocal function of the difference
          between the specified query value and the matching value in the
          index to calculate a score for this range query.
          zeroThis range query does not contribute to the
          score. This is the default.
          
        
        "slope-factor=number"
        Apply the given number as a scaling factor to the slope of the
        scoring function. The default is 1.0.
        "synonym"
        Specifies that all of the terms in the $regions parameter are
        considered synonyms for scoring purposes.  The result is that
        occurrences of more than one of the synonyms are scored as if
        there are more occurrence of the same term (as opposed to
        having a separate term that contributes to score).

**`$weight`** *(optional)*
A weight for this query.  The default is 1.0.

### Returns

`cts:json-property-child-geospatial-query`

### Usage Notes

The point value is expressed in the content of the property as a child
of numbers, separated by whitespace and punctuation (excluding decimal points
and sign characters).

      The value of the precision option takes precedence over
 that implied by the governing coordinate system name, including the
 value of the coordinate-system option. For example, if the
 governing coordinate system is "wgs84/double" and the precision
 option is "float", then the query uses single precision.

      Point values and boundary specifications of boxes are given in degrees
relative to the WGS84 coordinate system.  Southern latitudes and Western
longitudes take negative values.  Longitudes will be wrapped to the range
(-180,+180) and latitudes will be clipped to the range (-90,+90).

      If the northern boundary of a box is south of the southern boundary, no
points will  match. However, longitudes wrap around the globe, so that if
the western boundary is east of the eastern boundary,
then the box crosses the anti-meridian.

      Special handling occurs at the poles, as all longitudes exist at latitudes
+90 and -90.

      If neither "cached" nor "uncached" is present, it specifies "cached".
      "score-function=linear" means that values that are further away from
  the bounds will score higher. "score-function=reciprocal" means that values
  that are closer to the bounds will score higher. The functions are scaled
  appropriately for different types, so that in general the default slope
  factor will provide useful results. Using a slope factor greater than
  1 gives distinct scores over a smaller range of values, and produces
  generally higher scores.  Using a slope factor less than 1 gives distinct
  scores over a wider range of values, and produces generally lower scores.

### Examples

```xquery
(: create a document with test data :)
xdmp:document-insert("/points.json",
object-node {
  "item" : object-node {
    "point" : object-node {
      "pos" : "15.35, 35.34"
    }
  }
});

cts:search(doc("/points.json")//item,
  cts:json-property-child-geospatial-query("point", "pos",
    cts:box(10.0, 35.0, 20.0, 40.0)));
(:
  returns the following node: {"point":{"pos":"15.35, 35.34"}}
:)

cts:search(doc("/points.json")//item,
  cts:json-property-geospatial-query("point", cts:box(12.0, 20.0, 20.0, 35.0)));
(:
  returns ()
:)
```

---

## cts:json-property-child-geospatial-query-child-name

Returns the names used to construct the specified query.

### Signature

```xquery
cts:json-property-child-geospatial-query-child-name(
  $query as cts:json-property-child-geospatial-query
) as xs:string*
```

### Parameters

**`$query`**
A query.

### Returns

`xs:string*`

### Examples

```xquery
let $query := cts:json-property-child-geospatial-query("point", "pos",
     cts:box(10.1, 10.2, 20.1, 20.2))
return cts:json-property-child-geospatial-query-child-name($query)

=> "pos"
```

---

## cts:json-property-child-geospatial-query-options

Returns the options for the specified query.

### Signature

```xquery
cts:json-property-child-geospatial-query-options(
  $query as cts:json-property-child-geospatial-query
) as xs:string*
```

### Parameters

**`$query`**
A query.

### Returns

`xs:string*`

### Examples

```xquery
let $query := cts:json-property-child-geospatial-query("point", "pos",
     cts:box(10.1, 10.2, 20.1, 20.2))
return cts:json-property-child-geospatial-query-Options($query)

=> coordinate-system=wgs84
```

---

## cts:json-property-child-geospatial-query-property-name

Returns the names used to construct the specified query.

### Signature

```xquery
cts:json-property-child-geospatial-query-property-name(
  $query as cts:json-property-child-geospatial-query
) as xs:string*
```

### Parameters

**`$query`**
A query.

### Returns

`xs:string*`

### Examples

```xquery
let $query := cts:json-property-child-geospatial-query("point", "pos",
     cts:box(10.1, 10.2, 20.1, 20.2))
return cts:json-property-child-geospatial-query-property-name($query)

=> "point"
```

---

## cts:json-property-child-geospatial-query-region

Returns the geographical regions with which the specified query was
  constructed.

### Signature

```xquery
cts:json-property-child-geospatial-query-region(
  $query as cts:json-property-child-geospatial-query
) as cts:region*
```

### Parameters

**`$query`**
A query.

### Returns

`cts:region*`

### Examples

```xquery
let $query := cts:json-property-child-geospatial-query("point", "pos",
     cts:box(10.1, 10.2, 20.1, 20.2))
return cts:json-property-child-geospatial-query-region($query)

=> cts:box("[10.1, 10.2, 20.1, 20.2]")
```

---

## cts:json-property-child-geospatial-query-weight

Returns the weight with which the specified query was constructed.

### Signature

```xquery
cts:json-property-child-geospatial-query-weight(
  $query as cts:json-property-child-geospatial-query
) as xs:double
```

### Parameters

**`$query`**
A query.

### Returns

`xs:double`

### Examples

```xquery
let $query := cts:json-property-child-geospatial-query("point", "pos",
     cts:box(10.1, 10.2, 20.1, 20.2))
return cts:json-property-child-geospatial-query-Weight($query)

=> 1
```

---

## cts:json-property-geospatial-query

Returns a query matching json properties by name whose content
  represents a point contained within the given geographic box, circle, or
  polygon, or equal to the given point. Points that lie
  between the southern boundary and the northern boundary of a box,
  travelling northwards,
  and between the western boundary and the eastern boundary of the box,
  travelling eastwards, will match.
  Points contained within the given radius of the center point of a circle will
  match, using the curved distance on the surface of the Earth.
  Points contained within the given polygon will match, using great circle arcs
  over a spherical model of the Earth as edges.  An error may result
  if the polygon is malformed in some way.
  Points equal to the a given point will match, taking into account the fact
  that longitudes converge at the poles.
  Using the geospatial query constructors requires a valid geospatial
  license key; without a valid license key, searches that include
  geospatial queries will throw an exception.

### Signature

```xquery
cts:json-property-geospatial-query(
  $property-name as xs:string*,
  $regions as cts:region*,
  $options as xs:string*?,
  $weight as xs:double??
) as cts:json-property-geospatial-query
```

### Parameters

**`$property-name`**
One or more json property names to match.
    When multiple names are specified,
    the query matches if any name matches.

**`$regions`**
One or more geographic boxes, circles, polygons, or points. Where multiple
    regions are specified, the query matches if any region matches.

**`$options`** *(optional)*
Options to this query.  The default is ().
    Options include:
      
        
        "coordinate-system=string"
        Use the given coordinate system. Valid values are:
          
          wgs84The WGS84 coordinate system with degrees as the angular unit.
          wgs84/radiansThe WGS84 coordinate system with radians as the angular unit.
          wgs84/doubleThe WGS84 coordinate system at double precision with degrees as the angular unit.
          wgs84/radians/doubleThe WGS84 coordinate system at double precision with radians as the angular unit.
          etrs89The ETRS89 coordinate system.
          etrs89/doubleThe ETRS89 coordinate system at double precision.
          rawThe raw (unmapped) coordinate system.
          raw/doubleThe raw coordinate system at double precision.
          
          
          "precision=string"
          Use the coordinate system at the given precision. Allowed values:
          float (default) and double.
        "units=value"
        Measure distance and the radii of circles in the specified units.
         Allowed values: miles (default), km,
         feet, meters.
        "boundaries-included"
        Points on boxes', circles', and polygons' boundaries are counted as
         matching.  This is the default.
        "boundaries-excluded"
        Points on boxes', circles', and polygons' boundaries are not
  counted as matching.
        "boundaries-latitude-excluded"
        Points on boxes' latitude boundaries are not counted as
  matching.
        "boundaries-longitude-excluded"
        Points on boxes' longitude boundaries are not counted as
  matching.
        "boundaries-south-excluded"
        Points on the boxes' southern boundaries are not counted as
  matching.
        "boundaries-west-excluded"
        Points on the boxes' western boundaries are not counted as
  matching.
        "boundaries-north-excluded"
        Points on the boxes' northern boundaries are not counted as
  matching.
        "boundaries-east-excluded"
        Points on the boxes' eastern boundaries are not counted as
  matching.
        "boundaries-circle-excluded"
        Points on circles' boundary are not counted as matching.
        "boundaries-endpoints-excluded"
        Points on linestrings' boundary (the endpoints) are not counted as matching.
        "cached"
        Cache the results of this query in the list cache.
        "uncached"
        Do not cache the results of this query in the list cache.
        "type=long-lat-point"
        Specifies the format for the point in the data as longitude first,
        latitude second.
        "type=point"
        Specifies the format for the point in the data as latitude first,
        longitude second.  This is the default format.
        "score-function=function"
        Use the selected scoring function. The score function may be:
          
          linearUse a linear function of the difference between the
          specified query value and the matching value in the index to calculate
          a score for this range query.
          reciprocalUse a reciprocal function of the difference
          between the specified query value and the matching value in the
          index to calculate a score for this range query.
          zeroThis range query does not contribute to the
          score. This is the default.
          
        
        "slope-factor=number"
        Apply the given number as a scaling factor to the slope of the
        scoring function. The default is 1.0.
        "synonym"
        Specifies that all of the terms in the $regions parameter are
        considered synonyms for scoring purposes.  The result is that
        occurrences of more than one of the synonyms are scored as if
        there are more occurrence of the same term (as opposed to
        having a separate term that contributes to score).

**`$weight`** *(optional)*
A weight for this query.  The default is 1.0.

### Returns

`cts:json-property-geospatial-query`

### Usage Notes

The point value is expressed in the content of the element as a pair
of numbers, separated by whitespace and punctuation (excluding decimal points
and sign characters).

      The value of the precision option takes precedence over
 that implied by the governing coordinate system name, including the
 value of the coordinate-system option. For example, if the
 governing coordinate system is "wgs84/double" and the precision
 option is "float", then the query uses single precision.

      Point values and boundary specifications of
boxes are given in degrees
relative to the WGS84 coordinate system.  Southern latitudes and Western
longitudes take negative values.  Longitudes will be wrapped to the range
(-180,+180) and latitudes will be clipped to the range (-90,+90).

      If the northern boundary of a box is south of the southern boundary, no
points will match. However, longitudes wrap around the globe, so that if
the western boundary is east of the eastern boundary,
then the box crosses the anti-meridian.

      Special handling occurs at the poles, as all longitudes exist at latitudes
+90 and -90.

      If neither "cached" nor "uncached" is present, it specifies "cached".
      "score-function=linear" means that values that are further away from
  the bounds will score higher. "score-function=reciprocal" means that values
  that are closer to the bounds will score higher. The functions are scaled
  appropriately for different types, so that in general the default slope factor
  will provide useful results. Using a slope factor greater than 1 gives distinct
  scores over a smaller range of values, and produces generally higher scores.
  Using a slope factor less than 1 gives distinct scores over a wider range of
  values, and produces generally lower scores.

### Examples

```xquery
(: create a document with test data :)
xdmp:document-insert("/points.json",
object-node {
  "item" : object-node {
    "point" : "15.35, 35.34"
  }
});

cts:search(doc("/points.json")//item,
  cts:json-property-geospatial-query("point", cts:box(10.0, 35.0, 20.0, 40.0)));
(:
  returns the following node:  {"point":"15.35, 35.34"}
:)

cts:search(doc("/points.json")//item,
  cts:json-property-geospatial-query("point", cts:box(12.0, 20.0, 20.0, 35.0)));
(:
  returns ()
:)
```

---

## cts:json-property-geospatial-query-options

Returns the options for the specified query.

### Signature

```xquery
cts:json-property-geospatial-query-options(
  $query as cts:json-property-geospatial-query
) as xs:string*
```

### Parameters

**`$query`**
A query.

### Returns

`xs:string*`

### Examples

```xquery
let $query := cts:json-property-geospatial-query("point",
   cts:box(10.1, 10.2, 20.1, 20.2))
return
cts:json-property-geospatial-query-options($query)

=> coordinate-system=wgs84
```

---

## cts:json-property-geospatial-query-property-name

Returns the json property names used to construct the specified query.

### Signature

```xquery
cts:json-property-geospatial-query-property-name(
  $query as cts:json-property-geospatial-query
) as xs:string*
```

### Parameters

**`$query`**
A query.

### Returns

`xs:string*`

### Examples

```xquery
let $query := cts:json-property-geospatial-query("point",
   cts:box(10.1, 10.2, 20.1, 20.2))
return
cts:json-property-geospatial-query-property-name($query)

=> "point"
```

---

## cts:json-property-geospatial-query-region

Returns the geographical regions
  with which the specified query was constructed.

### Signature

```xquery
cts:json-property-geospatial-query-region(
  $query as cts:json-property-geospatial-query
) as cts:region*
```

### Parameters

**`$query`**
A query.

### Returns

`cts:region*`

### Examples

```xquery
let $query := cts:json-property-geospatial-query("point",
   cts:box(10.1, 10.2, 20.1, 20.2))
return
cts:json-property-geospatial-query-region($query)

=> cts:box("[10.1, 10.2, 20.1, 20.2]")
```

---

## cts:json-property-geospatial-query-weight

Returns the weight with which the specified query was constructed.

### Signature

```xquery
cts:json-property-geospatial-query-weight(
  $query as cts:json-property-geospatial-query
) as xs:double
```

### Parameters

**`$query`**
A query.

### Returns

`xs:double`

### Examples

```xquery
let $query := cts:json-property-geospatial-query("point",
   cts:box(10.1, 10.2, 20.1, 20.2))
return
cts:json-property-geospatial-query-weight($query)

=> 1
```

---

## cts:json-property-pair-geospatial-query

Returns a query matching json properties by name which has
  specific property children representing latitude and longitude values for
  a point contained within the given geographic box, circle, or polygon, or
  equal to the given point.
  Points that lie
  between the southern boundary and the northern boundary of a box,
  travelling northwards,
  and between the western boundary and the eastern boundary of the box,
  travelling eastwards, will match.
  Points contained within the given radius of the center point of a circle will
  match, using the curved distance on the surface of the Earth.
  Points contained within the given polygon will match, using great circle arcs
  over a spherical model of the Earth as edges.  An error may result
  if the polygon is malformed in some way.
  Points equal to the a given point will match, taking into account the fact
  that longitudes converge at the poles.
  Using the geospatial query constructors requires a valid geospatial
  license key; without a valid license key, searches that include
  geospatial queries will throw an exception.

### Signature

```xquery
cts:json-property-pair-geospatial-query(
  $property-name as xs:string*,
  $latitude-property-names as xs:string*,
  $longitude-property-names as xs:string*,
  $regions as cts:region*,
  $options as xs:string*?,
  $weight as xs:double??
) as cts:json-property-pair-geospatial-query
```

### Parameters

**`$property-name`**
One or more parent property names to match.
    When multiple names are specified,
    the query matches if any name matches.

**`$latitude-property-names`**
One or more latitude property names to match.
    When multiple names are specified, the query matches
    if any name matches; however, only the first matching latitude
    child in any point instance will be checked.

**`$longitude-property-names`**
One or more longitude property names to match.
    When multiple names are specified, the query matches
    if any name matches; however, only the first matching longitude
    child in any point instance will be checked.

**`$regions`**
One or more geographic boxes, circles, polygons, or points. Where multiple
    regions are specified, the query matches if any region matches.

**`$options`** *(optional)*
Options to this query.  The default is ().
    Options include:
      
        
        "coordinate-system=string"
        Use the given coordinate system. Valid values are:
          
          wgs84The WGS84 coordinate system with degrees as the angular unit.
          wgs84/radiansThe WGS84 coordinate system with radians as the angular unit.
          wgs84/doubleThe WGS84 coordinate system at double precision with degrees as the angular unit.
          wgs84/radians/doubleThe WGS84 coordinate system at double precision with radians as the angular unit.
          etrs89The ETRS89 coordinate system.
          etrs89/doubleThe ETRS89 coordinate system at double precision.
          rawThe raw (unmapped) coordinate system.
          raw/doubleThe raw coordinate system at double precision.
          
          
          "precision=value"
          Use the coordinate system at the given precision. Allowed values:
          float and double.
        "units=value"
        Measure distance and the radii of circles in the specified units.
         Allowed values: miles (default), km,
         feet, meters.
        "boundaries-included"
        Points on boxes', circles', and polygons' boundaries are counted
        as matching.  This is the default.
        "boundaries-excluded"
        Points on boxes', circles', and polygons' boundaries are not
  counted as matching.
        "boundaries-latitude-excluded"
        Points on boxes' latitude boundaries are not counted as
  matching.
        "boundaries-longitude-excluded"
        Points on boxes' longitude boundaries are not counted as
  matching.
        "boundaries-south-excluded"
        Points on the boxes' southern boundaries are not counted as
  matching.
        "boundaries-west-excluded"
        Points on the boxes' western boundaries are not counted as
  matching.
        "boundaries-north-excluded"
        Points on the boxes' northern boundaries are not counted as
  matching.
        "boundaries-east-excluded"
        Points on the boxes' eastern boundaries are not counted as
  matching.
        "boundaries-circle-excluded"
        Points on circles' boundary are not counted as matching.
        "boundaries-endpoints-excluded"
        Points on linestrings' boundary (the endpoints) are not counted as matching.
        "cached"
        Cache the results of this query in the list cache.
        "uncached"
        Do not cache the results of this query in the list cache.
        "score-function=function"
        Use the selected scoring function. The score function may be:
          
          linearUse a linear function of the difference between the
          specified query value and the matching value in the index to calculate
          a score for this range query.
          reciprocalUse a reciprocal function of the difference
          between the specified query value and the matching value in the
          index to calculate a score for this range query.
          zeroThis range query does not contribute to the
          score. This is the default.
          
        
        "slope-factor=number"
        Apply the given number as a scaling factor to the slope of the
        scoring function. The default is 1.0.
        "synonym"
        Specifies that all of the terms in the $regions parameter are
        considered synonyms for scoring purposes.  The result is that
        occurrences of more than one of the synonyms are scored as if
        there are more occurrence of the same term (as opposed to
        having a separate term that contributes to score).

**`$weight`** *(optional)*
A weight for this query.  The default is 1.0.

### Returns

`cts:json-property-pair-geospatial-query`

### Usage Notes

Point values and boundary specifications of boxes are given in degrees
relative to the WGS84 coordinate system.  Southern latitudes and Western
longitudes take negative values.  Longitudes will be wrapped to the range
(-180,+180) and latitudes will be clipped to the range (-90,+90).

      The value of the precision option takes precedence over
 that implied by the governing coordinate system name, including the
 value of the coordinate-system option. For example, if the
 governing coordinate system is "wgs84/double" and the precision
 option is "float", then the query uses single precision.

      If the northern boundary of a box is south of the southern boundary, no
points will  match. However, longitudes wrap around the globe, so that if
the western boundary is east of the eastern boundary,
then the box crosses the anti-meridian.

      Special handling occurs at the poles, as all longitudes exist at latitudes
+90 and -90.

      If neither "cached" nor "uncached" is present, it specifies "cached".
      "score-function=linear" means that values that are further away from
  the bounds will score higher. "score-function=reciprocal" means that values
  that are closer to the bounds will score higher. The functions are scaled
  appropriately for different types, so that in general the default slope factor
  will provide useful results. Using a slope factor greater than 1 gives
  distinct scores over a smaller range of values, and produces generally
  higher scores.  Using a slope factor less than 1 gives distinct scores
  over a wider range of values, and produces generally lower scores.

### Examples

```xquery
(: create a document with test data :)
xdmp:document-insert("/points.json",
object-node {
  "item" : object-node {
    "point" : object-node {
       "lat" : 15.35,
       "long" : 35.34
    }
  }
});

cts:search(doc("/points.json")//item,
  cts:json-property-pair-geospatial-query("point",
    "lat", "long", cts:box(10.0, 35.0, 20.0, 40.0)));
(:
  returns the following node:
:)

cts:search(doc("/points.json")//item,
  cts:json-property-pair-geospatial-query("point",
    "lat", "long", cts:box(12.0, 20.0, 20.0, 35.0)))
(:
  returns ()
:)
```

---

## cts:json-property-pair-geospatial-query-latitude-name

Returns the property names used to construct the specified query.

### Signature

```xquery
cts:json-property-pair-geospatial-query-latitude-name(
  $query as cts:json-property-pair-geospatial-query
) as xs:string*
```

### Parameters

**`$query`**
A query.

### Returns

`xs:string*`

### Examples

```xquery
let $query := cts:json-property-pair-geospatial-query("point",
     "lat", "long", cts:box(10.1, 10.2, 20.1, 20.2))
return cts:json-property-pair-geospatial-query-latitude-name($query)

=> "lat"
```

---

## cts:json-property-pair-geospatial-query-longitude-name

Returns the property names used to construct the specified query.

### Signature

```xquery
cts:json-property-pair-geospatial-query-longitude-name(
  $query as cts:json-property-pair-geospatial-query
) as xs:string*
```

### Parameters

**`$query`**
A query.

### Returns

`xs:string*`

### Examples

```xquery
let $query := cts:json-property-pair-geospatial-query("point",
     "lat", "long", cts:box(10.1, 10.2, 20.1, 20.2))
return cts:json-property-pair-geospatial-query-longitude-name($query)

=> "long"
```

---

## cts:json-property-pair-geospatial-query-options

Returns the options for the specified query.

### Signature

```xquery
cts:json-property-pair-geospatial-query-options(
  $query as cts:json-property-pair-geospatial-query
) as xs:string*
```

### Parameters

**`$query`**
A query.

### Returns

`xs:string*`

### Examples

```xquery
let $query := cts:json-property-pair-geospatial-query("point",
     "lat", "long", cts:box(10.1, 10.2, 20.1, 20.2))
return cts:json-property-pair-geospatial-query-options($query)

=> coordinate-system=wgs84
```

---

## cts:json-property-pair-geospatial-query-property-name

Returns the property names used to construct the specified query.

### Signature

```xquery
cts:json-property-pair-geospatial-query-property-name(
  $query as cts:json-property-pair-geospatial-query
) as xs:string*
```

### Parameters

**`$query`**
A query.

### Returns

`xs:string*`

### Examples

```xquery
let $query := cts:json-property-pair-geospatial-query("point",
     "lat", "long", cts:box(10.1, 10.2, 20.1, 20.2))
return cts:json-property-pair-geospatial-query-property-name($query)

=> "point"
```

---

## cts:json-property-pair-geospatial-query-region

Returns the geographical regions with which the specified query was
  constructed.

### Signature

```xquery
cts:json-property-pair-geospatial-query-region(
  $query as cts:json-property-pair-geospatial-query
) as cts:region*
```

### Parameters

**`$query`**
A query.

### Returns

`cts:region*`

### Examples

```xquery
let $query := cts:json-property-pair-geospatial-query("point",
     "lat", "long", cts:box(10.1, 10.2, 20.1, 20.2))
return cts:json-property-pair-geospatial-query-region($query)

=> cts:box("[10.1, 10.2, 20.1, 20.2]")
```

---

## cts:json-property-pair-geospatial-query-weight

Returns the weight with which the specified query was constructed.

### Signature

```xquery
cts:json-property-pair-geospatial-query-weight(
  $query as cts:json-property-pair-geospatial-query
) as xs:double
```

### Parameters

**`$query`**
A query.

### Returns

`xs:double`

### Examples

```xquery
let $query := cts:json-property-pair-geospatial-query("point",
     "lat", "long", cts:box(10.1, 10.2, 20.1, 20.2))
return cts:json-property-pair-geospatial-query-weight($query)

=> 1
```

---

## cts:json-property-range-query

Returns a cts:query matching JSON properties by name with a
  range-index entry equal to a given value.  Searches with the
  cts:json-property-range-query
  constructor require a property range index on the specified names;
  if there is no range index configured, then an exception is thrown.

### Signature

```xquery
cts:json-property-range-query(
  $property-name as xs:string*,
  $operator as xs:string,
  $value as xs:anyAtomicType*,
  $options as xs:string*?,
  $weight as xs:double??
) as cts:json-property-range-query
```

### Parameters

**`$property-name`**
One or more property name to match.
    When multiple names are specified,
    the query matches if any name matches.

**`$operator`**
A comparison operator.
    
      Operators include:
      
        "<"
        Match range index values less than $value.
        "<="
        Match range index values less than or equal to $value.
        ">"
        Match range index values greater than $value.
        ">="
        Match range index values greater than or equal to $value.
        "="
        Match range index values equal to $value.
        "!="
        Match range index values not equal to $value.

**`$value`**
One or more property values to match.
    When multiple values are specified,
    the query matches if any value matches. The value must be a type for
    which there is a range index defined.

**`$options`** *(optional)*
Options to this query.  The default is ().
    
      Options include:
      
        "collation=URI"
        Use the range index with the collation specified by
        URI.  If not specified, then the default collation
        from the query is used. If a range index with the specified
        collation does not exist, an error is thrown.
        "cached"
        Cache the results of this query in the list cache.
        "uncached"
        Do not cache the results of this query in the list cache.
        "cached-incremental"
        When querying on a short date or dateTime range, break the
        query into sub-queries on smaller ranges, and then cache the
        results of each.  See the Usage Notes for details.
        "min-occurs=number"
        Specifies the minimum number of occurrences required. If
        fewer that this number of words occur, the fragment does not match.
        The default is 1.
        "max-occurs=number"
        Specifies the maximum number of occurrences required.  If
        more than this number of words occur, the fragment does not match.
        The default is unbounded.
        "score-function=function"
        Use the selected scoring function. The score function may be:
          
          linearUse a linear function of the difference between the
          specified query value and the matching value in the index to calculate
          a score for this range query.
          reciprocalUse a reciprocal function of the difference
          between the specified query value and the matching value in the
          index to calculate a score for this range query.
          zeroThis range query does not contribute to the
          score. This is the default.
          
        
        "slope-factor=number"
        Apply the given number as a scaling factor to the slope of the
        scoring function. The default is 1.0.
        "synonym"
        Specifies that all of the terms in the $value parameter are
        considered synonyms for scoring purposes.  The result is that
        occurrences of more than one of the synonyms are scored as if
        there are more occurrences of the same term (as opposed to
        having a separate term that contributes to score).

**`$weight`** *(optional)*
A weight for this query.  The default is 1.0.

### Returns

`cts:json-property-range-query`

### Usage Notes

If you want to constrain on a range of values, you can combine multiple
  cts:json-property-range-query constructors together
  with cts:and-query or any of the other composable
  cts:query constructors.
      If neither "cached" nor "uncached" is present, it specifies "cached".
      The "cached-incremental" option can improve performance if you
   repeatedly perform range queries on date or dateTime values over a
   short range that does not vary widely over short period of time. To
   benefit, the operator should remain the same "direction" (<,<=, or >,>=) 
   across calls, the bounding date or dateTime changes slightly across calls,
   and the query runs very frequently (multiple times per minute).
   Note that using this options creates significantly more cached queries
   than the "cached" option.
  
      The "cached-incremental" option has the following restrictions and
   interactions: The "min-occurs" and "max-occurs" options will be ignored
   if you use "cached-incremental" in unfiltered search. You can only use
   "score-function=zero" with "cached-incremental". The "cached-incremental"
   option behaves like "cached" if you are not querying date or dateTime values.
  
      
    Negative "min-occurs" or "max-occurs" values will be treated as 0 and
    non-integral values will be rounded down.  An error will be raised if
    the "min-occurs" value is greater than the "max-occurs" value.
  
      "score-function=linear" means that values that are further away from
  the bounds will score higher. "score-function=reciprocal" means that values
  that are closer to the bounds will score higher. The functions are scaled
  appropriately for different types, so that in general the default slope factor
  will provide useful results. Using a slope factor greater than 1 gives distinct
  scores over a smaller range of values, and produces generally higher scores.
  Using a slope factor less than 1 gives distinct scores over a wider range of
  values, and produces generally lower scores.
  
      For queries against a dateTime index, when $value is an xs:dayTimeDuration
  or xs:yearMonthDuration, the query is executed as an age query. $value is
  subtracted from fn:current-dateTime() to create an xs:dateTime used in the query.
  If there is more than one item in $value, they must all be the same type.

### Examples

```xquery
(: Suppose there are three documents in the database :)

1.json:
{
  "entry" : {
    "date" : "2007-01-01",
    "info" : "Some information."
  }
}

2.json:
{
  "entry" : {
    "date" : "2006-06-23",
    "info" : "Some other information."
  }
}

3.json:
{
  "entry" : {
    "date" : "1971-12-23",
    "info" : "Some different information."
  }
}

(:
   requires a property (range) index of
   type xs:date on "date"
:)
cts:search(fn:collection(),
  cts:json-property-range-query("date", "<=",
      xs:date("2000-01-01")))
(:
  returns the third document
:)
```

---

## cts:json-property-range-query-operator

Returns the operator used to construct the specified query.

### Signature

```xquery
cts:json-property-range-query-operator(
  $query as cts:json-property-range-query
) as xs:string
```

### Parameters

**`$query`**
A query.

### Returns

`xs:string`

### Examples

```xquery
let $query := cts:json-property-range-query("date", "<=",
      xs:date("2000-01-01"))
return
cts:json-property-range-query-operator($query)
  => "<="
```

---

## cts:json-property-range-query-options

Returns the options for the specified query.

### Signature

```xquery
cts:json-property-range-query-options(
  $query as cts:json-property-range-query
) as xs:string*
```

### Parameters

**`$query`**
A query.

### Returns

`xs:string*`

### Examples

```xquery
let $query := cts:json-property-range-query("date", "<=",
      xs:date("2000-01-01"))
return
cts:json-property-range-query-options($query)
  => ()
```

---

## cts:json-property-range-query-property-name

Returns the JSON property name used to construct the specified query.

### Signature

```xquery
cts:json-property-range-query-property-name(
  $query as cts:json-property-range-query
) as xs:string*
```

### Parameters

**`$query`**
A query.

### Returns

`xs:string*`

### Examples

```xquery
let $query := cts:json-property-range-query("date", "<=",
      xs:date("2000-01-01"))
return
cts:json-property-range-query-property-name($query)
  => "date"
```

---

## cts:json-property-range-query-value

Returns the value used to construct the specified query.

### Signature

```xquery
cts:json-property-range-query-value(
  $query as cts:json-property-range-query
) as xs:anyAtomicType*
```

### Parameters

**`$query`**
A query.

### Returns

`xs:anyAtomicType*`

### Examples

```xquery
let $query := cts:json-property-range-query("date", "<=",
      xs:date("2000-01-01"))
return
cts:json-property-range-query-value($query)
  => 2000-01-01
```

---

## cts:json-property-range-query-weight

Returns the weight with which the specified query was constructed.

### Signature

```xquery
cts:json-property-range-query-weight(
  $query as cts:json-property-range-query
) as xs:double
```

### Parameters

**`$query`**
A query.

### Returns

`xs:double`

### Examples

```xquery
let $query := cts:json-property-range-query("date", "<=",
      xs:date("2000-01-01"))
return
cts:json-property-range-query-weight($query)
  => 1
```

---

## cts:json-property-scope-query

Returns a cts:query matching JSON properties by name
  with the content constrained by the given cts:query in the
  second parameter.
  Searches for matches in the specified property and all of its descendants.

### Signature

```xquery
cts:json-property-scope-query(
  $property-name as xs:string*,
  $query as cts:query
) as cts:json-property-scope-query
```

### Parameters

**`$property-name`**
One or more property names to match.
    When multiple names are specified,
    the query matches if any name matches.

**`$query`**
A query for the property to match.  If a string
   is entered, the string is treated as a cts:word-query of the
   specified string.

### Returns

`cts:json-property-scope-query`

### Usage Notes

Enabling both the word position and element word position indexes will
  speed up query performance for many queries that use
  cts:json-property-scope-query. The  position indexes enable MarkLogic
  Server to eliminate many false-positive results, which can reduce
  disk I/O and processing, thereby speeding the performance of many queries.
  The amount of benefit will vary depending on your data.

### Examples

```xquery
(:
Given a database that has a JSON document as follows:
{"a":"aa","new":["array","content"],"b":["aa","bb"]}
:)
  cts:search(doc(),
    cts:json-property-scope-query(
      "a",
      "aa"))

  => .. relevance-ordered sequence of JSON documents (including
     the above document) with a property named "a" and some text value 
     anywhere within this property that includes the word or token "aa".
```

---

## cts:json-property-scope-query-property-name

Returns the JSON property name used to construct the specified query.

### Signature

```xquery
cts:json-property-scope-query-property-name(
  $query as cts:json-property-scope-query
) as xs:string*
```

### Parameters

**`$query`**
A query.

### Returns

`xs:string*`

### Examples

```xquery
let $query := cts:json-property-scope-query(
              "function",
              "MarkLogic Corporation")
return cts:json-property-scope-query-property-name($query)

  => "function"
```

---

## cts:json-property-scope-query-query

Returns the query used to construct the property scope query.

### Signature

```xquery
cts:json-property-scope-query-query(
  $query as cts:json-property-scope-query
) as cts:query
```

### Parameters

**`$query`**
A query.

### Returns

`cts:query`

### Examples

```xquery
let $query := cts:json-property-scope-query(
                 "help",
                 cts:word-query("wanted"))
return cts:json-property-scope-query-query($query)

  => cts:word-query("wanted", ("lang=en"), 1)
```

---

## cts:json-property-value-query

Returns a query matching JSON properties by name with value equal the given
  value. For arrays, the query matches if the value of any elements in the array
  matches the given value.

### Signature

```xquery
cts:json-property-value-query(
  $property-name as xs:string*,
  $value as xs:anyAtomicType*,
  $options as xs:string*?,
  $weight as xs:double??
) as cts:json-property-value-query
```

### Parameters

**`$property-name`**
One or more property names to match.
    When multiple names are specified,
    the query matches if any name matches.

**`$value`**
One or more property values to match. When multiple values are specified,
    the query matches if any value matches. The values can be strings, numbers
    or booleans to match correspondingly typed nodes.
    If the value is the empty sequence, the query matches null.

**`$options`** *(optional)*
Options to this query.  The default is ().
    
      Options include:
      
        "case-sensitive"
        A case-sensitive query.
        "case-insensitive"
        A case-insensitive query.
        "diacritic-sensitive"
        A diacritic-sensitive query.
        "diacritic-insensitive"
        A diacritic-insensitive query.
        "punctuation-sensitive"
        A punctuation-sensitive query.
        "punctuation-insensitive"
        A punctuation-insensitive query.
        "whitespace-sensitive"
        A whitespace-sensitive query.
        "whitespace-insensitive"
        A whitespace-insensitive query.
        "stemmed"
        A stemmed query.
        "unstemmed"
        An unstemmed query.
        "wildcarded"
        A wildcarded query.
        "unwildcarded"
        An unwildcarded query.
        "exact"
        An exact match query. Shorthand for "case-sensitive",
        "diacritic-sensitive", "punctuation-sensitive",
        "whitespace-sensitive", "unstemmed", and "unwildcarded".
        
        "lang=iso639code"
        Specifies the language of the query. The iso639code
            code portion is case-insensitive, and uses the languages
            specified by
           ISO 639.
            The default is specified in the database configuration.
        "min-occurs=number"
        Specifies the minimum number of occurrences required. If
        fewer that this number of words occur, the fragment does not match.
        The default is 1.
        "max-occurs=number"
        Specifies the maximum number of occurrences required.  If
        more than this number of words occur, the fragment does not match.
        The default is unbounded.
        "synonym"
        Specifies that all of the terms in the $text parameter are
        considered synonyms for scoring purposes.  The result is that
        occurrences of more than one of the synonyms are scored as if
        there are more occurrences of the same term (as opposed to
        having a separate term that contributes to score).

**`$weight`** *(optional)*
A weight for this query.
    Higher weights move search results up in the relevance
    order.  The default is 1.0. The
    weight should be between 64 and -16.
    Weights greater than 64 will have the same effect as a
    weight of 64.
    Weights less than the absolute value of 0.0625 (between -0.0625 and
    0.0625) are rounded to 0, which means that they do not contribute to the
    score.

### Returns

`cts:json-property-value-query`

### Usage Notes

If neither "case-sensitive" nor "case-insensitive"
    is present, $text is used to determine case sensitivity.
    If $text contains no uppercase, it specifies "case-insensitive".
    If $text contains uppercase, it specifies "case-sensitive".
  
      
    If neither "diacritic-sensitive" nor "diacritic-insensitive"
    is present, $text is used to determine diacritic sensitivity.
    If $text contains no diacritics, it specifies "diacritic-insensitive".
    If $text contains diacritics, it specifies "diacritic-sensitive".
  
      
    If neither "punctuation-sensitive" nor "punctuation-insensitive"
    is present, $text is used to determine punctuation sensitivity.
    If $text contains no punctuation, it specifies "punctuation-insensitive".
    If $text contains punctuation, it specifies "punctuation-sensitive".
  
      
    If neither "whitespace-sensitive" nor "whitespace-insensitive"
    is present, the query is "whitespace-insensitive".
  
      
    If neither "wildcarded" nor "unwildcarded"
    is present, the database configuration and $text determine wildcarding.
    If the database has any wildcard indexes enabled ("three character
    searches", "two character searches", "one character searches",  or
    "trailing wildcard searches") and if $text contains either of the
    wildcard characters '?' or '*', it specifies "wildcarded".
    Otherwise it specifies "unwildcarded".
  
      
    If neither "stemmed" nor "unstemmed"
    is present, the database configuration determines stemming.
    If the database has "stemmed searches" enabled, it specifies "stemmed".
    Otherwise it specifies "unstemmed".
    If the query is a wildcarded query and also a phrase query
    (contains two or more terms), the wildcard terms in the query
    are unstemmed.
  
      
    When you use the "exact" option, you should also enable
    "fast case sensitive searches" and "fast diacritic sensitive searches"
    in your database configuration.
  
      
    Negative "min-occurs" or "max-occurs" values will be treated as 0 and
    non-integral values will be rounded down.  An error will be raised if
    the "min-occurs" value is greater than the "max-occurs" value.
  
       Note that the text content for the value in a
  cts:json-property-value-query is treated the same as a phrase in a
  cts:word-query, where the phrase is the property value.
  Therefore, any wildcard and/or stemming rules are treated like a phrase.
  For example, if you have an property value of "hello friend" with wildcarding
  enabled for a query, a cts:json-property-value-query for "he*" will
  not match because the wildcard matches do not span word boundaries, but a
  cts:json-property-value-query for "hello *" will match.  A search
  for "*" will match, because a "*" wildcard by itself is defined to match
  the value.  Similarly, stemming rules are applied to each term, so a
  search for "hello friends" would match when stemming is enabled for the query
  because "friends" matches "friend". For an example, see the
  fourth example below.
       Similarly, because a "*" wildcard by itself is defined to match
  the value, the following query will match any property with the
  name my-property, regardless of the wildcard indexes enabled in
  the database configuration:
  cts:json-property-value-query("my-property", "*", "wildcarded")

### Examples

#### Example 1

```xquery
cts:search(//module,
    cts:json-property-value-query(
      "function",
      "MarkLogic Corporation"))

  => .. relevance-ordered sequence of 'module' property
  ancestors of 'function' properties whose text
  content equals 'MarkLogic Corporation'.
```

#### Example 2

```xquery
cts:search(//module,
    cts:json-property-value-query(
      "function",
      "MarkLogic Corporation", "case-insensitive"))

  => .. relevance-ordered sequence of 'module' property
  ancestors of 'function' properties whose text
  content equals 'MarkLogic Corporation', or any other
  case-shift like 'MARKLOGIC CorpoRation'.
```

#### Example 3

```xquery
cts:search(//module,
    cts:and-query((
      cts:json-property-value-query(
        "function",
        "MarkLogic Corporation",
        "punctuation-insensitive", 0.5),
      cts:json-property-value-query(
        "title",
        "Word Query"))))
  => .. relevance-ordered sequence of 'module' properties
  which are ancestors of both:
  (a) 'function' properties with text content equal to
      'MarkLogic Corporation', ignoring embedded
      punctuation,
  AND
  (b) 'title' properties with text content equal to
      'Word Query', with the results of the first sub-query
      query given weight 0.5, and the results of the second
      sub-query given the default weight 1.0.  As a result,
      the title phrase 'Word Query' counts more heavily
      towards the relevance score.
```

#### Example 4

```xquery
(: for a document foo.json with content like {"foo" : 1} :)
cts:contains(fn:doc("foo.json"), cts:json-property-value-query("foo",1))

=> true
```

---

## cts:json-property-value-query-options

Returns the options for the specified query.

### Signature

```xquery
cts:json-property-value-query-options(
  $query as cts:json-property-value-query
) as xs:string*
```

### Parameters

**`$query`**
A query.

### Returns

`xs:string*`

### Examples

```xquery
let $query := cts:json-property-value-query(
              "function",
              "MarkLogic Corporation")
return cts:json-property-value-query-options($query)

  =>  "lang=en"
```

---

## cts:json-property-value-query-property-name

Returns the JSON property name used to construct the specified query.

### Signature

```xquery
cts:json-property-value-query-property-name(
  $query as cts:json-property-value-query
) as xs:string*
```

### Parameters

**`$query`**
A query.

### Returns

`xs:string*`

### Examples

```xquery
let $query := cts:json-property-value-query(
              "function",
              "MarkLogic Corporation")
return cts:json-property-value-query-property-name($query)

  => "function"
```

---

## cts:json-property-value-query-text

Returns the text used to construct the specified query.

### Signature

```xquery
cts:json-property-value-query-text(
  $query as cts:json-property-value-query
) as xs:string*
```

### Parameters

**`$query`**
A query.

### Returns

`xs:string*`

### Examples

```xquery
let $query := cts:json-property-value-query(
              "function",
              "MarkLogic Corporation")
return cts:json-property-value-query-text($query)

  => "MarkLogic Corporation"
```

---

## cts:json-property-value-query-value

Returns the value used to construct the specified query.

### Signature

```xquery
cts:json-property-value-query-value(
  $query as cts:json-property-value-query
) as xs:anyAtomicType*
```

### Parameters

**`$query`**
A query.

### Returns

`xs:anyAtomicType*`

### Examples

```xquery
let $query := cts:json-property-value-query(
              "function",
              "MarkLogic Corporation")
return cts:json-property-value-query-value($query)

  =>  "MarkLogic Corporation"
```

---

## cts:json-property-value-query-weight

Returns the weight with which the specified query was constructed.

### Signature

```xquery
cts:json-property-value-query-weight(
  $query as cts:json-property-value-query
) as xs:double
```

### Parameters

**`$query`**
A query.

### Returns

`xs:double`

### Examples

```xquery
let $query := cts:json-property-value-query(
              "function",
              "MarkLogic Corporation")
return cts:json-property-value-query-weight($query)

  =>  1
```

---

## cts:json-property-word-query

Returns a query matching JSON properties by name with text content containing
  a given phrase.  Searches only through immediate text node children of the
  specified property.

### Signature

```xquery
cts:json-property-word-query(
  $property-name as xs:string*,
  $text as xs:string*,
  $options as xs:string*?,
  $weight as xs:double??
) as cts:json-property-word-query
```

### Parameters

**`$property-name`**
One or more JSON property names to match.
    When multiple names are specified,
    the query matches if any name matches.

**`$text`**
Some words or phrases to match.
    When multiple strings are specified,
    the query matches if any string matches.

**`$options`** *(optional)*
Options to this query.  The default is ().
    
      Options include:
      
        "case-sensitive"
        A case-sensitive query.
        "case-insensitive"
        A case-insensitive query.
        "diacritic-sensitive"
        A diacritic-sensitive query.
        "diacritic-insensitive"
        A diacritic-insensitive query.
        "punctuation-sensitive"
        A punctuation-sensitive query.
        "punctuation-insensitive"
        A punctuation-insensitive query.
        "whitespace-sensitive"
        A whitespace-sensitive query.
        "whitespace-insensitive"
        A whitespace-insensitive query.
        "stemmed"
        A stemmed query.
        "unstemmed"
        An unstemmed query.
        "wildcarded"
        A wildcarded query.
        "unwildcarded"
        An unwildcarded query.
        "exact"
        An exact match query. Shorthand for "case-sensitive",
        "diacritic-sensitive", "punctuation-sensitive",
        "whitespace-sensitive", "unstemmed", and "unwildcarded".
        
        "lang=iso639code"
        Specifies the language of the query. The iso639code
            code portion is case-insensitive, and uses the languages
            specified by
           ISO 639.
            The default is specified in the database configuration.
        "distance-weight=number"
        A weight applied based on the minimum distance between matches
        of this query.  Higher weights add to the importance of
        proximity (as opposed to term matches) when the relevance order is
        calculated.
        The default value is 0.0 (no impact of proximity). The
        weight should be between 64 and -16.
        Weights greater than 64 will have the same effect as a
        weight of 64.
        This parameter has no effect if the word positions
        index is not enabled.  This parameter has no effect on searches that
        use score-simple, score-random, or score-zero (because those scoring
        algorithms do not consider term frequency, proximity is irrelevant).
        
        "min-occurs=number"
        Specifies the minimum number of occurrences required. If
        fewer that this number of words occur, the fragment does not match.
        The default is 1.
        "max-occurs=number"
        Specifies the maximum number of occurrences required.  If
        more than this number of words occur, the fragment does not match.
        The default is unbounded.
        "synonym"
        Specifies that all of the terms in the $text parameter are
        considered synonyms for scoring purposes.  The result is that
        occurrences of more than one of the synonyms are scored as if
        there are more occurrences of the same term (as opposed to
        having a separate term that contributes to score). 
  "lexicon-expand=value"
  The value is one of full,
  prefix-postfix, off, or
  heuristic (the default is heuristic).
  An option with a value of lexicon-expand=full
  specifies that wildcards are resolved by expanding the pattern to
  words in a lexicon (if there is one available), and turning into a
        series of cts:word-queries, even if this takes a long
  time to evaluate.
  An option with a value of lexicon-expand=prefix-postfix
  specifies that wildcards are resolved by expanding the pattern to the
  pre- and postfixes of the words in the word lexicon (if there is one),
  and turning the query into a series of character queries, even if it
  takes a long time to evaluate.
  An option with a value of lexicon-expand=off
  specifies that wildcards are only resolved by looking up character
  patterns in the search pattern index, not in the lexicon.
  An option with a value of lexicon-expand=heuristic,
  which is the default, specifies that wildcards are resolved by using
  a series of internal rules, such as estimating the number of lexicon
  entries that need to be scanned, seeing if the estimate crosses
  certain thresholds, and (if appropriate), using another way besides
  lexicon expansion to resolve the query.
        
       "lexicon-expansion-limit=number"
        Specifies the limit for lexicon expansion. This puts a restriction
  on the number of lexicon expansions that can be performed. If the limit is
  exceeded, the server may raise an error depending on whether the "limit-check"
  option is set. The default value for this option will be 4096.
        
        "limit-check"
        Specifies that an error will be raised if the lexicon expansion
  exceeds the specified limit.
        "no-limit-check"
        Specifies that error will not be raised if the lexicon expansion
  exceeds the specified limit. The server will try to resolve the wildcard.
  "no-limit-check" is default, if neither "limit-check" nor "no-limit-check" is explicitly
  specified.

**`$weight`** *(optional)*
A weight for this query.
    Higher weights move search results up in the relevance
    order.  The default is 1.0. The
    weight should be between 64 and -16.
    Weights greater than 64 will have the same effect as a
    weight of 64.
    Weights less than the absolute value of 0.0625 (between -0.0625 and
    0.0625) are rounded to 0, which means that they do not contribute to the
    score.

### Returns

`cts:json-property-word-query`

### Usage Notes

If neither "case-sensitive" nor "case-insensitive"
    is present, $text is used to determine case sensitivity.
    If $text contains no uppercase, it specifies "case-insensitive".
    If $text contains uppercase, it specifies "case-sensitive".
  
      
    If neither "diacritic-sensitive" nor "diacritic-insensitive"
    is present, $text is used to determine diacritic sensitivity.
    If $text contains no diacritics, it specifies "diacritic-insensitive".
    If $text contains diacritics, it specifies "diacritic-sensitive".
  
      
    If neither "punctuation-sensitive" nor "punctuation-insensitive"
    is present, $text is used to determine punctuation sensitivity.
    If $text contains no punctuation, it specifies "punctuation-insensitive".
    If $text contains punctuation, it specifies "punctuation-sensitive".
  
      
    If neither "whitespace-sensitive" nor "whitespace-insensitive"
    is present, the query is "whitespace-insensitive".
  
      
    If neither "wildcarded" nor "unwildcarded"
    is present, the database configuration and $text determine wildcarding.
    If the database has any wildcard indexes enabled ("three character
    searches", "two character searches", "one character searches",  or
    "trailing wildcard searches") and if $text contains either of the
    wildcard characters '?' or '*', it specifies "wildcarded".
    Otherwise it specifies "unwildcarded".
  
      
    If neither "stemmed" nor "unstemmed"
    is present, the database configuration determines stemming.
    If the database has "stemmed searches" enabled, it specifies "stemmed".
    Otherwise it specifies "unstemmed".
    If the query is a wildcarded query and also a phrase query
    (contains two or more terms), the wildcard terms in the query
    are unstemmed.
  
      
    Negative "min-occurs" or "max-occurs" values will be treated as 0 and
    non-integral values will be rounded down.  An error will be raised if
    the "min-occurs" value is greater than the "max-occurs" value.
  
      Relevance adjustment for the "distance-weight" option depends on
  the closest proximity of any two matches of the query.  For example,
  
  cts:json-property-word-query(xs:QName("p"),("dog","cat"),("distance-weight=10"))
  
  will adjust relevance based on the distance between the closest pair of
  matches of either "dog" or "cat" within a property named "p"
  (the pair may consist only of matches of
  "dog", only of matches of "cat", or a match of "dog" and a match of "cat").

### Examples

#### Example 1

```xquery
cts:search(//module,
    cts:json-property-word-query(
      "function",
      "MarkLogic Corporation"))

  => .. relevance-ordered sequence of 'module' properties
  ancestors (or self) of properties with name 'function'
  and text content containing the phrase 'MarkLogic
  Corporation'.
```

#### Example 2

```xquery
cts:search(//module,
    cts:json-property-word-query(
      "function",
      "MarkLogic Corporation", "case-sensitive"))

  => .. relevance-ordered sequence of 'module' properties
  ancestors (or self) of properties with name 'function'
  and text content containing the phrase 'MarkLogic
  Corporation',
  or any other case-shift, like 'MarkLogic Corporation'.
```

#### Example 3

```xquery
cts:search(//module,
    cts:and-query((
      cts:json-property-word-query(
        "function",
        "MarkLogic Corporation",
        ("case-insensitive", "punctuation-insensitive"), 0.5),
      cts:json-property-word-query(
        "title",
        "faster"))))

  => .. relevance-ordered sequence of 'module' properties
  ancestors (or self) of both:
  (a) 'function' properties with text content containing
      the phrase 'MarkLogic Corporation', ignoring embedded
      punctuation,
  AND
  (b) 'title' properties containing the word 'faster',
      with the results of the first sub-query query given
      weight 0.5, and the results of the second sub-query
      given the default weight 1.0.  As a result, the title
      term 'faster' counts more towards the relevance
      score.
```

---

## cts:json-property-word-query-options

Returns the options for the specified query.

### Signature

```xquery
cts:json-property-word-query-options(
  $query as cts:json-property-word-query
) as xs:string*
```

### Parameters

**`$query`**
A query.

### Returns

`xs:string*`

### Examples

```xquery
let $query := cts:json-property-word-query("prop", "choice of law")
  return
  cts:json-property-word-query-options($query)
  => "lang=en"
```

---

## cts:json-property-word-query-property-name

Returns the name used to construct the specified query.

### Signature

```xquery
cts:json-property-word-query-property-name(
  $query as cts:json-property-word-query
) as xs:string*
```

### Parameters

**`$query`**
A query.

### Returns

`xs:string*`

### Examples

```xquery
let $query := cts:json-property-word-query("prop", "choice of law")
  return
  cts:json-property-word-query-property-name($query)
  => "prop"
```

---

## cts:json-property-word-query-text

Returns the text used to construct the specified query.

### Signature

```xquery
cts:json-property-word-query-text(
  $query as cts:json-property-word-query
) as xs:string*
```

### Parameters

**`$query`**
A query.

### Returns

`xs:string*`

### Examples

```xquery
let $query := cts:json-property-word-query("prop", "choice of law")
  return
  cts:json-property-word-query-text($query)
  => "choice of law"
```

---

## cts:json-property-word-query-weight

Returns the weight with which the specified query was constructed.

### Signature

```xquery
cts:json-property-word-query-weight(
  $query as cts:json-property-word-query
) as xs:double
```

### Parameters

**`$query`**
A query.

### Returns

`xs:double`

### Examples

```xquery
let $query := cts:json-property-word-query("prop", "choice of law")
  return
  cts:json-property-word-query-weight($query)
  => 1
```

---

## cts:locks-fragment-query

Returns a query that matches all documents where $query matches
  document-locks.  When searching documents or document-properties,
  cts:locks-fragment-query provides a convenient way to
  additionally constrain the search against document-locks fragments.

### Signature

```xquery
cts:locks-fragment-query(
  $query as cts:query
) as cts:locks-fragment-query
```

### Parameters

**`$query`**
A query to be matched against the locks fragment.

### Returns

`cts:locks-fragment-query`

### Examples

```xquery
cts:search(
  fn:collection(),
    cts:locks-fragment-query(cts:word-query("12345")))

=>  All documents that have locks containing the word 12345.
```

---

## cts:locks-fragment-query-query

Returns the query used to construct the specified query.

### Signature

```xquery
cts:locks-fragment-query-query(
  $query as cts:locks-fragment-query
) as cts:query
```

### Parameters

**`$query`**
A query.

### Returns

`cts:query`

### Examples

```xquery
cts:locks-fragment-query-query(
    cts:locks-fragment-query(cts:word-query("word")))
  => cts:word-query("word", ("lang=en"), 1)
```

---

## cts:lsqt-query

Returns only documents before LSQT or a timestamp before LSQT for
stable query results.

### Signature

```xquery
cts:lsqt-query(
  $temporal-collection as xs:string,
  $timestamp as xs:dateTime??,
  $options as xs:string*?,
  $weight as xs:double??
) as cts:lsqt-query
```

### Parameters

**`$temporal-collection`**
The name of the temporal collection.

**`$timestamp`** *(optional)*
Return only temporal documents with a system start time less than or equal
   to this value.
   Default is temporal:get-lsqt($temporal-collection).
   Timestamps larger than LSQT are rejected.

**`$options`** *(optional)*
Options to this query.  The default is ().
    
      Options include:
      
        "cached"
        Cache the results of this query in the list cache.
        "uncached"
        Do not cache the results of this query in the list cache.
        "cached-incremental"
        Break down the query into sub-queries and then cache each
        one of them for better performance. This is enabled, by default.
        "score-function=function"
        Use the selected scoring function. The score function may be:
          
          linearUse a linear function of the difference between the
          specified query value and the matching value in the index to calculate
          a score for this range query.
          reciprocalUse a reciprocal function of the difference
          between the specified query value and the matching value in the
          index to calculate a score for this range query.
          zeroThis range query does not contribute to the
          score. This is the default.
          
        
        "slope-factor=number"
        Apply the given number as a scaling factor to the slope of the
        scoring function. The default is 1.0.

**`$weight`** *(optional)*
A weight for this query.
    Higher weights move search results up in the relevance
    order.  The default is 1.0. The
    weight should be between 64 and -16.
    Weights greater than 64 will have the same effect as a
    weight of 64.
    Weights less than the absolute value of 0.0625 (between -0.0625 and
    0.0625) are rounded to 0, which means that they do not contribute to the
    score.

### Returns

`cts:lsqt-query`

### Examples

```xquery
cts:lsqt-query("temporal",(),"cached-incremental", xs:double("3.13"))
```

---

## cts:lsqt-query-options

Returns the options for the specified query.

### Signature

```xquery
cts:lsqt-query-options(
  $query as cts:lsqt-query
) as xs:string*
```

### Parameters

**`$query`**
A query.

### Returns

`xs:string*`

### Examples

```xquery
let $query :=
  cts:lsqt-query("temporal",
                 xs:dateTime("2014-09-03T15:26:41.452342-07:00"),
                 "cached-incremental", xs:double("3.13"))
return
  cts:lsqt-query-options($query)
  => cached-incremental
```

---

## cts:lsqt-query-temporal-collection

Returns the name of the temporal collection used to construct specified query.

### Signature

```xquery
cts:lsqt-query-temporal-collection(
  $query as cts:lsqt-query
) as xs:string
```

### Parameters

**`$query`**
A query.

### Returns

`xs:string`

### Examples

```xquery
let $query :=
  cts:lsqt-query("temporal",(),"cached-incremental", xs:double("3.13"))
return
  cts:lsqt-query-temporal-collection($query)
  => temporal
```

---

## cts:lsqt-query-timestamp

Returns timestamp used to construct the specified query.

### Signature

```xquery
cts:lsqt-query-timestamp(
  $query as cts:lsqt-query
) as xs:dateTime
```

### Parameters

**`$query`**
A query.

### Returns

`xs:dateTime`

### Examples

```xquery
let $query :=
  cts:lsqt-query("temporal",
                 xs:dateTime("2014-09-03T15:26:41.452342-07:00"),
                 "cached-incremental", xs:double("3.13"))
return
  cts:lsqt-query-timestamp($query)
  => 2014-09-03T15:26:41.452342-07:00
```

---

## cts:lsqt-query-weight

Returns the weight with which the specified query was constructed.

### Signature

```xquery
cts:lsqt-query-weight(
  $query as cts:lsqt-query
) as xs:double
```

### Parameters

**`$query`**
A query.

### Returns

`xs:double`

### Examples

```xquery
let $query :=
  cts:lsqt-query("temporal",
                 xs:dateTime("2014-09-03T15:26:41.452342-07:00"),
                 "cached-incremental", xs:double("3.13"))
return
  cts:lsqt-query-weight($query)
  => 3.13
```

---

## cts:near-query

Returns a query matching all of the specified queries, where
  the matches occur within the specified distance from each other.

### Signature

```xquery
cts:near-query(
  $queries as cts:query*,
  $distance as xs:double??,
  $options as xs:string*?,
  $distance-weight as xs:double??
) as cts:near-query
```

### Parameters

**`$queries`**
A sequence of queries to match.

**`$distance`** *(optional)*
A distance, in number of words, between any two matching queries.
    The results match if two queries match and the distance between the
    two matches is equal to or less than the specified distance. A
    distance of 0 matches when the text is the exact same text or when
    there is overlapping text (see the third example below). A negative
    distance is treated as 0.  The default value is 10.

**`$options`** *(optional)*
Options to this query.  The default value is ().
    
      Options include:
      
        "ordered"
        Any near-query matches must occur in the order of
            the specified sub-queries.
        "unordered"
        Any near-query matches will satisfy the query,
        regardless of the order they were specified.  
        "minimum-distance"
        The minimum distance between two matching queries. The results
        match if the two queries match and the minimum distance between the two
        matches is greater than or equal to the specified minimum distance. The
        default value is zero. A negative distance is treated as 0.

**`$distance-weight`** *(optional)*
A weight attributed to the distance for this query.  Higher
    weights add to the importance of distance (as opposed to term matches)
    when the relevance order is calculated.  The default value is 1.0. The
    weight should be between 64 and -16.
    Weights greater than 64 will have the same effect as a
    weight of 64.
    Weights less than the absolute value of 0.0625 (between -0.0625 and
    0.0625) are rounded to 0, which means that they do not contribute to the
    score.  This parameter has no effect if the word positions
    index is not enabled.

### Returns

`cts:near-query`

### Usage Notes

If the options parameter contains neither "ordered" nor "unordered",
  then the default is "unordered".
      The word positions index will speed the performance of
  queries that use cts:near-query. The element word
  positions index will speed the performance of element-queries
  that use cts:near-query.
      If you use cts:near-query with a field, the distance
  specified is the distance in the whole document, not the distance
  in the field. For example, if the distance between two words is 20 in
  the document, but the distance is 10 if you look at a view of the document
  that only includes the elements in a field, a cts:near-query
  must have a distance of 20 or more to match; a distance of 10 would not
  match. The same applies to minimum distance as well.
      If you use cts:near-query with
  cts:field-word-query, the distance supplied in the near query
  applies to the whole document, not just to the field. This too applies to the
  minimum distance as well. For details, see
  cts:field-word-query.
      Expressions using the ordered option are more efficient
  than those using the unordered option, especially if they
  specify many queries to match.
      Minimum-distance and distances apply to each near-query match. Therefore, if
  minimum-distance is greater than distance there can be no matches.

### Examples

#### Example 1

```xquery
The following query searches for paragraphs containing
 both "MarkLogic" and "Server" within 3 words of each
 other, given the following paragraphs in a database:

  <p>MarkLogic Server is an enterprise-class
  database specifically built for content.</p>
  <p>MarkLogic is an excellent XML Content Server.</p>

  cts:search(//p,
    cts:near-query(
      (cts:word-query("MarkLogic"),
      cts:word-query("Server")),
      3))

  =>
  <p>MarkLogic Server is an enterprise-class
  database specifically built for content.</p>
```

#### Example 2

```xquery
let $x := <p>Now is the winter of our discontent</p>
return
cts:contains($x, cts:near-query(
                    ("discontent", "winter"),
                    3, "ordered"))

=> false because "discontent" comes after "winter"

let $x := <p>Now is the winter of our discontent</p>
return
cts:contains($x, cts:near-query(
                    ("discontent", "winter"),
                    3, "unordered"))

=> true because the query specifies "unordered",
        and it is still a match even though
        "discontent" comes after "winter"
```

#### Example 3

```xquery
let $x := <p>Now is the winter of our discontent</p>
return
cts:contains($x, cts:near-query(
                    ("is the winter", "winter of"),
                    0))

=> true because the phrases overlap

let $x := <p>Now is the winter of our discontent</p>
return
cts:contains($x, cts:near-query(
                    ("is the winter", "of our"),
                    0))

=> false because the phrases do not overlap
         (they have 1 word distance, not 0)
```

#### Example 4

```xquery
let $x := <p>Now is the winter of our discontent</p>
return
cts:contains($x, cts:near-query(
                    ("winter", "discontent"),
                    5, ("ordered", "minimum-distance=4")))

=> false because the distance between the queries is greater than the minimum
distance

let $x := <p>Now is the winter of our discontent</p>
return
cts:contains($x, cts:near-query(
                    ("winter", "discontent"),
                    5, ("ordered", "minimum-distance=3")))

=> true because the distance between the queries is less than or equal to the
minimum distance
```

---

## cts:near-query-distance

Returns the distance used to construct the near query.

### Signature

```xquery
cts:near-query-distance(
  $query as cts:near-query
) as xs:integer
```

### Parameters

**`$query`**
A query.

### Returns

`xs:integer`

### Examples

```xquery
let $query := cts:near-query(
                 cts:word-query("wanted"),
                 cts:word-query("unwanted"),
                 12)
return cts:near-query-distance($query)
=> 12
```

---

## cts:near-query-options

Returns the options for the specified query.

### Signature

```xquery
cts:near-query-options(
  $query as cts:near-query
) as xs:string*
```

### Parameters

**`$query`**
A query.

### Returns

`xs:string*`

### Examples

```xquery
let $query := cts:near-query(
                 (cts:word-query("wanted"),
                 cts:word-query("unwanted")),
                 12,
                 "ordered")
return
  cts:near-query-options($query)
  => "ordered"
```

---

## cts:near-query-queries

Returns the query sequence used to construct the near query.

### Signature

```xquery
cts:near-query-queries(
  $query as cts:near-query
) as cts:query*
```

### Parameters

**`$query`**
A query.

### Returns

`cts:query*`

### Examples

#### Example 1

```xquery
cts:near-query-queries($query)
  => ... a sequence of the queries used to
            construct this query
```

#### Example 2

```xquery
let $query :=
  cts:near-query((
    cts:word-query("to be or"),
    cts:word-query("or not to be")))
return cts:near-query-queries($query)
  => (cts:word-query("to be or", (), 1)
         cts:word-query("or not to be", (), 1))
```

---

## cts:near-query-weight

Returns the weight with which the specified query was constructed.

### Signature

```xquery
cts:near-query-weight(
  $query as cts:near-query
) as xs:double
```

### Parameters

**`$query`**
A query.

### Returns

`xs:double`

### Examples

```xquery
let $query := cts:near-query(
                 (cts:word-query("wanted"),
                 cts:word-query("unwanted")),
                 12, "ordered", 5.0)
return
  cts:near-query-weight($query)
  => 5.0
```

---

## cts:not-in-query

Returns a query matching the first sub-query, where those matches do not
  occur within 0 distance of the other query.

### Signature

```xquery
cts:not-in-query(
  $positive-query as cts:query,
  $negative-query as cts:query
) as cts:not-in-query
```

### Parameters

**`$positive-query`**
A positive query, specifying the search results
    filtered in.

**`$negative-query`**
A negative query, specifying the search results
    to filter out.

### Returns

`cts:not-in-query`

### Usage Notes

Positions are required to accurately resolve this query from the indexes.
    If you do not enable position indexes appropriate to the type of the
    sub-queries, then you may get surprising results in unfiltered searches.
    For example, if the sub queries are cts:word-query, then
    you should enable word positions in the database.
  
      
    False positives can occur if there are no positions available, such as
    when positions are not enabled. Filtered searches always have access to
    positions, but unfiltered searches do not.
  
      
    Some query types are intrinsically positionless, such as
    cts:collection-query or cts:directory-query.
    Matches to such a query are considered to occur at every position and
    causes the overall query to behave like cst:and-not-query.
    If no position can be determined, such as when positions are not enabled,
    then every match to $positive-query is a match for the
    whole query.

### Examples

#### Example 1

```xquery
cts:search(//PLAY,
  cts:not-in-query(
    cts:word-query("nettles"),
    cts:word-query("stinging nettles")))
=> A sequence of 'PLAY' elements containing some text node
   with the word 'nettles' where that occurrence is not in the
   phrase 'stinging nettles'.This sequence may be (in fact is) non-empty,
   but certainly does not contain the PLAY element with:

    PLAY/TITLE =
      "The Tragedy of King Richard the Second"

   since, while this play does contain 'nettles', it is only in the
   phrase 'stinging nettles'. On the other hand, this play
   will match the query:

     cts:search(//PLAY,
       cts:not-in-query(
         cts:word-query("summer"),
         cts:word-query("summer corn")))

   since, while the play does contain 'summer corn', it also contains 'summer'
   in other contexts as well.

   If word positions are not enabled, then an unfiltered search returns
   all documents containing "nettles".
```

#### Example 2

```xquery
cts:search(//PLAY,
  cts:not-in-query(
    cts:word-query("nettles"),
    cts:collection-query("TRAGEDY")))
=> A sequence of 'PLAY' elements containing some text node with
   the word "nettles", excluding occurrences in documents in the
   "TRAGEDY" collection. The collection query is intrinsically,
   positionless, so the negative query matches overlap with every
   match of the positive query.
```

---

## cts:not-in-query-negative-query

Returns the negative (second parameter) query used to construct the
  specified query.

### Signature

```xquery
cts:not-in-query-negative-query(
  $query as cts:not-in-query
) as cts:query
```

### Parameters

**`$query`**
A query.

### Returns

`cts:query`

### Examples

```xquery
let $query := cts:not-in-query(
                 cts:word-query("wanted"),
                 cts:word-query("not wanted"))
return cts:not-in-query-negative-query($query)

  => cts:word-query("not wanted", (), 1)
```

---

## cts:not-in-query-positive-query

Returns the positive (first parameter) query used to construct the
  specified query.

### Signature

```xquery
cts:not-in-query-positive-query(
  $query as cts:not-in-query
) as cts:query
```

### Parameters

**`$query`**
A query.

### Returns

`cts:query`

### Examples

```xquery
let $query := cts:not-in-query(
                 cts:word-query("wanted"),
                 cts:word-query("not wanted"))
return cts:not-in-query-positive-query($query)

  => cts:word-query("wanted", (), 1)
```

---

## cts:not-query

Returns a query specifying the matches not specified by its sub-query.

### Signature

```xquery
cts:not-query(
  $query as cts:query
) as cts:not-query
```

### Parameters

**`$query`**
A negative query, specifying the search results
    to filter out.

### Returns

`cts:not-query`

### Usage Notes

The cts:not-query constructor is fragment-based, so
  it returns true only if the specified query does not produce a match
  anywhere in a fragment.  Therefore, a search using
  cts:not-query is only guaranteed to be accurate if the underlying
  query that is being negated is accurate from its index resolution (that is,
  if the unfiltered results of the $query parameter to
  cts:not-query are accurate).  The accuracy of the index
  resolution depends on the many factors such as the query, if you search
  at a fragment root (that is, if the first parameter of
  cts:search specifies an XPath that resolves to a fragment root),
  the index options enabled on the database, the search options,
  and other factors.
  In cases where the $query parameter has false-positive matches,
  the negation of the query can miss matches (have false negative matches).
  In these cases,
  searches with cts:not-query can miss results, even if those
  searches are filtered.

### Examples

#### Example 1

```xquery
cts:search(//PLAY,
    cts:not-query(
      cts:word-query("summer")))
  => ...  sequence of 'PLAY' elements not containing
          any text node with the word 'summer'.
```

#### Example 2

```xquery
let $doc :=
  <doc>
   <p n="1">Dogs, cats, and pigs</p>
   <p n="2">Trees, frogs, and cats</p>
   <p n="3">Dogs, alligators, and wolves</p>
  </doc>
return
$doc//p[cts:contains(., cts:not-query("cat"))]
(: Returns the third p element (the one without
   a "cat" term). Note that the
   cts:contains forces the constraint to happen
   in the filtering stage of the query. :)
```

---

## cts:not-query-query

Returns the query used to construct the specified query.

### Signature

```xquery
cts:not-query-query(
  $query as cts:not-query
) as cts:query
```

### Parameters

**`$query`**
A query.

### Returns

`cts:query`

### Examples

```xquery
let $query := cts:not-query("MarkLogic Server);
return
cts:not-query-query($query)

=> cts:word-query("MarkLogic Server"), ("lang=en"), 1)
```

---

## cts:not-query-weight

Returns the weight with which the specified query was constructed.

### Signature

```xquery
cts:not-query-weight(
  $query as cts:not-query
) as xs:double
```

### Parameters

**`$query`**
A query.

### Returns

`xs:double`

### Examples

```xquery
let $query := cts:not-query("MarkLogic Server);
return
cts:not-query-weight($query)

=> 1
```

---

## cts:or-query

Returns a query specifying the union
  of the matches specified by the sub-queries.

### Signature

```xquery
cts:or-query(
  $queries as cts:query*,
  $options as xs:string*?
) as cts:or-query
```

### Parameters

**`$queries`**
A sequence of sub-queries.

**`$options`** *(optional)*
Options to this query. The default is ().
  
  Options include:
  
  
  "synonym"
  Specifies that all of the terms in the $queries parameter are
  considered synonyms for scoring purposes.  The result is that
  occurrences of more than one of the synonyms are scored as if
  there are more occurrences of the same term (as opposed to
  having a separate term that contributes to score).

### Returns

`cts:or-query`

### Examples

```xquery
cts:search(//PLAY,
    cts:or-query((
      cts:word-query("summer"),
      cts:word-query("sun of York"))))
  => .. a sequence of 'PLAY' elements which are
  ancestors (or self) of some node whose text content
  contains the word 'summer' OR some node
  whose text content contains the phrase 'sun of York'.
  This union contains at least one 'PLAY' node with:

    PLAY/TITLE =
      "The Tragedy of King Richard the Second",

  but also contains other 'PLAY' nodes containing some
  text node with the word "summer", for example,

    PLAY/TITLE = "A Midsummer Night's Dream".
```

---

## cts:or-query-options

Returns the options for the specified query.

### Signature

```xquery
cts:or-query-options(
  $query as cts:or-query
) as xs:string*
```

### Parameters

**`$query`**
A query.

### Returns

`xs:string*`

### Examples

```xquery
cts:or-query-options($query)
  => "synonym"
```

---

## cts:or-query-queries

Returns a sequence of the queries that were used to construct the specified
  query.

### Signature

```xquery
cts:or-query-queries(
  $query as cts:or-query
) as cts:query*
```

### Parameters

**`$query`**
A query.

### Returns

`cts:query*`

### Examples

```xquery
cts:or-query-queries($query)
  => ... a sequence of the queries used to construct this query
```

---

## cts:path-geospatial-query

Returns a query matching path expressions whose content
  represents a point contained within the given geographic box, circle, or
  polygon, or equal to the given point. Points that lie
  between the southern boundary and the northern boundary of a box,
  travelling northwards,
  and between the western boundary and the eastern boundary of the box,
  travelling eastwards, will match.
  Points contained within the given radius of the center point of a circle will
  match, using the curved distance on the surface of the Earth.
  Points contained within the given polygon will match, using great circle arcs
  over a spherical model of the Earth as edges.  An error may result
  if the polygon is malformed in some way.
  Points equal to the a given point will match, taking into account the fact
  that longitudes converge at the poles.
  Using the geospatial query constructors requires a valid geospatial
  license key; without a valid license key, searches that include
  geospatial queries will throw an exception.

### Signature

```xquery
cts:path-geospatial-query(
  $path-expression as xs:string*,
  $regions as cts:region*,
  $options as xs:string*?,
  $weight as xs:double??
) as cts:path-geospatial-query
```

### Parameters

**`$path-expression`**
One or more path expressions to match.
    When multiple path expressions are specified,
    the query matches if any path expression matches.

**`$regions`**
One or more geographic boxes, circles, polygons, or points. Where multiple
    regions are specified, the query matches if any region matches.

**`$options`** *(optional)*
Options to this query.  The default is ().
    Options include:
      
        
        "coordinate-system=string"
        Use the given coordinate system. Valid values are:
          
          wgs84The WGS84 coordinate system with degrees as the angular unit.
          wgs84/radiansThe WGS84 coordinate system with radians as the angular unit.
          wgs84/doubleThe WGS84 coordinate system at double precision with degrees as the angular unit.
          wgs84/radians/doubleThe WGS84 coordinate system at double precision with radians as the angular unit.
          etrs89The ETRS89 coordinate system.
          etrs89/doubleThe ETRS89 coordinate system at double precision.
          rawThe raw (unmapped) coordinate system.
          raw/doubleThe raw coordinate system at double precision.
          
          
          "precision=value"
          Use the coordinate system at the given precision. Allowed values:
          float and double.
        "units=value"
        Measure distance and the radii of circles in the specified units.
         Allowed values: miles (default), km,
         feet, meters.
        "boundaries-included"
        Points on boxes', circles', and polygons' boundaries are counted
        as matching.  This is the default.
        "boundaries-excluded"
        Points on boxes', circles', and polygons' boundaries are not
    counted as matching.
        "boundaries-latitude-excluded"
        Points on boxes' latitude boundaries are not counted as
    matching.
        "boundaries-longitude-excluded"
        Points on boxes' longitude boundaries are not counted as
    matching.
        "boundaries-south-excluded"
        Points on the boxes' southern boundaries are not counted as
    matching.
        "boundaries-west-excluded"
        Points on the boxes' western boundaries are not counted as
    matching.
        "boundaries-north-excluded"
        Points on the boxes' northern boundaries are not counted as
    matching.
        "boundaries-east-excluded"
        Points on the boxes' eastern boundaries are not counted as
    matching.
        "boundaries-circle-excluded"
        Points on circles' boundary are not counted as matching.
        "boundaries-endpoints-excluded"
        Points on linestrings' boundary (the endpoints) are not counted as matching.
        "cached"
        Cache the results of this query in the list cache.
        "uncached"
        Do not cache the results of this query in the list cache.
        "type=long-lat-point"
        Specifies the format for the point in the data as longitude first,
        latitude second.
        "type=point"
        Specifies the format for the point in the data as latitude first,
        longitude second.  This is the default format.
        "score-function=function"
        Use the selected scoring function. The score function may be:
          
          linearUse a linear function of the difference between the
          specified query value and the matching value in the index to calculate
          a score for this range query.
          reciprocalUse a reciprocal function of the difference
          between the specified query value and the matching value in the
          index to calculate a score for this range query.
          zeroThis range query does not contribute to the
          score. This is the default.
          
        
        "slope-factor=number"
        Apply the given number as a scaling factor to the slope of the
        scoring function. The default is 1.0.
        "synonym"
        Specifies that all of the terms in the $regions parameter are
        considered synonyms for scoring purposes.  The result is that
        occurrences of more than one of the synonyms are scored as if
        there are more occurrence of the same term (as opposed to
        having a separate term that contributes to score).

**`$weight`** *(optional)*
A weight for this query.  The default is 1.0.

### Returns

`cts:path-geospatial-query`

### Usage Notes

The point value is expressed in the content of an element that matches given
 path expression as a pair of numbers, separated by whitespace and punctuation
 (excluding decimal points and sign characters).

      The value of the precision option takes precedence over
 that implied by the governing coordinate system name, including the
 value of the coordinate-system option. For example, if the
 governing coordinate system is "wgs84/double" and the precision
 option is "float", then the query uses single precision.

      Point values and boundary specifications of
boxes are given in degrees
relative to the WGS84 coordinate system.  Southern latitudes and Western
longitudes take negative values.  Longitudes will be wrapped to the range
(-180,+180) and latitudes will be clipped to the range (-90,+90).

      If the northern boundary of a box is south of the southern boundary, no
points will match. However, longitudes wrap around the globe, so that if
the western boundary is east of the eastern boundary,
then the box crosses the anti-meridian.

      Special handling occurs at the poles, as all longitudes exist at latitudes
+90 and -90.

      If neither "cached" nor "uncached" is present, it specifies "cached".
      "score-function=linear" means that values that are further away from
  the bounds will score higher. "score-function=reciprocal" means that values
  that are closer to the bounds will score higher. The functions are scaled
  appropriately for different types, so that in general the default slope factor
  will provide useful results. Using a slope factor greater than 1 gives
  distinct scores over a smaller range of values, and produces generally
  higher scores.  Using a slope factor less than 1 gives distinct scores
  over a wider range of values, and produces generally lower scores.
  
      "score-function=linear" means that values that are further away from
  the bounds will score higher. "score-function=reciprocal" means that values
  that are closer to the bounds will score higher. The functions are scaled
  appropriately for different types, so that in general the default slope factor
  will provide useful results. Using a slope factor greater than 1 gives distinct
  scores over a smaller range of values, and produces generally higher scores.
  Using a slope factor less than 1 gives distinct scores over a wider range of
  values, and produces generally lower scores.

### Examples

```xquery
(: create a document with test data :)
xdmp:document-insert("/points.xml",
<root>
  <item><point>10.5, 30.0</point></item>
  <item><point>15.35, 35.34</point></item>
  <item><point>5.11, 40.55</point></item>
</root> );

cts:search(doc("/points.xml")//item,
  cts:path-geospatial-query("/root/item/point",
      cts:box(10.0, 35.0, 20.0, 40.0)));
(:
  returns the following node:
  <item><point>15.35, 35.34</point></item>
:)

cts:search(doc("/points.xml")//item,
  cts:path-geospatial-query("//item/point", cts:box(10.0, 40.0, 20.0, 35.0)));
(:
  returns the following nodes (wrapping around the Earth):
  <item><point>10.5, 30.0</point></item>
:)

cts:search(doc("/points.xml")//item,
  cts:path-geospatial-query("//point", cts:box(20.0, 35.0, 10.0, 40.0)))
(:
  throws an error (latitudes do not wrap)
:)
```

---

## cts:path-geospatial-query-options

Returns the options for the specified query.

### Signature

```xquery
cts:path-geospatial-query-options(
  $query as cts:path-geospatial-query
) as xs:string*
```

### Parameters

**`$query`**
A query.

### Returns

`xs:string*`

### Examples

```xquery
let $query := cts:path-geospatial-query("//point",
       cts:box(10.1, 10.2, 20.1, 20.2))
return cts:path-geospatial-query-options($query)

=> coordinate-system=wgs84
```

---

## cts:path-geospatial-query-path-expression

Returns the path expressions used to construct the specified query.

### Signature

```xquery
cts:path-geospatial-query-path-expression(
  $query as cts:path-geospatial-query
) as xs:string*
```

### Parameters

**`$query`**
A query.

### Returns

`xs:string*`

### Examples

```xquery
let $query := cts:path-geospatial-query("//point",
       cts:box(10.1, 10.2, 20.1, 20.2))
return cts:path-geospatial-query-path-expression($query)

=> "//point"
```

---

## cts:path-geospatial-query-region

Returns the geographical regions
  with which the specified query was constructed.

### Signature

```xquery
cts:path-geospatial-query-region(
  $query as cts:path-geospatial-query
) as cts:region*
```

### Parameters

**`$query`**
A query.

### Returns

`cts:region*`

### Examples

```xquery
let $query := cts:path-geospatial-query("//point",
       cts:box(10.1, 10.2, 20.1, 20.2))
return cts:path-geospatial-query-region($query)

=> cts:box("[10.1, 10.2, 20.1, 20.2]")
```

---

## cts:path-geospatial-query-weight

Returns the weight with which the specified query was constructed.

### Signature

```xquery
cts:path-geospatial-query-weight(
  $query as cts:path-geospatial-query
) as xs:double
```

### Parameters

**`$query`**
A query.

### Returns

`xs:double`

### Examples

```xquery
let $query := cts:path-geospatial-query("//point",
       cts:box(10.1, 10.2, 20.1, 20.2))
return cts:path-geospatial-query-weight($query)

=> 1
```

---

## cts:path-range-query

Returns a cts:query matching documents where the content
  addressed by an XPath expression satisfies the specified relationship
  (=, <, >, etc.) with respect to the input criteria values. A path range
  index must exist for each path when you perform a search.

### Signature

```xquery
cts:path-range-query(
  $path-expression as xs:string*,
  $operator as xs:string,
  $value as xs:anyAtomicType*,
  $options as xs:string*?,
  $weight as xs:double??
) as cts:path-range-query
```

### Parameters

**`$path-expression`**
One or more XPath expressions that identify the content to match.
    When multiple paths are specified, the query matches if any path matches.

**`$operator`**
A comparison operator.
    
      Operators include:
      
        "<"
        Match range index values less than $value.
        "<="
        Match range index values less than or equal to $value.
        ">"
        Match range index values greater than $value.
        ">="
        Match range index values greater than or equal to $value.
        "="
        Match range index values equal to $value.
        "!="
        Match range index values not equal to $value.

**`$value`**
One or more values to match. These values are compared to the value(s)
    addressed by the path-expression parameter. When multiple
    When multiple values are specified, the query matches if any value
    matches. The value must be a type for which there is a range index defined.

**`$options`** *(optional)*
Options to this query.  The default is ().
    
      Options include:
      
        "collation=URI"
        Use the range index with the collation specified by
        URI.  If not specified, then the default collation
        from the query is used. If a range index with the specified
        collation does not exist, an error is thrown.
        "cached"
        Cache the results of this query in the list cache.
        "uncached"
        Do not cache the results of this query in the list cache.
        "cached-incremental"
        When querying on a short date or dateTime range, break the
        query into sub-queries on smaller ranges, and then cache the
        results of each.  See the Usage Notes for details.
        "min-occurs=number"
        Specifies the minimum number of occurrences required. If
        fewer that this number of words occur, the fragment does not match.
        The default is 1.
        "max-occurs=number"
        Specifies the maximum number of occurrences required.  If
        more than this number of words occur, the fragment does not match.
        The default is unbounded.
        "score-function=function"
        Use the selected scoring function. The score function may be:
          
          linearUse a linear function of the difference between the
          specified query value and the matching value in the index to calculate
          a score for this range query.
          reciprocalUse a reciprocal function of the difference
          between the specified query value and the matching value in the
          index to calculate a score for this range query.
          zeroThis range query does not contribute to the
          score. This is the default.
          
        
        "slope-factor=number"
        Apply the given number as a scaling factor to the slope of the
        scoring function. The default is 1.0.
        "synonym"
        Specifies that all of the terms in the $value parameter are
        considered synonyms for scoring purposes.  The result is that
        occurrences of more than one of the synonyms are scored as if
        there are more occurrences of the same term (as opposed to
        having a separate term that contributes to score).

**`$weight`** *(optional)*
A weight for this query.  The default is 1.0.

### Returns

`cts:path-range-query`

### Usage Notes

If you want to constrain on a range of values, you can combine multiple
  cts:path-range-query constructors together
  with cts:and-query or any of the other composable
  cts:query constructors.
      If neither "cached" nor "uncached" is present, it specifies "cached".
      The "cached-incremental" option can improve performance if you
   repeatedly perform range queries on date or dateTime values over a
   short range that does not vary widely over short period of time. To
   benefit, the operator should remain the same "direction" (<,<=, or >,>=) 
   across calls, the bounding date or dateTime changes slightly across calls,
   and the query runs very frequently (multiple times per minute).
   Note that using this options creates significantly more cached queries
   than the "cached" option.
  
      The "cached-incremental" option has the following restrictions and
   interactions: The "min-occurs" and "max-occurs" options will be ignored
   if you use "cached-incremental" in unfiltered search. You can only use
   "score-function=zero" with "cached-incremental". The "cached-incremental"
   option behaves like "cached" if you are not querying date or dateTime values.
  
      
    Negative "min-occurs" or "max-occurs" values will be treated as 0 and
    non-integral values will be rounded down.  An error will be raised if
    the "min-occurs" value is greater than the "max-occurs" value.
  
      "score-function=linear" means that values that are further away from
  the bounds will score higher. "score-function=reciprocal" means that values
  that are closer to the bounds will score higher. The functions are scaled
  appropriately for different types, so that in general the default slope factor
  will provide useful results. Using a slope factor greater than 1 gives distinct
  scores over a smaller range of values, and produces generally higher scores.
  Using a slope factor less than 1 gives distinct scores over a wider range of
  values, and produces generally lower scores.
  
      For queries against a dateTime index, when $value is an xs:dayTimeDuration
  or xs:yearMonthDuration, the query is executed as an age query. $value is
  subtracted from fn:current-dateTime() to create an xs:dateTime used in the query.
  If there is more than one item in $value, they must all be the same type.

### Examples

```xquery
(: Insert few documents with test data :)
xdmp:document-insert("/aname1.xml",
  <name><fname>John</fname><mname>Rob</mname><lname>Goldings</lname></name>),
xdmp:document-insert("/aname2.xml",
  <name><fname>Jim</fname><mname>Ken</mname><lname>Kurla</lname></name>),
xdmp:document-insert("/aname3.xml",
  <name><fname>Ooi</fname><mname>Ben</mname><lname>Fu</lname></name>),
xdmp:document-insert("/aname4.xml",
  <name><fname>James</fname><mname>Rick</mname><lname>Tod</lname></name>)

Requires a path (range) index of type xs:string on path "/name/fname".

cts:contains(doc(),cts:path-range-query("/name/fname","=","John"))
 => true

cts:search(doc(),cts:path-range-query("/name/fname",">","Jim"),"filtered")
 =>
<?xml version="1.0" encoding="UTF-8"?>
<name><fname>John</fname><mname>Rob</mname><lname>Goldings</lname></name>
<?xml version="1.0" encoding="UTF-8"?>
<name><fname>Ooi</fname><mname>Ben</mname><lname>Fu</lname></name>

cts:search(doc(),cts:path-range-query("/name/fname","<","John"),"unfiltered")
 =>
<?xml version="1.0" encoding="UTF-8"?>
<name><fname>Jim</fname><mname>Ken</mname><lname>Kurla</lname></name>
<?xml version="1.0" encoding="UTF-8"?>
<name><fname>James</fname><mname>Rick</mname><lname>Tod</lname></name>
```

---

## cts:path-range-query-operator

Returns the operator used to construct the specified query.

### Signature

```xquery
cts:path-range-query-operator(
  $query as cts:path-range-query
) as xs:string
```

### Parameters

**`$query`**
A query.

### Returns

`xs:string`

### Examples

```xquery
let $query := cts:path-range-query("/a/b/c",">","Jim",
  "collation=http://marklogic.com/collation/", xs:double("3.13"))
return
cts:path-range-query-operator($query)
  => >
```

---

## cts:path-range-query-options

Returns the options for the specified query.

### Signature

```xquery
cts:path-range-query-options(
  $query as cts:path-range-query
) as xs:string*
```

### Parameters

**`$query`**
A query.

### Returns

`xs:string*`

### Examples

```xquery
let $query := cts:path-range-query("/a/b/c",">","Jim",
  "collation=http://marklogic.com/collation/", xs:double("3.13"))
return
cts:path-range-query-options($query)
  => "collation=http://marklogic.com/collation/"
```

---

## cts:path-range-query-path-name

Returns the path expression used to construct the specified query.

### Signature

```xquery
cts:path-range-query-path-name(
  $query as cts:path-range-query
) as xs:string*
```

### Parameters

**`$query`**
A query.

### Returns

`xs:string*`

### Examples

```xquery
let $query := cts:path-range-query("/a/b/c",">","Jim",
  "collation=http://marklogic.com/collation/", xs:double("3.13"))
return
cts:path-range-query-path-name($query)
  => /a/b/c
```

---

## cts:path-range-query-value

Returns the value used to construct the specified query.

### Signature

```xquery
cts:path-range-query-value(
  $query as cts:path-range-query
) as xs:anyAtomicType*
```

### Parameters

**`$query`**
A query.

### Returns

`xs:anyAtomicType*`

### Examples

```xquery
let $query := cts:path-range-query("/a/b/c",">","Jim",
  "collation=http://marklogic.com/collation/", xs:double("3.13"))
return
cts:path-range-query-value($query)
  => "Jim"
```

---

## cts:path-range-query-weight

Returns the weight with which the specified query was constructed.

### Signature

```xquery
cts:path-range-query-weight(
  $query as cts:path-range-query
) as xs:double
```

### Parameters

**`$query`**
A query.

### Returns

`xs:double`

### Examples

```xquery
let $query := cts:path-range-query("/a/b/c",">","Jim",
  "collation=http://marklogic.com/collation/", xs:double("3.13"))
return
cts:path-range-query-weight($query)
  => 3.13
```

---

## cts:period-compare-query

Returns a cts:query matching documents that have relevant
  pair of period values.  Searches with the
  cts:period-compare-query
  constructor require two valid names of period, if the either of the specified
  period does not exist, then an exception is thrown.

### Signature

```xquery
cts:period-compare-query(
  $axis-1 as xs:string,
  $operator as xs:string,
  $axis-2 as xs:string,
  $options as xs:string*?
) as cts:period-compare-query
```

### Parameters

**`$axis-1`**
Name of the first axis to compare

**`$operator`**
A comparison operator. Period is the two timestamps contained in the axis.
    
      Operators include:
      
        "aln_equals"
        Match documents whose period1 equals period2.
        "aln_contains"
        Match documents whose period1 contains period2. i.e. period1
        starts before period2 starts and ends before period2 ends.
        "aln_contained_by"
        Match documents whose period1 is contained by period2.
        "aln_meets"
        Match documents whose period1 meets period2, i.e. period1 ends at
        period2 start.
        "aln_met_by"
        Match documents whose period1 meets period2, i.e. period1 starts
        at period2 end.
        "aln_before"
        Match documents whose period1 is before period2, i.e. period1 ends
        before period2 starts.
        "aln_after"
        Match documents whose period1 is after period2, i.e. period1
        starts after period2 ends.
        "aln_starts"
        Match documents whose period1 starts period2, i.e. period1 starts
        at period2 start and ends before period2 ends.
        "aln_started_by"
        Match documents whose period2 starts period1, i.e. period1 starts
        at period2 start and ends after period2 ends.
        "aln_finishes"
        Match documents whose period1 finishes period2, i.e. period1
        finishes at period2 finish and starts after period2 starts.
        "aln_finished_by"
        Match documents whose period2 finishes period1, i.e. period1
        finishes at period2 finish and starts before period2 starts.
        "aln_overlaps"
        Match documents whose period1 overlaps period2, i.e. period1
        starts before period2 start and ends before period2 ends but after
        period2 starts.
        "aln_overlapped_by"
        Match documents whose period2 overlaps period1, i.e. period1
        starts after period2 start but before period2 ends and ends after
        period2 ends.
        "iso_contains"
        Match documents whose period1 contains period2 in sql 2011 standard.
        i.e. period1 starts before or at period2 starts and ends after or
        at period2 ends.
        "iso_overlaps"
        Match documents whose period1 overlaps period2 in sql 2011 standard.
        i.e. period1 and period2 have common time period.
        "iso_succeeds"
        Match documents whose period1 succeeds period2 in sql 2011 standard.
        i.e. period1 starts at or after period2 ends
        "iso_precedes"
        Match documents whose period1 precedes period2 in sql 2011 standard.
        i.e. period1 ends at or before period2 ends
        "iso_succeeds"
        Match documents whose period1 succeeds period2 in sql 2011 standard.
        i.e. period1 starts at or after period2 ends
        "iso_precedes"
        Match documents whose period1 precedes period2 in sql 2011 standard.
        i.e. period1 ends at or before period2 ends
        "iso_imm_succeeds"
        Match documents whose period1 immediately succeeds period2 in
        sql 2011 standard.  i.e. period1 starts at period2 ends
        "iso_imm_precedes"
        Match documents whose period1 immediately precedes period2 in
        sql 2011 standard.  i.e. period1 ends at period2 ends

**`$axis-2`**
Name of the second period to compare

**`$options`** *(optional)*
Options to this query.  The default is ().
    
      Options include:
      
        "cached"
        Cache the results of this query in the list cache.
        "uncached"
        Do not cache the results of this query in the list cache.

### Returns

`cts:period-compare-query`

### Usage Notes

If you want to constrain on a range of period comparisons, you can combine multiple
  cts: constructors together
  with cts:and-query or any of the other composable
  cts:query constructors, as in the last part of the example
  below.
      If neither "cached" nor "uncached" is present, it specifies "cached".
      
    Negative "min-occurs" or "max-occurs" values will be treated as 0 and
    non-integral values will be rounded down.  An error will be raised if
    the "min-occurs" value is greater than the "max-occurs" value.

### Examples

```xquery
cts:period-compare-query("system","aln_overlaps","valid",
    "cached", xs:double("3.13"))
```

---

## cts:period-compare-query-axis-1

Returns the name of the first axis used to construct the specified query.

### Signature

```xquery
cts:period-compare-query-axis-1(
  $query as cts:period-compare-query
) as xs:string
```

### Parameters

**`$query`**
A query.

### Returns

`xs:string`

### Examples

```xquery
let $query :=
  cts:period-compare-query("system","aln_overlaps","valid",
    "cached", xs:double("3.13"))
return
  cts:period-compare-query-axis-1($query)
  => system
```

---

## cts:period-compare-query-axis-2

Returns the name of the second axis used to construct the specified query.

### Signature

```xquery
cts:period-compare-query-axis-2(
  $query as cts:period-compare-query
) as xs:string
```

### Parameters

**`$query`**
A query.

### Returns

`xs:string`

### Examples

```xquery
let $query :=
  cts:period-compare-query("system","aln_overlaps","valid",
    "cached", xs:double("3.13"))
return
  cts:period-compare-query-axis-2($query)
  => valid
```

---

## cts:period-compare-query-operator

Returns the operator used to construct the specified query.

### Signature

```xquery
cts:period-compare-query-operator(
  $query as cts:period-compare-query
) as xs:string
```

### Parameters

**`$query`**
A query.

### Returns

`xs:string`

### Examples

```xquery
let $query :=
  cts:period-compare-query("system","aln_overlaps","valid",
    "cached", xs:double("3.13"))
return
  cts:period-compare-query-operator($query)
  => aln_overlaps
```

---

## cts:period-compare-query-options

Returns the options for the specified query.

### Signature

```xquery
cts:period-compare-query-options(
  $query as cts:period-compare-query
) as xs:string*
```

### Parameters

**`$query`**
A query.

### Returns

`xs:string*`

### Examples

```xquery
let $query :=
  cts:period-compare-query("system","aln_overlaps","valid",
    "cached", xs:double("3.13"))
return
  cts:period-compare-query-options($query)
  => cached
```

---

## cts:period-range-query

Returns a cts:query matching axis by name with a
  period value with an operator.  Searches with the
  cts:period-range-query
  constructor require a axis definition on the axis name;
  if there is no axis configured, then an exception is thrown.

### Signature

```xquery
cts:period-range-query(
  $axis-name as xs:string*,
  $operator as xs:string,
  $period as cts:period*?,
  $options as xs:string*?
) as cts:period-range-query
```

### Parameters

**`$axis-name`**
One or more axis to match on.

**`$operator`**
A comparison operator.
    
      Operators include:
      
        "aln_equals"
        Match documents whose period1 equals value.
        "aln_contains"
        Match documents whose period1 contains value. i.e. period1 starts
        before value starts and ends before value ends.
        "aln_contained_by"
        Match documents whose period1 is contained by value.
        "aln_meets"
        Match documents whose period1 meets value, i.e. period1 ends at
        value start.
        "aln_met_by"
        Match documents whose period1 meets value, i.e. period1 starts at
        value end.
        "aln_before"
        Match documents whose period1 is before value, i.e. period1 ends
        before value starts.
        "aln_after"
        Match documents whose period1 is after value, i.e. period1 starts
        after value ends.
        "aln_starts"
        Match documents whose period1 starts value, i.e. period1 starts at
        value start and ends before value ends.
        "aln_started_by"
        Match documents whose value starts period1, i.e. period1 starts at
        value start and ends after value ends.
        "aln_finishes"
        Match documents whose period1 finishes value, i.e. period1
        finishes at value finish and starts after value starts.
        "aln_finished_by"
        Match documents whose value finishes period1, i.e. period1
        finishes at value finish and starts before value starts.
        "aln_overlaps"
        Match documents whose period1 overlaps value, i.e. period1 starts
        before value start and ends before value ends but after value
        starts.
        "aln_overlapped_by"
        Match documents whose value overlaps period1, i.e. period1
        starts after value start but before value ends and ends after
        value ends.
        "iso_contains"
        Match documents whose period1 contains value in sql 2011 standard.
        i.e. period1 starts before or at value starts and ends after or at
        value ends.
        "iso_overlaps"
        Match documents whose period1 overlaps value in sql 2011 standard.
        i.e. period1 and value have common time period.
        "iso_succeeds"
        Match documents whose period1 succeeds value in sql 2011 standard.
        i.e. period1 starts at or after value ends
        "iso_precedes"
        Match documents whose period1 precedes value in sql 2011 standard.
        i.e. period1 ends at or before value ends
        "iso_imm_succeeds"
        Match documents whose period1 immediately succeeds value in
        sql 2011 standard.
        i.e. period1 starts at value end
        "iso_imm_precedes"
        Match documents whose period1 immediately precedes value in
        sql 2011 standard.
        i.e. period1 ends at value end

**`$period`** *(optional)*
the cts:period to perform operations on.
    When multiple values are specified,
    the query matches if any value matches.

**`$options`** *(optional)*
Options to this query.  The default is ().
    
      Options include:
      
        "cached"
        Cache the results of this query in the list cache.
        "uncached"
        Do not cache the results of this query in the list cache.
        "min-occurs=number"
        Specifies the minimum number of occurrences required. If
        fewer that this number of words occur, the fragment does not match.
        The default is 1.
        "max-occurs=number"
        Specifies the maximum number of occurrences required.  If
        more than this number of words occur, the fragment does not match.
        The default is unbounded.
        "score-function=function"
        Use the selected scoring function. The score function may be:
          
          linearUse a linear function of the difference between the
          specified query value and the matching value in the index to calculate
          a score for this range query.
          reciprocalUse a reciprocal function of the difference
          between the specified query value and the matching value in the
          index to calculate a score for this range query.
          
          zeroThis range query does not contribute to the
          score. This is the default.
        
        "slope-factor=number"
        Apply the given number as a scaling factor to the slope of the
        scoring function. The default is 1.0.

### Returns

`cts:period-range-query`

### Usage Notes

If you want to constrain on a range of values, you can combine multiple
  cts:period-range-query constructors together
  with cts:and-query or any of the other composable
  cts:query constructors, as in the last part of the example
  below.
      If neither "cached" nor "uncached" is present, it specifies "cached".
      
    Negative "min-occurs" or "max-occurs" values will be treated as 0 and
    non-integral values will be rounded down.  An error will be raised if
    the "min-occurs" value is greater than the "max-occurs" value.
  
      "score-function=linear" means that values that are further away from
  the bounds will score higher. "score-function=reciprocal" means that values
  that are closer to the bounds will score higher. The functions are scaled
  appropriately for different types, so that in general the default slope
  factor will provide useful results. Using a slope factor greater than
  1 gives distinct scores over a smaller range of values, and produces
  generally higher scores.  Using a slope factor less than 1 gives
  distinct scores over a wider range of values, and produces generally
  lower scores.

### Examples

```xquery
let $period := cts:period(xs:dateTime("2001-05-31T09:30:10-08:00"),
                          xs:dateTime("2003-05-31T09:30:10-08:00"))
let $query := cts:period-range-query("period1","aln_equals", $period)
return
cts:search(fn:doc(), $query)
  => documents matching the range query
```

---

## cts:period-range-query-axis

Returns the axis name used to construct the specified query.

### Signature

```xquery
cts:period-range-query-axis(
  $query as cts:period-range-query
) as xs:string*
```

### Parameters

**`$query`**
A query.

### Returns

`xs:string*`

### Examples

```xquery
let $period := cts:period(xs:dateTime("2001-05-31T09:30:10-08:00"),
                              xs:dateTime("2003-05-31T09:30:10-08:00"))
let $query := cts:period-range-query("period1","aln_equals", $period)
return
cts:period-range-query-axis($query)
  =>
    period1
```

---

## cts:period-range-query-operator

Returns the operator used to construct the specified query.

### Signature

```xquery
cts:period-range-query-operator(
  $query as cts:period-range-query
) as xs:string
```

### Parameters

**`$query`**
A query.

### Returns

`xs:string`

### Examples

```xquery
let $period := cts:period(xs:dateTime("2001-05-31T09:30:10-08:00"),
                          xs:dateTime("2003-05-31T09:30:10-08:00"))
let $query := cts:period-range-query("period1","aln_equals", $period)
return
cts:period-range-query-opertor($query)
  =>
    aln_equals
```

---

## cts:period-range-query-options

Returns the options for the specified query.

### Signature

```xquery
cts:period-range-query-options(
  $query as cts:period-range-query
) as xs:string*
```

### Parameters

**`$query`**
A query.

### Returns

`xs:string*`

### Examples

```xquery
let $period := cts:period(xs:dateTime("2001-05-31T09:30:10-08:00"),
                          xs:dateTime("2003-05-31T09:30:10-08:00"))
let $query := cts:period-range-query("period1","aln_equals", $period)
return
cts:period-range-query-options($query)
  => ()
```

---

## cts:period-range-query-period

Returns the period used to construct the specified query.

### Signature

```xquery
cts:period-range-query-period(
  $query as cts:period-range-query
) as xs:anyAtomicType*
```

### Parameters

**`$query`**
A query.

### Returns

`xs:anyAtomicType*`

### Examples

```xquery
let $period := cts:period(xs:dateTime("2001-05-31T09:30:10-08:00"),
                          xs:dateTime("2003-05-31T09:30:10-08:00"))
let $query := cts:period-range-query("period1","aln_equals", $period)
return
cts:period-range-query-period($query)
  =>
cts:period(xs:dateTime("2001-05-31T17:30:10"),
xs:dateTime("2003-05-31T17:30:10"))
```

---

## cts:properties-fragment-query

Returns a query that matches all documents where $query matches
  document-properties.  When searching documents or document-locks,
  this query type provides a convenient way to
  additionally constrain the search against document-properties fragments.

### Signature

```xquery
cts:properties-fragment-query(
  $query as cts:query
) as cts:properties-fragment-query
```

### Parameters

**`$query`**
A query to be matched against the properties fragment.

### Returns

`cts:properties-fragment-query`

### Examples

```xquery
cts:search(
  fn:collection(),
  cts:properties-fragment-query(
    cts:element-range-query(
        xs:QName("prop:last-modified"),">;",
        current-dateTime() - xs:dayTimeDuration("P1D"))))

(:  All documents modified up to one day in the past.
 :  Note that this example requires a dateTime range index on:
 :  namespace: http://marklogic.com/xdmp/property
 :  local name: last-modified :)
```

---

## cts:properties-fragment-query-query

Returns the query used to construct the specified query.

### Signature

```xquery
cts:properties-fragment-query-query(
  $query as cts:properties-fragment-query
) as cts:query
```

### Parameters

**`$query`**
A query.

### Returns

`cts:query`

### Examples

```xquery
cts:properties-fragment-query-query(
    cts:properties-fragment-query(cts:word-query("word")))
  => cts:word-query("word", ("lang=en"), 1)
```

---

## cts:query

Creates a query.

### Signature

```xquery
cts:query(
  $query as node()
) as cts:query
```

### Parameters

**`$query`**
A query.

### Returns

`cts:query`

### Examples

```xquery
cts:query(
  <cts:word-query xmlns:cts="http://marklogic.com/cts">
    <cts:text>word</cts:text>
  </cts:word-query>
)
```

---

## cts:range-query

Returns a cts:query matching specified nodes with a
  range-index entry compared to a given value.  Searches with the
  cts:range-query
  constructor require a range index;
  if there is no range index configured, then an exception is thrown.

### Signature

```xquery
cts:range-query(
  $index as cts:reference*,
  $operator as xs:string,
  $value as xs:anyAtomicType*,
  $options as xs:string*?,
  $weight as xs:double??
) as cts:range-query
```

### Parameters

**`$index`**
One or more range index references.
    When multiple indexes are specified,
    the query matches if any index matches.

**`$operator`**
A comparison operator.
    
      Operators include:
      
        "<"
        Match range index values less than $value.
        "<="
        Match range index values less than or equal to $value.
        ">"
        Match range index values greater than $value.
        ">="
        Match range index values greater than or equal to $value.
        "="
        Match range index values equal to $value.
        "!="
        Match range index values not equal to $value.

**`$value`**
One or more values to match.
    When multiple values are specified,
    the query matches if any value matches.

**`$options`** *(optional)*
Options to this query.  The default is ().
    
      Options include:
      
        "cached"
        Cache the results of this query in the list cache.
        "uncached"
        Do not cache the results of this query in the list cache.
        "min-occurs=number"
        Specifies the minimum number of occurrences required. If
        fewer that this number of words occur, the fragment does not match.
        The default is 1.
        "max-occurs=number"
        Specifies the maximum number of occurrences required.  If
        more than this number of words occur, the fragment does not match.
        The default is unbounded.
        "score-function=function"
        Use the selected scoring function. The score function may be:
          
          linearUse a linear function of the difference between the
          specified query value and the matching value in the index to calculate
          a score for this range query.
          reciprocalUse a reciprocal function of the difference
          between the specified query value and the matching value in the
          index to calculate a score for this range query.
          zeroThis range query does not contribute to the
          score. This is the default.
          
        
        "slope-factor=number"
        Apply the given number as a scaling factor to the slope of the
        scoring function. The default is 1.0.
        "synonym"
        Specifies that all of the terms in the $value parameter are
        considered synonyms for scoring purposes.  The result is that
        occurrences of more than one of the synonyms are scored as if
        there are more occurrences of the same term (as opposed to
        having a separate term that contributes to score).

**`$weight`** *(optional)*
A weight for this query.  The default is 1.0.

### Returns

`cts:range-query`

### Usage Notes

If you want to constrain on a range of values, you can combine multiple
  cts:range-query constructors together
  with cts:and-query or any of the other composable
  cts:query constructors, as in the last part of the example
  below.
      If neither "cached" nor "uncached" is present, it specifies "cached".
      
    Negative "min-occurs" or "max-occurs" values will be treated as 0 and
    non-integral values will be rounded down.  An error will be raised if
    the "min-occurs" value is greater than the "max-occurs" value.
  
      "score-function=linear" means that values that are further away from
  the bounds will score higher. "score-function=reciprocal" means that values
  that are closer to the bounds will score higher. The functions are scaled
  appropriately for different types, so that in general the default slope factor
  will provide useful results. Using a slope factor greater than 1 gives distinct
  scores over a smaller range of values, and produces generally higher scores.
  Using a slope factor less than 1 gives distinct scores over a wider range of
  values, and produces generally lower scores.

### Examples

```xquery
(: create a document with test data :)
xdmp:document-insert("/dates.xml",
<root>
  <entry>
    <date>2007-01-01</date>
    <info>Some information.</info>
  </entry>
  <entry>
    <date>2006-06-23</date>
    <info>Some other information.</info>
  </entry>
  <entry>
    <date>1971-12-23</date>
    <info>Some different information.</info>
  </entry>
</root>);

(:
   requires a range index of
   type xs:date on element "date"
:)
cts:search(doc("/dates.xml")/root/entry,
  cts:range-query(cts:element-reference(xs:QName("date")), "<=",
      xs:date("2000-01-01")))
(:
  returns the following node:
  <entry>
    <date>1971-12-23</date>
    <info>Some different information.</info>
  </entry>
:)
;
(:
   requires a range index of
   type xs:date on element "date"
:)
cts:search(doc("/dates.xml")/root/entry,
  cts:and-query((
   cts:range-query(cts:element-reference(xs:QName("date")), ">",
      xs:date("2006-01-01")),
   cts:range-query(cts:element-reference(xs:QName("date")), "<",
      xs:date("2008-01-01")))))
(:
  returns the following 2 nodes:
  <entry>
    <date>2007-01-01</date>
    <info>Some information.</info>
  </entry>

  <entry>
    <date>2006-06-23</date>
    <info>Some other information.</info>
  </entry>
:)
```

---

## cts:range-query-index

Returns the range index used to construct the specified query.

### Signature

```xquery
cts:range-query-index(
  $query as cts:range-query
) as xs:QName*
```

### Parameters

**`$query`**
A range query.

### Returns

`xs:QName*`

### Examples

```xquery
let $query := cts:range-query(cts:element-reference(xs:QName("date")), "<=",
      xs:date("2000-01-01"))
return
cts:range-query-index($query)
  => cts:element-reference(xs:QName("date"))
```

---

## cts:range-query-operator

Returns the operator used to construct the specified query.

### Signature

```xquery
cts:range-query-operator(
  $query as cts:range-query
) as xs:string
```

### Parameters

**`$query`**
A range query.

### Returns

`xs:string`

### Examples

```xquery
let $query := cts:range-query(xs:QName("date"), "<=",
      xs:date("2000-01-01"))
return
cts:range-query-operator($query)
  =>
     <=
```

---

## cts:range-query-options

Returns the options for the specified query.

### Signature

```xquery
cts:range-query-options(
  $query as cts:range-query
) as xs:string*
```

### Parameters

**`$query`**
A query.

### Returns

`xs:string*`

### Examples

```xquery
let $query := cts:range-query(xs:QName("date"), "<=",
      xs:date("2000-01-01"))
return
cts:range-query-options($query)
  => ()
```

---

## cts:range-query-value

Returns the value used to construct the specified query.

### Signature

```xquery
cts:range-query-value(
  $query as cts:range-query
) as xs:anyAtomicType*
```

### Parameters

**`$query`**
A query.

### Returns

`xs:anyAtomicType*`

### Examples

```xquery
let $query := cts:range-query(xs:QName("date"), "<=",
      xs:date("2000-01-01"))
return
cts:range-query-value($query)
  =>
     "2000-01-01" (as an xs.date)
```

---

## cts:range-query-weight

Returns the weight with which the specified query was constructed.

### Signature

```xquery
cts:range-query-weight(
  $query as cts:range-query
) as xs:double
```

### Parameters

**`$query`**
A query.

### Returns

`xs:double`

### Examples

```xquery
let $query := cts:range-query(xs:QName("date"), "<=",
      xs:date("2000-01-01"))
return
cts:range-query-weight($query)
  => 1
```

---

## cts:registered-query

Returns a query matching fragments specified by previously registered
  queries (see cts:register).  If
  the database is not empty and a registered query with the specified ID(s)
  is not found, then a cts:search operation with an invalid
  cts:registered-query throws an XDMP-UNREGISTERED exception.

### Signature

```xquery
cts:registered-query(
  $ids as xs:unsignedLong*,
  $options as xs:string*?,
  $weight as xs:double??
) as cts:registered-query
```

### Parameters

**`$ids`**
Some registered query identifiers.

**`$options`** *(optional)*
Options to this query.  The default is ().
    
      Options include:
      
        "filtered"
        A filtered query (the default). Filtered queries
        eliminate any false-positive results and properly resolve
        cases where there are multiple candidate matches within the same
        fragment, thereby guaranteeing
        that the results fully satisfy the original cts:query
        item that was registered.  This option is not currently available.
        "unfiltered"
        An unfiltered query.  Unfiltered registered queries
        select fragments from the indexes that are candidates to satisfy
        the cts:query.
        Depending on the original cts:query, the
        structure of the documents in the database, and the configuration
        of the database,
        unfiltered registered queries may result in false-positive results
        or in incorrect matches when there are multiple candidate matches
        within the same fragment.
        To avoid these problems, you should only use unfiltered queries
        on top-level XPath expressions (for example, document nodes,
        collections, directories) or on fragment roots. Using unfiltered
        queries on complex XPath expressions or on XPath expressions that
        traverse below a fragment root can result in unexpected results.
        This option is required in the current release.

**`$weight`** *(optional)*
A weight for this query.
    Higher weights move search results up in the relevance
    order.  The default is 1.0. The
    weight should be between 64 and -16.
    Weights greater than 64 will have the same effect as a
    weight of 64.
    Weights less than the absolute value of 0.0625 (between -0.0625 and
    0.0625) are rounded to 0, which means that they do not contribute to the
    score.

### Returns

`cts:registered-query`

### Usage Notes

Searches that use registered queries will generate results with 
 different scores than the equivalent searches using non-registered queries. 
 This is because registered queries are treated as a single term in 
 relevance calculations.
      If the options parameter does not contain "unfiltered",
then an error is returned, as the "unfiltered" option is required.
      Registered queries are persisted as a soft state only; they can
become unregistered through an explicit direction (using
cts:deregister),
as a result of the cache growing too large, or because of a server restart.
Consequently, either your XQuery code or your middleware layer should handle
the case when an XDMP-UNREGISTERED exception occurs (for example, you can
wrap your cts:registered-query code in a try/catch block
or your Java or .NET code can catch and handle the exception).
      Unfiltered queries, including registered queries, do not match in
 cts:walk or
 cts:highlight.

### Examples

#### Example 1

```xquery
cts:search(//function,
    cts:registered-query(1234567890123456,"unfiltered"))

  => .. relevance-ordered sequence of 'function' elements
  in any document that also matches the registered query
```

#### Example 2

```xquery
cts:search(fn:doc(),cts:registered-query(cts:register(cts:word-query("hello*world","wildcarded")), "unfiltered"))
```

---

## cts:registered-query-ids

Returns the registered query identifiers used to construct the specified
  query.

### Signature

```xquery
cts:registered-query-ids(
  $query as cts:registered-query
) as xs:unsignedLong*
```

### Parameters

**`$query`**
A query.

### Returns

`xs:unsignedLong*`

### Examples

```xquery
let $query := cts:registered-query(1234567890123456,"unfiltered")
return
cts:registered-query-ids($query)
  => 1234567890123456
```

---

## cts:registered-query-options

Returns the options for the specified query.

### Signature

```xquery
cts:registered-query-options(
  $query as cts:registered-query
) as xs:string*
```

### Parameters

**`$query`**
A query.

### Returns

`xs:string*`

### Examples

```xquery
let $query := cts:registered-query(1234567890123456,"unfiltered")
return
cts:registered-query-options($query)
  => "unfiltered"
```

---

## cts:registered-query-weight

Returns the weight with which the specified query was constructed.

### Signature

```xquery
cts:registered-query-weight(
  $query as cts:registered-query
) as xs:double
```

### Parameters

**`$query`**
A query.

### Returns

`xs:double`

### Examples

```xquery
let $query := cts:registered-query(1234567890123456,"unfiltered")
return
cts:registered-query-weight($query)
  => 1
```

---

## cts:reverse-query

Construct a query that matches serialized cts queries, based on a
  set of model input nodes. A serialized query matches if it would
  match the model nodes. Use with a cts:search or
  cts:contains over serialized cts:query nodes.

### Signature

```xquery
cts:reverse-query(
  $nodes as node()*,
  $weight as xs:double??
) as cts:reverse-query
```

### Parameters

**`$nodes`**
Model nodes that must be matchable by queries matched by this
    reverse query. See the Usage Notes for more details.

**`$weight`** *(optional)*
A weight for this query. This parameter has no effect because a reverse
    query does not contribute to score. That is, the score is always 0.

### Returns

`cts:reverse-query`

### Usage Notes

A reverse query matches serialized cts:query nodes.
    Construct a reverse query from nodes that model what that
    serialized query should match, rather than passing in the target query.
    For example, to match queries for the word "hello", specify a node
    containing the word "hello" as the nodes parameter.
    See the example, below. Reverse queries are useful for creating
    alerting applications.
      When evaluating a cts:reverse-query on a
    set of nodes, the cts:similar-query or
    cts:registered-query components of any stored query will
    match all nodes.
      
   You can create a node or document containing a serialized
    cts:query in XQuery by wrapping a cts:query
    constructor in an XML node. For example, the following snippet creates
    an XML element (foo) that contains a serialized word query:
    
    <foo>{cts:word-query("my search")}</foo>/element()
    
   
      A reverse query can match both the XML and JSON representations of
    a serialized query.

### Examples

```xquery
let $content := <query>{cts:word-query("hello")}</query>
let $model-node := <bar>hello</bar>
return
cts:contains($content, cts:reverse-query($model-node))
(:
   Returns true because the content contains a cts:word-query
   for "hello", which would match the model node. Here, the content is
   an in-memory node, but it could also be a document (or node) in the
   database.
:)
```

---

## cts:reverse-query-nodes

Returns the nodes used to construct the specified query.

### Signature

```xquery
cts:reverse-query-nodes(
  $query as cts:reverse-query
) as node()*
```

### Parameters

**`$query`**
A query.

### Returns

`node()*`

### Examples

```xquery
let $query := <query>{cts:word-query("hello")}</query>
let $x := <bar>hello</bar>
let $rev := cts:reverse-query($x)
return cts:reverse-query-nodes($rev)

  => <bar>hello</bar>
```

---

## cts:reverse-query-weight

Returns the weight with which the specified query was constructed.

### Signature

```xquery
cts:reverse-query-weight(
  $query as cts:reverse-query
) as xs:double
```

### Parameters

**`$query`**
A query.

### Returns

`xs:double`

### Examples

```xquery
let $query := <query>{cts:word-query("hello")}</query>
let $x := <bar>hello</bar>
let $rev := cts:reverse-query($x)
return cts:reverse-query-weight($rev)

  => 1
```

---

## cts:similar-query

Returns a query matching nodes similar to the model nodes.  It uses an
  algorithm which finds the most "relevant" terms in the model nodes
  (that is, the terms with the highest scores), and then creates a
  query equivalent to a cts:or-query of those terms.  By default
  16 terms are used.

### Signature

```xquery
cts:similar-query(
  $nodes as node()*,
  $weight as xs:double??,
  $options as element()??
) as cts:similar-query
```

### Parameters

**`$nodes`**
Some model nodes.

**`$weight`** *(optional)*
A weight for this query.
    Higher weights move search results up in the relevance
    order.  The default is 1.0. The
    weight should be between 64 and -16.
    Weights greater than 64 will have the same effect as a
    weight of 64.
    Weights less than the absolute value of 0.0625 (between -0.0625 and
    0.0625) are rounded to 0, which means that they do not contribute to the
    score.

**`$options`** *(optional)*
An XML representation of
     the options for defining
    which terms to generate and how to evaluate them.
    The options node must be in the
    cts:distinctive-terms namespace. The following is
    a sample options node
    :
    
    <options xmlns="cts:distinctive-terms">
      <max-terms>20</max-terms>
    </options> 
    

    See the
    cts:distinctive-terms
    options for the valid options to use with this function.
    
    Note that enabling index settings that
    are disabled in the database configuration will not affect the results,
    as similar documents will not be found on the basis of terms that do
    not exist in the actual database index.

### Returns

`cts:similar-query`

### Usage Notes

As the number of fragments in a database grows, the results
   of cts:similar-query
    become
   increasingly accurate. For best results, there should be at least 10,000
   fragments for 32-bit systems, and 1,000 fragments for 64-bit systems.

### Examples

#### Example 1

```xquery
cts:search(//function,
    cts:similar-query((//function)[1]))
  
  => .. relevance-ordered sequence of 'function' element
  ancestors (or self) of any node similar to the first
  'function' element.
```

#### Example 2

```xquery
xdmp:estimate(
  cts:search(//function,
    cts:similar-query((//function)[1], (),
    <options xmlns="cts:distinctive-terms">
      <max-terms>20</max-terms>
      <use-db-config>true</use-db-config>
    </options>)))
=> the number of fragments containing any node similar
   to the first 'function' element.
```

---

## cts:similar-query-nodes

Returns the nodes used to construct the specified query.

### Signature

```xquery
cts:similar-query-nodes(
  $query as cts:similar-query
) as node()*
```

### Parameters

**`$query`**
A query.

### Returns

`node()*`

### Examples

```xquery
let $query := cts:similar-query(fn:doc("/mydoc.xml"))
return cts:similar-query-nodes($query)
```

---

## cts:similar-query-weight

Returns the weight with which the specified query was constructed.

### Signature

```xquery
cts:similar-query-weight(
  $query as cts:similar-query
) as xs:double
```

### Parameters

**`$query`**
A query.

### Returns

`xs:double`

### Examples

```xquery
let $query := cts:similar-query(fn:doc("/mydoc.xml"))
return cts:similar-query-weight($query)
```

---

## cts:triple-range-query

Returns a 
  cts:query
  matching triples with a
  triple index entry equal to the given values. Searches with the
  cts:triple-range-query
  constructor require the triple index;
  if the triple index is not configured, then an exception is thrown.

### Signature

```xquery
cts:triple-range-query(
  $subject as xs:anyAtomicType*,
  $predicate as xs:anyAtomicType*,
  $object as xs:anyAtomicType*,
  $operator as xs:string*?,
  $options as xs:string*?,
  $weight as xs:double??
) as cts:triple-range-query
```

### Parameters

**`$subject`**
The subjects to look up.
    When multiple values are specified, the query matches if any value matches.
    When the empty sequence is specified, then triples with any subject are
    matched.

**`$predicate`**
The predicates to look up.
    When multiple values are specified, the query matches if any value matches.
    When the empty sequence is specified, then triples with any predicate are
    matched.

**`$object`**
The objects to look up.
    When multiple values are specified, the query matches if any value matches.
    When the empty sequence is specified, then triples with any object are
    matched.

**`$operator`** *(optional)*
If a single string is provided it is treated as the operator for the
    $object values. If a sequence of three strings are provided, they give
    the operators for $subject, $predicate and $object in turn.
    The default operator is "=".
    
      Operators include:
      
        "sameTerm"
        Match triple index values which are the same RDF term as $value.
        This compares aspects of values that are ignored in XML Schema
        comparison semantics,
        like timezone and derived type of $value.
        "<"
        Match range index values less than $value.
        "<="
        Match range index values less than or equal to $value.
        ">"
        Match range index values greater than $value.
        ">="
        Match range index values greater than or equal to $value.
        "="
        Match range index values equal to $value.
        "!="
        Match range index values not equal to $value.

**`$options`** *(optional)*
Options to this query.  The default is ().
    
      Options include:
      
        "cached"
        Cache the results of this query in the list cache.
        "uncached"
        Do not cache the results of this query in the list cache.
        "score-function=function"
        Use the selected scoring function. The score function may be:
          
          linearUse a linear function of the difference between the
          specified query value and the matching value in the index to calculate
          a score for this range query.
          reciprocalUse a reciprocal function of the difference
          between the specified query value and the matching value in the
          index to calculate a score for this range query.
          zeroThis range query does not contribute to the
          score. This is the default.
          
        
        "slope-factor=number"
        Apply the given number as a scaling factor to the slope of the
        scoring function. The default is 1.0.

**`$weight`** *(optional)*
A weight for this query.  The default is 1.0.

### Returns

`cts:triple-range-query`

### Usage Notes

If you want to constrain on a range of values, you can combine multiple
  cts:triple-range-query
  constructors together
  with 
  cts:and-query
  or any of the other composable
  cts:query
  constructors.
      If neither "cached" nor "uncached" is present, it specifies "cached".
      "score-function=linear" means that values that are further away from
  the bounds will score higher. "score-function=reciprocal" means that values
  that are closer to the bounds will score higher. The functions are scaled
  appropriately for different types, so that in general the default slope
  factor will provide useful results. Using a slope factor greater than
  1 gives distinct scores over a smaller range of values, and produces
  generally higher scores.  Using a slope factor less than 1 gives distinct
  scores over a wider range of values, and produces generally lower scores.

### Examples

```xquery
xquery version "1.0-ml";
import module namespace sem = "http://marklogic.com/semantics" at
"/MarkLogic/semantics.xqy";
(: insert a couple of triples :)

sem:rdf-insert(
  sem:triple(sem:iri("http://example.com/ns/directory#m"),
             sem:iri("http://example.com/ns/person#firstName"),
             "Mark"),
  "override-graph=test1") ,
sem:rdf-insert(
  sem:triple(sem:iri("http://example.com/Mark"),
             sem:iri("http://example.com/ns/person#age"),
             37),
  "override-graph=test1")

 =>
 /triplestore/46a9deab2e3d1e5a.xml
 /triplestore/b954ee9d04dc536d.xml


xquery version "1.0-ml";
import module namespace sem = "http://marklogic.com/semantics"
    at "/MarkLogic/semantics.xqy";
(: find all documents that have an embedded triple matching Mark-less-than-50 :)

let $query :=
  cts:triple-range-query(
    sem:iri("http://example.com/Mark"),
    sem:iri("http://example.com/ns/person#age"),
    50,
    "<")
return cts:search(fn:collection()//sem:triple, $query)

=>
<sem:triple xmlns:sem="http://marklogic.com/semantics">
  <sem:subject>http://example.com/Mark</sem:subject>
  <sem:predicate>http://example.com/ns/person#age</sem:predicate>
  <sem:object
    datatype="http://www.w3.org/2001/XMLSchema#integer">37</sem:object>
</sem:triple>
```

---

## cts:triple-range-query-object

Returns the object value used to construct the specified query.

### Signature

```xquery
cts:triple-range-query-object(
  $query as cts:triple-range-query
) as xs:anyAtomicType*
```

### Parameters

**`$query`**
A query.

### Returns

`xs:anyAtomicType*`

### Examples

```xquery
let $query :=
  cts:triple-range-query(
    sem:iri("http://example.com/Mark"),
    sem:iri("http://example.com/ns/person#age"),
    50,
    "<")
return
cts:triple-range-query-object($query)
  => 50
```

---

## cts:triple-range-query-operator

Returns the operators used to construct the specified query.

### Signature

```xquery
cts:triple-range-query-operator(
  $query as cts:triple-range-query
) as xs:string*
```

### Parameters

**`$query`**
A query.

### Returns

`xs:string*`

### Examples

```xquery
let $query :=
  cts:triple-range-query(
    sem:iri("http://example.com/Mark"),
    sem:iri("http://example.com/ns/person#age"),
    50,
    "<")
return
cts:triple-range-query-operator($query)
  =>
    =
    =
    <
```

---

## cts:triple-range-query-options

Returns the options for the specified query.

### Signature

```xquery
cts:triple-range-query-options(
  $query as cts:triple-range-query
) as xs:string*
```

### Parameters

**`$query`**
A query.

### Returns

`xs:string*`

### Examples

```xquery
let $query :=
  cts:triple-range-query(
    sem:iri("http://example.com/Mark"),
    sem:iri("http://example.com/ns/person#age"),
    50,
    "<")
return
cts:triple-range-query-options($query)
  => ()
```

---

## cts:triple-range-query-predicate

Returns the predicate value used to construct the specified query.

### Signature

```xquery
cts:triple-range-query-predicate(
  $query as cts:triple-range-query
) as xs:anyAtomicType*
```

### Parameters

**`$query`**
A query.

### Returns

`xs:anyAtomicType*`

### Examples

```xquery
let $query :=
  cts:triple-range-query(
    sem:iri("http://example.com/Mark"),
    sem:iri("http://example.com/ns/person#age"),
    50,
    "<")
return
cts:triple-range-query-predicate($query)
  => http://example.com/ns/person#age
```

---

## cts:triple-range-query-subject

Returns the subject value used to construct the specified query.

### Signature

```xquery
cts:triple-range-query-subject(
  $query as cts:triple-range-query
) as xs:anyAtomicType*
```

### Parameters

**`$query`**
A query.

### Returns

`xs:anyAtomicType*`

### Examples

```xquery
let $query :=
  cts:triple-range-query(
    sem:iri("http://example.com/Mark"),
    sem:iri("http://example.com/ns/person#age"),
    50,
    "<")
return
cts:triple-range-query-subject($query)
  => <http://example.com/Mark>
```

---

## cts:triple-range-query-weight

Returns the weight with which the specified query was constructed.

### Signature

```xquery
cts:triple-range-query-weight(
  $query as cts:triple-range-query
) as xs:double
```

### Parameters

**`$query`**
A query.

### Returns

`xs:double`

### Examples

```xquery
let $query :=
  cts:triple-range-query(
    sem:iri("http://example.com/Mark"),
    sem:iri("http://example.com/ns/person#age"),
    50,
    "<")
return
cts:triple-range-query-weight($query)
  => 1
```

---

## cts:true-query

Returns a query that matches all fragments.

### Returns

`cts:and-query`

### Examples

```xquery
cts:search(fn:doc(),cts:true-query())
  =&gt; all documents in database
```

---

## cts:word-query

Returns a query matching text content containing a given phrase.

### Signature

```xquery
cts:word-query(
  $text as xs:string*,
  $options as xs:string*?,
  $weight as xs:double??
) as cts:word-query
```

### Parameters

**`$text`**
Some words or phrases to match.
    When multiple strings are specified,
    the query matches if any string matches.

**`$options`** *(optional)*
Options to this query.  The default is ().
    
      Options include:
      
        "case-sensitive"
        A case-sensitive query.
        "case-insensitive"
        A case-insensitive query.
        "diacritic-sensitive"
        A diacritic-sensitive query.
        "diacritic-insensitive"
        A diacritic-insensitive query.
        "punctuation-sensitive"
        A punctuation-sensitive query.
        "punctuation-insensitive"
        A punctuation-insensitive query.
        "whitespace-sensitive"
        A whitespace-sensitive query.
        "whitespace-insensitive"
        A whitespace-insensitive query.
        "stemmed"
        A stemmed query.
        "unstemmed"
        An unstemmed query.
        "wildcarded"
        A wildcarded query.
        "unwildcarded"
        An unwildcarded query.
        "exact"
        An exact match query. Shorthand for "case-sensitive",
        "diacritic-sensitive", "punctuation-sensitive",
        "whitespace-sensitive", "unstemmed", and "unwildcarded".
        
        "lang=iso639code"
        Specifies the language of the query. The iso639code
            code portion is case-insensitive, and uses the languages
            specified by
           ISO 639.
            The default is specified in the database configuration.
        "distance-weight=number"
        A weight applied based on the minimum distance between matches
        of this query.  Higher weights add to the importance of
        proximity (as opposed to term matches) when the relevance order is
        calculated.
        The default value is 0.0 (no impact of proximity). The
        weight should be between 64 and -16.
        Weights greater than 64 will have the same effect as a
        weight of 64.
        This parameter has no effect if the word positions
        index is not enabled.  This parameter has no effect on searches that
        use score-simple, score-random, or score-zero (because those scoring
        algorithms do not consider term frequency, proximity is irrelevant).
        
        "min-occurs=number"
        Specifies the minimum number of occurrences required. If
        fewer that this number of words occur, the fragment does not match.
        The default is 1.
        "max-occurs=number"
        Specifies the maximum number of occurrences required.  If
        more than this number of words occur, the fragment does not match.
        The default is unbounded.
        "synonym"
        Specifies that all of the terms in the $text parameter are
        considered synonyms for scoring purposes.  The result is that
        occurrences of more than one of the synonyms are scored as if
        there are more occurrences of the same term (as opposed to
        having a separate term that contributes to score). 
        "lexicon-expand=value"
        The value is one of full,
        prefix-postfix, off, or
        heuristic (the default is heuristic).
        An option with a value of lexicon-expand=full
        specifies that wildcards are resolved by expanding the pattern to
        words in a lexicon (if there is one available), and turning into a
        series of cts:word-queries, even if this takes a long
        time to evaluate.
        An option with a value of lexicon-expand=prefix-postfix
        specifies that wildcards are resolved by expanding the pattern to the
        pre- and postfixes of the words in the word lexicon (if there is one),
        and turning the query into a series of character queries, even if it
        takes a long time to evaluate.
        An option with a value of lexicon-expand=off
        specifies that wildcards are only resolved by looking up character
        patterns in the search pattern index, not in the lexicon.
        An option with a value of lexicon-expand=heuristic,
        which is the default, specifies that wildcards are resolved by using
        a series of internal rules, such as estimating the number of lexicon
        entries that need to be scanned, seeing if the estimate crosses
        certain thresholds, and (if appropriate), using another way besides
        lexicon expansion to resolve the query.
        
        "lexicon-expansion-limit=number"
        Specifies the limit for lexicon expansion. This puts a restriction
  on the number of lexicon expansions that can be performed. If the limit is
  exceeded, the server may raise an error depending on whether the "limit-check"
  option is set. The default value for this option will be 4096.
        
        "limit-check"
        Specifies that an error will be raised if the lexicon expansion
  exceeds the specified limit.
        "no-limit-check"
        Specifies that error will not be raised if the lexicon expansion
  exceeds the specified limit. The server will try to resolve the wildcard.
  "no-limit-check" is default, if neither "limit-check" nor "no-limit-check" is explicitly
  specified.

**`$weight`** *(optional)*
A weight for this query.
    Higher weights move search results up in the relevance
    order.  The default is 1.0. The
    weight should be between 64 and -16.
    Weights greater than 64 will have the same effect as a
    weight of 64.
    Weights less than the absolute value of 0.0625 (between -0.0625 and
    0.0625) are rounded to 0, which means that they do not contribute to the
    score.

### Returns

`cts:word-query`

### Usage Notes

If neither "case-sensitive" nor "case-insensitive"
    is present, $text is used to determine case sensitivity.
    If $text contains no uppercase, it specifies "case-insensitive".
    If $text contains uppercase, it specifies "case-sensitive".
  
      
    If neither "diacritic-sensitive" nor "diacritic-insensitive"
    is present, $text is used to determine diacritic sensitivity.
    If $text contains no diacritics, it specifies "diacritic-insensitive".
    If $text contains diacritics, it specifies "diacritic-sensitive".
  
      
    If neither "punctuation-sensitive" nor "punctuation-insensitive"
    is present, $text is used to determine punctuation sensitivity.
    If $text contains no punctuation, it specifies "punctuation-insensitive".
    If $text contains punctuation, it specifies "punctuation-sensitive".
  
      
    If neither "whitespace-sensitive" nor "whitespace-insensitive"
    is present, the query is "whitespace-insensitive".
  
      
    If neither "wildcarded" nor "unwildcarded"
    is present, the database configuration and $text determine wildcarding.
    If the database has any wildcard indexes enabled ("three character
    searches", "two character searches", "one character searches",  or
    "trailing wildcard searches") and if $text contains either of the
    wildcard characters '?' or '*', it specifies "wildcarded".
    Otherwise it specifies "unwildcarded".
  
      
    If neither "stemmed" nor "unstemmed"
    is present, the database configuration determines stemming.
    If the database has "stemmed searches" enabled, it specifies "stemmed".
    Otherwise it specifies "unstemmed".
    If the query is a wildcarded query and also a phrase query
    (contains two or more terms), the wildcard terms in the query
    are unstemmed.
  
      
    Negative "min-occurs" or "max-occurs" values will be treated as 0 and
    non-integral values will be rounded down.  An error will be raised if
    the "min-occurs" value is greater than the "max-occurs" value.
  
      Relevance adjustment for the "distance-weight" option depends on
  the closest proximity of any two matches of the query.  For example,
  
  cts:word-query(("dog","cat"),("distance-weight=10"))
  
  will adjust relevance based on the distance between the closest pair of
  matches of either "dog" or "cat" (the pair may consist only of matches of
  "dog", only of matches of "cat", or a match of "dog" and a match of "cat").

### Examples

#### Example 1

```xquery
cts:search(//function,
    cts:word-query("MarkLogic Corporation"))

  => .. relevance-ordered sequence of 'function' element
  ancestors (or self) of any node containing the phrase
  'MarkLogic Corporation'.
```

#### Example 2

```xquery
cts:search(//function,
    cts:word-query("MarkLogic Corporation",
                   "case-insensitive"))
  => .. relevance-ordered sequence of 'function'
  element ancestors (or self) of any node containing
  the phrase 'MarkLogic Corporation' or any other
  case-shift like 'MarkLogic Corporation',
  'MARKLOGIC Corporation', etc.
```

#### Example 3

```xquery
cts:search(//SPEECH,
    cts:word-query("to be, or not to be",
                   "punctuation-insensitive"))

  => .. relevance-ordered sequence of 'SPEECH'
  element ancestors (or self) of any node
  containing the phrase 'to be, or not to be',
  ignoring punctuation.
```

#### Example 4

```xquery
(:
   the following query uses the "synonym" option to make the
   terms "cat" and "kitty" treated the same for scoring
   purposes
:)
cts:search(fn:collection(),
   cts:word-query(("cat", "kitty"), "synonym") )
 => Returns relevance-ordered documents containing
    at least one of the specified terms, where the
    words "cat" and "kitty" are treated, for scoring
    purposes, as if they are both the word "cat".
    Without the synonym option, there would be one
    contribution to the score from "cat" matches and
    one from "kitty" matches.
```

---

## cts:word-query-options

Returns the options for the specified query.

### Signature

```xquery
cts:word-query-options(
  $query as cts:word-query
) as xs:string*
```

### Parameters

**`$query`**
A query.

### Returns

`xs:string*`

### Examples

```xquery
cts:word-query-options($query)
  => ("case-sensitive", "punctuation-insensitive")
```

---

## cts:word-query-text

Returns the text used to construct the specified query.

### Signature

```xquery
cts:word-query-text(
  $query as cts:word-query
) as xs:string*
```

### Parameters

**`$query`**
A query.

### Returns

`xs:string*`

### Examples

```xquery
cts:word-query-text($query)
  => "choice of law"
```

---

## cts:word-query-weight

Returns the weight with which the specified query was constructed.

### Signature

```xquery
cts:word-query-weight(
  $query as cts:word-query
) as xs:double
```

### Parameters

**`$query`**
A query.

### Returns

`xs:double`

### Examples

```xquery
cts:word-query-weight($query)
  => 1
```

---
