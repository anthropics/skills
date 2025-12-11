# Search

7 functions in this category.

## cts:estimate

Returns the number of fragments selected by a search.
  This can be used as a fast estimate of the number of results.
  
  To retrieve the number of fragments using an XPath expression, use
  xdmp:estimate instead.

### Signature

```xquery
cts:estimate(
  $query as cts:query?,
  $options as (cts:order|xs:string)*?,
  $quality-weight as xs:double??,
  $forest-ids as xs:unsignedLong*?,
  $maximum as xs:double??
) as xs:integer
```

### Parameters

**`$query`**
A cts:query specifying the search to perform.  If a string
   is entered, the string is treated as a cts.wordQuery of the
   specified string.

**`$options`** *(optional)*
Options to this search.  The default is ().
    See cts.search
    for details on available options.

**`$quality-weight`** *(optional)*
A document quality weight to use when computing scores.
    The default is 1.0.

**`$forest-ids`** *(optional)*
A sequence of IDs of forests to which the search will be constrained.
    An empty sequence means to search all forests in the database.
    The default is (). In the XQuery version, you can use
    cts:search with this
    parameter and an empty cts:and-query to specify a
    forest-specific XPath statement (see the
    third
    example below). If you
    use this to constrain an XPath to one or more forests, you should set
    the quality-weight to zero to keep the XPath document
    order.

**`$maximum`** *(optional)*
The maximum value to return.
    Stop selecting fragments if this number is reached.

### Returns

`xs:integer`

### Examples

```xquery
cts:estimate(cts:word-query("unsually"))
   => 10476
```

---

## xdmp:diacritic-less

Returns the specified string, converting all of the characters with diacritics
to characters without diacritics.

### Signature

```xquery
xdmp:diacritic-less(
  $string as xs:string
) as xs:string
```

### Parameters

**`$string`**
The string to convert.

### Returns

`xs:string`

### Examples

```xquery
xdmp:diacritic-less("José")
=> Jose
```

---

## xdmp:estimate

Returns the number of fragments selected by an expression.
  This can be used as a fast estimate of the number of items in a sequence.
  To retrieve the number of fragments using a 
  
  cts:query
  object, use
  
  cts:estimate
  instead.

### Signature

```xquery
xdmp:estimate(
  $expression as item()*,
  $maximum as xs:double??
) as xs:integer
```

### Parameters

**`$expression`**
The expression to estimate.
    This must be a partially searchable XPath expression
    or a cts:search() expression.

**`$maximum`** *(optional)*
The maximum value to return.
    Stop selecting fragments if this number is reached.

### Returns

`xs:integer`

### Usage Notes

Queries that use xdmp:estimate require that the XPath
    expression searched is partially searchable.
    A partially searchable XPath expression is one whose first step
    is searchable. You can use xdmp:query-trace() to determine
    if a step is searchable.  If there are no entries in the
    xdmp:query-trace() output indicating that the first step
    is unsearchable, then the expression is partially searchable
    and you can perform an xdmp:estimate operation on it.

---

## xdmp:exists

Returns true if any fragment is selected by an expression, false if no
  fragments are selected.  This can be used as a fast existence check.

### Signature

```xquery
xdmp:exists(
  $expression as item()*
) as xs:boolean
```

### Parameters

**`$expression`**
The expression to check.
    This must be a partially searchable XPath expression
    or a cts:search() expression.

### Returns

`xs:boolean`

### Usage Notes

Queries that use xdmp:exists require that the XPath
    expression searched is partially searchable.
    A partially searchable XPath expression is one whose first step
    is searchable. You can use xdmp:query-trace() to determine
    if a step is searchable.  If there are no entries in the
    xdmp:query-trace() output indicating that the first step
    is unsearchable, then the expression is partially searchable
    and you can perform an xdmp:exists operation on it.
      Calling xdmp:exists on an expression is the same as
    calling xdmp:estimate on the expression with a maximum of 1.
    For example, the following are equivalent:
    
     xdmp:exists(cts:search(collection(), "foo"))

       is equivalent to:

     xs:boolean(xdmp:estimate(cts:search(collection(), "foo"), 1))

---

## xdmp:plan

Returns an XML element recording information about how the given
  expression will be processed by the index.  The information is a
  structured representation of the information provided in the error log
  when query trace is enabled.  The query will be processed up to the
  point of getting an estimate of the number of fragments returned by the
  index.

### Signature

```xquery
xdmp:plan(
  $expression as item()*,
  $maximum as xs:double??
) as element()
```

### Parameters

**`$expression`**
The expression to estimate.
    This must be a partially searchable XPath expression
    or a cts:search() expression.

**`$maximum`** *(optional)*
The maximum value to return.
    Stop selecting fragments if this number is reached.

### Returns

`element()`

### Usage Notes

The output from xdmp:plan will vary depending on various index
  settings.
      Running an xdmp:plan on a search is similar to running an
  xdmp:estimate on a search, but it returns a report on the
  search instead of just an estimate. As part of the report, the
  qry:result element includes the estimate.
  If the search expression argument cannot be run in the
  plan because it is not partially searchable, then an
  XDMP-UNSEARCHABLE exception is returned as part of the
  xdmp:plan output. 
      If you are running a search using the search API
  (for example, search:search), use the
  option <return-plan>true</return-plan> in your
  search API options node.

---

## xdmp:plannable

Returns a boolean showing whether the given expression is suitable to use
  with xdmp:plan.  Expressions that are fully searchable are
  "plannable"; that is, they will return query plan output when used with
  xdmp:plan.

### Signature

```xquery
xdmp:plannable(
  $expression as item()*
) as xs:boolean
```

### Parameters

**`$expression`**
The expression to determine if it is plannable.

### Returns

`xs:boolean`

### Usage Notes

Behaves the same as "Analyzing path for search" in
  xdmp:plan. When true is returned, the expression
  could be planned by xdmp:plan, otherwise the expression
  would throw an XDMP-UNSEARCHABLE exception when run in
  xdmp:plan.

---

## xdmp:request-timestamp

Returns the system timestamp for this request if the request is a query
  statement.  Returns the empty sequence if the current request is an update
  statement.

### Returns

`xs:unsignedLong?`

### Usage Notes

The xdmp:request-timestamp
  
  function returns the system
  timestamp that is in effect for current query.  This timestamp will
  remain unchanged for the duration of the query. If you want to get
  the most recent system timestamp external to the current running
  context during an update statement (for example, if your query takes
  a long time to run, and there are other updates occurring in your
  database while your update statement is running), you can use
  xdmp:eval
   
  to evaluate a separate query statement that
  returns the system timestamp at the time the 
  xdmp:eval
 
  query is evaluated.

### Examples

```xquery
xdmp:request-timestamp()
=> 1234567
```

---
