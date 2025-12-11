# General

103 functions in this category.

## fn:QName

Returns an xs:QName with the namespace URI given in $paramURI.
  If $paramURI is the zero-length string or the empty sequence, it
  represents "no namespace"; in this case, if the value of $paramQName
  contains a colon (:), an error is raised [err:FOCA0002].
  The prefix (or absence of a prefix) in $paramQName is retained in
  the returned xs:QName value. The local name in the result is taken
  from the local part of $paramQName.

### Signature

```xquery
fn:QName(
  $paramURI as xs:string?,
  $paramQName as xs:string
) as xs:QName
```

### Parameters

**`$paramURI`**
A namespace URI, as a string.

**`$paramQName`**
A lexical qualified name (xs:QName), a string of the form "prefix:localname"
or "localname".

### Returns

`xs:QName`

### Usage Notes

If $paramQName does not have the correct lexical form for
  xs:QName an error is raised [err:FOCA0002].

      
  Note that unlike xs:QName this function does not require an
  xs:string literal as the argument.

### Examples

```xquery
fn:QName("http://www.example.com/example", "person")

=> an xs:QName with namespace URI =
   "http://www.example.com/example",
   local name = "person", and
   prefix = "".

fn:QName("http://www.example.com/example", "ht:person")

=> an xs:QName with namespace URI =
   "http://www.example.com/example",
   local name = "person",
   and prefix = "ht".
```

---

## fn:abs

Returns the absolute value of $arg. If $arg is negative returns -$arg
otherwise returns $arg. If type of $arg is one of the four numeric types
xs:float, xs:double, xs:decimal or xs:integer the type of the result is
the same as the type of $arg. If the type of $arg is a type derived from
one of the numeric types, the result is an instance of the base numeric
type. 

      
For xs:float and xs:double arguments, if the argument is positive zero (+0)
or negative zero (-0), then positive zero (+0) is returned. If the argument
is positive or negative infinity, positive infinity is returned.

      
For detailed type semantics, see Section 7.2.1 The fn:abs, fn:ceiling,
fn:floor, fn:round, and fn:round-half-to-even functions of [XQuery 1.0 and
XPath 2.0 Formal Semantics].

### Signature

```xquery
fn:abs(
  $arg as numeric?
) as numeric?
```

### Parameters

**`$arg`**
A numeric value.

### Returns

`numeric?`

### Examples

```xquery
fn:abs(10.5) 
=> 10.5

fn:abs(-10.5)
=> 10.5
```

---

## fn:analyze-string

The result of the function is a new element node whose string value is the
original string, but which contains markup to show which parts of the
input match the regular expression.

### Signature

```xquery
fn:analyze-string(
  $in as xs:string?,
  $regex as xs:string,
  $flags as xs:string?
) as element(s:results)
```

### Parameters

**`$in`**
The string to start with.

**`$regex`**
The regular expression pattern to match.

**`$flags`** *(optional)*
The flag representing how to interpret the regular expression. One of
  "s", "m", "i", or "x", as defined in
  http://www.w3.org/TR/xpath-functions/#flags.

### Returns

`element(s:results)`

### Examples

#### Example 1

```xquery
fn:analyze-string('Tom Jim John',"Jim")

=>
<s:analyze-string-result>
  <s:non-match>Tom </s:non-match>
  <s:match>Jim</s:match>
  <s:non-match> John</s:non-match>
</s:analyze-string-result>
```

#### Example 2

```xquery
fn:analyze-string('Tom Jim John',"(Jim)")

=>
<s:analyze-string-result>
  <s:non-match>Tom </s:non-match>
    <s:match>
      <s:group nr="1">Jim</s:group>
    </s:match>
  <s:non-match> John</s:non-match>
</s:analyze-string-result>
```

#### Example 3

```xquery
fn:analyze-string('Tom Jim John',"((Jim) John)")

=>
<s:analyze-string-result>
  <s:non-match>Tom </s:non-match>
  <s:match>
    <s:group nr="1">
    <s:group nr="2">Jim</s:group>
    John
    </s:group>
  </s:match>
</s:analyze-string-result>
```

#### Example 4

```xquery
fn:analyze-string("http://example.com/", "\w+")

=>
<result xmlns="http://www.w3.org/2005/xpath-functions">
  <match>http</match>
  <non-match>://</non-match>
  <match>example</match>
  <non-match>.</non-match>
  <match>com</match>
  <non-match>/</non-match>
</result>
```

---

## fn:avg

Returns the average of the values in the input sequence $arg, that is, the sum
of the values divided by the number of values.

      
If $arg is the empty sequence, the empty sequence is returned.

      
If $arg contains values of type xs:untypedAtomic they are cast to xs:double.

      
Duration values must either all be xs:yearMonthDuration values or must all be
xs:dayTimeDuration values. For numeric values, the numeric promotion rules
defined in 6.2 Operators on Numeric Values are used to promote all values to
a single common type. After these operations, $arg must contain items of a
single type, which must be one of the four numeric
types,xs:yearMonthDuration or xs:dayTimeDuration or one if its subtypes.

      
If the above conditions are not met, then a type error is raised [err:FORG0006].

      
Otherwise, returns the average of the values computed as sum($arg) div
count($arg).

      
For detailed type semantics, see
Section
7.2.10 The fn:min, fn:max, fn:avg, and fn:sum functions[FS].

### Signature

```xquery
fn:avg(
  $arg as xs:anyAtomicType*
) as xs:anyAtomicType?
```

### Parameters

**`$arg`**
The sequence of values to average.

### Returns

`xs:anyAtomicType?`

### Examples

```xquery
Assume:
$d1 = xs:yearMonthDuration("P20Y")
$d2 = xs:yearMonthDuration("P10M")
$seq3 = (3, 4, 5)

Then:

fn:avg($seq3) returns 4.0.

fn:avg(($d1, $d2))
returns a yearMonthDuration with value 125 months.

fn:avg(($d1, $seq3)) raises a type error [err:FORG0006].

fn:avg(()) returns ().

fn:avg((xs:float('INF')), xs:float('-INF')) returns NaN.

fn:avg(($seq3, xs:float('NaN')) returns NaN.
```

---

## fn:base-uri

Returns the value of the base-uri property for the specified node.  If the
  node is part of a document and does not have a base-uri attribute explicitly
  set, fn:base-uri typically  returns the URI of the document
  in which the node resides.

### Signature

```xquery
fn:base-uri(
  $arg as node()??
) as xs:anyURI?
```

### Parameters

**`$arg`** *(optional)*
The node whose base-uri is to be returned.

### Returns

`xs:anyURI?`

### Examples

```xquery
for $x in xdmp:directory("/myDirectory/", "1")
return
base-uri($x)

=> a list of URIs for all of the documents in the
   directory "/myDirectory/"
```

---

## fn:boolean

Computes the effective boolean value of the sequence $arg. See Section 2.4.3
Effective Boolean Value[XP].

### Signature

```xquery
fn:boolean(
  $arg as item()*,
  $collation as xs:string?
) as xs:boolean
```

### Parameters

**`$arg`**
A sequence of items.

**`$collation`** *(optional)*
The optional name of a valid collation URI.  For information on the
  collation URI syntax, see the Search Developer's Guide.

### Returns

`xs:boolean`

### Usage Notes

When using XQuery version "1.0-ml", this function implements the semantics
  from May 2003.
      
If $arg is the empty sequence, fn:boolean returns false.

      
If $arg is a sequence whose first item is a node, fn:boolean returns true.

      
If $arg is a singleton value of type xs:boolean or a derived from xs:boolean,
fn:boolean returns $arg.

      
If $arg is a singleton value of type xs:string or a type derived from xs:string
or xs:untypedAtomic, fn:boolean returns false if the operand value has zero
length; otherwise it returns true.

      
If $arg is a singleton value of any numeric type or a type derived from a
numeric type, fn:boolean returns false if the operand value is NaN or is
numerically equal to zero; otherwise it returns true.

      
In all other cases, fn:boolean raises a type error [err:FORG0006] when 
run in XQuery strict mode (1.0).

      
The static semantics of this function are described in
Section
7.2.4 The fn:boolean function[FS].

      
Note:

      
The result of this function is not necessarily the same as " $arg cast as
xs:boolean ". For example, fn:boolean("false") returns the value "true" whereas
"false" cast as xs:boolean returns false.

### Examples

```xquery
xquery version "1.0";
let $x := ("a", "b", "c")
return
fn:boolean($x)
=> raises a type error [err:FORG0006].

xquery version "1.0-ml";
let $x := ("a", "b", "c")
return
fn:boolean($x)
=> true

let $x := ("a", "b", "c")
return
fn:boolean($x[1])
=> returns true.

let $x := ("a", "b", "c")
return
fn:boolean($x[0])
=> returns false.
```

---

## fn:ceiling

Returns the smallest (closest to negative infinity) number with no fractional
part that is not less than the value of $arg. If type of $arg is one of the
four numeric types xs:float, xs:double, xs:decimal or xs:integer the type of
the result is the same as the type of $arg. If the type of $arg is a type
derived from one of the numeric types, the result is an instance of the base
numeric type.

      
For xs:float and xs:double arguments, if the argument is positive zero, then
positive zero is returned. If the argument is negative zero, then negative zero
is returned. If the argument is less than zero and greater than -1, negative
zero is returned.

      
For detailed type semantics, see Section 7.2.3 The fn:abs, fn:ceiling,
fn:floor, fn:round, and fn:round-half-to-even functions[FS].

### Signature

```xquery
fn:ceiling(
  $arg as numeric?
) as numeric?
```

### Parameters

**`$arg`**
A numeric value.

### Returns

`numeric?`

### Examples

```xquery
fn:ceiling(10.5) 
=> 11

fn:ceiling(-10.5) 
=> -10
```

---

## fn:codepoint-equal

Returns true if the specified parameters are the same Unicode
code point, otherwise returns false. The codepoints are
compared according to the Unicode code point collation
(http://www.w3.org/2005/xpath-functions/collation/codepoint).

      
If either argument is the empty sequence, the result is the empty sequence.

### Signature

```xquery
fn:codepoint-equal(
  $comparand1 as xs:string?,
  $comparand2 as xs:string?
) as xs:boolean?
```

### Parameters

**`$comparand1`**
A string to be compared.

**`$comparand2`**
A string to be compared.

### Returns

`xs:boolean?`

### Examples

```xquery
let $cp := fn:string-to-codepoints("123456")
return
fn:codepoint-equal("123456", fn:codepoints-to-string($cp) )

=> true
```

---

## fn:codepoints-to-string

Creates an xs:string from a sequence of Unicode code points.
Returns the zero-length string if $arg is the empty sequence.
If any of the code points in $arg is not a legal XML character,
an error is raised.

### Signature

```xquery
fn:codepoints-to-string(
  $arg as xs:integer*
) as xs:string
```

### Parameters

**`$arg`**
A sequence of Unicode code points.

### Returns

`xs:string`

### Examples

```xquery
fn:codepoints-to-string(
  (104, 101, 108, 108, 111, 32, 119, 111, 114, 108, 100))
=> hello world
```

---

## fn:collection

Returns all of the documents that belong to the specified collection(s).

### Signature

```xquery
fn:collection(
  $uri as xs:string*?
) as document-node()*
```

### Parameters

**`$uri`** *(optional)*
The URI of the collection to retrieve.   If you omit this parameter,
  returns all of the documents in the database. If you specify a list of
  URIs, returns all of the documents in all of the collections at the URIs
  specified in the list.

### Returns

`document-node()*`

### Examples

```xquery
fn:collection("mycollection")[1]
=> returns the first document in the "mycollection" collection
```

---

## fn:compare

Returns -1, 0, or 1, depending on whether the value of the $comparand1 
  is respectively less than, equal to, or greater than the value of 
  $comparand2, according to the rules of the collation that is used.

### Signature

```xquery
fn:compare(
  $comparand1 as xs:string?,
  $comparand2 as xs:string?,
  $collation as xs:string?
) as xs:integer?
```

### Parameters

**`$comparand1`**
A string to be compared.

**`$comparand2`**
A string to be compared.

**`$collation`** *(optional)*
The optional name of a valid collation URI.  For information on the
  collation URI syntax, see the Search Developer's Guide.

### Returns

`xs:integer?`

### Examples

```xquery
fn:compare("hello", "goodbye")

=> 1
```

---

## fn:concat

Returns the xs:string that is the concatenation of the values
of the specified parameters. Accepts two or more xs:anyAtomicType
arguments and casts them to xs:string. If any of the parameters
is the empty sequence, the parameter is treated as the zero-length string.

### Signature

```xquery
fn:concat(
  $parameter1 as xs:anyAtomicType?,
  $parameterN as xs:anyAtomicType?,...?
) as xs:string
```

### Parameters

**`$parameter1`**
A value.

**`$parameterN`** *(optional)*
A value.

### Returns

`xs:string`

### Examples

```xquery
fn:concat("a", "b", "c")

=> abc
```

---

## fn:contains

Returns true if the first parameter contains the string
  from the second parameter, otherwise returns false.

### Signature

```xquery
fn:contains(
  $parameter1 as xs:string?,
  $parameter2 as xs:string?,
  $collation as xs:string?
) as xs:boolean
```

### Parameters

**`$parameter1`**
The string from which to test.

**`$parameter2`**
The string to test for existence in the first parameter.

**`$collation`** *(optional)*
The optional name of a valid collation URI.  For information on the
  collation URI syntax, see the Search Developer's Guide.

### Returns

`xs:boolean`

### Examples

```xquery
fn:contains("this is a string", "s a s")

=> true
```

---

## fn:count

Returns the number of items in the value of $arg.

      
Returns 0 if $arg is the empty sequence.

### Signature

```xquery
fn:count(
  $arg as item()*,
  $maximum as xs:double??
) as xs:integer
```

### Parameters

**`$arg`**
The sequence of items to count.

**`$maximum`** *(optional)*
The maximum value of the count to return. MarkLogic Server will stop
  count when the $maximum value is reached and return
  the $maximum value.  This is an extension to the W3C
  standard fn:count function.

### Returns

`xs:integer`

### Examples

```xquery
Assume:
$seq1 = ($item1, $item2)
$seq3 = (), the empty sequence

Then:

fn:count($seq1) returns 2.

fn:count($seq3) returns 0.

Assume $seq2 = (98.5, 98.3, 98.9).

Then:

fn:count($seq2) returns 3.
fn:count($seq2[. > 100]) returns 0.
```

---

## fn:current-date

Returns xs:date(fn:current-dateTime()). This is an
  xs:date (with timezone) that is current at some time
  during the evaluation of a query or transformation in which
  fn:current-date() is executed. This function is *stable*.
  The precise instant during the query or transformation represented
  by the value of fn:current-date() is
  *implementation dependent*.

### Returns

`xs:date`

### Usage Notes

fn:current-date() returns an xs:date
  corresponding to the current date and time.  For example, an
  invocation of fn:current-date() might return
  2004-05-12+01:00.

### Examples

```xquery
fn:current-date()

=> 2006-05-25-07:00
```

---

## fn:current-dateTime

Returns the current dateTime value (with timezone) from the dynamic context.
  (See
Section C.2 Dynamic
Context Components[XP].) This is an
  xs:dateTime that is current at some time during the
  evaluation of a query or transformation in which
  fn:current-dateTime() is executed. This function is
  *stable*. The precise instant during the query or transformation
  represented by the value of fn:current-dateTime() is
  *implementation dependent*.

### Returns

`xs:dateTime`

### Usage Notes

fn:current-dateTime() returns an xs:dateTime
  corresponding to the current date and time. For example, an invocation
  of fn:current-dateTime() might return
  2004-05-12T18:17:15.125Z corresponding to the current
  time on May 12, 2004 in timezone Z.

### Examples

```xquery
fn:current-dateTime()

=> 2014-05-25T18:21:24.454-07:00
```

---

## fn:current-time

Returns xs:time(fn:current-dateTime()). This is an
  xs:time (with timezone) that is current at some time
  during the evaluation of a query or transformation in which
  fn:current-time() is executed. This function is
  *stable*. The precise instant during the query or transformation
  represented by the value of fn:current-time() is
  *implementation dependent*.

### Returns

`xs:time`

### Usage Notes

fn:current-time() returns an xs:time
  corresponding to the current date and time.  For example, an
  invocation of fn:current-time() might return
  23:17:00.000-05:00.

### Examples

```xquery
fn:current-time()

=> 18:24:06-07:00
```

---

## fn:data

Takes a sequence of items and returns a sequence of atomic values. 
      The fn:data function returns the sequence of atomic values
 produced by applying the following rules to each item in $arg: 
      
	If the item is an atomic value, it is returned.
	If the item is a node:
  
	    If the node does not have a typed value an error is
  raised [err:FOTY0012].
	    Otherwise, fn:data returns the typed value of the node as
  defined by the accessor function dm:typed-value in Section 5.15
  typed-value Accessor[DM].

### Signature

```xquery
fn:data(
  $arg as item()*
) as xs:anyAtomicType*
```

### Parameters

**`$arg`**
The items whose typed values are to be returned.

### Returns

`xs:anyAtomicType*`

### Examples

```xquery
let $x := <hello>hello
            <goodbye>goodbye</goodbye>
          </hello>
return
fn:data($x)

=> hello goodbye
```

---

## fn:deep-equal

This function assesses whether two sequences are deep-equal to each other. To
be deep-equal, they must contain items that are pairwise deep-equal; and for
two items to be deep-equal, they must either be atomic values that compare
equal, or nodes of the same kind, with the same name, whose children are
deep-equal. This is defined in more detail below. The $collation argument
identifies a collation which is used at all levels of recursion when strings
are compared (but not when names are compared), according to the rules in 7.3.1
Collations.

      If the two sequences are both empty, the function returns true.

      
If the two sequences are of different lengths, the function returns false.

      
If the two sequences are of the same length, the function returns true if and
only if every item in the sequence $parameter1 is deep-equal to the item at the
same position in the sequence $parameter2. The rules for deciding whether two
items are deep-equal follow.

      
Call the two items $i1 and $i2 respectively.

      
If $i1 and $i2 are both atomic values, they are deep-equal if and only if ($i1
eq $i2) is true. Or if both values are NaN. If the eq operator is not defined
for $i1 and $i2, the function returns false.

      
If one of the pair $i1 or $i2 is an atomic value and the other is a node, the
function returns false.

      
If $i1 and $i2 are both nodes, they are compared as described below:

      
If the two nodes are of different kinds, the result is false.

      
If the two nodes are both document nodes then they are deep-equal if and only
if the sequence $i1/(*|text()) is deep-equal to the sequence $i2/(*|text()).

      
If the two nodes are both element nodes then they are deep-equal if and only if
all of the following conditions are satisfied:

      
	the two nodes have the same name, that is (node-name($i1) eq
  node-name($i2)).
	the two nodes are both annotated as having simple content or both nodes
  are annotated as having complex content.
	the two nodes have the same number of attributes, and for every attribute
  $a1 in $i1/@* there exists an attribute $a2 in $i2/@* such that $a1 and $a2
  are deep-equal. 
	One of the following conditions holds:
    
	    Both element nodes have a type annotation that is simple content, and
    the typed value of $i1 is deep-equal to the typed value of $i2. 
	    Both element nodes have a type annotation that is complex content with
    elementOnly content, and each child element of $i1 is deep-equal to the
    corresponding child element of $i2. 
	    Both element nodes have a type annotation that is complex content with
    mixed content, and the sequence $i1/(*|text()) is deep-equal to the
    sequence $i2/(*|text()). 
	    Both element nodes have a type annotation that is complex content with
    empty content. 
	  
  
      
      
If the two nodes are both attribute nodes then they are deep-equal if and only
if both the following conditions are satisfied:

      
	the two nodes have the same name, that is (node-name($i1) eq
  node-name($i2)).
	the typed value of $i1 is deep-equal to the typed value of $i2.
      
      
If the two nodes are both processing instruction nodes or namespace bindings,
then they are deep-equal if and only if both the following conditions are
satisfied:

      
	the two nodes have the same name, that is (node-name($i1) eq
  node-name($i2)). 
	the string value of $i1 is equal to the string value of $i2.
      
      
If the two nodes are both text nodes and their parent nodes are not object
nodes, then they are deep-equal if and only if their string-values are both
equal.

      
If the two nodes are both text nodes and their parent nodes are both object
nodes, then they are deep-equal if and only if their keys and string-values
are both equal.

      
If the two nodes are both comment nodes, then they are deep-equal
if and only if their string-values are equal.

      
If the two nodes are both object nodes, then they are deep-equal if and only if
all of the following conditions are satisfied:

      
	the two nodes have the same number of children, and the children have the
    same set of keys.
	two children of the two nodes with the same key are deep-equal.
	the order of children does not matter. 
      
      
If the two nodes are both boolean nodes, then they are deep-equal
if and only if their keys and boolean values are equal.

      
If the two nodes are both number nodes, then they are deep-equal
if and only if their keys and values are equal.

      
If the two nodes are both null nodes, they are deep-equal.

      
Notes:

      
The two nodes are not required to have the same type annotation, and they are
not required to have the same in-scope namespaces. They may also differ in
their parent, their base URI, and the values returned by the is-id and
is-idrefs accessors (see Section 5.5 is-id Accessor[DM] and Section 5.6 is-idrefs
Accessor[DM]). The order of children is significant, but the order of attributes
is insignificant.

      
The following note applies to the Jan 2007 XQuery specification, but not to the
May 2003 XQuery specification: 
The contents of comments and processing instructions are significant only if
these nodes appear directly as items in the two sequences being compared. The
content of a comment or processing instruction that appears as a descendant of
an item in one of the sequences being compared does not affect the
result. However, the presence of a comment or processing instruction, if it
causes a text node to be split into two text nodes, may affect the result.

      
The result of fn:deep-equal(1, current-dateTime()) is false; it does not raise
an error.

### Signature

```xquery
fn:deep-equal(
  $parameter1 as item()*,
  $parameter2 as item()*,
  $collation as xs:string?
) as xs:boolean
```

### Parameters

**`$parameter1`**
The first sequence of items, each item should be an atomic value or node.

**`$parameter2`**
The sequence of items to compare to the first sequence of items, again each
  item should be an atomic value or node.

**`$collation`** *(optional)*
The optional name of a valid collation URI.  For information on the
  collation URI syntax, see the Search Developer's Guide.

### Returns

`xs:boolean`

### Examples

```xquery
Assume $at := <attendees>
             <name last='Parker' first='Peter'/>
             <name last='Barker' first='Bob'/>
             <name last='Parker' first='Peter'/>
           </attendees>

Then:

fn:deep-equal($at, $at/&#42;) returns false.

fn:deep-equal($at/name[1], $at/name[2]) returns false.

fn:deep-equal($at/name[1], $at/name[3]) returns true.

fn:deep-equal($at/name[1], 'Peter Parker') returns false.
```

---

## fn:default-collation

Returns the value of the default collation property from the static context.
Components of the static context are discussed in 
Section C.1 Static Context Components[XP].

      The default collation property can never be undefined. If it is not
explicitly defined, a system defined default codepoint is used.
In the 1.0 XQuery dialect, if this is not provided, the Unicode
code point collation
(http://www.w3.org/2005/xpath-functions/collation/codepoint) is used.  In the 1.0-ml and 0.9-ml XQuery dialects,
the MarkLogic-defined codepoint URI is used
(http://marklogic.com/collation/codepoint).

### Returns

`xs:string`

### Usage Notes

For details about collations in MarkLogic Server, see the "Encodings and
  Collations" chapter of the Developer's Guide.

### Examples

#### Example 1

```xquery
xquery version "1.0-ml";
declare default collation "http://marklogic.com/collation/codepoint";
fn:default-collation()

=> http://marklogic.com/collation/codepoint
```

#### Example 2

```xquery
xquery version "1.0";
declare default collation "http://marklogic.com/collation/codepoint";
fn:default-collation()

=> http://www.w3.org/2005/xpath-functions/collation/codepoint
```

---

## fn:distinct-nodes

[0.9-ml only] Returns the sequence resulting from removing from the input
  sequence all but one of a set of nodes that have the same identity as one
  another. If the empty sequence is input, fn:distinct-nodes
  returns the empty sequence.

### Signature

```xquery
fn:distinct-nodes(
  $nodes as node()*
) as node()*
```

### Parameters

**`$nodes`**
A sequence of nodes from which to eliminate duplicate nodes (nodes with
  the same identity) so that only one node of each identity remains.

### Returns

`node()*`

### Usage Notes

Note that for a node to have the same identity as another node, it must
  be exactly the same node (not an equivalent node).  For example, for a node
  bound to the variable $x to have the same identity
  as a node bound to the variable $y, the following must return true: 
      $x is $y

### Examples

#### Example 1

```xquery
(:
    assume /mydoc.xml has the following contents:
    <a>hello</a>
  :)

  let $x := fn:doc("/mydoc.xml")/a
  let $y := /a
  return
  fn:distinct-nodes(($x, $y))

=> <a>hello</a>
```

#### Example 2

```xquery
(:
    assume /mydoc.xml has the following contents:
    <a>hello</a>
  :)

  let $x := fn:doc("/mydoc.xml")/a
  let $y := <a>hello</a>
  return
  fn:distinct-nodes(($x, $y))

=> (<a>hello</a>, <a>hello</a>)
   It returns both nodes because they do not
   have the same identity.
```

---

## fn:distinct-values

Returns the sequence that results from removing from $arg all but one of a set
of values that are eq to one other. Values that cannot be compared, i.e. the
eq operator is not defined for their types, are considered to be
distinct. Values of type xs:untypedAtomic are compared as if they were of
type xs:string. The order in which the sequence of values is returned is
implementation dependent. 

      
The static type of the result is a sequence of prime types as defined in
Section 7.2.7 The fn:distinct-values function[FS].

      
The collation used by the invocation of this function is determined according
to the rules in 7.3.1 Collations. The collation is used when string
comparison is required.

      
If $arg is the empty sequence, the empty sequence is returned.

      
For xs:float and xs:double values, positive zero is equal to negative zero and,
although NaN does not equal itself, if $arg contains multiple NaN values a
single NaN is returned.

      
If xs:dateTime, xs:date or xs:time values do not have a timezone, they are
considered to have the implicit timezone provided by the dynamic context for
the purpose of comparison. Note that xs:dateTime, xs:date or xs:time values
can compare equal even if their timezones are different.

      
Which value of a set of values that compare equal is returned is
implementation dependent.

### Signature

```xquery
fn:distinct-values(
  $arg as item()*,
  $collation as xs:string?
) as xs:anyAtomicType*
```

### Parameters

**`$arg`**
A sequence of items.

**`$collation`** *(optional)*
The optional name of a valid collation URI.  For information on the
  collation URI syntax, see the Search Developer's Guide.

### Returns

`xs:anyAtomicType*`

### Examples

```xquery
fn:distinct-values((1, 2.0, 3, 2)) might return (1, 3, 2.0).

The following query:

let $x as xs:untypedAtomic*
    := (xs:untypedAtomic("cherry"),
        xs:untypedAtomic("bar"),
        xs:untypedAtomic("bar"))
return fn:distinct-values ($x)
                                   
returns a sequence containing two items ("cherry", "bar")
of type xs:untypedAtomic.
```

---

## fn:doc

Returns the document(s) stored in the database at the specified 
  URI(s).

### Signature

```xquery
fn:doc(
  $uri as xs:string*?
) as document-node()*
```

### Parameters

**`$uri`** *(optional)*
The URI of the document to retrieve.  If you omit this parameter,
  returns all of the documents in the database - this is only allowed if
  you're not using xquery version 1.0 strict. If you specify a list of
  URIs, returns all of the documents at the URIs specified in the list.

### Returns

`document-node()*`

### Usage Notes

The document-node() returned for each item in the result
  contains an element() root node for XML documents, a
  text() root node for text documents, an 
  object-node(), array-node(), or another JSON node
  for a JSON document, and a binary() root node for binary 
  documents.

### Examples

```xquery
fn:doc("/mydocs/doc.xml")

=> returns the document at the URI /mydocs/doc.xml
```

---

## fn:doc-available

If fn:doc($uri) returns a document node, this function returns true.
If $uri is not a valid xs:anyURI, an error is raised [err:FODC0005].
Otherwise, this function returns false.

      If this function returns true, then calling fn:doc($uri) within the
same execution scope must return a document node.

### Signature

```xquery
fn:doc-available(
  $uri as xs:string?
) as xs:boolean
```

### Parameters

**`$uri`**
The URI of the document to check.

### Returns

`xs:boolean`

### Examples

```xquery
fn:doc-available("/mydocs/doc.xml")

=> true is /mydocs/doc.xml is a document in the database
   otherwise false
```

---

## fn:document-uri

Returns the value of the document-uri property for the specified node.
 If the node is a document node, then the value returned is the URI of the
 document. If the node is not a document node, then
 fn:document-uri returns the empty sequence.

### Signature

```xquery
fn:document-uri(
  $arg as node()?
) as xs:anyURI?
```

### Parameters

**`$arg`**
The node whose document-uri is to be returned.

### Returns

`xs:anyURI?`

### Usage Notes

fn:document-uri will only return the URI of a document
  when a document node is passed into it.  If you want to return the URI
  of a node that is not a document node, but has a document node ancestor,
  use fn:base-uri or 
  xdmp:node-uri.

### Examples

```xquery
for $x in xdmp:directory("/myDirectory/", "1")
return
fn:document-uri($x)

=> a list of URIs for all of the documents in the
   directory "/myDirectory/"
```

---

## fn:empty

If the value of $arg is the empty sequence, the function returns true;
otherwise, the function returns false.

### Signature

```xquery
fn:empty(
  $arg as item()*
) as xs:boolean
```

### Parameters

**`$arg`**
A sequence to test.

### Returns

`xs:boolean`

### Examples

```xquery
fn:empty(fn:remove(("hello", "world"), 1))

=> false
```

---

## fn:encode-for-uri

Invertible function that escapes characters required to be escaped
   inside path segments of URIs.

### Signature

```xquery
fn:encode-for-uri(
  $uri-part as xs:string
) as xs:string
```

### Parameters

**`$uri-part`**
A string representing an unescaped URI.

### Returns

`xs:string`

### Examples

```xquery
fn:encode-for-uri("http://example.com/Weather/Los%20Angeles#ocean")
=> "http%3A%2F%2Fexample.com%2FWeather%2FLos%2520Angeles%23ocean"
```

---

## fn:ends-with

Returns true if the first parameter ends with the string
 from the second parameter, otherwise returns false.

### Signature

```xquery
fn:ends-with(
  $parameter1 as xs:string?,
  $parameter2 as xs:string?,
  $collation as xs:string?
) as xs:boolean
```

### Parameters

**`$parameter1`**
The parameter from which to test.

**`$parameter2`**
The string to test whether it is at the end of the first parameter.

**`$collation`** *(optional)*
The optional name of a valid collation URI.  For information on the
  collation URI syntax, see the Search Developer's Guide.

### Returns

`xs:boolean`

### Examples

```xquery
fn:ends-with("this is a string", "a string")

=> true
```

---

## fn:escape-html-uri

%-escapes everything except printable ASCII characters.

### Signature

```xquery
fn:escape-html-uri(
  $uri-part as xs:string
) as xs:string
```

### Parameters

**`$uri-part`**
A string representing an unescaped URI.

### Returns

`xs:string`

### Examples

```xquery
fn:escape-html-uri("http://example.com/Weather/Los Angeles#ocean")
=> "http://example.com/Weather/Los Angeles#ocean"
```

---

## fn:escape-uri

This is a May 2003 function, and is only available in compatibility mode
 (XQuery 0.9-ML)--it has been replaced with fn:encode-for-uri,
 fn:iri-to-uri, and fn:escape-html-uri.
 Returns a string representing the specified URI either with escaped reserved
 characters ($escape-reserved=true) or with the reserved characters left as
 specified ($escape-reserved=true).  For more details, see the W3C XQuery Functions and Operators specification.

### Signature

```xquery
fn:escape-uri(
  $uri-part as xs:string,
  $escape-reserved as xs:boolean
) as xs:string
```

### Parameters

**`$uri-part`**
A string representing an unescaped URI.

**`$escape-reserved`**
Specify a boolean value of true to return an escaped URI or
  a boolean value of false to return an unescaped URI.

### Returns

`xs:string`

### Examples

```xquery
fn:escape-uri("http://developer.marklogic.com", fn:true())

=> http%3A%2F%2Fdeveloper.marklogic.com

fn:escape-uri("http://developer.marklogic.com", fn:false())

=> http://developer.marklogic.com
```

---

## fn:exactly-one

Returns $arg if it contains exactly one item. Otherwise, raises an error
   [err:FORG0005].

      
For detailed type semantics, see
Section 7.2.16 The fn:zero-or-one,
fn:one-or-more, and fn:exactly-one functions[FS].

### Signature

```xquery
fn:exactly-one(
  $arg as item()*
) as item()
```

### Parameters

**`$arg`**
The sequence of items.

### Returns

`item()`

### Examples

```xquery
fn:exactly-one(("hello"))

=> "hello"

fn:exactly-one(("hello", "goodbye"))

=> XDMP-NOTONEITEM exception (because there are 2 items)
```

---

## fn:exists

If the value of $arg is not the empty sequence, the function returns true;
otherwise, the function returns false.

### Signature

```xquery
fn:exists(
  $arg as item()*
) as xs:boolean
```

### Parameters

**`$arg`**
A sequence to test.

### Returns

`xs:boolean`

### Examples

```xquery
fn:exists(fn:remove(("hello"), 1))

=> false
```

---

## fn:expanded-QName

[0.9-ml only, use fn:QName instead]
  Returns an
  xs:QName with the namespace URI given in $paramURI and
  the local name in $paramLocal.
  If $paramURI is the zero-length string or the empty sequence, it
  represents "no namespace".

### Signature

```xquery
fn:expanded-QName(
  $paramURI as xs:string?,
  $paramLocal as xs:string
) as xs:QName
```

### Parameters

**`$paramURI`**
A namespace URI, as a string.

**`$paramLocal`**
A localname, as a string.

### Returns

`xs:QName`

---

## fn:false

Returns the xs:boolean value false.
  Equivalent to xs:boolean("0").

### Returns

`xs:boolean`

### Examples

```xquery
fn:false()

=> false
```

---

## fn:filter

Returns those items from the sequence $seq for which the supplied
  function $function returns true.
  For more details, see
  XPath 3.0 Functions and Operators.

### Signature

```xquery
fn:filter(
  $function as function(item()) as xs:boolean,
  $seq as item()*
) as item()*
```

### Parameters

**`$function`**
The function value.

**`$seq`**
The function value.

### Returns

`item()*`

### Examples

```xquery
fn:filter(function($a) { $a mod 2 = 0 }, (1 to 10))
=> (2, 4, 6, 8, 10)
```

---

## fn:floor

Returns the largest (closest to positive infinity) number with no fractional
part that is not greater than the value of $arg. If type of $arg is one of the
four numeric types xs:float, xs:double, xs:decimal or xs:integer the type of
the result is the same as the type of $arg. If the type of $arg is a type
derived from one of the numeric types, the result is an instance of the base
numeric type.

      
For float and double arguments, if the argument is positive zero, then positive
zero is returned. If the argument is negative zero, then negative zero is
returned.

      
For detailed type semantics, see Section 7.2.3 The fn:abs, fn:ceiling,
fn:floor, fn:round, and fn:round-half-to-even functions[FS].

### Signature

```xquery
fn:floor(
  $arg as numeric?
) as numeric?
```

### Parameters

**`$arg`**
A numeric value.

### Returns

`numeric?`

### Examples

```xquery
fn:floor(10.5) 
=> 10

fn:floor(-10.5) 
=> -11
```

---

## fn:fold-left

Processes the supplied sequence from left to right, applying the
  supplied function repeatedly to each item in turn, together with an
  accumulated result value.
  For more details, see
  XPath 3.0 Functions and Operators.

### Signature

```xquery
fn:fold-left(
  $function as function(item()*, item()) as item()*,
  $zero as item()*,
  $seq as item()*
) as item()*
```

### Parameters

**`$function`**
The fold function value.

**`$zero`**
The zero argument.

**`$seq`**
The sequence to fold

### Returns

`item()*`

### Examples

```xquery
fn:fold-left(function($z, $a) { $z || "," || $a }, ">>", ("a","b","c"))
=> ">>,a,b,c"
```

---

## fn:fold-right

Processes the supplied sequence from right to left, applying the
  supplied function repeatedly to each item in turn, together with an
  accumulated result value.
  For more details, see
  XPath 3.0 Functions and Operators.

### Signature

```xquery
fn:fold-right(
  $function as function(item(), item()*) as item()*,
  $zero as item()*,
  $seq as item()*
) as item()*
```

### Parameters

**`$function`**
The fold function value.

**`$zero`**
The zero argument.

**`$seq`**
The sequence to fold

### Returns

`item()*`

### Examples

```xquery
fn:fold-right(function($z, $a) { $z || "," || $a }, ">>", ("a","b","c"))
=> "a,b,c,>>"
```

---

## fn:function-arity

Returns the arity of the function(s) that the argument refers to.
  For more details, see
  XPath 3.0 Functions and Operators.

### Signature

```xquery
fn:function-arity(
  $function as function(*)
) as xs:integer
```

### Parameters

**`$function`**
The function value.

### Returns

`xs:integer`

### Examples

```xquery
let $fn := fn:empty#1
return
  fn:function-arity($fn)
=> 1
```

---

## fn:function-lookup

Returns a function with the given name and arity, or the empty sequence if
  none exists. You can use the returned function reference with 
  xdmp:apply.
  For more details, see
  XPath 3.0 Functions and Operators.

### Signature

```xquery
fn:function-lookup(
  $name as xs:QName,
  $arity as xs:integer
) as function(*)?
```

### Parameters

**`$name`**
The QName of the function.

**`$arity`**
The number of arguments the function takes.

### Returns

`function(*)?`

### Examples

#### Example 1

```xquery
let $fn := fn:function-lookup(fn:QName("http://www.w3.org/2005/xpath-functions","concat"),4)
return
  xdmp:function-signature($fn)
=> "function(xs:anyAtomicType?, xs:anyAtomicType?, xs:anyAtomicType?, xs:anyAtomicType?) as xs:string"
```

#### Example 2

```xquery
let $fn := fn:function-lookup(
  fn:QName("http://www.w3.org/2005/xpath-functions","concat"),4)
return
xdmp:apply($fn, "here", "is", "an", "example")

==> "hereisanexample"
```

---

## fn:function-name

Returns the QName of the function(s) that the argument refers to.
  For more details, see
  XPath 3.0 Functions and Operators.

### Signature

```xquery
fn:function-name(
  $function as function(*)
) as xs:QName?
```

### Parameters

**`$function`**
The function value.

### Returns

`xs:QName?`

---

## fn:generate-id

Returns a string that uniquely identifies a given node.  
       If $node is the empty sequence, the zero-length string is returned.  
      
If the function is called without an argument, the context item is used as
the default argument. The behavior of the function when the argument is
omitted is the same as if the context item is passed as an argument.
      If the context item is undefined an error is raised:
[err:XPDY0002]. If the context item is not a node an error is raised:
[err:XPTY0004].

### Signature

```xquery
fn:generate-id(
  $node as node()??
) as xs:string
```

### Parameters

**`$node`** *(optional)*
The node whose ID will be generated.

### Returns

`xs:string`

### Examples

```xquery
let $x := doc("auction.xml")
return
fn:generate-id($x)

=> n965c71980e85a011
```

---

## fn:head

Returns the first item in a sequence.
  For more details, see
  XPath 3.0 Functions and Operators.

### Signature

```xquery
fn:head(
  $seq as item()*
) as item()?
```

### Parameters

**`$seq`**
A sequence of items.

### Returns

`item()?`

### Examples

```xquery
fn:head((1,2,3))
=> 1
```

---

## fn:id

Returns the sequence of element nodes that have an ID value matching the value
of one or more of the IDREF values supplied in $arg.

### Signature

```xquery
fn:id(
  $arg as xs:string*,
  $node as node()?
) as element()*
```

### Parameters

**`$arg`**
The IDs of the elements to return.

**`$node`** *(optional)*
The target node.

### Returns

`element()*`

### Usage Notes

The function returns a sequence, in document order with duplicates eliminated,
containing every element node E that satisfies all the following conditions:

      
	E is in the target document. The target document is the document containing
$node, or the document containing the context node if the second argument is
omitted. An error is raised [err:FODC0001] if $node, or the context item if
the second argument is omitted, is a node in a tree whose root is not a
document node or if the second argument is omitted and there is no context
item [err:FONC0001], or if the context item is not a node [err:FOTY0011].

	E has an ID value equal to one of the candidate IDREF values, where:

	    An element has an ID value equal to V if either or both of the following
conditions are true:

		The is-id property (See Section 5.5 is-id AccessorDM.) of the element node
is true, and the typed value of the element node is equal to V under the
rules of the eq operator using the Unicode code point collation
  (http://www.w3.org/2005/xpath-functions/collation/codepoint).

		The element has an attribute node whose is-id property (See Section 5.5
is-id AccessorDM.) is true and whose typed value is equal to V under the
rules of the eq operator using the Unicode code point collation
  (http://www.w3.org/2005/xpath-functions/collation/codepoint).

	      

	    Each xs:string in $arg is parsed as if it were of type IDREFS, that is,
each xs:string in $arg is treated as a space-separated sequence of tokens,
each acting as an IDREF. These tokens are then included in the list of
candidate IDREFs. If any of the tokens is not a lexically valid IDREF (that
is, if it is not lexically an xs:NCName), it is ignored. Formally, The
candidate IDREF values are the strings in the sequence given by the
expression:

for $s in $arg
return fn:tokenize(fn:normalize-space($s), ' ')
                 [. castable as xs:IDREF]


	  

	If several elements have the same ID value, then E is the one that is first
in document order.

      
      Notes:
      
If the data model is constructed from an Infoset, an attribute will have the
is-id property if the corresponding attribute in the Infoset had an attribute
type of ID: typically this means the attribute was declared as an ID in a DTD.

      
If the data model is constructed from a PSVI, an element or attribute will have
the is-id property if its schema-defined type is xs:ID or a type derived by
restriction from xs:ID.

      
No error is raised in respect of a candidate IDREF value that does not match
the ID of any element in the document. If no candidate IDREF value matches the
ID value of any element, the function returns the empty sequence.

      
It is not necessary that the supplied argument should have type xs:IDREF or
xs:IDREFS, or that it should be derived from a node with the is-idrefs
property.

      
An element may have more than one ID value. This can occur with synthetic data
models or with data models constructed from a PSVI where an the element and one
of its attributes are both typed as xs:ID.

      
If the source document is well-formed but not valid, it is possible for two or
more elements to have the same ID value. In this situation, the function will
select the first such element.

      
It is also possible in a well-formed but invalid document to have an element or
attribute that has the is-id property but whose value does not conform to the
lexical rules for the xs:ID type. Such a node will never be selected by this
function.

### Examples

#### Example 1

```xquery
let $x := document{
  <html xmlns="http://www.w3.org/1999/xhtml">
    <p id="myID">hello</p>
  </html> }
return
fn:id("myID", $x)

=> <p id="myID" xmlns="http://www.w3.org/1999/xhtml">hello</p>
```

#### Example 2

```xquery
xquery version "1.0-ml";
declare namespace xh="http://www.w3.org/1999/xhtml";

let $x := document {
  <html xmlns="http://www.w3.org/1999/xhtml">
    <p id="myID">hello</p>
    <p>hello</p>
  </html> }
return
$x/xh:html/xh:p[. is fn:id("myID")]

=> <p id="myID" xmlns="http://www.w3.org/1999/xhtml">hello</p>
```

---

## fn:idref

Returns the sequence of element or attribute nodes that have an IDREF value
matching the value of one or more of the ID values supplied in $arg.

### Signature

```xquery
fn:idref(
  $arg as xs:string*,
  $node as node()?
) as node()*
```

### Parameters

**`$arg`**
The IDREFs of the elements and attributes to return.

**`$node`** *(optional)*
The target node.

### Returns

`node()*`

### Usage Notes

The function returns a sequence, in document order with duplicates eliminated,
containing every element or attribute node $N that satisfies all the following
// conditions:

      
	$N is in the target document. The target document is the document containing
$node, or the document containing the context node if the second argument is
omitted. An error is raised [err:FODC0001] if $node, or the context item if
the second argument is omitted, is a node in a tree whose root is not a
document node or if the second argument is omitted and there is no context
item [err:FONC0001], or if the context item is not a node [err:FOTY0011].

	$N has an IDREF value equal to one of the candidate ID values, where:

	    A node $N has an IDREF value equal to V if either or both of the following
conditions are true:

		The is-idrefs property (See Section 5.6 is-idref AccessorDM.) of $N is true.

		
The sequence
fn:tokenize(fn:normalize-space($N), ' ')
contains a string that is equal to V under the rules of the eq operator using
the Unicode code point collation
  (http://www.w3.org/2005/xpath-functions/collation/codepoint).

	      

	    Each xs:string in $arg is parsed as if it were of type xs:ID.  These
xs:strings are then included in the list of candidate xs:IDs. If any of the
xs:strings in $arg is not a lexically valid xs:ID (that
is, if it is not lexically an xs:NCName), it is ignored. More formally, The
candidate ID values are the strings in the sequence

$arg[. castable as xs:ID]


	  

      
      Notes:
      
An element or attribute typically acquires the is-idrefs property by being
validated against the schema type xs:IDREF or xs:IDREFS, or (for attributes
only) by being described as of type IDREF or IDREFS in a DTD.

      
No error is raised in respect of a candidate ID value that does not match the
IDREF value of any element or attribute in the document. If no candidate ID
value matches the IDREF value of any element or attribute, the function returns
the empty sequence.

      
It is possible for two or more nodes to have an IDREF value that matches a
given candidate ID value. In this situation, the function will return all such
nodes. However, each matching node will be returned at most once, regardless
how many candidate ID values it matches.

      
It is possible in a well-formed but invalid document to have a node whose
is-idrefs property is true but that does not conform to the lexical rules for
the xs:IDREF type. The effect of the above rules is that ill-formed candidate
ID values and ill-formed IDREF values are ignored

### Examples

```xquery
(:
   assume /mydocs/idref.xml has an element named idrefs that is
   of type xs:IDREF or xs:IDREFS
:)
fn:idref("myID", doc("/mydocs/idref.xml"))

=> <idrefs>myID</idrefs>
```

---

## fn:implicit-timezone

Returns the value of the implicit timezone property from the dynamic context.
Components of the dynamic context are discussed in
Section C.2 Dynamic
Context Components[XP].

### Returns

`xs:dayTimeDuration`

### Examples

```xquery
fn:implicit-timezone()

=> -PT7H
```

---

## fn:in-scope-prefixes

Returns the prefixes of the in-scope namespaces for $element. For namespaces
that have a prefix, it returns the prefix as an xs:NCName. For the default
namespace, which has no prefix, it returns the zero-length string.

### Signature

```xquery
fn:in-scope-prefixes(
  $element as element()
) as xs:string*
```

### Parameters

**`$element`**
The element whose in-scope prefixes will be returned.

### Returns

`xs:string*`

### Examples

```xquery
xquery version "1.0-ml";
declare namespace a="a";
declare namespace b="b";

let $x := <a:hello>hello
            <b:goodbye>goodbye</b:goodbye>
	  </a:hello>
return
fn:in-scope-prefixes($x)

=> ("a", "xml")

xquery version "1.0-ml";
declare namespace a="a";
declare namespace b="b";

let $x := <a:hello>hello
            <b:goodbye>goodbye</b:goodbye>
	  </a:hello>
return
fn:in-scope-prefixes($x/b:goodbye)

=> ("b", "a", "xml")
```

---

## fn:index-of

Returns a sequence of positive integers giving the positions within the
sequence $seqParam of items that are equal to $srchParam.

      
The collation used by the invocation of this function is determined according
to the rules in 7.3.1 Collations. The collation is used when string comparison
is required.

      
The items in the sequence $seqParam are compared with $srchParam under the
rules for the eq operator. Values that cannot be compared, i.e. the eq operator
is not defined for their types, are considered to be distinct. If an item
compares equal, then the position of that item in the sequence $srchParam is
included in the result.

      
If the value of $seqParam is the empty sequence, or if no item in $seqParam
matches $srchParam, then the empty sequence is returned.

      
The first item in a sequence is at position 1, not position 0.

      
The result sequence is in ascending numeric order.

### Signature

```xquery
fn:index-of(
  $seqParam as xs:anyAtomicType*,
  $srchParam as xs:anyAtomicType,
  $collationLiteral as xs:string?
) as xs:integer*
```

### Parameters

**`$seqParam`**
A sequence of values.

**`$srchParam`**
A value to find on the list.

**`$collationLiteral`** *(optional)*
A collation identifier.

### Returns

`xs:integer*`

### Examples

```xquery
fn:index-of((10, 20, 30, 40), 35) returns ().

fn:index-of((10, 20, 30, 30, 20, 10), 20)
  returns (2, 5).

fn:index-of(("a", "sport", "and", "a", "pastime"), "a")
  returns (1, 4).

If @a is an attribute of type xs:NMTOKENS whose
typed value is " red green blue ", then:

fn:index-of(@a, "blue") returns 3.

This is because the function calling mechanism
atomizes the attribute node to produce a sequence of
three xs:NMTOKENs.
```

---

## fn:insert-before

Returns a new sequence constructed from the value of $target with the value of
$inserts inserted at the position specified by the value of $position. (The
value of $target is not affected by the sequence construction.)

      
If $target is the empty sequence, $inserts is returned. If $inserts is the
empty sequence, $target is returned.

      
The value returned by the function consists of all items of $target whose index
is less than $position, followed by all items of $inserts, followed by the
remaining elements of $target, in that sequence.

      
If $position is less than one (1), the first position, the effective value of
$position is one (1). If $position is greater than the number of items in
$target, then the effective value of $position is equal to the number of items
in $target plus 1.

      
For detailed semantics see, Section
7.2.15 The fn:insert-before function[FS].

### Signature

```xquery
fn:insert-before(
  $target as item()*,
  $position as xs:integer,
  $inserts as item()*
) as item()*
```

### Parameters

**`$target`**
The sequence of items into which new items will be inserted.

**`$position`**
The position in the target sequence at which the new items will be added.

**`$inserts`**
The items to insert into the target sequence.

### Returns

`item()*`

### Examples

```xquery
let $x := ("a", "b", "c")
return
fn:insert-before($x, 0, "z") returns ("z", "a", "b", "c")

let $x := ("a", "b", "c")
return
fn:insert-before($x, 1, "z") returns ("z", "a", "b", "c")

let $x := ("a", "b", "c")
return
fn:insert-before($x, 2, "z") returns ("a", "z", "b", "c")

let $x := ("a", "b", "c")
return
fn:insert-before($x, 3, "z") returns ("a", "b", "z", "c")

let $x := ("a", "b", "c")
return
fn:insert-before($x, 4, "z") returns ("a", "b", "c", "z")
```

---

## fn:iri-to-uri

Idempotent function that escapes non-URI characters.

### Signature

```xquery
fn:iri-to-uri(
  $uri-part as xs:string
) as xs:string
```

### Parameters

**`$uri-part`**
A string representing an unescaped URI.

### Returns

`xs:string`

### Examples

```xquery
fn:iri-to-uri("http://example.com/Weather/Los%20Angeles#ocean")
=> "http://example.com/Weather/Los%20Angeles#ocean"
```

---

## fn:lang

This function tests whether the language of $node, or the context node if the
second argument is omitted, as specified by xml:lang attributes is the same
as, or is a sublanguage of, the language specified by $testlang. The
language of the argument node, or the context node if the second argument is
omitted, is determined by the value of the xml:lang attribute on the node,
or, if the node has no such attribute, by the value of the xml:lang
attribute on the nearest ancestor of the node that has an xml:lang
attribute. If there is no such ancestor, then the function returns false

      
If the second argument is omitted and the context item is undefined an error is
raised: [err:XPDY0002]. If the context item is not a node an error is raised
[err:XPTY0004].

      
If $testlang is the empty sequence it is interpreted as the zero-length string.

      
The relevant xml:lang attribute is determined by the value of the XPath
expression:  (ancestor-or-self::* /@xml:lang)[last()]

      If this expression returns an empty sequence, the function returns false.

      
Otherwise, the function returns true if and only if the string-value of the
relevant xml:lang attribute is equal to $testlang based on a caseless default
match as specified in section 3.13 of [The Unicode Standard], or if the
string-value of the relevant testlang attribute contains a hyphen, "-"
(The character "-" is HYPHEN-MINUS, #x002D) such that the part of the
string-value preceding that hyphen is equal to $testlang, using caseless
matching.

### Signature

```xquery
fn:lang(
  $testlang as xs:string?,
  $node as node()?
) as xs:boolean
```

### Parameters

**`$testlang`**
The language against which to test the node.

**`$node`** *(optional)*
The node to test.

### Returns

`xs:boolean`

---

## fn:last

Returns the context size from the dynamic context. (See
Section C.2 Dynamic
Context Components[XP].) If the context item is undefined, an error is
raised [err:FONC0001].

### Returns

`xs:integer`

### Usage Notes

fn:last() returns the exact context position of the
  last item in the current context, so it must count all the items to do
  this. It is as much work as fn:count().
  fn:last() is therefore best used to find the last item in
  a short context sequence.  For example, it is useful in a path
  expression predicate to find the last child node of a particular
  element node in a particular document.
      Using fn:last() in a predicate expression is not an
  efficient way to extract a subsequence of large item sequence. Its use
  for this purpose is strongly discouraged. It is much more efficient to
  use fn:tail() or fn:subsequence() instead.

---

## fn:local-name

Returns the local part of the name of $arg as an xs:string that
will either be the zero-length string or will have the lexical form of
an xs:NCName.

      
If the argument is omitted, it defaults to the context node. If the context
item is undefined an error is raised: [err:XPDY0002]. If the context item is
not a node an error is raised: [err:XPTY0004].

      
If the argument is supplied and is the empty sequence, the function
returns the zero-length string.

      
If the target node has no name (that is, if it is a document node, a
comment, a text node, or a namespace node having no name), the
function returns the zero-length string.

      
Otherwise, the value returned will be the local part of the expanded-QName of
the target node (as determined by the dm:node-name accessor in Section 5.11
node-name Accessor[DM]. This will be an xs:string whose lexical form is an
xs:NCName.

### Signature

```xquery
fn:local-name(
  $arg as node()??
) as xs:string
```

### Parameters

**`$arg`** *(optional)*
The node whose local name is to be returned.

### Returns

`xs:string`

### Examples

```xquery
xquery version "1.0-ml";
declare namespace a="a";

let $x := <a:hello/>
return
fn:local-name($x)

=> hello
```

---

## fn:local-name-from-QName

Returns an xs:NCName representing the local part of
  $arg. If $arg is the empty sequence, returns the empty sequence.

### Signature

```xquery
fn:local-name-from-QName(
  $arg as xs:QName?
) as xs:NCName?
```

### Parameters

**`$arg`**
A qualified name.

### Returns

`xs:NCName?`

### Examples

```xquery
fn:local-name-from-QName(
   fn:QName("http://www.example.com/example", "person") )

=> person
```

---

## fn:lower-case

Returns the specified string converting all of the characters to lower-case
characters.  If a character does not have a corresponding lower-case character,
then the original character is returned. The lower-case characters are
determined using the Unicode Case Mappings.

### Signature

```xquery
fn:lower-case(
  $string as xs:string?
) as xs:string
```

### Parameters

**`$string`**
The string to convert.

### Returns

`xs:string`

### Examples

```xquery
fn:lower-case("aBCD")

=> abcd
```

---

## fn:map

Applies the function item $function to every item from the sequence
  $seq in turn,
  returning the concatenation of the resulting sequences in order.
  For more details, see
  XPath 3.0 Functions and Operators.

### Signature

```xquery
fn:map(
  $function as function(item()) as item()*,
  $seq as item()*
) as item()*
```

### Parameters

**`$function`**
The function value.

**`$seq`**
The function value.

### Returns

`item()*`

### Examples

```xquery
fn:map(function($a) { $a * 2 }, (1 to 10))
=> (2, 4, 6, 8, 10, 12, 14, 16, 18, 20)
```

---

## fn:map-pairs

Applies the function item $function to successive pairs of items taken
  one from $seq1 and one from $seq2, returning the concatenation of the
  resulting sequences in order.
  For more details, see
  XPath 3.0 Functions and Operators.

### Signature

```xquery
fn:map-pairs(
  $function as function(item(), item()) as item()*,
  $seq1 as item()*,
  $seq2 as item()*
) as item()*
```

### Parameters

**`$function`**
The map function value.

**`$seq1`**
The first sequence argument.

**`$seq2`**
The second sequence argument.

### Returns

`item()*`

### Examples

```xquery
fn:map-pairs(function($a, $b) { $a * $b }, (1 to 10), (2 to 10))
=> (2, 6, 12, 20, 30, 42, 56, 72, 90)
```

---

## fn:matches

Returns true if the specified $input matches the specified
$pattern, otherwise returns false.

### Signature

```xquery
fn:matches(
  $input as xs:string?,
  $pattern as xs:string,
  $flags as xs:string?
) as xs:boolean?
```

### Parameters

**`$input`**
The input from which to match.

**`$pattern`**
The regular expression to match.

**`$flags`** *(optional)*
The flag representing how to interpret the regular expression. One of
  "s", "m", "i", or "x", as defined in
  http://www.w3.org/TR/xpath-functions/#flags.

### Returns

`xs:boolean?`

### Examples

```xquery
fn:matches("this is a string", "is")

=> true

fn:matches("this is a string", "zoo")

=> false
```

---

## fn:max

Selects an item from the input sequence $arg whose value is greater than or
equal to the value of every other item in the input sequence. If there are
two or more such items, then the specific item whose value is returned is
implementation dependent.

      
The following rules are applied to the input sequence:

      
	Values of type xs:untypedAtomic in $arg are cast to xs:double.
	For numeric values, the numeric promotion rules defined in 6.2 Operators on
Numeric Values are used to promote all values to a single common type.

      
      
The items in the resulting sequence may be reordered in an arbitrary order. The
resulting sequence is referred to below as the converted sequence.This
function returns an item from the converted sequence rather than the input
sequence.

      
If the converted sequence is empty, the empty sequence is returned.

      
All items in $arg must be numeric or derived from a single base type for which
the ge operator is defined. In addition, the values in the sequence must
have a total order. If date/time values do not have a timezone, they are
considered to have the implicit timezone provided by the dynamic context for
purposes of comparison. Duration values must either all be
xs:yearMonthDuration values or must all be xs:dayTimeDuration values.

      
If any of these conditions is not met, then a type error is raised
  [err:FORG0006].

      
If the converted sequence contains the value NaN, the value NaN is returned.

      
If the items in the value of $arg are of type xs:string or types derived by
restriction from xs:string, then the determination of the item with the
largest value is made according to the collation that is used. If the type
of the items in $arg is not xs:string and $collation is specified, the
collation is ignored.

      
The collation used by the invocation of this function is determined according
to the rules in 7.3.1 Collations.

      
Otherwise, the result of the function is the result of the expression:

      
   if (every $v in $c satisfies $c[1] ge $v)
   then $c[1]
   else fn:max(fn:subsequence($c, 2))

      
evaluated with $collation as the default collation if specified, and with $c as
the converted sequence.

      
For detailed type semantics, see
Section
7.2.10 The fn:min, fn:max, fn:avg, and fn:sum functions[FS].

      
Notes:

      
If the converted sequence contains exactly one value then that value is
returned.

      
The default type when the fn:max function is applied to xs:untypedAtomic
values is xs:double. This differs from the default type for operators such as
gt, and for sorting in XQuery and XSLT, which is xs:string.

### Signature

```xquery
fn:max(
  $arg as xs:anyAtomicType*,
  $collation as xs:string?
) as xs:anyAtomicType?
```

### Parameters

**`$arg`**
The sequence of values whose maximum will be returned.

**`$collation`** *(optional)*
The optional name of a valid collation URI.  For information on the
  collation URI syntax, see the Search Developer's Guide.

### Returns

`xs:anyAtomicType?`

### Examples

```xquery
fn:max((3,4,5)) returns 5.
fn:max((5, 5.0e0)) returns 5.0e0.
fn:max((3,4,"Zero")) raises a type error [err:FORG0006].
fn:max((fn:current-date(), xs:date("2001-01-01")))
typically returns the current date.
fn:max(("a", "b", "c")) returns "c" under a typical
                                default collation.
```

---

## fn:min

Selects an item from the input sequence $arg whose value is less than or
equal to the value of every other item in the input sequence. If there are
two or more such items, then the specific item whose value is returned is
implementation dependent.

      
The following rules are applied to the input sequence:

      
	Values of type xs:untypedAtomic in $arg are cast to xs:double.
	For numeric values, the numeric promotion rules defined in 6.2 Operators on
Numeric Values are used to promote all values to a single common type.

      
      
The items in the resulting sequence may be reordered in an arbitrary order. The
resulting sequence is referred to below as the converted sequence.This
function returns an item from the converted sequence rather than the input
sequence.

      
If the converted sequence is empty, the empty sequence is returned.

      
All items in $arg must be numeric or derived from a single base type for which
the le operator is defined. In addition, the values in the sequence must
have a total order. If date/time values do not have a timezone, they are
considered to have the implicit timezone provided by the dynamic context for
purposes of comparison. Duration values must either all be
xs:yearMonthDuration values or must all be xs:dayTimeDuration values.

      
If any of these conditions is not met, then a type error is raised
  [err:FORG0006].

      
If the converted sequence contains the value NaN, the value NaN is returned.

      
If the items in the value of $arg are of type xs:string or types derived by
restriction from xs:string, then the determination of the item with the
largest value is made according to the collation that is used. If the type
of the items in $arg is not xs:string and $collation is specified, the
collation is ignored.

      
The collation used by the invocation of this function is determined according
to the rules in 7.3.1 Collations.

      
Otherwise, the result of the function is the result of the expression:

      
   if (every $v in $c satisfies $c[1] le $v)
   then $c[1]
   else fn:min(fn:subsequence($c, 2))

      
evaluated with $collation as the default collation if specified, and with $c as
the converted sequence.

      
For detailed type semantics, see
Section
7.2.10 The fn:min, fn:max, fn:avg, and fn:sum functions[FS].

      
Notes:

      
If the converted sequence contains exactly one value then that value is
returned.

      
The default type when the fn:min function is applied to xs:untypedAtomic
values is xs:double. This differs from the default type for operators such as
gt, and for sorting in XQuery and XSLT, which is xs:string.

### Signature

```xquery
fn:min(
  $arg as xs:anyAtomicType*,
  $collation as xs:string?
) as xs:anyAtomicType?
```

### Parameters

**`$arg`**
The sequence of values whose minimum will be returned.

**`$collation`** *(optional)*
The optional name of a valid collation URI.  For information on the
  collation URI syntax, see the Search Developer's Guide.

### Returns

`xs:anyAtomicType?`

### Examples

```xquery
fn:min((3,4,5)) returns 3.

fn:min((5, 5.0e0)) returns 5.0e0.

fn:min((3,4,"Zero")) raises a type error [err:FORG0006].

fn:min(xs:float(0.0E0), xs:float(-0.0E0) can return
either positive or negative zero.
[XML Schema Part 2: Datatypes Second Edition] does
not distinguish between the values positive zero
and negative zero.
The result is implementation dependent.

fn:min((fn:current-date(), xs:date("2001-01-01")))
typically returns xs:date("2001-01-01").

fn:min(("a", "b", "c")) returns "a" under a
typical default collation.
```

---

## fn:name

Returns the name of a node, as an xs:string that is either the
zero-length string, or has the lexical form of an xs:QName.

      
If the argument is omitted, it defaults to the context node. If the context
item is undefined an error is raised: [err:XPDY002]. If the context item is
not a node an error is raised: [err:XPTY0004].

      
If the argument is supplied and is the empty sequence, the function
returns the zero-length string.

      
If the target node has no name (that is, if it is a document node, a
comment, a text node, or a namespace node having no name), the
function returns the zero-length string.

      
If the specified node was created with a namespace prefix, that namespace
prefix is returned with the element localname (for example,
a:hello).  Note that the namespace prefix is not always the same
prefix that would be returned if you serialized the QName of the node, as
the serialized QName will use the namespace from the XQuery context in
which it was serialized.

### Signature

```xquery
fn:name(
  $arg as node()??
) as xs:string
```

### Parameters

**`$arg`** *(optional)*
The node whose name is to be returned.

### Returns

`xs:string`

### Examples

```xquery
xquery version "1.0-ml";
declare namespace a="a";

let $x := <a:hello/>
return
fn:name($x)

=> a:hello
```

---

## fn:namespace-uri

Returns the namespace URI of the xs:QName of the node specified by $arg.

      
If the argument is omitted, it defaults to the context node. If the context
item is undefined an error is raised: [err:XPDY0002]. If the context item is
not a node an error is raised: [err:XPTY0004].

      
If $arg is the empty sequence, the xs:anyURI
corresponding to the zero-length string is returned.

      
If $arg is neither an element nor an attribute node, or if it is an element or
attribute node whose expanded-QName (as determined by the dm:node-name
accessor in the Section 5.11 node-name Accessor[DM]) is in no namespace, then
the function returns the xs:anyURI corresponding to the zero-length string.

### Signature

```xquery
fn:namespace-uri(
  $arg as node()??
) as xs:anyURI
```

### Parameters

**`$arg`** *(optional)*
The node whose namespace URI is to be returned.

### Returns

`xs:anyURI`

### Examples

```xquery
xquery version "1.0-ml";
declare namespace a="aaa";

let $x := <a:hello/>
return
fn:namespace-uri($x)

=> aaa
```

---

## fn:namespace-uri-for-prefix

Returns the namespace URI of one of the in-scope namespaces for $element,
  identified by its namespace prefix.

      
  If $element has an in-scope namespace whose namespace prefix is equal to
  $prefix, it returns the namespace URI of that namespace. If $prefix is the
  zero-length string or the empty sequence, it returns the namespace URI of
  the default (unnamed) namespace. Otherwise, it returns the empty sequence.

      
  Prefixes are equal only if their Unicode code points match exactly.

### Signature

```xquery
fn:namespace-uri-for-prefix(
  $prefix as xs:string?,
  $element as element()
) as xs:anyURI?
```

### Parameters

**`$prefix`**
A namespace prefix to look up.

**`$element`**
An element node providing namespace context.

### Returns

`xs:anyURI?`

### Examples

```xquery
xquery version "1.0-ml";
declare namespace ex = "http://www.example.com/example";

let $x := <ex:hello>1</ex:hello>
return
fn:namespace-uri-for-prefix("ex", $x)

=> the namespace URI corresponding to
   "http://www.example.com/example".
```

---

## fn:namespace-uri-from-QName

Returns the namespace URI for $arg as an xs:string. If
  $arg is the empty sequence, the empty sequence is returned. If $arg
  is in no namespace, the zero-length string is returned.

### Signature

```xquery
fn:namespace-uri-from-QName(
  $arg as xs:QName?
) as xs:anyURI?
```

### Parameters

**`$arg`**
A qualified name.

### Returns

`xs:anyURI?`

### Examples

```xquery
fn:namespace-uri-from-QName(
  fn:QName("http://www.example.com/example", "person") )

=> the namespace URI corresponding to
   "http://www.example.com/example".
```

---

## fn:nilled

Summary: Returns an xs:boolean indicating whether the argument node is
"nilled". If the argument is not an element node, returns the empty sequence.
If the argument is the empty sequence, returns the empty sequence.
For element nodes, true() is returned
if the element is nilled, otherwise false().
      
Elements may be defined in a schema as nillable, which allows an empty
instance of an element to a appear in a document even though its type
requires that it always have some content.  Nilled elements should always be
empty but an element is not considered nilled just because it's empty.
It must also have the type annotation attribute xsi:nil="true".

### Signature

```xquery
fn:nilled(
  $arg as node()?
) as xs:boolean?
```

### Parameters

**`$arg`**
The node to test for nilled status.

### Returns

`xs:boolean?`

### Examples

```xquery
fn:nilled(<foo/>)
=> false

fn:nilled(<foo xsi:nil="true"/>)
=> true, if the schema for foo allows nillable

fn:nilled(<foo xsi:nil="false"/>)
=> false

fn:nilled(())
=> ()

fn:nilled(text { "foo" })
=> ()
```

---

## fn:node-kind

[0.9-ml only, use xdmp:node-kind in 1.0 and 1.0-ml]
  Returns an xs:string representing the node's kind: either
  "document", "element", "attribute", "text", "namespace",
  "processing-instruction", "binary", or "comment".

### Signature

```xquery
fn:node-kind(
  $node as node()?
) as xs:string
```

### Parameters

**`$node`**
The node whose kind is to be returned.

### Returns

`xs:string`

---

## fn:node-name

Returns an expanded-QName for node kinds that can have names.
For other kinds of nodes it returns the empty sequence. If $arg is the
empty sequence, the empty sequence is returned.

### Signature

```xquery
fn:node-name(
  $arg as node()?
) as xs:QName?
```

### Parameters

**`$arg`**
The node whose name is to be returned.

### Returns

`xs:QName?`

### Examples

```xquery
let $x := <hello><goodbye>1</goodbye></hello>
return
fn:node-name($x/child::element())

=> goodbye
```

---

## fn:normalize-space

Returns the specified string with normalized whitespace, which strips off
 any leading or trailing whitespace and replaces any other sequences of
 more than one whitespace characters with a single space
 character (#x20).

### Signature

```xquery
fn:normalize-space(
  $input as xs:string??
) as xs:string?
```

### Parameters

**`$input`** *(optional)*
The string from which to normalize whitespace.

### Returns

`xs:string?`

### Examples

```xquery
fn:normalize-space("
this
is
  a string
  ")

=> this is a string
```

---

## fn:normalize-unicode

Return the argument normalized according to the
normalization criteria for a normalization form identified by the
value of $normalizationForm. The effective value of the
$normalizationForm is computed by removing leading and trailing
blanks, if present, and converting to upper case.

### Signature

```xquery
fn:normalize-unicode(
  $arg as xs:string?,
  $normalizationForm as xs:string?
) as xs:string?
```

### Parameters

**`$arg`**
The string to normalize.

**`$normalizationForm`** *(optional)*
The form under which to normalize the specified string: NFC, NFD,
  NFKC, or NFKD.

### Returns

`xs:string?`

### Examples

```xquery
fn:normalize-unicode("Abcd")

=> Abcd
```

---

## fn:not

Returns true if the
  effective boolean value is false, and false
  if the effective boolean value is true.
  The $arg parameter is first reduced to an effective
  boolean value by applying the fn:boolean function.

### Signature

```xquery
fn:not(
  $arg as item()*
) as xs:boolean
```

### Parameters

**`$arg`**
The expression to negate.

### Returns

`xs:boolean`

### Examples

#### Example 1

```xquery
fn:not(fn:true())

=> false
```

#### Example 2

```xquery
fn:not("false")

=> false
```

---

## fn:number

Returns the value indicated by $arg or, if $arg is not specified, the context
item after atomization, converted to an xs:double. If $arg is the empty
sequence or if $arg or the context item cannot be converted to an xs:double,
the xs:double value NaN is returned. If the context item is undefined an
error is raised: [err:XPDY0002].

      
Calling the zero-argument version of the function is defined to give the same
result as calling the single-argument version with an argument of ".". That
is, fn:number() is equivalent to fn:number(.).

      
If $arg is the empty sequence, NaN is returned. Otherwise, $arg, or the context
item after atomization, is converted to an xs:double following the rules of
17.1.3.2 Casting to xs:double. If the conversion to xs:double fails, the
xs:double value NaN is returned.

### Signature

```xquery
fn:number(
  $arg as xs:anyAtomicType??
) as xs:double
```

### Parameters

**`$arg`** *(optional)*
The value to be returned as an xs:double value.

### Returns

`xs:double`

### Examples

```xquery
fn:number($item1/quantity)
=> 5.0

fn:number($item2)
=> NaN

Assume that the context item is the xs:string "15".
fn:number() returns 1.5E1.
```

---

## fn:one-or-more

Returns $arg if it contains one or more items. Otherwise, raises an error
   [err:FORG0004].

      
For detailed type semantics, see
Section 7.2.16 The fn:zero-or-one,
fn:one-or-more, and fn:exactly-one functions[FS].

### Signature

```xquery
fn:one-or-more(
  $arg as item()*
) as item()+
```

### Parameters

**`$arg`**
The sequence of items.

### Returns

`item()+`

### Examples

```xquery
fn:one-or-more( () )

=> XDMP-ZEROITEMS exception

fn:one-or-more("hello")

=> "hello"
```

---

## fn:position

Returns the context position from the dynamic context. (See
Section C.2 Dynamic
Context Components[XP].) If the context item is undefined, an error is
raised [err:FONC0001].

### Returns

`xs:integer`

### Examples

```xquery
let $x := (10, 20, 30, 40, 50)
return
$x[position() eq 2]

=> 20, which is in the second position in the sequence
```

---

## fn:prefix-from-QName

Returns an xs:NCName representing the prefix of $arg.
  The empty sequence is returned if $arg is the empty sequence or
  if the value of $arg contains no prefix.

### Signature

```xquery
fn:prefix-from-QName(
  $arg as xs:QName?
) as xs:NCName?
```

### Parameters

**`$arg`**
A qualified name.

### Returns

`xs:NCName?`

### Examples

#### Example 1

```xquery
xquery version "1.0-ml";
declare namespace ex="http://www.example.com/example";

fn:prefix-from-QName(
   fn:QName("http://www.example.com/example", "person") )

=> empty sequence, because the QName constructed
   by fn:QName does not have a prefix
```

#### Example 2

```xquery
let $qn := fn:QName("http://www.w3.org/XML/1998/namespace", "lang")
return
fn:prefix-from-QName(fn:node-name( attribute {$qn} {"en"}))

=> xml
```

---

## fn:remove

Returns a new sequence constructed from the value of $target with the item at
the position specified by the value of $position removed.

      
If $position is less than 1 or greater than the number of items in $target,
$target is returned. Otherwise, the value returned by the function consists
of all items of $target whose index is less than $position, followed by all
items of $target whose index is greater than $position. If $target is the
empty sequence, the empty sequence is returned.

      
For detailed type semantics, see
Section 7.2.11 The fn:remove function[FS].

### Signature

```xquery
fn:remove(
  $target as item()*,
  $position as xs:integer
) as item()*
```

### Parameters

**`$target`**
The sequence of items from which items will be removed.

**`$position`**
The position in the target sequence from which the items will be removed.

### Returns

`item()*`

### Examples

```xquery
let $x := ("a", "b", "c")
return
fn:remove($x, 0) returns ("a", "b", "c")

let $x := ("a", "b", "c")
return
fn:remove($x, 1) returns ("b", "c")

let $x := ("a", "b", "c")
return
fn:remove($x, 6) returns ("a", "b", "c")

let $x := ("a", "b", "c")
return
fn:remove((), 3) returns ()
```

---

## fn:replace

Returns a string constructed by replacing the specified $pattern
on the $input string with the specified $replacement string.

### Signature

```xquery
fn:replace(
  $input as xs:string?,
  $pattern as xs:string,
  $replacement as xs:string,
  $flags as xs:string?
) as xs:string?
```

### Parameters

**`$input`**
The string to start with.

**`$pattern`**
The regular expression pattern to match.  If the pattern does not match the
  $input string, the function will return the $input string unchanged.

**`$replacement`**
The regular expression pattern to replace the $pattern with.  It can also
  be a capture expression (for more details, see
  http://www.w3.org/TR/xpath-functions/#func-replace).

**`$flags`** *(optional)*
The flag representing how to interpret the regular expression. One of
  "s", "m", "i", or "x", as defined in
  http://www.w3.org/TR/xpath-functions/#flags.

### Returns

`xs:string?`

### Examples

```xquery
fn:replace("this is a string", "this", "that")

=> that is a string
```

---

## fn:resolve-QName

Returns an xs:QName value (that is, an expanded QName)
  by taking an xs:string that has the lexical form of an
  xs:QName (a string in the form "prefix:local-name" or
  "local-name") and resolving it using the in-scope namespaces for a
  given element.

### Signature

```xquery
fn:resolve-QName(
  $qname as xs:string?,
  $element as element()
) as xs:QName?
```

### Parameters

**`$qname`**
A string of the form "prefix:local-name".

**`$element`**
An element providing the in-scope namespaces to use to resolve the
  qualified name.

### Returns

`xs:QName?`

### Usage Notes

Sometimes the requirement is to construct an xs:QName
without using the default namespace. This can be achieved by writing:

      
     if ( fn:contains($qname, ":") )
     then ( fn:resolve-QName($qname, $element) )
     else ( fn:QName("", $qname) )

      If the requirement is to construct an xs:QName using the
namespaces in the static context, then the xs:QName
constructor should be used.

      
If $qname does not have the correct lexical form for xs:QName
an error is raised [err:FOCA0002].

      
If $qname is the empty sequence, returns the empty sequence.

      
More specifically, the function searches the namespace bindings of $element for
a binding whose name matches the prefix of $qname, or the zero-length string
if it has no prefix, and constructs an expanded QName whose local name is
taken from the supplied $qname, and whose namespace URI is taken from the
string value of the namespace binding.

      
If the $qname has a prefix and if there is no namespace binding for $element
that matches this prefix, then an error is raised [err:FONS0004].

      
If the $qname has no prefix, and there is no namespace binding for $element
corresponding to the default (unnamed) namespace, then the resulting
expanded QName has no namespace part.

      
The prefix (or absence of a prefix) in the supplied $qname argument is retained
in the returned expanded QName, as discussed in Section 2.1 Terminology[DM].

### Examples

```xquery
Assume that the element bound to $element has a single
namespace binding bound to the prefix "eg".

fn:resolve-QName("hello", $element)

=> a QName with local name "hello"
   that is in no namespace.

fn:resolve-QName("eg:myFunc", $element)

=> an xs:QName whose namespace URI is specified
   by the namespace binding corresponding to the
   prefix "eg" and whose local name is "myFunc".
```

---

## fn:resolve-uri

Resolves a relative URI against an absolute URI.  If $base is specified,
  the URI is resolved relative to that base.  If $base is not specified, the
  base is set to the base-uri property from the static context, if the
  property exists; if it does not exist, an error is thrown.

### Signature

```xquery
fn:resolve-uri(
  $relative as xs:string?,
  $base as xs:string?
) as xs:anyURI?
```

### Parameters

**`$relative`**
A URI reference to resolve against the base.

**`$base`** *(optional)*
An absolute URI to use as the base of the resolution.

### Returns

`xs:anyURI?`

### Usage Notes

If $base is specified, it is assumed to be an absolute URI and
$relative is assumed to be an absolute or a relative URI reference.
If $relative is a relative URI reference, it is resolved against $base,
using an algorithm such as the ones described in
[RFC 2396] or
[RFC 3986], and
the resulting absolute URI reference is returned.

      
If $relative is the zero-length string, fn:resolve-uri returns
the value of $base, or the base-uri property from the static context
if there is no $base value specified (if the base-uri property is
not initialized in the static context, an error is raised).

      
Resolving a URI does not dereference it. This is merely a syntactic operation
on two character strings.

### Examples

```xquery
fn:resolve-uri("hello/goodbye.xml",
     "http://mycompany/default.xqy")

=>  http://mycompany/hello/goodbye.xml
```

---

## fn:reverse

Reverses the order of items in a sequence. If $arg is the empty sequence,
the empty sequence is returned.

      
For detailed type semantics, see
Section
7.2.12 The fn:reverse function[FS].

### Signature

```xquery
fn:reverse(
  $target as item()*
) as item()*
```

### Parameters

**`$target`**
The sequence of items to be reversed.

### Returns

`item()*`

### Usage Notes

The sequence you specify to reverse must fit into memory, so the sequence
  size should not be larger than your memory cache sizes.

### Examples

#### Example 1

```xquery
let $x := ("a", "b", "c")
return
fn:reverse($x)

=> ("c", "b", "a")
```

#### Example 2

```xquery
fn:reverse(("hello"))

=> ("hello")
```

#### Example 3

```xquery
fn:reverse(())

=> ()
```

---

## fn:root

Returns the root of the tree to which $arg belongs. This will usually, but
not necessarily, be a document node.

      
If $arg is the empty sequence, the empty sequence is returned.

      
If $arg is a document node, $arg is returned.

      
If the function is called without an argument, the context item is used as
the default argument. If the context item is undefined an error is raised:
[err:XPDY0002]. If the context item is not a node an error is raised:
[err:XPTY0004].

### Signature

```xquery
fn:root(
  $arg as node()??
) as node()?
```

### Parameters

**`$arg`** *(optional)*
The node whose root node will be returned.

### Returns

`node()?`

### Examples

#### Example 1

```xquery
Assume the following variable definitions:
let $i := <tool>wrench</tool>
let $o := <order> {$i} <quantity>5</quantity> </order>
let $odoc := document {$o}
let $newi := $o/tool

fn:root($i) returns $i
fn:root($o/quantity) returns $o
fn:root($odoc//quantity) returns $odoc
fn:root($newi) returns $o
```

#### Example 2

```xquery
var doc = fn.head(xdmp.unquote('<a><quantity>5.0</quantity></a>')
    );
var elem = doc.root;
fn.root(elem).xpath("/a/quantity");
=> <quantity>5.0</quantity>
```

---

## fn:round

Returns the number with no fractional part that is closest to the argument. If
there are two such numbers, then the one that is closest to positive infinity
is returned. If type of $arg is one of the four numeric types xs:float,
xs:double, xs:decimal or xs:integer the type of the result is the same as the
type of $arg. If the type of $arg is a type derived from one of the numeric
types, the result is an instance of the base numeric type.

      
For xs:float and xs:double arguments, if the argument is positive infinity,
then positive infinity is returned. If the argument is negative infinity, then
negative infinity is returned. If the argument is positive zero, then positive
zero is returned. If the argument is negative zero, then negative zero is
returned. If the argument is less than zero, but greater than or equal to -0.5,
then negative zero is returned. In the cases where positive zero or negative
zero is returned, negative zero or positive zero may be returned as [XML Schema
Part 2: Datatypes Second Edition] does not distinguish between the values
positive zero and negative zero.

      
For the last two cases, note that the result is not the same as fn:floor(x+0.5).

      
For detailed type semantics, see Section 7.2.3 The fn:abs, fn:ceiling, fn:floor,
fn:round, and fn:round-half-to-even functions[FS].

### Signature

```xquery
fn:round(
  $arg as numeric?
) as numeric?
```

### Parameters

**`$arg`**
A numeric value to round.

### Returns

`numeric?`

### Examples

```xquery
fn:round(2.5) 
=> 3

fn:round(2.4999) 
=> 2

fn:round(-2.5) 
=> -2 (not the possible alternative, -3)
```

---

## fn:round-half-to-even

The value returned is the nearest (that is, numerically closest) numeric to
$arg that is a multiple of ten to the power of minus $precision. If two such
values are equally near (e.g. if the fractional part in $arg is exactly
.500...), returns the one whose least significant digit is even. If type of
$arg is one of the four numeric types xs:float, xs:double, xs:decimal or
xs:integer the type of the result is the same as the type of $arg. If the type
of $arg is a type derived from one of the numeric types, the result is an
instance of the base numeric type.

      
If no precision is specified, the result produces is the same as with
$precision=0.

      
For arguments of type xs:float and xs:double, if the argument is positive zero,
then positive zero is returned. If the argument is negative zero, then negative
zero is returned. If the argument is less than zero, but greater than or equal
o -0.5, then negative zero is returned.

      
If $arg is of type xs:float or xs:double, rounding occurs on the value of the
mantissa computed with exponent = 0.

      
For detailed type semantics, see Section 7.2.3 The fn:abs, fn:ceiling,
fn:floor, fn:round, and fn:round-half-to-even functions[FS].

### Signature

```xquery
fn:round-half-to-even(
  $arg as numeric?,
  $precision as xs:integer?
) as numeric?
```

### Parameters

**`$arg`**
A numeric value to round.

**`$precision`** *(optional)*
The precision to which to round the value.

### Returns

`numeric?`

### Examples

```xquery
fn:round-half-to-even(0.5)
=> 0

fn:round-half-to-even(1.5) 
=> 2

fn:round-half-to-even(2.5) 
=> 2

fn:round-half-to-even(3.567812E+3, 2) 
=> 3567.81E0

fn:round-half-to-even(4.7564E-3, 2) 
=> 0.0E0

fn:round-half-to-even(35612.25, -2) 
=> 35600
```

---

## fn:starts-with

Returns true if the first parameter starts with the string
 from the second parameter, otherwise returns false.

### Signature

```xquery
fn:starts-with(
  $parameter1 as xs:string?,
  $parameter2 as xs:string?,
  $collation as xs:string?
) as xs:boolean
```

### Parameters

**`$parameter1`**
The string from which to test.

**`$parameter2`**
The string to test whether it is at the beginning of the first parameter.

**`$collation`** *(optional)*
The optional name of a valid collation URI.  For information on the
  collation URI syntax, see the Search Developer's Guide.

### Returns

`xs:boolean`

### Examples

```xquery
fn:starts-with("abcd", "ab")

=> true
```

---

## fn:static-base-uri

Returns the value of the base-uri property from the static context. If the
base-uri property is undefined, the empty sequence is returned. Components of
the static context are discussed in 
Section C.1 Static Context Components[XP].

### Returns

`xs:anyURI?`

### Examples

```xquery
fn:static-base-uri()

=> ()
```

---

## fn:string

Returns the value of $arg represented as an xs:string. If no
 argument is supplied, this function returns the string value of the
 context item (.).

### Signature

```xquery
fn:string(
  $arg as item()??
) as xs:string?
```

### Parameters

**`$arg`** *(optional)*
The item to be rendered as a string.

### Returns

`xs:string?`

### Usage Notes

If no argument is supplied and the context item is undefined, an error is
raised.

If $arg is the empty sequence, the zero-length string is returned.

If $arg is a node, the function returns the string-value of the node, as
obtained using the dm:string-value accessor.

If $arg is an atomic value, then the function returns the same string as is
returned by the expression:$arg cast as xs:string

### Examples

```xquery
let $x := <hello>hello<goodbye>goodbye</goodbye></hello>
return
fn:string($x)

=> hellogoodbye
```

---

## fn:string-join

Returns an xs:string created by concatenating the members of
the $parameter1 sequence using $parameter2 as a separator. If the value of $arg2 is the
zero-length string, then the members of $parameter1 are concatenated without a
separator.

      
If the value of $parameter1 is the empty sequence, the zero-length string is returned.

### Signature

```xquery
fn:string-join(
  $parameter1 as xs:string*,
  $parameter2 as xs:string
) as xs:string
```

### Parameters

**`$parameter1`**
A sequence of strings.

**`$parameter2`**
A separator string to concatenate between the items in $parameter1.

### Returns

`xs:string`

### Examples

#### Example 1

```xquery
fn:string-join(("hello", "goodbye"), " and ")

=> hello and goodbye
```

#### Example 2

```xquery
let $string := "this is a string"
return
fn:string-join(fn:tokenize($string, " "),
               "-")

=> this-is-a-string
```

---

## fn:string-length

Returns an integer representing the length of the specified string.  The
length is 1-based, so a string that is one character long returns a value of 1.

### Signature

```xquery
fn:string-length(
  $sourceString as xs:string??
) as xs:integer?
```

### Parameters

**`$sourceString`** *(optional)*
The string to calculate the length.

### Returns

`xs:integer?`

### Examples

```xquery
fn:string-length("12345")

=> 5
```

---

## fn:string-pad

[0.9-ml only] Returns a string representing the $padString
   concatenated with itself the number of times specified in $padCount.

### Signature

```xquery
fn:string-pad(
  $padString as xs:string?,
  $padCount as xs:integer
) as xs:string?
```

### Parameters

**`$padString`**
The string to pad.

**`$padCount`**
The number of times to pad the string.

### Returns

`xs:string?`

### Examples

```xquery
fn:string-pad("abc", 3)

=> abcabcabc
```

---

## fn:string-to-codepoints

Returns the sequence of Unicode code points that constitute an xs:string.
If $arg is a zero-length string or the empty sequence, the empty sequence is
returned.

### Signature

```xquery
fn:string-to-codepoints(
  $arg as xs:string
) as xs:integer*
```

### Parameters

**`$arg`**
A string.

### Returns

`xs:integer*`

### Examples

```xquery
fn:string-to-codepoints("Thèrése")

returns the sequence (84, 104, 233, 114, 232, 115, 101)
```

---

## fn:subsequence

Returns the contiguous sequence of items in the value of $sourceSeq beginning
at the position indicated by the value of $startingLoc and continuing for the
number of items indicated by the value of $length.

      
As described in https://www.w3.org/TR/xpath-functions/:

      
In the two-argument case, fn.subsequence returns a sequence comprising those items of 
$sourceSeq whose index position (counting from one) is greater than or equal to the 
value of $startingLoc (rounded to an integer):

      
$sourceSeq[fn:round($startingLoc) le $p]

      
No error occurs if $startingLoc is zero or negative. 

      
In the three-argument case, The function returns a sequence comprising those items of 
$sourceSeq whose index position (counting from one) is greater than or equal to the 
value of $startingLoc (rounded to an integer), and less than the sum of 
$startingLoc and $length (both rounded to integers): 

      
$sourceSeq[fn:round($startingLoc) le $p
     and $p lt fn:round($startingLoc) + fn:round($length)]

      
No error occurs if $startingLoc is zero or negative, or if $startingLoc
plus $length exceeds the number of items in the sequence, or if 
$length is negative.

      
Notes:

      
If $sourceSeq is the empty sequence, the empty sequence is returned.

      
If $startingLoc is zero or negative, the subsequence includes items from the
beginning of the $sourceSeq.

      
If $length is not specified, the subsequence includes items to the end of
$sourceSeq.

      
If $length is greater than the number of items in the value of $sourceSeq
following $startingLoc, the subsequence includes items to the end of
$sourceSeq.

      
The first item of a sequence is located at position 1, not position 0.

      
For detailed type semantics, see Section 7.2.13 The fn:subsequence functional specification.

      
The reason the function accepts arguments of type xs:double is that many
computations on untyped data return an xs:double result; and the reason for the
rounding rules is to compensate for any imprecision in these floating-point
computations.

### Signature

```xquery
fn:subsequence(
  $sourceSeq as item()*,
  $startingLoc as xs:double,
  $length as xs:double?
) as item()*
```

### Parameters

**`$sourceSeq`**
The sequence of items from which a subsequence will be selected.

**`$startingLoc`**
The starting position of the start of the subsequence.

**`$length`** *(optional)*
The length of the subsequence.

### Returns

`item()*`

### Examples

```xquery
Assume $seq = ($item1, $item2, $item3, $item4, ...)

fn:subsequence($seq, 4) returns ($item4, ...)

fn:subsequence($seq, 3, 2) returns ($item3, $item4)
```

---

## fn:substring

Returns a substring starting from the $startingLoc and continuing
for $length characters.

### Signature

```xquery
fn:substring(
  $sourceString as xs:string?,
  $startingLoc as xs:double,
  $length as xs:double?
) as xs:string?
```

### Parameters

**`$sourceString`**
The string from which to create a substring.

**`$startingLoc`**
The number of characters from the start of the $sourceString.

**`$length`** *(optional)*
The number of characters beyond the $startingLoc.

### Returns

`xs:string?`

### Examples

```xquery
fn:substring("123456", 2, 2)

=> "23"
```

---

## fn:substring-after

Returns the substring created by taking all of the input characters
  that occur after the specified $after characters.

### Signature

```xquery
fn:substring-after(
  $input as xs:string?,
  $after as xs:string?,
  $collation as xs:string?
) as xs:string?
```

### Parameters

**`$input`**
The string from which to create the substring.

**`$after`**
The string after which the substring is created.

**`$collation`** *(optional)*
The optional name of a valid collation URI.  For information on the
  collation URI syntax, see the Search Developer's Guide.

### Returns

`xs:string?`

### Examples

```xquery
fn:substring-after("123456", "3")

=> "456"
```

---

## fn:substring-before

Returns the substring created by taking all of the input characters
  that occur before the specified $before characters.

### Signature

```xquery
fn:substring-before(
  $input as xs:string?,
  $before as xs:string?,
  $collation as xs:string?
) as xs:string?
```

### Parameters

**`$input`**
The string from which to create the substring.

**`$before`**
The string before which the substring is created.

**`$collation`** *(optional)*
The optional name of a valid collation URI.  For information on the
  collation URI syntax, see the Search Developer's Guide.

### Returns

`xs:string?`

### Examples

```xquery
fn:substring-before("abcdef", "def")

=> abc
```

---

## fn:sum

Returns a value obtained by adding together the values in $arg. If $zero is not
specified, then the value returned for an empty sequence is the xs:integer
value 0. If $zero is specified, then the value returned for an empty
sequence is $zero.

      
Any values of type xs:untypedAtomic in $arg are cast to xs:double. The items
in the resulting sequence may be reordered in an arbitrary order. The
resulting sequence is referred to below as the converted sequence.

      
If the converted sequence is empty, then the single-argument form of the
function returns the xs:integer value 0; the two-argument form returns the
value of the argument $zero.

      
If the converted sequence contains the value NaN, NaN is returned.

      
All items in $arg must be numeric or derived from a single base type. In
addition, the type must support addition. Duration values must either all be
xs:yearMonthDuration values or must all be xs:dayTimeDuration values. For
numeric values, the numeric promotion rules defined in 6.2 Operators on
Numeric Values are used to promote all values to a single common type. The
sum of a sequence of integers will therefore be an integer, while the sum of
a numeric sequence that includes at least one xs:double will be an
xs:double.

      
If the above conditions are not met, a type error is raised [err:FORG0006].

      
Otherwise, the result of the function, using the second signature, is the
result of the expression:

      
   if (fn:count($c) eq 0) then
       $zero
   else if (fn:count($c) eq 1) then
       $c[1]
   else
       $c[1] + fn:sum(subsequence($c, 2))

      
where $c is the converted sequence.

      
The result of the function, using the first signature, is the result of the
expression:fn:sum($arg, 0).

      
For detailed type semantics, see
Section
7.2.10 The fn:min, fn:max, fn:avg, and fn:sum functions[FS].

      
Notes:

      
The second argument allows an appropriate value to be defined to represent the
sum of an empty sequence. For example, when summing a sequence of durations
it would be appropriate to return a zero-length duration of the appropriate
type. This argument is necessary because a system that does dynamic typing
cannot distinguish "an empty sequence of integers", for example, from "an
empty sequence of durations".

      
If the converted sequence contains exactly one value then that value is
returned.

### Signature

```xquery
fn:sum(
  $arg as xs:anyAtomicType*,
  $zero as xs:anyAtomicType??
) as xs:anyAtomicType?
```

### Parameters

**`$arg`**
The sequence of values to be summed.

**`$zero`** *(optional)*
The value to return as zero if the input sequence is the empty sequence.
   This parameter is not available in the 0.9-ml XQuery dialect.

### Returns

`xs:anyAtomicType?`

### Usage Notes

When running this in the 0.9-ml XQuery dialect, there is no second
  argument to fn:sum; the second ($zero) argument is available
  in both the 1.0 and 1.0-ml dialects.

### Examples

```xquery
Assume:
$d1 = xs:yearMonthDuration("P20Y")
$d2 = xs:yearMonthDuration("P10M")
$seq1 = ($d1, $d2)
$seq3 = (3, 4, 5)

fn:sum(($d1, $d2))
returns an xs:yearMonthDuration with a value of 250 months.

fn:sum($seq1[. &gt; xs:yearMonthDuration('P3M')],
                 xs:yearMonthDuration('P0M'))
returns an xs:yearMonthDuration with a value of 0 months.

fn:sum($seq3) returns 12.

fn:sum(()) returns 0.

fn:sum((),()) returns ().

fn:sum((1 to 100)[.&gt;0], 0) returns 0.

fn:sum(($d1, 9E1)) raises an error [err:FORG0006].
```

---

## fn:tail

Returns all but the first item in a sequence.
  For more details, see
  XPath 3.0 Functions and Operators.

### Signature

```xquery
fn:tail(
  $seq as item()*
) as item()*
```

### Parameters

**`$seq`**
The function value.

### Returns

`item()*`

### Examples

```xquery
fn:tail((1,2,3))
=> (2, 3)
```

---

## fn:tokenize

Returns a sequence of strings constructed by breaking the specified
  input into substrings separated by the specified $pattern.  The
  specified $pattern is not returned as part of the returned items.

### Signature

```xquery
fn:tokenize(
  $input as xs:string?,
  $pattern as xs:string,
  $flags as xs:string?
) as xs:string*
```

### Parameters

**`$input`**
The string to tokenize.

**`$pattern`**
The regular expression pattern from which to separate the tokens.

**`$flags`** *(optional)*
The flag representing how to interpret the regular expression. One of
  "s", "m", "i", or "x", as defined in
  http://www.w3.org/TR/xpath-functions/#flags.

### Returns

`xs:string*`

### Examples

```xquery
fn:tokenize("this is a string", " ")

=> returns the sequence ("this", "is", "a", "string")

fn:tokenize("this is a string", " ")[last()]

=> string
```

---

## fn:translate

Returns a string where every character in $src that occurs in some
position in the $mapString is translated into the $transString character
in the corresponding location of the $mapString character.

### Signature

```xquery
fn:translate(
  $src as xs:string?,
  $mapString as xs:string?,
  $transString as xs:string?
) as xs:string?
```

### Parameters

**`$src`**
The string to translate characters.

**`$mapString`**
The string representing characters to be translated.

**`$transString`**
The string representing the characters to which the
  $mapString characters are translated.

### Returns

`xs:string?`

### Examples

```xquery
fn:translate("abcd", "abcd", "wxyz")

=> wxyz
```

---

## fn:true

Returns the xs:boolean value true.
  Equivalent to xs:boolean("1").

### Returns

`xs:boolean`

### Examples

```xquery
fn:true()

=> true
```

---

## fn:unordered

Returns the items of $sourceSeq in an implementation dependent order.

      
Note:

      
Query optimizers may be able to do a better job if the order of the output
sequence is not specified. For example, when retrieving prices from a
purchase order, if an index exists on prices, it may be more efficient to
return the prices in index order rather than in document order.

### Signature

```xquery
fn:unordered(
  $sourceSeq as item()*
) as item()*
```

### Parameters

**`$sourceSeq`**
The sequence of items.

### Returns

`item()*`

### Examples

```xquery
fn:unordered((1, 3, 2))

=> 1, 3, 2
```

---

## fn:upper-case

Returns the specified string converting all of the characters to upper-case
characters.  If a character does not have a corresponding upper-case character,
then the original character is returned. The upper-case characters are
determined using the Unicode Case Mappings.

### Signature

```xquery
fn:upper-case(
  $string as xs:string?
) as xs:string
```

### Parameters

**`$string`**
The string to upper-case.

### Returns

`xs:string`

### Examples

```xquery
fn:upper-case("Abcd")

=> ABCD
```

---

## fn:zero-or-one

Returns $arg if it contains zero or one items. Otherwise, raises an error
   [err:FORG0003].

      
For detailed type semantics, see 
Section 7.2.16 The fn:zero-or-one,
fn:one-or-more, and fn:exactly-one functions[FS].

### Signature

```xquery
fn:zero-or-one(
  $arg as item()*
) as item()?
```

### Parameters

**`$arg`**
The sequence of items.

### Returns

`item()?`

### Examples

```xquery
fn:zero-or-one("hello")

=> "hello"

fn:zero-or-one(("hello", "goodbye"))

=> XDMP-MORETHANONEITEM exception (because there are two items)
```

---

## sql:glob

Returns true if the specified $input glob the specified
  $pattern, otherwise returns false.

### Signature

```xquery
sql:glob(
  $input as xs:string?,
  $pattern as xs:string
) as xs:boolean?
```

### Parameters

**`$input`**
The input from which to match.

**`$pattern`**
The expression to match.
  '?' matches one character and '*' matches any number of characters.

### Returns

`xs:boolean?`

### Examples

```xquery
sql:glob("this string", "id*")

  => false

  sql:glob("this", "t*i?")

  => true
```

---

## sql:like

Returns true if the specified $input like the specified
$pattern, otherwise returns false.

### Signature

```xquery
sql:like(
  $input as xs:string?,
  $pattern as xs:string,
  $escape as xs:string
) as xs:boolean?
```

### Parameters

**`$input`**
The input from which to match.

**`$pattern`**
The expression to match.
  '_' matches one character and '%' matches any number of characters.

**`$escape`**
If a '_' or '%' are preceeded by an escape character then it will be
  match as the char '_'/'%' themselves.

### Returns

`xs:boolean?`

### Examples

```xquery
sql:like("this string", "id%")

=> false

sql:like("this", "t%i_")

=> true
```

---
