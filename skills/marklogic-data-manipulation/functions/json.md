# Json

22 functions in this category.

## json:array

Creates a (JSON) array, which is like a sequence of values, but allows
  for nesting.

### Signature

```xquery
json:array(
  $array as element(json:array)?
) as json:array
```

### Parameters

**`$array`** *(optional)*
A serialized array element.

### Returns

`json:array`

---

## json:array-pop

Pop a value from the end of the array.

### Signature

```xquery
json:array-pop(
  $array as json:array
) as item()*
```

### Parameters

**`$array`**
An array.

### Returns

`item()*`

---

## json:array-push

Push a value to the end of the array, increasing the size of the array
  by one.

### Signature

```xquery
json:array-push(
  $array as json:array,
  $item as item()*
) as empty-sequence()
```

### Parameters

**`$array`**
An array.

**`$item`**
New entries.

### Returns

`empty-sequence()`

---

## json:array-resize

Resize the array to the new size. If the new size is greater than the old
  size, the new entries will be null. If the new size if smaller than the old
  size, the extra entries will be removed.

### Signature

```xquery
json:array-resize(
  $array as json:array,
  $newSize as xs:unsignedLong,
  $zero as item()??
) as empty-sequence()
```

### Parameters

**`$array`**
An array.

**`$newSize`**
New size.

**`$zero`** *(optional)*
The value to use to pad out the array, if necessary. By default the
    empty sequence is used.

### Returns

`empty-sequence()`

---

## json:array-set-javascript-by-ref

If true is specified, sets a json:array to be passed to JavaScript by
  reference.  By default, a map:map is passed to JavaScript by value.

### Signature

```xquery
json:array-set-javascript-by-ref(
  $array as json:array,
  $key as xs:boolean
) as empty-sequence()
```

### Parameters

**`$array`**
A json array.

**`$key`**
True or false.

### Returns

`empty-sequence()`

---

## json:array-size

Returns the size of the array.

### Signature

```xquery
json:array-size(
  $array as json:array?
) as xs:unsignedLong?
```

### Parameters

**`$array`**
An array.

### Returns

`xs:unsignedLong?`

---

## json:array-values

Returns the array values as an XQuery sequence.

### Signature

```xquery
json:array-values(
  $array as json:array,
  $flatten as xs:boolean??
) as item()*
```

### Parameters

**`$array`**
An array.

**`$flatten`** *(optional)*
Include values from subarrays in the sequence. The default is false,
    meaning that subarrays are returned as array values.

### Returns

`item()*`

---

## json:array-with

Push a value to the end of the array, increasing the size of the array
  by one. Returns the array as the result.

### Signature

```xquery
json:array-with(
  $array as json:array,
  $item as item()*
) as json:array
```

### Parameters

**`$array`**
An array.

**`$item`**
New entries.

### Returns

`json:array`

---

## json:null

Returns the JSON null value, which is an empty sequence to XQuery,
  but not a Sequence when passed to JavaScript.

### Returns

`empty-sequence()`

---

## json:object

Creates a JSON object, which is a kind of map with a fixed and ordered set of
  keys.

### Signature

```xquery
json:object(
  $map as element(json:object)?
) as map:map
```

### Parameters

**`$map`** *(optional)*
A serialized JSON object.

### Returns

`map:map`

---

## json:object-define

Creates a JSON object.

### Signature

```xquery
json:object-define(
  $keys as xs:string*?
) as json:object
```

### Parameters

**`$keys`** *(optional)*
The sequence of keys in this object.

### Returns

`json:object`

---

## json:set-item-at

Sets a value in an array at a specified position.

### Signature

```xquery
json:set-item-at(
  $array as json:array,
  $pos as xs:double,
  $value as item()*
) as empty-sequence()
```

### Parameters

**`$array`**
An array.

**`$pos`**
The position to update. Invalid positions throw XDMP-ARRAYINDEXOUTOFBOUNDS

**`$value`**
A value.  Empty sequences are allowed.

### Returns

`empty-sequence()`

---

## json:subarray

Extract a subarray from an array, producing a new array.
   The second and third arguments to this function operate similarly to
   those of fn:subsequence for XQuery sequences.

### Signature

```xquery
json:subarray(
  $array as json:array,
  $startingLoc as xs:double,
  $length as xs:double?
) as json:array
```

### Parameters

**`$array`**
An array.

**`$startingLoc`**
The starting position of the start of the subarray.

**`$length`** *(optional)*
The length of the subarray.

### Returns

`json:array`

---

## json:to-array

Constructs a json:array from a sequence of items.

### Signature

```xquery
json:to-array(
  $items as item()*?,
  $limit as xs:double??,
  $zero as item()??
) as json:array
```

### Parameters

**`$items`** *(optional)*
The items to be used as elements in the constructed array.

**`$limit`** *(optional)*
The size of the array to construct. If the size is less than the length
    of the item sequence, only as "limit" items are put into the array. If
    the size is more than the length of the sequence, the array is filled
    with null values up to the limit.

**`$zero`** *(optional)*
The value to use to pad out the array, if necessary. By default the empty
    sequence is used.

### Returns

`json:array`

### Usage Notes

Use this function to construct an in-memory object that represents
  a JSON array, suitable for use with xdmp:to-json.
  This function does not produce an array node. To construct an array node, 
  use the array-node constructor.

---

## xdmp:from-json

Atomizes a JSON node, returning a JSON value.

### Signature

```xquery
xdmp:from-json(
  $arg as node()
) as item()*
```

### Parameters

**`$arg`**
A node of kind object-node(), array-node(),
    text(), number-node(), boolean-node(),
    null-node(), or document-node().

### Returns

`item()*`

### Usage Notes

An object-node() atomizes as a json:object.
      An array-node() atomizes as a json:array.
      A null-node() atomizes as an empty sequence.
      A boolean-node() atomizes as an xs:boolean.
      A number-node() atomizes as an xs:integer,
     xs:decimal, or xs:double value.
      A text() node atomizes as an xs:untypedAtomic.
      A document-node() atomizes the same as its root.
      This function returns the same result as fn:data,
     but it only works on JSON nodes.
      To make a JSON node from a string, use xdmp:unquote
     with the "format-json" option.

---

## xdmp:from-json-string

Parses a string as JSON, returning an item sequence.

### Signature

```xquery
xdmp:from-json-string(
  $arg as xs:string
) as item()*
```

### Parameters

**`$arg`**
JSON input to be parsed.

### Returns

`item()*`

### Usage Notes

A JSON object or string is parsed as a json:object.
      The JSON null value is represented as the empty sequence, and serializes
  in a way that indicates it is a null value.  Therefore, when the null value
  is returned to JSON via xdmp:to-json, the null value is
  preserved.
      Nested arrays in JSON are turned into nested sets of
  json:arrays.
      Any codepoints in the JSON string that aren't allowed in XML are
     rejected and an error is thrown.

### Examples

#### Example 1

```xquery
xdmp:from-json-string('["a", null, false]')
=>
json:array(
<json:array xmlns:xs="http://www.w3.org/2001/XMLSchema"
   xmlns:xsi="http://www.w3.org/2001/XMLSchema-instance"
   xmlns:json="http://marklogic.com/xdmp/json">
   <json:value xsi:type="xs:string">a</json:value>
   <json:value xsi:nil="true"/>
   <json:value xsi:type="xs:boolean">false</json:value>
</json:array>)
```

#### Example 2

```xquery
xquery version "1.0-ml";

let $json :=
  '[{"some-key":45683}, "this is a string", 123]'
return
xdmp:from-json-string($json)

=>

json:array(
<json:array xmlns:xs="http://www.w3.org/2001/XMLSchema"
  xmlns:xsi="http://www.w3.org/2001/XMLSchema-instance"
  xmlns:json="http://marklogic.com/xdmp/json">
  <json:value>
    <json:object>
      <json:entry key="some-key">
        <json:value xsi:type="xs:integer">45683</json:value>
      </json:entry>
    </json:object>
  </json:value>
  <json:value xsi:type="xs:string">this is a string</json:value>
  <json:value xsi:type="xs:integer">123</json:value></json:array>)

Note that what is shown above is the serialization of the XQuery items to
a json:array.  You can also use some or all of the items in the XQuery data
model.  For example, consider the following, which adds to the map based on the
other values:

xquery version "1.0-ml";
let $json :=
  '[{"some-key":45683}, "this is a string", 123]'
let $items := xdmp:from-json-string($json)
let $put := map:put($items[1], xs:string($items[3]), $items[2])
return
($items[1], xdmp:to-json-string($items[1]))

(: returns the following json:array and JSON string:
json:object(
<json:object xmlns:xs="http://www.w3.org/2001/XMLSchema"
  xmlns:xsi="http://www.w3.org/2001/XMLSchema-instance"
  xmlns:json="http://marklogic.com/xdmp/json">
  <entry key="some-key">
    <json:value xsi:type="xs:integer">45683</json:value>
  </entry>
  <entry key="123">
    <json:value xsi:type="xs:string">this is a string</json:value>
  </entry>
</json:object>)
{"some-key":45683, "123":"this is a string"}

This query uses the map functions to modify the first json:object
in the json:array.
:)
```

---

## xdmp:json-validate

Validate a JSON node against a JSON Schema. If the node is not valid per the schema, raise an error. Otherwise, return the input node.

### Signature

```xquery
xdmp:json-validate(
  $node as node(),
  $schema as xs:string,
  $options as xs:string*
) as node()
```

### Parameters

**`$node`**
JSON node to be validated.

**`$schema`**
URI of the JSON schema to use for validation.

**`$options`**
Validation options. Supported options:
    
    "full"Keep trying to find all the errors.
    "strict"Stop after the first error. (Default)

### Returns

`node()`

### Examples

```xquery
(: Assuming the following JSON schema is in the schema database at
   "/schemas/example.json" :
    {
      "language": "zxx",
      "$schema": "http://json-schema.org/draft-07/schema#",
      "properties": {
         "count": { "type":"integer", "minimum":0 },
         "items": { "type":"array", "items": {"type":"string", "minLength":1 } }
      }
    }
:)
  xdmp:json-validate(
     object-node{ "count": 3, "items": array-node{12} }, "/schemas/example.json" )

=> XDMP-JSVALIDATEINVTYPE: Invalid node type: Expected node of type text, found number at number-node{12} using schema "/schemas/example.json"
at 1:0 [1.0-ml]
```

---

## xdmp:json-validate-node

Validate a JSON node against a JSON Schema. If the node is not valid per the schema, raise an error. Otherwise, return the input node.

### Signature

```xquery
xdmp:json-validate-node(
  $node as node(),
  $schema as node(),
  $options as xs:string*
) as node()
```

### Parameters

**`$node`**
JSON node to be validated.

**`$schema`**
A JSON schema node use for validatation.

**`$options`**
Validation options. Supported options:
    
    "full"Keep trying to find all the errors.
    "strict"Stop after the first error. (Default)

### Returns

`node()`

### Examples

```xquery
xdmp:json-validate-node(
     object-node{ "count": 3, "items": array-node{12} }, 
     object-node{
       "properties": object-node{
          "count": object-node{ "type":"integer", "minimum":0 },
          "items": object-node{ "type":"array", "items": object-node{"type":"string", "minLength":1 } }
        }
     })

=> XDMP-JSVALIDATEINVTYPE: Invalid node type: Expected node of type text, found number at number-node{12} using schema ""
at 1:0 [1.0-ml]
```

---

## xdmp:json-validate-report

Validate a JSON node against a JSON Schema and return an error report.

### Signature

```xquery
xdmp:json-validate-report(
  $node as node(),
  $schema as xs:string,
  $options as xs:string*
) as element(xdmp:validation-errors)
```

### Parameters

**`$node`**
JSON node to be validated.

**`$schema`**
URI of the JSON schema to use for validation.

**`$options`**
Validation options. Supported options:
    
    "full"Keep trying to find all the errors. (Default)
    "strict"Stop after the first error.

### Returns

`element(xdmp:validation-errors)`

### Examples

```xquery
(: Assuming the following JSON schema is in the schema database at
   "/schemas/example.json" :
    {
      "language": "zxx",
      "$schema": "http://json-schema.org/draft-07/schema#",
      "properties": {
         "count": { "type":"integer", "minimum":0 },
         "items": { "type":"array", "items": {"type":"string", "minLength":1 } }
      }
    }
:)
  xdmp:json-validate-report(
     object-node{ "count": 3, "items": array-node{12} }, "/schemas/example.json" )

=> 
<xdmp:validation-errors xmlns:xdmp="http://marklogic.com/xdmp">
<error:error xmlns:error="http://marklogic.com/xdmp/error" xmlns:xsi="http://www.w3.org/2001/XMLSchema-instance">
    <error:code>XDMP-JSVALIDATEINVTYPE</error:code>
    <error:name/>
    <error:xquery-version>1.0-ml</error:xquery-version>
    <error:message>Invalid node type</error:message>
    <error:format-string>XDMP-JSVALIDATEINVTYPE: Invalid node type: Expected node of type text, found number at number-node{12} using schema "/schemas/example.json"</error:format-string>
    <error:retryable>false</error:retryable>
    <error:expr/>
    <error:data>
      <error:datum>number-node{12}</error:datum>
      <error:datum>"/schemas/example.json"</error:datum>
      <error:datum>text</error:datum>
      <error:datum>number</error:datum>
    </error:data>
    <error:stack>
      <error:frame>
	<error:line>2</error:line>
	<error:column>2</error:column>
	<error:xquery-version>1.0-ml</error:xquery-version>
      </error:frame>
    </error:stack>
  </error:error>
  <error:error xmlns:error="http://marklogic.com/xdmp/error" xmlns:xsi="http://www.w3.org/2001/XMLSchema-instance">
    <error:code>XDMP-JSVALIDATEINVNODE</error:code>
    <error:name/>
    <error:xquery-version>1.0-ml</error:xquery-version>
    <error:message>Invalid node</error:message>
    <error:format-string>XDMP-JSVALIDATEINVNODE: Invalid node: Node number-node{12} not valid against property 'items' expected {type: string, minLength: 1} using schema "/schemas/example.json"</error:format-string>
    <error:retryable>false</error:retryable>
    <error:expr/>
    <error:data>
      <error:datum>items</error:datum>
      <error:datum>number-node{12}</error:datum>
      <error:datum>"/schemas/example.json"</error:datum>
      <error:datum>{type: string, minLength: 1}</error:datum>
    </error:data>
    <error:stack>
      <error:frame>
	<error:line>2</error:line>
	<error:column>2</error:column>
	<error:xquery-version>1.0-ml</error:xquery-version>
      </error:frame>
    </error:stack>
  </error:error>
  <error:error xmlns:error="http://marklogic.com/xdmp/error" xmlns:xsi="http://www.w3.org/2001/XMLSchema-instance">
    <error:code>XDMP-JSVALIDATEINVNODE</error:code>
    <error:name/>
    <error:xquery-version>1.0-ml</error:xquery-version>
    <error:message>Invalid node</error:message>
    <error:format-string>XDMP-JSVALIDATEINVNODE: Invalid node: Node object-node{"count":number-node{3}, "items":array-node{number-node{12}}} not valid against property 'properties' expected {properties: {count:{...}, items:{...}}} using schema "/schemas/example.json"</error:format-string>
    <error:retryable>false</error:retryable>
    <error:expr/>
    <error:data>
      <error:datum>properties</error:datum>
      <error:datum>object-node{"count":number-node{3}, "items":array-node{number-node{12}}}</error:datum>
      <error:datum>"/schemas/example.json"</error:datum>
      <error:datum>{properties: {count:{...}, items:{...}}}</error:datum>
    </error:data>
    <error:stack>
      <error:frame>
	<error:line>2</error:line>
	<error:column>2</error:column>
	<error:xquery-version>1.0-ml</error:xquery-version>
      </error:frame>
    </error:stack>
  </error:error>
</xdmp:validation-errors>
```

---

## xdmp:json-validate-report-node

Validate a JSON node against a JSON Schema and return an error report.

### Signature

```xquery
xdmp:json-validate-report-node(
  $node as node(),
  $schema as node(),
  $options as xs:string*
) as element(xdmp:validation-errors)
```

### Parameters

**`$node`**
JSON node to be validate-reportd.

**`$schema`**
A JSON schema node use for validatation.

**`$options`**
Validation options. Supported options:
    
    "full"Keep trying to find all the errors. (Default)
    "strict"Stop after the first error.

### Returns

`element(xdmp:validation-errors)`

### Examples

```xquery
xdmp:json-validate-report-node(
     object-node{ "count": 3, "items": array-node{12} }, 
     object-node{
       "properties": object-node{
          "count": object-node{ "type":"integer", "minimum":0 },
          "items": object-node{ "type":"array", "items": object-node{"type":"string", "minLength":1 } }
        }
     })

=> 
<xdmp:validation-errors xmlns:xdmp="http://marklogic.com/xdmp">
<error:error xmlns:error="http://marklogic.com/xdmp/error" xmlns:xsi="http://www.w3.org/2001/XMLSchema-instance">
    <error:code>XDMP-JSVALIDATEINVTYPE</error:code>
    <error:name/>
    <error:xquery-version>1.0-ml</error:xquery-version>
    <error:message>Invalid node type</error:message>
    <error:format-string>XDMP-JSVALIDATEINVTYPE: Invalid node type: Expected node of type text, found number at number-node{12} using schema ""</error:format-string>
    <error:retryable>false</error:retryable>
    <error:expr/>
    <error:data>
      <error:datum>number-node{12}</error:datum>
      <error:datum>""</error:datum>
      <error:datum>text</error:datum>
      <error:datum>number</error:datum>
    </error:data>
    <error:stack>
      <error:frame>
	<error:line>2</error:line>
	<error:column>2</error:column>
	<error:xquery-version>1.0-ml</error:xquery-version>
      </error:frame>
    </error:stack>
  </error:error>
  <error:error xmlns:error="http://marklogic.com/xdmp/error" xmlns:xsi="http://www.w3.org/2001/XMLSchema-instance">
    <error:code>XDMP-JSVALIDATEINVNODE</error:code>
    <error:name/>
    <error:xquery-version>1.0-ml</error:xquery-version>
    <error:message>Invalid node</error:message>
    <error:format-string>XDMP-JSVALIDATEINVNODE: Invalid node: Node number-node{12} not valid against property 'items' expected {type: string, minLength: 1} using schema ""</error:format-string>
    <error:retryable>false</error:retryable>
    <error:expr/>
    <error:data>
      <error:datum>items</error:datum>
      <error:datum>number-node{12}</error:datum>
      <error:datum>""</error:datum>
      <error:datum>{type: string, minLength: 1}</error:datum>
    </error:data>
    <error:stack>
      <error:frame>
	<error:line>2</error:line>
	<error:column>2</error:column>
	<error:xquery-version>1.0-ml</error:xquery-version>
      </error:frame>
    </error:stack>
  </error:error>
  <error:error xmlns:error="http://marklogic.com/xdmp/error" xmlns:xsi="http://www.w3.org/2001/XMLSchema-instance">
    <error:code>XDMP-JSVALIDATEINVNODE</error:code>
    <error:name/>
    <error:xquery-version>1.0-ml</error:xquery-version>
    <error:message>Invalid node</error:message>
    <error:format-string>XDMP-JSVALIDATEINVNODE: Invalid node: Node object-node{"count":number-node{3}, "items":array-node{number-node{12}}} not valid against property 'properties' expected {properties: {count:{...}, items:{...}}} using schema ""</error:format-string>
    <error:retryable>false</error:retryable>
    <error:expr/>
    <error:data>
      <error:datum>properties</error:datum>
      <error:datum>object-node{"count":number-node{3}, "items":array-node{number-node{12}}}</error:datum>
      <error:datum>""</error:datum>
      <error:datum>{properties: {count:{...}, items:{...}}}</error:datum>
    </error:data>
    <error:stack>
      <error:frame>
	<error:line>2</error:line>
	<error:column>2</error:column>
	<error:xquery-version>1.0-ml</error:xquery-version>
      </error:frame>
    </error:stack>
  </error:error>
</xdmp:validation-errors>
```

---

## xdmp:to-json

Constructs a JSON document.

### Signature

```xquery
xdmp:to-json(
  $item as item()*
) as document-node()
```

### Parameters

**`$item`**
A sequence of items from which the JSON document is to be constructed.
    The item sequence from which the JSON document is
    constructed.

### Returns

`document-node()`

### Usage Notes

An object-node() is constructed from a
  json:object, a map:map, or an
  object-node().
  An array-node() is constructed from a
  json:array, a sequence of multiple items, or an
  array-node().
  A null-node() is constructed from an empty sequence or
     an null-node().
  A boolean-node() is constructed from an
  xs:boolean or a boolean-node().
  A number-node() is constructed from an
  xs:integer, a xs:decimal, a
  xs:float, a xs:double, or a
  number-node(). Integers with absolute value greater than
     9007199254740991 are excluded and instead construct text()
     nodes to avoid any loss of precision.
  A text() node is constructed from all other items.
  
      To serialize a JSON node to a string, use xdmp:quote.

### Examples

#### Example 1

```xquery
xdmp:to-json(("a",fn:false()))
=>
["a", false]
```

#### Example 2

```xquery
let $object := json:object()
let $_ := map:put($object,"a",111)
return xdmp:to-json($object)
=>
{"a":111}
```

---

## xdmp:to-json-string

Returns a string representing a JSON
  serialization of a given item sequence.

### Signature

```xquery
xdmp:to-json-string(
  $item as item()*
) as xs:string
```

### Parameters

**`$item`**
The item sequence whose JSON serialization is 
    returned.

### Returns

`xs:string`

### Usage Notes

XML nodes are serialized to JSON strings.
      JSON has no serialization for infinity, not a number, and negative 0,
  therefore if you try and serialize INF, -INF, NaN, or -0 as JSON, an
  exception is thrown.  If you want to represent these values in some way in
  your serialized JSON, then you can catch the exception (with a try/catch, for
  example) and provide your own value for it.
      XQuery maps (map:map types) serialize to JSON name-value
  pairs.

### Examples

#### Example 1

```xquery
xdmp:to-json-string(("a",fn:false()))
   => ["a", false]
```

#### Example 2

```xquery
xdmp:to-json-string(
  xdmp:from-json-string('{ "a":111 }'))
=>
{"a":111}
```

---
