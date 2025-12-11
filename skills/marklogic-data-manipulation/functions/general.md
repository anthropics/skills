# General

109 functions in this category.

## cts:valid-tde-context

Parses path expressions and resolves namespaces using the $map parameter.
 Returns true if the argument is permissible as a context element
 in a TDE template.

### Signature

```xquery
cts:valid-tde-context(
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
cts:valid-tde-context("/foo/bar[@baz = '1']")
  => true
```

#### Example 2

```xquery
xquery version "1.0-ml";
  let $namespaces := map:map()
  let $_ := map:put($namespaces, "ns1", "http://example.org/myns")
  return cts:valid-tde-context("/ns1:foo/ns1:bar[@baz = '1']",$namespaces)
  => true
```

---

## json:check-config

This function checks a json configuration object and returns a report.

### Signature

```xquery
json:check-config(
  $config as map:map
) as element(json:report)*
```

### Parameters

**`$config`**
The configuration object representing the strategy.

### Returns

`element(json:report)*`

### Usage Notes

The supplied configuration object (a map:map) is checked for validity and any errors found returned.

### Examples

```xquery
xquery version "1.0-ml";
import module namespace json="http://marklogic.com/xdmp/json"
 at "/MarkLogic/json/json.xqy";

let $config := json:config("full") => map:with("whitespace", "ignore")
return json:check-config($config)
```

---

## json:config

This function creates a configuration object 
			for a specified strategy.

### Signature

```xquery
json:config(
  $strategy as xs:string
) as map:map
```

### Parameters

**`$strategy`**
The name of 
		    the strategy.  One of basic (simple default JSON  
        conversion, starting from JSON), full (starting from
        XML), or custom.

### Returns

`map:map`

### Usage Notes

Use this function to when you want to use a custom strategy.   
	    Supported strategies are basic, full, 
	    custom.  
	    The basic strategy is used if you supply no 
	    parameters and has no user customizable properties.
	    The following properties are user customizable to configure the 
	    behavior of the transformation.
    full strategy properties
      
        
	  
	    Property
	    Description
	    Default value
	  
	
        
	  
	    json-attributes
	    The member name used to contain attributes.
	    _attributes
	  
	  
	    json-children
	    The member name used to contain the children array.
	    _children
	  
	  
	    whitespace
	    How to handle XML text values that only contain
			    whitespace when converting to JSON. Allowed values:
                "preserve", "ignore". Default: "preserve".
	    empty string
	  
	
      
      custom strategy properties
      
        
	  
	    Property
	    Description
	    Direction
	    Type
	    Default value
	  
	
        
	  array-element-names
	  A list of XML element names which will be 
			  treated as an Array in JSON. These can be 
			  xs:QName or xs:string. 
			  If an xs:string is used then the 
			  default namespace is used to construct the 
			  QName.
	  XML to JSON 
	  (xs:QName | xs:string)*
	  () 
	
        
	  ignore-element-names
	  A list of XML element names which will be 
            ignored when transformed to JSON. These can be 
            xs:QName or xs:string. 
            If an xs:string is used then the 
            default namespace is used to construct the 
            QName.
	  XML to JSON 
	  (xs:QName | xs:string)*
	  () 
	
        
	  ignore-attribute-names
	  A list of XML attribute names which will be 
            ignored when transformed to JSON. These can be 
            xs:QName or xs:string. 
            If an xs:string is used then the 
            default namespace is used to construct the 
            QName.
	  XML to JSON 
	  (xs:QName | xs:string)*
	  () 
	
        
	  text-value
	  When converting from XML to JSON, the JSON property
            name to use for the text value of an element that contains
            both attributes and text. When converting from JSON to XML,
            the JSON property name whose value should become the element
            text value for an element that contains both attributes and
            text.
	  BOTH 
	  xs:string 
	  "_value"
	
        
	  attribute-names
	  A list of JSON names which are converted to 
			  XML attribute. 
	  JSON to XML 
	  xs:string*
	  () 
	
        
	  camel-case
	  A boolean value indicating if camel case 
			  transformation is applied to all element and 
			  attribute names when translating to and from
			  JSON. 
	  BOTH 
	  xs:boolean
	  fn:false()
	
        
	  element-namespace
	  The default namespace for elements.
	  JSON to XML 
	  xs:string
	  () 
	
        
	  element-namespace-prefix
	  The default prefix for elements.
	  JSON to XML 
	  xs:string
	  () 
	
        
	  attribute-namespace
	  The default namespace for attributes.
	  JSON to XML 
	  xs:string
	  () 
	
        
	  attribute-namespace-prefix
	  The default prefix for attributes.
	  JSON to XML 
	  xs:string
	  () 
	
        
	  attribute-prefix
	  If specified then when converting to 
			  JSON attributes are prefixed with this string. 
			  When converting to XML all names starting with 
			  this prefix are converted to attributes with 
			  the prefix removed. 
	  BOTH 
	  xs:string 
	  () 
	
        
	  full-element-names 
	  A list of XML element names which will 
			  be treated as an full expansion in 
			  JSON similar to the full strategy. 
			  These can be xs:QName or 
			  xs:string. If an xs:string 
			  is used then the default namespace is used to 
			  construct the QName. 
	  BOTH 
	   (xs:QName | xs:string)* 
	  () 
	
        
	  json-attributes 
	  The member name used to contain attributes when using the 
				full-element-names expansion. 
	  
	  xs:string
	  "_attributes" 
	
        
	  json-children
	  The member name used to contain the children array when 
               using the full-element-names expansion.
	  
	  xs:string
	  "_children"
	
        
	  whitespace
	  How to handle XML text values that only contain
			    whitespace when converting to JSON. Allowed values:
                "preserve", "ignore". Default: "preserve". 
	   
	  xs:string
	  ""

### Examples

#### Example 1

```xquery
(: sample.xml must be inserted first. 
For reference: 
xdmp:document-insert("/sample.xml", <a><b><attr>d</attr><LABEL>c</LABEL></b></a>) :)

xquery version "1.0-ml";
import module namespace json="http://marklogic.com/xdmp/json"
 at "/MarkLogic/json/json.xqy";

let $c := json:config("full")
return json:transform-to-json( fn:doc("/sample.xml") , $c )

(: The following output is produced: 
{
  "a": {
    "_children": [ { "b": {
          "_children": [
          { "attr": {
                "_children": ["d"] } },
            { "LABEL": {
                "_children": ["c"] } 
            } 
          ]
        }
      }
    ]
  }
} :)
```

#### Example 2

```xquery
xquery version "1.0-ml";
import module namespace json = "http://marklogic.com/xdmp/json"
    at "/MarkLogic/json/json.xqy";

declare variable $doc :=   <a><b attr="d">c</b></a>;
    
let $c := json:config("custom") ,
    $_ := map:put( $c, "array-element-names", (xs:QName("a"),xs:QName("b")) ),
    $_ := map:put( $c, "attribute-names", ("attr" ) ), 
    $_ := map:put( $c, "text-value", "LABEL" ),
    $j := json:transform-to-json($doc ,$c ),
    $x := json:transform-from-json($j,$c) 
return ($j, $x)

(: The JSON property name "LABEL" is used to hold the text value from
    the element <b/>. Without the "text-value" option, the property name
    would be "_value". The query produces the following output: 

{"a":[{"b":[{"attr":"d", "LABEL":"c"}]}]}
<a><b attr="d">c</b></a> :)
```

---

## json:transform-from-json

This function transforms a JSON document to 
		  XML using the default ("basic") strategy.

### Signature

```xquery
json:transform-from-json(
  $json as item(),
  $config as map:map?
) as item()*
```

### Parameters

**`$json`**
The JSON document to transform.
      This is typically an xs:string but also accepts a document, object-node(),
      array-node(), map:map, json:array,element(map:map) ,
      element(json:array) and element(json:object)

**`$config`** *(optional)*
The 
		      configuration object

### Returns

`item()*`

### Usage Notes

The supplied JSON document (as a string, element, 
      object or array) is transformed to XML using the default 
      (basic) strategy and returned as an element.

### Examples

#### Example 1

```xquery
xquery version "1.0-ml";
import module namespace json="http://marklogic.com/xdmp/json"
 at "/MarkLogic/json/json.xqy";
 
 declare variable $j :=  '{
    "first Key":"first value",
    "secondKey":["first item","second item",null,"third item",false],
    "thirdKey":3,
    "fourthKey":{"subKey":"sub value", "boolKey" : true, "empty" : null }
    ,"fifthKey": null,
    "sixthKey" : []
    }'  ;
 json:transform-from-json( $j)
 
(: The following output is produced:

<json type="object" xmlns="http://marklogic.com/xdmp/json/basic">
  <first_20_Key type="string">first value</first_20_Key>
  <secondKey type="array">
    <item type="string">first item</item>
    <item type="string">second item</item>
    <item type="null"/>
    <item type="string">third item</item>
    <item type="boolean">false</item>
  </secondKey>
  <thirdKey type="number">3</thirdKey>
  <fourthKey type="object">
    <subKey type="string">sub value</subKey>
    <boolKey type="boolean">true</boolKey>
    <empty type="null"/>
  </fourthKey>
  <fifthKey type="null"/>
  <sixthKey type="array"/>
</json> :)
```

#### Example 2

```xquery
xquery version "1.0-ml";
import module namespace json="http://marklogic.com/xdmp/json"
 at "/MarkLogic/json/json.xqy";
 
 declare variable $j :=  '{
   "object" : {
    "firstKey":"first value",
    "secondKey":["first item","second item","","third item",false],
    "thirdKey":3,
    "fourthKey":{"subKey":"sub value", "boolKey" : true, "empty" : null }
    ,"fifthKey": null,
    "sixthKey" : []
     }}'  ;

 let $config := json:config("custom") ,
          $cx := map:put( $config, "attribute-names" , ("subKey" , "boolKey" , "empty" ) )
 return 

json:transform-from-json( $j, $config )

(: The following output is produced:
<object>
  <firstKey>first value</firstKey>
  <secondKey>first item</secondKey>
  <secondKey>second item</secondKey>
  <secondKey/>
  <secondKey>third item</secondKey>
  <secondKey>false</secondKey>
  <thirdKey>3</thirdKey>
  <fourthKey subKey="sub value" boolKey="true" empty=""/>
  <fifthKey/>
</object> :)
```

---

## json:transform-to-json

This function transforms an XML document to JSON 
		  using the default ("basic") strategy if none is 
		  supplied.

### Signature

```xquery
json:transform-to-json(
  $node as node(),
  $config as map:map?
) as document-node()?
```

### Parameters

**`$node`**
The node to 
		    transform. The node must be a node that was
		    transformed from JSON  (for example, as the result of a 
		    json:transform-from-json  call with the
		    basic strategy or from JSON
		    that was loaded using the REST API).

**`$config`** *(optional)*
The 
	      configuration object representing the strategy.

### Returns

`document-node()?`

### Usage Notes

The supplied document (element or document node) is transformed to JSON
      using the default ("basic") strategy and returned as a document node containing a
      JSON node (object-node() or array-node()).
      When the default "basic" strategy is used, the XML node
	    must be in the http://marklogic.com/xdmp/json/basic 
	    namespace.  
      Note: Version of MarkLogic prior to 8.0.1 returned an xs:string.
    See 
    https://docs.marklogic.com/guide/relnotes/chap4#id_92312

### Examples

```xquery
(: sample.xml must be inserted first. 
For reference: 
xdmp:document-insert("/sample.xml", <a><b><attr>d</attr><LABEL>c</LABEL></b></a>) :)

xquery version "1.0-ml";
import module namespace json="http://marklogic.com/xdmp/json"
 at "/MarkLogic/json/json.xqy";
 
let $config := json:config("full") => map:with("whitespace", "ignore")
return json:transform-to-json( fn:doc("/sample.xml") , $config )
(: The following output is produced:
{
  "a": {
    "_children": [ { "b": {
          "_children": [
            {
              "attr": {
                "_children": ["d"]}
            },
            {
              "LABEL": {
                "_children": ["c"] }
            }
          ]
        }
      }
    ]
  }
}
:)
```

---

## json:transform-to-json-object

This function transforms an XML document to JSON 
		  and returns an object.

### Signature

```xquery
json:transform-to-json-object(
  $node as node(),
  $config as map:map
) as item()*
```

### Parameters

**`$node`**
The node to 
		    transform. The node must be a node that was
		    transformed from JSON  (for example, as the result of a 
		    json:transform-from-json call with the
		    basic strategy or from JSON
		    that was loaded using the REST API).

**`$config`**
The 
	      configuration object representing the strategy.

### Returns

`item()*`

### Usage Notes

The supplied document (element or document node) is 
	    transformed to JSON using the default (basic) strategy 
	    and returned as an object.  The object will be either a 
	    json:object or json:array.
      When the default "basic" strategy is used, the XML node
	    must be in the http://marklogic.com/xdmp/json/basic 
	    namespace.

### Examples

```xquery
xquery version '1.0-ml';
import module namespace json = "http://marklogic.com/xdmp/json"
    at "/MarkLogic/json/json.xqy";

json:transform-to-json-object(
  <root>
    <key>value</key>
  </root>, 
  json:config("full"))

(: The following JSON Object is produced: 

{
  "root": {
    "_children": [
      {
        "key": { 
        "_children": ["value"]
        }
      }
    ]
  }
} :)
```

---

## json:transform-to-json-xml

This function transforms an XML document to 
		  JSON and returns an xml element.

### Signature

```xquery
json:transform-to-json-xml(
  $node as node(),
  $config as map:map?
) as element()
```

### Parameters

**`$node`**
The node to transform. 
         If the config parameter is not supplied, or it is created from 
         json:config('basic') then the node must be a document 
         conforming to the schema produced by 
         json:transform-from-json when called with the
		 basic.

**`$config`** *(optional)*
If present, the configuration object representing the strategy, 
        otherwise the 'basic' strategy is used.

### Returns

`element()`

### Usage Notes

The supplied document (element or document node) is 
	    transformed to JSON using the default (basic) 
	    strategy and returned as an element.  The element will be 
	    either a json:object or json:array 
	    element.
      When the default "basic" strategy is used, the XML node
	    must be in the http://marklogic.com/xdmp/json/basic 
	    namespace.

### Examples

```xquery
xquery version '1.0-ml';
import module namespace json = "http://marklogic.com/xdmp/json"
    at "/MarkLogic/json/json.xqy";

json:transform-to-json-xml(
  <root>
    <key>value</key>
  </root>, 
  json:config("full"))

(:
The following JSON XML is produced:
<json:object xmlns:json="http://marklogic.com/xdmp/json" 
  xmlns:xsi="http://www.w3.org/2001/XMLSchema-instance" 
  xmlns:xs="http://www.w3.org/2001/XMLSchema">
  <json:entry key="root">
    <json:value>
      <json:object>
	<json:entry key="_children">
	  <json:value>
	    <json:array>
	      <json:value>
		<json:object>
		  <json:entry key="key">
		    <json:value>
		      <json:object>
			<json:entry key="_children">
			  <json:value>
			    <json:array>
			     <json:value xsi:type="xs:string">value
			     </json:value>
			    </json:array>
			  </json:value>
			</json:entry>
		      </json:object>
		    </json:value>
		  </json:entry>
		</json:object>
	      </json:value>
	    </json:array>
	  </json:value>
	</json:entry>
      </json:object>
    </json:value>
  </json:entry>
</json:object> :)
```

---

## map:clear

Clear a map.

### Signature

```xquery
map:clear(
  $map as map:map
) as empty-sequence()
```

### Parameters

**`$map`**
A map.

### Returns

`empty-sequence()`

---

## map:contains

Returns true if the key exists in the map.

### Signature

```xquery
map:contains(
  $map as map:map,
  $key as xs:string
) as xs:boolean
```

### Parameters

**`$map`**
A map.

**`$key`**
A key.

### Returns

`xs:boolean`

---

## map:count

Returns the number of keys used in the map.

### Signature

```xquery
map:count(
  $map as map:map
) as xs:unsignedInt
```

### Parameters

**`$map`**
A map.

### Returns

`xs:unsignedInt`

---

## map:delete

Delete a value from a map.

### Signature

```xquery
map:delete(
  $map as map:map,
  $key as xs:string
) as empty-sequence()
```

### Parameters

**`$map`**
A map.

**`$key`**
A key.

### Returns

`empty-sequence()`

---

## map:entry

Constructs a new map with a single entry consisting of the key and value
  specified as arguments. This is particularly helpful when
  used as part of an argument to map:new().

### Signature

```xquery
map:entry(
  $key as xs:string,
  $value as item()*
) as map:map
```

### Parameters

**`$key`**
The map key.

**`$value`**
The map value.

### Returns

`map:map`

---

## map:get

Get a value from a map.

### Signature

```xquery
map:get(
  $map as map:map,
  $key as xs:string
) as item()*
```

### Parameters

**`$map`**
A map.

**`$key`**
A key.

### Returns

`item()*`

---

## map:keys

Get the keys used in the map.

### Signature

```xquery
map:keys(
  $map as map:map
) as xs:string*
```

### Parameters

**`$map`**
A map.

### Returns

`xs:string*`

---

## map:map

Creates a map.

### Signature

```xquery
map:map(
  $map as element(map:map)?
) as map:map
```

### Parameters

**`$map`** *(optional)*
A serialized map element.

### Returns

`map:map`

---

## map:new

Constructs a new map by combining the keys from the maps given as an argument.
  If a given key exists in more than one argument map, the value from the
  last such map is used.

### Signature

```xquery
map:new(
  $maps as map:map*?
) as map:map
```

### Parameters

**`$maps`** *(optional)*
The argument maps.

### Returns

`map:map`

---

## map:put

Put a value into a map at the given key.

### Signature

```xquery
map:put(
  $map as map:map,
  $key as xs:string,
  $value as item()*
) as empty-sequence()
```

### Parameters

**`$map`**
A map.

**`$key`**
A key. If the key is not unique, it will overwrite the existing key.

**`$value`**
A value.  If the value is the empty sequence, it will remove the
    key from the map.

### Returns

`empty-sequence()`

---

## map:set-javascript-by-ref

If true is specified, sets a map:map to be passed to JavaScript by reference.
  By default, a map:map is passed to JavaScript by value.

### Signature

```xquery
map:set-javascript-by-ref(
  $map as map:map,
  $key as xs:boolean
) as empty-sequence()
```

### Parameters

**`$map`**
A map.

**`$key`**
True or false.

### Returns

`empty-sequence()`

---

## map:with

Updates a map, inserting a value into it at the given key. The map is returned as the result.

### Signature

```xquery
map:with(
  $map as map:map,
  $key as xs:string,
  $value as item()*
) as map:map
```

### Parameters

**`$map`**
A map.

**`$key`**
A key. If the key is not unique, it will overwrite the existing key.

**`$value`**
A value.  If the value is the empty sequence, it will remove the
    key from the map.

### Returns

`map:map`

---

## rest:check-options

This function validates the specified options node.  Validation 
  includes both schema validation and some additional 
  rule-based validation.  An empty sequence indicates valid options and any
  problems are reported via rest:report elements.

### Signature

```xquery
rest:check-options(
  $options as element(rest:options)
) as element(rest:report)?
```

### Parameters

**`$options`**
The options node to be validated.

### Returns

`element(rest:report)?`

---

## rest:check-request

This function takes a request element and returns a report of the 
  problems found. If this function 
  does not return an empty sequence, you have made a mistake and the library will not perform reliably.

### Signature

```xquery
rest:check-request(
  $options as element(rest:request)
) as element(rest:report)?
```

### Parameters

**`$options`**
The options node that defines the request.

### Returns

`element(rest:report)?`

---

## rest:get-raw-query-params

This function extracts all of the query parameters and returns them in a map.
  This does not include the parameters that would be derived from matching the 
  URI string. No error checking or type conversion is performed by this 
  function.  The parameters returned by this function are all strings, as 
  they are not type checked.

### Returns

`map:map`

---

## rest:matching-request

This function returns the request element in 
	  the options node that matches the specified URI. If 
	  you only specify options parameter, all criteria in the request 
	  environment are considered.  If you supply specific criteria, the 
	  filter is less strict, allowing the same options block to be used 
	  for simple url-based rewriting as well as request processing.

### Signature

```xquery
rest:matching-request(
  $options as element(rest:options),
  $match-criteria as xs:string+
) as element(rest:request)?
```

### Parameters

**`$options`**
The options node.

**`$match-criteria`**
Criteria to be used in matching request rules.  By default, all are used.
    Supply one or more of:  "uri", "accept", "conditions","method", "params".

### Returns

`element(rest:request)?`

---

## rest:process-request

This function is used in the endpoint main module to parse the 
	  incoming request against the options. It returns a map that 
	  contains all of the parameters as typed values.  Processing the 
	  request also checks all of the associated conditions and will 
	  raise an error if any condition is not met. 
      If the request is processed successfully, then all of the 
	  conditions have been met and the returned map contains all of 
	  the parameters. If not, an error occurs.

### Signature

```xquery
rest:process-request(
  $request as element(rest:request)
) as map:map
```

### Parameters

**`$request`**
The request to be processed into a map.

### Returns

`map:map`

---

## rest:report-error

This function formats the specified error structure.

### Signature

```xquery
rest:report-error(
  $error as element()
) as element()
```

### Parameters

**`$error`**
The error structure to be formatted.

### Returns

`element()`

---

## rest:rewrite

This function is used in the URL rewriter to map 
		the incoming request to an endpoint. By default, if you 
		supply only options, all aspects of the request environment 
		are used for rewriting.  If you supply specific criteria, the 
		filter is less strict, allowing the same options block to be 
		used for simple url-based rewriting as well as request 
		processing.

### Signature

```xquery
rest:rewrite(
  $options as element(rest:options),
  $match-criteria as xs:string+
) as xs:string?
```

### Parameters

**`$options`**
The options node that defines the request.

**`$match-criteria`**
Criteria to be used in matching request rules for rewriting.  
	    By default, all are used.  Supply one or more of:  
	    "uri", "accept", "conditions","method", "params".

### Returns

`xs:string?`

---

## tde:column-get-permissions

This function returns the permissions granted to a protected column.

### Signature

```xquery
tde:column-get-permissions(
  $schema as xs:string,
  $view as xs:string,
  $column as xs:string
) as item()*
```

### Parameters

**`$schema`**
The name of the schema containing the protected column.

**`$view`**
The name of the view containing the protected column.

**`$column`**
The name of the protected column.

### Returns

`item()*`

### Usage Notes

The tde-admin role is required to call this function.
      
        Note that this is a library function
        that requires that you import the tde.xqy module.
      
      If the specified protected column is not found, a TDE-COLUMNNOTFOUND error is raised.

### Examples

```xquery
xquery version "1.0-ml"; 
import module namespace tde = "http://marklogic.com/xdmp/tde" 
      at "/MarkLogic/tde.xqy";
      
tde:column-get-permissions("schema1", "view1", "column1")
```

---

## tde:column-remove-permissions

This function removes all permissions from a protected column.

### Signature

```xquery
tde:column-remove-permissions(
  $schema as xs:string,
  $view as xs:string,
  $column as xs:string
) as empty-sequence()
```

### Parameters

**`$schema`**
The name of the schema containing the protected column.

**`$view`**
The name of the view containing the protected column.

**`$column`**
The name of the protected column.

### Returns

`empty-sequence()`

### Usage Notes

The tde-admin role is required to call this function.
      
        Note that this is a library function
        that requires that you import the tde.xqy module.
      
        If the specified protected column is not found, a TDE-COLUMNNOTFOUND error is raised.

### Examples

```xquery
xquery version "1.0-ml"; 
import module namespace tde = "http://marklogic.com/xdmp/tde" 
      at "/MarkLogic/tde.xqy";
      
tde:column-remove-permissions("schema1", "view1", "column1")
```

---

## tde:column-set-permissions

This function sets the permissions of a protected column. 
      Any previous permissions on the column are removed.

### Signature

```xquery
tde:column-set-permissions(
  $schema as xs:string,
  $view as xs:string,
  $column as xs:string,
  $permissions as item()
) as empty-sequence()
```

### Parameters

**`$schema`**
The name of the schema containing the protected column.

**`$view`**
The name of the view containing the protected column.

**`$column`**
The name of the protected column.

**`$permissions`**
Roles that are permitted to access the column.

### Returns

`empty-sequence()`

### Usage Notes

The tde-admin role is required to call this function.
      
        Note that this is a library function
        that requires that you import the tde.xqy module.
      
        If the specified protected column is not found, a TDE-COLUMNNOTFOUND error is raised.

### Examples

```xquery
xquery version "1.0-ml"; 
import module namespace tde = "http://marklogic.com/xdmp/tde" 
      at "/MarkLogic/tde.xqy";
      
tde:column-set-permissions("schema1", "view1", "column1",
    <permissions xmlns="http://marklogic.com/xdmp/tde"> 
       <role-name>els-role-1</role-name>  
       <role-name>els-role-2</role-name>
    </permissions>)

(: Sets the permissions of the protected column, column1. :)
```

---

## tde:get-view

This function returns a view's description using a schema and a view name.

### Signature

```xquery
tde:get-view(
  $schema as xs:string,
  $view as xs:string
) as map:map
```

### Parameters

**`$schema`**
The schema name.

**`$view`**
The view name.

### Returns

`map:map`

### Examples

```xquery
xquery version "1.0-ml";

tde:get-view("Medical","Publications");
=>
{
  "view": {
    "id": "14910998190353932762",
    "name": "Publications",
    "schema": "Medical",
    "viewLayout": "identical",
    "columns": [
      {
        "column": {
          "id": "11565230576730337039",
          "name": "ID",
          "scalarType": "long",
          "nullable": 0
        }
      },
      {
        "column": {
          "id": "3103479464860941160",
          "name": "ISSN",
          "scalarType": "string",
          "nullable": 0
        }
      },
      {
        "column": {
          "id": "16141727252897579172",
          "name": "Volume",
          "scalarType": "string",
          "nullable": 0
        }
      }
    ]
  }
}
```

---

## tde:node-data-extract

Extracts row or triple data from a list of specified documents by applying
  extraction templates that are either stored in the schema database or
  provided as a second argument.

### Signature

```xquery
tde:node-data-extract(
  $documents as node()*,
  $templates as element(tde:template)*?
) as map:map
```

### Parameters

**`$documents`**
The sequence of input nodes from which row and triple data is extracted.

**`$templates`** *(optional)*
The tde:templates to use on $documents. If not specified or if an empty
    sequence is provided, stored templates in the schema database are used.

### Returns

`map:map`

### Examples

```xquery
xquery version "1.0-ml";

let $doc1 :=
<Citation>
  <ID>69152893</ID>
  <Article>
    <Journal>
      <ISSN>0123-4567</ISSN>
      <Details>
        <Volume>118-119</Volume>
        <PubDate>
          <Year>1968</Year>
          <Month>Dec</Month>
          <Day>7</Day>
        </PubDate>
      </Details>
    </Journal>
    <Authors>
      <Author>
       <LastName>Doe</LastName>
       <ForeName>John</ForeName>
      </Author>
      <Author>
        <LastName>Smith</LastName>
        <ForeName>Jane</ForeName>
      </Author>
    </Authors>
  </Article>
</Citation>

let $rowtde1:=
<template xmlns="http://marklogic.com/xdmp/tde">
  <context>/Citation/Article/Journal/Details</context>
  <rows>
    <row>
      <schema-name>Medical</schema-name>
      <view-name>Publications</view-name>
      <columns>
        <column>
          <name>ID</name>
          <scalar-type>long</scalar-type>
          <val>../../../ID</val>
        </column>
        <column>
          <name>ISSN</name>
          <scalar-type>string</scalar-type>
          <val>../ISSN</val>
        </column>
        <column>
          <name>Volume</name>
          <scalar-type>string</scalar-type>
          <val>Volume</val>
        </column>
        <column>
          <name>Date</name>
          <scalar-type>string</scalar-type>
          <val>PubDate/Year||'-'||PubDate/Month||'-'||PubDate/Day</val>
        </column>
      </columns>
    </row>
  </rows>
</template>

let $tripletde1:=
<template xmlns="http://marklogic.com/xdmp/tde">
  <context>//Authors/Author</context>
  <vars>
    <var>
      <name>prefix1</name>
      <val>"http://marklogic.com/example/pubs/"</val>
    </var>
  </vars>
  <triples>
    <triple>
      <subject>
        <val>sem:iri($prefix1||'person/'||./ForeName||'_'||./LastName)</val>
        <invalid-values>reject</invalid-values>
      </subject>
      <predicate>
        <val>sem:iri($prefix1||'authored')</val>
      </predicate>
      <object>
        <val>xs:string(../../Journal/ISSN)</val>
      </object>
    </triple>
  </triples>
</template>

return tde:node-data-extract(($doc1),($rowtde1,$tripletde1))

=>

{
  "document1":[
    {
      "row":{
        "schema":"Medical",
        "view":"Publications",
        "data":{
          "rowId":"5616425050360034031:18033860331543907366:2:0",
          "ID":69152893,
          "ISSN":"0123-4567",
          "Volume":"118-119",
          "Date":"1968-Dec-7"
        }
      }
    },
    {
      "triple":{
        "subject":"http://marklogic.com/example/pubs/person/John_Doe",
        "predicate":"http://marklogic.com/example/pubs/authored",
        "object":{
          "datatype":"http://www.w3.org/2001/XMLSchema#string",
          "value":"0123-4567"
        }
      }
    },
    {
      "triple":{
        "subject":"http://marklogic.com/example/pubs/person/Jane_Smith",
        "predicate":"http://marklogic.com/example/pubs/authored",
        "object":{
          "datatype":"http://www.w3.org/2001/XMLSchema#string",
          "value":"0123-4567"
        }
      }
    }
  ]
}
```

---

## tde:template-batch-insert

This function validates and inserts multiple templates, is similar to 
    tde:template-insert
    
    for individual template, throw errors for any invalid template or 
    duplicate template URIs provided by sequence of argument with
    tde:template-info
    .
    
      Before inserting, validates each
      new template against all other new and existing (not in the new URIs list)
      templates with same schema/view-name. Any existing template with the same
      URI in the new URIs list will be ignored and replaced directly even if the
      new template has same URI but different schema/view-name.

### Signature

```xquery
tde:template-batch-insert(
  $template-infos as map:map*
) as empty-sequence()
```

### Parameters

**`$template-infos`**
A sequence of maps that specify the template information 
      (URI, template, permissions, collections) to apply as produced by
      tde:template-info
      .

### Returns

`empty-sequence()`

### Usage Notes

The tde-admin role is required in order to insert templates into the 
    schema database.
    Note that this is a library function
      that requires that you import the tde.xqy module.

### Examples

```xquery
xquery version "1.0-ml"; 
import module "http://marklogic.com/xdmp/tde" at "/MarkLogic/tde.xqy";

let $t1 := 
<template xmlns="http://marklogic.com/xdmp/tde">
  <description>populates patients' data</description>
  <context>/MedlineCitation/Article</context>
  <rows>
    <row>
      <schema-name>Medical</schema-name>
      <view-name>Publications</view-name>
      <columns>
        <column>
          <name>ID</name>
          <scalar-type>long</scalar-type>
          <val>../MedlineID</val>
        </column>
        <column>
          <name>ISSN</name>
          <scalar-type>string</scalar-type>
          <val>Journal/ISSN</val>
        </column>
      </columns>
    </row>
  </rows>
</template>

return tde:template-batch-insert(
         ( tde:template-info("t1.xml",$t1),
           tde:template-info("t2.xml",xdmp:document-get("/temp/t2.xml")),
           tde:template-info("t3.xml",xdmp:document-get("/temp/t3.xml"),
             (xdmp:permission("role1","update"),
              xdmp:permission("role2","read")
             ),
             ("collectionA")
           )
         )
       )

(: Inserts 3 templates as t1.xml, t2.xml, t3.xml files. :)
```

---

## tde:template-info

This function returns a map:map (object[]) containing individual template information used for
    inserting templates with tde:template-batch-insert(). Permissions and collections
    are optional. If no permissions specified, xdmp:default-permissions() is the default.

### Signature

```xquery
tde:template-info(
  $uri as xs:string,
  $root as node(),
  $permissions as element(sec:permission)*?,
  $collections as xs:string*?
) as map:map
```

### Parameters

**`$uri`**
The URI of the template document to be inserted.

**`$root`**
The template document.  The template document can be in either
      JSON or XML format.

**`$permissions`** *(optional)*
Any permissions to set on the template document.

**`$collections`** *(optional)*
One or more collections in which to insert the template document.

### Returns

`map:map`

### Usage Notes

The tde-admin role is required in order to insert a template into the 
    schema database.
    
      Note that this is a library function
      that requires that you import the tde.xqy module.

### Examples

```xquery
xquery version "1.0-ml";
import module "http://marklogic.com/xdmp/tde" at "/MarkLogic/tde.xqy";
let $t1 :=
<template xmlns="http://marklogic.com/xdmp/tde">
  ...
</template>
return
  tde:template-info("t1.xml", $t1),
  (: or with permissions and collections
    tde:template-info("t1.xml",$t1,(xdmp:permission("role1","update")),("collectionA"))
  :)

=> 
<map:map xmlns:map="http://marklogic.com/xdmp/map" xmlns:xsi="http://www.w3.org/2001/XMLSchema-instance" xmlns:xs="http://www.w3.org/2001/XMLSchema">
 <map:entry key="uri"><map:value xsi:type="xs:string">t1.xml</map:value></map:entry>
 <map:entry key="template"><map:value>
   <template xmlns="http://marklogic.com/xdmp/tde">
    ...
   </template></map:value></map:entry>
</map:map>
```

---

## tde:template-insert

This function validates the template, inserts the template as a document into 
    the tde collection of the schema database (if executed on the content database) 
    with the default permissions, and reindexes the database.  
    
    Note that, when a template is inserted, only those document fragments affected 
    by the template are re-indexed.
 For more information, see Validating and Inserting a Template in the  Application Developer's Guide.

### Signature

```xquery
tde:template-insert(
  $uri as xs:string,
  $root as node(),
  $permissions as element(sec:permission)*?,
  $collections as xs:string*?
) as empty-sequence()
```

### Parameters

**`$uri`**
The URI of the template document to be inserted.

**`$root`**
The template document.  The template document can be in either
      JSON or XML format.

**`$permissions`** *(optional)*
Any permissions to set on the template document.

**`$collections`** *(optional)*
One or more collections in which to insert the template document.

### Returns

`empty-sequence()`

### Usage Notes

The tde-admin role is required in order to insert a template into the 
   schema database.
   
   Note that this is a library function
   that requires that you import the tde.xqy module.

### Examples

```xquery
xquery version "1.0-ml"; 
import module namespace tde = "http://marklogic.com/xdmp/tde" 
        at "/MarkLogic/tde.xqy";

let $template := 
<template xmlns="http://marklogic.com/xdmp/tde">
  <description>populates patients' data</description>
  <context>/MedlineCitation/Article</context>
  <rows>
    <row>
      <schema-name>Medical</schema-name>
      <view-name>Publications</view-name>
      <columns>
        <column>
          <name>ID</name>
          <scalar-type>long</scalar-type>
          <val>../MedlineID</val>
        </column>
        <column>
          <name>ISSN</name>
          <scalar-type>string</scalar-type>
          <val>Journal/ISSN</val>
        </column>
      </columns>
    </row>
  </rows>
</template>

return tde:template-insert("Template.xml", $template)

(: Inserts the template as the Template.xml file. :)
```

---

## tde:validate

In addition to 
  xdmp:validate
  
  that can be used for validating against the extraction template schema.
  
  The recommended workflow for users is to validate an extraction template
  before inserting it into the schema database. Unless you use the
    
   tde:template-insert function, 
  Ill-formed templates are not validated or rejected at document insertion time.
    
  For more information on extraction templates, 
 see Template Driven Extraction (TDE) in the  Application Developer's Guide.

### Signature

```xquery
tde:validate(
  $templates as element(tde:template)*,
  $excludeTemplateURIs as xs:string*?
) as map:map
```

### Parameters

**`$templates`**
The templates to validate.

**`$excludeTemplateURIs`** *(optional)*
A sequence of URIs for stored templates to ignore during the validation.
    When a template is being updated, users can exclude a previous version
    of the template that might conflict with the version passed to tde:validate.

### Returns

`map:map`

### Usage Notes

The tde:validate
  
  function enables users to do the following:
    
	  Check the template structure and format.
	  Validate the XQuery val expressions.
	  Check if the context expressions are legal.
	  Validate against stored templates (for view declaration consistency and
    other features).

### Examples

```xquery
xquery version "1.0-ml";

let $t1:=
<template xmlns="http://marklogic.com/xdmp/tde">
  <context>/Citation/Article/Journal/Details</context>
  <rows>
    <row>
      <schema-name>Medical</schema-name>
      <view-name>Publications</view-name>
      <columns>
        <column>
          <name>ID</name>
          <scalar-type>BAD_SCALAR_TYPE</scalar-type>
          <val>../../../ID</val></column>
      </columns>
    </row>
  </rows>
</template>

return tde:validate(($t1),("previous_version_of_t1.xml"))

=>

<map:map xmlns:map="http://marklogic.com/xdmp/map" xmlns:xsi="http://www.w3.org/2001/XMLSchema-instance" xmlns:xs="http://www.w3.org/2001/XMLSchema">
  <map:entry key="valid">
    <map:value xsi:type="xs:boolean">false</map:value>
  </map:entry>
  <map:entry key="error">
    <map:value xsi:type="xs:string">TDE-INVALIDTEMPLATENODE</map:value>
  </map:entry>
  <map:entry key="message">
    <map:value xsi:type="xs:string">TDE-INVALIDTEMPLATENODE: Invalid extraction template node: /tde:template/tde:rows/tde:row/tde:columns/tde:column/tde:scalar-type</map:value>
  </map:entry>
</map:map>
```

---

## view:add-column

This function adds column specifications to the current set of column specifications on the named 
  view in the named schema.

### Signature

```xquery
view:add-column(
  $schema-name as xs:string,
  $view-name as xs:string,
  $column as element(view:column)
) as empty-sequence()
```

### Parameters

**`$schema-name`**
The name of the schema specification containing the view.

**`$view-name`**
The name of the view to which the column specifications are to be added.

**`$column`**
The column specifications to be added to the view.

### Returns

`empty-sequence()`

### Examples

```xquery
xquery version "1.0-ml"; 
 
  import module namespace view = "http://marklogic.com/xdmp/view" 
      at "/MarkLogic/views.xqy";
 
  view:add-column("main", "songs",
      (view:column("author", cts:element-reference(xs:QName("AUTHOR")))) )

  (: Adds an 'author' column to the 'songs' view in the 'main' schema. :)
```

---

## view:add-field

This function adds a field to the named view.

### Signature

```xquery
view:add-field(
  $schema-name as xs:string,
  $view-name as xs:string,
  $field as element(view:field)
) as empty-sequence()
```

### Parameters

**`$schema-name`**
The name of the schema.

**`$view-name`**
The name of the view.

**`$field`**
The field element to be added to the view.

### Returns

`empty-sequence()`

### Examples

```xquery
xquery version "1.0-ml"; 
 
import module namespace view = "http://marklogic.com/xdmp/views" 
      at "/MarkLogic/views.xqy";
 
view:add-field("main", "employees", view:field("Employee"))

(: Adds the "Employee" field to the "employees" view. :)
```

---

## view:add-permissions

This function adds permissions to those already set for the named view in the 
  named schema specification.

### Signature

```xquery
view:add-permissions(
  $schema-name as xs:string,
  $view-name as xs:string,
  $permissions as item()*
) as empty-sequence()
```

### Parameters

**`$schema-name`**
The name of the schema specification containing the view.

**`$view-name`**
The name of the view to which the permissions are to be added.

**`$permissions`**
The permissions to be added to the view.
	    When run in an XQuery context, the permissions are a sequence of
	    XML elements (sec:permission). When importing this module into 
	    a Server-Side JavaScript context, the permissions are an array
	    of Objects.

### Returns

`empty-sequence()`

### Examples

```xquery
xquery version "1.0-ml"; 
 
  import module namespace view = "http://marklogic.com/xdmp/view" 
      at "/MarkLogic/views.xqy";
 
  view:add-permissions("main", "songs", (xdmp:permission("test-user", "read"),
                                         xdmp:permission("test-user", "update")))

  (: Enables users with the test-user role to read and update the 'main' schema. :)
```

---

## view:collection

This function return the URI of the protected collection holding all the views.

### Returns

`xs:string`

### Examples

```xquery
xquery version "1.0-ml"; 
 
  import module namespace view = "http://marklogic.com/xdmp/view" 
      at "/MarkLogic/views.xqy";

  view:collection()
 
  (: Returns the URI of the protected collection holding all of the views. :)
```

---

## view:collection-view-scope

This function constructs a new collection-style view scope specification.
    
 For details on view scoping, see Defining View Scope in the SQL Data Modeling Guide.

### Signature

```xquery
view:collection-view-scope(
  $collection as xs:string
) as element(*, view:view-scope)
```

### Parameters

**`$collection`**
The name of the collection to define the view scope.

### Returns

`element(*, view:view-scope)`

### Examples

```xquery
xquery version "1.0-ml"; 
 
  import module namespace view = "http://marklogic.com/xdmp/view" 
      at "/MarkLogic/views.xqy";
 
  view:collection-view-scope("http://marklogic.com/xdmp/view/songs")

  (: Returns a collection-style view scope specification. :)
```

---

## view:column

This function constructs a new column specification.

### Signature

```xquery
view:column(
  $name as xs:string,
  $range-index as cts:reference
) as element(view:column)
```

### Parameters

**`$name`**
The name of the column specification.

**`$range-index`**
The range index for the column.

### Returns

`element(view:column)`

### Examples

```xquery
xquery version "1.0-ml"; 
 
  import module namespace view = "http://marklogic.com/xdmp/view" 
      at "/MarkLogic/views.xqy";

  view:column("title", cts:element-reference(xs:QName("TITLE")))
 
  (: Constructs a column, named 'title', over an element range index, named 'TITLE'. :)
```

---

## view:columns

This function returns the sequence of column specifications set in the named 
  view in the named schema.

### Signature

```xquery
view:columns(
  $schema-name as xs:string,
  $view-name as xs:string
) as element(view:column)*
```

### Parameters

**`$schema-name`**
The name of the schema specification containing the view.

**`$view-name`**
The name of the view containing the column specifications.

### Returns

`element(view:column)*`

### Examples

```xquery
xquery version "1.0-ml"; 
 
  import module namespace view = "http://marklogic.com/xdmp/view" 
      at "/MarkLogic/views.xqy";
 
  view:columns("main", "songs")

  (: Returns the columns set in the 'songs' view in the 'main' schema. :)
```

---

## view:create

This function creates a new view in the specified schema specification.  The id of the view is returned.
  The view is checked for validity.
   
    Prior to executing this function, you must create a range index for each column 
    in your view.  For details on element range indexes, see 
 Range Indexes and Lexicons in the Administrator's Guide.

### Signature

```xquery
view:create(
  $schema-name as xs:string,
  $name as xs:string,
  $scope as element(*,view:view-scope),
  $columns as element(view:column)*,
  $fields as element(view:field)*,
  $permissions as item()*
) as xs:unsignedLong
```

### Parameters

**`$schema-name`**
The name of the schema specification in which the view is created.

**`$name`**
The name of the view.  The view name must be unique in the context of the schema in which it 
    is created. A valid view name is a single word that starts with an alpha character. The view
    name may contain numeric characters, but cannot contain punctuation or special characters.

**`$scope`**
The scope of the view used to constrain the subset of the database to which the view applies. 
    The scope can either limit rows in the view to documents with a specific element 
    (localname + namespace) or to documents in a particular collection.  Use the 
    view:element-view-scope function to
    set the scope to an element or the
    view:collection-view-scope function to
    set the scope to a collection.
    
 For details on view scoping, see Defining View Scope in the SQL Data Modeling Guide.

**`$columns`**
A sequence of view columns. Each column has a name and a range index reference.

**`$fields`**
A sequence of view fields. Each field has a name and a field reference.

**`$permissions`**
The permissions required to access this view.
	    When run in an XQuery context, the permissions are a sequence of
	    XML elements (sec:permission). When importing this module into 
	    a Server-Side JavaScript context, the permissions are an array
	    of Objects.

### Returns

`xs:unsignedLong`

### Examples

```xquery
xquery version "1.0-ml"; 
 
  import module namespace view = "http://marklogic.com/xdmp/view" 
      at "/MarkLogic/views.xqy";

  view:create(
      "main",
      "songs",
      view:element-view-scope(xs:QName("SONG")),
      ( view:column("uri", cts:uri-reference()), 
        view:column("title", cts:element-reference(xs:QName("TITLE"))),
        view:column("album", cts:element-reference(xs:QName("ALBUM"), ("nullable"))),
        view:column("year", cts:element-reference(xs:QName("YEAR"))) ),
      (),
      () )

  (: Creates a view, named 'songs', of the 'main' schema that contains four columns, 
     with a scope on the element, 'SONG'. :)
```

---

## view:element-view-scope

This function constructs a new element-style view scope specification.
    
 For details on view scoping, see Defining View Scope in the SQL Data Modeling Guide.

### Signature

```xquery
view:element-view-scope(
  $localname as xs:QName
) as element(*, view:view-scope)
```

### Parameters

**`$localname`**
The name of the element on which to define the view scope.

### Returns

`element(*, view:view-scope)`

### Examples

```xquery
xquery version "1.0-ml"; 
 
  import module namespace view = "http://marklogic.com/xdmp/view" 
      at "/MarkLogic/views.xqy";
 
  view:element-view-scope(xs:QName("SONG"))

  (: Returns the view scope specification for the element, 'SONG'. :)
```

---

## view:field

This function constructs a new element-style field specification for the named field.

### Signature

```xquery
view:field(
  $name as xs:string
) as element(view:field)
```

### Parameters

**`$name`**
The name of the field.

### Returns

`element(view:field)`

### Examples

```xquery
xquery version "1.0-ml"; 
 
import module namespace view = "http://marklogic.com/xdmp/views" 
      at "/MarkLogic/views.xqy";
 
view:field("Employee")

(: Constructs and element field specification for the "Employee" field. :)
```

---

## view:fields

This function returns the fields set on the named view.

### Signature

```xquery
view:fields(
  $schema-name as xs:string,
  $view-name as xs:string
) as element(view:field)*
```

### Parameters

**`$schema-name`**
The name of the schema.

**`$view-name`**
The name of the view.

### Returns

`element(view:field)*`

### Examples

```xquery
xquery version "1.0-ml"; 
 
import module namespace view = "http://marklogic.com/xdmp/views" 
      at "/MarkLogic/views.xqy";
 
view:fields("main", "employees") 

(: Returns the fields set on the "employees" view. :)
```

---

## view:get

This function returns the named view from the named schema specification.

### Signature

```xquery
view:get(
  $schema-name as xs:string,
  $view-name as xs:string
) as element(view:view)
```

### Parameters

**`$schema-name`**
The name of the schema containing the view.

**`$view-name`**
The name of the view.

### Returns

`element(view:view)`

### Examples

```xquery
xquery version "1.0-ml"; 
 
  import module namespace view = "http://marklogic.com/xdmp/view" 
      at "/MarkLogic/views.xqy";

  view:get("main", "songs")

  (: Returns the 'songs' view in the 'main' schema. :)
```

---

## view:get-bindings

This function generates a binding map suitable for use with 
  cts:parse from the named view.

### Signature

```xquery
view:get-bindings(
  $schema-name as xs:string,
  $view-name as xs:string
) as map:map
```

### Parameters

**`$schema-name`**
The name of the schema.

**`$view-name`**
The name of the view.

### Returns

`map:map`

### Examples

```xquery
xquery version "1.0-ml"; 
 
import module namespace view = "http://marklogic.com/xdmp/views" 
      at "/MarkLogic/views.xqy";
 
view:get-bindings("main", "employees")

(: Returns binging map from the "employees" view. :)
```

---

## view:get-by-id

This function returns the view with the specified id.

### Signature

```xquery
view:get-by-id(
  $view-id as xs:unsignedLong
) as element(view:view)
```

### Parameters

**`$view-id`**
The id of the view to be returned.

### Returns

`element(view:view)`

### Examples

```xquery
xquery version "1.0-ml"; 
 
  import module namespace view = "http://marklogic.com/xdmp/view" 
      at "/MarkLogic/views.xqy";

  view:get-by-id(5423110979916486998)
 
  (: Return the view with the specified id. :)
```

---

## view:get-column

This function returns the named column specification set in the named 
  view in the named schema.

### Signature

```xquery
view:get-column(
  $schema-name as xs:string,
  $view-name as xs:string,
  $column-name as xs:string
) as element(view:column)
```

### Parameters

**`$schema-name`**
The name of the schema specification containing the view.

**`$view-name`**
The name of the view containing the column specification.

**`$column-name`**
The name of the column specification to be returned.

### Returns

`element(view:column)`

### Examples

```xquery
xquery version "1.0-ml"; 
 
  import module namespace view = "http://marklogic.com/xdmp/view" 
      at "/MarkLogic/views.xqy";

  view:get-column("main", "songs", "title") 

  (: Returns the 'title' column from the 'songs' view in the 'main' schema. :)
```

---

## view:get-field

This function returns the element specification for the named field.

### Signature

```xquery
view:get-field(
  $schema-name as xs:string,
  $view-name as xs:string,
  $field-name as xs:string
) as element(view:field)
```

### Parameters

**`$schema-name`**
The name of the schema.

**`$view-name`**
The name of the view.

**`$field-name`**
The name of the field.

### Returns

`element(view:field)`

### Examples

```xquery
xquery version "1.0-ml"; 
 
import module namespace view = "http://marklogic.com/xdmp/views" 
      at "/MarkLogic/views.xqy";

view:get-field("main", "employees",  "Employee") 

(: Returns the element specification for the "Employee" field. :)
```

---

## view:get-permissions

This function returns the permissions set on the specified view.

### Signature

```xquery
view:get-permissions(
  $schema-name as xs:string,
  $view-name as xs:string
) as element(sec:permission)*
```

### Parameters

**`$schema-name`**
The name of the schema that contains the view.

**`$view-name`**
The name of the view.

### Returns

`element(sec:permission)*`

### Examples

```xquery
xquery version "1.0-ml"; 
 
  import module namespace view = "http://marklogic.com/xdmp/view" 
      at "/MarkLogic/views.xqy";
 
  view:get-permissions("main", "employees")

  (: Returns the permissions set on the 'employees' view in the 'main' schema. :)
```

---

## view:get-view-scope

This function returns the scope of the named view in the
  named schema.

### Signature

```xquery
view:get-view-scope(
  $schema-name as xs:string,
  $view-name as xs:string
) as element(*, view:view-scope)
```

### Parameters

**`$schema-name`**
The name of the schema specification containing the view.

**`$view-name`**
The name of the view from which to return the scope.

### Returns

`element(*, view:view-scope)`

### Examples

```xquery
xquery version "1.0-ml"; 
 
  import module namespace view = "http://marklogic.com/xdmp/view" 
      at "/MarkLogic/views.xqy";
 
  view:get-view-scope("main", "songs")
 
  (: Returns the scope of the 'songs' view in the 'main' schema. :)
```

---

## view:remove

This function removes the named view from the named schema specification.

### Signature

```xquery
view:remove(
  $schema-name as xs:string,
  $view-name as xs:string
) as empty-sequence()
```

### Parameters

**`$schema-name`**
The name of the schema containing the view to be removed.

**`$view-name`**
The name of the view to be removed.

### Returns

`empty-sequence()`

### Examples

```xquery
xquery version "1.0-ml"; 
 
  import module namespace view = "http://marklogic.com/xdmp/view" 
      at "/MarkLogic/views.xqy";
 
  view:remove("main", "songs")

  (: Removes the 'songs' view from the 'main' schema. :)
```

---

## view:remove-by-id

This function removes the view with the specified id.

### Signature

```xquery
view:remove-by-id(
  $view-id as xs:unsignedLong
) as empty-sequence()
```

### Parameters

**`$view-id`**
The id of the view to be removed.

### Returns

`empty-sequence()`

### Examples

```xquery
xquery version "1.0-ml"; 
 
  import module namespace view = "http://marklogic.com/xdmp/view" 
      at "/MarkLogic/views.xqy";
 
  view:remove-by-id(5423110979916486998)

  (: Remove the view with the specified id. :)
```

---

## view:remove-column

This function removes a column specification from the named 
  view in the named schema.

### Signature

```xquery
view:remove-column(
  $schema-name as xs:string,
  $view-name as xs:string,
  $column-name as xs:string
) as empty-sequence()
```

### Parameters

**`$schema-name`**
The name of the schema specification containing the view.

**`$view-name`**
The name of the view from which the column specification is to be removed.

**`$column-name`**
The name of the column specification to be removed from the view.

### Returns

`empty-sequence()`

### Examples

```xquery
xquery version "1.0-ml"; 
 
  import module namespace view = "http://marklogic.com/xdmp/view" 
      at "/MarkLogic/views.xqy";
 
  view:remove-column("main", "songs", "year")  

  (: Removes the 'year' column from the 'songs' view in the 'main' schema. :)
```

---

## view:remove-field

This function removes a field from the named view.

### Signature

```xquery
view:remove-field(
  $schema-name as xs:string,
  $view-name as xs:string,
  $field-name as xs:string
) as empty-sequence()
```

### Parameters

**`$schema-name`**
The name of the schema.

**`$view-name`**
The name of the view.

**`$field-name`**
The name of the field to be removed.

### Returns

`empty-sequence()`

### Examples

```xquery
xquery version "1.0-ml"; 
 
import module namespace view = "http://marklogic.com/xdmp/views" 
      at "/MarkLogic/views.xqy";
 
view:remove-field("main", "employees", "Employee")

(: Removes the "Employee" field from the "employees" view. :)
```

---

## view:remove-permissions

This function removes permissions from those set for the named view in the 
  named schema specification.

### Signature

```xquery
view:remove-permissions(
  $schema-name as xs:string,
  $view-name as xs:string,
  $permissions as item()*
) as empty-sequence()
```

### Parameters

**`$schema-name`**
The name of the schema specification containing the view.

**`$view-name`**
The name of the view from which the permissions are to be removed.

**`$permissions`**
The permissions to be removed from the view.
	    When run in an XQuery context, the permissions are a sequence of
	    XML elements (sec:permission). When importing this module into 
	    a Server-Side JavaScript context, the permissions are an array
	    of Objects.

### Returns

`empty-sequence()`

### Examples

```xquery
xquery version "1.0-ml"; 
 
  import module namespace view = "http://marklogic.com/xdmp/view" 
      at "/MarkLogic/views.xqy";
 
  view:remove-permissions("main", "songs", (xdmp:permission("test-user", "read"),
                                            xdmp:permission("test-user", "update")))

  (: Disables users with the test-user role from reading and updating the 
     'songs' view in the 'main' schema. :)
```

---

## view:schema-add-permissions

This function adds permissions to the specified schema specification.

### Signature

```xquery
view:schema-add-permissions(
  $schema-name as xs:string,
  $permissions as item()*
) as empty-sequence()
```

### Parameters

**`$schema-name`**
The name of the schema specification.

**`$permissions`**
The permissions to add to the schema specification.
	    When run in an XQuery context, the permissions are a sequence of
	    XML elements (sec:permission). When importing this module into 
	    a Server-Side JavaScript context, the permissions are an array
	    of Objects.

### Returns

`empty-sequence()`

### Examples

```xquery
xquery version "1.0-ml"; 
 
  import module namespace view = "http://marklogic.com/xdmp/view" 
      at "/MarkLogic/views.xqy";

  view:schema-add-permissions("main", (xdmp:permission("test-user", "read"),
                                       xdmp:permission("test-user", "update")))

  (: Enables users with the test-user role to read and update the 'main' schema. :)
```

---

## view:schema-create

This function creates a new relational schema in the Schema database.  
	The schema id is returned.  Every SQL deployment must include a default
	schema, called "main," as shown in the example below.
    
    This schema is typically created for Range Views.  However, such a schema can also
    contain Template Views. Note that Range Views cannot be created in a schema
    created by a Template View.

### Signature

```xquery
view:schema-create(
  $schema-name as xs:string,
  $permissions as item()*
) as xs:unsignedLong
```

### Parameters

**`$schema-name`**
The schema name.
    The schema name must be unique. A valid schema name is a single word that starts with an 
    alpha character. The schema name may contain numeric characters, but cannot contain 
    punctuation or special characters.

**`$permissions`**
Permissions that control access to the schema.  
	    If no permissions are specified, the default permissions are used.
	    When run in an XQuery context, the permissions are a sequence of
	    XML elements (sec:permission). When importing this module into 
	    a Server-Side JavaScript context, the permissions are an array
	    of Objects.

### Returns

`xs:unsignedLong`

### Examples

```xquery
xquery version "1.0-ml"; 
 
  import module namespace view = "http://marklogic.com/xdmp/view" 
      at "/MarkLogic/views.xqy";
 
  view:schema-create("main", ())

  (: Create a new schema, named 'main', using the default permissions. :)
```

---

## view:schema-get

This function returns the named schema specification document.

### Signature

```xquery
view:schema-get(
  $schema-name as xs:string
) as element(view:schema)
```

### Parameters

**`$schema-name`**
The name of the schema specification to return.

### Returns

`element(view:schema)`

### Examples

```xquery
xquery version "1.0-ml"; 
 
  import module namespace view = "http://marklogic.com/xdmp/view" 
      at "/MarkLogic/views.xqy";

  view:schema-get("main")

  (: Return the schema, named 'main'. :)
```

---

## view:schema-get-permissions

This function returns the permissions set on the specified schema.

### Signature

```xquery
view:schema-get-permissions(
  $schema-name as xs:string
) as element(sec:permission)*
```

### Parameters

**`$schema-name`**
The name of the schema.

### Returns

`element(sec:permission)*`

---

## view:schema-remove

This function removes the specified schema. 
  Removing a schema removes all the views that are part of that schema.

### Signature

```xquery
view:schema-remove(
  $schema-name as xs:string
) as empty-sequence()
```

### Parameters

**`$schema-name`**
The name of the schema to be removed.

### Returns

`empty-sequence()`

### Examples

```xquery
xquery version "1.0-ml"; 
 
  import module namespace view = "http://marklogic.com/xdmp/view" 
      at "/MarkLogic/views.xqy";
 
  view:schema-remove("main")

  (: Remove the schema, named 'main'. :)
```

---

## view:schema-remove-permissions

This function removes permissions from the specified schema specification.

### Signature

```xquery
view:schema-remove-permissions(
  $schema-name as xs:string,
  $permissions as item()*
) as empty-sequence()
```

### Parameters

**`$schema-name`**
The name of the schema specification.

**`$permissions`**
The permissions to remove from the schema specification.
	    When run in an XQuery context, the permissions are a sequence of
	    XML elements (sec:permission). When importing this module into 
	    a Server-Side JavaScript context, the permissions are an array
	    of Objects.

### Returns

`empty-sequence()`

### Examples

```xquery
xquery version "1.0-ml"; 
 
  import module namespace view = "http://marklogic.com/xdmp/view" 
      at "/MarkLogic/views.xqy";

  view:schema-remove-permissions("main", (xdmp:permission("test-user", "read"),
                                          xdmp:permission("test-user", "update")))

  (: Disables users with the test-user role from reading and updating the 'main' schema. :)
```

---

## view:schema-set-permissions

This function sets permissions on the specified schema specification. 
  Any existing permissions for the schema and removed.

### Signature

```xquery
view:schema-set-permissions(
  $schema-name as xs:string,
  $permissions as item()*
) as empty-sequence()
```

### Parameters

**`$schema-name`**
The name of the schema specification.

**`$permissions`**
The permissions to set on the schema specification.
	    When run in an XQuery context, the permissions are a sequence of
	    XML elements (sec:permission). When importing this module into 
	    a Server-Side JavaScript context, the permissions are an array
	    of Objects.

### Returns

`empty-sequence()`

### Examples

```xquery
xquery version "1.0-ml"; 
 
  import module namespace view = "http://marklogic.com/xdmp/view" 
      at "/MarkLogic/views.xqy";

  view:schema-set-permissions("main", (xdmp:permission("app-user", "read"),
                                       xdmp:permission("app-user", "update")))

  (: Enables only users with the app-user role to read and update the 'main' schema. :)
```

---

## view:schemas

This function returns all of the schema specifications.

### Returns

`element(view:schema)*`

### Examples

```xquery
xquery version "1.0-ml"; 
 
  import module namespace view = "http://marklogic.com/xdmp/view" 
      at "/MarkLogic/views.xqy";
 
  view:schemas()

  (: Returns all of the schema specifications. :)
```

---

## view:set-columns

This function replaces the current set of column specifications on the named 
  view in the named schema with a new set of columns.

### Signature

```xquery
view:set-columns(
  $schema-name as xs:string,
  $view-name as xs:string,
  $columns as element(view:column)*
) as empty-sequence()
```

### Parameters

**`$schema-name`**
The name of the schema specification containing the view.

**`$view-name`**
The name of the view containing the column specifications to be reset.

**`$columns`**
A sequence of column specifications for the view.

### Returns

`empty-sequence()`

### Examples

```xquery
xquery version "1.0-ml"; 
 
  import module namespace view = "http://marklogic.com/xdmp/view" 
      at "/MarkLogic/views.xqy";
 
  view:set-columns("main", "songs",
    ( view:column("uri", cts:uri-reference()), 
      view:column("title", cts:element-reference(xs:QName("TITLE"))),
      view:column("author", cts:element-reference(xs:QName("AUTHOR"))),
      view:column("album", cts:element-reference(xs:QName("ALBUM"), ("nullable"))),
      view:column("year", cts:element-reference(xs:QName("YEAR"))) ) )
 
  (: Sets five columns in the 'songs' view in the 'main' schema. :)
```

---

## view:set-fields

This function sets the specified fields on the specified view.  Any existing fields are 
  replaced or removed.

### Signature

```xquery
view:set-fields(
  $schema-name as xs:string,
  $view-name as xs:string,
  $fields as element(view:field)*
) as empty-sequence()
```

### Parameters

**`$schema-name`**
The name of the schema.

**`$view-name`**
The name of the view.

**`$fields`**
The sequence of field elements to be set on the view.

### Returns

`empty-sequence()`

### Examples

```xquery
xquery version "1.0-ml"; 
 
import module namespace view = "http://marklogic.com/xdmp/views" 
      at "/MarkLogic/views.xqy";
 
view:set-fields("main",
                "employees", 
                (view:field("Employee"), view:field("EmployeeID")) )

(: Sets the "Employee" and "EmployeeID" fields on the "employees" view. :)
```

---

## view:set-name

This function renames the named view in the named schema specification.

### Signature

```xquery
view:set-name(
  $schema-name as xs:string,
  $view-name as xs:string,
  $new-name as xs:string
) as empty-sequence()
```

### Parameters

**`$schema-name`**
The name of the schema specification containing the view.

**`$view-name`**
The current name of the view to be renamed.

**`$new-name`**
The new name of the view.  The view name must be unique in the context of the schema in which 
    it resides. A valid view name is a single word that starts with an alpha character. The view 
    name may contain numeric characters, but cannot contain punctuation or special characters.

### Returns

`empty-sequence()`

### Examples

```xquery
xquery version "1.0-ml"; 
 
  import module namespace view = "http://marklogic.com/xdmp/view" 
      at "/MarkLogic/views.xqy";
 
  view:set-name("main", "songs", "tunes")

  (: Renames the 'songs' view in the 'main' schema to 'tunes'. :)
```

---

## view:set-permissions

This function sets the permissions for the named view in the 
  named schema specification.  Any existing permissions for the view and
  removed.

### Signature

```xquery
view:set-permissions(
  $schema-name as xs:string,
  $view-name as xs:string,
  $permissions as item()*
) as empty-sequence()
```

### Parameters

**`$schema-name`**
The name of the schema specification containing the view.

**`$view-name`**
The name of the view for which the permissions are to be set.

**`$permissions`**
The permissions for the view.
	    When run in an XQuery context, the permissions are a sequence of
	    XML elements (sec:permission). When importing this module into 
	    a Server-Side JavaScript context, the permissions are an array
	    of Objects.

### Returns

`empty-sequence()`

### Examples

```xquery
xquery version "1.0-ml"; 
 
  import module namespace view = "http://marklogic.com/xdmp/view" 
      at "/MarkLogic/views.xqy";

  view:set-permissions("main", "songs", (xdmp:permission("app-user", "read"),
                                         xdmp:permission("app-user", "update")))

  (: Enables only users with the app-user role to read and update the 'songs' view
     in the 'main' schema. :)
```

---

## view:set-view-scope

This function sets the scope of the named view in the named 
  schema specification.

### Signature

```xquery
view:set-view-scope(
  $schema-name as xs:string,
  $view-name as xs:string,
  $scope as element(*,view:view-scope)
) as empty-sequence()
```

### Parameters

**`$schema-name`**
The name of the schema specification containing the view.

**`$view-name`**
The name of the view on which the scope is set.

**`$scope`**
The scope to be set on the view. Use the 
    view:element-view-scope 
    
    function to set the scope to an element or the
    view:collection-view-scope 
     
    function to set the scope to a collection.
    
 For details on view scoping, see Defining View Scope in the SQL Data Modeling Guide.

### Returns

`empty-sequence()`

### Examples

```xquery
xquery version "1.0-ml"; 
 
  import module namespace view = "http://marklogic.com/xdmp/view" 
      at "/MarkLogic/views.xqy";

  view:set-view-scope("main", "songs", view:element-view-scope(xs:QName("SONG"))) 

  (: Sets the scope of the 'songs' view in the 'main' schema to the 
     element, 'SONGS'. :)
```

---

## view:views

This function returns all of the view specifications in the named schema.

### Signature

```xquery
view:views(
  $schema-name as xs:string
) as element(view:view)*
```

### Parameters

**`$schema-name`**
The name of the schema specification containing the views to be returned.

### Returns

`element(view:view)*`

### Examples

```xquery
xquery version "1.0-ml"; 
 
  import module namespace view = "http://marklogic.com/xdmp/view" 
      at "/MarkLogic/views.xqy";
 
  view:views("main")

  (: Returns all of the views in the 'main' schema. :)
```

---

## xdmp:collection-delete

Deletes from the database every document in a collection. If there are
  no documents in the specified collection, then nothing is deleted, and
  xdmp:collection-delete
  
  still returns the empty sequence.

### Signature

```xquery
xdmp:collection-delete(
  $uri as xs:string
) as empty-sequence()
```

### Parameters

**`$uri`**
The URI of the collection to be deleted.

### Returns

`empty-sequence()`

### Examples

```xquery
xdmp:collection-delete("collection-uri")
```

---

## xdmp:directory-create

Creates a directory.  If security is enabled,
  the document permissions and collections are set to the given parameters,
  if supplied.  Otherwise, the current user's default permissions and/or
  collections are applied.  If the beginning of the document URI is
  protected, the user must have access to that URI privilege.  If the
  directory URI does not end with a '/' one is added.  If the directory already
  exists, then an XDMP-DIREXISTS exception is thrown.

### Signature

```xquery
xdmp:directory-create(
  $uri as xs:string,
  $permissions as element(sec:permission)*?,
  $collections as xs:string*?,
  $quality as xs:int??,
  $forest-ids as xs:unsignedLong*?,
  $options as (element()|map:map)??
) as empty-sequence()
```

### Parameters

**`$uri`**
The URI of the directory to be inserted.

**`$permissions`** *(optional)*
Security permission elements corresponding to the permissions
    for the document.

**`$collections`** *(optional)*
The collections to which the new directory belongs.

**`$quality`** *(optional)*
The quality of this document.  A positive value increases
    the relevance score of the document in text search functions.
    The converse is true for a negative value.  The default value is 0.

**`$forest-ids`** *(optional)*
Specifies the ID of the forest in which this directory is created.
    If the directory already exists in the database and if $forest-ids is
    not specified, it will remain in its existing forest.  If no such
    forest exists or if no such forest is attached to the context database,
    an error is raised.  If multiple forests are specified, the directory
    is created in one of the specified forests.
    
    If you have local disk failover enabled, specify the ID of the master
    forest.  In the event of a failover, MarkLogic server will automatically
    redirect documents to the replica forest.  Specify the ID of the replica
    forest will result in a "forest not in database" error.

**`$options`** *(optional)*
Options with which to customize this operation. You 
    can specify options as either an options XML element
    in the "xdmp:directory-create" namespace, or as a map:map. 
    The options names below are XML element localnames. When using a map,
    replace the hyphens with camel casing. For example, "an-option"
    becomes "anOption" when used as a map:map key.
    
    if-exists
    
     Action if directory already exists with the URI. Valid values are "error"
    and "allow".  Default value is "error".  An XDMP-DIREXISTS exception is
    thrown if the directory exists when "error" is specified or this
    option is left unspecified.

### Returns

`empty-sequence()`

### Examples

#### Example 1

```xquery
xdmp:directory-create("http://marklogic.com/a/",
            (xdmp:permission("development", "update"),
             xdmp:permission("qa", "read")),
             "http://marklogic.com/directories")

=> Creates a directory named "http://marklogic.com/a/",
   which has the parent directory "http://marklogic.com/".
   The directory is created with the specified permissions,
   and is added to the "http://marklogic.com/directories"
   collection.
```

#### Example 2

```xquery
xdmp:directory-create("/dir/myDirectory/")

=> Creates a directory named "/dir/myDirectory/",
   which has the parent directory "/dir/", which
   in turn has parent directory "/". If
   directory creation is set to automatic in
   the database configuration, this example creates
   all three directories ("/", "/dir/", and
    "/dir/myDirectory/").
```

---

## xdmp:directory-delete

Deletes a directory and all of its child and descendant documents and
  directories from the database.

### Signature

```xquery
xdmp:directory-delete(
  $uri as xs:string
) as empty-sequence()
```

### Parameters

**`$uri`**
The URI of the directory to be deleted.

### Returns

`empty-sequence()`

### Usage Notes

If you delete a directory, the directory and all of its children
  and descendants (recursively)
  are deleted, including all child documents and directories. A child
  document or directory of a given directory is one whose URI begins with
  the same string as the directory URI.

### Examples

```xquery
xdmp:directory-delete("http://example.com/")
```

---

## xdmp:document-add-collections

Adds the named document to the given collections.  For each collection
  that is protected, the user must have permissions to update that
  collection or have the any-collection privilege.
  For each unprotected collection, the user must have the
  unprotected-collections privilege.

### Signature

```xquery
xdmp:document-add-collections(
  $uri as xs:string,
  $collections as xs:string*
) as empty-sequence()
```

### Parameters

**`$uri`**
The document URI.

**`$collections`**
A set of collection URIs.

### Returns

`empty-sequence()`

### Examples

```xquery
xdmp:document-add-collections(
    "/example.xml",
    ("http://examples.com", "http://marklogic.com"))
```

---

## xdmp:document-add-permissions

Adds the given permissions to the given document or directory.
  The user must have update or insert permissions on the document.

### Signature

```xquery
xdmp:document-add-permissions(
  $uri as xs:string,
  $permissions as element(sec:permission)*
) as empty-sequence()
```

### Parameters

**`$uri`**
The document URI.

**`$permissions`**
Permission elements.

### Returns

`empty-sequence()`

### Examples

```xquery
xdmp:document-add-permissions(
    "/example.xml",
    (xdmp:permission("development", "update"),
     xdmp:permission("qa", "read")))
```

---

## xdmp:document-add-properties

Adds a sequence of properties to the properties of a document.

### Signature

```xquery
xdmp:document-add-properties(
  $uri as xs:string,
  $props as element()*
) as empty-sequence()
```

### Parameters

**`$uri`**
The URI of the document.

**`$props`**
The properties to add.

### Returns

`empty-sequence()`

### Examples

```xquery
xdmp:document-add-properties(
       "example.xml",
       (<priority>1</priority>,
        <status>unedited</status>))
=> ()
```

---

## xdmp:document-assign

Assign a document URI to a forest index,
  using the same algorithm as xdmp:document-insert.
  The return value will be a positive integer
  from 1 to $forest-count.
  
      
  This function does not insert or update the document;
  instead, it returns the index of the forest
  to which the document URI would be assigned
  if it were inserted as a new document.
  In order to match the document to the correct forest,
  use the list of forest-IDs as returned by xdmp:database-forests.
  
      
  If the document already exists, this function may not
  return the correct forest for the document. In this case,
  xdmp:document-forest will return the
  correct forest.
  
      
  If "assignment-policy" is specified, this function uses the specified
  policy to calculate the assignment. Otherwise, it uses the assignment
  policy of the context database to calculate the assignment.
  
      
  This function works only with the bucket assignment policy, the segment
  assignment policy and the (now deprecated) legacy assignment policy. It
  reports an error if any other policy is specified.
  
      
  Note that, if there are read-only or delete-only forests in a database that
  uses the bucket policy, the application may need to call this function twice
  to get the right assignment. The first call should pass in the total number
  of forests, including the read-only or delete-only ones. If the returned value
  happens to be a read-only or delete-only forest,  the second call should pass
  in the number of forests that excludes the read-only or delete-only ones and
  pass in "legacy" as the third parameter.

### Signature

```xquery
xdmp:document-assign(
  $uri as xs:string,
  $forest-count as xs:positiveInteger,
  $assignment-policy as xs:string?
) as xs:positiveInteger
```

### Parameters

**`$uri`**
The document URI to assign.

**`$forest-count`**
Specifies the number of forests from which this document
    may be assigned.

**`$assignment-policy`** *(optional)*
Specifies the assignment policy to use. The value must be
    either "legacy" or "bucket".

### Returns

`xs:positiveInteger`

### Examples

#### Example 1

```xquery
xdmp:document-assign("document-1.xml", 2)
=> 2
```

#### Example 2

```xquery
xdmp:document-assign("document-2.xml", 2, "legacy")
=> 1
```

#### Example 3

```xquery
let $forests := xdmp:database-forests(xdmp:database())
let $index := xdmp:document-assign("document-1.xml", count($forests))
return $forests[$index]

=> 17618760155059123769
```

#### Example 4

```xquery
xdmp.documentAssign("document-2.xml", 2, "legacy")
=> 1
```

#### Example 5

```xquery
var forests = xdmp.databaseForests(xdmp.database()).toArray();
var index = xdmp.documentAssign("document-1.xml", forests.length);
forests[index-1];

=> 17618760155059123769
```

---

## xdmp:document-delete

Deletes a document from the database.

### Signature

```xquery
xdmp:document-delete(
  $uri as xs:string,
  $options as (element()|map:map)??
) as empty-sequence()
```

### Parameters

**`$uri`**
The URI of the document to be deleted.

**`$options`** *(optional)*
Options with which to customize this operation. You 
    can specify options in either an XML options element in 
    the "xdmp:document-delete" namespace, or as 
    a map:map. The options names below are XML element 
    localnames. When using a map, replace the hyphens with camel casing. 
    For example, "an-option" becomes "anOption" when used as a 
    map:map key. This function supports the following 
    options:
    
    if-not-exists
    
     Action if no document exists with the URI. Valid values are "error"
    and "allow".  Default value is "error".  An XDMP-DOCNOTFOUND exception is
    thrown if the document does not exist when "error" is specified or this
    option is left unspecified.

### Returns

`empty-sequence()`

### Usage Notes

The xdmp:document-delete function deletes
  a document and all of its properties, except, when
  directory-creation is set to automatic or
  manual-enforced, the directory property; it does
  not delete a directory with the same URI as the document being deleted unless
  directory-creation is set to manual.
  To delete a directory, use the xdmp:directory-delete function.

### Examples

#### Example 1

```xquery
xdmp:document-delete("example.xml")
```

#### Example 2

```xquery
(: Enable deletion of a non-existent document without error, using
 : options expressed as an XML options node. :)
xdmp:document-delete("example.xml",
  <options xmlns="xdmp:document-delete">
    <if-not-exists>allow</if-not-exists>
  </options>)
```

#### Example 3

```xquery
(: Enable deletion of a non-existent document without error, using
 : options expressed as map:map. :)
xdmp:document-delete("example.xml",
                     map:map() => map:with("ifNotExists", "allow"))
```

---

## xdmp:document-insert

Inserts a new document into the database if a document with the
  specified URI does not already exist.  If a document already exists
  at the specified URI, the function replaces the content of the existing
  document with the specified content (the $root parameter)
  as an update operation.  In addition to replacing the content,
  xdmp:document-insert replaces any permissions, collections,
  and quality with the ones specified (or with the default values for these
  parameters, if not explicitly specified).  Also, if a properties
  document exists at the same URI, that properties document (including any
  content it contains) is preserved.

### Signature

```xquery
xdmp:document-insert(
  $uri as xs:string,
  $root as node(),
  $options as (element()|map:map)??
) as empty-sequence()
```

### Parameters

**`$uri`**
The URI of the document to be inserted.

**`$root`**
The root node.  The root node can be one of JSON format, XML format,
    binary (BLOB) format, or text (CLOB) format.

**`$options`** *(optional)*
Options with which to customize this operation. You 
    can specify options as either an options XML element
    in the "xdmp:document-insert" namespace, or as a map:map.
    The options names below are XML element localnames. When using a map,
    replace the hyphens with camel casing. For example, "an-option"
    becomes "anOption" when used as a map:map key.
    This function supports the following options, plus the options from the
    xdmp:http-get
    
    function.
    
    permissions
    Specify permissions for the document. If not supplied, the current
    user's default permissions are applied. The default value used 
    for permissions can be obtained by calling the
    xdmp:default-permissions
    
    function. A document that is
    created by a non-admin user (that is, by any user who does not have the
    admin role) must have at least one update permission,
    otherwise the creation will throw an XDMP-MUSTHAVEUPDATE
    exception. When expressing options using a map:map, 
    use the "object" format for permissions; see the output-kind 
    parameter of xdmp:permission and 
    xdmp:default-permissions.
    
    collections
    The collection URIs for collections to which this document
    belongs.  If not supplied, the document is added to the current
    user's default collections.  For each collection that is protected, the
    user must have permissions to update that collection or have the
    any-collection privilege. For each unprotected collection,
    the user must have the unprotected-collections privilege.
    The default value used for collections can be obtained by 
    calling the
    xdmp:default-collections
    
    function. When expressing options as an XML element,
    specify the collection URIs in <collection> child elements of this 
    option, one URI per child. When expressing options as a map:map,
    specify the value of the collections key as a sequence
    of collection URIs.
    
    quality
     The quality of this document.  A positive value increases
    the relevance score of the document in text search functions.
    The converse is true for a negative value.  The default value is 0.
    
    forests
    Specifies the IDs of one or more forests in which this document is 
    inserted. Each forest is specified in a separate <forest>
    element. If the document already exists in the database and if 
    forests is not specified, it will remain in its existing 
    forest. If no such forest exists or if no such forest is attached to the 
    context database, an error is raised. If multiple forests are specified, 
    the document is inserted into one of the specified forests. If the 
    document exists and the forest in which it is stored is set to delete-only,
    then the forests option must include one or more forests that 
    allow updates, otherwise an exception is thrown.
    If you have local disk failover enabled, specify the ID of the master 
    forest. In the event of a failover, MarkLogic server will automatically 
    redirect documents to the replica forest.  Specify the ID of the replica 
    forest will result in a "forest not in database" error.
    
    metadata
    Specifies key-value pairs representing certain metadata associated 
     with the document. Metadata values are strings. Non-string values are 
     converted to strings.  When you express options as an
     XML element, the value of a metadata element is a serialized
     map containing the key-value pairs. When you express options as a
     map:map, the value associated with "metadata" key is also a map:map.

### Returns

`empty-sequence()`

### Usage Notes

If a document is inserted with the admin user and its default permissions,
   the document will only be accessible by a user with the admin role
   as the default permissions of the admin user is empty.

### Examples

#### Example 1

```xquery
xdmp:document-insert(
    "/example.xml", <a>aaa</a>,
    <options xmlns="xdmp:document-insert">
      <metadata>{
        map:map() => map:with("w", "world")
                  => map:with("h", "hello")
      }</metadata>
      <permissions>{xdmp:default-permissions()}</permissions>
    </options>)
```

#### Example 2

```xquery
(: Insert with perm, collection, and quality options. Notice that this
 : example adds to, rather than replaces, the default collections. :)
xdmp:document-insert(
    "/example.xml",
    <a>aaa</a>,
    <options xmlns="xdmp:document-insert">  
      <permissions>{xdmp:default-permissions()}</permissions>
      <collections>{
        <collection>/my/additional/collection</collection>,
        for $coll in xdmp:default-collections()
        return <collection>{$coll}</collection>
      }</collections>
      <quality>10</quality>
    </options>)
```

#### Example 3

```xquery
(: Expressing options as a map instead of an element :)
xquery version "1.0-ml";
xdmp:document-insert("/example.xml", <a>aaa</a>,
  map:map() => map:with("collections", ("coll1","coll2"))
            => map:with("quality", 2)
            => map:with("permissions", 
                        (xdmp:default-permissions("objects"),
                         xdmp:permission("some-role", "read", "object")))
)
```

#### Example 4

```xquery
(:
   Specify the valid start and end time for a temporal document.
:)
xdmp:document-insert(
    "/example.xml",
    <root>new content here</root>, 
    <options xmlns="xdmp:document-insert">  
      <metadata>{
        map:map() => map:with("valid-start", "2014-06-03T14:13:05.472585-07:00")
                  => map:with("valid-end", "9999-12-31T11:59:59Z")
      }</metadata>
    </options>)
```

#### Example 5

```xquery
xquery version "1.0-ml";
(: create a text document :)
xdmp:document-insert("/text-doc.txt",
   text { "This is a text document." } )
```

---

## xdmp:document-load

Inserts a new document with the specified URI. If a document already exists
  at the URI, the function replaces the content in the existing document as
  an update operation.

### Signature

```xquery
xdmp:document-load(
  $location as xs:string,
  $options as (element()|map:map)??
) as empty-sequence()
```

### Parameters

**`$location`**
The location of the input document.  If the scheme of the location is
    HTTP (that is, if the string starts with "http://"), then the document is
    requested over HTTP.  If the scheme is file (that is, if the string starts
    with "file://"), then the document is requested over file protocol from
    the local filesystem.
    Otherwise, the document is fetched from the local
    filesystem. On the filesystem, the path can be fully qualified or relative.
    Relative pathnames are resolved from the directory in which
    MarkLogic Server is installed.

**`$options`** *(optional)*
Options with which to customize this operation. You 
    can specify options as either an options XML element
    in the "xdmp:load" namespace, or as a map:map. The
    options names below are XML element localnames. When using a map,
    replace the hyphens with camel casing. For example, "an-option"
    becomes "anOption" when used as a map:map key.
    This function supports the following options, plus the options from the
    xdmp:http-get
     function.
    
    uri
     The URI of the document to be loaded. If omitted, then the location
    is used for the URI.
    permissions
    Security permission corresponding to the permissions for the
    document. If not supplied, the current user's default permissions are
    applied. The default value used for $permissions can be obtained by
    calling xdmp:default-permissions()
    . A document that
    is created by a non-admin user (that is, by any user who does not have the
    admin role) must have at least one update permission,
    otherwise the creation will throw an XDMP-MUSTHAVEUPDATE
    exception. When expressing options using a map:map, 
    use the "object" format for permissions; see the output-kind 
    parameter of xdmp:permission and 
    xdmp:default-permissions.
    
    collections
    The collection URIs for collections to which this document belongs.
    If not supplied, the document is added to the current user's default
    collections  (the collections returned from
    xdmp:default-collections()
    ). For each
    collection that is protected, the user must have permissions to update
    that collection or have the any-collection privilege. For
    each unprotected collection, the user must have the
    unprotected-collections privilege. The
    <collections> element consists of one or more
    <collection> child elements. For example:
    
    <collections>
      <collection>myCollection1</collection>
      <collection>myCollection2</collection>
    </collections> 
    
    quality
     The quality of this document. A positive value increases the
    relevance score of the document in text search functions. The converse is
    true for a negative value. The default value is 0.
    default-namespace
    
    (XML only) The namespace to use if there is no namespace at the root
    node of the document.  The default value is "".
    repair
    A value of full specifies that malformed XML
        content be repaired.  A value of none specifies that
        malformed XML content is rejected.
        If no repair option is explicitly specified, the
	    default is implicitly specified by the XQuery version of the caller.
        In XQuery 1.0 and 1.0-ml the default
        is none.  In XQuery 0.9-ml the
        default is full.
        
        This option has no effect on binary, text or JSON documents.
    format
    A value of text specifies to get the document as a text
        document, regardless of the URI specified. A value of
        binary specifies to get the document as a binary
        document, regardless of the URI specified. A value of xml
        specifies to get the document as an XML document, regardless of the
        URI specified. A value of json
        specifies to get the document as a JSON document, regardless of the
        URI specified.
    default-language
    
    The language to specify in an xml:lang attribute on the
    root element node if the root element node does not already have an
    xml:lang attribute. This option applies only to XML documents.
    If this option is not specified, then nothing is added to the root element
    node.
    encoding
    Specifies the encoding to use when reading the document into MarkLogic
    Server. The value must either be "auto" or match an encoding name 
    according to the Unicode Charset Alias Matching rules
    (http://www.unicode.org/reports/tr22/#Charset_Alias_Matching).
    When the value is "auto", MarkLogic guesses the encoding from
    the document content. For a list of character set encodings by language, see
 Collations and Character Sets By Language in the Search Developer's Guide. 
    If you do not set this option, MarkLogic uses the encoding
    specified in the HTTP headers, if present. If you do not set this option
    and no encoding is available from HTTP headers, the encoding
    defaults to UTF-8. For more details, see
 Character Encoding in the Search Developer's Guide.
    forests
    Specifies the ID of the forest in which this document is inserted.
    Each forest ID is in a <forest> child element and
    is of type xs:unsignedLong.
    . If the document
    already exists in the database, it will remain in its existing forest. If
    no such forest exists or if no such forest is attached to the context
    database, an error is raised. If multiple forests
    are specified, the document is inserted into one of the specified
    forests.  If the document already exists and the forest in which it is
    stored is set to delete-only, then you must specify the forest IDs to
    include one or more forests that allow updates, otherwise an exception is
    thrown.
    
    If you have local disk failover enabled, specify the ID of the master
    forest.  In the event of a failover, MarkLogic server will automatically
    redirect documents to the replica forest.  Specify the ID of the replica
    forest will result in a "forest not in database" error.
    
    
    metadata
    Specifies key-value pairs representing user-defined metadata associated 
     with the document. Metadata values are strings. Non-string values are 
     converted to strings.  When you express the options as
     an XML element, the value of the metadata option element is 
     a serialized map:map. When you express the options as a map:map,
     the associated with the "metadata" option key is itself a map:map.

### Returns

`empty-sequence()`

### Usage Notes

When selecting documents over HTTP (where the $location
  parameter begins with http://), the response from the webserver
  is loaded into the database, regardless of what the headers returned
  from the webserver indicate.  For example, if the webserver returns a
  404 (file not found), then the response page that says "file not found"
  is loaded into the database.  If you want to examine the headers before
  loading the document, use xdmp:http-get
   (combined with
  xdmp:document-insert
  ) instead, as
  xdmp:http-get
  allows you to examine the headers returned from the HTTP server.

### Examples

#### Example 1

```xquery
(: Load a document from the file system, using options expressed
 : as an XML element. :)
xdmp:document-load("c:\myFile.xml",
    <options xmlns="xdmp:document-load">
      <uri>/documents/myFile.xml</uri>
      <repair>none</repair>
      <permissions>{xdmp:default-permissions()}</permissions>
      <metadata>{
        map:map() => map:with("h", "hello")
                  => map:with("w", "world")
      }</metadata>
    </options>)

(: Loads the document with a URI "/documents/myFile.xml"
 : and does not perform tag repair during the load. :)
```

#### Example 2

```xquery
(: Load a document from the file system, using options expressed
 : as a map:map. :)
xdmp:document-load("c:\myFile.xml",
    map:map() => map:with("uri", "/documents/myFile.xml")
              => map:with("repair", "none")
              => map:with("metadata", map:map() => map:with("key", "value"))
)

(: Loads the document with a URI "/documents/myFile.xml"
 : and does not perform tag repair during the load. :)
```

#### Example 3

```xquery
xdmp:document-load("http://myCompany.com/file.xml",
    <options xmlns="xdmp:document-load"
             xmlns:http="xdmp:http">
      <uri>/documents/myFile.xml</uri>
      <repair>none</repair>
      <permissions>{xdmp:default-permissions()}</permissions>
      <format>xml</format>
      <http:authentication>
          <http:username>user</http:username>
          <http:password>pass</http:password>
      </http:authentication>
    </options>)

(: Loads the document with a URI "/documents/myFile.xml"
 : from the server http://myCompany.com, sending the
 : credentials user/pass. Tag repair is not performed
 : during the load, the document is loaded as xml with
 : metadata key-value pairs of 'h:hello' and 'w:world'. :)
```

#### Example 4

```xquery
(: Using a map to expression options, rather than an XML element. :)
xdmp:document-load("c:\myFile.xml",
  map:map() => map:with("uri", "/documents/myFiles.xml")
            => map:with("permissions", 
                        (xdmp:default-permissions("objects"),
                         xdmp:permission("some-role", "read", "object")))
            => map:with("collections", ("myCollection1", "myCollection2"))
            => map:with("repair", "full")
            => map:with("forests", (xdmp:forest("myForest")))
)

(: Loads the document with a URI "/documents/myFile.xml"
 : performing tag repair during the load, adding the
 : document to the "myCollection1" and "myCollection2"
 : collections, and loading the document into the forest
 : named "myForest". :)
```

---

## xdmp:document-partition-assign

Assign a document to a partition number,
  using the partition queries in the database or in the second argument.
  The return value is the partition number where
  the document should be inserted.

### Signature

```xquery
xdmp:document-partition-assign(
  $root as node(),
  $partition-queries as map:map?
) as xs:unsignedInt?
```

### Parameters

**`$root`**
The document to assign.

**`$partition-queries`** *(optional)*
A map of partition-number to cts query.

### Returns

`xs:unsignedInt?`

### Examples

#### Example 1

```xquery
xdmp:document-partition-assign("<top><a>hello world</a></top>")
=> 2
```

#### Example 2

```xquery
xquery version "1.0-ml";

let $map := map:map()
let $put := map:put($map,"1",
  cts:element-range-query(
xs:QName("create-time"),
">=",
xs:dateTime("2014-01-01T00:00:00")))
let $put := map:put($map,"2",
  cts:element-range-query(
xs:QName("create-time"),
">=",
xs:dateTime("2013-01-01T00:00:00")))

return
xdmp:document-partition-assign(
<root>
<name>test1</name>
<create-time>2013-07-05T00:00:00</create-time>
</root>,
$map
)
=>2
```

---

## xdmp:document-put-metadata

Adds metadata to the document.  If any key already exists in the document
  metadata, the new specified value replaces the old one.  
  Metadata values are strings. Non-string values are converted to strings.

### Signature

```xquery
xdmp:document-put-metadata(
  $uri as xs:string,
  $metadata as map:map
) as empty-sequence()
```

### Parameters

**`$uri`**
The document URI.

**`$metadata`**
Metadata in the key value pairs to set on the document.

### Returns

`empty-sequence()`

### Examples

```xquery
xdmp:document-put-metadata(
  "foo.xml",
  map:map(
    <map:map xmlns:map="http://marklogic.com/xdmp/map">
      <map:entry key="w">
        <map:value>world</map:value>
      </map:entry>
      <map:entry key="h">
        <map:value>hello</map:value>
      </map:entry>
    </map:map>
  )
)
```

---

## xdmp:document-remove-collections

Removes the named document from the given collections.  For each
  collection that is protected, the user must have permissions to update
  that collection or have the any-collection privilege.  For each
  unprotected collection, the user must have the
  unprotected-collections privilege.

### Signature

```xquery
xdmp:document-remove-collections(
  $uri as xs:string,
  $collections as xs:string*
) as empty-sequence()
```

### Parameters

**`$uri`**
The document URI.

**`$collections`**
A set of collection URIs.

### Returns

`empty-sequence()`

### Examples

```xquery
xdmp:document-remove-collections(
  "/example.xml",
  ("http://examples.com", "http://marklogic.com"))
```

---

## xdmp:document-remove-metadata

Removes metadata with certain keys from a document.

### Signature

```xquery
xdmp:document-remove-metadata(
  $uri as xs:string,
  $metadata as xs:string*
) as empty-sequence()
```

### Parameters

**`$uri`**
The document URI.

**`$metadata`**
Name of the metadata to be removed.

### Returns

`empty-sequence()`

### Examples

```xquery
xdmp:document-remove-metadata("foo.xml", ("a","b"))
```

---

## xdmp:document-remove-permissions

Removes the given permissions from the named document or directory.
  The user must have update permissions on the document or directory.

### Signature

```xquery
xdmp:document-remove-permissions(
  $uri as xs:string,
  $permissions as element(sec:permission)*
) as empty-sequence()
```

### Parameters

**`$uri`**
The document URI.

**`$permissions`**
Permission elements.

### Returns

`empty-sequence()`

### Examples

```xquery
xdmp:document-remove-permissions(
    "/example.xml",
    (xdmp:permission("development", "update"),
     xdmp:permission("qa", "read")))
```

---

## xdmp:document-remove-properties

Removes a sequence of properties from the properties of a document.  If
  properties with the QNames given do not exist, nothing is done.

### Signature

```xquery
xdmp:document-remove-properties(
  $uri as xs:string,
  $property-names as xs:QName*
) as empty-sequence()
```

### Parameters

**`$uri`**
The URI of the document whose properties are being updated.

**`$property-names`**
The properties to remove.

### Returns

`empty-sequence()`

### Examples

```xquery
xdmp:document-remove-properties(
       "/example.xml",
       (fn:QName("", "priority"),
        fn:QName("", "status")))
=> ()
```

---

## xdmp:document-set-collections

Sets the named document to belong to the given collections, replacing any
  previously set collections on the named document.  To preserve existing
  collections, use xdmp:document-add-collections.  For each
  collection that is protected, the user must have permissions to update
  that collection or have the any-collection privilege.  For each
  unprotected collection, the user must have the
  unprotected-collections privilege.

### Signature

```xquery
xdmp:document-set-collections(
  $uri as xs:string,
  $collections as xs:string*
) as empty-sequence()
```

### Parameters

**`$uri`**
The document URI.

**`$collections`**
A set of collection URIs.

### Returns

`empty-sequence()`

### Examples

```xquery
xdmp:document-set-collections(
  "/example.xml",
  ("http://examples.com", "http://marklogic.com"))
```

---

## xdmp:document-set-metadata

Sets metadata to the document.  All existing metadata in the document will be
  replaced with the newly specified ones.  
  Metadata values are strings. Non-string values are converted to strings.

### Signature

```xquery
xdmp:document-set-metadata(
  $uri as xs:string,
  $metadata as map:map
) as empty-sequence()
```

### Parameters

**`$uri`**
The document URI.

**`$metadata`**
Metadata in the key value pairs to set on the document.

### Returns

`empty-sequence()`

### Examples

```xquery
xdmp:document-set-metadata(
    "foo.xml",
    map:map(<map:map xmlns:map="http://marklogic.com/xdmp/map">
      <map:entry key="w">
        <map:value>world</map:value>
      </map:entry>
      <map:entry key="h">
        <map:value>hello</map:value>
      </map:entry>
    </map:map>))
```

---

## xdmp:document-set-permissions

Sets the permissions on the named document (or directory) to the given
  permissions, replacing any permissions previously set on the
  document (or directory).  To preserve
  any existing permissions, use
  xdmp:document-add-permissions.
  .
  The user must have update permissions on the document or directory.

### Signature

```xquery
xdmp:document-set-permissions(
  $uri as xs:string,
  $permissions as element(sec:permission)*
) as empty-sequence()
```

### Parameters

**`$uri`**
The document URI.

**`$permissions`**
Permission elements.

### Returns

`empty-sequence()`

### Examples

```xquery
xdmp:document-set-permissions(
    "/example.xml",
    (xdmp:permission("development", "update"),
     xdmp:permission("qa", "read")))
```

---

## xdmp:document-set-properties

Sets the properties of a document to the given sequence of elements,
  replacing any properties that already exist on the document. To preserve
  existing document properties, use xdmp:document-add-properties.
  Each element QName is the property name and the element value is the
  property value.  Modifying properties requires update permissions on a
  document.

### Signature

```xquery
xdmp:document-set-properties(
  $uri as xs:string,
  $props as element()*
) as empty-sequence()
```

### Parameters

**`$uri`**
The URI of the document.

**`$props`**
The properties to set. Replaces any properties already set on the
    document.

### Returns

`empty-sequence()`

### Examples

```xquery
xdmp:document-set-properties(
         "example.xml",
         (<priority>1</priority>,
          <status>unedited</status>))
  => ()
```

---

## xdmp:document-set-property

Sets a property on a document.  If any properties with the same property
  QName exist, they are replaced with the new property.  If no properties
  exist with the same QName, the new property is added.

### Signature

```xquery
xdmp:document-set-property(
  $uri as xs:string,
  $prop as element()
) as empty-sequence()
```

### Parameters

**`$uri`**
The document URI for the property setting.

**`$prop`**
The property to set.

### Returns

`empty-sequence()`

### Examples

```xquery
xdmp:document-set-property(
  "http://marklogic.com/a/example.xml",
  <priority xmlns="http://example.com">5</priority>)
```

---

## xdmp:document-set-quality

Sets the quality of the document with the given URI.
  If the quality of the document is positive,
  the relevance score of the document is increased in text
  search functions.  The converse is true for "negative" quality.

### Signature

```xquery
xdmp:document-set-quality(
  $uri as xs:string,
  $quality as xs:integer
) as empty-sequence()
```

### Parameters

**`$uri`**
The URI of the document to which you are setting the quality.

**`$quality`**
The quality to which to set the document.

### Returns

`empty-sequence()`

### Examples

```xquery
xdmp:document-set-quality(
  "http://www.marklogic.com/test.xml",10)
=> ()
```

---

## xdmp:load

[DEPRECATED: use xdmp:document-load
  
  instead]
  Inserts a new document from the XML file at $path if a document
  with the specified URI does not already exist. Otherwise, the
  function replaces the content in the existing document as an update
  operation.

### Signature

```xquery
xdmp:load(
  $path as xs:string,
  $uri as xs:string??,
  $permissions as element(sec:permission)*?,
  $collections as xs:string*?,
  $quality as xs:int??,
  $default-namespace as xs:string??,
  $options as xs:string*?,
  $forest-ids as xs:unsignedLong*?
) as empty-sequence()
```

### Parameters

**`$path`**
The path to the input file.  The path can be fully qualified or relative.
    Relative pathnames are resolved from the directory in which
    MarkLogic Server is installed.

**`$uri`** *(optional)*
The URI of the document to be loaded.
    If omitted, then the pathname is used.

**`$permissions`** *(optional)*
Security permission elements corresponding to the permissions
    for the document. If not supplied, the current user's default
    permissions are applied.  The default value used for $permissions
    can be obtained by calling xdmp:default-permissions(). To specify
    no permissions, enter the empty sequence ().

**`$collections`** *(optional)*
The collection URIs for collections to which this document
    belongs.  If not supplied, the document is added to the current
    user's default collections.  The default value used for $collections
    can be obtained by calling xdmp:default-collections(). To specify
    no collections, enter the empty sequence ().

**`$quality`** *(optional)*
The quality of this document.  A positive value increases
    the relevance score of the document in text search functions.
    The converse is true for a negative value.  The default value is 0.

**`$default-namespace`** *(optional)*
If $default-namespace is specified and the root node of the
    loaded document does not explicitly specify a namespace,
    $default-namespace will be applied to the root node.
    The default value for $default-namespace is "".

**`$options`** *(optional)*
The options for loading this document.
    The default value is ().
    Options include:
    
    "repair-full"
    Specifies that malformed XML content be repaired during loading.
        This option has no effect on binary or text documents.
    "repair-none"
    Specifies that malformed XML content be rejected during loading.
        This option has no effect on binary or text documents.
    "format-text"
    Specifies to load the document as a text document,
        regardless of the URI specified.
    "format-binary"
    Specifies to load the document as a binary document,
        regardless of the URI specified.
    "format-xml"
    Specifies to load the document as an XML document,
        regardless of the URI specified.
    "format-json"
    Specifies to load the document as a JSON document,
        regardless of the URI specified.
    "lang=en"
    Specifies that the document is in english.

**`$forest-ids`** *(optional)*
Specifies the ID of the forest in which this document is inserted.
    If the document already exists in the database, it will remain in
    its existing forest.  If no such forest exists or if no such forest
    is attached to the context database, an error is raised.  If
    multiple forests are specified, the document is inserted into
    one of the specified forests.
    
    If you have local disk failover enabled, specify the ID of the master
    forest.
    In the event of a failover, MarkLogic server will automatically redirect
    documents
    to the replica forest.  Specify the ID of the replica forest will result
    in a "forest not in database" error.

### Returns

`empty-sequence()`

### Usage Notes

If no format is specified in $options, it is specified by the
  document content type specified by the extension of the document URI.
  The mimetype extensions and corresponding content types are set in the
  Admin Interface.
      If neither "repair-full" nor "repair-none" is present,
  the default is specified by the XQuery version of the caller.
  In XQuery version 1.0 and 1.0-ml the default is
  "repair-none".  In XQuery version 0.9-ml the default is
  "repair-full".

### Examples

#### Example 1

```xquery
xdmp:load("/home/test/example.xml", "/example.xml",
            (xdmp:permission("editor", "read"),
             xdmp:permission("editor", "update")),
            "http://examples.com",
            10,"http://www.marklogic.com/default")
```

#### Example 2

```xquery
xdmp:load("/home/test/example.xml",
            "/example.xml",
            xdmp:default-permissions(),
            xdmp:default-collections(),
            0,
            "",
            "repair-none")
```

---

## xdmp:lock-acquire

Acquire a lock on a document or directory for an extended amount of time.
  Locks restrict updates to a document or directory to the user who acquires
  the lock.

### Signature

```xquery
xdmp:lock-acquire(
  $uri as xs:string,
  $scope as xs:string??,
  $depth as xs:string??,
  $owner as item()*?,
  $timeout as xs:unsignedLong??
) as empty-sequence()
```

### Parameters

**`$uri`**
The URI of the document or directory to be locked.

**`$scope`** *(optional)*
The lock scope ("exclusive" or "shared").  The default is "exclusive".

**`$depth`** *(optional)*
The lock depth ("0" or "infinity").  "0" locks the URI only, and "infinity"
    locks the URI (the document or directory) and all of its children.  The
    default is "0".

**`$owner`** *(optional)*
Alternate description of the lock owner.  If not specified  or if
    specified as the empty sequence ( () ), then the owner is the user name
    of the user requesting the lock.

**`$timeout`** *(optional)*
Requested lock timeout in seconds. If not specified or if specified as the
    empty sequence ( () ) or if specified as 0, then the timeout is infinite.

### Returns

`empty-sequence()`

### Usage Notes

If you lock a directory specifying a depth of "infinity", the directory
   and all of it children (all documents and directories with a URI started with
   the locked directory) are locked. You will not be able to add any children
   to the directory until the lock is released.
      When a user locks a URI, it is locked to other users, but not to the user
   who locked it.  For example, if the user sam locks the URI
   /home/sam.xml by issuing the statement
   xdmp:lock-acquire("/home/sam.xml")
   ,
   the user sam
   can still issue update commands to the document at that URI, but other users
   (for example, the user josh) will get an exception if they try
   to update the document.
      If you attempt to acquire a lock on a document that already has a lock,
   the XDMP-LOCKCONFLICT exception is thrown.
      If you attempt to update a document that is locked by another user,
   the XDMP-LOCKED exception is thrown.
      Note that the lock described here is a relatively heavy persistent
   document lock for file system emulation through WebDAV, not a relatively
   light transaction lock for database consistency.

### Examples

```xquery
xquery version "1.0-ml";
declare namespace DAV="DAV:";

xdmp:lock-acquire("/example.xml",
           "exclusive",
           "0",
           <DAV:href>http://example.com/~user</DAV:href>,
           xs:unsignedLong(120))
=> ()
```

---

## xdmp:lock-for-update

Acquires an intent exclusive transaction lock on a URI.
  If a shared transaction lock on the URI is already held by
  the current transaction it is promoted to an exclusive lock.
  If a shared or exclusive transaction lock on the URI is already
  held by some other transaction, this function blocks until
  that lock is released.

### Signature

```xquery
xdmp:lock-for-update(
  $uri as xs:string
) as empty-sequence()
```

### Parameters

**`$uri`**
The URI to be locked for update.

### Returns

`empty-sequence()`

### Usage Notes

This function allows an update transaction to acquire an exclusive write
lock on a URI without specifying an update. Deadlocks and restarted transactions
can be avoided by first explicitly acquiring an exclusive transaction lock
on the URI with this function, before implicitly acquiring a
shared transaction lock reading a document with that URI.
      An exclusive transaction lock on a URI is automatically
and implicitly acquired when an update function is applied on that URI.
Similarly, a shared transaction lock on a URI is automatically and implicitly
acquired when a document with that URI is read by an update transaction.
If two update transactions concurrently read a document and
then apply an update function on it, a deadlock can occur, because each transaction
waits for the other to release its shared lock in order to escalate to
an exclusive lock. This deadlock is automatically detected by the system,
one of the transactions is restarted and its locks are released,
and the other transaction proceeds.
      Note that the lock acquired by this function is a relatively light transaction
lock for database consistency, not a relatively heavy persistent document
lock for file system emulation through WebDAV.

### Examples

```xquery
xdmp:lock-for-update("/example.xml")
```

---

## xdmp:lock-release

Unlock a document or directory.  Releases the lock created with
  xdmp:lock-acquire
  .

### Signature

```xquery
xdmp:lock-release(
  $uri as xs:string
) as empty-sequence()
```

### Parameters

**`$uri`**
The URI of the document or directory to be unlocked.

### Returns

`empty-sequence()`

### Usage Notes

Note that the lock described here area is a relatively heavy
  persistent document lock for file system emulation through WebDAV, not
  a relatively light transaction lock for database consistency.

### Examples

```xquery
xdmp:lock-release("/example.xml")
=> ()
```

---

## xdmp:merge

Starts merging the forests of the database, subject to specified
  options.

### Signature

```xquery
xdmp:merge(
  $options as (element()|map:map)??
) as empty-sequence()
```

### Parameters

**`$options`** *(optional)*
Options with which to customize this operation.
    You can specify options in either an XML 
    options element in the "xdmp:merge" namespace, or as 
    a map:map. The options names below are XML element 
    localnames. When using a map, replace any hyphens in an option name
    with camel casing. For example, "an-option" becomes "anOption" 
    when used as a map:map key. This function supports 
    the following options:
    
    merge-timestamp
    
    Fragments with a timestamp of this or newer are not garbage collected
    during this merge.
    A negative value means the timestamp is relative to the time the merge
    starts, at ten million ticks per second.
    For example, -6000000000 means ten minutes before the merge.
    The default is 0, which means not specifying a timestamp.
    merge-max-size
    
    The maximum allowable size, in megabytes, of a resultant stand. 
    The default value is taken from the database configuration.  
    A value of 0 means there is no limit. 
    It is possible for a stand larger than the merge-max-size to merge if
    the stand has enough deleted fragments to trigger the merge min ratio;
    in this case, MarkLogic will do a single-stand merge, merging out the
    deleted fragments (even if the resulting stand is larger than the
    merge-max-size value specified).
    
    merge-priority
    
    The CPU scheduler priority for the merge ("normal" or "lower").
    single-stand
    
    If any forests in the database have a single stand and this parameter
    is false, do not merge them.  The default is true.
    
    forests
    
    Specifies the IDs of the forests in which to perform merges.
    When you express options as an XML option node,
    specify each forest ID as a forest child element of this
    option, with a type of xs:unsignedLong. When you
    express options as a map, the value of this option is a sequence of
    forest IDs, with a type of xs:unsignedLong.
    
    The default is to merge all of the forests in the database.

### Returns

`empty-sequence()`

### Examples

#### Example 1

```xquery
xdmp:merge(<options xmlns="xdmp:merge">
               <merge-max-size>500</merge-max-size>
               <merge-timestamp>8273</merge-timestamp>
               <single-stand>false</single-stand>
               <forests>
                 <forest>{xdmp:forest("my-forest")}</forest>
                 <forest>{xdmp:forest("my-other-forest")}</forest>
               </forests>
             </options>)

(: Performs a merge on my-forest and my-other-forest.  If a stand
 : created by this merge would be greater than 500 megabytes, the merge
 : will be limited and not all stands will be merged (as many as can be
 : merged under 500 MB will be merged).  If my-forest or my-other-forest
 : have only one stand, they will not be merged.  Any fragments with
 : timestamp 8273 or newer will not be garbage collected.
:)
```

#### Example 2

```xquery
xdmp:merge(
  map:map() => map:with("mergeMaxSize", 500)
            => map:with("mergeTimestamp", 8273)
            => map:with("singleStand", fn:false())
            => map:with("forests", 
                        (xdmp:forest("my-forest"),
                         xdmp:forest("my-other-forest")))
)

(: Performs a merge on my-forest and my-other-forest.  If a stand
 : created by this merge would be greater than 500 megabytes, the merge
 : will be limited and not all stands will be merged (as many as can be
 : merged under 500 MB will be merged).  If my-forest or my-other-forest
 : have only one stand, they will not be merged.  Any fragments with
 : timestamp 8273 or newer will not be garbage collected.
:)
```

---

## xdmp:merging

Returns the forest IDs of any currently merging database forests.

### Returns

`xs:unsignedLong*`

### Examples

```xquery
xdmp:merging()
=> 23487234872334
```

---

## xdmp:node-delete

Deletes a node from the database.
  On-the-fly constructed nodes cannot be deleted.

### Signature

```xquery
xdmp:node-delete(
  $old as node()
) as empty-sequence()
```

### Parameters

**`$old`**
The node to be deleted.

### Returns

`empty-sequence()`

### Examples

```xquery
xdmp:document-insert("/example.xml",
    <a><b>bbb</b></a>);
xdmp:node-delete(doc("/example.xml")/a/b);
doc("/example.xml")
=>
 <a/>
```

---

## xdmp:node-insert-after

Adds an immediately following sibling to a node.

### Signature

```xquery
xdmp:node-insert-after(
  $sibling as node(),
  $new as node()
) as empty-sequence()
```

### Parameters

**`$sibling`**
The sibling node to be followed by the new node.

**`$new`**
The new node to be inserted.

### Returns

`empty-sequence()`

### Usage Notes

Attribute nodes cannot be followed by non-attribute nodes.
  Non-attribute nodes cannot be followed by attribute nodes.
  Element nodes cannot have document node children.
  Document nodes cannot have multiple roots.
  On-the-fly constructed nodes cannot be updated.

### Examples

```xquery
xdmp:document-insert("/example.xml",
    <a><b>bbb</b></a>);
  xdmp:node-insert-after(doc("/example.xml")/a/b,
    <c>ccc</c>);
  doc("/example.xml")
 =>
  <a><b>bbb</b><c>ccc</c></a>
```

---

## xdmp:node-insert-before

Adds an immediately preceding sibling to a node.

### Signature

```xquery
xdmp:node-insert-before(
  $sibling as node(),
  $new as node()
) as empty-sequence()
```

### Parameters

**`$sibling`**
The sibling node to be preceded by the new node.

**`$new`**
The new node to be inserted.

### Returns

`empty-sequence()`

### Usage Notes

Attribute nodes cannot be preceded by non-attribute nodes.
  Non-attribute nodes cannot be preceded by attribute nodes.
  Element nodes cannot have document node children.
  Document nodes cannot have multiple roots.
  On-the-fly constructed nodes cannot be updated.

### Examples

```xquery
(: create a document :)
xdmp:document-insert("/example.xml",
    <a><b>bbb</b></a>);

(: add a c node before the b node :)
xdmp:node-insert-before(fn:doc("/example.xml")/a/b,
    <c>ccc</c>);

(: look at the new document :)
fn:doc("/example.xml")
 =>
<?xml version="1.0" encoding="UTF-8"?>
<a><c>ccc</c><b>bbb</b></a>
```

---

## xdmp:node-insert-child

Adds a new last child to a node.
  For XML documents, only element nodes and document nodes can have children.
  For JSON documents, object nodes and array nodes can have children.
  Element nodes, object nodes, and array nodes cannot have document node
  children.
  Document nodes cannot have multiple roots.
  On-the-fly constructed nodes cannot be updated.
  The parameters must specify individual nodes and not node sets.

### Signature

```xquery
xdmp:node-insert-child(
  $parent as node(),
  $new as node()
) as empty-sequence()
```

### Parameters

**`$parent`**
The parent node which will have a new child node.

**`$new`**
The new child node to be inserted.

### Returns

`empty-sequence()`

### Examples

#### Example 1

```xquery
(: create a document :)
xdmp:document-insert("/example.xml",
    <a/>);

(: insert a child of a :)
xdmp:node-insert-child(doc("/example.xml")/a,
    <b>bbb</b>);

(: look at the new document :)
fn:doc("/example.xml")
 =>
<?xml version="1.0" encoding="UTF-8"?>
<a><b>bbb</b></a>
```

#### Example 2

```xquery
(: create a document :)
xdmp:document-insert("/example.xml",
    <a/>);

(: insert an attribute as child of a :)
  xdmp:node-insert-child(doc("/example.xml")/a,
    attribute b { "bbb" });

(: look at the new document :)
fn:doc("/example.xml")
 =>
<?xml version="1.0" encoding="UTF-8"?>
<a b="bbb"/>
```

---

## xdmp:node-replace

Replaces a node.

### Signature

```xquery
xdmp:node-replace(
  $old as node(),
  $new as node()
) as empty-sequence()
```

### Parameters

**`$old`**
The old node, to be replaced.

**`$new`**
The new node.

### Returns

`empty-sequence()`

### Usage Notes

Attribute nodes cannot be replaced by non-attribute nodes.
  Non-attribute nodes cannot be replaced by attribute nodes.
  Element nodes cannot have document node children.
  Document nodes cannot have multiple roots.
  If the caller of the function uses function mapping and $old 
  is an empty sequence, the node-replace function may return an 
  empty sequence. It will not return an error.

### Examples

#### Example 1

```xquery
(: create an XML document :)
  xdmp:document-insert("/example.xml",
    <a><b>bbb</b></a>);

(: replace the b node with a c node :)
  xdmp:node-replace(doc("/example.xml")/a/b, <c>ccc</c>);

(: look at the new document :)
fn:doc("/example.xml")
 =>
<?xml version="1.0" encoding="UTF-8"?>
<a><c>ccc</c></a>
```

#### Example 2

```xquery
(: This example shows how to update the root
   node of a text format document.  Start by
   creating a text document.     :)

xdmp:document-insert("/mydir/doc.txt",
text{"This is a line of text."} ) ;

(: Update the text node of the text document
   by appending another line of text to the
   text node.  Note that the text node is the
   root node of a text document.     :)

xdmp:node-replace(doc("/mydir/doc.txt")/text() ,
text{ concat(doc("/mydir/doc.txt")/text(), "
This is another line of text.") } ) ;

doc("/mydir/doc.txt")
=>
This is a line of text.
This is another line of text.
```

#### Example 3

```xquery
(: create a document :)
xdmp:document-insert("/foo.json", object-node {"foo":"this is a value"});
(: replace the value using xdmp:node-replace :)
xdmp:node-replace(fn:doc("/foo.json")/foo, text{"this is a different value"});
fn:doc("/foo.json")
=>
{"foo":"this is a different value"}
```

---

## xdmp:partition-forests

Returns a sequence of forest IDs with the specified partition number

### Signature

```xquery
xdmp:partition-forests(
  $partition-number as xs:unsignedInt
) as xs:unsignedLong*
```

### Parameters

**`$partition-number`**
A partition number.

### Returns

`xs:unsignedLong*`

### Examples

```xquery
xdmp:partition-forests(3)
=> (8456374036761185098, 10615125154705099114)
```

---

## xdmp:query-partitions

This function returns the partition numbers of the partitions that the specified 
query will be searched on.

### Signature

```xquery
xdmp:query-partitions(
  $query as cts:query
) as xs:unsigned*
```

### Parameters

**`$query`**
A query.

### Returns

`xs:unsigned*`

### Examples

```xquery
xdmp:query-partitions(
  cts:element-range-query(xs:QName("create-time"), ">=", xs:yearMonthDuration("P1Y"))
)
  =>
    1
```

---

## xdmp:range-partition-forests

Given a value, the function returns a list of forests that have ranges the
  value falls into. This function reports an error if the context database
  doesn't have the range assignment policy configured.

### Signature

```xquery
xdmp:range-partition-forests(
  $value as xs:anyAtomicType
) as xs:unsignedLong*
```

### Parameters

**`$value`**
The value, for example, xs:date("2013-01-01").

### Returns

`xs:unsignedLong*`

### Examples

```xquery
xdmp:range-partition-forests(xs:date("2013-01-01"))
=> 17618760155059123769, 71876760154452113797
```

---

## xdmp:save

Serializes a node as text and saves it to a file. The node can be any
  node, including a document node, an element node, a text node, or a binary
  node.

### Signature

```xquery
xdmp:save(
  $path as xs:string,
  $node as node(),
  $options as (element()|map:map)??
) as empty-sequence()
```

### Parameters

**`$path`**
The output file pathname. The path can be fully qualified or relative.
    Relative pathnames are resolved from the directory in which
    MarkLogic Server is installed.

**`$node`**
The node to be serialized.

**`$options`** *(optional)*
Options with which to customize this operation. You 
    can specify options as either an options XML element
    in the "xdmp:save" namespace, or as a map:map. The
    options names below are XML element localnames. When using a map,
    replace the hyphens with camel casing. For example, "an-option"
    becomes "anOption" when used as a map:map key.
    This function supports the following options:
    
      output-encoding
      
      Specifies the encoding to use when saving the document.
      output-sgml-character-entities
      
      Specifies if character entities should be output upon serialization
       of the XML.  Valid values are normal, none,
       math, and pub. By default (that is, if this
       option is not specified), no SGML entities are serialized on output,
       unless the App Server is configured to output SGML character
       entities.
      
      method
      Valid values are xml, html,
       xhtml, and text. This is like the 
       corresponding part of both the XSLT 
       xsl:output 
       instruction and the MarkLogic XQuery xdmp:output prolog 
       statement.
      
      cdata-section-elements
      
      A list of space-separated
        QNames to 
       output as CDATA sections. This is like the corresponding part of both
       the XSLT xsl:output 
       instruction and the MarkLogic XQuery xdmp:output 
       prolog statement.
      
      encoding
      The encoding. This is like the corresponding part of both the XSLT 
       xsl:output 
       instruction and the MarkLogic XQuery xdmp:output prolog 
       statement.
      
      use-character-maps
      
      One or more of the following values, 
       separated by spaces.
       
       Valid values are xdmp:sgml-entities-normal,
       xdmp:sgml-entities-math, and
       xdmp:sgml-entities-pub. This is like the corresponding
       part of both the XSLT 
       
       xsl:output instruction and the MarkLogic XQuery
       xdmp:output prolog statement.
      
      media-type
      
      A mimetype representing a media type. For example,
       text/plain or application/xml (or other
       valid mimetypes). This is like the corresponding part of both the XSLT 
       xsl:output 
       instruction and the MarkLogic XQuery xdmp:output prolog 
       statement.
      
      byte-order-mark
      
      Valid values are yes or no.
       This is like the corresponding part of both the XSLT 
       xsl:output 
       instruction and the MarkLogic XQuery xdmp:output prolog 
       statement.
      
      indent
      Specifies if typed XML (that is, XML for which there is an
       in-scope schema) should be pretty-printed (indented).  Valid
       values are yes or no. This is like the 
       corresponding part of both the XSLT 
       xsl:output 
       instruction and the MarkLogic XQuery xdmp:output prolog 
       statement.
      
      indent-untyped
      
      Specifies if untyped XML (that is, XML for which there is no
       in-scope schema) should be pretty-printed (indented).  Valid
       values are yes or no.
       This is like the corresponding part of both the XSLT 
       xsl:output 
       instruction and the MarkLogic XQuery xdmp:output prolog 
       statement.
      
      indent-tabs
      
      Specifies if tab characters should be used instead of 8 consecutive
       spaces when indenting. Valid values are yes or 
       no.
      
      include-content-type
      
      Include the content-type declaration when serializing the node.
       Valid values are yes or no.
      
      escape-uri-attributes
      
      Valid values are yes or no.
       This is like the corresponding part of both the XSLT 
       xsl:output 
       instruction and the MarkLogic XQuery xdmp:output prolog 
       statement.
      
      doctype-public
      
      A public identifier, which is the public identifier to use on the
       emitted DOCTYPE.  This is like the corresponding part of both the XSLT 
       xsl:output 
       instruction and the MarkLogic XQuery xdmp:output prolog 
       statement.
      
      doctype-system
      
      A system identifier, which is the system identifier to use on the
       emitted DOCTYPE. This is like the corresponding part of both the XSLT 
       xsl:output 
       instruction and the MarkLogic XQuery xdmp:output prolog 
       statement.
      
      omit-xml-declaration
      
      Valid values are yes or no.
       This is like the corresponding part of both the XSLT 
       xsl:output 
       instruction and the MarkLogic XQuery xdmp:output prolog 
       statement.
      
      standalone
      Valid values are yes or no.
       This is like the corresponding part of both the XSLT 
       xsl:output 
       instruction and the MarkLogic XQuery xdmp:output prolog 
       statement.
      
      normalization-form
      
      Valid values are NFC, NFD, and 
       NFKD. This is like the corresponding part of both the XSLT 
       xsl:output 
       instruction and the MarkLogic XQuery xdmp:output prolog 
       statement.
      
      default-attributes
      
      Specifies whether attributes defaulted with a schema should be
       included in the serialization. Valid values are yes or 
       no. This is like the corresponding part of both the XSLT 
       xsl:output 
       instruction and the MarkLogic XQuery xdmp:output prolog 
       statement.

### Returns

`empty-sequence()`

### Examples

#### Example 1

```xquery
(: serialize an XML document in the database to a file on disk :)
let $mynode := doc("/mydocs/example.xml")
return xdmp:save("hello.txt", $text)
```

#### Example 2

```xquery
(: save a text file :)
let $text := text { "hello" }
return xdmp:save("hello.txt", $text)
```

#### Example 3

```xquery
(: save a text document stored in the database to
   disk, explicitly specifying the output encoding :)
let $pdf := doc("/mydocs/stuff.pdf")
return
xdmp:save("mystuff.txt", $txt,
    <options xmlns="xdmp:save">
      <output-encoding>utf-8</output-encoding>
    </options>)
```

#### Example 4

```xquery
(: save a text document stored in the database to
   disk, explicitly specifying the output encoding :)
let $txt := doc("/mydocs/stuff.txt")
return
xdmp:save("mystuff.txt", $txt, 
          map:map() => map:with("outputEncoding", "utf-8"))
```

---
