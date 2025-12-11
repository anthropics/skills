# Semantic Functions

55 functions in this category.

## sem:binding

Creates a sem:binding object, which is a sub-type of
  json:object (and map:map).
  This function is a built-in.

### Signature

```xquery
sem:binding(
  $map as element(json:object)?
) as sem:binding
```

### Parameters

**`$map`** *(optional)*
A serialized sem:binding object.

### Returns

`sem:binding`

### Examples

```xquery
<a>{ sem:binding() }</a>
  => <a>
  <json:object xmlns:json="http://marklogic.com/xdmp/json"
               xmlns:xsi="http://www.w3.org/2001/XMLSchema-instance"
               xmlns:xs="http://www.w3.org/2001/XMLSchema"/>
</a>
```

---

## sem:bnode

This function returns an identifier for a blank node, allowing the construction 
  of a triple that refers to a blank node.
  This XQuery function backs up the SPARQL BNODE() function.
  This function is a built-in.

### Signature

```xquery
sem:bnode(
  $value as xs:anyAtomicType?
) as sem:blank
```

### Parameters

**`$value`** *(optional)*
If provided, the same blank node identifier is returned for the same argument
    value passed to the function.

### Returns

`sem:blank`

### Examples

```xquery
xquery version "1.0-ml";
import module namespace sem = "http://marklogic.com/semantics"
      at "/MarkLogic/semantics.xqy";

let $person1 := sem:bnode()
let $person2 := sem:bnode()
let $t1 := sem:triple($person1,
         sem:iri("http://www.w3.org/1999/02/22-rdf-syntax-ns#type"),
	       sem:iri("http://xmlns.com/foaf/0.1/Person"))
let $t2 := sem:triple($person2,
	       sem:iri("http://www.w3.org/1999/02/22-rdf-syntax-ns#type"),
	       sem:iri("http://xmlns.com/foaf/0.1/Person"))
let $t3 := sem:triple($person1,
	       sem:iri("http://xmlns.com/foaf/0.1/knows"), $person2) return ($t1,$t2,$t3)

 => (: returns identifiers for blank nodes :)
sem:triple(
  sem:blank("http://marklogic.com/semantics/blank/3098376212503391907"),
  sem:iri("http://www.w3.org/1999/02/22-rdf-syntax-ns#type"),
  sem:iri("http://xmlns.com/foaf/0.1/Person"))

sem:triple(
  sem:blank("http://marklogic.com/semantics/blank/3280643260770921296"),
  sem:iri("http://www.w3.org/1999/02/22-rdf-syntax-ns#type"),
  sem:iri("http://xmlns.com/foaf/0.1/Person"))

sem:triple(
  sem:blank("http://marklogic.com/semantics/blank/3098376212503391907"),
  sem:iri("http://xmlns.com/foaf/0.1/knows"),
  sem:blank("http://marklogic.com/semantics/blank/3280643260770921296"))
```

---

## sem:coalesce

Returns the value of the first argument that evaluates without error.
  This XQuery function backs up the SPARQL COALESCE() functional form.
  This function is a built-in.

### Signature

```xquery
sem:coalesce(
  $parameter1 as item()*,
  $parameterN as item()*,...?
) as item()*
```

### Parameters

**`$parameter1`**
A value.

**`$parameterN`** *(optional)*
A value.  You can specify as many parameters as you need.

### Returns

`item()*`

### Examples

```xquery
sem:coalesce("foo", "bar", "baz");
=>
foo
```

---

## sem:curie-expand

This function expands a CURIE (Compact URI) 
		into a sem:iri object. This raises SEM-UNKNOWNPREFIX if no 
		mapping is available. For more information about the default 
		prefixes, see sem:prefixes.

### Signature

```xquery
sem:curie-expand(
  $curie as xs:string,
  $mapping as map:map?
) as sem:iri
```

### Parameters

**`$curie`**
A CURIE string.

**`$mapping`** *(optional)*
An 
	    optional set of prefix mappings. If not specified, a default 
	    set of prefixes is used.

### Returns

`sem:iri`

### Examples

```xquery
xquery version "1.0-ml"; 
 
import module namespace sem = "http://marklogic.com/semantics" 
      at "/MarkLogic/semantics.xqy";
    
sem:curie-expand("foaf:person2")
	
(: expands and returns the sem:iri object :)
=>
    http://xmlns.com/foaf/0.1/person2
```

---

## sem:curie-shorten

This function shortens an IRI into a CURIE 
		(Compact URI) into a sem:iri object. Returns the IRI string 
		unchanged if no mapping is available.

### Signature

```xquery
sem:curie-shorten(
  $iri as sem:iri,
  $mapping as map:map?
) as xs:string
```

### Parameters

**`$iri`**
An IRI.

**`$mapping`** *(optional)*
An optional 
	    set of prefix mappings. If not specified, a default set of 
	    prefixes is used.

### Returns

`xs:string`

### Examples

```xquery
xquery version "1.0-ml"; 
 
import module namespace sem = "http://marklogic.com/semantics" 
      at "/MarkLogic/semantics.xqy";
      
sem:curie-shorten(sem:iri("http://xmlns.com/foaf/0.1/person2"))

  (: shortens and returns the CURIE (Compact URI) as a string :)
  =>
foaf:person2
```

---

## sem:database-nodes

This function returns database nodes backing given triples. 
	  Any given cts:triple may be backed by zero, one, or multiple 
	  database nodes.

### Signature

```xquery
sem:database-nodes(
  $triples as sem:triple*,
  $options as xs:string*?,
  $query as cts:query??
) as node()*
```

### Parameters

**`$triples`**
The triples to locate.

**`$options`** *(optional)*
Matching options. Valid options include:
        
        
          
             =
          
	  Specify equality matching (following the rules of the 
		  $operator argument to cts:triples).
          
             sameTerm
          
	  Specify sameTerm matching (following the rules of the 
		  $operator argument to cts:triples) (if neither '=' nor 
		  'sameTerm' are specified, this option gets used by default).
	  
          
             all
          
	  Specify to return all triple-backing nodes, no matter where 
		  or in what format they occur in MarkLogic 7, only 
		  sem:triple elements are recognized as triples). 
		  If this option is not specified, only 
		  sem:triple elements found in documents that 
		  have the root element of sem:triples will be returned.
          
             quads
          
	  Specify to examine the graph component in the passed 
		  in sem:triples and use it to match.

**`$query`** *(optional)*
A cts:query to limit the scope of nodes returned.

### Returns

`node()*`

### Examples

```xquery
xquery version "1.0-ml"; 
 
import module namespace sem = "http://marklogic.com/semantics" 
      at "/MarkLogic/semantics.xqy";
 
(: this program deletes data--use with care :)
sem:database-nodes($triple-list) ! xdmp:node-delete(.)
```

---

## sem:datatype

Returns the name of the simple type of the atomic value argument as a SPARQL
  style IRI. If the value is derived from sem:unknown or sem:invalid, the datatype IRI part of those values is returned.
  This XQuery function backs up the SPARQL datatype() function.
  This function is a built-in.

### Signature

```xquery
sem:datatype(
  $value as xs:anyAtomicType
) as sem:iri
```

### Parameters

**`$value`**
The value to return the type of.

### Returns

`sem:iri`

### Examples

```xquery
sem:datatype("some string")
=>
http://www.w3.org/2001/XMLSchema#string
```

---

## sem:default-graph-iri

Returns the iri of the default graph.
  This function is a built-in.

### Returns

`sem:iri`

### Examples

```xquery
sem:default-graph-iri()
=>
http://marklogic.com/semantics#default-graph
```

---

## sem:describe

This function implements the Concise Bounded Description 
	(CBD) specification to describe one or more nodes in the graph. This 
	implementation does not provide any reified statements, and will return 
	a maximum of 9,999 triples.

### Signature

```xquery
sem:describe(
  $iris as sem:iri*
) as sem:triple*
```

### Parameters

**`$iris`**
A set of IRIs representing 
		  graph nodes.

### Returns

`sem:triple*`

### Examples

```xquery
xquery version "1.0-ml"; 
 
import module namespace sem = "http://marklogic.com/semantics" 
      at "/MarkLogic/semantics.xqy";
sem:describe(sem:iri("urn:isbn:9780080540160"))
	
=>
   	sem:triple(sem:iri("urn:isbn:9780080540160"),
	sem:iri("http://purl.org/dc/elements/1.1/title"),
	"Query XML,&#10;XQuery, XPath, and SQL/XML in context")
```

---

## sem:graph

This function returns all triples from a named graph 
		  in the database.

### Signature

```xquery
sem:graph(
  $graphname as sem:iri
) as sem:triple*
```

### Parameters

**`$graphname`**
The name of the graph to retrieve.

### Returns

`sem:triple*`

### Examples

#### Example 1

```xquery
xquery version "1.0-ml"; 
 
import module namespace sem = "http://marklogic.com/semantics" 
      at "/MarkLogic/semantics.xqy";
 
sem:graph(sem:iri("http://marklogic.com/semantics#default-graph"))
 
 => (: returns all triples from the default graph :)
```

#### Example 2

```xquery
xquery version "1.0-ml"; 
 
import module namespace sem = "http://marklogic.com/semantics" 
      at "/MarkLogic/semantics.xqy";
    sem:graph(sem:iri("bookgraph"))

 => (: returns all triples from a named graph as triples :)
 
    sem:triple(sem:iri("urn:isbn:006251587X"), 
	sem:iri("http://purl.org/dc/elements/1.1/title"),
	"Weaving the Web", sem:iri("bookgraph"))
 
    sem:triple(sem:iri("urn:isbn:9780080540160"),
    sem:iri("http://purl.org/dc/elements/1.1/title"),
	"Query XML,&#10;XQuery, XPath, and SQL/XML in context", 
	sem:iri("bookgraph"))
```

---

## sem:graph-add-permissions

Add permissions to the graph specified.
  The user must have update or insert permissions on the graph.
  This function is a built-in.

### Signature

```xquery
sem:graph-add-permissions(
  $graph as sem:iri,
  $permissions as element(sec:permission)*
) as empty-sequence()
```

### Parameters

**`$graph`**
The graph IRI.

**`$permissions`**
Security permission elements corresponding to the permissions
    for the document. If not supplied, the current user's default
    permissions are applied.  The default value used for $permissions
    can be obtained by calling xdmp:default-permissions(). A document that is
    created by a non-admin user (that is, by any user who does not have the
    admin role) must have at least one update permission,
    otherwise the creation will throw an XDMP-MUSTHAVEUPDATE
    exception.

### Returns

`empty-sequence()`

### Examples

```xquery
xquery version "1.0-ml";

sem:graph-add-permissions(sem:iri("/my/graph/"), 
  (xdmp:permission("my-role", "read"), 
   xdmp:permission("my-role", "update")))
```

---

## sem:graph-delete

This function deletes a named graph, and its graph 
	    document containing metadata, from the database. This is an update 
	    function that deletes documents with a root element of 
	    sem:triples.  All other documents are not affected.

### Signature

```xquery
sem:graph-delete(
  $graphname as sem:iri
) as empty-sequence()
```

### Parameters

**`$graphname`**
The name of the graph 
		  to delete.

### Returns

`empty-sequence()`

### Usage Notes

The default graph document is restored after you use 
  graph-delete to delete graphs.

### Examples

```xquery
xquery version "1.0-ml"; 
 
import module namespace sem = "http://marklogic.com/semantics" 
      at "/MarkLogic/semantics.xqy";
  
sem:graph-delete(sem:iri("bookgraph"))
```

---

## sem:graph-get-permissions

Get permissions to the graph specified.
  The user must have read permissions on the graph.
  This function is a built-in.

### Signature

```xquery
sem:graph-get-permissions(
  $graph as sem:iri,
  $format as xs:string?
) as element(sec:permission)*
```

### Parameters

**`$graph`**
The graph IRI.

**`$format`** *(optional)*
Specify what format the result should be in.
    It can be either "elements" or "objects".
    With "elements", the built-in returns a sequence of XML elements.
    With "objects",  the built-in returns a sequence of map:map.
    The default is "elements".

### Returns

`element(sec:permission)*`

### Examples

```xquery
xquery version "1.0-ml";
import module namespace sem = "http://marklogic.com/semantics" 
      at "/MarkLogic/semantics.xqy";
  
sem:graph-get-permissions(sem:iri("PlayerGraph"))

=>
<sec:permission xmlns:sec="http://marklogic.com/xdmp/security">
<sec:capability>read</sec:capability>
<sec:role-id>5995163769635647336</sec:role-id>
</sec:permission>

<sec:permission xmlns:sec="http://marklogic.com/xdmp/security">
<sec:capability>update</sec:capability>
<sec:role-id>5995163769635647336</sec:role-id>
</sec:permission>

(: the role ID 5995163769635647336 has read and update capability on this graph :)
```

---

## sem:graph-insert

This function inserts triples into a named graph, 
		creating the graph if necessary. It also creates the graph 
		metadata for the graph specified by the "graphname" option. 
		This is an update function that returns document IDs.

### Signature

```xquery
sem:graph-insert(
  $graphname as sem:iri,
  $triples as sem:triple*,
  $permissions as item()*?,
  $collections as xs:string*?,
  $quality as xs:int??,
  $forest-ids as xs:unsignedLong*?
) as xs:string*
```

### Parameters

**`$graphname`**
The name of 
		  the graph to insert triples into.

**`$triples`**
The set of 
		  triples to insert.

**`$permissions`** *(optional)*
Permissions to apply to the inserted documents.	    
		  When run in an XQuery context, the permissions are a 
		  sequence of XML elements (sec:permission). When importing 
		  this module into a Server-Side JavaScript context, the 
		  permissions are an array of Objects.

**`$collections`** *(optional)*
Additional collections to set on inserted 
		  documents. If you use the collections argument when inserting 
	      triples, no graph document will be created for these collections.
		  When additional collections are set, inserted triples will 
		  exist in multiple collections.

**`$quality`** *(optional)*
The quality setting to use for inserted 
		  documents.

**`$forest-ids`** *(optional)*
The forest-ids to use when inserting 
		  documents.

### Returns

`xs:string*`

### Usage Notes

Using additional collections with graph-insert 
	  in the context of SPARQL Update can result in undefined behavior.

### Examples

#### Example 1

```xquery
xquery version "1.0-ml"; 
 
import module namespace sem = "http://marklogic.com/semantics" 
      at "/MarkLogic/semantics.xqy";
     
sem:graph-insert(sem:iri('bookgraph'), 
   sem:triple(sem:iri('urn:isbn:9780080540160'),
              sem:iri('http://purl.org/dc/elements/1.1/title'), 
              "Query XML,XQuery, XPath, and SQL/XML in context"))
			 
=>
    /triplestore/2c78915c5854b0f8.xml
```

#### Example 2

```xquery
xquery version "1.0-ml"; 
 
import module namespace sem = "http://marklogic.com/semantics" 
   at "/MarkLogic/semantics.xqy";

 let $string := '
    <urn:isbn:006251587X> <http://purl.org/dc/elements/1.1/creator>
    <http://www.w3.org/People/Berners-Lee/card#i> .
    <urn:isbn:006251587X> <http://purl.org/dc/elements/1.1/title> 
	"Weaving the Web" .
    <http://www.w3.org/People/Berners-Lee/card#i> 
    <http://www.w3.org/2006/vcard/title>"Director" .'

 let $triples := sem:rdf-parse($string, "ntriple")
 let $i := sem:graph-insert(sem:iri("bookgraph"), $triples, (), "smGraph")
 return(fn:collection("smGraph")//sem:triple);
			 
=> (: returns triples as nodes :)
 <sem:triple xmlns:sem="http://marklogic.com/semantics">
   <sem:subject>urn:isbn:006251587X</sem:subject>
   <sem:predicate>http://purl.org/dc/elements/1.1/creator</sem:predicate>
   <sem:object>http://www.w3.org/People/Berners-Lee/card#i</sem:object>
 </sem:triple>
 <sem:triple xmlns:sem="http://marklogic.com/semantics">
   <sem:subject>urn:isbn:006251587X</sem:subject>
   <sem:predicate>http://purl.org/dc/elements/1.1/title</sem:predicate>
   <sem:object datatype="http://www.w3.org/2001/XMLSchema#string">
    Weaving the Web</sem:object>
 </sem:triple>
 <sem:triple xmlns:sem="http://marklogic.com/semantics">
   <sem:subject>http://www.w3.org/People/Berners-Lee/card#i</sem:subject>
   <sem:predicate>http://www.w3.org/2006/vcard/title</sem:predicate>
   <sem:object datatype="http://www.w3.org/2001/XMLSchema#string">
   Director</sem:object>
 </sem:triple>
 <sem:triple xmlns:sem="http://marklogic.com/semantics">
   <sem:subject>urn:isbn:9780080540160</sem:subject>
   <sem:predicate>http://purl.org/dc/elements/1.1/title</sem:predicate>
   <sem:object datatype="http://www.w3.org/2001/XMLSchema#string">
   Query XML,XQuery, XPath, and SQL/XML in context</sem:object>
 </sem:triple>
```

---

## sem:graph-remove-permissions

Remove permissions from the graph specified.
  The user must have update permissions on the graph.
  This function is a built-in.

### Signature

```xquery
sem:graph-remove-permissions(
  $graph as sem:iri,
  $permissions as element(sec:permission)*
) as empty-sequence()
```

### Parameters

**`$graph`**
The graph IRI.

**`$permissions`**
Security permission elements corresponding to the permissions
    for the document. If not supplied, the current user's default
    permissions are applied.  The default value used for $permissions
    can be obtained by calling xdmp:default-permissions(). A document that is
    created by a non-admin user (that is, by any user who does not have the
    admin role) must have at least one update permission,
    otherwise the creation will throw an XDMP-MUSTHAVEUPDATE
    exception.

### Returns

`empty-sequence()`

### Examples

```xquery
xquery version "1.0-ml";
import module namespace sem = "http://marklogic.com/semantics" 
      at "/MarkLogic/semantics.xqy";
	  
let $perms := xdmp:default-permissions("graphs/MyDemoGraph2")
return 
sem:graph-remove-permissions(sem:iri("MyGraph"),($perms))
```

---

## sem:graph-set-permissions

Set permissions to the graph specified.
  The user must have update permissions on the graph.
  This function is a built-in.

### Signature

```xquery
sem:graph-set-permissions(
  $graph as sem:iri,
  $permissions as element(sec:permission)*
) as empty-sequence()
```

### Parameters

**`$graph`**
The graph IRI.

**`$permissions`**
Security permission elements corresponding to the permissions
    for the document. If not supplied, the current user's default
    permissions are applied.  The default value used for $permissions
    can be obtained by calling xdmp:default-permissions(). A document that is
    created by a non-admin user (that is, by any user who does not have the
    admin role) must have at least one update permission,
    otherwise the creation will throw an XDMP-MUSTHAVEUPDATE
    exception.

### Returns

`empty-sequence()`

### Examples

```xquery
xquery version "1.0-ml";
import module namespace sem = "http://marklogic.com/semantics" 
      at "/MarkLogic/semantics.xqy";
	
sem:graph-set-permissions((sem:iri("graphs/MyDemoGraph")),
(
    xdmp:permission( "demo-reader", "read" ),
    xdmp:permission( "demo-writer", "update"  )
  )
 )
```

---

## sem:if

The IF function form evaluates the first argument, interprets it as a
  effective boolean value, then returns the value of expression2 if the EBV is
  true, otherwise it returns the value of expression3. Only one of expression2
  and expression3 is evaluated. If evaluating the first argument raises an
  error, then an error is raised for the evaluation of the IF expression.
  This XQuery function backs up the SPARQL IF() functional form.
  This function is a built-in.

### Signature

```xquery
sem:if(
  $condition as xs:boolean,
  $then as item()*,
  $else as item()*
) as item()*
```

### Parameters

**`$condition`**
The condition.

**`$then`**
The then expression.

**`$else`**
The else expression.

### Returns

`item()*`

### Examples

```xquery
sem:if( fn:true(), "This is true", "This is not true")
=>
This is true
```

---

## sem:in-memory-store

Returns a sem:store constructor that queries from the sequence 
  of sem:triple values passed in as an argument. The 
  sem:store constructor returned from this function will raise an 
  error if it is passed as part of the options argument to a call to 
  sem:sparql-update().
  
  The default rulesets configured on the current database have no effect on a
  sem:store constructor created with sem:in-memory-store().
  
  
  This should be used along with sem:sparql() in preference to the
  deprecated sem:sparql-triples() function. We will remove documentation
  of sem:sparql-triples(), but leave the function for backwards
  compatibility.
  
  This function is a built-in.

### Signature

```xquery
sem:in-memory-store(
  $dataset as sem:triple*
) as sem:store
```

### Parameters

**`$dataset`**
A set of triple values representing the dataset for the
    store.
    The results from a SPARQL construct query or call to sem:rdf-parse()
    can be used directly as the value for this argument.

### Returns

`sem:store`

### Examples

```xquery
xquery version "1.0-ml";

import module namespace sem = "http://marklogic.com/semantics"
      at "/MarkLogic/semantics.xqy";

let $turtle-document := '
    @prefix rdf: <http://www.w3.org/1999/02/22-rdf-syntax-ns#> .
    @prefix dc: <http://purl.org/dc/elements/1.1/> .
    @prefix ex: <http://example.org/people/1.0/> .
  <http://www.w3.org/TR/rdf-syntax-grammar>
    dc:title "RDF/XML Syntax Specification (Revised)" ;
    ex:editor [
      ex:fullname "Dave Beckett";
      ex:homePage <http://purl.org/net/dajobe/>
    ] .'
let $triples := sem:rdf-parse($turtle-document, ("turtle", "repair") )
return
sem:in-memory-store($triples)
=>
sem:store() :  Use the value to pass into a function that
requires a sem:store (like sem:sparql-update).
```

---

## sem:invalid

Returns a sem:invalid value with the given literal value and 
  datatype IRI. The sem:invalid type extends xs:untypedAtomic,
  and represents an RDF value whose literal string is invalid according to the 
  schema for it's datatype.
  This function is a built-in.

### Signature

```xquery
sem:invalid(
  $string as xs:string,
  $datatype as sem:iri
) as sem:invalid
```

### Parameters

**`$string`**
The lexical value.

**`$datatype`**
The datatype IRI.

### Returns

`sem:invalid`

### Examples

```xquery
xdmp:describe(sem:invalid("invalid value", sem:iri("string")))
=>
sem:invalid("invalid value", sem:iri("string"))
```

---

## sem:invalid-datatype

Returns the datatype IRI of a sem:invalid value.
  This function is a built-in.

### Signature

```xquery
sem:invalid-datatype(
  $val as sem:invalid
) as sem:iri
```

### Parameters

**`$val`**
The sem:invalid value.

### Returns

`sem:iri`

### Examples

```xquery
sem:invalid-datatype(sem:invalid("invalid value", sem:iri("string")))
=>
string (as a sem:iri)
```

---

## sem:iri

This is a constructor function that takes a string
		and constructs an item of type sem:iri
		 from it.

### Signature

```xquery
sem:iri(
  $string-iri as xs:string
) as sem:iri
```

### Parameters

**`$string-iri`**
The string with which to construct the 
			sem:iri.

### Returns

`sem:iri`

### Usage Notes

When using sem:iri
    with 
   SPARQL or SPARQL Update, don't use < and > 
   around the iri string. For example, 
   sem:iri("my iri").

### Examples

```xquery
xquery version "1.0-ml"; 
 
sem:iri("/my/iri")
```

---

## sem:isBlank

Returns true if the argument is an RDF blank node - that is, derived from
  type sem:blank.
  This XQuery function backs up the SPARQL isBlank() function.
  This function is a built-in.

### Signature

```xquery
sem:isBlank(
  $value as xs:anyAtomicType
) as xs:boolean
```

### Parameters

**`$value`**
The value to test.

### Returns

`xs:boolean`

### Examples

```xquery
sem:isBlank(sem:bnode())
=>
true
```

---

## sem:isIRI

Returns true if the argument is an RDF IRI - that is, derived from
  type sem:iri, but not derived from type sem:blank.
  This XQuery function backs up the SPARQL isIRI() and isURI() functions.
  This function is a built-in.

### Signature

```xquery
sem:isIRI(
  $value as xs:anyAtomicType
) as xs:boolean
```

### Parameters

**`$value`**
The value to test.

### Returns

`xs:boolean`

### Examples

```xquery
xquery version "1.0-ml";
import module namespace sem = "http://marklogic.com/semantics" at "MarkLogic/semantics.xqy";

let $triple := sem:triple(sem:iri("subject"), sem:iri("predicate"), "object", sem:iri("foo"))

return
  sem:isIRI(sem:triple-subject($triple))

 => (: Returns fn:true. :)
```

---

## sem:isLiteral

Returns true if the argument is an RDF literal - that is, derived from
  type xs:anyAtomicType, but not derived from type sem:iri.
  This XQuery function backs up the SPARQL isLiteral() function.
  This function is a built-in.

### Signature

```xquery
sem:isLiteral(
  $value as xs:anyAtomicType
) as xs:boolean
```

### Parameters

**`$value`**
The value to test.

### Returns

`xs:boolean`

### Examples

```xquery
sem:isLiteral("subject text")
=>
true
```

---

## sem:isNumeric

Returns true if the argument is a valid numeric RDF literal.
  This XQuery function backs up the SPARQL isNumeric() function.
  This function is a built-in.

### Signature

```xquery
sem:isNumeric(
  $value as xs:anyAtomicType
) as xs:boolean
```

### Parameters

**`$value`**
The value to test.

### Returns

`xs:boolean`

### Examples

```xquery
sem:isNumeric(51)
=>
true
```

---

## sem:lang

Returns the language of the value passed in, or the empty string if the 
  value has no language. Only values derived from rdf:langString have a 
  language. This XQuery function backs up the SPARQL lang() function.
  This function is a built-in.

### Signature

```xquery
sem:lang(
  $value as xs:anyAtomicType
) as xs:string
```

### Parameters

**`$value`**
The value to return the language of.

### Returns

`xs:string`

### Examples

```xquery
sem:lang("hello")
=>
empty (because the term has no language value)
```

---

## sem:langMatches

Returns true if $lang-tag matches $lang-range 
  according to the basic filtering scheme defined in RFC4647.
  This XQuery function backs up the SPARQL langMatches() function.
  This function is a built-in.

### Signature

```xquery
sem:langMatches(
  $lang-tag as xs:string,
  $lang-range as xs:string
) as xs:boolean
```

### Parameters

**`$lang-tag`**
The language tag.

**`$lang-range`**
The language range.

### Returns

`xs:boolean`

### Examples

```xquery
let $triple := sem:triple(sem:iri("subject"), sem:iri("predicate"), "object")
return
sem:langMatches(sem:triple-subject($triple), "fr")
=>
false
```

---

## sem:prefixes

This function returns a set of prefix mappings for 
		use with CURIE processing. Calling this function returns the 
		internal set of default prefixes. The default mappings include 
		prefixes that are widely used and agreed upon, including 
		"cc" (Creative Commons), "dc" (Dublin Core), 
		"dcterms" (Dublin Core Terms), "dbpedia" (dbpedia resources), 
		"dbpedia-owl" (dbpedia ontology), "geonames" (geonames 
		ontology), "foaf" (FOAF), "media" (MediaRSS), "owl" (OWL), "
		rdf" (RDF), "product" (productV2), "rdfs" (RDF Schema), 
		"skos" (SKOS), "vcard" (VCard vocab), "void" (Vocabulary 
		of Interlinked Datasets), "wikidata" (wikidata entities), 
		"xhtml" (XHTML), and "xs" (XML Schema).

### Signature

```xquery
sem:prefixes(
  $prefixdef as xs:string?,
  $include-common as xs:boolean??
) as map:map
```

### Parameters

**`$prefixdef`**
A string specifying 
		  prefixes in RDFa @prefix format 
		  ("prefix: http://base1 prefix2: http://base2").

**`$include-common`** *(optional)*
Whether to include the default set of 
		  mappings. The default is true.

### Returns

`map:map`

### Examples

```xquery
xquery version "1.0-ml"; 
 
import module namespace sem = "http://marklogic.com/semantics" 
   at "/MarkLogic/semantics.xqy";

let $prefixes := sem:prefixes("ex: http://www.example.com/# 
               schema: http://schema.org/")
return sem:curie-expand("ex:prefLabel", $prefixes)
	
=>  (: returns an IRI :)
    <http://www.example.com/#prefLabel>
```

---

## sem:query-results-serialize

This function implements the W3C SPARQL Query Results 
	format. Any value sequence returned by sem:sparql can 
	be passed into this function. The result will be the W3C SPARQL 
	Results format, in either XML or JSON format.

### Signature

```xquery
sem:query-results-serialize(
  $results as option,
  $options as xs:string*?
) as query-results-serialize($results)
```

### Parameters

**`$results`**
The results of calling a SPARQL query.

**`$options`** *(optional)*
One of 'xml' (default) or 'json'.

### Returns

`query-results-serialize($results)`

### Examples

```xquery
xquery version "1.0-ml"; 
 
import module namespace sem = "http://marklogic.com/semantics" 
      at "/MarkLogic/semantics.xqy";
    
sem:query-results-serialize(sem:sparql('
    PREFIX foaf: <http://xmlns.com/foaf/0.1/>
    SELECT ?name WHERE { ?alum foaf:schoolHomepage <http://www.ucsb.edu/> .
                         ?alum foaf:knows ?person .
                         ?person foaf:name ?name }
'))

=>
  <sparql xmlns="http://www.w3.org/2005/sparql-results#">
    <head>
      <variable name="name">
      </variable>
    </head>
    <results>
      <result>
        <binding name="name">
           <literal datatype="http://www.w3.org/2001/XMLSchema#string">
            Karen Schouten
           </literal>
        </binding>
      </result>
      <result>
        <binding name="name">
           <literal datatype="http://www.w3.org/2001/XMLSchema#string">
           Nick Aster
           </literal>
        </binding>
      </result>
    </results>
  </sparql>
```

---

## sem:random

Returns a random double between 0 and 1.
  This XQuery function backs up the SPARQL RAND() function.
  This function is a built-in.

### Returns

`xs:double`

### Examples

```xquery
sem:random()
=>
0.462153059928251
```

---

## sem:rdf-builder

This function returns a function that builds triples 
		from CURIE and blank node syntax. The resulting function takes 
		three string arguments, representing subject, predicate, 
		and object respectively, which returns a sem:triple object 
		using the graph and prefix mappings passed in to the call to 
		sem:rdf-builder. 
		Blank nodes specified with a leading underscore (_) will 
		be assigned blank node identifiers, and will maintain that 
		identity across multiple invocations; for example, 
		"_:person1" will refer to the same node as a later 
		invocation that also mentions "_:person1". In the 
		predicate position, the special value of "a" will be 
		interpreted as the same as "rdf:type".

### Signature

```xquery
sem:rdf-builder(
  $prefixes as map:map??,
  $graph as sem:iri??
) as function(item(),item(),item()) as sem:triple
```

### Parameters

**`$prefixes`** *(optional)*
An 
		  optional set of prefix mappings.

**`$graph`** *(optional)*
The graph 
		  value in which to place triples. Defaults to 
		  "http://marklogic.com/semantics#default-graph".

### Returns

`function(item(),item(),item()) as sem:triple`

### Usage Notes

If you pass in a string to sem:rdf-builder, it will be 
	  interpreted as a CURIE. If you want it to be interpreted as an IRI, 
	  then cast the string to an IRI using sem:iri.

### Examples

#### Example 1

```xquery
xquery version "1.0-ml"; 
 
import module namespace sem = "http://marklogic.com/semantics" 
      at "/MarkLogic/semantics.xqy";
      
let $fac := sem:rdf-builder()
let $triple := $fac("foaf:person1", "foaf:knows", "foaf:person2")
return <result>{$triple}</result> 
	
=>
<result>
  <sem:triple xmlns:sem="http://marklogic.com/semantics">
     <sem:subject>http://xmlns.com/foaf/0.1/person1</sem:subject>
     <sem:predicate>http://xmlns.com/foaf/0.1/knows</sem:predicate>
     <sem:object>http://xmlns.com/foaf/0.1/person2</sem:object>
  </sem:triple>
</result>
```

#### Example 2

```xquery
xquery version "1.0-ml"; 
 
import module namespace sem = "http://marklogic.com/semantics" 
      at "/MarkLogic/semantics.xqy";

let $fac := sem:rdf-builder()
let $t1 := $fac("_:person1", "a", "foaf:Person") 
let $t2 := $fac("_:person2", "a", "foaf:Person") 
let $t3 := $fac("_:person1", "foaf:knows", "_:person2") 
return ($t1,$t2,$t3)
 
	
=>
sem:triple(
  sem:blank("http://marklogic.com/semantics/blank/3655782280846814211"),
  sem:iri("http://www.w3.org/1999/02/22-rdf-syntax-ns#type"),
  sem:iri("http://xmlns.com/foaf/0.1/Person"))

sem:triple(
  sem:blank("http://marklogic.com/semantics/blank/1129346327653055324"),
  sem:iri("http://www.w3.org/1999/02/22-rdf-syntax-ns#type"),
  sem:iri("http://xmlns.com/foaf/0.1/Person"))
 
sem:triple(
  sem:blank("http://marklogic.com/semantics/blank/3655782280846814211"),
  sem:iri("http://xmlns.com/foaf/0.1/knows"),
  sem:blank("http://marklogic.com/semantics/blank/1129346327653055324"))
```

---

## sem:rdf-get

This function returns sem:triples from a specified location.

### Signature

```xquery
sem:rdf-get(
  $location as xs:string,
  $options as xs:string*?,
  $http-opts as element()??
) as sem:triple*
```

### Parameters

**`$location`**
The location of the document.

**`$options`** *(optional)*
Parsing options.  Valid options include:
	
        
          
             base=URI
          
        
        A base URI to use during parsing.
		
          
             graph=URI
          
        
		The graph/context value to give to quads with no 
		explicit graph specified in the data.  Cannot be used with
		override-graph=URI (or an exception is thrown).
		
          
             override-graph=URI
          
        
		The graph/context value to give to every quad, whether 
		specified in the data or not.  Cannot be used with
		graph-URI (or an exception is thrown).
        
          
             ntriple
          
        		
        Specify N-Triples format for input.
        
          
             nquad
          
        		
        Specify N-Quads format for input (default). 
		
          
             turtle
          
        	
        Specify Turtle format for input. 
		
          
             rdfxml
          
        	
        Specify RDF/XML format for input.
	    
          
             rdfjson
          
        	
        Specify RDF/JSON format for input. 
        
          
             n3
          
        		
        Specify N3 format for input.
        
		
             trig
          
        		
        Specify TriG format for input.
        
          
             repair
          
        			
		Specify to repair if possible, or discard individual triples 
		that do not parse correctly. Otherwise any malformed input 
		results in an exception.
  
           
             triplexml
          
        
                Specify sem:triple XML format for input, either a 
		single sem:triple element or multiple elements 
		under a root element.  If you use the triplexml
		option, you cannot specify a graph.

**`$http-opts`** *(optional)*
An options node as described for the function 
		xdmp:http-get.

### Returns

`sem:triple*`

### Examples

```xquery
xquery version "1.0-ml"; 
 
import module namespace sem = "http://marklogic.com/semantics" 
      at "/MarkLogic/semantics.xqy";
 
sem:rdf-get('C:/Data/Semantics/example.ttl', "turtle")
	
=> 
    sem:triple(sem:iri("http://example.com/ns/data#item342"),
	sem:iri("http://example.com/ns/details#shipped"), xs:date("2013-05-20"))
    
    sem:triple(sem:iri("http://example.com/ns/data#item342"),
	sem:iri("http://example.com/ns/details#quantity"), 4)
    
    sem:triple(sem:iri("http://example.com/ns/data#item342"),
	sem:iri("http://example.com/ns/details#invoiced"), fn:false())
     
    sem:triple(sem:iri("http://example.com/ns/data#item342"),
	sem:iri("http://example.com/ns/details#costPerItem"), 10.5)
```

---

## sem:rdf-insert

This function inserts triples into a specified database as 
		 one or more sem:triples documents. It also 
		 creates graph metadata for the graph specified by the 
		 "graph" or "override-graph=URI" option. 
		 This is an update function that returns the document URIs of 
		 inserted documents.

### Signature

```xquery
sem:rdf-insert(
  $triples as sem:triple*,
  $options as xs:string*?,
  $permissions as element?,
  $collections as xs:string*?,
  $quality as xs:int??,
  $forest-ids as xs:unsignedLong*?
) as xs:string*
```

### Parameters

**`$triples`**
The triples to insert.

**`$options`** *(optional)*
Insertion options. Valid options values include:
	
        
          
             override-graph=URI
          
        
		The graph/context value to give to every quad, whether 
		specified in the data or not.
		
		  
             directory=URI
          
        
        The database directory path.

**`$permissions`** *(optional)*
Security permission elements corresponding to the permissions 
	        for the document.

**`$collections`** *(optional)*
Additional collections to set on inserted documents. If you use 
		the collections argument when inserting triples, no graph 
		document will be created for these collections.

**`$quality`** *(optional)*
The quality setting for inserted documents.

**`$forest-ids`** *(optional)*
The forest IDs to use for inserted documents.

### Returns

`xs:string*`

### Usage Notes

Using additional collections with sem:rdf-insert in the 
	  context of SPARQL Update can result in undefined behavior.

### Examples

```xquery
xquery version "1.0-ml"; 
 
import module namespace sem = "http://marklogic.com/semantics" 
      at "/MarkLogic/semantics.xqy";

sem:rdf-insert(sem:triple(sem:iri("http://example.com/ns/directory#m"),
	sem:iri("http://example.com/ns/person#firstName"), "Michael"))
 
 =>
   /triplestore/74521a908ece2074.xml
```

---

## sem:rdf-load

This function inserts an RDF document from a specified location
		into the designated database. It also creates the graph 
		metadata for the graph specified by the "graph=URI" or 
		"override-graph=URI" option.
		This is an update function that returns the document URIs of 
		inserted documents.

### Signature

```xquery
sem:rdf-load(
  $location as xs:string,
  $options as xs:string*?,
  $http-opts as element()??,
  $permissions as item()*?,
  $collections as xs:string*?,
  $quality as xs:int??,
  $forest-ids as xs:unsignedLong*?
) as xs:string*
```

### Parameters

**`$location`**
The location of the input file. If the file is not a 
		  recognized format, an exception is thrown.

**`$options`** *(optional)*
Parsing options: Only one base, or graph, or override-graph 
	    option along with one format option (ntriple, nquad, turtle, 
	    trig, n3, rdfxml, or rdfjson) is allowed. The graph and 
	    override-graph options cannot be used together. Valid options 
	    include:
	
        
          
             base=URI
          
        
        A base URI to use during parsing.
		
          
             graph=URI
          
        
		The graph/context value to give to quads with no 
		explicit graph specified in the data. Cannot be used with
		override-graph=URI (or an exception is thrown).
		
          
             override-graph=URI
          
        
		The graph/context value to give to every quad, 
		whether specified in the data or not. Cannot be used with
		graph=URI (or an exception is thrown).
        
		  
             directory=URI
          
        
        The database directory path.
		
          
             ntriple
          
        		
        Specify N-Triples format for input.
        
          
             nquad
          
        		
        Specify N-Quads format for input (default). 
		
          
             turtle
          
        	
        Specify Turtle format for input. 
		
          
             rdfxml
          
        	
        Specify RDF/XML format for input.
	    
          
             rdfjson
          
        	
        Specify RDF/JSON format for input. 
        
		 
             triplexml
         
        	
		Specify sem:triple XML format for input, either a 
		single sem:triple element or multiple elements 
		under a root element.  If you use the triplexml
		option, you cannot specify a graph.
        
          
             n3
          
        		
        Specify N3 format for input.
        
		
             trig
          
        		
        Specify TriG format for input.
        
          
             repair
          
        			
		Specify to repair if possible, or discard individual triples 
		that do not parse correctly. Otherwise any malformed input 
		results in an exception.

**`$http-opts`** *(optional)*
An options node as described for the function 
		xdmp:http-get.

**`$permissions`** *(optional)*
Permissions to apply to the inserted documents.
                When run in an XQuery context, the permissions are a sequence of
	        XML elements (sec:permission). When importing this module into 
	        a Server-Side JavaScript context, the permissions are an array
	        of Objects.

**`$collections`** *(optional)*
Additional collections to set on inserted documents. If you use the 
		collections argument when inserting triples, no graph document 
		will be created for these collections.

**`$quality`** *(optional)*
The quality setting for inserted documents.

**`$forest-ids`** *(optional)*
The forest-ids to use for inserted documents.

### Returns

`xs:string*`

### Usage Notes

Using additional collections with sem:rdf-load 
    in the context of SPARQL Update can result in undefined behavior.

### Examples

#### Example 1

```xquery
xquery version "1.0-ml"; 
 
import module namespace sem = "http://marklogic.com/semantics" 
      at "/MarkLogic/semantics.xqy";
 
sem:rdf-load('C:/data/example.rdf', "rdfxml")
 
 => 
    /triplestore/fbd28af1471b39e9.xml
```

#### Example 2

```xquery
xquery version "1.0-ml"; 
 
import module namespace sem = "http://marklogic.com/semantics" 
      at "/MarkLogic/semantics.xqy";
	  
sem:rdf-load(
    'C:/data/books.ttl',
    ("turtle", "graph=http://marklogic.com/semantics/sb/books1/"),
    (),
    xdmp:permission("demo-reader", "read")
    )
	
=>
    /triplestore/fbd28af1471b39e9.xml
  (: permissions on graph for demo-reader now set to "read" :)
```

---

## sem:rdf-parse

This function returns parsed sem:triple objects 
		from a text format or XML.

### Signature

```xquery
sem:rdf-parse(
  $in as item(),
  $options as xs:string*?
) as sem:triple*
```

### Parameters

**`$in`**
The source to parse. This must either be a string or a 
		  node.

**`$options`** *(optional)*
Parsing options. Only one each of the base, graph, 
		  override-graph, and format (ntriple, nquad, turtle, rdfxml, 
		  rdfjson, triplexml) options is allowed. Valid options 
		  include:
	
        
          
             base=URI
          
        
        A base URI to use during parsing.
		
          
             graph=URI
          
        
		The graph/context value to give to quads with no explicit graph 
		specified in the data. Cannot be used with
		override-graph=URI (or an exception is thrown).
		
          
             override-graph=URI
          
        
		The graph/context value to give to every quad, whether 
		specified in the data or not.  Cannot be used with
		graph=URI (or an exception is thrown).
        
          
             ntriple
          
        		
        Specify N-Triples format for input.
        
          
             nquad
          
        		
		Specify N-Quads format for input (default if the $in 
		paramater is a string). 
		
          
             turtle
          
        	
        Specify Turtle format for input. 
		
          
             rdfxml
          
        	
		Specify RDF/XML format for input (default if the $in 
		parameter is an element).
	    
		
             n3
          
        		
        Specify N3 format for input.
        
		
             trig
          
        		
        Specify TriG format for input.
        
          
             rdfjson
          
        	
        Specify RDF/JSON format for input. 
        
          
             triplexml
          
        	
		Specify sem:triple XML format for input, either a 
		single sem:triple element or multiple elements 
		under a root element.  If you use the triplexml
		option, you cannot specify a graph.
        
          
             repair
          
        			
		Specify to repair if possible, or discard individual 
		triples that do not parse correctly. Otherwise any 
		malformed input results in an exception.

### Returns

`sem:triple*`

### Examples

#### Example 1

```xquery
xquery version "1.0-ml"; 
 
import module namespace sem = "http://marklogic.com/semantics" 
      at "/MarkLogic/semantics.xqy";
declare namespace rdf="http://www.w3.org/1999/02/22-rdf-syntax-ns#";
declare namespace dc = "http://purl.org/dc/elements/1.1/";
declare namespace v="http://www.w3.org/2006/vcard/";

sem:rdf-parse(
<rdf:Description rdf:about="urn:isbn:006251587X">
  <dc:title>Weaving the Web</dc:title>
  <dc:creator rdf:resource="http://www.w3.org/People/Berners-Lee/card#i"/>
</rdf:Description>,
"rdfxml")	  
 
 => 
sem:triple(
  sem:iri("urn:isbn:006251587X"), 
  sem:iri("http://purl.org/dc/elements/1.1/title"), 
  "Weaving the Web")
	
sem:triple(
  sem:iri("urn:isbn:006251587X"), 
  sem:iri("http://purl.org/dc/elements/1.1/creator"), 
  sem:iri("http://www.w3.org/People/Berners-Lee/card#i"))
```

#### Example 2

```xquery
xquery version "1.0-ml"; 
 
import module namespace sem = "http://marklogic.com/semantics" 
      at "/MarkLogic/semantics.xqy";
      
let $turtle-document := '
    @prefix rdf: <http://www.w3.org/1999/02/22-rdf-syntax-ns#> .
    @prefix dc: <http://purl.org/dc/elements/1.1/> .
    @prefix ex: <http://example.org/people/1.0/> .
  <http://www.w3.org/TR/rdf-syntax-grammar>
    dc:title "RDF/XML Syntax Specification (Revised)" ;
    ex:editor [
      ex:fullname "Dave Beckett";
      ex:homePage <http://purl.org/net/dajobe/>
    ] .'
return sem:rdf-parse($turtle-document, ("turtle", "repair") )

=>  
sem:triple(
  sem:iri("http://www.w3.org/TR/rdf-syntax-grammar"), 
  sem:iri("http://purl.org/dc/elements/1.1/title"), 
  "RDF/XML Syntax Specification (Revised)")
	
sem:triple(
  sem:iri("http://www.w3.org/TR/rdf-syntax-grammar"), 
  sem:iri("http://example.org/people/1.0/editor"),
  sem:blank("http://marklogic.com/semantics/blank/15118066541381804840"))
	
sem:triple(
  sem:blank("http://marklogic.com/semantics/blank/15118066541381804840"),
  sem:iri("http://example.org/people/1.0/fullname"), 
  "Dave Beckett")

sem:triple(
  sem:blank("http://marklogic.com/semantics/blank/15118066541381804840"),
  sem:iri("http://example.org/people/1.0/homePage"),
  sem:iri("http://purl.org/net/dajobe/"))
```

---

## sem:rdf-serialize

This function returns a string or json or XML serialization 
		of the provided triples.

### Signature

```xquery
sem:rdf-serialize(
  $triples as sem:triple*,
  $options as xs:string*?
) as item()
```

### Parameters

**`$triples`**
The triples to serialize.

**`$options`** *(optional)*
Parsing options. Only one of the format options is allowed. 
		  Valid option values include:
	
        
           
             ntriple
          
        
		Specify N-Triples format for output as an xs:string.
		
		    
             nquad
          
        
        Specify N-Quads format for output as an xs:string (default).
		
		    
             turtle
          
        
        Specify Turtle format for output as an xs:string.
		
		    
             rdfxml
          
        
        Specify RDF/XML format for output as an element.
        
		    
             rdfjson
          
        
		Specify JSON format for output as a json:object. Note: To 
		serialize a JSON string, manually call 
		xdmp:to-json on this object.
		    
		    
             n3
          
        		
        Specify N3 format for output as an xs:string.
        
		
             trig
          
        		
        Specify TriG format for output as an xs:string.
        
          
             triplexml
          
        
                Specify sem:triple XML format for output, either a 
		single sem:triple element or multiple elements 
		under a root element.  If you use the triplexml
		option, you cannot specify a graph.

### Returns

`item()`

### Examples

#### Example 1

```xquery
xquery version "1.0-ml"; 
 
import module namespace sem = "http://marklogic.com/semantics" 
      at "/MarkLogic/semantics.xqy";

sem:rdf-serialize(
  (sem:triple(
     sem:iri("http://example.com/ns/directory#m"),
     sem:iri("http://example.com/ns/person#firstName"), "Michelle")))

=> 
    <http://example.com/ns/directory#m> 
	<http://example.com/ns/person#firstName> "Michelle" .
```

#### Example 2

```xquery
xquery version "1.0-ml"; 
 
import module namespace sem = "http://marklogic.com/semantics" 
      at "/MarkLogic/semantics.xqy";
      
sem:rdf-serialize(
    sem:triple(sem:iri("http://example.com/ns/directory#m"),
	sem:iri("http://example.com/ns/person#firstName"),
	"Michelle"), "rdfxml")

=>
<rdf:RDF xmlns:rdf="http://www.w3.org/1999/02/22-rdf-syntax-ns#">
    <rdf:Description rdf:about="http://example.com/ns/directory#m">
      <firstName rdf:datatype="http://www.w3.org/2001/XMLSchema#string" 
        xmlns="http://example.com/ns/person#">Michelle
      </firstName>
    </rdf:Description>
</rdf:RDF>
```

---

## sem:ruleset-store

The sem:ruleset-store function returns a set of triples derived 
  by applying the ruleset to the triples in the sem:store constructor 
  provided in $store ("the triples that can be inferred from 
  these rules").
  
  If graph URIs are included with a sem:sparql query that includes
  sem:ruleset-store, the query will include "triples in the $store
  that are also in these graphs".
  
  This function is a built-in.

### Signature

```xquery
sem:ruleset-store(
  $locations as xs:string*,
  $store as sem:store*?,
  $options as xs:string*?
) as sem:store
```

### Parameters

**`$locations`**
The locations of the rulesets.

**`$store`** *(optional)*
The base store(s) over which to apply the ruleset to get inferred triples. The 
	default for sem:store is an empty sequence, which means 
	accessing the current database's triple index using the default rulesets
	configured for that database.

**`$options`** *(optional)*
Options as a sequence of string values. Available options are:
    
    "size=number of MB"
    The maximum size of the memory used to cache inferred triples. This 
    defaults to the default inference size set for the app-server. If the 
    value provided is bigger than the maximum inference size set for the 
    App Server, an error is raised [XDMP-INFSIZE].

### Returns

`sem:store`

### Examples

```xquery
xquery version "1.0-ml";

import module namespace sem = "http://marklogic.com/semantics" 
      at "/MarkLogic/semantics.xqy";     

let $store := sem:store((), cts:word-query("Alfa Romeo"))
return
sem:ruleset-store("my-location", $store)
=>
Returns a sem:store() derived from specified triples using
the specified ruleset.
```

---

## sem:sameTerm

Returns true if the arguments are the same RDF term as defined by
  the RDF concepts specification.
  This XQuery function backs up the SPARQL sameTerm() function.
  This function is a built-in.

### Signature

```xquery
sem:sameTerm(
  $a as xs:anyAtomicType*,
  $b as xs:anyAtomicType*
) as xs:boolean
```

### Parameters

**`$a`**
The first value to test.

**`$b`**
The second value to test.

### Returns

`xs:boolean`

### Examples

```xquery
sem:sameTerm("hello", "goodbye")
=>
false
```

---

## sem:sparql

Executes a SPARQL query against the database.
  SPARQL "SELECT" queries return a solution as a sequence of map objects
  in the form of a table, where each map represents a set of bindings that
  satisfies the query.
  SPARQL "CONSTRUCT" queries return triples as a sequence of
  sem:triple values in an RDF graph.
  SPARQL "DESCRIBE" queries return a sequence of sem:triple values as an RDF
  graph that describes the resources found by the query.
  SPARQL "ASK" queries return a single xs:boolean value (true or false)
  indicating whether a query pattern matches in the dataset.
  This function is a built-in.

### Signature

```xquery
sem:sparql(
  $sparql as xs:string,
  $bindings as map:map??,
  $options as xs:string*?,
  $store as sem:store*?
) as item()*
```

### Parameters

**`$sparql`**
The SPARQL query to be executed.

**`$bindings`** *(optional)*
A map containing initial values for variables from the query, or the
    empty sequence if no query variables are to be initially bound. This
    is a way to parameterize the query.

**`$options`** *(optional)*
Options as a sequence of string values. Available options are:
    
    "base=IRI"
    The initial base IRI for the query.
    "default-graph=IRI*"
    Add the named graph or graphs specified by the IRI to the default graph for
    the query.
    "named-graph=IRI*"
    Add the named graph or graphs specified by the IRI to the list of named graphs
    available in the query.
    "parse-check"
    Parse the query, but don't perform static checks or execute it.
    The default is false.
    "prepare"
    Parse and optimize the query, caching the result. No execution is
    performed. Default is false.
    "optimize=N"
    Sets the optimization level to use. Levels of 0 (off), 1, and 2 are
    recognized. The default is 1.
    "trace=ID"
    This parameter outputs the query's plan, optimization and execution
    details in the log while getting results. ID is the identifier to identify
    the query in the logs.
    "dedup=N"
    Sets de-duplication of triples results to "on" or "off". The default, 
    standards-compliant behavior is "on".
    arrayReturn the result as a sequence of array
    values (json:array).
    mapReturn the result as a sequence of map values,
    where the key is the column name (sem:binding).

**`$store`** *(optional)*
A sem:store constructor to use as the source of the triples 
	for the SPARQL query. If multiple sem:store constructors are 
	supplied, the triples from all the sources are merged and queried together. 
	The default	for sem:store is the current database's triple index, 
	restricted by its options and query argument (for instance, "triples in documents matching this query").
	
    Options for "any", "document", "properties", "locks", "checked", or
    "unchecked", which used to be part of the sem:sparql signature, 
	must be specified as part of sem:store, 
	not as part of sem:sparql. The sem:sparql query 
	will run with the locking option specified in sem:store. 
	Locking is ignored in a query transaction.
	
	
    If a sem:store value is not supplied, then the default
    sem:store for the statement will be used. This is the same 
	as calling sem:store() with all arguments omitted, which 
	will access the current database's triple index, using the default 
	rulesets configured for that database. The default for locking is 
	read-write.

### Returns

`item()*`

### Usage Notes

The options parse-check and prepare cannot be
   used at the same time.

### Examples

#### Example 1

```xquery
xquery version "1.0-ml";

import module namespace sem = "http://marklogic.com/semantics"
  at "/MarkLogic/semantics.xqy";

(: load an rdf triple that will match the SPARQL query :)

sem:rdf-insert(
  sem:triple(sem:iri("http://www.example.org/dept/108/invoices/20963"),
	           sem:iri("http://www.example.org/dept/108/invoices/paid"),
             "true")) ;
(: returns the URI of the document that contains the triple :)

sem:sparql('
PREFIX inv: <http://www.example.org/dept/108/invoices/>

SELECT ?predicate ?object
WHERE
{ inv:20963 ?predicate ?object }
')
(:
 returns the predicate(s) and object(s) for the matching triple(s)
 :)
```

#### Example 2

```xquery
xquery version "1.0-ml";

(:
   this query uses the data from the previous query and shows how to
   pass bindings in a parameter to sem:sparql
:)
let $params :=
  map:new(map:entry("subject",
		sem:iri("http://www.example.org/dept/108/invoices/20963")))
return
sem:sparql("
  SELECT ?predicate ?object
  WHERE
  { ?subject ?predicate ?object } ",
  $params)

(:
 returns the predicate(s) and object(s) for the matching triple(s)
 :)
 [{"predicate":"<http://www.example.org/dept/108/invoices/paid>",
   "object":"\"true\""}]
```

#### Example 3

```xquery
xquery version "1.0-ml";

import module namespace sem = "http://marklogic.com/semantics"
  at "/MarkLogic/semantics.xqy";

(: load sample data triples and ontology triple in turtle format :)

sem:rdf-insert(sem:rdf-parse('
@prefix rdfs: <http://www.w3.org/2000/01/rdf-schema#> .
@prefix rdf: <http://www.w3.org/1999/02/22-rdf-syntax-ns#> .
@prefix p0: <http://www.example.org/products/> .
@prefix p2: <http://www.example.com/> .

p2:Henley       <http://www.w3.org/2000/01/rdf-schema#subClassOf>
                                p2:shirt .

p0:prod:1001    p2:color        "blue" ;
                a               p2:Henley .

p0:prod:1002    p2:color        "blue" ;
                a               p2:shirt .', ("graph=graph-1", "turtle")));

(: create a store that uses an RDFS ruleset for inferencing :)

let $rdfs-store := sem:ruleset-store("rdfs.rules",sem:store() )
return

(: use the store you just created - pass it in to sem:sparql() :)

sem:sparql('
    prefix rdfs: <http://www.w3.org/2000/01/rdf-schema#>
    prefix rdf: <http://www.w3.org/1999/02/22-rdf-syntax-ns#>
    prefix p0: <http://www.example.org/products/>
    prefix p2: <http://www.example.com/>

    SELECT ?product
    FROM <graph-1>
    WHERE
    {
      ?product rdf:type p2:shirt ;
      p2:color "blue"
    }',
    (),
    (),
    $rdfs-store
  )

(:
 returns the triples you inserted and the triples that match the query
 :)
 /triplestore/5766e26a98b19b21.xml

                      product
<http://example.org/products/prod:1001>
<http://example.org/products/prod:1002>
}]
```

#### Example 4

```xquery
xquery version "1.0-ml";

import module namespace sem = "http://marklogic.com/semantics"
  at "/MarkLogic/semantics.xqy";

(: load three rdf triples, two of which will match the SPARQL query :)
  
let $triples := (sem:triple(sem:iri("http://www.example.org/dept/108/invoices/20963"),
                          sem:iri("http://www.example.org/dept/108/invoices/paid"),
                          "true"),
                 sem:triple(sem:iri("http://www.example.org/dept/108/invoices/99887"),
                          sem:iri("http://www.example.org/dept/108/invoices/paid"),
                          "true"),
                  sem:triple(sem:iri("http://www.example.org/dept/108/invoices/11111"),
                          sem:iri("http://www.example.org/dept/108/invoices/paid"),
                          "true"))

for $triple in $triples
return sem:rdf-insert($triple)

(: returns the URI of the document that contains the triple :)

(: Run this sparql to select two of the triples using an array of IRIs in the binding. :)

xquery version "1.0-ml";

let $params :=
  map:new(map:entry("invoices",(sem:iri("http://www.example.org/dept/108/invoices/20963"),
                                sem:iri("http://www.example.org/dept/108/invoices/99887"))))
  
return
sem:sparql("
        SELECT ?predicate ?object
        WHERE { 
            ?inv ?predicate ?object 
            FILTER (?inv = ?invoices)
        }",
  $params)
  
(:
 returns the triples that match the query
 :)

 [
{
"predicate": "<http://www.example.org/dept/108/invoices/paid>", 
"object": "\"true\""
}, 
{
"predicate": "<http://www.example.org/dept/108/invoices/paid>", 
"object": "\"true\""
}
]
```

---

## sem:sparql-plan

Return a node representing the query plan of the given SPARQL query.

### Signature

```xquery
sem:sparql-plan(
  $sparql as xs:string,
  $bindingNames as xs:string*?,
  $options as xs:string*?
) as element()
```

### Parameters

**`$sparql`**
The SPARQL query to be executed.

**`$bindingNames`** *(optional)*
A sequence of strings naming the variables whose values should be provided
    by the sem:sparql() call. These values will be substituted into the query
    where referenced as if they were literals.

**`$options`** *(optional)*
Options as a sequence of string values. Available options are:
    
    "base=IRI"
    The initial base IRI for the query.
    "optimize=N"
    Sets the optimization level to use. Levels of 0 (off), 1, and 2 are
    recognized. The default is 1.
    "xml"
    Outputs an XML format query plan. This is the default.
    "json"
    Outputs a JSON format query plan. The default is "xml".

### Returns

`element()`

### Examples

```xquery
sem:sparql-plan("select * { ?s ?p ?o }",(),"optimize=1")
```

---

## sem:sparql-update

Executes a SPARQL Update operation against the database.
    Graph Update - addition and removal of triples from some graphs within
    the Graph Store.
    Graph Management - creating and deletion of graphs within the Graph
    Store, as well as convenient shortcuts for graph update operations often
    used during graph management (to add, move, and copy graphs).
	This function is a built-in.

### Signature

```xquery
sem:sparql-update(
  $sparql as xs:string,
  $bindings as map:map??,
  $options as xs:string*?,
  $store as sem:store*?,
  $default-permissions as element(sec:permission)*?
) as empty-sequence()
```

### Parameters

**`$sparql`**
The SPARQL Update to be executed.

**`$bindings`** *(optional)*
A map containing initial values for variables from the query, or the
    empty sequence if no query variables are to be initially bound. This is
    a way to parameterize the query.

**`$options`** *(optional)*
Options as a sequence of string values. Available options are:
    
    "base=IRI"
    The initial base IRI for the query.
    "default-graph=IRI*"
    Add the named graph or graphs specified by the IRI to the default graph for
    the query.
    "named-graph=IRI*"
    Add the named graph or graphs specified by the IRI to the list of named graphs
    available in the query.
    "parse-check"
    Parse the query, but don't perform static checks or execute it.
    "prepare"
    Parse and optimize the query, caching the result. No execution is
    performed.
    "optimize=N"
    Sets the optimization level to use. Levels of 0 (off), 1, and 2 are
    recognized, with 1 as the default.
    "dedup=N"
    Sets de-duplication of triples results to "on" or "off". The default, 
    standards-compliant behavior is "on".
    "directory=URI"
    Sets The database directory path of triples document. Default location
    is /triplestore.
    "triples-document-size=xs:nonNegativeInteger"
    The number of triples in a triples document. Default is 100.
    "existing-graph"
    Update fails if the specified destination graph does not already
    exist.
    "isolation=ISOLATION_LEVEL"
    ISOLATION_LEVEL can be different-transaction or same-statement.
    Default is different-transaction, which will not change the transaction
    mode of the calling transaction. If isolation is same-statement, the
    calling transaction should be run in update mode and the $sparql cannot
    contain multiple statements.
    "transaction-id=TXN_ID"
    TXN_ID is the transaction ID which the SPARQL program is in.
    Setting transaction-id implies isolation to be different-transaction.
    Transaction-id cannot coexist with isolation same-statement.

**`$store`** *(optional)*
A sem:store constructor to use as the source of the triples for
    SPARQL Update. If multiple sem:store constructors are supplied,
    the triples from all the sources are merged and queried together. The
	default for sem:store the current database's triple index. 
	The locking option specified in sem:store will be used by sem:sparql-update.	
	
    If a sem:store value is not supplied, then the default
    sem:store for the statement will be used. This is the same 
	as calling sem:store() with all arguments omitted, which 
	will access the current database's triple index, using the default 
	rulesets configured for that database. The default for locking is 
	read-write.
	
	
	Note: You cannot use an in-memory store with SPARQL Update.

**`$default-permissions`** *(optional)*
Security permission elements corresponding to the permissions for the
    graph during graph creation. If not supplied, the current user's default
    permissions are applied.  The default value used for this parameter can
    be obtained by calling xdmp:default-permissions(). A RDF
    graph that is created by a non-admin user (that is, by any user who does
    not have the admin role) must have at least one update permission,
    otherwise the creation will throw an XDMP-MUSTHAVEUPDATE exception.
    Parameter is ignored if the operation does not involve graph creation.

### Returns

`empty-sequence()`

### Usage Notes

You cannot use an in-memory store with SPARQL Update.

### Examples

```xquery
xquery version "1.0-ml";
import module namespace sem = "http://marklogic.com/semantics"
      at "/MarkLogic/semantics.xqy";

(: Insert a triple into default graph and three triples into graph <BOOKS>. :)
sem:sparql-update('
PREFIX dc: <http://marklogic.com/dc/elements/1.1/>
INSERT DATA
{
   <http://example/book0> dc:title "A default book"
  GRAPH <BOOKS> {<http://example/book1> dc:title "A new book" }
  GRAPH <BOOKS> {<http://example/book2> dc:title "A second book" }
  GRAPH <BOOKS> {<http://example/book3> dc:title "A third book" }
}
');

(: Update any book title which is "A new book" to be "Insert MarkLogic Server". :)

sem:sparql-update('
PREFIX dc: <http://marklogic.com/dc/elements/1.1/>
WITH <BOOKS>
DELETE {?b dc:title "A new book" }
INSERT {?b dc:title "Inside MarkLogic Server" }
WHERE {
  ?b dc:title "A new book" .
}
')
```

---

## sem:sparql-values

This function executes a SPARQL SELECT query using
		passed-in bindings participating as a starting point for 
		the query.

### Signature

```xquery
sem:sparql-values(
  $sparql as xs:string,
  $values as map:map*,
  $options as xs:string*?,
  $store as item()*?
) as map:map*
```

### Parameters

**`$sparql`**
The SPARQL query to be executed. Must be a SELECT query 
		  form.

**`$values`**
A map containing initial bindings for variables 
		  used in the query.  Unlike sem:sparql, a 
		  sequence of bindings is acceptable and will be processed 
		  as the equivalent of an outermost VALUES block in the query.

**`$options`** *(optional)*
Query options. Valid options values include:
      
        
          
		    "base=IRI"
          
          
            The initial base IRI for the query.
          
          
            "default-graph=IRI*"
          
          
		  Add the named graph or graphs specified by the IRI to the default 
		  graph for the query.
          
          
            "named-graph=IRI*"
          
          
		  Add the named graph or graphs specified by the IRI to the list of 
		  named graphs available in the query.
          
          
		  "optimize=N"
          
          
		  Sets the optimization level to use. Levels of 0 (off), 
		  1, and 2 are recognized. Default is 1.

**`$store`** *(optional)*
Options for "any", "document", "properties", "locks", "checked", and 
		"unchecked", which used to be part of the sem:sparql-values 
		signature, must be specified as part of 
		sem:store, not as part of 
		sem:sparql-values.  
		This parameter is designed to take sem:store*, but is 
		typed as an item()* for backward compatibility. The default 
		for sem:store is the current database's triple index, restricted by the options and the cts:query argument (for instance, "triples in documents matching this query"). 
		
		The locking option specified in sem:store will be used 
		by sem:sparql-values. Locking is ignored in a query transaction. 
		
		
		If a sem:store value is not supplied, then the default 
		sem:store for the statement will be used. This is the 
		same as calling sem:store() with all arguments omitted, 
		which will access the current database's triple index, using 
		the default rulesets configured for that database. The default for 
		locking is read-write.

### Returns

`map:map*`

### Usage Notes

If $values is an empty sequence, nothing is returned. 
       A variable can be in both bindings and the VALUES clause. 
       The binding variable must occur in either the SELECT clause
      or the triple patterns, otherwise an "Undefined variable" 
	  exception is thrown. 
      The sem:sparql-values function performs a join 
	  (SPARQL style, natural join) between the bindings returned 
	  from the SELECT expression and the bindings passed in as 
	  an argument, therefore the results reflect this join.

### Examples

```xquery
xquery version "1.0-ml"; 
 
import module namespace sem = "http://marklogic.com/semantics" 
    at "/MarkLogic/semantics.xqy";

let $bindings := (
    map:entry("s",
        sem:iri("http://example.net/foaf.rdf#Lenovo_T61")),
    map:entry("s",
        sem:iri("http://example.net/foaf.rdf#Nokia_N80"))
    )
return sem:sparql-values("select * where { ?s ?p ?o }", $bindings)
```

---

## sem:store

The sem:store function defines a set of criteria, that when evaluated,
  selects a set of triples to be passed in to sem:sparql(),
  sem:sparql-update(), or sem:sparql-values() as part
  of the options argument. The sem:store constructor queries from the
  current database's triple index, restricted by the options and the cts:query
  argument (for instance, "triples in documents matching this query").

  This function is a built-in.

### Signature

```xquery
sem:store(
  $options as xs:string*?,
  $query as cts:query??
) as sem:store
```

### Parameters

**`$options`** *(optional)*
Options as a sequence of string values. Available options are:
    
    "any"
    Values from any fragment should be included.
    "document"
    Values from document fragments should be included.
    "properties"
    Values from properties fragments should be included.
    "locks"
    Values from locks fragments should be included.
    "checked"
    Word positions should be checked when resolving the query.
    "unchecked"
    Word positions should not be checked when resolving the query.
    "size=number of MB"
    The maximum size of the memory used to cache inferred triples. This
    defaults to the default inference size set for the app-server. If the
    value provided is bigger than the maximum inference size set for the
    App Server, an error is raised [XDMP-INFSIZE].
    "no-default-rulesets"
    Don't apply the database's default rulesets to the sem:store.
    "locking=read-write/write"
    read-write: Read-lock documents containing triples being accessed,
    write-lock documents being updated; write: Only write-lock documents
    being updated. Default is locking=read-write. Locking is ignored in
    query transaction.

**`$query`** *(optional)*
Only include triples in fragments selected by the cts:query.
    The triples do not need to match the query, but they must occur in
    fragments selected by the query.
    The fragments are not filtered to ensure they match the query,
    but instead selected in the same manner as 
    "unfiltered" cts:search operations.  If a string
    is entered, the string is treated as a cts:word-query of the
    specified string.

### Returns

`sem:store`

### Usage Notes

Only one of "any", "document", "properties", or "locks" may be specified
    in the options parameter. If none of "any", "document", "properties", or
    "locks" are specified and there is a $query parameter, then
    the default is "document". If there is no $query parameter
    then the default is "any". 
      
    Options for "any", "document", "properties", "locks", "checked", or
    "unchecked" must be specified as part of sem:store, not
    as part of sem:sparql, sem:sparql-update, or
	sem:sparql-values.

### Examples

```xquery
xquery version "1.0-ml";

import module namespace sem = "http://marklogic.com/semantics"
      at "/MarkLogic/semantics.xqy";

sem:store((), cts:word-query("Alfa Romeo"))
=>
Returns a sem:store() containing all of the triples that exist in documents
that match a query for "Alfa Romeo".
```

---

## sem:timezone-string

Returns the timezone of an xs:dateTime value as a string.
  This XQuery function backs up the SPARQL TZ() function.
  This function is a built-in.

### Signature

```xquery
sem:timezone-string(
  $value as xs:dateTime
) as xs:string
```

### Parameters

**`$value`**
The dateTime value

### Returns

`xs:string`

### Examples

```xquery
sem:timezone-string(fn:current-dateTime())
=>
-08:00
```

---

## sem:transitive-closure

From a starting set of seeds, follow a given set 
		of predicates, to a given depth, and return all unique node 
		IRIs.

### Signature

```xquery
sem:transitive-closure(
  $seeds as sem:iri*,
  $predicates as sem:iri*,
  $limit as xs:integer
) as sem:iri*
```

### Parameters

**`$seeds`**
A set of seed IRIs.

**`$predicates`**
A set of predicates to follow.

**`$limit`**
A limit of how many predicates to follow.

### Returns

`sem:iri*`

### Examples

```xquery
xquery version "1.0-ml"; 
 
import module namespace sem = "http://marklogic.com/semantics" 
      at "/MarkLogic/semantics.xqy";

sem:transitive-closure(
    sem:iri("http://www.w3.org/People/Berners-Lee/card#i"),
    sem:iri("http://xmlns.com/foaf/0.1/knows"),
    9)
=>
http://www.w3.org/People/Berners-Lee/card#i
```

---

## sem:triple

Creates a triple object, which represents an RDF triple
  containing atomic values representing the subject, predicate, object, and
  optionally graph identifier (graph IRI).
  This function is a built-in.

### Signature

```xquery
sem:triple(
  $subject_or_node as item(),
  $predicate as xs:anyAtomicType?,
  $object as xs:anyAtomicType?,
  $graph as sem:iri??
) as sem:triple
```

### Parameters

**`$subject_or_node`**
The triple's subject as an atomic value, or the whole triple as a
    node.
    If specifying a node as a triple, this function must be used
    as a single-parameter version (that is, you cannot specify a triple
    in this parameter and also use the other parameters).

**`$predicate`** *(optional)*
The triple's predicate.

**`$object`** *(optional)*
The triple's object.

**`$graph`** *(optional)*
The triple's graph IRI.  This parameter is only available if you have
    specified a subject, predicate, and object, and is not available if you
    have specified an element as a triple in the first parameter.

### Returns

`sem:triple`

### Usage Notes

It is possible to create triples with sem:triple that might not
   be valid RDF triples.  For example, you can create a triple with a blank
   node (sem:bnode()) as a predicate,
   even though that is not allowed in RDF.  This is because the triples
   you can create with sem:triple are more general than what is
   allowed in RDF.

### Examples

#### Example 1

```xquery
xquery version "1.0-ml";
import module namespace sem = "http://marklogic.com/semantics"
   at "MarkLogic/semantics.xqy";

sem:triple(sem:iri("subject"), sem:iri("predicate"), "object")

(: Returns the specified triple. :)
```

#### Example 2

```xquery
xquery version "1.0-ml";
import module namespace sem = "http://marklogic.com/semantics"
   at "MarkLogic/semantics.xqy";

sem:triple(
<sem:triple xmlns:sem="http://marklogic.com/semantics">
  <sem:subject>subject</sem:subject>
  <sem:predicate>predicate</sem:predicate>
  <sem:object
   datatype="http://www.w3.org/2001/XMLSchema#string">object</sem:object>
</sem:triple>)

(: Returns the specified triple. :)
```

#### Example 3

```xquery
xquery version "1.0-ml";
import module namespace sem = "http://marklogic.com/semantics"
   at "MarkLogic/semantics.xqy";

sem:triple(
  object-node {
    "triple" : object-node {
      "subject" : "subject",
      "predicate" : "predicate",
      "object" : object-node {
        "value" : "object",
        "datatype" : "http://www.w3.org/2001/XMLSchema#string"
      }
    }
  }
)

(: Returns the specified triple. :)
```

#### Example 4

```xquery
xquery version "1.0-ml";
import module namespace sem = "http://marklogic.com/semantics"
   at "MarkLogic/semantics.xqy";

sem:triple(
<foo>{sem:triple(sem:iri("subject"), sem:iri("predicate"),
      "object")}
</foo>/element())

(: Returns the specified triple. :)
```

---

## sem:triple-graph

Returns the graph identifier (graph IRI) from a sem:triple value.
  This function is a built-in.

### Signature

```xquery
sem:triple-graph(
  $triple as sem:triple
) as sem:iri?
```

### Parameters

**`$triple`**
The triple.

### Returns

`sem:iri?`

### Examples

```xquery
xquery version "1.0-ml";
import module namespace sem = "http://marklogic.com/semantics" 
   at "/MarkLogic/semantics.xqy";

let $triple := sem:triple(sem:iri("subject"), sem:iri("predicate"), "object")

return
    sem:triple-graph($triple)

=>
empty (because there is no graph URI)
```

---

## sem:triple-object

Returns the object from a sem:triple value.
  This function is a built-in.

### Signature

```xquery
sem:triple-object(
  $triple as sem:triple
) as xs:anyAtomicType
```

### Parameters

**`$triple`**
The triple.

### Returns

`xs:anyAtomicType`

### Examples

```xquery
xquery version "1.0-ml";
import module namespace sem = "http://marklogic.com/semantics" 
   at "/MarkLogic/semantics.xqy";

let $triple := sem:triple(sem:iri("subject"), sem:iri("predicate"), "object")

return
    sem:triple-object($triple)

(: Returns 'object'. :)
```

---

## sem:triple-predicate

Returns the predicate from a sem:triple value.
  This function is a built-in.

### Signature

```xquery
sem:triple-predicate(
  $triple as sem:triple
) as xs:anyAtomicType
```

### Parameters

**`$triple`**
The triple.

### Returns

`xs:anyAtomicType`

### Examples

```xquery
xquery version "1.0-ml";
import module namespace sem = "http://marklogic.com/semantics" 
  at "/MarkLogic/semantics.xqy";

let $triple := sem:triple(sem:iri("subject"), sem:iri("predicate"), "object")

return
    sem:triple-predicate($triple)

(: Returns 'predicate'. :)
```

---

## sem:triple-subject

Returns the subject from a sem:triple value.
  This function is a built-in.

### Signature

```xquery
sem:triple-subject(
  $triple as sem:triple
) as xs:anyAtomicType
```

### Parameters

**`$triple`**
The triple.

### Returns

`xs:anyAtomicType`

### Examples

```xquery
xquery version "1.0-ml";
import module namespace sem = "http://marklogic.com/semantics" 
   at "/MarkLogic/semantics.xqy";

let $triple := sem:triple(sem:iri("subject"), sem:iri("predicate"), "object")

return
    sem:triple-subject($triple)

    (: Returns 'subject'. :)
```

---

## sem:typed-literal

Returns a value to represent the RDF typed literal with lexical value 
  $value and datatype IRI $datatype. Returns a value 
  of type sem:unknown for datatype IRIs for which there is no schema, 
  and a value of type sem:invalid for lexical values which are invalid according to the schema for the given datatype. This XQuery function backs up the 
  SPARQL STRDT() function.
  This function is a built-in.

### Signature

```xquery
sem:typed-literal(
  $value as xs:string,
  $datatype as sem:iri
) as xs:anyAtomicType
```

### Parameters

**`$value`**
The lexical value.

**`$datatype`**
The datatype IRI.

### Returns

`xs:anyAtomicType`

### Examples

```xquery
xquery version "1.0-ml";
 
xdmp:describe(sem:typed-literal("object", sem:iri("http://www.w3.org/2001/XMLSchema#string")))
=>
"object"
<http://www.w3.org/2001/XMLSchema#string>
```

---

## sem:unknown

Returns a sem:unknown value with the given literal value and 
  datatype IRI. The sem:unknown type extends xs:untypedAtomic, and represents an RDF value with a datatype IRI for which no schema is available.
  This function is a built-in.

### Signature

```xquery
sem:unknown(
  $string as xs:string,
  $datatype as sem:iri
) as sem:unknown
```

### Parameters

**`$string`**
The lexical value.

**`$datatype`**
The datatype IRI.

### Returns

`sem:unknown`

### Examples

```xquery
xdmp:describe(sem:unknown("unknown value", sem:iri("string")))
=>
sem:unknown("unknown value", sem:iri("string"))
```

---

## sem:unknown-datatype

Returns the datatype IRI of a sem:unknown value.
  This function is a built-in.

### Signature

```xquery
sem:unknown-datatype(
  $val as sem:unknown
) as sem:iri
```

### Parameters

**`$val`**
The sem:unknown value.

### Returns

`sem:iri`

### Examples

```xquery
sem:unknown-datatype(sem:unknown("unknown value", sem:iri("string")));
=>
"string"
```

---

## sem:uuid

Return a UUID URN (RFC4122) as a sem:iri value.
  This XQuery function backs up the SPARQL UUID() function.
  This function is a built-in.

### Returns

`sem:iri`

### Examples

```xquery
sem:uuid()
=>
urn:uuid:3e25ff09-c6a8-4176-bb83-b771a9eb0e4c
```

---

## sem:uuid-string

Return a string that is the scheme specific part of random UUID URN (RFC4122).
  This XQuery function backs up the SPARQL STRUUID() function.
  This function is a built-in.

### Returns

`xs:string`

### Examples

```xquery
sem:uuid-string()
=>
3e25ff09-c6a8-4176-bb83-b771a9eb0e4c
```

---
