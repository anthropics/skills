---
name: marklogic-search-and-query
description: MarkLogic search, query construction, and semantic functions for XQuery
globs: **/*.xqy,**/*.xq
---

# MarkLogic Search & Query Functions

This skill provides comprehensive coverage of MarkLogic's search and query construction capabilities, including CTS query constructors, lexicon operations, vector search, and semantic/RDF functions.

This skill provides 393 XQuery functions organized into 10 functional areas.

## Functions by Category

### Lexicon

*Detailed documentation: [functions/lexicon.md](functions/lexicon.md)*

| Function | Summary |
|----------|---------|
| `cts:collection-match` | Returns values from the collection lexicon  that match the specified wildcard pattern.  This function requires the collection-lexicon database configuration  parameter to be enabled. If the collection lexicon database configuration  parameter is not enabled, an exception is thrown. |
| `cts:collection-reference` | Creates a reference to the collection lexicon, for use as a parameter to  cts:value-tuples. Since lexicons are implemented with range indexes,  this function will throw an exception if the specified range index does  not exist. |
| `cts:collections` | Returns values from the collection lexicon.  This function requires the collection-lexicon database configuration  parameter to be enabled. If the collection-lexicon database-configuration  parameter is not enabled, an exception is thrown. |
| `cts:element-attribute-reference` | Creates a reference to an element attribute value lexicon, for use as a  parameter to cts:value-tuples. Since lexicons are implemented with range  indexes, this function will throw an exception if the specified range index  does not exist. |
| `cts:element-attribute-value-co-occurrences` | Returns value co-occurrences from the specified element or element-attribute  value lexicon(s).  Value lexicons are implemented using range indexes;  consequently this function requires a range index for each element/attribute  pairs specified in the function.  If there is not a range index configured for each of the specified  element or element/attribute pairs, then an exception is thrown. |
| `cts:element-attribute-value-match` | Returns values from the specified element-attribute value lexicon(s)  that match the specified pattern. Element-attribute value lexicons are  implemented using range indexes; consequently this function requires an  attribute range index for each of the element/attribute pairs specified  in the function. If there is not a range index configured for each of the  specified element/attribute pairs, then an exception is thrown. |
| `cts:element-attribute-value-ranges` | Returns value ranges from the specified element-attribute value lexicon(s).  Element-attribute value lexicons are implemented using indexes;  consequently this function requires an attribute range index  of for each of the element/attribute pairs specified in the function.  If there is not a range index configured for each of the specified  element/attribute pairs, then an exception is thrown.    The values are divided into buckets. The $bounds parameter specifies  the number of buckets and the size of each bucket.  All included values are bucketed, even those less than the lowest bound  or greater than the highest bound. An empty sequence for $bounds specifies  one bucket, a single value specifies two buckets, two values specify  three buckets, and so on.    If you have string values and you pass a $bounds parameter  as in the following call:    cts:element-value-ranges(xs:QName("myElement"), ("f", "m"))    The first bucket contains string values that are less than the  string f, the second bucket contains string values greater than  or equal to f but less than m, and the third bucket  contains string values that are greater than or equal to m.    For each non-empty bucket, a cts:range element is returned.  Each cts:range element has a cts:minimum child  and a cts:maximum child. If a bucket is bounded, its  cts:range element will also have a  cts:lower-bound child if it is bounded from below, and  a cts:upper-bound element if it is bounded from above.  Empty buckets return nothing unless the "empties" option is specified. |
| `cts:element-attribute-values` | Returns values from the specified element-attribute value lexicon(s).  Element-attribute value lexicons are implemented using indexes;  consequently this function requires an attribute range index  of for each of the element/attribute pairs specified in the function.  If there is not a range index configured for each of the specified  element/attribute pairs, then an exception is thrown. |
| `cts:element-attribute-word-match` | Returns words from the specified element-attribute word lexicon(s) that  match a wildcard pattern.  This function requires an element-attribute  word lexicon for each of the element/attribute pairs specified in the  function. If there is not an element-attribute word lexicon  configured for any of the specified element/attribute pairs, then  an exception is thrown. |
| `cts:element-attribute-words` | Returns words from the specified element-attribute word lexicon(s).  This function requires an element-attribute word lexicon for each of the  element/attribute pairs specified in the function. If there is not an  element/attribute word lexicon configured for any of the specified  element/attribute pairs, then an exception is thrown. The words are  returned in collation order. |
| `cts:element-reference` | Creates a reference to an element value lexicon, for use as a parameter to  cts:value-tuples,  temporal:axis-create, or any  other function that takes an index reference. Since lexicons are  implemented with range indexes, this function will throw an exception if  the specified range index does not exist. |
| `cts:element-value-co-occurrences` | Returns value co-occurrences (that is, pairs of values, both of which appear  in the same fragment) from the specified element value lexicon(s). The  values are returned as an XML element  with two children, each child  containing one of the co-occurring values. You can use  cts:frequency  on each item returned to find how many times the pair occurs.  Value lexicons are implemented using range indexes; consequently  this function requires an element range index for each element specified  in the function. If there is not a range index configured for each  of the specified elements, an exception is thrown. |
| `cts:element-value-match` | Returns values from the specified element value lexicon(s)  that match the specified wildcard pattern. Element value lexicons  are implemented using range indexes; consequently this function  requires an element range index for each element specified in the  function. If there is not a range index configured for each of the  specified elements, then an exception is thrown. |
| `cts:element-value-ranges` | Returns value ranges from the specified element value lexicon(s).  Value lexicons are implemented using range indexes; consequently this  function requires an element range index for each element specified  in the function. If there is not a range index configured for each  of the specified elements, an exception is thrown.    The values are divided into buckets. The $bounds parameter specifies  the number of buckets and the size of each bucket.  All included values are bucketed, even those less than the lowest bound  or greater than the highest bound. An empty sequence for $bounds specifies  one bucket, a single value specifies two buckets, two values specify  three buckets, and so on.    If you have string values and you pass a $bounds parameter  as in the following call:    cts:element-value-ranges(xs:QName("myElement"), ("f", "m"))    The first bucket contains string values that are less than the  string f, the second bucket contains string values greater than  or equal to f but less than m, and the third bucket  contains string values that are greater than or equal to m.    For each non-empty bucket, a cts:range element is returned.  Each cts:range element has a cts:minimum child  and a cts:maximum child. If a bucket is bounded, its  cts:range element will also have a  cts:lower-bound child if it is bounded from below, and  a cts:upper-bound element if it is bounded from above.  Empty buckets return nothing unless the "empties" option is specified. |
| `cts:element-values` | Returns values from the specified element value lexicon(s).  Value lexicons are implemented using range indexes; consequently this  function requires an element range index for each element specified  in the function. If there is not a range index configured for each  of the specified elements, an exception is thrown. |
| `cts:element-word-match` | Returns words from the specified element word lexicon(s) that match  a wildcard pattern.  This function requires an element word lexicon  configured for each of the specified elements in the function. If there  is not an element word lexicon configured for any of the specified  elements, an exception is thrown. |
| `cts:element-words` | Returns words from the specified element word lexicon. This function  requires an element word lexicon for each of the element specified in the  function. If there is not an element word lexicon configured for any  of the specified elements, an exception is thrown. The words are  returned in collation order. |
| `cts:field-reference` | Creates a reference to a field value lexicon, for use as a  parameter to  cts:value-tuples.  Since lexicons are implemented with range indexes, this function will  throw an exception if the specified range index does not exist. |
| `cts:field-value-co-occurrences` | Returns value co-occurrences (that is, pairs of values, both of which appear  in the same fragment) from the specified field value lexicon(s). The  values are returned as an XML element  with two children, each child  containing one of the co-occurring values. You can use  cts:frequency  on each item returned to find how many times the pair occurs.  Value lexicons are implemented using range indexes; consequently  this function requires an field range index for each field specified  in the function. If there is not a range index configured for each  of the specified fields, an exception is thrown. |
| `cts:field-value-match` | Returns values from the specified field value lexicon(s)  that match the specified wildcard pattern. Field value lexicons  are implemented using range indexes; consequently this function  requires a field range index for each field specified in the  function. If there is not a range index configured for each of the  specified fields, then an exception is thrown. |
| `cts:field-value-ranges` | Returns value ranges from the specified field value lexicon(s).  Value lexicons are implemented using range indexes; consequently this  function requires a field range index for each element specified  in the function. If there is not a range index configured for each  of the specified fields, an exception is thrown.    The values are divided into buckets. The $bounds parameter specifies  the number of buckets and the size of each bucket.  All included values are bucketed, even those less than the lowest bound  or greater than the highest bound. An empty sequence for $bounds specifies  one bucket, a single value specifies two buckets, two values specify  three buckets, and so on.    If you have string values and you pass a $bounds parameter  as in the following call:    cts:field-value-ranges("myField", ("f", "m"))    The first bucket contains string values that are less than the  string f, the second bucket contains string values greater than  or equal to f but less than m, and the third bucket  contains string values that are greater than or equal to m.    For each non-empty bucket, a cts:range element is returned.  Each cts:range element has a cts:minimum child  and a cts:maximum child. If a bucket is bounded, its  cts:range element will also have a  cts:lower-bound child if it is bounded from below, and  a cts:upper-bound element if it is bounded from above.  Empty buckets return nothing unless the "empties" option is specified. |
| `cts:field-values` | Returns values from the specified field value lexicon(s).  Value lexicons are implemented using range indexes; consequently this  function requires an field range index for each field specified  in the function. If there is not a range index configured for each  of the specified fields, an exception is thrown. |
| `cts:field-word-match` | Returns words from the specified field word lexicon(s) that match  a wildcard pattern.  This function requires an field word lexicon  configured for each of the specified fields in the function. If there  is not an field word lexicon configured for any of the specified  fields, an exception is thrown. |
| `cts:field-words` | Returns words from the specified field word lexicon. This function  requires an field lexicon for each of the field specified in the  function. If there is not an field word lexicon configured for any  of the specified fields, an exception is thrown. The words are  returned in collation order. |
| `cts:frequency` | Returns an integer representing the number of times in which a particular  value occurs in a value lexicon lookup. |
| `cts:iri-reference` | Creates a reference to the URI lexicon, for use as a parameter to  cts:value-tuples. This function requires the URI lexicon to be enabled,  otherwise it throws an exception. This reference returns URIs as IRIs. |
| `cts:json-property-reference` | Creates a reference to a JSON property value lexicon, for use as a parameter  to cts:value-tuples. Since lexicons are implemented with range indexes,  this function will throw an exception if the specified range index does  not exist. |
| `cts:json-property-word-match` | Returns words from the specified JSON property word lexicon(s) that match  a wildcard pattern.  This function requires a property word lexicon  configured for each of the specified properties in the function. If there  is not a property word lexicon configured for any of the specified  properties, an exception is thrown. |
| `cts:json-property-words` | Returns words from the specified JSON property word lexicon. This function  requires a property word lexicon for each of the property specified in the  function. If there is not a property word lexicon configured for any  of the specified properties, an exception is thrown. The words are  returned in collation order. |
| `cts:path-reference` | Creates a reference to a path value lexicon, for use as a  parameter to cts:value-tuples. Since lexicons are implemented with range  indexes, this function will throw an exception if the specified range index  does not exist. |
| `cts:reference-collation` | Accessor for the collation of a reference to a string value lexicon. |
| `cts:reference-coordinate-system` | Accessor for the coordinate-system of a reference to a geospatial lexicon. |
| `cts:reference-namespaces` | Accessor for the namespaces of a reference to a [geospatial] path lexicon. |
| `cts:reference-nullable` | Returns true() if the reference is nullable, false() otherwise. |
| `cts:reference-parse` | Creates a reference to a value lexicon by parsing its XML or JSON  representation, for use as a parameter to cts:value-tuples. Since  lexicons are implemented with range indexes, this function will  throw an exception if the specified range index does not exist. |
| `cts:reference-scalar-type` | Accessor for the scalar type of a reference to a value lexicon. |
| `cts:triple-value-statistics` | Returns statistics from the triple index for the values given. Note that these are estimates, rather than exact counts. |
| `cts:triples` | Returns values from the triple index. If subject, predicate, and object are  given, then only triples with those given component values are returned. Triples can be  returned in any of the sort orders present in the triple index. |
| `cts:uri-match` | Returns values from the URI lexicon  that match the specified wildcard pattern.  This function requires the uri-lexicon database configuration  parameter to be enabled. If the uri-lexicon database-configuration  parameter is not enabled, an exception is thrown. |
| `cts:uri-reference` | Creates a reference to the URI lexicon, for use as a parameter to  cts:value-tuples. This function requires the URI lexicon to be enabled,  otherwise it throws an exception. |
| `cts:uris` | Returns values from the URI lexicon.  This function requires the uri-lexicon database configuration  parameter to be enabled. If the uri-lexicon database-configuration  parameter is not enabled, an exception is thrown. |
| `cts:value-co-occurrences` | Returns value co-occurrences (that is, pairs of values, both of which appear  in the same fragment) from the specified value lexicon(s). The  values are returned as an XML element  with two children, each child  containing one of the co-occurring values. You can use  cts:frequency  on each item returned to find how many times the pair occurs.  Value lexicons are implemented using range indexes; consequently  this function requires a range index for each input index reference.  If an index or lexicon is not configured for any of the input references,  an exception is thrown. |
| `cts:value-match` | Returns values from the specified value lexicon(s)  that match the specified wildcard pattern. Value lexicons  are implemented using range indexes; consequently this function  requires a range index for each index reference specified in the  function. If there is not a range index configured for each of the  specified references, then an exception is thrown. |
| `cts:value-ranges` | Returns value ranges from the specified value lexicon(s).  Value lexicons are implemented using range indexes; consequently this  function requires a range index for each element specified  in the function. If there is not an index or lexicon configured for  one of the specified references, an exception is thrown.    The values are divided into buckets. The $bounds parameter specifies  the number of buckets and the size of each bucket.  All included values are bucketed, even those less than the lowest bound  or greater than the highest bound. An empty sequence for $bounds specifies  one bucket, a single value specifies two buckets, two values specify  three buckets, and so on.    If you have string values and you pass a $bounds parameter  as in the following call:    cts:value-ranges(cts:path-reference("/name/fname"), ("f", "m"))    The first bucket contains string values that are less than the  string f, the second bucket contains string values greater than  or equal to f but less than m, and the third bucket  contains string values that are greater than or equal to m.    For each non-empty bucket, a cts:range element is returned.  Each cts:range element has a cts:minimum child  and a cts:maximum child. If a bucket is bounded, its  cts:range element will also have a  cts:lower-bound child if it is bounded from below, and  a cts:upper-bound element if it is bounded from above.  Empty buckets return nothing unless the "empties" option is specified. |
| `cts:value-tuples` | Returns value co-occurrence tuples (that is, tuples of values, each of  which appear in the same fragment) from the specified value lexicons. The  values are returned as json:array values  , where each slot contains  one of the co-occurring values. You can use  cts:frequency on each item returned to find how many times  the tuple occurs.  Value lexicons are implemented using range indexes; consequently  this function requires a range index for each lexicon specified  in the function, and the range index must have range value positions  set to true. If there is not a range index configured for each  of the specified elements, an exception is thrown. |
| `cts:values` | Returns values from the specified value lexicon(s).  Value lexicons are implemented using range indexes; consequently this  function requires a range index for each of the $range-indexes specified  in the function. If there is not a range index configured for each  of the specified range indexes, an exception is thrown. |
| `cts:word-match` | Returns words from the word lexicon that match the wildcard pattern.  This function requires the word lexicon to be enabled. If the word  lexicon is not enabled, an exception is thrown. |
| `cts:words` | Returns words from the word lexicon. This function requires the word  lexicon to be enabled. If the word lexicon is not enabled, an  exception is thrown. The words are returned in collation order. |

### Rdf Functions

*Detailed documentation: [functions/rdf-functions.md](functions/rdf-functions.md)*

| Function | Summary |
|----------|---------|
| `rdf:langString` | Returns an rdf:langString value with the   given value and language tag. The rdf:langString type extends   xs:string, and represents a language tagged string in RDF.     This function is a built-in. |
| `rdf:langString-language` | Returns the language of an rdf:langString   value.    This function is a built-in. |

### Search

*Detailed documentation: [functions/search.md](functions/search.md)*

| Function | Summary |
|----------|---------|
| `cts:confidence` | Returns the confidence of a node,  or of the context node if no node is provided. |
| `cts:contains` | Returns true if any of a sequence of values matches a query. |
| `cts:deregister` | Deregister a registered query, explicitly releasing the associated  resources. |
| `cts:distinctive-terms` | Return the most "relevant" terms in the model nodes (that is, the  terms with the highest scores). |
| `cts:element-walk` | Returns a copy of the node, replacing any elements found  with the specified expression. |
| `cts:entity` | Returns a cts:entity object. This is an opaque object that can be used to build an entity dictionary. |
| `cts:entity-dictionary` | Returns a cts:entity-dictionary object. |
| `cts:entity-dictionary-get` | Retrieve an entity dictionary previously cached in the database. |
| `cts:entity-dictionary-parse` | Construct a cts:entity-dictionary object by parsing it from a formatted string. |
| `cts:entity-highlight` | Returns a copy of the node, replacing any entities found  with the specified expression. You can use this function  to easily highlight any entities in an XML document in an arbitrary manner.  If you do not need fine-grained control of the XML markup returned,  you can use the entity:enrich XQuery module function instead.  A valid entity enrichment license key is required  to use cts:entity-highlight;  without a valid license key, it throws an exception. If you  have a valid license for entity enrichment, you can entity enrich text  in English and in any other languages for which you have a valid license  key. For languages in which you do not have a valid license key,  cts:entity-highlight finds no entities for text in that  language. |
| `cts:entity-walk` | Walk an XML document or element node, evaluating an  expression  against any matching entities. This functions is similar to  cts:entity-highlight  in how it processes matched entities, but it differs in what it returns. |
| `cts:fitness` | Returns the fitness of a node,  or of the context node if no node is provided. Fitness is a normalized  measure of relevance that is based on how well a node matches the query  issued, not taking into account the number of documents in which  the query term(s) occur. |
| `cts:highlight` | Returns a copy of the node, replacing any text matching the query  with the specified expression. You can use this function  to easily highlight any text found in a query. Unlike  fn:replace and other XQuery string functions that match  literal text, cts:highlight matches every term that  matches the search, including stemmed matches or matches with  different capitalization. |
| `cts:parse` | Parses a query string |
| `cts:part-of-speech` | Returns the part of speech for a cts:token, if any. |
| `cts:quality` | Returns the quality of a node,  or of the context node if no node is provided. |
| `cts:register` | Register a query for later use. |
| `cts:relevance-info` | Return the relevance score computation report for a node. |
| `cts:remainder` | Returns an estimated search result size for a node,  or of the context node if no node is provided.  The search result size for a node is the number of fragments remaining  (including the current node) in the result sequence containing the node.  This is useful to quickly estimate the size of a search result sequence,  without using fn:count() or xdmp:estimate(). |
| `cts:score` | Returns the score of a node,  or of the context node if no node is provided. |
| `cts:search` | Returns a relevance-ordered sequence of nodes specified by a given query. |
| `cts:stem` | Returns the stem(s) for a word. |
| `cts:tokenize` | Tokenizes text into words, punctuation, and spaces. Returns output in  the type cts:token, which has subtypes  cts:word, cts:punctuation, and  cts:space, all of which are subtypes of  xs:string. |
| `cts:walk` | Walks a node, evaluating an expression with any text matching a query.  It returns a sequence of all the values returned by the expression  evaluations. This is similar to cts:highlight in how it  evaluates its expression, but it is different in what it returns. |

### Semantic Functions

*Detailed documentation: [functions/semantic-functions.md](functions/semantic-functions.md)*

| Function | Summary |
|----------|---------|
| `sem:binding` | Creates a sem:binding object, which is a sub-type of  json:object (and map:map).  This function is a built-in. |
| `sem:bnode` | This function returns an identifier for a blank node, allowing the construction  of a triple that refers to a blank node.  This XQuery function backs up the SPARQL BNODE() function.  This function is a built-in. |
| `sem:coalesce` | Returns the value of the first argument that evaluates without error.  This XQuery function backs up the SPARQL COALESCE() functional form.  This function is a built-in. |
| `sem:curie-expand` | This function expands a CURIE (Compact URI) 		into a sem:iri object. This raises SEM-UNKNOWNPREFIX if no 		mapping is available. For more information about the default 		prefixes, see sem:prefixes. |
| `sem:curie-shorten` | This function shortens an IRI into a CURIE 		(Compact URI) into a sem:iri object. Returns the IRI string 		unchanged if no mapping is available. |
| `sem:database-nodes` | This function returns database nodes backing given triples. 	 Any given cts:triple may be backed by zero, one, or multiple 	 database nodes. |
| `sem:datatype` | Returns the name of the simple type of the atomic value argument as a SPARQL  style IRI. If the value is derived from sem:unknown or sem:invalid, the datatype IRI part of those values is returned.  This XQuery function backs up the SPARQL datatype() function.  This function is a built-in. |
| `sem:default-graph-iri` | Returns the iri of the default graph.  This function is a built-in. |
| `sem:describe` | This function implements the Concise Bounded Description 	(CBD) specification to describe one or more nodes in the graph. This 	implementation does not provide any reified statements, and will return 	a maximum of 9,999 triples. |
| `sem:graph` | This function returns all triples from a named graph 		 in the database. |
| `sem:graph-add-permissions` | Add permissions to the graph specified.  The user must have update or insert permissions on the graph.  This function is a built-in. |
| `sem:graph-delete` | This function deletes a named graph, and its graph 	  document containing metadata, from the database. This is an update 	  function that deletes documents with a root element of 	  sem:triples. All other documents are not affected. |
| `sem:graph-get-permissions` | Get permissions to the graph specified.  The user must have read permissions on the graph.  This function is a built-in. |
| `sem:graph-insert` | This function inserts triples into a named graph, 		creating the graph if necessary. It also creates the graph 		metadata for the graph specified by the "graphname" option. 		This is an update function that returns document IDs. |
| `sem:graph-remove-permissions` | Remove permissions from the graph specified.  The user must have update permissions on the graph.  This function is a built-in. |
| `sem:graph-set-permissions` | Set permissions to the graph specified.  The user must have update permissions on the graph.  This function is a built-in. |
| `sem:if` | The IF function form evaluates the first argument, interprets it as a  effective boolean value, then returns the value of expression2 if the EBV is  true, otherwise it returns the value of expression3. Only one of expression2  and expression3 is evaluated. If evaluating the first argument raises an  error, then an error is raised for the evaluation of the IF expression.  This XQuery function backs up the SPARQL IF() functional form.  This function is a built-in. |
| `sem:in-memory-store` | Returns a sem:store constructor that queries from the sequence  of sem:triple values passed in as an argument. The  sem:store constructor returned from this function will raise an  error if it is passed as part of the options argument to a call to  sem:sparql-update().   The default rulesets configured on the current database have no effect on a  sem:store constructor created with sem:in-memory-store().     This should be used along with sem:sparql() in preference to the  deprecated sem:sparql-triples() function. We will remove documentation  of sem:sparql-triples(), but leave the function for backwards  compatibility.   This function is a built-in. |
| `sem:invalid` | Returns a sem:invalid value with the given literal value and  datatype IRI. The sem:invalid type extends xs:untypedAtomic,  and represents an RDF value whose literal string is invalid according to the  schema for it's datatype.  This function is a built-in. |
| `sem:invalid-datatype` | Returns the datatype IRI of a sem:invalid value.  This function is a built-in. |
| `sem:iri` | This is a constructor function that takes a string 		and constructs an item of type sem:iri 		 from it. |
| `sem:isBlank` | Returns true if the argument is an RDF blank node - that is, derived from  type sem:blank.  This XQuery function backs up the SPARQL isBlank() function.  This function is a built-in. |
| `sem:isIRI` | Returns true if the argument is an RDF IRI - that is, derived from  type sem:iri, but not derived from type sem:blank.  This XQuery function backs up the SPARQL isIRI() and isURI() functions.  This function is a built-in. |
| `sem:isLiteral` | Returns true if the argument is an RDF literal - that is, derived from  type xs:anyAtomicType, but not derived from type sem:iri.  This XQuery function backs up the SPARQL isLiteral() function.  This function is a built-in. |
| `sem:isNumeric` | Returns true if the argument is a valid numeric RDF literal.  This XQuery function backs up the SPARQL isNumeric() function.  This function is a built-in. |
| `sem:lang` | Returns the language of the value passed in, or the empty string if the  value has no language. Only values derived from rdf:langString have a  language. This XQuery function backs up the SPARQL lang() function.  This function is a built-in. |
| `sem:langMatches` | Returns true if $lang-tag matches $lang-range  according to the basic filtering scheme defined in RFC4647.  This XQuery function backs up the SPARQL langMatches() function.  This function is a built-in. |
| `sem:prefixes` | This function returns a set of prefix mappings for 		use with CURIE processing. Calling this function returns the 		internal set of default prefixes. The default mappings include 		prefixes that are widely used and agreed upon, including 		"cc" (Creative Commons), "dc" (Dublin Core), 		"dcterms" (Dublin Core Terms), "dbpedia" (dbpedia resources), 		"dbpedia-owl" (dbpedia ontology), "geonames" (geonames 		ontology), "foaf" (FOAF), "media" (MediaRSS), "owl" (OWL), " 		rdf" (RDF), "product" (productV2), "rdfs" (RDF Schema), 		"skos" (SKOS), "vcard" (VCard vocab), "void" (Vocabulary 		of Interlinked Datasets), "wikidata" (wikidata entities), 		"xhtml" (XHTML), and "xs" (XML Schema). |
| `sem:query-results-serialize` | This function implements the W3C SPARQL Query Results 	format. Any value sequence returned by sem:sparql can 	be passed into this function. The result will be the W3C SPARQL 	Results format, in either XML or JSON format. |
| `sem:random` | Returns a random double between 0 and 1.  This XQuery function backs up the SPARQL RAND() function.  This function is a built-in. |
| `sem:rdf-builder` | This function returns a function that builds triples 		from CURIE and blank node syntax. The resulting function takes 		three string arguments, representing subject, predicate, 		and object respectively, which returns a sem:triple object 		using the graph and prefix mappings passed in to the call to 		sem:rdf-builder. 		Blank nodes specified with a leading underscore (_) will 		be assigned blank node identifiers, and will maintain that 		identity across multiple invocations; for example, 		"_:person1" will refer to the same node as a later 		invocation that also mentions "_:person1". In the 		predicate position, the special value of "a" will be 		interpreted as the same as "rdf:type". |
| `sem:rdf-get` | This function returns sem:triples from a specified location. |
| `sem:rdf-insert` | This function inserts triples into a specified database as 		 one or more sem:triples documents. It also 		 creates graph metadata for the graph specified by the 		 "graph" or "override-graph=URI" option. 		 This is an update function that returns the document URIs of 		 inserted documents. |
| `sem:rdf-load` | This function inserts an RDF document from a specified location 		into the designated database. It also creates the graph 		metadata for the graph specified by the "graph=URI" or 		"override-graph=URI" option. 		This is an update function that returns the document URIs of 		inserted documents. |
| `sem:rdf-parse` | This function returns parsed sem:triple objects 		from a text format or XML. |
| `sem:rdf-serialize` | This function returns a string or json or XML serialization 		of the provided triples. |
| `sem:ruleset-store` | The sem:ruleset-store function returns a set of triples derived  by applying the ruleset to the triples in the sem:store constructor  provided in $store ("the triples that can be inferred from  these rules").   If graph URIs are included with a sem:sparql query that includes  sem:ruleset-store, the query will include "triples in the $store  that are also in these graphs".   This function is a built-in. |
| `sem:sameTerm` | Returns true if the arguments are the same RDF term as defined by  the RDF concepts specification.  This XQuery function backs up the SPARQL sameTerm() function.  This function is a built-in. |
| `sem:sparql` | Executes a SPARQL query against the database.  SPARQL "SELECT" queries return a solution as a sequence of map objects  in the form of a table, where each map represents a set of bindings that  satisfies the query.  SPARQL "CONSTRUCT" queries return triples as a sequence of  sem:triple values in an RDF graph.  SPARQL "DESCRIBE" queries return a sequence of sem:triple values as an RDF  graph that describes the resources found by the query.  SPARQL "ASK" queries return a single xs:boolean value (true or false)  indicating whether a query pattern matches in the dataset.  This function is a built-in. |
| `sem:sparql-plan` | Return a node representing the query plan of the given SPARQL query. |
| `sem:sparql-update` | Executes a SPARQL Update operation against the database.   Graph Update - addition and removal of triples from some graphs within   the Graph Store.   Graph Management - creating and deletion of graphs within the Graph   Store, as well as convenient shortcuts for graph update operations often   used during graph management (to add, move, and copy graphs). 	This function is a built-in. |
| `sem:sparql-values` | This function executes a SPARQL SELECT query using 		passed-in bindings participating as a starting point for 		the query. |
| `sem:store` | The sem:store function defines a set of criteria, that when evaluated,  selects a set of triples to be passed in to sem:sparql(),  sem:sparql-update(), or sem:sparql-values() as part  of the options argument. The sem:store constructor queries from the  current database's triple index, restricted by the options and the cts:query  argument (for instance, "triples in documents matching this query").  This function is a built-in. |
| `sem:timezone-string` | Returns the timezone of an xs:dateTime value as a string.  This XQuery function backs up the SPARQL TZ() function.  This function is a built-in. |
| `sem:transitive-closure` | From a starting set of seeds, follow a given set 		of predicates, to a given depth, and return all unique node 		IRIs. |
| `sem:triple` | Creates a triple object, which represents an RDF triple  containing atomic values representing the subject, predicate, object, and  optionally graph identifier (graph IRI).  This function is a built-in. |
| `sem:triple-graph` | Returns the graph identifier (graph IRI) from a sem:triple value.  This function is a built-in. |
| `sem:triple-object` | Returns the object from a sem:triple value.  This function is a built-in. |
| `sem:triple-predicate` | Returns the predicate from a sem:triple value.  This function is a built-in. |
| `sem:triple-subject` | Returns the subject from a sem:triple value.  This function is a built-in. |
| `sem:typed-literal` | Returns a value to represent the RDF typed literal with lexical value  $value and datatype IRI $datatype. Returns a value  of type sem:unknown for datatype IRIs for which there is no schema,  and a value of type sem:invalid for lexical values which are invalid according to the schema for the given datatype. This XQuery function backs up the  SPARQL STRDT() function.  This function is a built-in. |
| `sem:unknown` | Returns a sem:unknown value with the given literal value and  datatype IRI. The sem:unknown type extends xs:untypedAtomic, and represents an RDF value with a datatype IRI for which no schema is available.  This function is a built-in. |
| `sem:unknown-datatype` | Returns the datatype IRI of a sem:unknown value.  This function is a built-in. |
| `sem:uuid` | Return a UUID URN (RFC4122) as a sem:iri value.  This XQuery function backs up the SPARQL UUID() function.  This function is a built-in. |
| `sem:uuid-string` | Return a string that is the scheme specific part of random UUID URN (RFC4122).  This XQuery function backs up the SPARQL STRUUID() function.  This function is a built-in. |

### Vector Constructors

*Detailed documentation: [functions/vector-constructors.md](functions/vector-constructors.md)*

| Function | Summary |
|----------|---------|
| `vec:base64-decode` | Returns a vector value by decoding the base64 encoded string input. |
| `vec:vector` | Returns a vector value. |

### Vector Operations

*Detailed documentation: [functions/vector-operations.md](functions/vector-operations.md)*

| Function | Summary |
|----------|---------|
| `vec:add` | Returns the sum of two vectors. The vectors must be of the same dimension. |
| `vec:base64-encode` | Returns the base64 encoding of the vector. Useful for compressing a   high-dimensional float vector represented as a string into fewer characters. |
| `vec:cosine` | Returns the cosine of the angle between two vectors. The vectors must be of   the same dimension. |
| `vec:cosine-distance` | Returns the cosine distance between two vectors. The vectors must be of   the same dimension. |
| `vec:dimension` | Returns the dimension of the vector passed in. |
| `vec:dot-product` | Returns the dot product between two vectors. The vectors must be of   the same dimension. Use this function to calculate similarity between   vectors if you are certain they are both of magnitude 1. |
| `vec:euclidean-distance` | Returns the Euclidean distance between two vectors. The vectors must be of   the same dimension. |
| `vec:get` | Returns the element at the k-th index of the vector. |
| `vec:magnitude` | Returns the magnitude of the vector. |
| `vec:normalize` | Returns the vector passed in, normalized to a length of 1. |
| `vec:subtract` | Returns the difference of two vectors. The vectors must be of the same dimension. |
| `vec:subvector` | Returns a subvector of the input vector, starting at the specified index, with the specified length (optional). |
| `vec:vector-score` | A helper function that returns a hybrid score using a cts score and a vector distance calculation result.  You can tune the effect of the vector distance on the score using the distanceWeight option. The ideal  value for distanceWeight depends on your application.  The hybrid score is calculated using the formula:  score = weight * annScore + (1 - weight) * ctsScore.  - annScore is derived from the distance and distanceWeight, where a larger distanceWeight reduces the annScore for the same distance.  - weight determines the contribution of the annScore and ctsScore to the final score. A weight of 0.5 balances both equally.  This formula allows you to combine traditional cts scoring with vector-based distance scoring, providing a flexible way to rank results. |

### Xpath Validation

*Detailed documentation: [functions/xpath-validation.md](functions/xpath-validation.md)*

| Function | Summary |
|----------|---------|
| `cts:valid-document-patch-path` | Parses path expressions and resolves namespaces using the $map parameter. Returns true if the argument is permissible as a path for document PATCH. |
| `cts:valid-extract-path` | Parses path expressions and resolves namespaces using the $map parameter. Returns true if the argument is permissible as a path for extract-path option in extract-document-data |
| `cts:valid-index-path` | Parses path expressions and resolves namespaces based on the server run-time environment. Returns true if the argument is permissible as a path for indexing. |
| `cts:valid-optic-path` | Parses path expressions and resolves namespaces using the $map parameter. Support built in functions inside path since ML 11.0.0. Returns true if the argument is permissible as a path for Optic op:xpath |

### Cts:Order Constructors

*Detailed documentation: [functions/cts-order-constructors.md](functions/cts-order-constructors.md)*

| Function | Summary |
|----------|---------|
| `cts:confidence-order` | Creates a confidence-based ordering clause, for use as an option to   cts:search. |
| `cts:document-order` | Creates a document-based ordering clause, for use as an option to   cts:search. |
| `cts:fitness-order` | Creates a fitness-based ordering clause, for use as an option to   cts:search. |
| `cts:index-order` | Creates a index-based ordering clause, for use as an option to   cts:search. |
| `cts:quality-order` | Creates a quality-based ordering clause, for use as an option to   cts:search. |
| `cts:score-order` | Creates a score-based ordering clause, for use as an option to   cts:search. |
| `cts:unordered` | Specifies that results should be unordered, for use with   cts:search. |

### Cts:Query Constructors

*Detailed documentation: [functions/cts-query-constructors.md](functions/cts-query-constructors.md)*

| Function | Summary |
|----------|---------|
| `cts:after-query` | Returns a query matching fragments committed after a specified timestamp. |
| `cts:after-query-timestamp` | Returns the timestamp with which a specified query was constructed. |
| `cts:and-not-query` | Returns a query specifying the set difference of  the matches specified by two sub-queries. |
| `cts:and-not-query-negative-query` | Returns the negative (second parameter) query used to construct the  specified query. |
| `cts:and-not-query-positive-query` | Returns the positive (first parameter) query used to construct the  specified query. |
| `cts:and-query` | Returns a query specifying the intersection  of the matches specified by the sub-queries. |
| `cts:and-query-options` | Returns the options for the specified query. |
| `cts:and-query-queries` | Returns a sequence of the queries that were used to construct the specified  query. |
| `cts:before-query` | Returns a query matching fragments committed before or at a specified timestamp. |
| `cts:before-query-timestamp` | Returns the timestamp with which a specified query was constructed. |
| `cts:boost-query` | Returns a query specifying that matches to $matching-query  should have their search relevance scores boosted if they also match  $boosting-query. |
| `cts:boost-query-boosting-query` | Returns the boosting (second parameter) query used to construct the  specified boost query. |
| `cts:boost-query-matching-query` | Returns the matching (first parameter) query used to construct the  specified boost query. |
| `cts:collection-query` | Match documents in at least one of the specified collections.  It will match both documents and properties documents in the collections  with the given URIs. |
| `cts:collection-query-uris` | Returns the URIs used to construct the specified query. |
| `cts:column-range-query` | Returns a  cts:query  matching documents matching a TDE-view column equals to an value. Searches with the  cts:column-range-query  constructor require the triple index;  if the triple index is not configured, then an exception is thrown. |
| `cts:directory-query` | Returns a query matching documents in the directories with the given URIs. |
| `cts:directory-query-depth` | Returns the depth used to construct the specified query. |
| `cts:directory-query-uris` | Returns the URIs used to construct the specified query. |
| `cts:document-format-query` | Returns a query matching documents of a given format. |
| `cts:document-format-query-format` | Returns the formt used to construct the specified query. |
| `cts:document-fragment-query` | Returns a query that matches all documents where $query matches  any document fragment. When searching documents, document-properties, or  document-locks, this function provides a  convenient way to additionally constrain the search against any document  fragment. |
| `cts:document-fragment-query-query` | Returns the query used to construct the specified query. |
| `cts:document-permission-query` | Returns a query matching documents with a given permission. |
| `cts:document-permission-query-capability` | Returns the capability used to construct the specified query. |
| `cts:document-query` | Returns a query matching documents with the given URIs. It will match both  documents and properties documents with the given URIs. |
| `cts:document-query-uris` | Returns the URIs used to construct the specified query. |
| `cts:document-root-query` | Returns a query matching documents with a given root element. |
| `cts:document-root-query-root` | Returns the QName used to construct the specified query. |
| `cts:element-attribute-pair-geospatial-query` | Returns a query matching elements by name which has  specific attributes representing latitude and longitude values for  a point contained within the given geographic box, circle, or polygon,  or equal to the given point. Points that lie  between the southern boundary and the northern boundary of a box,  travelling northwards,  and between the western boundary and the eastern boundary of the box,  travelling eastwards, will match.  Points contained within the given radius of the center point of a circle will  match, using the curved distance on the surface of the Earth.  Points contained within the given polygon will match, using great circle arcs  over a spherical model of the Earth as edges. An error may result  if the polygon is malformed in some way.  Points equal to the a given point will match, taking into account the fact  that longitudes converge at the poles.  Using the geospatial query constructors requires a valid geospatial  license key; without a valid license key, searches that include  geospatial queries will throw an exception. |
| `cts:element-attribute-pair-geospatial-query-element-name` | Returns the QNames used to construct the specified query. |
| `cts:element-attribute-pair-geospatial-query-latitude-name` | Returns the QNames used to construct the specified query. |
| `cts:element-attribute-pair-geospatial-query-longitude-name` | Returns the QNames used to construct the specified query. |
| `cts:element-attribute-pair-geospatial-query-options` | Returns the options for the specified query. |
| `cts:element-attribute-pair-geospatial-query-region` | Returns the geographical regions with which the specified query was constructed. |
| `cts:element-attribute-pair-geospatial-query-weight` | Returns the weight with which the specified query was constructed. |
| `cts:element-attribute-range-query` | Constructs a query that matches element-attributes by name with a  range-index entry equal to a given value. An element attribute range  index on the specified QName(s) must exist when you use this query  in a search; if no such range index exists, the search throws an exception. |
| `cts:element-attribute-range-query-attribute-name` | Returns the QNames used to construct the specified query. |
| `cts:element-attribute-range-query-element-name` | Returns the QNames used to construct the specified query. |
| `cts:element-attribute-range-query-operator` | Returns the operator used to construct the specified query. |
| `cts:element-attribute-range-query-options` | Returns the options for the specified query. |
| `cts:element-attribute-range-query-value` | Returns the value used to construct the specified query. |
| `cts:element-attribute-range-query-weight` | Returns the weight with which the specified query was constructed. |
| `cts:element-attribute-value-query` | Returns a query matching elements by name with attributes by name  with text content equal a given phrase. |
| `cts:element-attribute-value-query-attribute-name` | Returns the attribute QNames used to construct the specified query. |
| `cts:element-attribute-value-query-element-name` | Returns the element QNames used to construct the specified query. |
| `cts:element-attribute-value-query-options` | Returns the options for the specified query. |
| `cts:element-attribute-value-query-text` | Returns the text used to construct the specified query. |
| `cts:element-attribute-value-query-weight` | Returns the weight with which the specified query was constructed. |
| `cts:element-attribute-word-query` | Returns a query matching elements by name  with attributes by name  with text content containing a given phrase. |
| `cts:element-attribute-word-query-attribute-name` | Returns the attribute QNames used to construct the specified query. |
| `cts:element-attribute-word-query-element-name` | Returns the element QNames used to construct the specified query. |
| `cts:element-attribute-word-query-options` | Returns the options for the specified query. |
| `cts:element-attribute-word-query-text` | Returns the text used to construct the specified query. |
| `cts:element-attribute-word-query-weight` | Returns the weight with which the specified query was constructed. |
| `cts:element-child-geospatial-query` | Returns a query matching elements by name which has  specific element children representing latitude and longitude values for  a point contained within the given geographic box, circle, or polygon, or  equal to the given point. Points that lie  between the southern boundary and the northern boundary of a box,  travelling northwards,  and between the western boundary and the eastern boundary of the box,  travelling eastwards, will match.  Points contained within the given radius of the center point of a circle will  match, using the curved distance on the surface of the Earth.  Points contained within the given polygon will match, using great circle arcs  over a spherical model of the Earth as edges. An error may result  if the polygon is malformed in some way.  Points equal to the a given point will match, taking into account the fact  that longitudes converge at the poles.  Using the geospatial query constructors requires a valid geospatial  license key; without a valid license key, searches that include  geospatial queries will throw an exception. |
| `cts:element-child-geospatial-query-child-name` | Returns the QNames used to construct the specified query. |
| `cts:element-child-geospatial-query-element-name` | Returns the QNames used to construct the specified query. |
| `cts:element-child-geospatial-query-options` | Returns the options for the specified query. |
| `cts:element-child-geospatial-query-region` | Returns the geographical regions with which the specified query was constructed. |
| `cts:element-child-geospatial-query-weight` | Returns the weight with which the specified query was constructed. |
| `cts:element-geospatial-query` | Returns a query matching elements by name whose content  represents a point contained within the given geographic box, circle, or  polygon, or equal to the given point. Points that lie  between the southern boundary and the northern boundary of a box,  travelling northwards,  and between the western boundary and the eastern boundary of the box,  travelling eastwards, will match.  Points contained within the given radius of the center point of a circle will  match, using the curved distance on the surface of the Earth.  Points contained within the given polygon will match, using great circle arcs  over a spherical model of the Earth as edges. An error may result  if the polygon is malformed in some way.  Points equal to the a given point will match, taking into account the fact  that longitudes converge at the poles.  Using the geospatial query constructors requires a valid geospatial  license key; without a valid license key, searches that include  geospatial queries will throw an exception. |
| `cts:element-geospatial-query-element-name` | Returns the QNames used to construct the specified query. |
| `cts:element-geospatial-query-options` | Returns the options for the specified query. |
| `cts:element-geospatial-query-region` | Returns the geographical regions  with which the specified query was constructed. |
| `cts:element-geospatial-query-weight` | Returns the weight with which the specified query was constructed. |
| `cts:element-pair-geospatial-query` | Returns a query matching elements by name which has  specific element children representing latitude and longitude values for  a point contained within the given geographic box, circle, or polygon, or  equal to the given point.  Points that lie  between the southern boundary and the northern boundary of a box,  travelling northwards,  and between the western boundary and the eastern boundary of the box,  travelling eastwards, will match.  Points contained within the given radius of the center point of a circle will  match, using the curved distance on the surface of the Earth.  Points contained within the given polygon will match, using great circle arcs  over a spherical model of the Earth as edges. An error may result  if the polygon is malformed in some way.  Points equal to the a given point will match, taking into account the fact  that longitudes converge at the poles.  Using the geospatial query constructors requires a valid geospatial  license key; without a valid license key, searches that include  geospatial queries will throw an exception. |
| `cts:element-pair-geospatial-query-element-name` | Returns the QNames used to construct the specified query. |
| `cts:element-pair-geospatial-query-latitude-name` | Returns the QNames used to construct the specified query. |
| `cts:element-pair-geospatial-query-longitude-name` | Returns the QNames used to construct the specified query. |
| `cts:element-pair-geospatial-query-options` | Returns the options for the specified query. |
| `cts:element-pair-geospatial-query-region` | Returns the geographical regions with which the specified query was  constructed. |
| `cts:element-pair-geospatial-query-weight` | Returns the weight with which the specified query was constructed. |
| `cts:element-query` | Constructs a query that matches elements by name with the content  constrained by the query given in the second parameter.  Searches for matches in the specified element and all of its descendants.  If the query specified in the second parameter includes any element  attribute sub-queries, it will search attributes on the specified element  and attributes on any descendant elements. See the  second example  below). |
| `cts:element-query-element-name` | Returns the QNames used to construct the specified query. |
| `cts:element-query-query` | Returns the query used to construct the element query. |
| `cts:element-range-query` | Constructs a query that matches elements by name with range index  entry equal to a given value. Searches that use an element range query  require an element range index on the specified QName(s);  if no such range index exists, then an exception is thrown. |
| `cts:element-range-query-element-name` | Returns the QNames used to construct the specified query. |
| `cts:element-range-query-operator` | Returns the operator used to construct the specified query. |
| `cts:element-range-query-options` | Returns the options for the specified query. |
| `cts:element-range-query-value` | Returns the value used to construct the specified query. |
| `cts:element-range-query-weight` | Returns the weight with which the specified query was constructed. |
| `cts:element-value-query` | Returns a query matching elements by name with text content equal a  given phrase. cts:element-value-query only matches against  simple elements (that is, elements that contain only text and have no element  children). |
| `cts:element-value-query-element-name` | Returns the QNames used to construct the specified query. |
| `cts:element-value-query-options` | Returns the options for the specified query. |
| `cts:element-value-query-text` | Returns the text used to construct the specified query. |
| `cts:element-value-query-weight` | Returns the weight with which the specified query was constructed. |
| `cts:element-word-query` | Returns a query matching elements by name with text content containing  a given phrase. Searches only through immediate text node children of  the specified element as well as any text node children of child elements  defined in the Admin Interface as element-word-query-throughs  or phrase-throughs; does not search through any other children of  the specified element. If neither word searches nor stemmed word searches is  enabled for the target database, an XDMP-SEARCH error is thrown. |
| `cts:element-word-query-element-name` | Returns the QNames used to construct the specified query. |
| `cts:element-word-query-options` | Returns the options for the specified query. |
| `cts:element-word-query-text` | Returns the text used to construct the specified query. |
| `cts:element-word-query-weight` | Returns the weight with which the specified query was constructed. |
| `cts:false-query` | Returns a query that matches no fragments. |
| `cts:field-range-query` | Returns a cts:query matching fields by name with a  range-index entry equal to a given value. Searches with the  cts:field-range-query  constructor require a field range index on the specified field name(s);  if there is no range index configured, then an exception is thrown. |
| `cts:field-range-query-field-name` | Returns the fieldname used to construct the specified query. |
| `cts:field-range-query-operator` | Returns the operator used to construct the specified query. |
| `cts:field-range-query-options` | Returns the options for the specified query. |
| `cts:field-range-query-value` | Returns the value used to construct the specified query. |
| `cts:field-range-query-weight` | Returns the weight with which the specified query was constructed. |
| `cts:field-value-query` | Returns a query matching text content containing a given value in the  specified field. If the specified field does not exist,  cts:field-value-query throws an exception.  If the specified field does not have the index setting  field value searches enabled, either for the database or  for the specified field, then a cts:search with a  cts:field-value-query throws an exception. A field  is a named object that specified elements to include and exclude  from a search, and can include score weights for any included elements.  You create fields at the database level using the Admin Interface. For  details on fields, see the chapter on "Fields Database Settings" in the  Administrator's Guide. |
| `cts:field-value-query-field-name` | Returns the names used to construct the specified  cts:field-value-query. |
| `cts:field-value-query-options` | Returns the options for the specified  cts:field-value-query. |
| `cts:field-value-query-text` | Returns the values used to construct the specified  cts:field-value-query. |
| `cts:field-value-query-weight` | Returns the weight with which the specified query was constructed. |
| `cts:field-word-query` | Returns a query matching fields with text content containing a given  phrase. If the specified field does not exist, this function  throws an exception. A field  is a named object that specified elements to include and exclude  from a search, and can include score weights for any included elements.  You create fields at the database level using the Admin Interface. For  details on fields, see the chapter on "Fields Database Settings" in the  Administrator's Guide. |
| `cts:field-word-query-field-name` | Returns the names used to construct the specified  cts:field-word-query. |
| `cts:field-word-query-options` | Returns the options for the specified  cts:field-word-query. |
| `cts:field-word-query-text` | Returns the text used to construct the specified  cts:field-word-query. |
| `cts:field-word-query-weight` | Returns the weight with which the specified query was constructed. |
| `cts:geospatial-region-query` | Construct a query to match regions in documents   that satisfy a specified relationship relative to other regions. For   example, regions in documents that intersect with regions specified   in the search criteria. |
| `cts:geospatial-region-query-operation` | Returns the comparison operation specified when constructing the   input query. |
| `cts:geospatial-region-query-options` | Returns the options specified when constructing the input query. |
| `cts:geospatial-region-query-reference` | Returns the geospatial region path index reference(s) specified   when constructing the input query. |
| `cts:geospatial-region-query-region` | Returns the region criteria specified when constructing the   input query. |
| `cts:geospatial-region-query-weight` | Returns the weight specified when constructing the input query. |
| `cts:json-property-child-geospatial-query` | Returns a query matching json properties by name which has  specific children representing latitude and longitude values for  a point contained within the given geographic box, circle, or polygon, or  equal to the given point. Points that lie  between the southern boundary and the northern boundary of a box,  travelling northwards,  and between the western boundary and the eastern boundary of the box,  travelling eastwards, will match.  Points contained within the given radius of the center point of a circle will  match, using the curved distance on the surface of the Earth.  Points contained within the given polygon will match, using great circle arcs  over a spherical model of the Earth as edges. An error may result  if the polygon is malformed in some way.  Points equal to the a given point will match, taking into account the fact  that longitudes converge at the poles.  Using the geospatial query constructors requires a valid geospatial  license key; without a valid license key, searches that include  geospatial queries will throw an exception. |
| `cts:json-property-child-geospatial-query-child-name` | Returns the names used to construct the specified query. |
| `cts:json-property-child-geospatial-query-options` | Returns the options for the specified query. |
| `cts:json-property-child-geospatial-query-property-name` | Returns the names used to construct the specified query. |
| `cts:json-property-child-geospatial-query-region` | Returns the geographical regions with which the specified query was  constructed. |
| `cts:json-property-child-geospatial-query-weight` | Returns the weight with which the specified query was constructed. |
| `cts:json-property-geospatial-query` | Returns a query matching json properties by name whose content  represents a point contained within the given geographic box, circle, or  polygon, or equal to the given point. Points that lie  between the southern boundary and the northern boundary of a box,  travelling northwards,  and between the western boundary and the eastern boundary of the box,  travelling eastwards, will match.  Points contained within the given radius of the center point of a circle will  match, using the curved distance on the surface of the Earth.  Points contained within the given polygon will match, using great circle arcs  over a spherical model of the Earth as edges. An error may result  if the polygon is malformed in some way.  Points equal to the a given point will match, taking into account the fact  that longitudes converge at the poles.  Using the geospatial query constructors requires a valid geospatial  license key; without a valid license key, searches that include  geospatial queries will throw an exception. |
| `cts:json-property-geospatial-query-options` | Returns the options for the specified query. |
| `cts:json-property-geospatial-query-property-name` | Returns the json property names used to construct the specified query. |
| `cts:json-property-geospatial-query-region` | Returns the geographical regions  with which the specified query was constructed. |
| `cts:json-property-geospatial-query-weight` | Returns the weight with which the specified query was constructed. |
| `cts:json-property-pair-geospatial-query` | Returns a query matching json properties by name which has  specific property children representing latitude and longitude values for  a point contained within the given geographic box, circle, or polygon, or  equal to the given point.  Points that lie  between the southern boundary and the northern boundary of a box,  travelling northwards,  and between the western boundary and the eastern boundary of the box,  travelling eastwards, will match.  Points contained within the given radius of the center point of a circle will  match, using the curved distance on the surface of the Earth.  Points contained within the given polygon will match, using great circle arcs  over a spherical model of the Earth as edges. An error may result  if the polygon is malformed in some way.  Points equal to the a given point will match, taking into account the fact  that longitudes converge at the poles.  Using the geospatial query constructors requires a valid geospatial  license key; without a valid license key, searches that include  geospatial queries will throw an exception. |
| `cts:json-property-pair-geospatial-query-latitude-name` | Returns the property names used to construct the specified query. |
| `cts:json-property-pair-geospatial-query-longitude-name` | Returns the property names used to construct the specified query. |
| `cts:json-property-pair-geospatial-query-options` | Returns the options for the specified query. |
| `cts:json-property-pair-geospatial-query-property-name` | Returns the property names used to construct the specified query. |
| `cts:json-property-pair-geospatial-query-region` | Returns the geographical regions with which the specified query was  constructed. |
| `cts:json-property-pair-geospatial-query-weight` | Returns the weight with which the specified query was constructed. |
| `cts:json-property-range-query` | Returns a cts:query matching JSON properties by name with a  range-index entry equal to a given value. Searches with the  cts:json-property-range-query  constructor require a property range index on the specified names;  if there is no range index configured, then an exception is thrown. |
| `cts:json-property-range-query-operator` | Returns the operator used to construct the specified query. |
| `cts:json-property-range-query-options` | Returns the options for the specified query. |
| `cts:json-property-range-query-property-name` | Returns the JSON property name used to construct the specified query. |
| `cts:json-property-range-query-value` | Returns the value used to construct the specified query. |
| `cts:json-property-range-query-weight` | Returns the weight with which the specified query was constructed. |
| `cts:json-property-scope-query` | Returns a cts:query matching JSON properties by name  with the content constrained by the given cts:query in the  second parameter.  Searches for matches in the specified property and all of its descendants. |
| `cts:json-property-scope-query-property-name` | Returns the JSON property name used to construct the specified query. |
| `cts:json-property-scope-query-query` | Returns the query used to construct the property scope query. |
| `cts:json-property-value-query` | Returns a query matching JSON properties by name with value equal the given  value. For arrays, the query matches if the value of any elements in the array  matches the given value. |
| `cts:json-property-value-query-options` | Returns the options for the specified query. |
| `cts:json-property-value-query-property-name` | Returns the JSON property name used to construct the specified query. |
| `cts:json-property-value-query-text` | Returns the text used to construct the specified query. |
| `cts:json-property-value-query-value` | Returns the value used to construct the specified query. |
| `cts:json-property-value-query-weight` | Returns the weight with which the specified query was constructed. |
| `cts:json-property-word-query` | Returns a query matching JSON properties by name with text content containing  a given phrase. Searches only through immediate text node children of the  specified property. |
| `cts:json-property-word-query-options` | Returns the options for the specified query. |
| `cts:json-property-word-query-property-name` | Returns the name used to construct the specified query. |
| `cts:json-property-word-query-text` | Returns the text used to construct the specified query. |
| `cts:json-property-word-query-weight` | Returns the weight with which the specified query was constructed. |
| `cts:locks-fragment-query` | Returns a query that matches all documents where $query matches  document-locks. When searching documents or document-properties,  cts:locks-fragment-query provides a convenient way to  additionally constrain the search against document-locks fragments. |
| `cts:locks-fragment-query-query` | Returns the query used to construct the specified query. |
| `cts:lsqt-query` | Returns only documents before LSQT or a timestamp before LSQT for stable query results. |
| `cts:lsqt-query-options` | Returns the options for the specified query. |
| `cts:lsqt-query-temporal-collection` | Returns the name of the temporal collection used to construct specified query. |
| `cts:lsqt-query-timestamp` | Returns timestamp used to construct the specified query. |
| `cts:lsqt-query-weight` | Returns the weight with which the specified query was constructed. |
| `cts:near-query` | Returns a query matching all of the specified queries, where  the matches occur within the specified distance from each other. |
| `cts:near-query-distance` | Returns the distance used to construct the near query. |
| `cts:near-query-options` | Returns the options for the specified query. |
| `cts:near-query-queries` | Returns the query sequence used to construct the near query. |
| `cts:near-query-weight` | Returns the weight with which the specified query was constructed. |
| `cts:not-in-query` | Returns a query matching the first sub-query, where those matches do not  occur within 0 distance of the other query. |
| `cts:not-in-query-negative-query` | Returns the negative (second parameter) query used to construct the  specified query. |
| `cts:not-in-query-positive-query` | Returns the positive (first parameter) query used to construct the  specified query. |
| `cts:not-query` | Returns a query specifying the matches not specified by its sub-query. |
| `cts:not-query-query` | Returns the query used to construct the specified query. |
| `cts:not-query-weight` | Returns the weight with which the specified query was constructed. |
| `cts:or-query` | Returns a query specifying the union  of the matches specified by the sub-queries. |
| `cts:or-query-options` | Returns the options for the specified query. |
| `cts:or-query-queries` | Returns a sequence of the queries that were used to construct the specified  query. |
| `cts:path-geospatial-query` | Returns a query matching path expressions whose content  represents a point contained within the given geographic box, circle, or  polygon, or equal to the given point. Points that lie  between the southern boundary and the northern boundary of a box,  travelling northwards,  and between the western boundary and the eastern boundary of the box,  travelling eastwards, will match.  Points contained within the given radius of the center point of a circle will  match, using the curved distance on the surface of the Earth.  Points contained within the given polygon will match, using great circle arcs  over a spherical model of the Earth as edges. An error may result  if the polygon is malformed in some way.  Points equal to the a given point will match, taking into account the fact  that longitudes converge at the poles.  Using the geospatial query constructors requires a valid geospatial  license key; without a valid license key, searches that include  geospatial queries will throw an exception. |
| `cts:path-geospatial-query-options` | Returns the options for the specified query. |
| `cts:path-geospatial-query-path-expression` | Returns the path expressions used to construct the specified query. |
| `cts:path-geospatial-query-region` | Returns the geographical regions  with which the specified query was constructed. |
| `cts:path-geospatial-query-weight` | Returns the weight with which the specified query was constructed. |
| `cts:path-range-query` | Returns a cts:query matching documents where the content  addressed by an XPath expression satisfies the specified relationship  (=, <, >, etc.) with respect to the input criteria values. A path range  index must exist for each path when you perform a search. |
| `cts:path-range-query-operator` | Returns the operator used to construct the specified query. |
| `cts:path-range-query-options` | Returns the options for the specified query. |
| `cts:path-range-query-path-name` | Returns the path expression used to construct the specified query. |
| `cts:path-range-query-value` | Returns the value used to construct the specified query. |
| `cts:path-range-query-weight` | Returns the weight with which the specified query was constructed. |
| `cts:period-compare-query` | Returns a cts:query matching documents that have relevant  pair of period values. Searches with the  cts:period-compare-query  constructor require two valid names of period, if the either of the specified  period does not exist, then an exception is thrown. |
| `cts:period-compare-query-axis-1` | Returns the name of the first axis used to construct the specified query. |
| `cts:period-compare-query-axis-2` | Returns the name of the second axis used to construct the specified query. |
| `cts:period-compare-query-operator` | Returns the operator used to construct the specified query. |
| `cts:period-compare-query-options` | Returns the options for the specified query. |
| `cts:period-range-query` | Returns a cts:query matching axis by name with a  period value with an operator. Searches with the  cts:period-range-query  constructor require a axis definition on the axis name;  if there is no axis configured, then an exception is thrown. |
| `cts:period-range-query-axis` | Returns the axis name used to construct the specified query. |
| `cts:period-range-query-operator` | Returns the operator used to construct the specified query. |
| `cts:period-range-query-options` | Returns the options for the specified query. |
| `cts:period-range-query-period` | Returns the period used to construct the specified query. |
| `cts:properties-fragment-query` | Returns a query that matches all documents where $query matches  document-properties. When searching documents or document-locks,  this query type provides a convenient way to  additionally constrain the search against document-properties fragments. |
| `cts:properties-fragment-query-query` | Returns the query used to construct the specified query. |
| `cts:query` | Creates a query. |
| `cts:range-query` | Returns a cts:query matching specified nodes with a  range-index entry compared to a given value. Searches with the  cts:range-query  constructor require a range index;  if there is no range index configured, then an exception is thrown. |
| `cts:range-query-index` | Returns the range index used to construct the specified query. |
| `cts:range-query-operator` | Returns the operator used to construct the specified query. |
| `cts:range-query-options` | Returns the options for the specified query. |
| `cts:range-query-value` | Returns the value used to construct the specified query. |
| `cts:range-query-weight` | Returns the weight with which the specified query was constructed. |
| `cts:registered-query` | Returns a query matching fragments specified by previously registered  queries (see cts:register). If  the database is not empty and a registered query with the specified ID(s)  is not found, then a cts:search operation with an invalid  cts:registered-query throws an XDMP-UNREGISTERED exception. |
| `cts:registered-query-ids` | Returns the registered query identifiers used to construct the specified  query. |
| `cts:registered-query-options` | Returns the options for the specified query. |
| `cts:registered-query-weight` | Returns the weight with which the specified query was constructed. |
| `cts:reverse-query` | Construct a query that matches serialized cts queries, based on a  set of model input nodes. A serialized query matches if it would  match the model nodes. Use with a cts:search or  cts:contains over serialized cts:query nodes. |
| `cts:reverse-query-nodes` | Returns the nodes used to construct the specified query. |
| `cts:reverse-query-weight` | Returns the weight with which the specified query was constructed. |
| `cts:similar-query` | Returns a query matching nodes similar to the model nodes. It uses an  algorithm which finds the most "relevant" terms in the model nodes  (that is, the terms with the highest scores), and then creates a  query equivalent to a cts:or-query of those terms. By default  16 terms are used. |
| `cts:similar-query-nodes` | Returns the nodes used to construct the specified query. |
| `cts:similar-query-weight` | Returns the weight with which the specified query was constructed. |
| `cts:triple-range-query` | Returns a  cts:query  matching triples with a  triple index entry equal to the given values. Searches with the  cts:triple-range-query  constructor require the triple index;  if the triple index is not configured, then an exception is thrown. |
| `cts:triple-range-query-object` | Returns the object value used to construct the specified query. |
| `cts:triple-range-query-operator` | Returns the operators used to construct the specified query. |
| `cts:triple-range-query-options` | Returns the options for the specified query. |
| `cts:triple-range-query-predicate` | Returns the predicate value used to construct the specified query. |
| `cts:triple-range-query-subject` | Returns the subject value used to construct the specified query. |
| `cts:triple-range-query-weight` | Returns the weight with which the specified query was constructed. |
| `cts:true-query` | Returns a query that matches all fragments. |
| `cts:word-query` | Returns a query matching text content containing a given phrase. |
| `cts:word-query-options` | Returns the options for the specified query. |
| `cts:word-query-text` | Returns the text used to construct the specified query. |
| `cts:word-query-weight` | Returns the weight with which the specified query was constructed. |

### General

*Detailed documentation: [functions/general.md](functions/general.md)*

| Function | Summary |
|----------|---------|
| `search:check-options` | This function verifies that options XML is 		 properly structured. Used in debugging, normally not 		 in production. Returns the empty sequence on success, 		 otherwise it returns one or more error messages 		 inside <report> elements. |
| `search:estimate` | This function quickly estimates the number of hits a query will return.    The result is unfiltered and reflects the index resolution of the search. |
| `search:get-default-options` | This function returns the default options 		 XML. Default options do not contain any constraints 		 or anything else that requires specific index 		 settings. |
| `search:parse` | This function parses query text according    to given options and returns the appropriate    cts:query XML. If the query string to be parsed does not    conform to the query grammar, the behavior differs, depending on the    value of $output:    	cts:query throws a reportable error. 	search:query throws away the terms after the 	location of the parse error and runs the query with the terms 	before the location of the parse error, typically broadening the 	query.       MarkLogic recommends that you use cts:query for parsing    text. |
| `search:remove-constraint` | NOTE: This function is deprecated. This function safely      removes a token from query text, 		 ensuring that grammar elements (AND, OR, quotes, 		 parentheses) are handled properly. |
| `search:resolve` | This function is the same as 		 search:search, except that it takes 		 a parsed and annotated cts:query XML node or a    structured search search:query XML node as 		 input. |
| `search:resolve-nodes` | This function performs the same search as 		 search:search, but it takes 		 a parsed and annotated cts:query XML node or a    structured search search:query XML node as 		 input and returns the actual result nodes from the database. |
| `search:search` | This function parses and invokes a query according to          specified options, returning up to $page-length result nodes          starting from $start. |
| `search:snippet` | This function extracts matching text from the 		 result node based on options, and returns the matches 		 wrapped in a containing node, with highlights 		 tagged. |
| `search:suggest` | This function returns a sequence of suggested text 		 strings that match a wildcarded search for the 		 $qtext input, ready for use in a user 		 interface. Typically this is used for type-ahead 		 applications to provide the user 		 suggestions while entering terms in a search box. |
| `search:unparse` | NOTE: This function is deprecated. Turn a serialized,     annotated cts:query (typically from 		search:parse) back into query text according to     the specified rules. |
| `search:values` | This function returns lexicon values and co-occurrences,   and allows you to calculate aggregates based on the lexicon values. |

## Alphabetical Index

Each function links to its detailed documentation file.

- [`cts:after-query`](functions/cts-query-constructors.md) - Returns a query matching fragments committed after a specified timestamp
- [`cts:after-query-timestamp`](functions/cts-query-constructors.md) - Returns the timestamp with which a specified query was constructed
- [`cts:and-not-query`](functions/cts-query-constructors.md) - Returns a query specifying the set difference of
  the matches specified by two sub-queries
- [`cts:and-not-query-negative-query`](functions/cts-query-constructors.md) - Returns the negative (second parameter) query used to construct the
  specified query
- [`cts:and-not-query-positive-query`](functions/cts-query-constructors.md) - Returns the positive (first parameter) query used to construct the
  specified query
- [`cts:and-query`](functions/cts-query-constructors.md) - Returns a query specifying the intersection
  of the matches specified by the sub-queries
- [`cts:and-query-options`](functions/cts-query-constructors.md) - Returns the options for the specified query
- [`cts:and-query-queries`](functions/cts-query-constructors.md) - Returns a sequence of the queries that were used to construct the specified
  query
- [`cts:before-query`](functions/cts-query-constructors.md) - Returns a query matching fragments committed before or at a specified timestamp
- [`cts:before-query-timestamp`](functions/cts-query-constructors.md) - Returns the timestamp with which a specified query was constructed
- [`cts:boost-query`](functions/cts-query-constructors.md) - Returns a query specifying that matches to $matching-query
  should have their search relevance scores boosted if they also match
  $boosting-query
- [`cts:boost-query-boosting-query`](functions/cts-query-constructors.md) - Returns the boosting (second parameter) query used to construct the
  specified boost query
- [`cts:boost-query-matching-query`](functions/cts-query-constructors.md) - Returns the matching (first parameter) query used to construct the
  specified boost query
- [`cts:collection-match`](functions/lexicon.md) - Returns values from the collection lexicon
   that match the specified wildcard pattern
- [`cts:collection-query`](functions/cts-query-constructors.md) - Match documents in at least one of the specified collections
- [`cts:collection-query-uris`](functions/cts-query-constructors.md) - Returns the URIs used to construct the specified query
- [`cts:collection-reference`](functions/lexicon.md) - Creates a reference to the collection lexicon, for use as a parameter to
  cts:value-tuples
- [`cts:collections`](functions/lexicon.md) - Returns values from the collection lexicon
- [`cts:column-range-query`](functions/cts-query-constructors.md) - Returns a 
  cts:query
  matching documents matching a TDE-view column equals to an value
- [`cts:confidence`](functions/search.md) - Returns the confidence of a node,
  or of the context node if no node is provided
- [`cts:confidence-order`](functions/cts-order-constructors.md) - Creates a confidence-based ordering clause, for use as an option to
  
  cts:search
- [`cts:contains`](functions/search.md) - Returns true if any of a sequence of values matches a query
- [`cts:deregister`](functions/search.md) - Deregister a registered query, explicitly releasing the associated
  resources
- [`cts:directory-query`](functions/cts-query-constructors.md) - Returns a query matching documents in the directories with the given URIs
- [`cts:directory-query-depth`](functions/cts-query-constructors.md) - Returns the depth used to construct the specified query
- [`cts:directory-query-uris`](functions/cts-query-constructors.md) - Returns the URIs used to construct the specified query
- [`cts:distinctive-terms`](functions/search.md) - Return the most "relevant" terms in the model nodes (that is, the
  terms with the highest scores)
- [`cts:document-format-query`](functions/cts-query-constructors.md) - Returns a query matching documents of a given format
- [`cts:document-format-query-format`](functions/cts-query-constructors.md) - Returns the formt used to construct the specified query
- [`cts:document-fragment-query`](functions/cts-query-constructors.md) - Returns a query that matches all documents where $query matches
  any document fragment
- [`cts:document-fragment-query-query`](functions/cts-query-constructors.md) - Returns the query used to construct the specified query
- [`cts:document-order`](functions/cts-order-constructors.md) - Creates a document-based ordering clause, for use as an option to
  
  cts:search
- [`cts:document-permission-query`](functions/cts-query-constructors.md) - Returns a query matching documents with a given permission
- [`cts:document-permission-query-capability`](functions/cts-query-constructors.md) - Returns the capability used to construct the specified query
- [`cts:document-query`](functions/cts-query-constructors.md) - Returns a query matching documents with the given URIs
- [`cts:document-query-uris`](functions/cts-query-constructors.md) - Returns the URIs used to construct the specified query
- [`cts:document-root-query`](functions/cts-query-constructors.md) - Returns a query matching documents with a given root element
- [`cts:document-root-query-root`](functions/cts-query-constructors.md) - Returns the QName used to construct the specified query
- [`cts:element-attribute-pair-geospatial-query`](functions/cts-query-constructors.md) - Returns a query matching elements by name which has
  specific attributes representing latitude and longitude values for
  a point contained within the given geographic box, circle, or polygon,
  or equal to the given point
- [`cts:element-attribute-pair-geospatial-query-element-name`](functions/cts-query-constructors.md) - Returns the QNames used to construct the specified query
- [`cts:element-attribute-pair-geospatial-query-latitude-name`](functions/cts-query-constructors.md) - Returns the QNames used to construct the specified query
- [`cts:element-attribute-pair-geospatial-query-longitude-name`](functions/cts-query-constructors.md) - Returns the QNames used to construct the specified query
- [`cts:element-attribute-pair-geospatial-query-options`](functions/cts-query-constructors.md) - Returns the options for the specified query
- [`cts:element-attribute-pair-geospatial-query-region`](functions/cts-query-constructors.md) - Returns the geographical regions with which the specified query was constructed
- [`cts:element-attribute-pair-geospatial-query-weight`](functions/cts-query-constructors.md) - Returns the weight with which the specified query was constructed
- [`cts:element-attribute-range-query`](functions/cts-query-constructors.md) - Constructs a query that matches element-attributes by name with a
  range-index entry equal to a given value
- [`cts:element-attribute-range-query-attribute-name`](functions/cts-query-constructors.md) - Returns the QNames used to construct the specified query
- [`cts:element-attribute-range-query-element-name`](functions/cts-query-constructors.md) - Returns the QNames used to construct the specified query
- [`cts:element-attribute-range-query-operator`](functions/cts-query-constructors.md) - Returns the operator used to construct the specified query
- [`cts:element-attribute-range-query-options`](functions/cts-query-constructors.md) - Returns the options for the specified query
- [`cts:element-attribute-range-query-value`](functions/cts-query-constructors.md) - Returns the value used to construct the specified query
- [`cts:element-attribute-range-query-weight`](functions/cts-query-constructors.md) - Returns the weight with which the specified query was constructed
- [`cts:element-attribute-reference`](functions/lexicon.md) - Creates a reference to an element attribute value lexicon, for use as a
  parameter to cts:value-tuples
- [`cts:element-attribute-value-co-occurrences`](functions/lexicon.md) - Returns value co-occurrences from the specified element or element-attribute
  value lexicon(s)
- [`cts:element-attribute-value-match`](functions/lexicon.md) - Returns values from the specified element-attribute value lexicon(s)
   that match the specified pattern
- [`cts:element-attribute-value-query`](functions/cts-query-constructors.md) - Returns a query matching elements by name with attributes by name
  with text content equal a given phrase
- [`cts:element-attribute-value-query-attribute-name`](functions/cts-query-constructors.md) - Returns the attribute QNames used to construct the specified query
- [`cts:element-attribute-value-query-element-name`](functions/cts-query-constructors.md) - Returns the element QNames used to construct the specified query
- [`cts:element-attribute-value-query-options`](functions/cts-query-constructors.md) - Returns the options for the specified query
- [`cts:element-attribute-value-query-text`](functions/cts-query-constructors.md) - Returns the text used to construct the specified query
- [`cts:element-attribute-value-query-weight`](functions/cts-query-constructors.md) - Returns the weight with which the specified query was constructed
- [`cts:element-attribute-value-ranges`](functions/lexicon.md) - Returns value ranges from the specified element-attribute value lexicon(s)
- [`cts:element-attribute-values`](functions/lexicon.md) - Returns values from the specified element-attribute value lexicon(s)
- [`cts:element-attribute-word-match`](functions/lexicon.md) - Returns words from the specified element-attribute word lexicon(s) that
  match a wildcard pattern
- [`cts:element-attribute-word-query`](functions/cts-query-constructors.md) - Returns a query matching elements by name
  with attributes by name
  with text content containing a given phrase
- [`cts:element-attribute-word-query-attribute-name`](functions/cts-query-constructors.md) - Returns the attribute QNames used to construct the specified query
- [`cts:element-attribute-word-query-element-name`](functions/cts-query-constructors.md) - Returns the element QNames used to construct the specified query
- [`cts:element-attribute-word-query-options`](functions/cts-query-constructors.md) - Returns the options for the specified query
- [`cts:element-attribute-word-query-text`](functions/cts-query-constructors.md) - Returns the text used to construct the specified query
- [`cts:element-attribute-word-query-weight`](functions/cts-query-constructors.md) - Returns the weight with which the specified query was constructed
- [`cts:element-attribute-words`](functions/lexicon.md) - Returns words from the specified element-attribute word lexicon(s)
- [`cts:element-child-geospatial-query`](functions/cts-query-constructors.md) - Returns a query matching elements by name which has
  specific element children representing latitude and longitude values for
  a point contained within the given geographic box, circle, or polygon, or
  equal to the given point
- [`cts:element-child-geospatial-query-child-name`](functions/cts-query-constructors.md) - Returns the QNames used to construct the specified query
- [`cts:element-child-geospatial-query-element-name`](functions/cts-query-constructors.md) - Returns the QNames used to construct the specified query
- [`cts:element-child-geospatial-query-options`](functions/cts-query-constructors.md) - Returns the options for the specified query
- [`cts:element-child-geospatial-query-region`](functions/cts-query-constructors.md) - Returns the geographical regions with which the specified query was constructed
- [`cts:element-child-geospatial-query-weight`](functions/cts-query-constructors.md) - Returns the weight with which the specified query was constructed
- [`cts:element-geospatial-query`](functions/cts-query-constructors.md) - Returns a query matching elements by name whose content
  represents a point contained within the given geographic box, circle, or
  polygon, or equal to the given point
- [`cts:element-geospatial-query-element-name`](functions/cts-query-constructors.md) - Returns the QNames used to construct the specified query
- [`cts:element-geospatial-query-options`](functions/cts-query-constructors.md) - Returns the options for the specified query
- [`cts:element-geospatial-query-region`](functions/cts-query-constructors.md) - Returns the geographical regions
  with which the specified query was constructed
- [`cts:element-geospatial-query-weight`](functions/cts-query-constructors.md) - Returns the weight with which the specified query was constructed
- [`cts:element-pair-geospatial-query`](functions/cts-query-constructors.md) - Returns a query matching elements by name which has
  specific element children representing latitude and longitude values for
  a point contained within the given geographic box, circle, or polygon, or
  equal to the given point
- [`cts:element-pair-geospatial-query-element-name`](functions/cts-query-constructors.md) - Returns the QNames used to construct the specified query
- [`cts:element-pair-geospatial-query-latitude-name`](functions/cts-query-constructors.md) - Returns the QNames used to construct the specified query
- [`cts:element-pair-geospatial-query-longitude-name`](functions/cts-query-constructors.md) - Returns the QNames used to construct the specified query
- [`cts:element-pair-geospatial-query-options`](functions/cts-query-constructors.md) - Returns the options for the specified query
- [`cts:element-pair-geospatial-query-region`](functions/cts-query-constructors.md) - Returns the geographical regions with which the specified query was
  constructed
- [`cts:element-pair-geospatial-query-weight`](functions/cts-query-constructors.md) - Returns the weight with which the specified query was constructed
- [`cts:element-query`](functions/cts-query-constructors.md) - Constructs a query that matches elements by name with the content
  constrained by the query given in the second parameter
- [`cts:element-query-element-name`](functions/cts-query-constructors.md) - Returns the QNames used to construct the specified query
- [`cts:element-query-query`](functions/cts-query-constructors.md) - Returns the query used to construct the element query
- [`cts:element-range-query`](functions/cts-query-constructors.md) - Constructs a query that matches elements by name with range index
  entry equal to a given value
- [`cts:element-range-query-element-name`](functions/cts-query-constructors.md) - Returns the QNames used to construct the specified query
- [`cts:element-range-query-operator`](functions/cts-query-constructors.md) - Returns the operator used to construct the specified query
- [`cts:element-range-query-options`](functions/cts-query-constructors.md) - Returns the options for the specified query
- [`cts:element-range-query-value`](functions/cts-query-constructors.md) - Returns the value used to construct the specified query
- [`cts:element-range-query-weight`](functions/cts-query-constructors.md) - Returns the weight with which the specified query was constructed
- [`cts:element-reference`](functions/lexicon.md) - Creates a reference to an element value lexicon, for use as a parameter to
  cts:value-tuples,
  temporal:axis-create, or any
  other function that takes an index reference
- [`cts:element-value-co-occurrences`](functions/lexicon.md) - Returns value co-occurrences (that is, pairs of values, both of which appear
  in the same fragment) from the specified element value lexicon(s)
- [`cts:element-value-match`](functions/lexicon.md) - Returns values from the specified element value lexicon(s)
   that match the specified wildcard pattern
- [`cts:element-value-query`](functions/cts-query-constructors.md) - Returns a query matching elements by name with text content equal a
  given phrase
- [`cts:element-value-query-element-name`](functions/cts-query-constructors.md) - Returns the QNames used to construct the specified query
- [`cts:element-value-query-options`](functions/cts-query-constructors.md) - Returns the options for the specified query
- [`cts:element-value-query-text`](functions/cts-query-constructors.md) - Returns the text used to construct the specified query
- [`cts:element-value-query-weight`](functions/cts-query-constructors.md) - Returns the weight with which the specified query was constructed
- [`cts:element-value-ranges`](functions/lexicon.md) - Returns value ranges from the specified element value lexicon(s)
- [`cts:element-values`](functions/lexicon.md) - Returns values from the specified element value lexicon(s)
- [`cts:element-walk`](functions/search.md) - Returns a copy of the node, replacing any elements found
  with the specified expression
- [`cts:element-word-match`](functions/lexicon.md) - Returns words from the specified element word lexicon(s) that match
  a wildcard pattern
- [`cts:element-word-query`](functions/cts-query-constructors.md) - Returns a query matching elements by name with text content containing
  a given phrase
- [`cts:element-word-query-element-name`](functions/cts-query-constructors.md) - Returns the QNames used to construct the specified query
- [`cts:element-word-query-options`](functions/cts-query-constructors.md) - Returns the options for the specified query
- [`cts:element-word-query-text`](functions/cts-query-constructors.md) - Returns the text used to construct the specified query
- [`cts:element-word-query-weight`](functions/cts-query-constructors.md) - Returns the weight with which the specified query was constructed
- [`cts:element-words`](functions/lexicon.md) - Returns words from the specified element word lexicon
- [`cts:entity`](functions/search.md) - Returns a cts:entity object
- [`cts:entity-dictionary`](functions/search.md) - Returns a cts:entity-dictionary object
- [`cts:entity-dictionary-get`](functions/search.md) - Retrieve an entity dictionary previously cached in the database
- [`cts:entity-dictionary-parse`](functions/search.md) - Construct a cts:entity-dictionary object by parsing it from a formatted string
- [`cts:entity-highlight`](functions/search.md) - Returns a copy of the node, replacing any entities found
  with the specified expression
- [`cts:entity-walk`](functions/search.md) - Walk an XML document or element node, evaluating an
   expression
   against any matching entities
- [`cts:false-query`](functions/cts-query-constructors.md) - Returns a query that matches no fragments
- [`cts:field-range-query`](functions/cts-query-constructors.md) - Returns a cts:query matching fields by name with a
  range-index entry equal to a given value
- [`cts:field-range-query-field-name`](functions/cts-query-constructors.md) - Returns the fieldname used to construct the specified query
- [`cts:field-range-query-operator`](functions/cts-query-constructors.md) - Returns the operator used to construct the specified query
- [`cts:field-range-query-options`](functions/cts-query-constructors.md) - Returns the options for the specified query
- [`cts:field-range-query-value`](functions/cts-query-constructors.md) - Returns the value used to construct the specified query
- [`cts:field-range-query-weight`](functions/cts-query-constructors.md) - Returns the weight with which the specified query was constructed
- [`cts:field-reference`](functions/lexicon.md) - Creates a reference to a field value lexicon, for use as a
  parameter to 
  cts:value-tuples
- [`cts:field-value-co-occurrences`](functions/lexicon.md) - Returns value co-occurrences (that is, pairs of values, both of which appear
  in the same fragment) from the specified field value lexicon(s)
- [`cts:field-value-match`](functions/lexicon.md) - Returns values from the specified field value lexicon(s)
   that match the specified wildcard pattern
- [`cts:field-value-query`](functions/cts-query-constructors.md) - Returns a query matching text content containing a given value in the
  specified field
- [`cts:field-value-query-field-name`](functions/cts-query-constructors.md) - Returns the names used to construct the specified
  cts:field-value-query
- [`cts:field-value-query-options`](functions/cts-query-constructors.md) - Returns the options for the specified
  cts:field-value-query
- [`cts:field-value-query-text`](functions/cts-query-constructors.md) - Returns the values used to construct the specified
  cts:field-value-query
- [`cts:field-value-query-weight`](functions/cts-query-constructors.md) - Returns the weight with which the specified query was constructed
- [`cts:field-value-ranges`](functions/lexicon.md) - Returns value ranges from the specified field value lexicon(s)
- [`cts:field-values`](functions/lexicon.md) - Returns values from the specified field value lexicon(s)
- [`cts:field-word-match`](functions/lexicon.md) - Returns words from the specified field word lexicon(s) that match
  a wildcard pattern
- [`cts:field-word-query`](functions/cts-query-constructors.md) - Returns a query matching fields with text content containing a given
  phrase
- [`cts:field-word-query-field-name`](functions/cts-query-constructors.md) - Returns the names used to construct the specified
  cts:field-word-query
- [`cts:field-word-query-options`](functions/cts-query-constructors.md) - Returns the options for the specified
  cts:field-word-query
- [`cts:field-word-query-text`](functions/cts-query-constructors.md) - Returns the text used to construct the specified
  cts:field-word-query
- [`cts:field-word-query-weight`](functions/cts-query-constructors.md) - Returns the weight with which the specified query was constructed
- [`cts:field-words`](functions/lexicon.md) - Returns words from the specified field word lexicon
- [`cts:fitness`](functions/search.md) - Returns the fitness of a node,
  or of the context node if no node is provided
- [`cts:fitness-order`](functions/cts-order-constructors.md) - Creates a fitness-based ordering clause, for use as an option to
  
  cts:search
- [`cts:frequency`](functions/lexicon.md) - Returns an integer representing the number of times in which a particular
  value occurs in a value lexicon lookup
- [`cts:geospatial-region-query`](functions/cts-query-constructors.md) - Construct a query to match regions in documents
    that satisfy a specified relationship relative to other regions
- [`cts:geospatial-region-query-operation`](functions/cts-query-constructors.md) - Returns the comparison operation specified when constructing the
    input query
- [`cts:geospatial-region-query-options`](functions/cts-query-constructors.md) - Returns the options specified when constructing the input query
- [`cts:geospatial-region-query-reference`](functions/cts-query-constructors.md) - Returns the geospatial region path index reference(s) specified
    when constructing the input query
- [`cts:geospatial-region-query-region`](functions/cts-query-constructors.md) - Returns the region criteria specified when constructing the
    input query
- [`cts:geospatial-region-query-weight`](functions/cts-query-constructors.md) - Returns the weight specified when constructing the input query
- [`cts:highlight`](functions/search.md) - Returns a copy of the node, replacing any text matching the query
  with the specified expression
- [`cts:index-order`](functions/cts-order-constructors.md) - Creates a index-based ordering clause, for use as an option to
  
  cts:search
- [`cts:iri-reference`](functions/lexicon.md) - Creates a reference to the URI lexicon, for use as a parameter to
  cts:value-tuples
- [`cts:json-property-child-geospatial-query`](functions/cts-query-constructors.md) - Returns a query matching json properties by name which has
  specific children representing latitude and longitude values for
  a point contained within the given geographic box, circle, or polygon, or
  equal to the given point
- [`cts:json-property-child-geospatial-query-child-name`](functions/cts-query-constructors.md) - Returns the names used to construct the specified query
- [`cts:json-property-child-geospatial-query-options`](functions/cts-query-constructors.md) - Returns the options for the specified query
- [`cts:json-property-child-geospatial-query-property-name`](functions/cts-query-constructors.md) - Returns the names used to construct the specified query
- [`cts:json-property-child-geospatial-query-region`](functions/cts-query-constructors.md) - Returns the geographical regions with which the specified query was
  constructed
- [`cts:json-property-child-geospatial-query-weight`](functions/cts-query-constructors.md) - Returns the weight with which the specified query was constructed
- [`cts:json-property-geospatial-query`](functions/cts-query-constructors.md) - Returns a query matching json properties by name whose content
  represents a point contained within the given geographic box, circle, or
  polygon, or equal to the given point
- [`cts:json-property-geospatial-query-options`](functions/cts-query-constructors.md) - Returns the options for the specified query
- [`cts:json-property-geospatial-query-property-name`](functions/cts-query-constructors.md) - Returns the json property names used to construct the specified query
- [`cts:json-property-geospatial-query-region`](functions/cts-query-constructors.md) - Returns the geographical regions
  with which the specified query was constructed
- [`cts:json-property-geospatial-query-weight`](functions/cts-query-constructors.md) - Returns the weight with which the specified query was constructed
- [`cts:json-property-pair-geospatial-query`](functions/cts-query-constructors.md) - Returns a query matching json properties by name which has
  specific property children representing latitude and longitude values for
  a point contained within the given geographic box, circle, or polygon, or
  equal to the given point
- [`cts:json-property-pair-geospatial-query-latitude-name`](functions/cts-query-constructors.md) - Returns the property names used to construct the specified query
- [`cts:json-property-pair-geospatial-query-longitude-name`](functions/cts-query-constructors.md) - Returns the property names used to construct the specified query
- [`cts:json-property-pair-geospatial-query-options`](functions/cts-query-constructors.md) - Returns the options for the specified query
- [`cts:json-property-pair-geospatial-query-property-name`](functions/cts-query-constructors.md) - Returns the property names used to construct the specified query
- [`cts:json-property-pair-geospatial-query-region`](functions/cts-query-constructors.md) - Returns the geographical regions with which the specified query was
  constructed
- [`cts:json-property-pair-geospatial-query-weight`](functions/cts-query-constructors.md) - Returns the weight with which the specified query was constructed
- [`cts:json-property-range-query`](functions/cts-query-constructors.md) - Returns a cts:query matching JSON properties by name with a
  range-index entry equal to a given value
- [`cts:json-property-range-query-operator`](functions/cts-query-constructors.md) - Returns the operator used to construct the specified query
- [`cts:json-property-range-query-options`](functions/cts-query-constructors.md) - Returns the options for the specified query
- [`cts:json-property-range-query-property-name`](functions/cts-query-constructors.md) - Returns the JSON property name used to construct the specified query
- [`cts:json-property-range-query-value`](functions/cts-query-constructors.md) - Returns the value used to construct the specified query
- [`cts:json-property-range-query-weight`](functions/cts-query-constructors.md) - Returns the weight with which the specified query was constructed
- [`cts:json-property-reference`](functions/lexicon.md) - Creates a reference to a JSON property value lexicon, for use as a parameter
  to cts:value-tuples
- [`cts:json-property-scope-query`](functions/cts-query-constructors.md) - Returns a cts:query matching JSON properties by name
  with the content constrained by the given cts:query in the
  second parameter
- [`cts:json-property-scope-query-property-name`](functions/cts-query-constructors.md) - Returns the JSON property name used to construct the specified query
- [`cts:json-property-scope-query-query`](functions/cts-query-constructors.md) - Returns the query used to construct the property scope query
- [`cts:json-property-value-query`](functions/cts-query-constructors.md) - Returns a query matching JSON properties by name with value equal the given
  value
- [`cts:json-property-value-query-options`](functions/cts-query-constructors.md) - Returns the options for the specified query
- [`cts:json-property-value-query-property-name`](functions/cts-query-constructors.md) - Returns the JSON property name used to construct the specified query
- [`cts:json-property-value-query-text`](functions/cts-query-constructors.md) - Returns the text used to construct the specified query
- [`cts:json-property-value-query-value`](functions/cts-query-constructors.md) - Returns the value used to construct the specified query
- [`cts:json-property-value-query-weight`](functions/cts-query-constructors.md) - Returns the weight with which the specified query was constructed
- [`cts:json-property-word-match`](functions/lexicon.md) - Returns words from the specified JSON property word lexicon(s) that match
  a wildcard pattern
- [`cts:json-property-word-query`](functions/cts-query-constructors.md) - Returns a query matching JSON properties by name with text content containing
  a given phrase
- [`cts:json-property-word-query-options`](functions/cts-query-constructors.md) - Returns the options for the specified query
- [`cts:json-property-word-query-property-name`](functions/cts-query-constructors.md) - Returns the name used to construct the specified query
- [`cts:json-property-word-query-text`](functions/cts-query-constructors.md) - Returns the text used to construct the specified query
- [`cts:json-property-word-query-weight`](functions/cts-query-constructors.md) - Returns the weight with which the specified query was constructed
- [`cts:json-property-words`](functions/lexicon.md) - Returns words from the specified JSON property word lexicon
- [`cts:locks-fragment-query`](functions/cts-query-constructors.md) - Returns a query that matches all documents where $query matches
  document-locks
- [`cts:locks-fragment-query-query`](functions/cts-query-constructors.md) - Returns the query used to construct the specified query
- [`cts:lsqt-query`](functions/cts-query-constructors.md) - Returns only documents before LSQT or a timestamp before LSQT for
stable query results
- [`cts:lsqt-query-options`](functions/cts-query-constructors.md) - Returns the options for the specified query
- [`cts:lsqt-query-temporal-collection`](functions/cts-query-constructors.md) - Returns the name of the temporal collection used to construct specified query
- [`cts:lsqt-query-timestamp`](functions/cts-query-constructors.md) - Returns timestamp used to construct the specified query
- [`cts:lsqt-query-weight`](functions/cts-query-constructors.md) - Returns the weight with which the specified query was constructed
- [`cts:near-query`](functions/cts-query-constructors.md) - Returns a query matching all of the specified queries, where
  the matches occur within the specified distance from each other
- [`cts:near-query-distance`](functions/cts-query-constructors.md) - Returns the distance used to construct the near query
- [`cts:near-query-options`](functions/cts-query-constructors.md) - Returns the options for the specified query
- [`cts:near-query-queries`](functions/cts-query-constructors.md) - Returns the query sequence used to construct the near query
- [`cts:near-query-weight`](functions/cts-query-constructors.md) - Returns the weight with which the specified query was constructed
- [`cts:not-in-query`](functions/cts-query-constructors.md) - Returns a query matching the first sub-query, where those matches do not
  occur within 0 distance of the other query
- [`cts:not-in-query-negative-query`](functions/cts-query-constructors.md) - Returns the negative (second parameter) query used to construct the
  specified query
- [`cts:not-in-query-positive-query`](functions/cts-query-constructors.md) - Returns the positive (first parameter) query used to construct the
  specified query
- [`cts:not-query`](functions/cts-query-constructors.md) - Returns a query specifying the matches not specified by its sub-query
- [`cts:not-query-query`](functions/cts-query-constructors.md) - Returns the query used to construct the specified query
- [`cts:not-query-weight`](functions/cts-query-constructors.md) - Returns the weight with which the specified query was constructed
- [`cts:or-query`](functions/cts-query-constructors.md) - Returns a query specifying the union
  of the matches specified by the sub-queries
- [`cts:or-query-options`](functions/cts-query-constructors.md) - Returns the options for the specified query
- [`cts:or-query-queries`](functions/cts-query-constructors.md) - Returns a sequence of the queries that were used to construct the specified
  query
- [`cts:parse`](functions/search.md) - Parses a query string
- [`cts:part-of-speech`](functions/search.md) - Returns the part of speech for a cts:token, if any
- [`cts:path-geospatial-query`](functions/cts-query-constructors.md) - Returns a query matching path expressions whose content
  represents a point contained within the given geographic box, circle, or
  polygon, or equal to the given point
- [`cts:path-geospatial-query-options`](functions/cts-query-constructors.md) - Returns the options for the specified query
- [`cts:path-geospatial-query-path-expression`](functions/cts-query-constructors.md) - Returns the path expressions used to construct the specified query
- [`cts:path-geospatial-query-region`](functions/cts-query-constructors.md) - Returns the geographical regions
  with which the specified query was constructed
- [`cts:path-geospatial-query-weight`](functions/cts-query-constructors.md) - Returns the weight with which the specified query was constructed
- [`cts:path-range-query`](functions/cts-query-constructors.md) - Returns a cts:query matching documents where the content
  addressed by an XPath expression satisfies the specified relationship
  (=, <, >, etc
- [`cts:path-range-query-operator`](functions/cts-query-constructors.md) - Returns the operator used to construct the specified query
- [`cts:path-range-query-options`](functions/cts-query-constructors.md) - Returns the options for the specified query
- [`cts:path-range-query-path-name`](functions/cts-query-constructors.md) - Returns the path expression used to construct the specified query
- [`cts:path-range-query-value`](functions/cts-query-constructors.md) - Returns the value used to construct the specified query
- [`cts:path-range-query-weight`](functions/cts-query-constructors.md) - Returns the weight with which the specified query was constructed
- [`cts:path-reference`](functions/lexicon.md) - Creates a reference to a path value lexicon, for use as a
  parameter to cts:value-tuples
- [`cts:period-compare-query`](functions/cts-query-constructors.md) - Returns a cts:query matching documents that have relevant
  pair of period values
- [`cts:period-compare-query-axis-1`](functions/cts-query-constructors.md) - Returns the name of the first axis used to construct the specified query
- [`cts:period-compare-query-axis-2`](functions/cts-query-constructors.md) - Returns the name of the second axis used to construct the specified query
- [`cts:period-compare-query-operator`](functions/cts-query-constructors.md) - Returns the operator used to construct the specified query
- [`cts:period-compare-query-options`](functions/cts-query-constructors.md) - Returns the options for the specified query
- [`cts:period-range-query`](functions/cts-query-constructors.md) - Returns a cts:query matching axis by name with a
  period value with an operator
- [`cts:period-range-query-axis`](functions/cts-query-constructors.md) - Returns the axis name used to construct the specified query
- [`cts:period-range-query-operator`](functions/cts-query-constructors.md) - Returns the operator used to construct the specified query
- [`cts:period-range-query-options`](functions/cts-query-constructors.md) - Returns the options for the specified query
- [`cts:period-range-query-period`](functions/cts-query-constructors.md) - Returns the period used to construct the specified query
- [`cts:properties-fragment-query`](functions/cts-query-constructors.md) - Returns a query that matches all documents where $query matches
  document-properties
- [`cts:properties-fragment-query-query`](functions/cts-query-constructors.md) - Returns the query used to construct the specified query
- [`cts:quality`](functions/search.md) - Returns the quality of a node,
  or of the context node if no node is provided
- [`cts:quality-order`](functions/cts-order-constructors.md) - Creates a quality-based ordering clause, for use as an option to
  
  cts:search
- [`cts:query`](functions/cts-query-constructors.md) - Creates a query
- [`cts:range-query`](functions/cts-query-constructors.md) - Returns a cts:query matching specified nodes with a
  range-index entry compared to a given value
- [`cts:range-query-index`](functions/cts-query-constructors.md) - Returns the range index used to construct the specified query
- [`cts:range-query-operator`](functions/cts-query-constructors.md) - Returns the operator used to construct the specified query
- [`cts:range-query-options`](functions/cts-query-constructors.md) - Returns the options for the specified query
- [`cts:range-query-value`](functions/cts-query-constructors.md) - Returns the value used to construct the specified query
- [`cts:range-query-weight`](functions/cts-query-constructors.md) - Returns the weight with which the specified query was constructed
- [`cts:reference-collation`](functions/lexicon.md) - Accessor for the collation of a reference to a string value lexicon
- [`cts:reference-coordinate-system`](functions/lexicon.md) - Accessor for the coordinate-system of a reference to a geospatial lexicon
- [`cts:reference-namespaces`](functions/lexicon.md) - Accessor for the namespaces of a reference to a [geospatial] path lexicon
- [`cts:reference-nullable`](functions/lexicon.md) - Returns true() if the reference is nullable, false() otherwise
- [`cts:reference-parse`](functions/lexicon.md) - Creates a reference to a value lexicon by parsing its XML or JSON
  representation, for use as a parameter to cts:value-tuples
- [`cts:reference-scalar-type`](functions/lexicon.md) - Accessor for the scalar type of a reference to a value lexicon
- [`cts:register`](functions/search.md) - Register a query for later use
- [`cts:registered-query`](functions/cts-query-constructors.md) - Returns a query matching fragments specified by previously registered
  queries (see cts:register)
- [`cts:registered-query-ids`](functions/cts-query-constructors.md) - Returns the registered query identifiers used to construct the specified
  query
- [`cts:registered-query-options`](functions/cts-query-constructors.md) - Returns the options for the specified query
- [`cts:registered-query-weight`](functions/cts-query-constructors.md) - Returns the weight with which the specified query was constructed
- [`cts:relevance-info`](functions/search.md) - Return the relevance score computation report for a node
- [`cts:remainder`](functions/search.md) - Returns an estimated search result size for a node,
  or of the context node if no node is provided
- [`cts:reverse-query`](functions/cts-query-constructors.md) - Construct a query that matches serialized cts queries, based on a
  set of model input nodes
- [`cts:reverse-query-nodes`](functions/cts-query-constructors.md) - Returns the nodes used to construct the specified query
- [`cts:reverse-query-weight`](functions/cts-query-constructors.md) - Returns the weight with which the specified query was constructed
- [`cts:score`](functions/search.md) - Returns the score of a node,
  or of the context node if no node is provided
- [`cts:score-order`](functions/cts-order-constructors.md) - Creates a score-based ordering clause, for use as an option to
  
  cts:search
- [`cts:search`](functions/search.md) - Returns a relevance-ordered sequence of nodes specified by a given query
- [`cts:similar-query`](functions/cts-query-constructors.md) - Returns a query matching nodes similar to the model nodes
- [`cts:similar-query-nodes`](functions/cts-query-constructors.md) - Returns the nodes used to construct the specified query
- [`cts:similar-query-weight`](functions/cts-query-constructors.md) - Returns the weight with which the specified query was constructed
- [`cts:stem`](functions/search.md) - Returns the stem(s) for a word
- [`cts:tokenize`](functions/search.md) - Tokenizes text into words, punctuation, and spaces
- [`cts:triple-range-query`](functions/cts-query-constructors.md) - Returns a 
  cts:query
  matching triples with a
  triple index entry equal to the given values
- [`cts:triple-range-query-object`](functions/cts-query-constructors.md) - Returns the object value used to construct the specified query
- [`cts:triple-range-query-operator`](functions/cts-query-constructors.md) - Returns the operators used to construct the specified query
- [`cts:triple-range-query-options`](functions/cts-query-constructors.md) - Returns the options for the specified query
- [`cts:triple-range-query-predicate`](functions/cts-query-constructors.md) - Returns the predicate value used to construct the specified query
- [`cts:triple-range-query-subject`](functions/cts-query-constructors.md) - Returns the subject value used to construct the specified query
- [`cts:triple-range-query-weight`](functions/cts-query-constructors.md) - Returns the weight with which the specified query was constructed
- [`cts:triple-value-statistics`](functions/lexicon.md) - Returns statistics from the triple index for the values given
- [`cts:triples`](functions/lexicon.md) - Returns values from the triple index
- [`cts:true-query`](functions/cts-query-constructors.md) - Returns a query that matches all fragments
- [`cts:unordered`](functions/cts-order-constructors.md) - Specifies that results should be unordered, for use with
  
  cts:search
- [`cts:uri-match`](functions/lexicon.md) - Returns values from the URI lexicon
   that match the specified wildcard pattern
- [`cts:uri-reference`](functions/lexicon.md) - Creates a reference to the URI lexicon, for use as a parameter to
  cts:value-tuples
- [`cts:uris`](functions/lexicon.md) - Returns values from the URI lexicon
- [`cts:valid-document-patch-path`](functions/xpath-validation.md) - Parses path expressions and resolves namespaces using the $map parameter
- [`cts:valid-extract-path`](functions/xpath-validation.md) - Parses path expressions and resolves namespaces using the $map parameter
- [`cts:valid-index-path`](functions/xpath-validation.md) - Parses path expressions and resolves namespaces based on the server
 run-time environment
- [`cts:valid-optic-path`](functions/xpath-validation.md) - Parses path expressions and resolves namespaces using the $map parameter
- [`cts:value-co-occurrences`](functions/lexicon.md) - Returns value co-occurrences (that is, pairs of values, both of which appear
  in the same fragment) from the specified value lexicon(s)
- [`cts:value-match`](functions/lexicon.md) - Returns values from the specified value lexicon(s)
   that match the specified wildcard pattern
- [`cts:value-ranges`](functions/lexicon.md) - Returns value ranges from the specified value lexicon(s)
- [`cts:value-tuples`](functions/lexicon.md) - Returns value co-occurrence tuples (that is, tuples of values, each of
  which appear in the same fragment) from the specified value lexicons
- [`cts:values`](functions/lexicon.md) - Returns values from the specified value lexicon(s)
- [`cts:walk`](functions/search.md) - Walks a node, evaluating an expression with any text matching a query
- [`cts:word-match`](functions/lexicon.md) - Returns words from the word lexicon that match the wildcard pattern
- [`cts:word-query`](functions/cts-query-constructors.md) - Returns a query matching text content containing a given phrase
- [`cts:word-query-options`](functions/cts-query-constructors.md) - Returns the options for the specified query
- [`cts:word-query-text`](functions/cts-query-constructors.md) - Returns the text used to construct the specified query
- [`cts:word-query-weight`](functions/cts-query-constructors.md) - Returns the weight with which the specified query was constructed
- [`cts:words`](functions/lexicon.md) - Returns words from the word lexicon
- [`rdf:langString`](functions/rdf-functions.md) - Returns an rdf:langString value with the 
   given value and language tag
- [`rdf:langString-language`](functions/rdf-functions.md) - Returns the language of an rdf:langString 
   value
- [`search:check-options`](functions/general.md) - This function verifies that options XML is 
		  properly structured
- [`search:estimate`](functions/general.md) - This function quickly estimates the number of hits a query will return
- [`search:get-default-options`](functions/general.md) - This function returns the default options 
		  XML
- [`search:parse`](functions/general.md) - This function parses query text according 
      to given options and returns the appropriate 
      cts:query XML
- [`search:remove-constraint`](functions/general.md) - NOTE: This function is deprecated
- [`search:resolve`](functions/general.md) - This function is the same as 
		  search:search, except that it takes 
		  a parsed and annotated cts:query XML node or a 
      structured search search:query XML node as 
		  input
- [`search:resolve-nodes`](functions/general.md) - This function performs the same search as 
		  search:search, but it takes 
		  a parsed and annotated cts:query XML node or a 
      structured search search:query XML node as 
		  input and returns the actual result nodes from the database
- [`search:search`](functions/general.md) - This function parses and invokes a query according to
                  specified options, returning up to $page-length result nodes
                  starting from $start
- [`search:snippet`](functions/general.md) - This function extracts matching text from the
		  result node based on options, and returns the matches 
		  wrapped in a containing node, with highlights 
		  tagged
- [`search:suggest`](functions/general.md) - This function returns a sequence of suggested text 
		  strings that match a wildcarded search for the 
		  $qtext input, ready for use in a user 
		  interface
- [`search:unparse`](functions/general.md) - NOTE: This function is deprecated
- [`search:values`](functions/general.md) - This function returns lexicon values and co-occurrences,
    and allows you to calculate aggregates based on the lexicon values
- [`sem:binding`](functions/semantic-functions.md) - Creates a sem:binding object, which is a sub-type of
  json:object (and map:map)
- [`sem:bnode`](functions/semantic-functions.md) - This function returns an identifier for a blank node, allowing the construction 
  of a triple that refers to a blank node
- [`sem:coalesce`](functions/semantic-functions.md) - Returns the value of the first argument that evaluates without error
- [`sem:curie-expand`](functions/semantic-functions.md) - This function expands a CURIE (Compact URI) 
		into a sem:iri object
- [`sem:curie-shorten`](functions/semantic-functions.md) - This function shortens an IRI into a CURIE 
		(Compact URI) into a sem:iri object
- [`sem:database-nodes`](functions/semantic-functions.md) - This function returns database nodes backing given triples
- [`sem:datatype`](functions/semantic-functions.md) - Returns the name of the simple type of the atomic value argument as a SPARQL
  style IRI
- [`sem:default-graph-iri`](functions/semantic-functions.md) - Returns the iri of the default graph
- [`sem:describe`](functions/semantic-functions.md) - This function implements the Concise Bounded Description 
	(CBD) specification to describe one or more nodes in the graph
- [`sem:graph`](functions/semantic-functions.md) - This function returns all triples from a named graph 
		  in the database
- [`sem:graph-add-permissions`](functions/semantic-functions.md) - Add permissions to the graph specified
- [`sem:graph-delete`](functions/semantic-functions.md) - This function deletes a named graph, and its graph 
	    document containing metadata, from the database
- [`sem:graph-get-permissions`](functions/semantic-functions.md) - Get permissions to the graph specified
- [`sem:graph-insert`](functions/semantic-functions.md) - This function inserts triples into a named graph, 
		creating the graph if necessary
- [`sem:graph-remove-permissions`](functions/semantic-functions.md) - Remove permissions from the graph specified
- [`sem:graph-set-permissions`](functions/semantic-functions.md) - Set permissions to the graph specified
- [`sem:if`](functions/semantic-functions.md) - The IF function form evaluates the first argument, interprets it as a
  effective boolean value, then returns the value of expression2 if the EBV is
  true, otherwise it returns the value of expression3
- [`sem:in-memory-store`](functions/semantic-functions.md) - Returns a sem:store constructor that queries from the sequence 
  of sem:triple values passed in as an argument
- [`sem:invalid`](functions/semantic-functions.md) - Returns a sem:invalid value with the given literal value and 
  datatype IRI
- [`sem:invalid-datatype`](functions/semantic-functions.md) - Returns the datatype IRI of a sem:invalid value
- [`sem:iri`](functions/semantic-functions.md) - This is a constructor function that takes a string
		and constructs an item of type sem:iri
		 from it
- [`sem:isBlank`](functions/semantic-functions.md) - Returns true if the argument is an RDF blank node - that is, derived from
  type sem:blank
- [`sem:isIRI`](functions/semantic-functions.md) - Returns true if the argument is an RDF IRI - that is, derived from
  type sem:iri, but not derived from type sem:blank
- [`sem:isLiteral`](functions/semantic-functions.md) - Returns true if the argument is an RDF literal - that is, derived from
  type xs:anyAtomicType, but not derived from type sem:iri
- [`sem:isNumeric`](functions/semantic-functions.md) - Returns true if the argument is a valid numeric RDF literal
- [`sem:lang`](functions/semantic-functions.md) - Returns the language of the value passed in, or the empty string if the 
  value has no language
- [`sem:langMatches`](functions/semantic-functions.md) - Returns true if $lang-tag matches $lang-range 
  according to the basic filtering scheme defined in RFC4647
- [`sem:prefixes`](functions/semantic-functions.md) - This function returns a set of prefix mappings for 
		use with CURIE processing
- [`sem:query-results-serialize`](functions/semantic-functions.md) - This function implements the W3C SPARQL Query Results 
	format
- [`sem:random`](functions/semantic-functions.md) - Returns a random double between 0 and 1
- [`sem:rdf-builder`](functions/semantic-functions.md) - This function returns a function that builds triples 
		from CURIE and blank node syntax
- [`sem:rdf-get`](functions/semantic-functions.md) - This function returns sem:triples from a specified location
- [`sem:rdf-insert`](functions/semantic-functions.md) - This function inserts triples into a specified database as 
		 one or more sem:triples documents
- [`sem:rdf-load`](functions/semantic-functions.md) - This function inserts an RDF document from a specified location
		into the designated database
- [`sem:rdf-parse`](functions/semantic-functions.md) - This function returns parsed sem:triple objects 
		from a text format or XML
- [`sem:rdf-serialize`](functions/semantic-functions.md) - This function returns a string or json or XML serialization 
		of the provided triples
- [`sem:ruleset-store`](functions/semantic-functions.md) - The sem:ruleset-store function returns a set of triples derived 
  by applying the ruleset to the triples in the sem:store constructor 
  provided in $store ("the triples that can be inferred from 
  these rules")
- [`sem:sameTerm`](functions/semantic-functions.md) - Returns true if the arguments are the same RDF term as defined by
  the RDF concepts specification
- [`sem:sparql`](functions/semantic-functions.md) - Executes a SPARQL query against the database
- [`sem:sparql-plan`](functions/semantic-functions.md) - Return a node representing the query plan of the given SPARQL query
- [`sem:sparql-update`](functions/semantic-functions.md) - Executes a SPARQL Update operation against the database
- [`sem:sparql-values`](functions/semantic-functions.md) - This function executes a SPARQL SELECT query using
		passed-in bindings participating as a starting point for 
		the query
- [`sem:store`](functions/semantic-functions.md) - The sem:store function defines a set of criteria, that when evaluated,
  selects a set of triples to be passed in to sem:sparql(),
  sem:sparql-update(), or sem:sparql-values() as part
  of the options argument
- [`sem:timezone-string`](functions/semantic-functions.md) - Returns the timezone of an xs:dateTime value as a string
- [`sem:transitive-closure`](functions/semantic-functions.md) - From a starting set of seeds, follow a given set 
		of predicates, to a given depth, and return all unique node 
		IRIs
- [`sem:triple`](functions/semantic-functions.md) - Creates a triple object, which represents an RDF triple
  containing atomic values representing the subject, predicate, object, and
  optionally graph identifier (graph IRI)
- [`sem:triple-graph`](functions/semantic-functions.md) - Returns the graph identifier (graph IRI) from a sem:triple value
- [`sem:triple-object`](functions/semantic-functions.md) - Returns the object from a sem:triple value
- [`sem:triple-predicate`](functions/semantic-functions.md) - Returns the predicate from a sem:triple value
- [`sem:triple-subject`](functions/semantic-functions.md) - Returns the subject from a sem:triple value
- [`sem:typed-literal`](functions/semantic-functions.md) - Returns a value to represent the RDF typed literal with lexical value 
  $value and datatype IRI $datatype
- [`sem:unknown`](functions/semantic-functions.md) - Returns a sem:unknown value with the given literal value and 
  datatype IRI
- [`sem:unknown-datatype`](functions/semantic-functions.md) - Returns the datatype IRI of a sem:unknown value
- [`sem:uuid`](functions/semantic-functions.md) - Return a UUID URN (RFC4122) as a sem:iri value
- [`sem:uuid-string`](functions/semantic-functions.md) - Return a string that is the scheme specific part of random UUID URN (RFC4122)
- [`vec:add`](functions/vector-operations.md) - Returns the sum of two vectors
- [`vec:base64-decode`](functions/vector-constructors.md) - Returns a vector value by decoding the base64 encoded string input
- [`vec:base64-encode`](functions/vector-operations.md) - Returns the base64 encoding of the vector
- [`vec:cosine`](functions/vector-operations.md) - Returns the cosine of the angle between two vectors
- [`vec:cosine-distance`](functions/vector-operations.md) - Returns the cosine distance between two vectors
- [`vec:dimension`](functions/vector-operations.md) - Returns the dimension of the vector passed in
- [`vec:dot-product`](functions/vector-operations.md) - Returns the dot product between two vectors
- [`vec:euclidean-distance`](functions/vector-operations.md) - Returns the Euclidean distance between two vectors
- [`vec:get`](functions/vector-operations.md) - Returns the element at the k-th index of the vector
- [`vec:magnitude`](functions/vector-operations.md) - Returns the magnitude of the vector
- [`vec:normalize`](functions/vector-operations.md) - Returns the vector passed in, normalized to a length of 1
- [`vec:subtract`](functions/vector-operations.md) - Returns the difference of two vectors
- [`vec:subvector`](functions/vector-operations.md) - Returns a subvector of the input vector, starting at the specified index, with the specified length (optional)
- [`vec:vector`](functions/vector-constructors.md) - Returns a vector value
- [`vec:vector-score`](functions/vector-operations.md) - A helper function that returns a hybrid score using a cts score and a vector distance calculation result

## Related Skills

- `marklogic-data-manipulation`
- `marklogic-xquery-stdlib`
- `marklogic-development`
