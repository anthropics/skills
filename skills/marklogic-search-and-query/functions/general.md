# General

12 functions in this category.

## search:check-options

This function verifies that options XML is 
		  properly structured. Used in debugging, normally not 
		  in production. Returns the empty sequence on success, 
		  otherwise it returns one or more error messages 
		  inside <report> elements.

### Signature

```xquery
search:check-options(
  $options as element(search:options),
  $strict as xs:boolean??
) as element(search:report)*
```

### Parameters

**`$options`**
Options that define the search 
		    grammar and control the search. See the description for 
		    $options
		    for the function search:search.

**`$strict`** *(optional)*
If 
	      true, index settings are additionally 
	      verified. The default is false.

### Returns

`element(search:report)*`

### Examples

```xquery
xquery version "1.0-ml";
import module namespace search = "http://marklogic.com/appservices/search"
    at "/MarkLogic/appservices/search/search.xqy";

search:check-options(
    <options xmlns="http://marklogic.com/appservices/search">
      <grammar>
        <joiner strength="10" apply="infix"
                element="cts:or-query">|</joiner>
        <joiner strength="20" apply="infix"
                element="cts:and-query">&amp;</joiner>
      </grammar>
    </options>)
=>
()
```

---

## search:estimate

This function quickly estimates the number of hits a query will return.
      The result is unfiltered and reflects the index resolution of the search.

### Signature

```xquery
search:estimate(
  $cts-query as element(),
  $options as element(search:options)??
) as xs:unsignedLong
```

### Parameters

**`$cts-query`**
A cts:query object or serialized cts:query.

**`$options`** *(optional)*
Search API query options with which to customize the search.
        For details, see
 Appendix: Query Options Reference in the Search Developer's Guide.

### Returns

`xs:unsignedLong`

### Usage Notes

This function is equivalent to calling 
     xdmp:estimate in XQuery with a
     cts:search expression, or to calling
     cts.estimate in Server-Side JavaScript, 
     except that this function enables you to include Search API
     query options in the search.
     For example, the following calls are equivalent:

(: XQuery :)
xdmp:estimate(cts:search(fn:doc(),cts:parse("merry")))
search:estimate(search:parse("merry"))

// JavaScript
cts.estimate(cts.wordQuery("merry");
cts.search(search.parse("merry"));

### Examples

#### Example 1

```xquery
xquery version "1.0-ml";
import module namespace search = "http://marklogic.com/appservices/search"
    at "/MarkLogic/appservices/search/search.xqy";

search:estimate(search:parse("merry"))

(: Returns an estimate of the number of fragments matching the
   word query produced by search:parse.
 :)
```

#### Example 2

```xquery
xquery version "1.0-ml";
import module namespace search = "http://marklogic.com/appservices/search"
    at "/MarkLogic/appservices/search/search.xqy";

search:estimate(cts:word-query("merry"))

(: Returns an estimate of the number of fragments matching the word query. :)
```

---

## search:get-default-options

This function returns the default options 
		  XML. Default options do not contain any constraints 
		  or anything else that requires specific index 
		  settings.

### Returns

`element(search:options)`

### Examples

```xquery
xquery version "1.0-ml";
import module namespace search = "http://marklogic.com/appservices/search"
    at "/MarkLogic/appservices/search/search.xqy";

search:get-default-options()

=>

<options xmlns="http://marklogic.com/appservices/search">
  ...
</options>
```

---

## search:parse

This function parses query text according 
      to given options and returns the appropriate 
      cts:query XML. If the query string to be parsed does not
      conform to the query grammar, the behavior differs, depending on the
      value of $output:
      
	cts:query throws a reportable error.
	search:query throws away the terms after the
	location of the parse error and runs the query with the terms
	before the location of the parse error, typically broadening the
	query.
      
      MarkLogic recommends that you use cts:query for parsing
      text.

### Signature

```xquery
search:parse(
  $qtext as xs:string+,
  $options as element(search:options)??,
  $output as xs:string??
) as element()?
```

### Parameters

**`$qtext`**
The query 
        text to parse. This may be a sequence, to accommodate 
        more complex search UI. Multiple query texts will be 
        ANDed together.

**`$options`** *(optional)*
Options to define the search 
        grammar and control the search. See the description for 
        $options 
        for the function search:search.

**`$output`** *(optional)*
The format of the parsed query, one of
        schema-element(cts:query) (default), 
        cts:query, search:query, or
        cts:annotated-query (deprecated). See the Usage Notes 
        for details.

### Returns

`element()?`

### Usage Notes

Use the $output parameter to specify one of the 
     following output formats. All the formats are suitable for use with
     search:resolve, but "cts:query" is
     most efficient if you do not need to transform or traverse the query. 
     Passing a cts:query object avoids an extra parsing step.
     
	schema-element(cts:query): The XML serialization of
        a cts:query object. Use this form if you want a cts:query but
        need to transform or inspect the query tree, or if you need a
        serialized query. This is the default result type.
      
	cts:query: A cts:query object that can be passed to
        functions such as cts:search, cts:values,
        cts:value-tuples, xdmp:sql, 
        sem:sparql, op:when, or their Server-Side
        JavaScript equivalents, without additional modification. This form
        is most efficient, but cannot be modified or traversed.
      
	search:query: The XML serialization of a structured
        query that you can use with search:resolve. You can
        also use structured queries with the Node.js, Java, or 
        REST Client APIs, though the Java and Node.js APIs have query
        builder interfaces that usually make a raw query unnecessary.
      
	cts:annotated-query: Equivalent to the output
        produced by schema-element(cts:query), but with the
        addition of annotations. THIS FORM IS DEPRECATED and will be
        removed in a future release.

### Examples

#### Example 1

```xquery
xquery version "1.0-ml";
import module namespace search = "http://marklogic.com/appservices/search"
     at "/MarkLogic/appservices/search/search.xqy";

search:parse("tag:technology AND format:pdf",
   <options xmlns="http://marklogic.com/appservices/search">
     <constraint name="tag">
       <collection/>
     </constraint>
     <constraint name="format">
        <value>
          <element ns="http://purl.org/dc/elements/1.1/" name="tag"/>
        </value>
     </constraint>
   </options>
) 

==>

<cts:and-query xmlns:cts="http://marklogic.com/cts">
  <cts:collection-query>
    <cts:uri>technology</cts:uri>
  </cts:collection-query>
  <cts:element-value-query>
    <cts:element xmlns:_1="http://purl.org/dc/elements/1.1/">_1:tag</cts:element>
    <cts:text xml:lang="en">pdf</cts:text>
  </cts:element-value-query>
</cts:and-query>
```

#### Example 2

```xquery
xquery version "1.0-ml";
import module namespace search = "http://marklogic.com/appservices/search"
     at "/MarkLogic/appservices/search/search.xqy";

search:parse("hello tag:technology AND format:pdf",
   <options xmlns="http://marklogic.com/appservices/search">
     <constraint name="tag">
       <collection/>
     </constraint>
     <constraint name="format">
        <value>
          <element ns="http://purl.org/dc/elements/1.1/" name="tag"/>
        </value>
     </constraint>
   </options>, "search:query")

=> the following structured query:

<search:query xmlns:search="http://marklogic.com/appservices/search">
  <search:and-query>
    <search:term-query>
      <search:text>hello</search:text>
    </search:term-query>
    <search:and-query>
      <search:collection-constraint-query>
        <search:constraint-name>tag</search:constraint-name>
        <search:uri>technology</search:uri>
      </search:collection-constraint-query>
      <search:value-constraint-query>
        <search:constraint-name>format</search:constraint-name>
        <search:text>pdf</search:text>
      </search:value-constraint-query>
    </search:and-query>
  </search:and-query>
</search:query>
```

---

## search:remove-constraint

NOTE: This function is deprecated. This function safely 
          removes a token from query text, 
		  ensuring that grammar elements (AND, OR, quotes, 
		  parentheses) are handled properly.

### Signature

```xquery
search:remove-constraint(
  $qtext as xs:string,
  $ptext as xs:string,
  $options as element(search:options)?
) as xs:string?
```

### Parameters

**`$qtext`**
The full query 
		    text string.

**`$ptext`**
A token to remove 
		    from full query text.

**`$options`**
Options to define the search 
		    grammar and control the search. See the description for 
		    $options 
		    for the function search:search.

### Returns

`xs:string?`

### Examples

```xquery
xquery version "1.0-ml";
import module namespace search = "http://marklogic.com/appservices/search"
   at "/MarkLogic/appservices/search/search.xqy";

let $options :=
 <options xmlns="http://marklogic.com/appservices/search">
   <constraint name="tag">
     <word>
      <element ns="http://widgets-r-us.com" name="tag"/>
     </word>
   </constraint>
   <constraint name="year">
     <value>
      <element ns="http://widgets-r-us.com" name="year"/>
     </value>
   </constraint>
 </options>
return
search:remove-constraint("tag:foo AND (year:2007 OR year:2008)",
   "year:2008", $options)

=>
"tag:foo AND year:2007"
```

---

## search:resolve

This function is the same as 
		  search:search, except that it takes 
		  a parsed and annotated cts:query XML node or a 
      structured search search:query XML node as 
		  input.

### Signature

```xquery
search:resolve(
  $query as element(),
  $options as element(search:options)??,
  $start as xs:unsignedLong??,
  $page-length as xs:unsignedLong??
) as element(search:response)
```

### Parameters

**`$query`**
A cts:query object, a serialized cts:query, or
		    a structured query (search:query). 
		    You can generate any of these forms of query using
		    search:parse.

**`$options`** *(optional)*
Options to define the search 
		    grammar and control the search. See the description for 
		    $options
		    for the function search:search.

**`$start`** *(optional)*
The index of the first hit to return. 
		    The default is 1.

**`$page-length`** *(optional)*
The maximum number of hits to return. 
		    The default is 10. If the value is 0, no results 
		    are returned.

### Returns

`element(search:response)`

### Examples

#### Example 1

```xquery
xquery version "1.0-ml";
import module namespace search = "http://marklogic.com/appservices/search"
    at "/MarkLogic/appservices/search/search.xqy";

search:resolve(search:parse("Vannevar Bush"),
    <options xmlns="http://marklogic.com/appservices/search">
      <return-results>false</return-results>
      <return-facets>true</return-facets>
    </options>)

=>

<search:response total="1234" start="1" page-length="10" xmlns=""
        xmlns:search="http://marklogic.com/appservices/search">
  <search:facet name="date">
	  <search:facet-value value="today" count="1000">
		  Today</search:facet-value>
	  <search:facet-value value="yesterday" count="234">
		  Yesterday</search:facet-value>
	  <search:facet-value value="thismonth" count="1234">
		  This Month</search:facet-value>
  <search:/facet>
    ...
</search:response>
```

#### Example 2

```xquery
(: structured query example, plain search for "hello" :)
xquery version "1.0-ml";
import module namespace search = "http://marklogic.com/appservices/search"
     at "/MarkLogic/appservices/search/search.xqy";

let $struct-query :=
<query xmlns="http://marklogic.com/appservices/search">
 <term-query>
  <text>hello</text>
 </term-query>
</query>
return
search:resolve($struct-query)
=> returns the a search:response node that matches a query for "hello"
```

---

## search:resolve-nodes

This function performs the same search as 
		  search:search, but it takes 
		  a parsed and annotated cts:query XML node or a 
      structured search search:query XML node as 
		  input and returns the actual result nodes from the database.

### Signature

```xquery
search:resolve-nodes(
  $query as element(),
  $options as element(search:options)??,
  $start as xs:unsignedLong??,
  $page-length as xs:unsignedLong??
) as node()*
```

### Parameters

**`$query`**
Either a
		    serialized and annotated cts:query, or
		    a structured query (search:query). 
		    You can generate either form of query as the result of a 
		    call to 
		    search:parse.

**`$options`** *(optional)*
Options to define the search 
		    grammar and control the search. See the description for 
		    $options 
		    for the function search:search.

**`$start`** *(optional)*
The index of the first hit to return. 
		    The default is 1.

**`$page-length`** *(optional)*
The maximum number of hits to return. 
		    The default is 10. If the value is 0, no results are 
		    returned.

### Returns

`node()*`

### Usage Notes

When used in conjunction with the extract-document-data
      option, each returned node contains the data specified by the
      extraction, rather than the entire document or fragment.
      To obtain a search:response instead of the matching
      nodes, use search:resolve.

### Examples

#### Example 1

```xquery
xquery version "1.0-ml";
import module namespace search = "http://marklogic.com/appservices/search"
    at "/MarkLogic/appservices/search/search.xqy";

search:resolve-nodes(search:parse("Vannevar Bush"),
    <options xmlns="http://marklogic.com/appservices/search">
      <return-results>false</return-results>
      <return-facets>true</return-facets>
    </options>)

=>

... sequence of document nodes ...
```

#### Example 2

```xquery
(: structured query example, plain search for "hello" :)
xquery version "1.0-ml";
import module namespace search = "http://marklogic.com/appservices/search"
     at "/MarkLogic/appservices/search/search.xqy";

let $struct-query :=
<query xmlns="http://marklogic.com/appservices/search">
 <term-query>
  <text>hello</text>
 </term-query>
</query>
return
search:resolve-nodes($struct-query)
=> returns the nodes that match a query for "hello"
```

---

## search:search

This function parses and invokes a query according to
                  specified options, returning up to $page-length result nodes
                  starting from $start.

### Signature

```xquery
search:search(
  $qtext as xs:string+,
  $options as element(search:options)??,
  $start as xs:unsignedLong??,
  $page-length as xs:unsignedLong??
) as element(search:response)
```

### Parameters

**`$qtext`**
The query text to
                    parse. This may be a sequence,
                    to accommodate more complex search UI. Multiple query texts
                    are combined with an AND operator.

**`$options`** *(optional)*
Options to define
        the search grammar and control the search.
	 The following is a list of the options that
        apply to document searches. The options node can contain other
        options, such as a values specification, but such
        options are not used in this context. For details, see
 Appendix: Query Options Reference in the Search Developer's Guide.
    
  
	      
     additional-query - Additional query(s) to apply to the 
     search. For details, see
 additional-query in the Search Developer's Guide
    
	      
     concurrency-level - The maximum number of threads to
     use when resolving facets. For details, see
 concurrency-level in the Search Developer's Guide
    
	      
     constraint - Limit the scope of a search and define facets.
     For details, see
 constraint in the Search Developer's Guide
    
	      
     debug - Enable or disable inclusion of debugging
     data in the search results. For details, see
 debug in the Search Developer's Guide
    
	      
     default-suggestion-source - Define a source for generating
     suggestions for naked terms. For details, see
 default-suggestion-source in the Search Developer's Guide
    
	      
     extract-document-data - Select elements, attributes, and
     JSON properties to include in the search results. For details, see
 extract-document-data in the Search Developer's Guide
    
	      
     extract-metadata: This option is deprecated. Use
     extract-document-data instead. For details, see
 extract-document-data in the Search Developer's Guide.
    
	      
     forest - Limit a search or lexicon query to specific 
     forests. For details, see
 forest in the Search Developer's Guide
    
	      
     fragment-scope - Control the global fragment scope 
     (properties or documents) over which to search. For details, see
 fragment-scope in the Search Developer's Guide
    
	      
     grammar - Define a custom search grammar. For details, see
 grammar in the Search Developer's Guide
    
	      
     operator - For details, see
 operator in the Search Developer's Guide
    
	      
     page-length - The number of results to return in each
     page of results. For details, see
 page-length in the Search Developer's Guide
    
	      
     quality-weight - A document quality weight to use when
     computing scores. For details, see
 quality-weight in the Search Developer's Guide
    
	      
     result-decorator - Specify a function with which to 
     decorate each search results with additional information. For details, see
 result-decorator in the Search Developer's Guide
    
	      
     return-constraints - Whether or not to include the input
     constraint definitions in the search response. For details, see
 return-constraints in the Search Developer's Guide
    
	      
     return-facets - Whether or not to include facets in the
     search response. For details, see
 return-facets in the Search Developer's Guide
    
	      
     return-metrics - Whether or not to include query
     performance data in the search response. For details, see
 return-metrics in the Search Developer's Guide
    
	      
     return-plan - Whether or not to include a query plan
     in the search response. For details, see
 return-plan in the Search Developer's Guide
    
	      
     return-qtext - Whether or not to include the input
     query text in the search response. For details, see
 return-qtext in the Search Developer's Guide
    
	      
     return-query - Whether or not to include the final
     representation of the input query in the search response. For details, see
 return-query in the Search Developer's Guide
    
	      
     return-results - Whether or not to include search result
     details in the search response. For details, see
 return-results in the Search Developer's Guide
    
	      
     return-similar - Whether or not to include a list of
     similar document for each search result in the response. For details, see
 return-similar in the Search Developer's Guide
    
	      
     search-option - Specify an advanced option to pass to
     the underlying cts query layer. For details, see
 search-option in the Search Developer's Guide
    
	      
     searchable-expression - An XPath expression that selects
     the documents to include in a search.  For details, see
 searchable-expression in the Search Developer's Guide.
     Due to security and performance considerations, beginning in MarkLogic
     9.0-10, the searchable-expression property/element in query options is
     deprecated. In addition, in 10.0-2 and moving forward, the
     searchable-expression requires the eval-search-string privilege.
    
	      
     sort-order - Define elements, attributes, fields, or
     JSON properties on which to order results. For details, see
 sort-order in the Search Developer's Guide
    
	      
     suggestion-source - Define a suggestion completion
     source for constraint-qualified search terms. For details, see
 suggestion-source in the Search Developer's Guide
    
	      
     term - Specify the handling of empty searches and
     search terms not associated with a constraint. For details, see
 term in the Search Developer's Guide
    
	      
     transform-results - Specify a function to use for
     generating snippets. For details, see
 transform-results in the Search Developer's Guide

**`$start`** *(optional)*
The 
	      index of the first hit to return. If 0, treated as 1. If 
	      greater than the number of results, no results will be
	      returned. The default is 1.

**`$page-length`** *(optional)*
The maximum number of hits to return. 
	      The default is 10. If the value is 0, no results are returned.

### Returns

`element(search:response)`

### Usage Notes

The output of search:search returns a 
		    <response> element, which in turn 
		    contains a total attribute. The value of the
		    total attribute is an estimate, based
		    on the index resolution of the query, and it is not 
		    filtered for accuracy. The accuracy of the index resolution
		    depends on the index configuration of the database, on the
		    query, and on the data being searched.

### Examples

#### Example 1

```xquery
xquery version "1.0-ml";
import module namespace search = "http://marklogic.com/appservices/search"
    at "/MarkLogic/appservices/search/search.xqy";

search:search("Vannevar Bush",
    <options xmlns="http://marklogic.com/appservices/search">
      <return-results>false</return-results>
      <return-facets>true</return-facets>
    </options>)

=>

<search:response total="1234" start="1" page-length="10" xmlns=""
        xmlns:search="http://marklogic.com/appservices/search">
  <search:facet name="date">
	  <search:facet-value value="today" count="1000">
		  Today</search:facet-value>
	  <search:facet-value value="yesterday" count="234">
		  Yesterday</search:facet-value>
	  <search:facet-value value="thismonth" count="1234">
		  This Month</search:facet-value>
  <search:/facet>
    ...
</search:response>
```

#### Example 2

```xquery
(: properties constraint example :)
xquery version "1.0-ml";
(: create a document with some properties to test with :)
xdmp:document-insert("/foo.xml", <foo>hello</foo>);
xdmp:document-set-properties("/foo.xml", <blah>boo</blah>);

(: do a properties constraint search :)
import module namespace search = "http://marklogic.com/appservices/search"
     at "/MarkLogic/appservices/search/search.xqy";

search:search("hello sample-property-constraint:boo",
<options xmlns="http://marklogic.com/appservices/search">
  <constraint name="sample-property-constraint">
    <properties />
  </constraint>
  <debug>true</debug>
</options>)

=>

<search:response total="1" start="1" page-length="10" xmlns=""
	xmlns:search="http://marklogic.com/appservices/search">
  <search:result index="1" uri="/foo.xml" 
		path="fn:doc(&quot;/foo.xml&quot;)" score="328" 
		confidence="0.807121" fitness="0.901397">
    <search:snippet>
	    <search:match path="fn:doc(&quot;/foo.xml&quot;)/foo">
		    <search:highlight>hello</search:highlight></search:match>
    </search:snippet>
  </search:result>
  <search:qtext>hello sample-property-constraint:boo</search:qtext>
  <search:report id="SEARCH-FLWOR">(cts:search(fn:collection(), 
	  cts:and-query((cts:word-query("hello", ("lang=en"), 1), 
	  cts:properties-query(cts:word-query("boo", ("lang=en"), 1))), 
	  ()), ("score-logtfidf"), 1))[1 to 10]
  </search:report>
  <search:metrics>
    <search:query-resolution-time>PT0.647S</search:query-resolution-time>
    <search:facet-resolution-time>PT0S</search:facet-resolution-time>
    <search:snippet-resolution-time>PT0.002S</search:snippet-resolution-time>
    <search:total-time>PT0.651S</search:total-time>
  </search:metrics>
</search:response>
```

---

## search:snippet

This function extracts matching text from the
		  result node based on options, and returns the matches 
		  wrapped in a containing node, with highlights 
		  tagged.

### Signature

```xquery
search:snippet(
  $result as node(),
  $cts-query as schema-element(cts:query),
  $options as element(search:transform-results)??
) as element(search:snippet)
```

### Parameters

**`$result`**
A node from which 
		    to pull matching snippets from.

**`$cts-query`**
A
		    serialized and annotated cts:query, 
		    typically the result of a call to 
		    search:parse.

**`$options`** *(optional)*
Options to define the search 
		    grammar and control the search. See description for 
		    $options for 
		    the function search:search. Note that 
		    you cannot specify the apply attribute
		    on the transform-results option with
		    search:snippet; to use a different snippetting
		    function, use 
		    search:search or 
		    search:resolve
		    instead.

### Returns

`element(search:snippet)`

### Examples

```xquery
xquery version "1.0-ml";
import module namespace search = "http://marklogic.com/appservices/search"
    at "/MarkLogic/appservices/search/search.xqy";

search:snippet(
 <html xmlns="http://www.w3.org/1999/xhtml">
     <head>
        <title>Page Title</title>
     </head>
     <body>
       <div>Query terms in this div will be ignored for snippeting.</div>
       <p>Text surrounding query terms is highlighted and truncated
               according to configuration.</p>
     </body>
     </html>,
      search:parse("terms"),
      <transform-results apply="snippet"
      xmlns="http://marklogic.com/appservices/search">
          <per-match-tokens>30</per-match-tokens>
          <max-matches>4</max-matches>
          <max-snippet-chars>200</max-snippet-chars>
          <preferred-matches>
              <element name="p" ns="http://www.w3.org/1999/xhtml"/>
          </preferred-matches>
      </transform-results>)

=>

<search:snippet xmlns:search="http://marklogic.com/appservices/search">
  <search:match path="/*:html/*:body/*:p[1]">
      Text surrounding query
    <search:highlight>terms</search:highlight>
      is highlighted and truncated according to configuration.
  </search:match>
</search:snippet>
```

---

## search:suggest

This function returns a sequence of suggested text 
		  strings that match a wildcarded search for the 
		  $qtext input, ready for use in a user 
		  interface.  Typically this is used for type-ahead 
		  applications to provide the user 
		  suggestions while entering terms in a search box.

### Signature

```xquery
search:suggest(
  $qtext as xs:string+,
  $options as element(search:options)??,
  $limit as xs:unsignedInt??,
  $cursor-position as xs:unsignedInt??,
  $focus as xs:positiveInteger??,
  $query as element(search:query)*?
) as xs:string*
```

### Parameters

**`$qtext`**
One or more strings 
		    of query text.  The first string in the list (or the
		    string corresponding to the position in the $focus 
		    parameter value) is used to find matching suggestions
		    by performing a lexicon match query.
		    The other strings (if any) are parsed as a 
		    cts:query, with the resulting queries 
		    combined with a cts:and-query, and the
		    resulting cts:query is passed as a 
		    constraining query to the lexicon match query, restricting 
		    the suggestions to fragments that match the 
		    cts:query.  Typically, each item in the
		    sequence corresponds to a single text entry box in a 
		    user interface.

**`$options`** *(optional)*
Options to define the search 
		    grammar and control the search. See description for 
		    $options
		    for the function search:search.  In particular, 
		    the default-suggestion-source and 
		    suggestion-source options are specific to
		    search:suggest.

**`$limit`** *(optional)*
The maximum number of
		    suggestions to return. The default is 10.

**`$cursor-position`** *(optional)*
The position of the cursor, from point of 
		    origin, in the text box corresponding to the 
		    $focus parameter. This is used to determine 
		    on which part of the query text to perform a lexicon 
		    match.  The default is the string length of the 
		    $focus string (all of the string).

**`$focus`** *(optional)*
If there are multiple
		    $qtext strings, the index of the string 
		    corresponding to the text box that has current 
		    "focus" in the user interface (and therefore containing 
		    a partial query text for completion). The
		    default is 1 (the first $qtext string.

**`$query`** *(optional)*
Zero or more structured queries with which to constrain the
          scope of the match for qtext. Default: No additional
          constraints on the suggestions.

### Returns

`xs:string*`

### Usage Notes

On large databases, the performance of using a 
		    word lexicon for suggestions will probably be slower than
		    using a value lexicon.  This can be very application 
		    specific, and in some cases the performance might be good,
		    but in general, value lexicons (range constraints) will 
		    perform much better than word lexicons (word constraints)
		    with search:suggest. Therefore, MarkLogic 
		    recommends using value lexicons for suggestions, not word 
		    lexicons.  
	    
      
		    The performance of search:suggest is highly
		    data-dependent.  The best performing suggestion sources 
		    are value lexicons (range indexes) that use the 
		    codepoint collation.  Performance is also impacted based on
		    the number of matches, and it can help to design the 
		    interaction between search:suggest and the UI
		    so that suggestions are given after a minimum of 3 
		    characters are entered (that is, the lexicon match calls 
		    will have at least 3 characters).  Again, this is quite 
		    data-dependent, so you should try it on a large data set
		    with your own data.
	    
      
		    The output of search:suggest is a sequence of 
		    query text strings, not a sequence of words.  Each 
		    query text string can include quoted text, such as
		    phrases.  The output of  search:suggest
		    is appropriate to pass into the first argument of
		    search:search, including any quoted phrases. 
		    For example, if you have a suggestion that returns 
		    multi-word phrases
		    (for example, from range element index values), then
		    the suggestion will quote the phrase.
	    
      
          Use the query parameter to supply structured
          queries with which to constrain the returned results. Only
          suggestions that match these additional queries are returned.
          For more information about structured queries, see
 Searching Using Structured Queries in the Search Developer's Guide.

### Examples

#### Example 1

```xquery
xquery version "1.0-ml";
import module namespace search = "http://marklogic.com/appservices/search"
    at "/MarkLogic/appservices/search/search.xqy";

let $options := 
<search:options xmlns="http://marklogic.com/appservices/search">
 <default-suggestion-source>
   <range collation="http://marklogic.com/collation/" 
          type="xs:string" facet="true">
      <element ns="http://marklogic.com/xdmp/apidoc" 
               name="function"/>
      <attribute ns="" name="name"/>
   </range>
 </default-suggestion-source>
</search:options>
return
search:suggest("docu", $options)

=> a sequence of strings representing query text:

document-add-collections
document-add-permissions
document-add-properties
document-checkin
document-checkout
```

#### Example 2

```xquery
xquery version "1.0-ml";
import module namespace search = "http://marklogic.com/appservices/search"
    at "/MarkLogic/appservices/search/search.xqy";

let $options := 
<search:options xmlns="http://marklogic.com/appservices/search">
 <default-suggestion-source>
    <range collation="http://marklogic.com/collation/" 
          type="xs:string" facet="true">
      <element ns="" name="hello"/>
   </range>
 </default-suggestion-source>
</search:options>
return
search:suggest("a", $options)

=>  a sequence of strings representing query text:
"and that"
"and this"
```

#### Example 3

```xquery
xquery version "1.0-ml";
import module namespace search = "http://marklogic.com/appservices/search"
    at "/MarkLogic/appservices/search/search.xqy";

search:suggest(("ta","foo"),(),5)

=>  a sequence of strings representing query text:

tab
table
tadpole
tag
```

#### Example 4

```xquery
xquery version "1.0-ml";
import module namespace search = "http://marklogic.com/appservices/search"
    at "/MarkLogic/appservices/search/search.xqy";

search:suggest(("table","foo"),(),(),5,2)

=>  a sequence of strings representing query text:

food
fool
foolhardy
foolish
foolishness
```

#### Example 5

```xquery
xquery version "1.0-ml";
import module namespace search = "http://marklogic.com/appservices/search"
    at "/MarkLogic/appservices/search/search.xqy";

(: 
given a document created with the following:

xdmp:document-insert("/test.xml",
<root>
  <my:my-element xmlns:my="my-namespace" shortname="fool"/>
  <my:my-element xmlns:my="my-namespace" shortname="food"/>
  <my:my-element xmlns:my="my-namespace" shortname="foolhardy"/>
  <my:my-element xmlns:my="my-namespace" shortname="foolish"/>
  <my:my-element xmlns:my="my-namespace" shortname="foolishness"/>
  <my:my-element xmlns:my="my-namespace" name="foody"/>
</root>)
:)
let $options := 
<options xmlns="http://marklogic.com/appservices/search">
 <constraint name="tag">
   <range collation="http://marklogic.com/collation/" 
          type="xs:string" facet="true">
      <element ns="my-namespace" 
               name="my-element"/>
      <attribute ns="" name="name"/>
   </range>
 </constraint>
 <suggestion-source ref="tag">
   <range collation="http://marklogic.com/collation/" 
          type="xs:string" facet="true">
      <element ns="my-namespace" 
               name="my-element"/>
      <attribute ns="" name="shortname"/>
   </range>
 </suggestion-source>
</options>
return	  
search:suggest("tag:foo", $options)

=>
suggestions to complete tag: from the range index on the 
"shortname" attribute (notice "foody" is not in the answer):

tag:food
tag:fool
tag:foolhardy
tag:foolish
tag:foolishness
```

---

## search:unparse

NOTE: This function is deprecated. Turn a serialized,
        annotated cts:query (typically from 
		search:parse) back into query text according to 
        the specified rules.

### Signature

```xquery
search:unparse(
  $qtree as element()
) as xs:string+
```

### Parameters

**`$qtree`**
A
		    serialized and annotated cts:query, 
		    typically the result of a call to 
		    search:parse.

### Returns

`xs:string+`

### Usage Notes

You can only use search:unparse on an annotated 
      cts:query. You can generate an annotated query by
      passing "cts:annotated-query" as the 3rd parameter of
      search:parse.

### Examples

```xquery
xquery version "1.0-ml";
import module namespace search = "http://marklogic.com/appservices/search"
    at "/MarkLogic/appservices/search/search.xqy";

search:unparse(
    search:parse("tag:technology AND format:pdf",
      search:get-default-options(), "cts:annotated-query"))

=>

"tag:technology AND format:pdf"
```

---

## search:values

This function returns lexicon values and co-occurrences,
    and allows you to calculate aggregates based on the lexicon values.

### Signature

```xquery
search:values(
  $spec-name as xs:string,
  $options as element(search:options),
  $query as element(search:query)??,
  $limit as xs:unsignedLong??,
  $start as xs:anyAtomicType??,
  $page-start as xs:unsignedLong??,
  $page-length as xs:unsignedLong??
) as element(search:values-response)
```

### Parameters

**`$spec-name`**
The name of a
 values in the Search Developer's Guide or
 tuples in the Search Developer's Guide
          specification in the supplied options node.

**`$options`**
Options that define and control the query. The options must
		  include the $spec-name definitions supplied in the first parameter.
	      The following is a list of the options that affect lexicon queries; 
          the options node can contain other options, but they are not used.
          For details, see
 Appendix: Query Options Reference in the Search Developer's Guide.
  
	      
     tuples - For details, see
 tuples in the Search Developer's Guide
    
	      
     values - For details, see
 values in the Search Developer's Guide
    
	      
     debug - For details, see
 debug in the Search Developer's Guide
    
	      
     forest - For details, see
 forest in the Search Developer's Guide
    
	      
     quality-weight - For details, see
 quality-weight in the Search Developer's Guide
    
	      
     return-aggregates - For details, see
 return-aggregates in the Search Developer's Guide
    
	      
     return-frequencies - For details, see
 return-frequencies in the Search Developer's Guide
    
	      
     return-metrics - For details, see
 return-metrics in the Search Developer's Guide
    
	      
     return-values - For details, see
 return-values in the Search Developer's Guide

**`$query`** *(optional)*
A structured query to apply as a constraint when retrieving 
		  lexicon values.

**`$limit`** *(optional)*
The maximum number of values to return. The default is no 
		  limit.

**`$start`** *(optional)*
A starting value in the lexicon.  If the $start is
          not present in the lexicon, the values
		  are returned starting with the next value in the range index
          after where $start would logically appear. If no
          $start value is supplied, values are returned
          beginning with the first value in the lexicon.

**`$page-start`** *(optional)*
The index of the first value to return from within the subset
          defined by limit and start. Default: 1.

**`$page-length`** *(optional)*
The number of values to return within the subset of values
          defined by limit and start. Default:
          Return all values.

### Returns

`element(search:values-response)`

### Usage Notes

For details and more examples, see
 Returning Lexicon Values With search:values in the Search Developer's Guide.

### Examples

#### Example 1

```xquery
xquery version "1.0-ml";
import module namespace search = "http://marklogic.com/appservices/search"
    at "/MarkLogic/appservices/search/search.xqy";

let $options := 
<options xmlns="http://marklogic.com/appservices/search">
  <values name="uri">
    <uri/>
    <aggregate apply="min"/>
  </values>
</options>
return
search:values("uri", $options)
=>
<values-response name="uri" type="xs:string" 
  xmlns="http://marklogic.com/appservices/search" 
  xmlns:xs="http://www.w3.org/2001/XMLSchema">
  <distinct-value frequency="2">/date.xml</distinct-value>
  <distinct-value frequency="2">/gajanan.xml</distinct-value>
  <distinct-value frequency="2">/test/keys.json</distinct-value>
  <aggregate-result name="min">/date.xml</aggregate-result>
  <metrics>
    <values-resolution-time>PT0.000193S</values-resolution-time>
    <aggregate-resolution-time>PT0.000409S</aggregate-resolution-time>
    <total-time>PT0.001987S</total-time>
  </metrics>
</values-response>
```

#### Example 2

```xquery
xquery version "1.0-ml";
import module namespace search = "http://marklogic.com/appservices/search"
     at "/MarkLogic/appservices/search/search.xqy";

(: 
   Requires URI lexicon and string range index on "hello". 
   This finds the values for "hello" for all documents that 
   have the element "hello".
:)
let $options := 
<options xmlns="http://marklogic.com/appservices/search">
  <tuples name="hello">
    <uri/>
    <range type="xs:string" collation="http://marklogic.com/collation/">
      <element ns="" name="hello"/>
    </range>
  </tuples>
</options>
let $values:= search:values("hello", $options)
return (
$values, 
fn:doc($values/search:tuple/search:distinct-value/fn:data()) )
=>
<values-response name="hello" 
  xmlns="http://marklogic.com/appservices/search" 
  xmlns:xs="http://www.w3.org/2001/XMLSchema">
  <tuple frequency="1">
    <distinct-value xsi:type="xs:string" 
      xmlns:xsi="http://www.w3.org/2001/XMLSchema-instance"
      >/date.xml</distinct-value>
    <distinct-value xsi:type="xs:string" 
      xmlns:xsi="http://www.w3.org/2001/XMLSchema-instance"
      >2012-08-10-05:00</distinct-value>
  </tuple>
  <tuple frequency="1">
    <distinct-value xsi:type="xs:string" 
      xmlns:xsi="http://www.w3.org/2001/XMLSchema-instance"
      >/gajanan.xml</distinct-value>
    <distinct-value xsi:type="xs:string" 
      xmlns:xsi="http://www.w3.org/2001/XMLSchema-instance"
      >fooooooooo</distinct-value>
  </tuple>
  <metrics>
    <values-resolution-time>PT0.0006S</values-resolution-time>
    <aggregate-resolution-time>PT0.000014S</aggregate-resolution-time>
    <total-time>PT0.002337S</total-time>
  </metrics>
</values-response>
<?xml version="1.0" encoding="UTF-8"?>
<hello>2012-08-10-05:00</hello>
<?xml version="1.0" encoding="UTF-8"?>
<foo>bar</foo>
```

#### Example 3

```xquery
xquery version "1.0-ml";
import module namespace search = "http://marklogic.com/appservices/search"
    at "/MarkLogic/appservices/search/search.xqy";

let $options := 
<options xmlns="http://marklogic.com/appservices/search">
  <values name="animals">
    <range type="xs:string">
      <field name="animal-name" collation="http://marklogic.com/collation/" />
    </range>
  </values>
</options>
return
search:values("animals", $options, 
  search:parse("mammal OR marsupial", (), "search:query"), 
  10, "camel", 5, 3)

==> Assuming the value subset defined by the query (mammal OR marsupial),
    limit (10), and start ("buffalo") contains the values (camel, fox,
    hare, jaguar, kangaroo, lemur, moose, ocelot, panda, rhino), then
    adding a page-start of 5 and a page-length of 3, you get the following:

<values-response name="animals" type="xs:string" xmlns="http://marklogic.com/appservices/search" xmlns:xs="http://www.w3.org/2001/XMLSchema">
<distinct-value frequency="1">kangaroo</distinct-value>
<distinct-value frequency="1">lemur</distinct-value>
<distinct-value frequency="1">moose</distinct-value>
<metrics>
<values-resolution-time>PT0.000242S</values-resolution-time>
<total-time>PT0.00134S</total-time>
</metrics>
</values-response>
```

---
