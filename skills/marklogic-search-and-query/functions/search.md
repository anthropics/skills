# Search

24 functions in this category.

## cts:confidence

Returns the confidence of a node,
  or of the context node if no node is provided.

### Signature

```xquery
cts:confidence(
  $node as node()?
) as xs:float
```

### Parameters

**`$node`** *(optional)*
A node. Typically this is an item in the result sequence of a
    cts:search operation.

### Returns

`xs:float`

### Usage Notes

Confidence is similar to score, except that it is bounded.
   It is similar to fitness, except that it is influenced by term IDFs.
   It is an xs:float in the range of 0.0 to 1.0.
   It does not include quality.
      When using with any of the scoring methods, the confidence is
   calculated by first bounding the score in the range of 0.0 to 1.0,
   then taking the square root of that number.

### Examples

```xquery
let $x := cts:search(collection(), "dog")
return
cts:confidence($x[1])

 => Returns the confidence value for the first item
    in the search.
```

---

## cts:contains

Returns true if any of a sequence of values matches a query.

### Signature

```xquery
cts:contains(
  $nodes as item()*,
  $query as cts:query
) as xs:boolean?
```

### Parameters

**`$nodes`**
The nodes or atomic values to be checked for a match. Atomic
    values are converted to a text node before checking for a match,
    which may result in an error if the value cannot be converted.

**`$query`**
A query to match against.  If a string
   is entered, the string is treated as a cts:word-query of the
   specified string.

### Returns

`xs:boolean?`

### Examples

```xquery
cts:contains(//PLAY
  [TITLE="The Tragedy of Hamlet, Prince of Denmark"]
      /ACT[3]/SCENE[1],
    cts:word-query("To be, or not to be"))
  => ..true, if ACT II, SCENE I of Hamlet contains
    the phrase "To be, or not to be" (it does).
```

---

## cts:deregister

Deregister a registered query, explicitly releasing the associated
  resources.

### Signature

```xquery
cts:deregister(
  $id as xs:unsignedLong
) as empty-sequence()
```

### Parameters

**`$id`**
A registered query identifier.

### Returns

`empty-sequence()`

### Examples

```xquery
cts:deregister(xs:unsignedLong("12345678901234567"))

=> ()
```

---

## cts:distinctive-terms

Return the most "relevant" terms in the model nodes (that is, the
  terms with the highest scores).

### Signature

```xquery
cts:distinctive-terms(
  $nodes as node()*,
  $options as element()??
) as element(cts:class)
```

### Parameters

**`$nodes`**
Some model nodes.

**`$options`** *(optional)*
An XML
    
    representation of the options for defining which terms to
    generate and how to evaluate them.
    
    The options node must be in the cts:distinctive-terms
    namespace. The following is a sample options
    node:
    
    <options xmlns="cts:distinctive-terms">
      <max-terms>20</max-terms>
    </options> 
    
    

    The
    
    cts:distinctive-terms options (which are also valid for
    cts:similar-query, cts:train,
    and cts:cluster)
    
    
    include:
    
    
    <max-terms>
    
    
    An integer defining the maximum number of distinctive terms to list
    in the
    cts:distinctive-terms
     output.
    The default is 16.
    
    
    <min-val>
    
    
    A double specifying the minimum value a term can
    have and still be considered a distinctive term. The default is 0.
    
    <min-weight>
    
    A number specifying the minimum weighted term frequency a term can
    have and still be considered a distinctive term.  In general this value
    will be either 0 (include unweighted terms) or 1 (don't include unweighted
    terms). The default is 1.
    
    <score>
    
    A string defining which scoring method to use in comparing the values
    of the terms.
    The default is logtfidf.  See the description of scoring
    methods in the cts:search function for more details.
    Possible values are:
      
      logtfidf
      Compute scores using the logtfidf method.
      logtf
      Compute scores using the logtf method.
      simple
      Compute scores using the simple method.
      
    
    
    <complete>
    
    A boolean value indicating whether to return terms even if there is no
    query associated with them.  The default is false.
    
    
    <use-db-config>
    
     The options below may be used to easily target a small set of terms.
    <use-db-config>
    
    is a boolean value indicating whether to use the currently configured DB options
    as defaults (overriding the built-in ones below) to determine the terms to
    generate.  This is true by default. When this is
    false, any options below not explicitly specified
    take their default values as listed; they do not take the database
    settings' values. Flags explicitly specified override defaults, whether
    built-in (listed below), or from the database configuration.
    Flags not specified in a field apply to all fields, unless the field
    has its own setting, which will be the final value. In other words
    it's a hierarchy, with each more-specific level overriding previous
    less-specific levels.
    
    
    
    The options element also includes indexing options in the
    http://marklogic.com/xdmp/database namespace.
    
    
    These control which terms to use. 
    These database options include the following
     (shown here with a db prefix to
    denote the
    http://marklogic.com/xdmp/database namespace.
    The default given below is the default value if
    use-db-config
     is set
    to false:
    
    
    
    <db:word-searches>
    
    Include terms for the words in the node. The default is
    false.
    <db:stemmed-searches>
    
    Define whether to include terms for the stems in the node, and at
    what level of stemming: off, basic,
    advanced, or decompounding. The default is
    basic.
    
    <db:word-positions>
    
    Include terms for word positions in the node. The default is
    false.
    <db:fast-case-sensitive-searches>
    
    Include terms for case-sensitive variations of the words in the
    node. The default is false.
    <db:fast-diacritic-sensitive-searches>
    
    Include terms for diacritic-sensitive variations of the words in
    the node.  The default is false.
    <db:fast-phrase-searches>
    Include
    terms for two-word phrases in the node.  The default is
    true.
    <db:phrase-throughs>
    If phrase
    terms are included, include terms for phrases that cross the given
    elements.  The default is to have no such elements.
    Any number can be passed in a single string, separated by spaces.
    
    <db:phrase-arounds>
    If phrase
    terms are included, include terms for phrases that skip over the
    given elements.  The default is to have no such elements.
    Any number can be passed in a single string, separated by spaces.
    
    <db:fast-element-word-searches>
    
    Include terms for words in particular elements.  The default is
    true.
    <db:fast-element-phrase-searches>
    
    Include terms for phrases in particular elements. The default is
    true.
    <db:element-word-positions>
    
    Include terms for element word positions in the node. The default is
    false.
    <db:element-word-query-throughs>
    
    Include terms for words in sub-elements of the given elements. The
    default is to have no such elements. Any number can be
    passed in a single string, separated by spaces.
    
    <db:fast-element-character-searches>
    
    Include terms for characters in particular elements.  The default is
    false.
    <db:range-element-indexes>
    
    Include terms for data values in specific elements.  The default is
    to have no such indexes. 


    <db:range-field-indexes>
    
    Include terms for data values in specific fields.  The default is
    to have no such indexes.




    <db:range-element-attribute-indexes>
    
    Include terms for data values in specific attributes.  The default
    is to have no such indexes.
    


    <db:one-character-searches>
    
    Include terms for single character.  The default is
    false.
    <db:two-character-searches>
    
    Include terms for two-character sequences. The default is
    false.
    <db:three-character-searches>
    
    Include terms three-character sequences.  The default is
    false.
    <db:trailing-wildcard-searches>
    
    Include terms for trailing wildcards. The default is
    false.
    
    <db:fast-element-trailing-wildcard-searches>
    
    
    If trailing wildcard terms are included, include terms for
    trailing wildcards by element.  The default is false.
    <db:fields>
    
    Include terms for the defined fields.  The default is to have
    no fields.

### Returns

`element(cts:class)`

### Usage Notes

Output Format
The output of the function is a 
cts:class element  containing
a sequence
 of
cts:term elements.
 (This is the same as the weights form of a class for
the SVM classifier; see cts:train.)  Each cts:term element
 identifies the term ID as well
as a score, confidence, and fitness measure for the term, in addition
to a cts:query
 that corresponds to
the term.  The correspondence of terms to queries is not precise:
queries typically make use of multiple terms, and not all terms
correspond to a query. However, a search using the query given for a
term will match the model node that gave rise to it.

### Examples

#### Example 1

```xquery
cts:distinctive-terms( fn:doc("book.xml"),
   <options xmlns="cts:distinctive-terms"><max-terms>3</max-terms></options> )
== >
<cts:class name="dterms book.xml" offset="0" xmlns:cts="http://marklogic.com/cts">
  <cts:term id="1230725848944963443" val="482" score="372" confidence="0.686441" fitness="0.781011">
    <cts:element-word-query>
      <cts:element>title</cts:element>
      <cts:text xml:lang="en">the</cts:text>
      <cts:option>case-insensitive</cts:option>
      <cts:option>diacritic-insensitive</cts:option>
      <cts:option>stemmed</cts:option>
      <cts:option>unwildcarded</cts:option>
    </cts:element-word-query>
  </cts:term>
  <cts:term id="2859044029148442125" val="435" score="662" confidence="0.922555" fitness="0.971371">
    <cts:word-query>
      <cts:text xml:lang="en">text</cts:text>
      <cts:option>case-insensitive</cts:option>
      <cts:option>diacritic-insensitive</cts:option>
      <cts:option>stemmed</cts:option>
      <cts:option>unwildcarded</cts:option>
    </cts:word-query>
  </cts:term>
  <cts:term id="17835615465481541363" val="221" score="237" confidence="0.65647" fitness="0.781263">
    <cts:word-query>
      <cts:text xml:lang="en">of</cts:text>
      <cts:option>case-insensitive</cts:option>
      <cts:option>diacritic-insensitive</cts:option>
      <cts:option>stemmed</cts:option>
      <cts:option>unwildcarded</cts:option>
    </cts:word-query>
  </cts:term>
</cts:class>
```

#### Example 2

```xquery
cts:distinctive-terms(//title,
    <options xmlns="cts:distinctive-terms">
      <use-db-config>true</use-db-config>
    </options>)

=> a cts:class element containing the 16 most distinctive query terms
```

#### Example 3

```xquery
cts:distinctive-terms(<foo>hello there you</foo>,
    <options xmlns="cts:distinctive-terms"
             xmlns:db="http://marklogic.com/xdmp/database">
            <db:word-positions>true</db:word-positions>
    </options>)

=> a cts:class element containing the 16 most distinctive query terms
```

---

## cts:element-walk

Returns a copy of the node, replacing any elements found
  with the specified expression.

### Signature

```xquery
cts:element-walk(
  $node as node(),
  $element as xs:QName*,
  $expr as item()*
) as node()
```

### Parameters

**`$node`**
A node to run the walk over.  The node must be either a document node
    or an element node; it cannot be a text node.

**`$element`**
The name of elements to replace.

**`$expr`**
An expression with which to replace each match. You can use the
    variables $cts:node and $cts:action
    (described below) in the expression.

### Returns

`node()`

### Usage Notes

There are two built-in variables to represent an element match.
    These variables can be used inline in the expression parameter.
  
      
    $cts:node as element()
    The matching element node.
    $cts:action as xs:string
    Use xdmp:set on this to specify what should happen
    next
    
      "continue"
      (default) Walk the next match.
      If there are no more matches, return all evaluation results.
      "skip"
      Skip walking any more matches and return all evaluation results.
      "break"
      Stop walking matches and return all evaluation results.

---

## cts:entity

Returns a cts:entity object. This is an opaque object that can be used to build an entity dictionary.

### Signature

```xquery
cts:entity(
  $id as xs:string,
  $normalizedText as xs:string,
  $text as xs:string,
  $type as xs:string
) as cts:entity
```

### Parameters

**`$id`**
A unique ID for the entity. A unique entity may have multiple entries in the dictionary with different matching words: the unique ID ties them all together. For entities created from a SKOS ontology this could be the URI of the  Concept. The variable $cts:entity-id in cts:entity-highlight and cts:entity-walk will be filled in with this ID for each matching entity.

**`$normalizedText`**
The normalized form of the entity.  For entities created from a SKOS ontology this could be the preferred label of the Concept. The variable $cts:normalized-text in cts:entity-highlight and cts:entity-walk will be filled in with this form for each matching entity.

**`$text`**
The word (or phrase) to match during entity extraction. This will be an exact match, unless the dictionary was created with the "case-insensitive" option, in which case the string is matched with case folding. For entities created from a SKOS ontology this could be a label or alternative label for the Concept.

**`$type`**
The type of the entity. For entities created from a SKOS ontology this could be the id of the top concept for the matching Concept, or its preferred label. The variable $cts:entity-type in cts:entity-highlight and cts:entity-walk will be filled in with this type for each matching entity.

### Returns

`cts:entity`

### Examples

```xquery
let $dict := 
  cts:entity-dictionary(
    for $alt in ("ADA", "Obamacare", "Affordable Care Act")
    return cts:entity("E1", "ADA", $alt", "Law")
  )
return 
  cts:entity-highlight(<root>ADA is often called Obamacare</root>,
    element {$cts:entity-type} {attribute norm {$cts:normalized-text}, $cts:text}, $dict)
=>
<root><Law norm="ADA">ADA</Law> is often called <Law norm="ADA">Obamacare</Law>.</root>
```

---

## cts:entity-dictionary

Returns a cts:entity-dictionary object.

### Signature

```xquery
cts:entity-dictionary(
  $entities as cts:entity*,
  $options as xs:string*?
) as cts:entity-dictionary
```

### Parameters

**`$entities`**
The entities to put into the dictionary.

**`$options`** *(optional)*
Dictionary building options. The default is case-sensitive, allow-overlaps, and whole-words.
    
      Options include:
      
        "case-sensitive"
        Entity names are case-sensitive.
        "case-insensitive"
        Entity names are case-insensitive.
        "whole-words"
        Require that matches align with token boundaries.
        "partial-words"
        Allow matches to fall within token boundaries.
        "allow-overlaps"
        Allow overlapping entity labels.
        "remove-overlaps"
        Remove overlapping entity labels.

### Returns

`cts:entity-dictionary`

### Usage Notes

Only one of "case-sensitive" and "case-insensitive", "whole-words" and "partial-words", and "allow-overlaps" and "remove-overlaps" is permitted. It is strongly recommended that the defaults be used.
  
      Use this method when creating ad hoc entity dictionaries, or as a prelude to saving the entity dictionary to the database.

### Examples

```xquery
let $dict := 
  cts:entity-dictionary(
    for $alt in ("ADA", "Obamacare", "Affordable Care Act")
    return cts:entity("E1", "ADA", $alt", "Law")
  )
return 
  cts:entity-highlight(<root>ADA is often called Obamacare</root>,
    element {$cts:entity-type} {attribute norm {$cts:normalized-text}, $cts:text}, $dict)
=>
<root><Law norm="ADA">ADA</Law> is often called <Law norm="ADA">Obamacare</Law>.</root>
```

---

## cts:entity-dictionary-get

Retrieve an entity dictionary previously cached in the database.

### Signature

```xquery
cts:entity-dictionary-get(
  $uri as xs:string
) as cts:entity-dictionary
```

### Parameters

**`$uri`**
The URI of an entity dictionary previously been saved in the database.

### Returns

`cts:entity-dictionary`

### Usage Notes

If no dictionary exists with the specified URI, this function throws
  XDMP-NOSUCHDICT.

### Examples

```xquery
(: Assume you previously inserted an entity dictionary with the
 : URI "/ontology/people", using entity:dictionary-load or
 : entity:dictionary-insert.
 :)
xquery version "1.0-ml";
cts:entity-dictionary-get("/ontology/people")

(: Returns an opaque cts:entity-dictionary object suitable for use with
 : functions that accept a cts:entity-dictionary as input. :)
```

---

## cts:entity-dictionary-parse

Construct a cts:entity-dictionary object by parsing it from a formatted string.

### Signature

```xquery
cts:entity-dictionary-parse(
  $contents as xs:string*,
  $options as xs:string*?
) as cts:entity-dictionary
```

### Parameters

**`$contents`**
The dictionary entries to parse. Each line (or string) must consist of
   four tab-delimited fields: The entity ID, the normalized form of the
   entity, the word or phrase to match during entity identification, and
   the entity type. For more details about the fields, see
   cts:entity.
   Multiple formatted strings can be passed in and they will be combined 
   into a single dictionary object.

**`$options`** *(optional)*
Dictionary building options. The default is case-sensitive, allow-overlaps,
    and whole-words.
    
      Options include:
      
        "case-sensitive"
        Entity names are case-sensitive.
        "case-insensitive"
        Entity names are case-insensitive.
        "whole-words"
        Require that matches align with token boundaries.
        "partial-words"
        Allow matches to fall within token boundaries.
        "allow-overlaps"
        Allow overlapping entity labels.
        "remove-overlaps"
        Remove overlapping entity labels.

### Returns

`cts:entity-dictionary`

---

## cts:entity-highlight

Returns a copy of the node, replacing any entities found
  with the specified expression.  You can use this function
  to easily highlight any entities in an XML document in an arbitrary manner.
  If you do not need fine-grained control of the XML markup returned,
  you can use the entity:enrich XQuery module function instead.
  A valid entity enrichment license key is required
  to use cts:entity-highlight;
  without a valid license key, it throws an exception.  If you
  have a valid license for entity enrichment, you can entity enrich text
  in English and in any other languages for which you have a valid license
  key. For languages in which you do not have a valid license key,
  cts:entity-highlight finds no entities for text in that
  language.

### Signature

```xquery
cts:entity-highlight(
  $node as node(),
  $expr as item()*,
  $dict as cts:entity-dictionary?
) as node()
```

### Parameters

**`$node`**
A node to run entity highlight on.  The node must be either a document node
    or an element node; it cannot be a text node.

**`$expr`**
An expression with which to replace each match. You can use the
    variables $cts:text, $cts:node,
    $cts:entity-type and $cts:normalized-text,
    $cts:start, and $cts:action
    (described below) in the expression.

**`$dict`** *(optional)*
The entity dictionary to use for matching entities in the text 
    of the input node. If you omit this parameter, the default entity 
    dictionary is used. (No default dictionaries currently exist.)  
    See the Usage Notes for details.

### Returns

`node()`

### Usage Notes

In addition to a valid Entity Enrichment license key, this function
    requires that you have installed the Entity Enrichment package. For
    details on installing the Entity Enrichment package, see the
    Installation Guide and the "Marking Up Documents With
    Entity Enrichment" chapter of the Search Developer's Guide.
  
      
    There are six built-in variables to represent an entity match.
    These variables can be used inline in the expression parameter.
  
      
    $cts:text as xs:string
    The matched text.
    $cts:node as text()
    The node containing the matched text.
    $cts:start as xs:integer
    The string-length position of the first character of
    $cts:text in $cts:node.  Therefore, the following
    always returns true:
    fn:substring($cts:node, $cts:start,
             fn:string-length($cts:text)) eq $cts:text 
    
    $cts:action as xs:string
    Use xdmp:set on this to specify what should happen
    next
    
      "continue"
      (default) Walk the next match.
      If there are no more matches, return all evaluation results.
      "skip"
      Skip walking any more matches and return all evaluation results.
      "break"
      Stop walking matches and return all evaluation results.
    
    
    $cts:entity-type as xs:string
    The type of the matching entity.
    $cts:normalized-text as xs:string
    The normalized entity text (only applicable for some
    languages).
 
      The following are the entity types returned from the
 $cts:entity-type built-in variable (in alphabetical order):
      
    FACILITY
       A place used as a facility.
    GPE
       Geo-political entity.  Differs from location because it has a
       person-made aspect to it (for example, California is a GPE because
       its boundaries were defined by a government).
    IDENTIFIER:CREDIT_CARD_NUM
       A number identifying a credit card number.
    IDENTIFIER:DISTANCE
       A number identifying a distance.
    IDENTIFIER:EMAIL
       Identifies an email address.
    IDENTIFIER:LATITUDE_LONGITUDE
       Latitude and longitude coordinates.
    IDENTIFIER:MONEY
       Identifies currency (dollars, euros, and so on).
    IDENTIFIER:NUMBER
       Identifies a number.
    IDENTIFIER:PERSONAL_ID_NUM
       A number identifying a social security number or other ID
       number.
    IDENTIFIER:PHONE_NUMBER
       A number identifying a telephone number.
    IDENTIFIER:URL
       Identifies a web site address (URL).
    IDENTIFIER:UTM
       Identifies Universal Transverse Mercator coordinates.
    LOCATION
       A geographic location (Mount Everest, for example).
    NATIONALITY
       The nationality of someone or something (for example, American).
    ORGANIZATION
       An organization.
    PERSON
       A person.
    RELIGION
       A religion.
    TEMPORAL:DATE
       Date-related.
    TEMPORAL:TIME
       Time-related.
    TITLE
       Appellation or honorific associated with a person.
    URL
       A URL on the world wide web.
    UTM
       A point in the Universal Transverse Mercator (UTM)
        coordinate system.

---

## cts:entity-walk

Walk an XML document or element node, evaluating an
   expression
   against any matching entities. This functions is similar to
   cts:entity-highlight
   in how it processes matched entities, but it differs in what it returns.

### Signature

```xquery
cts:entity-walk(
  $node as node(),
  $expr as item()*,
  $dict as cts:entity-dictionary?
) as empty-sequence()
```

### Parameters

**`$node`**
A node to walk.  The node must be either an XML
      document node or an XML element node; it cannot be a text node.

**`$expr`**
An expression to evaluate for each match. You can use the
      variables $cts:text, $cts:node,
      $cts:entity-type, $cts:normalized-text,
      $cts:entity-id, $cts:start, 
      and $cts:action
      in the expression. See the Usage Notes for details.

**`$dict`** *(optional)*
The entity dictionary to use for matching entities in the text
      of the input node. If you omit this parameter, the default entity
      dictionary is used. (No default dictionaries currently exist.) 
      See the Usage Notes for details.

### Returns

`empty-sequence()`

### Usage Notes

The following variables are available for use 
     inline in the expr parameter. These variables make aspects 
     of the matched entity available to your inline code.
      
        $cts:node as text()
         The node containing the match.
        $cts:text as xs:string
         The matched text. In the case of overlapping matches, this value
          may not encompass the entirety of the entity match string. Rather,
          it contains only the non-overlapping part of the text, in order
          to prevent introduction of duplicate text in the final result.
        $cts:entity-type
         The type of the matched entity, as defined by the
          type field of the matching entity dictionary entry.
        $cts:entity-id
         The ID of the matched entity, as defined by the
          id field of the matching entity dictionary entry.
        $cts:normalized-text as xs:string
         The normalized entity text (only applicable to some languages).
        $cts:start as xs:integer
         The offset (in codepoints) of the start of $cts:text
          in the matched text node.
        $cts:action as xs:string
         The action to take. Use xdmp:set on this variable in
          your inline code to specify what should happen next. Use
          xdmp:set to set the value to one of the following:
          
           "continue"
            Walk the next match. If there are no more matches, return 
             all evaluation results. This is the default action.
           "skip"
            Skip walking any more matches and return all evaluation results.
           "break"
            Stop walking matches and return all evaluation results.

---

## cts:fitness

Returns the fitness of a node,
  or of the context node if no node is provided. Fitness is a normalized
  measure of relevance that is based on how well a node matches the query
  issued, not taking into account the number of documents in which
  the query term(s) occur.

### Signature

```xquery
cts:fitness(
  $node as node()?
) as xs:float
```

### Parameters

**`$node`** *(optional)*
A node. Typically this is an item in the result sequence of a
    cts:search operation.

### Returns

`xs:float`

### Usage Notes

Fitness is similar to score, except that it is bounded.
   It is similar to confidence, except that it is not influenced by term IDFs.
   It is an xs:float in the range of 0.0 to 1.0.
   It does not include quality.

### Examples

```xquery
let $x := cts:search(collection(), "dog")
return
cts:fitness($x[1])

=> Returns the fitness value for the first item
   in the search.
```

---

## cts:highlight

Returns a copy of the node, replacing any text matching the query
  with the specified expression.  You can use this function
  to easily highlight any text found in a query. Unlike
  fn:replace and other XQuery string functions that match
  literal text, cts:highlight matches every term that
  matches the search, including stemmed matches or matches with
  different capitalization.

### Signature

```xquery
cts:highlight(
  $node as node(),
  $query as cts:query,
  $expr as item()*
) as node()
```

### Parameters

**`$node`**
A node to highlight.  The node must be either a document node
    or an element node; it cannot be a text node.

**`$query`**
A query specifying the text to highlight.  If a string
   is entered, the string is treated as a cts:word-query of the
   specified string.

**`$expr`**
An expression with which to replace each match. You can use the
    variables $cts:text, $cts:node,
    $cts:queries, $cts:start, and
    $cts:action (described below) in the expression.

### Returns

`node()`

### Usage Notes

There are five built-in variables to represent a query match.
    These variables can be used inline in the expression parameter.
  
      
    $cts:text as xs:string
    The matched text.
    $cts:node as text()
    The node containing the matched text.
    $cts:queries as cts:query*
    The matching queries.
    $cts:start as xs:integer
    The string-length position of the first character of
    $cts:text in $cts:node.  Therefore, the following
    always returns true:
    fn:substring($cts:node, $cts:start,
             fn:string-length($cts:text)) eq $cts:text 
    
    $cts:action as xs:string
    Use xdmp:set on this to specify what should happen
    next
    
      "continue"
      (default) Walk the next match.
      If there are no more matches, return all evaluation results.
      "skip"
      Skip walking any more matches and return all evaluation results.
      "break"
      Stop walking matches and return all evaluation results.
    
    
 
      You cannot use cts:highlight to highlight results matching
 cts:similar-query and cts:element-attribute-*-query
 items.  Using cts:highlight with these queries will
 return the nodes without any highlighting. 
      You can also use cts:highlight as a general search
 and replace function. The specified expression will replace any matching
 text. For example, you could replace the word "hello" with "goodbye"
 in a query similar to the following:
      
 cts:highlight($node, "hello", "goodbye")
      Because the expressions can be any XQuery expression, they can be very
 simple like the above example or they can be extremely complex.
      Unfiltered queries, including registered queries, do not match in
 cts:walk or
 cts:highlight.

---

## cts:parse

Parses a query string

### Signature

```xquery
cts:parse(
  $query as xs:string,
  $bindings as map:map??
) as cts:query
```

### Parameters

**`$query`**
The query string. For details, see
 Creating a Query From Search Text With cts:parse in the Search Developer's Guide.

**`$bindings`** *(optional)*
Bindings for mapping x:y parts of the query string. 
  The map key can be either a simple string with no embedded spaces or 
  punctuation or the empty string. The empty string defines the parsing 
  of untagged words. For details, see
 Binding a Tag to a Reference, Field, or Query Generator in the Search Developer's Guide.
  The map value for the label can be:
  
  cts:reference
  A reference to the tag in the query corresponds to a query against the indicated index, which constructs a query.
    
      
		  Reference
		  Operator
		  Query
		
      
		  cts:element-reference
		  ":"
		  cts:element-word-query
		
      
		  cts:element-reference
		  "="
		  cts:element-value-query
		
      
		  cts:element-attribute-reference
		  ":"
		  cts:element-attribute-word-query
		
      
		  cts:element-attribute-reference
		  "="
		  cts:element-attribute-value-query
		
      
		  cts:json-property-reference
		  ":"
		  cts:json-property-word-query
		
      
		  cts:json-property-reference
		  "="
		  cts:json-property-value-query
		
      
		  cts:field-reference
		  ":"
		  cts:field-word-query
		
      
		  cts:field-reference
		  "="
		  cts:field-value-query
		
      
		  geospatial reference
		  ":"
		  geospatial query, parameter parsed as a region
		
      
		  geospatial reference
		  "=" or eq
		  geospatial query, parameter parsed as a region
		
      
		  geospatial reference
		  other operator
		  error
		
      
		  cts:uri-reference
		  ":"
		  cts:document-query
		
      
		  cts:uri-reference
		  "="
		  cts:document-query
		
      
		  cts:collection-reference
		  ":"
		  cts:collection-query
		
      
		  cts:collection-reference
		  "="
		  cts:collection-query
		
      
		  cts:path-reference
		  ":"
		  cts:word-query (no path word-query)
		
      
		  cts:path-reference
		  "="
		  cts:path-range-query with operator "=" (no path value-query)
		
      
		  any
		  EQ
		  range-query with operator "="
		
      
		  any
		  NE
		  range-query with operator "!="
		
      
		  any
		  LT
		  range-query with operator "<"
		
      
		  any
		  LE
		  range-query with operator "<="
		
      
		  any
		  GE
		  range-query with operator ">="
		
      
		  any
		  GT
		  range-query with operator ">"
		
    
  
  function ($operator as xs:string, $values as xs:string*, $options as xs:string*) as cts:query?A reference to the tag in the query calls the function to produce a query.
  xs:stringA reference to the tag in the query corresponds to a field query against the named field.

### Returns

`cts:query`

### Examples

#### Example 1

```xquery
xquery version "1.0-ml";
cts:search(fn:doc(), cts:parse("cat AND dog"))

==> all documents containing the words "dog" and "cat"
```

#### Example 2

```xquery
xquery version "1.0-ml";
cts:parse("cat NEAR/5 dog AND mouse")

==>

cts:and-query(
  (cts:near-query(
     (cts:word-query("cat", ("lang=en"), 1), 
      cts:word-query("dog", ("lang=en"), 1)), 
     5, ("unordered"), 1), 
   cts:word-query("mouse", ("lang=en"), 1)), 
  ("unordered"))
```

#### Example 3

```xquery
xquery version "1.0-ml";
let $bindings := 
  let $map := map:map()
  return (
    map:put($map, "title", cts:element-reference(xs:QName("title"))),
    map:put($map, "by", "person-field"),
    map:put($map, "cat", function($operator, $values, $options) {
            cts:collection-query($values) }),
    map:put($map, "", function($operator, $values, $options) {
            cts:json-property-word-query('desc', $values, 'case-sensitive', 2)}),
    $map
  )
return
cts:parse("title:grapes by:steinbeck cat:classics california", $bindings)

==> 

cts:and-query(
  (cts:element-word-query(fn:QName("","title"), "grapes", ("lang=en"), 1), 
   cts:field-word-query("by", "steinbeck", ("lang=en"), 1), 
   cts:collection-query("classics"), 
   cts:json-property-word-query("desc", "california", 
      ("case-sensitive","lang=en"), 2)), 
  ("unordered"))
```

---

## cts:part-of-speech

Returns the part of speech for a cts:token, if any.

### Signature

```xquery
cts:part-of-speech(
  $token as cts:token
) as xs:string
```

### Parameters

**`$token`**
A token, as returned from cts:tokenize.

### Returns

`xs:string`

### Usage Notes

This function is useful for testing custom tokenizers. Built in tokenizers do not use parts of speech and will return an empty string for the part of speech.

### Examples

```xquery
cts:part-of-speech(cts:tokenize("an example","en"))
=> ("","","")
```

---

## cts:quality

Returns the quality of a node,
  or of the context node if no node is provided.

### Signature

```xquery
cts:quality(
  $node as node()?
) as xs:integer
```

### Parameters

**`$node`** *(optional)*
A node. Typically this is an item in the result sequence of a
    cts:search
     operation.

### Returns

`xs:integer`

### Usage Notes

If you run cts:quality
   on a constructed node, it always
  returns 0; it is primarily intended to run on nodes that are the retrieved
  from the database (an item from a cts:search
   result or an
  item from the result of an XPath expression that searches through the
  database).

### Examples

#### Example 1

```xquery
xdmp:document-insert("/test.xml", <a>my test</a>, (), (), 50);
for $x in cts:search(collection(),"my test")
return cts:quality($x)

=> 50
```

#### Example 2

```xquery
for $a in cts:search(collection(),"my test")
where $a[cts:quality() gt 10]
return xdmp:node-uri($a)

=> /test.xml
```

---

## cts:register

Register a query for later use.

### Signature

```xquery
cts:register(
  $query as cts:query
) as xs:unsignedLong
```

### Parameters

**`$query`**
A query to register.

### Returns

`xs:unsignedLong`

### Examples

```xquery
cts:register(cts:collection-query("mycollection"))

  => 12345678901234567
```

---

## cts:relevance-info

Return the relevance score computation report for a node.

### Signature

```xquery
cts:relevance-info(
  $node as node()?,
  $output-kind as xs:string?
) as element()?
```

### Parameters

**`$node`** *(optional)*
A node. Typically this is an item in the result sequence of a
    cts:search
     operation.
    If this parameter is omitted, the context node is used.

**`$output-kind`** *(optional)*
The output kind. It can be either "element" or "object".
    With "element", the built-in returns an XML element.
    With "object",  the built-in returns a map:map.
    The default is "element".

### Returns

`element()?`

### Usage Notes

This function returns an XML report
     that contains
    details about the
    score computation only if the following conditions are met:
    The node parameter or context node is the result
    of a cts:search
     call that
    included the relevance-trace option; and the score is
    non-zero. For
    example, you will not get a report if you use the score-zero
    option on your cts:search
    , if the
    search returns no results, or if node is not the result
    of cts:search
    .
  
      
    The score computation reflects the scoring method specified in the
    cts:search
     expression,
    if any. The score-zero and score-random
    methods do not generate a report.
  
      
    Collecting score computation details with which to generate this report
    is costly, so using the relevance-trace option will
    slow down your search significantly.

### Examples

#### Example 1

```xquery
(: must use the relevance-trace option on cts:search to get relevance info :)
for $n in cts:search(//SPEECH,"to be or not to be", "relevance-trace")
return cts:relevance-info($n);
=>
<qry:relevance-info xmlns:qry="http://marklogic.com/cts/query">
  <qry:score
    formula="(256*scoreSum/weightSum)+(256*qualityWeight*documentQuality)"
    computation="(256*1274/4)+(256*1*0)">81536</qry:score>
  <qry:confidence
    formula="sqrt(score/(256*8*maxlogtf*maxidf))"
    computation="sqrt(81536/(256*8*18*log(11360)))">0.486687</qry:confidence>
  <qry:fitness
    formula="sqrt(score/(256*8*maxlogtf*avgidf))"
    computation="sqrt(81536/(256*8*18*(23.6745/4)))">0.611312</qry:fitness>
  <qry:uri>hamlet.xml</qry:uri>
  <qry:path>fn:doc("hamlet.xml")/PLAY/ACT[3]/SCENE[1]/SPEECH[19]</qry:path>
  <qry:and>
    <qry:score formula="scoreSum" computation="390+366+228+290">1274</qry:score>
    <qry:term weight="8.125">
      <qry:score formula="8*weight*logtf" computation="65*6">390</qry:score>
      <qry:key>13470285622946442720</qry:key>
      <qry:annotation>pair(word("be"),word("or"))</qry:annotation>
    </qry:term>
    <qry:term weight="7.625">
      <qry:score formula="8*weight*logtf" computation="61*6">366</qry:score>
      <qry:key>13951883977767006862</qry:key>
      <qry:annotation>pair(word("or"),word("not"))</qry:annotation>
    </qry:term>
    <qry:term weight="4.75">
      <qry:score formula="8*weight*logtf" computation="38*6">228</qry:score>
      <qry:key>13642437994068421010</qry:key>
      <qry:annotation>pair(word("not"),word("to"))</qry:annotation>
    </qry:term>
    <qry:term weight="3.625">
      <qry:score formula="8*weight*logtf" computation="29*10">290</qry:score>
      <qry:key>7885524737699073672</qry:key>
      <qry:annotation>pair(word("to"),word("be"))</qry:annotation>
    </qry:term>
  </qry:and>
</qry:relevance-info>
```

#### Example 2

```xquery
(: must use the relevance-trace option on cts:search to get relevance info
   The BM25 scoring method has additional variables in the score calculation:
    length: the length of the resultant document
    bm25lw: the weight of the resultant document's length on the score calculation
    avgdl: the average length of all documents in the target database
:)
let $result := cts:search(fn:doc(),"animals", ("relevance-trace","score-bm25","bm25-length-weight=0.75"))
return cts:relevance-info(fn:head($result));
=>
<qry:relevance-info xmlns:qry="http://marklogic.com/cts/query">
  <qry:score formula="(256*scoreSum/weightSum)+(256*qualityWeight*documentQuality)" computation="(256*354/1)+(256*1*0)">90624</qry:score>
  <qry:confidence formula="sqrt(score/(256*8*maxlogtf*maxidf))" computation="sqrt(90624/(256*8*18*log(7162)))">0.5262576</qry:confidence>
  <qry:fitness formula="sqrt(score/(256*8*maxlogtf*avgidf))" computation="sqrt(90624/(256*8*18*(7.26711/1)))">0.5816204</qry:fitness>
  <qry:uri>/VGFHNOBGUOFGIGTX/20161171439249/4/311R.xml</qry:uri>
  <qry:path>fn:doc("/VGFHNOBGUOFGIGTX/20161171439249/4/311R.xml")</qry:path>
  <qry:term weight="7.375">
    <qry:score formula="8*weight*round(logtf/(length/avgdl*bm25lw+(1-bm25lw)))" computation="59*round(5/(9080/10799.3*0.75+(1-0.75)))" resolution="59*6">354</qry:score>
    <qry:key>17161663675614076798</qry:key>
    <qry:annotation>word("animals")</qry:annotation>
  </qry:term>
</qry:relevance-info>
```

---

## cts:remainder

Returns an estimated search result size for a node,
  or of the context node if no node is provided.
  The search result size for a node is the number of fragments remaining
  (including the current node) in the result sequence containing the node.
  This is useful to quickly estimate the size of a search result sequence,
  without using fn:count() or xdmp:estimate().

### Signature

```xquery
cts:remainder(
  $node as node()?
) as xs:integer
```

### Parameters

**`$node`** *(optional)*
A node. Typically this is an item in the result sequence of a
    cts:search operation.  If you specify the first item
    from a cts:search expression,
    then cts:remainder will return an estimate of the number
    of fragments that match that expression.

### Returns

`xs:integer`

### Usage Notes

This function makes it efficient to estimate the size of a search result
  and execute that search in the same query.  If you only need an estimate of
  the size of a search but do not need to run the search, then
  xdmp:estimate
  
  is more efficient.
      To return the estimated size of a search with
  cts:remainder
  ,
  use the first item of a
  cts:search
  
  result sequence as the
  parameter to
  cts:remainder. For example, the following
  query returns the estimated number of fragments that contain the word
  "dog":
      
  cts:remainder(cts:search(collection(), "dog")[1]) 
      When you put the position predicate on the
  cts:search result sequence, 
  
  MarkLogic Server will filter all of the false-positive results
  up to the specified position, but not the false-positive results beyond
  the specified
  position. Because of this, when you
  increase the position number in the parameter, the
  result from cts:remainder 
  
  might decrease
  by a larger number than the increase in position number, or it might not
  decrease at all. For example, if
  the query above returned 10, then the following query might return 9, it
  might return 10, or it might return less than 9, depending on how the
  results are dispersed throughout different fragments:
      
  cts:remainder(cts:search(collection(), "dog")[2]) 
      If you run cts:remainder
   on a constructed node, it always
  returns 0; it is primarily intended to run on nodes that are the retrieved
  from the database (an item from a search result or an
  item from the result of an XPath expression that searches through the
  database).

### Examples

#### Example 1

```xquery
let $x := cts:search(collection(), "dog")
return
(cts:remainder($x[1]), $x)

=> Returns the estimated number of items in the search
   for "dog" followed by the results of the search.
```

#### Example 2

```xquery
xdmp:document-insert("/test.xml", <a>my test</a>);
for $x in cts:search(collection(),"my test")
return cts:remainder($x)
=> 1
```

#### Example 3

```xquery
for $a in cts:search(collection(),"my test")
where $a[cts:remainder() eq 1]
return xdmp:node-uri($a)
=> /test.xml
```

---

## cts:score

Returns the score of a node,
  or of the context node if no node is provided.

### Signature

```xquery
cts:score(
  $node as node()?
) as xs:integer
```

### Parameters

**`$node`** *(optional)*
A node. Typically this is an item in the result sequence of a
    cts:search
     operation.

### Returns

`xs:integer`

### Usage Notes

Score is computed according to the scoring method specified in the
  cts:search
     expression, if any.
      If you run cts:score
   on a constructed node, it always
  returns 0; it is primarily intended to run on nodes that are retrieved
  from the database (an item from a search result or an
  item from the result of an XPath expression that searches through the
  database).

### Examples

#### Example 1

```xquery
(: run this on the Shakespeare content set :)
for $hit in cts:search(//SPEECH,
    cts:word-query("with flowers"))[1 to 10]
return element hit {
  attribute score { cts:score($hit) },
  $hit
}
```

#### Example 2

```xquery
xdmp:document-insert("/test.xml", <a>my test</a>);
  for $x in cts:search(doc("/test.xml"),"my test")
  return cts:score($x) => 11
```

#### Example 3

```xquery
for $a in cts:search(collection(),"my test")
  where $a[cts:score() gt 10]
  return xdmp:node-uri($a) => /test.xml
```

---

## cts:search

Returns a relevance-ordered sequence of nodes specified by a given query.

### Signature

```xquery
cts:search(
  $expression as node()*,
  $query as cts:query?,
  $options as (cts:order|xs:string)*?,
  $quality-weight as xs:double??,
  $forest-ids as xs:unsignedLong*?
) as node()*
```

### Parameters

**`$expression`**
An expression to be searched.
    This must be an inline fully searchable path expression.

**`$query`**
A cts:query
    
    specifying the search to perform.  If a string is entered, the string is
    treated as a cts:word-query
     of the specified string.

**`$options`** *(optional)*
Options to this search.  The default is ().
    
      Options include:
      
        "filtered"
        A filtered search (the default). Filtered searches
        eliminate any false-positive matches and properly resolve cases where
        there are multiple candidate matches within the same fragment.
        Filtered search results fully satisfy the specified
        cts:query
        .
        
        "unfiltered"
        
        An unfiltered search.  An unfiltered search
        selects fragments from the indexes that are candidates to satisfy
        the specified cts:query, and then it returns
        a single node from within each fragment that satisfies the specified
        searchable path expression. Unfiltered searches are useful because
        of the performance they afford when jumping deep into the
        result set (for example, when paginating a long result set and
        jumping to the 1,000,000th result). However, depending on the
        searchable path expression, the
        cts:query specified, the structure of the documents in
        the database, and the configuration of the database, unfiltered
        searches may yield false-positive results being included in the
        search results.  Unfiltered searches may also result in missed
        matches or in incorrect matches, especially when there are
        multiple candidate matches within a single fragment.
        To avoid these problems, you should only use unfiltered searches
        on top-level XPath expressions (for example, document nodes,
        collections, directories) or on fragment roots. Using unfiltered
        searches on complex XPath expressions or on XPath expressions that
        traverse below a fragment root can result in unexpected results.
        
        
        "score-logtfidf"
        Compute scores using the logtfidf method (the default scoring
        method). This uses the formula: 
          log(term frequency) * (inverse document frequency)
        
        "score-logtf"
        Compute scores using the logtf method. This does not take into
        account how many documents have the term and uses the formula: 
        
          log(term frequency)
        "score-simple"
        Compute scores using the simple method. The score-simple
        method gives a score of 8*weight for each matching term in the
        cts:query
         expression, and then scales the score up by
        multiplying by 256. It does not matter how
        many times a given term matches (that is, the term
        frequency does not matter); each match contributes 8*weight
        to the score.  For example, the following query  (assume the
        default weight of 1) would give a score of 8*256=2048 for
        any fragment with one or more matches for "hello", a score of
        16*256=4096
        for any fragment that also has one or more matches for "goodbye",
        or a score of zero for fragments that have no matches for
        either term:
          cts:or-query(("hello", "goodbye"))
        "score-random"
        Compute scores using the random method. The score-random
        method gives a random value to the score.  You can use this
        to randomly choose fragments matching a query.
        "score-zero"
        Compute all scores as zero.
        When combined with a quality weight of zero,
        this is the fastest consistent scoring method.
        "score-bm25"
        Compute scores using the bm25 method. This uses the formula: 
        
          
        (log(term frequency) / (1-'bm25-length-weight'+'bm25-length-weight'*(doc length / average doc length))) * (inverse document frequency)
        
        "checked"
        Word positions are checked (the default) when resolving
        the query. Checked searches eliminate false-positive matches for
        phrases during the index resolution phase of search processing.
        "unchecked"
        Word positions are not checked when resolving the
        query.  Unchecked searches do not take into account word positions
        and can lead to false-positive matches during the index resolution
        phase of search processing.  This setting is useful
        for debugging, but not recommended for normal use.
        "too-many-positions-error"
        If too much memory is needed to perform positions calculations
        to check whether a document matches a query,
        return an XDMP-TOOMANYPOSITIONS error,
        instead of accepting the document as a match.
        "faceted"
        Do a little more work to save faceting information about
        fragments matching this search so that calculating facets
        will be faster.
        "unfaceted"
        Do not save faceting information about fragments matching
        this search.
        "relevance-trace"
        Collect relevance score computation details with which you
        can generate a trace report using cts:relevance-info
        .
        Collecting this information is costly and will significantly
        slow down your search, so you should only use it when using
        cts:relevance-info
         to tune a query.
        "format-FORMAT"
        Limit the search to documents in document format specified
        by FORMAT (binary, json, text, or xml)
        
        
        
        
        
        
        
        
        cts:order Specification
        A sequence of cts:order
         specifications. The order
        is evaluated in the order each appears in the sequence. Default:
    (cts:score-order("descending"),cts:document-order("ascending")).
    The sequence typically consists of one or more of:
        cts:index-order,
        cts:score-order,
        cts:confidence-order,
        cts:fitness-order,
        cts:quality-order,
        cts:document-order,
        cts:unordered.  When using
        cts:index-order, there must be a range index defined
        on the index(es) specified by the cts:reference
        specification (for example,
     cts:element-reference.)
        
        "bm25-length-weight=NUMBER"
        The weight of the document length to average document length
        ratio while using the "score-BM25" option. Valid values are greater than
        0.0 and less than or equal to 1.0. The default is 0.333.

**`$quality-weight`** *(optional)*
A document quality weight to use when computing scores.
    The default is 1.0.

**`$forest-ids`** *(optional)*
A sequence of IDs of forests to which the search will be constrained.
    An empty sequence means to search all forests in the database.
    The default is (). In the XQuery version, you can use
    cts:search with this
    parameter and an empty cts:and-query to specify a
    forest-specific XPath statement (see the third
    example below). If you
    use this to constrain an XPath to one or more forests, you should set
    the quality-weight to zero to keep the XPath document
    order.

### Returns

`node()*`

### Usage Notes

Queries that use cts:search require that
the XPath expression
searched is fully searchable. A fully searchable path is one that
has no steps that are unsearchable and whose last step is searchable.
You can use the
xdmp:query-trace() function to see if the path is fully
searchable. If there are no entries in the xdmp:query-trace()
output indicating that a step is unsearchable, and if the last step
is searchable, then that path is fully
searchable. Queries that use cts:search on unsearchable
XPath expressions will fail with an error message. You can often make
the path expressions fully searchable by rewriting the query or adding
new indexes.
      Each node that
cts:search returns has a score with which
it is associated. To access the score, use the
cts:score
function. The nodes are returned in relevance order (most relevant to least
relevant), where more relevant nodes have a higher score.
      Only one of the "filtered" or "unfiltered" options may be specified
in the options parameter. If neither "filtered" nor "unfiltered", is
specified then the default is "filtered".
      Only one of the "score-logtfidf", "score-logtf", "score-simple",
"score-random", "score-zero", or "score-bm25" options may be specified in the
options parameter.
If none of "score-logtfidf", "score-logtf", "score-simple", "score-random",
"score-zero", or "score-bm25" are specified, then the default is "score-logtfidf".
      Only one of the "checked" or "unchecked" options may be specified
in the options parameter.  If the neither "checked" nor "unchecked" are
specified, then the default is "checked".
      Only one of the "faceted" or "unfaceted" options may be specified
in the options parameter.  If the neither "faceted" nor "unfaceted" are
specified, then the default is "unfaceted".
      If the cts:query specified is the
empty string (equivalent to cts:word-query("")), then the
search returns the empty sequence.
      With the cts:index-order
parameter, results with no comparable index value are always returned at the end of the ordered
result sequence.
       With an XQuery "order by" clause, results with no comparable
value are normally returned by MarkLogic at the end of the ordered result sequence.
You can override this behavior by specifying the "empty greatest" or "empty least"
modifier to the "order by" clause.
See https://www.w3.org/TR/2010/REC-xquery-20101214/#id-orderby-return for how to
specify "order by" clauses.
      If "bm25-length-weight=NUMBER" is provided along with the "score-bm25"
option, the BM25 scoring method is used with the weight specified. If the "score-bm25"
option is provided but "bm25-length-weight=NUMBER" is not specified, the default
value is 0.333. If provided, the value must be greater than 0.0 and less than or equal to 1.0.
This value is used to calculate the BM25 score of each search result, and determines
how much of an effect the document length to average document length ratio has on this score.
Use lower values for "bm25-length-weight=NUMBER" to push the scores in favor of
log(term frequency) and higher values to push the scores in favor of
(document length / average document length). The optimal value for
"bm25-length-weight=NUMBER" depends on your document collection. Experiment
with this value to receive results that best fit your application.

### Examples

#### Example 1

```xquery
cts:search(//SPEECH,
    cts:word-query("with flowers"))

  => ... a sequence of 'SPEECH' element ancestors (or self)
     of any node containing the phrase 'with flowers'.
```

#### Example 2

```xquery
cts:search(collection("self-help")/book,
    cts:element-query(xs:QName("title"), "meditation"),
    "score-simple", 1.0, (xdmp:forest("prod"),xdmp:forest("preview")))

  => ... a sequence of book elements matching the XPath
     expression which are members of the "self-help"
     collection, reside in the "prod" or "preview" forests and
     contain "meditation" in the title element, using the
     "score-simple" option.
```

#### Example 3

```xquery
cts:search(/some/xpath, cts:and-query(()), (), 0.0,
    xdmp:forest("myForest"))

  => ... a sequence of /some/xpath elements that are
     in the forest named "myForest".  Note the
     empty and-query, which matches all documents (and
     scores them all the same) and the quality-weight
     of 0, which together make each result have a score
     of 0, which keeps the results in document order.
```

#### Example 4

```xquery
cts:search(fn:doc(), "hello",
    ("unfiltered",
     cts:index-order(cts:element-reference(xs:QName("Title")))
    ) )[1 to 10]
=> Returns the first 10 documents with the word "hello", unfiltered,
   ordered by the range index on the element "Title".  An element
   range index on Title is required for this search, otherwise it
   throws an exception.
```

#### Example 5

```xquery
xquery version "1.0-ml";
let $scr:= 'score-bm25'
let $fct:= 'unfaceted'
let $lw := 'bm25-length-weight=0.5'
for $doc in cts:search(doc(),
  cts:near-query(
    (cts:word-query(("poison","potion"),"synonym"),
     cts:word-query(("king","duke"),("synonym"))),1),
  ($scr,$fct,"relevance-trace",$lw))
return cts:relevance-info($doc)
=> Returns the relevance information of the BM25 search results 
   with a BM25 length weight of 0.5
```

---

## cts:stem

Returns the stem(s) for a word.

### Signature

```xquery
cts:stem(
  $text as xs:string,
  $language as xs:string??,
  $partOfSpeech as xs:string??
) as xs:string*
```

### Parameters

**`$text`**
A word or phrase to stem.

**`$language`** *(optional)*
A language to use for stemming.  If not supplied, it uses the
    database default language.

**`$partOfSpeech`** *(optional)*
A part of speech to use for stemming. The default is the unspecified
   part of speech. This parameter is for testing custom stemmers.

### Returns

`xs:string*`

### Usage Notes

In general, you should pass a word into
cts:stem;
if you enter a phrase, it will stem the phrase, which will normally stem to
itself.
      When you stem a word through
cts:stem,
it returns all of the stems for the word, including decompounding and multiple
stems, regardless of the database stemming setting.

### Examples

```xquery
cts:stem("ran","en")
=> "run"
```

---

## cts:tokenize

Tokenizes text into words, punctuation, and spaces.  Returns output in
  the type cts:token, which has subtypes
  cts:word, cts:punctuation, and
  cts:space, all of which are subtypes of
  xs:string.

### Signature

```xquery
cts:tokenize(
  $text as xs:string,
  $language as xs:string??,
  $field as xs:string??
) as cts:token*
```

### Parameters

**`$text`**
A word or phrase to tokenize.

**`$language`** *(optional)*
A language to use for tokenization.  If not supplied, it uses the
    database default language.

**`$field`** *(optional)*
A field to use for tokenization. If the field has custom tokenization rules,
    they will be used. If no field is supplied or the field has no custom
    tokenization rules, the default tokenization rules are used.

### Returns

`cts:token*`

### Usage Notes

When you tokenize a string with cts:tokenize, each word is
  represented by an instance of
  cts:word, each punctuation character
  is represented by an instance of cts:punctuation,
  each set of adjacent spaces is represented by an instance of
  cts:space, and each set of adjacent line breaks
  is represented by an instance of cts:space.
      
   Unlike the standard XQuery function fn:tokenize,
   cts:tokenize returns words, punctuation, and spaces
   as different types. You can therefore use a typeswitch to handle each type
   differently. For example, you can use cts:tokenize to remove
   all punctuation from a string, or create logic to test for the type and
   return different things for different types, as shown in the first
   two examples below.

      
   You can use xdmp:describe to show how a given string will be
   tokenized. When run on the results of cts:tokenize, the
   xdmp:describe function returns the types and the values
   for each token. For a sample of this pattern, see the third example below.

### Examples

#### Example 1

```xquery
(: Remove all punctuation :)
let $string := "The red, blue, green, and orange
                balloons were launched!"
let $noPunctuation :=
  for $token in cts:tokenize($string)
  return
    typeswitch ($token)
     case $token as cts:punctuation return ""
     case $token as cts:word return $token
     case $token as cts:space return $token
     default return ()
return string-join($noPunctuation, "")
  
 => The red blue green and orange
    balloons were launched
```

#### Example 2

```xquery
(: Insert the string "XX" before and after
   all punctuation tokens :)
let $string := "The red, blue, green, and orange
                 balloons were launched!"
let $tokens := cts:tokenize($string)
return string-join(
for $x in $tokens
return if ($x instance of cts:punctuation)
       then (concat("XX",
                     $x, "XX"))
       else ($x) , "")
=> The redXX,XX blueXX,XX greenXX,XX and orange
    balloons were launchedXX!XX
```

#### Example 3

```xquery
(: show the types and tokens for a string :)
xdmp:describe(cts:tokenize("blue, green"))

=> (cts:word("blue"), cts:punctuation(","),
    cts:space(" "), cts:word("green"))
```

---

## cts:walk

Walks a node, evaluating an expression with any text matching a query.
  It returns a sequence of all the values returned by the expression
  evaluations.  This is similar to cts:highlight in how it
  evaluates its expression, but it is different in what it returns.

### Signature

```xquery
cts:walk(
  $node as node(),
  $query as cts:query,
  $expr as item()*
) as item()*
```

### Parameters

**`$node`**
A node to walk.  The node must be either a document node
    or an element node; it cannot be a text node.

**`$query`**
A query specifying the text on which to evaluate the expression.
   If a string is entered, the string is treated as a
   cts:word-query of the specified string.

**`$expr`**
An expression to evaluate with matching text. You can use the
    variables $cts:text, $cts:node,
    $cts:queries, $cts:start, and
    $cts:action (described below) in the expression.

### Returns

`item()*`

### Usage Notes

There are five built-in variables to represent a query match.
    These variables can be used inline in the expression parameter.
  
      
    $cts:text as xs:string
    The matched text.
    $cts:node as text()
    The node containing the matched text.
    $cts:queries as cts:query*
    The matching queries.
    $cts:start as xs:integer
    The string-length position of the first character of
    $cts:text in $cts:node.  Therefore, the following
    always returns true:
    fn:substring($cts:node, $cts:start,
             fn:string-length($cts:text)) eq $cts:text 
    
    $cts:action as xs:string
    Use xdmp:set on this to specify what should happen
    next
    
      "continue"
      (default) Walk the next match.
      If there are no more matches, return all evaluation results.
      "skip"
      Skip walking any more matches and return all evaluation results.
      "break"
      Stop walking matches and return all evaluation results.
    
    
 
      You cannot use cts:walk to walk results matching
 cts:similar-query and cts:element-attribute-*-query
 items.
      Because the expressions can be any XQuery expression, they can be very
 simple like the above example or they can be extremely complex.
      Unfiltered queries, including registered queries, do not match in
 cts:walk or
 cts:highlight.

---
