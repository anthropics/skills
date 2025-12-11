---
name: marklogic-data-manipulation
description: MarkLogic data manipulation, document operations, JSON, and utility functions for XQuery
globs: **/*.xqy,**/*.xq
---

# MarkLogic Data Manipulation Functions

This skill covers data manipulation operations including document management, updates, JSON processing, XQuery context operations, and various utility functions for everyday MarkLogic development.

This skill provides 256 XQuery functions organized into 8 functional areas.

## Functions by Category

### Documents, Directories, Properties, And Locks

*Detailed documentation: [functions/documents,-directories,-properties,-and-locks.md](functions/documents,-directories,-properties,-and-locks.md)*

| Function | Summary |
|----------|---------|
| `xdmp:collection-locks` | Returns locks of documents in a collection. |
| `xdmp:collection-properties` | Returns a sequence of properties documents, one for each document in the  specified collection(s) that has a corresponding properties document. |
| `xdmp:directory` | Returns the documents from the database in a directory. Note that these are  database documents, not from the filesystem; if you want documents from a  filesystem directory, use xdmp:filesystem-directory instead. |
| `xdmp:directory-locks` | Returns locks of documents in a directory. |
| `xdmp:directory-properties` | Returns a sequence of properties documents, one for each document in  the specified directory that has a corresponding properties document. |
| `xdmp:document-get-properties` | Returns the property values for a document's property. Throws  XDMP-DOCNOTFOUND if there is no document at the specified URI. |
| `xdmp:document-get-quality` | Returns the quality of the specified document if the document exists.  Otherwise, returns the empty sequence. |
| `xdmp:document-locks` | Returns the locks for one or more documents or directories.  Returns the locks for all documents and directories  in the database if no parameter is given. |
| `xdmp:document-properties` | Returns a sequence of properties documents, one for each of the specified  documents that has a corresponding properties document. If no documents  are specified, returns a sequence of properties documents for all  documents in the database that have a corresponding properties document. |

### Extension

*Detailed documentation: [functions/extension.md](functions/extension.md)*

| Function | Summary |
|----------|---------|
| `sem:resolve-iri` | Resolves a relative URI against an absolute URI. If $base is specified,  the URI is resolved relative to that base. If $base is not specified, the  base is set to the base-uri property from the static context, if the  property exists; if it does not exist, an error is thrown.  This XQuery function backs up the SPARQL IRI() function. |
| `xdmp:QName-from-key` | Construct a QName from a string of the form "{namespaceURI}localname".  This function is useful for constructing Clark notation  parameters for the   xdmp:xslt-eval    and   xdmp:xslt-invoke    functions. |
| `xdmp:add64` | Add two 64-bit integer values, discarding overflow. |
| `xdmp:and64` | AND two 64-bit integer values. |
| `xdmp:atomizable` | Returns true if a value could be atomized without error.  If no argument is supplied, this function checks  whether the context item can be atomized without error. |
| `xdmp:aws-region` | Returns the current Amazon Web Services region.  If MarkLogic is not running on Amazon Web Services, returns an empty sequence. |
| `xdmp:aws-services-domain` | Returns the current Amazon Web Services services domain.  If MarkLogic is not running on Amazon Web Services, returns an empty sequence. |
| `xdmp:aws-services-partition` | Returns the current Amazon Web Services services partition.  If MarkLogic is not running on Amazon Web Services, returns an empty sequence. |
| `xdmp:azure-environment` | Returns the current Microsoft Azure Environment.  If MarkLogic is not running on Micorosft Azure, returns an empty sequence. |
| `xdmp:azure-region` | Returns the current Microsoft Azure Region.  If MarkLogic is not running on Microsoft Azure, returns an empty sequence. |
| `xdmp:base64-decode` | Converts base64-encoded string to plaintext. |
| `xdmp:base64-encode` | Converts plaintext into base64-encoded string. |
| `xdmp:binary-decode` | Converts an encoded byte sequence, passed in as a binary node, from the  specified encoding to a unicode string. |
| `xdmp:binary-to-integer` | Parses a binary string, returning an integer. |
| `xdmp:caller-dialect` | Returns the dialect (e.g., "javascript", "1.0-ml", etc) of the caller  or the empty sequence if no dialect information is available.  Note that the return is not the language the function that calls  this built-in is written in; it is the dialect the function is called from.  For example, if a JavaScript program calls function "foo",  which uses xdmp:caller-dialect, then the return from xdmp:caller-dialect  will be “javascript” even if "foo" is implemented in XQuery. |
| `xdmp:castable-as` | Returns true if a value is castable.  This is similar to the "castable as" XQuery predicate, except that the  type is determined at runtime. |
| `xdmp:crypt` | Calculates the password hash for the given password and salt. |
| `xdmp:crypt2` | Calculates the password hash for the given plain-text password. |
| `xdmp:decode-from-NCName` | Invertible function that decodes characters an NCName produced by  xdmp:encode-for-NCName.  Given the NCName produced by xdmp:encode-for-NCName this  function returns the original string. |
| `xdmp:document-get-collections` | Returns the collections to which a given document belongs. |
| `xdmp:document-get-metadata` | Returns the metadata value of a given document. |
| `xdmp:document-get-metadata-value` | Returns the metadata value of a given document. |
| `xdmp:eager` | Returns the value of its argument, evaluated eagerly. |
| `xdmp:element-content-type` | Returns the schema-defined content-type of an element  ("empty", "simple", "element-only", or "mixed"). |
| `xdmp:email` | Send an email in an XQuery program. A valid SMTP Relay must be  configured in the Groups page of the Admin Interface for the email to be  sent. The format of the email message can be an XML file that  complies with the schema files listed below, or it can be a JavaScript  object that follows our definition of JSON email format  (please see xdmp.email). |
| `xdmp:encode-for-NCName` | Invertible function that escapes characters required to be part of  an NCName.  This is useful when translating names from other representations such as  JSON to XML.  Given any string, the result is always a valid NCName.  Providing all names are passed through this function the result is  distinct NCNames so the results can be used for searching as well as  name generation.  The inverse function is   xdmp:decode-from-NCName. |
| `xdmp:encoding-language-detect` | Analyzes binary, text, or XML data and suggests possible pairs of encoding  and language, with a confidence score for each pair. Scores of 10 and  above are high confidence recommendations.  The results are given in order of decreasing score.  Accuracy may be poor for short documents. |
| `xdmp:hash32` | Returns the 32-bit hash of a string. |
| `xdmp:hash64` | Returns the 64-bit hash of a string. |
| `xdmp:hex-to-integer` | Parses a hexadecimal string, returning an integer. |
| `xdmp:hmac-md5` | Calculates the Hash-based Message Authentication Code (HMAC) using the md5 hash function of the given secret key and message arguments. |
| `xdmp:hmac-sha1` | Calculates the Hash-based Message Authentication Code (HMAC) using the SHA1 hash function of the given secret key and message arguments. |
| `xdmp:hmac-sha256` | Calculates the Hash-based Message Authentication Code (HMAC) using the SHA256 hash function of the given secret key and message arguments. |
| `xdmp:hmac-sha512` | Calculates the Hash-based Message Authentication Code (HMAC) using the SHA512  hash function of the given secret key and message arguments. |
| `xdmp:initcap` | Returns the string where the first letter of each token has been uppercased. |
| `xdmp:integer-to-binary` | Returns a binary representation of an integer. |
| `xdmp:integer-to-hex` | Returns a hexadecimal representation of an integer. |
| `xdmp:integer-to-octal` | Returns an octal representation of an integer. |
| `xdmp:is-whitespace-node` | Returns true if the node is a text node containing only whitespace. |
| `xdmp:key-from-QName` | Construct a context-independent string from a QName. This string is  of the form "{namespaceURI}localname" and is suitable for use as a map  key. |
| `xdmp:lazy` | Returns the value of its argument, evaluated lazily. |
| `xdmp:ldap-lookup` | Returns an ldap entry. |
| `xdmp:ldap-search` | Returns ldap search result. |
| `xdmp:lshift64` | Left-shift a 64-bit integer value. |
| `xdmp:md5` | Calculates the md5 hash of the given argument. |
| `xdmp:mul64` | Multiply two 64-bit integer values, discarding overflow. |
| `xdmp:multipart-decode` | Extract the parts from a multipart encoding. The first item in the  sequence is a manifest, and the remaining items are the decoded parts.    An attempt will be made to determine the type of content based on  headers such as the part's content-type. If possible, an element will be  returned, falling back to an xs:string, and finally binary().    The options control how the parts are unpacked, and are similar to  xdmp:zip-get  -  default-namespace, repair,  format, default-language,  and encoding. The options apply to all parts, so specifying a format of  binary will cause all parts to be returned as binary, and specifying text  will cause all parts to be returned as xs:string if possible, falling back  to binary() if necessary. This is useful if different parts need different  options, in which case the resulting strings can each be passed to  xdmp:unquote   with appropriate options. |
| `xdmp:multipart-encode` | Create a multipart encoding of the specified node. The returned binary  node can be passed to  xdmp:http-post  .  The manifest is modeled after the  manifest that is passed to  xdmp:zip-create  ,  with the headers element being  the same as is described for  xdmp:http-get   allowing users to add arbitrary  headers to each part. If a content-type header is not specified for a part,  it will be determined if possible from the content.    There should be one part element for each node in the content sequence.    Each part also has an optional options node to control how xml or text  will be serialized. The two options are the same as for  xdmp:save  .    <part>   <headers>    <Content-Type>image/jpeg</Content-Type>   <headers>   <options>    <output-encoding>...</output-encoding>    <output-sgml-character-entities>...</output-sgml-character-entities>   </options>  </part> |
| `xdmp:node-kind` | Returns an xs:string  representing the node's kind: either  "document", "element", "attribute", "text", "namespace",  "processing-instruction", "binary", or "comment".      The fn:node-kind  builtin was dropped from the final XQuery 1.0  spec. This is the equivalent function in the xdmp:  namespace  carried over for MarkLogic 1.0 dialects. |
| `xdmp:node-metadata` | Returns the metadata value of a given node. |
| `xdmp:node-metadata-value` | Returns the metadata value of a node for a particular key. |
| `xdmp:not64` | NOT a 64-bit integer value. |
| `xdmp:octal-to-integer` | Parses an octal string, returning an integer. |
| `xdmp:or64` | OR two 64-bit integer values. |
| `xdmp:parse-dateTime` | Parses a string containing date, time or dateTime using the supplied  picture argument and returns a dateTime value. While this function  is closely related to other XSLT functions, it is available in XSLT  as well as in all XQuery dialects and in Server-Side JavaScript. |
| `xdmp:parse-yymmdd` | Parses a string containing date, time or dateTime using the supplied  picture argument and returns a dateTime value.  While this function  is closely related to other XSLT functions, it is available in XSLT  as well as in all XQuery dialects and in Server-Side JavaScript. |
| `xdmp:position` | Returns an integer value representing the starting position of a  string within the search string. Note, the string starting position is 1.  If the first parameter is empty, the result is the empty sequence. |
| `xdmp:random` | Returns a random unsigned integer between 0 and a number up to 64 bits long. |
| `xdmp:resolve-uri` | Resolves a relative URI against an absolute URI. If $base is specified,  the URI is resolved relative to that base. If $base is not specified, the  base is set to the base-uri property from the static context, if the  property exists; if it does not exist, an error is thrown. |
| `xdmp:rshift64` | Right-shift a 64-bit integer value. |
| `xdmp:set-response-output-method` | Sets the serialization method. This overrides  any output option set in the xdmp:output XQuery prolog  option. |
| `xdmp:sha1` | Calculates the SHA1 hash of the given argument. |
| `xdmp:sha256` | Calculates the SHA256 hash of the given argument. |
| `xdmp:sha384` | Calculates the SHA384 hash of the given argument. |
| `xdmp:sha512` | Calculates the SHA512 hash of the given argument. |
| `xdmp:sleep` | Delays for a specific amount of time. |
| `xdmp:step64` | Combines an initial hash with a subsequent hash. |
| `xdmp:strftime` | Formats a dateTime value using POSIX strftime. This function uses  the POSIX strftime system call in the way it is implemented on each  platform. For other XQuery functions that have more functionality  (for example, for things like timezones), use one or more if the  various XQuery or XSLT standard functions such as  fn:format-dateTime  . |
| `xdmp:timestamp-to-wallclock` | Converts a 64 bit timestamp value to an xs:dateTime. |
| `xdmp:type` | Returns the name of the simple type of the atomic value argument as an  xs:QName.  This function is a built-in. |
| `xdmp:user-last-login` | Returns the last-login node for the current user. If no last-login  database is specified in the App Server configuration, then the empty  sequence is returned. |
| `xdmp:wallclock-to-timestamp` | Converts an xs:dateTime to a 64 bit timestamp value. |
| `xdmp:xor64` | XOR two 64-bit integer values. |

### Function Values

*Detailed documentation: [functions/function-values.md](functions/function-values.md)*

| Function | Summary |
|----------|---------|
| `xdmp:annotation` | Returns the named annotation from the function. |
| `xdmp:apply` | Applies an xdmp:function with the given parameters. |
| `xdmp:function` | Returns a function value as an xdmp:function   type.  You can return an xdmp:function   from an expression or  a function. You can execute the function referred to by an  xdmp:function    by passing the xdmp:function   value to  xdmp:apply. If the module-path ends with a file  extension matching the ones configured for  application/vnd.marklogic-javascript in your  MarkLogic Mimetypes configuration, and the function's namespace URI is  empty, the module is considered to be JavaScript. In this case, the function  parameter can be empty. |
| `xdmp:function-module` | Returns the module location (if any) that the  xdmp:function   value refers to. |
| `xdmp:function-name` | Returns the QName of the function(s) that the  xdmp:function   refers to. |
| `xdmp:function-parameter-name` | Returns the name of the parameter at the designated (1-based) position from the given function's signature. |
| `xdmp:function-parameter-type` | Returns the type of the parameter at the designated (1-based) position from the given function's signature. |
| `xdmp:function-return-type` | Returns the return type from the given function's signature. |
| `xdmp:function-signature` | Returns the signature of the function that the argument refers to. |
| `xdmp:functions` | Returns all in-scope functions. |

### Json

*Detailed documentation: [functions/json.md](functions/json.md)*

| Function | Summary |
|----------|---------|
| `json:array` | Creates a (JSON) array, which is like a sequence of values, but allows  for nesting. |
| `json:array-pop` | Pop a value from the end of the array. |
| `json:array-push` | Push a value to the end of the array, increasing the size of the array  by one. |
| `json:array-resize` | Resize the array to the new size. If the new size is greater than the old  size, the new entries will be null. If the new size if smaller than the old  size, the extra entries will be removed. |
| `json:array-set-javascript-by-ref` | If true is specified, sets a json:array to be passed to JavaScript by  reference. By default, a map:map is passed to JavaScript by value. |
| `json:array-size` | Returns the size of the array. |
| `json:array-values` | Returns the array values as an XQuery sequence. |
| `json:array-with` | Push a value to the end of the array, increasing the size of the array  by one. Returns the array as the result. |
| `json:null` | Returns the JSON null value, which is an empty sequence to XQuery,  but not a Sequence when passed to JavaScript. |
| `json:object` | Creates a JSON object, which is a kind of map with a fixed and ordered set of  keys. |
| `json:object-define` | Creates a JSON object. |
| `json:set-item-at` | Sets a value in an array at a specified position. |
| `json:subarray` | Extract a subarray from an array, producing a new array.  The second and third arguments to this function operate similarly to  those of fn:subsequence for XQuery sequences. |
| `json:to-array` | Constructs a json:array from a sequence of items. |
| `xdmp:from-json` | Atomizes a JSON node, returning a JSON value. |
| `xdmp:from-json-string` | Parses a string as JSON, returning an item sequence. |
| `xdmp:json-validate` | Validate a JSON node against a JSON Schema. If the node is not valid per the schema, raise an error. Otherwise, return the input node. |
| `xdmp:json-validate-node` | Validate a JSON node against a JSON Schema. If the node is not valid per the schema, raise an error. Otherwise, return the input node. |
| `xdmp:json-validate-report` | Validate a JSON node against a JSON Schema and return an error report. |
| `xdmp:json-validate-report-node` | Validate a JSON node against a JSON Schema and return an error report. |
| `xdmp:to-json` | Constructs a JSON document. |
| `xdmp:to-json-string` | Returns a string representing a JSON  serialization of a given item sequence. |

### Search

*Detailed documentation: [functions/search.md](functions/search.md)*

| Function | Summary |
|----------|---------|
| `cts:estimate` | Returns the number of fragments selected by a search.  This can be used as a fast estimate of the number of results.   To retrieve the number of fragments using an XPath expression, use  xdmp:estimate instead. |
| `xdmp:diacritic-less` | Returns the specified string, converting all of the characters with diacritics to characters without diacritics. |
| `xdmp:estimate` | Returns the number of fragments selected by an expression.  This can be used as a fast estimate of the number of items in a sequence.  To retrieve the number of fragments using a    cts:query  object, use   cts:estimate  instead. |
| `xdmp:exists` | Returns true if any fragment is selected by an expression, false if no  fragments are selected. This can be used as a fast existence check. |
| `xdmp:plan` | Returns an XML element recording information about how the given  expression will be processed by the index. The information is a  structured representation of the information provided in the error log  when query trace is enabled. The query will be processed up to the  point of getting an estimate of the number of fragments returned by the  index. |
| `xdmp:plannable` | Returns a boolean showing whether the given expression is suitable to use  with xdmp:plan. Expressions that are fully searchable are  "plannable"; that is, they will return query plan output when used with  xdmp:plan. |
| `xdmp:request-timestamp` | Returns the system timestamp for this request if the request is a query  statement. Returns the empty sequence if the current request is an update  statement. |

### Xml

*Detailed documentation: [functions/xml.md](functions/xml.md)*

| Function | Summary |
|----------|---------|
| `xdmp:quote` | Returns the unevaluated serialized representation  of the input parameter as a string. |
| `xdmp:unquote` | Parses a string as XML, returning one or more document nodes. |

### Xquery Context

*Detailed documentation: [functions/xquery-context.md](functions/xquery-context.md)*

| Function | Summary |
|----------|---------|
| `xdmp:describe` | Returns a string representing the  description of a given item sequence. If you take  the output of this function and evaluate it as an XQuery program,  it returns the item(s) input to the function. |
| `xdmp:eval` | Returns the result of evaluating a string as an XQuery module.  To evaluate JavaScript, see  xdmp:javascript-eval. |
| `xdmp:eval-in` | [DEPRECATED: use xdmp:eval with the  database option instead] Returns the result of evaluating a string as  an XQuery module in a given database. |
| `xdmp:invoke` | Returns the result of evaluating an XQuery or Server-Side JavaScript  module at the given path. |
| `xdmp:invoke-function` | Returns the result of evaluating  an XQuery  function value. |
| `xdmp:invoke-in` | [DEPRECATED: use xdmp:invoke with the  database option instead] Returns the result of evaluating a module  at the given path. |
| `xdmp:javascript-eval` | Returns the result of evaluating a string as a JavaScript module.  To evaluate XQuery, see xdmp:eval. |
| `xdmp:node-collections` | Returns any collections for the node's document in the database. If  the specified node does not come from a document in a database, then  xdmp:node-collections    returns an empty sequence. |
| `xdmp:node-database` | Returns the database id where the parameter is stored. If  the specified node does not come from a document in a database, then  xdmp:node-database    returns an empty list. |
| `xdmp:node-get-info` | This function returns information about the node i.e. the node-repid, uniquekey, compressed tree size and database of an input node.  Database is true if the node is read from the database, false otherwise. |
| `xdmp:node-uri` | Returns the document-uri property of the parameter or its ancestor. |
| `xdmp:path` | Returns a string whose value corresponds to the  path of the node. |
| `xdmp:set` | Set the value of a variable to the specified expression. The  xdmp:set command allows you to introduce changes to the  state (side effects) of a query by changing the value of a variable to  something other than what it is bound to. |
| `xdmp:spawn` | Place the specified module on the task queue for evaluation. |
| `xdmp:spawn-function` | Place the specified function value on the task queue for evaluation. |
| `xdmp:spawn-in` | [DEPRECATED: use xdmp:spawn with the  database option instead] Place the specified module on the task  queue for evaluation. It will be evaluated in the given database. |
| `xdmp:sql` | Executes an ad hoc SQL query. This function is for testing  your SQL views when data modeling. |
| `xdmp:sql-plan` | Returns a node representing the query plan of the given SQL SELECT query.  Raises an error if the SQL query is not a SELECT query. |
| `xdmp:unpath` | Evaluate a string as an XPath and return the corresponding node(s).  Any value that is the result of xdmp:path is a  valid input to xdmp:unpath. Any invalid inputs  throw an XDMP-UNPATH exception. To evaluate non-XPath  expressions, use xdmp:value. |
| `xdmp:value` | Evaluate an expression in the context of the current evaluating statement.  This differs from xdmp:eval in that xdmp:value  preserves all of the context from the calling query, so you do not  need to re-define namespaces, variables, and so on. Although the expression  retains the context from the calling query, it is evaluated in its own  transaction with same-statement isolation. |
| `xdmp:with-namespaces` | Evaluates the expression in the context of a specific set of namespace  bindings. |
| `xdmp:xquery-version` | Returns the XQuery language version of the calling module.  Currently supported XQuery versions are:  	"0.9-ml": The legacy MarkLogic XQuery version. This was the only   XQuery version available on MarkLogic Server 3.2 and   earlier. It is based on the May 2003 XQuery Draft Recommendation,   with MarkLogic extensions   	"1.0-ml": XQuery version 1.0, with MarkLogic extensions. This   is the preferred version of XQuery beginning with release 4.0.   	"1.0": Strict XQuery version 1.0. This XQuery version complies   as closely as possible with the published XQuery 1.0 specification. |
| `xdmp:xslt-eval` | Executes an XSLT stylesheet against a node. |
| `xdmp:xslt-invoke` | Executes an XSLT stylesheet against a node. |

### General

*Detailed documentation: [functions/general.md](functions/general.md)*

| Function | Summary |
|----------|---------|
| `cts:valid-tde-context` | Parses path expressions and resolves namespaces using the $map parameter. Returns true if the argument is permissible as a context element in a TDE template. |
| `json:check-config` | This function checks a json configuration object and returns a report. |
| `json:config` | This function creates a configuration object 			for a specified strategy. |
| `json:transform-from-json` | This function transforms a JSON document to 		 XML using the default ("basic") strategy. |
| `json:transform-to-json` | This function transforms an XML document to JSON 		 using the default ("basic") strategy if none is 		 supplied. |
| `json:transform-to-json-object` | This function transforms an XML document to JSON 		 and returns an object. |
| `json:transform-to-json-xml` | This function transforms an XML document to 		 JSON and returns an xml element. |
| `map:clear` | Clear a map. |
| `map:contains` | Returns true if the key exists in the map. |
| `map:count` | Returns the number of keys used in the map. |
| `map:delete` | Delete a value from a map. |
| `map:entry` | Constructs a new map with a single entry consisting of the key and value  specified as arguments. This is particularly helpful when  used as part of an argument to map:new(). |
| `map:get` | Get a value from a map. |
| `map:keys` | Get the keys used in the map. |
| `map:map` | Creates a map. |
| `map:new` | Constructs a new map by combining the keys from the maps given as an argument.  If a given key exists in more than one argument map, the value from the  last such map is used. |
| `map:put` | Put a value into a map at the given key. |
| `map:set-javascript-by-ref` | If true is specified, sets a map:map to be passed to JavaScript by reference.  By default, a map:map is passed to JavaScript by value. |
| `map:with` | Updates a map, inserting a value into it at the given key. The map is returned as the result. |
| `rest:check-options` | This function validates the specified options node. Validation  includes both schema validation and some additional  rule-based validation. An empty sequence indicates valid options and any  problems are reported via rest:report elements. |
| `rest:check-request` | This function takes a request element and returns a report of the  problems found. If this function  does not return an empty sequence, you have made a mistake and the library will not perform reliably. |
| `rest:get-raw-query-params` | This function extracts all of the query parameters and returns them in a map.  This does not include the parameters that would be derived from matching the  URI string. No error checking or type conversion is performed by this  function. The parameters returned by this function are all strings, as  they are not type checked. |
| `rest:matching-request` | This function returns the request element in 	 the options node that matches the specified URI. If 	 you only specify options parameter, all criteria in the request 	 environment are considered. If you supply specific criteria, the 	 filter is less strict, allowing the same options block to be used 	 for simple url-based rewriting as well as request processing. |
| `rest:process-request` | This function is used in the endpoint main module to parse the 	 incoming request against the options. It returns a map that 	 contains all of the parameters as typed values. Processing the 	 request also checks all of the associated conditions and will 	 raise an error if any condition is not met.    If the request is processed successfully, then all of the 	 conditions have been met and the returned map contains all of 	 the parameters. If not, an error occurs. |
| `rest:report-error` | This function formats the specified error structure. |
| `rest:rewrite` | This function is used in the URL rewriter to map 		the incoming request to an endpoint. By default, if you 		supply only options, all aspects of the request environment 		are used for rewriting. If you supply specific criteria, the 		filter is less strict, allowing the same options block to be 		used for simple url-based rewriting as well as request 		processing. |
| `tde:column-get-permissions` | This function returns the permissions granted to a protected column. |
| `tde:column-remove-permissions` | This function removes all permissions from a protected column. |
| `tde:column-set-permissions` | This function sets the permissions of a protected column.    Any previous permissions on the column are removed. |
| `tde:get-view` | This function returns a view's description using a schema and a view name. |
| `tde:node-data-extract` | Extracts row or triple data from a list of specified documents by applying  extraction templates that are either stored in the schema database or  provided as a second argument. |
| `tde:template-batch-insert` | This function validates and inserts multiple templates, is similar to   tde:template-insert     for individual template, throw errors for any invalid template or   duplicate template URIs provided by sequence of argument with   tde:template-info   .      Before inserting, validates each    new template against all other new and existing (not in the new URIs list)    templates with same schema/view-name. Any existing template with the same    URI in the new URIs list will be ignored and replaced directly even if the    new template has same URI but different schema/view-name. |
| `tde:template-info` | This function returns a map:map (object[]) containing individual template information used for   inserting templates with tde:template-batch-insert(). Permissions and collections   are optional. If no permissions specified, xdmp:default-permissions() is the default. |
| `tde:template-insert` | This function validates the template, inserts the template as a document into   the tde collection of the schema database (if executed on the content database)   with the default permissions, and reindexes the database.      Note that, when a template is inserted, only those document fragments affected   by the template are re-indexed. For more information, see Validating and Inserting a Template in the Application Developer's Guide. |
| `tde:validate` | In addition to  xdmp:validate   that can be used for validating against the extraction template schema.   The recommended workflow for users is to validate an extraction template  before inserting it into the schema database. Unless you use the     tde:template-insert function,  Ill-formed templates are not validated or rejected at document insertion time.    For more information on extraction templates,  see Template Driven Extraction (TDE) in the Application Developer's Guide. |
| `view:add-column` | This function adds column specifications to the current set of column specifications on the named  view in the named schema. |
| `view:add-field` | This function adds a field to the named view. |
| `view:add-permissions` | This function adds permissions to those already set for the named view in the  named schema specification. |
| `view:collection` | This function return the URI of the protected collection holding all the views. |
| `view:collection-view-scope` | This function constructs a new collection-style view scope specification.    For details on view scoping, see Defining View Scope in the SQL Data Modeling Guide. |
| `view:column` | This function constructs a new column specification. |
| `view:columns` | This function returns the sequence of column specifications set in the named  view in the named schema. |
| `view:create` | This function creates a new view in the specified schema specification. The id of the view is returned.  The view is checked for validity.     Prior to executing this function, you must create a range index for each column   in your view. For details on element range indexes, see  Range Indexes and Lexicons in the Administrator's Guide. |
| `view:element-view-scope` | This function constructs a new element-style view scope specification.    For details on view scoping, see Defining View Scope in the SQL Data Modeling Guide. |
| `view:field` | This function constructs a new element-style field specification for the named field. |
| `view:fields` | This function returns the fields set on the named view. |
| `view:get` | This function returns the named view from the named schema specification. |
| `view:get-bindings` | This function generates a binding map suitable for use with  cts:parse from the named view. |
| `view:get-by-id` | This function returns the view with the specified id. |
| `view:get-column` | This function returns the named column specification set in the named  view in the named schema. |
| `view:get-field` | This function returns the element specification for the named field. |
| `view:get-permissions` | This function returns the permissions set on the specified view. |
| `view:get-view-scope` | This function returns the scope of the named view in the  named schema. |
| `view:remove` | This function removes the named view from the named schema specification. |
| `view:remove-by-id` | This function removes the view with the specified id. |
| `view:remove-column` | This function removes a column specification from the named  view in the named schema. |
| `view:remove-field` | This function removes a field from the named view. |
| `view:remove-permissions` | This function removes permissions from those set for the named view in the  named schema specification. |
| `view:schema-add-permissions` | This function adds permissions to the specified schema specification. |
| `view:schema-create` | This function creates a new relational schema in the Schema database.  	The schema id is returned. Every SQL deployment must include a default 	schema, called "main," as shown in the example below.     This schema is typically created for Range Views. However, such a schema can also   contain Template Views. Note that Range Views cannot be created in a schema   created by a Template View. |
| `view:schema-get` | This function returns the named schema specification document. |
| `view:schema-get-permissions` | This function returns the permissions set on the specified schema. |
| `view:schema-remove` | This function removes the specified schema.  Removing a schema removes all the views that are part of that schema. |
| `view:schema-remove-permissions` | This function removes permissions from the specified schema specification. |
| `view:schema-set-permissions` | This function sets permissions on the specified schema specification.  Any existing permissions for the schema and removed. |
| `view:schemas` | This function returns all of the schema specifications. |
| `view:set-columns` | This function replaces the current set of column specifications on the named  view in the named schema with a new set of columns. |
| `view:set-fields` | This function sets the specified fields on the specified view. Any existing fields are  replaced or removed. |
| `view:set-name` | This function renames the named view in the named schema specification. |
| `view:set-permissions` | This function sets the permissions for the named view in the  named schema specification. Any existing permissions for the view and  removed. |
| `view:set-view-scope` | This function sets the scope of the named view in the named  schema specification. |
| `view:views` | This function returns all of the view specifications in the named schema. |
| `xdmp:collection-delete` | Deletes from the database every document in a collection. If there are  no documents in the specified collection, then nothing is deleted, and  xdmp:collection-delete   still returns the empty sequence. |
| `xdmp:directory-create` | Creates a directory. If security is enabled,  the document permissions and collections are set to the given parameters,  if supplied. Otherwise, the current user's default permissions and/or  collections are applied. If the beginning of the document URI is  protected, the user must have access to that URI privilege. If the  directory URI does not end with a '/' one is added. If the directory already  exists, then an XDMP-DIREXISTS exception is thrown. |
| `xdmp:directory-delete` | Deletes a directory and all of its child and descendant documents and  directories from the database. |
| `xdmp:document-add-collections` | Adds the named document to the given collections. For each collection  that is protected, the user must have permissions to update that  collection or have the any-collection privilege.  For each unprotected collection, the user must have the  unprotected-collections privilege. |
| `xdmp:document-add-permissions` | Adds the given permissions to the given document or directory.  The user must have update or insert permissions on the document. |
| `xdmp:document-add-properties` | Adds a sequence of properties to the properties of a document. |
| `xdmp:document-assign` | Assign a document URI to a forest index,  using the same algorithm as xdmp:document-insert.  The return value will be a positive integer  from 1 to $forest-count.       This function does not insert or update the document;  instead, it returns the index of the forest  to which the document URI would be assigned  if it were inserted as a new document.  In order to match the document to the correct forest,  use the list of forest-IDs as returned by xdmp:database-forests.       If the document already exists, this function may not  return the correct forest for the document. In this case,  xdmp:document-forest will return the  correct forest.       If "assignment-policy" is specified, this function uses the specified  policy to calculate the assignment. Otherwise, it uses the assignment  policy of the context database to calculate the assignment.       This function works only with the bucket assignment policy, the segment  assignment policy and the (now deprecated) legacy assignment policy. It  reports an error if any other policy is specified.       Note that, if there are read-only or delete-only forests in a database that  uses the bucket policy, the application may need to call this function twice  to get the right assignment. The first call should pass in the total number  of forests, including the read-only or delete-only ones. If the returned value  happens to be a read-only or delete-only forest, the second call should pass  in the number of forests that excludes the read-only or delete-only ones and  pass in "legacy" as the third parameter. |
| `xdmp:document-delete` | Deletes a document from the database. |
| `xdmp:document-insert` | Inserts a new document into the database if a document with the  specified URI does not already exist. If a document already exists  at the specified URI, the function replaces the content of the existing  document with the specified content (the $root parameter)  as an update operation. In addition to replacing the content,  xdmp:document-insert replaces any permissions, collections,  and quality with the ones specified (or with the default values for these  parameters, if not explicitly specified). Also, if a properties  document exists at the same URI, that properties document (including any  content it contains) is preserved. |
| `xdmp:document-load` | Inserts a new document with the specified URI. If a document already exists  at the URI, the function replaces the content in the existing document as  an update operation. |
| `xdmp:document-partition-assign` | Assign a document to a partition number,  using the partition queries in the database or in the second argument.  The return value is the partition number where  the document should be inserted. |
| `xdmp:document-put-metadata` | Adds metadata to the document. If any key already exists in the document  metadata, the new specified value replaces the old one.   Metadata values are strings. Non-string values are converted to strings. |
| `xdmp:document-remove-collections` | Removes the named document from the given collections. For each  collection that is protected, the user must have permissions to update  that collection or have the any-collection privilege. For each  unprotected collection, the user must have the  unprotected-collections privilege. |
| `xdmp:document-remove-metadata` | Removes metadata with certain keys from a document. |
| `xdmp:document-remove-permissions` | Removes the given permissions from the named document or directory.  The user must have update permissions on the document or directory. |
| `xdmp:document-remove-properties` | Removes a sequence of properties from the properties of a document. If  properties with the QNames given do not exist, nothing is done. |
| `xdmp:document-set-collections` | Sets the named document to belong to the given collections, replacing any  previously set collections on the named document. To preserve existing  collections, use xdmp:document-add-collections. For each  collection that is protected, the user must have permissions to update  that collection or have the any-collection privilege. For each  unprotected collection, the user must have the  unprotected-collections privilege. |
| `xdmp:document-set-metadata` | Sets metadata to the document. All existing metadata in the document will be  replaced with the newly specified ones.   Metadata values are strings. Non-string values are converted to strings. |
| `xdmp:document-set-permissions` | Sets the permissions on the named document (or directory) to the given  permissions, replacing any permissions previously set on the  document (or directory). To preserve  any existing permissions, use  xdmp:document-add-permissions.  .  The user must have update permissions on the document or directory. |
| `xdmp:document-set-properties` | Sets the properties of a document to the given sequence of elements,  replacing any properties that already exist on the document. To preserve  existing document properties, use xdmp:document-add-properties.  Each element QName is the property name and the element value is the  property value. Modifying properties requires update permissions on a  document. |
| `xdmp:document-set-property` | Sets a property on a document. If any properties with the same property  QName exist, they are replaced with the new property. If no properties  exist with the same QName, the new property is added. |
| `xdmp:document-set-quality` | Sets the quality of the document with the given URI.  If the quality of the document is positive,  the relevance score of the document is increased in text  search functions. The converse is true for "negative" quality. |
| `xdmp:load` | [DEPRECATED: use xdmp:document-load   instead]  Inserts a new document from the XML file at $path if a document  with the specified URI does not already exist. Otherwise, the  function replaces the content in the existing document as an update  operation. |
| `xdmp:lock-acquire` | Acquire a lock on a document or directory for an extended amount of time.  Locks restrict updates to a document or directory to the user who acquires  the lock. |
| `xdmp:lock-for-update` | Acquires an intent exclusive transaction lock on a URI.  If a shared transaction lock on the URI is already held by  the current transaction it is promoted to an exclusive lock.  If a shared or exclusive transaction lock on the URI is already  held by some other transaction, this function blocks until  that lock is released. |
| `xdmp:lock-release` | Unlock a document or directory. Releases the lock created with  xdmp:lock-acquire  . |
| `xdmp:merge` | Starts merging the forests of the database, subject to specified  options. |
| `xdmp:merging` | Returns the forest IDs of any currently merging database forests. |
| `xdmp:node-delete` | Deletes a node from the database.  On-the-fly constructed nodes cannot be deleted. |
| `xdmp:node-insert-after` | Adds an immediately following sibling to a node. |
| `xdmp:node-insert-before` | Adds an immediately preceding sibling to a node. |
| `xdmp:node-insert-child` | Adds a new last child to a node.  For XML documents, only element nodes and document nodes can have children.  For JSON documents, object nodes and array nodes can have children.  Element nodes, object nodes, and array nodes cannot have document node  children.  Document nodes cannot have multiple roots.  On-the-fly constructed nodes cannot be updated.  The parameters must specify individual nodes and not node sets. |
| `xdmp:node-replace` | Replaces a node. |
| `xdmp:partition-forests` | Returns a sequence of forest IDs with the specified partition number |
| `xdmp:query-partitions` | This function returns the partition numbers of the partitions that the specified query will be searched on. |
| `xdmp:range-partition-forests` | Given a value, the function returns a list of forests that have ranges the  value falls into. This function reports an error if the context database  doesn't have the range assignment policy configured. |
| `xdmp:save` | Serializes a node as text and saves it to a file. The node can be any  node, including a document node, an element node, a text node, or a binary  node. |

## Alphabetical Index

Each function links to its detailed documentation file.

- [`cts:estimate`](functions/search.md) - Returns the number of fragments selected by a search
- [`cts:valid-tde-context`](functions/general.md) - Parses path expressions and resolves namespaces using the $map parameter
- [`json:array`](functions/json.md) - Creates a (JSON) array, which is like a sequence of values, but allows
  for nesting
- [`json:array-pop`](functions/json.md) - Pop a value from the end of the array
- [`json:array-push`](functions/json.md) - Push a value to the end of the array, increasing the size of the array
  by one
- [`json:array-resize`](functions/json.md) - Resize the array to the new size
- [`json:array-set-javascript-by-ref`](functions/json.md) - If true is specified, sets a json:array to be passed to JavaScript by
  reference
- [`json:array-size`](functions/json.md) - Returns the size of the array
- [`json:array-values`](functions/json.md) - Returns the array values as an XQuery sequence
- [`json:array-with`](functions/json.md) - Push a value to the end of the array, increasing the size of the array
  by one
- [`json:check-config`](functions/general.md) - This function checks a json configuration object and returns a report
- [`json:config`](functions/general.md) - This function creates a configuration object 
			for a specified strategy
- [`json:null`](functions/json.md) - Returns the JSON null value, which is an empty sequence to XQuery,
  but not a Sequence when passed to JavaScript
- [`json:object`](functions/json.md) - Creates a JSON object, which is a kind of map with a fixed and ordered set of
  keys
- [`json:object-define`](functions/json.md) - Creates a JSON object
- [`json:set-item-at`](functions/json.md) - Sets a value in an array at a specified position
- [`json:subarray`](functions/json.md) - Extract a subarray from an array, producing a new array
- [`json:to-array`](functions/json.md) - Constructs a json:array from a sequence of items
- [`json:transform-from-json`](functions/general.md) - This function transforms a JSON document to 
		  XML using the default ("basic") strategy
- [`json:transform-to-json`](functions/general.md) - This function transforms an XML document to JSON 
		  using the default ("basic") strategy if none is 
		  supplied
- [`json:transform-to-json-object`](functions/general.md) - This function transforms an XML document to JSON 
		  and returns an object
- [`json:transform-to-json-xml`](functions/general.md) - This function transforms an XML document to 
		  JSON and returns an xml element
- [`map:clear`](functions/general.md) - Clear a map
- [`map:contains`](functions/general.md) - Returns true if the key exists in the map
- [`map:count`](functions/general.md) - Returns the number of keys used in the map
- [`map:delete`](functions/general.md) - Delete a value from a map
- [`map:entry`](functions/general.md) - Constructs a new map with a single entry consisting of the key and value
  specified as arguments
- [`map:get`](functions/general.md) - Get a value from a map
- [`map:keys`](functions/general.md) - Get the keys used in the map
- [`map:map`](functions/general.md) - Creates a map
- [`map:new`](functions/general.md) - Constructs a new map by combining the keys from the maps given as an argument
- [`map:put`](functions/general.md) - Put a value into a map at the given key
- [`map:set-javascript-by-ref`](functions/general.md) - If true is specified, sets a map:map to be passed to JavaScript by reference
- [`map:with`](functions/general.md) - Updates a map, inserting a value into it at the given key
- [`rest:check-options`](functions/general.md) - This function validates the specified options node
- [`rest:check-request`](functions/general.md) - This function takes a request element and returns a report of the 
  problems found
- [`rest:get-raw-query-params`](functions/general.md) - This function extracts all of the query parameters and returns them in a map
- [`rest:matching-request`](functions/general.md) - This function returns the request element in 
	  the options node that matches the specified URI
- [`rest:process-request`](functions/general.md) - This function is used in the endpoint main module to parse the 
	  incoming request against the options
- [`rest:report-error`](functions/general.md) - This function formats the specified error structure
- [`rest:rewrite`](functions/general.md) - This function is used in the URL rewriter to map 
		the incoming request to an endpoint
- [`sem:resolve-iri`](functions/extension.md) - Resolves a relative URI against an absolute URI
- [`tde:column-get-permissions`](functions/general.md) - This function returns the permissions granted to a protected column
- [`tde:column-remove-permissions`](functions/general.md) - This function removes all permissions from a protected column
- [`tde:column-set-permissions`](functions/general.md) - This function sets the permissions of a protected column
- [`tde:get-view`](functions/general.md) - This function returns a view's description using a schema and a view name
- [`tde:node-data-extract`](functions/general.md) - Extracts row or triple data from a list of specified documents by applying
  extraction templates that are either stored in the schema database or
  provided as a second argument
- [`tde:template-batch-insert`](functions/general.md) - This function validates and inserts multiple templates, is similar to 
    tde:template-insert
    
    for individual template, throw errors for any invalid template or 
    duplicate template URIs provided by sequence of argument with
    tde:template-info
    
- [`tde:template-info`](functions/general.md) - This function returns a map:map (object[]) containing individual template information used for
    inserting templates with tde:template-batch-insert()
- [`tde:template-insert`](functions/general.md) - This function validates the template, inserts the template as a document into 
    the tde collection of the schema database (if executed on the content database) 
    with the default permissions, and reindexes the database
- [`tde:validate`](functions/general.md) - In addition to 
  xdmp:validate
  
  that can be used for validating against the extraction template schema
- [`view:add-column`](functions/general.md) - This function adds column specifications to the current set of column specifications on the named 
  view in the named schema
- [`view:add-field`](functions/general.md) - This function adds a field to the named view
- [`view:add-permissions`](functions/general.md) - This function adds permissions to those already set for the named view in the 
  named schema specification
- [`view:collection`](functions/general.md) - This function return the URI of the protected collection holding all the views
- [`view:collection-view-scope`](functions/general.md) - This function constructs a new collection-style view scope specification
- [`view:column`](functions/general.md) - This function constructs a new column specification
- [`view:columns`](functions/general.md) - This function returns the sequence of column specifications set in the named 
  view in the named schema
- [`view:create`](functions/general.md) - This function creates a new view in the specified schema specification
- [`view:element-view-scope`](functions/general.md) - This function constructs a new element-style view scope specification
- [`view:field`](functions/general.md) - This function constructs a new element-style field specification for the named field
- [`view:fields`](functions/general.md) - This function returns the fields set on the named view
- [`view:get`](functions/general.md) - This function returns the named view from the named schema specification
- [`view:get-bindings`](functions/general.md) - This function generates a binding map suitable for use with 
  cts:parse from the named view
- [`view:get-by-id`](functions/general.md) - This function returns the view with the specified id
- [`view:get-column`](functions/general.md) - This function returns the named column specification set in the named 
  view in the named schema
- [`view:get-field`](functions/general.md) - This function returns the element specification for the named field
- [`view:get-permissions`](functions/general.md) - This function returns the permissions set on the specified view
- [`view:get-view-scope`](functions/general.md) - This function returns the scope of the named view in the
  named schema
- [`view:remove`](functions/general.md) - This function removes the named view from the named schema specification
- [`view:remove-by-id`](functions/general.md) - This function removes the view with the specified id
- [`view:remove-column`](functions/general.md) - This function removes a column specification from the named 
  view in the named schema
- [`view:remove-field`](functions/general.md) - This function removes a field from the named view
- [`view:remove-permissions`](functions/general.md) - This function removes permissions from those set for the named view in the 
  named schema specification
- [`view:schema-add-permissions`](functions/general.md) - This function adds permissions to the specified schema specification
- [`view:schema-create`](functions/general.md) - This function creates a new relational schema in the Schema database
- [`view:schema-get`](functions/general.md) - This function returns the named schema specification document
- [`view:schema-get-permissions`](functions/general.md) - This function returns the permissions set on the specified schema
- [`view:schema-remove`](functions/general.md) - This function removes the specified schema
- [`view:schema-remove-permissions`](functions/general.md) - This function removes permissions from the specified schema specification
- [`view:schema-set-permissions`](functions/general.md) - This function sets permissions on the specified schema specification
- [`view:schemas`](functions/general.md) - This function returns all of the schema specifications
- [`view:set-columns`](functions/general.md) - This function replaces the current set of column specifications on the named 
  view in the named schema with a new set of columns
- [`view:set-fields`](functions/general.md) - This function sets the specified fields on the specified view
- [`view:set-name`](functions/general.md) - This function renames the named view in the named schema specification
- [`view:set-permissions`](functions/general.md) - This function sets the permissions for the named view in the 
  named schema specification
- [`view:set-view-scope`](functions/general.md) - This function sets the scope of the named view in the named 
  schema specification
- [`view:views`](functions/general.md) - This function returns all of the view specifications in the named schema
- [`xdmp:QName-from-key`](functions/extension.md) - Construct a QName from a string of the form "{namespaceURI}localname"
- [`xdmp:add64`](functions/extension.md) - Add two 64-bit integer values, discarding overflow
- [`xdmp:and64`](functions/extension.md) - AND two 64-bit integer values
- [`xdmp:annotation`](functions/function-values.md) - Returns the named annotation from the function
- [`xdmp:apply`](functions/function-values.md) - Applies an xdmp:function with the given parameters
- [`xdmp:atomizable`](functions/extension.md) - Returns true if a value could be atomized without error
- [`xdmp:aws-region`](functions/extension.md) - Returns the current Amazon Web Services region
- [`xdmp:aws-services-domain`](functions/extension.md) - Returns the current Amazon Web Services services domain
- [`xdmp:aws-services-partition`](functions/extension.md) - Returns the current Amazon Web Services services partition
- [`xdmp:azure-environment`](functions/extension.md) - Returns the current Microsoft Azure Environment
- [`xdmp:azure-region`](functions/extension.md) - Returns the current Microsoft Azure Region
- [`xdmp:base64-decode`](functions/extension.md) - Converts base64-encoded string to plaintext
- [`xdmp:base64-encode`](functions/extension.md) - Converts plaintext into base64-encoded string
- [`xdmp:binary-decode`](functions/extension.md) - Converts an encoded byte sequence, passed in as a binary node, from the
  specified encoding to a unicode string
- [`xdmp:binary-to-integer`](functions/extension.md) - Parses a binary string, returning an integer
- [`xdmp:caller-dialect`](functions/extension.md) - Returns the dialect (e
- [`xdmp:castable-as`](functions/extension.md) - Returns true if a value is castable
- [`xdmp:collection-delete`](functions/general.md) - Deletes from the database every document in a collection
- [`xdmp:collection-locks`](functions/documents,-directories,-properties,-and-locks.md) - Returns locks of documents in a collection
- [`xdmp:collection-properties`](functions/documents,-directories,-properties,-and-locks.md) - Returns a sequence of properties documents, one for each document in the
  specified collection(s) that has a corresponding properties document
- [`xdmp:crypt`](functions/extension.md) - Calculates the password hash for the given password and salt
- [`xdmp:crypt2`](functions/extension.md) - Calculates the password hash for the given plain-text password
- [`xdmp:decode-from-NCName`](functions/extension.md) - Invertible function that decodes characters an NCName produced by
   xdmp:encode-for-NCName
- [`xdmp:describe`](functions/xquery-context.md) - Returns a string representing the
  description of a given item sequence
- [`xdmp:diacritic-less`](functions/search.md) - Returns the specified string, converting all of the characters with diacritics
to characters without diacritics
- [`xdmp:directory`](functions/documents,-directories,-properties,-and-locks.md) - Returns the documents from the database in a directory
- [`xdmp:directory-create`](functions/general.md) - Creates a directory
- [`xdmp:directory-delete`](functions/general.md) - Deletes a directory and all of its child and descendant documents and
  directories from the database
- [`xdmp:directory-locks`](functions/documents,-directories,-properties,-and-locks.md) - Returns locks of documents in a directory
- [`xdmp:directory-properties`](functions/documents,-directories,-properties,-and-locks.md) - Returns a sequence of properties documents, one for each document in
  the specified directory that has a corresponding properties document
- [`xdmp:document-add-collections`](functions/general.md) - Adds the named document to the given collections
- [`xdmp:document-add-permissions`](functions/general.md) - Adds the given permissions to the given document or directory
- [`xdmp:document-add-properties`](functions/general.md) - Adds a sequence of properties to the properties of a document
- [`xdmp:document-assign`](functions/general.md) - Assign a document URI to a forest index,
  using the same algorithm as xdmp:document-insert
- [`xdmp:document-delete`](functions/general.md) - Deletes a document from the database
- [`xdmp:document-get-collections`](functions/extension.md) - Returns the collections to which a given document belongs
- [`xdmp:document-get-metadata`](functions/extension.md) - Returns the metadata value of a given document
- [`xdmp:document-get-metadata-value`](functions/extension.md) - Returns the metadata value of a given document
- [`xdmp:document-get-properties`](functions/documents,-directories,-properties,-and-locks.md) - Returns the property values for a document's property
- [`xdmp:document-get-quality`](functions/documents,-directories,-properties,-and-locks.md) - Returns the quality of the specified document if the document exists
- [`xdmp:document-insert`](functions/general.md) - Inserts a new document into the database if a document with the
  specified URI does not already exist
- [`xdmp:document-load`](functions/general.md) - Inserts a new document with the specified URI
- [`xdmp:document-locks`](functions/documents,-directories,-properties,-and-locks.md) - Returns the locks for one or more documents or directories
- [`xdmp:document-partition-assign`](functions/general.md) - Assign a document to a partition number,
  using the partition queries in the database or in the second argument
- [`xdmp:document-properties`](functions/documents,-directories,-properties,-and-locks.md) - Returns a sequence of properties documents, one for each of the specified
  documents that has a corresponding properties document
- [`xdmp:document-put-metadata`](functions/general.md) - Adds metadata to the document
- [`xdmp:document-remove-collections`](functions/general.md) - Removes the named document from the given collections
- [`xdmp:document-remove-metadata`](functions/general.md) - Removes metadata with certain keys from a document
- [`xdmp:document-remove-permissions`](functions/general.md) - Removes the given permissions from the named document or directory
- [`xdmp:document-remove-properties`](functions/general.md) - Removes a sequence of properties from the properties of a document
- [`xdmp:document-set-collections`](functions/general.md) - Sets the named document to belong to the given collections, replacing any
  previously set collections on the named document
- [`xdmp:document-set-metadata`](functions/general.md) - Sets metadata to the document
- [`xdmp:document-set-permissions`](functions/general.md) - Sets the permissions on the named document (or directory) to the given
  permissions, replacing any permissions previously set on the
  document (or directory)
- [`xdmp:document-set-properties`](functions/general.md) - Sets the properties of a document to the given sequence of elements,
  replacing any properties that already exist on the document
- [`xdmp:document-set-property`](functions/general.md) - Sets a property on a document
- [`xdmp:document-set-quality`](functions/general.md) - Sets the quality of the document with the given URI
- [`xdmp:eager`](functions/extension.md) - Returns the value of its argument, evaluated eagerly
- [`xdmp:element-content-type`](functions/extension.md) - Returns the schema-defined content-type of an element
  ("empty", "simple", "element-only", or "mixed")
- [`xdmp:email`](functions/extension.md) - Send an email in an XQuery program
- [`xdmp:encode-for-NCName`](functions/extension.md) - Invertible function that escapes characters required to be part of
   an NCName
- [`xdmp:encoding-language-detect`](functions/extension.md) - Analyzes binary, text, or XML data and suggests possible pairs of encoding
  and language, with a confidence score for each pair
- [`xdmp:estimate`](functions/search.md) - Returns the number of fragments selected by an expression
- [`xdmp:eval`](functions/xquery-context.md) - Returns the result of evaluating a string as an XQuery module
- [`xdmp:eval-in`](functions/xquery-context.md) - [DEPRECATED: use xdmp:eval with the
  database option instead] Returns the result of evaluating a string as
  an XQuery module in a given database
- [`xdmp:exists`](functions/search.md) - Returns true if any fragment is selected by an expression, false if no
  fragments are selected
- [`xdmp:from-json`](functions/json.md) - Atomizes a JSON node, returning a JSON value
- [`xdmp:from-json-string`](functions/json.md) - Parses a string as JSON, returning an item sequence
- [`xdmp:function`](functions/function-values.md) - Returns a function value as an xdmp:function 
   type
- [`xdmp:function-module`](functions/function-values.md) - Returns the module location (if any) that the 
  xdmp:function
  
  value refers to
- [`xdmp:function-name`](functions/function-values.md) - Returns the QName of the function(s) that the 
  xdmp:function
  
  refers to
- [`xdmp:function-parameter-name`](functions/function-values.md) - Returns the name of the parameter at the designated (1-based) position from the given function's signature
- [`xdmp:function-parameter-type`](functions/function-values.md) - Returns the type of the parameter at the designated (1-based) position from the given function's signature
- [`xdmp:function-return-type`](functions/function-values.md) - Returns the return type from the given function's signature
- [`xdmp:function-signature`](functions/function-values.md) - Returns the signature of the function that the argument refers to
- [`xdmp:functions`](functions/function-values.md) - Returns all in-scope functions
- [`xdmp:hash32`](functions/extension.md) - Returns the 32-bit hash of a string
- [`xdmp:hash64`](functions/extension.md) - Returns the 64-bit hash of a string
- [`xdmp:hex-to-integer`](functions/extension.md) - Parses a hexadecimal string, returning an integer
- [`xdmp:hmac-md5`](functions/extension.md) - Calculates the Hash-based Message Authentication Code (HMAC) using the md5 hash function of the given secret key and message arguments
- [`xdmp:hmac-sha1`](functions/extension.md) - Calculates the Hash-based Message Authentication Code (HMAC) using the SHA1 hash function of the given secret key and message arguments
- [`xdmp:hmac-sha256`](functions/extension.md) - Calculates the Hash-based Message Authentication Code (HMAC) using the SHA256 hash function of the given secret key and message arguments
- [`xdmp:hmac-sha512`](functions/extension.md) - Calculates the Hash-based Message Authentication Code (HMAC) using the SHA512   hash function of the given secret key and message arguments
- [`xdmp:initcap`](functions/extension.md) - Returns the string where the first letter of each token has been uppercased
- [`xdmp:integer-to-binary`](functions/extension.md) - Returns a binary representation of an integer
- [`xdmp:integer-to-hex`](functions/extension.md) - Returns a hexadecimal representation of an integer
- [`xdmp:integer-to-octal`](functions/extension.md) - Returns an octal representation of an integer
- [`xdmp:invoke`](functions/xquery-context.md) - Returns the result of evaluating an XQuery or Server-Side JavaScript
  module at the given path
- [`xdmp:invoke-function`](functions/xquery-context.md) - Returns the result of evaluating 
  an XQuery
  function value
- [`xdmp:invoke-in`](functions/xquery-context.md) - [DEPRECATED: use xdmp:invoke with the
  database option instead] Returns the result of evaluating a module
  at the given path
- [`xdmp:is-whitespace-node`](functions/extension.md) - Returns true if the node is a text node containing only whitespace
- [`xdmp:javascript-eval`](functions/xquery-context.md) - Returns the result of evaluating a string as a JavaScript module
- [`xdmp:json-validate`](functions/json.md) - Validate a JSON node against a JSON Schema
- [`xdmp:json-validate-node`](functions/json.md) - Validate a JSON node against a JSON Schema
- [`xdmp:json-validate-report`](functions/json.md) - Validate a JSON node against a JSON Schema and return an error report
- [`xdmp:json-validate-report-node`](functions/json.md) - Validate a JSON node against a JSON Schema and return an error report
- [`xdmp:key-from-QName`](functions/extension.md) - Construct a context-independent string from a QName
- [`xdmp:lazy`](functions/extension.md) - Returns the value of its argument, evaluated lazily
- [`xdmp:ldap-lookup`](functions/extension.md) - Returns an ldap entry
- [`xdmp:ldap-search`](functions/extension.md) - Returns ldap search result
- [`xdmp:load`](functions/general.md) - [DEPRECATED: use xdmp:document-load
  
  instead]
  Inserts a new document from the XML file at $path if a document
  with the specified URI does not already exist
- [`xdmp:lock-acquire`](functions/general.md) - Acquire a lock on a document or directory for an extended amount of time
- [`xdmp:lock-for-update`](functions/general.md) - Acquires an intent exclusive transaction lock on a URI
- [`xdmp:lock-release`](functions/general.md) - Unlock a document or directory
- [`xdmp:lshift64`](functions/extension.md) - Left-shift a 64-bit integer value
- [`xdmp:md5`](functions/extension.md) - Calculates the md5 hash of the given argument
- [`xdmp:merge`](functions/general.md) - Starts merging the forests of the database, subject to specified
  options
- [`xdmp:merging`](functions/general.md) - Returns the forest IDs of any currently merging database forests
- [`xdmp:mul64`](functions/extension.md) - Multiply two 64-bit integer values, discarding overflow
- [`xdmp:multipart-decode`](functions/extension.md) - Extract the parts from a multipart encoding
- [`xdmp:multipart-encode`](functions/extension.md) - Create a multipart encoding of the specified node
- [`xdmp:node-collections`](functions/xquery-context.md) - Returns any collections for the node's document in the database
- [`xdmp:node-database`](functions/xquery-context.md) - Returns the database id where the parameter is stored
- [`xdmp:node-delete`](functions/general.md) - Deletes a node from the database
- [`xdmp:node-get-info`](functions/xquery-context.md) - This function returns information about the node i
- [`xdmp:node-insert-after`](functions/general.md) - Adds an immediately following sibling to a node
- [`xdmp:node-insert-before`](functions/general.md) - Adds an immediately preceding sibling to a node
- [`xdmp:node-insert-child`](functions/general.md) - Adds a new last child to a node
- [`xdmp:node-kind`](functions/extension.md) - Returns an xs:string
  representing the node's kind: either
  "document", "element", "attribute", "text", "namespace",
  "processing-instruction", "binary", or "comment"
- [`xdmp:node-metadata`](functions/extension.md) - Returns the metadata value of a given node
- [`xdmp:node-metadata-value`](functions/extension.md) - Returns the metadata value of a node for a particular key
- [`xdmp:node-replace`](functions/general.md) - Replaces a node
- [`xdmp:node-uri`](functions/xquery-context.md) - Returns the document-uri property of the parameter or its ancestor
- [`xdmp:not64`](functions/extension.md) - NOT a 64-bit integer value
- [`xdmp:octal-to-integer`](functions/extension.md) - Parses an octal string, returning an integer
- [`xdmp:or64`](functions/extension.md) - OR two 64-bit integer values
- [`xdmp:parse-dateTime`](functions/extension.md) - Parses a string containing date, time or dateTime using the supplied
   picture argument and returns a dateTime value
- [`xdmp:parse-yymmdd`](functions/extension.md) - Parses a string containing date, time or dateTime using the supplied
   picture argument and returns a dateTime value
- [`xdmp:partition-forests`](functions/general.md) - Returns a sequence of forest IDs with the specified partition number
- [`xdmp:path`](functions/xquery-context.md) - Returns a string whose value corresponds to the
  path of the node
- [`xdmp:plan`](functions/search.md) - Returns an XML element recording information about how the given
  expression will be processed by the index
- [`xdmp:plannable`](functions/search.md) - Returns a boolean showing whether the given expression is suitable to use
  with xdmp:plan
- [`xdmp:position`](functions/extension.md) - Returns an integer value representing the starting position of a
  string within the search string
- [`xdmp:query-partitions`](functions/general.md) - This function returns the partition numbers of the partitions that the specified 
query will be searched on
- [`xdmp:quote`](functions/xml.md) - Returns the unevaluated serialized representation
  of the input parameter as a string
- [`xdmp:random`](functions/extension.md) - Returns a random unsigned integer between 0 and a number up to 64 bits long
- [`xdmp:range-partition-forests`](functions/general.md) - Given a value, the function returns a list of forests that have ranges the
  value falls into
- [`xdmp:request-timestamp`](functions/search.md) - Returns the system timestamp for this request if the request is a query
  statement
- [`xdmp:resolve-uri`](functions/extension.md) - Resolves a relative URI against an absolute URI
- [`xdmp:rshift64`](functions/extension.md) - Right-shift a 64-bit integer value
- [`xdmp:save`](functions/general.md) - Serializes a node as text and saves it to a file
- [`xdmp:set`](functions/xquery-context.md) - Set the value of a variable to the specified expression
- [`xdmp:set-response-output-method`](functions/extension.md) - Sets the serialization method
- [`xdmp:sha1`](functions/extension.md) - Calculates the SHA1 hash of the given argument
- [`xdmp:sha256`](functions/extension.md) - Calculates the SHA256 hash of the given argument
- [`xdmp:sha384`](functions/extension.md) - Calculates the SHA384 hash of the given argument
- [`xdmp:sha512`](functions/extension.md) - Calculates the SHA512 hash of the given argument
- [`xdmp:sleep`](functions/extension.md) - Delays for a specific amount of time
- [`xdmp:spawn`](functions/xquery-context.md) - Place the specified module on the task queue for evaluation
- [`xdmp:spawn-function`](functions/xquery-context.md) - Place the specified function value on the task queue for evaluation
- [`xdmp:spawn-in`](functions/xquery-context.md) - [DEPRECATED: use xdmp:spawn with the
  database option instead] Place the specified module on the task
  queue for evaluation
- [`xdmp:sql`](functions/xquery-context.md) - Executes an ad hoc SQL query
- [`xdmp:sql-plan`](functions/xquery-context.md) - Returns a node representing the query plan of the given SQL SELECT query
- [`xdmp:step64`](functions/extension.md) - Combines an initial hash with a subsequent hash
- [`xdmp:strftime`](functions/extension.md) - Formats a dateTime value using POSIX strftime
- [`xdmp:timestamp-to-wallclock`](functions/extension.md) - Converts a 64 bit timestamp value to an xs:dateTime
- [`xdmp:to-json`](functions/json.md) - Constructs a JSON document
- [`xdmp:to-json-string`](functions/json.md) - Returns a string representing a JSON
  serialization of a given item sequence
- [`xdmp:type`](functions/extension.md) - Returns the name of the simple type of the atomic value argument as an 
  xs:QName
- [`xdmp:unpath`](functions/xquery-context.md) - Evaluate a string as an XPath and return the corresponding node(s)
- [`xdmp:unquote`](functions/xml.md) - Parses a string as XML, returning one or more document nodes
- [`xdmp:user-last-login`](functions/extension.md) - Returns the last-login node for the current user
- [`xdmp:value`](functions/xquery-context.md) - Evaluate an expression in the context of the current evaluating statement
- [`xdmp:wallclock-to-timestamp`](functions/extension.md) - Converts an xs:dateTime to a 64 bit timestamp value
- [`xdmp:with-namespaces`](functions/xquery-context.md) - Evaluates the expression in the context of a specific set of namespace
  bindings
- [`xdmp:xor64`](functions/extension.md) - XOR two 64-bit integer values
- [`xdmp:xquery-version`](functions/xquery-context.md) - Returns the XQuery language version of the calling module
- [`xdmp:xslt-eval`](functions/xquery-context.md) - Executes an XSLT stylesheet against a node
- [`xdmp:xslt-invoke`](functions/xquery-context.md) - Executes an XSLT stylesheet against a node

## Related Skills

- `marklogic-search-and-query`
- `marklogic-xquery-stdlib`
- `marklogic-development`
