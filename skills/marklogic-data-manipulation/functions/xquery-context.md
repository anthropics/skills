# Xquery Context

24 functions in this category.

## xdmp:describe

Returns a string representing the
  description of a given item sequence.  If you take
  the output of this function and evaluate it as an XQuery program, 
  it returns the item(s) input to the function.

### Signature

```xquery
xdmp:describe(
  $item as item()*,
  $max-sequence-length as xs:unsignedInt??,
  $max-item-length as xs:unsignedInt??
) as xs:string
```

### Parameters

**`$item`**
The item sequence whose description is returned.

**`$max-sequence-length`** *(optional)*
Represents the maximum number of items per sequence to print.
    The default is 3.

**`$max-item-length`** *(optional)*
Represents the maximum number of characters per item to print.
    The default is 64.  The minimum is 8.

### Returns

`xs:string`

### Usage Notes

If you specify an item that is in a database, this function
  returns the path to the item (or to the items if you specify multiple items).
  If the item or items are constructed in XQuery, then it prints out the item,
  truncating the characters in each item according to the
  max-item-length parameter.

### Examples

#### Example 1

```xquery
xdmp:describe(current-date())

=> xs:date("2007-01-15-08:00")
```

#### Example 2

```xquery
let $x := <mynode>Some text here.</mynode>
  return
  xdmp:describe($x)

  => <mynode>Some text here.</mynode>
```

#### Example 3

```xquery
(:  assume /mydoc.xml is an XML document with
      the following content:
      <mynode>Some text here.</mynode> :)
  xdmp:describe(doc("/mydoc.xml")/mynode)

  => doc("/mydoc.xml")/mynode
```

---

## xdmp:eval

Returns the result of evaluating a string as an XQuery module.
  To evaluate JavaScript, see 
  xdmp:javascript-eval.

### Signature

```xquery
xdmp:eval(
  $xquery as xs:string,
  $vars as item()* | map:map?,
  $options as (element()|map:map)??
) as item()*
```

### Parameters

**`$xquery`**
A string containing the XQuery code to be evaluated.  If the 
    string contains double quotes ("), surround the string with single 
    quotes (').

**`$vars`** *(optional)*
External variable values to make available to the evaluated code,
    expressed as either a sequence of alternating QName-value pairs, or
    a map:map. If you use a sequence, it must contain 
    alternating variable QNames and values. e.g.  
    (xs:QName("var1"), "val1", xs:Qname("var2"), "val2").
    If you use a map, then each key is a string representing the Clark 
    notation of the variable QName ("{namespaceURI}localname"), and its
    value is the corresponding variable value. You can use
    xdmp:key-from-QName
    to generate the Clark notation to use as a key.

**`$options`** *(optional)*
Options with which to customize this operation. 
     You can specify options as either an options XML element
     in the namespace "xdmp:eval", or as a map:map. The
     option names below are XML localnames. When using a map, replace any
     hyphens in an option name with camel casing. For example, "an-option"
     becomes "anOption" when used as a map:map entry key.
     This function supports the following options:
    
	  
    database
    The id of the content database. You can use functions such
      as xdmp:database
       to get a database ID.
      See the Usage Notes for more details. Use of this option to specify
      a database other than the context database requires additional
      privileges. For details, see Required Privileges, below.
    modules
    The ID of the modules database to use for resolving module imports.
      If you do not specify a modules option, this operation
      uses the current modules database. Use a value of 0 to
      specify using the file system to resolve module imports. Use of this
      option to specify a modules database other than the one configured
      for the App Server requires additional privileges. For details, see
      Required Privileges, below.
    root
    The root path for modules. If you do not explicitly specify a
      root option, the current root is used. Use of this
      option to specify a root path other than the one configured for the
      App Server requires additional privileges. For details, see
      Required Privileges, below.
    timestamp
    The system timestamp to use for this evaluation. If you omit this
      option, the most recent timestamp is used. You may only specify a
      timestamp for a query statement, not for an update statement. Use a
      value of zero to specify the current system timestamp (the value that
      would be returned by xdmp:request-timestamp
	  ). 
	  For more details see
 Understanding Point-In-Time Queries in the  Application Developer's Guide.
      Use of this option requires additional privileges. For 
      details, see Required Privileges, below.
    
    ignore-amps
    
    
     Whether or not to evaluate the code without using any Amps from the caller.
     Allowed values: true, false (default). If this option is set to
     true, the code is evaluated without using Amps from the 
     caller.  For more details, see
 Temporarily Increasing Privileges with Amps in the Security Guide.
     You cannot use this option with dbg:eval.
    
    isolation
    Specify the transaction isolation for this operation. Allowed values:
     same-statement, different-transaction (default).
     When set to same-statement, the evaluation occurs in the
     same transaction in which this function is called. When set to
     different-transaction, the evaluation occurs in a separate
     transaction from the one in which this function is called. If you use
     same-statement isolation in a query (read-only) statement
     and the eval'd code attempts an update, MarkLogic throws the exception
     XDMP-UPDATEFUNCTIONFROMQUERY. For more details, see
 Isolation Option to xdmp:eval/invoke in the  Application Developer's Guide.
    
    commit
    
     The commit mode for the transaction in which the code is evaluated.
     Allowed values: auto (default), explicit.
     In auto mode, a transaction is committed for every statement.
     In explicit mode, the transaction must be explicitely
     committed or rolled back. For more details, see
 Commit Mode in the  Application Developer's Guide.
    
    update
    
     Specify the transaction type in which to evaluate this code, or let
     MarkLogic determine the transaction type. Allowed values:
     "true", "false", "auto" (default).
     For more details, see
 Transaction Type Overview in the  Application Developer's Guide.
    
    static-check
    
    
     Whether or not to only perform a static analysis of the code, without
     executing it. Allowed values: true, false
     (default).
    
    prevent-deadlocks
    
    
     Whether or not to disallow update requests from an update transaction.
     Allowed values: true, false (default). This
     option only has an effect when you set the isolation option 
     to different-transaction since there is no possibility of
     deadlock if the isolation is same-statement. When you set
     this option to true in an update request calling another
     update request, MarkLogic throws the exception
     XDMP-PREVENTDEADLOCKS. Setting this option to 
     true prevents deadlocks from occurring when evaluating
     or invoking an update transaction from another update transaction.
     For more details, see
 Preventing Deadlocks in the  Application Developer's Guide.
    
    default-xquery-version
    
    The default XQuery language version to use for the query, if the query
     does not contain an explicit version declaration.  If this option is not
     provided, then MarkLogic uses the default XQuery version for the 
     App Server that called this function. The version may vary from module
     to module if a query consists of modules written in multiple XQuery
     versions. If may also var from run to run if the App Server default
     changes across runs.
     Allowable values for this option are "0.9-ml", "1.0-ml", "1.0", and
     the special value "app-server". The first three are XQuery language
     versions. The last indicates that the default XQuery language
     version set on this App Server should be used.  This is useful if code
     written in an older XQuery version needs to call this function
     on strings that may have been passed as parameters, but should be
     interpreted in the App Server default language version.  A module
     can discover its own XQuery language version with
     xdmp:xquery-version()
     .
    
    user-id
    
    The ID of the user under which this operation should be performed.
     If you do not set this option, the operation is performed as the
     current user. Use of htis option requires additional privileges. For
     details, see Required Privileges, below. NOTE: This is a very 
     privileged operation since it enables a user to evaluate requests as 
     any other user. For an example, see the 
     fourth example below.
    default-collation
    
    Specifies the collation to use for this operation if a collation
     is not explicitly specified, such as in the XQuery prolog or in a
     function call that allows you to specify a collation. For more
     details, see
 Encodings and Collations in the Search Developer's Guide.
    
    default-coordinate-system
    
    Specifies the geospatial coordinate system to use for this operation, 
     if a coordinate system is not explicitly specified, such as in the XQuery prolog
     or in a function call that allows you to specify a coordinate system.
     For more details, see 
 Controlling Coordinate System and Precision in the Search Developer's Guide and 
 Supported Coordinate Systems in the Search Developer's Guide.
    
    transaction-mode
    
    [DEPRECATED: Use the update and commit
     options instead.] Explicitly set the transaction mode for this context. 
     Allowed values: auto (default), query, 
     update-auto-commit, update. For details, see
 Transaction Mode in the  Application Developer's Guide.
     For simple updates to be implicitly committed, specify a transaction 
     mode of update-auto-commit. A transaction mode of
     update creates a new multi-statement update 
     transaction and requires an explicit commit in the code.
     Within a session there can be only one active multi-statement 
     transaction at a time. If a new multi-statement transaction is 
     specified nested inside a multi-statement transaction, MarkLogic throws
     the exception XDMP-NESTEDMULTI. If a new multi-statement 
     transaction is specified after another has been concurrently created 
     in the same session by another request, MarkLogic throws the exception
     XDMP-SESSIONTXN and retries the current request.
     An xdmp:transaction-mode XQuery prolog 
     option in the evaluated code overrides any transaction mode specified
     with this option.

### Returns

`item()*`

### Usage Notes

To get the database ID for options that require one, such as
  the database or modules options, you can use
  functions such as the following. Use the function appropriate to the
  database you want to reference.
      
	xdmp:database
	xdmp:modules-database
	xdmp:security-database
	xdmp:schema-database

### Examples

#### Example 1

```xquery
xdmp:eval("1+1")
=> 2
```

#### Example 2

```xquery
xquery version "1.0-ml";
declare namespace my='http://mycompany.com/test';

let $s :=
      "xquery version '1.0-ml';
       declare namespace my='http://mycompany.com/test';
       declare variable $my:x as xs:string external;
       declare variable $my:y as xs:string external := 'goodbye';
       concat('hello ', $my:x, ' ', $my:y)"
return
    (: evaluate the query string $s using the variables
       supplied as the second parameter to xdmp:eval :)
    xdmp:eval($s, (xs:QName("my:x"), "world"))

=> hello world goodbye
   (the "goodbye" comes from the default value specified for $my:y)
```

#### Example 3

```xquery
xdmp:eval("doc('/docs/mydoc.xml')",  (),
                  <options xmlns="xdmp:eval">
		    <database>{xdmp:database("otherdb")}</database>
		  </options>)
=> The '/docs/mydoc.xml' document from the
   otherdb database.
```

#### Example 4

```xquery
xdmp:eval('xdmp:get-current-user()', (),
 <options xmlns="xdmp:eval">
  <user-id>{xdmp:user("someuser")}</user-id>
 </options>)
(:
  returns "someuser", assuming "someuser" exists in the
  security database and the user running the eval request has the
  xdmp:login privilege.
:)
```

---

## xdmp:eval-in

[DEPRECATED: use xdmp:eval with the
  database option instead] Returns the result of evaluating a string as
  an XQuery module in a given database.

### Signature

```xquery
xdmp:eval-in(
  $xquery as xs:string,
  $ID as xs:unsignedLong*,
  $vars as item()*?,
  $modules as xs:unsignedLong??,
  $root as xs:string??
) as item()*
```

### Parameters

**`$xquery`**
The XQuery string to be evaluated.  If the XQuery string contains
    double quotes ("), surround the string with single quotes (').

**`$ID`**
The database ID, from xdmp:database("db_name"),
    xdmp:security-database(),
    or xdmp:schema-database().

**`$vars`** *(optional)*
The external variable values for this evaluation.
    This must be a sequence of even length, alternating QNames and items.
    Each QName and item pair specify a variable name and value.

**`$modules`** *(optional)*
The modules database for processing module imports.
    The empty sequence specifies the current modules database.

**`$root`** *(optional)*
The root path for modules.  
    The empty sequence specifies the current root.

### Returns

`item()*`

---

## xdmp:invoke

Returns the result of evaluating an XQuery or Server-Side JavaScript
  module at the given path.

### Signature

```xquery
xdmp:invoke(
  $path as xs:string,
  $vars as item()* | map:map?,
  $options as (element()|map:map)??
) as item()*
```

### Parameters

**`$path`**
The path of an XQuery or JavaScript module to be executed, as a string.
    The path is resolved against the root of the App Server evaluating the 
    query, the Modules directory, or relative to the calling module. 
    For details on module path resolution, see
 Importing XQuery Modules, XSLT Stylesheets, and Resolving Paths in the  Application Developer's Guide.
    The module is considered to be JavaScript if the module path ends with 
    a file extension configured for the MIME type
    application/vnd.marklogic-javascript in MarkLogic's
    Mimetypes configuration. Otherwise, it is assumed to be XQuery.

**`$vars`** *(optional)*
External variable values to make available to the evaluated code,
    expressed as either a sequence of alternating QName-value pairs, or
    a map:map. If you use a sequence, it must contain 
    alternating variable QNames and values. e.g.  
    (xs:QName("var1"), "val1", xs:Qname("var2"), "val2").
    If you use a map, then each key is a string representing the Clark 
    notation of the variable QName ("{namespaceURI}localname"), and its
    value is the corresponding variable value. You can use
    xdmp:key-from-QName
    to generate the Clark notation to use as a key.

**`$options`** *(optional)*
Options with which to customize this operation. 
     You can specify options as either an options XML element
     in the namespace "xdmp:eval", or as a map:map. The
     option names below are XML localnames. When using a map, replace any
     hyphens in an option name with camel casing. For example, "an-option"
     becomes "anOption" when used as a map:map entry key.
     This function supports the following options:
    
	  
    database
    The id of the content database. You can use functions such
      as xdmp:database
       to get a database ID.
      See the Usage Notes for more details. Use of this option may require
      additional privileges. For details, see Required Privileges, below.
    modules
    The ID of the modules database to use for resolving module imports.
      If you do not specify a modules option, this operation
      uses the current modules database. Use a value of 0 to
      specify using the file system to resolve module imports. Use of this
      option may required additional privileges. For details, see Required
      Privileges, below.
    root
    The root path for modules. If you do not explicitly specify a
      root option, the current root is used. Use of this
      option may require additional privileges. For details, see Required
      Privileges, below.
     
    timestamp
    The system timestamp to use for this evaluation. If you omit this
      option, the most recent timestamp is used. You may only specify a
      timestamp for a query statement, not for an update statement. Use a
      value of zero to specify the current system timestamp (the value that
      would be returned by xdmp:request-timestamp
	  ). 
	  For more details see
 Understanding Point-In-Time Queries in the  Application Developer's Guide.
      Use of this option requires an additional privilege. For details, see 
      Required Privileges, below.
    
    ignore-amps
    
    
     Whether or not to invoke the module without using any Amps from the caller.
     Allowed values: true, false (default). If this option is set to
     true, the code is evaluated without using Amps from the
     caller. For more details, see
 Temporarily Increasing Privileges with Amps in the Security Guide.
     This option is not usable with
     dbg:invoke.
    
    isolation
    Specify the transaction isolation for this operation. Allowed values:
     same-statement, different-transaction (default).
     When set to same-statement, the evaluation occurs in the
     same transaction in which this function is called. When set to
     different-transaction, the evaluation occurs in a separate
     transaction from the one in which this function is called. If you use
     same-statement isolation in a query (read-only) statement
     and the eval'd code attempts an update, MarkLogic throws the exception
     XDMP-UPDATEFUNCTIONFROMQUERY. For more details, see
 Isolation Option to xdmp:eval/invoke in the  Application Developer's Guide.
    
    commit
    
     The commit mode for the transaction in which the code is evaluated.
     Allowed values: auto (default), explicit.
     In auto mode, a transaction is committed for every statement.
     In explicit mode, the transaction must be explicitely
     committed or rolled back. For more details, see
 Commit Mode in the  Application Developer's Guide.
    
    update
    
     Specify the transaction type in which to evaluate this code, or let
     MarkLogic determine the transaction type. Allowed values:
     "true", "false", "auto" (default).
     For more details, see
 Transaction Type Overview in the  Application Developer's Guide.
    
    static-check
    
    
     Whether or not to only perform a static analysis of the code, without
     executing it. Allowed values: true, false
     (default).
    
    prevent-deadlocks
    
    
     Whether or not to disallow update requests from an update transaction.
     Allowed values: true, false (default). This
     option only has an effect when you set the isolation option 
     to different-transaction since there is no possibility of
     deadlock if the isolation is same-statement. When you set
     this option to true in an update request calling another
     update request, MarkLogic throws the exception
     XDMP-PREVENTDEADLOCKS. Setting this option to 
     true prevents deadlocks from occurring when evaluating
     or invoking an update transaction from another update transaction.
     For more details, see
 Preventing Deadlocks in the  Application Developer's Guide.
    
    default-xquery-version
    
    The default XQuery language version to use for the query, if the query
     does not contain an explicit version declaration.  If this option is not
     provided, then MarkLogic uses the default XQuery version for the 
     App Server that the invocation occurs on. Note that this may be different 
     than the XQuery version of the module calling invoke.
     Allowable values for this option are "0.9-ml", "1.0-ml", "1.0", and
     the special value "app-server". The first three are XQuery language
     versions. The last indicates that the default XQuery language
     version set on this App Server should be used.  This is useful if code
     written in an older XQuery version needs to call this function
     on strings that may have been passed as parameters, but should be
     interpreted in the App Server default language version.  A module
     can discover its own XQuery language version with
     xdmp:xquery-version()
     .
    
    user-id
    
    The ID of the user under which this operation should be performed.
     If you do not set this option, the operation is performed as the
     current user. Use of this option requires additional privileges. For
     details, see Required Privileges, below. NOTE: This is a very privileged 
     operation since it enables a user to evaluate requests as any other 
     user. 
    default-collation
    
    Specifies the collation to use for this operation if a collation
     is not explicitly specified, such as in the XQuery prolog or in a
     function call that allows you to specify a collation. For more
     details, see
 Encodings and Collations in the Search Developer's Guide.
    
    default-coordinate-system
    
    Specifies the geospatial coordinate system to use for this operation, 
     if a coordinate system is not explicitly specified, such as in the XQuery prolog
     or in a function call that allows you to specify a coordinate system.
     For more details, see 
 Controlling Coordinate System and Precision in the Search Developer's Guide and 
 Supported Coordinate Systems in the Search Developer's Guide.
    
    transaction-mode
    
    [DEPRECATED: Use the update and commit
     options instead.] Explicitly set the transaction mode for this context. 
     Allowed values: auto (default), query, 
     update-auto-commit, update. For details, see
 Transaction Mode in the  Application Developer's Guide.
     For simple updates to be implicitly committed, specify a transaction 
     mode of update-auto-commit. A transaction mode of
     update creates a new multi-statement update 
     transaction and requires an explicit commit in the code.
     Within a session there can be only one active multi-statement 
     transaction at a time. If a new multi-statement transaction is 
     specified nested inside a multi-statement transaction, MarkLogic throws
     the exception XDMP-NESTEDMULTI. If a new multi-statement 
     transaction is specified after another has been concurrently created 
     in the same session by another request, MarkLogic throws the exception
     XDMP-SESSIONTXN and retries the current request.
     An xdmp:transaction-mode XQuery prolog 
     option in the evaluated code overrides any transaction mode specified
     with this option.

### Returns

`item()*`

### Usage Notes

To get the database ID for options that require one, such as
  the database or modules options, you can use
  functions such as the following. Use the function appropriate to the
  database you want to reference.
      
	xdmp:database
	xdmp:modules-database
	xdmp:security-database
	xdmp:schema-database

### Examples

#### Example 1

```xquery
xdmp:invoke("http://example.com/modules/foo.xqy")
  => 2
```

#### Example 2

```xquery
This example invokes a module using external variables.
 
  Assume you have a module in the modules database with a URI
  "http://example.com/application/module.xqy" containing the
  following code:

  xquery version "1.0-ml";
  declare namespace my="my-namespace-uri";
  declare variable $my:var as xs:string external;
  xdmp:log($my:var)

  Then you can call this module using xdmp:invoke as follows:

  xquery version "1.0-ml";
  declare namespace my="my-namespace-uri";
  xdmp:invoke("module.xqy",
        (xs:QName("my:var"), "log this"),
        <options xmlns="xdmp:eval">
          <modules>{xdmp:modules-database()}</modules>
	  <root>http://example.com/application/</root>
         </options>)
	
  => Invokes an XQuery module from the modules database
     with the URI http://example.com/application/module.xqy.
     The invoked module will then be executed, logging the
     message sent in the external variable to the log.
```

---

## xdmp:invoke-function

Returns the result of evaluating 
  an XQuery
  function value.

### Signature

```xquery
xdmp:invoke-function(
  $func as function(),
  $options as (element()|map:map)??
) as item()*
```

### Parameters

**`$func`**
A zero arity function value to execute.

**`$options`** *(optional)*
Options controlling the evaluation. The default is no options. For
   detailed option information, see
   xdmp:invoke 
    
   for detailed option information. NOTE: Some options require additional
   privileges. For details, see the Required Privileges section of
   xdmp:invoke.
   When expressed as an element, the options node 
    must be in the xdmp:eval namespace.

### Returns

`item()*`

### Usage Notes

The XQuery version of this function (xdmp:invoke-function)
  can only be used to invoke XQuery functions. The Server-Side JavaScript
  version of this function (xdmp.invokeFunction) can only
  be used to invoke JavaScript functions.

### Examples

#### Example 1

```xquery
xquery version "1.0-ml";
  let $content := <doc/>
  return
    xdmp:invoke-function(
      function() { xdmp:document-insert("doc",$content) },
      <options xmlns="xdmp:eval">
        <update>auto</update>
        <commit>auto</commit>
      </options>)
	
  (: Invokes the function value in an update-auto-commit transaction. :)
```

#### Example 2

```xquery
xquery version "1.0-ml";
  let $content := <doc/>
  return
    xdmp:invoke-function(
      function() { xdmp:document-insert("doc",$content), xdmp:commit() },
      <options xmlns="xdmp:eval">
        <update>true</update>
        <commit>explicit</commit>
      </options>)
	
  (: Invokes the function value in a multi-statement update transaction. :)
```

---

## xdmp:invoke-in

[DEPRECATED: use xdmp:invoke with the
  database option instead] Returns the result of evaluating a module
  at the given path.

### Signature

```xquery
xdmp:invoke-in(
  $uri as xs:string,
  $ID as xs:unsignedLong*,
  $vars as item()*?,
  $modules as xs:unsignedLong??,
  $root as xs:string??
) as item()*
```

### Parameters

**`$uri`**
The path of the module to be executed.  The path is resolved against
    the root of the App Server evaluating the query.  The path must
    resolve to a main module (not a library module).

**`$ID`**
The database ID, from xdmp:database("db_name"),
    xdmp:security-database(),
    or xdmp:schema-database().

**`$vars`** *(optional)*
The external variable values for this evaluation.
    This must be a sequence of even length, alternating QNames and items.
    Each QName and item pair specify a variable name and value.

**`$modules`** *(optional)*
The modules database containing the module to invoke.
    The empty sequence specifies the current modules database.

**`$root`** *(optional)*
The root path for modules.  
    The empty sequence specifies the current root.

### Returns

`item()*`

---

## xdmp:javascript-eval

Returns the result of evaluating a string as a JavaScript module.
  To evaluate XQuery, see xdmp:eval.

### Signature

```xquery
xdmp:javascript-eval(
  $javascript as xs:string,
  $vars as item()* | map:map?,
  $options as (node()? | map:map)??
) as item()*
```

### Parameters

**`$javascript`**
A string containing JavaScript code to be evaluated. 
    The JavaScript string to be evaluated. If the JavaScript string contains
    single quotes ('), surround the string with double quotes (").

**`$vars`** *(optional)*
External variable values to make available to the evaluated code,
    expressed as either a sequence of alternating variable name-value pairs, 
    or a map:map. If you use a sequence, it must contain 
    alternating variable names and values. e.g.  
    ("var1", "val1", "var2", "val2").
    If you use a map, then each map entry has a key corresponding to the
    variable name and a value corresponding to the variable value.

**`$options`** *(optional)*
Options with which to customize this operation. 
     You can specify options as either an options XML element
     in the namespace "xdmp:eval", or as a map:map. The
     option names below are XML localnames. When using a map, replace any
     hyphens in an option name with camel casing. For example, "an-option"
     becomes "anOption" when used as a map:map entry key.
     This function supports the following options:
    
    database
    The id of the content database. You can use functions such
      as xdmp:database to get a database ID. Using this option
      may require additional privileges. For details, see Required
      Privileges, below.
    modules
    The ID of the modules database to use for resolving module imports.
      If you do not specify a modules option, this operation
      uses the current modules database. Use a value of 0 to
      specify using the file system to resolve module imports. Using this
      option may require additional privileges. For details, see Required
      Privileges, below.
    root
    The root path for modules. If you do not explicitly specify a
      root option, the current root is used. Use of this
      option may require additional privileges. For details, see 
      Required Privileges, below.
     
    timestamp
    The system timestamp to use for this evaluation. If you omit this
      option, the most recent timestamp is used. You may only specify a
      timestamp for a query statement, not for an update statement. Use a
      value of zero to specify the current system timestamp (the value that
      would be returned by xdmp:request-timestamp). Use of this
	  option requires the privilege 
	  http://marklogic.com/xdmp/privileges/xdmp-timestamp 
	  For more details see
 Understanding Point-In-Time Queries in the  Application Developer's Guide.
    
    ignore-amps
    
     Whether or not to evaluate the code without using any Amps from the caller.
     Allowed values: true, false (default). If this option is set to
     true, the code is evaluated without using Amps from the caller.
     For more details, see
 Temporarily Increasing Privileges with Amps in the Security Guide.
     This option is not usable with dbg:eval.
    
    isolation
    Specify the transaction isolation for this operation. Allowed values:
     same-statement, different-transaction (default).
     When set to same-statement, the evaluation occurs in the
     same transaction in which this function is called. When set to
     different-transaction, the evaluation occurs in a separate
     transaction from the one in which this function is called. If you use
     same-statement isolation in a query (read-only) statement
     and the eval'd code attempts an update, MarkLogic throws the exception
     XDMP-UPDATEFUNCTIONFROMQUERY. For more details, see
 Isolation Option to xdmp:eval/invoke in the  Application Developer's Guide.
    
    commit
    
     The commit mode for the transaction in which the code is evaluated.
     Allowed values: auto (default), explicit.
     In auto mode, a transaction is committed for every statement.
     In explicit mode, the transaction must be explicitely
     committed or rolled back. For more details, see
 Commit Mode in the  Application Developer's Guide.
    
    update
    
     Specify the transaction type in which to evaluate this code, or let
     MarkLogic determine the transaction type. Allowed values:
     "true", "false", "auto" (default).
     For more details, see
 Transaction Type Overview in the  Application Developer's Guide.
    
    static-check
    
     Whether or not to only perform a static analysis of the code, without
     executing it. Allowed values: true, false
     (default).
    
    prevent-deadlocks
    
     Whether or not to disallow update requests from an update transaction.
     Allowed values: true, false (default). This
     option only has an effect when you set the isolation option 
     to different-transaction since there is no possibility of
     deadlock if the isolation is same-statement. When you set
     this option to true in an update request calling another
     update request, MarkLogic throws the exception
     XDMP-PREVENTDEADLOCKS. Setting this option to 
     true prevents deadlocks from occurring when evaluating
     or invoking an update transaction from another update transaction.
     For more details, see
 Preventing Deadlocks in the  Application Developer's Guide.
    
    user-id
    The ID of the user under which this operation should be performed.
     If you do not set this option, the operation is performed as the
     current user. Use of this option requires additional privileges. For
     details, see Required Privileges, below. NOTE: This is a very 
     privileged operation since it enables a user to
     to evaluate requests as any other user. 
    default-collation
    Specifies the collation to use for this operation if a collation
     is not explicitly specified, such as in the XQuery prolog or in a
     function call that allows you to specify a collation. For more
     details, see
 Encodings and Collations in the Search Developer's Guide.
    
    default-coordinate-system
    Specifies the geospatial coordinate system to use for this operation, 
     if a coordinate system is not explicitly specified, such as in the XQuery prolog
     or in a function call that allows you to specify a coordinate system.
     For more details, see 
 Controlling Coordinate System and Precision in the Search Developer's Guide and 
 Supported Coordinate Systems in the Search Developer's Guide.
    
    transaction-mode
    [DEPRECATED: Use the update and commit
     options instead.] Explicitly set the transaction mode for this context. 
     Allowed values: auto (default), query, 
     update-auto-commit, update. For details, see
 Transaction Mode in the  Application Developer's Guide.
     For simple updates to be implicitly committed, specify a transaction 
     mode of update-auto-commit. A transaction mode of
     update creates a new multi-statement update 
     transaction and requires an explicit commit in the code.
     Within a session there can be only one active multi-statement 
     transaction at a time. If a new multi-statement transaction is 
     specified nested inside a multi-statement transaction, MarkLogic throws
     the exception XDMP-NESTEDMULTI. If a new multi-statement 
     transaction is specified after another has been concurrently created 
     in the same session by another request, MarkLogic throws the exception
     XDMP-SESSIONTXN and retries the current request.
     An xdmp:transaction-mode XQuery prolog 
     option in the evaluated code overrides any transaction mode specified
     with this option.

### Returns

`item()*`

### Usage Notes

To get the database ID for options that require one, such as
  the database or modules options, you can use
  functions such as the following. Use the function appropriate to the
  database you want to reference.
      
	xdmp:database
	xdmp:modules-database
	xdmp:security-database
	xdmp:schema-database

---

## xdmp:node-collections

Returns any collections for the node's document in the database. If
  the specified node does not come from a document in a database, then
  xdmp:node-collections
   
  returns an empty sequence.

### Signature

```xquery
xdmp:node-collections(
  $node as node()
) as xs:string*
```

### Parameters

**`$node`**
The node whose collections are to be returned.

### Returns

`xs:string*`

### Examples

```xquery
xdmp:node-collections(doc("http://marklogic.com/document"))
=> ("http://acme.com/this-collection", "http://acme.com/that-collection")
```

---

## xdmp:node-database

Returns the database id where the parameter is stored. If
  the specified node does not come from a document in a database, then
  xdmp:node-database
   
  returns an empty list.

### Signature

```xquery
xdmp:node-database(
  $node as node()
) as xs:unsignedLong?
```

### Parameters

**`$node`**
The node whose database is returned.

### Returns

`xs:unsignedLong?`

### Examples

```xquery
xdmp:node-database(doc("http://marklogic.com/document"))
=> 18384173956586417397
```

---

## xdmp:node-get-info

This function returns information about the node i.e. the node-repid, uniquekey, compressed tree size and database of an input node.
  Database is true if the node is read from the database, false otherwise.

### Signature

```xquery
xdmp:node-get-info(
  $node as node(),
  $output-kind as xs:string*?
) as 
```

### Parameters

**`$node`**
The node whose noderepid/uniqueKey is returned.

**`$output-kind`** *(optional)*
The output kind can be either:
    
    "xml"Return the result as a sequence of xml elements.
    "json"Return the result as a sequence of json elements
    "map"Return the result as a sequence of map values
    defaultThe default is "json".

### Examples

```xquery
xdmp:node-database(doc("http://marklogic.com/document"),"xml")
==>
<xdmp:node-info xmlns:xdmp="http://marklogic.com/xdmp">
  <compressed-tree-size>78</compressed-tree-size>
  <node-rep-id>0</node-rep-id>
  <node-unique-key>152469828419602699</node-unique-key>
  <database-node>1</database-node>
</xdmp:node-info>
```

---

## xdmp:node-uri

Returns the document-uri property of the parameter or its ancestor.

### Signature

```xquery
xdmp:node-uri(
  $node as node()
) as xs:string?
```

### Parameters

**`$node`**
The node whose URI is returned.

### Returns

`xs:string?`

### Examples

```xquery
xdmp:node-uri(doc("/some/document.xml"))
=> "/some/document.xml"
```

---

## xdmp:path

Returns a string whose value corresponds to the
  path of the node.

### Signature

```xquery
xdmp:path(
  $node as node(),
  $include-document as xs:boolean??
) as xs:string
```

### Parameters

**`$node`**
The node whose path is returned.

**`$include-document`** *(optional)*
If true, then the path is presented with a leading doc(..)/..,
    otherwise the path is presented as /...

### Returns

`xs:string`

### Examples

```xquery
let $arg := <a><b><c>ccc</c></b>
                <b>bbb</b></a>
return xdmp:path($arg/b[1]/c)

  => "/a/b[1]/c"
```

---

## xdmp:set

Set the value of a variable to the specified expression. The
  xdmp:set command allows you to introduce changes to the
  state (side effects) of a query by changing the value of a variable to
  something other than what it is bound to.

### Signature

```xquery
xdmp:set(
  $variable as item()*,
  $expr as item()*
) as empty-sequence()
```

### Parameters

**`$variable`**
A variable to set.

**`$expr`**
A value to set the variable.

### Returns

`empty-sequence()`

### Usage Notes

When a variable is bound to a sequence in a for loop, and when
  that variable is changed by xdmp:set in the return
  clause, the change only affects the value for one iteration of the
  for loop at a time; when the next value is sent to the return
  clause, it is set to the next value in the sequence specified in the
  for clause.  The value changes only after the
  xdmp:set call is made.

---

## xdmp:spawn

Place the specified module on the task queue for evaluation.

### Signature

```xquery
xdmp:spawn(
  $path as xs:string,
  $vars as item()* | map:map?,
  $options as (element()|map:map)??
) as item()*
```

### Parameters

**`$path`**
The path of an XQuery or JavaScript module to be executed, as a string.
    The path is resolved against the root of the App Server evaluating the 
    query, the Modules directory, or relative to the calling module. 
    For details on module path resolution, see
 Importing XQuery Modules, XSLT Stylesheets, and Resolving Paths in the  Application Developer's Guide.
    The module is considered to be JavaScript if the module path ends with 
    a file extension configured for the MIME type
    application/vnd.marklogic-javascript in MarkLogic's
    Mimetypes configuration. Otherwise, it is assumed to be XQuery.

**`$vars`** *(optional)*
External variable values to make available to the evaluated code,
    expressed as either a sequence of alternating QName-value pairs, or
    a map:map. If you use a sequence, it must contain 
    alternating variable QNames and values. e.g.  
    (xs:QName("var1"), "val1", xs:Qname("var2"), "val2").
    If you use a map, then each key is a string representing the Clark 
    notation of the variable QName ("{namespaceURI}localname"), and its
    value is the corresponding variable value. You can use
    xdmp:key-from-QName
    to generate the Clark notation to use as a key.

**`$options`** *(optional)*
Options with which to customize this operation. 
     You can specify options as either an options XML element
     in the namespace "xdmp:eval", or as a map:map. The
     option names below are XML localnames. When using a map, replace any
     hyphens in an option name with camel casing. For example, "an-option"
     becomes "anOption" when used as a map:map entry key.
     This function supports the following options:
    
	  
    database
    The id of the content database. You can use functions such
      as xdmp:database
       to get a database ID.
      See the Usage Notes for more details. Using this option to specify
      a database other than the context database requires additional
      privileges. For details, see Required Privileges, below.
    modules
    The ID of the modules database to use for resolving module imports.
      If you do not specify a modules option, this operation
      uses the current modules database. Use a value of 0 to
      specify using the file system to resolve module imports. Using this
      option may require additional privileges. For details, see Required
      Privileges, below.
    root
    The root path for modules. If you do not explicitly specify a
      root option, the current root is used. Use of this
      option may require additional privileges. For details, see Required
      Privileges, below.
     
    timestamp
    The system timestamp to use for this evaluation. If you omit this
      option, the most recent timestamp is used. You may only specify a
      timestamp for a query statement, not for an update statement. Use a
      value of zero to specify the current system timestamp (the value that
      would be returned by xdmp:request-timestamp
	  ). 
	  For more details see
 Understanding Point-In-Time Queries in the  Application Developer's Guide.
      Use of this option requires additional privileges. For details, see 
      Required Privileges, below.
    
    isolation
    Specify the transaction isolation for this operation. Allowed values:
     same-statement, different-transaction (default).
     When set to same-statement, the evaluation occurs in the
     same transaction in which this function is called. When set to
     different-transaction, the evaluation occurs in a separate
     transaction from the one in which this function is called. If you use
     same-statement isolation in a query (read-only) statement
     and the eval'd code attempts an update, MarkLogic throws the exception
     XDMP-UPDATEFUNCTIONFROMQUERY. For more details, see
 Isolation Option to xdmp:eval/invoke in the  Application Developer's Guide.
    
    commit
    
     The commit mode for the transaction in which the code is evaluated.
     Allowed values: auto (default), explicit.
     In auto mode, a transaction is committed for every statement.
     In explicit mode, the transaction must be explicitely
     committed or rolled back. For more details, see
 Commit Mode in the  Application Developer's Guide.
    
    update
    
     Specify the transaction type in which to evaluate this code, or let
     MarkLogic determine the transaction type. Allowed values:
     "true", "false", "auto" (default).
     For more details, see
 Transaction Type Overview in the  Application Developer's Guide.
    
    static-check
    
    
     Whether or not to only perform a static analysis of the code, without
     executing it. Allowed values: true, false
     (default).
    
    default-xquery-version
    
    The default XQuery language version to use for the query, if the query
     does not contain an explicit version declaration. By default, MarkLogic
     uses the default XQuery version of the App Server that called 
     spawn. The Task Server has no default XQuery version, so
     the version is passed as part of the task request.
     Allowable values for this option are "0.9-ml", "1.0-ml", "1.0", and
     the special value "app-server". The first three are XQuery language
     versions. The last indicates that the default XQuery language
     version set on this App Server should be used.  This is useful if code
     written in an older XQuery version needs to call this function
     on strings that may have been passed as parameters, but should be
     interpreted in the App Server default language version.  A module
     may discover its own XQuery language version with
     xdmp:xquery-version()
     .
    
    time-limit
    
    Override the default time limit with this time limit for this
     operation. Specify the value in seconds. You can set the value up
     to the maximum-time-limit value for the App Server in which the
     request is evaluated or to a lower value than the default time limit.
    user-id
    
    The ID of the user under which this operation should be performed.
     If you do not set this option, the operation is performed as the
     current user. Use of this option requires additional privileges. For
     details, see Required Privileges, below. NOTE: This is a very 
     privileged operation since it enables a user to evaluate requests as 
     any other user.
    default-collation
    
    Specifies the collation to use for this operation if a collation
     is not explicitly specified, such as in the XQuery prolog or in a
     function call that allows you to specify a collation. For more
     details, see
 Encodings and Collations in the Search Developer's Guide.
    
    default-coordinate-system
    
    Specifies the geospatial coordinate system to use for this operation, 
     if a coordinate system is not explicitly specified, such as in the XQuery prolog
     or in a function call that allows you to specify a coordinate system.
     For more details, see 
 Controlling Coordinate System and Precision in the Search Developer's Guide and 
 Supported Coordinate Systems in the Search Developer's Guide.
    
    priority
    Specify the priority of the spawned task. Allowed values:
     normal (default), higher.
    result
    Return a value future for the result of the spawned task.
     This value future can bound be to a variable without waiting so
     that work can proceed concurrently with the spawned task. 
     When the calling request uses the value future in any operation,
     it will automatically wait for the spawned task to complete and it will
     use the result. For an example, see
     The second example.
    transaction-mode
    
    [DEPRECATED: Use the update and commit
     options instead.] Explicitly set the transaction mode for this context. 
     Allowed values: auto (default), query, 
     update-auto-commit, update. For details, see
 Transaction Mode in the  Application Developer's Guide.
     For simple updates to be implicitly committed, specify a transaction 
     mode of update-auto-commit. A transaction mode of
     update creates a new multi-statement update 
     transaction and requires an explicit commit in the code.
     Within a session there can be only one active multi-statement 
     transaction at a time. If a new multi-statement transaction is 
     specified nested inside a multi-statement transaction, MarkLogic throws
     the exception XDMP-NESTEDMULTI. If a new multi-statement 
     transaction is specified after another has been concurrently created 
     in the same session by another request, MarkLogic throws the exception
     XDMP-SESSIONTXN and retries the current request.
     An xdmp:transaction-mode XQuery prolog 
     option in the evaluated code overrides any transaction mode specified
     with this option.

### Returns

`item()*`

### Usage Notes

This function places the specified module
   in the task queue to be processed. The module will be evaluated when the
   task server has the available resources to process it. Tasks are
   processed in the order in which they are added to the queue. 
      Once this function is called, it cannot be rolled back,
   even if the transaction from which it is called does not complete.
   Therefore, use care calling this function from an update transaction.
   Once a module is spawned, its evaluation is asynchronous
   of the transaction in which spawn is called.
   Consequently, if you call this function from a module, and if
   the module ends up retrying (for example, if a deadlock is detected), 
   then the entire module is re-evaluated and this function is therefore
   called again. 
      To get the database ID for options that require one, such as
   the database or modules options, you can use
   functions such as the following. Use the function appropriate to the
   database you want to reference.
      
	xdmp:database
	xdmp:modules-database
	xdmp:security-database
	xdmp:schema-database

### Examples

#### Example 1

```xquery
xdmp:spawn("module.xqy", (),
        <options xmlns="xdmp:eval">
          <modules>{xdmp:modules-database()}</modules>
	  <root>http://example.com/application/</root>
         </options>)
	
  => Puts the module from the modules database with the
     URI http://example.com/application/module.xqy
     in the task server queue.
```

#### Example 2

```xquery
(:
   This example uses the <result> option to use the results of a
   spawned task in the query
:)  
let $x := xdmp:spawn("/oneplusone.xqy", (),
  <options xmlns="xdmp:eval">
    <result>{fn:true()}</result>
  </options>
)
return
($x + 2)
(:
   if /oneplusone.xqy has the following body:

   1 + 1

   then this query returns 4
:)
```

---

## xdmp:spawn-function

Place the specified function value on the task queue for evaluation.

### Signature

```xquery
xdmp:spawn-function(
  $function as function() as item()*,
  $options as (element()|map:map)??
) as item()*
```

### Parameters

**`$function`**
A zero arity function value to execute.

**`$options`** *(optional)*
The options node. The default value is (). The node must be in the
  xdmp:eval namespace.  For detailed options information, see
  xdmp:spawn.

### Returns

`item()*`

### Usage Notes

The xdmp:spawn-function function places the specified 
    function value in the task queue to be processed. The function will be 
    executed when the task server has the available resources to process it. 
    The tasks are processed in the order in which they are added to the 
    queue. 
      Once xdmp:spawn-function is called, it cannot be rolled 
    back, even if the transaction from which it is called does not complete.
    Therefore, use care calling xdmp:spawn-function from an update
    transaction.  Once a module is spawned, its evaluation is asynchronous
    of the transaction in which xdmp:spawn-function was called. 
    Consequently, if you call xdmp:spawn-function from a module,
    and if the module ends up retrying (for example, if a deadlock is detected), 
    then the entire module is re-evaluated and the xdmp:spawn-function
    call is therefore called again. For details on how transactions work in MarkLogic
    Server, see "Understanding Transactions in MarkLogic Server" in the 
    Application Developer's Guide.

---

## xdmp:spawn-in

[DEPRECATED: use xdmp:spawn with the
  database option instead] Place the specified module on the task
  queue for evaluation.  It will be evaluated in the given database.

### Signature

```xquery
xdmp:spawn-in(
  $path as xs:string,
  $ID as xs:unsignedLong,
  $vars as item()*?,
  $modules as xs:unsignedLong??,
  $root as xs:string??
) as empty-sequence()
```

### Parameters

**`$path`**
The path, relative to the specified root, of the module to be executed.

**`$ID`**
The database ID, from xdmp:database("db_name"),
    xdmp:security-database(),
    or xdmp:schema-database().

**`$vars`** *(optional)*
The external variable values for this evaluation.
    This must be a sequence of even length, alternating QNames and items.
    Each QName and item pair specify a variable name and value.

**`$modules`** *(optional)*
The modules database that contains the module to invoke.
    The empty sequence specifies the current modules database.

**`$root`** *(optional)*
The root path for modules.
    The empty sequence specifies the current root.

### Returns

`empty-sequence()`

### Usage Notes

The xdmp:spawn-in function places the specified XQuery
    module in the task queue to be processed. The module will be evaluated
    when the task server has the available resources to process it. The tasks
    are processed in the order in which they are added to the queue.

---

## xdmp:sql

Executes an ad hoc SQL query.  This function is for testing
  your SQL views when data modeling.

### Signature

```xquery
xdmp:sql(
  $sql as xs:string,
  $options as xs:string*?,
  $bindings as map:map??,
  $query as cts:query??
) as item()*
```

### Parameters

**`$sql`**
The SQL statement to be executed.

**`$options`** *(optional)*
Options as a sequence of string values. Available options are:
    
    "array"Return the result as a sequence of array
    values (json:array).
    "format"Return the results as formatted strings.
    "map"Return the result as a sequence of map values,
    where the key is the column name.
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

**`$bindings`** *(optional)*
A map containing initial values for variables from the query, or the
    empty sequence if no query variables are to be initially bound. This
    is a way to parameterize the query.
    
    One of the benefits of parameterizing the query is that you can reuse the same
    query multiple times with different values plugged in.  In this case, the SQL engine
    will not have to analyze the query each time it runs and instead use the cached
    query plan for increased speed.  You should always using bindings, rather than
    string concatenation, to parameterize queries.
    
   
    As shown in the example below, bindings are passed in as a map:map
    of values. The keys for the map are either a string representation of the ordinal
    number of the ? dynamic parameter in the SQL query, or the name of a named SQL
    parameter using the :name, @name, or $name
    syntax. Ordinal parameters can also be expressed as ?NNNwhere
    NNN is an explicit ordinal number rather than an implicitly asigned
    one as with ? by itself.

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

`item()*`

### Usage Notes

Only one of the "map" and "array" options may be specified. If neither
is specified, the default is "array". If the "format" option is specified, the
output will be formatted, regardless of whether "array" or "map" was selected.

      The first tuple returned will always be one consisting of the column names.

### Examples

#### Example 1

```xquery
xdmp:sql("select title,author from books limit 4", "format")
==>
| title| author|
| The C++ Programming Language| Bjarne Stroustrup|
| Modern Information Retrieval| Ricardo Baeza-Yates|
| Modern Information Retrieval| Berthier Ribeiro-Neto|
| Unicode Demystified| Richard Gillam|
```

#### Example 2

```xquery
xdmp:to-json(xdmp:sql("select title,author from books limit 4", "array"))
==>
[["title", "author"],
 ["The C++ Programming Language", "Bjarne Stroustrup"],
 ["Modern Information Retrieval", "Ricardo Baeza-Yates"],
 ["Modern Information Retrieval", "Berthier Ribeiro-Neto"],
 ["Unicode Demystified", "Richard Gillam"]
]
```

#### Example 3

```xquery
for $row in xdmp:sql("select title,author from books limit 4")
return fn:concat("Title=",$row[1],"; Author=",$row[2])
==>
Title=title, Author=author
Title=The C++ Programming Language; Author=Bjarne Stroustrup
Title=Modern Information Retrieval; Author=Ricardo Baeza-Yates
Title=Modern Information Retrieval; Author=Berthier Ribeiro-Neto
Title=Unicode Demystified; Author=Richard Gillam
```

#### Example 4

```xquery
let $bindings := map:new(map:entry("num", 1))
return (
xdmp:sql("SELECT * FROM main.employees
          where EmployeeID > @num
          order by LastName, EmployeeID",("format","locking=read-write"), $bindings))
==>
| main.employees.EmployeeID| main.employees.FirstName| main.employees.LastName| main.employees.Position|
| 4| Debbie| Goodall| Senior Widget Researcher|
| 4| Debbie| Goodall| Senior Widget Researcher|
| 2| Jane| Lead| Manager of Widget Research|
| 2| Jane| Lead| Manager of Widget Research|
| 3| Steve| Manager| Senior Technical Lead|
| 3| Steve| Manager| Senior Technical Lead|
```

---

## xdmp:sql-plan

Returns a node representing the query plan of the given SQL SELECT query.
  Raises an error if the SQL query is not a SELECT query.

### Signature

```xquery
xdmp:sql-plan(
  $sql as xs:string,
  $options as xs:string*?
) as element()
```

### Parameters

**`$sql`**
The SQL query to be executed.

**`$options`** *(optional)*
Options as a sequence of string values. Available options are:
    
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
xdmp:sql-plan("select  customername, customersince
from customers
where year(customersince)  >  2000
and year(customersince)  <  2013")
```

---

## xdmp:unpath

Evaluate a string as an XPath and return the corresponding node(s).
  Any value that is the result of xdmp:path is a
  valid input to xdmp:unpath.  Any invalid inputs
  throw an XDMP-UNPATH exception. To evaluate non-XPath
  expressions, use xdmp:value.

### Signature

```xquery
xdmp:unpath(
  $expr as xs:string,
  $map as map:map??,
  $context as node()??
) as item()*
```

### Parameters

**`$expr`**
The XPath expression string to evaluate. The XPath expression must be
   of the form returned by xdmp:path.

**`$map`** *(optional)*
A map of namespace bindings. The keys should be namespace prefixes and the
  values should be namespace URIs. These namespace bindings will be added to
  the in-scope namespace bindings in the evaluation of the path.

**`$context`** *(optional)*
Bind the context node to this value during evaluation of the expression.

### Returns

`item()*`

---

## xdmp:value

Evaluate an expression in the context of the current evaluating statement.
  This differs from xdmp:eval in that xdmp:value
  preserves all of the context from the calling query, so you do not
  need to re-define namespaces, variables, and so on.  Although the expression
  retains the context from the calling query, it is evaluated in its own
  transaction with same-statement isolation.

### Signature

```xquery
xdmp:value(
  $expr as xs:string,
  $map as map:map??,
  $context as item()??
) as item()*
```

### Parameters

**`$expr`**
The string representing an expression to evaluate.

**`$map`** *(optional)*
A map of namespace bindings. The keys should be namespace prefixes and the
  values should be namespace URIs. These namespace bindings will be added to
  the in-scope namespace bindings in the evaluation of the expression.

**`$context`** *(optional)*
Bind the context item to this value during evaluation of the expression.

### Returns

`item()*`

### Usage Notes

You can only evaluate expressions with xdmp:value; no
  prolog definitions (namespace declarations, function definitions,
  module imports, and so on) are allowed.
      If the expression references something not in the context of either
  the calling query or the value expression, then an error is thrown. For
  example, the following throws an undefined variable exception:
      xdmp:value("$y")
      It is not recommended to use this with an inline function as static analysis of
  inline functions do not look inside strings passed to xdmp:value.

---

## xdmp:with-namespaces

Evaluates the expression in the context of a specific set of namespace
  bindings.

### Signature

```xquery
xdmp:with-namespaces(
  $nsbindings as (xs:string*|map:map),
  $expr as item()*
) as item()*
```

### Parameters

**`$nsbindings`**
A set of namespace prefix bindings, expressed as either a sequence of
  alternating (prefix,uri) pairs, or a map:map where the
  keys are prefixes and the values are namespace URIs. If the prefix is 
  the empty string, the following URI becomes the default namespace of the 
  resulting item(s).

**`$expr`**
An expression to evaluate in the context of the given namespace bindings.

### Returns

`item()*`

### Examples

#### Example 1

```xquery
(: Using a sequence of prefix-URI pairs to define the bindings :)
let $version := "1.2" return
xdmp:with-namespaces(("p", fn:concat("http://marklogic.com/p/",$version)),
   <p:bar/>
)

(: Returns: <p:bar xmlns:p="http://marklogic.com/p/1.2"/> :)
```

#### Example 2

```xquery
(: Using a map:map to define the bindings :)
let $version := "1.2" 
return xdmp:with-namespaces(
  map:map() => map:with("p", fn:concat("http://marklogic.com/p/",$version)),
  <p:bar/>
)

(: Returns: <p:bar xmlns:p="http://marklogic.com/p/1.2"/> :)
```

#### Example 3

```xquery
(: Defining a default namespace :)
xdmp:with-namespaces(
   ('', 'x'),
   <test>
      <test1>hello</test1>
   </test>
=>
<test xmlns="x">
  <test1>hello</test1>
</test>
```

---

## xdmp:xquery-version

Returns the XQuery language version of the calling module.
  Currently supported XQuery versions are:
  
	"0.9-ml": The legacy MarkLogic XQuery version.  This was the only
    XQuery version available on MarkLogic Server 3.2 and
    earlier.  It is based on the May 2003 XQuery Draft Recommendation,
    with MarkLogic extensions
    
	"1.0-ml": XQuery version 1.0, with MarkLogic extensions.  This
    is the preferred version of XQuery beginning with release 4.0.
    
	"1.0": Strict XQuery version 1.0.  This XQuery version complies
    as closely as possible with the published XQuery 1.0 specification.

### Returns

`xs:string`

---

## xdmp:xslt-eval

Executes an XSLT stylesheet against a node.

### Signature

```xquery
xdmp:xslt-eval(
  $stylesheet as node(),
  $input as node()??,
  $params as map:map??,
  $options as (element()|map:map)??
) as document-node()*
```

### Parameters

**`$stylesheet`**
The XSLT stylesheet to be executed.

**`$input`** *(optional)*
The context node to which the stylesheet is applied.

**`$params`** *(optional)*
The stylesheet parameter values for this evaluation.
    Each key in the map is a string representing the name of the parameter
    in Clark notation: "{namespaceURI}localname". The function
    xdmp:key-from-QName 
    
    is a convenient way to generate these keys.
    Each entry in the map is the value of the corresponding parameter.

**`$options`** *(optional)*
The options node. The default value is (). The node 
  must be in the xdmp:eval namespace.  See the
  xdmp:eval section for a list of 
  options.
  
  Additional options include:
  
  <mode>
  
  A QName  
  specifying the
  initial stylesheet mode to use (the <xsl:template> with the
  specified mode attribute).
  <template>
  
  A QName  
  specifying the name of the initial template to apply.

### Returns

`document-node()*`

### Usage Notes

When creating the xsl:stylesheet element that is the
  stylesheet parameter to 
  xdmp:xslt-eval
  ,
  keep in mind that it has to first be parsed by XQuery before
  it is evaluated as a stylesheet.  Therefore, any characters in the stylesheet
  that require escaping in XQuery must be escaped, otherwise you get an error
  in the XQuery.  For example, if the stylesheet has any curly braces
  ( { or } ), you must escape the curly braces (with curly braces). For
  an example, see the example below.
      When running an XSLT stylesheet in MarkLogic, you pass in a node on
  which the stylesheet operates.  Many stylesheets are written
  to expect the initial node to be a document
  node.  In other XSLT processors, the node you pass to the stylesheet is
  typically read in from the filesystem and is always treated as a document
  node.  In MarkLogic, you often get the node to pass to the stylesheet as
  the result of a query or a search, and the node  is not necessarily a
  document node.  Therefore, if your stylesheet expects
  the context node to be a document node, make sure to pass in a document
  node and not an element node.  If you pass in an element node to a
  stylesheet that has default template rules to expect a document node,
  then you might miss the processing on the element you passed
  in (because the stylesheet might expect the child node to be the root
  element of the XML document, but if you passed in the root element instead of
  its parent document node, then the child nodes would be the children of the
  root element, causing the root element to miss its default processing).

### Examples

#### Example 1

```xquery
let $foo-to-bar :=
  <xsl:stylesheet xmlns:xsl="http://www.w3.org/1999/XSL/Transform"
                  version="2.0">
    <xsl:template match="foo">
      <bar>
        <xsl:apply-templates select="node()"/>
      </bar>
    </xsl:template>
    <xsl:template match="@*|node()">
      <xsl:copy>
        <xsl:apply-templates select="@*|node()"/>
      </xsl:copy>
    </xsl:template>
  </xsl:stylesheet>
return xdmp:xslt-eval($foo-to-bar,
  <stuff>
   <one/>
   <foo/>
   <two/>
   <foo><blah>42</blah></foo>
   <bar>22</bar>
  </stuff>)/element()
```

#### Example 2

```xquery
xquery version "1.0-ml" ;

(: Hello World example for xslt:eval, with a parameter :)

let $params := map:map()
let $_put := map:put(
                    $params,
                    xdmp:key-from-QName(fn:QName("foo", "pName")),
                    "Stephen")
let $_put := map:put(
                    $params,
                    xdmp:key-from-QName(fn:QName("bar", "bName")),
                    "Ron")
let $_put := map:put(
                    $params,
                    "cName",
                    "Dave")
return
  xdmp:xslt-eval(
    <xsl:stylesheet xmlns:xsl="http://www.w3.org/1999/XSL/Transform"
      xmlns:f="foo" xmlns:b="bar"
      version="2.0">
    <xsl:param name="f:pName"/>
    <xsl:param name="b:bName"/>
    <xsl:param name="cName"/>
    <xsl:param name="greeting" select="'Hi there '"/>
    <xsl:template match="/">
       <output>
         <xsl:copy-of select="node"/>
         <greeting><xsl:value-of select="$greeting"/></greeting>
         <param><xsl:value-of select="$f:pName"/></param>
         <param><xsl:value-of select="$b:bName"/></param>
         <param><xsl:value-of select="$cName"/></param>
       </output>
    </xsl:template>
  </xsl:stylesheet>,
  document { <node>Hello World</node> },
  $params)
=>
<?xml version="1.0" encoding="ASCII"?>
<output xmlns:f="foo" xmlns:b="bar">
  <node>Hello World</node>
  <greeting>Hi there </greeting>
  <param>Stephen</param>
  <param>Ron</param>
  <param>Dave</param>
</output>
```

#### Example 3

```xquery
xquery version "1.0-ml" ;

(: example that passes in a QName for a mode :)
xdmp:xslt-eval(
    <xsl:stylesheet xmlns:xsl="http://www.w3.org/1999/XSL/Transform"
     version="2.0">
    <xsl:template match="/">
       <output>this has no mode</output>
    </xsl:template>
    <xsl:template match="/" mode="my-mode">
      <debug>this has a mode</debug>
    </xsl:template>
  </xsl:stylesheet>,
  document { <node>Hello World</node> },
  (),
  <options xmlns="xdmp:eval">
    <mode>{fn:QName("", "my-mode")}</mode>
  </options>)
=>
<?xml version="1.0" encoding="ASCII"?>
<debug>this has a mode</debug>
```

#### Example 4

```xquery
xquery version "1.0-ml";

(:
  Note the esacped curly braces ( {{ and }} on the name attribute
  of xsl:element), as the stylesheet must first be parsed by XQuery
  before it is evaluated as a stylesheet.  If you do not escape
  the curly braces, the query throws the XQuery exception:
  [1.0-ml] XDMP-CONTEXT: (err:XPDY0002) Expression depends on the context
           where none is defined
  That is because, without the escaped braces, XQuery tries to evaluate
  the expression in the name attribute, but there is no context for it.
:)
xdmp:xslt-eval(
<xsl:stylesheet xmlns:xsl="http://www.w3.org/1999/XSL/Transform"
      version="2.0">
    <xsl:template match="foo">
     <xsl:element name="{{name(.)}}"/>
    </xsl:template>
</xsl:stylesheet>
,
document{ <foo>something goes here</foo>} )
=>
<?xml version="1.0" encoding="ASCII"?>
<foo/>
```

---

## xdmp:xslt-invoke

Executes an XSLT stylesheet against a node.

### Signature

```xquery
xdmp:xslt-invoke(
  $path as xs:string,
  $input as node()??,
  $params as map:map??,
  $options as (element()|map:map)??
) as document-node()*
```

### Parameters

**`$path`**
The path of the stylesheet to be executed.  The path is resolved against
    the root of the App Server evaluating the query, the Modules directory,
    or relative to the calling module.  For details on resolving paths,
    see "Importing XQuery Modules and Resolving Paths" in the
    Application Developer's Guide.

**`$input`** *(optional)*
The context node to which the stylesheet is applied.

**`$params`** *(optional)*
The stylesheet parameter values for this evaluation.
    Each key in the map is a string representing the name of the parameter
    in Clark notation: "{namespaceURI}localname". The function
    xdmp:key-from-QName 
    
    is a convenient way to generate these keys.
    Each entry in the map is the value of the corresponding parameter.

**`$options`** *(optional)*
The options node. The default value is (). The node 
  must be in the
  xdmp:eval namespace.  See the
  xdmp:eval section for a list of 
  options.
  
  Additional options include:
  
  <mode>
  
  A QName  specifying 
  the
  initial stylesheet mode to use (the <xsl:template> with 
  the specified mode attribute).
  <template>
  
  A QName  specifying 
  the name of the initial template to apply.
  <encoding>
  
  Specifies the encoding to use when reading the stylesheet into MarkLogic
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

### Returns

`document-node()*`

### Usage Notes

When running an XSLT stylesheet in MarkLogic, you pass in a node on
  which the stylesheet operates.  Many stylesheets are written
  to expect the initial node to be a document
  node.  In other XSLT processors, the node you pass to the stylesheet is
  typically read in from the filesystem and is always treated as a document
  node.  In MarkLogic, you often get the node to pass to the stylesheet as
  the result of a query or a search, and the node  is not necessarily a
  document node.  Therefore, if your stylesheet expects
  the context node to be a document node, make sure to pass in a document
  node and not an element node.  If you pass in an element node to a
  stylesheet that has default template rules to expect a document node,
  then you might miss the processing on the element you passed
  in (because the stylesheet might expect the child node to be the root
  element of the XML document, but if you passed in the root element instead of
  its parent document node, then the child nodes would be the children of the
  root element, causing the root element to miss its default processing).

### Examples

#### Example 1

```xquery
xquery version "1.0-ml";

(:
this example requires a document named hello.xsl directly
at the App Server root with the following content:

<xsl:stylesheet xmlns:xsl="http://www.w3.org/1999/XSL/Transform"
                  version="2.0">
    <xsl:template match="/">
        <xsl:text>hello</xsl:text>
    </xsl:template>
</xsl:stylesheet>
:)
xdmp:xslt-invoke("/hello.xsl", document{ <foo/> })
=>
hello
```

#### Example 2

```xquery
xquery version "1.0-ml" ;

(: Hello World example for xslt:invoke, with a parameter.
   Assumes a stylesheet named params.xsl directly at
   the App Server root with the following content:
<xsl:stylesheet xmlns:xsl="http://www.w3.org/1999/XSL/Transform"
      xmlns:f="foo" xmlns:b="bar"
      version="2.0">
    <xsl:param name="f:pName"/>
    <xsl:param name="b:bName"/>
    <xsl:param name="cName"/>
    <xsl:param name="greeting" select="'Hi there '"/>
    <xsl:template match="/">
       <output>
         <xsl:copy-of select="node"/>
         <greeting><xsl:value-of select="$greeting"/></greeting>
         <param><xsl:value-of select="$f:pName"/></param>
         <param><xsl:value-of select="$b:bName"/></param>
         <param><xsl:value-of select="$cName"/></param>
       </output>
    </xsl:template>
  </xsl:stylesheet>
:)

let $params := map:map()
let $_put := map:put(
                    $params,
                    xdmp:key-from-QName(fn:QName("foo", "pName")),
                    "Stephen")
let $_put := map:put(
                    $params,
                    xdmp:key-from-QName(fn:QName("bar", "bName")),
                    "Ron")
let $_put := map:put(
                    $params,
                    "cName",
                    "Dave")
return
xdmp:xslt-invoke("/params.xsl",
    document { <node>Hello World</node> },
    $params)
=>
<?xml version="1.0" encoding="ASCII"?>
<output xmlns:f="foo" xmlns:b="bar">
  <node>Hello World</node>
  <greeting>Hi there </greeting>
  <param>Stephen</param>
  <param>Ron</param>
  <param>Dave</param>
</output>
```

---
