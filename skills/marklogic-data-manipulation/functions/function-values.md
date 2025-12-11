# Function Values

10 functions in this category.

## xdmp:annotation

Returns the named annotation from the function.

### Signature

```xquery
xdmp:annotation(
  $function as function(*),
  $name as xs:QName
) as item()*
```

### Parameters

**`$function`**
The function value.

**`$name`**
The annotation name.

### Returns

`item()*`

### Examples

```xquery
xquery version "1.0-ml";

declare %local:annotation(1,2,"foo")
  function local:function() { () };
  
xdmp:annotation(local:function#0,xs:QName("local:annotation"))
=> (1, 2, "foo")
```

---

## xdmp:apply

Applies an xdmp:function with the given parameters.

### Signature

```xquery
xdmp:apply(
  $function as xdmp:function,
  $params-1-to-N as item()*?
) as item()*
```

### Parameters

**`$function`**
The xdmp:function value to be applied.

**`$params-1-to-N`** *(optional)*
The parameters to pass into the specified function value.  Specify one
    parameter for each parameter that the specified function takes, with the
    first parameter corresponding to the first parameter in the specified
    function's signature, the second parameter corresponding to the second,
    and so on.  Omit this parameter if the specified function takes no
    parameters.

### Returns

`item()*`

### Examples

#### Example 1

```xquery
let $function := xdmp:function(xs:QName("fn:empty"))
  return
    xdmp:apply($function, ())

  => true
```

#### Example 2

```xquery
let $function := xdmp:function(xs:QName("fn:concat"))
  return
    xdmp:apply($function, "hello", " world")

  => hello world
```

#### Example 3

```xquery
let $function := xdmp:function(xs:QName("fn:current-date"))
  return
    xdmp:apply($function)

  => 2009-02-14-08:00  (or whatever is the current date)
```

---

## xdmp:function

Returns a function value as an xdmp:function 
   type. 
  You can return an xdmp:function 
   from an expression or
  a function.  You can execute the function referred to by an
  xdmp:function 
  
  by passing the xdmp:function 
    value to
  xdmp:apply. If the module-path ends with a file 
  extension matching the ones configured for 
  application/vnd.marklogic-javascript in your
  MarkLogic Mimetypes configuration, and the function's namespace URI is
  empty, the module is considered to be JavaScript.  In this case, the function
  parameter can be empty.

### Signature

```xquery
xdmp:function(
  $function as xs:QName?,
  $module-path as xs:string??
) as xdmp:function
```

### Parameters

**`$function`**
The function QName, which includes its local name and namespace. If the
    function is not found in the current query context or in the module
    specified in the second parameter, then an exception is thrown when
    the function is used with xdmp:apply.

**`$module-path`** *(optional)*
The optional path to the module where the function specified in the
    first parameter is defined.  If the module-path is not supplied, the
    function QName must be in-scope in the query context.  If the empty
    sequence is supplied, the function behaves as if the parameter is not
    supplied (that is, it uses the in-scope query context).

### Returns

`xdmp:function`

### Examples

#### Example 1

```xquery
xquery version "1.0-ml";

xdmp:function(xs:QName("fn:empty"))
```

#### Example 2

```xquery
xquery version "1.0-ml";

declare namespace admin="http://marklogic.com/xdmp/admin";

xdmp:function(xs:QName("admin:get-configuration"),
      "/MarkLogic/admin.xqy")
```

#### Example 3

```xquery
xquery version "1.0-ml";

let $function := xdmp:function(xs:QName("fn:concat"))
return
   xdmp:apply($function, "hello", " world")

=> hello world
```

---

## xdmp:function-module

Returns the module location (if any) that the 
  xdmp:function
  
  value refers to.

### Signature

```xquery
xdmp:function-module(
  $function as xdmp:function
) as xs:string
```

### Parameters

**`$function`**
The function value.

### Returns

`xs:string`

### Examples

```xquery
xquery version "1.0-ml";
declare namespace admin="http://marklogic.com/xdmp/admin";

let $fn := xdmp:function(xs:QName("admin:get-configuration"),
             "/MarkLogic/admin.xqy")
return
xdmp:function-module($fn)

=> "/MarkLogic/admin.xqy"
```

---

## xdmp:function-name

Returns the QName of the function(s) that the 
  xdmp:function
  
  refers to.

### Signature

```xquery
xdmp:function-name(
  $function as xdmp:function
) as xs:QName?
```

### Parameters

**`$function`**
The xdmp:function
     value.

### Returns

`xs:QName?`

### Examples

```xquery
let $fn := xdmp:function(xs:QName("fn:empty"))
return
  xdmp:function-name($fn)
=> "fn:empty"
```

---

## xdmp:function-parameter-name

Returns the name of the parameter at the designated (1-based) position from the given function's signature.

### Signature

```xquery
xdmp:function-parameter-name(
  $function as function(*),
  $position as xs:integer
) as xs:QName
```

### Parameters

**`$function`**
The function value.

**`$position`**
The 1-based position of the parameter.

### Returns

`xs:QName`

### Examples

```xquery
let $fn := fn:empty#1
return
  xdmp:function-parameter-name($fn,1)
=> "arg1"
```

---

## xdmp:function-parameter-type

Returns the type of the parameter at the designated (1-based) position from the given function's signature.

### Signature

```xquery
xdmp:function-parameter-type(
  $function as function(*),
  $position as xs:integer
) as xs:string
```

### Parameters

**`$function`**
The function value.

**`$position`**
The 1-based position of the parameter.

### Returns

`xs:string`

### Examples

```xquery
let $fn := fn:empty#1
return
  xdmp:function-parameter-type($fn,1)
=> "item()*"
```

---

## xdmp:function-return-type

Returns the return type from the given function's signature.

### Signature

```xquery
xdmp:function-return-type(
  $function as function(*)
) as xs:string
```

### Parameters

**`$function`**
The function value.

### Returns

`xs:string`

### Examples

```xquery
let $fn := fn:empty#1
return
  xdmp:function-return-type($fn)
=> "xs:boolean"
```

---

## xdmp:function-signature

Returns the signature of the function that the argument refers to.

### Signature

```xquery
xdmp:function-signature(
  $function as function(*)
) as xs:string?
```

### Parameters

**`$function`**
The function value.

### Returns

`xs:string?`

### Examples

```xquery
let $fn := fn:empty#1
return
  xdmp:function-signature($fn)
=> "function(item()*) as xs:boolean"
```

---

## xdmp:functions

Returns all in-scope functions.

### Returns

`function(*)*`

### Examples

```xquery
xdmp:describe(fn:function-name(xdmp:functions()[1]))
=> "xs:QName("cts:element-range-query-options")"
```

---
