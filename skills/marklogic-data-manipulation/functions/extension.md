# Extension

73 functions in this category.

## sem:resolve-iri

Resolves a relative URI against an absolute URI.  If $base is specified,
  the URI is resolved relative to that base.  If $base is not specified, the
  base is set to the base-uri property from the static context, if the
  property exists; if it does not exist, an error is thrown.
  This XQuery function backs up the SPARQL IRI() function.

### Signature

```xquery
sem:resolve-iri(
  $relative as xs:string,
  $base as xs:string?
) as sem:iri
```

### Parameters

**`$relative`**
A URI reference to resolve against the base.

**`$base`** *(optional)*
An absolute URI to use as the base of the resolution.

### Returns

`sem:iri`

### Usage Notes

If $base is specified, it is assumed to be an absolute URI and
$relative is assumed to be an absolute or a relative URI reference.
If $relative is a relative URI reference, it is resolved against $base,
using an algorithm such as the ones described in
[RFC 2396] or
[RFC 3986], and
the resulting absolute URI reference is returned.

      
Resolving a URI does not dereference it. This is merely a syntactic operation
on two character strings.

### Examples

```xquery
sem:resolve-iri("hello/goodbye.xml",
     "/mycompany/default.xqy")

=>  /mycompany/hello/goodbye.xml
```

---

## xdmp:QName-from-key

Construct a QName from a string of the form "{namespaceURI}localname".
   This function is useful for constructing Clark notation
   parameters for the 
   xdmp:xslt-eval
   
   and 
   xdmp:xslt-invoke
   
   functions.

### Signature

```xquery
xdmp:QName-from-key(
  $key as xs:string
) as xs:QName
```

### Parameters

**`$key`**
The string from which to construct a QName.

### Returns

`xs:QName`

### Examples

#### Example 1

```xquery
(: Using a key based on a QName with an in-scope namespace prefix :)
xquery version "1.0-ml";
let $key := xdmp:key-from-QName(xs:QName("xs:string"))
let $qname := xdmp:QName-from-key($key)
return ($key, $qname)

(: Returns output of the following form:
     ( {http://www.w3.org/2001/XMLSchema}string, xs:string )
   The generated QName uses the "xs" namespace prefix because
   this binding is implicitly defined in MarkLogic.
:)
```

#### Example 2

```xquery
(: Using a key based on an arbitrary namespace :)
xquery version "1.0-ml";
xdmp:QName-from-key("{/my/namespace}thing")

(: Returns output of the following form: 
     thing
 :)
```

---

## xdmp:add64

Add two 64-bit integer values, discarding overflow.

### Signature

```xquery
xdmp:add64(
  $x as xs:unsignedLong,
  $y as xs:unsignedLong
) as xs:unsignedLong
```

### Parameters

**`$x`**
The first value.

**`$y`**
The second value.

### Returns

`xs:unsignedLong`

### Examples

```xquery
xdmp:add64(11442580934957149475,14565934789622151058)
=> 7561771650869748917
```

---

## xdmp:and64

AND two 64-bit integer values.

### Signature

```xquery
xdmp:and64(
  $x as xs:unsignedLong,
  $y as xs:unsignedLong
) as xs:unsignedLong
```

### Parameters

**`$x`**
The first value.

**`$y`**
The second value.

### Returns

`xs:unsignedLong`

### Examples

```xquery
xdmp:and64(255, 2)
=> 2
```

---

## xdmp:atomizable

Returns true if a value could be atomized without error.
  If no argument is supplied, this function checks
  whether the context item can be atomized without error.

### Signature

```xquery
xdmp:atomizable(
  $item as item()?
) as xs:boolean
```

### Parameters

**`$item`** *(optional)*
The item to be tested for atomizability.

### Returns

`xs:boolean`

### Examples

```xquery
xdmp:atomizable(<x xsi:type="xs:integer">a</x>)

=> false()
```

---

## xdmp:aws-region

Returns the current Amazon Web Services region.
  If MarkLogic is not running on Amazon Web Services, returns an empty sequence.

### Returns

`string?`

### Examples

```xquery
xdmp:aws-region() => "us-east-1"
```

---

## xdmp:aws-services-domain

Returns the current Amazon Web Services services domain.
  If MarkLogic is not running on Amazon Web Services, returns an empty sequence.

### Returns

`string?`

### Examples

```xquery
xdmp:aws-services-domain() => "amazonaws.com"
```

---

## xdmp:aws-services-partition

Returns the current Amazon Web Services services partition.
  If MarkLogic is not running on Amazon Web Services, returns an empty sequence.

### Returns

`string?`

### Examples

```xquery
xdmp:aws-services-partition() => "aws"
```

---

## xdmp:azure-environment

Returns the current Microsoft Azure Environment.
  If MarkLogic is not running on Micorosft Azure, returns an empty sequence.

### Returns

`string?`

### Examples

```xquery
xdmp:azure-environment() => "AzurePublicCloud"
```

---

## xdmp:azure-region

Returns the current Microsoft Azure Region.
  If MarkLogic is not running on Microsoft Azure, returns an empty sequence.

### Returns

`string?`

### Examples

```xquery
xdmp:azure-region() => "westus"
```

---

## xdmp:base64-decode

Converts base64-encoded string to plaintext.

### Signature

```xquery
xdmp:base64-decode(
  $encoded as xs:string
) as xs:string
```

### Parameters

**`$encoded`**
Encoded text to be decoded.

### Returns

`xs:string`

### Examples

```xquery
xdmp:base64-decode(
     "c2xpbmdzIGFuZCBhcnJvd3Mgb2Ygb3V0cmFnZW91cyBmb3J0dW5l")
=> slings and arrows of outrageous fortune
```

---

## xdmp:base64-encode

Converts plaintext into base64-encoded string.

### Signature

```xquery
xdmp:base64-encode(
  $plaintext as xs:string
) as xs:string
```

### Parameters

**`$plaintext`**
Plaintext to be encoded.

### Returns

`xs:string`

### Examples

```xquery
xdmp:base64-encode("slings and arrows of outrageous fortune")
=> c2xpbmdzIGFuZCBhcnJvd3Mgb2Ygb3V0cmFnZW91cyBmb3J0dW5l
```

---

## xdmp:binary-decode

Converts an encoded byte sequence, passed in as a binary node, from the
  specified encoding to a unicode string.

### Signature

```xquery
xdmp:binary-decode(
  $encoded as node(),
  $encoding-name as xs:string
) as xs:string
```

### Parameters

**`$encoded`**
A binary node containing the encoded stream.

**`$encoding-name`**
Specifies the encoding to use when decoding the document.
    Supported values include UTF-8 and ISO-8859-1.
    The string specified for the encoding option will be matched
    to a registered encoding name using the Unicode Charset Alias Matching rules
    (http://www.unicode.org/reports/tr22/#Charset_Alias_Matching).

### Returns

`xs:string`

### Examples

```xquery
xdmp:binary-decode(
   fn:doc("binary_doc_encoded_as_ShiftJIS.dat")/node(),
          "sjis")
=> contents of document after decoding, in unicode characters
```

---

## xdmp:binary-to-integer

Parses a binary string, returning an integer.

### Signature

```xquery
xdmp:binary-to-integer(
  $binary as xs:string
) as xs:integer
```

### Parameters

**`$binary`**
The binary string.

### Returns

`xs:integer`

### Examples

```xquery
xdmp:binary-to-integer("1001001100101100000001011010010")
=> 1234567890
```

---

## xdmp:caller-dialect

Returns the dialect (e.g., "javascript", "1.0-ml", etc) of the caller
  or the empty sequence if no dialect information is available.
  Note that the return is not the language the function that calls
  this built-in is written in; it is the dialect the function is called from.
  For example, if a JavaScript program calls function "foo",
  which uses xdmp:caller-dialect, then the return from xdmp:caller-dialect
  will be “javascript” even if "foo" is implemented in XQuery.

### Returns

`xs:string?`

---

## xdmp:castable-as

Returns true if a value is castable.
  This is similar to the "castable as" XQuery predicate, except that the
  type is determined at runtime.

### Signature

```xquery
xdmp:castable-as(
  $namespace-uri as xs:string,
  $local-name as xs:string,
  $item as item()?
) as xs:boolean
```

### Parameters

**`$namespace-uri`**
The namespace URI of the type.

**`$local-name`**
The local-name of the type.

**`$item`**
The item to be cast.

### Returns

`xs:boolean`

### Examples

```xquery
xdmp:castable-as(
    "http://www.w3.org/2001/XMLSchema",
    "integer",
    "12")
=> true()
```

---

## xdmp:crypt

Calculates the password hash for the given password and salt.

### Signature

```xquery
xdmp:crypt(
  $password as xs:string,
  $salt as xs:string
) as xs:string
```

### Parameters

**`$password`**
String to be hashed.

**`$salt`**
Salt to avoid 1:1 mapping from passwords to hashes. 
    Only the first 8 characters of the salt are significant; any 
    characters beyond the eighth are ignored.

### Returns

`xs:string`

### Usage Notes

You typically use the username as the salt, which ensures that no two 
hash values will be the same, even if different users have the same 
password.

### Examples

```xquery
xdmp:crypt("123abc","admin")
  => "arQEnpM6JHR8vY4n3e5gr0"
```

---

## xdmp:crypt2

Calculates the password hash for the given plain-text password.

### Signature

```xquery
xdmp:crypt2(
  $password as xs:string
) as xs:string
```

### Parameters

**`$password`**
String to be hashed.

### Returns

`xs:string`

### Usage Notes

The password is encrypted using sha256 encoding and it is salted. A salt
 is generated using base-64 representation of a random number. This
 minimizes the probability of hash collisions even if different users have
 the same password.

### Examples

```xquery
xdmp:crypt2("123abc")
  => "$2$aUI4j7YVqvecKkJ7QrK01.$2$ElWEwaxZ"
```

---

## xdmp:decode-from-NCName

Invertible function that decodes characters an NCName produced by
   xdmp:encode-for-NCName.
   Given the NCName produced by xdmp:encode-for-NCName this
   function returns the original string.

### Signature

```xquery
xdmp:decode-from-NCName(
  $name as xs:string
) as xs:string
```

### Parameters

**`$name`**
A string representing an NCName.  This string must have been the result of
  a previous call to xdmp:decode-from-NCName or undefined
  results will occur.

### Returns

`xs:string`

### Examples

```xquery
xdmp:decode-from-NCName("A_20_Name")
=> "A name"
```

---

## xdmp:document-get-collections

Returns the collections to which a given document belongs.

### Signature

```xquery
xdmp:document-get-collections(
  $uri as xs:string
) as xs:string*
```

### Parameters

**`$uri`**
The document URI.

### Returns

`xs:string*`

### Examples

```xquery
xdmp:document-get-collections("chapter5.xml")
=> ("http://marklogic.com/all-books",
        "http://marklogic.com/xml-books")
```

---

## xdmp:document-get-metadata

Returns the metadata value of a given document.

### Signature

```xquery
xdmp:document-get-metadata(
  $uri as xs:string
) as map:map?
```

### Parameters

**`$uri`**
The document URI.

### Returns

`map:map?`

### Examples

```xquery
(: Set some metadata on a document. :)
xquery version "1.0-ml";
xdmp:document-set-metadata("foo.xml",
  map:map() => map:with("someKey", "someValue")
            => map:with("someOtherKey", 123));

(: Fetch the metadata. :)
xquery version "1.0-ml";
xdmp:document-get-metadata("foo.xml")

(: Returns the metadata for the document, as a map. For example:
 :
 : <map:map xmlns:map="http://marklogic.com/xdmp/map" 
 :     xmlns:xsi="http://www.w3.org/2001/XMLSchema-instance" 
 :     xmlns:xs="http://www.w3.org/2001/XMLSchema">
 :   <map:entry key="someKey">
 :     <map:value xsi:type="xs:string">somevalue</map:value>
 :   </map:entry>
 :   <map:entry key="someOtherKey">
 :     <map:value xsi:type="xs:string">123</map:value>
 :   </map:entry>
 : </map:map> 
 :)
```

---

## xdmp:document-get-metadata-value

Returns the metadata value of a given document.

### Signature

```xquery
xdmp:document-get-metadata-value(
  $uri as xs:string,
  $keyName as xs:string
) as xs:string?
```

### Parameters

**`$uri`**
The document URI.

**`$keyName`**
Name of the key for the metadata.

### Returns

`xs:string?`

### Examples

```xquery
xdmp:document-get-metadata-value("/foo.xml", "a")
=> Metadata of key "a" on /foo.xml
```

---

## xdmp:eager

Returns the value of its argument, evaluated eagerly.

### Signature

```xquery
xdmp:eager(
  $arg as item()*
) as item()*
```

### Parameters

**`$arg`**
The value to return

### Returns

`item()*`

### Usage Notes

This function does not change what result is returned; it only changes when the result is calculated.
     Eager evaluation performs all the work before the function returns.
     Lazy evaluation postpones the work to happen on demand as the result is consumed.
      Lazy evaluation may be good idea if a result sequence is not consumed, or only partially consumed.
     For example, a long result sequence could be passed through fn:subsequence to only consume the first few items.
     Path expressions and cts functions that stream results are lazy by default for this reason.
      Lazy evaluation is not a good idea if the result is consumed multiple times.
     Then the work is duplicated each time the result is consumed.
     Binding a result sequence to a variable and using the variable multiple times is consuming the result multiple times.
     In that case eager evaluation would be faster than lazy evaluation.
     If the streaming result of a path expression or cts function is used multiple times, xdmp:eager could make the code faster.

### Examples

```xquery
let $eager := xdmp:eager(cts:search(fn:doc(), "hello"))
let $complex := xdmp:lazy(my:bigCalculation())
return
  if (fn:count($eager) > 10 )
  then $complex
  else ()
```

---

## xdmp:element-content-type

Returns the schema-defined content-type of an element
  ("empty", "simple", "element-only", or "mixed").

### Signature

```xquery
xdmp:element-content-type(
  $element as element()
) as xs:string
```

### Parameters

**`$element`**
An element node.

### Returns

`xs:string`

### Examples

```xquery
xdmp:element-content-type(<html xmlns="http://www.w3.org/1999/xhtml"/>)
  => "element-only"
```

---

## xdmp:email

Send an email in an XQuery program.  A valid SMTP Relay must be
  configured in the Groups page of the Admin Interface for the email to be
  sent. The format of the email message can be an XML file that
  complies with the schema files listed below, or it can be a JavaScript
  object that follows our definition of JSON email format
  (please see xdmp.email).

### Signature

```xquery
xdmp:email(
  $message as element(),
  $options as (element()|map:map)??
) as empty-sequence()
```

### Parameters

**`$message`**
An XML representation of an email message to send.  The message must
  comply with the XML schemas defined in the following schema files:
  
	    install_dir/Config/email-xml.xsd
	    install_dir/Config/rfc822.xsd
	  
  where install_dir is the directory in which
  MarkLogic Server is installed.

**`$options`** *(optional)*
Options with which to customize this operation.
    You can specify options as either an XML element
    in the "xdmp:email" namespace, or as a map:map. The
    options below are XML element localnames. When using a map,
    replace the hyphens with camel casing. For example, "an-option"
    becomes "anOption" when used as a map:map key.
    When including an option from another
    function in an XML options node, use the namespace appropriate to
    that function in the option element.
    
    <authentication>
    
    The credentials to use for this request. This element
    can contain the following child elements:
    
		  username: The username of the user to be authenticated
        on the http server
		  password: The password for username.
		
    An error will be thrown if authentication is used for a SMTP server that
    only supports classic STMP protocol.
    
    <verify-cert>
    
    A boolean value to specify whether the server's certificate should be
    verified. For an SMTP server that supports Extended SMTP, the default value is
    true. For an SMTP server that only supports classic SMTP, the
    default value is false. If a value of true is
    specified but the SMTP server only supports classic SMTP, an error will be thrown.

### Returns

`empty-sequence()`

### Examples

#### Example 1

```xquery
This example demonstrates sending a message with
HTML content.
  
xdmp:email(
<em:Message
 xmlns:em="URN:ietf:params:email-xml:"
 xmlns:rf="URN:ietf:params:rfc822:">
  <rf:subject>Sample HTML Email</rf:subject>
  <rf:from>
    <em:Address>
      <em:name>MarkLogic</em:name>
      <em:adrs>marklogic@yourdomain</em:adrs>
    </em:Address>
  </rf:from>
  <rf:to>
    <em:Address>
      <em:name>System Administrator</em:name>
      <em:adrs>admin@yourdomain</em:adrs>
    </em:Address>
  </rf:to>
  <em:content>
    <html xmlns="http://www.w3.org/1999/xhtml">
      <head>
        <title>Test HTML message</title>
      </head>
      <body>
        <h1>Test HTML message</h1>
        <p>Here is a simple paragraph</p>
      </body>
    </html>
  </em:content>
</em:Message>)
```

#### Example 2

```xquery
This example demonstrates sending a message with
plain text content.

xdmp:email(
<em:Message
 xmlns:em="URN:ietf:params:email-xml:"
 xmlns:rf="URN:ietf:params:rfc822:">
  <rf:subject>Sample Plain Text Email</rf:subject>
  <rf:from>
    <em:Address>
      <em:name>MarkLogic</em:name>
      <em:adrs>marklogic@yourdomain</em:adrs>
    </em:Address>
  </rf:from>
  <rf:to>
    <em:Address>
      <em:name>System Administrator</em:name>
      <em:adrs>admin@yourdomain</em:adrs>
    </em:Address>
  </rf:to>
  <em:content xml:space="preserve">
This is a sample email with a plain text body.
</em:content>
</em:Message>)
```

#### Example 3

```xquery
This example demonstrates sending a message with
attachments.

let $newline := "&#13;&#10;"
let $boundary := concat("blah", xdmp:random())
let $content-type := concat("multipart/mixed; boundary=",$boundary)
let $attachment1 := xs:base64Binary(doc("/space/binaries/testdata1/Bon-Jovi.jpeg"))
let $attachment2 := xs:base64Binary(doc("/space/binaries/testdata1/logo.gif"))
let $content := concat(
  "--",$boundary,$newline,
  $newline,
  "This is a test email with two images attached.", $newline,
  "--",$boundary,$newline,
  "Content-Type: image/jpeg", $newline,
  "Content-Disposition: attachment; filename=Bon-Jovi.jpeg", $newline,
  "Content-Transfer-Encoding: base64", $newline,
  $newline,
  $attachment1, $newline,
  "--",$boundary,$newline,
  "Content-Type: image/gif", $newline,
  "Content-Disposition: attachment; filename=logo.gif", $newline,
  "Content-Transfer-Encoding: base64", $newline,
  $newline,
  $attachment2, $newline,
  "--",$boundary,"--", $newline)

return
  xdmp:email(
  <em:Message
    xmlns:em="URN:ietf:params:email-xml:"
    xmlns:rf="URN:ietf:params:rfc822:">
    <rf:subject>Sample Email</rf:subject>
    <rf:from>
      <em:Address>
        <em:name>MarkLogic</em:name>
        <em:adrs>marklogic@yourdomain</em:adrs>
      </em:Address>
    </rf:from>
    <rf:to>
      <em:Address>
        <em:name>System Administrator</em:name>
        <em:adrs>admin@yourdomain</em:adrs>
      </em:Address>
    </rf:to>
    <rf:content-type>{$content-type}</rf:content-type>
    <em:content xml:space="preserve">
      {$content}
    </em:content>
  </em:Message>)
```

#### Example 4

```xquery
xdmp:email(<em:Message
    xmlns:em="URN:ietf:params:email-xml:"
    xmlns:rf="URN:ietf:params:rfc822:">
    <rf:subject>Sample Email</rf:subject>
    <rf:from>
      <em:Address>
        <em:name>MarkLogic</em:name>
        <em:adrs>marklogic@yourdomain</em:adrs>
      </em:Address>
    </rf:from>
    <rf:to>
      <em:Address>
        <em:name>System Administrator</em:name>
        <em:adrs>admin@yourdomain</em:adrs>
      </em:Address>
    </rf:to>
  </em:Message>,
     <options xmlns="xdmp:email">
       <authentication>
         <username>myname</username>
         <password>mypassword</password>
       </authentication>
       <verify-cert>true</verify-cert>
     </options>)
```

#### Example 5

```xquery
(:This example demonstrates sending a message that contains diacritic headers.:)

let $newline := "&#13;&#10;"
let $boundary := concat("blah", xdmp:random())
let $content-type := concat("multipart/mixed; boundary=",$boundary)
let $attachment1 := xs:base64Binary(doc("/space/binaries/testdata1/Bon-Jovi.jpeg"))
let $attachment2 := xs:base64Binary(doc("/space/binaries/testdata1/logo.gif"))
let $content := concat(
  "--",$boundary,$newline,
  $newline,
  "This is a test email with two images attached.", $newline,
  "--",$boundary,$newline,
  "Content-Type: image/jpeg", $newline,
  "Content-Disposition: attachment; filename=Bon-Jovi.jpeg", $newline,
  "Content-Transfer-Encoding: base64", $newline,
  $newline,
  $attachment1, $newline,
  "--",$boundary,$newline,
  "Content-Type: image/gif", $newline,
  "Content-Disposition: attachment; filename=logo.gif", $newline,
  "Content-Transfer-Encoding: base64", $newline,
  $newline,
  $attachment2, $newline,
  "--",$boundary,"--", $newline)

return
  xdmp:email(
  <em:Message
    xmlns:em="URN:ietf:params:email-xml:"
    xmlns:rf="URN:ietf:params:rfc822:">
    <rf:subject>=?utf-8?Q?Subject with diäcritic?=</rf:subject>
    <rf:from>
      <em:Address>
        <em:name>=?utf-8?Q?Diäcritic sender?=</em:name>
        <em:adrs>marklogic@yourdomain</em:adrs>
      </em:Address>
    </rf:from>
    <rf:to>
      <em:Address>
        <em:name>=?utf-8?Q?Diäcritic receiver?=</em:name>
        <em:adrs>admin@yourdomain</em:adrs>
      </em:Address>
    </rf:to>
    <rf:content-type>{$content-type}</rf:content-type>
    <em:content xml:space="preserve">
      {$content}
    </em:content>
  </em:Message>)
```

---

## xdmp:encode-for-NCName

Invertible function that escapes characters required to be part of
   an NCName.
   This is useful when translating names from other representations such as
   JSON to XML.
   Given any string, the result is always a valid NCName.
   Providing all names are passed through this function the result is
   distinct NCNames so the results can be used for searching as well as
   name generation.
   The inverse function is 
   xdmp:decode-from-NCName.

### Signature

```xquery
xdmp:encode-for-NCName(
  $name as xs:string
) as xs:string
```

### Parameters

**`$name`**
A string which is used as an NCName (such as the localname for an
  element or attribute).

### Returns

`xs:string`

### Examples

```xquery
xdmp:encode-for-NCName("A name")
=> "A_20_Name"
```

---

## xdmp:encoding-language-detect

Analyzes binary, text, or XML data and suggests possible pairs of encoding
  and language, with a confidence score for each pair. Scores of 10 and
  above are high confidence recommendations.
  The results are given in order of decreasing score.
  Accuracy may be poor for short documents.

### Signature

```xquery
xdmp:encoding-language-detect(
  $document as node()
) as element()*
```

### Parameters

**`$document`**
Node to be analyzed for possible encodings and languages.  If the node is
    an XML element or document node, the function takes the string value
    of the specified node (equivalent of fn:string($node)) to
    detect the encoding and language.

### Returns

`element()*`

### Usage Notes

If the input is very small (for example, less than two words), then
  this built-in returns the empty sequence.
      For best results, the input should be at least several hundred bytes.

### Examples

```xquery
xdmp:encoding-language-detect(xdmp:document-get("/tmp/unknown.dat"))
=>
<encoding-language xmlns="xdmp:encoding-language-detect">
  <encoding>windows-1252</encoding>
  <language>en</language>
  <score>9.834</score>
</encoding-language>
<encoding-language xmlns="xdmp:encoding-language-detect">
  <encoding>windows-1252</encoding>
  <language>it</language>
  <score>8.976</score>
</encoding-language>
<encoding-language xmlns="xdmp:encoding-language-detect">
  <encoding>windows-1250</encoding>
  <language>sl</language>
  <score>8.265</score>
</encoding-language>
...
```

---

## xdmp:hash32

Returns the 32-bit hash of a string.

### Signature

```xquery
xdmp:hash32(
  $string as xs:string
) as xs:unsignedInt
```

### Parameters

**`$string`**
The string to be hashed.

### Returns

`xs:unsignedInt`

### Examples

```xquery
xdmp:hash32("/a/b[1]/c")
=> 152930691
```

---

## xdmp:hash64

Returns the 64-bit hash of a string.

### Signature

```xquery
xdmp:hash64(
  $string as xs:string
) as xs:unsignedLong
```

### Parameters

**`$string`**
The string to be hashed.

### Returns

`xs:unsignedLong`

### Examples

```xquery
xdmp:hash64("/a/b[1]/c")
=> 5082244643751628547
```

---

## xdmp:hex-to-integer

Parses a hexadecimal string, returning an integer.

### Signature

```xquery
xdmp:hex-to-integer(
  $hex as xs:string
) as xs:integer
```

### Parameters

**`$hex`**
The hexadecimal string.

### Returns

`xs:integer`

### Examples

```xquery
xdmp:hex-to-integer("1234567890abcdef")
=> 1311768467294899695
```

---

## xdmp:hmac-md5

Calculates the Hash-based Message Authentication Code (HMAC) using the md5 hash function of the given secret key and message arguments.

### Signature

```xquery
xdmp:hmac-md5(
  $secretkey as item(),
  $message as item(),
  $encoding as xs:string?
) as xs:string
```

### Parameters

**`$secretkey`**
The secret key. Must be xs:string or a binary node.

**`$message`**
Message to be authenticated. Must be xs:string or a binary node.

**`$encoding`** *(optional)*
Encoding format for the output string, must be "hex" for hexadecimal
    or "base64". Default is "hex".

### Returns

`xs:string`

### Examples

#### Example 1

```xquery
xdmp:hmac-md5("foo", "bar")
  => "0c7a250281315ab863549f66cd8a3a53"
```

#### Example 2

```xquery
xdmp:hmac-md5("foo", "bar", "base64")
  => "DHolAoExWrhjVJ9mzYo6Uw=="
```

---

## xdmp:hmac-sha1

Calculates the Hash-based Message Authentication Code (HMAC) using the SHA1 hash function of the given secret key and message arguments.

### Signature

```xquery
xdmp:hmac-sha1(
  $secretkey as item(),
  $message as item(),
  $encoding as xs:string?
) as xs:string
```

### Parameters

**`$secretkey`**
The secret key. Must be xs:string or a binary node.

**`$message`**
Message to be authenticated. Must be xs:string or a binary node.

**`$encoding`** *(optional)*
Encoding format for the output string, must be "hex" for hexadecimal
    or "base64". Default is "hex".

### Returns

`xs:string`

### Examples

#### Example 1

```xquery
xdmp:hmac-sha1("foo", "bar")
  => "46b4ec586117154dacd49d664e5d63fdc88efb51"
```

#### Example 2

```xquery
xdmp:hmac-sha1("foo", "bar", "base64")
  => "RrTsWGEXFU2s1J1mTl1j/ciO+1E="
```

---

## xdmp:hmac-sha256

Calculates the Hash-based Message Authentication Code (HMAC) using the SHA256 hash function of the given secret key and message arguments.

### Signature

```xquery
xdmp:hmac-sha256(
  $secretkey as item(),
  $message as item(),
  $encoding as xs:string?
) as xs:string
```

### Parameters

**`$secretkey`**
The secret key. Must be xs:string or a binary node.

**`$message`**
Message to be authenticated. Must be xs:string or a binary node.

**`$encoding`** *(optional)*
Encoding format for the output string, must be "hex" for hexadecimal
    or "base64". Default is "hex".

### Returns

`xs:string`

### Examples

#### Example 1

```xquery
xdmp:hmac-sha256("foo", "bar")
  => "f9320baf0249169e73850cd6156ded0106e2bb6ad8cab01b7bbbebe6d1065317"
```

#### Example 2

```xquery
xdmp:hmac-sha256("foo", "bar", "base64")
  => "+TILrwJJFp5zhQzWFW3tAQbiu2rYyrAbe7vr5tEGUxc="
```

---

## xdmp:hmac-sha512

Calculates the Hash-based Message Authentication Code (HMAC) using the SHA512   hash function of the given secret key and message arguments.

### Signature

```xquery
xdmp:hmac-sha512(
  $secretkey as item(),
  $message as item(),
  $encoding as xs:string?
) as xs:string
```

### Parameters

**`$secretkey`**
The secret key. Must be xs:string or a binary node.

**`$message`**
Message to be authenticated. Must be xs:string or a binary node.

**`$encoding`** *(optional)*
Encoding format for the output string, must be "hex" for hexadecimal
    or "base64". Default is "hex".

### Returns

`xs:string`

### Examples

#### Example 1

```xquery
xdmp:hmac-sha512("foo", "bar")
  => "114682914c5d017dfe59fdc804118b56a3a652a0b8870759cf9e792ed7426b08197076\
      bf7d01640b1b0684df79e4b67e37485669e8ce98dbab60445f0db94fce"
```

#### Example 2

```xquery
xdmp:hmac-sha512("foo", "bar", "base64")
  => "EUaCkUxdAX3+Wf3IBBGLVqOmUqC4hwdZz555LtdCawgZcHa/fQFkCxsGhN955LZ\
      +N0hWaejOmNurYERfDblPzg=="
```

---

## xdmp:initcap

Returns the string where the first letter of each token has been uppercased.

### Signature

```xquery
xdmp:initcap(
  $string as xs:string?
) as xs:string?
```

### Parameters

**`$string`**
The string to modify.

### Returns

`xs:string?`

### Examples

```xquery
xdmp:initcap("my simple example")

=> "My Simple Example"
```

---

## xdmp:integer-to-binary

Returns a binary representation of an integer.

### Signature

```xquery
xdmp:integer-to-binary(
  $val as xs:integer
) as xs:string
```

### Parameters

**`$val`**
The integer value.

### Returns

`xs:string`

### Examples

```xquery
xdmp:integer-to-binary(1234567890)
=> "1001001100101100000001011010010"
```

---

## xdmp:integer-to-hex

Returns a hexadecimal representation of an integer.

### Signature

```xquery
xdmp:integer-to-hex(
  $val as xs:integer
) as xs:string
```

### Parameters

**`$val`**
The integer value.

### Returns

`xs:string`

### Examples

```xquery
xdmp:integer-to-hex(1234567890)
=> "499602d2"
```

---

## xdmp:integer-to-octal

Returns an octal representation of an integer.

### Signature

```xquery
xdmp:integer-to-octal(
  $val as xs:integer
) as xs:string
```

### Parameters

**`$val`**
The integer value.

### Returns

`xs:string`

### Examples

```xquery
xdmp:integer-to-octal(1234567890)
=> "11145401322"
```

---

## xdmp:is-whitespace-node

Returns true if the node is a text node containing only whitespace.

### Signature

```xquery
xdmp:is-whitespace-node(
  $text as node()?
) as xs:boolean
```

### Parameters

**`$text`** *(optional)*
The node to be tested.

### Returns

`xs:boolean`

### Examples

```xquery
xdmp:is-whitespace-node(<x>a</x>)

=> false()
```

---

## xdmp:key-from-QName

Construct a context-independent string from a QName.  This string is
   of the form "{namespaceURI}localname" and is suitable for use as a map
   key.

### Signature

```xquery
xdmp:key-from-QName(
  $name as xs:QName
) as xs:string
```

### Parameters

**`$name`**
The QName to compute a key for.

### Returns

`xs:string`

### Examples

#### Example 1

```xquery
(: Using a QName with an in-scope namespace prefix :)
xquery version "1.0-ml";
xdmp:key-from-QName(xs:QName("xs:string"))

(: Returns output of the following form:
     {http://www.w3.org/2001/XMLSchema}string

   The generated key includes the XMLSchema namespace URI because the
   "xs" namespace binding is implicitly defined in MarkLogic.
:)
```

#### Example 2

```xquery
(: Using a QName with an arbitrary namespace :)
xquery version "1.0-ml";
xdmp:key-from-QName(fn:QName("/my/namespace","thing"))

(: Returns output of the following form: 
     {/my/namespace}thing
 :)
```

---

## xdmp:lazy

Returns the value of its argument, evaluated lazily.

### Signature

```xquery
xdmp:lazy(
  $arg as item()*
) as item()*
```

### Parameters

**`$arg`**
The value to return

### Returns

`item()*`

### Usage Notes

This function does not change what result is returned; it only changes when the result is calculated.
     Eager evaluation performs all the work before the function returns.
     Lazy evaluation postpones the work to happen on demand as the result is consumed.
      Lazy evaluation may be good idea if a result sequence is not consumed, or only partially consumed.
     For example, a long result sequence could be passed through fn:subsequence to only consume the first few items.
     Path expressions and cts functions that stream results are lazy by default for this reason.
      Lazy evaluation is not a good idea if the result is consumed multiple times.
     Then the work is duplicated each time the result is consumed.
     Binding a result sequence to a variable and using the variable multiple times is consuming the result multiple times.
     In that case eager evaluation would be faster than lazy evaluation.
     If the streaming result of a path expression or cts function is used multiple times, xdmp:eager could make the code faster.

### Examples

```xquery
let $eager := xdmp:eager(cts:search(fn:doc(), "hello"))
let $complex := xdmp:lazy(my:bigCalculation())
return
  if (fn:count($eager) > 10 )
  then $complex
  else ()
```

---

## xdmp:ldap-lookup

Returns an ldap entry.

### Signature

```xquery
xdmp:ldap-lookup(
  $DN as xs:string,
  $options as (element()|map:map)??
) as element()*
```

### Parameters

**`$DN`**
The DN of the entry to be returned.

**`$options`** *(optional)*
Options with which to customize this operation.
    You can specify options as either an XML element
    in the "xdmp:ldap" namespace, or as a map:map. The
    options names below are XML element localnames. When using a map,
    replace the hyphens with camel casing. For example, "an-option"
    becomes "anOption" when used as a map:map key.
    This function supports the following options:
    
    username
    ldap username.
    password
    ldap password.
    server-uri
    
    ldap server uri.
    use-appserver-config
    
    Use appserver config as default. Specify true or false. The default
    is false.
    bind-method
    
    ldap bind method. Specify simple or external.
    The default is simple.
    credential-id
    
    The credential to be used to sign the generated certificate.
    "start-tls"
    
    start tls (Transport Layer Security) extended operation. Specify true or false. The default
    is false.
    "certificate"
    
    client certificate.
    "private-key"
    
    private key for the client certificate.
    "nested-lookup"
    
    Enable nested group lookup. Specify true or false. The default
    is true.

### Returns

`element()*`

### Examples

```xquery
xdmp:ldap-lookup(
  "CN=Jane Doe,CN=Users,DC=MLTEST1,DC=LOCAL",
   <options xmlns="xdmp:ldap">
  <username>admin</username>
  <password>admin</password>
  <server-uri>ldap://dc1.mltest1.local:389</server-uri>
 </options>)

=>
<ldap-object xmlns="http://marklogic.com/xdmp/ldap/object">
<ldap-attribute id="DN">CN=Jane Doe,CN=Users,DC=MLTEST1,DC=LOCAL</ldap-attribute>
<ldap-attribute id="objectClass">top</ldap-attribute>
<ldap-attribute id="objectClass">person</ldap-attribute>
<ldap-attribute id="objectClass">organizationalPerson</ldap-attribute>
<ldap-attribute id="objectClass">user</ldap-attribute>
<ldap-attribute id="cn">Jane Doe</ldap-attribute>
<ldap-attribute id="sn">Tsoi</ldap-attribute>
<ldap-attribute id="givenName">Jane</ldap-attribute>
<ldap-attribute id="distinguishedName">CN=Jane Doe,CN=Users,DC=MLTEST1,DC=LOCAL</ldap-attribute>
<ldap-attribute id="instanceType">4</ldap-attribute>
<ldap-attribute id="whenCreated">20120418134913.0Z</ldap-attribute>
<ldap-attribute id="whenChanged">20130423001215.0Z</ldap-attribute>
<ldap-attribute id="displayName">Jane Doe</ldap-attribute>
<ldap-attribute id="uSNCreated">21173</ldap-attribute>
<ldap-attribute id="memberOf">CN=TestGroup Admin,CN=Users,DC=MLTEST1,DC=LOCAL</ldap-attribute>
<ldap-attribute id="memberOf">CN=Domain Admins,CN=Users,DC=MLTEST1,DC=LOCAL</ldap-attribute>
<ldap-attribute id="memberOf">CN=Remote Desktop Users,CN=Builtin,DC=MLTEST1,DC=LOCAL</ldap-attribute>
<ldap-attribute id="uSNChanged">82727</ldap-attribute>
<ldap-attribute id="name">Jane Doe</ldap-attribute>
<ldap-attribute id="userAccountControl">66048</ldap-attribute>
<ldap-attribute id="badPwdCount">0</ldap-attribute>
<ldap-attribute id="codePage">0</ldap-attribute>
<ldap-attribute id="countryCode">0</ldap-attribute>
<ldap-attribute id="badPasswordTime">130112986222890625</ldap-attribute>
<ldap-attribute id="lastLogoff">0</ldap-attribute>
<ldap-attribute id="lastLogon">130117512192890625</ldap-attribute>
<ldap-attribute id="pwdLastSet">129792305530986328</ldap-attribute>
<ldap-attribute id="primaryGroupID">513</ldap-attribute>
<ldap-attribute id="adminCount">1</ldap-attribute>
<ldap-attribute id="accountExpires">9223372036854775807</ldap-attribute>
<ldap-attribute id="logonCount">205</ldap-attribute>
<ldap-attribute id="sAMAccountName">jdoe</ldap-attribute>
<ldap-attribute id="sAMAccountType">805306368</ldap-attribute>
<ldap-attribute id="userPrincipalName">jdoe@MLTEST1.LOCAL</ldap-attribute>
<ldap-attribute id="objectCategory">CN=Person,CN=Schema,CN=Configuration,DC=MLTEST1,DC=LOCAL</ldap-attribute>
<ldap-attribute id="dSCorePropagationData">20120530014553.0Z</ldap-attribute>
<ldap-attribute id="dSCorePropagationData">16010101000000.0Z</ldap-attribute>
<ldap-attribute id="lastLogonTimestamp">130111495353203125</ldap-attribute>
</ldap-object>
```

---

## xdmp:ldap-search

Returns ldap search result.

### Signature

```xquery
xdmp:ldap-search(
  $query as xs:string,
  $options as (element()|map:map)??
) as element()*
```

### Parameters

**`$query`**
The query is a string representation of the filter to apply in the search.
    The string should conform to the format specified in RFC 4515 as
    extended by RFC 4526. For example, "(cn=Jane Doe)".

**`$options`** *(optional)*
Options with which to customize this operation.
    You can specify options as either an XML element
    in the "xdmp:ldap" namespace, or as a map:map. The
    options names below are XML element localnames. When using a map,
    replace the hyphens with camel casing. For example, "an-option"
    becomes "anOption" when used as a map:map key.
    This function supports the following options:
    
    username
    ldap username.
    password
    ldap password.
    server-uri
    
    ldap server uri.
    search-base
    
    search-base is the DN of the entry at which to start the search.
    use-appserver-config
    
    Use appserver config as default. Specify true or false. The default
    is false.
    bind-method
    
    ldap bind method. Specify simple, MD5 or external.
    The default is simple.
    credential-id
    
    The credential to be used to sign the generated certificate.
    "start-tls"
    
    start tls (Transport Layer Security) extended operation. Specify true or false. The default
    is false.
    "certificate"
    
    client certificate.
    "private-key"
    
    private key for the client certificate.

### Returns

`element()*`

### Examples

```xquery
xdmp:ldap-search(
  "(cn=Jane Doe)",
   <options xmlns="xdmp:ldap">
  <username>admin</username>
  <password>admin</password>
  <server-uri>ldap://dc1.mltest1.local:389</server-uri>
  <search-base>CN=Users,DC=MLTEST1,DC=LOCAL</search-base>
 </options>)

=>
<ldap-object xmlns="http://marklogic.com/xdmp/ldap/object">
<ldap-attribute id="DN">CN=Jane Doe,CN=Users,DC=MLTEST1,DC=LOCAL</ldap-attribute>
<ldap-attribute id="objectClass">top</ldap-attribute>
<ldap-attribute id="objectClass">person</ldap-attribute>
<ldap-attribute id="objectClass">organizationalPerson</ldap-attribute>
<ldap-attribute id="objectClass">user</ldap-attribute>
<ldap-attribute id="cn">Jane Doe</ldap-attribute>
<ldap-attribute id="sn">Tsoi</ldap-attribute>
<ldap-attribute id="givenName">Jane</ldap-attribute>
<ldap-attribute id="distinguishedName">CN=Jane Doe,CN=Users,DC=MLTEST1,DC=LOCAL</ldap-attribute>
<ldap-attribute id="instanceType">4</ldap-attribute>
<ldap-attribute id="whenCreated">20120418134913.0Z</ldap-attribute>
<ldap-attribute id="whenChanged">20130423001215.0Z</ldap-attribute>
<ldap-attribute id="displayName">Jane Doe</ldap-attribute>
<ldap-attribute id="uSNCreated">21173</ldap-attribute>
<ldap-attribute id="memberOf">CN=TestGroup Admin,CN=Users,DC=MLTEST1,DC=LOCAL</ldap-attribute>
<ldap-attribute id="memberOf">CN=Domain Admins,CN=Users,DC=MLTEST1,DC=LOCAL</ldap-attribute>
<ldap-attribute id="memberOf">CN=Remote Desktop Users,CN=Builtin,DC=MLTEST1,DC=LOCAL</ldap-attribute>
<ldap-attribute id="uSNChanged">82727</ldap-attribute>
<ldap-attribute id="name">Jane Doe</ldap-attribute>
<ldap-attribute id="userAccountControl">66048</ldap-attribute>
<ldap-attribute id="badPwdCount">0</ldap-attribute>
<ldap-attribute id="codePage">0</ldap-attribute>
<ldap-attribute id="countryCode">0</ldap-attribute>
<ldap-attribute id="badPasswordTime">130112986222890625</ldap-attribute>
<ldap-attribute id="lastLogoff">0</ldap-attribute>
<ldap-attribute id="lastLogon">130117512192890625</ldap-attribute>
<ldap-attribute id="pwdLastSet">129792305530986328</ldap-attribute>
<ldap-attribute id="primaryGroupID">513</ldap-attribute>
<ldap-attribute id="adminCount">1</ldap-attribute>
<ldap-attribute id="accountExpires">9223372036854775807</ldap-attribute>
<ldap-attribute id="logonCount">205</ldap-attribute>
<ldap-attribute id="sAMAccountName">jdoe</ldap-attribute>
<ldap-attribute id="sAMAccountType">805306368</ldap-attribute>
<ldap-attribute id="userPrincipalName">jdoe@MLTEST1.LOCAL</ldap-attribute>
<ldap-attribute id="objectCategory">CN=Person,CN=Schema,CN=Configuration,DC=MLTEST1,DC=LOCAL</ldap-attribute>
<ldap-attribute id="dSCorePropagationData">20120530014553.0Z</ldap-attribute>
<ldap-attribute id="dSCorePropagationData">16010101000000.0Z</ldap-attribute>
<ldap-attribute id="lastLogonTimestamp">130111495353203125</ldap-attribute>
</ldap-object>
```

---

## xdmp:lshift64

Left-shift a 64-bit integer value.

### Signature

```xquery
xdmp:lshift64(
  $x as xs:unsignedLong,
  $y as xs:integer
) as xs:unsignedLong
```

### Parameters

**`$x`**
The value to shift.

**`$y`**
The left shift to perform. This value may be negative.

### Returns

`xs:unsignedLong`

### Examples

```xquery
xdmp:lshift64(255, 2)
=> 1020
```

---

## xdmp:md5

Calculates the md5 hash of the given argument.

### Signature

```xquery
xdmp:md5(
  $data as item(),
  $encoding as xs:string?
) as xs:string
```

### Parameters

**`$data`**
Data to be hashed. Must be xs:string or a binary node.

**`$encoding`** *(optional)*
Encoding format for the output string, must be "hex" for hexadecimal
    or "base64". Default is "hex".

### Returns

`xs:string`

### Examples

#### Example 1

```xquery
xdmp:md5("foo")
  => "acbd18db4cc2f85cedef654fccc4a4d8"
```

#### Example 2

```xquery
xdmp:md5("foo", "base64")
  => "rL0Y20zC+Fzt72VPzMSk2A=="
```

---

## xdmp:mul64

Multiply two 64-bit integer values, discarding overflow.

### Signature

```xquery
xdmp:mul64(
  $x as xs:unsignedLong,
  $y as xs:unsignedLong
) as xs:unsignedLong
```

### Parameters

**`$x`**
The first value.

**`$y`**
The second value.

### Returns

`xs:unsignedLong`

### Examples

```xquery
xdmp:mul64(15107650474313474666,13290239292956375463)
=> 1404109880107289894
```

---

## xdmp:multipart-decode

Extract the parts from a multipart encoding. The first item in the
  sequence is a manifest, and the remaining items are the decoded parts.
      An attempt will be made to determine the type of content based on
  headers such as the part's content-type. If possible, an element will be
  returned, falling back to an xs:string, and finally binary().
      The options control how the parts are unpacked, and are similar to
  xdmp:zip-get
   -
  default-namespace, repair,
  format, default-language,
  and encoding. The options apply to all parts, so specifying a format of
  binary will cause all parts to be returned as binary, and specifying text
  will cause all parts to be returned as xs:string if possible, falling back
  to binary() if necessary. This is useful if different parts need different
  options, in which case the resulting strings can each be passed to
  xdmp:unquote
  
  with appropriate options.

### Signature

```xquery
xdmp:multipart-decode(
  $separator as xs:string,
  $data as binary(),
  $options as element()?
) as node()*
```

### Parameters

**`$separator`**
The string that is to be used as a separator.

**`$data`**
The data (as a binary node) to be decoded.

**`$options`** *(optional)*
Decode options.

### Returns

`node()*`

### Examples

```xquery
xquery version "1.0-ml";
let $html := document{ <html><p>Some stuff in an .html document</p></html> }
let $xml := document{ <root><a>Some other stuff in a .xml document</a></root> }
let $json := xdmp:to-json(("a",fn:false()))
let $boundary-string := "gc0p4Jq0M2Yt08jU534c0p"
let $mpe := xdmp:multipart-encode(
   $boundary-string,
   <manifest>
     <part>
       <headers>
         <Content-Type>application/xml</Content-Type>
         <boundary>gc0p4Jq0M2Yt08jU534c0p</boundary>
       </headers>
     </part>
     <part>
       <headers>
         <Content-Type>text/html</Content-Type>
       </headers>
      </part>
     <part>
       <headers>
         <Content-Type>application/json</Content-Type>
       </headers>
     </part>
   </manifest>,
   ($xml,$html,$json) )
return xdmp:multipart-decode($boundary-string, $mpe)
=>
<manifest>
  <part>
    <headers>
      <Content-Type>application/xml</Content-Type>
      <boundary>gc0p4Jq0M2Yt08jU534c0p</boundary>
      <Content-Length>94</Content-Length>
    </headers>
  </part>
  <part>
    <headers>
      <Content-Type>text/html</Content-Type>
      <Content-Length>90</Content-Length>
    </headers>
  </part>
  <part>
    <headers>
      <Content-Type>application/json</Content-Type>
      <Content-Length>12</Content-Length>
    </headers>
  </part>
</manifest>
<?xml version="1.0" encoding="UTF-8"?>
<root><a>Some other stuff in a .xml document</a></root>
<?xml version="1.0" encoding="UTF-8"?>
<html><p>Some stuff in an .html document</p></html>
["a", false]
```

---

## xdmp:multipart-encode

Create a multipart encoding of the specified node. The returned binary
  node can be passed to 
  xdmp:http-post
  .
  The manifest is modeled after the
  manifest that is passed to 
  xdmp:zip-create
  ,
  with the headers element being
  the same as is described for 
  xdmp:http-get
  
  allowing users to add arbitrary
  headers to each part. If a content-type header is not specified for a part,
  it will be determined if possible from the content.
      There should be one part element for each node in the content sequence.
      Each part also has an optional options node to control how xml or text
  will be serialized. The two options are the same as for
  xdmp:save
  .
      <part>
    <headers>
      <Content-Type>image/jpeg</Content-Type>
    <headers>
    <options>
      <output-encoding>...</output-encoding>
      <output-sgml-character-entities>...</output-sgml-character-entities>
    </options>
  </part>

### Signature

```xquery
xdmp:multipart-encode(
  $separator as xs:string,
  $manifest as element(),
  $content as node()*
) as binary()
```

### Parameters

**`$separator`**
The string that is to be used as a separator.

**`$manifest`**
The manifest.

**`$content`**
The nodes that are to be encoded.

### Returns

`binary()`

### Examples

```xquery
xquery version "1.0-ml";
let $html := document{ <html><p>Some stuff in an .html document</p></html> }
let $xml := document{ <root><a>Some other stuff in a .xml document</a></root> }
let $json := xdmp:to-json(("a",fn:false()))
let $boundary-string := "gc0p4Jq0M2Yt08jU534c0p"
return
xdmp:multipart-encode(
   $boundary-string,
   <manifest>
     <part>
       <headers>
         <Content-Type>application/xml</Content-Type>
         <boundary>gc0p4Jq0M2Yt08jU534c0p</boundary>
       </headers>
     </part>
     <part>
       <headers>
         <Content-Type>text/html</Content-Type>
       </headers>
     </part>
     <part>
       <headers>
         <Content-Type>application/json</Content-Type>
       </headers>
     </part>
   </manifest>,
   ($xml,$html,$json) )
=>
--gc0p4Jq0M2Yt08jU534c0p
Content-Type: application/xml
boundary: gc0p4Jq0M2Yt08jU534c0p
Content-Length: 94

<?xml version="1.0" encoding="UTF-8"?>
<root><a>Some other stuff in a .xml document</a></root>
--gc0p4Jq0M2Yt08jU534c0p
Content-Type: text/html
Content-Length: 90

<?xml version="1.0" encoding="UTF-8"?>
<html><p>Some stuff in an .html document</p></html>
--gc0p4Jq0M2Yt08jU534c0p
Content-Type: application/json
Content-Length: 12

["a", false]
--gc0p4Jq0M2Yt08jU534c0p--
```

---

## xdmp:node-kind

Returns an xs:string
  representing the node's kind: either
  "document", "element", "attribute", "text", "namespace",
  "processing-instruction", "binary", or "comment".

      
  The fn:node-kind
  builtin was dropped from the final XQuery 1.0
  spec.  This is the equivalent function in the xdmp:
   namespace
  carried over for MarkLogic 1.0 dialects.

### Signature

```xquery
xdmp:node-kind(
  $node as node()
) as xs:string
```

### Parameters

**`$node`**
The node whose kind is to be returned.

### Returns

`xs:string`

### Examples

```xquery
let $x := <hello><goodbye>1</goodbye></hello>
return
xdmp:node-kind($x/node())

=> element
```

---

## xdmp:node-metadata

Returns the metadata value of a given node.

### Signature

```xquery
xdmp:node-metadata(
  $node as node()
) as map:map?
```

### Parameters

**`$node`**
The node whose metadata are to be returned.

### Returns

`map:map?`

### Examples

```xquery
xdmp:node-metadata(fn:doc("/foo.xml"))
=> Metadata of document node of /foo.xml
```

---

## xdmp:node-metadata-value

Returns the metadata value of a node for a particular key.

### Signature

```xquery
xdmp:node-metadata-value(
  $node as node(),
  $keyName as xs:string
) as xs:string?
```

### Parameters

**`$node`**
The node whose metadata are to be returned.

**`$keyName`**
Name of the key for the metadata.

### Returns

`xs:string?`

### Examples

```xquery
xdmp:node-metadata-value(fn:doc("/foo.xml"), "a")
=> Metadata of key "a" on document node /foo.xml
```

---

## xdmp:not64

NOT a 64-bit integer value.

### Signature

```xquery
xdmp:not64(
  $x as xs:unsignedLong
) as xs:unsignedLong
```

### Parameters

**`$x`**
The input value.

### Returns

`xs:unsignedLong`

### Examples

```xquery
xdmp:not64(255)
=> 18446744073709551360
```

---

## xdmp:octal-to-integer

Parses an octal string, returning an integer.

### Signature

```xquery
xdmp:octal-to-integer(
  $octal as xs:string
) as xs:integer
```

### Parameters

**`$octal`**
The octal string.

### Returns

`xs:integer`

### Examples

```xquery
xdmp:octal-to-integer("12345670")
=> 2739128
```

---

## xdmp:or64

OR two 64-bit integer values.

### Signature

```xquery
xdmp:or64(
  $x as xs:unsignedLong,
  $y as xs:unsignedLong
) as xs:unsignedLong
```

### Parameters

**`$x`**
The first value.

**`$y`**
The second value.

### Returns

`xs:unsignedLong`

### Examples

```xquery
xdmp:or64(255, 2)
=> 255
```

---

## xdmp:parse-dateTime

Parses a string containing date, time or dateTime using the supplied
   picture argument and returns a dateTime value.  While this function
   is closely related to other XSLT functions, it is available in XSLT
   as well as in all XQuery dialects and in Server-Side JavaScript.

### Signature

```xquery
xdmp:parse-dateTime(
  $picture as xs:string,
  $value as xs:string,
  $language as xs:string??,
  $calendar as xs:string??,
  $country as xs:string??
) as xs:dateTime
```

### Parameters

**`$picture`**
The desired string representation of the given $value.
     The picture string is a sequence of characters, in which the
     characters represent variables such as, decimal-separator-sign,
     grouping-sign, zero-digit-sign, digit-sign, pattern-separator,
     percent sign and per-mille-sign.  For details on the picture string, see
     http://www.w3.org/TR/xslt20/#date-picture-string.
     This follows the specification of
     picture string in the W3C XSLT 2.0
     specification for the fn:format-dateTime function.
     

   Symbol         Description
  -----------------------------------
     'Y'        year(absolute value)
     'M'        month in year
     'D'        day in month
     'd'        day in year
     'F'        day of week
     'W'        week in year
     'w'        week in month
     'H'        hour in day
     'h'        hour in half-day
     'P'        am/pm marker
     'm'        minute in hour
     's'        second in minute
     'f'        fractional seconds
     'Z'        timezone as a time offset from UTC
                for example PST
     'z'        timezone as an offset using GMT,
                for example GMT+1

**`$value`**
The given string $value representing the dateTime value
     that needs to be formatted.

**`$language`** *(optional)*
The language used in string representation of the date, time or
     dateTime value.

**`$calendar`** *(optional)*
This argument is reserved for future use. The only calendar supported
     at this point is "Gregorian" or "AD".

**`$country`** *(optional)*
$country is used to take into account if there any country specific
     interpretation of the string while converting it into dateTime value.

### Returns

`xs:dateTime`

### Usage Notes

Dates before October 15, 1582 (the start of the Gregorian calendar) will
    not return the correct dateTime value.
      The xdmp:parse-dateTime function will not parse all dates;
    if it does not parse a date, it can throw the
    XDMP-PATTERNVALUEMISMATCH exception.  To help normalize
    the dates so they can be parsed, you can try using the XSLT functions
    defined in the following stylesheet:
      <marklogic-dir>/Modules/MarkLogic/appservices/utils/normalize-dates.xsl
      In particular xdmp:parse-dateTime does not support parsing names of days or months.

### Examples

```xquery
xdmp:parse-dateTime("[Y0001]-[M01]-[D01]T[h01]:[m01]:[s01].[f1][Z]",
		   "2014-01-06T17:13:50.873594-08:00")
   =>
   2014-01-06T17:13:50.874-08:00
```

---

## xdmp:parse-yymmdd

Parses a string containing date, time or dateTime using the supplied
   picture argument and returns a dateTime value.    While this function
   is closely related to other XSLT functions, it is available in XSLT
   as well as in all XQuery dialects and in Server-Side JavaScript.

### Signature

```xquery
xdmp:parse-yymmdd(
  $picture as xs:string,
  $value as xs:string,
  $language as xs:string??,
  $calendar as xs:string??,
  $country as xs:string??
) as xs:dateTime
```

### Parameters

**`$picture`**
The desired string representation of the given $value.
     This follows the specification of picture string which is
     compatible to the format specification in icu. See
     http://icu-project.org/apiref/icu4j/com/ibm/icu/text/SimpleDateFormat.html
     for more details.

     The following is the summary of the formatting symbols:
     

     Symbol     Description
  ----------------------------
     "y"       year(absolute value)
     "M"       month in year
     "d"       day in month
     "D"       day in year
     "E"       day of week
     "w"       week in year
     "W"       week in month
     "H"       hour in day
     "K"       hour in half-day
     "a"       am/pm marker
     "s"       second in minute
     "S"       fractional seconds
     "Z"       timezone as a time offset from UTC
               for example PST
     "ZZZZ"    timezone as an offset using GMT,
               for example GMT+1

**`$value`**
The given string $value that needs to be formatted.

**`$language`** *(optional)*
The language used in string representation of the date, time or
     dateTime value.

**`$calendar`** *(optional)*
This argument is reserved for future use. The only calendar supported
     at this point is "Gregorian" or "AD".

**`$country`** *(optional)*
$country is used to take into account if there any country specific
     interpretation of the string while converting it into dateTime value.

### Returns

`xs:dateTime`

### Usage Notes

Dates before October 15, 1582 (the start of the Gregorian calendar) will
    not return the correct dateTime value.

### Examples

```xquery
xdmp:parse-yymmdd("yyyy-MM-ddThh:mm:ss.Sz",
      "2014-01-06T17:13:50.873594-8.00")
   =>
   2014-01-06T17:13:50.874-08:00
```

---

## xdmp:position

Returns an integer value representing the starting position of a
  string within the search string. Note, the string starting position is 1.
  If the first parameter is empty, the result is the empty sequence.

### Signature

```xquery
xdmp:position(
  $test as xs:string?,
  $target as xs:string?,
  $collation as xs:string??
) as xs:integer?
```

### Parameters

**`$test`**
The string to test for existence in the second parameter.

**`$target`**
The string from which to test.

**`$collation`** *(optional)*
The optional name of a valid collation URI.  For information on the
collation URI syntax, see the Search Developer's Guide.

### Returns

`xs:integer?`

### Examples

```xquery
xdmp:position("chin","searchintext")

=> 5
```

---

## xdmp:random

Returns a random unsigned integer between 0 and a number up to 64 bits long.

### Signature

```xquery
xdmp:random(
  $max as xs:unsignedLong?
) as xs:unsignedLong
```

### Parameters

**`$max`** *(optional)*
The optional maximum value (inclusive).

### Returns

`xs:unsignedLong`

### Examples

```xquery
xdmp:random(100)
=> 47
```

---

## xdmp:resolve-uri

Resolves a relative URI against an absolute URI.  If $base is specified,
  the URI is resolved relative to that base.  If $base is not specified, the
  base is set to the base-uri property from the static context, if the
  property exists; if it does not exist, an error is thrown.

### Signature

```xquery
xdmp:resolve-uri(
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

This function is the same as 
fn:resolve-uri
, 
but always accepts a relative
base URI. The  
fn:resolve-uri
, 
function raises an error in this case in
standards compatible dialects.

      
If $base is specified, it is assumed to be an absolute URI and
$relative is assumed to be an absolute or a relative URI reference.
If $relative is a relative URI reference, it is resolved against $base,
using an algorithm such as the ones described in
[RFC 2396] or
[RFC 3986], and
the resulting absolute URI reference is returned.

      
If $relative is the zero-length string,  
fn:resolve-uri
, 
returns
the value of $base, or the base-uri property from the static context
if there is no $base value specified (if the base-uri property is
not initialized in the static context, an error is raised).

      
Resolving a URI does not dereference it. This is merely a syntactic operation
on two character strings.

### Examples

```xquery
xdmp:resolve-uri("hello/goodbye.xml",
     "/mycompany/default.xqy")

=>  /mycompany/hello/goodbye.xml
```

---

## xdmp:rshift64

Right-shift a 64-bit integer value.

### Signature

```xquery
xdmp:rshift64(
  $x as xs:unsignedLong,
  $y as xs:integer
) as xs:unsignedLong
```

### Parameters

**`$x`**
The value to shift.

**`$y`**
The right shift to perform. This value may be negative.

### Returns

`xs:unsignedLong`

### Examples

```xquery
xdmp:rshift64(255, 2)
=> 63
```

---

## xdmp:set-response-output-method

Sets the serialization method.  This overrides
  any output option set in the xdmp:output XQuery prolog 
  option.

### Signature

```xquery
xdmp:set-response-output-method(
  $method as xs:string
) as empty-sequence()
```

### Parameters

**`$method`**
The serialization method.  These are the same strings as used in the 
    xdmp:output XQuery prolog option.  For a list of the options,
 see xdmp:output in the XQuery and XSLT Reference Guide.

### Returns

`empty-sequence()`

### Examples

```xquery
xdmp:set-response-output-method("n-triples");
```

---

## xdmp:sha1

Calculates the SHA1 hash of the given argument.

### Signature

```xquery
xdmp:sha1(
  $data as item(),
  $encoding as xs:string?
) as xs:string
```

### Parameters

**`$data`**
Data to be hashed. Must be xs:string or a binary node.

**`$encoding`** *(optional)*
Encoding format for the output string, must be "hex" for hexadecimal
    or "base64". Default is "hex".

### Returns

`xs:string`

### Examples

#### Example 1

```xquery
xdmp:sha1("foo")
  => "0beec7b5ea3f0fdbc95d0dd47f3c5bc275da8a33"
```

#### Example 2

```xquery
xdmp:sha1("foo", "base64")
  => "C+7Hteo/D9vJXQ3UfzxbwnXaijM="
```

---

## xdmp:sha256

Calculates the SHA256 hash of the given argument.

### Signature

```xquery
xdmp:sha256(
  $data as item(),
  $encoding as xs:string?
) as xs:string
```

### Parameters

**`$data`**
Data to be hashed. Must be xs:string or a binary node.

**`$encoding`** *(optional)*
Encoding format for the output string, must be "hex" for hexadecimal
    or "base64". Default is "hex".

### Returns

`xs:string`

### Examples

#### Example 1

```xquery
xdmp:sha256("foo")
  => "2c26b46b68ffc68ff99b453c1d30413413422d706483bfa0f98a5e886266e7ae"
```

#### Example 2

```xquery
xdmp:sha256("foo", "base64")
  => "LCa0a2j/xo/5m0U8HTBBNBNCLXBkg7+g+YpeiGJm564="
```

---

## xdmp:sha384

Calculates the SHA384 hash of the given argument.

### Signature

```xquery
xdmp:sha384(
  $data as item(),
  $encoding as xs:string?
) as xs:string
```

### Parameters

**`$data`**
Data to be hashed. Must be xs:string or a binary node.

**`$encoding`** *(optional)*
Encoding format for the output string, must be "hex" for hexadecimal
    or "base64". Default is "hex".

### Returns

`xs:string`

### Examples

#### Example 1

```xquery
xdmp:sha384("foo")
  => "f7fbba6e0636f890e56fbbf3283e524c6fa3204ae298382d624741d0dc6638326e\
      282c41be5e4254d8820772c5518a2c5a8c0c7f7eda19594a7eb539453e1ed7"
```

#### Example 2

```xquery
xdmp:sha384("foo", "base64")
  => "9/u6bgY2+JDlb7vzKD5STG+jIErimDgtYkdB0NxmODJuKCxBvl5CVNiCB3LFUYos\
      WowMf37aGVlKfrU5RT4e1w=="
```

---

## xdmp:sha512

Calculates the SHA512 hash of the given argument.

### Signature

```xquery
xdmp:sha512(
  $data as item(),
  $encoding as xs:string?
) as xs:string
```

### Parameters

**`$data`**
Data to be hashed. Must be xs:string or a binary node.

**`$encoding`** *(optional)*
Encoding format for the output string, must be "hex" for hexadecimal
    or "base64". Default is "hex".

### Returns

`xs:string`

### Examples

#### Example 1

```xquery
xdmp:sha512("foo")
  => "f7fbba6e0636f890e56fbbf3283e524c6fa3204ae298382d624741d0dc6638326e\
      282c41be5e4254d8820772c5518a2c5a8c0c7f7eda19594a7eb539453e1ed7"
```

#### Example 2

```xquery
xdmp:sha512("foo", "base64")
  => "9/u6bgY2+JDlb7vzKD5STG+jIErimDgtYkdB0NxmODJuKCxBvl5CVNiCB3LFUYos\
      WowMf37aGVlKfrU5RT4e1w=="
```

---

## xdmp:sleep

Delays for a specific amount of time.

### Signature

```xquery
xdmp:sleep(
  $msec as xs:unsignedInt
) as empty-sequence()
```

### Parameters

**`$msec`**
The amount of time to sleep, in milliseconds.

### Returns

`empty-sequence()`

### Examples

```xquery
(: sleep for 1 second :)
xdmp:sleep(1000)
=> ()
```

---

## xdmp:step64

Combines an initial hash with a subsequent hash.

### Signature

```xquery
xdmp:step64(
  $initial as xs:unsignedLong,
  $step as xs:unsignedLong
) as xs:unsignedLong
```

### Parameters

**`$initial`**
An initial hash.

**`$step`**
A step hash to be combined with the initial hash.

### Returns

`xs:unsignedLong`

### Examples

```xquery
xdmp:step64(xdmp:hash64("initial"), xdmp:hash64("step"))
=> 12899951685816192752
```

---

## xdmp:strftime

Formats a dateTime value using POSIX strftime.  This function uses
  the POSIX strftime system call in the way it is implemented on each
  platform.  For other XQuery functions that have more functionality
  (for example, for things like timezones), use one or more if the
  various XQuery or XSLT standard functions such as
  fn:format-dateTime
  .

### Signature

```xquery
xdmp:strftime(
  $format as xs:string,
  $value as xs:dateTime
) as xs:string
```

### Parameters

**`$format`**
The strftime format string.

**`$value`**
The dateTime value.

### Returns

`xs:string`

### Usage Notes

The supported format strings differ for different platforms.  For the
 supported format strings for Windows, see the following link:
      https://learn.microsoft.com/en-us/cpp/c-runtime-library/reference/strftime-wcsftime-strftime-l-wcsftime-l?view=msvc-170
      For the supported format strings for Linux, see the following link:
      https://linux.die.net/man/3/strftime

### Examples

```xquery
xdmp:strftime("%a, %d %b %Y %H:%M:%S", fn:current-dateTime())
=> Thu, 06 Nov 2014 14:08:37
```

---

## xdmp:timestamp-to-wallclock

Converts a 64 bit timestamp value to an xs:dateTime.

### Signature

```xquery
xdmp:timestamp-to-wallclock(
  $timestamp as xs:unsignedLong
) as xs:dateTime
```

### Parameters

**`$timestamp`**
The timestamp.

### Returns

`xs:dateTime`

### Examples

```xquery
xdmp:timestamp-to-wallclock(9476208600000000)
=> 2000-01-11T12:01:00
```

---

## xdmp:type

Returns the name of the simple type of the atomic value argument as an 
  xs:QName.
  This function is a built-in.

### Signature

```xquery
xdmp:type(
  $value as xs:anyAtomicType
) as xs:QName
```

### Parameters

**`$value`**
The value to return the type of.

### Returns

`xs:QName`

### Examples

```xquery
xdmp:type(3)
=>
integer
```

---

## xdmp:user-last-login

Returns the last-login node for the current user. If no last-login
  database is specified in the App Server configuration, then the empty
  sequence is returned.

### Returns

`element(last-login)?`

### Examples

```xquery
xdmp:user-last-login()
  => 
  <last-login xmlns="http://marklogic.com/xdmp/last-login">
    <user-id>1134406269933351074</user-id>
    <last-successful-login>2008-03-19T15:41:08</last-successful-login>
    <last-unsuccessful-login>2008-03-19T15:40:45</last-unsuccessful-login>
    <number-unsuccessful-logins>0</number-unsuccessful-logins>
    <display-last-login>true</display-last-login>
  </last-login>
```

---

## xdmp:wallclock-to-timestamp

Converts an xs:dateTime to a 64 bit timestamp value.

### Signature

```xquery
xdmp:wallclock-to-timestamp(
  $timestamp as xs:dateTime
) as xs:unsignedLong
```

### Parameters

**`$timestamp`**
The xs:datetime value.

### Returns

`xs:unsignedLong`

### Examples

```xquery
xdmp:wallclock-to-timestamp(xs:dateTime("2000-01-11T12:01:00"))
=> 9476208600000000
```

---

## xdmp:xor64

XOR two 64-bit integer values.

### Signature

```xquery
xdmp:xor64(
  $x as xs:unsignedLong,
  $y as xs:unsignedLong
) as xs:unsignedLong
```

### Parameters

**`$x`**
The first value.

**`$y`**
The second value.

### Returns

`xs:unsignedLong`

### Examples

```xquery
xdmp:xor64(255, 2)
=> 253
```

---
