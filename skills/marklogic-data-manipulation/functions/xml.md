# Xml

2 functions in this category.

## xdmp:quote

Returns the unevaluated serialized representation
  of the input parameter as a string.

### Signature

```xquery
xdmp:quote(
  $arg as item()*,
  $options as (element()|map:map)??
) as xs:string
```

### Parameters

**`$arg`**
Input to be quoted.

**`$options`** *(optional)*
Options with which to customize this operation.
    You can specify options as either an XML element
    in the "xdmp:quote" namespace, or as a map:map. The
    options names below are XML element localnames. When using a map,
    replace the hyphens with camel casing. For example, "an-option"
    becomes "anOption" when used as a map:map key.
    This function supports the following options:
    
      
	<output-encoding>
      
      Specifies the encoding to use for this quote operation. This is
      only used to escape characters that cannot be represented.
      
	<output-sgml-character-entities>
      
      Specifies if character entities should be output upon serialization
      of the XML.  Valid values are normal, none,
      math, and pub. By default (that is, if this
      option is not specified), no SGML entities are serialized on output,
      unless the App Server is configured to output SGML character
      entities.
      
	<method>
      
 Valid values are listed in xdmp:output in the XQuery and XSLT Reference Guide.
      This is like the corresponding part of both
      the XSLT 
      xsl:output instruction.
      and the MarkLogic XQuery xdmp:output prolog statement.
      
      
	<cdata-section-elements>
      
      A list of space-separated
       QNames to output
      as CDATA sections. This is like the corresponding part of both the XSLT
      
      xsl:output instruction and the MarkLogic XQuery
      xdmp:output prolog statement.
      
      
	<encoding>
      
      The encoding.
      This is like the corresponding part of both
      the XSLT 
      xsl:output
      instruction
       and the MarkLogic XQuery
      xdmp:output prolog statement.
      
      
	<use-character-maps>
      
      One or more of the following values, separated by spaces.
      
      Valid values are
      xdmp:sgml-entities-normal,
      
      xdmp:sgml-entities-math,
      
      and
      xdmp:sgml-entities-pub.
      
      This is like the corresponding part of both
      the XSLT 
      xsl:output instruction and the MarkLogic XQuery
      prolog statement.
      
      
	<media-type>
      
      A mimetype representing a media type. For example,
      text/plain or application/xml (or other valid
      mimetypes).
      This is like the corresponding part of both
      the XSLT 
      xsl:output instruction and the MarkLogic XQuery
      xdmp:output prolog statement.
      
      
	<byte-order-mark>
      
      Valid values are yes or no.
      This is like the corresponding part of both
      the XSLT 
      xsl:output
      
      instruction
       and the MarkLogic XQuery
      xdmp:output prolog statement.
      
      
	<indent>
      
      Specifies if typed XML (that is, XML for which there is an
      in-scope schema) should be pretty-printed (indented).  Valid
      values are yes or no.
      This is like the corresponding part of both
      the XSLT 
      xsl:output
      
      instruction
       and the MarkLogic XQuery
      xdmp:output prolog statement.
      
      
	<indent-untyped>
      
      Specifies if untyped XML (that is, XML for which there is no
      in-scope schema) should be pretty-printed (indented).  Valid
      values are yes or no.
      This is like the corresponding part of both
      the XSLT 
      xsl:output
      
      instruction
       and the MarkLogic XQuery
      xdmp:output prolog statement.
      
      
	<indent-tabs>
      
      Specifies if tab characters should be used instead of 8 consecutive
      spaces when indenting.  Valid values are yes or no.
      
      
	<include-content-type>
      
      Include the content-type declaration when serializing the node.
      Valid values are
      yes or no.
      
	<escape-uri-attributes>
      
      Valid values are yes or no.
      This is like the corresponding part of both
      the XSLT 
      xsl:output
      
      instruction
       and the MarkLogic XQuery
      xdmp:output prolog statement.
      
      
	<doctype-public>
      
      A public identifier, which is the public identifier to use on the
      emitted DOCTYPE.
      This is like the corresponding part of both
      the XSLT 
      xsl:output
      
      instruction
       and the MarkLogic XQuery
      xdmp:output prolog statement.
      
      
	<doctype-system>
      
      A system identifier, which is the system identifier to use on the
      emitted DOCTYPE.
      This is like the corresponding part of both
      the XSLT 
      xsl:output
      
      instruction
       and the MarkLogic XQuery
      xdmp:output prolog statement.
      
      
	<omit-xml-declaration>
      
      Valid values are yes or no.
      This is like the corresponding part of both
      the XSLT 
      xsl:output
      
      instruction
       and the MarkLogic XQuery
      xdmp:output prolog statement.
      
      
	<standalone>
      
      Valid values are yes or no.
      This is like the corresponding part of both
      the XSLT 
      xsl:output
      
      instruction
       and the MarkLogic XQuery
      xdmp:output prolog statement.
      
      
	<normalization-form>
      
      Valid values are NFC, NFD,
      and NFKD.
      This is like the corresponding part of both
      the XSLT 
      xsl:output
      
      instruction
       and the MarkLogic XQuery
      xdmp:output prolog statement.
      
      
	<default-attributes>
      
      Specifies whether attributes defaulted with a schema should be
      included in the serialization.
      Valid values are yes or no.
      This is like the corresponding part of both
      the XSLT 
      xsl:output
      
      instruction
       and the MarkLogic XQuery
      xdmp:output prolog statement.

### Returns

`xs:string`

### Examples

#### Example 1

```xquery
let $arg := <a>aaa</a>
return ($arg, xdmp:quote($arg))

(: returns the following output:
   (<a>aaa</a>, "<a>aaa</a>")
 :)
```

#### Example 2

```xquery
xquery version "1.0-ml";

let $input-node := <parent><child>content</child></parent>
let $options :=
  <options xmlns="xdmp:quote">
    <indent-untyped>yes</indent-untyped>
    <omit-xml-declaration>no</omit-xml-declaration>
  </options>
return xdmp:quote($input-node, $options)

(: Returns the following (as a string value):
    <?xml version="1.0" encoding="UTF-8"?>
    <parent>
      <child>content</child>
    </parent>
 :)
```

#### Example 3

```xquery
xquery version "1.0-ml";

let $input-node := <parent><child>content</child></parent>
let $options := 
  map:map() => map:with("indentUntyped", "yes")
            => map:with("omitXmlDeclaration", "no")
return xdmp:quote($input-node, $options)

(: Returns the following (as a string value):
    <?xml version="1.0" encoding="UTF-8"?>
    <parent>
      <child>content</child>
    </parent>
 :)
```

---

## xdmp:unquote

Parses a string as XML, returning one or more document nodes.

### Signature

```xquery
xdmp:unquote(
  $arg as xs:string,
  $default-namespace as xs:string??,
  $options as xs:string*?
) as document-node()+
```

### Parameters

**`$arg`**
Input to be unquoted.

**`$default-namespace`** *(optional)*
Default namespace for nodes in the first parameter.

**`$options`** *(optional)*
The options for getting this document.
    The default value is ().
    Options include:
    
    "repair-full"
    Specifies that malformed XML content be repaired.
        XML content with multiple top-level elements will be
        parsed as multiple documents.
        This option has no effect on binary or text documents.
    "repair-none"
    Specifies that malformed XML content be rejected.
        XML content will be parsed as a single document, so
        a maximum of one document node will be returned.
        This option has no effect on binary or text documents.
    "format-text"
    Specifies to get the document as a text document,
        regardless of the URI specified.
    "format-binary"
    Specifies to get the document as a binary document,
        regardless of the URI specified.
    "format-xml"
    Specifies to get the document as an XML document,
        regardless of the URI specified.
    "format-json"
    Specifies to get the document as a JSON document,
        regardless of the URI specified.
    "default-language=xx"
     If the root element node specified in the first parameter does not
    already have an xml:lang attribute, the language to
    specify in an xml:lang attribute on the root element node.
    If default-language is not specified, then nothing is
    added to the root element node. Some examples are
    default-language=en and default-language=fr.

### Returns

`document-node()+`

### Usage Notes

If no format is specified in $options, it is inferred from the input.
  If the first non-whitespace character is either '{' or '[' it is JSON.
  Otherwise it is XML.
      If neither "repair-full" nor "repair-none" is present,
  the default is specified by the XQuery version of the caller.
  In XQuery version 1.0 and 1.0-ml the default is
  "repair-none".  In XQuery version 0.9-ml the default is
  "repair-full".
      If $arg is the empty string, xdmp:unquote returns an empty
  document node.

### Examples

#### Example 1

```xquery
xdmp:unquote("<foo/>")
=> <foo/>
  It returns this as a document node.
```

#### Example 2

```xquery
xdmp:unquote('<foo>hello</foo>', "",
          ("repair-none", "default-language=en"))
  => <foo xml:lang="en">hello</foo>
  It returns this as a document node and does
  not perform tag repair on the node.
```

---
