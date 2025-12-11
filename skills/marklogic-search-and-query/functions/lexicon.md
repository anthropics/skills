# Lexicon

48 functions in this category.

## cts:collection-match

Returns values from the collection lexicon
   that match the specified wildcard pattern.
   This function requires the collection-lexicon database configuration
   parameter to be enabled. If the collection lexicon database configuration
   parameter is not enabled, an exception is thrown.

### Signature

```xquery
cts:collection-match(
  $pattern as xs:string,
  $options as xs:string*?,
  $query as cts:query??,
  $quality-weight as xs:double??,
  $forest-ids as xs:unsignedLong*?
) as xs:string*
```

### Parameters

**`$pattern`**
Wildcard pattern to match.

**`$options`** *(optional)*
Options.  The default is ().
    
      Options include:
      
        "case-sensitive"
        A case-sensitive match.
        "case-insensitive"
        A case-insensitive match.
        "diacritic-sensitive"
        A diacritic-sensitive match.
        "diacritic-insensitive"
        A diacritic-insensitive match.
        "ascending"
        URIs should be returned in ascending order.
        "descending"
        URIs should be returned in descending order.
        "any"
        URIs from any fragment should be included.
        "document"
        URIs from document fragments should be included.
        "properties"
        URIs from properties fragments should be included.
        "locks"
        URIs from locks fragments should be included.
        "frequency-order"
        URIs should be returned ordered by frequency.
        "item-order"
        URIs should be returned ordered by item.
        "limit=N"
        Return no more than N collections. You should not
        use this option with the "skip" option. Use "truncate" instead.
        "skip=N"
        Skip over fragments selected by the cts:query
        to treat the Nth fragment as the first fragment.
        URIs from skipped fragments are not included.
        This option affects the number of fragments selected
        by the cts:query to calculate frequencies.
        Only applies when a $query parameter is specified.
        "sample=N"
        Return only URIs from the first N fragments after
        skip selected by the cts:query.
        This option does not affect the number of fragments selected
        by the cts:query to calculate frequencies.
        Only applies when a $query parameter is specified.
        "truncate=N"
        Include only URIs from the first N fragments after
        skip selected by the cts:query.
        This option also affects the number of fragments selected
        by the cts:query to calculate frequencies.
        Only applies when a $query parameter is specified.
        "score-logtfidf"
        Compute scores using the logtfidf method.
        Only applies when a $query parameter is specified.
        "score-logtf"
        Compute scores using the logtf method.
        Only applies when a $query parameter is specified.
        "score-simple"
        Compute scores using the simple method.
        Only applies when a $query parameter is specified.
        "score-random"
        Compute scores using the random method.
        Only applies when a $query parameter is specified.
        "score-zero"
        Compute all scores as zero.
        Only applies when a $query parameter is specified.
        "checked"
        Word positions should be checked when resolving the query.
        "unchecked"
        Word positions should not be checked when resolving the query.
        "too-many-positions-error"
        If too much memory is needed to perform positions calculations
        to check whether a document matches a query,
        return an XDMP-TOOMANYPOSITIONS error,
        instead of accepting the document as a match.
        "eager"
        Perform most of the work concurrently before returning
        the first item from the indexes, and only some of the work
        sequentially while iterating through the rest of the items.
        This usually takes the shortest time for a complete item-order
        result or for any frequency-order result.
        "lazy"
        Perform only some the work concurrently before returning
        the first item from the indexes, and most of the work
        sequentially while iterating through the rest of the items.
        This usually takes the shortest time for a small item-order
        partial result.
        "concurrent"
        Perform the work concurrently in another thread. This is a hint
        to the query optimizer to help parallelize the lexicon work, allowing
        the calling query to continue performing other work while the lexicon
        processing occurs.  This is especially useful in cases where multiple
        lexicon calls occur in the same query (for example, resolving many
        facets in a single query).
        "map"
        Return results as a single map:map
         value instead of as an xs:string* sequence
         .

**`$query`** *(optional)*
Only include URIs from fragments selected by the cts:query,
    and compute frequencies from this set of included URIs.
    The fragments are not filtered to ensure they match the query,
    but instead selected in the same manner as
    
    "unfiltered" cts:search
    
    operations.  If a string
   is entered, the string is treated as a cts:word-query of the
   specified string.

**`$quality-weight`** *(optional)*
A document quality weight to use when computing scores.
    The default is 1.0.

**`$forest-ids`** *(optional)*
A sequence of IDs of forests to which the search will be constrained.
    An empty sequence means to search all forests in the database.
    The default is ().

### Returns

`xs:string*`

### Usage Notes

Only one of "frequency-order" or "item-order" may be specified
  in the options parameter.  If neither "frequency-order" nor "item-order"
  is specified, then the default is "item-order".
      Only one of "ascending" or "descending" may be specified
  in the options parameter.  If neither "ascending" nor "descending"
  is specified, then the default is "ascending" if "item-order" is
  specified, and "descending" if "frequency-order" is specified.
      Only one of "eager" or "lazy" may be specified
  in the options parameter.  If neither "eager" nor "lazy"
  is specified, then the default is "lazy" if "item-order" is
  specified, and "eager" if "frequency-order" is specified.
      Only one of "any", "document", "properties", or "locks"
  may be specified in the options parameter.
  If none of "any", "document", "properties", or "locks" are specified
  and there is a $query parameter, then the default is "document".
  If there is no $query parameter then the default is "any".
      Only one of the "score-logtfidf", "score-logtf", "score-simple",
  "score-random", or "score-zero" options may be specified in the options
  parameter.
  If none of "score-logtfidf", "score-logtf", "score-simple", "score-random",
  or "score-zero" are specified, then the default is "score-logtfidf".
      Only one of the "checked" or "unchecked" options may be specified
  in the options parameter.
  If neither "checked" nor "unchecked" are specified,
  then the default is "checked".
      If "sample=N" is not specified in the options parameter,
  then all included URIs may be returned. If a $query parameter
  is not present, then "sample=N" has no effect.
      If "truncate=N" is not specified in the options parameter,
  then URIs from all fragments selected by the $query parameter
  are included.  If a $query parameter is not present, then
  "truncate=N" has no effect.
      To incrementally fetch a subset of the values returned by this function,
  use fn:subsequence
  
  on the output, rather than 
  the "skip" option. The "skip" option is based on fragments matching the 
  query parameter (if present), not on values. A fragment 
  matched by query might contain multiple values or no values. 
  The number of fragments skipped does not correspond to the number of 
  values. Also, the skip is applied to the relevance ordered query matches, 
  not to the ordered values list. 
      When using the "skip" option, use the "truncate" option rather than 
  the "limit" option to control the number of matching fragments from which 
  to draw values.
      
    If neither "case-sensitive" nor "case-insensitive"
    is present, $pattern is used to determine case sensitivity.
    If $pattern contains no uppercase, it specifies "case-insensitive".
    If $pattern contains uppercase, it specifies "case-sensitive".
  
      
    If neither "diacritic-sensitive" nor "diacritic-insensitive"
    is present, $pattern is used to determine diacritic sensitivity.
    If $pattern contains no diacritics, it specifies "diacritic-insensitive".
    If $pattern contains diacritics, it specifies "diacritic-sensitive".

### Examples

```xquery
cts:collection-match("collection*")
  => ("collection1", "collection2", ...)
```

---

## cts:collection-reference

Creates a reference to the collection lexicon, for use as a parameter to
  cts:value-tuples.  Since lexicons are implemented with range indexes,
  this function will throw an exception if the specified range index does
  not exist.

### Signature

```xquery
cts:collection-reference(
  $options as xs:string*?
) as cts:reference
```

### Parameters

**`$options`** *(optional)*
Options.  The default is ().
    
      Options include:
      
        "nullable"
        Allow null values in tuples reported from cts:value-tuples when
        using this lexicon.
        "unchecked"
        Do not check the definition against the context database.

### Returns

`cts:reference`

### Examples

```xquery
cts:collection-reference()
=>
cts:collection-reference(())
```

---

## cts:collections

Returns values from the collection lexicon.
  This function requires the collection-lexicon database configuration
  parameter to be enabled. If the collection-lexicon database-configuration
  parameter is not enabled, an exception is thrown.

### Signature

```xquery
cts:collections(
  $start as xs:string??,
  $options as xs:string*?,
  $query as cts:query??,
  $quality-weight as xs:double??,
  $forest-ids as xs:unsignedLong*?
) as xs:string*
```

### Parameters

**`$start`** *(optional)*
A starting value.  Return only this value and following values.
    If the parameter is not in the lexicon, then it returns the values
    beginning with the next value.

**`$options`** *(optional)*
Options.  The default is ().
    
      Options include:
      
        "ascending"
        URIs should be returned in ascending order.
        "descending"
        URIs should be returned in descending order.
        "any"
        URIs from any fragment should be included.
        "document"
        URIs from document fragments should be included.
        "properties"
        URIs from properties fragments should be included.
        "locks"
        URIs from locks fragments should be included.
        "frequency-order"
        URIs should be returned ordered by frequency.
        "item-order"
        URIs should be returned ordered by item.
        "limit=N"
        Return no more than N URIs. You should not
        use this option with the "skip" option. Use "truncate" instead.
        "skip=N"
        Skip over fragments selected by the cts:query
        to treat the Nth fragment as the first fragment.
        URIs from skipped fragments are not included.
        This option affects the number of fragments selected
        by the cts:query to calculate frequencies.
        Only applies when a $query parameter is specified.
        "sample=N"
        Return only URIs from the first N fragments after
        skip selected by the cts:query.
        This option does not affect the number of fragments selected
        by the cts:query to calculate frequencies.
        Only applies when a $query parameter is specified.
        "truncate=N"
        Include only URIs from the first N fragments after
        skip selected by the cts:query.
        This option also affects the number of fragments selected
        by the cts:query to calculate frequencies.
        Only applies when a $query parameter is specified.
        "score-logtfidf"
        Compute scores using the logtfidf method.
        Only applies when a $query parameter is specified.
        "score-logtf"
        Compute scores using the logtf method.
        Only applies when a $query parameter is specified.
        "score-simple"
        Compute scores using the simple method.
        Only applies when a $query parameter is specified.
        "score-random"
        Compute scores using the random method.
        Only applies when a $query parameter is specified.
        "score-zero"
        Compute all scores as zero.
        Only applies when a $query parameter is specified.
        "checked"
        Word positions should be checked when resolving the query.
        "unchecked"
        Word positions should not be checked when resolving the query.
        "too-many-positions-error"
        If too much memory is needed to perform positions calculations
        to check whether a document matches a query,
        return an XDMP-TOOMANYPOSITIONS error,
        instead of accepting the document as a match.
        "eager"
        Perform most of the work concurrently before returning
        the first item from the indexes, and only some of the work
        sequentially while iterating through the rest of the items.
        This usually takes the shortest time for a complete item-order
        result or for any frequency-order result.
        "lazy"
        Perform only some the work concurrently before returning
        the first item from the indexes, and most of the work
        sequentially while iterating through the rest of the items.
        This usually takes the shortest time for a small item-order
        partial result.
        "concurrent"
        Perform the work concurrently in another thread. This is a hint
        to the query optimizer to help parallelize the lexicon work, allowing
        the calling query to continue performing other work while the lexicon
        processing occurs.  This is especially useful in cases where multiple
        lexicon calls occur in the same query (for example, resolving many
        facets in a single query).
        "map"
        Return results as a single map:map
         value instead of as an xs:string* sequence
         .

**`$query`** *(optional)*
Only include URIs from fragments selected by the cts:query,
    and compute frequencies from this set of included URIs.
    The fragments are not filtered to ensure they match the query,
    but instead selected in the same manner as
    
    "unfiltered" cts:search
    
    operations.  If a string
   is entered, the string is treated as a cts:word-query of the
   specified string.

**`$quality-weight`** *(optional)*
A document quality weight to use when computing scores.
    The default is 1.0.

**`$forest-ids`** *(optional)*
A sequence of IDs of forests to which the search will be constrained.
    An empty sequence means to search all forests in the database.
    The default is ().

### Returns

`xs:string*`

### Usage Notes

Only one of "frequency-order" or "item-order" may be specified
  in the options parameter.  If neither "frequency-order" nor "item-order"
  is specified, then the default is "item-order".
      Only one of "ascending" or "descending" may be specified
  in the options parameter.  If neither "ascending" nor "descending"
  is specified, then the default is "ascending" if "item-order" is
  specified, and "descending" if "frequency-order" is specified.
      Only one of "eager" or "lazy" may be specified
  in the options parameter.  If neither "eager" nor "lazy"
  is specified, then the default is "lazy" if "item-order" is
  specified, and "eager" if "frequency-order" is specified.
      Only one of "any", "document", "properties", or "locks"
  may be specified in the options parameter.
  If none of "any", "document", "properties", or "locks" are specified
  and there is a $query parameter, then the default is "document".
  If there is no $query parameter then the default is "any".
      Only one of the "score-logtfidf", "score-logtf", "score-simple",
  "score-random", or "score-zero" options may be specified in the options
  parameter.
  If none of "score-logtfidf", "score-logtf", "score-simple", "score-random",
  or "score-zero" are specified, then the default is "score-logtfidf".
      Only one of the "checked" or "unchecked" options may be specified
  in the options parameter.
  If neither "checked" nor "unchecked" are specified,
  then the default is "checked".
      If "sample=N" is not specified in the options parameter,
  then all included words may be returned. If a $query parameter
  is not present, then "sample=N" has no effect.
      If "truncate=N" is not specified in the options parameter,
  then words from all fragments selected by the $query parameter
  are included.  If a $query parameter is not present, then
  "truncate=N" has no effect.
      To incrementally fetch a subset of the values returned by this function,
  use fn:subsequence
  
  on the output, rather than 
  the "skip" option. The "skip" option is based on fragments matching the 
  query parameter (if present), not on values. A fragment 
  matched by query might contain multiple values or no values. 
  The number of fragments skipped does not correspond to the number of 
  values. Also, the skip is applied to the relevance ordered query matches, 
  not to the ordered values list. 
      When using the "skip" option, use the "truncate" option rather than 
  the "limit" option to control the number of matching fragments from which 
  to draw values.

### Examples

```xquery
cts:collections("aardvark")
  => ("aardvark", "aardvarks", ...)
```

---

## cts:element-attribute-reference

Creates a reference to an element attribute value lexicon, for use as a
  parameter to cts:value-tuples.  Since lexicons are implemented with range
  indexes, this function will throw an exception if the specified range index
  does not exist.

### Signature

```xquery
cts:element-attribute-reference(
  $element as xs:QName,
  $attribute as xs:QName,
  $options as xs:string*?
) as cts:reference
```

### Parameters

**`$element`**
An element QName.

**`$attribute`**
An attribute QName.

**`$options`** *(optional)*
Options.  The default is ().
    
      Options include:
      
        "type=type"
        Use the lexicon with the type specified by type
        (int, unsignedInt, long, unsignedLong, float, double, decimal,
        dateTime, time, date, gYearMonth, gYear, gMonth, gDay,
        yearMonthDuration, dayTimeDuration, string, anyURI, point, or
        long-lat-point)
        "collation=URI"
        Use the lexicon with the collation specified by URI.
        "nullable"
        Allow null values in tuples reported from cts:value-tuples when
        using this lexicon.
        "unchecked"
        Read the scalar type, collation and coordinate-system info
        only from the input. Do not check the definition against the
        context database.
        "coordinate-system=name"
        Create a reference to an index or lexicon based on the specified
         coordinate system. Allowed values: "wgs84", "wgs84/double", "raw",
         "raw/double". Only applicable if the index/lexicon value type is
         point or long-lat-point.
        "precision=value"
        Create a reference to an index or lexicon configured with the
         specified geospatial precision. Allowed values: float
         and double. Only applicable if the index/lexicon value
         type is point or long-lat-point. This
         value takes precedence over the precision implicit in the coordinate
         system name.

### Returns

`cts:reference`

### Examples

```xquery
cts:element-attribute-reference(xs:QName("SONG"), xs:QName("rating"));
=>
cts:element-reference(fn:QName("", "SONG"), fn:QName("","rating"),
   ("type=int") )
```

---

## cts:element-attribute-value-co-occurrences

Returns value co-occurrences from the specified element or element-attribute
  value lexicon(s).
  Value lexicons are implemented using range indexes;
  consequently this function requires a range index for each element/attribute
  pairs specified in the function.
  If there is not a range index configured for each of the specified
  element or element/attribute pairs, then an exception is thrown.

### Signature

```xquery
cts:element-attribute-value-co-occurrences(
  $element-name-1 as xs:QName,
  $attribute-name-1 as xs:QName?,
  $element-name-2 as xs:QName,
  $attribute-name-2 as xs:QName?,
  $options as xs:string*?,
  $query as cts:query??,
  $quality-weight as xs:double??,
  $forest-ids as xs:unsignedLong*?
) as element(cts:co-occurrence)*
```

### Parameters

**`$element-name-1`**
An element QName.

**`$attribute-name-1`**
An attribute QName or empty sequence.
    The empty sequence specifies an element lexicon.

**`$element-name-2`**
An element QName.

**`$attribute-name-2`**
An attribute QName or empty sequence.
    The empty sequence specifies an element lexicon.

**`$options`** *(optional)*
Options.  The default is ().
    
      Options include:
      
        "ascending"
        Co-occurrences should be returned in ascending order.
        "descending"
        Co-occurrences should be returned in descending order.
        "any"
        Co-occurrences from any fragment should be included.
        "document"
        Co-occurrences from document fragments should be included.
        "properties"
        Co-occurrences from properties fragments should be included.
        "locks"
        Co-occurrences from locks fragments should be included.
        "frequency-order"
        Co-occurrences should be returned ordered by frequency.
        "item-order"
        Co-occurrences should be returned ordered by item.
        "fragment-frequency"
        Frequency should be the number of fragments with
        an included co-occurrences.
        This option is used with cts:frequency.
        "item-frequency"
        Frequency should be the number of occurrences of
        an included co-occurrence.
        This option is used with cts:frequency.
        "type=type"
        For both lexicons, use the type specified by type
        (int, unsignedInt, long, unsignedLong, float, double, decimal,
        dateTime, time, date, gYearMonth, gYear, gMonth, gDay,
        yearMonthDuration, dayTimeDuration, string, or anyURI)
        "type-1=type"
        For the first lexicon, use the type specified by type
        (int, unsignedInt, long, unsignedLong, float, double, decimal,
        dateTime, time, date, gYearMonth, gYear, gMonth, gDay,
        yearMonthDuration, dayTimeDuration, string, or anyURI)
        "type-2=type"
        For the second lexicon, use the type specified by type
        (int, unsignedInt, long, unsignedLong, float, double, decimal,
        dateTime, time, date, gYearMonth, gYear, gMonth, gDay,
        yearMonthDuration, dayTimeDuration, string, or anyURI)
        "collation=URI"
        For both lexicons, use the collation specified by
        URI.
        "collation-1=URI"
        For the first lexicon, use the collation specified by
        URI.
        "collation-2=URI"
        For the second lexicon, use the collation specified by
        URI.
        "timezone=TZ"
        Return timezone sensitive values (dateTime, time, date,
        gYearMonth, gYear, gMonth, and gDay) adjusted to the timezone
        specified by TZ.
        Example timezones: Z, -08:00, +01:00.
        "ordered"
        Include co-occurrences only when the value from the first lexicon
        appears before the value from the second lexicon.
        Requires that word positions be enabled for both lexicons.
        "proximity=N"
        Include co-occurrences only when the values appear within
        N words of each other.
        Requires that word positions be enabled for both lexicons.
        "limit=N"
        Return no more than N co-occurrences. You should not
        use this option with the "skip" option. Use "truncate" instead.
        "skip=N"
        Skip over fragments selected by the cts:query
        to treat the Nth fragment as the first fragment.
        Co-occurrences from skipped fragments are not included.
        This option affects the number of fragments selected
        by the cts:query to calculate frequencies.
        Only applies when a $query parameter is specified.
        "sample=N"
        Return only co-occurrences from the first N
        fragments after skip selected by the cts:query.
        This option does not affect the number of fragments selected
        by the cts:query to calculate frequencies.
        Only applies when a $query parameter is specified.
        "truncate=N"
        Include only co-occurrences from the first N
        fragments after skip selected by the cts:query.
        This option also affects the number of fragments selected
        by the cts:query to calculate frequencies.
        Only applies when a $query parameter is specified.
        "score-logtfidf"
        Compute scores using the logtfidf method.
        Only applies when a $query parameter is specified.
        "score-logtf"
        Compute scores using the logtf method.
        Only applies when a $query parameter is specified.
        "score-simple"
        Compute scores using the simple method.
        Only applies when a $query parameter is specified.
        "score-random"
        Compute scores using the random method.
        Only applies when a $query parameter is specified.
        "score-zero"
        Compute all scores as zero.
        Only applies when a $query parameter is specified.
        "checked"
        Word positions should be checked when resolving the query.
        "unchecked"
        Word positions should not be checked when resolving the query.
        "too-many-positions-error"
        If too much memory is needed to perform positions calculations
        to check whether a document matches a query,
        return an XDMP-TOOMANYPOSITIONS error,
        instead of accepting the document as a match.
        "eager"
        Perform most of the work concurrently before returning
        the first item from the indexes, and only some of the work
        sequentially while iterating through the rest of the items.
        This usually takes the shortest time for a complete item-order
        result or for any frequency-order result.
        "lazy"
        Perform only some the work concurrently before returning
        the first item from the indexes, and most of the work
        sequentially while iterating through the rest of the items.
        This usually takes the shortest time for a small item-order
        partial result.
        "concurrent"
        Perform the work concurrently in another thread. This is a hint
        to the query optimizer to help parallelize the lexicon work, allowing
        the calling query to continue performing other work while the lexicon
        processing occurs.  This is especially useful in cases where multiple
        lexicon calls occur in the same query (for example, resolving many
        facets in a single query).
        "map"
        Return results as a single map:map
         value instead of as an element(cts:co-occurrence)* sequence
         .
        "coordinate-system=name"
        Use the lexicon that is configured with the specified coordinate
         system. Allowed values: "wgs84", "wgs84/double", "raw",
         "raw/double". Only applicable if the lexicon value type is
         point or long-lat-point.
        "precision=value"
        Use the lexicon that is configured with the specified precision.
         Allowed values: float and double.
         Only applicable if the lexicon value type is point or
         long-lat-point. This value takes precedence over the
         precision implicit in the coordinate system name.

**`$query`** *(optional)*
Only include co-occurrences in fragments selected by the
    cts:query,
    and compute frequencies from this set of included co-occurrences.
    The co-occurrences do not need to match the query, but they must occur in
    fragments selected by the query.
    The fragments are not filtered to ensure they match the query,
    but instead selected in the same manner as
    
    "unfiltered" cts:search
    
    operations.  If a string
   is entered, the string is treated as a cts:word-query of the
   specified string.

**`$quality-weight`** *(optional)*
A document quality weight to use when computing scores.
    The default is 1.0.

**`$forest-ids`** *(optional)*
A sequence of IDs of forests to which the search will be constrained.
    An empty sequence means to search all forests in the database.
    The default is ().

### Returns

`element(cts:co-occurrence)*`

### Usage Notes

Only one of "frequency-order" or "item-order" may be specified
  in the options parameter.  If neither "frequency-order" nor "item-order"
  is specified, then the default is "item-order".
      Only one of "fragment-frequency" or "item-frequency" may be specified
  in the options parameter.  If neither "fragment-frequency" nor
  "item-frequency" is specified, then the default is "fragment-frequency".
      Only one of "ascending" or "descending" may be specified
  in the options parameter.  If neither "ascending" nor "descending"
  is specified, then the default is "ascending" if "item-order" is
  specified, and "descending" if "frequency-order" is specified.
      Only one of "eager" or "lazy" may be specified
  in the options parameter.  If neither "eager" nor "lazy"
  is specified, then the default is "eager" if "frequency-order" or "map"
  is specified, otherwise "lazy".
      Only one of "any", "document", "properties", or "locks"
  may be specified in the options parameter.
  If none of "any", "document", "properties", or "locks" are specified
  and there is a $query parameter, then the default is "document".
  If there is no $query parameter then the default is "any".
      Only one of the "score-logtfidf", "score-logtf", "score-simple",
  "score-random", or "score-zero" options may be specified in the options
  parameter.
  If none of "score-logtfidf", "score-logtf", "score-simple", "score-random",
  or "score-zero" are specified, then the default is "score-logtfidf".
      Only one of the "checked" or "unchecked" options may be specified
  in the options parameter.
  If neither "checked" nor "unchecked" are specified,
  then the default is "checked".
      If "collation=URI" is not specified in the options parameter,
  then the default collation is used. If a lexicon with that collation
  does not exist, an error is thrown.
      If "sample=N" is not specified in the options parameter,
  then all included co-occurrences may be returned.
  If a $query parameter
  is not present, then "sample=N" has no effect.
      If "truncate=N" is not specified in the options parameter,
  then co-occurrences from all fragments selected by the
  $query parameter are included.
  If a $query parameter is not present, then
  "truncate=N" has no effect.
      To incrementally fetch a subset of the co-occurrences returned by this 
  function, use fn:subsequence
  
  on the output, rather than 
  the "skip" option. The "skip" option is based on fragments matching the 
  query parameter (if present), not on occurrences. A fragment 
  matched by query might contain multiple occurrences or no occurrences. 
  The number of fragments skipped does not correspond to the number of 
  values. Also, the skip is applied to the relevance ordered query matches, 
  not to the ordered result list. 
      When using the "skip" option, use the "truncate" option rather than 
  the "limit" option to control the number of matching fragments from which 
  to draw values.

### Examples

```xquery
(:
     This query requires attribute range indexes with positions enabled
     on the following attributes:

        value/@attr1
        value/@attr2
  :)

  (: load documents :)
xdmp:document-insert("/eaco1.xml",
<root>
  <value attr1="value1">text</value>
  <value attr2="value2">other text</value>
</root>),
xdmp:document-insert("/eaco2.xml",
<root>
  <value attr1="value3">text</value>
  <value attr2="value4">other text</value>
</root>);

  (: run co-occurrences query :)
 cts:element-attribute-value-co-occurrences(
    xs:QName("value"),xs:QName("attr1"),
    xs:QName("value"),xs:QName("attr2"),
    ("frequency-order","ordered"))

  =>
<cts:co-occurrence xmlns:cts="http://marklogic.com/cts"
  xmlns:xsi="http://www.w3.org/2001/XMLSchema-instance"
  xmlns:xs="http://www.w3.org/2001/XMLSchema">
  <cts:value xsi:type="xs:string">value1</cts:value>
  <cts:value xsi:type="xs:string">value2</cts:value>
</cts:co-occurrence>
<cts:co-occurrence xmlns:cts="http://marklogic.com/cts"
  xmlns:xsi="http://www.w3.org/2001/XMLSchema-instance"
  xmlns:xs="http://www.w3.org/2001/XMLSchema">
  <cts:value xsi:type="xs:string">value3</cts:value>
  <cts:value xsi:type="xs:string">value4</cts:value>
</cts:co-occurrence>
```

---

## cts:element-attribute-value-match

Returns values from the specified element-attribute value lexicon(s)
   that match the specified pattern.  Element-attribute value lexicons are
   implemented using range indexes; consequently this function requires an
   attribute range index for each of the element/attribute pairs specified
   in the function.  If there is not a range index configured for each of the
   specified element/attribute pairs, then an exception is thrown.

### Signature

```xquery
cts:element-attribute-value-match(
  $element-names as xs:QName*,
  $attribute-names as xs:QName*,
  $pattern as xs:anyAtomicType,
  $options as xs:string*?,
  $query as cts:query??,
  $quality-weight as xs:double??,
  $forest-ids as xs:unsignedLong*?
) as xs:anyAtomicType*
```

### Parameters

**`$element-names`**
One or more element QNames.

**`$attribute-names`**
One or more attribute QNames.

**`$pattern`**
A pattern to match.  The parameter type must match the lexicon type.
    String parameters may include wildcard characters.

**`$options`** *(optional)*
Options.  The default is ().
    
      Options include:
      
        "case-sensitive"
        A case-sensitive match.
        "case-insensitive"
        A case-insensitive match.
        "diacritic-sensitive"
        A diacritic-sensitive match.
        "diacritic-insensitive"
        A diacritic-insensitive match.
        "ascending"
        Values should be returned in ascending order.
        "descending"
        Values should be returned in descending order.
        "any"
        Values from any fragment should be included.
        "document"
        Values from document fragments should be included.
        "properties"
        Values from properties fragments should be included.
        "locks"
        Values from locks fragments should be included.
        "frequency-order"
        Values should be returned ordered by frequency.
        "item-order"
        Values should be returned ordered by item.
        "fragment-frequency"
        Frequency should be the number of fragments with
        an included value.
        This option is used with cts:frequency.
        "item-frequency"
        Frequency should be the number of occurrences of
        an included value.
        This option is used with cts:frequency.
        "item-order"
        Values should be returned ordered by item.
        "type=type"
        Use the lexicon with the type specified by type
        (int, unsignedInt, long, unsignedLong, float, double, decimal,
        dateTime, time, date, gYearMonth, gYear, gMonth, gDay,
        yearMonthDuration, dayTimeDuration, string, or anyURI)
        "collation=URI"
        Use the range index with the collation specified by
        URI.
        "timezone=TZ"
        Return timezone sensitive values (dateTime, time, date,
        gYearMonth, gYear, gMonth, and gDay) adjusted to the timezone
        specified by TZ.
        Example timezones: Z, -08:00, +01:00.
        "limit=N"
        Return no more than N values. You should not
        use this option with the "skip" option. Use "truncate" instead.
        "skip=N"
        Skip over fragments selected by the cts:query
        to treat the Nth fragment as the first fragment.
        Values from skipped fragments are not included.
        This option affects the number of fragments selected
        by the cts:query to calculate frequencies.
        Only applies when a $query parameter is specified.
        "sample=N"
        Return only values from the first N
        fragments after skip selected by the cts:query.
        This option does not affect the number of fragments selected
        by the cts:query to calculate frequencies.
        Only applies when a $query parameter is specified.
        "truncate=N"
        Include only values from the first N fragments
        after skip selected by the cts:query.
        This option also affects the number of fragments selected
        by the cts:query to calculate frequencies.
        Only applies when a $query parameter is specified.
        "score-logtfidf"
        Compute scores using the logtfidf method.
        Only applies when a $query parameter is specified.
        "score-logtf"
        Compute scores using the logtf method.
        Only applies when a $query parameter is specified.
        "score-simple"
        Compute scores using the simple method.
        Only applies when a $query parameter is specified.
        "score-random"
        Compute scores using the random method.
        Only applies when a $query parameter is specified.
        "score-zero"
        Compute all scores as zero.
        Only applies when a $query parameter is specified.
        "checked"
        Word positions should be checked when resolving the query.
        "unchecked"
        Word positions should not be checked when resolving the query.
        "too-many-positions-error"
        If too much memory is needed to perform positions calculations
        to check whether a document matches a query,
        return an XDMP-TOOMANYPOSITIONS error,
        instead of accepting the document as a match.
        "eager"
        Perform most of the work concurrently before returning
        the first item from the indexes, and only some of the work
        sequentially while iterating through the rest of the items.
        This usually takes the shortest time for a complete item-order
        result or for any frequency-order result.
        "lazy"
        Perform only some the work concurrently before returning
        the first item from the indexes, and most of the work
        sequentially while iterating through the rest of the items.
        This usually takes the shortest time for a small item-order
        partial result.
        "concurrent"
        Perform the work concurrently in another thread. This is a hint
        to the query optimizer to help parallelize the lexicon work, allowing
        the calling query to continue performing other work while the lexicon
        processing occurs.  This is especially useful in cases where multiple
        lexicon calls occur in the same query (for example, resolving many
        facets in a single query).
        "map"
        Return results as a single map:map
         value instead of as an xs:anyAtomicType* sequence
         .
        "coordinate-system=name"
        Use the lexicon that is configured with the specified coordinate
         system. Allowed values: "wgs84", "wgs84/double", "raw",
         "raw/double". Only applicable if the lexicon value type is
         point or long-lat-point.
        "precision=value"
        Use the lexicon that is configured with the specified precision.
         Allowed values: float and double.
         Only applicable if the lexicon value type is point or
         long-lat-point. This value takes precedence over the
         precision implicit in the coordinate system name.

**`$query`** *(optional)*
Only include values in fragments selected by the cts:query,
    and compute frequencies from this set of included values.
    The values do not need to match the query, but they must occur in
    fragments selected by the query.
    The fragments are not filtered to ensure they match the query,
    but instead selected in the same manner as
    
    "unfiltered" cts:search
    
    operations.  If a string
   is entered, the string is treated as a cts:word-query of the
   specified string.

**`$quality-weight`** *(optional)*
A document quality weight to use when computing scores.
    The default is 1.0.

**`$forest-ids`** *(optional)*
A sequence of IDs of forests to which the search will be constrained.
    An empty sequence means to search all forests in the database.
    The default is ().

### Returns

`xs:anyAtomicType*`

### Usage Notes

Only one of "frequency-order" or "item-order" may be specified
  in the options parameter.  If neither "frequency-order" nor "item-order"
  is specified, then the default is "item-order".
      Only one of "fragment-frequency" or "item-frequency" may be specified
  in the options parameter.  If neither "fragment-frequency" nor
  "item-frequency" is specified, then the default is "fragment-frequency".
      Only one of "ascending" or "descending" may be specified
  in the options parameter.  If neither "ascending" nor "descending"
  is specified, then the default is "ascending" if "item-order" is
  specified, and "descending" if "frequency-order" is specified.
      Only one of "eager" or "lazy" may be specified
  in the options parameter.  If neither "eager" nor "lazy"
  is specified, then the default is "lazy" if "item-order" is
  specified, and "eager" if "frequency-order" is specified.
      Only one of "any", "document", "properties", or "locks"
  may be specified in the options parameter.
  If none of "any", "document", "properties", or "locks" are specified
  and there is a $query parameter, then the default is "document".
  If there is no $query parameter then the default is "any".
      Only one of the "score-logtfidf", "score-logtf", "score-simple",
  "score-random", or "score-zero" options may be specified in the options
  parameter.
  If none of "score-logtfidf", "score-logtf", "score-simple", "score-random",
  or "score-zero" are specified, then the default is "score-logtfidf".
      Only one of the "checked" or "unchecked" options may be specified
  in the options parameter.
  If neither "checked" nor "unchecked" are specified,
  then the default is "checked".
      If "collation=URI" is not specified in the options parameter,
  then the default collation is used. If a range index with that collation
  does not exist, an error is thrown.
      If "sample=N" is not specified in the options parameter,
  then all included values may be returned. If a $query parameter
  is not present, then "sample=N" has no effect.
      If "truncate=N" is not specified in the options parameter,
  then values from all fragments selected by the $query parameter
  are included.  If a $query parameter is not present, then
  "truncate=N" has no effect.
      To incrementally fetch a subset of the values returned by this function,
  use fn:subsequence
  
  on the output, rather than 
  the "skip" option. The "skip" option is based on fragments matching the 
  query parameter (if present), not on values. A fragment 
  matched by query might contain multiple values or no values. 
  The number of fragments skipped does not correspond to the number of 
  values. Also, the skip is applied to the relevance ordered query matches, 
  not to the ordered values list. 
      When using the "skip" option, use the "truncate" option rather than 
  the "limit" option to control the number of matching fragments from which 
  to draw values.
      
    If neither "case-sensitive" nor "case-insensitive"
    is present, $pattern is used to determine case sensitivity.
    If $pattern contains no uppercase, it specifies "case-insensitive".
    If $pattern contains uppercase, it specifies "case-sensitive".
  
      
    If neither "diacritic-sensitive" nor "diacritic-insensitive"
    is present, $pattern is used to determine diacritic sensitivity.
    If $pattern contains no diacritics, it specifies "diacritic-insensitive".
    If $pattern contains diacritics, it specifies "diacritic-sensitive".
  
      When multiple element and/or attribute QNames are specified,
  then all possible element/attribute QName combinations are used
  to select the matching values.

### Examples

```xquery
cts:element-attribute-value-match(xs:QName("animals"),
                     xs:QName("name"),"aardvark*")
  => ("aardvark","aardvarks")
```

---

## cts:element-attribute-value-ranges

Returns value ranges from the specified element-attribute value lexicon(s).
  Element-attribute value lexicons are implemented using indexes;
  consequently this function requires an attribute range index
  of for each of the element/attribute pairs specified in the function.
  If there is not a range index configured for each of the specified
  element/attribute pairs, then an exception is thrown.
      The values are divided into buckets. The $bounds parameter specifies
  the number of buckets and the size of each bucket.
  All included values are bucketed, even those less than the lowest bound
  or greater than the highest bound. An empty sequence for $bounds specifies
  one bucket, a single value specifies two buckets, two values specify
  three buckets, and so on.
      If you have string values and you pass a $bounds parameter
   as in the following call:
      cts:element-value-ranges(xs:QName("myElement"), ("f", "m"))
      The first bucket contains string values that are less than the
  string f, the second bucket contains string values greater than
  or equal to f but less than m, and the third bucket
  contains string values that are greater than or equal to m.
      For each non-empty bucket, a cts:range element is returned.
  Each cts:range element has a cts:minimum child
  and a cts:maximum child.  If a bucket is bounded, its
  cts:range element will also have a
  cts:lower-bound child if it is bounded from below, and
  a cts:upper-bound element if it is bounded from above.
  Empty buckets return nothing unless the "empties" option is specified.

### Signature

```xquery
cts:element-attribute-value-ranges(
  $element-names as xs:QName*,
  $attribute-names as xs:QName*,
  $bounds as xs:anyAtomicType*?,
  $options as xs:string*?,
  $query as cts:query??,
  $quality-weight as xs:double??,
  $forest-ids as xs:unsignedLong*?
) as element(cts:range)*
```

### Parameters

**`$element-names`**
One or more element QNames.

**`$attribute-names`**
One or more attribute QNames.

**`$bounds`** *(optional)*
A sequence of range bounds.
    The types must match the lexicon type.
    The values must be in strictly ascending order.

**`$options`** *(optional)*
Options.  The default is ().
    
      Options include:
      
        "ascending"
        Ranges should be returned in ascending order.
        "descending"
        Ranges should be returned in descending order.
        "empties"
        Include fully-bounded ranges whose frequency is 0. These ranges
        will have no minimum or maximum value.  Only empty ranges that have
        both their upper and lower bounds specified in the $bounds
        options are returned;
        any empty ranges that are less than the first bound or greater than the
        last bound are not returned.  For example, if you specify 4 bounds
        and there are no results for any of the bounds, 3 elements are
        returned (not 5 elements).
        "any"
        Values from any fragment should be included.
        "document"
        Values from document fragments should be included.
        "properties"
        Values from properties fragments should be included.
        "locks"
        Values from locks fragments should be included.
        "frequency-order"
        Ranges should be returned ordered by frequency.
        "item-order"
        Ranges should be returned ordered by item.
        "fragment-frequency"
        Frequency should be the number of fragments with
        an included value.
        This option is used with cts:frequency.
        "item-frequency"
        Frequency should be the number of occurrences of
        an included value.
        This option is used with cts:frequency.
        "type=type"
        Use the lexicon with the type specified by type
        (int, unsignedInt, long, unsignedLong, float, double, decimal,
        dateTime, time, date, gYearMonth, gYear, gMonth, gDay,
        yearMonthDuration, dayTimeDuration, string, or anyURI)
        "collation=URI"
        Use the range index with the collation specified by
        URI.
        "timezone=TZ"
        Return timezone sensitive values (dateTime, time, date,
        gYearMonth, gYear, gMonth, and gDay) adjusted to the timezone
        specified by TZ.
        Example timezones: Z, -08:00, +01:00.
        "limit=N"
        Return no more than N ranges. You should not
        use this option with the "skip" option. Use "truncate" instead.
        "skip=N"
        Skip over fragments selected by the cts:query
        to treat the Nth fragment as the first fragment.
        Values from skipped fragments are not included.
        This option affects the number of fragments selected
        by the cts:query to calculate frequencies.
        Only applies when a $query parameter is specified.
        "sample=N"
        Return only ranges for buckets with at least one value from
        the first N fragments after skip selected by the
        cts:query.
        This option does not affect the number of fragments selected
        by the cts:query to calculate frequencies.
        Only applies when a $query parameter is specified.
        "truncate=N"
        Include only values from the first N fragments
        after skip selected by the cts:query.
        This option also affects the number of fragments selected
        by the cts:query to calculate frequencies.
        Only applies when a $query parameter is specified.
        "score-logtfidf"
        Compute scores using the logtfidf method.
        Only applies when a $query parameter is specified.
        "score-logtf"
        Compute scores using the logtf method.
        Only applies when a $query parameter is specified.
        "score-simple"
        Compute scores using the simple method.
        Only applies when a $query parameter is specified.
        "score-random"
        Compute scores using the random method.
        Only applies when a $query parameter is specified.
        "score-zero"
        Compute all scores as zero.
        Only applies when a $query parameter is specified.
        "checked"
        Word positions should be checked when resolving the query.
        "unchecked"
        Word positions should not be checked when resolving the query.
        "too-many-positions-error"
        If too much memory is needed to perform positions calculations
        to check whether a document matches a query,
        return an XDMP-TOOMANYPOSITIONS error,
        instead of accepting the document as a match.
        "eager"
        Perform most of the work concurrently before returning
        the first item from the indexes, and only some of the work
        sequentially while iterating through the rest of the items.
        This usually takes the shortest time for a complete item-order
        result or for any frequency-order result.
        "lazy"
        Perform only some the work concurrently before returning
        the first item from the indexes, and most of the work
        sequentiallya while iterating through the rest of the items.
        This usually takes the shortest time for a small item-order
        partial result.
        "concurrent"
        Perform the work concurrently in another thread. This is a hint
        to the query optimizer to help parallelize the lexicon work, allowing
        the calling query to continue performing other work while the lexicon
        processing occurs.  This is especially useful in cases where multiple
        lexicon calls occur in the same query (for example, resolving many
        facets in a single query).
        "coordinate-system=name"
        Use the lexicon that is configured with the specified coordinate
         system. Allowed values: "wgs84", "wgs84/double", "raw",
         "raw/double". Only applicable if the lexicon value type is
         point or long-lat-point.
        "precision=value"
        Use the lexicon that is configured with the specified precision.
         Allowed values: float and double.
         Only applicable if the lexicon value type is point or
         long-lat-point. This value takes precedence over the
         precision implicit in the coordinate system name.

**`$query`** *(optional)*
Only include values in fragments selected by the cts:query,
    and compute frequencies from this set of included values.
    The values do not need to match the query, but they must occur in
    fragments selected by the query.
    The fragments are not filtered to ensure they match the query,
    but instead selected in the same manner as
    
    "unfiltered" cts:search
    
    operations.  If a string
   is entered, the string is treated as a cts:word-query of the
   specified string.

**`$quality-weight`** *(optional)*
A document quality weight to use when computing scores.
    The default is 1.0.

**`$forest-ids`** *(optional)*
A sequence of IDs of forests to which the search will be constrained.
    An empty sequence means to search all forests in the database.
    The default is ().

### Returns

`element(cts:range)*`

### Usage Notes

Only one of "frequency-order" or "item-order" may be specified
  in the options parameter.  If neither "frequency-order" nor "item-order"
  is specified, then the default is "item-order".
      Only one of "fragment-frequency" or "item-frequency" may be specified
  in the options parameter.  If neither "fragment-frequency" nor
  "item-frequency" is specified, then the default is "fragment-frequency".
      Only one of "ascending" or "descending" may be specified
  in the options parameter.  If neither "ascending" nor "descending"
  is specified, then the default is "ascending" if "item-order" is
  specified, and "descending" if "frequency-order" is specified.
      Only one of "eager" or "lazy" may be specified
  in the options parameter.  If neither "eager" nor "lazy"
  is specified, then the default is "eager" if "frequency-order" or "empties"
  is specified, otherwise "lazy".
      Only one of "any", "document", "properties", or "locks"
  may be specified in the options parameter.
  If none of "any", "document", "properties", or "locks" are specified
  and there is a $query parameter, then the default is "document".
  If there is no $query parameter then the default is "any".
      Only one of the "score-logtfidf", "score-logtf", "score-simple",
  "score-random", or "score-zero" options may be specified in the options
  parameter.
  If none of "score-logtfidf", "score-logtf", "score-simple", "score-random",
  or "score-zero" are specified, then the default is "score-logtfidf".
      Only one of the "checked" or "unchecked" options may be specified
  in the options parameter.
  If neither "checked" nor "unchecked" are specified,
  then the default is "checked".
      If "collation=URI" is not specified in the options parameter,
  then the default collation is used. If a range index with that collation
  does not exist, an error is thrown.
      If "sample=N" is not specified in the options parameter,
  then ranges with all included values may be returned. If a
  $query parameter is not present, then "sample=N"
  has no effect.
      If "truncate=N" is not specified in the options parameter,
  then values from all fragments selected by the $query parameter
  are included.  If a $query parameter is not present, then
  "truncate=N" has no effect.
      When multiple element and/or attribute QNames are specified,
  then all possible element/attribute QName combinations are used
  to select the matching values.
      To incrementally fetch a subset of the values returned by this function,
  use fn:subsequence
  
  on the output, rather than 
  the "skip" option. The "skip" option is based on fragments matching the 
  query parameter (if present), not on values. A fragment 
  matched by query might contain multiple values or no values. 
  The number of fragments skipped does not correspond to the number of 
  values. Also, the skip is applied to the relevance ordered query matches, 
  not to the ordered results list. 
      When using the "skip" option, use the "truncate" option rather than 
  the "limit" option to control the number of matching fragments from which 
  to draw values.

### Examples

```xquery
(: Run the following to load data for this example.
   Make sure you have an int element attribute
   range index on my-node/@number. :)
for $x in  (1 to 10)
return
xdmp:document-insert(fn:concat("/doc", fn:string($x), ".xml"),
 <root><my-node number={$x}/></root>) ;

(: The following is based on the above setup :)
cts:element-attribute-value-ranges(xs:QName("my-node"),
  xs:QName("number"), (5, 10, 15, 20), "empties")
=>

<cts:range xmlns:cts="http://marklogic.com/cts"
           xmlns:xsi="http://www.w3.org/2001/XMLSchema-instance"
           xmlns:xs="http://www.w3.org/2001/XMLSchema">
  <cts:minimum xsi:type="xs:int">1</cts:minimum>
  <cts:maximum xsi:type="xs:int">4</cts:maximum>
  <cts:upper-bound xsi:type="xs:int">5</cts:upper-bound>
</cts:range>
<cts:range xmlns:cts="http://marklogic.com/cts"
           xmlns:xsi="http://www.w3.org/2001/XMLSchema-instance"
           xmlns:xs="http://www.w3.org/2001/XMLSchema">
  <cts:minimum xsi:type="xs:int">5</cts:minimum>
  <cts:maximum xsi:type="xs:int">9</cts:maximum>
  <cts:lower-bound xsi:type="xs:int">5</cts:lower-bound>
  <cts:upper-bound xsi:type="xs:int">10</cts:upper-bound>
</cts:range>
<cts:range xmlns:cts="http://marklogic.com/cts"
           xmlns:xsi="http://www.w3.org/2001/XMLSchema-instance"
           xmlns:xs="http://www.w3.org/2001/XMLSchema">
  <cts:minimum xsi:type="xs:int">10</cts:minimum>
  <cts:maximum xsi:type="xs:int">10</cts:maximum>
  <cts:lower-bound xsi:type="xs:int">10</cts:lower-bound>
  <cts:upper-bound xsi:type="xs:int">15</cts:upper-bound>
</cts:range>
<cts:range xmlns:cts="http://marklogic.com/cts"
           xmlns:xsi="http://www.w3.org/2001/XMLSchema-instance"
           xmlns:xs="http://www.w3.org/2001/XMLSchema">
  <cts:lower-bound xsi:type="xs:int">15</cts:lower-bound>
  <cts:upper-bound xsi:type="xs:int">20</cts:upper-bound>
</cts:range>
<cts:range xmlns:cts="http://marklogic.com/cts"
           xmlns:xsi="http://www.w3.org/2001/XMLSchema-instance"
           xmlns:xs="http://www.w3.org/2001/XMLSchema">
  <cts:lower-bound xsi:type="xs:int">20</cts:lower-bound>
</cts:range>
```

---

## cts:element-attribute-values

Returns values from the specified element-attribute value lexicon(s).
  Element-attribute value lexicons are implemented using indexes;
  consequently this function requires an attribute range index
  of for each of the element/attribute pairs specified in the function.
  If there is not a range index configured for each of the specified
  element/attribute pairs, then an exception is thrown.

### Signature

```xquery
cts:element-attribute-values(
  $element-names as xs:QName*,
  $attribute-names as xs:QName*,
  $start as xs:anyAtomicType??,
  $options as xs:string*?,
  $query as cts:query??,
  $quality-weight as xs:double??,
  $forest-ids as xs:unsignedLong*?
) as xs:anyAtomicType*
```

### Parameters

**`$element-names`**
One or more element QNames.

**`$attribute-names`**
One or more attribute QNames.

**`$start`** *(optional)*
A starting value.  The parameter type must match the lexicon type.
    If the parameter value is not in the lexicon, then the values are
    returned beginning with the next value.

**`$options`** *(optional)*
Options.  The default is ().
    
      Options include:
      
        "ascending"
        Values should be returned in ascending order.
        "descending"
        Values should be returned in descending order.
        "any"
        Values from any fragment should be included.
        "document"
        Values from document fragments should be included.
        "properties"
        Values from properties fragments should be included.
        "locks"
        Values from locks fragments should be included.
        "frequency-order"
        Values should be returned ordered by frequency.
        "item-order"
        Values should be returned ordered by item.
        "fragment-frequency"
        Frequency should be the number of fragments with
        an included value.
        This option is used with cts:frequency.
        "item-frequency"
        Frequency should be the number of occurrences of
        an included value.
        This option is used with cts:frequency.
        "type=type"
        Use the lexicon with the type specified by type
        (int, unsignedInt, long, unsignedLong, float, double, decimal,
        dateTime, time, date, gYearMonth, gYear, gMonth, gDay,
        yearMonthDuration, dayTimeDuration, string, or anyURI)
        "collation=URI"
        Use the range index with the collation specified by
        URI.
        "timezone=TZ"
        Return timezone sensitive values (dateTime, time, date,
        gYearMonth, gYear, gMonth, and gDay) adjusted to the timezone
        specified by TZ.
        Example timezones: Z, -08:00, +01:00.
        "limit=N"
        Return no more than N values. You should not
        use this option with the "skip" option. Use "truncate" instead.
        "skip=N"
        Skip over fragments selected by the cts:query
        to treat the Nth fragment as the first fragment.
        Values from skipped fragments are not included.
        This option affects the number of fragments selected
        by the cts:query to calculate frequencies.
        Only applies when a $query parameter is specified.
        "sample=N"
        Return only values from the first N fragments after
        skip selected by the cts:query.
        This option does not affect the number of fragments selected
        by the cts:query to calculate frequencies.
        Only applies when a $query parameter is specified.
        "truncate=N"
        Include only values from the first N fragments
        after skip selected by the cts:query.
        This option also affects the number of fragments selected
        by the cts:query to calculate frequencies.
        Only applies when a $query parameter is specified.
        "score-logtfidf"
        Compute scores using the logtfidf method.
        Only applies when a $query parameter is specified.
        "score-logtf"
        Compute scores using the logtf method.
        Only applies when a $query parameter is specified.
        "score-simple"
        Compute scores using the simple method.
        Only applies when a $query parameter is specified.
        "score-random"
        Compute scores using the random method.
        Only applies when a $query parameter is specified.
        "score-zero"
        Compute all scores as zero.
        Only applies when a $query parameter is specified.
        "checked"
        Word positions should be checked when resolving the query.
        "unchecked"
        Word positions should not be checked when resolving the query.
        "too-many-positions-error"
        If too much memory is needed to perform positions calculations
        to check whether a document matches a query,
        return an XDMP-TOOMANYPOSITIONS error,
        instead of accepting the document as a match.
        "eager"
        Perform most of the work concurrently before returning
        the first item from the indexes, and only some of the work
        sequentially while iterating through the rest of the items.
        This usually takes the shortest time for a complete item-order
        result or for any frequency-order result.
        "lazy"
        Perform only some the work concurrently before returning
        the first item from the indexes, and most of the work
        sequentially while iterating through the rest of the items.
        This usually takes the shortest time for a small item-order
        partial result.
        "concurrent"
        Perform the work concurrently in another thread. This is a hint
        to the query optimizer to help parallelize the lexicon work, allowing
        the calling query to continue performing other work while the lexicon
        processing occurs.  This is especially useful in cases where multiple
        lexicon calls occur in the same query (for example, resolving many
        facets in a single query).
        "map"
        Return results as a single map:map
         value instead of as an xs:anyAtomicType* sequence
         .
        "coordinate-system=name"
        Use the lexicon that is configured with the specified coordinate
         system. Allowed values: "wgs84", "wgs84/double", "raw",
         "raw/double". Only applicable if the lexicon value type is
         point or long-lat-point.
        "precision=value"
        Use the lexicon that is configured with the specified precision.
         Allowed values: float and double.
         Only applicable if the lexicon value type is point or
         long-lat-point. This value takes precedence over the
         precision implicit in the coordinate system name.

**`$query`** *(optional)*
Only include values in fragments selected by the cts:query,
    and compute frequencies from this set of included values.
    The values do not need to match the query, but they must occur in
    fragments selected by the query.
    The fragments are not filtered to ensure they match the query,
    but instead selected in the same manner as
    
    "unfiltered" cts:search
    
    operations.  If a string
   is entered, the string is treated as a cts:word-query of the
   specified string.

**`$quality-weight`** *(optional)*
A document quality weight to use when computing scores.
    The default is 1.0.

**`$forest-ids`** *(optional)*
A sequence of IDs of forests to which the search will be constrained.
    An empty sequence means to search all forests in the database.
    The default is ().

### Returns

`xs:anyAtomicType*`

### Usage Notes

Only one of "frequency-order" or "item-order" may be specified
  in the options parameter.  If neither "frequency-order" nor "item-order"
  is specified, then the default is "item-order".
      Only one of "fragment-frequency" or "item-frequency" may be specified
  in the options parameter.  If neither "fragment-frequency" nor
  "item-frequency" is specified, then the default is "fragment-frequency".
      Only one of "ascending" or "descending" may be specified
  in the options parameter.  If neither "ascending" nor "descending"
  is specified, then the default is "ascending" if "item-order" is
  specified, and "descending" if "frequency-order" is specified.
      Only one of "eager" or "lazy" may be specified
  in the options parameter.  If neither "eager" nor "lazy"
  is specified, then the default is "lazy" if "item-order" is
  specified, and "eager" if "frequency-order" is specified.
      Only one of "any", "document", "properties", or "locks"
  may be specified in the options parameter.
  If none of "any", "document", "properties", or "locks" are specified
  and there is a $query parameter, then the default is "document".
  If there is no $query parameter then the default is "any".
      Only one of the "score-logtfidf", "score-logtf", "score-simple",
  "score-random", or "score-zero" options may be specified in the options
  parameter.
  If none of "score-logtfidf", "score-logtf", "score-simple", "score-random",
  or "score-zero" are specified, then the default is "score-logtfidf".
      Only one of the "checked" or "unchecked" options may be specified
  in the options parameter.
  If neither "checked" nor "unchecked" are specified,
  then the default is "checked".
      If "collation=URI" is not specified in the options parameter,
  then the default collation is used. If a range index with that collation
  does not exist, an error is thrown.
      If "sample=N" is not specified in the options parameter,
  then all included values may be returned. If a $query parameter
  is not present, then "sample=N" has no effect.
      If "truncate=N" is not specified in the options parameter,
  then values from all fragments selected by the $query parameter
  are included.  If a $query parameter is not present, then
  "truncate=N" has no effect.
      When multiple element and/or attribute QNames are specified,
  then all possible element/attribute QName combinations are used
  to select the matching values.
      To incrementally fetch a subset of the values returned by this function,
  use fn:subsequence
  
  on the output, rather than 
  the "skip" option. The "skip" option is based on fragments matching the 
  query parameter (if present), not on values. A fragment 
  matched by query might contain multiple values or no values. 
  The number of fragments skipped does not correspond to the number of 
  values. Also, the skip is applied to the relevance ordered query matches, 
  not to the ordered values list. 
      When using the "skip" option, use the "truncate" option rather than 
  the "limit" option to control the number of matching fragments from which 
  to draw values.

### Examples

```xquery
cts:element-attribute-values(xs:QName("animal"),
                               xs:QName("name"),
                               "aardvark")
  => ("aardvark","aardvarks","aardwolf",...)
```

---

## cts:element-attribute-word-match

Returns words from the specified element-attribute word lexicon(s) that
  match a wildcard pattern.   This function requires an element-attribute
  word lexicon for each of the element/attribute pairs specified in the
  function.  If there is not an element-attribute word lexicon
  configured for any of the specified element/attribute pairs, then
  an exception is thrown.

### Signature

```xquery
cts:element-attribute-word-match(
  $element-names as xs:QName*,
  $attribute-names as xs:QName*,
  $pattern as xs:string,
  $options as xs:string*?,
  $query as cts:query??,
  $quality-weight as xs:double??,
  $forest-ids as xs:unsignedLong*?
) as xs:string*
```

### Parameters

**`$element-names`**
One or more element QNames.

**`$attribute-names`**
One or more attribute QNames.

**`$pattern`**
Wildcard pattern to match.

**`$options`** *(optional)*
Options.  The default is ().
    
      Options include:
      
        "case-sensitive"
        A case-sensitive match.
        "case-insensitive"
        A case-insensitive match.
        "diacritic-sensitive"
        A diacritic-sensitive match.
        "diacritic-insensitive"
        A diacritic-insensitive match.
        "ascending"
        Words should be returned in ascending order.
        "descending"
        Words should be returned in descending order.
        "any"
        Words from any fragment should be included.
        "document"
        Words from document fragments should be included.
        "properties"
        Words from properties fragments should be included.
        "locks"
        Words from locks fragments should be included.
        "collation=URI"
        Use the lexicon with the collation specified by URI.
        "limit=N"
        Return no more than N words. You should not
        use this option with the "skip" option. Use "truncate" instead.
        "skip=N"
        Skip over fragments selected by the cts:query
        to treat the Nth fragment as the first fragment.
        Words from skipped fragments are not included.
        Only applies when a $query parameter is specified.
        "sample=N"
        Return only words from the first N fragments after
        skip selected by the cts:query.
        Only applies when a $query parameter is specified.
        "truncate=N"
        Include only words from the first N fragments after
        skip selected by the cts:query.
        Only applies when a $query parameter is specified.
        "score-logtfidf"
        Compute scores using the logtfidf method.
        Only applies when a $query parameter is specified.
        "score-logtf"
        Compute scores using the logtf method.
        Only applies when a $query parameter is specified.
        "score-simple"
        Compute scores using the simple method.
        Only applies when a $query parameter is specified.
        "score-random"
        Compute scores using the random method.
        Only applies when a $query parameter is specified.
        "score-zero"
        Compute all scores as zero.
        Only applies when a $query parameter is specified.
        "checked"
        Word positions should be checked when resolving the query.
        "unchecked"
        Word positions should not be checked when resolving the query.
        "too-many-positions-error"
        If too much memory is needed to perform positions calculations
        to check whether a document matches a query,
        return an XDMP-TOOMANYPOSITIONS error,
        instead of accepting the document as a match.
        "concurrent"
        Perform the work concurrently in another thread. This is a hint
        to the query optimizer to help parallelize the lexicon work, allowing
        the calling query to continue performing other work while the lexicon
        processing occurs.  This is especially useful in cases where multiple
        lexicon calls occur in the same query (for example, resolving many
        facets in a single query).
        "map"
        Return results as a single map:map
         value instead of as an xs:string* sequence
         .

**`$query`** *(optional)*
Only include words in fragments selected by the cts:query.
    The words do not need to match the query, but the words must occur
    in fragments selected by the query.
    The fragments are not filtered to ensure they match the query,
    but instead selected in the same manner as
    
    "unfiltered" cts:search
    
    operations.  If a string
   is entered, the string is treated as a cts:word-query of the
   specified string.

**`$quality-weight`** *(optional)*
A document quality weight to use when computing scores.
    The default is 1.0.

**`$forest-ids`** *(optional)*
A sequence of IDs of forests to which the search will be constrained.
    An empty sequence means to search all forests in the database.
    The default is ().

### Returns

`xs:string*`

### Usage Notes

Only one of "ascending" or "descending" may be specified
  in the options parameter.  If neither "ascending" nor "descending"
  is specified, then the default is "ascending".
      Only one of "any", "document", "properties", or "locks"
  may be specified in the options parameter.
  If none of "any", "document", "properties", or "locks" are specified
  and there is a $query parameter, then the default is "document".
  If there is no $query parameter then the default is "any".
      Only one of the "score-logtfidf", "score-logtf", "score-simple",
  "score-random", or "score-zero" options may be specified in the options
  parameter.
  If none of "score-logtfidf", "score-logtf", "score-simple", "score-random",
  or "score-zero" are specified, then the default is "score-logtfidf".
      Only one of the "checked" or "unchecked" options may be specified
  in the options parameter.
  If neither "checked" nor "unchecked" are specified,
  then the default is "checked".
      If "collation=URI" is not specified in the options parameter,
  then the default collation is used. If a lexicon with that collation
  does not exist, an error is thrown.
      If "sample=N" is not specified in the options parameter,
  then all included words may be returned. If a $query parameter
  is not present, then "sample=N" has no effect.
      If "truncate=N" is not specified in the options parameter,
  then words from all fragments selected by the $query parameter
  are included.  If a $query parameter is not present, then
  "truncate=N" has no effect.
      To incrementally fetch a subset of the values returned by this function,
  use fn:subsequence
  
  on the output, rather than 
  the "skip" option. The "skip" option is based on fragments matching the 
  query parameter (if present), not on values. A fragment 
  matched by query might contain multiple values or no values. 
  The number of fragments skipped does not correspond to the number of 
  values. Also, the skip is applied to the relevance ordered query matches, 
  not to the ordered values list. 
      When using the "skip" option, use the "truncate" option rather than 
  the "limit" option to control the number of matching fragments from which 
  to draw values.
      
    If neither "case-sensitive" nor "case-insensitive"
    is present, $pattern is used to determine case sensitivity.
    If $pattern contains no uppercase, it specifies "case-insensitive".
    If $pattern contains uppercase, it specifies "case-sensitive".
  
      
    If neither "diacritic-sensitive" nor "diacritic-insensitive"
    is present, $pattern is used to determine diacritic sensitivity.
    If $pattern contains no diacritics, it specifies "diacritic-insensitive".
    If $pattern contains diacritics, it specifies "diacritic-sensitive".
  
      When multiple element and/or attribute QNames are specified,
  then all possible element/attribute QName combinations are used
  to select the matching values.

### Examples

```xquery
cts:element-word-match(xs:QName("animals"),"aardvark*")
  => ("aardvark","aardvarks")
```

---

## cts:element-attribute-words

Returns words from the specified element-attribute word lexicon(s).
  This function requires an element-attribute word lexicon for each of the
  element/attribute pairs specified in the function.  If there is not an
  element/attribute word lexicon configured for any of the specified
  element/attribute pairs, then an exception is thrown.  The words are
  returned in collation order.

### Signature

```xquery
cts:element-attribute-words(
  $element-names as xs:QName*,
  $attribute-names as xs:QName*,
  $start as xs:string??,
  $options as xs:string*?,
  $query as cts:query??,
  $quality-weight as xs:double??,
  $forest-ids as xs:unsignedLong*?
) as xs:string*
```

### Parameters

**`$element-names`**
One or more element QNames.

**`$attribute-names`**
One or more attribute QNames.

**`$start`** *(optional)*
A starting word.  Returns only this word and any following words
    from the lexicon.  If the parameter is not in the lexicon, then it
    returns the words beginning with the next word.

**`$options`** *(optional)*
Options.  The default is ().
    
      Options include:
      
        "ascending"
        Words should be returned in ascending order.
        "descending"
        Words should be returned in descending order.
        "any"
        Words from any fragment should be included.
        "document"
        Words from document fragments should be included.
        "properties"
        Words from properties fragments should be included.
        "locks"
        Words from locks fragments should be included.
        "collation=URI"
        Use the lexicon with the collation specified by URI.
        "limit=N"
        Return no more than N words. You should not
        use this option with the "skip" option. Use "truncate" instead.
        "skip=N"
        Skip over fragments selected by the cts:query
        to treat the Nth fragment as the first fragment.
        Words from skipped fragments are not included.
        Only applies when a $query parameter is specified.
        "sample=N"
        Return only words from the first N fragments after
        skip selected by the cts:query.
        Only applies when a $query parameter is specified.
        "truncate=N"
        Include only words from the first N fragments after
        skip selected by the cts:query.
        Only applies when a $query parameter is specified.
        "score-logtfidf"
        Compute scores using the logtfidf method.
        Only applies when a $query parameter is specified.
        "score-logtf"
        Compute scores using the logtf method.
        Only applies when a $query parameter is specified.
        "score-simple"
        Compute scores using the simple method.
        Only applies when a $query parameter is specified.
        "score-random"
        Compute scores using the random method.
        Only applies when a $query parameter is specified.
        "score-zero"
        Compute all scores as zero.
        Only applies when a $query parameter is specified.
        "checked"
        Word positions should be checked when resolving the query.
        "unchecked"
        Word positions should not be checked when resolving the query.
        "too-many-positions-error"
        If too much memory is needed to perform positions calculations
        to check whether a document matches a query,
        return an XDMP-TOOMANYPOSITIONS error,
        instead of accepting the document as a match.
        "concurrent"
        Perform the work concurrently in another thread. This is a hint
        to the query optimizer to help parallelize the lexicon work, allowing
        the calling query to continue performing other work while the lexicon
        processing occurs.  This is especially useful in cases where multiple
        lexicon calls occur in the same query (for example, resolving many
        facets in a single query).
        "map"
        Return results as a single map:map
         value instead of as an xs:string* sequence
         .

**`$query`** *(optional)*
Only include words in fragments selected by the cts:query.
    The words do not need to match the query, but the words must occur
    in fragments selected by the query.
    The fragments are not filtered to ensure they match the query,
    but instead selected in the same manner as
    
    "unfiltered" cts:search
    
    operations.  If a string
   is entered, the string is treated as a cts:word-query of the
   specified string.

**`$quality-weight`** *(optional)*
A document quality weight to use when computing scores.
    The default is 1.0.

**`$forest-ids`** *(optional)*
A sequence of IDs of forests to which the search will be constrained.
    An empty sequence means to search all forests in the database.
    The default is ().

### Returns

`xs:string*`

### Usage Notes

Only one of "ascending" or "descending" may be specified
  in the options parameter.  If neither "ascending" nor "descending"
  is specified, then the default is "ascending".
      Only one of "any", "document", "properties", or "locks"
  may be specified in the options parameter.
  If none of "any", "document", "properties", or "locks" are specified
  and there is a $query parameter, then the default is "document".
  If there is no $query parameter then the default is "any".
      Only one of the "score-logtfidf", "score-logtf", "score-simple",
  "score-random", or "score-zero" options may be specified in the options
  parameter.
  If none of "score-logtfidf", "score-logtf", "score-simple", "score-random",
  or "score-zero" are specified, then the default is "score-logtfidf".
      Only one of the "checked" or "unchecked" options may be specified
  in the options parameter.
  If neither "checked" nor "unchecked" are specified,
  then the default is "checked".
      If "collation=URI" is not specified in the options parameter,
  then the default collation is used. If a lexicon with that collation
  does not exist, an error is thrown.
      If "sample=N" is not specified in the options parameter,
  then all included words may be returned. If a $query parameter
  is not present, then "sample=N" has no effect.
      If "truncate=N" is not specified in the options parameter,
  then words from all fragments selected by the $query parameter
  are included.  If a $query parameter is not present, then
  "truncate=N" has no effect.
      When multiple element and/or attribute QNames are specified,
  then all possible element/attribute QName combinations are used
  to select the matching values.
      When run without a $query parameter and as a user with the admin role,
  the word lexicon functions return results that might include words from
  deleted fragments. However, when run as a user with the admin role and
  without a $query parameter, the word lexicon functions run faster (because
  they do not need to look up where each word comes from). It is therefore
  faster to run word lexicon functions as an admin user without passing a
  $query parameter.
      To incrementally fetch a subset of the values returned by this function, 
  use fn:subsequence
  
  on the output, rather than 
  the "skip" option. The "skip" option is based on fragments matching the 
  query parameter (if present), not on values. A fragment 
  matched by query might contain multiple values or no values. 
  The number of fragments skipped does not correspond to the number of 
  values. Also, the skip is applied to the relevance ordered query matches, 
  not to the ordered values list. 
      When using the "skip" option, use the "truncate" option rather than 
  the "limit" option to control the number of matching fragments from which 
  to draw values.

### Examples

```xquery
cts:element-attribute-words(xs:QName("animal"),
                              xs:QName("name"),
                              "aardvark")
  => ("aardvark","aardvarks","aardwolf",...)
```

---

## cts:element-reference

Creates a reference to an element value lexicon, for use as a parameter to
  cts:value-tuples,
  temporal:axis-create, or any
  other function that takes an index reference.  Since lexicons are
  implemented with range indexes, this function will throw an exception if
  the specified range index does not exist.

### Signature

```xquery
cts:element-reference(
  $element as xs:QName,
  $options as xs:string*?
) as cts:reference
```

### Parameters

**`$element`**
An element QName.

**`$options`** *(optional)*
Options.  The default is ().
    
      Options include:
      
        "type=type"
        Use the lexicon with the type specified by type
        (int, unsignedInt, long, unsignedLong, float, double, decimal,
        dateTime, time, date, gYearMonth, gYear, gMonth, gDay,
        yearMonthDuration, dayTimeDuration, string, anyURI, point, or
        long-lat-point)
        "collation=URI"
        Use the lexicon with the collation specified by URI.
        "nullable"
        Allow null values in tuples reported from cts:value-tuples when
        using this lexicon.
        "unchecked"
        Read the scalar type, collation and coordinate-system info
        only from the input. Do not check the definition against the
        context database.
        "coordinate-system=name"
        Create a reference to an index or lexicon based on the specified
         coordinate system. Allowed values: "wgs84", "wgs84/double", "raw",
         "raw/double". Only applicable if the index/lexicon value type is
         point or long-lat-point.
        "precision=value"
        Create a reference to an index or lexicon configured with the
         specified geospatial precision. Allowed values: float
         and double. Only applicable if the index/lexicon value
         type is point or long-lat-point. This
         value takes precedence over the precision implicit in the coordinate
         system name.

### Returns

`cts:reference`

### Examples

```xquery
cts:element-reference(xs:QName("TITLE"))
=>
cts:element-reference(fn:QName("", "TITLE"),
  ("type=string","collation=http://marklogic.com/collation/"))
```

---

## cts:element-value-co-occurrences

Returns value co-occurrences (that is, pairs of values, both of which appear
  in the same fragment) from the specified element value lexicon(s).  The
  values are returned as an XML element
   with two children, each child
  containing one of the co-occurring values.  You can use
  cts:frequency
  on each item returned to find how many times the pair occurs.
  Value lexicons are implemented using range indexes; consequently
  this function requires an element range index for each element specified
  in the function.  If there is not a range index configured for each
  of the specified elements, an exception is thrown.

### Signature

```xquery
cts:element-value-co-occurrences(
  $element-name-1 as xs:QName,
  $element-name-2 as xs:QName,
  $options as xs:string*?,
  $query as cts:query??,
  $quality-weight as xs:double??,
  $forest-ids as xs:unsignedLong*?
) as element(cts:co-occurrence)*
```

### Parameters

**`$element-name-1`**
An element QName.

**`$element-name-2`**
An element QName.

**`$options`** *(optional)*
Options.  The default is ().
    
      Options include:
      
        "ascending"
        Co-occurrences should be returned in ascending order.
        "descending"
        Co-occurrences should be returned in descending order.
        "any"
        Co-occurrences from any fragment should be included.
        "document"
        Co-occurrences from document fragments should be included.
        "properties"
        Co-occurrences from properties fragments should be included.
        "locks"
        Co-occurrences from locks fragments should be included.
        "frequency-order"
        Co-occurrences should be returned ordered by frequency.
        "item-order"
        Co-occurrences should be returned ordered by item.
        "fragment-frequency"
        Frequency should be the number of fragments with
        an included co-occurrences.
        This option is used with cts:frequency.
        "item-frequency"
        Frequency should be the number of occurrences of
        an included co-occurrence.
        This option is used with cts:frequency.
        "type=type"
        For both lexicons, use the type specified by type
        (int, unsignedInt, long, unsignedLong, float, double, decimal,
        dateTime, time, date, gYearMonth, gYear, gMonth, gDay,
        yearMonthDuration, dayTimeDuration, string, or anyURI)
        "type-1=type"
        For the first lexicon, use the type specified by type
        (int, unsignedInt, long, unsignedLong, float, double, decimal,
        dateTime, time, date, gYearMonth, gYear, gMonth, gDay,
        yearMonthDuration, dayTimeDuration, string, or anyURI)
        "type-2=type"
        For the second lexicon, use the type specified by type
        (int, unsignedInt, long, unsignedLong, float, double, decimal,
        dateTime, time, date, gYearMonth, gYear, gMonth, gDay,
        yearMonthDuration, dayTimeDuration, string, or anyURI)
        "collation=URI"
        For both lexicons, use the collation specified by
        URI.
        "collation-1=URI"
        For the first lexicon, use the collation specified by
        URI.
        "collation-2=URI"
        For the second lexicon, use the collation specified by
        URI.
        "timezone=TZ"
        Return timezone sensitive values (dateTime, time, date,
        gYearMonth, gYear, gMonth, and gDay) adjusted to the timezone
        specified by TZ.
        Example timezones: Z, -08:00, +01:00.
        "ordered"
        Include co-occurrences only when the value from the first lexicon
        appears before the value from the second lexicon.
        Requires that word positions be enabled for both lexicons.
        "proximity=N"
        Include co-occurrences only when the values appear within
        N words of each other.
        Requires that word positions be enabled for both lexicons.
        "limit=N"
        Return no more than N co-occurrences. You should not
        use this option with the "skip" option. Use "truncate" instead.
        "skip=N"
        Skip over fragments selected by the cts:query
        to treat the Nth fragment as the first fragment.
        Co-occurrences from skipped fragments are not included.
        This option affects the number of fragments selected
        by the cts:query to calculate frequencies.
        Only applies when a $query parameter is specified.
        "sample=N"
        Return only co-occurrences from the first N
        fragments after skip selected by the cts:query.
        This option does not affect the number of fragments selected
        by the cts:query to calculate frequencies.
        Only applies when a $query parameter is specified.
        "truncate=N"
        Include only co-occurrences from the first N
        fragments after skip selected by the cts:query.
        This option also affects the number of fragments selected
        by the cts:query to calculate frequencies.
        Only applies when a $query parameter is specified.
        "score-logtfidf"
        Compute scores using the logtfidf method.
        Only applies when a $query parameter is specified.
        "score-logtf"
        Compute scores using the logtf method.
        Only applies when a $query parameter is specified.
        "score-simple"
        Compute scores using the simple method.
        Only applies when a $query parameter is specified.
        "score-random"
        Compute scores using the random method.
        Only applies when a $query parameter is specified.
        "score-zero"
        Compute all scores as zero.
        Only applies when a $query parameter is specified.
        "checked"
        Word positions should be checked when resolving the query.
        "unchecked"
        Word positions should not be checked when resolving the query.
        "too-many-positions-error"
        If too much memory is needed to perform positions calculations
        to check whether a document matches a query,
        return an XDMP-TOOMANYPOSITIONS error,
        instead of accepting the document as a match.
        "eager"
        Perform most of the work concurrently before returning
        the first item from the indexes, and only some of the work
        sequentially while iterating through the rest of the items.
        This usually takes the shortest time for a complete item-order
        result or for any frequency-order result.
        "lazy"
        Perform only some the work concurrently before returning
        the first item from the indexes, and most of the work
        sequentially while iterating through the rest of the items.
        This usually takes the shortest time for a small item-order
        partial result.
        "concurrent"
        Perform the work concurrently in another thread. This is a hint
        to the query optimizer to help parallelize the lexicon work, allowing
        the calling query to continue performing other work while the lexicon
        processing occurs.  This is especially useful in cases where multiple
        lexicon calls occur in the same query (for example, resolving many
        facets in a single query).
        "map"
        Return results as a single map:map
         value instead of as an element(cts:co-occurrence)* sequence
         .
        "coordinate-system=name"
        Use lexicons configured with the specified coordinate
         system. Allowed values: "wgs84", "wgs84/double", "raw",
         "raw/double". Only applicable if the lexicon value type is
         point or long-lat-point.
        "precision=value"
        Use lexicons configured with the specified precision.
         Allowed values: float and double.
         Only applicable if the lexicon value type is point or
         long-lat-point. This value takes precedence over the
         precision implicit in the coordinate system name.

**`$query`** *(optional)*
Only include co-occurrences in fragments selected by the
    cts:query,
    and compute frequencies from this set of included co-occurrences.
    The co-occurrences do not need to match the query, but they must occur in
    fragments selected by the query.
    The fragments are not filtered to ensure they match the query,
    but instead selected in the same manner as
    
    "unfiltered" cts:search
    
    operations.  If a string
   is entered, the string is treated as a cts:word-query of the
   specified string.

**`$quality-weight`** *(optional)*
A document quality weight to use when computing scores.
    The default is 1.0.

**`$forest-ids`** *(optional)*
A sequence of IDs of forests to which the search will be constrained.
    An empty sequence means to search all forests in the database.
    The default is ().

### Returns

`element(cts:co-occurrence)*`

### Usage Notes

Only one of "frequency-order" or "item-order" may be specified
  in the options parameter.  If neither "frequency-order" nor "item-order"
  is specified, then the default is "item-order".
      Only one of "fragment-frequency" or "item-frequency" may be specified
  in the options parameter.  If neither "fragment-frequency" nor
  "item-frequency" is specified, then the default is "fragment-frequency".
      Only one of "ascending" or "descending" may be specified
  in the options parameter.  If neither "ascending" nor "descending"
  is specified, then the default is "ascending" if "item-order" is
  specified, and "descending" if "frequency-order" is specified.
      Only one of "eager" or "lazy" may be specified
  in the options parameter.  If neither "eager" nor "lazy"
  is specified, then the default is "eager" if "frequency-order" or "map"
  is specified, otherwise "lazy".
      Only one of "any", "document", "properties", or "locks"
  may be specified in the options parameter.
  If none of "any", "document", "properties", or "locks" are specified
  and there is a $query parameter, then the default is "document".
  If there is no $query parameter then the default is "any".
      Only one of the "score-logtfidf", "score-logtf", "score-simple",
  "score-random", or "score-zero" options may be specified in the options
  parameter.
  If none of "score-logtfidf", "score-logtf", "score-simple", "score-random",
  or "score-zero" are specified, then the default is "score-logtfidf".
      Only one of the "checked" or "unchecked" options may be specified
  in the options parameter.
  If neither "checked" nor "unchecked" are specified,
  then the default is "checked".
      If "collation=URI" is not specified in the options parameter,
  then the default collation is used. If a lexicon with that collation
  does not exist, an error is thrown.
      If "sample=N" is not specified in the options parameter,
  then all included co-occurrences may be returned.
  If a $query parameter
  is not present, then "sample=N" has no effect.
      If "truncate=N" is not specified in the options parameter,
  then co-occurrences from all fragments selected by the
  $query parameter are included.
  If a $query parameter is not present, then
  "truncate=N" has no effect.
      To incrementally fetch a subset of the co-occurrences returned by this 
  function, use fn:subsequence
  
  on the output, rather than 
  the "skip" option. The "skip" option is based on fragments matching the 
  query parameter (if present), not on values. A fragment 
  matched by query might contain multiple occurrences or no occurrences. 
  The number of fragments skipped does not correspond to the number of 
  values. Also, the skip is applied to the relevance ordered query matches, 
  not to the ordered co-occurrences list. 
      When using the "skip" option, use the "truncate" option rather than 
  the "limit" option to control the number of matching fragments from which 
  to draw values.

### Examples

#### Example 1

```xquery
(:
     This query has the database fragmented on SPEECH and
     finds the first 3 SPEAKERs that co-occur in a SPEECH
     in the play Hamlet.
     Requires an element range index on SPEAKER with range
     value positions enabled on the range index.
  :)
  cts:element-value-co-occurrences(
    xs:QName("SPEAKER"),xs:QName("SPEAKER"),
    ("frequency-order","ordered"),
    cts:document-query("/shakespeare/plays/hamlet.xml"))[1 to 3]
  =>
  <cts:co-occurrence xmlns:cts="http://marklogic.com/cts"
      xmlns:xsi="http://www.w3.org/2001/XMLSchema-instance"
      xmlns:xs="http://www.w3.org/2001/XMLSchema">
    <cts:value xsi:type="xs:string">MARCELLUS</cts:value>
    <cts:value xsi:type="xs:string">BERNARDO</cts:value>
  </cts:co-occurrence>
  <cts:co-occurrence xmlns:cts="http://marklogic.com/cts"
      xmlns:xsi="http://www.w3.org/2001/XMLSchema-instance"
      xmlns:xs="http://www.w3.org/2001/XMLSchema">
    <cts:value xsi:type="xs:string">ROSENCRANTZ</cts:value>
    <cts:value xsi:type="xs:string">GUILDENSTERN</cts:value>
  </cts:co-occurrence>
  <cts:co-occurrence xmlns:cts="http://marklogic.com/cts"
      xmlns:xsi="http://www.w3.org/2001/XMLSchema-instance"
      xmlns:xs="http://www.w3.org/2001/XMLSchema">
    <cts:value xsi:type="xs:string">HORATIO</cts:value>
    <cts:value xsi:type="xs:string">MARCELLUS</cts:value>
  </cts:co-occurrence>
```

#### Example 2

```xquery
(:
     this query has the database fragmented on SPEECH and
     finds SPEAKERs that co-occur in a SPEECH in the play Hamlet,
     returned as a map
  :)
  cts:element-value-co-occurrences(
    xs:QName("SPEAKER"),xs:QName("SPEAKER"),
    ("frequency-order","ordered", "map"),
    cts:document-query("/shakespeare/plays/hamlet.xml"))
  =>
  map:map(
   <map:map xmlns:xs="http://www.w3.org/2001/XMLSchema"
     xmlns:xsi="http://www.w3.org/2001/XMLSchema-instance"
     xmlns:map="http://marklogic.com/xdmp/map">
     <map:entry key="HORATIO">
       <map:value xsi:type="xs:string">MARCELLUS</map:value>
     </map:entry>
     <map:entry key="CORNELIUS">
         <map:value xsi:type="xs:string">VOLTIMAND</map:value>
     </map:entry>
     <map:entry key="MARCELLUS">
         <map:value xsi:type="xs:string">BERNARDO</map:value>
         <map:value xsi:type="xs:string">HORATIO</map:value>
     </map:entry>
     <map:entry key="ROSENCRANTZ">
       <map:value xsi:type="xs:string">GUILDENSTERN</map:value>
     </map:entry>
   </map:map>)
```

#### Example 3

```xquery
xquery version "1.0-ml";
(:
This example uses the co-occurrences between the URI lexicon
and an element range index to effectively join documents together.
:)
(: Load sample data :)
xdmp:document-insert("/test1.xml",
  <test1><hello>this is a value</hello></test1>),
xdmp:document-insert("/test2.xml",
  <test2><hello>this is a value</hello></test2>),
xdmp:document-insert("/test3.xml",
  <test3><hello>this is a different value</hello></test3>);
(:
Requires an element range index on 'hello' and the URI lexicon.
This query finds 'hello' elements that occur in more than one document.
It is an efficient way to join documents using range indexes.
:)
let $x :=
  cts:element-value-co-occurrences(
  (: note the special xdmp:document QName for the URI lexicon :)
    xs:QName("hello"),xs:QName("xdmp:document"),
    ("frequency-order", "map",
     "collation-1=http://marklogic.com/collation/",
     "collation-2=http://marklogic.com/collation/codepoint"))
for $key in map:keys($x)
where fn:count(map:get($x, $key)) gt 1
return
<result>
  <key>{$key}</key>
  <value>{for $uri in map:get($x, $key)
          return <uri>{$uri}</uri>}</value>
</result>

(: returns the values that occur in more than one document (URI) :)

=>
<result>
  <key>this is a value</key>
  <value>
    <uri>/test1.xml</uri>
    <uri>/test2.xml</uri>
  </value>
</result>
```

---

## cts:element-value-match

Returns values from the specified element value lexicon(s)
   that match the specified wildcard pattern.  Element value lexicons
   are implemented using range indexes; consequently this function
   requires an element range index for each element specified in the
   function.  If there is not a range index configured for each of the
   specified elements, then an exception is thrown.

### Signature

```xquery
cts:element-value-match(
  $element-names as xs:QName*,
  $pattern as xs:anyAtomicType,
  $options as xs:string*?,
  $query as cts:query??,
  $quality-weight as xs:double??,
  $forest-ids as xs:unsignedLong*?
) as xs:anyAtomicType*
```

### Parameters

**`$element-names`**
One or more element QNames.

**`$pattern`**
A pattern to match.  The parameter type must match the lexicon type.
    String parameters may include wildcard characters.

**`$options`** *(optional)*
Options.  The default is ().
    
      Options include:
      
        "case-sensitive"
        A case-sensitive match.
        "case-insensitive"
        A case-insensitive match.
        "diacritic-sensitive"
        A diacritic-sensitive match.
        "diacritic-insensitive"
        A diacritic-insensitive match.
        "ascending"
        Values should be returned in ascending order.
        "descending"
        Values should be returned in descending order.
        "any"
        Values from any fragment should be included.
        "document"
        Values from document fragments should be included.
        "properties"
        Values from properties fragments should be included.
        "locks"
        Values from locks fragments should be included.
        "frequency-order"
        Values should be returned ordered by frequency.
        "item-order"
        Values should be returned ordered by item.
        "fragment-frequency"
        Frequency should be the number of fragments with
        an included value.
        This option is used with cts:frequency.
        "item-frequency"
        Frequency should be the number of occurrences of
        an included value.
        This option is used with cts:frequency.
        "type=type"
        Use the lexicon with the type specified by type
        (int, unsignedInt, long, unsignedLong, float, double, decimal,
        dateTime, time, date, gYearMonth, gYear, gMonth, gDay,
        yearMonthDuration, dayTimeDuration, string, or anyURI)
        "collation=URI"
        Use the range index with the collation specified by
        URI.
        "timezone=TZ"
        Return timezone sensitive values (dateTime, time, date,
        gYearMonth, gYear, gMonth, and gDay) adjusted to the timezone
        specified by TZ.
        Example timezones: Z, -08:00, +01:00.
        "limit=N"
        Return no more than N values. You should not
        use this option with the "skip" option. Use "truncate" instead.
        "skip=N"
        Skip over fragments selected by the cts:query
        to treat the Nth fragment as the first fragment.
        Values from skipped fragments are not included.
        This option affects the number of fragments selected
        by the cts:query to calculate frequencies.
        Only applies when a $query parameter is specified.
        "sample=N"
        Return only values from the first N
        fragments after skip selected by the cts:query.
        This option does not affect the number of fragments selected
        by the cts:query to calculate frequencies.
        Only applies when a $query parameter is specified.
        "truncate=N"
        Include only values from the first N fragments
        after skip selected by the cts:query.
        This option also affects the number of fragments selected
        by the cts:query to calculate frequencies.
        Only applies when a $query parameter is specified.
        "score-logtfidf"
        Compute scores using the logtfidf method.
        Only applies when a $query parameter is specified.
        "score-logtf"
        Compute scores using the logtf method.
        Only applies when a $query parameter is specified.
        "score-simple"
        Compute scores using the simple method.
        Only applies when a $query parameter is specified.
        "score-random"
        Compute scores using the random method.
        Only applies when a $query parameter is specified.
        "score-zero"
        Compute all scores as zero.
        Only applies when a $query parameter is specified.
        "checked"
        Word positions should be checked when resolving the query.
        "unchecked"
        Word positions should not be checked when resolving the query.
        "too-many-positions-error"
        If too much memory is needed to perform positions calculations
        to check whether a document matches a query,
        return an XDMP-TOOMANYPOSITIONS error,
        instead of accepting the document as a match.
        "eager"
        Perform most of the work concurrently before returning
        the first item from the indexes, and only some of the work
        sequentially while iterating through the rest of the items.
        This usually takes the shortest time for a complete item-order
        result or for any frequency-order result.
        "lazy"
        Perform only some the work concurrently before returning
        the first item from the indexes, and most of the work
        sequentially while iterating through the rest of the items.
        This usually takes the shortest time for a small item-order
        partial result.
        "concurrent"
        Perform the work concurrently in another thread. This is a hint
        to the query optimizer to help parallelize the lexicon work, allowing
        the calling query to continue performing other work while the lexicon
        processing occurs.  This is especially useful in cases where multiple
        lexicon calls occur in the same query (for example, resolving many
        facets in a single query).
        "map"
        Return results as a single map:map
         value instead of as an xs:anyAtomicType* sequence
         .
        "coordinate-system=name"
        Use the lexicon that is configured with the specified coordinate
         system. Allowed values: "wgs84", "wgs84/double", "raw",
         "raw/double". Only applicable if the lexicon value type is
         point or long-lat-point.
        "precision=value"
        Use the lexicon that is configured with the specified precision.
         Allowed values: float and double.
         Only applicable if the lexicon value type is point or
         long-lat-point. This value takes precedence over the
         precision implicit in the coordinate system name.

**`$query`** *(optional)*
Only include values in fragments selected by the cts:query,
    and compute frequencies from this set of included values.
    The values do not need to match the query, but they must occur in
    fragments selected by the query.
    The fragments are not filtered to ensure they match the query,
    but instead selected in the same manner as
    
    "unfiltered" cts:search
    
    operations.  If a string
   is entered, the string is treated as a cts:word-query of the
   specified string.

**`$quality-weight`** *(optional)*
A document quality weight to use when computing scores.
    The default is 1.0.

**`$forest-ids`** *(optional)*
A sequence of IDs of forests to which the search will be constrained.
    An empty sequence means to search all forests in the database.
    The default is ().

### Returns

`xs:anyAtomicType*`

### Usage Notes

Only one of "frequency-order" or "item-order" may be specified
  in the options parameter.  If neither "frequency-order" nor "item-order"
  is specified, then the default is "item-order".
      Only one of "fragment-frequency" or "item-frequency" may be specified
  in the options parameter.  If neither "fragment-frequency" nor
  "item-frequency" is specified, then the default is "fragment-frequency".
      Only one of "ascending" or "descending" may be specified
  in the options parameter.  If neither "ascending" nor "descending"
  is specified, then the default is "ascending" if "item-order" is
  specified, and "descending" if "frequency-order" is specified.
      Only one of "eager" or "lazy" may be specified
  in the options parameter.  If neither "eager" nor "lazy"
  is specified, then the default is "lazy" if "item-order" is
  specified, and "eager" if "frequency-order" is specified.
      Only one of "any", "document", "properties", or "locks"
  may be specified in the options parameter.
  If none of "any", "document", "properties", or "locks" are specified
  and there is a $query parameter, then the default is "document".
  If there is no $query parameter then the default is "any".
      Only one of the "score-logtfidf", "score-logtf", "score-simple",
  "score-random", or "score-zero" options may be specified in the options
  parameter.
  If none of "score-logtfidf", "score-logtf", "score-simple", "score-random",
  or "score-zero" are specified, then the default is "score-logtfidf".
      Only one of the "checked" or "unchecked" options may be specified
  in the options parameter.
  If neither "checked" nor "unchecked" are specified,
  then the default is "checked".
      If "collation=URI" is not specified in the options parameter,
  then the default collation is used.  If a range index with that collation
  does not exist, an error is thrown.
      If "sample=N" is not specified in the options parameter,
  then all included values may be returned. If a $query parameter
  is not present, then "sample=N" has no effect.
      If "truncate=N" is not specified in the options parameter,
  then values from all fragments selected by the $query parameter
  are included.  If a $query parameter is not present, then
  "truncate=N" has no effect.
      To incrementally fetch a subset of the values returned by this function,
  use fn:subsequence
  
  on the output, rather than 
  the "skip" option. The "skip" option is based on fragments matching the 
  query parameter (if present), not on values. A fragment 
  matched by query might contain multiple values or no values. 
  The number of fragments skipped does not correspond to the number of 
  values. Also, the skip is applied to the relevance ordered query matches, 
  not to the ordered values list. 
      When using the "skip" option, use the "truncate" option rather than 
  the "limit" option to control the number of matching fragments from which 
  to draw values.
      
    If neither "case-sensitive" nor "case-insensitive"
    is present, $pattern is used to determine case sensitivity.
    If $pattern contains no uppercase, it specifies "case-insensitive".
    If $pattern contains uppercase, it specifies "case-sensitive".
  
      
    If neither "diacritic-sensitive" nor "diacritic-insensitive"
    is present, $pattern is used to determine diacritic sensitivity.
    If $pattern contains no diacritics, it specifies "diacritic-insensitive".
    If $pattern contains diacritics, it specifies "diacritic-sensitive".

### Examples

```xquery
cts:element-value-match(xs:QName("animal"),"aardvark*")
  => ("aardvark","aardvarks")
```

---

## cts:element-value-ranges

Returns value ranges from the specified element value lexicon(s).
  Value lexicons are implemented using range indexes; consequently this
  function requires an element range index for each element specified
  in the function.  If there is not a range index configured for each
  of the specified elements, an exception is thrown.
      The values are divided into buckets. The $bounds parameter specifies
  the number of buckets and the size of each bucket.
  All included values are bucketed, even those less than the lowest bound
  or greater than the highest bound. An empty sequence for $bounds specifies
  one bucket, a single value specifies two buckets, two values specify
  three buckets, and so on.
      If you have string values and you pass a $bounds parameter
   as in the following call:
      cts:element-value-ranges(xs:QName("myElement"), ("f", "m"))
      The first bucket contains string values that are less than the
  string f, the second bucket contains string values greater than
  or equal to f but less than m, and the third bucket
  contains string values that are greater than or equal to m.
      For each non-empty bucket, a cts:range element is returned.
  Each cts:range element has a cts:minimum child
  and a cts:maximum child.  If a bucket is bounded, its
  cts:range element will also have a
  cts:lower-bound child if it is bounded from below, and
  a cts:upper-bound element if it is bounded from above.
  Empty buckets return nothing unless the "empties" option is specified.

### Signature

```xquery
cts:element-value-ranges(
  $element-names as xs:QName*,
  $bounds as xs:anyAtomicType*?,
  $options as xs:string*?,
  $query as cts:query??,
  $quality-weight as xs:double??,
  $forest-ids as xs:unsignedLong*?
) as element(cts:range)*
```

### Parameters

**`$element-names`**
One or more element QNames.

**`$bounds`** *(optional)*
A sequence of range bounds.
    The types must match the lexicon type.
    The values must be in strictly ascending order, otherwise an exception
    is thrown.

**`$options`** *(optional)*
Options.  The default is ().
    
      Options include:
      
        "ascending"
        Ranges should be returned in ascending order.
        "descending"
        Ranges should be returned in descending order.
        "empties"
        Include fully-bounded ranges whose frequency is 0. These ranges
        will have no minimum or maximum value.  Only empty ranges that have
        both their upper and lower bounds specified in the $bounds
        options are returned;
        any empty ranges that are less than the first bound or greater than the
        last bound are not returned.  For example, if you specify 4 bounds
        and there are no results for any of the bounds, 3 elements are
        returned (not 5 elements).
        "any"
        Values from any fragment should be included.
        "document"
        Values from document fragments should be included.
        "properties"
        Values from properties fragments should be included.
        "locks"
        Values from locks fragments should be included.
        "frequency-order"
        Ranges should be returned ordered by frequency.
        "item-order"
        Ranges should be returned ordered by item.
        "fragment-frequency"
        Frequency should be the number of fragments with
        an included value.
        This option is used with cts:frequency.
        "item-frequency"
        Frequency should be the number of occurrences of
        an included value.
        This option is used with cts:frequency.
        "type=type"
        Use the lexicon with the type specified by type
        (int, unsignedInt, long, unsignedLong, float, double, decimal,
        dateTime, time, date, gYearMonth, gYear, gMonth, gDay,
        yearMonthDuration, dayTimeDuration, string, or anyURI)
        "collation=URI"
        Use the lexicon with the collation specified by URI.
        "timezone=TZ"
        Return timezone sensitive values (dateTime, time, date,
        gYearMonth, gYear, gMonth, and gDay) adjusted to the timezone
        specified by TZ.
        Example timezones: Z, -08:00, +01:00.
        "limit=N"
        Return no more than N ranges. You should not
        use this option with the "skip" option. Use "truncate" instead.
        "skip=N"
        Skip over fragments selected by the cts:query
        to treat the Nth fragment as the first fragment.
        Values from skipped fragments are not included.
        This option affects the number of fragments selected
        by the cts:query to calculate frequencies.
        Only applies when a $query parameter is specified.
        "sample=N"
        Return only ranges for buckets with at least one value from
        the first N fragments after skip selected by the
        cts:query.
        This option does not affect the number of fragments selected
        by the cts:query to calculate frequencies.
        Only applies when a $query parameter is specified.
        "truncate=N"
        Include only values from the first N fragments
        after skip selected by the cts:query.
        This option also affects the number of fragments selected
        by the cts:query to calculate frequencies.
        Only applies when a $query parameter is specified.
        "score-logtfidf"
        Compute scores using the logtfidf method.
        Only applies when a $query parameter is specified.
        "score-logtf"
        Compute scores using the logtf method.
        Only applies when a $query parameter is specified.
        "score-simple"
        Compute scores using the simple method.
        Only applies when a $query parameter is specified.
        "score-random"
        Compute scores using the random method.
        Only applies when a $query parameter is specified.
        "score-zero"
        Compute all scores as zero.
        Only applies when a $query parameter is specified.
        "checked"
        Word positions should be checked when resolving the query.
        "unchecked"
        Word positions should not be checked when resolving the query.
        "too-many-positions-error"
        If too much memory is needed to perform positions calculations
        to check whether a document matches a query,
        return an XDMP-TOOMANYPOSITIONS error,
        instead of accepting the document as a match.
        "eager"
        Perform most of the work concurrently before returning
        the first item from the indexes, and only some of the work
        sequentially while iterating through the rest of the items.
        This usually takes the shortest time for a complete item-order
        result or for any frequency-order result.
        "lazy"
        Perform only some the work concurrently before returning
        the first item from the indexes, and most of the work
        sequentially while iterating through the rest of the items.
        This usually takes the shortest time for a small item-order
        partial result.
        "concurrent"
        Perform the work concurrently in another thread. This is a hint
        to the query optimizer to help parallelize the lexicon work, allowing
        the calling query to continue performing other work while the lexicon
        processing occurs.  This is especially useful in cases where multiple
        lexicon calls occur in the same query (for example, resolving many
        facets in a single query).
        "coordinate-system=name"
        Use the lexicon that is configured with the specified coordinate
         system. Allowed values: "wgs84", "wgs84/double", "raw",
         "raw/double". Only applicable if the lexicon value type is
         point or long-lat-point.
        "precision=value"
        Use the lexicon that is configured with the specified precision.
         Allowed values: float and double.
         Only applicable if the lexicon value type is point or
         long-lat-point. This value takes precedence over the
         precision implicit in the coordinate system name.

**`$query`** *(optional)*
Only include values in fragments selected by the cts:query,
    and compute frequencies from this set of included values.
    The values do not need to match the query, but they must occur in
    fragments selected by the query.
    The fragments are not filtered to ensure they match the query,
    but instead selected in the same manner as
    
    "unfiltered" cts:search
    
    operations.  If a string
   is entered, the string is treated as a cts:word-query of the
   specified string.

**`$quality-weight`** *(optional)*
A document quality weight to use when computing scores.
    The default is 1.0.

**`$forest-ids`** *(optional)*
A sequence of IDs of forests to which the search will be constrained.
    An empty sequence means to search all forests in the database.
    The default is ().

### Returns

`element(cts:range)*`

### Usage Notes

Only one of "frequency-order" or "item-order" may be specified
  in the options parameter.  If neither "frequency-order" nor "item-order"
  is specified, then the default is "item-order".
      Only one of "fragment-frequency" or "item-frequency" may be specified
  in the options parameter.  If neither "fragment-frequency" nor
  "item-frequency" is specified, then the default is "fragment-frequency".
      Only one of "ascending" or "descending" may be specified
  in the options parameter.  If neither "ascending" nor "descending"
  is specified, then the default is "ascending" if "item-order" is
  specified, and "descending" if "frequency-order" is specified.
      Only one of "eager" or "lazy" may be specified
  in the options parameter.  If neither "eager" nor "lazy"
  is specified, then the default is "eager" if "frequency-order" or "empties"
  is specified, otherwise "lazy".
      Only one of "any", "document", "properties", or "locks"
  may be specified in the options parameter.
  If none of "any", "document", "properties", or "locks" are specified
  and there is a $query parameter, then the default is "document".
  If there is no $query parameter then the default is "any".
      Only one of the "score-logtfidf", "score-logtf", "score-simple",
  "score-random", or "score-zero" options may be specified in the options
  parameter.
  If none of "score-logtfidf", "score-logtf", "score-simple", "score-random",
  or "score-zero" are specified, then the default is "score-logtfidf".
      Only one of the "checked" or "unchecked" options may be specified
  in the options parameter.
  If neither "checked" nor "unchecked" are specified,
  then the default is "checked".
      If "collation=URI" is not specified in the options parameter,
  then the default collation is used. If a lexicon with that collation
  does not exist, an error is thrown.
      If "sample=N" is not specified in the options parameter,
  then ranges with all included values may be returned. If a
  $query parameter is not present, then "sample=N"
  has no effect.
      If "truncate=N" is not specified in the options parameter,
  then values from all fragments selected by the $query parameter
  are included.  If a $query parameter is not present, then
  "truncate=N" has no effect.
      To incrementally fetch a subset of the values returned by this function,
  use fn:subsequence
  
  on the output, rather than 
  the "skip" option. The "skip" option is based on fragments matching the 
  query parameter (if present), not on values. A fragment 
  matched by query might contain multiple values or no values. 
  The number of fragments skipped does not correspond to the number of 
  values. Also, the skip is applied to the relevance ordered query matches, 
  not to the ordered results list. 
      When using the "skip" option, use the "truncate" option rather than 
  the "limit" option to control the number of matching fragments from which 
  to draw values.

### Examples

#### Example 1

```xquery
(: Run the following to load data for this example.
   Make sure you have an int element range index on
   number. :)
for $x in  (1 to 10)
return
xdmp:document-insert(fn:concat("/doc", fn:string($x), ".xml"),
 <root><number>{$x}</number></root>) ;

(: The following is based on the above setup :)
cts:element-value-ranges(xs:QName("number"),
  (5, 10, 15, 20), "empties")
=>

<cts:range xmlns:cts="http://marklogic.com/cts"
           xmlns:xsi="http://www.w3.org/2001/XMLSchema-instance"
           xmlns:xs="http://www.w3.org/2001/XMLSchema">
  <cts:minimum xsi:type="xs:int">1</cts:minimum>
  <cts:maximum xsi:type="xs:int">4</cts:maximum>
  <cts:upper-bound xsi:type="xs:int">5</cts:upper-bound>
</cts:range>
<cts:range xmlns:cts="http://marklogic.com/cts"
           xmlns:xsi="http://www.w3.org/2001/XMLSchema-instance"
           xmlns:xs="http://www.w3.org/2001/XMLSchema">
  <cts:minimum xsi:type="xs:int">5</cts:minimum>
  <cts:maximum xsi:type="xs:int">9</cts:maximum>
  <cts:lower-bound xsi:type="xs:int">5</cts:lower-bound>
  <cts:upper-bound xsi:type="xs:int">10</cts:upper-bound>
</cts:range>
<cts:range xmlns:cts="http://marklogic.com/cts"
           xmlns:xsi="http://www.w3.org/2001/XMLSchema-instance"
           xmlns:xs="http://www.w3.org/2001/XMLSchema">
  <cts:minimum xsi:type="xs:int">10</cts:minimum>
  <cts:maximum xsi:type="xs:int">10</cts:maximum>
  <cts:lower-bound xsi:type="xs:int">10</cts:lower-bound>
  <cts:upper-bound xsi:type="xs:int">15</cts:upper-bound>
</cts:range>
<cts:range xmlns:cts="http://marklogic.com/cts"
           xmlns:xsi="http://www.w3.org/2001/XMLSchema-instance"
           xmlns:xs="http://www.w3.org/2001/XMLSchema">
  <cts:lower-bound xsi:type="xs:int">15</cts:lower-bound>
  <cts:upper-bound xsi:type="xs:int">20</cts:upper-bound>
</cts:range>
<cts:range xmlns:cts="http://marklogic.com/cts"
           xmlns:xsi="http://www.w3.org/2001/XMLSchema-instance"
           xmlns:xs="http://www.w3.org/2001/XMLSchema">
  <cts:lower-bound xsi:type="xs:int">20</cts:lower-bound>
</cts:range>
```

#### Example 2

```xquery
(: this query has the database fragmented on SPEECH and
     finds four ranges of SPEAKERs :)
  cts:element-value-ranges(xs:QName("SPEAKER"),("F","N","S"));
  =>
  <cts:range xmlns:cts="http://marklogic.com/cts"
      xmlns:xsi="http://www.w3.org/2001/XMLSchema-instance"
      xmlns:xs="http://www.w3.org/2001/XMLSchema">
    <cts:minimum xsi:type="xs:string">All</cts:minimum>
    <cts:maximum xsi:type="xs:string">Danes</cts:maximum>
    <cts:upper-bound xsi:type="xs:string">F</cts:maximum>
  </cts:range>
  <cts:range xmlns:cts="http://marklogic.com/cts"
      xmlns:xsi="http://www.w3.org/2001/XMLSchema-instance"
      xmlns:xs="http://www.w3.org/2001/XMLSchema">
    <cts:minimum xsi:type="xs:string">First Ambassador</cts:minimum>
    <cts:maximum xsi:type="xs:string">Messenger</cts:maximum>
    <cts:lower-bound xsi:type="xs:string">F</cts:maximum>
    <cts:upper-bound xsi:type="xs:string">N</cts:maximum>
  </cts:range>
  <cts:range xmlns:cts="http://marklogic.com/cts"
      xmlns:xsi="http://www.w3.org/2001/XMLSchema-instance"
      xmlns:xs="http://www.w3.org/2001/XMLSchema">
    <cts:minimum xsi:type="xs:string">OPHELIA</cts:minimum>
    <cts:maximum xsi:type="xs:string">ROSENCRANTZ</cts:maximum>
    <cts:lower-bound xsi:type="xs:string">N</cts:maximum>
    <cts:upper-bound xsi:type="xs:string">S</cts:maximum>
  </cts:range>
  <cts:range xmlns:cts="http://marklogic.com/cts"
      xmlns:xsi="http://www.w3.org/2001/XMLSchema-instance"
      xmlns:xs="http://www.w3.org/2001/XMLSchema">
    <cts:minimum xsi:type="xs:string">Second Clown</cts:minimum>
    <cts:maximum xsi:type="xs:string">VOLTIMAND</cts:maximum>
    <cts:lower-bound xsi:type="xs:string">S</cts:maximum>
  </cts:range>
```

---

## cts:element-values

Returns values from the specified element value lexicon(s).
  Value lexicons are implemented using range indexes; consequently this
  function requires an element range index for each element specified
  in the function.  If there is not a range index configured for each
  of the specified elements, an exception is thrown.

### Signature

```xquery
cts:element-values(
  $element-names as xs:QName*,
  $start as xs:anyAtomicType??,
  $options as xs:string*?,
  $query as cts:query??,
  $quality-weight as xs:double??,
  $forest-ids as xs:unsignedLong*?
) as xs:anyAtomicType*
```

### Parameters

**`$element-names`**
One or more element QNames. If you specify multiple lexicons, they
    must all be over the same value type (string, int, etc.).

**`$start`** *(optional)*
A starting value.  The parameter type must match the lexicon type.
    If the parameter value is not in the lexicon, then the values are
    returned beginning with the next value.

**`$options`** *(optional)*
Options.  The default is ().
    
      Options include:
      
        "ascending"
        Values should be returned in ascending order.
        "descending"
        Values should be returned in descending order.
        "any"
        Values from any fragment should be included.
        "document"
        Values from document fragments should be included.
        "properties"
        Values from properties fragments should be included.
        "locks"
        Values from locks fragments should be included.
        "frequency-order"
        Values should be returned ordered by frequency.
        "item-order"
        Values should be returned ordered by item.
        "fragment-frequency"
        Frequency should be the number of fragments with
        an included value.
        This option is used with cts:frequency.
        "item-frequency"
        Frequency should be the number of occurrences of
        an included value.
        This option is used with cts:frequency.
        "type=type"
        Use the lexicon with the type specified by type
        (int, unsignedInt, long, unsignedLong, float, double, decimal,
        dateTime, time, date, gYearMonth, gYear, gMonth, gDay,
        yearMonthDuration, dayTimeDuration, string, or anyURI)
        "collation=URI"
        Use the lexicon with the collation specified by URI.
        "timezone=TZ"
        Return timezone sensitive values (dateTime, time, date,
        gYearMonth, gYear, gMonth, and gDay) adjusted to the timezone
        specified by TZ.
        Example timezones: Z, -08:00, +01:00.
        "limit=N"
        Return no more than N words. You should not
        use this option with the "skip" option. Use "truncate" instead.
        "skip=N"
        Skip over fragments selected by the cts:query
        to treat the Nth fragment as the first fragment.
        Values from skipped fragments are not included.
        This option affects the number of fragments selected
        by the cts:query to calculate frequencies.
        Only applies when a $query parameter is specified.
        "sample=N"
        Return only values from the first N
        fragments after skip selected by the cts:query.
        This option does not affect the number of fragments selected
        by the cts:query to calculate frequencies.
        Only applies when a $query parameter is specified.
        "truncate=N"
        Include only values from the first N fragments
        after skip selected by the cts:query.
        This option also affects the number of fragments selected
        by the cts:query to calculate frequencies.
        Only applies when a $query parameter is specified.
        "score-logtfidf"
        Compute scores using the logtfidf method.
        Only applies when a $query parameter is specified.
        "score-logtf"
        Compute scores using the logtf method.
        Only applies when a $query parameter is specified.
        "score-simple"
        Compute scores using the simple method.
        Only applies when a $query parameter is specified.
        "score-random"
        Compute scores using the random method.
        Only applies when a $query parameter is specified.
        "score-zero"
        Compute all scores as zero.
        Only applies when a $query parameter is specified.
        "checked"
        Word positions should be checked when resolving the query.
        "unchecked"
        Word positions should not be checked when resolving the query.
        "too-many-positions-error"
        If too much memory is needed to perform positions calculations
        to check whether a document matches a query,
        return an XDMP-TOOMANYPOSITIONS error,
        instead of accepting the document as a match.
        "eager"
        Perform most of the work concurrently before returning
        the first item from the indexes, and only some of the work
        sequentially while iterating through the rest of the items.
        This usually takes the shortest time for a complete item-order
        result or for any frequency-order result.
        "lazy"
        Perform only some the work concurrently before returning
        the first item from the indexes, and most of the work
        sequentially while iterating through the rest of the items.
        This usually takes the shortest time for a small item-order
        partial result.
        "concurrent"
        Perform the work concurrently in another thread. This is a hint
        to the query optimizer to help parallelize the lexicon work, allowing
        the calling query to continue performing other work while the lexicon
        processing occurs.  This is especially useful in cases where multiple
        lexicon calls occur in the same query (for example, resolving many
        facets in a single query).
        "map"
        Return results as a single map:map
             value instead of as an xs:anyAtomicType* sequence
             .
        "coordinate-system=name"
        Use the lexicon that is configured with the specified coordinate
         system. Allowed values: "wgs84", "wgs84/double", "raw",
         "raw/double". Only applicable if the lexicon value type is
         point or long-lat-point.
        "precision=value"
        Use the lexicon that is configured with the specified precision.
         Allowed values: float and double.
         Only applicable if the lexicon value type is point or
         long-lat-point. This value takes precedence over the
         precision implicit in the coordinate system name.

**`$query`** *(optional)*
Only include values in fragments selected by the cts:query,
    and compute frequencies from this set of included values.
    The values do not need to match the query, but they must occur in
    fragments selected by the query.
    The fragments are not filtered to ensure they match the query,
    but instead selected in the same manner as
    
    "unfiltered" cts:search
    
    operations.  If a string
   is entered, the string is treated as a cts:word-query of the
   specified string.

**`$quality-weight`** *(optional)*
A document quality weight to use when computing scores.
    The default is 1.0.

**`$forest-ids`** *(optional)*
A sequence of IDs of forests to which the search will be constrained.
    An empty sequence means to search all forests in the database.
    The default is ().

### Returns

`xs:anyAtomicType*`

### Usage Notes

Only one of "frequency-order" or "item-order" may be specified
  in the options parameter.  If neither "frequency-order" nor "item-order"
  is specified, then the default is "item-order".
      Only one of "fragment-frequency" or "item-frequency" may be specified
  in the options parameter.  If neither "fragment-frequency" nor
  "item-frequency" is specified, then the default is "fragment-frequency".
      Only one of "ascending" or "descending" may be specified
  in the options parameter.  If neither "ascending" nor "descending"
  is specified, then the default is "ascending" if "item-order" is
  specified, and "descending" if "frequency-order" is specified.
      Only one of "eager" or "lazy" may be specified
  in the options parameter.  If neither "eager" nor "lazy"
  is specified, then the default is "lazy" if "item-order" is
  specified, and "eager" if "frequency-order" is specified.
      Only one of "any", "document", "properties", or "locks"
  may be specified in the options parameter.
  If none of "any", "document", "properties", or "locks" are specified
  and there is a $query parameter, then the default is "document".
  If there is no $query parameter then the default is "any".
      Only one of the "score-logtfidf", "score-logtf", "score-simple",
  "score-random", or "score-zero" options may be specified in the options
  parameter.
  If none of "score-logtfidf", "score-logtf", "score-simple", "score-random",
  or "score-zero" are specified, then the default is "score-logtfidf".
      Only one of the "checked" or "unchecked" options may be specified
  in the options parameter.
  If neither "checked" nor "unchecked" are specified,
  then the default is "checked".
      If "collation=URI" is not specified in the options parameter,
  then the default collation is used. If a lexicon with that collation
  does not exist, an error is thrown.
      If "sample=N" is not specified in the options parameter,
  then all included values may be returned. If a $query parameter
  is not present, then "sample=N" has no effect.
      If "truncate=N" is not specified in the options parameter,
  then values from all fragments selected by the query parameter
  are included.  If a query parameter is not present, then
  "truncate=N" has no effect.
      To incrementally fetch a subset of the values returned by this function,
  use fn:subsequence
  
  on the output, rather than 
  the "skip" option. The "skip" option is based on fragments matching the 
  query parameter (if present), not on values. A fragment 
  matched by query might contain multiple values or no values. 
  The number of fragments skipped does not correspond to the number of 
  values. Also, the skip is applied to the relevance ordered query matches, 
  not to the ordered values list. 
      When using the "skip" option, use the "truncate" option rather than 
  the "limit" option to control the number of matching fragments from which 
  to draw values.

### Examples

```xquery
(:
  an element range index must exist on "animal" or
  this example throws XDMP-ELEMRIDXNOTFOUND
:)
  cts:element-values(xs:QName("animal"),"aardvark")
  => ("aardvark","aardvarks","aardwolf",...)
```

---

## cts:element-word-match

Returns words from the specified element word lexicon(s) that match
  a wildcard pattern.   This function requires an element word lexicon
  configured for each of the specified elements in the function.  If there
  is not an element word lexicon configured for any of the specified
  elements, an exception is thrown.

### Signature

```xquery
cts:element-word-match(
  $element-names as xs:QName*,
  $pattern as xs:string?,
  $options as xs:string*?,
  $query as cts:query??,
  $quality-weight as xs:double??,
  $forest-ids as xs:unsignedLong*?
) as xs:string*
```

### Parameters

**`$element-names`**
One or more element QNames.

**`$pattern`**
Wildcard pattern to match.

**`$options`** *(optional)*
Options.  The default is ().
    
      Options include:
      
        "case-sensitive"
        A case-sensitive match.
        "case-insensitive"
        A case-insensitive match.
        "diacritic-sensitive"
        A diacritic-sensitive match.
        "diacritic-insensitive"
        A diacritic-insensitive match.
        "ascending"
        Words should be returned in ascending order.
        "descending"
        Words should be returned in descending order.
        "any"
        Words from any fragment should be included.
        "document"
        Words from document fragments should be included.
        "properties"
        Words from properties fragments should be included.
        "locks"
        Words from locks fragments should be included.
        "collation=URI"
        Use the lexicon with the collation specified by URI.
        "limit=N"
        Return no more than N words. You should not
        use this option with the "skip" option. Use "truncate" instead.
        "skip=N"
        Skip over fragments selected by the cts:query
        to treat the Nth fragment as the first fragment.
        Words from skipped fragments are not included.
        Only applies when a $query parameter is specified.
        "sample=N"
        Return only words from the first N fragments after skip
        selected by the cts:query.
        Only applies when a $query parameter is specified.
        "truncate=N"
        Include only words from the first N fragments after skip
        selected by the cts:query.
        Only applies when a $query parameter is specified.
        "score-logtfidf"
        Compute scores using the logtfidf method.
        Only applies when a $query parameter is specified.
        "score-logtf"
        Compute scores using the logtf method.
        Only applies when a $query parameter is specified.
        "score-simple"
        Compute scores using the simple method.
        Only applies when a $query parameter is specified.
        "score-random"
        Compute scores using the random method.
        Only applies when a $query parameter is specified.
        "score-zero"
        Compute all scores as zero.
        Only applies when a $query parameter is specified.
        "checked"
        Word positions should be checked when resolving the query.
        "unchecked"
        Word positions should not be checked when resolving the query.
        "too-many-positions-error"
        If too much memory is needed to perform positions calculations
        to check whether a document matches a query,
        return an XDMP-TOOMANYPOSITIONS error,
        instead of accepting the document as a match.
        "concurrent"
        Perform the work concurrently in another thread. This is a hint
        to the query optimizer to help parallelize the lexicon work, allowing
        the calling query to continue performing other work while the lexicon
        processing occurs.  This is especially useful in cases where multiple
        lexicon calls occur in the same query (for example, resolving many
        facets in a single query).
        "map"
        Return results as a single map:map
         value instead of as an xs:string* sequence
         .

**`$query`** *(optional)*
Only include words in fragments selected by the cts:query.
    The words do not need to match the query, but the words must occur
    in fragments selected by the query.
    The fragments are not filtered to ensure they match the query,
    but instead selected in the same manner as
    
    "unfiltered" cts:search
    
    operations.  If a string
   is entered, the string is treated as a cts:word-query of the
   specified string.

**`$quality-weight`** *(optional)*
A document quality weight to use when computing scores.
    The default is 1.0.

**`$forest-ids`** *(optional)*
A sequence of IDs of forests to which the search will be constrained.
    An empty sequence means to search all forests in the database.
    The default is ().

### Returns

`xs:string*`

### Usage Notes

Only one of "ascending" or "descending" may be specified
  in the options parameter.  If neither "ascending" nor "descending"
  is specified, then the default is "ascending".
      Only one of "any", "document", "properties", or "locks"
  may be specified in the options parameter.
  If none of "any", "document", "properties", or "locks" are specified
  and there is a $query parameter, then the default is "document".
  If there is no $query parameter then the default is "any".
      Only one of the "score-logtfidf", "score-logtf", "score-simple",
  "score-random", or "score-zero" options may be specified in the options
  parameter.
  If none of "score-logtfidf", "score-logtf", "score-simple", "score-random",
  or "score-zero" are specified, then the default is "score-logtfidf".
      Only one of the "checked" or "unchecked" options may be specified
  in the options parameter.
  If neither "checked" nor "unchecked" are specified,
  then the default is "checked".
      If "collation=URI" is not specified in the options parameter,
  then the default collation is used. If a lexicon with that collation
  does not exist, an error is thrown.
      If "sample=N" is not specified in the options parameter,
  then all included words may be returned. If a $query parameter
  is not present, then "sample=N" has no effect.
      If "truncate=N" is not specified in the options parameter,
  then words from all fragments selected by the $query parameter
  are included.  If a $query parameter is not present, then
  "truncate=N" has no effect.
      To incrementally fetch a subset of the values returned by this function,
  use fn:subsequence
  
  on the output, rather than 
  the "skip" option. The "skip" option is based on fragments matching the 
  query parameter (if present), not on values. A fragment 
  matched by query might contain multiple values or no values. 
  The number of fragments skipped does not correspond to the number of 
  values. Also, the skip is applied to the relevance ordered query matches, 
  not to the ordered values list. 
      When using the "skip" option, use the "truncate" option rather than 
  the "limit" option to control the number of matching fragments from which 
  to draw values.
      
    If neither "case-sensitive" nor "case-insensitive"
    is present, $pattern is used to determine case sensitivity.
    If $pattern contains no uppercase, it specifies "case-insensitive".
    If $pattern contains uppercase, it specifies "case-sensitive".
  
      
    If neither "diacritic-sensitive" nor "diacritic-insensitive"
    is present, $pattern is used to determine diacritic sensitivity.
    If $pattern contains no diacritics, it specifies "diacritic-insensitive".
    If $pattern contains diacritics, it specifies "diacritic-sensitive".
  
      Only words that can be matched with element-word-query are included.
  That is, only words present in immediate text node children of the
  specified element as well as any text node children of child elements
  defined in the Admin Interface as element-word-query-throughs or
  phrase-throughs.

### Examples

```xquery
(:
 an element word lexicon must exist on "animal" or
 this example throws XDMP-ELEMLXCNNOTFOUND
:)
  cts:element-word-match(xs:QName("animal"),"aardvark*")
  => ("aardvark","aardvarks")
```

---

## cts:element-words

Returns words from the specified element word lexicon.  This function
  requires an element word lexicon for each of the element specified in the
  function.  If there is not an element word lexicon configured for any
  of the specified elements, an exception is thrown.  The words are
  returned in collation order.

### Signature

```xquery
cts:element-words(
  $element-names as xs:QName*,
  $start as xs:string??,
  $options as xs:string*?,
  $query as cts:query??,
  $quality-weight as xs:double??,
  $forest-ids as xs:unsignedLong*?
) as xs:string*
```

### Parameters

**`$element-names`**
One or more element QNames.

**`$start`** *(optional)*
A starting word.  Returns only this word and any following words
    from the lexicon.  If the parameter is not in the lexicon, then it
    returns the words beginning with the next word.

**`$options`** *(optional)*
Options.  The default is ().
    
      Options include:
      
        "ascending"
        Words should be returned in ascending order.
        "descending"
        Words should be returned in descending order.
        "any"
        Words from any fragment should be included.
        "document"
        Words from document fragments should be included.
        "properties"
        Words from properties fragments should be included.
        "locks"
        Words from locks fragments should be included.
        "collation=URI"
        Use the lexicon with the collation specified by URI.
        "limit=N"
        Return no more than N words. You should not
        use this option with the "skip" option. Use "truncate" instead.
        "skip=N"
        Skip over fragments selected by the cts:query
        to treat the Nth fragment as the first fragment.
        Words from skipped fragments are not included.
        Only applies when a $query parameter is specified.
        "sample=N"
        Return only words from the first N fragments after skip
        selected by the cts:query.
        Only applies when a $query parameter is specified.
        "truncate=N"
        Include only words from the first N fragments after skip
        selected by the cts:query.
        Only applies when a $query parameter is specified.
        "score-logtfidf"
        Compute scores using the logtfidf method.
        Only applies when a $query parameter is specified.
        "score-logtf"
        Compute scores using the logtf method.
        Only applies when a $query parameter is specified.
        "score-simple"
        Compute scores using the simple method.
        Only applies when a $query parameter is specified.
        "score-random"
        Compute scores using the random method.
        Only applies when a $query parameter is specified.
        "score-zero"
        Compute all scores as zero.
        Only applies when a $query parameter is specified.
        "checked"
        Word positions should be checked when resolving the query.
        "unchecked"
        Word positions should not be checked when resolving the query.
        "too-many-positions-error"
        If too much memory is needed to perform positions calculations
        to check whether a document matches a query,
        return an XDMP-TOOMANYPOSITIONS error,
        instead of accepting the document as a match.
        "concurrent"
        Perform the work concurrently in another thread. This is a hint
        to the query optimizer to help parallelize the lexicon work, allowing
        the calling query to continue performing other work while the lexicon
        processing occurs.  This is especially useful in cases where multiple
        lexicon calls occur in the same query (for example, resolving many
        facets in a single query).
        "map"
        Return results as a single map:map
         value instead of as an xs:string* sequence
         .

**`$query`** *(optional)*
Only include words in fragments selected by the cts:query.
    The words do not need to match the query, but the words must occur
    in fragments selected by the query.
    The fragments are not filtered to ensure they match the query,
    but instead selected in the same manner as
    
    "unfiltered" cts:search
    
    operations.  If a string
   is entered, the string is treated as a cts:word-query of the
   specified string.

**`$quality-weight`** *(optional)*
A document quality weight to use when computing scores.
    The default is 1.0.

**`$forest-ids`** *(optional)*
A sequence of IDs of forests to which the search will be constrained.
    An empty sequence means to search all forests in the database.
    The default is ().

### Returns

`xs:string*`

### Usage Notes

Only one of "ascending" or "descending" may be specified
  in the options parameter.  If neither "ascending" nor "descending"
  is specified, then the default is "ascending".
      Only one of "any", "document", "properties", or "locks"
  may be specified in the options parameter.
  If none of "any", "document", "properties", or "locks" are specified
  and there is a $query parameter, then the default is "document".
  If there is no $query parameter then the default is "any".
      Only one of the "score-logtfidf", "score-logtf", "score-simple",
  "score-random", or "score-zero" options may be specified in the options
  parameter.
  If none of "score-logtfidf", "score-logtf", "score-simple", "score-random",
  or "score-zero" are specified, then the default is "score-logtfidf".
      Only one of the "checked" or "unchecked" options may be specified
  in the options parameter.
  If neither "checked" nor "unchecked" are specified,
  then the default is "checked".
      If "collation=URI" is not specified in the options parameter,
  then the default collation is used. If a lexicon with that collation
  does not exist, an error is thrown.
      If "sample=N" is not specified in the options parameter,
  then all included words may be returned. If a $query parameter
  is not present, then "sample=N" has no effect.
      If "truncate=N" is not specified in the options parameter,
  then words from all fragments selected by the $query parameter
  are included.  If a $query parameter is not present, then
  "truncate=N" has no effect.
      Only words that can be matched with element-word-query are included.
  That is, only words present in immediate text node children of the
  specified element as well as any text node children of child elements
  defined in the Admin Interface as element-word-query-throughs or
  phrase-throughs. 
      When run without a $query parameter and as a user with the admin role,
  the word lexicon functions return results that might include words from
  deleted fragments. However, when run as a user with the admin role and
  without a $query parameter, the word lexicon functions run faster (because
  they do not need to look up where each word comes from). It is therefore
  faster to run word lexicon functions as an admin user without passing a
  $query parameter.
      To incrementally fetch a subset of the values returned by this function, 
  use fn:subsequence
  
  on the output, rather than 
  the "skip" option. The "skip" option is based on fragments matching the 
  query parameter (if present), not on values. A fragment 
  matched by query might contain multiple values or no values. 
  The number of fragments skipped does not correspond to the number of 
  values. Also, the skip is applied to the relevance ordered query matches, 
  not to the ordered values list. 
      When using the "skip" option, use the "truncate" option rather than 
  the "limit" option to control the number of matching fragments from which 
  to draw values.

### Examples

```xquery
(:
 an element word lexicon must exist on "animal" or
 this example throws XDMP-ELEMLXCNNOTFOUND
:)
  cts:element-words(xs:QName("animal"),"aardvark")
  => ("aardvark","aardvarks","aardwolf",...)
```

---

## cts:field-reference

Creates a reference to a field value lexicon, for use as a
  parameter to 
  cts:value-tuples.
  Since lexicons are implemented with range indexes, this function will 
  throw an exception if the specified range index does not exist.

### Signature

```xquery
cts:field-reference(
  $field as xs:string,
  $options as xs:string*?
) as cts:reference
```

### Parameters

**`$field`**
A field name.

**`$options`** *(optional)*
Options.  The default is ().
    
      Options include:
      
        "type=type"
        Use the lexicon with the type specified by type
        (int, unsignedInt, long, unsignedLong, float, double, decimal,
        dateTime, time, date, gYearMonth, gYear, gMonth, gDay,
        yearMonthDuration, dayTimeDuration, string, anyURI, point, or
        long-lat-point)
        "collation=URI"
        Use the lexicon with the collation specified by URI.
        "nullable"
        Allow null values in tuples reported from cts:value-tuples when
        using this lexicon.
        "unchecked"
        Read the scalar type, collation and coordinate-system info
        only from the input. Do not check the definition against the
        context database.
        "coordinate-system=name"
        Create a reference to an index or lexicon based on the specified
         coordinate system. Allowed values: "wgs84", "wgs84/double", "raw",
         "raw/double". Only applicable if the index/lexicon value type is
         point or long-lat-point.
        "precision=value"
        Create a reference to an index or lexicon configured with the
         specified geospatial precision. Allowed values: float
         and double. Only applicable if the index/lexicon value
         type is point or long-lat-point. This
         value takes precedence over the precision implicit in the coordinate
         system name.

### Returns

`cts:reference`

### Examples

```xquery
cts:field-reference("authors",("collation=http://marklogic.com/collation/en"))
=>
cts:field-reference("authors",
  ("type=string","collation=http://marklogic.com/collation/en"))
```

---

## cts:field-value-co-occurrences

Returns value co-occurrences (that is, pairs of values, both of which appear
  in the same fragment) from the specified field value lexicon(s).  The
  values are returned as an XML element
   with two children, each child
  containing one of the co-occurring values.  You can use
  cts:frequency
  on each item returned to find how many times the pair occurs.
  Value lexicons are implemented using range indexes; consequently
  this function requires an field range index for each field specified
  in the function.  If there is not a range index configured for each
  of the specified fields, an exception is thrown.

### Signature

```xquery
cts:field-value-co-occurrences(
  $field-name-1 as xs:string,
  $field-name-2 as xs:string,
  $options as xs:string*?,
  $query as cts:query??,
  $quality-weight as xs:double??,
  $forest-ids as xs:unsignedLong*?
) as element(cts:co-occurrence)*
```

### Parameters

**`$field-name-1`**
A string.

**`$field-name-2`**
A string.

**`$options`** *(optional)*
Options.  The default is ().
    
      Options include:
      
        "ascending"
        Co-occurrences should be returned in ascending order.
        "descending"
        Co-occurrences should be returned in descending order.
        "any"
        Co-occurrences from any fragment should be included.
        "document"
        Co-occurrences from document fragments should be included.
        "properties"
        Co-occurrences from properties fragments should be included.
        "locks"
        Co-occurrences from locks fragments should be included.
        "frequency-order"
        Co-occurrences should be returned ordered by frequency.
        "item-order"
        Co-occurrences should be returned ordered by item.
        "fragment-frequency"
        Frequency should be the number of fragments with
        an included co-occurrences.
        This option is used with cts:frequency.
        "item-frequency"
        Frequency should be the number of occurrences of
        an included co-occurrence.
        This option is used with cts:frequency.
        "type=type"
        For both lexicons, use the type specified by type
        (int, unsignedInt, long, unsignedLong, float, double, decimal,
        dateTime, time, date, gYearMonth, gYear, gMonth, gDay,
        yearMonthDuration, dayTimeDuration, string, or anyURI)
        "type-1=type"
        For the first lexicon, use the type specified by type
        (int, unsignedInt, long, unsignedLong, float, double, decimal,
        dateTime, time, date, gYearMonth, gYear, gMonth, gDay,
        yearMonthDuration, dayTimeDuration, string, or anyURI)
        "type-2=type"
        For the second lexicon, use the type specified by type
        (int, unsignedInt, long, unsignedLong, float, double, decimal,
        dateTime, time, date, gYearMonth, gYear, gMonth, gDay,
        yearMonthDuration, dayTimeDuration, string, or anyURI)
        "collation=URI"
        For both lexicons, use the collation specified by
        URI.
        "collation-1=URI"
        For the first lexicon, use the collation specified by
        URI.
        "collation-2=URI"
        For the second lexicon, use the collation specified by
        URI.
        "timezone=TZ"
        Return timezone sensitive values (dateTime, time, date,
        gYearMonth, gYear, gMonth, and gDay) adjusted to the timezone
        specified by TZ.
        Example timezones: Z, -08:00, +01:00.
        "ordered"
        Include co-occurrences only when the value from the first lexicon
        appears before the value from the second lexicon.
        Requires that word positions be enabled for both lexicons.
        "proximity=N"
        Include co-occurrences only when the values appear within
        N words of each other.
        Requires that word positions be enabled for both lexicons.
        "limit=N"
        Return no more than N co-occurrences. You should not
        use this option with the "skip" option. Use "truncate" instead.
        "skip=N"
        Skip over fragments selected by the cts:query
        to treat the Nth fragment as the first fragment.
        Co-occurrences from skipped fragments are not included.
        This option affects the number of fragments selected
        by the cts:query to calculate frequencies.
        Only applies when a $query parameter is specified.
        "sample=N"
        Return only co-occurrences from the first N
        fragments after skip selected by the cts:query.
        This option does not affect the number of fragments selected
        by the cts:query to calculate frequencies.
        Only applies when a $query parameter is specified.
        Return only co-occurrences from the first N
        fragments after skip selected by the cts:query,
        bit do not affect frequencies.
        Only applies when a $query parameter is specified.
        "truncate=N"
        Include only co-occurrences from the first N
        fragments after skip selected by the cts:query.
        This option also affects the number of fragments selected
        by the cts:query to calculate frequencies.
        Only applies when a $query parameter is specified.
        "score-logtfidf"
        Compute scores using the logtfidf method.
        Only applies when a $query parameter is specified.
        "score-logtf"
        Compute scores using the logtf method.
        Only applies when a $query parameter is specified.
        "score-simple"
        Compute scores using the simple method.
        Only applies when a $query parameter is specified.
        "score-random"
        Compute scores using the random method.
        Only applies when a $query parameter is specified.
        "score-zero"
        Compute all scores as zero.
        Only applies when a $query parameter is specified.
        "checked"
        Word positions should be checked when resolving the query.
        "unchecked"
        Word positions should not be checked when resolving the query.
        "too-many-positions-error"
        If too much memory is needed to perform positions calculations
        to check whether a document matches a query,
        return an XDMP-TOOMANYPOSITIONS error,
        instead of accepting the document as a match.
        "eager"
        Perform most of the work concurrently before returning
        the first item from the indexes, and only some of the work
        sequentially while iterating through the rest of the items.
        This usually takes the shortest time for a complete item-order
        result or for any frequency-order result.
        "lazy"
        Perform only some the work concurrently before returning
        the first item from the indexes, and most of the work
        sequentially while iterating through the rest of the items.
        This usually takes the shortest time for a small item-order
        partial result.
        "concurrent"
        Perform the work concurrently in another thread. This is a hint
        to the query optimizer to help parallelize the lexicon work, allowing
        the calling query to continue performing other work while the lexicon
        processing occurs.  This is especially useful in cases where multiple
        lexicon calls occur in the same query (for example, resolving many
        facets in a single query).
        "map"
        Return results as a single map:map
         value instead of as an element(cts:co-occurrence)* sequence
         .
        "coordinate-system=name"
        Use the lexicon that is configured with the specified coordinate
         system. Allowed values: "wgs84", "wgs84/double", "raw",
         "raw/double". Only applicable if the lexicon value type is
         point or long-lat-point.
        "precision=value"
        Use the lexicon that is configured with the specified precision.
         Allowed values: float and double.
         Only applicable if the lexicon value type is point or
         long-lat-point. This value takes precedence over the
         precision implicit in the coordinate system name.

**`$query`** *(optional)*
Only include co-occurrences in fragments selected by the cts:query,
    and compute frequencies from this set of included co-occurrences.
    The co-occurrences do not need to match the query, but they must occur in
    fragments selected by the query.
    The fragments are not filtered to ensure they match the query,
    but instead selected in the same manner as
    
    "unfiltered" cts:search
    
    operations.  If a string
   is entered, the string is treated as a cts:word-query of the
   specified string.

**`$quality-weight`** *(optional)*
A document quality weight to use when computing scores.
    The default is 1.0.

**`$forest-ids`** *(optional)*
A sequence of IDs of forests to which the search will be constrained.
    An empty sequence means to search all forests in the database.
    The default is ().

### Returns

`element(cts:co-occurrence)*`

### Usage Notes

Only one of "frequency-order" or "item-order" may be specified
  in the options parameter.  If neither "frequency-order" nor "item-order"
  is specified, then the default is "item-order".
      Only one of "fragment-frequency" or "item-frequency" may be specified
  in the options parameter.  If neither "fragment-frequency" nor
  "item-frequency" is specified, then the default is "fragment-frequency".
      Only one of "ascending" or "descending" may be specified
  in the options parameter.  If neither "ascending" nor "descending"
  is specified, then the default is "ascending" if "item-order" is
  specified, and "descending" if "frequency-order" is specified.
      Only one of "eager" or "lazy" may be specified
  in the options parameter.  If neither "eager" nor "lazy"
  is specified, then the default is "eager" if "frequency-order" or "map"
  is specified, otherwise "lazy".
      Only one of "any", "document", "properties", or "locks"
  may be specified in the options parameter.
  If none of "any", "document", "properties", or "locks" are specified
  and there is a $query parameter, then the default is "document".
  If there is no $query parameter then the default is "any".
      Only one of the "score-logtfidf", "score-logtf", "score-simple",
  "score-random", or "score-zero" options may be specified in the options
  parameter.
  If none of "score-logtfidf", "score-logtf", "score-simple", "score-random",
  or "score-zero" are specified, then the default is "score-logtfidf".
      Only one of the "checked" or "unchecked" options may be specified
  in the options parameter.
  If neither "checked" nor "unchecked" are specified,
  then the default is "checked".
      If "collation=URI" is not specified in the options parameter,
  then the default collation is used. If a lexicon with that collation
  does not exist, an error is thrown.
      If "sample=N" is not specified in the options parameter,
  then all included co-occurrences may be returned.
  If a $query parameter
  is not present, then "sample=N" has no effect.
      If "truncate=N" is not specified in the options parameter,
  then co-occurrences from all fragments selected by the
  $query parameter are included.
  If a $query parameter is not present, then
  "truncate=N" has no effect.
      To incrementally fetch a subset of the co-occurrences returned by this
  function, use fn:subsequence
  
  on the output, rather than 
  the "skip" option. The "skip" option is based on fragments matching the 
  query parameter (if present), not on values. A fragment 
  matched by query might contain multiple occurrences or no occurrences. 
  The number of fragments skipped does not correspond to the number of 
  values. Also, the skip is applied to the relevance ordered query matches, 
  not to the ordered co-occurrences list. 
      When using the "skip" option, use the "truncate" option rather than 
  the "limit" option to control the number of matching fragments from which 
  to draw values.

### Examples

#### Example 1

```xquery
(: Suppose we insert these two documents in the database.

  Document 1:
  <doc>
  <name1>
    <i11>John</i11><e12>Smith</e12><i13>Griffith</i13>
  </name1>
  <name2>
    <i21>Will</i21><e22>Tim</e22><i23>Shields</i23>
  </name2>
 </doc>

  Document 2:
  <doc>
  <name1>
    <i11>Will<e12>Frank</e12>Shields</i11>
  </name1>
  <name2>
    <i21>John<e22>Tim</e22>Griffith</i21>
  </name2>
</doc>
:)

 (: Now suppose we have two fields aname1 and aname2 defined on the database.
    The field aname1 includes element "name1" and excludes "e12".
    The field aname2 includes element "name2" and excludes "e22".
    Both the fields have field range indexes configures with positions ON.
 :)

  cts:field-value-co-occurrences("aname1","aname2")
=>
<cts:co-occurrence
  xmlns:cts="http://marklogic.com/cts"
  xmlns:xsi="http://www.w3.org/2001/XMLSchema-instance"
  xmlns:xs="http://www.w3.org/2001/XMLSchema">
  <cts:value xsi:type="xs:string">John Griffith</cts:value>
  <cts:value xsi:type="xs:string">Will Shields</cts:value>
</cts:co-occurrence>
<cts:co-occurrence
  xmlns:cts="http://marklogic.com/cts"
  xmlns:xsi="http://www.w3.org/2001/XMLSchema-instance"
  xmlns:xs="http://www.w3.org/2001/XMLSchema">
  <cts:value xsi:type="xs:string">Will Shields</cts:value>
  <cts:value xsi:type="xs:string">John Griffith</cts:value>
</cts:co-occurrence>
```

#### Example 2

```xquery
(: Here is another example that finds co-occurrence between field value
     and an element-value using cts:element-value-co-occurrences() API. :)

  (: Suppose we have the following document in the database. :)
<doc>
 <person>
  <name>
    <first-name>Will</first-name>
    <middle-name>Frank</middle-name>
    <last-name>Shields</last-name>
  </name>
  <address>
    <ZIP>92341</ZIP>
  </address>
  <phoneNumber>650-472-4444</phoneNumber>
 </person>
 <person>
  <name>
    <first-name>John</first-name>
    <middle-name>Tim</middle-name>
    <last-name>Hearst</last-name>
  </name>
  <address>
    <ZIP>96345</ZIP>
  </address>
  <phoneNumber>750-947-5555</phoneNumber>
 </person>
</doc>
  (: This database has element range indexes defined on elements
     ZIP and phoneNumber. Positions are set true on the range indexes.

     There is a field, named "aname" defined on this database
     which excludes element middle-name.

     A string range index is configured on the field "aname".
     Position is set true on the database.

     In the following query we are using lexicons on field values of
     "aname" and element value "ZIP" to determine value co-occurrences.
     However, notice the field is being treated as if it were an
     element with a MarkLogic predefined namespace
     "http://marklogic.com/fields".
  :)
declare namespace my="http://marklogic.com/fields";
cts:element-value-co-occurrences(xs:QName("ZIP"),xs:QName("my:aname"))
  =>
<cts:co-occurrence
   xmlns:cts="http://marklogic.com/cts"
   xmlns:xsi="http://www.w3.org/2001/XMLSchema-instance"
   xmlns:xs="http://www.w3.org/2001/XMLSchema">
  <cts:value xsi:type="xs:int">68645</cts:value>
  <cts:value xsi:type="xs:string">Jill Tom Lawless</cts:value>
</cts:co-occurrence>
<cts:co-occurrence
  xmlns:cts="http://marklogic.com/cts"
  xmlns:xsi="http://www.w3.org/2001/XMLSchema-instance"
  xmlns:xs="http://www.w3.org/2001/XMLSchema">
  <cts:value xsi:type="xs:int">68645</cts:value>
  <cts:value xsi:type="xs:string">Nancy Smith Finkman</cts:value>
</cts:co-occurrence>
<cts:co-occurrence
   xmlns:cts="http://marklogic.com/cts"
   xmlns:xsi="http://www.w3.org/2001/XMLSchema-instance"
   xmlns:xs="http://www.w3.org/2001/XMLSchema">
  <cts:value xsi:type="xs:int">92341</cts:value>
  <cts:value xsi:type="xs:string">John Tim Hearst</cts:value>
</cts:co-occurrence>
<cts:co-occurrence
   xmlns:cts="http://marklogic.com/cts"
   xmlns:xsi="http://www.w3.org/2001/XMLSchema-instance"
   xmlns:xs="http://www.w3.org/2001/XMLSchema">
  <cts:value xsi:type="xs:int">92341</cts:value>
  <cts:value xsi:type="xs:string">Will Frank Shields</cts:value>
</cts:co-occurrence>
<cts:co-occurrence
   xmlns:cts="http://marklogic.com/cts"
   xmlns:xsi="http://www.w3.org/2001/XMLSchema-instance"
   xmlns:xs="http://www.w3.org/2001/XMLSchema">
  <cts:value xsi:type="xs:int">93452</cts:value>
  <cts:value xsi:type="xs:string">Jill Tom Lawless</cts:value>
</cts:co-occurrence>
<cts:co-occurrence
   xmlns:cts="http://marklogic.com/cts"
   xmlns:xsi="http://www.w3.org/2001/XMLSchema-instance"
   xmlns:xs="http://www.w3.org/2001/XMLSchema">
  <cts:value xsi:type="xs:int">93452</cts:value>
  <cts:value xsi:type="xs:string">Nancy Smith Finkman</cts:value>
</cts:co-occurrence>
<cts:co-occurrence
  xmlns:cts="http://marklogic.com/cts"
  xmlns:xsi="http://www.w3.org/2001/XMLSchema-instance"
  xmlns:xs="http://www.w3.org/2001/XMLSchema">
  <cts:value xsi:type="xs:int">96345</cts:value>
  <cts:value xsi:type="xs:string">John Tim Hearst</cts:value>
</cts:co-occurrence>
<cts:co-occurrence
  xmlns:cts="http://marklogic.com/cts"
  xmlns:xsi="http://www.w3.org/2001/XMLSchema-instance"
  xmlns:xs="http://www.w3.org/2001/XMLSchema">
  <cts:value xsi:type="xs:int">96345</cts:value>
  <cts:value xsi:type="xs:string">Will Frank Shields</cts:value>
</cts:co-occurrence>
```

---

## cts:field-value-match

Returns values from the specified field value lexicon(s)
   that match the specified wildcard pattern.  Field value lexicons
   are implemented using range indexes; consequently this function
   requires a field range index for each field specified in the
   function.  If there is not a range index configured for each of the
   specified fields, then an exception is thrown.

### Signature

```xquery
cts:field-value-match(
  $field-names as xs:string*,
  $pattern as xs:anyAtomicType,
  $options as xs:string*?,
  $query as cts:query??,
  $quality-weight as xs:double??,
  $forest-ids as xs:unsignedLong*?
) as xs:anyAtomicType*
```

### Parameters

**`$field-names`**
One or more field names.

**`$pattern`**
A pattern to match.  The parameter type must match the lexicon type.
    String parameters may include wildcard characters.

**`$options`** *(optional)*
Options.  The default is ().
    
      Options include:
      
        "case-sensitive"
        A case-sensitive match.
        "case-insensitive"
        A case-insensitive match.
        "diacritic-sensitive"
        A diacritic-sensitive match.
        "diacritic-insensitive"
        A diacritic-insensitive match.
        "ascending"
        Values should be returned in ascending order.
        "descending"
        Values should be returned in descending order.
        "any"
        Values from any fragment should be included.
        "document"
        Values from document fragments should be included.
        "properties"
        Values from properties fragments should be included.
        "locks"
        Values from locks fragments should be included.
        "frequency-order"
        Values should be returned ordered by frequency.
        "item-order"
        Values should be returned ordered by item.
        "fragment-frequency"
        Frequency should be the number of fragments with
        an included value.
        This option is used with cts:frequency.
        "item-frequency"
        Frequency should be the number of occurrences of
        an included value.
        This option is used with cts:frequency.
        "type=type"
        Use the lexicon with the type specified by type
        (int, unsignedInt, long, unsignedLong, float, double, decimal,
        dateTime, time, date, gYearMonth, gYear, gMonth, gDay,
        yearMonthDuration, dayTimeDuration, string, or anyURI)
        "collation=URI"
        Use the range index with the collation specified by
        URI.
        "timezone=TZ"
        Return timezone sensitive values (dateTime, time, date,
        gYearMonth, gYear, gMonth, and gDay) adjusted to the timezone
        specified by TZ.
        Example timezones: Z, -08:00, +01:00.
        "limit=N"
        Return no more than N values. You should not
        use this option with the "skip" option. Use "truncate" instead.
        "skip=N"
        Skip over fragments selected by the cts:query
        to treat the Nth fragment as the first fragment.
        Values from skipped fragments are not included.
        This option affects the number of fragments selected
        by the cts:query to calculate frequencies.
        Only applies when a $query parameter is specified.
        "sample=N"
        Return only values from the first N
        fragments after skip selected by the cts:query.
        This option does not affect the number of fragments selected
        by the cts:query to calculate frequencies.
        Only applies when a $query parameter is specified.
        "truncate=N"
        Include only values from the first N fragments
        after skip selected by the cts:query.
        This option also affects the number of fragments selected
        by the cts:query to calculate frequencies.
        Only applies when a $query parameter is specified.
        "score-logtfidf"
        Compute scores using the logtfidf method.
        Only applies when a $query parameter is specified.
        "score-logtf"
        Compute scores using the logtf method.
        Only applies when a $query parameter is specified.
        "score-simple"
        Compute scores using the simple method.
        Only applies when a $query parameter is specified.
        "score-random"
        Compute scores using the random method.
        Only applies when a $query parameter is specified.
        "score-zero"
        Compute all scores as zero.
        Only applies when a $query parameter is specified.
        "checked"
        Word positions should be checked when resolving the query.
        "unchecked"
        Word positions should not be checked when resolving the query.
        "too-many-positions-error"
        If too much memory is needed to perform positions calculations
        to check whether a document matches a query,
        return an XDMP-TOOMANYPOSITIONS error,
        instead of accepting the document as a match.
        "eager"
        Perform most of the work concurrently before returning
        the first item from the indexes, and only some of the work
        sequentially while iterating through the rest of the items.
        This usually takes the shortest time for a complete item-order
        result or for any frequency-order result.
        "lazy"
        Perform only some the work concurrently before returning
        the first item from the indexes, and most of the work
        sequentially while iterating through the rest of the items.
        This usually takes the shortest time for a small item-order
        partial result.
        "concurrent"
        Perform the work concurrently in another thread. This is a hint
        to the query optimizer to help parallelize the lexicon work, allowing
        the calling query to continue performing other work while the lexicon
        processing occurs.  This is especially useful in cases where multiple
        lexicon calls occur in the same query (for example, resolving many
        facets in a single query).
        "map"
        Return results as a single
         map:map value instead of as an xs:anyAtomicType* sequence
         .
        "coordinate-system=name"
        Use the lexicon that is configured with the specified coordinate
         system. Allowed values: "wgs84", "wgs84/double", "raw",
         "raw/double". Only applicable if the lexicon value type is
         point or long-lat-point.
        "precision=value"
        Use the lexicon that is configured with the specified precision.
         Allowed values: float and double.
         Only applicable if the lexicon value type is point or
         long-lat-point. This value takes precedence over the
         precision implicit in the coordinate system name.

**`$query`** *(optional)*
Only include values in fragments selected by the cts:query,
    and compute frequencies from this set of included values.
    The values do not need to match the query, but they must occur in
    fragments selected by the query.
    The fragments are not filtered to ensure they match the query,
    but instead selected in the same manner as
    
    "unfiltered" cts:search
    
    operations.  If a string
   is entered, the string is treated as a cts:word-query of the
   specified string.

**`$quality-weight`** *(optional)*
A document quality weight to use when computing scores.
    The default is 1.0.

**`$forest-ids`** *(optional)*
A sequence of IDs of forests to which the search will be constrained.
    An empty sequence means to search all forests in the database.
    The default is ().

### Returns

`xs:anyAtomicType*`

### Usage Notes

Only one of "frequency-order" or "item-order" may be specified
  in the options parameter.  If neither "frequency-order" nor "item-order"
  is specified, then the default is "item-order".
      Only one of "fragment-frequency" or "item-frequency" may be specified
  in the options parameter.  If neither "fragment-frequency" nor
  "item-frequency" is specified, then the default is "fragment-frequency".
      Only one of "ascending" or "descending" may be specified
  in the options parameter.  If neither "ascending" nor "descending"
  is specified, then the default is "ascending" if "item-order" is
  specified, and "descending" if "frequency-order" is specified.
      Only one of "eager" or "lazy" may be specified
  in the options parameter.  If neither "eager" nor "lazy"
  is specified, then the default is "lazy" if "item-order" is
  specified, and "eager" if "frequency-order" is specified.
      Only one of "any", "document", "properties", or "locks"
  may be specified in the options parameter.
  If none of "any", "document", "properties", or "locks" are specified
  and there is a $query parameter, then the default is "document".
  If there is no $query parameter then the default is "any".
      Only one of the "score-logtfidf", "score-logtf", "score-simple",
  "score-random", or "score-zero" options may be specified in the options
  parameter.
  If none of "score-logtfidf", "score-logtf", "score-simple", "score-random",
  or "score-zero" are specified, then the default is "score-logtfidf".
      Only one of the "checked" or "unchecked" options may be specified
  in the options parameter.
  If neither "checked" nor "unchecked" are specified,
  then the default is "checked".
      If "collation=URI" is not specified in the options parameter,
  then the default collation is used.  If a range index with that collation
  does not exist, an error is thrown.
      If "sample=N" is not specified in the options parameter,
  then all included values may be returned. If a $query parameter
  is not present, then "sample=N" has no effect.
      If "truncate=N" is not specified in the options parameter,
  then values from all fragments selected by the $query parameter
  are included.  If a $query parameter is not present, then
  "truncate=N" has no effect.
      To incrementally fetch a subset of the values returned by this function,
  use fn:subsequence
  
  on the output, rather than 
  the "skip" option. The "skip" option is based on fragments matching the 
  query parameter (if present), not on values. A fragment 
  matched by query might contain multiple values or no values. 
  The number of fragments skipped does not correspond to the number of 
  values. Also, the skip is applied to the relevance ordered query matches, 
  not to the ordered values list. 
      When using the "skip" option, use the "truncate" option rather than 
  the "limit" option to control the number of matching fragments from which 
  to draw values.
      
    If neither "case-sensitive" nor "case-insensitive"
    is present, $pattern is used to determine case sensitivity.
    If $pattern contains no uppercase, it specifies "case-insensitive".
    If $pattern contains uppercase, it specifies "case-sensitive".
  
      
    If neither "diacritic-sensitive" nor "diacritic-insensitive"
    is present, $pattern is used to determine diacritic sensitivity.
    If $pattern contains no diacritics, it specifies "diacritic-insensitive".
    If $pattern contains diacritics, it specifies "diacritic-sensitive".

### Examples

```xquery
cts:field-value-match("aname","Jim *")
  => "Jim Kurla"
```

---

## cts:field-value-ranges

Returns value ranges from the specified field value lexicon(s).
  Value lexicons are implemented using range indexes; consequently this
  function requires a field range index for each element specified
  in the function.  If there is not a range index configured for each
  of the specified fields, an exception is thrown.
      The values are divided into buckets. The $bounds parameter specifies
  the number of buckets and the size of each bucket.
  All included values are bucketed, even those less than the lowest bound
  or greater than the highest bound. An empty sequence for $bounds specifies
  one bucket, a single value specifies two buckets, two values specify
  three buckets, and so on.
      If you have string values and you pass a $bounds parameter
   as in the following call:
      cts:field-value-ranges("myField", ("f", "m"))
      The first bucket contains string values that are less than the
  string f, the second bucket contains string values greater than
  or equal to f but less than m, and the third bucket
  contains string values that are greater than or equal to m.
      For each non-empty bucket, a cts:range element is returned.
  Each cts:range element has a cts:minimum child
  and a cts:maximum child.  If a bucket is bounded, its
  cts:range element will also have a
  cts:lower-bound child if it is bounded from below, and
  a cts:upper-bound element if it is bounded from above.
  Empty buckets return nothing unless the "empties" option is specified.

### Signature

```xquery
cts:field-value-ranges(
  $field-names as xs:string*,
  $bounds as xs:anyAtomicType*?,
  $options as xs:string*?,
  $query as cts:query??,
  $quality-weight as xs:double??,
  $forest-ids as xs:unsignedLong*?
) as element(cts:range)*
```

### Parameters

**`$field-names`**
One or more element QNames.

**`$bounds`** *(optional)*
A sequence of range bounds.
    The types must match the lexicon type.
    The values must be in strictly ascending order, otherwise an exception
    is thrown.

**`$options`** *(optional)*
Options.  The default is ().
    
      Options include:
      
        "ascending"
        Ranges should be returned in ascending order.
        "descending"
        Ranges should be returned in descending order.
        "empties"
        Include fully-bounded ranges whose frequency is 0. These ranges
        will have no minimum or maximum value.  Only empty ranges that have
        both their upper and lower bounds specified in the $bounds
        options are returned;
        any empty ranges that are less than the first bound or greater than the
        last bound are not returned.  For example, if you specify 4 bounds
        and there are no results for any of the bounds, 3 elements are
        returned (not 5 elements).
        "any"
        Values from any fragment should be included.
        "document"
        Values from document fragments should be included.
        "properties"
        Values from properties fragments should be included.
        "locks"
        Values from locks fragments should be included.
        "frequency-order"
        Ranges should be returned ordered by frequency.
        "item-order"
        Ranges should be returned ordered by item.
        "fragment-frequency"
        Frequency should be the number of fragments with
        an included value.
        This option is used with cts:frequency.
        "item-frequency"
        Frequency should be the number of occurrences of
        an included value.
        This option is used with cts:frequency.
        "type=type"
        Use the lexicon with the type specified by type
        (int, unsignedInt, long, unsignedLong, float, double, decimal,
        dateTime, time, date, gYearMonth, gYear, gMonth, gDay,
        yearMonthDuration, dayTimeDuration, string, or anyURI)
        "collation=URI"
        Use the lexicon with the collation specified by URI.
        "timezone=TZ"
        Return timezone sensitive values (dateTime, time, date,
        gYearMonth, gYear, gMonth, and gDay) adjusted to the timezone
        specified by TZ.
        Example timezones: Z, -08:00, +01:00.
        "limit=N"
        Return no more than N ranges. You should not
        use this option with the "skip" option. Use "truncate" instead.
        "skip=N"
        Skip over fragments selected by the cts:query
        to treat the Nth fragment as the first fragment.
        Values from skipped fragments are not included.
        This option affects the number of fragments selected
        by the cts:query to calculate frequencies.
        Only applies when a $query parameter is specified.
        "sample=N"
        Return only ranges for buckets with at least one value from
        the first N fragments after skip selected by the
        cts:query.
        This option does not affect the number of fragments selected
        by the cts:query to calculate frequencies.
        Only applies when a $query parameter is specified.
        "truncate=N"
        Include only values from the first N fragments
        after skip selected by the cts:query.
        This option also affects the number of fragments selected
        by the cts:query to calculate frequencies.
        Only applies when a $query parameter is specified.
        "score-logtfidf"
        Compute scores using the logtfidf method.
        Only applies when a $query parameter is specified.
        "score-logtf"
        Compute scores using the logtf method.
        Only applies when a $query parameter is specified.
        "score-simple"
        Compute scores using the simple method.
        Only applies when a $query parameter is specified.
        "score-random"
        Compute scores using the random method.
        Only applies when a $query parameter is specified.
        "score-zero"
        Compute all scores as zero.
        Only applies when a $query parameter is specified.
        "checked"
        Word positions should be checked when resolving the query.
        "unchecked"
        Word positions should not be checked when resolving the query.
        "too-many-positions-error"
        If too much memory is needed to perform positions calculations
        to check whether a document matches a query,
        return an XDMP-TOOMANYPOSITIONS error,
        instead of accepting the document as a match.
        "eager"
        Perform most of the work concurrently before returning
        the first item from the indexes, and only some of the work
        sequentially while iterating through the rest of the items.
        This usually takes the shortest time for a complete item-order
        result or for any frequency-order result.
        "lazy"
        Perform only some the work concurrently before returning
        the first item from the indexes, and most of the work
        sequentially while iterating through the rest of the items.
        This usually takes the shortest time for a small item-order
        partial result.
        "concurrent"
        Perform the work concurrently in another thread. This is a hint
        to the query optimizer to help parallelize the lexicon work, allowing
        the calling query to continue performing other work while the lexicon
        processing occurs.  This is especially useful in cases where multiple
        lexicon calls occur in the same query (for example, resolving many
        facets in a single query).
        "coordinate-system=name"
        Use the lexicon that is configured with the specified coordinate
         system. Allowed values: "wgs84", "wgs84/double", "raw",
         "raw/double". Only applicable if the lexicon value type is
         point or long-lat-point.
        "precision=value"
        Use the lexicon that is configured with the specified precision.
         Allowed values: float and double.
         Only applicable if the lexicon value type is point or
         long-lat-point. This value takes precedence over the
         precision implicit in the coordinate system name.

**`$query`** *(optional)*
Only include values in fragments selected by the cts:query,
    and compute frequencies from this set of included values.
    The values do not need to match the query, but they must occur in
    fragments selected by the query.
    The fragments are not filtered to ensure they match the query,
    but instead selected in the same manner as
    
    "unfiltered" cts:search
    
    operations.  If a string
   is entered, the string is treated as a cts:word-query of the
   specified string.

**`$quality-weight`** *(optional)*
A document quality weight to use when computing scores.
    The default is 1.0.

**`$forest-ids`** *(optional)*
A sequence of IDs of forests to which the search will be constrained.
    An empty sequence means to search all forests in the database.
    The default is ().

### Returns

`element(cts:range)*`

### Usage Notes

Only one of "frequency-order" or "item-order" may be specified
  in the options parameter.  If neither "frequency-order" nor "item-order"
  is specified, then the default is "item-order".
      Only one of "fragment-frequency" or "item-frequency" may be specified
  in the options parameter.  If neither "fragment-frequency" nor
  "item-frequency" is specified, then the default is "fragment-frequency".
      Only one of "ascending" or "descending" may be specified
  in the options parameter.  If neither "ascending" nor "descending"
  is specified, then the default is "ascending" if "item-order" is
  specified, and "descending" if "frequency-order" is specified.
      Only one of "eager" or "lazy" may be specified
  in the options parameter.  If neither "eager" nor "lazy"
  is specified, then the default is "eager" if "frequency-order" or "empties"
  is specified, otherwise "lazy".
      Only one of "any", "document", "properties", or "locks"
  may be specified in the options parameter.
  If none of "any", "document", "properties", or "locks" are specified
  and there is a $query parameter, then the default is "document".
  If there is no $query parameter then the default is "any".
      Only one of the "score-logtfidf", "score-logtf", "score-simple",
  "score-random", or "score-zero" options may be specified in the options
  parameter.
  If none of "score-logtfidf", "score-logtf", "score-simple", "score-random",
  or "score-zero" are specified, then the default is "score-logtfidf".
      Only one of the "checked" or "unchecked" options may be specified
  in the options parameter.
  If neither "checked" nor "unchecked" are specified,
  then the default is "checked".
      If "collation=URI" is not specified in the options parameter,
  then the default collation is used. If a lexicon with that collation
  does not exist, an error is thrown.
      If "sample=N" is not specified in the options parameter,
  then ranges with all included values may be returned. If a
  $query parameter is not present, then "sample=N"
  has no effect.
      If "truncate=N" is not specified in the options parameter,
  then values from all fragments selected by the $query parameter
  are included.  If a $query parameter is not present, then
  "truncate=N" has no effect.
      To incrementally fetch a subset of the values returned by this function,
  use fn:subsequence
  
  on the output, rather than 
  the "skip" option. The "skip" option is based on fragments matching the 
  query parameter (if present), not on values. A fragment 
  matched by query might contain multiple values or no values. 
  The number of fragments skipped does not correspond to the number of 
  values. Also, the skip is applied to the relevance ordered query matches, 
  not to the ordered results list. 
      When using the "skip" option, use the "truncate" option rather than 
  the "limit" option to control the number of matching fragments from which 
  to draw values.

### Examples

```xquery
(: Run the following to load data for this example.
   Make sure you have a string field range index on
   field aname that includes name and excludes mname. :)

let $content1 := <name><fname>John</fname><mname>Rob</mname><lname>Goldings</lname></name>
let $content2 := <name><fname>Jim</fname><mname>Ken</mname><lname>Kurla</lname></name>
let $content3 := <name><fname>Ooi</fname><mname>Ben</mname><lname>Fu</lname></name>
let $content4 := <name><fname>James</fname><mname>Rick</mname><lname>Tod</lname></name>
let $content5 := <name><fname>Anthony</fname><mname>Rob</mname><lname>Flemings</lname></name>
let $content6 := <name><fname>Charles</fname><mname>Ken</mname><lname>Winter</lname></name>
let $content7 := <name><fname>Nancy</fname><mname>Ben</mname><lname>Schmidt</lname></name>
let $content8 := <name><fname>Robert</fname><mname>Rick</mname><lname>Hanson</lname></name>
return (
xdmp:document-insert("/aname1.xml",$content1),
xdmp:document-insert("/aname2.xml",$content2),
xdmp:document-insert("/aname3.xml",$content3),
xdmp:document-insert("/aname4.xml",$content4),
xdmp:document-insert("/aname5.xml",$content5),
xdmp:document-insert("/aname6.xml",$content6),
xdmp:document-insert("/aname7.xml",$content7),
xdmp:document-insert("/aname8.xml",$content8)
)

(: The following is based on the above setup :)
cts:field-value-ranges("aname",("A","J","O"));
=>
<cts:range xmlns:cts="http://marklogic.com/cts" xmlns:xsi="http://www.w3.org/2001/XMLSchema-instance" xmlns:xs="http://www.w3.org/2001/XMLSchema">
<cts:minimum xsi:type="xs:string">Anthony Flemings</cts:minimum>
<cts:maximum xsi:type="xs:string">Charles Winter</cts:maximum>
<cts:lower-bound xsi:type="xs:string">A</cts:lower-bound>
<cts:upper-bound xsi:type="xs:string">J</cts:upper-bound>
</cts:range>
<cts:range xmlns:cts="http://marklogic.com/cts" xmlns:xsi="http://www.w3.org/2001/XMLSchema-instance" xmlns:xs="http://www.w3.org/2001/XMLSchema">
<cts:minimum xsi:type="xs:string">James Tod</cts:minimum>
<cts:maximum xsi:type="xs:string">Nancy Schmidt</cts:maximum>
<cts:lower-bound xsi:type="xs:string">J</cts:lower-bound>
<cts:upper-bound xsi:type="xs:string">O</cts:upper-bound>
</cts:range>
<cts:range xmlns:cts="http://marklogic.com/cts" xmlns:xsi="http://www.w3.org/2001/XMLSchema-instance" xmlns:xs="http://www.w3.org/2001/XMLSchema">
<cts:minimum xsi:type="xs:string">Ooi Fu</cts:minimum>
<cts:maximum xsi:type="xs:string">Robert Hanson</cts:maximum>
<cts:lower-bound xsi:type="xs:string">O</cts:lower-bound>
</cts:range>

(: And you can call cts:frequency on each result item :)
```

---

## cts:field-values

Returns values from the specified field value lexicon(s).
  Value lexicons are implemented using range indexes; consequently this
  function requires an field range index for each field specified
  in the function.  If there is not a range index configured for each
  of the specified fields, an exception is thrown.

### Signature

```xquery
cts:field-values(
  $field-names as xs:string*,
  $start as xs:anyAtomicType??,
  $options as xs:string*?,
  $query as cts:query??,
  $quality-weight as xs:double??,
  $forest-ids as xs:unsignedLong*?
) as xs:anyAtomicType*
```

### Parameters

**`$field-names`**
One or more field names.

**`$start`** *(optional)*
A starting value.  The parameter type must match the lexicon type.
    If the parameter value is not in the lexicon, then the values are
    returned beginning with the next value.

**`$options`** *(optional)*
Options.  The default is ().
    
      Options include:
      
        "ascending"
        Values should be returned in ascending order.
        "descending"
        Values should be returned in descending order.
        "any"
        Values from any fragment should be included.
        "document"
        Values from document fragments should be included.
        "properties"
        Values from properties fragments should be included.
        "locks"
        Values from locks fragments should be included.
        "frequency-order"
        Values should be returned ordered by frequency.
        "item-order"
        Values should be returned ordered by item.
        "fragment-frequency"
        Frequency should be the number of fragments with
        an included value.
        This option is used with cts:frequency.
        "item-frequency"
        Frequency should be the number of occurrences of
        an included value.
        This option is used with cts:frequency.
        "type=type"
        Use the lexicon with the type specified by type
        (int, unsignedInt, long, unsignedLong, float, double, decimal,
        dateTime, time, date, gYearMonth, gYear, gMonth, gDay,
        yearMonthDuration, dayTimeDuration, string, or anyURI)
        "collation=URI"
        Use the lexicon with the collation specified by URI.
        "timezone=TZ"
        Return timezone sensitive values (dateTime, time, date,
        gYearMonth, gYear, gMonth, and gDay) adjusted to the timezone
        specified by TZ.
        Example timezones: Z, -08:00, +01:00.
        "limit=N"
        Return no more than N words. You should not
        use this option with the "skip" option. Use "truncate" instead.
        "skip=N"
        Skip over fragments selected by the cts:query
        to treat the Nth fragment as the first fragment.
        Values from skipped fragments are not included.
        This option affects the number of fragments selected
        by the cts:query to calculate frequencies.
        Only applies when a $query parameter is specified.
        "sample=N"
        Return only values from the first N
        fragments after skip selected by the cts:query.
        This option does not affect the number of fragments selected
        by the cts:query to calculate frequencies.
        Only applies when a $query parameter is specified.
        "truncate=N"
        Include only values from the first N fragments
        after skip selected by the cts:query.
        This option also affects the number of fragments selected
        by the cts:query to calculate frequencies.
        Only applies when a $query parameter is specified.
        "score-logtfidf"
        Compute scores using the logtfidf method.
        Only applies when a $query parameter is specified.
        "score-logtf"
        Compute scores using the logtf method.
        Only applies when a $query parameter is specified.
        "score-simple"
        Compute scores using the simple method.
        Only applies when a $query parameter is specified.
        "score-random"
        Compute scores using the random method.
        Only applies when a $query parameter is specified.
        "score-zero"
        Compute all scores as zero.
        Only applies when a $query parameter is specified.
        "checked"
        Word positions should be checked when resolving the query.
        "unchecked"
        Word positions should not be checked when resolving the query.
        "too-many-positions-error"
        If too much memory is needed to perform positions calculations
        to check whether a document matches a query,
        return an XDMP-TOOMANYPOSITIONS error,
        instead of accepting the document as a match.
        "eager"
        Perform most of the work concurrently before returning
        the first item from the indexes, and only some of the work
        sequentially while iterating through the rest of the items.
        This usually takes the shortest time for a complete item-order
        result or for any frequency-order result.
        "lazy"
        Perform only some the work concurrently before returning
        the first item from the indexes, and most of the work
        sequentially while iterating through the rest of the items.
        This usually takes the shortest time for a small item-order
        partial result.
        "concurrent"
        Perform the work concurrently in another thread. This is a hint
        to the query optimizer to help parallelize the lexicon work, allowing
        the calling query to continue performing other work while the lexicon
        processing occurs.  This is especially useful in cases where multiple
        lexicon calls occur in the same query (for example, resolving many
        facets in a single query).
        "map"
        Return results as a single map:map
         value instead of as an xs:anyAtomicType* sequence
         .

**`$query`** *(optional)*
Only include values in fragments selected by the cts:query,
    and compute frequencies from this set of included values.
    The values do not need to match the query, but they must occur in
    fragments selected by the query.
    The fragments are not filtered to ensure they match the query,
    but instead selected in the same manner as
    
    "unfiltered" cts:search
    
    operations.  If a string
   is entered, the string is treated as a cts:word-query of the
   specified string.

**`$quality-weight`** *(optional)*
A document quality weight to use when computing scores.
    The default is 1.0.

**`$forest-ids`** *(optional)*
A sequence of IDs of forests to which the search will be constrained.
    An empty sequence means to search all forests in the database.
    The default is ().

### Returns

`xs:anyAtomicType*`

### Usage Notes

Only one of "frequency-order" or "item-order" may be specified
  in the options parameter.  If neither "frequency-order" nor "item-order"
  is specified, then the default is "item-order".
      Only one of "fragment-frequency" or "item-frequency" may be specified
  in the options parameter.  If neither "fragment-frequency" nor
  "item-frequency" is specified, then the default is "fragment-frequency".
      Only one of "ascending" or "descending" may be specified
  in the options parameter.  If neither "ascending" nor "descending"
  is specified, then the default is "ascending" if "item-order" is
  specified, and "descending" if "frequency-order" is specified.
      Only one of "eager" or "lazy" may be specified
  in the options parameter.  If neither "eager" nor "lazy"
  is specified, then the default is "lazy" if "item-order" is
  specified, and "eager" if "frequency-order" is specified.
      Only one of "any", "document", "properties", or "locks"
  may be specified in the options parameter.
  If none of "any", "document", "properties", or "locks" are specified
  and there is a $query parameter, then the default is "document".
  If there is no $query parameter then the default is "any".
      Only one of the "score-logtfidf", "score-logtf", "score-simple",
  "score-random", or "score-zero" options may be specified in the options
  parameter.
  If none of "score-logtfidf", "score-logtf", "score-simple", "score-random",
  or "score-zero" are specified, then the default is "score-logtfidf".
      Only one of the "checked" or "unchecked" options may be specified
  in the options parameter.
  If neither "checked" nor "unchecked" are specified,
  then the default is "checked".
      If "collation=URI" is not specified in the options parameter,
  then the default collation is used. If a lexicon with that collation
  does not exist, an error is thrown.
      If "sample=N" is not specified in the options parameter,
  then all included values may be returned. If a $query parameter
  is not present, then "sample=N" has no effect.
      If "truncate=N" is not specified in the options parameter,
  then values from all fragments selected by the $query parameter
  are included.  If a $query parameter is not present, then
  "truncate=N" has no effect.
      To incrementally fetch a subset of the values returned by this function,
  use fn:subsequence
  
  on the output, rather than 
  the "skip" option. The "skip" option is based on fragments matching the 
  query parameter (if present), not on values. A fragment 
  matched by query might contain multiple values or no values. 
  The number of fragments skipped does not correspond to the number of 
  values. Also, the skip is applied to the relevance ordered query matches, 
  not to the ordered values list. 
      When using the "skip" option, use the "truncate" option rather than 
  the "limit" option to control the number of matching fragments from which 
  to draw values.

### Examples

```xquery
(: If a field range index does not exist on "my_field", then
 :  this example throws XDMP-FIELDRIDXNOTFOUND :)

  cts:field-values("my_field","John Goldings")

(: Returns output similar to the following:
 :   ("John Goldings","Ooi Fu",...)  :)
```

---

## cts:field-word-match

Returns words from the specified field word lexicon(s) that match
  a wildcard pattern.   This function requires an field word lexicon
  configured for each of the specified fields in the function.  If there
  is not an field word lexicon configured for any of the specified
  fields, an exception is thrown.

### Signature

```xquery
cts:field-word-match(
  $field-names as xs:string*,
  $pattern as xs:string,
  $options as xs:string*?,
  $query as cts:query??,
  $quality-weight as xs:double??,
  $forest-ids as xs:unsignedLong*?
) as xs:string*
```

### Parameters

**`$field-names`**
One or more field names.

**`$pattern`**
Wildcard pattern to match.

**`$options`** *(optional)*
Options.  The default is ().
    
      Options include:
      
        "case-sensitive"
        A case-sensitive match.
        "case-insensitive"
        A case-insensitive match.
        "diacritic-sensitive"
        A diacritic-sensitive match.
        "diacritic-insensitive"
        A diacritic-insensitive match.
        "ascending"
        Words should be returned in ascending order.
        "descending"
        Words should be returned in descending order.
        "any"
        Words from any fragment should be included.
        "document"
        Words from document fragments should be included.
        "properties"
        Words from properties fragments should be included.
        "locks"
        Words from locks fragments should be included.
        "collation=URI"
        Use the lexicon with the collation specified by URI.
        "limit=N"
        Return no more than N words. You should not
        use this option with the "skip" option. Use "truncate" instead.
        "skip=N"
        Skip over fragments selected by the cts:query
        to treat the Nth matching fragment as the first fragment.
        Words from skipped fragments are not included.
        Only applies when a $query parameter is specified.
        "sample=N"
        Return only words from the first N fragments after
        skip selected by the cts:query.
        Only applies when a $query parameter is specified.
        "truncate=N"
        Include only words from the first N fragments after
        skip selected by the cts:query.
        Only applies when a $query parameter is specified.
        "score-logtfidf"
        Compute scores using the logtfidf method.
        Only applies when a $query parameter is specified.
        "score-logtf"
        Compute scores using the logtf method.
        Only applies when a $query parameter is specified.
        "score-simple"
        Compute scores using the simple method.
        Only applies when a $query parameter is specified.
        "score-random"
        Compute scores using the random method.
        Only applies when a $query parameter is specified.
        "score-zero"
        Compute all scores as zero.
        Only applies when a $query parameter is specified.
        "checked"
        Word positions should be checked when resolving the query.
        "unchecked"
        Word positions should not be checked when resolving the query.
        "too-many-positions-error"
        If too much memory is needed to perform positions calculations
        to check whether a document matches a query,
        return an XDMP-TOOMANYPOSITIONS error,
        instead of accepting the document as a match.
        "concurrent"
        Perform the work concurrently in another thread. This is a hint
        to the query optimizer to help parallelize the lexicon work, allowing
        the calling query to continue performing other work while the lexicon
        processing occurs.  This is especially useful in cases where multiple
        lexicon calls occur in the same query (for example, resolving many
        facets in a single query).
        "map"
        Return results as a single map:map
         value instead of as an xs:string* sequence
         .

**`$query`** *(optional)*
Only include words in fragments selected by the cts:query.
    The words do not need to match the query, but the words must occur
    in fragments selected by the query.
    The fragments are not filtered to ensure they match the query,
    but instead selected in the same manner as
    
    "unfiltered" cts:search
    
    operations.  If a string
   is entered, the string is treated as a cts:word-query of the
   specified string.

**`$quality-weight`** *(optional)*
A document quality weight to use when computing scores.
    The default is 1.0.

**`$forest-ids`** *(optional)*
A sequence of IDs of forests to which the search will be constrained.
    An empty sequence means to search all forests in the database.
    The default is ().

### Returns

`xs:string*`

### Usage Notes

Only one of "ascending" or "descending" may be specified
  in the options parameter.  If neither "ascending" nor "descending"
  is specified, then the default is "ascending".
      Only one of "any", "document", "properties", or "locks"
  may be specified in the options parameter.
  If none of "any", "document", "properties", or "locks" are specified
  and there is a $query parameter, then the default is "document".
  If there is no $query parameter then the default is "any".
      Only one of the "score-logtfidf", "score-logtf", "score-simple",
  "score-random", or "score-zero" options may be specified in the options
  parameter.
  If none of "score-logtfidf", "score-logtf", "score-simple", "score-random",
  or "score-zero" are specified, then the default is "score-logtfidf".
      Only one of the "checked" or "unchecked" options may be specified
  in the options parameter.
  If neither "checked" nor "unchecked" are specified,
  then the default is "checked".
      If "collation=URI" is not specified in the options parameter,
  then the default collation is used. If a lexicon with that collation
  does not exist, an error is thrown.
      If "sample=N" is not specified in the options parameter,
  then all included words may be returned. If a $query parameter
  is not present, then "sample=N" has no effect.
      If "truncate=N" is not specified in the options parameter,
  then words from all fragments selected by the $query parameter
  are included.  If a $query parameter is not present, then
  "truncate=N" has no effect.
      To incrementally fetch a subset of the values returned by this function,
  use fn:subsequence
  
  on the output, rather than 
  the "skip" option. The "skip" option is based on fragments matching the 
  query parameter (if present), not on values. A fragment 
  matched by query might contain multiple values or no values. 
  The number of fragments skipped does not correspond to the number of 
  values. Also, the skip is applied to the relevance ordered query matches, 
  not to the ordered values list. 
      When using the "skip" option, use the "truncate" option rather than 
  the "limit" option to control the number of matching fragments from which 
  to draw values.
      
    If neither "case-sensitive" nor "case-insensitive"
    is present, $pattern is used to determine case sensitivity.
    If $pattern contains no uppercase, it specifies "case-insensitive".
    If $pattern contains uppercase, it specifies "case-sensitive".
  
      
    If neither "diacritic-sensitive" nor "diacritic-insensitive"
    is present, $pattern is used to determine diacritic sensitivity.
    If $pattern contains no diacritics, it specifies "diacritic-insensitive".
    If $pattern contains diacritics, it specifies "diacritic-sensitive".
  
      Only words that can be matched with field-word-query are included.
  That is, only words present in immediate text node children of the
  specified field as well as any text node children of child fields
  defined in the Admin Interface as field-word-query-throughs or
  phrase-throughs.

### Examples

```xquery
cts:field-word-match("animal","aardvark*")
  => ("aardvark","aardvarks")
```

---

## cts:field-words

Returns words from the specified field word lexicon.  This function
  requires an field lexicon for each of the field specified in the
  function.  If there is not an field word lexicon configured for any
  of the specified fields, an exception is thrown.  The words are
  returned in collation order.

### Signature

```xquery
cts:field-words(
  $field-names as xs:string*,
  $start as xs:string??,
  $options as xs:string*?,
  $query as cts:query??,
  $quality-weight as xs:double??,
  $forest-ids as xs:unsignedLong*?
) as xs:string*
```

### Parameters

**`$field-names`**
One or more field names.

**`$start`** *(optional)*
A starting word.  Returns only this word and any following words
    from the lexicon.  If the parameter is not in the lexicon, then it
    returns the words beginning with the next word.

**`$options`** *(optional)*
Options.  The default is ().
    
      Options include:
      
        "ascending"
        Words should be returned in ascending order.
        "descending"
        Words should be returned in descending order.
        "any"
        Words from any fragment should be included.
        "document"
        Words from document fragments should be included.
        "properties"
        Words from properties fragments should be included.
        "locks"
        Words from locks fragments should be included.
        "collation=URI"
        Use the lexicon with the collation specified by URI.
        "limit=N"
        Return no more than N words. You should not
        use this option with the "skip" option. Use "truncate" instead.
        "skip=N"
        Skip over fragments selected by the cts:query
        to treat the Nth fragment as the first fragment.
        Words from skipped fragments are not included.
        Only applies when a $query parameter is specified.
        "sample=N"
        Return only words from the first N fragments after
        skip selected by the cts:query.
        Only applies when a $query parameter is specified.
        "truncate=N"
        Include only words from the first N fragments after
        skip selected by the cts:query.
        Only applies when a $query parameter is specified.
        "score-logtfidf"
        Compute scores using the logtfidf method.
        Only applies when a $query parameter is specified.
        "score-logtf"
        Compute scores using the logtf method.
        Only applies when a $query parameter is specified.
        "score-simple"
        Compute scores using the simple method.
        Only applies when a $query parameter is specified.
        "score-random"
        Compute scores using the random method.
        Only applies when a $query parameter is specified.
        "score-zero"
        Compute all scores as zero.
        Only applies when a $query parameter is specified.
        "checked"
        Word positions should be checked when resolving the query.
        "unchecked"
        Word positions should not be checked when resolving the query.
        "too-many-positions-error"
        If too much memory is needed to perform positions calculations
        to check whether a document matches a query,
        return an XDMP-TOOMANYPOSITIONS error,
        instead of accepting the document as a match.
        "concurrent"
        Perform the work concurrently in another thread. This is a hint
        to the query optimizer to help parallelize the lexicon work, allowing
        the calling query to continue performing other work while the lexicon
        processing occurs.  This is especially useful in cases where multiple
        lexicon calls occur in the same query (for example, resolving many
        facets in a single query).
        "map"
        Return results as a single map:map
         value instead of as an xs:string* sequence
         .

**`$query`** *(optional)*
Only include words in fragments selected by the cts:query.
    The words do not need to match the query, but the words must occur
    in fragments selected by the query.
    The fragments are not filtered to ensure they match the query,
    but instead selected in the same manner as
    
    "unfiltered" cts:search
    
    operations.  If a string
   is entered, the string is treated as a cts:word-query of the
   specified string.

**`$quality-weight`** *(optional)*
A document quality weight to use when computing scores.
    The default is 1.0.

**`$forest-ids`** *(optional)*
A sequence of IDs of forests to which the search will be constrained.
    An empty sequence means to search all forests in the database.
    The default is ().

### Returns

`xs:string*`

### Usage Notes

Only one of "ascending" or "descending" may be specified
  in the options parameter.  If neither "ascending" nor "descending"
  is specified, then the default is "ascending".
      Only one of "any", "document", "properties", or "locks"
  may be specified in the options parameter.
  If none of "any", "document", "properties", or "locks" are specified
  and there is a $query parameter, then the default is "document".
  If there is no $query parameter then the default is "any".
      Only one of the "score-logtfidf", "score-logtf", "score-simple",
  "score-random", or "score-zero" options may be specified in the options
  parameter.
  If none of "score-logtfidf", "score-logtf", "score-simple", "score-random",
  or "score-zero" are specified, then the default is "score-logtfidf".
      Only one of the "checked" or "unchecked" options may be specified
  in the options parameter.
  If neither "checked" nor "unchecked" are specified,
  then the default is "checked".
      If "collation=URI" is not specified in the options parameter,
  then the default collation is used. If a lexicon with that collation
  does not exist, an error is thrown.
      If "sample=N" is not specified in the options parameter,
  then all included words may be returned. If a $query parameter
  is not present, then "sample=N" has no effect.
      If "truncate=N" is not specified in the options parameter,
  then words from all fragments selected by the $query parameter
  are included.  If a $query parameter is not present, then
  "truncate=N" has no effect.
      Only words that can be matched with field-word-query are included.
  That is, only words present in immediate text node children of the
  specified field as well as any text node children of child fields
  defined in the Admin Interface as field-word-query-throughs or
  phrase-throughs. 
      When run without a $query parameter and as a user with the admin role,
  the word lexicon functions return results that might include words from
  deleted fragments. However, when run as a user with the admin role and
  without a $query parameter, the word lexicon functions run faster (because
  they do not need to look up where each word comes from). It is therefore
  faster to run word lexicon functions as an admin user without passing a
  $query parameter.
      To incrementally fetch a subset of the values returned by this function, 
  use fn:subsequence
  
  on the output, rather than 
  the "skip" option. The "skip" option is based on fragments matching the 
  query parameter (if present), not on values. A fragment 
  matched by query might contain multiple values or no values. 
  The number of fragments skipped does not correspond to the number of 
  values. Also, the skip is applied to the relevance ordered query matches, 
  not to the ordered values list. 
      When using the "skip" option, use the "truncate" option rather than 
  the "limit" option to control the number of matching fragments from which 
  to draw values.

### Examples

```xquery
cts:field-words("animal","aardvark")
  => ("aardvark","aardvarks","aardwolf",...)
```

---

## cts:frequency

Returns an integer representing the number of times in which a particular
  value occurs in a value lexicon lookup.

### Signature

```xquery
cts:frequency(
  $value as item()
) as xs:integer
```

### Parameters

**`$value`**
A value from a lexicon lookup function. For example, a value returned by
    a function such as
    
      cts:values,
      cts:words,
      cts:field-values,
      cts:field-word-match,
      or cts:geospatial-boxes.

### Returns

`xs:integer`

### Usage Notes

You must have a suitable index configured to use the lexicon APIs. 
 For example you must configure a range index to use value 
 lexicon lookup functions such as 
   cts:element-values, cts:element-value-match,
   cts:element-attribute-values, or
   cts:element-attribute-value-match.
 
      If the value specified is not from a value lexicon lookup,
 this function returns a frequency of 0.
      When using the fragment-frequency lexicon option, this function
  returns the number of fragments in which the lexicon value occurs. When
  using the item-frequency lexicon option, this function returns
  the total number of times in which the lexicon value occurs in each item.
      The frequency returned this function is fragment-based
 by default (using the default fragment-frequency option in the
 lexicon API).  If there are multiple occurrences of the value in any given
 fragment, the frequency is still one per fragment when using
 fragment-frequency. For example, if this function returns
 a value of 13, then the input value occurs in 13 fragments.
      To get the total frequency rather than the fragment-based frequency,
 pass the item-frequency option to the lexicon lookup
 function that generates the input values for this function. See the
 second example, below.

### Examples

#### Example 1

```xquery
<results>{
(: Example using fragment frequency (default). An element range index
 : on SPEAKER must exist. 
 :)
let $x := cts:element-values(xs:QName("SPEAKER"),"",(),
  cts:document-query("/shakespeare/plays/hamlet.xml"))
for $speaker in $x
return
(
<result>
  <SPEAKER>{$speaker}</SPEAKER>
  <NUMBER-OF-SPEECHES>{cts:frequency($speaker)}</NUMBER-OF-SPEECHES>
</result>
)
}</results>

(: Returns the names of the speakers in Hamlet with the number of times 
 : they speak. If the play is fragmented at the SCENE level, then
 : it returns the number of scenes in which each speaker speaks. 
 : For example:
 :
 : <results>
 :  <result>
 :    <SPEAKER>All</SPEAKER>
 :    <NUMBER-OF-SPEECHES>4</NUMBER-OF-SPEECHES>
 :  </result>
 :  <result>
 :    <SPEAKER>BERNARDO</SPEAKER>
 :    <NUMBER-OF-SPEECHES>2</NUMBER-OF-SPEECHES>
 :  </result>
 : ...
 : </results>
 :)
```

#### Example 2

```xquery
(: Example using item frequency. An element range index
 : on SPEAKER must exist. 
 :)
<results>{
let $x := cts:element-values(xs:QName("SPEAKER"),
  "", "item-frequency",
  cts:document-query("/shakespeare/plays/hamlet.xml"))
for $speaker in $x
return
(
<result>
  <SPEAKER>{$speaker}</SPEAKER>
  <NUMBER-OF-SPEECHES>
    {cts:frequency($speaker)}
  </NUMBER-OF-SPEECHES>
</result>
)
}</results>

(: Returns the names of the speakers in Hamlet with the number of times 
 : they speak. Returns the total times they speak, regardless of 
 : fragmentation. For example:
 :
 : <results>
 :  <result>
 :    <SPEAKER>All</SPEAKER>
 :    <NUMBER-OF-SPEECHES>4</NUMBER-OF-SPEECHES>
 :  </result>
 :  <result>
 :    <SPEAKER>BERNARDO</SPEAKER>
 :    <NUMBER-OF-SPEECHES>23</NUMBER-OF-SPEECHES>
 :  </result>
 : ...
 : </results>
 :)
```

---

## cts:iri-reference

Creates a reference to the URI lexicon, for use as a parameter to
  cts:value-tuples.  This function requires the URI lexicon to be enabled,
  otherwise it throws an exception. This reference returns URIs as IRIs.

### Returns

`cts:reference`

### Examples

```xquery
cts:iri-reference()
=>
cts:iri-reference()
```

---

## cts:json-property-reference

Creates a reference to a JSON property value lexicon, for use as a parameter
  to cts:value-tuples.  Since lexicons are implemented with range indexes,
  this function will throw an exception if the specified range index does
  not exist.

### Signature

```xquery
cts:json-property-reference(
  $property as xs:string,
  $options as xs:string*?
) as cts:reference
```

### Parameters

**`$property`**
A property name.

**`$options`** *(optional)*
Options.  The default is ().
    
      Options include:
      
        "type=type"
        Use the lexicon with the type specified by type
        (int, unsignedInt, long, unsignedLong, float, double, decimal,
        dateTime, time, date, gYearMonth, gYear, gMonth, gDay,
        yearMonthDuration, dayTimeDuration, string, anyURI, point, or
        long-lat-point)
        "collation=URI"
        Use the lexicon with the collation specified by URI.
        "nullable"
        Allow null values in tuples reported from cts:value-tuples when
        using this lexicon.
        "unchecked"
        Read the scalar type, collation and coordinate-system info
        only from the input. Do not check the definition against the
        context database.
        "coordinate-system=name"
        Create a reference to an index or lexicon based on the specified
         coordinate system. Allowed values: "wgs84", "wgs84/double", "raw",
         "raw/double". Only applicable if the index/lexicon value type is
         point or long-lat-point.
        "precision=value"
        Create a reference to an index or lexicon configured with the
         specified geospatial precision. Allowed values: float
         and double. Only applicable if the index/lexicon value
         type is point or long-lat-point. This
         value takes precedence over the precision implicit in the coordinate
         system name.

### Returns

`cts:reference`

### Examples

```xquery
cts:json-property-reference("TITLE");
=>
cts:json-property-reference("TITLE",("type=string","collation=http://marklogic.com/collation/"))
```

---

## cts:json-property-word-match

Returns words from the specified JSON property word lexicon(s) that match
  a wildcard pattern.   This function requires a property word lexicon
  configured for each of the specified properties in the function.  If there
  is not a property word lexicon configured for any of the specified
  properties, an exception is thrown.

### Signature

```xquery
cts:json-property-word-match(
  $property-names as xs:string*,
  $pattern as xs:string?,
  $options as xs:string*?,
  $query as cts:query??,
  $quality-weight as xs:double??,
  $forest-ids as xs:unsignedLong*?
) as xs:string*
```

### Parameters

**`$property-names`**
One or more property names.

**`$pattern`**
Wildcard pattern to match.

**`$options`** *(optional)*
Options.  The default is ().
    
      Options include:
      
        "case-sensitive"
        A case-sensitive match.
        "case-insensitive"
        A case-insensitive match.
        "diacritic-sensitive"
        A diacritic-sensitive match.
        "diacritic-insensitive"
        A diacritic-insensitive match.
        "ascending"
        Words should be returned in ascending order.
        "descending"
        Words should be returned in descending order.
        "any"
        Words from any fragment should be included.
        "document"
        Words from document fragments should be included.
        "properties"
        Words from properties fragments should be included.
        "locks"
        Words from locks fragments should be included.
        "collation=URI"
        Use the lexicon with the collation specified by URI.
        "limit=N"
        Return no more than N words. You should not
        use this option with the "skip" option. Use "truncate" instead.
        "skip=N"
        Skip over fragments selected by the cts:query
        to treat the Nth fragment as the first fragment.
        Words from skipped fragments are not included.
        Only applies when a $query parameter is specified.
        "sample=N"
        Return only words from the first N fragments after skip
        selected by the cts:query.
        Only applies when a $query parameter is specified.
        "truncate=N"
        Include only words from the first N fragments after skip
        selected by the cts:query.
        Only applies when a $query parameter is specified.
        "score-logtfidf"
        Compute scores using the logtfidf method.
        Only applies when a $query parameter is specified.
        "score-logtf"
        Compute scores using the logtf method.
        Only applies when a $query parameter is specified.
        "score-simple"
        Compute scores using the simple method.
        Only applies when a $query parameter is specified.
        "score-random"
        Compute scores using the random method.
        Only applies when a $query parameter is specified.
        "score-zero"
        Compute all scores as zero.
        Only applies when a $query parameter is specified.
        "checked"
        Word positions should be checked when resolving the query.
        "unchecked"
        Word positions should not be checked when resolving the query.
        "too-many-positions-error"
        If too much memory is needed to perform positions calculations
        to check whether a document matches a query,
        return an XDMP-TOOMANYPOSITIONS error,
        instead of accepting the document as a match.
        "concurrent"
        Perform the work concurrently in another thread. This is a hint
        to the query optimizer to help parallelize the lexicon work, allowing
        the calling query to continue performing other work while the lexicon
        processing occurs.  This is especially useful in cases where multiple
        lexicon calls occur in the same query (for example, resolving many
        facets in a single query).
        "map"
        Return results as a single map:map
         value instead of as an xs:string* sequence
         .

**`$query`** *(optional)*
Only include words in fragments selected by the cts:query.
    The words do not need to match the query, but the words must occur
    in fragments selected by the query.
    The fragments are not filtered to ensure they match the query,
    but instead selected in the same manner as
    
    "unfiltered" cts:search
    
    operations.  If a string
   is entered, the string is treated as a cts:word-query of the
   specified string.

**`$quality-weight`** *(optional)*
A document quality weight to use when computing scores.
    The default is 1.0.

**`$forest-ids`** *(optional)*
A sequence of IDs of forests to which the search will be constrained.
    An empty sequence means to search all forests in the database.
    The default is ().

### Returns

`xs:string*`

### Usage Notes

Only one of "ascending" or "descending" may be specified
  in the options parameter.  If neither "ascending" nor "descending"
  is specified, then the default is "ascending".
      Only one of "any", "document", "properties", or "locks"
  may be specified in the options parameter.
  If none of "any", "document", "properties", or "locks" are specified
  and there is a $query parameter, then the default is "document".
  If there is no $query parameter then the default is "any".
      Only one of the "score-logtfidf", "score-logtf", "score-simple",
  "score-random", or "score-zero" options may be specified in the options
  parameter.
  If none of "score-logtfidf", "score-logtf", "score-simple", "score-random",
  or "score-zero" are specified, then the default is "score-logtfidf".
      Only one of the "checked" or "unchecked" options may be specified
  in the options parameter.
  If neither "checked" nor "unchecked" are specified,
  then the default is "checked".
      If "collation=URI" is not specified in the options parameter,
  then the default collation is used. If a lexicon with that collation
  does not exist, an error is thrown.
      If "sample=N" is not specified in the options parameter,
  then all included words may be returned. If a $query parameter
  is not present, then "sample=N" has no effect.
      If "truncate=N" is not specified in the options parameter,
  then words from all fragments selected by the $query parameter
  are included.  If a $query parameter is not present, then
  "truncate=N" has no effect.
      To incrementally fetch a subset of the values returned by this function,
  use fn:subsequence
  
  on the output, rather than 
  the "skip" option. The "skip" option is based on fragments matching the 
  query parameter (if present), not on values. A fragment 
  matched by query might contain multiple values or no values. 
  The number of fragments skipped does not correspond to the number of 
  values. Also, the skip is applied to the relevance ordered query matches, 
  not to the ordered values list. 
      When using the "skip" option, use the "truncate" option rather than 
  the "limit" option to control the number of matching fragments from which 
  to draw values.
      
    If neither "case-sensitive" nor "case-insensitive"
    is present, $pattern is used to determine case sensitivity.
    If $pattern contains no uppercase, it specifies "case-insensitive".
    If $pattern contains uppercase, it specifies "case-sensitive".
  
      
    If neither "diacritic-sensitive" nor "diacritic-insensitive"
    is present, $pattern is used to determine diacritic sensitivity.
    If $pattern contains no diacritics, it specifies "diacritic-insensitive".
    If $pattern contains diacritics, it specifies "diacritic-sensitive".
  
      Only words that can be matched with json-property-word-query are
  included.

### Examples

```xquery
(:
 an element word lexicon must exist on "animal" or
 this example throws XDMP-ELEMLXCNNOTFOUND
:)
  cts:json-property-word-match("animal","aardvark*")
  => ("aardvark","aardvarks")
```

---

## cts:json-property-words

Returns words from the specified JSON property word lexicon.  This function
  requires a property word lexicon for each of the property specified in the
  function.  If there is not a property word lexicon configured for any
  of the specified properties, an exception is thrown.  The words are
  returned in collation order.

### Signature

```xquery
cts:json-property-words(
  $property-names as xs:string*,
  $start as xs:string??,
  $options as xs:string*?,
  $query as cts:query??,
  $quality-weight as xs:double??,
  $forest-ids as xs:unsignedLong*?
) as xs:string*
```

### Parameters

**`$property-names`**
One or more property names.

**`$start`** *(optional)*
A starting word.  Returns only this word and any following words
    from the lexicon.  If the parameter is not in the lexicon, then it
    returns the words beginning with the next word.

**`$options`** *(optional)*
Options.  The default is ().
    
      Options include:
      
        "ascending"
        Words should be returned in ascending order.
        "descending"
        Words should be returned in descending order.
        "any"
        Words from any fragment should be included.
        "document"
        Words from document fragments should be included.
        "properties"
        Words from properties fragments should be included.
        "locks"
        Words from locks fragments should be included.
        "collation=URI"
        Use the lexicon with the collation specified by URI.
        "limit=N"
        Return no more than N words. You should not
        use this option with the "skip" option. Use "truncate" instead.
        "skip=N"
        Skip over fragments selected by the cts:query
        to treat the Nth fragment as the first fragment.
        Words from skipped fragments are not included.
        Only applies when a $query parameter is specified.
        "sample=N"
        Return only words from the first N fragments after skip
        selected by the cts:query.
        Only applies when a $query parameter is specified.
        "truncate=N"
        Include only words from the first N fragments after skip
        selected by the cts:query.
        Only applies when a $query parameter is specified.
        "score-logtfidf"
        Compute scores using the logtfidf method.
        Only applies when a $query parameter is specified.
        "score-logtf"
        Compute scores using the logtf method.
        Only applies when a $query parameter is specified.
        "score-simple"
        Compute scores using the simple method.
        Only applies when a $query parameter is specified.
        "score-random"
        Compute scores using the random method.
        Only applies when a $query parameter is specified.
        "score-zero"
        Compute all scores as zero.
        Only applies when a $query parameter is specified.
        "checked"
        Word positions should be checked when resolving the query.
        "unchecked"
        Word positions should not be checked when resolving the query.
        "too-many-positions-error"
        If too much memory is needed to perform positions calculations
        to check whether a document matches a query,
        return an XDMP-TOOMANYPOSITIONS error,
        instead of accepting the document as a match.
        "concurrent"
        Perform the work concurrently in another thread. This is a hint
        to the query optimizer to help parallelize the lexicon work, allowing
        the calling query to continue performing other work while the lexicon
        processing occurs.  This is especially useful in cases where multiple
        lexicon calls occur in the same query (for example, resolving many
        facets in a single query).
        "map"
        Return results as a single map:map
         value instead of as an xs:string* sequence
         .

**`$query`** *(optional)*
Only include words in fragments selected by the cts:query.
    The words do not need to match the query, but the words must occur
    in fragments selected by the query.
    The fragments are not filtered to ensure they match the query,
    but instead selected in the same manner as
    
    "unfiltered" cts:search
    
    operations.  If a string
   is entered, the string is treated as a cts:word-query of the
   specified string.

**`$quality-weight`** *(optional)*
A document quality weight to use when computing scores.
    The default is 1.0.

**`$forest-ids`** *(optional)*
A sequence of IDs of forests to which the search will be constrained.
    An empty sequence means to search all forests in the database.
    The default is ().

### Returns

`xs:string*`

### Usage Notes

Only one of "ascending" or "descending" may be specified
  in the options parameter.  If neither "ascending" nor "descending"
  is specified, then the default is "ascending".
      Only one of "any", "document", "properties", or "locks"
  may be specified in the options parameter.
  If none of "any", "document", "properties", or "locks" are specified
  and there is a $query parameter, then the default is "document".
  If there is no $query parameter then the default is "any".
      Only one of the "score-logtfidf", "score-logtf", "score-simple",
  "score-random", or "score-zero" options may be specified in the options
  parameter.
  If none of "score-logtfidf", "score-logtf", "score-simple", "score-random",
  or "score-zero" are specified, then the default is "score-logtfidf".
      Only one of the "checked" or "unchecked" options may be specified
  in the options parameter.
  If neither "checked" nor "unchecked" are specified,
  then the default is "checked".
      If "collation=URI" is not specified in the options parameter,
  then the default collation is used. If a lexicon with that collation
  does not exist, an error is thrown.
      If "sample=N" is not specified in the options parameter,
  then all included words may be returned. If a $query parameter
  is not present, then "sample=N" has no effect.
      If "truncate=N" is not specified in the options parameter,
  then words from all fragments selected by the $query parameter
  are included.  If a $query parameter is not present, then
  "truncate=N" has no effect.
      Only words that can be matched with json-property-word-query are
  included.
      When run without a $query parameter and as a user with the admin role,
  the word lexicon functions return results that might include words from
  deleted fragments. However, when run as a user with the admin role and
  without a $query parameter, the word lexicon functions run faster (because
  they do not need to look up where each word comes from). It is therefore
  faster to run word lexicon functions as an admin user without passing a
  $query parameter. 
      To incrementally fetch a subset of the values returned by this function, 
  use fn:subsequence
  
  on the output, rather than 
  the "skip" option. The "skip" option is based on fragments matching the 
  query parameter (if present), not on values. A fragment 
  matched by query might contain multiple values or no values. 
  The number of fragments skipped does not correspond to the number of 
  values. Also, the skip is applied to the relevance ordered query matches, 
  not to the ordered values list. 
      When using the "skip" option, use the "truncate" option rather than 
  the "limit" option to control the number of matching fragments from which 
  to draw values.

### Examples

```xquery
(:
 an element word lexicon must exist on "animal" or
 this example throws XDMP-ELEMLXCNNOTFOUND
:)
  cts:json-property-words("animal","aardvark")
  => ("aardvark","aardvarks","aardwolf",...)
```

---

## cts:path-reference

Creates a reference to a path value lexicon, for use as a
  parameter to cts:value-tuples.  Since lexicons are implemented with range
  indexes, this function will throw an exception if the specified range index
  does not exist.

### Signature

```xquery
cts:path-reference(
  $path-expression as xs:string,
  $options as xs:string*?,
  $map as map:map?
) as cts:reference
```

### Parameters

**`$path-expression`**
A path range index expression.

**`$options`** *(optional)*
Options.  The default is ().
    
      Options include:
      
        "type=type"
        Use the lexicon with the type specified by type
        (int, unsignedInt, long, unsignedLong, float, double, decimal,
        dateTime, time, date, gYearMonth, gYear, gMonth, gDay,
        yearMonthDuration, dayTimeDuration, string, anyURI, point, or
        long-lat-point)
        "collation=URI"
        Use the lexicon with the collation specified by URI.
        "nullable"
        Allow null values in tuples reported from cts:value-tuples when
        using this lexicon.
        "unchecked"
        Read the scalar type, collation and coordinate-system info
        only from the input. Do not check the definition against the
        context database.
        "coordinate-system=name"
        Create a reference to an index or lexicon based on the specified
         coordinate system. Allowed values: "wgs84", "wgs84/double", "raw",
         "raw/double". Only applicable if the index/lexicon value type is
         point or long-lat-point.
        "precision=value"
        Create a reference to an index or lexicon configured with the
         specified geospatial precision. Allowed values: float
         and double. Only applicable if the index/lexicon value
         type is point or long-lat-point. This
         value takes precedence over the precision implicit in the coordinate
         system name.

**`$map`** *(optional)*
A map of namespace bindings. The keys should be namespace prefixes and the
  values should be namespace URIs. These namespace bindings will be added to
  the in-scope namespace bindings in the interpretation of the path.

### Returns

`cts:reference`

### Examples

```xquery
cts:path-reference("/section/title", ())
=>
cts:path-reference("/section/title",("type=string","collation=http://marklogic.com/collation/"))
```

---

## cts:reference-collation

Accessor for the collation of a reference to a string value lexicon.

### Signature

```xquery
cts:reference-collation(
  $index as cts:reference
) as xs:string
```

### Parameters

**`$index`**
The value lexicon reference, as created from cts:element-reference,
    for example.

### Returns

`xs:string`

### Examples

```xquery
cts:reference-collation(cts:element-reference(xs:QName("TITLE")))
=>
"http://marklogic.com/collation/"
```

---

## cts:reference-coordinate-system

Accessor for the coordinate-system of a reference to a geospatial lexicon.

### Signature

```xquery
cts:reference-coordinate-system(
  $index as cts:reference
) as xs:string
```

### Parameters

**`$index`**
The value lexicon reference, as created from cts:geospatial-element-reference,
    for example.

### Returns

`xs:string`

### Examples

```xquery
cts:reference-coordinate-system(cts:geospatial-element-reference(xs:QName("Point")))
=>
"wgs84"
```

---

## cts:reference-namespaces

Accessor for the namespaces of a reference to a [geospatial] path lexicon.

### Signature

```xquery
cts:reference-namespaces(
  $index as cts:reference
) as map:map
```

### Parameters

**`$index`**
The value lexicon reference, as created from cts:[geospatial-]path-reference,
    for example.

### Returns

`map:map`

### Examples

```xquery
let $ns := map:map() => map:with("a", "a-namespace")
                     => map:with("b", "b-namespace")
cts:reference-namespaces(cts:path-reference("/a:section/b:title", ("type=point"), $ns)
=>
<map:map xmlns:map="http://marklogic.com/xdmp/map" xmlns:xsi="http://www.w3.org/2001/XMLSchema-instance" xmlns:xs="http://www.w3.org/2001/XMLSchema">
  <map:entry key="a">
    <map:value xsi:type="xs:string">a-namespace</map:value>
  </map:entry>
  <map:entry key="b">
    <map:value xsi:type="xs:string">b-namespace</map:value>
  </map:entry>
</map:map>
```

---

## cts:reference-nullable

Returns true() if the reference is nullable, false() otherwise.

### Signature

```xquery
cts:reference-nullable(
  $reference as cts:reference
) as xs:boolean
```

### Parameters

**`$reference`**
An index reference.

### Returns

`xs:boolean`

### Examples

```xquery
cts:reference-nullable(cts:element-reference("title","nullable"))
=>
true()
```

---

## cts:reference-parse

Creates a reference to a value lexicon by parsing its XML or JSON
  representation, for use as a parameter to cts:value-tuples.  Since
  lexicons are implemented with range indexes, this function will
  throw an exception if the specified range index does not exist.

### Signature

```xquery
cts:reference-parse(
  $reference as node()
) as cts:reference
```

### Parameters

**`$reference`**
A reference to a range index.

### Returns

`cts:reference`

### Examples

```xquery
cts:reference-parse(
  <cts:element-reference xmlns:cts="http://marklogic.com/cts">
    <cts:namespace-uri>http://example.com/namespace</cts:namespace-uri>
    <cts:localname>title</cts:localname>
  </cts:element-reference>
)
=>
cts:element-reference(
  fn:QName("http://example.com/namespace","title"),("type=unknown"))
```

---

## cts:reference-scalar-type

Accessor for the scalar type of a reference to a value lexicon.

### Signature

```xquery
cts:reference-scalar-type(
  $index as cts:reference
) as xs:string
```

### Parameters

**`$index`**
The value lexicon reference, as created from cts:element-reference,
    for example.

### Returns

`xs:string`

### Examples

```xquery
cts:reference-scalar-type(cts:element-reference(xs:QName("TITLE")))
=>
"string"
```

---

## cts:triple-value-statistics

Returns statistics from the triple index for the values given. Note that these are estimates, rather than exact counts.

### Signature

```xquery
cts:triple-value-statistics(
  $values as xs:anyAtomicType*?,
  $forest-ids as xs:unsignedLong*?
) as element(triple-value-statistics)*
```

### Parameters

**`$values`** *(optional)*
The values to look up.

**`$forest-ids`** *(optional)*
A sequence of IDs of forests to which the search will be constrained.
    An empty sequence means to search all forests in the database.
    The default is ().

### Returns

`element(triple-value-statistics)*`

### Examples

```xquery
cts:triple-value-statistics((
  sem:iri("http://www.w3.org/2000/01/rdf-schema#subClassOf"),
  sem:iri("http://swat.cse.lehigh.edu/onto/univ-bench.owl#worksFor")
))
=>
<triple-value-statistics count="1104552010" unique-subjects="190980967" unique-predicates="587" unique-objects="280592619" xmlns="cts:triple-value-statistics">
  <triple-value-entries>
    <triple-value-entry count="86">
      <triple-value>http://www.w3.org/2000/01/rdf-schema#subClassOf</triple-value>
      <subject-statistics count="0" unique-predicates="0" unique-objects="0"/>
      <predicate-statistics count="86" unique-subjects="81" unique-objects="51"/>
      <object-statistics count="0" unique-subjects="0" unique-predicates="0"/>
    </triple-value-entry>
    <triple-value-entry count="5754107">
      <triple-value>http://swat.cse.lehigh.edu/onto/univ-bench.owl#worksFor</triple-value>
      <subject-statistics count="3" unique-predicates="3" unique-objects="3"/>
      <predicate-statistics count="5754099" unique-subjects="5754099" unique-objects="856163"/>
      <object-statistics count="4" unique-subjects="4" unique-predicates="4"/>
    </triple-value-entry>
  </triple-value-entries>
</triple-value-statistics>
```

---

## cts:triples

Returns values from the triple index. If subject, predicate, and object are
  given, then only triples with those given component values are returned. Triples can be
  returned in any of the sort orders present in the triple index.

### Signature

```xquery
cts:triples(
  $subject as xs:anyAtomicType*?,
  $predicate as xs:anyAtomicType*?,
  $object as xs:anyAtomicType*?,
  $operator as xs:string*?,
  $options as xs:string*?,
  $query as cts:query??,
  $forest-ids as xs:unsignedLong*?
) as sem:triple*
```

### Parameters

**`$subject`** *(optional)*
The subjects to look up. When multiple values are specified, the query matches if any value matches. When the empty sequence is specified, then triples with any subject are matched.

**`$predicate`** *(optional)*
The predicates to look up. When multiple values are specified, the query matches if any value matches. When the empty sequence is specified, then triples with any subject are matched.

**`$object`** *(optional)*
The objects to look up. When multiple values are specified, the query matches if any value matches. When the empty sequence is specified, then triples with any subject are matched.

**`$operator`** *(optional)*
If a single string is provided it is treated as the operator for the $object values. If a sequence
    of three strings are provided, they give the operators for $subject, $predicate and $object in turn.
    The default operator is "=".
    
      Operators include:
      
        "sameTerm"
        Match triple index values which are the same RDF term as $value.
        This compares aspects of values that are ignored in XML Schema comparison semantics,
        like timezone and derived type of $value.
        "<"
        Match range index values less than $value.
        "<="
        Match range index values less than or equal to $value.
        ">"
        Match range index values greater than $value.
        ">="
        Match range index values greater than or equal to $value.
        "="
        Match range index values equal to $value.
        "!="
        Match range index values not equal to $value.

**`$options`** *(optional)*
Options.  The default is ().
    
      Options include:
      
        "order-pso"
        Return results ordered by predicate, then subject, then object.
        "order-sop"
        Return results ordered by subject, then object, then predicate.
        "order-ops"
        Return results ordered by object, then predicate, then subject.
        "quads"
        Return quads that include values for the named graph that the
        triples are in. Requires the collection lexicon enabled.
        "any"
        Values from any fragment should be included.
        "document"
        Values from document fragments should be included.
        "properties"
        Values from properties fragments should be included.
        "locks"
        Values from locks fragments should be included.
        "fragment-frequency"
        Frequency should be the number of fragments with
        an included value.
        This option is used with cts:frequency.
        "item-frequency"
        Frequency should be the number of occurrences of
        an included value.
        This option is used with cts:frequency.
        
        "checked"
        Word positions should be checked when resolving the query.
        "unchecked"
        Word positions should not be checked when resolving the query.
        "too-many-positions-error"
        If too much memory is needed to perform positions calculations
        to check whether a document matches a query,
        return an XDMP-TOOMANYPOSITIONS error,
        instead of accepting the document as a match.
        "eager"
        Perform work concurrently whilst returning triples from the index -
        buffering some results into memory.
        This usually takes the shortest time when returning a complete
        result.
        "lazy"
        Perform only some the work concurrently before returning
        the first triple from the index, and most of the work
        sequentially while iterating through the rest of the triples.
        This usually takes the shortest time when returning a partial result.
        
        "concurrent"
        Perform the work concurrently in another thread. This is a hint
        to the query optimizer to help parallelize the lexicon work, allowing
        the calling query to continue performing other work while the lexicon
        processing occurs.  This is especially useful in cases where multiple
        lexicon calls occur in the same query (for example, resolving many
        facets in a single query).

**`$query`** *(optional)*
Only include values in fragments selected by the cts:query,
    and compute frequencies from this set of included values.
    The values do not need to match the query, but they must occur in
    fragments selected by the query.
    The fragments are not filtered to ensure they match the query,
    but instead selected in the same manner as
    
    "unfiltered" cts:search
    
    operations.  If a string
   is entered, the string is treated as a cts:word-query of the
   specified string.

**`$forest-ids`** *(optional)*
A sequence of IDs of forests to which the search will be constrained.
    An empty sequence means to search all forests in the database.
    The default is ().

### Returns

`sem:triple*`

### Usage Notes

Only one of "eager" or "lazy" may be specified
  in the options parameter.  If neither "eager" nor "lazy"
  is specified, then the default is "lazy".
      Only one of "any", "document", "properties", or "locks"
  may be specified in the options parameter.
  If none of "any", "document", "properties", or "locks" are specified
  and there is a $query parameter, then the default is "document".
  If there is no $query parameter then the default is "any".
      Only one of the "order-pso", "order-sop", or "order-ops"
  options may be specified in the options parameter.
  If none is specified, then the default is chosen to most efficiently retrieve
  the required values.
      Only one of the "checked" or "unchecked" options may be specified
  in the options parameter.
  If neither "checked" nor "unchecked" are specified,
  then the default is "checked".

### Examples

```xquery
cts:triples(sem:iri("http://subject"), sem:iri("http://predicate"), "object")
=>
 The triples with the given subject, predicate, and object.
```

---

## cts:uri-match

Returns values from the URI lexicon
   that match the specified wildcard pattern.
   This function requires the uri-lexicon database configuration
   parameter to be enabled. If the uri-lexicon database-configuration
   parameter is not enabled, an exception is thrown.

### Signature

```xquery
cts:uri-match(
  $pattern as xs:string,
  $options as xs:string*?,
  $query as cts:query??,
  $quality-weight as xs:double??,
  $forest-ids as xs:unsignedLong*?
) as xs:string*
```

### Parameters

**`$pattern`**
Wildcard pattern to match.

**`$options`** *(optional)*
Options.  The default is ().
    
      Options include:
      
        "case-sensitive"
        A case-sensitive match.
        "case-insensitive"
        A case-insensitive match.
        "diacritic-sensitive"
        A diacritic-sensitive match.
        "diacritic-insensitive"
        A diacritic-insensitive match.
        "ascending"
        URIs should be returned in ascending order.
        "descending"
        URIs should be returned in descending order.
        "any"
        URIs from any fragment should be included.
        "document"
        URIs from document fragments should be included.
        "properties"
        URIs from properties fragments should be included.
        "locks"
        URIs from locks fragments should be included.
        "frequency-order"
        URIs should be returned ordered by frequency.
        "item-order"
        URIs should be returned ordered by item.
        "limit=N"
        Return no more than N URIs. You should not
        use this option with the "skip" option. Use "truncate" instead.
        "skip=N"
        Skip over fragments selected by the cts:query
        to treat the Nth fragment as the first fragment.
        URIs from skipped fragments are not included.
        This option affects the number of fragments selected
        by the cts:query to calculate frequencies.
        Only applies when a $query parameter is specified.
        "sample=N"
        Return only URIs from the first N fragments after
        skip selected by the cts:query.
        This option does not affect the number of fragments selected
        by the cts:query to calculate frequencies.
        Only applies when a $query parameter is specified.
        "truncate=N"
        Include only URIs from the first N fragments after
        skip selected by the cts:query.
        This option also affects the number of fragments selected
        by the cts:query to calculate frequencies.
        Only applies when a $query parameter is specified.
        "score-logtfidf"
        Compute scores using the logtfidf method.
        Only applies when a $query parameter is specified.
        "score-logtf"
        Compute scores using the logtf method.
        Only applies when a $query parameter is specified.
        "score-simple"
        Compute scores using the simple method.
        Only applies when a $query parameter is specified.
        "score-random"
        Compute scores using the random method.
        Only applies when a $query parameter is specified.
        "score-zero"
        Compute all scores as zero.
        Only applies when a $query parameter is specified.
        "checked"
        Word positions should be checked when resolving the query.
        "unchecked"
        Word positions should not be checked when resolving the query.
        "too-many-positions-error"
        If too much memory is needed to perform positions calculations
        to check whether a document matches a query,
        return an XDMP-TOOMANYPOSITIONS error,
        instead of accepting the document as a match.
        "eager"
        Perform most of the work concurrently before returning
        the first item from the indexes, and only some of the work
        sequentially while iterating through the rest of the items.
        This usually takes the shortest time for a complete item-order
        result or for any frequency-order result.
        "lazy"
        Perform only some the work concurrently before returning
        the first item from the indexes, and most of the work
        sequentially while iterating through the rest of the items.
        This usually takes the shortest time for a small item-order
        partial result.
        "concurrent"
        Perform the work concurrently in another thread. This is a hint
        to the query optimizer to help parallelize the lexicon work, allowing
        the calling query to continue performing other work while the lexicon
        processing occurs.  This is especially useful in cases where multiple
        lexicon calls occur in the same query (for example, resolving many
        facets in a single query).
        "map"
        Return results as a single map:map
         value instead of as an xs:string* sequence
         .

**`$query`** *(optional)*
Only include URIs from fragments selected by the cts:query,
    and compute frequencies from this set of included URIs.
    The fragments are not filtered to ensure they match the query,
    but instead selected in the same manner as
    
    "unfiltered" cts:search
    
    operations.  If a string
   is entered, the string is treated as a cts:word-query of the
   specified string.

**`$quality-weight`** *(optional)*
A document quality weight to use when computing scores.
    The default is 1.0.

**`$forest-ids`** *(optional)*
A sequence of IDs of forests to which the search will be constrained.
    An empty sequence means to search all forests in the database.
    The default is ().

### Returns

`xs:string*`

### Usage Notes

Only one of "frequency-order" or "item-order" may be specified
  in the options parameter.  If neither "frequency-order" nor "item-order"
  is specified, then the default is "item-order".
      Only one of "ascending" or "descending" may be specified
  in the options parameter.  If neither "ascending" nor "descending"
  is specified, then the default is "ascending" if "item-order" is
  specified, and "descending" if "frequency-order" is specified.
      Only one of "eager" or "lazy" may be specified
  in the options parameter.  If neither "eager" nor "lazy"
  is specified, then the default is "lazy" if "item-order" is
  specified, and "eager" if "frequency-order" is specified.
      Only one of "any", "document", "properties", or "locks"
  may be specified in the options parameter.
  If none of "any", "document", "properties", or "locks" are specified
  and there is a $query parameter, then the default is "document".
  If there is no $query parameter then the default is "any".
      Only one of the "score-logtfidf", "score-logtf", "score-simple",
  "score-random", or "score-zero" options may be specified in the options
  parameter.
  If none of "score-logtfidf", "score-logtf", "score-simple", "score-random",
  or "score-zero" are specified, then the default is "score-logtfidf".
      Only one of the "checked" or "unchecked" options may be specified
  in the options parameter.
  If neither "checked" nor "unchecked" are specified,
  then the default is "checked".
      If "sample=N" is not specified in the options parameter,
  then all included URIs may be returned. If a $query parameter
  is not present, then "sample=N" has no effect.
      If "truncate=N" is not specified in the options parameter,
  then URIs from all fragments selected by the $query parameter
  are included.  If a $query parameter is not present, then
  "truncate=N" has no effect.
      To incrementally fetch a subset of the values returned by this function,
  use fn:subsequence
  
  on the output, rather than the "skip" option as 
  the skip is applied to the relevance ordered query matches, 
  not to the ordered values list. 
      When using the "skip" option, use the "truncate" option rather than 
  the "limit" option to control the number of matching fragments from which 
  to draw values.
      
    If neither "case-sensitive" nor "case-insensitive"
    is present, $pattern is used to determine case sensitivity.
    If $pattern contains no uppercase, it specifies "case-insensitive".
    If $pattern contains uppercase, it specifies "case-sensitive".
  
      
    If neither "diacritic-sensitive" nor "diacritic-insensitive"
    is present, $pattern is used to determine diacritic sensitivity.
    If $pattern contains no diacritics, it specifies "diacritic-insensitive".
    If $pattern contains diacritics, it specifies "diacritic-sensitive".

### Examples

```xquery
cts:uri-match("http://foo.com*.html")
  => ("http://foo.com/bar.html", "http://foo.com/baz/bork.html", ...)
```

---

## cts:uri-reference

Creates a reference to the URI lexicon, for use as a parameter to
  cts:value-tuples.  This function requires the URI lexicon to be enabled,
  otherwise it throws an exception.

### Returns

`cts:reference`

### Examples

```xquery
cts:uri-reference()
=>
cts:uri-reference()
```

---

## cts:uris

Returns values from the URI lexicon.
  This function requires the uri-lexicon database configuration
  parameter to be enabled. If the uri-lexicon database-configuration
  parameter is not enabled, an exception is thrown.

### Signature

```xquery
cts:uris(
  $start as xs:string??,
  $options as xs:string*?,
  $query as cts:query??,
  $quality-weight as xs:double??,
  $forest-ids as xs:unsignedLong*?
) as xs:string*
```

### Parameters

**`$start`** *(optional)*
A starting value.  Return only this value and following values.  If
    the empty string, return all values.  If the parameter is not in
    the lexicon, then it returns the values beginning with the next
    value.

**`$options`** *(optional)*
Options.  The default is ().
    
      Options include:
      
        "ascending"
        URIs should be returned in ascending order.
        "descending"
        URIs should be returned in descending order.
        "any"
        URIs from any fragment should be included.
        "document"
        URIs from document fragments should be included.
        "properties"
        URIs from properties fragments should be included.
        "locks"
        URIs from locks fragments should be included.
        "frequency-order"
        URIs should be returned ordered by frequency.
        "item-order"
        URIs should be returned ordered by item.
        "limit=N"
        Return no more than N URIs. You should not
        use this option with the "skip" option. Use "truncate" instead.
        "skip=N"
        Skip over fragments selected by the cts:query
        to treat the Nth fragment as the first fragment.
        URIs from skipped fragments are not included.
        This option affects the number of fragments selected
        by the cts:query to calculate frequencies.
        Only applies when a $query parameter is specified.
        "sample=N"
        Return only URIs from the first N fragments after
        skip selected by the cts:query.
        This option does not affect the number of fragments selected
        by the cts:query to calculate frequencies.
        Only applies when a $query parameter is specified.
        "truncate=N"
        Include only URIs from the first N fragments after
        skip selected by the cts:query.
        This option also affects the number of fragments selected
        by the cts:query to calculate frequencies.
        Only applies when a $query parameter is specified.
        "score-logtfidf"
        Compute scores using the logtfidf method.
        Only applies when a $query parameter is specified.
        "score-logtf"
        Compute scores using the logtf method.
        Only applies when a $query parameter is specified.
        "score-simple"
        Compute scores using the simple method.
        Only applies when a $query parameter is specified.
        "score-random"
        Compute scores using the random method.
        Only applies when a $query parameter is specified.
        "score-zero"
        Compute all scores as zero.
        Only applies when a $query parameter is specified.
        "checked"
        Word positions should be checked when resolving the query.
        "unchecked"
        Word positions should not be checked when resolving the query.
        "too-many-positions-error"
        If too much memory is needed to perform positions calculations
        to check whether a document matches a query,
        return an XDMP-TOOMANYPOSITIONS error,
        instead of accepting the document as a match.
        "eager"
        Perform most of the work concurrently before returning
        the first item from the indexes, and only some of the work
        sequentially while iterating through the rest of the items.
        This usually takes the shortest time for a complete item-order
        result or for any frequency-order result.
        "lazy"
        Perform only some the work concurrently before returning
        the first item from the indexes, and most of the work
        sequentially while iterating through the rest of the items.
        This usually takes the shortest time for a small item-order
        partial result.
        "concurrent"
        Perform the work concurrently in another thread. This is a hint
        to the query optimizer to help parallelize the lexicon work, allowing
        the calling query to continue performing other work while the lexicon
        processing occurs.  This is especially useful in cases where multiple
        lexicon calls occur in the same query (for example, resolving many
        facets in a single query).
        "map"
        Return results as a single map:map
         value instead of as an xs:string* sequence
         .

**`$query`** *(optional)*
Only include URIs from fragments selected by the cts:query,
    and compute frequencies from this set of included URIs.
    The fragments are not filtered to ensure they match the query,
    but instead selected in the same manner as
    
    "unfiltered" cts:search
    
    operations.  If a string
   is entered, the string is treated as a cts:word-query of the
   specified string.

**`$quality-weight`** *(optional)*
A document quality weight to use when computing scores.
    The default is 1.0.

**`$forest-ids`** *(optional)*
A sequence of IDs of forests to which the search will be constrained.
    An empty sequence means to search all forests in the database.
    The default is ().

### Returns

`xs:string*`

### Usage Notes

Only one of "frequency-order" or "item-order" may be specified
  in the options parameter.  If neither "frequency-order" nor "item-order"
  is specified, then the default is "item-order".
      Only one of "ascending" or "descending" may be specified
  in the options parameter.  If neither "ascending" nor "descending"
  is specified, then the default is "ascending" if "item-order" is
  specified, and "descending" if "frequency-order" is specified.
      Only one of "eager" or "lazy" may be specified
  in the options parameter.  If neither "eager" nor "lazy"
  is specified, then the default is "lazy" if "item-order" is
  specified, and "eager" if "frequency-order" is specified.
      Only one of "any", "document", "properties", or "locks"
  may be specified in the options parameter.
  If none of "any", "document", "properties", or "locks" are specified
  and there is a $query parameter, then the default is "document".
  If there is no $query parameter then the default is "any".
      Only one of the "score-logtfidf", "score-logtf", "score-simple",
  "score-random", or "score-zero" options may be specified in the options
  parameter.
  If none of "score-logtfidf", "score-logtf", "score-simple", "score-random",
  or "score-zero" are specified, then the default is "score-logtfidf".
      Only one of the "checked" or "unchecked" options may be specified
  in the options parameter.
  If neither "checked" nor "unchecked" are specified,
  then the default is "checked".
      If "sample=N" is not specified in the options parameter,
  then all included URIs may be returned. If a $query parameter
  is not present, then "sample=N" has no effect.
      If "truncate=N" is not specified in the options parameter,
  then URIs from all fragments selected by the $query parameter
  are included.  If a $query parameter is not present, then
  "truncate=N" has no effect.
      To incrementally fetch a subset of the values returned by this function,
  use fn:subsequence
  
  on the output, rather than the "skip" option as
  the skip is applied to the relevance ordered query matches, 
  not to the ordered values list. 
      When using the "skip" option, use the "truncate" option rather than 
  the "limit" option to control the number of matching fragments from which 
  to draw values.

### Examples

#### Example 1

```xquery
cts:uris("http://foo.com/")
  => ("http://foo.com/", "http://foo.com/bar.html", ...)
```

#### Example 2

```xquery
cts:uris("", (), cts:word-query("word"))
  => all the URIs of documents that have the word "word" in them
```

---

## cts:value-co-occurrences

Returns value co-occurrences (that is, pairs of values, both of which appear
  in the same fragment) from the specified value lexicon(s).  The
  values are returned as an XML element
   with two children, each child
  containing one of the co-occurring values.  You can use
  cts:frequency
  on each item returned to find how many times the pair occurs.
  Value lexicons are implemented using range indexes; consequently
  this function requires a range index for each input index reference.
  If an index or lexicon is not configured for any of the input references,
  an exception is thrown.

### Signature

```xquery
cts:value-co-occurrences(
  $range-index-1 as cts:reference,
  $range-index-2 as cts:reference,
  $options as xs:string*?,
  $query as cts:query??,
  $quality-weight as xs:double??,
  $forest-ids as xs:unsignedLong*?
) as element(cts:co-occurrence)*
```

### Parameters

**`$range-index-1`**
A reference to a range index.

**`$range-index-2`**
A reference to a range index.

**`$options`** *(optional)*
Options.  The default is ().
    
      Options include:
      
        "ascending"
        Co-occurrences should be returned in ascending order.
        "descending"
        Co-occurrences should be returned in descending order.
        "any"
        Co-occurrences from any fragment should be included.
        "document"
        Co-occurrences from document fragments should be included.
        "properties"
        Co-occurrences from properties fragments should be included.
        "locks"
        Co-occurrences from locks fragments should be included.
        "frequency-order"
        Co-occurrences should be returned ordered by frequency.
        "item-order"
        Co-occurrences should be returned ordered by item.
        "fragment-frequency"
        Frequency should be the number of fragments with
        an included co-occurrences.
        This option is used with cts:frequency.
        "item-frequency"
        Frequency should be the number of occurrences of
        an included co-occurrence.
        This option is used with cts:frequency.
        "timezone=TZ"
        Return timezone sensitive values (dateTime, time, date,
        gYearMonth, gYear, gMonth, and gDay) adjusted to the timezone
        specified by TZ.
        Example timezones: Z, -08:00, +01:00.
        "ordered"
        Include co-occurrences only when the value from the first lexicon
        appears before the value from the second lexicon.
        Requires that word positions be enabled for both lexicons.
        "proximity=N"
        Include co-occurrences only when the values appear within
        N words of each other.
        Requires that word positions be enabled for both lexicons.
        "limit=N"
        Return no more than N co-occurrences. You should not
        use this option with the "skip" option. Use "truncate" instead.
        "skip=N"
        Skip over fragments selected by the cts:query
        to treat the Nth fragment as the first fragment.
        Co-occurrences from skipped fragments are not included.
        This option affects the number of fragments selected
        by the cts:query to calculate frequencies.
        Only applies when a $query parameter is specified.
        "sample=N"
        Return only co-occurrences from the first N
        fragments after skip selected by the cts:query.
        This option does not affect the number of fragments selected
        by the cts:query to calculate frequencies.
        Only applies when a $query parameter is specified.
        Return only co-occurrences from the first N
        fragments after skip selected by the cts:query,
        bit do not affect frequencies.
        Only applies when a $query parameter is specified.
        "truncate=N"
        Include only co-occurrences from the first N
        fragments after skip selected by the cts:query.
        This option also affects the number of fragments selected
        by the cts:query to calculate frequencies.
        Only applies when a $query parameter is specified.
        "score-logtfidf"
        Compute scores using the logtfidf method.
        Only applies when a $query parameter is specified.
        "score-logtf"
        Compute scores using the logtf method.
        Only applies when a $query parameter is specified.
        "score-simple"
        Compute scores using the simple method.
        Only applies when a $query parameter is specified.
        "score-random"
        Compute scores using the random method.
        Only applies when a $query parameter is specified.
        "score-zero"
        Compute all scores as zero.
        Only applies when a $query parameter is specified.
        "checked"
        Word positions should be checked when resolving the query.
        "unchecked"
        Word positions should not be checked when resolving the query.
        "too-many-positions-error"
        If too much memory is needed to perform positions calculations
        to check whether a document matches a query,
        return an XDMP-TOOMANYPOSITIONS error,
        instead of accepting the document as a match.
        "eager"
        Perform most of the work concurrently before returning
        the first item from the indexes, and only some of the work
        sequentially while iterating through the rest of the items.
        This usually takes the shortest time for a complete item-order
        result or for any frequency-order result.
        "lazy"
        Perform only some the work concurrently before returning
        the first item from the indexes, and most of the work
        sequentially while iterating through the rest of the items.
        This usually takes the shortest time for a small item-order
        partial result.
        "concurrent"
        Perform the work concurrently in another thread. This is a hint
        to the query optimizer to help parallelize the lexicon work, allowing
        the calling query to continue performing other work while the lexicon
        processing occurs.  This is especially useful in cases where multiple
        lexicon calls occur in the same query (for example, resolving many
        facets in a single query).
        "map"
        Return results as a single map:map
         value instead of as an element(cts:co-occurrence)* sequence
         .

**`$query`** *(optional)*
Only include co-occurrences in fragments selected by the
    cts:query,
    and compute frequencies from this set of included co-occurrences.
    The co-occurrences do not need to match the query, but they must occur in
    fragments selected by the query.
    The fragments are not filtered to ensure they match the query,
    but instead selected in the same manner as
    
    "unfiltered" cts:search
    
    operations.  If a string
   is entered, the string is treated as a cts:word-query of the
   specified string.

**`$quality-weight`** *(optional)*
A document quality weight to use when computing scores.
    The default is 1.0.

**`$forest-ids`** *(optional)*
A sequence of IDs of forests to which the search will be constrained.
    An empty sequence means to search all forests in the database.
    The default is ().

### Returns

`element(cts:co-occurrence)*`

### Usage Notes

Only one of "frequency-order" or "item-order" may be specified
  in the options parameter.  If neither "frequency-order" nor "item-order"
  is specified, then the default is "item-order".
      Only one of "fragment-frequency" or "item-frequency" may be specified
  in the options parameter.  If neither "fragment-frequency" nor
  "item-frequency" is specified, then the default is "fragment-frequency".
      Only one of "ascending" or "descending" may be specified
  in the options parameter.  If neither "ascending" nor "descending"
  is specified, then the default is "ascending" if "item-order" is
  specified, and "descending" if "frequency-order" is specified.
      Only one of "eager" or "lazy" may be specified
  in the options parameter.  If neither "eager" nor "lazy"
  is specified, then the default is "eager" if "frequency-order" or "map"
  is specified, otherwise "lazy".
      Only one of "any", "document", "properties", or "locks"
  may be specified in the options parameter.
  If none of "any", "document", "properties", or "locks" are specified
  and there is a $query parameter, then the default is "document".
  If there is no $query parameter then the default is "any".
      Only one of the "score-logtfidf", "score-logtf", "score-simple",
  "score-random", or "score-zero" options may be specified in the options
  parameter.
  If none of "score-logtfidf", "score-logtf", "score-simple", "score-random",
  or "score-zero" are specified, then the default is "score-logtfidf".
      Only one of the "checked" or "unchecked" options may be specified
  in the options parameter.
  If neither "checked" nor "unchecked" are specified,
  then the default is "checked".
      If "collation=URI" is not specified in the options parameter,
  then the default collation is used. If a lexicon with that collation
  does not exist, an error is thrown.
      If "sample=N" is not specified in the options parameter,
  then all included co-occurrences may be returned.
  If a $query parameter
  is not present, then "sample=N" has no effect.
      If "truncate=N" is not specified in the options parameter,
  then co-occurrences from all fragments selected by the
  $query parameter are included.
  If a $query parameter is not present, then
  "truncate=N" has no effect.
      To incrementally fetch a subset of the co-occurrences returned by this
  function, use fn:subsequence
  
  on the output, rather than 
  the "skip" option. The "skip" option is based on fragments matching the 
  query parameter (if present), not on occurrences. A fragment 
  matched by query might contain multiple occurrences or no occurrences. 
  The number of fragments skipped does not correspond to the number of 
  values. Also, the skip is applied to the relevance ordered query matches, 
  not to the ordered co-occurrences list. 
      When using the "skip" option, use the "truncate" option rather than 
  the "limit" option to control the number of matching fragments from which 
  to draw values.

### Examples

```xquery
(: Suppose we have a document with many news items in the database. :)

xdmp:document-insert("/news.xml",
<news>
  <sale>
   <sold-item>Bike</sold-item>
    <name>
      <first>John</first><last>Griffith</last>
    </name>
    <city>Reno</city>
    <text>...</text>
  </sale>
  <sale>
   <sold-item>Car</sold-item>
    <name>
      <first>Will</first><last>Shields</last>
    </name>
    <city>Lexington</city>
    <text>...</text>
  </sale>
  <theft>
    <stolen-item>Bike</stolen-item>
    <reporter>
      <first>John</first><last>Smith</last>
    </reporter>
    <city>Las Vegas</city>
    <text>...</text>
  </theft>
  <theft>
    <stolen-item>Car</stolen-item>
    <reporter>
      <first>Will</first><last>Shields</last>
    </reporter>
    <city>Indianapolis</city>
    <text>...</text>
  </theft>
</news>);


(: Now suppose we have two path range indexes defined.
     Index1: /news/sale/sold-item string type
     Index2: /news/sale/city  string type

   We can find co-occurrence of items sold and the city it was sold in.
:)

  cts:value-co-occurrences(cts:path-reference("/news/sale/sold-item"),
                           cts:path-reference("/news/sale/city"))
=>
<cts:co-occurrence xmlns:cts="http://marklogic.com/cts"
  xmlns:xsi="http://www.w3.org/2001/XMLSchema-instance"
  xmlns:xs="http://www.w3.org/2001/XMLSchema">
  <cts:value xsi:type="xs:string">Bike</cts:value>
  <cts:value xsi:type="xs:string">Lexington</cts:value>
</cts:co-occurrence>
<cts:co-occurrence xmlns:cts="http://marklogic.com/cts"
  xmlns:xsi="http://www.w3.org/2001/XMLSchema-instance"
  xmlns:xs="http://www.w3.org/2001/XMLSchema">
  <cts:value xsi:type="xs:string">Bike</cts:value>
  <cts:value xsi:type="xs:string">Reno</cts:value>
</cts:co-occurrence>
<cts:co-occurrence xmlns:cts="http://marklogic.com/cts"
  xmlns:xsi="http://www.w3.org/2001/XMLSchema-instance"
  xmlns:xs="http://www.w3.org/2001/XMLSchema">
  <cts:value xsi:type="xs:string">Car</cts:value>
  <cts:value xsi:type="xs:string">Lexington</cts:value>
</cts:co-occurrence>
<cts:co-occurrence xmlns:cts="http://marklogic.com/cts"
  xmlns:xsi="http://www.w3.org/2001/XMLSchema-instance"
  xmlns:xs="http://www.w3.org/2001/XMLSchema">
  <cts:value xsi:type="xs:string">Car</cts:value>
  <cts:value xsi:type="xs:string">Reno</cts:value>
</cts:co-occurrence>
```

---

## cts:value-match

Returns values from the specified value lexicon(s)
   that match the specified wildcard pattern.  Value lexicons
   are implemented using range indexes; consequently this function
   requires a range index for each index reference specified in the
   function.  If there is not a range index configured for each of the
   specified references, then an exception is thrown.

### Signature

```xquery
cts:value-match(
  $range-indexes as cts:reference*,
  $pattern as xs:anyAtomicType,
  $options as xs:string*?,
  $query as cts:query??,
  $quality-weight as xs:double??,
  $forest-ids as xs:unsignedLong*?
) as xs:anyAtomicType*
```

### Parameters

**`$range-indexes`**
A sequence of references to range indexes.

**`$pattern`**
A pattern to match. The parameter type must match the lexicon type.
    String parameters may include wildcard characters.

**`$options`** *(optional)*
Options.  The default is ().
    
      Options include:
      
        "case-sensitive"
        A case-sensitive match.
        "case-insensitive"
        A case-insensitive match.
        "diacritic-sensitive"
        A diacritic-sensitive match.
        "diacritic-insensitive"
        A diacritic-insensitive match.
        "ascending"
        Values should be returned in ascending order.
        "descending"
        Values should be returned in descending order.
        "any"
        Values from any fragment should be included.
        "document"
        Values from document fragments should be included.
        "properties"
        Values from properties fragments should be included.
        "locks"
        Values from locks fragments should be included.
        "frequency-order"
        Values should be returned ordered by frequency.
        "item-order"
        Values should be returned ordered by item.
        "fragment-frequency"
        Frequency should be the number of fragments with
        an included value.
        This option is used with cts:frequency.
        "item-frequency"
        Frequency should be the number of occurrences of
        an included value.
        This option is used with cts:frequency.
        "timezone=TZ"
        Return timezone sensitive values (dateTime, time, date,
        gYearMonth, gYear, gMonth, and gDay) adjusted to the timezone
        specified by TZ.
        Example timezones: Z, -08:00, +01:00.
        "limit=N"
        Return no more than N values. You should not
        use this option with the "skip" option. Use "truncate" instead.
        "skip=N"
        Skip over fragments selected by the cts:query
        to treat the Nth fragment as the first fragment.
        Values from skipped fragments are not included.
        This option affects the number of fragments selected
        by the cts:query to calculate frequencies.
        Only applies when a $query parameter is specified.
        "sample=N"
        Return only values from the first N
        fragments after skip selected by the cts:query.
        This option does not affect the number of fragments selected
        by the cts:query to calculate frequencies.
        Only applies when a $query parameter is specified.
        "truncate=N"
        Include only values from the first N fragments
        after skip selected by the cts:query.
        This option also affects the number of fragments selected
        by the cts:query to calculate frequencies.
        Only applies when a $query parameter is specified.
        "score-logtfidf"
        Compute scores using the logtfidf method.
        Only applies when a $query parameter is specified.
        "score-logtf"
        Compute scores using the logtf method.
        Only applies when a $query parameter is specified.
        "score-simple"
        Compute scores using the simple method.
        Only applies when a $query parameter is specified.
        "score-random"
        Compute scores using the random method.
        Only applies when a $query parameter is specified.
        "score-zero"
        Compute all scores as zero.
        Only applies when a $query parameter is specified.
        "checked"
        Word positions should be checked when resolving the query.
        "unchecked"
        Word positions should not be checked when resolving the query.
        "too-many-positions-error"
        If too much memory is needed to perform positions calculations
        to check whether a document matches a query,
        return an XDMP-TOOMANYPOSITIONS error,
        instead of accepting the document as a match.
        "eager"
        Perform most of the work concurrently before returning
        the first item from the indexes, and only some of the work
        sequentially while iterating through the rest of the items.
        This usually takes the shortest time for a complete item-order
        result or for any frequency-order result.
        "lazy"
        Perform only some the work concurrently before returning
        the first item from the indexes, and most of the work
        sequentially while iterating through the rest of the items.
        This usually takes the shortest time for a small item-order
        partial result.
        "concurrent"
        Perform the work concurrently in another thread. This is a hint
        to the query optimizer to help parallelize the lexicon work, allowing
        the calling query to continue performing other work while the lexicon
        processing occurs.  This is especially useful in cases where multiple
        lexicon calls occur in the same query (for example, resolving many
        facets in a single query).
        "map"
        Return results as a single map:map
         value instead of as an xs:anyAtomicType* sequence
         .

**`$query`** *(optional)*
Only include values in fragments selected by the cts:query,
    and compute frequencies from this set of included values.
    The values do not need to match the query, but they must occur in
    fragments selected by the query.
    The fragments are not filtered to ensure they match the query,
    but instead selected in the same manner as
    
    "unfiltered" cts:search
    
    operations.  If a string
   is entered, the string is treated as a cts:word-query of the
   specified string.

**`$quality-weight`** *(optional)*
A document quality weight to use when computing scores.
    The default is 1.0.

**`$forest-ids`** *(optional)*
A sequence of IDs of forests to which the search will be constrained.
    An empty sequence means to search all forests in the database.
    The default is ().

### Returns

`xs:anyAtomicType*`

### Usage Notes

Only one of "frequency-order" or "item-order" may be specified
  in the options parameter.  If neither "frequency-order" nor "item-order"
  is specified, then the default is "item-order".
      Only one of "fragment-frequency" or "item-frequency" may be specified
  in the options parameter.  If neither "fragment-frequency" nor
  "item-frequency" is specified, then the default is "fragment-frequency".
      Only one of "ascending" or "descending" may be specified
  in the options parameter.  If neither "ascending" nor "descending"
  is specified, then the default is "ascending" if "item-order" is
  specified, and "descending" if "frequency-order" is specified.
      Only one of "any", "document", "properties", or "locks"
  may be specified in the options parameter.
  If none of "any", "document", "properties", or "locks" are specified
  and there is a $query parameter, then the default is "document".
  If there is no $query parameter then the default is "any".
      Only one of the "score-logtfidf", "score-logtf", "score-simple",
  "score-random", or "score-zero" options may be specified in the options
  parameter.
  If none of "score-logtfidf", "score-logtf", "score-simple", "score-random",
  or "score-zero" are specified, then the default is "score-logtfidf".
      Only one of the "checked" or "unchecked" options may be specified
  in the options parameter.
  If neither "checked" nor "unchecked" are specified,
  then the default is "checked".
      If "collation=URI" is not specified in the options parameter,
  then the default collation is used.  If a range index with that collation
  does not exist, an error is thrown.
      If "sample=N" is not specified in the options parameter,
  then all included values may be returned. If a $query parameter
  is not present, then "sample=N" has no effect.
      If "truncate=N" is not specified in the options parameter,
  then values from all fragments selected by the $query parameter
  are included.  If a $query parameter is not present, then
  "truncate=N" has no effect.
      To incrementally fetch a subset of the values returned by this function,
  use fn:subsequence
  
  on the output, rather than 
  the "skip" option. The "skip" option is based on fragments matching the 
  query parameter (if present), not on values. A fragment 
  matched by query might contain multiple values or no values. 
  The number of fragments skipped does not correspond to the number of 
  values. Also, the skip is applied to the relevance ordered query matches, 
  not to the ordered values list. 
      When using the "skip" option, use the "truncate" option rather than 
  the "limit" option to control the number of matching fragments from which 
  to draw values.
      
    If neither "case-sensitive" nor "case-insensitive"
    is present, $pattern is used to determine case sensitivity.
    If $pattern contains no uppercase, it specifies "case-insensitive".
    If $pattern contains uppercase, it specifies "case-sensitive".
  
      
    If neither "diacritic-sensitive" nor "diacritic-insensitive"
    is present, $pattern is used to determine diacritic sensitivity.
    If $pattern contains no diacritics, it specifies "diacritic-insensitive".
    If $pattern contains diacritics, it specifies "diacritic-sensitive".

### Examples

```xquery
(:
  Assuming that there are path namespaces defined with the following prefixes:
  my: http://aaa.com
  his: http://bbb.com

  Further assuming that a path index is defined using the above namespaces,
  '/my:a[@his:b="B1"]/my:c'.
:)
  xquery version "1.0-ml";

  declare namespace my = "http://aaa.com";
  declare namespace his = "http://bbb.com";

  xdmp:document-insert("/abc1.xml",<my:a his:b="B1"><my:c>C1</my:c></my:a>),
  xdmp:document-insert("/abc2.xml",<my:a his:b="B1"><my:c>C2</my:c></my:a>),
  xdmp:document-insert("/abc3.xml",<my:a his:b="B1"><my:c>C3</my:c></my:a>)

  (: The following is based on the above setup :)
  xquery version "1.0-ml";

  declare namespace my = "http://aaa.com";
  declare namespace his = "http://bbb.com";

  cts:value-match(cts:path-reference('/my:a[@his:b="B1"]/my:c'), "?3")
  =>
    C3
```

---

## cts:value-ranges

Returns value ranges from the specified value lexicon(s).
  Value lexicons are implemented using range indexes; consequently this
  function requires a range index for each element specified
  in the function.  If there is not an index or lexicon configured for
  one of the specified references, an exception is thrown.
      The values are divided into buckets. The $bounds parameter specifies
  the number of buckets and the size of each bucket.
  All included values are bucketed, even those less than the lowest bound
  or greater than the highest bound. An empty sequence for $bounds specifies
  one bucket, a single value specifies two buckets, two values specify
  three buckets, and so on.
      If you have string values and you pass a $bounds parameter
   as in the following call:
      cts:value-ranges(cts:path-reference("/name/fname"), ("f", "m"))
      The first bucket contains string values that are less than the
  string f, the second bucket contains string values greater than
  or equal to f but less than m, and the third bucket
  contains string values that are greater than or equal to m.
      For each non-empty bucket, a cts:range element is returned.
  Each cts:range element has a cts:minimum child
  and a cts:maximum child.  If a bucket is bounded, its
  cts:range element will also have a
  cts:lower-bound child if it is bounded from below, and
  a cts:upper-bound element if it is bounded from above.
  Empty buckets return nothing unless the "empties" option is specified.

### Signature

```xquery
cts:value-ranges(
  $range-indexes as cts:reference*,
  $bounds as xs:anyAtomicType*?,
  $options as xs:string*?,
  $query as cts:query??,
  $quality-weight as xs:double??,
  $forest-ids as xs:unsignedLong*?
) as element(cts:range)*
```

### Parameters

**`$range-indexes`**
A sequence of references to range indexes.

**`$bounds`** *(optional)*
A sequence of range bounds.
    The types must match the lexicon type.
    The values must be in strictly ascending order, otherwise an exception
    is thrown.

**`$options`** *(optional)*
Options.  The default is ().
    
      Options include:
      
        "ascending"
        Ranges should be returned in ascending order.
        "descending"
        Ranges should be returned in descending order.
        "empties"
        Include fully-bounded ranges whose frequency is 0. These ranges
        will have no minimum or maximum value.  Only empty ranges that have
        both their upper and lower bounds specified in the $bounds
        options are returned;
        any empty ranges that are less than the first bound or greater than the
        last bound are not returned.  For example, if you specify 4 bounds
        and there are no results for any of the bounds, 3 elements are
        returned (not 5 elements).
        "any"
        Values from any fragment should be included.
        "document"
        Values from document fragments should be included.
        "properties"
        Values from properties fragments should be included.
        "locks"
        Values from locks fragments should be included.
        "frequency-order"
        Ranges should be returned ordered by frequency.
        "item-order"
        Ranges should be returned ordered by item.
        "fragment-frequency"
        Frequency should be the number of fragments with
        an included value.
        This option is used with cts:frequency.
        "item-frequency"
        Frequency should be the number of occurrences of
        an included value.
        This option is used with cts:frequency.
        "timezone=TZ"
        Return timezone sensitive values (dateTime, time, date,
        gYearMonth, gYear, gMonth, and gDay) adjusted to the timezone
        specified by TZ.
        Example timezones: Z, -08:00, +01:00.
        "limit=N"
        Return no more than N ranges. You should not
        use this option with the "skip" option. Use "truncate" instead.
        "skip=N"
        Skip over fragments selected by the cts:query
        to treat the Nth fragment as the first fragment.
        Values from skipped fragments are not included.
        This option affects the number of fragments selected
        by the cts:query to calculate frequencies.
        Only applies when a $query parameter is specified.
        "sample=N"
        Return only ranges for buckets with at least one value from
        the first N fragments after skip selected by the
        cts:query.
        This option does not affect the number of fragments selected
        by the cts:query to calculate frequencies.
        Only applies when a $query parameter is specified.
        "truncate=N"
        Include only values from the first N fragments
        after skip selected by the cts:query.
        This option also affects the number of fragments selected
        by the cts:query to calculate frequencies.
        Only applies when a $query parameter is specified.
        "score-logtfidf"
        Compute scores using the logtfidf method.
        Only applies when a $query parameter is specified.
        "score-logtf"
        Compute scores using the logtf method.
        Only applies when a $query parameter is specified.
        "score-simple"
        Compute scores using the simple method.
        Only applies when a $query parameter is specified.
        "score-random"
        Compute scores using the random method.
        Only applies when a $query parameter is specified.
        "score-zero"
        Compute all scores as zero.
        Only applies when a $query parameter is specified.
        "checked"
        Word positions should be checked when resolving the query.
        "unchecked"
        Word positions should not be checked when resolving the query.
        "too-many-positions-error"
        If too much memory is needed to perform positions calculations
        to check whether a document matches a query,
        return an XDMP-TOOMANYPOSITIONS error,
        instead of accepting the document as a match.
        "eager"
        Perform most of the work concurrently before returning
        the first item from the indexes, and only some of the work
        sequentially while iterating through the rest of the items.
        This usually takes the shortest time for a complete item-order
        result or for any frequency-order result.
        "lazy"
        Perform only some the work concurrently before returning
        the first item from the indexes, and most of the work
        sequentially while iterating through the rest of the items.
        This usually takes the shortest time for a small item-order
        partial result.
        "concurrent"
        Perform the work concurrently in another thread. This is a hint
        to the query optimizer to help parallelize the lexicon work, allowing
        the calling query to continue performing other work while the lexicon
        processing occurs.  This is especially useful in cases where multiple
        lexicon calls occur in the same query (for example, resolving many
        facets in a single query).

**`$query`** *(optional)*
Only include values in fragments selected by the cts:query,
    and compute frequencies from this set of included values.
    The values do not need to match the query, but they must occur in
    fragments selected by the query.
    The fragments are not filtered to ensure they match the query,
    but instead selected in the same manner as
    
    "unfiltered" cts:search
    
    operations.  If a string
   is entered, the string is treated as a cts:word-query of the
   specified string.

**`$quality-weight`** *(optional)*
A document quality weight to use when computing scores.
    The default is 1.0.

**`$forest-ids`** *(optional)*
A sequence of IDs of forests to which the search will be constrained.
    An empty sequence means to search all forests in the database.
    The default is ().

### Returns

`element(cts:range)*`

### Usage Notes

Only one of "frequency-order" or "item-order" may be specified
  in the options parameter.  If neither "frequency-order" nor "item-order"
  is specified, then the default is "item-order".
      Only one of "fragment-frequency" or "item-frequency" may be specified
  in the options parameter.  If neither "fragment-frequency" nor
  "item-frequency" is specified, then the default is "fragment-frequency".
      Only one of "ascending" or "descending" may be specified
  in the options parameter.  If neither "ascending" nor "descending"
  is specified, then the default is "ascending" if "item-order" is
  specified, and "descending" if "frequency-order" is specified.
      Only one of "eager" or "lazy" may be specified
  in the options parameter.  If neither "eager" nor "lazy"
  is specified, then the default is "eager" if "frequency-order" or "empties"
  is specified, otherwise "lazy".
      Only one of "any", "document", "properties", or "locks"
  may be specified in the options parameter.
  If none of "any", "document", "properties", or "locks" are specified
  and there is a $query parameter, then the default is "document".
  If there is no $query parameter then the default is "any".
      Only one of the "score-logtfidf", "score-logtf", "score-simple",
  "score-random", or "score-zero" options may be specified in the options
  parameter.
  If none of "score-logtfidf", "score-logtf", "score-simple", "score-random",
  or "score-zero" are specified, then the default is "score-logtfidf".
      Only one of the "checked" or "unchecked" options may be specified
  in the options parameter.
  If neither "checked" nor "unchecked" are specified,
  then the default is "checked".
      If "collation=URI" is not specified in the options parameter,
  then the default collation is used. If a lexicon with that collation
  does not exist, an error is thrown.
      If "sample=N" is not specified in the options parameter,
  then ranges with all included values may be returned. If a
  $query parameter is not present, then "sample=N"
  has no effect.
      If "truncate=N" is not specified in the options parameter,
  then values from all fragments selected by the $query parameter
  are included.  If a $query parameter is not present, then
  "truncate=N" has no effect.
      To incrementally fetch a subset of the values returned by this function,
  use fn:subsequence
  
  on the output, rather than 
  the "skip" option. The "skip" option is based on fragments matching the 
  query parameter (if present), not on values. A fragment 
  matched by query might contain multiple values or no values. 
  The number of fragments skipped does not correspond to the number of 
  values. Also, the skip is applied to the relevance ordered query matches, 
  not to the ordered results list. 
      When using the "skip" option, use the "truncate" option rather than 
  the "limit" option to control the number of matching fragments from which 
  to draw values.

### Examples

```xquery
(: Run the following to load data for this example.
   Make sure you have a string path range index on
   path /name/fname. :)
xquery version "1.0-ml";

xdmp:document-insert("/aname1.xml",
 <name><fname>John</fname><mname>Rob</mname><lname>Goldings</lname></name>),
xdmp:document-insert("/aname2.xml",
 <name><fname>Jim</fname><mname>Ken</mname><lname>Kurla</lname></name>),
xdmp:document-insert("/aname3.xml",
 <name><fname>Ooi</fname><mname>Ben</mname><lname>Fu</lname></name>),
xdmp:document-insert("/aname4.xml",
 <name><fname>James</fname><mname>Rick</mname><lname>Tod</lname></name>),
xdmp:document-insert("/aname5.xml",
 <name><fname>Anthony</fname><mname>Rob</mname><lname>Flemings</lname>
 </name>),
xdmp:document-insert("/aname6.xml",
 <name><fname>Charles</fname><mname>Ken</mname><lname>Winter</lname></name>),
xdmp:document-insert("/aname7.xml",
 <name><fname>Nancy</fname><mname>Ben</mname><lname>Schmidt</lname></name>),
xdmp:document-insert("/aname8.xml",
 <name><fname>Robert</fname><mname>Rick</mname><lname>Hanson</lname></name>)

(: The following is based on the above setup :)

xquery version "1.0-ml";

cts:value-ranges(cts:path-reference("/name/fname"),("A","J","O"))
=>
<cts:range xmlns:cts="http://marklogic.com/cts"
  xmlns:xsi="http://www.w3.org/2001/XMLSchema-instance"
  xmlns:xs="http://www.w3.org/2001/XMLSchema">
  <cts:minimum xsi:type="xs:string">Anthony Flemings</cts:minimum>
  <cts:maximum xsi:type="xs:string">Charles Winter</cts:maximum>
  <cts:lower-bound xsi:type="xs:string">A</cts:lower-bound>
  <cts:upper-bound xsi:type="xs:string">J</cts:upper-bound>
</cts:range>
<cts:range xmlns:cts="http://marklogic.com/cts"
  xmlns:xsi="http://www.w3.org/2001/XMLSchema-instance"
  xmlns:xs="http://www.w3.org/2001/XMLSchema">
  <cts:minimum xsi:type="xs:string">James Tod</cts:minimum>
  <cts:maximum xsi:type="xs:string">Nancy Schmidt</cts:maximum>
  <cts:lower-bound xsi:type="xs:string">J</cts:lower-bound>
  <cts:upper-bound xsi:type="xs:string">O</cts:upper-bound>
</cts:range>
<cts:range xmlns:cts="http://marklogic.com/cts"
  xmlns:xsi="http://www.w3.org/2001/XMLSchema-instance"
  xmlns:xs="http://www.w3.org/2001/XMLSchema">
  <cts:minimum xsi:type="xs:string">Ooi Fu</cts:minimum>
  <cts:maximum xsi:type="xs:string">Robert Hanson</cts:maximum>
  <cts:lower-bound xsi:type="xs:string">O</cts:lower-bound>
</cts:range>
```

---

## cts:value-tuples

Returns value co-occurrence tuples (that is, tuples of values, each of
  which appear in the same fragment) from the specified value lexicons.  The
  values are returned as json:array values
  , where each slot contains
  one of the co-occurring values.  You can use
  cts:frequency on each item returned to find how many times
  the tuple occurs.
  Value lexicons are implemented using range indexes; consequently
  this function requires a range index for each lexicon specified
  in the function, and the range index must have range value positions
  set to true.  If there is not a range index configured for each
  of the specified elements, an exception is thrown.

### Signature

```xquery
cts:value-tuples(
  $range-indexes as cts:reference*,
  $options as xs:string*?,
  $query as cts:query??,
  $quality-weight as xs:double??,
  $forest-ids as xs:unsignedLong*?
) as json:array*
```

### Parameters

**`$range-indexes`**
A sequence of references to range indexes.

**`$options`** *(optional)*
Options.  The default is ().
    
      Options include:
      
        "ascending"
        Co-occurrences should be returned in ascending order.
        "descending"
        Co-occurrences should be returned in descending order.
        "any"
        Co-occurrences from any fragment should be included.
        "document"
        Co-occurrences from document fragments should be included.
        "properties"
        Co-occurrences from properties fragments should be included.
        "locks"
        Co-occurrences from locks fragments should be included.
        "frequency-order"
        Co-occurrences should be returned ordered by frequency.
        "item-order"
        Co-occurrences should be returned ordered by item.
        "fragment-frequency"
        Frequency should be the number of fragments with
        an included co-occurrences.
        This option is used with cts:frequency.
        "item-frequency"
        Frequency should be the number of occurrences of
        an included co-occurrence.
        This option is used with cts:frequency.
        "timezone=TZ"
        Return timezone sensitive values (dateTime, time, date,
        gYearMonth, gYear, gMonth, and gDay) adjusted to the timezone
        specified by TZ.
        Example timezones: Z, -08:00, +01:00.
        "ordered"
        Include co-occurrences only when the value from the first lexicon
        appears before the value from the second lexicon.
        Requires that word positions be enabled for both lexicons.
        "proximity=N"
        Include co-occurrences only when the values appear within
        N words of each other.
        Requires that word positions be enabled for both lexicons.
        "limit=N"
        Return no more than N tuples. You should not
        use this option with the "skip" option. Use "truncate" instead.
        "skip=N"
        Skip over fragments selected by the cts:query
        to treat the Nth fragment as the first fragment.
        Co-occurrences from skipped fragments are not included.
        This option affects the number of fragments selected
        by the cts:query to calculate frequencies.
        Only applies when a $query parameter is specified.
        "sample=N"
        Return only co-occurrences from the first N
        fragments after skip selected by the cts:query.
        This option does not affect the number of fragments selected
        by the cts:query to calculate frequencies.
        Only applies when a $query parameter is specified.
        "truncate=N"
        Include only co-occurrences from the first N
        fragments after skip selected by the cts:query.
        This option also affects the number of fragments selected
        by the cts:query to calculate frequencies.
        Only applies when a $query parameter is specified.
        "score-logtfidf"
        Compute scores using the logtfidf method.
        Only applies when a $query parameter is specified.
        "score-logtf"
        Compute scores using the logtf method.
        Only applies when a $query parameter is specified.
        "score-simple"
        Compute scores using the simple method.
        Only applies when a $query parameter is specified.
        "score-random"
        Compute scores using the random method.
        Only applies when a $query parameter is specified.
        "score-zero"
        Compute all scores as zero.
        Only applies when a $query parameter is specified.
        "checked"
        Word positions should be checked when resolving the query.
        "unchecked"
        Word positions should not be checked when resolving the query.
        "too-many-positions-error"
        If too much memory is needed to perform positions calculations
        to check whether a document matches a query,
        return an XDMP-TOOMANYPOSITIONS error,
        instead of accepting the document as a match.
        "eager"
        Perform most of the work concurrently before returning
        the first item from the indexes, and only some of the work
        sequentially while iterating through the rest of the items.
        This usually takes the shortest time for a complete item-order
        result or for any frequency-order result.
        "lazy"
        Perform only some the work concurrently before returning
        the first item from the indexes, and most of the work
        sequentially while iterating through the rest of the items.
        This usually takes the shortest time for a small item-order
        partial result.
        "concurrent"
        Perform the work concurrently in another thread. This is a hint
        to the query optimizer to help parallelize the lexicon work, allowing
        the calling query to continue performing other work while the lexicon
        processing occurs.  This is especially useful in cases where multiple
        lexicon calls occur in the same query (for example, resolving many
        facets in a single query).

**`$query`** *(optional)*
Only include co-occurrences in fragments selected by the cts:query,
    and compute frequencies from this set of included co-occurrences.
    The co-occurrences do not need to match the query, but they must occur in
    fragments selected by the query.
    The fragments are not filtered to ensure they match the query,
    but instead selected in the same manner as
    
    "unfiltered" cts:search
    
    operations.  If a string
   is entered, the string is treated as a cts:word-query of the
   specified string.

**`$quality-weight`** *(optional)*
A document quality weight to use when computing scores.
    The default is 1.0.

**`$forest-ids`** *(optional)*
A sequence of IDs of forests to which the search will be constrained.
    An empty sequence means to search all forests in the database.
    The default is ().

### Returns

`json:array*`

### Usage Notes

Only one of "frequency-order" or "item-order" may be specified
  in the options parameter.  If neither "frequency-order" nor "item-order"
  is specified, then the default is "item-order".
      Only one of "fragment-frequency" or "item-frequency" may be specified
  in the options parameter.  If neither "fragment-frequency" nor
  "item-frequency" is specified, then the default is "fragment-frequency".
      Only one of "ascending" or "descending" may be specified
  in the options parameter.  If neither "ascending" nor "descending"
  is specified, then the default is "ascending" if "item-order" is
  specified, and "descending" if "frequency-order" is specified.
      Only one of "eager" or "lazy" may be specified
  in the options parameter.  If neither "eager" nor "lazy"
  is specified, then the default is "lazy" if "item-order" is
  specified, and "eager" if "frequency-order" is specified.
      Only one of "any", "document", "properties", or "locks"
  may be specified in the options parameter.
  If none of "any", "document", "properties", or "locks" are specified
  and there is a $query parameter, then the default is "document".
  If there is no $query parameter then the default is "any".
      Only one of the "score-logtfidf", "score-logtf", "score-simple",
  "score-random", or "score-zero" options may be specified in the options
  parameter.
  If none of "score-logtfidf", "score-logtf", "score-simple", "score-random",
  or "score-zero" are specified, then the default is "score-logtfidf".
      Only one of the "checked" or "unchecked" options may be specified
  in the options parameter.
  If neither "checked" nor "unchecked" are specified,
  then the default is "checked".
      If "sample=N" is not specified in the options parameter,
  then all included co-occurrences may be returned.
  If a $query parameter
  is not present, then "sample=N" has no effect.
      If "truncate=N" is not specified in the options parameter,
  then co-occurrences from all fragments selected by the
  $query parameter are included.
  If a $query parameter is not present, then
  "truncate=N" has no effect.
      To incrementally fetch a subset of the tuples returned by this function,
  use fn:subsequence
  
  on the output, rather than 
  the "skip" option. The "skip" option is based on fragments matching the 
  query parameter (if present), not on values. A fragment 
  matched by query might contain multiple occurrences or no occurrences. 
  The number of fragments skipped does not correspond to the number of 
  tuples. Also, the skip is applied to the relevance ordered query matches, 
  not to the ordered tuples list. 
      When using the "skip" option, use the "truncate" option rather than 
  the "limit" option to control the number of matching fragments from which 
  to draw values.

### Examples

```xquery
cts:value-tuples(
  (cts:uri-reference(),
   cts:element-reference(xs:QName("hello")))
   )
(:
  Returns zero or more json:arrays listing co-occurrences between
  URIs with values from the lexicon for the element "hello".
  Requires a URI lexicon and an element range index on "hello".
:)
```

---

## cts:values

Returns values from the specified value lexicon(s).
  Value lexicons are implemented using range indexes; consequently this
  function requires a range index for each of the $range-indexes specified
  in the function.  If there is not a range index configured for each
  of the specified range indexes, an exception is thrown.

### Signature

```xquery
cts:values(
  $range-indexes as cts:reference*,
  $start as xs:anyAtomicType??,
  $options as xs:string*?,
  $query as cts:query??,
  $quality-weight as xs:double??,
  $forest-ids as xs:unsignedLong*?
) as xs:anyAtomicType*
```

### Parameters

**`$range-indexes`**
A sequence of references to range indexes.

**`$start`** *(optional)*
A starting value.  The parameter type must match the lexicon type.
    If the parameter value is not in the lexicon, then the values are
    returned beginning with the next value.

**`$options`** *(optional)*
Options.  The default is ().
    
      Options include:
      
        "ascending"
        Values should be returned in ascending order.
        "descending"
        Values should be returned in descending order.
        "any"
        Values from any fragment should be included.
        "document"
        Values from document fragments should be included.
        "properties"
        Values from properties fragments should be included.
        "locks"
        Values from locks fragments should be included.
        "frequency-order"
        Values should be returned ordered by frequency.
        "item-order"
        Values should be returned ordered by item.
        "fragment-frequency"
        Frequency should be the number of fragments with
        an included value.
        This option is used with cts:frequency.
        "item-frequency"
        Frequency should be the number of occurrences of
        an included value.
        This option is used with cts:frequency.
        "timezone=TZ"
        Return timezone sensitive values (dateTime, time, date,
        gYearMonth, gYear, gMonth, and gDay) adjusted to the timezone
        specified by TZ.
        Example timezones: Z, -08:00, +01:00.
        "limit=N"
        Return no more than N values. You should not
        use this option with the "skip" option. Use "truncate" instead.
        "skip=N"
        Skip over fragments selected by the cts:query
        to treat the Nth fragment as the first fragment.
        Values from skipped fragments are not included.
        This option affects the number of fragments selected
        by the cts:query to calculate frequencies.
        Only applies when a $query parameter is specified.
        "sample=N"
        Return only values from the first N
        fragments after skip selected by the cts:query.
        This option does not affect the number of fragments selected
        by the cts:query to calculate frequencies.
        Only applies when a $query parameter is specified.
        "truncate=N"
        Include only values from the first N fragments
        after skip selected by the cts:query.
        This option also affects the number of fragments selected
        by the cts:query to calculate frequencies.
        Only applies when a $query parameter is specified.
        "score-logtfidf"
        Compute scores using the logtfidf method.
        Only applies when a $query parameter is specified.
        "score-logtf"
        Compute scores using the logtf method.
        Only applies when a $query parameter is specified.
        "score-simple"
        Compute scores using the simple method.
        Only applies when a $query parameter is specified.
        "score-random"
        Compute scores using the random method.
        Only applies when a $query parameter is specified.
        "score-zero"
        Compute all scores as zero.
        Only applies when a $query parameter is specified.
        "checked"
        Word positions should be checked when resolving the query.
        "unchecked"
        Word positions should not be checked when resolving the query.
        "too-many-positions-error"
        If too much memory is needed to perform positions calculations
        to check whether a document matches a query,
        return an XDMP-TOOMANYPOSITIONS error,
        instead of accepting the document as a match.
        "eager"
        Perform most of the work concurrently before returning
        the first item from the indexes, and only some of the work
        sequentially while iterating through the rest of the items.
        This usually takes the shortest time for a complete item-order
        result or for any frequency-order result.
        "lazy"
        Perform only some the work concurrently before returning
        the first item from the indexes, and most of the work
        sequentially while iterating through the rest of the items.
        This usually takes the shortest time for a small item-order
        partial result.
        "concurrent"
        Perform the work concurrently in another thread. This is a hint
        to the query optimizer to help parallelize the lexicon work, allowing
        the calling query to continue performing other work while the lexicon
        processing occurs.  This is especially useful in cases where multiple
        lexicon calls occur in the same query (for example, resolving many
        facets in a single query).
        "map"
        Return results as a single map:map
         value instead of as an xs:anyAtomicType* sequence
         .

**`$query`** *(optional)*
Only include values in fragments selected by the cts:query,
    and compute frequencies from this set of included values.
    The values do not need to match the query, but they must occur in
    fragments selected by the query.
    The fragments are not filtered to ensure they match the query,
    but instead selected in the same manner as
    
    "unfiltered" cts:search
    
    operations.  If a string
   is entered, the string is treated as a cts:word-query of the
   specified string.

**`$quality-weight`** *(optional)*
A document quality weight to use when computing scores.
    The default is 1.0.

**`$forest-ids`** *(optional)*
A sequence of IDs of forests to which the search will be constrained.
    An empty sequence means to search all forests in the database.
    The default is ().

### Returns

`xs:anyAtomicType*`

### Usage Notes

Only one of "frequency-order" or "item-order" may be specified
  in the options parameter.  If neither "frequency-order" nor "item-order"
  is specified, then the default is "item-order".
      Only one of "fragment-frequency" or "item-frequency" may be specified
  in the options parameter.  If neither "fragment-frequency" nor
  "item-frequency" is specified, then the default is "fragment-frequency".
      Only one of "ascending" or "descending" may be specified
  in the options parameter.  If neither "ascending" nor "descending"
  is specified, then the default is "ascending" if "item-order" is
  specified, and "descending" if "frequency-order" is specified.
      Only one of "any", "document", "properties", or "locks"
  may be specified in the options parameter.
  If none of "any", "document", "properties", or "locks" are specified
  and there is a $query parameter, then the default is "document".
  If there is no $query parameter then the default is "any".
      Only one of the "score-logtfidf", "score-logtf", "score-simple",
  "score-random", or "score-zero" options may be specified in the options
  parameter.
  If none of "score-logtfidf", "score-logtf", "score-simple", "score-random",
  or "score-zero" are specified, then the default is "score-logtfidf".
      Only one of the "checked" or "unchecked" options may be specified
  in the options parameter.
  If neither "checked" nor "unchecked" are specified,
  then the default is "checked".
      If "collation=URI" is not specified in the options parameter,
  then the default collation is used. If a lexicon with that collation
  does not exist, an error is thrown.
      If "sample=N" is not specified in the options parameter,
  then all included values may be returned. If a $query parameter
  is not present, then "sample=N" has no effect.
      If "truncate=N" is not specified in the options parameter,
  then values from all fragments selected by the $query parameter
  are included.  If a $query parameter is not present, then
  "truncate=N" has no effect.
      To incrementally fetch a subset of the values returned by this function,
  use fn:subsequence
  
  on the output, rather than 
  the "skip" option. The "skip" option is based on fragments matching the 
  query parameter (if present), not on values. A fragment 
  matched by query might contain multiple values or no values. 
  The number of fragments skipped does not correspond to the number of 
  values. Also, the skip is applied to the relevance ordered query matches, 
  not to the ordered values list. 
      When using the "skip" option, use the "truncate" option rather than 
  the "limit" option to control the number of matching fragments from which 
  to draw values.

### Examples

```xquery
(:
  Assuming that there are path namespaces defined with the following prefixes:
  my: http://aaa.com
  his: http://bbb.com

  Further assuming that a path index is defined using the above namespaces,
  '/my:a[@his:b="B1"]/my:c'.
:)
  xquery version "1.0-ml";

  declare namespace my = "http://aaa.com";
  declare namespace his = "http://bbb.com";

  xdmp:document-insert("/abc1.xml",<my:a his:b="B1"><my:c>C1</my:c></my:a>),
  xdmp:document-insert("/abc2.xml",<my:a his:b="B2"><my:c>C2</my:c></my:a>)

  (: The following is based on the above setup :)
  xquery version "1.0-ml";

  declare namespace my = "http://aaa.com";
  declare namespace his = "http://bbb.com";

  cts:values(cts:path-reference('/my:a[@his:b="B1"]/my:c'))
  =>
    C1
```

---

## cts:word-match

Returns words from the word lexicon that match the wildcard pattern.
  This function requires the word lexicon to be enabled. If the word
  lexicon is not enabled, an exception is thrown.

### Signature

```xquery
cts:word-match(
  $pattern as xs:string,
  $options as xs:string*?,
  $query as cts:query??,
  $quality-weight as xs:double??,
  $forest-ids as xs:unsignedLong*?
) as xs:string*
```

### Parameters

**`$pattern`**
A wildcard pattern to match.

**`$options`** *(optional)*
Options.  The default is ().
    
      Options include:
      
        "case-sensitive"
        A case-sensitive match.
        "case-insensitive"
        A case-insensitive match.
        "diacritic-sensitive"
        A diacritic-sensitive match.
        "diacritic-insensitive"
        A diacritic-insensitive match.
        "ascending"
        Words should be returned in ascending order.
        "descending"
        Words should be returned in descending order.
        "any"
        Words from any fragment should be included.
        "document"
        Words from document fragments should be included.
        "properties"
        Words from properties fragments should be included.
        "locks"
        Words from locks fragments should be included.
        "collation=URI"
        Use the lexicon with the collation specified by URI.
        "limit=N"
        Return no more than N words. You should not
        use this option with the "skip" option. Use "truncate" instead.
        "skip=N"
        Skip over fragments selected by the cts:query
        to treat the Nth fragment as the first fragment.
        Words from skipped fragments are not included.
        Only applies when a $query parameter is specified.
        "sample=N"
        Return only words from the first N fragments after skip
        selected by the cts:query.
        Only applies when a $query parameter is specified.
        "truncate=N"
        Include only words from the first N fragments after skip
        selected by the cts:query.
        Only applies when a $query parameter is specified.
        "score-logtfidf"
        Compute scores using the logtfidf method.
        Only applies when a $query parameter is specified.
        "score-logtf"
        Compute scores using the logtf method.
        Only applies when a $query parameter is specified.
        "score-simple"
        Compute scores using the simple method.
        Only applies when a $query parameter is specified.
        "score-random"
        Compute scores using the random method.
        Only applies when a $query parameter is specified.
        "score-zero"
        Compute all scores as zero.
        Only applies when a $query parameter is specified.
        "checked"
        Word positions should be checked when resolving the query.
        "unchecked"
        Word positions should not be checked when resolving the query.
        "too-many-positions-error"
        If too much memory is needed to perform positions calculations
        to check whether a document matches a query,
        return an XDMP-TOOMANYPOSITIONS error,
        instead of accepting the document as a match.
        "concurrent"
        Perform the work concurrently in another thread. This is a hint
        to the query optimizer to help parallelize the lexicon work, allowing
        the calling query to continue performing other work while the lexicon
        processing occurs.  This is especially useful in cases where multiple
        lexicon calls occur in the same query (for example, resolving many
        facets in a single query).
        "map"
        Return results as a single map:map
         value instead of as an xs:string* sequence
         .

**`$query`** *(optional)*
Only include words in fragments selected by the cts:query.
    The words do not need to match the query, but the words must occur
    in fragments selected by the query.
    The fragments are not filtered to ensure they match the query,
    but instead selected in the same manner as
    
    "unfiltered" cts:search
    
    operations.  If a string
   is entered, the string is treated as a cts:word-query of the
   specified string.

**`$quality-weight`** *(optional)*
A document quality weight to use when computing scores.
    The default is 1.0.

**`$forest-ids`** *(optional)*
A sequence of IDs of forests to which the search will be constrained.
    An empty sequence means to search all forests in the database.
    The default is ().

### Returns

`xs:string*`

### Usage Notes

Only one of "ascending" or "descending" may be specified
  in the options parameter.  If neither "ascending" nor "descending"
  is specified, then the default is "ascending".
      Only one of "any", "document", "properties", or "locks"
  may be specified in the options parameter.
  If none of "any", "document", "properties", or "locks" are specified
  and there is a $query parameter, then the default is "document".
  If there is no $query parameter then the default is "any".
      Only one of the "score-logtfidf", "score-logtf", "score-simple",
  "score-random", or "score-zero" options may be specified in the options
  parameter.
  If none of "score-logtfidf", "score-logtf", "score-simple", "score-random",
  or "score-zero" are specified, then the default is "score-logtfidf".
      Only one of the "checked" or "unchecked" options may be specified
  in the options parameter.
  If neither "checked" nor "unchecked" are specified,
  then the default is "checked".
      If "collation=URI" is not specified in the options parameter,
  then the default collation is used. If a lexicon with that collation
  does not exist, an error is thrown.
      If "sample=N" is not specified in the options parameter,
  then all included words may be returned. If a $query parameter
  is not present, then "sample=N" has no effect.
      If "truncate=N" is not specified in the options parameter,
  then words from all fragments selected by the $query parameter
  are included.  If a $query parameter is not present, then
  "truncate=N" has no effect.
      To incrementally fetch a subset of the values returned by this function,
  use fn:subsequence
  
  on the output, rather than 
  the "skip" option. The "skip" option is based on fragments matching the 
  query parameter (if present), not on values. A fragment 
  matched by query might contain multiple values or no values. 
  The number of fragments skipped does not correspond to the number of 
  values. Also, the skip is applied to the relevance ordered query matches, 
  not to the ordered values list. 
      When using the "skip" option, use the "truncate" option rather than 
  the "limit" option to control the number of matching fragments from which 
  to draw values.
      
    If neither "case-sensitive" nor "case-insensitive"
    is present, $pattern is used to determine case sensitivity.
    If $pattern contains no uppercase, it specifies "case-insensitive".
    If $pattern contains uppercase, it specifies "case-sensitive".
  
      
    If neither "diacritic-sensitive" nor "diacritic-insensitive"
    is present, $pattern is used to determine diacritic sensitivity.
    If $pattern contains no diacritics, it specifies "diacritic-insensitive".
    If $pattern contains diacritics, it specifies "diacritic-sensitive".

### Examples

```xquery
(:
   a word lexicon must exist in the query's collation
   otherwise this will throw XDMP-WORDLXCNNOTFOUND
:)
  cts:word-match("aardvark*")
  => ("aardvark","aardvarks")
```

---

## cts:words

Returns words from the word lexicon.  This function requires the word
  lexicon to be enabled. If the word lexicon is not enabled, an
  exception is thrown.  The words are returned in collation order.

### Signature

```xquery
cts:words(
  $start as xs:string??,
  $options as xs:string*?,
  $query as cts:query??,
  $quality-weight as xs:double??,
  $forest-ids as xs:unsignedLong*?
) as xs:string*
```

### Parameters

**`$start`** *(optional)*
A starting word.  Returns only this word and any following words
    from the lexicon.  If the parameter is not in the lexicon, then it
    returns the words beginning with the next word.

**`$options`** *(optional)*
Options.  The default is ().
    
      Options include:
      
        "ascending"
        Words should be returned in ascending order.
        "descending"
        Words should be returned in descending order.
        "any"
        Words from any fragment should be included.
        "document"
        Words from document fragments should be included.
        "properties"
        Words from properties fragments should be included.
        "locks"
        Words from locks fragments should be included.
        "collation=URI"
        Use the lexicon with the collation specified by URI.
        "limit=N"
        Return no more than N words. You should not
        use this option with the "skip" option. Use "truncate" instead.
        "skip=N"
        Skip over fragments selected by the cts:query
        to treat the Nth fragment as the first fragment.
        Words from skipped fragments are not included.
        Only applies when a $query parameter is specified.
        "sample=N"
        Return only words from the first N fragments after skip
        selected by the cts:query.
        Only applies when a $query parameter is specified.
        "truncate=N"
        Include only words from the first N fragments after skip
        selected by the cts:query.
        Only applies when a $query parameter is specified.
        "score-logtfidf"
        Compute scores using the logtfidf method.
        Only applies when a $query parameter is specified.
        "score-logtf"
        Compute scores using the logtf method.
        Only applies when a $query parameter is specified.
        "score-simple"
        Compute scores using the simple method.
        Only applies when a $query parameter is specified.
        "score-random"
        Compute scores using the random method.
        Only applies when a $query parameter is specified.
        "score-zero"
        Compute all scores as zero.
        Only applies when a $query parameter is specified.
        "checked"
        Word positions should be checked when resolving the query.
        "unchecked"
        Word positions should not be checked when resolving the query.
        "too-many-positions-error"
        If too much memory is needed to perform positions calculations
        to check whether a document matches a query,
        return an XDMP-TOOMANYPOSITIONS error,
        instead of accepting the document as a match.
        "concurrent"
        Perform the work concurrently in another thread. This is a hint
        to the query optimizer to help parallelize the lexicon work, allowing
        the calling query to continue performing other work while the lexicon
        processing occurs.  This is especially useful in cases where multiple
        lexicon calls occur in the same query (for example, resolving many
        facets in a single query).
        "map"
        Return results as a single map:map
         value instead of as an xs:string* sequence
         .

**`$query`** *(optional)*
Only include words in fragments selected by the cts:query.
    The words do not need to match the query, but the words must occur
    in fragments selected by the query.
    The fragments are not filtered to ensure they match the query,
    but instead selected in the same manner as 
    "unfiltered" cts:search operations.  If a string
   is entered, the string is treated as a cts:word-query of the
   specified string.

**`$quality-weight`** *(optional)*
A document quality weight to use when computing scores.
    The default is 1.0.

**`$forest-ids`** *(optional)*
A sequence of IDs of forests to which the search will be constrained.
    An empty sequence means to search all forests in the database.
    The default is ().

### Returns

`xs:string*`

### Usage Notes

Only one of "ascending" or "descending" may be specified
  in the options parameter.  If neither "ascending" nor "descending"
  is specified, then the default is "ascending".
      Only one of "any", "document", "properties", or "locks"
  may be specified in the options parameter.
  If none of "any", "document", "properties", or "locks" are specified
  and there is a $query parameter, then the default is "document".
  If there is no $query parameter then the default is "any".
      Only one of the "score-logtfidf", "score-logtf", "score-simple",
  "score-random", or "score-zero" options may be specified in the options
  parameter.
  If none of "score-logtfidf", "score-logtf", "score-simple", "score-random",
  or "score-zero" are specified, then the default is "score-logtfidf".
      Only one of the "checked" or "unchecked" options may be specified
  in the options parameter.
  If neither "checked" nor "unchecked" are specified,
  then the default is "checked".
      If "collation=URI" is not specified in the options parameter,
  then the default collation is used. If a lexicon with that collation
  does not exist, an error is thrown.
      If "sample=N" is not specified in the options parameter,
  then all included words may be returned. If a $query parameter
  is not present, then "sample=N" has no effect.
      If "truncate=N" is not specified in the options parameter,
  then words from all fragments selected by the $query parameter
  are included.  If a $query parameter is not present, then
  "truncate=N" has no effect.
      To incrementally fetch a subset of the values returned by this function,
  use fn:subsequence
  
  on the output, rather than 
  the "skip" option. The "skip" option is based on fragments matching the 
  query parameter (if present), not on values. A fragment 
  matched by query might contain multiple values or no values. 
  The number of fragments skipped does not correspond to the number of 
  values. Also, the skip is applied to the relevance ordered query matches, 
  not to the ordered values list. 
      When using the "skip" option, use the "truncate" option rather than 
  the "limit" option to control the number of matching fragments from which 
  to draw values.

### Examples

```xquery
(:
   a word lexicon must exist in the query's collation
   otherwise this will throw XDMP-WORDLXCNNOTFOUND
:)
  cts:words("aardvark")
  => ("aardvark","aardvarks","aardwolf",...)
```

---
