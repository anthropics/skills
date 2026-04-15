# Schema Type Mapping (Step 5b)

If the project has a schema validation layer, you need to understand what each field accepts before writing boundary tests. Common validation layers by language: Pydantic models (Python), JSON Schema (any), TypeScript interfaces/Zod schemas (TypeScript), Bean Validation annotations (Java), case class codecs/Circe decoders (Scala), serde attributes (Rust). Without this mapping, you'll write mutations that the schema rejects before they reach the code you're trying to test — producing validation errors instead of meaningful boundary tests.

## Why This Matters

Consider this common mistake:

```typescript
// TypeScript — WRONG: tests the validation mechanism, not the requirement
test('bad value rejected', () => {
    fixture.field = 'invalid';  // Zod schema rejects this before processing!
    expect(() => process(fixture)).toThrow(ZodError);
    // Tells you nothing about the output
});

// TypeScript — RIGHT: tests the requirement using a schema-valid mutation
test('bad value not in output', () => {
    fixture.field = undefined;  // Schema accepts undefined for optional fields
    const output = process(fixture);
    expect(output).not.toContain(badProperty);  // Bad data absent
    expect(output).toContain(expectedType);      // Rest still works
});
```

```python
# Python — WRONG: tests the validation mechanism, not the requirement
def test_bad_value_rejected(fixture):
    fixture.field = "invalid"  # Pydantic rejects this before processing!
    with pytest.raises(ValidationError):
        process(fixture)
    # Tells you nothing about the output

# Python — RIGHT: tests the requirement using a schema-valid mutation
def test_bad_value_not_in_output(fixture):
    fixture.field = None  # Schema accepts None for Optional fields
    output = process(fixture)
    assert field_property not in output  # Bad data absent
    assert expected_type in output  # Rest still works
```

```java
// Java — WRONG: tests Bean Validation, not the requirement
@Test
void testBadValueRejected() {
    fixture.setField("invalid");  // @NotNull/@Pattern rejects this!
    assertThrows(ConstraintViolationException.class, () -> process(fixture));
}

// Java — RIGHT: tests the requirement using a schema-valid mutation
@Test
void testBadValueNotInOutput() {
    fixture.setField(null);  // nullable String field accepts null
    var output = process(fixture);
    assertFalse(output.contains(badProperty));
    assertTrue(output.contains(expectedType));
}
```

```scala
// Scala — WRONG: tests the decoder, not the requirement
"bad value" should "be rejected" in {
    val input = fixture.copy(field = "invalid")  // Circe decoder fails!
    a [DecodingFailure] should be thrownBy process(input)
}

// Scala — RIGHT: tests the requirement using a schema-valid mutation
"missing optional field" should "not produce bad output" in {
    val input = fixture.copy(field = None)  // Option[String] accepts None
    val output = process(input)
    output should not contain badProperty
}
```

```go
// Go — WRONG: tests validation, not the requirement
func TestBadValueRejected(t *testing.T) {
    fixture.Field = "invalid"  // Struct tag validator rejects this!
    _, err := Process(fixture)
    if err == nil { t.Fatal("expected validation error") }
    // Tells you nothing about the output
}

// Go — RIGHT: tests the requirement using a valid zero value
func TestBadValueNotInOutput(t *testing.T) {
    fixture.Field = ""  // Zero value is valid for optional string fields
    output, err := Process(fixture)
    if err != nil { t.Fatalf("unexpected error: %v", err) }
    // Assert bad data absent, rest still works
}
```

```rust
// Rust — WRONG: tests serde deserialization, not the requirement
#[test]
fn test_bad_value_rejected() {
    let input = Fixture { field: "invalid".into(), ..default() };
    // serde rejects before processing!
    assert!(process(&input).is_err());
}

// Rust — RIGHT: tests the requirement using a schema-valid mutation
#[test]
fn test_bad_value_not_in_output() {
    let input = Fixture { field: None, ..default() };  // Option<String> accepts None
    let output = process(&input).expect("should succeed");
    assert!(!output.contains(bad_property));
    assert!(output.contains(expected_type));
}
```

The WRONG tests fail with a validation/decoding error because the mutation value isn't schema-valid. The RIGHT tests use values the schema accepts (null, None, nil, zero values, empty Option) so the mutation reaches the actual processing logic.

## How to Build the Map

For every field you found a defensive pattern for in Step 5, record:

| Field | Schema Type | Accepts | Rejects |
|-------|-----------|---------|---------|
| `metadata` | optional object (`Optional[MetadataObject]` / `MetadataObject?` / `MetadataObject \| null`) | valid object, `null`/`undefined` | `string`, `number`, `array` |
| `count_field` | optional integer (`Optional[int]` / `number?` / `Integer`) | integer, `null` | `string`, `object` |
| `child_list` | array of objects (`List[Child]` / `Child[]` / `Seq[Child]`) | array of objects, `[]` | `[null, "invalid"]`, `null` |
| `optional_object` | optional object | `{"key": value}`, `null` | `"bad"`, `[1,2]` |

## Rules for Choosing Mutation Values

When writing boundary tests, always use values from the "Accepts" column. The idiomatic "missing/empty" value varies by language:

- **Optional/nullable fields:** Python `None`, Java `null`, Scala `None` (for `Option`), TypeScript `undefined`/`null`, Go zero value (`""`, `0`, `nil` for pointers), Rust `None` (for `Option<T>`)
- **Numeric fields:** `0`, negative values, or boundary values — language-agnostic
- **Arrays/lists:** Python `[]`, Java `List.of()`, Scala `Seq.empty`, TypeScript `[]`, Go `nil` or empty slice, Rust `Vec::new()`
- **Strings:** `""` (empty string) — language-agnostic
- **Objects/structs:** Python `{}`, Java `new Obj()` with missing fields, Scala `copy()` with `None`, TypeScript `{}`, Go zero-value struct, Rust `Default::default()` or builder with missing fields

Never use values from the "Rejects" column — they test the schema validator, not the business logic.

## When to Skip This Step

If the project has no schema validation layer (data flows directly into processing without type checking), you can skip the mapping and use any mutation values. But most modern projects have some form of validation, so check first.
