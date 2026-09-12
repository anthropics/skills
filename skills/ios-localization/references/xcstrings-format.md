# Localizable.xcstrings Format Reference

## File Structure

The `.xcstrings` file is a JSON-based localization format introduced in Xcode 15.

```json
{
  "sourceLanguage": "en",
  "strings": {
    "Hello": {
      "localizations": {
        "fr": {
          "stringUnit": {
            "state": "translated",
            "value": "Bonjour"
          }
        }
      }
    }
  },
  "version": "1.0"
}
```

## Key Properties

### String Entry Structure

```json
"String Key": {
  "comment": "Optional developer comment",
  "extractionState": "manual|extracted_with_value|stale",
  "shouldTranslate": true|false,
  "localizations": {
    "<lang_code>": {
      "stringUnit": {
        "state": "translated|needs_review|new",
        "value": "Translated text"
      }
    }
  }
}
```

### Translation States

| State | Description |
|-------|-------------|
| `translated` | Translation is complete and verified |
| `needs_review` | Translation exists but needs review |
| `new` | New string, not yet translated |

### shouldTranslate Flag

Set `shouldTranslate: false` for strings that should not be translated:
- Technical identifiers (aspect ratios: "16:9", "4:3")
- Universal symbols ("OK", "PDF", "USB")
- Brand names ("iPhone", "Kodak")
- Format specifiers used alone ("%lld", "%@")

## Common Language Codes

| Code | Language | Code | Language |
|------|----------|------|----------|
| ar | Arabic | ko | Korean |
| ca | Catalan | ms | Malay |
| zh-Hans | Chinese (Simplified) | nl | Dutch |
| zh-Hant | Chinese (Traditional) | pl | Polish |
| cs | Czech | pt-BR | Portuguese (Brazil) |
| da | Danish | pt-PT | Portuguese (Portugal) |
| de | German | ro | Romanian |
| el | Greek | ru | Russian |
| es | Spanish | sk | Slovak |
| fi | Finnish | sv | Swedish |
| fr | French | th | Thai |
| he | Hebrew | tr | Turkish |
| hi | Hindi | uk | Ukrainian |
| hr | Croatian | vi | Vietnamese |
| hu | Hungarian | | |
| id | Indonesian | | |
| it | Italian | | |
| ja | Japanese | | |

## Format Specifiers

Preserve these exactly in translations:

| Specifier | Type | Example |
|-----------|------|---------|
| `%@` | String/Object | "Hello %@" |
| `%d`, `%i` | Integer | "%d items" |
| `%lld` | Long integer | "%lld photos" |
| `%f` | Float | "%.2f MB" |
| `%%` | Literal % | "100%%" |

### Positional Arguments

For reordering in translations:
```
English: "Move %1$@ to %2$@"
German: "Verschiebe %1$@ nach %2$@"
Japanese: "%2$@に%1$@を移動"
```

## Pluralization

For plural forms, use `stringUnit` with `variations`:

```json
"%lld items": {
  "localizations": {
    "en": {
      "variations": {
        "plural": {
          "one": {
            "stringUnit": {
              "state": "translated",
              "value": "%lld item"
            }
          },
          "other": {
            "stringUnit": {
              "state": "translated",
              "value": "%lld items"
            }
          }
        }
      }
    }
  }
}
```

### Plural Categories by Language

| Category | Languages |
|----------|-----------|
| one, other | English, German, Italian, Spanish, Portuguese |
| one, few, many, other | Russian, Polish, Ukrainian |
| one, two, few, many, other | Arabic |
| other only | Chinese, Japanese, Korean, Vietnamese, Thai |

## Device Variations

For device-specific strings:

```json
"Welcome": {
  "localizations": {
    "en": {
      "variations": {
        "device": {
          "iphone": {
            "stringUnit": {
              "state": "translated",
              "value": "Welcome to iPhone"
            }
          },
          "ipad": {
            "stringUnit": {
              "state": "translated",
              "value": "Welcome to iPad"
            }
          }
        }
      }
    }
  }
}
```

## Best Practices

### String Keys

- Use English text as the key (acts as fallback)
- Keep keys consistent and descriptive
- Avoid special characters in keys when possible

### Comments

Add comments for context:
```json
"Save": {
  "comment": "Button title for saving document",
  "localizations": { ... }
}
```

### Grouping

The xcstrings format doesn't support groups, but use consistent naming:
```
"settings.title"
"settings.privacy"
"editor.brush"
"editor.eraser"
```

## Validation

Check for common issues:
1. Missing translations for target languages
2. Mismatched format specifiers
3. Empty translation values
4. Inconsistent plural forms
