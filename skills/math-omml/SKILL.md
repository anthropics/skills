---
name: math-omml
description: "Use this skill whenever math formulas, equations, or mathematical expressions need to be inserted into Word (.docx) documents. Covers fractions, integrals, summations, matrices, square roots, subscripts, superscripts, Greek letters, and any LaTeX-style expression that must render natively in Microsoft Word. Triggers on: 'add equation to Word', 'math in docx', 'formula in Word document', 'insert integral/fraction/matrix into doc', 'OMML', 'Office Math Markup Language', or any request where a .docx output needs proper typeset mathematics. DO NOT use MathML, LaTeX strings, or Unicode workarounds — always use OMML XML injected directly into document.xml. This skill is the ONLY reliable approach for math in docx on this LibreOffice-based backend."
---

# Math Formulas in Word Documents (OMML)

## Why OMML (not LaTeX or MathML)

The backend runs **LibreOffice**, which cannot reliably render LaTeX strings or convert MathML to Word-native math. The only format Word opens natively on every platform is **OOXML Math Markup Language (OMML)**, serialized as `<m:oMath>` XML inside `word/document.xml`. This skill shows how to inject OMML directly.

---

## Core Approach: Unpack → Inject XML → Repack

All math work follows the Editing Existing Documents workflow from the docx skill:

```bash
# 1. Unpack
python scripts/office/unpack.py document.docx unpacked/

# 2. Edit unpacked/word/document.xml (add OMML, see below)

# 3. Repack
python scripts/office/pack.py unpacked/ output.docx --original document.docx
```

For **new documents**, use docx-js to scaffold the file, then unpack → inject OMML → repack.

---

## Namespace Declaration (REQUIRED)

The root `<w:document>` element in `document.xml` must declare the math namespace. Check if it's already present; if not, add it:

```xml
<w:document
  xmlns:wpc="http://schemas.microsoft.com/office/word/2010/wordprocessingCanvas"
  xmlns:m="http://schemas.openxmlformats.org/officeDocument/2006/math"
  xmlns:w="http://schemas.openxmlformats.org/wordprocessingml/2006/main"
  ...>
```

**Always verify** `xmlns:m=` exists before adding OMML. If missing, add it to the opening `<w:document ...>` tag.

---

## Anatomy of an OMML Block

Every formula lives in a `<m:oMathPara>` (block/display) or inline `<m:oMath>` inside a `<w:p>`:

```xml
<!-- DISPLAY (block) equation — centered on its own line -->
<w:p>
  <m:oMathPara>
    <m:oMathParaPr>
      <m:jc m:val="center"/>   <!-- center | left | right -->
    </m:oMathParaPr>
    <m:oMath>
      <!-- formula elements go here -->
    </m:oMath>
  </m:oMathPara>
</w:p>

<!-- INLINE equation — inside a regular paragraph -->
<w:p>
  <w:r><w:t xml:space="preserve">See formula </w:t></w:r>
  <m:oMath>
    <!-- formula elements -->
  </m:oMath>
  <w:r><w:t xml:space="preserve"> for details.</w:t></w:r>
</w:p>
```

---

## OMML Element Reference

### Plain text / variable

```xml
<m:r><m:t>x</m:t></m:r>
```

### Superscript (x²)

```xml
<m:sSup>
  <m:e><m:r><m:t>x</m:t></m:r></m:e>   <!-- base -->
  <m:sup><m:r><m:t>2</m:t></m:r></m:sup>
</m:sSup>
```

### Subscript (x₁)

```xml
<m:sSub>
  <m:e><m:r><m:t>x</m:t></m:r></m:e>
  <m:sub><m:r><m:t>1</m:t></m:r></m:sub>
</m:sSub>
```

### Sub+Superscript (xᵢⁿ)

```xml
<m:sSubSup>
  <m:e><m:r><m:t>x</m:t></m:r></m:e>
  <m:sub><m:r><m:t>i</m:t></m:r></m:sub>
  <m:sup><m:r><m:t>n</m:t></m:r></m:sup>
</m:sSubSup>
```

### Fraction (a/b)

```xml
<m:f>
  <m:num><m:r><m:t>a</m:t></m:r></m:num>
  <m:den><m:r><m:t>b</m:t></m:r></m:den>
</m:f>
```

### Square Root (√x)

```xml
<m:rad>
  <m:radPr><m:degHide m:val="1"/></m:radPr>   <!-- hide degree for √ -->
  <m:deg/>
  <m:e><m:r><m:t>x</m:t></m:r></m:e>
</m:rad>
```

### nth Root (ⁿ√x)

```xml
<m:rad>
  <m:deg><m:r><m:t>n</m:t></m:r></m:deg>
  <m:e><m:r><m:t>x</m:t></m:r></m:e>
</m:rad>
```

### Summation (Σ)

```xml
<m:nary>
  <m:naryPr>
    <m:chr m:val="∑"/>
    <m:limLoc m:val="undOvr"/>   <!-- limits above/below -->
  </m:naryPr>
  <m:sub><m:r><m:t>i=1</m:t></m:r></m:sub>
  <m:sup><m:r><m:t>n</m:t></m:r></m:sup>
  <m:e><m:r><m:t>i</m:t></m:r></m:e>  <!-- body of sum -->
</m:nary>
```

### Integral (∫)

```xml
<m:nary>
  <m:naryPr>
    <m:chr m:val="∫"/>
    <m:limLoc m:val="subSup"/>   <!-- limits as sub/sup (inline style) -->
  </m:naryPr>
  <m:sub><m:r><m:t>0</m:t></m:r></m:sub>
  <m:sup><m:r><m:t>&#x221E;</m:t></m:r></m:sup>  <!-- ∞ -->
  <m:e>
    <m:r><m:t>f(x)</m:t></m:r>
    <m:r><m:t xml:space="preserve"> dx</m:t></m:r>
  </m:e>
</m:nary>
```

### Parentheses / Brackets (auto-sizing)

```xml
<m:d>
  <m:dPr>
    <m:begChr m:val="("/>
    <m:endChr m:val=")"/>
  </m:dPr>
  <m:e>
    <!-- content inside parens -->
    <m:r><m:t>x+y</m:t></m:r>
  </m:e>
</m:d>
```

Use `[` `]` for square brackets, `{` `}` for curly braces, `|` `|` for absolute value.

### Matrix / System of equations

```xml
<m:m>
  <m:mPr>
    <m:mcs>
      <m:mc><m:mcPr>
        <m:count m:val="2"/>        <!-- number of columns -->
        <m:mcJc m:val="center"/>
      </m:mcPr></m:mc>
    </m:mcs>
  </m:mPr>
  <m:mr>  <!-- row 1 -->
    <m:e><m:r><m:t>a</m:t></m:r></m:e>
    <m:e><m:r><m:t>b</m:t></m:r></m:e>
  </m:mr>
  <m:mr>  <!-- row 2 -->
    <m:e><m:r><m:t>c</m:t></m:r></m:e>
    <m:e><m:r><m:t>d</m:t></m:r></m:e>
  </m:mr>
</m:m>
```

Wrap in `<m:d>` with `[` `]` or `(` `)` delimiters for bracketed matrix notation.

### Limit (lim)

```xml
<m:func>
  <m:funcPr/>
  <m:fName>
    <m:limLow>
      <m:e><m:r><m:rPr><m:sty m:val="p"/></m:rPr><m:t>lim</m:t></m:r></m:e>
      <m:lim>
        <m:r><m:t>x&#x2192;0</m:t></m:r>  <!-- x→0 -->
      </m:lim>
    </m:limLow>
  </m:fName>
  <m:e><m:r><m:t>f(x)</m:t></m:r></m:e>
</m:func>
```

### Run properties (italic, bold, font size)

```xml
<m:r>
  <m:rPr>
    <m:sty m:val="i"/>    <!-- i=italic (default for vars), b=bold, bi=bold-italic, p=plain -->
  </m:rPr>
  <m:t>x</m:t>
</m:r>
```

---

## Greek Letters & Symbols (Unicode in `<m:t>`)

Use Unicode directly inside `<m:t>` — Word renders them correctly in math context:

| Symbol | Unicode entity | Symbol | Unicode entity |
|--------|---------------|--------|---------------|
| α | `&#x03B1;` | π | `&#x03C0;` |
| β | `&#x03B2;` | σ | `&#x03C3;` |
| γ | `&#x03B3;` | Σ | `&#x03A3;` |
| δ | `&#x03B4;` | θ | `&#x03B8;` |
| λ | `&#x03BB;` | μ | `&#x03BC;` |
| ∞ | `&#x221E;` | → | `&#x2192;` |
| ± | `&#x00B1;` | ≤ | `&#x2264;` |
| ≥ | `&#x2265;` | ≠ | `&#x2260;` |
| ∂ | `&#x2202;` | ∇ | `&#x2207;` |
| ∈ | `&#x2208;` | ⊆ | `&#x2286;` |

---

## Complete Formula Examples

### Quadratic formula

```xml
<w:p>
  <m:oMathPara>
    <m:oMathParaPr><m:jc m:val="center"/></m:oMathParaPr>
    <m:oMath>
      <m:r><m:t>x</m:t></m:r>
      <m:r><m:t>=</m:t></m:r>
      <m:f>
        <m:num>
          <m:r><m:t>&#x2212;b</m:t></m:r>   <!-- −b -->
          <m:r><m:t>&#x00B1;</m:t></m:r>     <!-- ± -->
          <m:rad>
            <m:radPr><m:degHide m:val="1"/></m:radPr>
            <m:deg/>
            <m:e>
              <m:sSup>
                <m:e><m:r><m:t>b</m:t></m:r></m:e>
                <m:sup><m:r><m:t>2</m:t></m:r></m:sup>
              </m:sSup>
              <m:r><m:t>&#x2212;4ac</m:t></m:r>
            </m:e>
          </m:rad>
        </m:num>
        <m:den><m:r><m:t>2a</m:t></m:r></m:den>
      </m:f>
    </m:oMath>
  </m:oMathPara>
</w:p>
```

### Euler's identity

```xml
<w:p>
  <m:oMathPara>
    <m:oMathParaPr><m:jc m:val="center"/></m:oMathParaPr>
    <m:oMath>
      <m:sSup>
        <m:e><m:r><m:t>e</m:t></m:r></m:e>
        <m:sup>
          <m:r><m:t>i&#x03C0;</m:t></m:r>   <!-- iπ -->
        </m:sup>
      </m:sSup>
      <m:r><m:t>+1=0</m:t></m:r>
    </m:oMath>
  </m:oMathPara>
</w:p>
```

### Definite integral

```xml
<w:p>
  <m:oMathPara>
    <m:oMathParaPr><m:jc m:val="center"/></m:oMathParaPr>
    <m:oMath>
      <m:nary>
        <m:naryPr>
          <m:chr m:val="∫"/>
          <m:limLoc m:val="undOvr"/>
        </m:naryPr>
        <m:sub><m:r><m:t>a</m:t></m:r></m:sub>
        <m:sup><m:r><m:t>b</m:t></m:r></m:sup>
        <m:e>
          <m:r><m:t>f</m:t></m:r>
          <m:d>
            <m:dPr><m:begChr m:val="("/> <m:endChr m:val=")"/></m:dPr>
            <m:e><m:r><m:t>x</m:t></m:r></m:e>
          </m:d>
          <m:r><m:t xml:space="preserve"> dx</m:t></m:r>
        </m:e>
      </m:nary>
    </m:oMath>
  </m:oMathPara>
</w:p>
```

### Matrix (2×2)

```xml
<w:p>
  <m:oMathPara>
    <m:oMathParaPr><m:jc m:val="center"/></m:oMathParaPr>
    <m:oMath>
      <m:d>
        <m:dPr>
          <m:begChr m:val="["/>
          <m:endChr m:val="]"/>
        </m:dPr>
        <m:e>
          <m:m>
            <m:mPr>
              <m:mcs>
                <m:mc><m:mcPr>
                  <m:count m:val="2"/>
                  <m:mcJc m:val="center"/>
                </m:mcPr></m:mc>
              </m:mcs>
            </m:mPr>
            <m:mr>
              <m:e><m:r><m:t>a</m:t></m:r></m:e>
              <m:e><m:r><m:t>b</m:t></m:r></m:e>
            </m:mr>
            <m:mr>
              <m:e><m:r><m:t>c</m:t></m:r></m:e>
              <m:e><m:r><m:t>d</m:t></m:r></m:e>
            </m:mr>
          </m:m>
        </m:e>
      </m:d>
    </m:oMath>
  </m:oMathPara>
</w:p>
```

---

## Workflow for New Documents With Math

```bash
# 1. Create document scaffold with docx-js (no math yet)
node create.js   # outputs doc.docx

# 2. Validate the scaffold
python scripts/office/validate.py doc.docx

# 3. Unpack
python scripts/office/unpack.py doc.docx unpacked/

# 4. Verify xmlns:m in document.xml opening tag — add if missing

# 5. Inject <m:oMathPara> blocks at the correct <w:p> positions
#    Use str_replace / view tools to find insertion point

# 6. Repack
python scripts/office/pack.py unpacked/ output.docx --original doc.docx
```

---

## Critical Rules

- **Never use LibreOffice to render math** — it corrupts OMML on this backend
- **Never use `<w:t>` for fractions/roots** — always use OMML elements
- **Never use Unicode superscript characters** (e.g., ² ³) — they render as text, not math
- **Namespace `xmlns:m=` must exist** in `<w:document>` — check before injecting, add if missing
- **Block equations need `<m:oMathPara>` inside `<w:p>`** — not a bare `<m:oMath>` at paragraph level
- **Inline equations use bare `<m:oMath>`** as a sibling of `<w:r>` runs inside `<w:p>`
- **Use `xml:space="preserve"`** on `<m:t>` whenever the text has leading or trailing spaces (e.g., ` dx`)
- **`<m:degHide m:val="1"/>`** hides the degree indicator for plain square roots
- **`<m:limLoc m:val="undOvr"/>`** puts limits above/below (display); `subSup` puts them inline

---

## Quick Conversion: LaTeX → OMML

| LaTeX | OMML element(s) |
|-------|----------------|
| `\frac{a}{b}` | `<m:f><m:num>…</m:num><m:den>…</m:den></m:f>` |
| `x^{2}` | `<m:sSup>…</m:sSup>` |
| `x_{i}` | `<m:sSub>…</m:sSub>` |
| `\sqrt{x}` | `<m:rad>` with `<m:degHide m:val="1"/>` |
| `\sqrt[n]{x}` | `<m:rad>` with degree |
| `\sum_{i=1}^{n}` | `<m:nary>` with `∑` chr |
| `\int_{a}^{b}` | `<m:nary>` with `∫` chr |
| `\left( … \right)` | `<m:d>` with `(` `)` |
| `\begin{pmatrix}` | `<m:d>` + `<m:m>` |
| `\lim_{x\to 0}` | `<m:func>` + `<m:limLow>` |
| `\alpha \beta \pi` | Unicode in `<m:t>`: `&#x03B1; &#x03B2; &#x03C0;` |
