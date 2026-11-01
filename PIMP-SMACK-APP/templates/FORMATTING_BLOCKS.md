# PIMP SMACK - Formatting Block Reference
Extracted from Tyler's Word 2003 XML template (Untitled-2.xml)

---

## LIST DEFINITIONS (Auto-Numbering)

### Heading2 List (Roman Numerals: I., II., III.)
```xml
<w:listDef w:listDefId="0">
  <w:lsid w:val="1E4B68AC"/>
  <w:plt w:val="HybridMultilevel"/>
  <w:tmpl w:val="B84E2310"/>
  
  <!-- Level 0: Roman Numerals (I., II., III.) -->
  <w:lvl w:ilvl="0" w:tplc="C4F45EA2">
    <w:start w:val="1"/>
    <w:nfc w:val="1"/>  <!-- 1 = uppercase roman -->
    <w:pStyle w:val="Heading2"/>
    <w:lvlText w:val="%1."/>
    <w:lvlJc w:val="right"/>
    <w:pPr>
      <w:ind w:left="720" w:hanging="360"/>
    </w:pPr>
  </w:lvl>
  
  <!-- Level 1: Arabic (1., 2., 3.) -->
  <w:lvl w:ilvl="1" w:tplc="EEE0C9D4">
    <w:start w:val="1"/>
    <w:lvlText w:val="%2."/>
    <w:lvlJc w:val="left"/>
    <w:pPr>
      <w:ind w:left="1440" w:hanging="360"/>
    </w:pPr>
    <w:rPr>
      <w:rFonts w:hint="default"/>
      <w:b/>
    </w:rPr>
  </w:lvl>
  
  <!-- Level 2: Lowercase Letters (a., b., c.) -->
  <w:lvl w:ilvl="2" w:tplc="0409001B">
    <w:start w:val="1"/>
    <w:nfc w:val="2"/>  <!-- 2 = lowercase roman -->
    <w:lvlText w:val="%3."/>
    <w:lvlJc w:val="right"/>
    <w:pPr>
      <w:ind w:left="2160" w:hanging="180"/>
    </w:pPr>
  </w:lvl>
</w:listDef>
```

### Bullet List (Em-dash style)
```xml
<w:listDef w:listDefId="1">
  <w:lsid w:val="25416467"/>
  <w:plt w:val="HybridMultilevel"/>
  <w:lvl w:ilvl="0" w:tplc="7BF85F4E">
    <w:start w:val="4"/>
    <w:nfc w:val="23"/>  <!-- 23 = bullet -->
    <w:lvlText w:val="—"/>  <!-- em-dash -->
    <w:lvlJc w:val="left"/>
    <w:pPr>
      <w:ind w:left="1080" w:hanging="360"/>
    </w:pPr>
    <w:rPr>
      <w:rFonts w:ascii="Californian FB" w:h-ansi="Californian FB" w:hint="default"/>
    </w:rPr>
  </w:lvl>
</w:listDef>
```

### List Instance Reference
```xml
<!-- To use list in a paragraph -->
<w:p>
  <w:pPr>
    <w:pStyle w:val="Heading2"/>
    <w:listPr>
      <wx:t wx:val="I."/>  <!-- Display text hint -->
      <wx:font wx:val="Times New Roman"/>
    </w:listPr>
  </w:pPr>
  <w:r><w:t>HEADING TEXT HERE</w:t></w:r>
</w:p>
```

---

## SIGNATURE BLOCK

### Complete Signature Block Structure
```xml
<!-- "Respectfully submitted," line -->
<w:p>
  <w:pPr>
    <w:spacing w:before="240" w:after="60" w:line="480" w:line-rule="auto"/>
    <w:rPr>
      <w:rFonts w:ascii="Californian FB" w:h-ansi="Californian FB"/>
      <w:sz w:val="28"/><w:sz-cs w:val="28"/>
    </w:rPr>
  </w:pPr>
  <w:r>
    <w:rPr>
      <w:rFonts w:ascii="Californian FB" w:h-ansi="Californian FB"/>
      <w:sz w:val="28"/><w:sz-cs w:val="28"/>
    </w:rPr>
    <w:t>Respectfully submitted,</w:t>
  </w:r>
</w:p>

<!-- Signature line (Edwardian Script, underlined) -->
<w:p>
  <w:pPr>
    <w:ind w:left="3600" w:first-line="720"/>
  </w:pPr>
  <w:r>
    <w:rPr>
      <w:rFonts w:ascii="Edwardian Script ITC" w:h-ansi="Edwardian Script ITC"/>
      <w:b/><w:b-cs/>
      <w:i/><w:i-cs/>
      <w:sz w:val="52"/><w:sz-cs w:val="52"/>
      <w:u w:val="single"/>
    </w:rPr>
    <w:t>/s/ Tyler Allen Lofall</w:t>
  </w:r>
</w:p>

<!-- Name in CAPS (bold) -->
<w:p>
  <w:pPr>
    <w:ind w:left="3600" w:first-line="720"/>
  </w:pPr>
  <w:r>
    <w:rPr>
      <w:rFonts w:ascii="Californian FB" w:h-ansi="Californian FB"/>
      <w:b/><w:b-cs/>
      <w:sz w:val="28"/><w:sz-cs w:val="28"/>
    </w:rPr>
    <w:t>TYLER ALLEN LOFALL</w:t>
  </w:r>
  <w:r>
    <w:rPr>
      <w:rFonts w:ascii="Californian FB" w:h-ansi="Californian FB"/>
      <w:sz w:val="28"/><w:sz-cs w:val="28"/>
    </w:rPr>
    <w:t>, Pro se</w:t>
  </w:r>
</w:p>

<!-- Address with MAIL/ONLY tabs -->
<w:p>
  <w:pPr>
    <w:ind w:left="3600" w:first-line="720"/>
  </w:pPr>
  <w:r>
    <w:rPr>
      <w:rFonts w:ascii="Californian FB" w:h-ansi="Californian FB"/>
      <w:sz w:val="28"/><w:sz-cs w:val="28"/>
    </w:rPr>
    <w:t>5809 W Park Place</w:t>
  </w:r>
  <w:r><w:tab/></w:r>
  <w:r>
    <w:rPr>
      <w:rFonts w:ascii="Californian FB" w:h-ansi="Californian FB"/>
      <w:sz w:val="28"/><w:sz-cs w:val="28"/>
    </w:rPr>
    <w:t>MAIL</w:t>
  </w:r>
</w:p>

<w:p>
  <w:pPr>
    <w:ind w:left="3600" w:first-line="720"/>
  </w:pPr>
  <w:r>
    <w:rPr>
      <w:rFonts w:ascii="Californian FB" w:h-ansi="Californian FB"/>
      <w:sz w:val="28"/><w:sz-cs w:val="28"/>
    </w:rPr>
    <w:t>Pasco, WA 99301</w:t>
  </w:r>
  <w:r><w:tab/><w:tab/></w:r>
  <w:r>
    <w:rPr>
      <w:rFonts w:ascii="Californian FB" w:h-ansi="Californian FB"/>
      <w:sz w:val="28"/><w:sz-cs w:val="28"/>
    </w:rPr>
    <w:t>ONLY</w:t>
  </w:r>
</w:p>

<!-- Email -->
<w:p>
  <w:pPr>
    <w:ind w:left="3600" w:first-line="720"/>
  </w:pPr>
  <w:r>
    <w:rPr>
      <w:rFonts w:ascii="Californian FB" w:h-ansi="Californian FB"/>
      <w:sz w:val="28"/><w:sz-cs w:val="28"/>
    </w:rPr>
    <w:t>Email - tyleralofall@gmail.com</w:t>
  </w:r>
</w:p>

<!-- Phone -->
<w:p>
  <w:pPr>
    <w:spacing w:after="360"/>
    <w:ind w:left="3600" w:first-line="720"/>
  </w:pPr>
  <w:r>
    <w:rPr>
      <w:rFonts w:ascii="Californian FB" w:h-ansi="Californian FB"/>
      <w:sz w:val="28"/><w:sz-cs w:val="28"/>
    </w:rPr>
    <w:t>Phone - (386) 262-3322</w:t>
  </w:r>
</w:p>
```

---

## SIGNATURE STYLE SUMMARY

| Element | Font | Size | Style |
|---------|------|------|-------|
| Signature /s/ | Edwardian Script ITC | 26pt (52 half-pts) | Bold, Italic, Underline |
| Name (CAPS) | Californian FB | 14pt (28 half-pts) | Bold |
| "Pro se" | Californian FB | 14pt | Normal |
| Address/Contact | Californian FB | 14pt | Normal |
| Indent | Left 3600 twips (2.5") + first-line 720 (0.5") | | |

---

## TABLE STRUCTURE

### Basic Table with Borders
```xml
<w:tbl>
  <w:tblPr>
    <w:tblW w:w="0" w:type="auto"/>
    <w:jc w:val="center"/>
    <w:tblBorders>
      <w:top w:val="single" w:sz="4" w:space="0" w:color="auto"/>
      <w:left w:val="single" w:sz="4" w:space="0" w:color="auto"/>
      <w:bottom w:val="single" w:sz="4" w:space="0" w:color="auto"/>
      <w:right w:val="single" w:sz="4" w:space="0" w:color="auto"/>
      <w:insideH w:val="single" w:sz="4" w:space="0" w:color="auto"/>
      <w:insideV w:val="single" w:sz="4" w:space="0" w:color="auto"/>
    </w:tblBorders>
    <w:tblCellMar>
      <w:top w:w="43" w:type="dxa"/>
      <w:left w:w="43" w:type="dxa"/>
      <w:bottom w:w="43" w:type="dxa"/>
      <w:right w:w="43" w:type="dxa"/>
    </w:tblCellMar>
  </w:tblPr>
  
  <!-- Grid defines column widths -->
  <w:tblGrid>
    <w:gridCol w:w="2429"/>
    <w:gridCol w:w="3660"/>
    <w:gridCol w:w="1228"/>
    <w:gridCol w:w="1707"/>
  </w:tblGrid>
  
  <!-- Header Row -->
  <w:tr>
    <w:trPr>
      <w:tblHeader/>  <!-- Repeat on each page -->
      <w:jc w:val="center"/>
    </w:trPr>
    <w:tc>
      <w:tcPr>
        <w:tcW w:w="2429" w:type="dxa"/>
        <w:shd w:val="clear" w:color="auto" w:fill="D9E2F3"/>  <!-- Light blue -->
      </w:tcPr>
      <w:p>
        <w:r>
          <w:rPr>
            <w:rFonts w:ascii="Amasis MT Pro Medium" w:h-ansi="Amasis MT Pro Medium"/>
          </w:rPr>
          <w:t>Column Header</w:t>
        </w:r>
      </w:p>
    </w:tc>
    <!-- More cells... -->
  </w:tr>
  
  <!-- Data Row -->
  <w:tr>
    <w:tc>
      <w:tcPr>
        <w:tcW w:w="2429" w:type="dxa"/>
      </w:tcPr>
      <w:p>
        <w:r><w:t>Cell content</w:t></w:r>
      </w:p>
    </w:tc>
  </w:tr>
</w:tbl>
```

---

## HEADER / FOOTER

### Header (Case Number, Centered)
```xml
<w:hdr w:type="odd">
  <w:p>
    <w:pPr>
      <w:jc w:val="center"/>
    </w:pPr>
    <w:r>
      <w:rPr>
        <w:rFonts w:ascii="Californian FB" w:h-ansi="Californian FB"/>
        <w:b/>
        <w:sz w:val="28"/>
      </w:rPr>
      <w:t>Case No. 25-6461</w:t>
    </w:r>
  </w:p>
</w:hdr>
```

### Footer (Page Number Field)
```xml
<w:ftr w:type="odd">
  <w:p>
    <w:pPr>
      <w:jc w:val="center"/>
    </w:pPr>
    <w:r>
      <w:rPr><w:sz w:val="20"/></w:rPr>
      <w:t>Page </w:t>
    </w:r>
    <w:r>
      <w:rPr><w:sz w:val="20"/></w:rPr>
      <w:fldChar w:fldCharType="begin"/>
    </w:r>
    <w:r>
      <w:rPr><w:sz w:val="20"/></w:rPr>
      <w:instrText>PAGE</w:instrText>
    </w:r>
    <w:r>
      <w:rPr><w:sz w:val="20"/></w:rPr>
      <w:fldChar w:fldCharType="separate"/>
    </w:r>
    <w:r>
      <w:rPr><w:sz w:val="20"/></w:rPr>
      <w:t>1</w:t>
    </w:r>
    <w:r>
      <w:rPr><w:sz w:val="20"/></w:rPr>
      <w:fldChar w:fldCharType="end"/>
    </w:r>
  </w:p>
</w:ftr>
```

---

## PAGE SETTINGS

```xml
<w:sectPr>
  <!-- Page Size: Letter (8.5" x 11") -->
  <w:pgSz w:w="12240" w:h="15840"/>
  
  <!-- Margins: 1" all around -->
  <w:pgMar 
    w:top="1440" 
    w:right="1440" 
    w:bottom="1440" 
    w:left="1440" 
    w:header="720" 
    w:footer="720" 
    w:gutter="0"/>
</w:sectPr>
```

**Units:**
- 1440 twips = 1 inch
- 720 twips = 0.5 inch
- Font size in half-points (28 = 14pt)
