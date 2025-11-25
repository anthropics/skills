
# GenerateBlocks Patterns Library

Production-ready patterns extracted from real implementations.

---

## Pattern 1: Hero Section with Two-Column Grid + Feature Card

**Use Case**: Landing page hero with content on left, featured card on right

### Structure
```
section.gbp-section (full-width background)
└── div.gbp-section__inner (1280px max-width)
    └── div (2-col grid: content + card)
        ├── div (Content column)
        │   ├── h1 (Headline)
        │   ├── p (Description)
        │   └── div (Button container - flexbox)
        │       ├── a.gbp-button--primary
        │       └── a.gbp-button--secondary
        └── div (Card column)
            └── div (White card with shadow)
                ├── div (Icon container + SVG)
                ├── h2 (Card title)
                └── p (Card description)
```

### Complete Code

```html
<!-- wp:generateblocks/element {
  "uniqueId":"hero001",
  "tagName":"section",
  "styles":{
    "backgroundColor":"#f0fdf4",
    "paddingTop":"4rem",
    "paddingBottom":"4rem"
  },
  "globalClasses":["gbp-section"],
  "metadata":{"name":"Hero Section"}
} -->
<section class="gbp-section gb-element-hero001">

  <!-- Inner Container: 1280px max-width -->
  <!-- wp:generateblocks/element {
    "uniqueId":"hero002",
    "tagName":"div",
    "styles":{
      "marginLeft":"auto",
      "marginRight":"auto",
      "display":"grid",
      "gridTemplateColumns":"repeat(2, minmax(0, 1fr))",
      "columnGap":"3rem",
      "@media (max-width:1024px)":{
        "display":"block"
      },
      "alignItems":"center",
      "maxWidth":"1280px"
    },
    "globalClasses":["gbp-section__inner"]
  } -->
  <div class="gbp-section__inner gb-element-hero002">

    <!-- Left Column: Content -->
    <!-- wp:generateblocks/element {
      "uniqueId":"hero003",
      "tagName":"div"
    } -->
    <div class="gb-element-hero003">

      <!-- Headline -->
      <!-- wp:generateblocks/text {
        "uniqueId":"hero004",
        "tagName":"h1",
        "content":"Your Headline Here",
        "styles":{
          "fontSize":"2.25rem",
          "fontWeight":"700",
          "lineHeight":"1.25",
          "marginBottom":"1.5rem",
          "color":"#111827"
        },
        "globalClasses":["gbp-section__headline"]
      } /-->

      <!-- Description -->
      <!-- wp:generateblocks/text {
        "uniqueId":"hero005",
        "tagName":"p",
        "content":"Your description text goes here...",
        "styles":{
          "fontSize":"1.25rem",
          "lineHeight":"1.75",
          "marginBottom":"2rem",
          "color":"#4b5563"
        },
        "globalClasses":["gbp-section__text"]
      } /-->

      <!-- Button Container -->
      <!-- wp:generateblocks/element {
        "uniqueId":"hero006",
        "tagName":"div",
        "styles":{
          "marginTop":"2rem",
          "display":"flex",
          "columnGap":"1rem",
          "rowGap":"1rem",
          "flexWrap":"wrap"
        }
      } -->
      <div class="gb-element-hero006">

        <!-- Primary Button -->
        <!-- wp:generateblocks/text {
          "uniqueId":"hero007",
          "tagName":"a",
          "content":"Primary Action",
          "styles":{
            "backgroundColor":"#80b238",
            "color":"#ffffff",
            "padding":"1rem 2rem",
            "borderRadius":"0.5rem",
            "fontSize":"1rem",
            "fontWeight":"600",
            "display":"inline-flex",
            "alignItems":"center",
            "textDecoration":"none",
            "&:is(:hover, :focus)":{
              "backgroundColor":"#6a9530"
            }
          },
          "globalClasses":["gbp-button--primary"],
          "htmlAttributes":{"href":"/about"}
        } /-->

        <!-- Secondary Button -->
        <!-- wp:generateblocks/text {
          "uniqueId":"hero008",
          "tagName":"a",
          "content":"Secondary Action",
          "styles":{
            "backgroundColor":"transparent",
            "color":"#80b238",
            "padding":"1rem 2rem",
            "border":"2px solid #80b238",
            "borderRadius":"0.5rem",
            "fontSize":"1rem",
            "fontWeight":"600",
            "display":"inline-flex",
            "alignItems":"center",
            "textDecoration":"none",
            "&:is(:hover, :focus)":{
              "backgroundColor":"#80b238",
              "color":"#ffffff"
            }
          },
          "globalClasses":["gbp-button--secondary"],
          "htmlAttributes":{"href":"/support"}
        } /-->

      </div>
      <!-- /wp:generateblocks/element -->

    </div>
    <!-- /wp:generateblocks/element -->

    <!-- Right Column: Feature Card -->
    <!-- wp:generateblocks/element {
      "uniqueId":"hero009",
      "tagName":"div"
    } -->
    <div class="gb-element-hero009">

      <!-- White Card with Shadow -->
      <!-- wp:generateblocks/element {
        "uniqueId":"hero010",
        "tagName":"div",
        "styles":{
          "position":"relative",
          "backgroundColor":"#ffffff",
          "borderRadius":"1rem",
          "padding":"2rem",
          "boxShadow":"0 25px 50px -12px rgba(0,0,0,0.25)"
        }
      } -->
      <div class="gb-element-hero010">

        <!-- Icon Container -->
        <!-- wp:generateblocks/element {
          "uniqueId":"hero011",
          "tagName":"div",
          "styles":{
            "backgroundColor":"rgba(189, 216, 147, 0.3)",
            "borderRadius":"0.75rem",
            "padding":"1.5rem",
            "marginBottom":"1.5rem",
            "width":"80px",
            "marginLeft":"auto",
            "marginRight":"auto"
          }
        } -->
        <div class="gb-element-hero011">
          <!-- wp:html -->
          <svg style="width:64px;height:64px;color:#80b238;margin:0 auto;display:block"
               xmlns="http://www.w3.org/2000/svg" viewBox="0 0 24 24"
               fill="none" stroke="currentColor" stroke-width="2">
            <path d="M11 20A7 7 0 0 1 9.8 6.1C15.5 5 17 4.48 19 2c1 2 2 4.18 2 8 0 5.5-4.78 10-10 10Z"/>
            <path d="M2 21c0-3 1.85-5.36 5.08-6C9.5 14.52 12 13 13 12"/>
          </svg>
          <!-- /wp:html -->
        </div>
        <!-- /wp:generateblocks/element -->

        <!-- Card Title -->
        <!-- wp:generateblocks/text {
          "uniqueId":"hero012",
          "tagName":"h2",
          "content":"Card Title",
          "styles":{
            "fontSize":"1.5rem",
            "fontWeight":"700",
            "marginBottom":"1rem",
            "textAlign":"center",
            "color":"#111827"
          }
        } /-->

        <!-- Card Description -->
        <!-- wp:generateblocks/text {
          "uniqueId":"hero013",
          "tagName":"p",
          "content":"Card description text...",
          "styles":{
            "textAlign":"center",
            "color":"#4b5563",
            "lineHeight":"1.7"
          }
        } /-->

      </div>
      <!-- /wp:generateblocks/element -->

    </div>
    <!-- /wp:generateblocks/element -->

  </div>
  <!-- /wp:generateblocks/element -->

</section>
<!-- /wp:generateblocks/element -->
```

---

## Pattern 2: Quote Section with Centered Card

**Use Case**: Inspirational quote with attribution

### Complete Code

```html
<!-- wp:generateblocks/element {
  "uniqueId":"quote001",
  "tagName":"section",
  "styles":{
    "backgroundColor":"#80b238",
    "paddingTop":"4rem",
    "paddingBottom":"4rem"
  },
  "globalClasses":["gbp-section"]
} -->
<section class="gbp-section gb-element-quote001">

  <!-- Inner Container: 900px max-width for quotes -->
  <!-- wp:generateblocks/element {
    "uniqueId":"quote002",
    "tagName":"div",
    "styles":{
      "maxWidth":"900px",
      "marginLeft":"auto",
      "marginRight":"auto",
      "paddingLeft":"1.5rem",
      "paddingRight":"1.5rem"
    },
    "globalClasses":["gbp-section__inner"]
  } -->
  <div class="gbp-section__inner gb-element-quote002">

    <!-- White Card -->
    <!-- wp:generateblocks/element {
      "uniqueId":"quote003",
      "tagName":"div",
      "styles":{
        "backgroundColor":"#ffffff",
        "textAlign":"center",
        "borderRadius":"1rem",
        "padding":"3rem 2rem",
        "boxShadow":"0 25px 50px -12px rgba(0,0,0,0.25)"
      }
    } -->
    <div class="gb-element-quote003">

      <!-- Quote Icon -->
      <!-- wp:html -->
      <div style="margin-bottom:1.5rem;text-align:center">
        <svg style="width:48px;height:48px;color:#80b238;margin:0 auto;opacity:0.5"
             fill="currentColor" viewBox="0 0 24 24">
          <path d="M14.017 21v-7.391c0-5.704 3.731-9.57 8.983-10.609l.995 2.151c-2.432.917-3.995 3.638-3.995 5.849h4v10h-9.983zm-14.017 0v-7.391c0-5.704 3.748-9.57 9-10.609l.996 2.151c-2.433.917-3.996 3.638-3.996 5.849h4v10h-10z"/>
        </svg>
      </div>
      <!-- /wp:html -->

      <!-- Quote Text -->
      <!-- wp:generateblocks/text {
        "uniqueId":"quote004",
        "tagName":"p",
        "content":"Your inspiring quote goes here.",
        "styles":{
          "fontSize":"2rem",
          "fontWeight":"700",
          "fontStyle":"italic",
          "textAlign":"center",
          "color":"#111827",
          "marginBottom":"1.5rem",
          "lineHeight":"1.2"
        }
      } /-->

      <!-- Gradient Divider -->
      <!-- wp:generateblocks/element {
        "uniqueId":"quote005",
        "tagName":"div",
        "styles":{
          "backgroundImage":"linear-gradient(to right, #80b238 0%, #bdd893 100%)",
          "width":"96px",
          "height":"4px",
          "marginLeft":"auto",
          "marginRight":"auto",
          "marginBottom":"1.5rem"
        }
      } /-->

      <!-- Author Name -->
      <!-- wp:generateblocks/text {
        "uniqueId":"quote006",
        "tagName":"p",
        "content":"Author Name",
        "styles":{
          "color":"#4b5563",
          "textAlign":"center",
          "fontWeight":"600",
          "fontSize":"1.125rem",
          "marginBottom":"0.5rem"
        }
      } /-->

      <!-- Author Details -->
      <!-- wp:generateblocks/text {
        "uniqueId":"quote007",
        "tagName":"p",
        "content":"Author title or description",
        "styles":{
          "color":"#6b7280",
          "textAlign":"center",
          "fontSize":"0.875rem"
        }
      } /-->

    </div>
    <!-- /wp:generateblocks/element -->

  </div>
  <!-- /wp:generateblocks/element -->

</section>
<!-- /wp:generateblocks/element -->
```

---

## Pattern 3: Stats Section (2→4 Column Responsive)

**Use Case**: Data/metrics visualization
**Responsive**: 2 cols mobile → 4 cols desktop

### Complete Code

```html
<!-- wp:generateblocks/element {
  "uniqueId":"stats001",
  "tagName":"section",
  "styles":{
    "backgroundColor":"#80b238",
    "paddingTop":"4rem",
    "paddingBottom":"4rem"
  },
  "globalClasses":["gbp-section"]
} -->
<section class="gbp-section gb-element-stats001">

  <!-- Inner Container -->
  <!-- wp:generateblocks/element {
    "uniqueId":"stats002",
    "tagName":"div",
    "styles":{
      "marginLeft":"auto",
      "marginRight":"auto",
      "maxWidth":"1280px",
      "paddingLeft":"1.5rem",
      "paddingRight":"1.5rem"
    },
    "globalClasses":["gbp-section__inner"]
  } -->
  <div class="gbp-section__inner gb-element-stats002">

    <!-- Section Title -->
    <!-- wp:generateblocks/text {
      "uniqueId":"stats003",
      "tagName":"h2",
      "content":"Section Title",
      "styles":{
        "fontSize":"2.25rem",
        "fontWeight":"700",
        "marginBottom":"1rem",
        "textAlign":"center",
        "color":"#ffffff"
      }
    } /-->

    <!-- Section Description -->
    <!-- wp:generateblocks/text {
      "uniqueId":"stats004",
      "tagName":"p",
      "content":"Section description text...",
      "styles":{
        "fontSize":"1.25rem",
        "lineHeight":"1.75",
        "marginBottom":"3rem",
        "textAlign":"center",
        "color":"rgba(255, 255, 255, 0.8)",
        "maxWidth":"768px",
        "marginLeft":"auto",
        "marginRight":"auto"
      }
    } /-->

    <!-- Stats Grid: 2 cols mobile, 4 cols desktop -->
    <!-- wp:generateblocks/element {
      "uniqueId":"stats005",
      "tagName":"div",
      "styles":{
        "display":"grid",
        "gridTemplateColumns":"repeat(2, minmax(0, 1fr))",
        "columnGap":"2rem",
        "rowGap":"2rem",
        "@media (min-width:1024px)":{
          "gridTemplateColumns":"repeat(4, minmax(0, 1fr))"
        }
      }
    } -->
    <div class="gb-element-stats005">

      <!-- Stat Item 1 -->
      <!-- wp:generateblocks/element {
        "uniqueId":"stats006",
        "tagName":"div",
        "styles":{"textAlign":"center"}
      } -->
      <div class="gb-element-stats006">
        <!-- wp:generateblocks/text {
          "uniqueId":"stats007",
          "tagName":"div",
          "content":"5,000+",
          "styles":{
            "fontSize":"2.25rem",
            "fontWeight":"700",
            "color":"#ffffff",
            "marginBottom":"0.5rem",
            "lineHeight":"1",
            "@media (min-width:1024px)":{"fontSize":"3rem"}
          }
        } /-->
        <!-- wp:generateblocks/text {
          "uniqueId":"stats008",
          "tagName":"div",
          "content":"Stat Label",
          "styles":{
            "color":"rgba(255, 255, 255, 0.8)",
            "fontWeight":"500"
          }
        } /-->
      </div>
      <!-- /wp:generateblocks/element -->

      <!-- Stat Item 2 -->
      <!-- wp:generateblocks/element {
        "uniqueId":"stats009",
        "tagName":"div",
        "styles":{"textAlign":"center"}
      } -->
      <div class="gb-element-stats009">
        <!-- wp:generateblocks/text {
          "uniqueId":"stats010",
          "tagName":"div",
          "content":"100%",
          "styles":{
            "fontSize":"2.25rem",
            "fontWeight":"700",
            "color":"#ffffff",
            "marginBottom":"0.5rem",
            "lineHeight":"1",
            "@media (min-width:1024px)":{"fontSize":"3rem"}
          }
        } /-->
        <!-- wp:generateblocks/text {
          "uniqueId":"stats011",
          "tagName":"div",
          "content":"Stat Label",
          "styles":{
            "color":"rgba(255, 255, 255, 0.8)",
            "fontWeight":"500"
          }
        } /-->
      </div>
      <!-- /wp:generateblocks/element -->

      <!-- Stat Item 3 & 4: Copy pattern above -->

    </div>
    <!-- /wp:generateblocks/element -->

  </div>
  <!-- /wp:generateblocks/element -->

</section>
<!-- /wp:generateblocks/element -->
```

---

## Pattern 4: 3-Column Feature Grid with Color-Coded Cards

**Use Case**: Mission statements or features with different colored cards

### Card Colors
| Card | Background | Icon BG | Icon Color |
|------|-----------|---------|------------|
| Green | `#dcfce7` | `rgba(34,197,94,0.2)` | `#16a34a` |
| Blue | `#dbeafe` | `rgba(59,130,246,0.2)` | `#2563eb` |
| Purple | `#f3e8ff` | `rgba(168,85,247,0.2)` | `#7c3aed` |

### Card Structure
```html
<!-- wp:generateblocks/element {
  "uniqueId":"mission006",
  "tagName":"div",
  "styles":{
    "backgroundColor":"#dcfce7",
    "borderRadius":"1rem",
    "padding":"2rem"
  }
} -->
<div class="gb-element-mission006">

  <!-- Icon Container -->
  <!-- wp:generateblocks/element {
    "uniqueId":"mission007",
    "tagName":"div",
    "styles":{
      "backgroundColor":"rgba(34, 197, 94, 0.2)",
      "borderRadius":"0.75rem",
      "padding":"1rem",
      "marginBottom":"1.5rem",
      "width":"64px"
    }
  } -->
  <div class="gb-element-mission007">
    <!-- wp:html -->
    <svg style="width:48px;height:48px;color:#16a34a"
         xmlns="http://www.w3.org/2000/svg" viewBox="0 0 24 24"
         fill="none" stroke="currentColor" stroke-width="2">
      <path d="M12 2L15.09 8.26L22 9.27L17 14.14L18.18 21.02L12 17.77L5.82 21.02L7 14.14L2 9.27L8.91 8.26L12 2Z"/>
    </svg>
    <!-- /wp:html -->
  </div>
  <!-- /wp:generateblocks/element -->

  <!-- Card Title -->
  <!-- wp:generateblocks/text {
    "uniqueId":"mission008",
    "tagName":"h3",
    "content":"Card Title",
    "styles":{
      "fontSize":"1.5rem",
      "fontWeight":"700",
      "marginBottom":"1rem",
      "color":"#111827"
    }
  } /-->

  <!-- Card Description -->
  <!-- wp:generateblocks/text {
    "uniqueId":"mission009",
    "tagName":"p",
    "content":"Card description text...",
    "styles":{
      "color":"#4b5563",
      "lineHeight":"1.7"
    }
  } /-->

</div>
<!-- /wp:generateblocks/element -->
```

---

## Pattern 5: Video Section with 16:9 Container

**Critical CSS for 16:9 Video**:
```css
.gb-element-video007 {
  position: relative !important;
  padding-bottom: 56.25% !important;
  height: 0 !important;
  overflow: hidden !important;
  border-radius: 1rem !important;
}

.gb-element-video007 iframe {
  position: absolute !important;
  top: 0 !important;
  left: 0 !important;
  width: 100% !important;
  height: 100% !important;
  border: 0 !important;
}
```

### Video Container Code
```html
<!-- wp:generateblocks/element {
  "uniqueId":"video007",
  "tagName":"div",
  "styles":{
    "position":"relative",
    "paddingBottom":"56.25%",
    "height":"0",
    "overflow":"hidden",
    "borderRadius":"1rem"
  }
} -->
<div class="gb-element-video007">
  <!-- wp:html -->
  <iframe
    src="https://www.youtube.com/embed/VIDEO_ID"
    title="Video Title"
    allow="accelerometer; autoplay; clipboard-write; encrypted-media; gyroscope; picture-in-picture"
    allowfullscreen>
  </iframe>
  <!-- /wp:html -->
</div>
<!-- /wp:generateblocks/element -->
```

---

## Global Classes Reference

| Class | Purpose | CSS |
|-------|---------|-----|
| `.gbp-section` | Full-width container | `width: 100vw; margin-left: calc(50% - 50vw);` |
| `.gbp-section__inner` | Constrained container | `max-width: 1280px; margin: 0 auto;` |
| `.gbp-button--primary` | Primary button | Green background, white text |
| `.gbp-button--secondary` | Outline button | White background, green border |

---

## Required Fallback CSS

```css
/* Full-width section architecture */
.page-id-XX .gbp-section {
  max-width: none !important;
  width: 100vw !important;
  margin-left: calc(50% - 50vw) !important;
  margin-right: calc(50% - 50vw) !important;
  padding-left: 0 !important;
  padding-right: 0 !important;
}

.page-id-XX .gbp-section__inner {
  max-width: 1280px !important;
  margin-left: auto !important;
  margin-right: auto !important;
  padding-left: 1.5rem !important;
  padding-right: 1.5rem !important;
}

/* Primary Button */
.page-id-XX .gbp-button--primary {
  background-color: #80b238 !important;
  color: #ffffff !important;
  padding: 1rem 2rem !important;
  border-radius: 0.5rem !important;
  font-weight: 600 !important;
  text-decoration: none !important;
  transition: all 0.3s ease-in-out !important;
}

.page-id-XX .gbp-button--primary:hover {
  background-color: #6a9530 !important;
}

/* Secondary Button */
.page-id-XX .gbp-button--secondary {
  background-color: transparent !important;
  color: #80b238 !important;
  padding: 1rem 2rem !important;
  border: 2px solid #80b238 !important;
  border-radius: 0.5rem !important;
  font-weight: 600 !important;
  text-decoration: none !important;
  transition: all 0.3s ease-in-out !important;
}

.page-id-XX .gbp-button--secondary:hover {
  background-color: #80b238 !important;
  color: #ffffff !important;
}

/* Responsive Stats Grid */
.page-id-XX .gb-element-stats005 {
  display: grid !important;
  grid-template-columns: repeat(2, minmax(0, 1fr)) !important;
  gap: 2rem !important;
}

@media (min-width: 1024px) {
  .page-id-XX .gb-element-stats005 {
    grid-template-columns: repeat(4, minmax(0, 1fr)) !important;
  }
}
```

---

## Usage Notes

1. **Replace `page-id-XX`** with your actual page ID
2. **Update `uniqueId`** values to avoid conflicts
3. **Open editor and click Update** after WP-CLI imports to trigger CSS generation
4. **Always provide fallback CSS** in child theme style.css
