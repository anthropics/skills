#!/usr/bin/env python3
"""Landing Page Scaffolder — Generate landing pages as HTML or Next.js TSX from config.

Creates production-ready landing pages with hero sections, features,
testimonials, pricing, CTAs, and responsive design.

Usage:
    python landing_page_scaffolder.py config.json --format html --output page.html
    python landing_page_scaffolder.py config.json --format tsx --output LandingPage.tsx
    python landing_page_scaffolder.py config.json --format json
"""

import argparse
import json
import sys
from typing import Dict, List, Any, Optional
from datetime import datetime
import html as html_module


def escape(text: str) -> str:
    """HTML-escape text."""
    return html_module.escape(str(text))


# ---------------------------------------------------------------------------
# Tailwind style mappings for TSX output
# ---------------------------------------------------------------------------

DESIGN_STYLES = {
    "dark-saas": {
        "bg": "bg-gray-950", "text": "text-white",
        "accent": "violet", "card_bg": "bg-gray-900 border border-gray-800",
        "btn": "bg-violet-600 hover:bg-violet-500 text-white",
        "btn_secondary": "border border-gray-700 text-gray-300 hover:bg-gray-800",
        "section_alt": "bg-gray-900/50", "muted": "text-gray-400",
        "border": "border-gray-800",
    },
    "clean-minimal": {
        "bg": "bg-white", "text": "text-gray-900",
        "accent": "blue", "card_bg": "bg-gray-50 border border-gray-200 rounded-2xl",
        "btn": "bg-blue-600 hover:bg-blue-700 text-white",
        "btn_secondary": "border border-gray-300 text-gray-700 hover:bg-gray-50",
        "section_alt": "bg-gray-50", "muted": "text-gray-500",
        "border": "border-gray-200",
    },
    "bold-startup": {
        "bg": "bg-white", "text": "text-gray-900",
        "accent": "orange", "card_bg": "shadow-xl rounded-3xl bg-white",
        "btn": "bg-orange-500 hover:bg-orange-600 text-white",
        "btn_secondary": "border-2 border-orange-500 text-orange-600 hover:bg-orange-50",
        "section_alt": "bg-orange-50/30", "muted": "text-gray-500",
        "border": "border-gray-200",
    },
    "enterprise": {
        "bg": "bg-slate-50", "text": "text-slate-900",
        "accent": "slate", "card_bg": "bg-white border border-slate-200 shadow-sm",
        "btn": "bg-slate-900 hover:bg-slate-800 text-white",
        "btn_secondary": "border border-slate-300 text-slate-700 hover:bg-slate-100",
        "section_alt": "bg-white", "muted": "text-slate-500",
        "border": "border-slate-200",
    },
}


# ---------------------------------------------------------------------------
# TSX generators
# ---------------------------------------------------------------------------

def tsx_nav(config: Dict[str, Any], style: Dict[str, str]) -> str:
    brand = config.get("brand", "Brand")
    nav_links = config.get("nav_links", [])
    cta = config.get("nav_cta", {"text": "Get Started", "url": "#"})
    links_jsx = "\n          ".join(
        f'<a href="{l.get("url", "#")}" className="{style["muted"]} hover:{style["text"]} font-medium transition-colors">{l.get("text", "")}</a>'
        for l in nav_links
    )
    return f'''function Navbar() {{
  return (
    <nav className="sticky top-0 z-50 {style["bg"]} border-b {style["border"]} backdrop-blur-sm">
      <div className="mx-auto flex max-w-7xl items-center justify-between px-6 py-4">
        <a href="#" className="text-xl font-bold {style["text"]}">{brand}</a>
        <div className="hidden items-center gap-8 md:flex">
          {links_jsx}
          <a href="{cta.get("url", "#")}" className="rounded-lg {style["btn"]} px-5 py-2.5 text-sm font-semibold transition-colors">
            {cta.get("text", "Get Started")}
          </a>
        </div>
      </div>
    </nav>
  );
}}'''


def tsx_hero(hero: Dict[str, Any], style: Dict[str, str]) -> str:
    h1 = hero.get("headline", "Your Headline Here")
    sub = hero.get("subheadline", "")
    primary_cta = hero.get("primary_cta", {"text": "Get Started", "url": "#"})
    secondary_cta = hero.get("secondary_cta", None)
    secondary_jsx = ""
    if secondary_cta:
        secondary_jsx = f'''
          <a href="{secondary_cta.get("url", "#")}" className="rounded-lg {style["btn_secondary"]} px-8 py-3 text-lg font-semibold transition-colors">
            {secondary_cta.get("text", "Learn More")}
          </a>'''
    return f'''function Hero() {{
  return (
    <section className="flex min-h-[80vh] flex-col items-center justify-center px-6 py-24 text-center {style["bg"]}">
      <div className="mx-auto max-w-4xl">
        <h1 className="mb-6 text-5xl font-bold tracking-tight {style["text"]} md:text-7xl">
          {h1}
        </h1>
        <p className="mx-auto mb-10 max-w-2xl text-xl {style["muted"]}">
          {sub}
        </p>
        <div className="flex flex-col items-center gap-4 sm:flex-row sm:justify-center">
          <a href="{primary_cta.get("url", "#")}" className="rounded-lg {style["btn"]} px-8 py-3 text-lg font-semibold transition-colors">
            {primary_cta.get("text", "Get Started")}
          </a>{secondary_jsx}
        </div>
      </div>
    </section>
  );
}}'''


def tsx_features(features: Dict[str, Any], style: Dict[str, str]) -> str:
    title = features.get("title", "Features")
    subtitle = features.get("subtitle", "")
    items = features.get("items", [])
    cards_jsx = "\n        ".join(
        f'''<div className="{style["card_bg"]} rounded-xl p-8">
          <div className="mb-4 text-3xl">{f.get("icon", "")}</div>
          <h3 className="mb-3 text-xl font-semibold {style["text"]}">{f.get("title", "")}</h3>
          <p className="{style["muted"]}">{f.get("description", "")}</p>
        </div>'''
        for f in items
    )
    return f'''function Features() {{
  return (
    <section className="{style["section_alt"]} px-6 py-24">
      <div className="mx-auto max-w-7xl">
        <h2 className="mb-4 text-center text-4xl font-bold {style["text"]}">{title}</h2>
        <p className="mx-auto mb-16 max-w-2xl text-center text-lg {style["muted"]}">{subtitle}</p>
        <div className="grid gap-8 md:grid-cols-2 lg:grid-cols-3">
        {cards_jsx}
        </div>
      </div>
    </section>
  );
}}'''


def tsx_testimonials(testimonials: Dict[str, Any], style: Dict[str, str]) -> str:
    title = testimonials.get("title", "What Our Customers Say")
    items = testimonials.get("items", [])
    if not items:
        return ""
    cards_jsx = "\n        ".join(
        f'''<div className="rounded-xl border {style["border"]} p-8">
          <p className="mb-6 text-lg italic {style["muted"]}">"{t.get("quote", "")}"</p>
          <div>
            <p className="font-semibold {style["text"]}">{t.get("name", "")}</p>
            <p className="text-sm {style["muted"]}">{t.get("title", "")}, {t.get("company", "")}</p>
          </div>
        </div>'''
        for t in items
    )
    return f'''function Testimonials() {{
  return (
    <section className="px-6 py-24 {style["bg"]}">
      <div className="mx-auto max-w-7xl">
        <h2 className="mb-16 text-center text-4xl font-bold {style["text"]}">{title}</h2>
        <div className="grid gap-8 md:grid-cols-2 lg:grid-cols-3">
        {cards_jsx}
        </div>
      </div>
    </section>
  );
}}'''


def tsx_pricing(pricing: Dict[str, Any], style: Dict[str, str]) -> str:
    title = pricing.get("title", "Pricing")
    plans = pricing.get("plans", [])
    if not plans:
        return ""
    accent = style["accent"]
    cards = []
    for p in plans:
        featured = p.get("featured", False)
        border_cls = f"border-2 border-{accent}-500 ring-4 ring-{accent}-500/20" if featured else f"border {style['border']}"
        badge = f'\n            <div className="absolute -top-3 left-1/2 -translate-x-1/2 rounded-full bg-{accent}-600 px-4 py-1 text-xs font-semibold text-white">Most Popular</div>' if featured else ""
        features_jsx = "\n              ".join(
            f'<li className="flex items-center gap-2 py-2"><span className="text-{accent}-500 font-bold">&#10003;</span> {feat}</li>'
            for feat in p.get("features", [])
        )
        cards.append(f'''<div className="relative rounded-2xl {border_cls} {style["card_bg"]} p-8 text-center">{badge}
            <h3 className="mb-2 text-xl font-semibold {style["text"]}">{p.get("name", "")}</h3>
            <div className="my-6 text-5xl font-extrabold {style["text"]}">${p.get("price", "0")}<span className="text-base font-normal {style["muted"]}">/mo</span></div>
            <p className="{style["muted"]} mb-6">{p.get("description", "")}</p>
            <ul className="mb-8 space-y-1 text-left {style["muted"]}">
              {features_jsx}
            </ul>
            <a href="{p.get("cta_url", "#")}" className="block w-full rounded-lg {style["btn"]} py-3 text-center font-semibold transition-colors">
              {p.get("cta_text", "Choose Plan")}
            </a>
          </div>''')
    cards_jsx = "\n        ".join(cards)
    return f'''function Pricing() {{
  return (
    <section className="{style["section_alt"]} px-6 py-24">
      <div className="mx-auto max-w-5xl">
        <h2 className="mb-16 text-center text-4xl font-bold {style["text"]}">{title}</h2>
        <div className="grid gap-8 lg:grid-cols-{min(len(plans), 3)}">
        {cards_jsx}
        </div>
      </div>
    </section>
  );
}}'''


def tsx_cta(cta: Dict[str, Any], style: Dict[str, str]) -> str:
    accent = style["accent"]
    return f'''function CTASection() {{
  return (
    <section className="bg-{accent}-600 px-6 py-24 text-center text-white">
      <div className="mx-auto max-w-3xl">
        <h2 className="mb-4 text-4xl font-bold">{cta.get("headline", "Ready to get started?")}</h2>
        <p className="mb-10 text-xl opacity-90">{cta.get("subheadline", "")}</p>
        <a href="{cta.get("url", "#")}" className="rounded-lg bg-white px-8 py-3 text-lg font-semibold text-{accent}-600 transition-colors hover:bg-gray-100">
          {cta.get("text", "Start Free Trial")}
        </a>
      </div>
    </section>
  );
}}'''


def tsx_footer(config: Dict[str, Any], style: Dict[str, str]) -> str:
    brand = config.get("brand", "Company")
    year = datetime.now().year
    footer_text = config.get("footer_text", f"{year} {brand}. All rights reserved.")
    return f'''function Footer() {{
  return (
    <footer className="border-t {style["border"]} {style["bg"]} px-6 py-10 text-center {style["muted"]}">
      <p>&copy; {footer_text}</p>
    </footer>
  );
}}'''


def generate_tsx(config: Dict[str, Any]) -> str:
    """Generate complete Next.js/React TSX landing page with Tailwind CSS."""
    style_name = config.get("design_style", "clean-minimal")
    style = DESIGN_STYLES.get(style_name, DESIGN_STYLES["clean-minimal"])

    components = []
    component_names = []

    components.append(tsx_nav(config, style))
    component_names.append("Navbar")

    if config.get("hero"):
        components.append(tsx_hero(config["hero"], style))
        component_names.append("Hero")

    if config.get("features"):
        components.append(tsx_features(config["features"], style))
        component_names.append("Features")

    if config.get("testimonials") and config["testimonials"].get("items"):
        components.append(tsx_testimonials(config["testimonials"], style))
        component_names.append("Testimonials")

    if config.get("pricing") and config["pricing"].get("plans"):
        components.append(tsx_pricing(config["pricing"], style))
        component_names.append("Pricing")

    if config.get("cta"):
        components.append(tsx_cta(config["cta"], style))
        component_names.append("CTASection")

    components.append(tsx_footer(config, style))
    component_names.append("Footer")

    title = config.get("title", "Landing Page")
    meta_desc = config.get("meta_description", "")

    page_body = "\n      ".join(f"<{name} />" for name in component_names)
    all_components = "\n\n".join(components)

    return f'''// Generated by Landing Page Scaffolder — {datetime.now().strftime("%Y-%m-%d")}
// Stack: Next.js 14+ App Router, React, Tailwind CSS
// Design style: {style_name}

import type {{ Metadata }} from "next";

export const metadata: Metadata = {{
  title: "{title}",
  description: "{meta_desc}",
  openGraph: {{
    title: "{title}",
    description: "{meta_desc}",
    type: "website",
  }},
}};

{all_components}

export default function LandingPage() {{
  return (
    <main>
      {page_body}
    </main>
  );
}}
'''


# ---------------------------------------------------------------------------
# HTML generators (existing)
# ---------------------------------------------------------------------------

def generate_css(config: Dict[str, Any]) -> str:
    """Generate responsive CSS from config theme."""
    theme = config.get("theme", {})
    primary = theme.get("primary_color", "#2563eb")
    secondary = theme.get("secondary_color", "#1e40af")
    bg = theme.get("background", "#ffffff")
    text_color = theme.get("text_color", "#1f2937")
    font = theme.get("font", "Inter, system-ui, -apple-system, sans-serif")

    return f"""
    * {{ margin: 0; padding: 0; box-sizing: border-box; }}
    body {{ font-family: {font}; color: {text_color}; background: {bg}; line-height: 1.6; }}
    .container {{ max-width: 1200px; margin: 0 auto; padding: 0 24px; }}
    nav {{ padding: 16px 0; border-bottom: 1px solid #e5e7eb; position: sticky; top: 0; background: {bg}; z-index: 100; }}
    nav .container {{ display: flex; justify-content: space-between; align-items: center; }}
    .nav-logo {{ font-size: 1.5rem; font-weight: 700; color: {primary}; text-decoration: none; }}
    .nav-links {{ display: flex; gap: 24px; list-style: none; }}
    .nav-links a {{ text-decoration: none; color: {text_color}; font-weight: 500; }}
    .nav-cta {{ background: {primary}; color: white; padding: 8px 20px; border-radius: 6px; text-decoration: none; font-weight: 600; }}
    .hero {{ padding: 80px 0; text-align: center; }}
    .hero h1 {{ font-size: 3.5rem; font-weight: 800; line-height: 1.1; margin-bottom: 24px; max-width: 800px; margin-left: auto; margin-right: auto; }}
    .hero p {{ font-size: 1.25rem; color: #6b7280; max-width: 600px; margin: 0 auto 32px; }}
    .hero-cta {{ display: inline-flex; gap: 16px; }}
    .btn-primary {{ background: {primary}; color: white; padding: 14px 32px; border-radius: 8px; text-decoration: none; font-weight: 600; font-size: 1.1rem; }}
    .btn-secondary {{ background: transparent; color: {primary}; padding: 14px 32px; border-radius: 8px; text-decoration: none; font-weight: 600; font-size: 1.1rem; border: 2px solid {primary}; }}
    .features {{ padding: 80px 0; background: #f9fafb; }}
    .section-title {{ text-align: center; font-size: 2.5rem; font-weight: 700; margin-bottom: 16px; }}
    .section-subtitle {{ text-align: center; color: #6b7280; font-size: 1.1rem; margin-bottom: 48px; max-width: 600px; margin-left: auto; margin-right: auto; }}
    .features-grid {{ display: grid; grid-template-columns: repeat(auto-fit, minmax(300px, 1fr)); gap: 32px; }}
    .feature-card {{ background: white; padding: 32px; border-radius: 12px; box-shadow: 0 1px 3px rgba(0,0,0,0.1); }}
    .feature-icon {{ font-size: 2rem; margin-bottom: 16px; }}
    .feature-card h3 {{ font-size: 1.25rem; margin-bottom: 12px; }}
    .feature-card p {{ color: #6b7280; }}
    .testimonials {{ padding: 80px 0; }}
    .testimonials-grid {{ display: grid; grid-template-columns: repeat(auto-fit, minmax(350px, 1fr)); gap: 24px; }}
    .testimonial-card {{ padding: 32px; border: 1px solid #e5e7eb; border-radius: 12px; }}
    .testimonial-text {{ font-size: 1.1rem; font-style: italic; margin-bottom: 20px; }}
    .testimonial-author {{ display: flex; align-items: center; gap: 12px; }}
    .author-info strong {{ display: block; }}
    .author-info span {{ color: #6b7280; font-size: 0.9rem; }}
    .pricing {{ padding: 80px 0; background: #f9fafb; }}
    .pricing-grid {{ display: grid; grid-template-columns: repeat(auto-fit, minmax(300px, 1fr)); gap: 24px; max-width: 900px; margin: 0 auto; }}
    .pricing-card {{ background: white; padding: 32px; border-radius: 12px; border: 2px solid #e5e7eb; text-align: center; }}
    .pricing-card.featured {{ border-color: {primary}; position: relative; }}
    .pricing-card.featured::before {{ content: "Most Popular"; position: absolute; top: -12px; left: 50%; transform: translateX(-50%); background: {primary}; color: white; padding: 4px 16px; border-radius: 20px; font-size: 0.8rem; font-weight: 600; }}
    .pricing-name {{ font-size: 1.25rem; font-weight: 600; margin-bottom: 8px; }}
    .pricing-price {{ font-size: 3rem; font-weight: 800; margin: 16px 0; }}
    .pricing-price span {{ font-size: 1rem; font-weight: 400; color: #6b7280; }}
    .pricing-features {{ list-style: none; text-align: left; margin: 24px 0; }}
    .pricing-features li {{ padding: 8px 0; border-bottom: 1px solid #f3f4f6; }}
    .pricing-features li::before {{ content: "\\2713 "; color: {primary}; font-weight: 700; }}
    .cta-section {{ padding: 80px 0; text-align: center; background: {primary}; color: white; }}
    .cta-section h2 {{ font-size: 2.5rem; margin-bottom: 16px; }}
    .cta-section p {{ font-size: 1.1rem; opacity: 0.9; margin-bottom: 32px; }}
    .btn-white {{ background: white; color: {primary}; padding: 14px 32px; border-radius: 8px; text-decoration: none; font-weight: 600; font-size: 1.1rem; }}
    footer {{ padding: 40px 0; border-top: 1px solid #e5e7eb; color: #6b7280; text-align: center; }}
    @media (max-width: 768px) {{
        .hero h1 {{ font-size: 2.25rem; }}
        .hero-cta {{ flex-direction: column; align-items: center; }}
        .nav-links {{ display: none; }}
        .features-grid {{ grid-template-columns: 1fr; }}
        .pricing-grid {{ grid-template-columns: 1fr; }}
    }}
    """


def render_nav(config: Dict[str, Any]) -> str:
    brand = escape(config.get("brand", "Brand"))
    nav_links = config.get("nav_links", [])
    cta = config.get("nav_cta", {"text": "Get Started", "url": "#"})
    links = "\n".join(
        f'<li><a href="{escape(l.get("url", "#"))}">{escape(l.get("text", ""))}</a></li>'
        for l in nav_links
    )
    return f"""
    <nav><div class="container">
        <a href="#" class="nav-logo">{brand}</a>
        <ul class="nav-links">{links}</ul>
        <a href="{escape(cta.get('url', '#'))}" class="nav-cta">{escape(cta.get('text', 'Get Started'))}</a>
    </div></nav>"""


def render_hero(hero: Dict[str, Any]) -> str:
    h1 = escape(hero.get("headline", "Your Headline Here"))
    sub = escape(hero.get("subheadline", ""))
    primary_cta = hero.get("primary_cta", {"text": "Get Started", "url": "#"})
    secondary_cta = hero.get("secondary_cta", None)
    cta_html = f'<a href="{escape(primary_cta.get("url", "#"))}" class="btn-primary">{escape(primary_cta.get("text", "Get Started"))}</a>'
    if secondary_cta:
        cta_html += f'\n<a href="{escape(secondary_cta.get("url", "#"))}" class="btn-secondary">{escape(secondary_cta.get("text", "Learn More"))}</a>'
    return f"""
    <section class="hero"><div class="container">
        <h1>{h1}</h1>
        <p>{sub}</p>
        <div class="hero-cta">{cta_html}</div>
    </div></section>"""


def render_features(features: Dict[str, Any]) -> str:
    title = escape(features.get("title", "Features"))
    subtitle = escape(features.get("subtitle", ""))
    items = features.get("items", [])
    cards = "\n".join(f"""
        <div class="feature-card">
            <div class="feature-icon">{escape(f.get('icon', ''))}</div>
            <h3>{escape(f.get('title', ''))}</h3>
            <p>{escape(f.get('description', ''))}</p>
        </div>""" for f in items)
    return f"""
    <section class="features"><div class="container">
        <h2 class="section-title">{title}</h2>
        <p class="section-subtitle">{subtitle}</p>
        <div class="features-grid">{cards}</div>
    </div></section>"""


def render_testimonials(testimonials: Dict[str, Any]) -> str:
    title = escape(testimonials.get("title", "What Our Customers Say"))
    items = testimonials.get("items", [])
    if not items:
        return ""
    cards = "\n".join(f"""
        <div class="testimonial-card">
            <p class="testimonial-text">"{escape(t.get('quote', ''))}"</p>
            <div class="testimonial-author">
                <div class="author-info">
                    <strong>{escape(t.get('name', ''))}</strong>
                    <span>{escape(t.get('title', ''))}, {escape(t.get('company', ''))}</span>
                </div>
            </div>
        </div>""" for t in items)
    return f"""
    <section class="testimonials"><div class="container">
        <h2 class="section-title">{title}</h2>
        <div class="testimonials-grid">{cards}</div>
    </div></section>"""


def render_pricing(pricing: Dict[str, Any]) -> str:
    title = escape(pricing.get("title", "Pricing"))
    plans = pricing.get("plans", [])
    if not plans:
        return ""
    cards = "\n".join(f"""
        <div class="pricing-card {'featured' if p.get('featured') else ''}">
            <div class="pricing-name">{escape(p.get('name', ''))}</div>
            <div class="pricing-price">${escape(str(p.get('price', '0')))}<span>/mo</span></div>
            <p>{escape(p.get('description', ''))}</p>
            <ul class="pricing-features">
                {"".join(f'<li>{escape(f)}</li>' for f in p.get('features', []))}
            </ul>
            <a href="{escape(p.get('cta_url', '#'))}" class="btn-primary">{escape(p.get('cta_text', 'Choose Plan'))}</a>
        </div>""" for p in plans)
    return f"""
    <section class="pricing"><div class="container">
        <h2 class="section-title">{title}</h2>
        <div class="pricing-grid">{cards}</div>
    </div></section>"""


def render_cta(cta: Dict[str, Any]) -> str:
    return f"""
    <section class="cta-section"><div class="container">
        <h2>{escape(cta.get('headline', 'Ready to get started?'))}</h2>
        <p>{escape(cta.get('subheadline', ''))}</p>
        <a href="{escape(cta.get('url', '#'))}" class="btn-white">{escape(cta.get('text', 'Start Free Trial'))}</a>
    </div></section>"""


def generate_html(config: Dict[str, Any]) -> str:
    """Generate complete HTML landing page."""
    title = escape(config.get("title", "Landing Page"))
    css = generate_css(config)
    sections = []
    sections.append(render_nav(config))
    if config.get("hero"):
        sections.append(render_hero(config["hero"]))
    if config.get("features"):
        sections.append(render_features(config["features"]))
    if config.get("testimonials"):
        sections.append(render_testimonials(config["testimonials"]))
    if config.get("pricing"):
        sections.append(render_pricing(config["pricing"]))
    if config.get("cta"):
        sections.append(render_cta(config["cta"]))
    sections.append(f"""
    <footer><div class="container">
        <p>{escape(config.get('footer_text', f'{datetime.now().year} {config.get("brand", "Company")}. All rights reserved.'))}</p>
    </div></footer>""")
    return f"""<!DOCTYPE html>
<html lang="en">
<head>
    <meta charset="UTF-8">
    <meta name="viewport" content="width=device-width, initial-scale=1.0">
    <title>{title}</title>
    <meta name="description" content="{escape(config.get('meta_description', ''))}">
    <style>{css}</style>
</head>
<body>
{"".join(sections)}
</body>
</html>"""


def main():
    parser = argparse.ArgumentParser(
        description="Generate landing pages as HTML or Next.js TSX with Tailwind CSS"
    )
    parser.add_argument("input", help="Path to page config JSON")
    parser.add_argument(
        "--format", choices=["html", "tsx", "json"], default="tsx",
        help="Output format: tsx (Next.js + Tailwind), html (standalone), json (metadata)"
    )
    parser.add_argument("--output", type=str, default=None, help="Output file path")

    args = parser.parse_args()

    with open(args.input) as f:
        config = json.load(f)

    if args.format == "json":
        output = json.dumps({
            "generated_at": datetime.now().isoformat(),
            "config": config,
            "formats_available": ["html", "tsx"],
            "sections": [k for k in ["nav", "hero", "features", "testimonials", "pricing", "cta", "footer"]
                         if config.get(k) or k in ("nav", "footer")]
        }, indent=2)
    elif args.format == "tsx":
        output = generate_tsx(config)
    else:
        output = generate_html(config)

    if args.output:
        with open(args.output, "w") as f:
            f.write(output)
        print(f"Landing page written to {args.output}")
    else:
        print(output)


if __name__ == "__main__":
    main()
