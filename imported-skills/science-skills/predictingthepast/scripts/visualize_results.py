# Copyright 2026 Google LLC
#
# Licensed under the Apache License, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# You may obtain a copy of the License at
#
#     http://www.apache.org/licenses/LICENSE-2.0
#
# Unless required by applicable law or agreed to in writing, software
# distributed under the License is distributed on an "AS IS" BASIS,
# WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
# See the License for the specific language governing permissions and
# limitations under the License.

"""Generate an interactive HTML from Predicting The Past JSON outputs.

Reads the combined JSON produced by run_inference.py and renders a single
self-contained HTML file with:
  - Geographical attribution (horizontal bar chart + saliency map)
  - Chronological attribution (histogram + mean/max markers + saliency map)
  - Restoration hypotheses (monospace table with highlighted restored chars)
  - Restoration saliency map (step-by-step per-character saliency)
  - Contextualization parallels (card grid with metadata)

Usage:
  uv run visualize_results.py --input results.json --output dashboard.html
  cat results.json | uv run visualize_results.py --output dashboard.html
"""

# /// script
# requires-python = ">=3.10"
# ///

import argparse
import html
import json
import sys
from typing import Any


def bce_ce(year: int | None) -> str:
  if year is None:
    return ''
  if year < 0:
    return f'{abs(year)} BCE'
  if year > 0:
    return f'{year} CE'
  return '0'


def saliency_spans(
    text: str, saliency: list[float], color: str = '248,127,195'
) -> str:
  parts = []
  for i, ch in enumerate(text):
    score = saliency[i] if i < len(saliency) else 0.0
    safe = html.escape(ch) if ch != ' ' else '&nbsp;'
    parts.append(
        f'<span style="background:rgba({color},{score:.2f})" '
        f'title="saliency {score:.3f}">{safe}</span>'
    )
  return ''.join(parts)


def render_attribution_section(attr: dict[str, Any] | None) -> str:
  """Renders the geographical and chronological attribution HTML section."""
  if not attr:
    return ''

  # Average Attribution already handled by run_inference.py if multi-window
  loc_rows = ''
  locations = attr.get('locations', [])
  top10 = locations[:10]
  max_score = max((l.get('score', 0) for l in top10), default=1) or 1

  for loc in top10:
    name = loc.get('location_name', f"Region {loc.get('location_id', '?')}")
    score = loc.get('score', 0)
    pct = score * 100
    bar_width = (score / max_score) * 100
    loc_rows += f"""
      <tr>
        <td class="region-name">{html.escape(name)}</td>
        <td class="bar-cell">
          <div class="bar-bg"><div class="bar-fill" style="width:{bar_width:.1f}%"></div></div>
        </td>
        <td class="score-val">{pct:.1f}%</td>
      </tr>"""

  top_year = attr.get('top_year', '')
  avg_year = attr.get('weighted_average_year', '')

  year_dist = attr.get('year_distribution', {})
  year_labels = []
  year_values = []
  if year_dist:
    for k in sorted(year_dist.keys(), key=int):
      year_labels.append(bce_ce(int(k)))
      year_values.append(year_dist[k] * 100)

  avg_label = bce_ce(avg_year) if avg_year else None
  top_label = bce_ce(top_year) if top_year else None

  date_sal_html = ''
  if 'date_saliency' in attr and 'input_text' in attr:
    date_sal_html = f"""
    <h3>Chronological attribution saliency map</h3>
    <p class="desc">Purple shading highlights which characters most influenced the dating prediction.</p>
    <div class="saliency-box">{saliency_spans(attr['input_text'], attr['date_saliency'])}</div>"""

  loc_sal_html = ''
  if 'location_saliency' in attr and 'input_text' in attr:
    loc_sal_html = f"""
    <h3>Geographical attribution saliency map</h3>
    <p class="desc">Purple shading highlights which characters most influenced the geographical prediction.</p>
    <div class="saliency-box">{saliency_spans(attr['input_text'], attr['location_saliency'])}</div>"""

  year_chart_js = ''
  if year_labels:
    labels_json = json.dumps(year_labels)
    values_json = json.dumps(year_values)
    avg_label_json = json.dumps(avg_label)
    top_label_json = json.dumps(top_label)
    year_chart_js = f"""
    <script>
    google.charts.load('current', {{'packages': ['corechart']}});
    google.charts.setOnLoadCallback(function() {{
      var labels = {labels_json};
      var values = {values_json};
      var avgLabel = {avg_label_json};
      var topLabel = {top_label_json};

      function decadeRange(lbl) {{
        var m = lbl.match(/^(\\d+)\\s*(BCE|CE)$/);
        if (!m) return lbl;
        var mid = parseInt(m[1], 10);
        var era = m[2];
        var lo = mid - 5, hi = mid + 5;
        if (era === 'BCE') return hi + '-' + lo + ' ' + era;
        return lo + '-' + hi + ' ' + era;
      }}
      var rows = [];
      for (var i = 0; i < labels.length; i++) {{
        var color = '#fdcc75';
        if (avgLabel && labels[i] === avgLabel) color = '#da2b2f';
        if (topLabel && labels[i] === topLabel) color = '#1a73e8';
        rows.push([labels[i], values[i], color,
          'Decade: ' + decadeRange(labels[i]) + '\\nProb: ' + values[i].toFixed(1) + '%']);
      }}

      var data = new google.visualization.DataTable();
      data.addColumn('string', 'Date');
      data.addColumn('number', 'Probability (%)');
      data.addColumn({{type: 'string', role: 'style'}});
      data.addColumn({{type: 'string', role: 'tooltip'}});
      data.addRows(rows);

      var chart = new google.visualization.ColumnChart(
        document.getElementById('chronoChart'));
      chart.draw(data, {{
        legend: 'none',
        hAxis: {{title: 'Date (years)', showTextEvery: Math.ceil(labels.length / 20)}},
        vAxis: {{title: 'Probability (%)', minValue: 0}},
        chartArea: {{width: '95%', height: '70%'}},
        bar: {{groupWidth: '95%'}},
        colors: ['#fdcc75'],
      }});
    }});
    </script>"""

  return f"""
  <section>
    <h2>Geographical Attribution</h2>
    <p class="desc">Top-10 geographical attribution hypotheses ranked by probability.</p>
    <table class="geo-table">
      <tbody>{loc_rows}
      </tbody>
    </table>
    {loc_sal_html}
  </section>

  <section>
    <h2>Chronological Attribution</h2>
    <p class="desc">Date distribution over decades between 800 BCE and 800 CE.
    Top year: <strong>{bce_ce(top_year)}</strong>, weighted average: <strong>{bce_ce(avg_year)}</strong>.</p>
    <div class="chart-container"><div id="chronoChart" style="width:100%;height:350px;"></div></div>
    {year_chart_js}
    {date_sal_html}
  </section>"""


def render_restoration_window(
    restore_data: dict[str, Any] | None, window_idx: int | None = None
) -> str:
  """Renders a single restoration window with hypotheses and saliency."""
  if not restore_data:
    return ''

  missing = set(restore_data.get('missing', []))
  input_text = restore_data.get('input_text', '')

  input_chars = ''
  for i, ch in enumerate(input_text):
    safe = html.escape(ch) if ch != ' ' else '&nbsp;'
    if i in missing:
      input_chars += f'<span class="pred">{safe}</span>'
    else:
      input_chars += safe

  pred_rows = ''
  for idx, pred in enumerate(restore_data.get('predictions', [])[:20]):
    restored = set(pred.get('restored', []))
    score = pred.get('score', 0)
    text = pred.get('text', '')
    chars = ''
    for i, ch in enumerate(text):
      safe = html.escape(ch) if ch != ' ' else '&nbsp;'
      if i in restored:
        chars += f'<span class="pred">{safe}</span>'
      else:
        chars += safe
    pred_rows += f"""
      <tr>
        <td class="header header-1">Hypothesis {idx+1}:</td>
        <td class="header header-2">{score*100:.1f}%</td>
        <td>{chars}</td>
      </tr>"""

  sal_rows = ''
  for sal_entry in restore_data.get('prediction_saliency', []):
    sal_text = sal_entry.get('text', '')
    restored_idx = sal_entry.get('restored_idx', -1)
    sal_values = sal_entry.get('saliency', [])
    predicted_char = (
        sal_text[restored_idx] if 0 <= restored_idx < len(sal_text) else '?'
    )
    if predicted_char == ' ':
      predicted_char = '⎵'

    chars = ''
    for i, ch in enumerate(sal_text):
      safe = html.escape(ch) if ch != ' ' else '&nbsp;'
      if i == restored_idx:
        chars += f'<span class="pred restored-pos">{safe}</span>'
      else:
        alpha = sal_values[i] if i < len(sal_values) else 0.0
        chars += (
            f'<span style="background:rgba(171,71,188,{alpha:.2f})">'
            f'{safe}</span>'
        )

    step_num = len(sal_rows.split('<tr>')) - 1
    sal_rows += f"""
      <tr>
        <td class="header header-1">Step {step_num + 1}:</td>
        <td class="header header-2">{html.escape(predicted_char)}</td>
        <td>{chars}</td>
      </tr>"""

  sal_section = ''
  if sal_rows:
    sal_section = f"""
    <h4>Restoration Saliency Map</h4>
    <p class="desc">For each character predicted in the top hypothesis, purple
    shading shows which input characters most influenced that step.</p>
    <div class="mono-scroll">
    <table class="mono-table" cellspacing="0">
      <tr>
        <td colspan="2" class="header header-2col">Input text:</td>
        <td>{input_chars}</td>
      </tr>{sal_rows}
    </table>
    </div>"""

  title_suffix = f' (Window {window_idx + 1})' if window_idx is not None else ''
  return f"""
    <div class="window-block">
    <h3>Restoration Hypotheses{title_suffix}</h3>
    <div class="mono-scroll">
    <table class="mono-table" cellspacing="0">
      <tr>
        <td colspan="2" class="header header-2col">Input text:</td>
        <td>{input_chars}</td>
      </tr>{pred_rows}
    </table>
    </div>
    {sal_section}
    </div>"""


def render_restoration_section(restore_data):
  """Renders the full restoration section, handling single or multi-window."""
  if not restore_data:
    return ''

  html_content = '<h2>Restoration</h2>'

  if isinstance(restore_data, list):
    # Multi-window
    for i, window_data in enumerate(restore_data):
      if window_data:
        html_content += render_restoration_window(window_data, window_idx=i)
  else:
    # Single window fallback
    html_content += render_restoration_window(restore_data)

  return f'<section>{html_content}</section>'


def render_contextualization_section(
    ctx_data_list: list[dict[str, Any]] | None,
) -> str:
  """Renders the contextualization parallels section as a card grid."""
  if not ctx_data_list:
    return ''

  # Ensure it is a list
  if not isinstance(ctx_data_list, list):
    ctx_data_list = [ctx_data_list]

  cards = ''
  card_index = 0

  for win_idx, ctx_data in enumerate(ctx_data_list):
    if not ctx_data:
      continue

    ids = ctx_data.get('ids', [])
    texts = ctx_data.get('text', [])
    loc_names = ctx_data.get('location_names', [])
    loc_ids = ctx_data.get('location_ids', [])
    date_mins = ctx_data.get('date_min', [])
    date_maxs = ctx_data.get('date_max', [])
    scores = ctx_data.get('score', [])
    partner_links = ctx_data.get('partner_link', [])
    ids_alt = ctx_data.get('ids_alt', [])

    for i in range(len(ids)):
      text = texts[i] if i < len(texts) else ''
      rec_id = ids[i] if i < len(ids) else ''

      province = ''
      if i < len(loc_names) and loc_names[i]:
        province = loc_names[i]
      elif i < len(loc_ids) and loc_ids[i] is not None:
        province = f'Region {loc_ids[i]}'

      d_min = date_mins[i] if i < len(date_mins) else None
      d_max = date_maxs[i] if i < len(date_maxs) else None
      date_str = ''
      if d_min is not None and d_max is not None:
        date_str = f'{bce_ce(d_min)} – {bce_ce(d_max)}'
      elif d_min is not None:
        date_str = f'from {bce_ce(d_min)}'
      elif d_max is not None:
        date_str = f'until {bce_ce(d_max)}'

      score = scores[i] if i < len(scores) else 0
      score_pct = score * 100

      link_html = ''
      if i < len(partner_links) and partner_links[i]:
        link_html = (
            '<div><strong>Source:</strong> '
            f'<a href="{html.escape(partner_links[i])}" target="_blank" '
            'rel="noopener">View on partner site</a></div>'
        )

      alt_html = ''
      if i < len(ids_alt) and ids_alt[i]:
        for key, val in ids_alt[i].items():
          alt_html += (
              f'<div><strong>{html.escape(key)}:</strong> '
              f'{html.escape(str(val))}</div>'
          )

      window_tag = (
          f'<div class="window-tag">Win {win_idx+1}</div>'
          if len(ctx_data_list) > 1
          else ''
      )

      cards += f"""
        <div class="card" id="card-{card_index}">
          {window_tag}
          <div>
            <div class="plus-button" onclick="toggleCard(this)">+</div>
            <p class="card-text">{html.escape(text)}</p>
          </div>
          <div class="metadata">
            <div><strong>Record Number:</strong> {html.escape(str(rec_id))}</div>
            {alt_html}
            <div><strong>Province:</strong> {html.escape(province)}</div>
            <div><strong>Date:</strong> {date_str if date_str else 'Not Available'}</div>
            {link_html}
            <div class="score-bar-container">
              <div class="score-bar" style="width:{score_pct:.0f}%"></div>
            </div>
          </div>
        </div>"""
      card_index += 1

  return f"""
  <section>
    <h2>Parallels (Contextualization)</h2>
    <p class="desc">Most relevant contextual parallels from the corpus, ranked by similarity.</p>
    <div class="results-grid">{cards}
    </div>
  </section>"""


def build_html(data: dict[str, Any]) -> str:
  """Assembles the HTML from the inference data."""
  attr = data.get('attribution')
  restore = data.get('restoration')
  ctx = data.get('contextualize')
  num_windows = data.get('num_windows', 1)

  window_note = ''
  if num_windows > 1:
    window_note = (
        f'<p class="window-note">Text was split into {num_windows} '
        'overlapping windows; attribution scores are averaged.</p>'
    )

  attribution_html = render_attribution_section(attr)
  restoration_html = render_restoration_section(restore)
  ctx_html = render_contextualization_section(ctx)

  return f"""<!DOCTYPE html>
<html lang="en">
<head>
<meta charset="UTF-8">
<meta name="viewport" content="width=device-width, initial-scale=1.0">
<title>Predicting The Past — Results Dashboard</title>
<link rel="preconnect" href="https://fonts.googleapis.com">
<link rel="preconnect" href="https://fonts.gstatic.com" crossorigin>
<link href="https://fonts.googleapis.com/css2?family=Roboto+Mono:wght@400&family=Roboto:wght@300;400;700&display=swap" rel="stylesheet">
<script src="https://www.gstatic.com/charts/loader.js"></script>
<style>
* {{ box-sizing: border-box; margin: 0; padding: 0; }}
body {{ font-family: 'Roboto', sans-serif; color: #212529; background: #f8f9fa; padding: 24px; line-height: 1.6; }}
h1 {{ font-weight: 300; font-size: 2em; margin-bottom: 8px; }}
h2 {{ font-weight: 400; font-size: 1.5em; margin: 0 0 8px; padding-bottom: 8px; border-bottom: 2px solid #e9ecef; }}
h3 {{ font-weight: 400; font-size: 1.15em; margin: 24px 0 8px; color: #495057; }}
h4 {{ font-weight: 400; font-size: 1.0em; margin: 16px 0 8px; color: #6c757d; }}
.desc {{ color: #6c757d; font-size: 14px; margin-bottom: 16px; }}
.window-note {{ background: #fff3cd; padding: 8px 16px; border-radius: 4px; font-size: 14px; margin-bottom: 16px; }}
section {{ background: white; border-radius: 8px; padding: 24px; margin-bottom: 24px; box-shadow: 0 1px 3px rgba(0,0,0,0.05); }}
.window-block {{ border-bottom: 1px dotted #e9ecef; padding-bottom: 16px; margin-bottom: 16px; }}
.window-block:last-child {{ border-bottom: none; }}

/* Geo bar chart */
.geo-table {{ width: 100%; max-width: 600px; border-collapse: collapse; }}
.geo-table td {{ padding: 6px 8px; vertical-align: middle; }}
.region-name {{ font-size: 14px; white-space: nowrap; width: 160px; text-align: right; padding-right: 12px !important; }}
.bar-cell {{ width: 100%; }}
.bar-bg {{ background: #e9ecef; height: 20px; border-radius: 4px; overflow: hidden; }}
.bar-fill {{ background: #da2b2f; height: 100%; border-radius: 4px; transition: width 0.3s; }}
.score-val {{ font-size: 13px; color: #6c757d; white-space: nowrap; width: 50px; }}

/* Chrono chart */
.chart-container {{ width: 100%; margin: 16px 0; }}

/* Saliency */
.saliency-box {{ font-family: 'Roboto Mono', monospace; font-size: 15px; padding: 16px; border: 1px solid #e9ecef; border-radius: 4px; background: white; word-wrap: break-word; line-height: 1.8; margin: 8px 0 16px; }}

/* Restoration table */
.mono-scroll {{ overflow-x: auto; margin: 8px 0 16px; }}
.mono-table {{ font-family: 'Roboto Mono', monospace; font-size: 14px; white-space: nowrap; table-layout: fixed; }}
.mono-table td {{ border-bottom: 1px solid #ccc; padding: 4px 0; }}
.mono-table td.header {{ font-family: 'Roboto', sans-serif; position: sticky; background: white; }}
.header-1 {{ width: 120px; min-width: 120px; left: 0; text-align: right; padding-right: 8px !important; }}
.header-2 {{ left: 120px; width: 50px; min-width: 50px; max-width: 50px; text-align: center; padding-right: 5px !important; }}
.header-2col {{ width: 170px; min-width: 170px; left: 0; text-align: right; padding-right: 8px !important; }}
.mono-table td:not(.header) {{ border-left: 1px solid #ddd; padding-left: 5px; }}
.pred {{ background: #ddd; }}
.restored-pos {{ background: #bdb; font-weight: bold; }}
.mono-table tr:hover .header-2 {{ background: #bdb; font-weight: bold; }}
.mono-table tr:hover .restored-pos {{ background: #bdb; }}

/* Parallels cards */
.results-grid {{ display: grid; grid-template-columns: repeat(auto-fill, minmax(300px, 1fr)); gap: 20px; }}
.card {{ background: white; border: 1px solid #dee2e6; border-radius: 8px; padding: 20px; display: flex; flex-direction: column; position: relative; box-shadow: 0 1px 3px rgba(0,0,0,0.05); transition: box-shadow 0.2s; }}
.card:hover {{ box-shadow: 0 4px 12px rgba(0,0,0,0.1); }}
.card-text {{ font-size: 15px; line-height: 1.5; color: #343a40; margin: 0 0 16px; height: 72px; overflow: hidden; }}
.card.is-expanded .card-text {{ height: auto; }}
.plus-button {{ position: absolute; top: 12px; right: 12px; width: 28px; height: 28px; border-radius: 50%; border: 1px solid #ced4da; background: white; color: #495057; font-size: 20px; display: flex; align-items: center; justify-content: center; cursor: pointer; user-select: none; }}
.window-tag {{ position: absolute; top: 12px; left: 12px; background: #e9ecef; padding: 2px 6px; border-radius: 4px; font-size: 11px; color: #6c757d; font-weight: bold; }}
.metadata {{ font-size: 13px; color: #495057; border-top: 1px solid #e9ecef; padding-top: 12px; margin-top: auto; }}
.metadata div {{ margin-bottom: 4px; }}
.metadata strong {{ font-weight: 700; color: #212529; }}
.metadata a {{ color: #007bff; text-decoration: none; }}
.score-bar-container {{ width: 100%; height: 6px; background: #e9ecef; border-radius: 3px; margin-top: 8px; overflow: hidden; }}
.score-bar {{ height: 100%; background: #ffc107; border-radius: 3px; }}
</style>
</head>
<body>

<h1>Predicting The Past — Results</h1>

<section>
<h2>Citation</h2>
<p class="desc">When using these outputs, please cite the corresponding paper:</p>
<p style="font-size:13px;line-height:1.7;color:#495057;">
<strong>Ithaca</strong> (Ancient Greek):<br>
Assael, Y., Sommerschield, T., Shillingford, B. et al.
Restoring and attributing ancient texts using deep neural networks.
<em>Nature</em> 603, 280&ndash;283 (2022).
<a href="https://doi.org/10.1038/s41586-022-04448-z" target="_blank" rel="noopener">https://doi.org/10.1038/s41586-022-04448-z</a>
</p>
<p style="font-size:13px;line-height:1.7;color:#495057;">
<strong>Aeneas</strong> (Latin):<br>
Assael, Y., Sommerschield, T., Cooley, A. et al.
Contextualizing ancient texts with generative neural networks.
<em>Nature</em> 645, 141&ndash;147 (2025).
<a href="https://doi.org/10.1038/s41586-025-09292-5" target="_blank" rel="noopener">https://doi.org/10.1038/s41586-025-09292-5</a>
</p>
<p style="font-size:13px;color:#6c757d;">For more information, visit
<a href="https://predictingthepast.com" target="_blank" rel="noopener">predictingthepast.com</a>.
</p>
</section>

{window_note}
{restoration_html}
{attribution_html}
{ctx_html}

<section>
<h2>Dataset Acknowledgements</h2>
<div style="font-size:13px;line-height:1.7;color:#495057;">
<p style="margin-bottom:8px;">
The Ithaca and Aeneas projects rely on the availability of high-quality datasets
of ancient Greek and Latin inscriptions, respectively. These datasets were built
through centuries of scholarly collection and decades of digital editorial work.
</p>

<p style="margin-bottom:8px;">
<strong>Ithaca</strong> (Ancient Greek): In particular, Ithaca draws on a 2019
version of the Searchable Greek Inscriptions database made available under
&ldquo;Fair Use&rdquo; license by the Packard Humanities Institute, generously supported
by David Packard: <a href="https://inscriptions.packhum.org" target="_blank" rel="noopener">inscriptions.packhum.org</a>.
</p>

<p style="margin-bottom:4px;"><strong>Aeneas</strong> (Latin): Aeneas was trained on data from:</p>
<ul style="margin-left:20px;margin-bottom:8px;">
<li>
<strong>Epigraphic Database Roma (EDR)</strong>: Made available pursuant to a
Creative Commons Attribution 4.0 International License (CC-BY) on
<a href="https://zenodo.org/records/3575495" target="_blank" rel="noopener">Zenodo</a>.
EDR is also available at <a href="http://edr-edr.it" target="_blank" rel="noopener">edr-edr.it</a>.
</li>
<li>
<strong>Epigraphic Database Heidelberg (EDH)</strong>: Made available pursuant to a
Creative Commons Attribution-ShareAlike 4.0 International License (CC-BY-SA) on
<a href="https://zenodo.org/records/3575155" target="_blank" rel="noopener">Zenodo</a>.
EDH is also available at <a href="https://edh.ub.uni-heidelberg.de/" target="_blank" rel="noopener">edh.ub.uni-heidelberg.de</a>.
</li>
<li>
<strong>ETL repository for Epigraphic Database Clauss Slaby (EDCS_ETL)</strong>:
Made available pursuant to a Creative Commons Attribution 4.0 International License (CC-BY) on
<a href="https://zenodo.org/records/7072337" target="_blank" rel="noopener">Zenodo</a>.
EDCS_ETL is also available at <a href="http://www.manfredclauss.de/" target="_blank" rel="noopener">manfredclauss.de</a> and
<a href="https://github.com/sdam-au/EDCS_ETL" target="_blank" rel="noopener">github.com/sdam-au/EDCS_ETL</a>.
</li>
</ul>

<p>
These resources bring together a large proportion of published inscriptions in a
searchable digital format. Any use of these datasets should acknowledge and cite
the original data sources.
</p>
</div>
</section>

<script>
function toggleCard(btn) {{
  const card = btn.closest('.card');
  if (card) {{
    const expanded = card.classList.toggle('is-expanded');
    btn.textContent = expanded ? '−' : '+';
  }}
}}
</script>
</body>
</html>"""


def main():
  parser = argparse.ArgumentParser(
      description='Visualize Predicting The Past inference results as HTML.'
  )
  parser.add_argument(
      '--input',
      default='',
      help='Path to JSON results file. Reads stdin if omitted.',
  )
  parser.add_argument(
      '--output',
      default='',
      help='Path to write HTML dashboard. Prints to stdout if omitted.',
  )
  args = parser.parse_args()

  if args.input:
    with open(args.input, 'r', encoding='utf-8') as f:
      data = json.load(f)
  else:
    data = json.load(sys.stdin)

  dashboard = build_html(data)

  if args.output:
    with open(args.output, 'w', encoding='utf-8') as f:
      f.write(dashboard)
    print(f'Dashboard written to {args.output}', file=sys.stderr)
  else:
    print(dashboard)


if __name__ == '__main__':
  main()
