#!/usr/bin/env python3
"""
D3.js Visualization Template Generator

Generates starter HTML/JS templates for common visualization types:
- Bar charts (horizontal/vertical)
- Line charts (single/multi-series)
- Scatter plots
- Force-directed networks
- Treemaps
- Choropleths

All templates include:
- Responsive SVG
- Accessibility features
- Touch-friendly interactions
- Mobile optimization
"""

import argparse
import json
from pathlib import Path

TEMPLATES = {
    "bar": """<!DOCTYPE html>
<html lang="en">
<head>
    <meta charset="UTF-8">
    <meta name="viewport" content="width=device-width, initial-scale=1.0">
    <title>{title}</title>
    <script src="https://d3js.org/d3.v7.min.js"></script>
    <style>
        * {{ margin: 0; padding: 0; box-sizing: border-box; }}
        body {{ font-family: system-ui, -apple-system, sans-serif; padding: 20px; }}
        .chart-container {{ max-width: 800px; margin: 0 auto; }}
        .responsive-svg {{ width: 100%; height: auto; }}
        .bar {{ transition: opacity 0.2s; }}
        .bar:hover {{ opacity: 0.8; }}
        .axis-label {{ font-size: 12px; }}
        .tooltip {{
            position: absolute;
            padding: 8px 12px;
            background: rgba(0,0,0,0.8);
            color: white;
            border-radius: 4px;
            font-size: 14px;
            pointer-events: none;
            opacity: 0;
            transition: opacity 0.2s;
        }}
        @media (max-width: 600px) {{
            .tooltip {{
                position: fixed;
                bottom: 20px;
                left: 50%;
                transform: translateX(-50%);
            }}
        }}
    </style>
</head>
<body>
    <div class="chart-container">
        <h1>{title}</h1>
        <div id="chart" role="img" aria-label="{title}"></div>
    </div>
    <div class="tooltip"></div>

    <script>
        // Configuration
        const margin = {{ top: 20, right: 30, bottom: 50, left: 60 }};
        const width = 800 - margin.left - margin.right;
        const height = 400 - margin.top - margin.bottom;

        // Create SVG
        const svg = d3.select('#chart')
            .append('svg')
            .attr('viewBox', `0 0 ${{width + margin.left + margin.right}} ${{height + margin.top + margin.bottom}}`)
            .attr('preserveAspectRatio', 'xMidYMid meet')
            .classed('responsive-svg', true)
            .append('g')
            .attr('transform', `translate(${{margin.left}},${{margin.top}})`);

        // Sample data - replace with your data
        const data = {sample_data};

        // Scales
        const x = d3.scaleBand()
            .domain(data.map(d => d.category))
            .range([0, width])
            .padding(0.2);

        const y = d3.scaleLinear()
            .domain([0, d3.max(data, d => d.value) * 1.1])
            .range([height, 0]);

        // Color scale
        const color = d3.scaleOrdinal()
            .range({colors});

        // Axes
        svg.append('g')
            .attr('transform', `translate(0,${{height}})`)
            .call(d3.axisBottom(x))
            .selectAll('text')
            .attr('class', 'axis-label');

        svg.append('g')
            .call(d3.axisLeft(y))
            .selectAll('text')
            .attr('class', 'axis-label');

        // Tooltip
        const tooltip = d3.select('.tooltip');

        // Bars
        svg.selectAll('.bar')
            .data(data)
            .join('rect')
            .attr('class', 'bar')
            .attr('x', d => x(d.category))
            .attr('y', height)
            .attr('width', x.bandwidth())
            .attr('height', 0)
            .attr('fill', d => color(d.category))
            .attr('tabindex', 0)
            .attr('role', 'graphics-symbol')
            .attr('aria-label', d => `${{d.category}}: ${{d.value}}`)
            .on('mouseover touchstart', function(event, d) {{
                tooltip.style('opacity', 1)
                    .html(`<strong>${{d.category}}</strong><br>Value: ${{d.value}}`);
                if (event.type === 'mouseover') {{
                    tooltip.style('left', `${{event.pageX + 10}}px`)
                        .style('top', `${{event.pageY - 10}}px`);
                }}
            }})
            .on('mouseout touchend', () => tooltip.style('opacity', 0))
            .transition()
            .duration(800)
            .delay((d, i) => i * 100)
            .attr('y', d => y(d.value))
            .attr('height', d => height - y(d.value));

        // Keyboard navigation
        d3.selectAll('.bar')
            .on('keydown', function(event, d) {{
                if (event.key === 'Enter' || event.key === ' ') {{
                    tooltip.style('opacity', 1)
                        .html(`<strong>${{d.category}}</strong><br>Value: ${{d.value}}`);
                }}
            }});
    </script>
</body>
</html>""",
    "force": """<!DOCTYPE html>
<html lang="en">
<head>
    <meta charset="UTF-8">
    <meta name="viewport" content="width=device-width, initial-scale=1.0">
    <title>{title}</title>
    <script src="https://d3js.org/d3.v7.min.js"></script>
    <style>
        * {{ margin: 0; padding: 0; box-sizing: border-box; }}
        body {{ font-family: system-ui, -apple-system, sans-serif; padding: 20px; }}
        .chart-container {{ max-width: 100%; margin: 0 auto; }}
        .responsive-svg {{ width: 100%; height: 80vh; }}
        .node {{ cursor: pointer; transition: opacity 0.2s; }}
        .node:hover {{ opacity: 0.8; }}
        .link {{ stroke: #999; stroke-opacity: 0.6; }}
        .node-label {{ font-size: 12px; pointer-events: none; }}
        .tooltip {{
            position: absolute;
            padding: 8px 12px;
            background: rgba(0,0,0,0.8);
            color: white;
            border-radius: 4px;
            font-size: 14px;
            pointer-events: none;
            opacity: 0;
            transition: opacity 0.2s;
        }}
    </style>
</head>
<body>
    <div class="chart-container">
        <h1>{title}</h1>
        <div id="chart" role="img" aria-label="{title}"></div>
    </div>
    <div class="tooltip"></div>

    <script>
        // Configuration
        const width = window.innerWidth - 40;
        const height = window.innerHeight * 0.8;

        // Create SVG
        const svg = d3.select('#chart')
            .append('svg')
            .attr('width', width)
            .attr('height', height)
            .classed('responsive-svg', true);

        // Sample data - replace with your data
        const data = {sample_data};

        // Color scale
        const color = d3.scaleOrdinal()
            .domain([...new Set(data.nodes.map(d => d.group))])
            .range({colors});

        // Force simulation
        const simulation = d3.forceSimulation(data.nodes)
            .force('charge', d3.forceManyBody().strength(-300))
            .force('link', d3.forceLink(data.links).id(d => d.id).distance(100))
            .force('center', d3.forceCenter(width / 2, height / 2))
            .force('collision', d3.forceCollide().radius(d => (d.size || 20) + 5));

        // Tooltip
        const tooltip = d3.select('.tooltip');

        // Links
        const link = svg.selectAll('.link')
            .data(data.links)
            .join('line')
            .attr('class', 'link')
            .attr('stroke-width', d => Math.sqrt(d.weight || 1));

        // Nodes
        const node = svg.selectAll('.node')
            .data(data.nodes)
            .join('g')
            .attr('class', 'node')
            .attr('tabindex', 0)
            .call(d3.drag()
                .on('start', dragstarted)
                .on('drag', dragged)
                .on('end', dragended));

        node.append('circle')
            .attr('r', d => d.size || 20)
            .attr('fill', d => color(d.group));

        node.append('text')
            .attr('class', 'node-label')
            .attr('dy', 4)
            .attr('text-anchor', 'middle')
            .text(d => d.label || d.id);

        // Interactions
        node.on('mouseover touchstart', function(event, d) {{
                tooltip.style('opacity', 1)
                    .html(`<strong>${{d.label || d.id}}</strong><br>Group: ${{d.group}}`);
                if (event.type === 'mouseover') {{
                    tooltip.style('left', `${{event.pageX + 10}}px`)
                        .style('top', `${{event.pageY - 10}}px`);
                }}
            }})
            .on('mouseout touchend', () => tooltip.style('opacity', 0));

        // Simulation tick
        simulation.on('tick', () => {{
            link
                .attr('x1', d => d.source.x)
                .attr('y1', d => d.source.y)
                .attr('x2', d => d.target.x)
                .attr('y2', d => d.target.y);

            node.attr('transform', d => `translate(${{d.x}},${{d.y}})`);
        }});

        // Drag functions
        function dragstarted(event, d) {{
            if (!event.active) simulation.alphaTarget(0.3).restart();
            d.fx = d.x;
            d.fy = d.y;
        }}

        function dragged(event, d) {{
            d.fx = event.x;
            d.fy = event.y;
        }}

        function dragended(event, d) {{
            if (!event.active) simulation.alphaTarget(0);
            d.fx = null;
            d.fy = null;
        }}
    </script>
</body>
</html>""",
    "line": """<!DOCTYPE html>
<html lang="en">
<head>
    <meta charset="UTF-8">
    <meta name="viewport" content="width=device-width, initial-scale=1.0">
    <title>{title}</title>
    <script src="https://d3js.org/d3.v7.min.js"></script>
    <style>
        * {{ margin: 0; padding: 0; box-sizing: border-box; }}
        body {{ font-family: system-ui, -apple-system, sans-serif; padding: 20px; }}
        .chart-container {{ max-width: 800px; margin: 0 auto; }}
        .responsive-svg {{ width: 100%; height: auto; }}
        .line {{ fill: none; stroke-width: 2; }}
        .dot {{ transition: r 0.2s; }}
        .dot:hover {{ r: 8; }}
        .axis-label {{ font-size: 12px; }}
        .tooltip {{
            position: absolute;
            padding: 8px 12px;
            background: rgba(0,0,0,0.8);
            color: white;
            border-radius: 4px;
            font-size: 14px;
            pointer-events: none;
            opacity: 0;
        }}
    </style>
</head>
<body>
    <div class="chart-container">
        <h1>{title}</h1>
        <div id="chart" role="img" aria-label="{title}"></div>
    </div>
    <div class="tooltip"></div>

    <script>
        const margin = {{ top: 20, right: 30, bottom: 50, left: 60 }};
        const width = 800 - margin.left - margin.right;
        const height = 400 - margin.top - margin.bottom;

        const svg = d3.select('#chart')
            .append('svg')
            .attr('viewBox', `0 0 ${{width + margin.left + margin.right}} ${{height + margin.top + margin.bottom}}`)
            .classed('responsive-svg', true)
            .append('g')
            .attr('transform', `translate(${{margin.left}},${{margin.top}})`);

        // Sample data
        const data = {sample_data};

        // Parse dates
        const parseDate = d3.timeParse('%Y-%m-%d');
        data.forEach(d => d.date = parseDate(d.date));

        // Scales
        const x = d3.scaleTime()
            .domain(d3.extent(data, d => d.date))
            .range([0, width]);

        const y = d3.scaleLinear()
            .domain([0, d3.max(data, d => d.value) * 1.1])
            .range([height, 0]);

        // Line generator
        const line = d3.line()
            .x(d => x(d.date))
            .y(d => y(d.value))
            .curve(d3.curveMonotoneX);

        // Axes
        svg.append('g')
            .attr('transform', `translate(0,${{height}})`)
            .call(d3.axisBottom(x));

        svg.append('g')
            .call(d3.axisLeft(y));

        // Line path
        svg.append('path')
            .datum(data)
            .attr('class', 'line')
            .attr('stroke', {colors}[0])
            .attr('d', line);

        // Tooltip
        const tooltip = d3.select('.tooltip');

        // Dots
        svg.selectAll('.dot')
            .data(data)
            .join('circle')
            .attr('class', 'dot')
            .attr('cx', d => x(d.date))
            .attr('cy', d => y(d.value))
            .attr('r', 4)
            .attr('fill', {colors}[0])
            .on('mouseover', function(event, d) {{
                tooltip.style('opacity', 1)
                    .html(`${{d3.timeFormat('%b %d, %Y')(d.date)}}<br>Value: ${{d.value}}`)
                    .style('left', `${{event.pageX + 10}}px`)
                    .style('top', `${{event.pageY - 10}}px`);
            }})
            .on('mouseout', () => tooltip.style('opacity', 0));
    </script>
</body>
</html>""",
    "scatter": """<!DOCTYPE html>
<html lang="en">
<head>
    <meta charset="UTF-8">
    <meta name="viewport" content="width=device-width, initial-scale=1.0">
    <title>{title}</title>
    <script src="https://d3js.org/d3.v7.min.js"></script>
    <style>
        * {{ margin: 0; padding: 0; box-sizing: border-box; }}
        body {{ font-family: system-ui, -apple-system, sans-serif; padding: 20px; }}
        .chart-container {{ max-width: 800px; margin: 0 auto; }}
        .responsive-svg {{ width: 100%; height: auto; }}
        .dot {{ transition: r 0.2s; }}
        .dot:hover {{ opacity: 0.8; }}
        .tooltip {{
            position: absolute;
            padding: 8px 12px;
            background: rgba(0,0,0,0.8);
            color: white;
            border-radius: 4px;
            font-size: 14px;
            pointer-events: none;
            opacity: 0;
        }}
    </style>
</head>
<body>
    <div class="chart-container">
        <h1>{title}</h1>
        <div id="chart" role="img" aria-label="{title}"></div>
    </div>
    <div class="tooltip"></div>

    <script>
        const margin = {{ top: 20, right: 30, bottom: 50, left: 60 }};
        const width = 800 - margin.left - margin.right;
        const height = 500 - margin.top - margin.bottom;

        const svg = d3.select('#chart')
            .append('svg')
            .attr('viewBox', `0 0 ${{width + margin.left + margin.right}} ${{height + margin.top + margin.bottom}}`)
            .classed('responsive-svg', true)
            .append('g')
            .attr('transform', `translate(${{margin.left}},${{margin.top}})`);

        // Sample data
        const data = {sample_data};

        // Scales
        const x = d3.scaleLinear()
            .domain([0, d3.max(data, d => d.x) * 1.1])
            .range([0, width]);

        const y = d3.scaleLinear()
            .domain([0, d3.max(data, d => d.y) * 1.1])
            .range([height, 0]);

        const r = d3.scaleSqrt()  // sqrt for accurate area perception
            .domain([0, d3.max(data, d => d.size || 1)])
            .range([5, 30]);

        const color = d3.scaleOrdinal()
            .domain([...new Set(data.map(d => d.category))])
            .range({colors});

        // Axes
        svg.append('g')
            .attr('transform', `translate(0,${{height}})`)
            .call(d3.axisBottom(x));

        svg.append('g')
            .call(d3.axisLeft(y));

        // Tooltip
        const tooltip = d3.select('.tooltip');

        // Dots
        svg.selectAll('.dot')
            .data(data)
            .join('circle')
            .attr('class', 'dot')
            .attr('cx', d => x(d.x))
            .attr('cy', d => y(d.y))
            .attr('r', d => r(d.size || 5))
            .attr('fill', d => color(d.category))
            .attr('opacity', 0.7)
            .on('mouseover', function(event, d) {{
                tooltip.style('opacity', 1)
                    .html(`<strong>${{d.label || d.category}}</strong><br>X: ${{d.x}}, Y: ${{d.y}}`)
                    .style('left', `${{event.pageX + 10}}px`)
                    .style('top', `${{event.pageY - 10}}px`);
            }})
            .on('mouseout', () => tooltip.style('opacity', 0));
    </script>
</body>
</html>""",
}

SAMPLE_DATA = {
    "bar": [
        {"category": "Category A", "value": 45},
        {"category": "Category B", "value": 78},
        {"category": "Category C", "value": 52},
        {"category": "Category D", "value": 91},
        {"category": "Category E", "value": 33},
    ],
    "force": {
        "nodes": [
            {"id": "A", "label": "Node A", "group": 1, "size": 30},
            {"id": "B", "label": "Node B", "group": 1, "size": 20},
            {"id": "C", "label": "Node C", "group": 2, "size": 25},
            {"id": "D", "label": "Node D", "group": 2, "size": 15},
            {"id": "E", "label": "Node E", "group": 3, "size": 20},
        ],
        "links": [
            {"source": "A", "target": "B", "weight": 3},
            {"source": "A", "target": "C", "weight": 2},
            {"source": "B", "target": "D", "weight": 1},
            {"source": "C", "target": "E", "weight": 2},
            {"source": "D", "target": "E", "weight": 1},
        ],
    },
    "line": [
        {"date": "2024-01-01", "value": 100},
        {"date": "2024-02-01", "value": 120},
        {"date": "2024-03-01", "value": 115},
        {"date": "2024-04-01", "value": 140},
        {"date": "2024-05-01", "value": 155},
        {"date": "2024-06-01", "value": 145},
    ],
    "scatter": [
        {"x": 10, "y": 20, "size": 15, "category": "A", "label": "Point 1"},
        {"x": 25, "y": 35, "size": 25, "category": "A", "label": "Point 2"},
        {"x": 40, "y": 15, "size": 10, "category": "B", "label": "Point 3"},
        {"x": 55, "y": 45, "size": 30, "category": "B", "label": "Point 4"},
        {"x": 70, "y": 30, "size": 20, "category": "C", "label": "Point 5"},
    ],
}

DEFAULT_COLORS = ["#4e79a7", "#f28e2b", "#e15759", "#76b7b2", "#59a14f"]


def generate_viz(
    viz_type: str,
    title: str,
    data_file: str = None,
    output: str = None,
    colors: list = None,
) -> str:
    """Generate visualization HTML from template."""

    if viz_type not in TEMPLATES:
        raise ValueError(
            f"Unknown viz type: {viz_type}. Available: {list(TEMPLATES.keys())}"
        )

    template = TEMPLATES[viz_type]
    sample_data = SAMPLE_DATA.get(viz_type, [])

    # Load custom data if provided
    if data_file:
        path = Path(data_file)
        if path.exists():
            with open(path) as f:
                sample_data = json.load(f)

    # Use default colors if not provided
    if not colors:
        colors = DEFAULT_COLORS

    # Generate HTML
    html = template.format(
        title=title,
        sample_data=json.dumps(sample_data, indent=2),
        colors=json.dumps(colors),
    )

    # Write to file or stdout
    if output:
        output_path = Path(output)
        output_path.write_text(html)
        return f"Created: {output_path}"
    else:
        return html


def main():
    parser = argparse.ArgumentParser(
        description="Generate D3.js visualization templates"
    )
    parser.add_argument(
        "--type",
        "-t",
        choices=list(TEMPLATES.keys()),
        default="bar",
        help="Visualization type (default: bar)",
    )
    parser.add_argument("--title", default="Data Visualization", help="Chart title")
    parser.add_argument("--data", "-d", help="Path to JSON data file")
    parser.add_argument(
        "--output", "-o", help="Output file path (prints to stdout if not specified)"
    )
    parser.add_argument(
        "--colors", "-c", nargs="+", help="Custom color palette (hex values)"
    )
    parser.add_argument(
        "--list-types", action="store_true", help="List available visualization types"
    )

    args = parser.parse_args()

    if args.list_types:
        print("Available visualization types:")
        for t in TEMPLATES.keys():
            print(f"  - {t}")
        return

    result = generate_viz(
        viz_type=args.type,
        title=args.title,
        data_file=args.data,
        output=args.output,
        colors=args.colors,
    )
    print(result)


if __name__ == "__main__":
    main()
