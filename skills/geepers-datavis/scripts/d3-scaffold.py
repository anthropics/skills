#!/usr/bin/env python3
"""
D3.js Visualization Project Scaffolder

Generates boilerplate HTML/CSS/JS for common visualization types.

Usage:
    python d3-scaffold.py my-viz --type force-network
    python d3-scaffold.py my-viz --type timeline --output ~/html/datavis/
    python d3-scaffold.py my-viz --type choropleth --single-file

Types:
    force-network  - Force-directed node-link graph
    timeline       - Horizontal scrolling timeline
    choropleth     - Geographic map with color encoding
    bar-race       - Animated bar chart race
    treemap        - Hierarchical treemap
    sankey         - Flow diagram

Author: Luke Steuber
"""

import argparse
import os
import sys
from pathlib import Path
from typing import Dict

# Base HTML template
HTML_TEMPLATE = """<!DOCTYPE html>
<html lang="en">
<head>
    <meta charset="UTF-8">
    <meta name="viewport" content="width=device-width, initial-scale=1.0">
    <title>{title}</title>

    <!-- Open Graph -->
    <meta property="og:title" content="{title}">
    <meta property="og:description" content="{description}">
    <meta property="og:type" content="website">

    <script src="https://d3js.org/d3.v7.min.js"></script>
{extra_scripts}
    <style>
{css}
    </style>
</head>
<body>
    <header>
        <h1>{title}</h1>
        <p class="subtitle">{description}</p>
    </header>

    <main>
        <div id="visualization"></div>
        <p class="instructions">{instructions}</p>
    </main>

    <footer>
        <p class="attribution">Visualization by Luke Steuber</p>
        <p class="sources">Data sources: <a href="#">Source</a></p>
    </footer>

    <script>
{js}
    </script>
</body>
</html>
"""

# Base CSS (shared)
BASE_CSS = """        * {
            box-sizing: border-box;
            margin: 0;
            padding: 0;
        }

        body {
            font-family: 'Helvetica Neue', system-ui, sans-serif;
            background: #fafafa;
            color: #1a1a1a;
            line-height: 1.6;
        }

        header {
            text-align: center;
            padding: 2rem 1rem;
            background: white;
            border-bottom: 1px solid #e0e0e0;
        }

        h1 {
            font-size: 2rem;
            font-weight: 600;
            margin-bottom: 0.5rem;
        }

        .subtitle {
            color: #666;
            font-size: 1.1rem;
        }

        main {
            max-width: 1200px;
            margin: 0 auto;
            padding: 2rem 1rem;
        }

        #visualization {
            background: white;
            border-radius: 8px;
            box-shadow: 0 2px 8px rgba(0,0,0,0.1);
            overflow: hidden;
        }

        .instructions {
            text-align: center;
            color: #888;
            font-size: 0.9rem;
            margin-top: 1rem;
        }

        footer {
            text-align: center;
            padding: 2rem;
            color: #666;
            font-size: 0.85rem;
        }

        footer a {
            color: #0077BB;
        }

        /* Tooltip */
        .tooltip {
            position: absolute;
            background: rgba(0, 0, 0, 0.85);
            color: white;
            padding: 8px 12px;
            border-radius: 4px;
            font-size: 0.85rem;
            pointer-events: none;
            opacity: 0;
            transition: opacity 0.2s;
            max-width: 250px;
            z-index: 1000;
        }

        .tooltip.visible {
            opacity: 1;
        }

        /* Responsive */
        @media (max-width: 768px) {
            h1 { font-size: 1.5rem; }
            .subtitle { font-size: 1rem; }
        }"""


# Type-specific templates
TEMPLATES: Dict[str, Dict] = {
    'force-network': {
        'title': 'Network Visualization',
        'description': 'Interactive force-directed network graph',
        'instructions': 'Drag nodes to reposition. Hover for details.',
        'extra_scripts': '',
        'css': BASE_CSS + """

        .node {
            cursor: grab;
        }

        .node:active {
            cursor: grabbing;
        }

        .node circle {
            stroke: white;
            stroke-width: 2px;
            transition: r 0.2s;
        }

        .node:hover circle {
            stroke: #333;
        }

        .node text {
            font-size: 11px;
            fill: #333;
            pointer-events: none;
        }

        .link {
            fill: none;
            stroke: #999;
            stroke-opacity: 0.6;
        }

        .link.highlighted {
            stroke: #0077BB;
            stroke-opacity: 1;
        }""",
        'js': """
// Sample data - replace with your data
const data = {
    nodes: [
        { id: 'A', name: 'Node A', group: 1 },
        { id: 'B', name: 'Node B', group: 1 },
        { id: 'C', name: 'Node C', group: 2 },
        { id: 'D', name: 'Node D', group: 2 },
        { id: 'E', name: 'Node E', group: 3 },
    ],
    links: [
        { source: 'A', target: 'B', value: 1 },
        { source: 'A', target: 'C', value: 2 },
        { source: 'B', target: 'D', value: 1 },
        { source: 'C', target: 'D', value: 3 },
        { source: 'D', target: 'E', value: 1 },
    ]
};

// Dimensions
const container = document.getElementById('visualization');
const width = container.clientWidth;
const height = 600;

// Color scale
const colorScale = d3.scaleOrdinal(d3.schemeTableau10);

// Create SVG
const svg = d3.select('#visualization')
    .append('svg')
    .attr('viewBox', `0 0 ${width} ${height}`)
    .attr('preserveAspectRatio', 'xMidYMid meet');

// Tooltip
const tooltip = d3.select('body')
    .append('div')
    .attr('class', 'tooltip');

// Force simulation
const simulation = d3.forceSimulation(data.nodes)
    .force('link', d3.forceLink(data.links).id(d => d.id).distance(100))
    .force('charge', d3.forceManyBody().strength(-300))
    .force('center', d3.forceCenter(width / 2, height / 2))
    .force('collision', d3.forceCollide().radius(30));

// Draw links
const links = svg.append('g')
    .selectAll('line')
    .data(data.links)
    .join('line')
    .attr('class', 'link')
    .attr('stroke-width', d => Math.sqrt(d.value) * 2);

// Draw nodes
const nodes = svg.append('g')
    .selectAll('g')
    .data(data.nodes)
    .join('g')
    .attr('class', 'node')
    .call(drag(simulation));

nodes.append('circle')
    .attr('r', 20)
    .attr('fill', d => colorScale(d.group));

nodes.append('text')
    .attr('dy', 4)
    .attr('text-anchor', 'middle')
    .text(d => d.id);

// Interactions
nodes.on('mouseover', function(event, d) {
    tooltip
        .html(`<strong>${d.name}</strong><br>Group: ${d.group}`)
        .style('left', (event.pageX + 10) + 'px')
        .style('top', (event.pageY - 10) + 'px')
        .classed('visible', true);

    // Highlight connected links
    links.classed('highlighted', l => l.source.id === d.id || l.target.id === d.id);
})
.on('mouseout', function() {
    tooltip.classed('visible', false);
    links.classed('highlighted', false);
});

// Simulation tick
simulation.on('tick', () => {
    links
        .attr('x1', d => d.source.x)
        .attr('y1', d => d.source.y)
        .attr('x2', d => d.target.x)
        .attr('y2', d => d.target.y);

    nodes.attr('transform', d => `translate(${d.x},${d.y})`);
});

// Drag behavior
function drag(simulation) {
    function dragstarted(event) {
        if (!event.active) simulation.alphaTarget(0.3).restart();
        event.subject.fx = event.subject.x;
        event.subject.fy = event.subject.y;
    }

    function dragged(event) {
        event.subject.fx = event.x;
        event.subject.fy = event.y;
    }

    function dragended(event) {
        if (!event.active) simulation.alphaTarget(0);
        event.subject.fx = null;
        event.subject.fy = null;
    }

    return d3.drag()
        .on('start', dragstarted)
        .on('drag', dragged)
        .on('end', dragended);
}"""
    },

    'timeline': {
        'title': 'Interactive Timeline',
        'description': 'Scroll horizontally to explore events over time',
        'instructions': 'Scroll horizontally to explore. Click events for details.',
        'extra_scripts': '',
        'css': BASE_CSS + """

        #visualization {
            overflow-x: auto;
            overflow-y: hidden;
        }

        .timeline-container {
            min-width: 2000px;
            height: 400px;
            position: relative;
        }

        .axis-line {
            stroke: #333;
            stroke-width: 2;
        }

        .event-marker {
            cursor: pointer;
            transition: transform 0.2s;
        }

        .event-marker:hover {
            transform: scale(1.2);
        }

        .event-label {
            font-size: 11px;
            fill: #333;
        }

        .year-label {
            font-size: 12px;
            fill: #666;
        }""",
        'js': """
// Sample data - replace with your data
const events = [
    { year: 2020, month: 1, title: 'Event A', category: 'category1' },
    { year: 2020, month: 6, title: 'Event B', category: 'category2' },
    { year: 2021, month: 3, title: 'Event C', category: 'category1' },
    { year: 2021, month: 9, title: 'Event D', category: 'category3' },
    { year: 2022, month: 2, title: 'Event E', category: 'category2' },
    { year: 2022, month: 11, title: 'Event F', category: 'category1' },
    { year: 2023, month: 5, title: 'Event G', category: 'category3' },
];

// Dimensions
const margin = { top: 50, right: 50, bottom: 50, left: 50 };
const width = 2000;
const height = 400;

// Scales
const parseDate = d => new Date(d.year, d.month - 1);
const xScale = d3.scaleTime()
    .domain(d3.extent(events, d => parseDate(d)))
    .range([margin.left, width - margin.right]);

const colorScale = d3.scaleOrdinal()
    .domain(['category1', 'category2', 'category3'])
    .range(['#0077BB', '#CC6677', '#44AA99']);

// Create SVG
const svg = d3.select('#visualization')
    .append('div')
    .attr('class', 'timeline-container')
    .append('svg')
    .attr('width', width)
    .attr('height', height);

// Tooltip
const tooltip = d3.select('body')
    .append('div')
    .attr('class', 'tooltip');

// Draw axis
const axisY = height / 2;

svg.append('line')
    .attr('class', 'axis-line')
    .attr('x1', margin.left)
    .attr('y1', axisY)
    .attr('x2', width - margin.right)
    .attr('y2', axisY);

// Year markers
const years = d3.timeYear.range(
    d3.timeYear.floor(xScale.domain()[0]),
    d3.timeYear.ceil(xScale.domain()[1])
);

svg.selectAll('.year-marker')
    .data(years)
    .join('g')
    .attr('class', 'year-marker')
    .attr('transform', d => `translate(${xScale(d)}, ${axisY})`)
    .call(g => {
        g.append('line')
            .attr('y1', -10)
            .attr('y2', 10)
            .attr('stroke', '#999');
        g.append('text')
            .attr('class', 'year-label')
            .attr('y', 25)
            .attr('text-anchor', 'middle')
            .text(d => d.getFullYear());
    });

// Draw events
const eventGroups = svg.selectAll('.event-marker')
    .data(events)
    .join('g')
    .attr('class', 'event-marker')
    .attr('transform', (d, i) => {
        const x = xScale(parseDate(d));
        const y = axisY + (i % 2 === 0 ? -60 : 60);
        return `translate(${x}, ${y})`;
    });

eventGroups.append('circle')
    .attr('r', 12)
    .attr('fill', d => colorScale(d.category));

eventGroups.append('line')
    .attr('y1', d => events.indexOf(d) % 2 === 0 ? 12 : -12)
    .attr('y2', d => events.indexOf(d) % 2 === 0 ? 48 : -48)
    .attr('stroke', '#ccc')
    .attr('stroke-dasharray', '3,3');

eventGroups.append('text')
    .attr('class', 'event-label')
    .attr('y', d => events.indexOf(d) % 2 === 0 ? -18 : 22)
    .attr('text-anchor', 'middle')
    .text(d => d.title);

// Interactions
eventGroups.on('mouseover', function(event, d) {
    tooltip
        .html(`<strong>${d.title}</strong><br>${d.year}`)
        .style('left', (event.pageX + 10) + 'px')
        .style('top', (event.pageY - 10) + 'px')
        .classed('visible', true);
})
.on('mouseout', () => tooltip.classed('visible', false));

// Scroll to center
document.getElementById('visualization').scrollLeft = (width - window.innerWidth) / 2;"""
    },

    'choropleth': {
        'title': 'Geographic Data Map',
        'description': 'Color-encoded geographic visualization',
        'instructions': 'Hover over regions for details.',
        'extra_scripts': '    <script src="https://d3js.org/topojson.v3.min.js"></script>',
        'css': BASE_CSS + """

        .state {
            stroke: white;
            stroke-width: 0.5;
            cursor: pointer;
            transition: opacity 0.2s;
        }

        .state:hover {
            opacity: 0.8;
            stroke-width: 1.5;
        }

        .legend {
            font-size: 12px;
        }

        .legend-title {
            font-weight: 600;
        }""",
        'js': """
// Dimensions
const width = 960;
const height = 600;

// Color scale - adjust domain based on your data
const colorScale = d3.scaleSequential(d3.interpolateBlues)
    .domain([0, 100]);

// Create SVG
const svg = d3.select('#visualization')
    .append('svg')
    .attr('viewBox', `0 0 ${width} ${height}`)
    .attr('preserveAspectRatio', 'xMidYMid meet');

// Tooltip
const tooltip = d3.select('body')
    .append('div')
    .attr('class', 'tooltip');

// Projection
const projection = d3.geoAlbersUsa()
    .scale(1200)
    .translate([width / 2, height / 2]);

const path = d3.geoPath().projection(projection);

// Load US TopoJSON
d3.json('https://cdn.jsdelivr.net/npm/us-atlas@3/states-10m.json')
    .then(us => {
        const states = topojson.feature(us, us.objects.states).features;

        // Sample data - replace with your data
        // Map FIPS codes to values
        const data = new Map([
            ['06', 85], // California
            ['48', 72], // Texas
            ['12', 65], // Florida
            ['36', 90], // New York
            // ... add more states
        ]);

        // Draw states
        svg.selectAll('.state')
            .data(states)
            .join('path')
            .attr('class', 'state')
            .attr('d', path)
            .attr('fill', d => {
                const value = data.get(d.id);
                return value ? colorScale(value) : '#eee';
            })
            .on('mouseover', function(event, d) {
                const value = data.get(d.id) || 'No data';
                tooltip
                    .html(`<strong>${d.properties.name}</strong><br>Value: ${value}`)
                    .style('left', (event.pageX + 10) + 'px')
                    .style('top', (event.pageY - 10) + 'px')
                    .classed('visible', true);
            })
            .on('mouseout', () => tooltip.classed('visible', false));

        // Legend
        const legendWidth = 200;
        const legendHeight = 10;

        const legend = svg.append('g')
            .attr('class', 'legend')
            .attr('transform', `translate(${width - legendWidth - 40}, ${height - 40})`);

        // Gradient
        const defs = svg.append('defs');
        const gradient = defs.append('linearGradient')
            .attr('id', 'legend-gradient');

        gradient.selectAll('stop')
            .data(d3.range(0, 1.1, 0.1))
            .join('stop')
            .attr('offset', d => d * 100 + '%')
            .attr('stop-color', d => colorScale(d * 100));

        legend.append('rect')
            .attr('width', legendWidth)
            .attr('height', legendHeight)
            .attr('fill', 'url(#legend-gradient)');

        legend.append('text')
            .attr('class', 'legend-title')
            .attr('y', -5)
            .text('Value');

        legend.append('text')
            .attr('x', 0)
            .attr('y', legendHeight + 15)
            .text('0');

        legend.append('text')
            .attr('x', legendWidth)
            .attr('y', legendHeight + 15)
            .attr('text-anchor', 'end')
            .text('100');
    });"""
    },

    'bar-race': {
        'title': 'Animated Bar Chart Race',
        'description': 'Watch rankings change over time',
        'instructions': 'Press Play to start the animation.',
        'extra_scripts': '',
        'css': BASE_CSS + """

        .controls {
            text-align: center;
            margin-bottom: 1rem;
        }

        .controls button {
            padding: 0.5rem 1.5rem;
            font-size: 1rem;
            background: #0077BB;
            color: white;
            border: none;
            border-radius: 4px;
            cursor: pointer;
            margin: 0 0.5rem;
        }

        .controls button:hover {
            background: #005588;
        }

        .year-display {
            font-size: 4rem;
            font-weight: bold;
            fill: #ddd;
            text-anchor: end;
        }

        .bar-label {
            font-size: 12px;
            fill: white;
            font-weight: 600;
        }

        .bar-value {
            font-size: 12px;
            fill: #333;
        }""",
        'js': """
// Sample data - replace with your data
// Format: { name, value, year }
const rawData = [
    { name: 'A', value: 10, year: 2020 },
    { name: 'B', value: 15, year: 2020 },
    { name: 'C', value: 8, year: 2020 },
    { name: 'A', value: 25, year: 2021 },
    { name: 'B', value: 20, year: 2021 },
    { name: 'C', value: 30, year: 2021 },
    { name: 'A', value: 40, year: 2022 },
    { name: 'B', value: 35, year: 2022 },
    { name: 'C', value: 25, year: 2022 },
];

// Group by year
const years = [...new Set(rawData.map(d => d.year))].sort();
const dataByYear = new Map(
    years.map(year => [year, rawData.filter(d => d.year === year)])
);

// Dimensions
const margin = { top: 20, right: 100, bottom: 30, left: 100 };
const width = 800;
const height = 400;
const barHeight = 40;
const topN = 10;

// Scales
const xScale = d3.scaleLinear()
    .range([margin.left, width - margin.right]);

const yScale = d3.scaleBand()
    .range([margin.top, margin.top + topN * barHeight])
    .padding(0.1);

const colorScale = d3.scaleOrdinal(d3.schemeTableau10);

// Create SVG
const svg = d3.select('#visualization')
    .append('svg')
    .attr('viewBox', `0 0 ${width} ${height}`);

// Year display
const yearText = svg.append('text')
    .attr('class', 'year-display')
    .attr('x', width - margin.right)
    .attr('y', height - 30)
    .text(years[0]);

// Controls
d3.select('#visualization')
    .insert('div', 'svg')
    .attr('class', 'controls')
    .html('<button id="play">Play</button><button id="reset">Reset</button>');

let currentIndex = 0;
let interval;

function update(year) {
    const data = dataByYear.get(year)
        .sort((a, b) => b.value - a.value)
        .slice(0, topN);

    xScale.domain([0, d3.max(data, d => d.value)]);
    yScale.domain(data.map(d => d.name));

    // Bars
    const bars = svg.selectAll('.bar')
        .data(data, d => d.name);

    bars.enter()
        .append('rect')
        .attr('class', 'bar')
        .attr('x', margin.left)
        .attr('y', d => yScale(d.name))
        .attr('height', yScale.bandwidth())
        .attr('fill', d => colorScale(d.name))
        .merge(bars)
        .transition()
        .duration(500)
        .attr('y', d => yScale(d.name))
        .attr('width', d => xScale(d.value) - margin.left);

    bars.exit().remove();

    // Labels
    const labels = svg.selectAll('.bar-label')
        .data(data, d => d.name);

    labels.enter()
        .append('text')
        .attr('class', 'bar-label')
        .attr('x', margin.left + 5)
        .attr('y', d => yScale(d.name) + yScale.bandwidth() / 2 + 4)
        .merge(labels)
        .transition()
        .duration(500)
        .attr('y', d => yScale(d.name) + yScale.bandwidth() / 2 + 4)
        .text(d => d.name);

    labels.exit().remove();

    // Values
    const values = svg.selectAll('.bar-value')
        .data(data, d => d.name);

    values.enter()
        .append('text')
        .attr('class', 'bar-value')
        .attr('y', d => yScale(d.name) + yScale.bandwidth() / 2 + 4)
        .merge(values)
        .transition()
        .duration(500)
        .attr('x', d => xScale(d.value) + 5)
        .attr('y', d => yScale(d.name) + yScale.bandwidth() / 2 + 4)
        .text(d => d.value.toLocaleString());

    values.exit().remove();

    // Year
    yearText.text(year);
}

// Initialize
update(years[0]);

// Controls
d3.select('#play').on('click', function() {
    if (interval) {
        clearInterval(interval);
        interval = null;
        this.textContent = 'Play';
    } else {
        this.textContent = 'Pause';
        interval = setInterval(() => {
            currentIndex++;
            if (currentIndex >= years.length) {
                clearInterval(interval);
                interval = null;
                d3.select('#play').text('Play');
                return;
            }
            update(years[currentIndex]);
        }, 1000);
    }
});

d3.select('#reset').on('click', () => {
    if (interval) {
        clearInterval(interval);
        interval = null;
        d3.select('#play').text('Play');
    }
    currentIndex = 0;
    update(years[0]);
});"""
    },
    'bubble-chart': {
        'title': 'Multi-Dimensional Bubble Chart',
        'description': '3-variable analysis (x, y, size) using Chart.js',
        'instructions': 'Hover over bubbles for detailed metrics.',
        'extra_scripts': '    <script src="https://cdn.jsdelivr.net/npm/chart.js@3"></script>',
        'css': BASE_CSS + """
        .chart-container {
            position: relative;
            height: 600px;
            width: 100%;
        }
        """,
        'js': """
// Sample data
const datasets = [
    {
        label: 'Region A',
        data: [
            { x: 20, y: 30, r: 15 },
            { x: 40, y: 10, r: 10 },
            { x: 25, y: 20, r: 20 }
        ]
    },
    {
        label: 'Region B',
        data: [
            { x: 30, y: 25, r: 25 },
            { x: 15, y: 35, r: 12 }
        ]
    }
];

const ctx = document.createElement('canvas');
document.getElementById('visualization').appendChild(ctx);
ctx.style.width = '100%';
ctx.style.height = '100%';

// Chart.js Configuration
new Chart(ctx, {
    type: 'bubble',
    data: {
        datasets: datasets.map((ds, i) => ({
            label: ds.label,
            data: ds.data,
            backgroundColor: `hsla(${i * 137.5 % 360}, 70%, 50%, 0.6)`,
            borderColor: `hsl(${i * 137.5 % 360}, 70%, 50%)`,
            borderWidth: 1
        }))
    },
    options: {
        responsive: true,
        maintainAspectRatio: false,
        plugins: {
            title: {
                display: true,
                text: 'Market Analysis (Income vs Growth vs Size)'
            },
            tooltip: {
                callbacks: {
                    label: (ctx) => {
                        const point = ctx.raw;
                        return `${ctx.dataset.label}: (${point.x}, ${point.y}, ${point.r})`;
                    }
                }
            }
        },
        scales: {
            x: { title: { display: true, text: 'Income ($k)' } },
            y: { title: { display: true, text: 'Growth (%)' } }
        }
    }
});
"""
    },

    'radial-tree': {
        'title': 'Radial Hierarchy Tree',
        'description': 'Circular tree layout for deep hierarchies',
        'instructions': 'Scroll to zoom. Drag to pan. Hover for details.',
        'extra_scripts': '<script src="https://d3js.org/d3.v7.min.js"></script>',
        'css': BASE_CSS + """
        #visualization {
            height: 800px;
            background: #111;
            color: #eee;
        }
        .node circle {
            transition: all 0.3s;
            cursor: pointer;
        }
        .node text {
            font-family: 'Helvetica Neue', sans-serif;
            fill: #ccc;
            font-size: 10px;
            pointer-events: none;
            text-shadow: 0 1px 4px #000;
        }
        .link {
            fill: none;
            stroke: #555;
            stroke-opacity: 0.4;
            stroke-width: 1.5px;
        }
        """,
        'js': """
// Sample Hierarchy Data
const data = {
  name: "Flare",
  children: [
    {
      name: "Analytics",
      children: [
        {name: "Cluster", value: 3938},
        {name: "Graph", value: 3534},
        {name: "Optimization", value: 7074}
      ]
    },
    {
      name: "Animate",
      children: [
        {name: "Easing", value: 17010},
        {name: "Function", value: 5842},
        {name: "Interpolate", value: 8746}
      ]
    },
    {
      name: "Display",
      children: [
        {name: "DirtySprite", value: 8833},
        {name: "LineSprite", value: 1732},
        {name: "RectSprite", value: 3623}
      ]
    }
  ]
};

const width = 800;
const height = 800;
const radius = width / 2;

const svg = d3.select("#visualization")
  .append("svg")
  .attr("viewBox", `0 0 ${width} ${height}`)
  .style("width", "100%")
  .style("height", "auto")
  .style("font", "10px sans-serif");

const g = svg.append("g")
  .attr("transform", `translate(${width/2},${height/2})`);

const root = d3.hierarchy(data);
const tree = d3.tree()
    .size([2 * Math.PI, radius - 100])
    .separation((a, b) => (a.parent == b.parent ? 1 : 2) / a.depth);

tree(root);

// Links
g.append("g")
  .attr("fill", "none")
  .attr("stroke", "#555")
  .attr("stroke-opacity", 0.4)
  .attr("stroke-width", 1.5)
.selectAll("path")
  .data(root.links())
  .join("path")
  .attr("d", d3.linkRadial()
      .angle(d => d.x)
      .radius(d => d.y));

// Nodes
const node = g.append("g")
.selectAll("a")
.data(root.descendants())
.join("a")
  .attr("transform", d => `rotate(${d.x * 180 / Math.PI - 90}) translate(${d.y},0)`);

node.append("circle")
  .attr("fill", d => d.children ? "#555" : "#999")
  .attr("r", 2.5);

node.append("text")
  .attr("dy", "0.31em")
  .attr("x", d => d.x < Math.PI === !d.children ? 6 : -6)
  .attr("text-anchor", d => d.x < Math.PI === !d.children ? "start" : "end")
  .attr("transform", d => d.x >= Math.PI ? "rotate(180)" : null)
  .text(d => d.data.name)
  .clone(true).lower()
  .attr("stroke", "black");

// Zoom
const zoom = d3.zoom().on("zoom", e => {
    g.attr("transform", `translate(${width/2},${height/2}) ${e.transform}`);
});
svg.call(zoom);
"""
    },

    'sankey': {
        'title': 'Sankey Flow Diagram',
        'description': 'Visualize flows, transfers, and process steps',
        'instructions': 'Hover links to see flow volume.',
        'extra_scripts': """
    <script src="https://d3js.org/d3.v7.min.js"></script>
    <script src="https://unpkg.com/d3-sankey@0.12.3/dist/d3-sankey.min.js"></script>
        """,
        'css': BASE_CSS + """
        .link {
            fill: none;
            stroke-opacity: 0.5;
            transition: stroke-opacity 0.2s;
        }
        .link:hover {
            stroke-opacity: 0.8;
        }
        .node rect {
            fill-opacity: 0.9;
            shape-rendering: crispEdges;
        }
        .node text {
            text-shadow: 0 1px 0 #fff;
            font-size: 12px;
            font-weight: bold;
        }
        """,
        'js': """
// Sample Flow Data
const data = {
  nodes: [
    {name: "Agricultural Waste"}, {name: "Bio-conversion"}, 
    {name: "Liquid"}, {name: "Losses"}, 
    {name: "Solid"}, {name: "Gas"},
    {name: "Biofuel User"}, {name: "Chemical Plant"}
  ],
  links: [
    {source: 0, target: 1, value: 124.729},
    {source: 1, target: 2, value: 0.597},
    {source: 1, target: 3, value: 26.862},
    {source: 1, target: 4, value: 280.122},
    {source: 1, target: 5, value: 81.144},
    {source: 2, target: 6, value: 35.1},
    {source: 5, target: 7, value: 12.3},
    {source: 4, target: 7, value: 20.0}
  ]
};

const width = 900;
const height = 600;

const svg = d3.select("#visualization").append("svg")
    .attr("viewBox", `0 0 ${width} ${height}`)
    .style("width", "100%")
    .style("height", "auto");

const sankey = d3.sankey()
    .nodeWidth(15)
    .nodePadding(10)
    .extent([[1, 5], [width - 1, height - 5]]);

const {nodes, links} = sankey(data);

// Color scale
const color = d3.scaleOrdinal(d3.schemeCategory10);

// Draw nodes
svg.append("g")
  .selectAll("rect")
  .data(nodes)
  .join("rect")
    .attr("x", d => d.x0)
    .attr("y", d => d.y0)
    .attr("height", d => d.y1 - d.y0)
    .attr("width", d => d.x1 - d.x0)
    .attr("fill", d => color(d.name))
  .append("title")
    .text(d => `${d.name}\\n${d.value.toLocaleString()}`);

// Draw links
const link = svg.append("g")
    .attr("fill", "none")
    .attr("stroke-opacity", 0.5)
  .selectAll("g")
  .data(links)
  .join("g")
    .style("mix-blend-mode", "multiply");

const gradient = link.append("linearGradient")
    .attr("id", d => (d.uid = `link-${Math.random().toString(36).substr(2, 9)}`))
    .attr("gradientUnits", "userSpaceOnUse")
    .attr("x1", d => d.source.x1)
    .attr("x2", d => d.target.x0);

gradient.append("stop")
    .attr("offset", "0%")
    .attr("stop-color", d => color(d.source.name));

gradient.append("stop")
    .attr("offset", "100%")
    .attr("stop-color", d => color(d.target.name));

link.append("path")
    .attr("d", d3.sankeyLinkHorizontal())
    .attr("stroke", d => `url(#${d.uid})`)
    .attr("stroke-width", d => Math.max(1, d.width));

// Text
svg.append("g")
    .style("font", "10px sans-serif")
  .selectAll("text")
  .data(nodes)
  .join("text")
    .attr("x", d => d.x0 < width / 2 ? d.x1 + 6 : d.x0 - 6)
    .attr("y", d => (d.y1 + d.y0) / 2)
    .attr("dy", "0.35em")
    .attr("text-anchor", d => d.x0 < width / 2 ? "start" : "end")
    .text(d => d.name);
"""
    }
}


# Add simpler templates
TEMPLATES['treemap'] = {
    'title': 'Hierarchical Treemap',
    'description': 'Nested rectangles showing part-to-whole relationships',
    'instructions': 'Click to zoom into categories. Click background to zoom out.',
    'extra_scripts': '',
    'css': BASE_CSS + """

        .cell {
            cursor: pointer;
            stroke: white;
            stroke-width: 1;
        }

        .cell:hover {
            stroke-width: 2;
        }

        .cell-label {
            font-size: 11px;
            fill: white;
            pointer-events: none;
            text-shadow: 0 1px 2px rgba(0,0,0,0.5);
        }""",
    'js': """
// Sample hierarchical data
const data = {
    name: 'root',
    children: [
        { name: 'Category A', value: 100 },
        { name: 'Category B', children: [
            { name: 'B1', value: 50 },
            { name: 'B2', value: 30 },
        ]},
        { name: 'Category C', value: 80 },
        { name: 'Category D', children: [
            { name: 'D1', value: 40 },
            { name: 'D2', value: 25 },
            { name: 'D3', value: 35 },
        ]},
    ]
};

const width = 800;
const height = 600;

const colorScale = d3.scaleOrdinal(d3.schemeTableau10);

const svg = d3.select('#visualization')
    .append('svg')
    .attr('viewBox', `0 0 ${width} ${height}`);

const tooltip = d3.select('body')
    .append('div')
    .attr('class', 'tooltip');

const root = d3.hierarchy(data)
    .sum(d => d.value)
    .sort((a, b) => b.value - a.value);

const treemap = d3.treemap()
    .size([width, height])
    .padding(2);

treemap(root);

const cells = svg.selectAll('.cell')
    .data(root.leaves())
    .join('rect')
    .attr('class', 'cell')
    .attr('x', d => d.x0)
    .attr('y', d => d.y0)
    .attr('width', d => d.x1 - d.x0)
    .attr('height', d => d.y1 - d.y0)
    .attr('fill', d => colorScale(d.parent.data.name));

const labels = svg.selectAll('.cell-label')
    .data(root.leaves().filter(d => (d.x1 - d.x0) > 40 && (d.y1 - d.y0) > 20))
    .join('text')
    .attr('class', 'cell-label')
    .attr('x', d => d.x0 + 5)
    .attr('y', d => d.y0 + 15)
    .text(d => d.data.name);

cells.on('mouseover', function(event, d) {
    tooltip
        .html(`<strong>${d.data.name}</strong><br>Value: ${d.value.toLocaleString()}`)
        .style('left', (event.pageX + 10) + 'px')
        .style('top', (event.pageY - 10) + 'px')
        .classed('visible', true);
})
.on('mouseout', () => tooltip.classed('visible', false));"""
}


def create_project(name: str, viz_type: str, output_dir: str, single_file: bool):
    """Create the visualization project files."""
    template = TEMPLATES.get(viz_type)
    if not template:
        print(f"Error: Unknown type '{viz_type}'", file=sys.stderr)
        print(f"Available types: {', '.join(TEMPLATES.keys())}", file=sys.stderr)
        sys.exit(1)

    # Create directory
    project_dir = Path(output_dir) / name
    project_dir.mkdir(parents=True, exist_ok=True)

    # Generate HTML
    html_content = HTML_TEMPLATE.format(
        title=template['title'],
        description=template['description'],
        instructions=template['instructions'],
        extra_scripts=template['extra_scripts'],
        css=template['css'],
        js=template['js'],
    )

    # Write files
    index_path = project_dir / 'index.html'
    index_path.write_text(html_content)

    print(f"\nCreated: {project_dir}")
    print(f"  - index.html ({viz_type} template)")

    if not single_file:
        # Also create separate files for easier editing
        (project_dir / 'data').mkdir(exist_ok=True)
        (project_dir / 'data' / 'sample.json').write_text('[\n  {"name": "example", "value": 100}\n]')
        print(f"  - data/sample.json")

    print(f"\nNext steps:")
    print(f"  1. cd {project_dir}")
    print(f"  2. python3 -m http.server 8000")
    print(f"  3. Open http://localhost:8000/")
    print(f"  4. Replace sample data with your own")


def main():
    parser = argparse.ArgumentParser(
        description='Scaffold a D3.js visualization project',
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog=f"""
Available types:
  {chr(10).join(f'  {k:15} - {v["description"]}' for k, v in TEMPLATES.items())}

Examples:
  %(prog)s my-network --type force-network
  %(prog)s my-map --type choropleth --output ~/html/datavis/
  %(prog)s my-timeline --type timeline --single-file
        """
    )

    parser.add_argument('name', nargs='?',
                        help='Project name (will create directory)')
    parser.add_argument('--type', '-t',
                        choices=list(TEMPLATES.keys()),
                        help='Visualization type')
    parser.add_argument('--output', '-o', default='.',
                        help='Output directory (default: current)')
    parser.add_argument('--single-file', '-s', action='store_true',
                        help='Create single HTML file (no separate assets)')
    parser.add_argument('--list', '-l', action='store_true',
                        help='List available templates')

    args = parser.parse_args()

    if args.list:
        print("Available templates:")
        for name, template in TEMPLATES.items():
            print(f"\n  {name}:")
            print(f"    {template['description']}")
        return

    # Validate required args when creating project
    if not args.name:
        parser.error("name is required (unless using --list)")
    if not args.type:
        parser.error("--type is required (unless using --list)")

    create_project(args.name, args.type, args.output, args.single_file)


if __name__ == '__main__':
    main()
