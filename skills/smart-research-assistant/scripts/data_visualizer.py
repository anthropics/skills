#!/usr/bin/env python3
"""
Data Visualizer Script for Research Skills

This script creates simple charts and graphs for research reports
using matplotlib and other visualization libraries.
"""

import matplotlib.pyplot as plt
import matplotlib.patches as mpatches
import numpy as np
import json
import pandas as pd
from typing import List, Dict, Optional, Tuple
import argparse
import sys

class DataVisualizer:
    def __init__(self):
        self.chart_types = {
            'bar': self._create_bar_chart,
            'line': self._create_line_chart,
            'pie': self._create_pie_chart,
            'scatter': self._create_scatter_plot,
            'histogram': self._create_histogram,
            'box': self._create_box_plot,
            'heatmap': self._create_heatmap
        }
        
        # Set up matplotlib for better-looking plots
        plt.style.use('seaborn-v0_8')
        self.colors = ['#2E86AB', '#A23B72', '#F18F01', '#C73E1D', '#592E83', '#1B998B', '#ED217C', '#F4A261']

    def create_chart(self, data: Dict, chart_type: str, title: str = "", 
                    output_file: str = None, **kwargs) -> str:
        """Create a chart from data and save to file"""
        if chart_type not in self.chart_types:
            raise ValueError(f"Unsupported chart type: {chart_type}")
        
        # Create the plot
        fig, ax = plt.subplots(figsize=(10, 6))
        
        # Call the appropriate chart creation function
        self.chart_types[chart_type](ax, data, **kwargs)
        
        # Set title and formatting
        if title:
            ax.set_title(title, fontsize=14, fontweight='bold', pad=20)
        
        # Adjust layout
        plt.tight_layout()
        
        # Generate filename if not provided
        if not output_file:
            timestamp = pd.Timestamp.now().strftime('%Y%m%d_%H%M%S')
            output_file = f"chart_{chart_type}_{timestamp}.png"
        
        # Save the plot
        plt.savefig(output_file, dpi=300, bbox_inches='tight')
        plt.close()
        
        return output_file

    def _create_bar_chart(self, ax, data: Dict, **kwargs):
        """Create a bar chart"""
        categories = data.get('categories', [])
        values = data.get('values', [])
        
        if not categories or not values:
            raise ValueError("Bar chart requires 'categories' and 'values' in data")
        
        # Create bars
        bars = ax.bar(categories, values, color=self.colors[:len(categories)])
        
        # Add value labels on bars
        for bar, value in zip(bars, values):
            height = bar.get_height()
            ax.text(bar.get_x() + bar.get_width()/2., height + max(values)*0.01,
                   f'{value:.1f}', ha='center', va='bottom')
        
        # Customize
        ax.set_xlabel(data.get('x_label', 'Categories'))
        ax.set_ylabel(data.get('y_label', 'Values'))
        ax.grid(axis='y', alpha=0.3)
        
        # Rotate x-axis labels if many categories
        if len(categories) > 5:
            plt.xticks(rotation=45, ha='right')

    def _create_line_chart(self, ax, data: Dict, **kwargs):
        """Create a line chart"""
        x_values = data.get('x_values', [])
        y_values = data.get('y_values', [])
        
        if not x_values or not y_values:
            raise ValueError("Line chart requires 'x_values' and 'y_values' in data")
        
        # Create line
        line = ax.plot(x_values, y_values, marker='o', linewidth=2, 
                     markersize=6, color=self.colors[0])
        
        # Customize
        ax.set_xlabel(data.get('x_label', 'X Values'))
        ax.set_ylabel(data.get('y_label', 'Y Values'))
        ax.grid(True, alpha=0.3)
        
        # Add trend line if requested
        if kwargs.get('trend_line', False):
            z = np.polyfit(x_values, y_values, 1)
            p = np.poly1d(z)
            ax.plot(x_values, p(x_values), "--", alpha=0.7, color=self.colors[1])

    def _create_pie_chart(self, ax, data: Dict, **kwargs):
        """Create a pie chart"""
        labels = data.get('labels', [])
        values = data.get('values', [])
        
        if not labels or not values:
            raise ValueError("Pie chart requires 'labels' and 'values' in data")
        
        # Create pie chart
        wedges, texts, autotexts = ax.pie(values, labels=labels, autopct='%1.1f%%',
                                         colors=self.colors[:len(labels)], startangle=90)
        
        # Customize text
        for autotext in autotexts:
            autotext.set_color('white')
            autotext.set_fontweight('bold')
        
        ax.axis('equal')

    def _create_scatter_plot(self, ax, data: Dict, **kwargs):
        """Create a scatter plot"""
        x_values = data.get('x_values', [])
        y_values = data.get('y_values', [])
        
        if not x_values or not y_values:
            raise ValueError("Scatter plot requires 'x_values' and 'y_values' in data")
        
        # Create scatter plot
        scatter = ax.scatter(x_values, y_values, alpha=0.7, 
                            c=self.colors[0], s=60)
        
        # Customize
        ax.set_xlabel(data.get('x_label', 'X Values'))
        ax.set_ylabel(data.get('y_label', 'Y Values'))
        ax.grid(True, alpha=0.3)
        
        # Add regression line if requested
        if kwargs.get('regression_line', False):
            z = np.polyfit(x_values, y_values, 1)
            p = np.poly1d(z)
            ax.plot(x_values, p(x_values), "--", alpha=0.7, color=self.colors[1])

    def _create_histogram(self, ax, data: Dict, **kwargs):
        """Create a histogram"""
        values = data.get('values', [])
        
        if not values:
            raise ValueError("Histogram requires 'values' in data")
        
        # Create histogram
        n, bins, patches = ax.hist(values, bins=kwargs.get('bins', 20), 
                                  alpha=0.7, color=self.colors[0], edgecolor='black')
        
        # Customize
        ax.set_xlabel(data.get('x_label', 'Values'))
        ax.set_ylabel(data.get('y_label', 'Frequency'))
        ax.grid(True, alpha=0.3, axis='y')

    def _create_box_plot(self, ax, data: Dict, **kwargs):
        """Create a box plot"""
        categories = data.get('categories', [])
        data_groups = data.get('data_groups', [])
        
        if not categories or not data_groups:
            raise ValueError("Box plot requires 'categories' and 'data_groups' in data")
        
        # Create box plot
        box_plot = ax.box(data_groups, patch_artist=True, labels=categories)
        
        # Color the boxes
        for patch, color in zip(box_plot['boxes'], self.colors):
            patch.set_facecolor(color)
            patch.set_alpha(0.7)
        
        # Customize
        ax.set_ylabel(data.get('y_label', 'Values'))
        ax.grid(True, alpha=0.3, axis='y')

    def _create_heatmap(self, ax, data: Dict, **kwargs):
        """Create a heatmap"""
        matrix = data.get('matrix', [])
        x_labels = data.get('x_labels', [])
        y_labels = data.get('y_labels', [])
        
        if not matrix:
            raise ValueError("Heatmap requires 'matrix' in data")
        
        # Create heatmap
        im = ax.imshow(matrix, cmap='RdYlBu_r', aspect='auto')
        
        # Add colorbar
        plt.colorbar(im, ax=ax)
        
        # Set labels
        if x_labels:
            ax.set_xticks(range(len(x_labels)))
            ax.set_xticklabels(x_labels, rotation=45, ha='right')
        
        if y_labels:
            ax.set_yticks(range(len(y_labels)))
            ax.set_yticklabels(y_labels)
        
        # Add text annotations
        for i in range(len(matrix)):
            for j in range(len(matrix[0])):
                text = ax.text(j, i, f'{matrix[i][j]:.2f}',
                             ha="center", va="center", color="black", fontweight='bold')

    def create_research_summary_chart(self, research_data: Dict) -> str:
        """Create a summary chart for research findings"""
        # Extract key metrics
        sources_evaluated = len(research_data.get('sources', []))
        credibility_score = research_data.get('overall_credibility', 0)
        findings_count = len(research_data.get('findings', []))
        
        # Create summary data
        summary_data = {
            'categories': ['Sources Evaluated', 'Credibility Score', 'Key Findings'],
            'values': [sources_evaluated, credibility_score, findings_count],
            'x_label': 'Research Metrics',
            'y_label': 'Count / Score'
        }
        
        return self.create_chart(summary_data, 'bar', 'Research Summary')

    def create_credibility_distribution(self, sources: List[Dict]) -> str:
        """Create a distribution chart of source credibility scores"""
        scores = [source.get('credibility_score', 50) for source in sources]
        
        # Create histogram data
        hist_data = {
            'values': scores,
            'x_label': 'Credibility Score',
            'y_label': 'Number of Sources'
        }
        
        return self.create_chart(hist_data, 'histogram', 'Distribution of Source Credibility')

    def create_timeline_chart(self, events: List[Dict]) -> str:
        """Create a timeline chart of research events"""
        dates = [event.get('date', '') for event in events]
        importance = [event.get('importance', 1) for event in events]
        
        # Convert dates to numeric for plotting
        date_numbers = list(range(len(dates)))
        
        timeline_data = {
            'x_values': date_numbers,
            'y_values': importance,
            'x_label': 'Timeline',
            'y_label': 'Importance'
        }
        
        return self.create_chart(timeline_data, 'line', 'Research Timeline')

def main():
    """Command line interface for data visualization"""
    parser = argparse.ArgumentParser(description='Create charts and graphs for research reports')
    parser.add_argument('data_file', help='JSON file containing chart data')
    parser.add_argument('--type', default='bar', 
                       choices=['bar', 'line', 'pie', 'scatter', 'histogram', 'box', 'heatmap'],
                       help='Type of chart to create')
    parser.add_argument('--title', help='Chart title')
    parser.add_argument('--output', help='Output file name')
    parser.add_argument('--research-summary', action='store_true',
                       help='Create research summary chart')
    
    args = parser.parse_args()
    
    try:
        with open(args.data_file, 'r', encoding='utf-8') as f:
            data = json.load(f)
        
        visualizer = DataVisualizer()
        
        if args.research_summary:
            # Create research summary chart
            output_file = visualizer.create_research_summary_chart(data)
        else:
            # Create regular chart
            output_file = visualizer.create_chart(
                data, args.type, args.title or '', args.output
            )
        
        print(f"Chart saved to: {output_file}")
    
    except FileNotFoundError:
        print(f"Error: Data file '{args.data_file}' not found")
        sys.exit(1)
    except json.JSONDecodeError as e:
        print(f"Error: Invalid JSON in data file - {e}")
        sys.exit(1)
    except Exception as e:
        print(f"Error: {e}")
        sys.exit(1)

if __name__ == "__main__":
    main()