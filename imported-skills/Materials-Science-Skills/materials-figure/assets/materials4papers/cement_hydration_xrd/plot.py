#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
XRD phase analysis during cement hydration
Style: Cement and Concrete Research (CC Research)
- Stacked XRD patterns at different hydration ages
- Monochrome color scheme
- Clear phase annotations
- 2θ range: 5-70°
"""

import numpy as np
import matplotlib.pyplot as plt
import csv
from pathlib import Path

# Publication-quality rcParams
plt.rcParams.update({
    'font.family': 'Arial',
    'font.size': 10,
    'axes.linewidth': 1.2,
    'xtick.major.width': 1.0,
    'ytick.major.width': 1.0,
    'xtick.major.size': 5,
    'ytick.major.size': 5,
    'xtick.direction': 'in',
    'ytick.direction': 'in',
    'legend.frameon': False,
    'figure.dpi': 300,
    'savefig.dpi': 300,
    'savefig.bbox': 'tight',
})


def gaussian(x, amplitude, center, sigma):
    """Generate Gaussian peak"""
    return amplitude * np.exp(-((x - center) ** 2) / (2 * sigma ** 2))


def load_phase_reference(csv_path):
    """Load phase reference data from CSV"""
    phases = []
    with open(csv_path, 'r', encoding='utf-8') as f:
        reader = csv.DictReader(f)
        for row in reader:
            phases.append({
                'phase': row['phase'],
                'two_theta_deg': float(row['two_theta_deg']),
                'relative_intensity': float(row['relative_intensity']),
            })
    return phases


def generate_xrd_pattern(two_theta, phases, hydration_age):
    """
    Generate synthetic XRD pattern based on phase references
    Simulates hydration progress (C3S decreases, CH and C-S-H increase)
    """
    pattern = np.zeros_like(two_theta)

    # Hydration degree factor (0-1)
    hydration_degree = 1 - np.exp(-0.1 * hydration_age)

    for phase in phases:
        center = phase['two_theta_deg']
        max_intensity = phase['relative_intensity']
        phase_name = phase['phase']

        # Adjust intensity based on phase type and hydration
        if 'C3S' in phase_name:
            # C3S decreases with hydration
            intensity = max_intensity * (1 - 0.6 * hydration_degree)
        elif 'CH' in phase_name or 'C-S-H' in phase_name:
            # CH and C-S-H increase with hydration
            intensity = max_intensity * (0.3 + 0.7 * hydration_degree)
        else:
            # Other phases remain relatively constant
            intensity = max_intensity * 0.8

        # Add Gaussian peak with some broadening
        sigma = 0.15 + 0.02 * hydration_degree  # Peak broadening with hydration
        pattern += gaussian(two_theta, intensity, center, sigma)

    # Add small noise
    noise = np.random.normal(0, 0.5, len(two_theta))
    pattern = pattern + noise

    # Smooth to simulate real XRD (simple moving average)
    kernel_size = 11
    kernel = np.ones(kernel_size) / kernel_size
    pattern = np.convolve(pattern, kernel, mode='same')

    return np.maximum(pattern, 0)


def plot_xrd_hydration():
    """Create stacked XRD plot for cement hydration"""

    # Load phase reference data
    data_dir = Path(__file__).parent / 'data'
    phases = load_phase_reference(data_dir / 'phase_reference.csv')

    # Add C-S-H phase (amorphous hump around 30°)
    phases.append({
        'phase': 'C-S-H',
        'two_theta_deg': 30.0,
        'relative_intensity': 40,
    })

    # Generate 2θ range
    two_theta = np.linspace(5, 70, 1000)

    # Hydration ages
    ages = [1, 3, 7, 28]
    age_labels = ['1 day', '3 days', '7 days', '28 days']

    # Generate patterns for each age
    patterns = {}
    for age in ages:
        patterns[age] = generate_xrd_pattern(two_theta, phases, age)

    # Create stacked plot (offset each pattern)
    fig, ax = plt.subplots(figsize=(8, 6))

    offset_step = 50  # Vertical offset between patterns
    colors = ['#000000', '#333333', '#666666', '#999999']  # Monochrome

    for i, (age, label) in enumerate(zip(ages, age_labels)):
        offset = i * offset_step
        pattern = patterns[age] + offset

        ax.plot(two_theta, pattern, color=colors[i], linewidth=1.2, label=label)

        # Fill under curve
        ax.fill_between(two_theta, offset, pattern, alpha=0.1, color=colors[i])

    # Annotate key phases
    annotations = [
        (11.7, 'C3S\n(001)', 0.8),
        (20.3, 'CH\n(001)', 0.9),
        (29.4, 'C3S\n(111)', 0.7),
        (32.2, 'C3S\n(211)', 1.0),
        (34.1, 'CH\n(101)', 0.6),
    ]

    for x, text, age_factor in annotations:
        # Find y position from 28-day pattern
        idx = np.argmin(np.abs(two_theta - x))
        y = patterns[28][idx] + 3 * offset_step

        ax.annotate(text, xy=(x, y), xytext=(x, y + 8),
                   fontsize=8, ha='center', va='bottom',
                   arrowprops=dict(arrowstyle='->', color='black', lw=0.8))

    # C-S-H hump annotation
    idx_30 = np.argmin(np.abs(two_theta - 30))
    y_30 = patterns[28][idx_30] + 3 * offset_step
    ax.annotate('C-S-H\n(amorphous)', xy=(30, y_30),
               xytext=(38, 180), fontsize=8, ha='center',
               arrowprops=dict(arrowstyle='->', color='black', lw=0.8, connectionstyle='arc3,rad=0.3'))

    ax.set_xlabel('2θ (degrees)', fontsize=11, fontweight='bold')
    ax.set_ylabel('Intensity (a.u.) + offset', fontsize=11, fontweight='bold')
    ax.set_title('XRD patterns of cement paste during hydration', fontsize=12, fontweight='bold')

    ax.set_xlim(5, 70)
    ax.set_ylim(-5, max(patterns[28]) + 4 * offset_step + 20)

    # Legend
    ax.legend(loc='upper right', fontsize=9)

    # Grid (subtle)
    ax.grid(True, linestyle=':', alpha=0.3)

    plt.tight_layout()

    # Save
    fig_dir = Path(__file__).parent / 'figures'
    fig_dir.mkdir(exist_ok=True)
    fig.savefig(fig_dir / 'xrd_hydration_stacked.png', dpi=300, bbox_inches='tight')
    print(f"Saved: {fig_dir / 'xrd_hydration_stacked.png'}")

    plt.close()


if __name__ == '__main__':
    plot_xrd_hydration()
