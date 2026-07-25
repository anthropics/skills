#!/usr/bin/env python3
"""
Dashboard Generator - Generate comprehensive dashboard specifications

This script generates dashboard specifications based on service/system descriptions:
- Panel layout optimized for different screen sizes and roles
- Metric queries (Prometheus-style) for comprehensive monitoring
- Visualization types appropriate for different metric types
- Drill-down paths for effective troubleshooting workflows
- Golden signals coverage (latency, traffic, errors, saturation)
- RED/USE method implementation
- Business metrics integration

Usage:
    python dashboard_generator.py --input service_definition.json --output dashboard_spec.json
    python dashboard_generator.py --service-type api --name "Payment Service" --output payment_dashboard.json
"""

import json
import argparse
import sys
import math
from typing import Dict, List, Any, Tuple
from datetime import datetime, timedelta


class DashboardGenerator:
    """Generate comprehensive dashboard specifications."""
    
    # Dashboard layout templates by role
    ROLE_LAYOUTS = {
        'sre': {
            'primary_focus': ['availability', 'latency', 'errors', 'resource_utilization'],
            'secondary_focus': ['throughput', 'capacity', 'dependencies'],
            'time_ranges': ['1h', '6h', '1d', '7d'],
            'default_refresh': '30s'
        },
        'developer': {
            'primary_focus': ['latency', 'errors', 'throughput', 'business_metrics'],
            'secondary_focus': ['resource_utilization', 'dependencies'],
            'time_ranges': ['15m', '1h', '6h', '1d'],
            'default_refresh': '1m'
        },
        'executive': {
            'primary_focus': ['availability', 'business_metrics', 'user_experience'],
            'secondary_focus': ['cost', 'capacity_trends'],
            'time_ranges': ['1d', '7d', '30d'],
            'default_refresh': '5m'
        },
        'ops': {
            'primary_focus': ['resource_utilization', 'capacity', 'alerts', 'deployments'],
            'secondary_focus': ['throughput', 'latency'],
            'time_ranges': ['5m', '30m', '2h', '1d'],
            'default_refresh': '15s'
        }
    }
    
    # Service type specific metric configurations
    SERVICE_METRICS = {
        'api': {
            'golden_signals': ['latency', 'traffic', 'errors', 'saturation'],
            'key_metrics': [
                'http_requests_total',
                'http_request_duration_seconds',
                'http_request_size_bytes',
                'http_response_size_bytes'
            ],
            'resource_metrics': ['cpu_usage', 'memory_usage', 'goroutines']
        },
        'web': {
            'golden_signals': ['latency', 'traffic', 'errors', 'saturation'],
            'key_metrics': [
                'http_requests_total',
                'http_request_duration_seconds',
                'page_load_time',
                'user_sessions'
            ],
            'resource_metrics': ['cpu_usage', 'memory_usage', 'connections']
        },
        'database': {
            'golden_signals': ['latency', 'traffic', 'errors', 'saturation'],
            'key_metrics': [
                'db_connections_active',
                'db_query_duration_seconds',
                'db_queries_total',
                'db_slow_queries_total'
            ],
            'resource_metrics': ['cpu_usage', 'memory_usage', 'disk_io', 'connections']
        },
        'queue': {
            'golden_signals': ['latency', 'traffic', 'errors', 'saturation'],
            'key_metrics': [
                'queue_depth',
                'message_processing_duration',
                'messages_published_total',
                'messages_consumed_total'
            ],
            'resource_metrics': ['cpu_usage', 'memory_usage', 'disk_usage']
        }
    }
    
    # Visualization type recommendations
    VISUALIZATION_TYPES = {
        'latency': 'line_chart',
        'throughput': 'line_chart',
        'error_rate': 'line_chart',
        'success_rate': 'stat',
        'resource_utilization': 'gauge',
        'queue_depth': 'bar_chart',
        'status': 'stat',
        'distribution': 'heatmap',
        'alerts': 'table',
        'logs': 'logs_panel'
    }

    def __init__(self):
        """Initialize the Dashboard Generator."""
        self.service_config = {}
        self.dashboard_spec = {}

    def load_service_definition(self, file_path: str) -> Dict[str, Any]:
        """Load service definition from JSON file."""
        try:
            with open(file_path, 'r') as f:
                return json.load(f)
        except FileNotFoundError:
            raise ValueError(f"Service definition file not found: {file_path}")
        except json.JSONDecodeError as e:
            raise ValueError(f"Invalid JSON in service definition: {e}")

    def create_service_definition(self, service_type: str, name: str, 
                                criticality: str = 'medium') -> Dict[str, Any]:
        """Create a service definition from parameters."""
        return {
            'name': name,
            'type': service_type,
            'criticality': criticality,
            'description': f'{name} - A {criticality} criticality {service_type} service',
            'team': 'platform',
            'environment': 'production',
            'dependencies': [],
            'tags': []
        }

    def generate_dashboard_specification(self, service_def: Dict[str, Any], 
                                       target_role: str = 'sre') -> Dict[str, Any]:
        """Generate comprehensive dashboard specification."""
        service_name = service_def.get('name', 'Service')
        service_type = service_def.get('type', 'api')
        
        # Get role-specific configuration
        role_config = self.ROLE_LAYOUTS.get(target_role, self.ROLE_LAYOUTS['sre'])
        
        dashboard_spec = {
            'metadata': {
                'title': f"{service_name} - {target_role.upper()} Dashboard",
                'service': service_def,
                'target_role': target_role,
                'generated_at': datetime.utcnow().isoformat() + 'Z',
                'version': '1.0'
            },
            'configuration': {
                'time_ranges': role_config['time_ranges'],
                'default_time_range': role_config['time_ranges'][1],  # Second option as default
                'refresh_interval': role_config['default_refresh'],
                'timezone': 'UTC',
                'theme': 'dark'
            },
            'layout': self._generate_dashboard_layout(service_def, role_config),
            'panels': self._generate_panels(service_def, role_config),
            'variables': self._generate_template_variables(service_def),
            'alerts_integration': self._generate_alerts_integration(service_def),
            'drill_down_paths': self._generate_drill_down_paths(service_def)
        }
        
        return dashboard_spec

    def _generate_dashboard_layout(self, service_def: Dict[str, Any], 
                                 role_config: Dict[str, Any]) -> Dict[str, Any]:
        """Generate dashboard layout configuration."""
        return {
            'grid_settings': {
                'width': 24,  # Grafana-style 24-column grid
                'height_unit': 'px',
                'cell_height': 30
            },
            'sections': [
                {
                    'title': 'Service Overview',
                    'collapsed': False,
                    'y_position': 0,
                    'panels': ['service_status', 'slo_summary', 'error_budget']
                },
                {
                    'title': 'Golden Signals',
                    'collapsed': False,
                    'y_position': 8,
                    'panels': ['latency', 'traffic', 'errors', 'saturation']
                },
                {
                    'title': 'Resource Utilization',
                    'collapsed': False,
                    'y_position': 16,
                    'panels': ['cpu_usage', 'memory_usage', 'network_io', 'disk_io']
                },
                {
                    'title': 'Dependencies & Downstream',
                    'collapsed': True,
                    'y_position': 24,
                    'panels': ['dependency_status', 'downstream_latency', 'circuit_breakers']
                }
            ]
        }

    def _generate_panels(self, service_def: Dict[str, Any], 
                        role_config: Dict[str, Any]) -> List[Dict[str, Any]]:
        """Generate dashboard panels based on service and role."""
        service_name = service_def.get('name', 'service')
        service_type = service_def.get('type', 'api')
        panels = []
        
        # Service Overview Panels
        panels.extend(self._create_overview_panels(service_def))
        
        # Golden Signals Panels
        panels.extend(self._create_golden_signals_panels(service_def))
        
        # Resource Utilization Panels
        panels.extend(self._create_resource_panels(service_def))
        
        # Service-specific panels
        if service_type == 'api':
            panels.extend(self._create_api_specific_panels(service_def))
        elif service_type == 'database':
            panels.extend(self._create_database_specific_panels(service_def))
        elif service_type == 'queue':
            panels.extend(self._create_queue_specific_panels(service_def))
        
        # Role-specific additional panels
        if 'business_metrics' in role_config['primary_focus']:
            panels.extend(self._create_business_metrics_panels(service_def))
        
        if 'capacity' in role_config['primary_focus']:
            panels.extend(self._create_capacity_panels(service_def))
        
        return panels

    def _create_overview_panels(self, service_def: Dict[str, Any]) -> List[Dict[str, Any]]:
        """Create service overview panels."""
        service_name = service_def.get('name', 'service')
        
        return [
            {
                'id': 'service_status',
                'title': 'Service Status',
                'type': 'stat',
                'grid_pos': {'x': 0, 'y': 0, 'w': 6, 'h': 4},
                'targets': [
                    {
                        'expr': f'up{{service="{service_name}"}}',
                        'legendFormat': 'Status'
                    }
                ],
                'field_config': {
                    'overrides': [
                        {
                            'matcher': {'id': 'byName', 'options': 'Status'},
                            'properties': [
                                {'id': 'color', 'value': {'mode': 'thresholds'}},
                                {'id': 'thresholds', 'value': {
                                    'steps': [
                                        {'color': 'red', 'value': 0},
                                        {'color': 'green', 'value': 1}
                                    ]
                                }},
                                {'id': 'mappings', 'value': [
                                    {'options': {'0': {'text': 'DOWN'}}, 'type': 'value'},
                                    {'options': {'1': {'text': 'UP'}}, 'type': 'value'}
                                ]}
                            ]
                        }
                    ]
                },
                'options': {
                    'orientation': 'horizontal',
                    'textMode': 'value_and_name'
                }
            },
            {
                'id': 'slo_summary',
                'title': 'SLO Achievement (30d)',
                'type': 'stat',
                'grid_pos': {'x': 6, 'y': 0, 'w': 9, 'h': 4},
                'targets': [
                    {
                        'expr': f'(1 - (increase(http_requests_total{{service="{service_name}",code=~"5.."}}[30d]) / increase(http_requests_total{{service="{service_name}"}}[30d]))) * 100',
                        'legendFormat': 'Availability'
                    },
                    {
                        'expr': f'histogram_quantile(0.95, increase(http_request_duration_seconds_bucket{{service="{service_name}"}}[30d])) * 1000',
                        'legendFormat': 'P95 Latency (ms)'
                    }
                ],
                'field_config': {
                    'defaults': {
                        'color': {'mode': 'thresholds'},
                        'thresholds': {
                            'steps': [
                                {'color': 'red', 'value': 0},
                                {'color': 'yellow', 'value': 99.0},
                                {'color': 'green', 'value': 99.9}
                            ]
                        }
                    }
                },
                'options': {
                    'orientation': 'horizontal',
                    'textMode': 'value_and_name'
                }
            },
            {
                'id': 'error_budget',
                'title': 'Error Budget Remaining',
                'type': 'gauge',
                'grid_pos': {'x': 15, 'y': 0, 'w': 9, 'h': 4},
                'targets': [
                    {
                        'expr': f'(1 - (increase(http_requests_total{{service="{service_name}",code=~"5.."}}[30d]) / increase(http_requests_total{{service="{service_name}"}}[30d])) - 0.999) / 0.001 * 100',
                        'legendFormat': 'Error Budget %'
                    }
                ],
                'field_config': {
                    'defaults': {
                        'color': {'mode': 'thresholds'},
                        'min': 0,
                        'max': 100,
                        'thresholds': {
                            'steps': [
                                {'color': 'red', 'value': 0},
                                {'color': 'yellow', 'value': 25},
                                {'color': 'green', 'value': 50}
                            ]
                        },
                        'unit': 'percent'
                    }
                },
                'options': {
                    'showThresholdLabels': True,
                    'showThresholdMarkers': True
                }
            }
        ]

    def _create_golden_signals_panels(self, service_def: Dict[str, Any]) -> List[Dict[str, Any]]:
        """Create golden signals monitoring panels."""
        service_name = service_def.get('name', 'service')
        
        return [
            {
                'id': 'latency',
                'title': 'Request Latency',
                'type': 'timeseries',
                'grid_pos': {'x': 0, 'y': 8, 'w': 12, 'h': 6},
                'targets': [
                    {
                        'expr': f'histogram_quantile(0.50, rate(http_request_duration_seconds_bucket{{service="{service_name}"}}[5m])) * 1000',
                        'legendFormat': 'P50 Latency'
                    },
                    {
                        'expr': f'histogram_quantile(0.95, rate(http_request_duration_seconds_bucket{{service="{service_name}"}}[5m])) * 1000',
                        'legendFormat': 'P95 Latency'
                    },
                    {
                        'expr': f'histogram_quantile(0.99, rate(http_request_duration_seconds_bucket{{service="{service_name}"}}[5m])) * 1000',
                        'legendFormat': 'P99 Latency'
                    }
                ],
                'field_config': {
                    'defaults': {
                        'color': {'mode': 'palette-classic'},
                        'unit': 'ms',
                        'custom': {
                            'drawStyle': 'line',
                            'lineInterpolation': 'linear',
                            'lineWidth': 1,
                            'fillOpacity': 10
                        }
                    }
                },
                'options': {
                    'tooltip': {'mode': 'multi', 'sort': 'desc'},
                    'legend': {'displayMode': 'table', 'placement': 'bottom'}
                }
            },
            {
                'id': 'traffic',
                'title': 'Request Rate',
                'type': 'timeseries',
                'grid_pos': {'x': 12, 'y': 8, 'w': 12, 'h': 6},
                'targets': [
                    {
                        'expr': f'sum(rate(http_requests_total{{service="{service_name}"}}[5m]))',
                        'legendFormat': 'Total RPS'
                    },
                    {
                        'expr': f'sum(rate(http_requests_total{{service="{service_name}",code=~"2.."}}[5m]))',
                        'legendFormat': '2xx RPS'
                    },
                    {
                        'expr': f'sum(rate(http_requests_total{{service="{service_name}",code=~"4.."}}[5m]))',
                        'legendFormat': '4xx RPS'
                    },
                    {
                        'expr': f'sum(rate(http_requests_total{{service="{service_name}",code=~"5.."}}[5m]))',
                        'legendFormat': '5xx RPS'
                    }
                ],
                'field_config': {
                    'defaults': {
                        'color': {'mode': 'palette-classic'},
                        'unit': 'reqps',
                        'custom': {
                            'drawStyle': 'line',
                            'lineInterpolation': 'linear',
                            'lineWidth': 1,
                            'fillOpacity': 0
                        }
                    }
                },
                'options': {
                    'tooltip': {'mode': 'multi', 'sort': 'desc'},
                    'legend': {'displayMode': 'table', 'placement': 'bottom'}
                }
            },
            {
                'id': 'errors',
                'title': 'Error Rate',
                'type': 'timeseries',
                'grid_pos': {'x': 0, 'y': 14, 'w': 12, 'h': 6},
                'targets': [
                    {
                        'expr': f'sum(rate(http_requests_total{{service="{service_name}",code=~"5.."}}[5m])) / sum(rate(http_requests_total{{service="{service_name}"}}[5m])) * 100',
                        'legendFormat': '5xx Error Rate'
                    },
                    {
                        'expr': f'sum(rate(http_requests_total{{service="{service_name}",code=~"4.."}}[5m])) / sum(rate(http_requests_total{{service="{service_name}"}}[5m])) * 100',
                        'legendFormat': '4xx Error Rate'
                    }
                ],
                'field_config': {
                    'defaults': {
                        'color': {'mode': 'palette-classic'},
                        'unit': 'percent',
                        'custom': {
                            'drawStyle': 'line',
                            'lineInterpolation': 'linear',
                            'lineWidth': 2,
                            'fillOpacity': 20
                        }
                    },
                    'overrides': [
                        {
                            'matcher': {'id': 'byName', 'options': '5xx Error Rate'},
                            'properties': [{'id': 'color', 'value': {'fixedColor': 'red'}}]
                        }
                    ]
                },
                'options': {
                    'tooltip': {'mode': 'multi', 'sort': 'desc'},
                    'legend': {'displayMode': 'table', 'placement': 'bottom'}
                }
            },
            {
                'id': 'saturation',
                'title': 'Saturation Metrics',
                'type': 'timeseries',
                'grid_pos': {'x': 12, 'y': 14, 'w': 12, 'h': 6},
                'targets': [
                    {
                        'expr': f'rate(process_cpu_seconds_total{{service="{service_name}"}}[5m]) * 100',
                        'legendFormat': 'CPU Usage %'
                    },
                    {
                        'expr': f'process_resident_memory_bytes{{service="{service_name}"}} / process_virtual_memory_max_bytes{{service="{service_name}"}} * 100',
                        'legendFormat': 'Memory Usage %'
                    }
                ],
                'field_config': {
                    'defaults': {
                        'color': {'mode': 'palette-classic'},
                        'unit': 'percent',
                        'max': 100,
                        'custom': {
                            'drawStyle': 'line',
                            'lineInterpolation': 'linear',
                            'lineWidth': 1,
                            'fillOpacity': 10
                        }
                    }
                },
                'options': {
                    'tooltip': {'mode': 'multi', 'sort': 'desc'},
                    'legend': {'displayMode': 'table', 'placement': 'bottom'}
                }
            }
        ]

    def _create_resource_panels(self, service_def: Dict[str, Any]) -> List[Dict[str, Any]]:
        """Create resource utilization panels."""
        service_name = service_def.get('name', 'service')
        
        return [
            {
                'id': 'cpu_usage',
                'title': 'CPU Usage',
                'type': 'gauge',
                'grid_pos': {'x': 0, 'y': 20, 'w': 6, 'h': 4},
                'targets': [
                    {
                        'expr': f'rate(process_cpu_seconds_total{{service="{service_name}"}}[5m]) * 100',
                        'legendFormat': 'CPU %'
                    }
                ],
                'field_config': {
                    'defaults': {
                        'color': {'mode': 'thresholds'},
                        'unit': 'percent',
                        'min': 0,
                        'max': 100,
                        'thresholds': {
                            'steps': [
                                {'color': 'green', 'value': 0},
                                {'color': 'yellow', 'value': 70},
                                {'color': 'red', 'value': 90}
                            ]
                        }
                    }
                },
                'options': {
                    'showThresholdLabels': True,
                    'showThresholdMarkers': True
                }
            },
            {
                'id': 'memory_usage',
                'title': 'Memory Usage',
                'type': 'gauge',
                'grid_pos': {'x': 6, 'y': 20, 'w': 6, 'h': 4},
                'targets': [
                    {
                        'expr': f'process_resident_memory_bytes{{service="{service_name}"}} / 1024 / 1024',
                        'legendFormat': 'Memory MB'
                    }
                ],
                'field_config': {
                    'defaults': {
                        'color': {'mode': 'thresholds'},
                        'unit': 'decbytes',
                        'thresholds': {
                            'steps': [
                                {'color': 'green', 'value': 0},
                                {'color': 'yellow', 'value': 512000000},  # 512MB
                                {'color': 'red', 'value': 1024000000}     # 1GB
                            ]
                        }
                    }
                }
            },
            {
                'id': 'network_io',
                'title': 'Network I/O',
                'type': 'timeseries',
                'grid_pos': {'x': 12, 'y': 20, 'w': 6, 'h': 4},
                'targets': [
                    {
                        'expr': f'rate(process_network_receive_bytes_total{{service="{service_name}"}}[5m])',
                        'legendFormat': 'RX Bytes/s'
                    },
                    {
                        'expr': f'rate(process_network_transmit_bytes_total{{service="{service_name}"}}[5m])',
                        'legendFormat': 'TX Bytes/s'
                    }
                ],
                'field_config': {
                    'defaults': {
                        'color': {'mode': 'palette-classic'},
                        'unit': 'binBps'
                    }
                }
            },
            {
                'id': 'disk_io',
                'title': 'Disk I/O',
                'type': 'timeseries',
                'grid_pos': {'x': 18, 'y': 20, 'w': 6, 'h': 4},
                'targets': [
                    {
                        'expr': f'rate(process_disk_read_bytes_total{{service="{service_name}"}}[5m])',
                        'legendFormat': 'Read Bytes/s'
                    },
                    {
                        'expr': f'rate(process_disk_write_bytes_total{{service="{service_name}"}}[5m])',
                        'legendFormat': 'Write Bytes/s'
                    }
                ],
                'field_config': {
                    'defaults': {
                        'color': {'mode': 'palette-classic'},
                        'unit': 'binBps'
                    }
                }
            }
        ]

    def _create_api_specific_panels(self, service_def: Dict[str, Any]) -> List[Dict[str, Any]]:
        """Create API-specific panels."""
        service_name = service_def.get('name', 'service')
        
        return [
            {
                'id': 'endpoint_latency',
                'title': 'Top Slowest Endpoints',
                'type': 'table',
                'grid_pos': {'x': 0, 'y': 24, 'w': 12, 'h': 6},
                'targets': [
                    {
                        'expr': f'topk(10, histogram_quantile(0.95, sum by (handler) (rate(http_request_duration_seconds_bucket{{service="{service_name}"}}[5m])))) * 1000',
                        'legendFormat': '{{handler}}',
                        'format': 'table',
                        'instant': True
                    }
                ],
                'transformations': [
                    {
                        'id': 'organize',
                        'options': {
                            'excludeByName': {'Time': True},
                            'renameByName': {'Value': 'P95 Latency (ms)'}
                        }
                    }
                ],
                'field_config': {
                    'overrides': [
                        {
                            'matcher': {'id': 'byName', 'options': 'P95 Latency (ms)'},
                            'properties': [
                                {'id': 'color', 'value': {'mode': 'thresholds'}},
                                {'id': 'thresholds', 'value': {
                                    'steps': [
                                        {'color': 'green', 'value': 0},
                                        {'color': 'yellow', 'value': 100},
                                        {'color': 'red', 'value': 500}
                                    ]
                                }}
                            ]
                        }
                    ]
                }
            },
            {
                'id': 'request_size_distribution',
                'title': 'Request Size Distribution',
                'type': 'heatmap',
                'grid_pos': {'x': 12, 'y': 24, 'w': 12, 'h': 6},
                'targets': [
                    {
                        'expr': f'sum by (le) (rate(http_request_size_bytes_bucket{{service="{service_name}"}}[5m]))',
                        'legendFormat': '{{le}}'
                    }
                ],
                'options': {
                    'calculate': True,
                    'yAxis': {'unit': 'bytes'},
                    'color': {'scheme': 'Spectral'}
                }
            }
        ]

    def _create_database_specific_panels(self, service_def: Dict[str, Any]) -> List[Dict[str, Any]]:
        """Create database-specific panels."""
        service_name = service_def.get('name', 'service')
        
        return [
            {
                'id': 'db_connections',
                'title': 'Database Connections',
                'type': 'timeseries',
                'grid_pos': {'x': 0, 'y': 24, 'w': 8, 'h': 6},
                'targets': [
                    {
                        'expr': f'db_connections_active{{service="{service_name}"}}',
                        'legendFormat': 'Active Connections'
                    },
                    {
                        'expr': f'db_connections_idle{{service="{service_name}"}}',
                        'legendFormat': 'Idle Connections'
                    },
                    {
                        'expr': f'db_connections_max{{service="{service_name}"}}',
                        'legendFormat': 'Max Connections'
                    }
                ]
            },
            {
                'id': 'query_performance',
                'title': 'Query Performance',
                'type': 'timeseries',
                'grid_pos': {'x': 8, 'y': 24, 'w': 8, 'h': 6},
                'targets': [
                    {
                        'expr': f'rate(db_queries_total{{service="{service_name}"}}[5m])',
                        'legendFormat': 'Queries/sec'
                    },
                    {
                        'expr': f'rate(db_slow_queries_total{{service="{service_name}"}}[5m])',
                        'legendFormat': 'Slow Queries/sec'
                    }
                ]
            },
            {
                'id': 'db_locks',
                'title': 'Database Locks',
                'type': 'stat',
                'grid_pos': {'x': 16, 'y': 24, 'w': 8, 'h': 6},
                'targets': [
                    {
                        'expr': f'db_locks_waiting{{service="{service_name}"}}',
                        'legendFormat': 'Waiting Locks'
                    }
                ],
                'field_config': {
                    'defaults': {
                        'color': {'mode': 'thresholds'},
                        'thresholds': {
                            'steps': [
                                {'color': 'green', 'value': 0},
                                {'color': 'yellow', 'value': 1},
                                {'color': 'red', 'value': 5}
                            ]
                        }
                    }
                }
            }
        ]

    def _create_queue_specific_panels(self, service_def: Dict[str, Any]) -> List[Dict[str, Any]]:
        """Create queue-specific panels."""
        service_name = service_def.get('name', 'service')
        
        return [
            {
                'id': 'queue_depth',
                'title': 'Queue Depth',
                'type': 'timeseries',
                'grid_pos': {'x': 0, 'y': 24, 'w': 12, 'h': 6},
                'targets': [
                    {
                        'expr': f'queue_depth{{service="{service_name}"}}',
                        'legendFormat': 'Messages in Queue'
                    }
                ]
            },
            {
                'id': 'message_throughput',
                'title': 'Message Throughput',
                'type': 'timeseries',
                'grid_pos': {'x': 12, 'y': 24, 'w': 12, 'h': 6},
                'targets': [
                    {
                        'expr': f'rate(messages_published_total{{service="{service_name}"}}[5m])',
                        'legendFormat': 'Published/sec'
                    },
                    {
                        'expr': f'rate(messages_consumed_total{{service="{service_name}"}}[5m])',
                        'legendFormat': 'Consumed/sec'
                    }
                ]
            }
        ]

    def _create_business_metrics_panels(self, service_def: Dict[str, Any]) -> List[Dict[str, Any]]:
        """Create business metrics panels."""
        service_name = service_def.get('name', 'service')
        
        return [
            {
                'id': 'business_kpis',
                'title': 'Business KPIs',
                'type': 'stat',
                'grid_pos': {'x': 0, 'y': 30, 'w': 24, 'h': 4},
                'targets': [
                    {
                        'expr': f'rate(business_transactions_total{{service="{service_name}"}}[1h])',
                        'legendFormat': 'Transactions/hour'
                    },
                    {
                        'expr': f'avg(business_transaction_value{{service="{service_name}"}}) * rate(business_transactions_total{{service="{service_name}"}}[1h])',
                        'legendFormat': 'Revenue/hour'
                    },
                    {
                        'expr': f'rate(user_registrations_total{{service="{service_name}"}}[1h])',
                        'legendFormat': 'New Users/hour'
                    }
                ],
                'field_config': {
                    'defaults': {
                        'color': {'mode': 'palette-classic'},
                        'custom': {
                            'displayMode': 'basic'
                        }
                    }
                },
                'options': {
                    'orientation': 'horizontal',
                    'textMode': 'value_and_name'
                }
            }
        ]

    def _create_capacity_panels(self, service_def: Dict[str, Any]) -> List[Dict[str, Any]]:
        """Create capacity planning panels."""
        service_name = service_def.get('name', 'service')
        
        return [
            {
                'id': 'capacity_trends',
                'title': 'Capacity Trends (7d)',
                'type': 'timeseries',
                'grid_pos': {'x': 0, 'y': 34, 'w': 24, 'h': 6},
                'targets': [
                    {
                        'expr': f'predict_linear(avg_over_time(rate(http_requests_total{{service="{service_name}"}}[5m])[7d:1h]), 7*24*3600)',
                        'legendFormat': 'Predicted Traffic (7d)'
                    },
                    {
                        'expr': f'predict_linear(avg_over_time(process_resident_memory_bytes{{service="{service_name}"}}[7d:1h]), 7*24*3600)',
                        'legendFormat': 'Predicted Memory Usage (7d)'
                    }
                ],
                'field_config': {
                    'defaults': {
                        'color': {'mode': 'palette-classic'},
                        'custom': {
                            'drawStyle': 'line',
                            'lineStyle': {'dash': [10, 10]}
                        }
                    }
                }
            }
        ]

    def _generate_template_variables(self, service_def: Dict[str, Any]) -> List[Dict[str, Any]]:
        """Generate template variables for dynamic dashboard filtering."""
        service_name = service_def.get('name', 'service')
        
        return [
            {
                'name': 'environment',
                'type': 'query',
                'query': 'label_values(environment)',
                'current': {'text': 'production', 'value': 'production'},
                'includeAll': False,
                'multi': False,
                'refresh': 'on_dashboard_load'
            },
            {
                'name': 'instance',
                'type': 'query',
                'query': f'label_values(up{{service="{service_name}"}}, instance)',
                'current': {'text': 'All', 'value': '$__all'},
                'includeAll': True,
                'multi': True,
                'refresh': 'on_time_range_change'
            },
            {
                'name': 'handler',
                'type': 'query',
                'query': f'label_values(http_requests_total{{service="{service_name}"}}, handler)',
                'current': {'text': 'All', 'value': '$__all'},
                'includeAll': True,
                'multi': True,
                'refresh': 'on_time_range_change'
            }
        ]

    def _generate_alerts_integration(self, service_def: Dict[str, Any]) -> Dict[str, Any]:
        """Generate alerts integration configuration."""
        service_name = service_def.get('name', 'service')
        
        return {
            'alert_annotations': True,
            'alert_rules_query': f'ALERTS{{service="{service_name}"}}',
            'alert_panels': [
                {
                    'title': 'Active Alerts',
                    'type': 'table',
                    'query': f'ALERTS{{service="{service_name}",alertstate="firing"}}',
                    'columns': ['alertname', 'severity', 'instance', 'description']
                }
            ]
        }

    def _generate_drill_down_paths(self, service_def: Dict[str, Any]) -> Dict[str, Any]:
        """Generate drill-down navigation paths."""
        service_name = service_def.get('name', 'service')
        
        return {
            'service_overview': {
                'from': 'service_status',
                'to': 'detailed_health_dashboard',
                'url': f'/d/service-health/{service_name}-health',
                'params': ['var-service', 'var-environment']
            },
            'error_investigation': {
                'from': 'errors',
                'to': 'error_details_dashboard',
                'url': f'/d/errors/{service_name}-errors',
                'params': ['var-service', 'var-time_range']
            },
            'latency_analysis': {
                'from': 'latency',
                'to': 'trace_analysis_dashboard',
                'url': f'/d/traces/{service_name}-traces',
                'params': ['var-service', 'var-handler']
            },
            'capacity_planning': {
                'from': 'saturation',
                'to': 'capacity_dashboard',
                'url': f'/d/capacity/{service_name}-capacity',
                'params': ['var-service', 'var-time_range']
            }
        }

    def generate_grafana_json(self, dashboard_spec: Dict[str, Any]) -> Dict[str, Any]:
        """Convert dashboard specification to Grafana JSON format."""
        metadata = dashboard_spec['metadata']
        config = dashboard_spec['configuration']
        
        grafana_json = {
            'dashboard': {
                'id': None,
                'title': metadata['title'],
                'tags': [metadata['service']['type'], metadata['target_role'], 'generated'],
                'timezone': config['timezone'],
                'refresh': config['refresh_interval'],
                'time': {
                    'from': 'now-1h',
                    'to': 'now'
                },
                'templating': {
                    'list': dashboard_spec['variables']
                },
                'panels': self._convert_panels_to_grafana_format(dashboard_spec['panels']),
                'version': 1,
                'schemaVersion': 30
            },
            'overwrite': True
        }
        
        return grafana_json

    def _convert_panels_to_grafana_format(self, panels: List[Dict[str, Any]]) -> List[Dict[str, Any]]:
        """Convert panel specifications to Grafana format."""
        grafana_panels = []
        
        for panel in panels:
            grafana_panel = {
                'id': hash(panel['id']) % 1000,  # Generate numeric ID
                'title': panel['title'],
                'type': panel['type'],
                'gridPos': panel['grid_pos'],
                'targets': panel['targets'],
                'fieldConfig': panel.get('field_config', {}),
                'options': panel.get('options', {}),
                'transformations': panel.get('transformations', [])
            }
            grafana_panels.append(grafana_panel)
        
        return grafana_panels

    def generate_documentation(self, dashboard_spec: Dict[str, Any]) -> str:
        """Generate documentation for the dashboard."""
        metadata = dashboard_spec['metadata']
        service = metadata['service']
        
        doc_content = f"""# {metadata['title']} Documentation

## Overview
This dashboard provides comprehensive monitoring for {service['name']}, a {service['type']} service with {service['criticality']} criticality.

**Target Audience:** {metadata['target_role'].upper()} teams
**Generated:** {metadata['generated_at']}

## Dashboard Sections

### Service Overview
- **Service Status**: Real-time availability status
- **SLO Achievement**: 30-day SLO compliance metrics
- **Error Budget**: Remaining error budget visualization

### Golden Signals Monitoring
- **Latency**: P50, P95, P99 response times
- **Traffic**: Request rate by status code
- **Errors**: Error rates for 4xx and 5xx responses
- **Saturation**: CPU and memory utilization

### Resource Utilization
- **CPU Usage**: Process CPU consumption
- **Memory Usage**: Memory utilization tracking
- **Network I/O**: Network throughput metrics
- **Disk I/O**: Disk read/write operations

## Key Metrics

### SLIs Tracked
"""
        
        # Add service-type specific metrics
        service_type = service.get('type', 'api')
        if service_type in self.SERVICE_METRICS:
            metrics = self.SERVICE_METRICS[service_type]['key_metrics']
            for metric in metrics:
                doc_content += f"- `{metric}`: Core service metric\n"
        
        doc_content += f"""
## Alert Integration
- Active alerts are displayed in context with relevant panels
- Alert annotations show on time series charts
- Click-through to alert management system available

## Drill-Down Paths
"""
        
        drill_downs = dashboard_spec.get('drill_down_paths', {})
        for path_name, path_config in drill_downs.items():
            doc_content += f"- **{path_name}**: From {path_config['from']} → {path_config['to']}\n"
        
        doc_content += f"""
## Usage Guidelines

### Time Ranges
Use appropriate time ranges for different investigation types:
- **Real-time monitoring**: 15m - 1h
- **Recent incident investigation**: 1h - 6h  
- **Trend analysis**: 1d - 7d
- **Capacity planning**: 7d - 30d

### Variables
- **environment**: Filter by deployment environment
- **instance**: Focus on specific service instances
- **handler**: Filter by API endpoint or handler

### Performance Optimization
- Use longer time ranges for capacity planning
- Refresh intervals are optimized per role:
  - SRE: 30s for operational awareness
  - Developer: 1m for troubleshooting
  - Executive: 5m for high-level monitoring

## Maintenance
- Dashboard panels automatically adapt to service changes
- Template variables refresh based on actual metric labels
- Review and update business metrics quarterly
"""
        
        return doc_content

    def export_specification(self, dashboard_spec: Dict[str, Any], output_file: str, 
                           format_type: str = 'json'):
        """Export dashboard specification."""
        if format_type.lower() == 'json':
            with open(output_file, 'w') as f:
                json.dump(dashboard_spec, f, indent=2)
        elif format_type.lower() == 'grafana':
            grafana_json = self.generate_grafana_json(dashboard_spec)
            with open(output_file, 'w') as f:
                json.dump(grafana_json, f, indent=2)
        else:
            raise ValueError(f"Unsupported format: {format_type}")

    def print_summary(self, dashboard_spec: Dict[str, Any]):
        """Print human-readable summary of dashboard specification."""
        metadata = dashboard_spec['metadata']
        service = metadata['service']
        config = dashboard_spec['configuration']
        panels = dashboard_spec['panels']
        
        print(f"\n{'='*60}")
        print(f"DASHBOARD SPECIFICATION SUMMARY")
        print(f"{'='*60}")
        
        print(f"\nDashboard Details:")
        print(f"  Title: {metadata['title']}")
        print(f"  Target Role: {metadata['target_role'].upper()}")
        print(f"  Service: {service['name']} ({service['type']})")
        print(f"  Criticality: {service['criticality']}")
        print(f"  Generated: {metadata['generated_at']}")
        
        print(f"\nConfiguration:")
        print(f"  Default Time Range: {config['default_time_range']}")
        print(f"  Refresh Interval: {config['refresh_interval']}")
        print(f"  Available Time Ranges: {', '.join(config['time_ranges'])}")
        
        print(f"\nPanels ({len(panels)}):")
        panel_types = {}
        for panel in panels:
            panel_type = panel['type']
            panel_types[panel_type] = panel_types.get(panel_type, 0) + 1
        
        for panel_type, count in panel_types.items():
            print(f"  {panel_type}: {count}")
        
        variables = dashboard_spec.get('variables', [])
        print(f"\nTemplate Variables ({len(variables)}):")
        for var in variables:
            print(f"  {var['name']} ({var['type']})")
        
        drill_downs = dashboard_spec.get('drill_down_paths', {})
        print(f"\nDrill-down Paths: {len(drill_downs)}")
        
        print(f"\nKey Features:")
        print(f"  • Golden Signals monitoring")
        print(f"  • Resource utilization tracking")
        print(f"  • Alert integration")
        print(f"  • Role-optimized layout")
        print(f"  • Service-type specific panels")
        
        print(f"\n{'='*60}\n")


def main():
    """Main function for CLI usage."""
    parser = argparse.ArgumentParser(
        description='Generate comprehensive dashboard specifications',
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog="""
Examples:
    # Generate from service definition file
    python dashboard_generator.py --input service.json --output dashboard.json
    
    # Generate from command line parameters
    python dashboard_generator.py --service-type api --name "Payment Service" --output payment_dashboard.json
    
    # Generate Grafana-compatible JSON
    python dashboard_generator.py --input service.json --output dashboard.json --format grafana
    
    # Generate with specific role focus
    python dashboard_generator.py --service-type web --name "Frontend" --role developer --output frontend_dev.json
        """
    )
    
    parser.add_argument('--input', '-i',
                       help='Input service definition JSON file')
    parser.add_argument('--output', '-o', 
                       help='Output dashboard specification file')
    parser.add_argument('--service-type',
                       choices=['api', 'web', 'database', 'queue', 'batch', 'ml'],
                       help='Service type')
    parser.add_argument('--name',
                       help='Service name')
    parser.add_argument('--criticality',
                       choices=['critical', 'high', 'medium', 'low'],
                       default='medium',
                       help='Service criticality level')
    parser.add_argument('--role',
                       choices=['sre', 'developer', 'executive', 'ops'],
                       default='sre',
                       help='Target role for dashboard optimization')
    parser.add_argument('--format',
                       choices=['json', 'grafana'],
                       default='json',
                       help='Output format (json specification or grafana compatible)')
    parser.add_argument('--doc-output',
                       help='Generate documentation file')
    parser.add_argument('--summary-only', action='store_true',
                       help='Only display summary, do not save files')
    
    args = parser.parse_args()
    
    if not args.input and not (args.service_type and args.name):
        parser.error("Must provide either --input file or --service-type and --name")
    
    generator = DashboardGenerator()
    
    try:
        # Load or create service definition
        if args.input:
            service_def = generator.load_service_definition(args.input)
        else:
            service_def = generator.create_service_definition(
                args.service_type, args.name, args.criticality
            )
        
        # Generate dashboard specification
        dashboard_spec = generator.generate_dashboard_specification(service_def, args.role)
        
        # Output results
        if not args.summary_only:
            output_file = args.output or f"{service_def['name'].replace(' ', '_').lower()}_dashboard.json"
            generator.export_specification(dashboard_spec, output_file, args.format)
            print(f"Dashboard specification saved to: {output_file}")
            
            # Generate documentation if requested
            if args.doc_output:
                documentation = generator.generate_documentation(dashboard_spec)
                with open(args.doc_output, 'w') as f:
                    f.write(documentation)
                print(f"Documentation saved to: {args.doc_output}")
        
        # Always show summary
        generator.print_summary(dashboard_spec)
        
    except Exception as e:
        print(f"Error: {e}", file=sys.stderr)
        sys.exit(1)


if __name__ == '__main__':
    main()