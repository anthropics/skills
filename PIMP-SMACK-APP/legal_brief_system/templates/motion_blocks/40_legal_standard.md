<!-- Block: Legal Standard -->
{{ legal_standard.heading }}
{% for point in legal_standard.points %}
- {{ point }}
{% endfor %}

Authorities: {{ supporting_citations | join(", ") }}
