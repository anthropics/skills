<!-- Block: Introduction & Relief Summary -->
Pursuant to FRAP 27 and Ninth Cir. R. 27-1, {{moving_party}} respectfully requests:
{% for item in relief_requested %}
{{ loop.index }}. {{ item }}
{% endfor %}

Immediate relief is necessary because {{emergency_basis}}.
