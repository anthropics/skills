<!-- Block: Attachments -->
{% if attachments %}
Attachments:
{% for attachment in attachments %}
Exhibit {{ loop.index }} – {{ attachment }}
{% endfor %}
{% endif %}
