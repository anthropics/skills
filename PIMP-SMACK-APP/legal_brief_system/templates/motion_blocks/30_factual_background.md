<!-- Block: Factual Background -->
{% for fact in motion_facts %}
{{ fact.statement }}{% if fact.record_cite %} {{ fact.record_cite }}{% endif %}

{% endfor %}
