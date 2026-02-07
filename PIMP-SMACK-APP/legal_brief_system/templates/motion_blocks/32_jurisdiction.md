<!-- Block: Jurisdiction / Authority -->
{% for block in jurisdiction_blocks %}
{{ block.text }}{% if block.cite %} {{ block.cite }}{% endif %}

{% endfor %}
