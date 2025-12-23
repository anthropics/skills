<!-- Block: Argument Section -->
{% for argument in arguments %}
{{ argument.heading }}
{{ argument.text }}

{% if argument.footnotes %}
{% for footnote in argument.footnotes %}
{{ footnote.marker }} {{ footnote.text }}
{% endfor %}

{% endif %}
{% endfor %}
