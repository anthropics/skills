<!-- Block: Requested Relief & Conclusion -->
For these reasons, {{moving_party}} asks the Court to grant the following relief:
{% for item in relief_requested %}
- {{ item }}
{% endfor %}

Respectfully submitted,
{{signature_block}}
