<!-- Block: Certificate of Service -->
I certify that on {{ service_date }} I served this motion on:
{% for recipient in service_list %}
- {{ recipient }}
{% endfor %}
