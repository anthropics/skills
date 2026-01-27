from flask import Flask, request, jsonify, send_from_directory
from flask_cors import CORS
import anthropic
import os

app = Flask(__name__, static_folder='.')
CORS(app)

@app.route('/')
def index():
    return send_from_directory('.', 'index.html')

@app.route('/api/chat', methods=['POST'])
def chat():
    try:
        data = request.json
        api_key = data.get('apiKey')
        messages = data.get('messages')
        system_prompt = data.get('systemPrompt')

        if not api_key or not messages:
            return jsonify({'error': 'Missing required fields'}), 400

        client = anthropic.Anthropic(api_key=api_key)

        response = client.messages.create(
            model="claude-3-5-sonnet-20241022",
            max_tokens=1024,
            system=system_prompt,
            messages=messages
        )

        return jsonify({
            'response': response.content[0].text
        })

    except Exception as e:
        return jsonify({'error': str(e)}), 500

if __name__ == '__main__':
    app.run(host='0.0.0.0', port=8080)
