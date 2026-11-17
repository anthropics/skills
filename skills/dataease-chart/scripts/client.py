import json
import time
import uuid
import base64
import requests
import jwt
from cryptography.hazmat.primitives.ciphers import Cipher, algorithms, modes
from cryptography.hazmat.primitives import padding
from cryptography.hazmat.backends import default_backend
import urllib3

urllib3.disable_warnings()

class DataEaseClient:
    def __init__(self, base_url, access_key, secret_key):
        self.base_url = base_url.rstrip('/')
        self.access_key = access_key
        self.secret_key = secret_key

    def _get_signature(self, uid, timestamp):
        src_str = f"{self.access_key}|{uid}|{timestamp}"
        padder = padding.PKCS7(128).padder()
        padded_data = padder.update(src_str.encode('utf-8')) + padder.finalize()
        cipher = Cipher(
            algorithms.AES(self.secret_key.encode('utf-8')),
            modes.CBC(self.access_key.encode('utf-8')),
            backend=default_backend()
        )
        encryptor = cipher.encryptor()
        ciphertext = encryptor.update(padded_data) + encryptor.finalize()
        return base64.b64encode(ciphertext).decode('utf-8')

    def _get_headers(self):
        timestamp = str(int(time.time() * 1000))
        uid = str(uuid.uuid4())
        signature = self._get_signature(uid, timestamp)
        claims = {
            "accessKey": self.access_key,
            "signature": signature
        }
        token = jwt.encode(claims, self.secret_key, algorithm="HS256")
        if isinstance(token, bytes):
            token = token.decode('utf-8')
        
        return {
            "accessKey": self.access_key,
            "signature": signature,
            "x-de-ask-token": token,
            "timestamp": timestamp,
            "nonce": uid,
            "Content-Type": "application/json"
        }

    def get(self, path, params=None):
        url = f"{self.base_url}{path}"
        response = requests.get(url, headers=self._get_headers(), params=params, verify=False)
        return response

    def post(self, path, payload=None):
        url = f"{self.base_url}{path}"
        response = requests.post(url, headers=self._get_headers(), json=payload, verify=False)
        return response

    def get_dataset_fields(self, dataset_id):
        return self.post(f"/datasetField/listByDatasetGroup/{dataset_id}").json()

    def update_publish_status(self, dashboard_id, name, status=1, type='dashboard', mobile_layout=False, active_view_ids=None):
        url = f"{self.base_url}/dataVisualization/updatePublishStatus"
        payload = {
            "id": dashboard_id,
            "name": name,
            "mobileLayout": mobile_layout,
            "activeViewIds": active_view_ids or [],
            "status": status,
            "type": type
        }
        response = requests.post(url, headers=self._get_headers(), json=payload, verify=False)
        response.raise_for_status()
        return response.json()
