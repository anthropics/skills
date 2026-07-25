# Cryptography Implementation Guide

Practical cryptographic patterns for securing data at rest, in transit, and in use.

---

## Table of Contents

- [Cryptographic Primitives](#cryptographic-primitives)
- [Symmetric Encryption](#symmetric-encryption)
- [Asymmetric Encryption](#asymmetric-encryption)
- [Hashing and Password Storage](#hashing-and-password-storage)
- [Key Management](#key-management)
- [Common Cryptographic Mistakes](#common-cryptographic-mistakes)

---

## Cryptographic Primitives

### Algorithm Selection Guide

| Use Case | Recommended Algorithm | Avoid |
|----------|----------------------|-------|
| Symmetric encryption | AES-256-GCM, ChaCha20-Poly1305 | DES, 3DES, AES-ECB, RC4 |
| Asymmetric encryption | RSA-OAEP (2048+), ECIES | RSA-PKCS1v1.5 |
| Digital signatures | Ed25519, ECDSA P-256, RSA-PSS | RSA-PKCS1v1.5 |
| Key exchange | X25519, ECDH P-256 | RSA key transport |
| Password hashing | Argon2id, bcrypt, scrypt | MD5, SHA-1, plain SHA-256 |
| Message authentication | HMAC-SHA256, Poly1305 | MD5, SHA-1 |
| Random generation | OS CSPRNG | Math.random(), time-based |

### Security Strength Comparison

| Key Size | Security Level | Equivalent Symmetric |
|----------|----------------|---------------------|
| RSA 2048 | 112 bits | AES-128 |
| RSA 3072 | 128 bits | AES-128 |
| RSA 4096 | 152 bits | AES-192 |
| ECDSA P-256 | 128 bits | AES-128 |
| ECDSA P-384 | 192 bits | AES-192 |
| Ed25519 | 128 bits | AES-128 |

---

## Symmetric Encryption

### AES-256-GCM Implementation

```python
from cryptography.hazmat.primitives.ciphers.aead import AESGCM
import os

class AESGCMEncryption:
    """
    AES-256-GCM authenticated encryption.

    Provides both confidentiality and integrity.
    GCM mode prevents tampering with authentication tag.
    """

    def __init__(self, key: bytes = None):
        if key is None:
            key = AESGCM.generate_key(bit_length=256)
        if len(key) != 32:
            raise ValueError("Key must be 32 bytes (256 bits)")
        self.key = key
        self.aesgcm = AESGCM(key)

    def encrypt(self, plaintext: bytes, associated_data: bytes = None) -> bytes:
        """
        Encrypt with random nonce.

        Returns: nonce (12 bytes) + ciphertext + tag (16 bytes)
        """
        nonce = os.urandom(12)  # 96-bit nonce for GCM
        ciphertext = self.aesgcm.encrypt(nonce, plaintext, associated_data)
        return nonce + ciphertext

    def decrypt(self, ciphertext: bytes, associated_data: bytes = None) -> bytes:
        """
        Decrypt and verify authentication tag.

        Raises InvalidTag if tampered.
        """
        nonce = ciphertext[:12]
        actual_ciphertext = ciphertext[12:]
        return self.aesgcm.decrypt(nonce, actual_ciphertext, associated_data)


# Usage
encryptor = AESGCMEncryption()
plaintext = b"Sensitive data to encrypt"
aad = b"user_id:12345"  # Authenticated but not encrypted

ciphertext = encryptor.encrypt(plaintext, associated_data=aad)
decrypted = encryptor.decrypt(ciphertext, associated_data=aad)
```

### ChaCha20-Poly1305 Implementation

```python
from cryptography.hazmat.primitives.ciphers.aead import ChaCha20Poly1305
import os

class ChaChaEncryption:
    """
    ChaCha20-Poly1305 authenticated encryption.

    Faster than AES on systems without hardware AES support.
    Resistant to timing attacks (constant-time implementation).
    """

    def __init__(self, key: bytes = None):
        if key is None:
            key = ChaCha20Poly1305.generate_key()
        self.key = key
        self.chacha = ChaCha20Poly1305(key)

    def encrypt(self, plaintext: bytes, associated_data: bytes = None) -> bytes:
        """Encrypt with random 96-bit nonce."""
        nonce = os.urandom(12)
        ciphertext = self.chacha.encrypt(nonce, plaintext, associated_data)
        return nonce + ciphertext

    def decrypt(self, ciphertext: bytes, associated_data: bytes = None) -> bytes:
        """Decrypt and verify Poly1305 authentication tag."""
        nonce = ciphertext[:12]
        actual_ciphertext = ciphertext[12:]
        return self.chacha.decrypt(nonce, actual_ciphertext, associated_data)
```

### Envelope Encryption Pattern

```python
"""
Envelope Encryption: Encrypt data with a Data Encryption Key (DEK),
then encrypt DEK with a Key Encryption Key (KEK).

Benefits:
- KEK can be rotated without re-encrypting data
- DEK can be stored alongside encrypted data
- Enables per-record encryption with different DEKs
"""

from cryptography.hazmat.primitives.ciphers.aead import AESGCM
from cryptography.hazmat.primitives import serialization
from cryptography.hazmat.primitives.asymmetric import padding
from cryptography.hazmat.primitives import hashes
import os
import json
import base64

class EnvelopeEncryption:
    def __init__(self, kek_public_key, kek_private_key=None):
        self.kek_public = kek_public_key
        self.kek_private = kek_private_key

    def encrypt(self, plaintext: bytes) -> dict:
        """
        1. Generate random DEK
        2. Encrypt plaintext with DEK
        3. Encrypt DEK with KEK
        4. Return encrypted DEK + encrypted data
        """
        # Generate Data Encryption Key
        dek = AESGCM.generate_key(bit_length=256)
        aesgcm = AESGCM(dek)

        # Encrypt data with DEK
        nonce = os.urandom(12)
        encrypted_data = aesgcm.encrypt(nonce, plaintext, None)

        # Encrypt DEK with KEK (RSA-OAEP)
        encrypted_dek = self.kek_public.encrypt(
            dek,
            padding.OAEP(
                mgf=padding.MGF1(algorithm=hashes.SHA256()),
                algorithm=hashes.SHA256(),
                label=None
            )
        )

        return {
            'encrypted_dek': base64.b64encode(encrypted_dek).decode(),
            'nonce': base64.b64encode(nonce).decode(),
            'ciphertext': base64.b64encode(encrypted_data).decode()
        }

    def decrypt(self, envelope: dict) -> bytes:
        """
        1. Decrypt DEK with KEK
        2. Decrypt data with DEK
        """
        if self.kek_private is None:
            raise ValueError("Private key required for decryption")

        # Decrypt DEK
        encrypted_dek = base64.b64decode(envelope['encrypted_dek'])
        dek = self.kek_private.decrypt(
            encrypted_dek,
            padding.OAEP(
                mgf=padding.MGF1(algorithm=hashes.SHA256()),
                algorithm=hashes.SHA256(),
                label=None
            )
        )

        # Decrypt data
        aesgcm = AESGCM(dek)
        nonce = base64.b64decode(envelope['nonce'])
        ciphertext = base64.b64decode(envelope['ciphertext'])

        return aesgcm.decrypt(nonce, ciphertext, None)
```

---

## Asymmetric Encryption

### RSA Key Generation and Usage

```python
from cryptography.hazmat.primitives.asymmetric import rsa, padding
from cryptography.hazmat.primitives import hashes, serialization

def generate_rsa_keypair(key_size=4096):
    """Generate RSA key pair for encryption/signing."""
    private_key = rsa.generate_private_key(
        public_exponent=65537,
        key_size=key_size
    )
    public_key = private_key.public_key()

    return private_key, public_key

def serialize_keys(private_key, public_key, password=None):
    """Serialize keys for storage."""
    # Private key (encrypted with password)
    if password:
        encryption = serialization.BestAvailableEncryption(password.encode())
    else:
        encryption = serialization.NoEncryption()

    private_pem = private_key.private_bytes(
        encoding=serialization.Encoding.PEM,
        format=serialization.PrivateFormat.PKCS8,
        encryption_algorithm=encryption
    )

    # Public key
    public_pem = public_key.public_bytes(
        encoding=serialization.Encoding.PEM,
        format=serialization.PublicFormat.SubjectPublicKeyInfo
    )

    return private_pem, public_pem

def rsa_encrypt(public_key, plaintext: bytes) -> bytes:
    """RSA-OAEP encryption (for small data like keys)."""
    return public_key.encrypt(
        plaintext,
        padding.OAEP(
            mgf=padding.MGF1(algorithm=hashes.SHA256()),
            algorithm=hashes.SHA256(),
            label=None
        )
    )

def rsa_decrypt(private_key, ciphertext: bytes) -> bytes:
    """RSA-OAEP decryption."""
    return private_key.decrypt(
        ciphertext,
        padding.OAEP(
            mgf=padding.MGF1(algorithm=hashes.SHA256()),
            algorithm=hashes.SHA256(),
            label=None
        )
    )
```

### Digital Signatures (Ed25519)

```python
from cryptography.hazmat.primitives.asymmetric.ed25519 import (
    Ed25519PrivateKey, Ed25519PublicKey
)

class Ed25519Signer:
    """
    Ed25519 digital signatures.

    Fast, secure, and deterministic.
    256-bit keys provide 128-bit security.
    """

    def __init__(self, private_key=None):
        if private_key is None:
            private_key = Ed25519PrivateKey.generate()
        self.private_key = private_key
        self.public_key = private_key.public_key()

    def sign(self, message: bytes) -> bytes:
        """Create digital signature."""
        return self.private_key.sign(message)

    def verify(self, message: bytes, signature: bytes) -> bool:
        """Verify digital signature."""
        try:
            self.public_key.verify(signature, message)
            return True
        except Exception:
            return False

    def get_public_key_bytes(self) -> bytes:
        """Export public key for verification."""
        return self.public_key.public_bytes(
            encoding=serialization.Encoding.Raw,
            format=serialization.PublicFormat.Raw
        )


# Usage for message signing
signer = Ed25519Signer()
message = b"Important document content"
signature = signer.sign(message)

# Verification (can be done with public key only)
is_valid = signer.verify(message, signature)
```

### ECDH Key Exchange

```python
from cryptography.hazmat.primitives.asymmetric import x25519
from cryptography.hazmat.primitives.kdf.hkdf import HKDF
from cryptography.hazmat.primitives import hashes

class X25519KeyExchange:
    """
    X25519 Diffie-Hellman key exchange.

    Used to establish shared secrets over insecure channels.
    """

    def __init__(self):
        self.private_key = x25519.X25519PrivateKey.generate()
        self.public_key = self.private_key.public_key()

    def get_public_key_bytes(self) -> bytes:
        """Get public key to send to peer."""
        return self.public_key.public_bytes(
            encoding=serialization.Encoding.Raw,
            format=serialization.PublicFormat.Raw
        )

    def derive_shared_key(self, peer_public_key_bytes: bytes,
                          info: bytes = b"") -> bytes:
        """
        Derive shared encryption key from peer's public key.

        Uses HKDF to derive a proper encryption key.
        """
        peer_public_key = x25519.X25519PublicKey.from_public_bytes(
            peer_public_key_bytes
        )

        shared_secret = self.private_key.exchange(peer_public_key)

        # Derive encryption key using HKDF
        derived_key = HKDF(
            algorithm=hashes.SHA256(),
            length=32,
            salt=None,
            info=info,
        ).derive(shared_secret)

        return derived_key


# Key exchange example
alice = X25519KeyExchange()
bob = X25519KeyExchange()

# Exchange public keys (can be done over insecure channel)
alice_public = alice.get_public_key_bytes()
bob_public = bob.get_public_key_bytes()

# Both derive the same shared key
alice_shared = alice.derive_shared_key(bob_public, info=b"session-key")
bob_shared = bob.derive_shared_key(alice_public, info=b"session-key")

assert alice_shared == bob_shared  # Same key!
```

---

## Hashing and Password Storage

### Password Hashing with Argon2

```python
import argon2
from argon2 import PasswordHasher, Type

class SecurePasswordHasher:
    """
    Argon2id password hashing.

    Argon2id combines resistance to:
    - GPU attacks (memory-hard)
    - Side-channel attacks (data-independent)
    """

    def __init__(self):
        # OWASP recommended parameters
        self.hasher = PasswordHasher(
            time_cost=3,        # Iterations
            memory_cost=65536,  # 64 MB
            parallelism=4,      # Threads
            hash_len=32,        # Output length
            type=Type.ID        # Argon2id variant
        )

    def hash_password(self, password: str) -> str:
        """
        Hash password for storage.

        Returns encoded string with algorithm parameters and salt.
        """
        return self.hasher.hash(password)

    def verify_password(self, password: str, hash: str) -> bool:
        """
        Verify password against stored hash.

        Automatically handles timing-safe comparison.
        """
        try:
            self.hasher.verify(hash, password)
            return True
        except argon2.exceptions.VerifyMismatchError:
            return False

    def needs_rehash(self, hash: str) -> bool:
        """Check if hash needs upgrading to current parameters."""
        return self.hasher.check_needs_rehash(hash)


# Usage
hasher = SecurePasswordHasher()

# During registration
password = "user_password_123!"
password_hash = hasher.hash_password(password)
# Store password_hash in database

# During login
stored_hash = password_hash  # From database
if hasher.verify_password("user_password_123!", stored_hash):
    print("Login successful")

    # Check if hash needs upgrading
    if hasher.needs_rehash(stored_hash):
        new_hash = hasher.hash_password(password)
        # Update stored hash
```

### Bcrypt Alternative

```python
import bcrypt

class BcryptHasher:
    """
    Bcrypt password hashing.

    Well-established, widely supported.
    Use when Argon2 is not available.
    """

    def __init__(self, rounds=12):
        self.rounds = rounds

    def hash_password(self, password: str) -> str:
        salt = bcrypt.gensalt(rounds=self.rounds)
        return bcrypt.hashpw(password.encode(), salt).decode()

    def verify_password(self, password: str, hash: str) -> bool:
        return bcrypt.checkpw(password.encode(), hash.encode())
```

### HMAC for Message Authentication

```python
import hmac
import hashlib
import secrets

def create_hmac(key: bytes, message: bytes) -> bytes:
    """Create HMAC-SHA256 authentication tag."""
    return hmac.new(key, message, hashlib.sha256).digest()

def verify_hmac(key: bytes, message: bytes, tag: bytes) -> bool:
    """Verify HMAC in constant time."""
    expected = hmac.new(key, message, hashlib.sha256).digest()
    return hmac.compare_digest(expected, tag)

# API request signing example
def sign_api_request(secret_key: bytes, method: str, path: str,
                     body: bytes, timestamp: str) -> str:
    """Sign API request for authentication."""
    message = f"{method}\n{path}\n{timestamp}\n".encode() + body
    signature = create_hmac(secret_key, message)
    return signature.hex()
```

---

## Key Management

### Key Derivation Functions

```python
from cryptography.hazmat.primitives.kdf.pbkdf2 import PBKDF2HMAC
from cryptography.hazmat.primitives.kdf.scrypt import Scrypt
from cryptography.hazmat.primitives import hashes
import os

def derive_key_pbkdf2(password: str, salt: bytes = None,
                       iterations: int = 600000) -> tuple:
    """
    Derive encryption key from password using PBKDF2.

    NIST recommends minimum 600,000 iterations for PBKDF2-SHA256.
    """
    if salt is None:
        salt = os.urandom(16)

    kdf = PBKDF2HMAC(
        algorithm=hashes.SHA256(),
        length=32,
        salt=salt,
        iterations=iterations
    )

    key = kdf.derive(password.encode())
    return key, salt

def derive_key_scrypt(password: str, salt: bytes = None) -> tuple:
    """
    Derive key using scrypt (memory-hard).

    More resistant to hardware attacks than PBKDF2.
    """
    if salt is None:
        salt = os.urandom(16)

    kdf = Scrypt(
        salt=salt,
        length=32,
        n=2**17,  # CPU/memory cost
        r=8,      # Block size
        p=1       # Parallelization
    )

    key = kdf.derive(password.encode())
    return key, salt
```

### Key Rotation Strategy

```python
from datetime import datetime, timedelta
from typing import Dict, Optional
import json

class KeyManager:
    """
    Manage encryption key lifecycle.

    Supports key rotation without data re-encryption.
    """

    def __init__(self, storage_backend):
        self.storage = storage_backend

    def generate_key(self, key_id: str, algorithm: str = 'AES-256-GCM') -> dict:
        """Generate and store new encryption key."""
        key_material = os.urandom(32)

        key_metadata = {
            'key_id': key_id,
            'algorithm': algorithm,
            'created_at': datetime.utcnow().isoformat(),
            'expires_at': (datetime.utcnow() + timedelta(days=365)).isoformat(),
            'status': 'active'
        }

        self.storage.store_key(key_id, key_material, key_metadata)
        return key_metadata

    def rotate_key(self, old_key_id: str) -> dict:
        """
        Rotate encryption key.

        1. Mark old key as 'decrypt-only'
        2. Generate new key as 'active'
        3. Old key can still decrypt, new key encrypts
        """
        # Mark old key as decrypt-only
        old_metadata = self.storage.get_key_metadata(old_key_id)
        old_metadata['status'] = 'decrypt-only'
        self.storage.update_key_metadata(old_key_id, old_metadata)

        # Generate new key
        new_key_id = f"{old_key_id.rsplit('_', 1)[0]}_{datetime.utcnow().strftime('%Y%m%d')}"
        return self.generate_key(new_key_id)

    def get_encryption_key(self) -> tuple:
        """Get current active key for encryption."""
        return self.storage.get_active_key()

    def get_decryption_key(self, key_id: str) -> bytes:
        """Get specific key for decryption."""
        return self.storage.get_key(key_id)
```

### Hardware Security Module Integration

```python
# AWS CloudHSM / KMS integration pattern
import boto3

class AWSKMSProvider:
    """
    AWS KMS integration for key management.

    Keys never leave AWS infrastructure.
    """

    def __init__(self, key_id: str, region: str = 'us-east-1'):
        self.kms = boto3.client('kms', region_name=region)
        self.key_id = key_id

    def encrypt(self, plaintext: bytes) -> bytes:
        """Encrypt using KMS master key."""
        response = self.kms.encrypt(
            KeyId=self.key_id,
            Plaintext=plaintext
        )
        return response['CiphertextBlob']

    def decrypt(self, ciphertext: bytes) -> bytes:
        """Decrypt using KMS master key."""
        response = self.kms.decrypt(
            KeyId=self.key_id,
            CiphertextBlob=ciphertext
        )
        return response['Plaintext']

    def generate_data_key(self) -> tuple:
        """Generate data encryption key."""
        response = self.kms.generate_data_key(
            KeyId=self.key_id,
            KeySpec='AES_256'
        )
        return response['Plaintext'], response['CiphertextBlob']
```

---

## Common Cryptographic Mistakes

### Mistake 1: Using ECB Mode

```python
# BAD: ECB mode reveals patterns
from cryptography.hazmat.primitives.ciphers import Cipher, algorithms, modes

def bad_ecb_encrypt(key, plaintext):
    cipher = Cipher(algorithms.AES(key), modes.ECB())
    encryptor = cipher.encryptor()
    return encryptor.update(plaintext) + encryptor.finalize()

# GOOD: Use authenticated encryption (GCM)
from cryptography.hazmat.primitives.ciphers.aead import AESGCM

def good_gcm_encrypt(key, plaintext):
    aesgcm = AESGCM(key)
    nonce = os.urandom(12)
    return nonce + aesgcm.encrypt(nonce, plaintext, None)
```

### Mistake 2: Reusing Nonces

```python
# BAD: Static nonce
nonce = b"fixed_nonce!"  # NEVER DO THIS

# GOOD: Random nonce per encryption
nonce = os.urandom(12)

# ALSO GOOD: Counter-based nonce (if you can guarantee no repeats)
class NonceCounter:
    def __init__(self):
        self.counter = 0

    def get_nonce(self):
        self.counter += 1
        return self.counter.to_bytes(12, 'big')
```

### Mistake 3: Rolling Your Own Crypto

```python
# BAD: Custom "encryption"
def bad_encrypt(data, key):
    return bytes([b ^ k for b, k in zip(data, key * len(data))])

# GOOD: Use established libraries
from cryptography.fernet import Fernet

def good_encrypt(data, key):
    f = Fernet(key)
    return f.encrypt(data)
```

### Mistake 4: Weak Random Generation

```python
import random
import secrets

# BAD: Predictable random
def bad_generate_token():
    return ''.join(random.choices('abcdef0123456789', k=32))

# GOOD: Cryptographically secure
def good_generate_token():
    return secrets.token_hex(16)
```

### Mistake 5: Timing Attacks in Comparison

```python
# BAD: Early exit reveals length
def bad_compare(a, b):
    if len(a) != len(b):
        return False
    for x, y in zip(a, b):
        if x != y:
            return False
    return True

# GOOD: Constant-time comparison
import hmac

def good_compare(a, b):
    return hmac.compare_digest(a, b)
```

---

## Quick Reference Card

| Operation | Algorithm | Key Size | Notes |
|-----------|-----------|----------|-------|
| Symmetric encryption | AES-256-GCM | 256 bits | Use random 96-bit nonce |
| Alternative encryption | ChaCha20-Poly1305 | 256 bits | Faster on non-AES hardware |
| Asymmetric encryption | RSA-OAEP | 2048+ bits | Only for small data/keys |
| Key exchange | X25519 | 256 bits | Derive key with HKDF |
| Digital signature | Ed25519 | 256 bits | Fast, deterministic |
| Password hashing | Argon2id | - | 64MB memory, 3 iterations |
| Message authentication | HMAC-SHA256 | 256 bits | Use for API signing |
| Key derivation | PBKDF2-SHA256 | - | 600,000+ iterations |
