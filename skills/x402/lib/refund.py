"""Refund handling: parse and internalize server-to-client refund payments."""

import base64
import logging
from lib.metanet import internalize_action

log = logging.getLogger(__name__)


class RefundInfo:
    """Parsed refund data from a server error response."""
    def __init__(self, transaction, derivation_prefix, derivation_suffix,
                 sender_identity_key, satoshis, txid):
        self.transaction = transaction
        self.derivation_prefix = derivation_prefix
        self.derivation_suffix = derivation_suffix
        self.sender_identity_key = sender_identity_key
        self.satoshis = satoshis
        self.txid = txid

    def __repr__(self):
        return f"RefundInfo(sats={self.satoshis}, txid={self.txid[:16]}...)"


def parse_refund(response_body):
    """Extract refund info from a server response body. Returns None if absent."""
    refund = response_body.get("refund")
    if not refund or not isinstance(refund, dict):
        return None
    if refund.get("already_refunded"):
        log.info("Refund already issued: txid=%s", refund.get("txid"))
        return None
    required = ["transaction", "derivationPrefix", "derivationSuffix",
                "senderIdentityKey", "satoshis", "txid"]
    missing = [k for k in required if k not in refund]
    if missing:
        log.warning("Incomplete refund data, missing: %s", missing)
        return None
    return RefundInfo(
        transaction=refund["transaction"],
        derivation_prefix=refund["derivationPrefix"],
        derivation_suffix=refund["derivationSuffix"],
        sender_identity_key=refund["senderIdentityKey"],
        satoshis=refund["satoshis"],
        txid=refund["txid"],
    )


def process_refund(refund):
    """Internalize a refund transaction into the client's wallet."""
    tx_bytes = base64.b64decode(refund.transaction)
    log.info("Internalizing refund: %d sats, txid=%s", refund.satoshis, refund.txid[:16])
    result = internalize_action(
        tx_bytes=tx_bytes,
        outputs=[{
            "outputIndex": 0,
            "protocol": "wallet payment",
            "paymentRemittance": {
                "derivationPrefix": refund.derivation_prefix,
                "derivationSuffix": refund.derivation_suffix,
                "senderIdentityKey": refund.sender_identity_key,
            },
        }],
        description=f"Refund: {refund.satoshis} sats (txid: {refund.txid[:16]}...)",
    )
    log.info("Refund result: accepted=%s", result.get("accepted"))
    return result
