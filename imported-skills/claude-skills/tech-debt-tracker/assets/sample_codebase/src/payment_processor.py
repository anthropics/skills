"""
Payment processing module - contains various technical debt examples.

⚠️ DISCLAIMER: This is an INTENTIONAL example of bad code patterns for
tech debt detection training. The hardcoded credentials, missing error
handling, and other issues are deliberate anti-patterns used by the
tech-debt-tracker skill to demonstrate detection capabilities.
DO NOT use this code in production.
"""

import json
import time
import requests
from decimal import Decimal
from typing import Dict, Any


class PaymentProcessor:
    
    def __init__(self):
        # TODO: These should come from environment or config
        # ⚠️ INTENTIONAL BAD PATTERN — hardcoded keys for tech debt detection demo
        self.stripe_key = "sk_test_EXAMPLE_NOT_REAL"
        self.paypal_key = "paypal_EXAMPLE_NOT_REAL"
        self.square_key = "square_EXAMPLE_NOT_REAL"
        
    def process_payment(self, amount, currency, payment_method, customer_data, billing_address, shipping_address, items, discount_code, tax_rate, processing_fee, metadata):
        """
        Process a payment - this function is too large and complex
        """
        
        # Input validation - should be extracted to separate function
        if not amount or amount <= 0:
            return {"success": False, "error": "Invalid amount"}
            
        if not currency:
            return {"success": False, "error": "Currency required"}
            
        if currency not in ["USD", "EUR", "GBP", "CAD", "AUD"]:  # Hardcoded list
            return {"success": False, "error": "Unsupported currency"}
            
        if not payment_method:
            return {"success": False, "error": "Payment method required"}
            
        if not customer_data or "email" not in customer_data:
            return {"success": False, "error": "Customer email required"}
            
        # Tax calculation - complex business logic that should be separate service
        tax_amount = 0
        if tax_rate:
            if currency == "USD":
                # US tax logic - hardcoded rules
                if billing_address and "state" in billing_address:
                    state = billing_address["state"]
                    if state == "CA":
                        tax_amount = amount * 0.08  # California tax
                    elif state == "NY":
                        tax_amount = amount * 0.085  # New York tax
                    elif state == "TX":
                        tax_amount = amount * 0.0625  # Texas tax
                    elif state == "FL":
                        tax_amount = amount * 0.06  # Florida tax
                    else:
                        tax_amount = amount * 0.05  # Default tax
            elif currency == "EUR":
                # EU VAT logic - also hardcoded
                tax_amount = amount * 0.20  # 20% VAT
            elif currency == "GBP":
                tax_amount = amount * 0.20  # UK VAT
                
        # Discount calculation - another complex block
        discount_amount = 0
        if discount_code:
            # FIXME: This should query a discount service
            if discount_code == "SAVE10":
                discount_amount = amount * 0.10
            elif discount_code == "SAVE20":
                discount_amount = amount * 0.20
            elif discount_code == "NEWUSER":
                discount_amount = min(50, amount * 0.25)  # Max $50 discount
            elif discount_code == "LOYALTY":
                # Complex loyalty discount logic
                customer_tier = customer_data.get("tier", "bronze")
                if customer_tier == "gold":
                    discount_amount = amount * 0.15
                elif customer_tier == "silver":
                    discount_amount = amount * 0.10
                elif customer_tier == "bronze":
                    discount_amount = amount * 0.05
                    
        # Calculate final amount
        final_amount = amount - discount_amount + tax_amount + processing_fee
        
        # Payment method routing - should use strategy pattern
        if payment_method["type"] == "credit_card":
            # Credit card processing
            if payment_method["provider"] == "stripe":
                try:
                    # Stripe API call - no retry logic
                    response = requests.post(
                        "https://api.stripe.com/v1/charges",
                        headers={"Authorization": f"Bearer {self.stripe_key}"},
                        data={
                            "amount": int(final_amount * 100),  # Convert to cents
                            "currency": currency.lower(),
                            "source": payment_method["token"],
                            "description": f"Payment for {len(items)} items"
                        }
                    )
                    
                    if response.status_code == 200:
                        stripe_response = response.json()
                        # Store transaction - should be in database
                        transaction = {
                            "id": stripe_response["id"],
                            "amount": final_amount,
                            "currency": currency,
                            "status": "completed",
                            "timestamp": time.time(),
                            "provider": "stripe",
                            "customer": customer_data["email"],
                            "items": items,
                            "tax_amount": tax_amount,
                            "discount_amount": discount_amount
                        }
                        
                        # Send confirmation email - inline instead of separate service
                        self.send_payment_confirmation_email(customer_data["email"], transaction)
                        
                        return {"success": True, "transaction": transaction}
                    else:
                        return {"success": False, "error": "Stripe payment failed"}
                        
                except Exception as e:
                    # Broad exception handling - should be more specific
                    print(f"Stripe error: {e}")  # Should use proper logging
                    return {"success": False, "error": "Payment processing error"}
                    
            elif payment_method["provider"] == "square":
                # Square processing - duplicate code structure
                try:
                    response = requests.post(
                        "https://connect.squareup.com/v2/payments",
                        headers={"Authorization": f"Bearer {self.square_key}"},
                        json={
                            "source_id": payment_method["token"],
                            "amount_money": {
                                "amount": int(final_amount * 100),
                                "currency": currency
                            }
                        }
                    )
                    
                    if response.status_code == 200:
                        square_response = response.json()
                        transaction = {
                            "id": square_response["payment"]["id"],
                            "amount": final_amount,
                            "currency": currency, 
                            "status": "completed",
                            "timestamp": time.time(),
                            "provider": "square",
                            "customer": customer_data["email"],
                            "items": items,
                            "tax_amount": tax_amount,
                            "discount_amount": discount_amount
                        }
                        
                        self.send_payment_confirmation_email(customer_data["email"], transaction)
                        
                        return {"success": True, "transaction": transaction}
                    else:
                        return {"success": False, "error": "Square payment failed"}
                        
                except Exception as e:
                    print(f"Square error: {e}")
                    return {"success": False, "error": "Payment processing error"}
                    
        elif payment_method["type"] == "paypal":
            # PayPal processing - more duplicate code
            try:
                response = requests.post(
                    "https://api.paypal.com/v2/checkout/orders",
                    headers={"Authorization": f"Bearer {self.paypal_key}"},
                    json={
                        "intent": "CAPTURE",
                        "purchase_units": [{
                            "amount": {
                                "currency_code": currency,
                                "value": str(final_amount)
                            }
                        }]
                    }
                )
                
                if response.status_code == 201:
                    paypal_response = response.json()
                    transaction = {
                        "id": paypal_response["id"],
                        "amount": final_amount,
                        "currency": currency,
                        "status": "completed", 
                        "timestamp": time.time(),
                        "provider": "paypal",
                        "customer": customer_data["email"],
                        "items": items,
                        "tax_amount": tax_amount,
                        "discount_amount": discount_amount
                    }
                    
                    self.send_payment_confirmation_email(customer_data["email"], transaction)
                    
                    return {"success": True, "transaction": transaction}
                else:
                    return {"success": False, "error": "PayPal payment failed"}
                    
            except Exception as e:
                print(f"PayPal error: {e}")
                return {"success": False, "error": "Payment processing error"}
                
        else:
            return {"success": False, "error": "Unsupported payment method"}
    
    def send_payment_confirmation_email(self, email, transaction):
        # Email sending logic - should be separate service
        # HACK: Using print instead of actual email service
        print(f"Sending confirmation email to {email}")
        print(f"Transaction ID: {transaction['id']}")
        print(f"Amount: {transaction['currency']} {transaction['amount']}")
        
        # TODO: Implement actual email sending
        pass
    
    def refund_payment(self, transaction_id, amount=None):
        # Refund logic - incomplete implementation
        # TODO: Implement refund for different providers
        print(f"Refunding transaction {transaction_id}")
        if amount:
            print(f"Partial refund: {amount}")
        else:
            print("Full refund")
            
        # XXX: This doesn't actually process the refund
        return {"success": True, "message": "Refund initiated"}
    
    def get_transaction(self, transaction_id):
        # Should query database, but we don't have one
        # FIXME: Implement actual transaction lookup
        return {"id": transaction_id, "status": "unknown"}
        
    def validate_credit_card(self, card_number, expiry_month, expiry_year, cvv):
        # Basic card validation - should use proper validation library
        if not card_number or len(card_number) < 13 or len(card_number) > 19:
            return False
            
        # Luhn algorithm check - reimplemented poorly
        digits = [int(d) for d in card_number if d.isdigit()]
        checksum = 0
        for i, digit in enumerate(reversed(digits)):
            if i % 2 == 1:
                digit *= 2
                if digit > 9:
                    digit -= 9
            checksum += digit
        
        if checksum % 10 != 0:
            return False
            
        # Expiry validation
        if expiry_month < 1 or expiry_month > 12:
            return False
            
        current_year = int(time.strftime("%Y"))
        current_month = int(time.strftime("%m"))
        
        if expiry_year < current_year:
            return False
        elif expiry_year == current_year and expiry_month < current_month:
            return False
            
        # CVV validation
        if not cvv or len(cvv) < 3 or len(cvv) > 4:
            return False
            
        return True


# Module-level functions that should be in class or separate module
def calculate_processing_fee(amount, provider):
    """Calculate processing fee - hardcoded rates"""
    if provider == "stripe":
        return amount * 0.029 + 0.30  # Stripe rates
    elif provider == "paypal":
        return amount * 0.031 + 0.30  # PayPal rates  
    elif provider == "square":
        return amount * 0.026 + 0.10  # Square rates
    else:
        return 0


def format_currency(amount, currency):
    """Format currency - basic implementation"""
    # Should use proper internationalization
    if currency == "USD":
        return f"${amount:.2f}"
    elif currency == "EUR":
        return f"€{amount:.2f}"
    elif currency == "GBP":
        return f"£{amount:.2f}"
    else:
        return f"{currency} {amount:.2f}"


# Global state - anti-pattern
payment_processor_instance = None


def get_payment_processor():
    global payment_processor_instance
    if payment_processor_instance is None:
        payment_processor_instance = PaymentProcessor()
    return payment_processor_instance