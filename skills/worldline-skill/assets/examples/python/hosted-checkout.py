"""
Worldline Direct - Hosted Checkout Example (Python)

This example shows how to create a hosted checkout session
and handle the return from payment using Flask.
"""

import os
from flask import Flask, request, jsonify, redirect
from onlinepayments.sdk.factory import Factory
from onlinepayments.sdk.domain.create_hosted_checkout_request import CreateHostedCheckoutRequest
from onlinepayments.sdk.domain.amount_of_money import AmountOfMoney
from onlinepayments.sdk.domain.order import Order
from onlinepayments.sdk.domain.customer import Customer
from onlinepayments.sdk.domain.address import Address
from onlinepayments.sdk.domain.contact_details import ContactDetails
from onlinepayments.sdk.domain.order_references import OrderReferences
from onlinepayments.sdk.domain.hosted_checkout_specific_input import HostedCheckoutSpecificInput
from onlinepayments.sdk.domain.payment_product_filters_hosted_checkout import PaymentProductFiltersHostedCheckout
from onlinepayments.sdk.domain.payment_product_filter import PaymentProductFilter

app = Flask(__name__)

# Initialize the client
client = Factory.create_client_from_configuration({
    "onlinePayments.api.endpoint.host": "payment.preprod.direct.worldline-solutions.com",
    "onlinePayments.api.apiKeyId": os.environ.get("WORLDLINE_API_KEY"),
    "onlinePayments.api.secretApiKey": os.environ.get("WORLDLINE_SECRET_KEY"),
    "onlinePayments.api.integrator": "YourCompany"
})

MERCHANT_ID = os.environ.get("WORLDLINE_MERCHANT_ID")
BASE_URL = os.environ.get("BASE_URL", "http://localhost:5000")

# Store checkout sessions (use a real database in production)
checkout_sessions = {}


@app.route("/api/checkout", methods=["POST"])
def create_checkout():
    """Create a hosted checkout session"""
    try:
        data = request.get_json()
        order_id = data.get("orderId")
        amount = data.get("amount")
        currency = data.get("currency", "EUR")
        customer_data = data.get("customer", {})

        # Build the request
        checkout_request = CreateHostedCheckoutRequest()

        # Order details
        amount_of_money = AmountOfMoney()
        amount_of_money.amount = amount  # Amount in cents
        amount_of_money.currency_code = currency

        order = Order()
        order.amount_of_money = amount_of_money

        # Customer details
        customer = Customer()
        customer.merchant_customer_id = customer_data.get("id")

        if customer_data.get("address"):
            address = Address()
            address.street = customer_data["address"].get("street")
            address.city = customer_data["address"].get("city")
            address.country_code = customer_data["address"].get("country")
            address.zip = customer_data["address"].get("postalCode")
            customer.billing_address = address

        if customer_data.get("email"):
            contact_details = ContactDetails()
            contact_details.email_address = customer_data.get("email")
            customer.contact_details = contact_details

        order.customer = customer

        # Order references
        references = OrderReferences()
        references.merchant_reference = order_id
        order.references = references

        checkout_request.order = order

        # Hosted checkout configuration
        hosted_checkout_input = HostedCheckoutSpecificInput()
        hosted_checkout_input.return_url = f"{BASE_URL}/checkout/complete?orderId={order_id}"
        hosted_checkout_input.show_result_page = False
        hosted_checkout_input.locale = "en_GB"

        # Optional: Restrict payment methods
        product_filter = PaymentProductFilter()
        product_filter.products = [1, 3, 809, 840, 3012]  # Visa, MC, iDEAL, PayPal, Klarna

        payment_filters = PaymentProductFiltersHostedCheckout()
        payment_filters.restrict_to = product_filter
        hosted_checkout_input.payment_product_filters = payment_filters

        checkout_request.hosted_checkout_specific_input = hosted_checkout_input

        # Create the hosted checkout
        response = client.merchant(MERCHANT_ID).hosted_checkout().create_hosted_checkout(checkout_request)

        # Store session for verification on return
        checkout_sessions[order_id] = {
            "hosted_checkout_id": response.hosted_checkout_id,
            "return_mac": response.RETURNMAC
        }

        # Build redirect URL
        redirect_url = f"https://payment.preprod.direct.worldline-solutions.com/hostedcheckout/{response.hosted_checkout_id}"

        return jsonify({
            "success": True,
            "redirectUrl": redirect_url,
            "hostedCheckoutId": response.hosted_checkout_id
        })

    except Exception as e:
        print(f"Checkout creation failed: {e}")
        return jsonify({
            "success": False,
            "error": str(e)
        }), 500


@app.route("/checkout/complete")
def checkout_complete():
    """Handle return from hosted checkout"""
    try:
        order_id = request.args.get("orderId")
        return_mac = request.args.get("RETURNMAC")
        hosted_checkout_id = request.args.get("hostedCheckoutId")

        # Verify session exists
        session = checkout_sessions.get(order_id)
        if not session:
            return redirect(f"/order/{order_id}/error?reason=session_not_found")

        # Verify RETURNMAC to prevent tampering
        if return_mac != session.get("return_mac"):
            return redirect(f"/order/{order_id}/error?reason=invalid_return")

        # Get checkout status from Worldline
        status = client.merchant(MERCHANT_ID).hosted_checkout().get_hosted_checkout_status(
            hosted_checkout_id
        )

        if status.status == "PAYMENT_CREATED":
            payment = status.created_payment_output.payment
            payment_status = payment.status

            if payment_status in ["CAPTURED", "PENDING_CAPTURE"]:
                # Payment successful
                payment_id = payment.id
                token = None
                if payment.payment_output and payment.payment_output.card_payment_method_specific_output:
                    token = payment.payment_output.card_payment_method_specific_output.token

                print(f"Order {order_id} paid. Payment ID: {payment_id}")
                if token:
                    print(f"Card token stored: {token}")

                # Cleanup session
                del checkout_sessions[order_id]

                return redirect(f"/order/{order_id}/success")

        # Payment not successful
        print(f"Order {order_id} failed. Status: {status.status}")
        if order_id in checkout_sessions:
            del checkout_sessions[order_id]

        return redirect(f"/order/{order_id}/failed")

    except Exception as e:
        print(f"Checkout completion error: {e}")
        return redirect(f"/order/{request.args.get('orderId')}/error")


@app.route("/api/checkout/<hosted_checkout_id>/status")
def get_checkout_status(hosted_checkout_id):
    """Check payment status (for polling if needed)"""
    try:
        status = client.merchant(MERCHANT_ID).hosted_checkout().get_hosted_checkout_status(
            hosted_checkout_id
        )

        payment_status = None
        payment_id = None
        if status.created_payment_output and status.created_payment_output.payment:
            payment_status = status.created_payment_output.payment.status
            payment_id = status.created_payment_output.payment.id

        return jsonify({
            "status": status.status,
            "paymentStatus": payment_status,
            "paymentId": payment_id
        })

    except Exception as e:
        return jsonify({"error": str(e)}), 500


# ============================================
# Example: Direct Usage (without Flask)
# ============================================

def create_checkout_session(order_id, amount, currency="EUR", customer_email=None):
    """
    Create a hosted checkout session directly.
    Returns the redirect URL for the customer.
    """
    checkout_request = CreateHostedCheckoutRequest()

    # Order
    amount_of_money = AmountOfMoney()
    amount_of_money.amount = amount
    amount_of_money.currency_code = currency

    order = Order()
    order.amount_of_money = amount_of_money

    references = OrderReferences()
    references.merchant_reference = order_id
    order.references = references

    if customer_email:
        customer = Customer()
        contact_details = ContactDetails()
        contact_details.email_address = customer_email
        customer.contact_details = contact_details
        order.customer = customer

    checkout_request.order = order

    # Hosted checkout config
    hosted_checkout_input = HostedCheckoutSpecificInput()
    hosted_checkout_input.return_url = f"{BASE_URL}/checkout/complete?orderId={order_id}"
    hosted_checkout_input.show_result_page = False
    checkout_request.hosted_checkout_specific_input = hosted_checkout_input

    # Create checkout
    response = client.merchant(MERCHANT_ID).hosted_checkout().create_hosted_checkout(checkout_request)

    redirect_url = f"https://payment.preprod.direct.worldline-solutions.com/hostedcheckout/{response.hosted_checkout_id}"

    return {
        "hosted_checkout_id": response.hosted_checkout_id,
        "redirect_url": redirect_url,
        "return_mac": response.RETURNMAC
    }


def get_payment_status(hosted_checkout_id):
    """
    Get the status of a hosted checkout session.
    """
    status = client.merchant(MERCHANT_ID).hosted_checkout().get_hosted_checkout_status(
        hosted_checkout_id
    )

    result = {
        "status": status.status,
        "payment_created": status.status == "PAYMENT_CREATED"
    }

    if status.created_payment_output and status.created_payment_output.payment:
        payment = status.created_payment_output.payment
        result["payment_id"] = payment.id
        result["payment_status"] = payment.status
        result["is_successful"] = payment.status in ["CAPTURED", "PENDING_CAPTURE"]

        if payment.payment_output:
            result["amount"] = payment.payment_output.amount_of_money.amount
            result["currency"] = payment.payment_output.amount_of_money.currency_code

            if payment.payment_output.card_payment_method_specific_output:
                card_output = payment.payment_output.card_payment_method_specific_output
                result["token"] = card_output.token
                result["card_number"] = card_output.card.card_number  # Masked

    return result


# ============================================
# Example Usage
# ============================================

if __name__ == "__main__":
    import sys

    if len(sys.argv) > 1 and sys.argv[1] == "test":
        # Test mode - create a checkout session
        print("Creating test checkout session...")

        result = create_checkout_session(
            order_id=f"order-test-{int(__import__('time').time())}",
            amount=4999,  # €49.99
            currency="EUR",
            customer_email="test@example.com"
        )

        print(f"Hosted Checkout ID: {result['hosted_checkout_id']}")
        print(f"Redirect URL: {result['redirect_url']}")
        print(f"\nRedirect customer to this URL to complete payment.")

    else:
        # Run Flask server
        port = int(os.environ.get("PORT", 5000))
        app.run(host="0.0.0.0", port=port, debug=True)
