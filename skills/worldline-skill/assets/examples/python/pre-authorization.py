"""
Worldline Direct - Pre-Authorization Example (Python)

This example shows how to create a pre-authorization,
perform partial captures, and handle the full lifecycle.

Perfect for: Car rental, hotels, variable-amount transactions
"""

import os
from onlinepayments.sdk.factory import Factory
from onlinepayments.sdk.domain.create_payment_request import CreatePaymentRequest
from onlinepayments.sdk.domain.capture_payment_request import CapturePaymentRequest
from onlinepayments.sdk.domain.amount_of_money import AmountOfMoney
from onlinepayments.sdk.domain.order import Order
from onlinepayments.sdk.domain.order_references import OrderReferences
from onlinepayments.sdk.domain.card_payment_method_specific_input import CardPaymentMethodSpecificInput
from onlinepayments.sdk.domain.card import Card
from onlinepayments.sdk.domain.three_d_secure import ThreeDSecure
from onlinepayments.sdk.domain.redirection_data import RedirectionData

# Initialize the client
client = Factory.create_client_from_configuration({
    "onlinePayments.api.endpoint.host": "payment.preprod.direct.worldline-solutions.com",
    "onlinePayments.api.apiKeyId": os.environ.get("WORLDLINE_API_KEY"),
    "onlinePayments.api.secretApiKey": os.environ.get("WORLDLINE_SECRET_KEY"),
    "onlinePayments.api.integrator": "YourCompany"
})

MERCHANT_ID = os.environ.get("WORLDLINE_MERCHANT_ID")


def create_pre_authorization(amount, currency, order_id, card_data, return_url=None):
    """
    Create a pre-authorization.
    Blocks funds for up to 30 days without capturing.

    Args:
        amount: Amount in cents (e.g., 50000 = €500.00)
        currency: Currency code (e.g., "EUR")
        order_id: Your order reference
        card_data: Dict with number, expiry, cvv, name
        return_url: URL for 3DS redirect return

    Returns:
        Payment response with ID and status
    """
    request = CreatePaymentRequest()

    # Order details
    amount_of_money = AmountOfMoney()
    amount_of_money.amount = amount
    amount_of_money.currency_code = currency

    order = Order()
    order.amount_of_money = amount_of_money

    references = OrderReferences()
    references.merchant_reference = order_id
    order.references = references

    request.order = order

    # Card payment input
    card_input = CardPaymentMethodSpecificInput()
    card_input.authorization_mode = "PRE_AUTHORIZATION"  # Key setting!
    card_input.tokenize = True  # Store for future charges

    card = Card()
    card.card_number = card_data["number"]
    card.expiry_date = card_data["expiry"]  # MMYY format
    card.cvv = card_data["cvv"]
    card.cardholder_name = card_data["name"]
    card_input.card = card

    # 3D Secure
    three_d_secure = ThreeDSecure()
    redirection_data = RedirectionData()
    redirection_data.return_url = return_url or "https://yoursite.com/3ds/complete"
    three_d_secure.redirection_data = redirection_data
    card_input.three_d_secure = three_d_secure

    request.card_payment_method_specific_input = card_input

    # Create payment
    response = client.merchant(MERCHANT_ID).payments().create_payment(request)

    return response


def capture_payment(payment_id, amount=None, is_final=True):
    """
    Capture funds from a pre-authorization.

    Args:
        payment_id: The payment ID from pre-authorization
        amount: Amount to capture in cents (None = full amount)
        is_final: If False, more captures are possible

    Returns:
        Capture response
    """
    request = CapturePaymentRequest()

    if amount is not None:
        request.amount = amount

    request.is_final = is_final

    response = client.merchant(MERCHANT_ID).payments().capture_payment(payment_id, request)

    return response


def cancel_authorization(payment_id):
    """
    Cancel a pre-authorization (release funds).

    Args:
        payment_id: The payment ID to cancel

    Returns:
        Cancel response
    """
    response = client.merchant(MERCHANT_ID).payments().cancel_payment(payment_id)
    return response


def get_payment_status(payment_id):
    """
    Get payment status and details.

    Args:
        payment_id: The payment ID to check

    Returns:
        Dict with status, amounts, and token
    """
    response = client.merchant(MERCHANT_ID).payments().get_payment_details(payment_id)

    result = {
        "status": response.status,
        "authorized_amount": None,
        "captured_amount": 0,
        "token": None
    }

    if response.payment_output:
        if response.payment_output.amount_of_money:
            result["authorized_amount"] = response.payment_output.amount_of_money.amount

        if response.payment_output.acquired_amount:
            result["captured_amount"] = response.payment_output.acquired_amount.amount

        if response.payment_output.card_payment_method_specific_output:
            result["token"] = response.payment_output.card_payment_method_specific_output.token

    return result


# ============================================
# Example: Car Rental Flow
# ============================================

def car_rental_example():
    """
    Demonstrates a car rental payment flow:
    1. Pre-authorize €500 deposit
    2. Capture €350 for actual rental
    3. Capture €45 for fuel
    4. Remaining €105 is released
    """
    print("=== Car Rental Payment Flow ===\n")

    import time
    order_id = f"rental-{int(time.time())}"

    # 1. Pre-authorize deposit
    print("1. Creating pre-authorization for €500 deposit...")
    pre_auth = create_pre_authorization(
        amount=50000,  # €500
        currency="EUR",
        order_id=order_id,
        card_data={
            "number": "4111111111111111",
            "expiry": "1225",
            "cvv": "123",
            "name": "John Doe"
        },
        return_url="https://example.com/3ds"
    )

    payment_id = pre_auth.payment.id
    print(f"   Pre-auth created: {payment_id}")
    print(f"   Status: {pre_auth.payment.status}")

    # Check for 3DS redirect
    if pre_auth.merchant_action and pre_auth.merchant_action.action_type == "REDIRECT":
        print("   3DS required - redirect customer to:")
        print(f"   {pre_auth.merchant_action.redirect_data.redirect_URL}")
        print("   (In real app, wait for customer to return)\n")
    else:
        print()

    # Get token for future use
    token = None
    if pre_auth.payment.payment_output and pre_auth.payment.payment_output.card_payment_method_specific_output:
        token = pre_auth.payment.payment_output.card_payment_method_specific_output.token
        print(f"   Token stored: {token}\n")

    # 2. Capture actual rental cost
    print("2. Car returned - Capturing €350 (actual rental cost)...")
    capture1 = capture_payment(payment_id, amount=35000, is_final=False)
    print(f"   Captured €350. Status: {capture1.status}\n")

    # 3. Capture fuel charge
    print("3. Adding fuel charge - Capturing €45...")
    capture2 = capture_payment(payment_id, amount=4500, is_final=True)
    print(f"   Captured €45. Status: {capture2.status}\n")

    # 4. Check final status
    print("4. Checking final status...")
    status = get_payment_status(payment_id)
    print(f"   Status: {status['status']}")
    print(f"   Authorized: €{status['authorized_amount'] / 100:.2f}")
    print(f"   Captured: €{status['captured_amount'] / 100:.2f}")

    remaining = status['authorized_amount'] - status['captured_amount']
    print(f"   Remaining €{remaining / 100:.2f} was released\n")

    return {"payment_id": payment_id, "token": token}


# ============================================
# Example: Hotel Flow
# ============================================

def hotel_example():
    """
    Demonstrates a hotel booking payment flow:
    1. Pre-authorize €1000 (room + incidentals buffer)
    2. At checkout, capture €750 (room €700 + minibar €50)
    3. Remaining €250 is released
    """
    print("=== Hotel Booking Flow ===\n")

    import time
    order_id = f"hotel-{int(time.time())}"

    # 1. Pre-authorize for stay + incidentals
    print("1. Creating pre-authorization for €1000 (room + incidentals)...")
    pre_auth = create_pre_authorization(
        amount=100000,  # €1000
        currency="EUR",
        order_id=order_id,
        card_data={
            "number": "5399999999999999",
            "expiry": "1225",
            "cvv": "123",
            "name": "Jane Smith"
        }
    )

    payment_id = pre_auth.payment.id
    print(f"   Pre-auth created: {payment_id}\n")

    # 2. Guest checks out - capture room + extras
    print("2. Checkout - Capturing €750 (room €700 + minibar €50)...")
    capture = capture_payment(payment_id, amount=75000, is_final=True)
    print(f"   Captured: {capture.status}")
    print("   Remaining €250 released automatically\n")

    return {"payment_id": payment_id}


# ============================================
# Example: Cancellation
# ============================================

def cancellation_example():
    """
    Demonstrates cancelling a pre-authorization:
    1. Create pre-authorization
    2. Customer cancels booking
    3. Release all funds
    """
    print("=== Cancellation Flow ===\n")

    import time
    order_id = f"cancel-test-{int(time.time())}"

    # 1. Create pre-auth
    print("1. Creating pre-authorization...")
    pre_auth = create_pre_authorization(
        amount=20000,  # €200
        currency="EUR",
        order_id=order_id,
        card_data={
            "number": "4111111111111111",
            "expiry": "1225",
            "cvv": "123",
            "name": "Test User"
        }
    )

    payment_id = pre_auth.payment.id
    print(f"   Pre-auth created: {payment_id}\n")

    # 2. Customer cancels
    print("2. Customer cancels - Releasing funds...")
    cancel = cancel_authorization(payment_id)
    print(f"   Cancelled: {cancel.payment.status}")
    print("   Funds released to cardholder\n")

    return {"payment_id": payment_id}


# ============================================
# Example: Partial Captures
# ============================================

def partial_capture_example():
    """
    Demonstrates multiple partial captures:
    1. Pre-authorize €100
    2. Capture €30 (first shipment)
    3. Capture €45 (second shipment)
    4. Capture €25 (final shipment)
    """
    print("=== Partial Capture Example ===\n")

    import time
    order_id = f"partial-{int(time.time())}"

    # 1. Create pre-auth
    print("1. Creating pre-authorization for €100...")
    pre_auth = create_pre_authorization(
        amount=10000,  # €100
        currency="EUR",
        order_id=order_id,
        card_data={
            "number": "4111111111111111",
            "expiry": "1225",
            "cvv": "123",
            "name": "Test User"
        }
    )

    payment_id = pre_auth.payment.id
    print(f"   Pre-auth created: {payment_id}\n")

    # 2. First partial capture
    print("2. First shipment - Capturing €30...")
    capture1 = capture_payment(payment_id, amount=3000, is_final=False)
    status = get_payment_status(payment_id)
    print(f"   Captured: {capture1.status}")
    print(f"   Remaining: €{(status['authorized_amount'] - status['captured_amount']) / 100:.2f}\n")

    # 3. Second partial capture
    print("3. Second shipment - Capturing €45...")
    capture2 = capture_payment(payment_id, amount=4500, is_final=False)
    status = get_payment_status(payment_id)
    print(f"   Captured: {capture2.status}")
    print(f"   Remaining: €{(status['authorized_amount'] - status['captured_amount']) / 100:.2f}\n")

    # 4. Final capture
    print("4. Final shipment - Capturing €25 (final)...")
    capture3 = capture_payment(payment_id, amount=2500, is_final=True)
    status = get_payment_status(payment_id)
    print(f"   Captured: {capture3.status}")
    print(f"   Total captured: €{status['captured_amount'] / 100:.2f}\n")

    return {"payment_id": payment_id}


# ============================================
# Run Examples
# ============================================

if __name__ == "__main__":
    import sys

    examples = {
        "car-rental": car_rental_example,
        "hotel": hotel_example,
        "cancel": cancellation_example,
        "partial": partial_capture_example
    }

    if len(sys.argv) > 1:
        example_name = sys.argv[1]
        if example_name in examples:
            try:
                examples[example_name]()
            except Exception as e:
                print(f"Error: {e}")
                if hasattr(e, 'body') and hasattr(e.body, 'errors'):
                    print(f"Details: {e.body.errors}")
        else:
            print(f"Unknown example: {example_name}")
            print(f"Available: {', '.join(examples.keys())}")
    else:
        # Run all examples
        try:
            car_rental_example()
            print("---\n")
            hotel_example()
            print("---\n")
            cancellation_example()
        except Exception as e:
            print(f"Error: {e}")
            if hasattr(e, 'body') and hasattr(e.body, 'errors'):
                print(f"Details: {e.body.errors}")
