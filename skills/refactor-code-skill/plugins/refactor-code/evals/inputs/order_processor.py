def process_order(user_id, items, shipping_address, payment_info, promo_code=None):
    if not user_id:
        return {"error": "no user"}
    if not items or len(items) == 0:
        return {"error": "no items"}
    if not shipping_address:
        return {"error": "no shipping address"}
    if not payment_info:
        return {"error": "no payment info"}

    subtotal = 0
    for item in items:
        if item["in_stock"] == True:
            if item["on_sale"] == True:
                subtotal = subtotal + (item["price"] * 0.8 * item["quantity"])
            else:
                subtotal = subtotal + (item["price"] * item["quantity"])
        else:
            return {"error": "item out of stock: " + item["name"]}

    discount = 0
    if promo_code:
        if promo_code == "SAVE10":
            discount = subtotal * 0.1
        elif promo_code == "SAVE20":
            if subtotal > 100:
                discount = subtotal * 0.2
            else:
                discount = 0
        elif promo_code == "FREESHIP":
            discount = 5.99
        else:
            pass

    tax = (subtotal - discount) * 0.0875

    shipping = 5.99
    if subtotal - discount > 50:
        shipping = 0

    total = subtotal - discount + tax + shipping

    if payment_info["type"] == "credit":
        if payment_info["card_number"][0] == "4":
            processor = "visa"
        elif payment_info["card_number"][0] == "5":
            processor = "mastercard"
        elif payment_info["card_number"][0] == "3":
            processor = "amex"
        else:
            processor = "unknown"
    elif payment_info["type"] == "paypal":
        processor = "paypal"
    else:
        processor = "other"

    return {
        "subtotal": subtotal,
        "discount": discount,
        "tax": tax,
        "shipping": shipping,
        "total": total,
        "processor": processor,
        "status": "ok"
    }
