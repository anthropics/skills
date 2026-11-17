# Mobile SDK Integration

Native payment integration for iOS and Android apps with low PCI scope.

## Available SDKs

| Platform | SDK | Package |
|----------|-----|---------|
| iOS | Swift SDK | `WorldlineConnectKit` |
| Android | Android SDK | `com.worldline.connect:sdk-client-android` |
| Flutter | Flutter SDK | `worldline_connect_flutter_sdk` |
| React Native | RN SDK | `onlinepayments-sdk-client-reactnative` |

## How It Works

1. Create a client session on your server
2. Initialize SDK with session in mobile app
3. SDK encrypts card data locally
4. Send encrypted payload to your server
5. Your server creates payment with Worldline

## iOS (Swift) Integration

### Installation

```swift
// Swift Package Manager
.package(url: "https://github.com/Online-Payments/sdk-client-swift", from: "1.0.0")
```

### Initialize Session

```swift
import OnlinePaymentsKit

class PaymentManager {
    var session: Session?

    func startPayment() async throws {
        // Get session from your server
        let sessionData = try await fetchSession()

        session = Session(
            clientSessionId: sessionData.clientSessionId,
            customerId: sessionData.customerId,
            baseURL: sessionData.assetUrl,
            assetBaseURL: sessionData.assetUrl,
            appIdentifier: "your-app-id",
            environment: .production // or .sandbox
        )
    }
}
```

### Get Payment Products

```swift
func getPaymentProducts() async throws -> BasicPaymentProducts {
    let context = PaymentContext(
        amountOfMoney: AmountOfMoney(totalAmount: 4999, currencyCodeString: "EUR"),
        isRecurring: false,
        countryCode: "NL"
    )

    return try await session!.paymentProducts(for: context)
}
```

### Create Payment Request

```swift
func createPaymentRequest(product: BasicPaymentProduct) -> PaymentRequest {
    let paymentRequest = PaymentRequest(paymentProduct: product)

    paymentRequest.setValue(forField: "cardNumber", value: "4111111111111111")
    paymentRequest.setValue(forField: "expiryDate", value: "1225")
    paymentRequest.setValue(forField: "cvv", value: "123")
    paymentRequest.setValue(forField: "cardholderName", value: "John Doe")

    return paymentRequest
}
```

### Encrypt and Submit

```swift
func submitPayment(request: PaymentRequest) async throws -> PaymentResult {
    // Encrypt locally
    let preparedRequest = try session!.prepare(paymentRequest: request)

    // Send to your server
    let result = try await apiClient.processPayment(
        encryptedFields: preparedRequest.encryptedFields,
        encodedClientMetaInfo: preparedRequest.encodedClientMetaInfo
    )

    return result
}
```

## Android Integration

### Installation

```kotlin
// build.gradle
dependencies {
    implementation 'com.worldline.connect:sdk-client-android:7.0.0'
}
```

### Initialize Session

```kotlin
import com.onlinepayments.sdk.client.android.model.PaymentContext
import com.onlinepayments.sdk.client.android.session.Session

class PaymentViewModel : ViewModel() {
    private var session: Session? = null

    fun initSession(sessionData: SessionData) {
        session = Session(
            clientSessionId = sessionData.clientSessionId,
            customerId = sessionData.customerId,
            clientApiUrl = sessionData.clientApiUrl,
            assetUrl = sessionData.assetUrl,
            isEnvironmentProduction = false,
            appIdentifier = "your-app-id"
        )
    }
}
```

### Get Payment Products

```kotlin
fun getPaymentProducts(): LiveData<PaymentProducts> {
    val context = PaymentContext(
        AmountOfMoney(4999, "EUR"),
        "NL",
        false // isRecurring
    )

    return liveData {
        val products = session?.getPaymentProducts(context)
        emit(products)
    }
}
```

### Create and Encrypt

```kotlin
fun preparePayment(product: PaymentProduct): PreparedPaymentRequest {
    val request = PaymentRequest(product)

    request.setValue("cardNumber", "4111111111111111")
    request.setValue("expiryDate", "1225")
    request.setValue("cvv", "123")
    request.setValue("cardholderName", "John Doe")

    return session!!.preparePaymentRequest(request)
}
```

## Flutter Integration

### Installation

```yaml
# pubspec.yaml
dependencies:
  worldline_connect_flutter_sdk: ^1.0.0
```

### Usage

```dart
import 'package:worldline_connect_flutter_sdk/worldline_connect_flutter_sdk.dart';

class PaymentService {
  late Session _session;

  Future<void> initSession(SessionData data) async {
    _session = Session(
      clientSessionId: data.clientSessionId,
      customerId: data.customerId,
      clientApiUrl: data.clientApiUrl,
      assetUrl: data.assetUrl,
    );
  }

  Future<PreparedPaymentRequest> preparePayment(PaymentProduct product) async {
    final request = PaymentRequest(product);

    request.setValue('cardNumber', '4111111111111111');
    request.setValue('expiryDate', '1225');
    request.setValue('cvv', '123');
    request.setValue('cardholderName', 'John Doe');

    return await _session.preparePaymentRequest(request);
  }
}
```

## React Native Integration

### Installation

```bash
npm install onlinepayments-sdk-client-reactnative
```

### Usage

```javascript
import {
  Session,
  PaymentRequest
} from 'onlinepayments-sdk-client-reactnative';

const initSession = async (sessionData) => {
  const session = new Session({
    clientSessionId: sessionData.clientSessionId,
    customerId: sessionData.customerId,
    clientApiUrl: sessionData.clientApiUrl,
    assetUrl: sessionData.assetUrl
  });

  return session;
};

const preparePayment = async (session, product, cardData) => {
  const request = new PaymentRequest(product);

  request.setValue('cardNumber', cardData.number);
  request.setValue('expiryDate', cardData.expiry);
  request.setValue('cvv', cardData.cvv);
  request.setValue('cardholderName', cardData.name);

  return await session.preparePaymentRequest(request);
};
```

## Server-Side Payment Creation

After receiving encrypted data from mobile app:

```javascript
app.post('/api/mobile-payment', async (req, res) => {
  const { encryptedFields, encodedClientMetaInfo, orderId } = req.body;

  const payment = await client.payments.createPayment(merchantId, {
    order: {
      amountOfMoney: { amount: 4999, currencyCode: "EUR" },
      references: { merchantReference: orderId }
    },
    cardPaymentMethodSpecificInput: {
      paymentProductId: 1, // Visa
      encryptedCustomerInput: encryptedFields
    },
    // Required for mobile
    device: {
      acceptHeader: "application/json",
      locale: "en_US",
      userAgent: encodedClientMetaInfo
    }
  });

  res.json(payment);
});
```

## Apple Pay Integration

```swift
import PassKit

class ApplePayHandler: NSObject, PKPaymentAuthorizationViewControllerDelegate {

    func startApplePay() {
        let request = PKPaymentRequest()
        request.merchantIdentifier = "merchant.com.yourapp"
        request.supportedNetworks = [.visa, .masterCard, .amex]
        request.merchantCapabilities = .capability3DS
        request.countryCode = "NL"
        request.currencyCode = "EUR"
        request.paymentSummaryItems = [
            PKPaymentSummaryItem(label: "Your Product", amount: 49.99)
        ]

        let vc = PKPaymentAuthorizationViewController(paymentRequest: request)
        vc?.delegate = self
        present(vc!, animated: true)
    }

    func paymentAuthorizationViewController(
        _ controller: PKPaymentAuthorizationViewController,
        didAuthorizePayment payment: PKPayment,
        handler completion: @escaping (PKPaymentAuthorizationResult) -> Void
    ) {
        // Send payment.token.paymentData to your server
        let tokenData = payment.token.paymentData

        Task {
            let result = await processApplePayment(tokenData)
            completion(PKPaymentAuthorizationResult(status: result ? .success : .failure, errors: nil))
        }
    }
}
```

## Google Pay Integration

```kotlin
import com.google.android.gms.wallet.*

class GooglePayHandler(private val activity: Activity) {

    private val paymentsClient = Wallet.getPaymentsClient(
        activity,
        Wallet.WalletOptions.Builder()
            .setEnvironment(WalletConstants.ENVIRONMENT_TEST)
            .build()
    )

    fun startGooglePay() {
        val request = PaymentDataRequest.fromJson("""
            {
                "apiVersion": 2,
                "apiVersionMinor": 0,
                "merchantInfo": {
                    "merchantName": "Your Store"
                },
                "allowedPaymentMethods": [{
                    "type": "CARD",
                    "parameters": {
                        "allowedAuthMethods": ["PAN_ONLY", "CRYPTOGRAM_3DS"],
                        "allowedCardNetworks": ["VISA", "MASTERCARD"]
                    },
                    "tokenizationSpecification": {
                        "type": "PAYMENT_GATEWAY",
                        "parameters": {
                            "gateway": "worldlinedirect",
                            "gatewayMerchantId": "$merchantId"
                        }
                    }
                }],
                "transactionInfo": {
                    "totalPrice": "49.99",
                    "totalPriceStatus": "FINAL",
                    "currencyCode": "EUR"
                }
            }
        """.trimIndent())

        AutoResolveHelper.resolveTask(
            paymentsClient.loadPaymentData(request),
            activity,
            LOAD_PAYMENT_DATA_REQUEST_CODE
        )
    }
}
```

## Best Practices

1. **Secure session storage** - Don't persist session IDs
2. **SSL pinning** - Verify server certificates
3. **Encrypt at rest** - If storing tokens locally
4. **Handle errors gracefully** - User-friendly messages
5. **Test on real devices** - Emulators may differ
6. **Biometric confirmation** - For stored cards
