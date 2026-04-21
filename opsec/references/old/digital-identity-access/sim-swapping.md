# SIM Swapping

SIM swapping occurs when a threat actor trick a mobile phone provider into transferring a victim's phone number to a SIM
card that the criminals control. This allows the criminals to intercept the victim's text messages and phone calls,
including any two-factor authentication codes. With access to the victim's phone number, the criminals can then gain
unauthorized access to the victim's accounts.

## Stop Using SMS-Based 2FA

This is by far the most important thing you can do to protect yourself against SIM swaps. Think about your most
important online accounts and how valuable they are to an attacker:

- They can read all the information available on that account. This includes emails, photos, private messages, or
embarrassing details from years ago that you forgot you sent.
- They can steal everything of value in that account, like money, crypto, important documents, or other personal
information.
- They can use it to impersonate you while scamming people you know, putting them at risk and putting you in a really
tough spot.

If this thought scares you, you should go and **make sure SMS 2FA is disabled** for any account that you care about.
Instead, consider using either an app like Google Authenticator (make sure to disable cloud sync!) or a security key
(e.g., Yubico). Avoid using Authy, as it is tied to your phone number too.

Not sure where to start? Here’s a brief list of services to inspire you:

- **Email**: Gmail, Yahoo
- **Social Media**: Facebook, Twitter
- **Instant Messaging**: Telegram, Discord
- **Crypto Exchanges**: Coinbase, Gemini, Binance
- **Domain Registrars**: GoDaddy, Squarespace
- **Banking**: PayPal, Revolut

## Switch to a High-Security Carrier

The next best thing you can do is to simply switch to a new carrier entirely. Generally speaking, there are two ways
that an attacker can compromise your phone number:

- Social engineer a support agent (easier)
- Compromise an insider (harder)

By switching to a high-security carrier, you reduce or eliminate the risk from social engineering, but you’re still at
risk of an insider attack. Unfortunately, there’s almost nothing you can do to defend against that.

### USA

If you live in the USA, you get the option of one of the big three Mobile Network Operators: AT&T, Verizon, and
T-Mobile. None is perfect, but AT&T and Verizon are slightly ahead in terms of security reputation, while T-Mobile has
been compromised a handful of times.

#### Google Fi

[Google Fi](https://fi.google.com/) is an MVNO using T-Mobile’s network and only offers online support via your Google
account. Given the seriousness that Google approaches security with, Google Fi is one of the most secure self-service
carriers you can choose in the USA. This is even more so if you enable Advanced Protection on your Google account.

For an added bonus, you might consider creating a new Google account under a fake name and purchasing Google Fi from
there. This will ensure that an insider at T-Mobile won’t be able to find your phone number by name.

#### Efani

[Efani](https://www.efani.com/) is an MVNO using AT&T’s and Verizon’s networks and is designed for high-risk
individuals. Efani has negotiated agreements in which they are responsible for manually approving requests to modify
subscriber accounts instead of allowing agents at AT&T or Verizon to make those changes. Efani also masks your
information before submitting it to the MNOs, making it harder for an insider to locate your account.

## Place a Note on Your Carrier Account

If you can’t switch carriers or no secure carriers are available in your area, your next option is to mitigate the
likelihood of a support agent being social engineered. Some carriers will offer this explicitly (for example, some sort
of account lock that you can opt into). If there is no option, you may need to either call or go in-store and ask for a
note to be placed on your account.

Keep in mind that some support agents may not know about SIM swapping, and that’s not their fault. If this happens, you
might need to politely ask to speak to a manager or just come back another day. Also, keep in mind that while you may be
able to add an internal note to your account, there’s no guarantee that whatever support agent who is communicating
with a scammer will actually read the note. The scammer may also be able to convince the agent that they’re desperately
in need to regain access quickly, and to ignore the note entirely. As such, placing a note on your account is a nice
additional measure but not nearly as effective as simply disabling SMS 2FA on your accounts.

---

