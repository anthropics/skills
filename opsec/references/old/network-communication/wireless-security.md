# Wireless Security

Wireless networks offers convenience and flexibility. However, they also present unique security challenges.

## Key Components of Wireless Security

### Secure Network Configuration

1. Use WPA3 (Wi-Fi Protected Access 3) for the highest level of security. If WPA3 is not available, use WPA2 with AES
encryption.
2. Disable SSID broadcasting to hide the network from casual discovery, although it's still visible by scanners. Use a
non-identifiable SSID that does not reveal the project’s name or purpose.
3. Segment the wireless network from the wired network, if you have critical devices connected via the wired network
that does not require someone to access it from the wireless network. Use VLANs to separate different types of traffic
and limit access to sensitive resources.

### Access Control

1. Use strong, unique passwords for network access. Never use default passwords provided by the manufacturer.
2. Consider implementing MAC address filtering to restrict network access to authorized devices only. Regularly update
the list of allowed devices.
3. Considering using enterprise-grade authentication methods, such as 802.1X with RADIUS, to authenticate users before
granting network access.

### Monitoring and Intrusion Detection

1. Deploy WIDS to monitor for suspicious activities, unauthorized devices, and rogue access points, especially if built
into the wireless network system of your choice.
2. Monitor network traffic for unusual patterns that may indicate a security breach or attack, which can be enabled on
some wireless network devices.

### Device Security

1. Regularly update the firmware of wireless access points and routers to patch security vulnerabilities.
2. Disable unnecessary services and features on wireless devices to reduce the attack surface. Implement strong access
controls and change default settings.
3. Secure wireless access points in locked enclosures to prevent tampering and unauthorized access.

## Best Practices for Wireless Security

### Network Security

1. Consider the security implications of someone obtaining access into your network via an activated inbound VPN
connection, and make configurations to prevent a disaster should this happen, if inbound VPN must be enabled.
2. Create a secure wireless network for your work, and use a less safe wireless network for other devices such as IoT
devices, TVs, and other types of non-work related devices that is on a restricted network.

### Guest Networks

1. Set up a separate guest network for friends and temporary users. Ensure it is isolated from the main corporate
network.
2. Restrict guest network access to the internet only. Implement bandwidth limits and usage policies to prevent abuse.

---

