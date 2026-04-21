# Defining Thresholds for On-Chain Monitoring

Setting appropriate thresholds for on-chain monitoring is hard when taking into account you want to detect unusual
activities, without generating excessive false positives. Here are some guidelines for defining and configuring
thresholds.

## Generic Guidelines

### Understand Normal Activity Patterns

1. Establish baseline metrics for normal activities, such as average transaction volumes and typical token minting rates
(if any).
2. Use historical data to understand activity patterns and identify deviations from the norm.

### Set Thresholds for Alerts

1. Define thresholds for large fund transfers from project wallets, considering both absolute amounts and relative
percentages.
2. Set thresholds for token minting events, including the number of tokens minted and the frequency of minting.
3. Establish thresholds for changes in contract ownership or significant modifications to contract code.

### Adjust Thresholds Over Time

1. Implement adaptive thresholds that can adjust based on changing activity patterns and emerging threats.
2. Periodically review and update thresholds to ensure they remain relevant and effective.

### Multi-Layered Thresholds

1. Use primary thresholds for critical alerts and secondary thresholds for less urgent notifications.
2. Define thresholds based on a combination of metrics to reduce false positives and improve accuracy.

### Anomaly Detection

It is hard, if not impossible, to predict every type of alert one should setup for their project. As such, implementing
an anomaly detection system can be of great value as it will monitor the project and its transactions in real time, and
compare it to its previous behavior. If for example it is common that 4% of tokens change owner each day and there's a
day with 20% of tokens changing owner in the past 10 minutes, then that could be detected as an anomaly cause for
investigation.

---

