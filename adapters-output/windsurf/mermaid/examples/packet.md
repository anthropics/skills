## Instructions

Packet diagrams visualize network packet structures, showing the layers and fields of network protocols.

### Syntax

- Use `packet-beta` keyword
- Packets: `packet PacketName { }`
- Fields: `field FieldName : Type`
- Nested structures: Indentation for nested fields
- Bit fields: `field FieldName : Type (bits)`

### Example

```mermaid
packet-beta
    packet Ethernet {
        field Destination MAC : 48 bits
        field Source MAC : 48 bits
        field Type : 16 bits
    }
    packet IPv4 {
        field Version : 4 bits
        field Header Length : 4 bits
        field Total Length : 16 bits
        field Protocol : 8 bits
    }
```
