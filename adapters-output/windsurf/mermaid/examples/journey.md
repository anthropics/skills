## Instructions

User journey diagrams visualize the experience of a user as they interact with a system or service, showing different stages and touchpoints.

### Syntax

- Use `journey` keyword
- Title: `title Title Text`
- Sections: `section Section Name`
- Steps: `Step Name: Score: Actor1, Actor2`
- Score: 1-5 (satisfaction level)
- Actors: Who performs the step

### Example

```mermaid
journey
    title User Shopping Journey
    section Browse
      Visit Website: 5: User
      Search Products: 4: User
      View Product Details: 5: User
    section Purchase
      Add to Cart: 4: User
      Checkout: 3: User
      Payment: 4: User, Payment System
    section Delivery
      Order Confirmation: 5: System
      Shipping: 4: Logistics
      Receive Product: 5: User
```
