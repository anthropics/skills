export function calculateShippingCost(
  provider: string,
  weightKg: number,
  destinationCountry: string,
  isExpress: boolean
): number {
  let baseCost = 0;
  let perKgCost = 0;

  switch (provider) {
    case 'usps':
      baseCost = 5.50;
      perKgCost = 2.30;
      if (destinationCountry !== 'US') {
        baseCost = 15.00;
        perKgCost = 8.00;
      }
      break;
    case 'ups':
      baseCost = 8.00;
      perKgCost = 3.50;
      if (destinationCountry !== 'US') {
        baseCost = 20.00;
        perKgCost = 10.00;
      }
      break;
    case 'fedex':
      baseCost = 9.00;
      perKgCost = 4.00;
      if (destinationCountry !== 'US') {
        baseCost = 25.00;
        perKgCost = 12.00;
      }
      break;
    case 'dhl':
      baseCost = 12.00;
      perKgCost = 5.00;
      if (destinationCountry !== 'US') {
        baseCost = 18.00;
        perKgCost = 7.50;
      }
      break;
    default:
      throw new Error('Unknown provider: ' + provider);
  }

  let cost = baseCost + (perKgCost * weightKg);

  if (isExpress) {
    if (provider === 'usps') cost = cost * 1.5;
    else if (provider === 'ups') cost = cost * 1.75;
    else if (provider === 'fedex') cost = cost * 1.8;
    else if (provider === 'dhl') cost = cost * 2.0;
  }

  if (weightKg > 20) {
    cost = cost + 10;
  } else if (weightKg > 10) {
    cost = cost + 5;
  }

  return cost;
}
