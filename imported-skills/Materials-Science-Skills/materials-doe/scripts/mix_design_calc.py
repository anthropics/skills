"""Mix design calculations: dense packing (Furnas model) and volume method (ACI 211.1)."""

import argparse
import json
import sys

import numpy as np


def dense_packing(components: list[dict]) -> list[dict]:
    """Compute optimal volume fractions using the Furnas packing model.

    Each component dict: {name, size_min_mm, size_max_mm, packing_density}
    packing_density: void ratio of the fraction when loosely packed (0-1).

    Returns components sorted by size descending with computed volume_fractions.
    """
    sorted_comp = sorted(components, key=lambda c: c["size_max_mm"], reverse=True)

    if len(sorted_comp) < 2:
        for c in sorted_comp:
            c["volume_fraction"] = 1.0 / len(sorted_comp) if sorted_comp else 0.0
        return sorted_comp

    voids = [1.0 - c["packing_density"] for c in sorted_comp]

    fractions = []
    remaining = 1.0
    for i, comp in enumerate(sorted_comp):
        if i == len(sorted_comp) - 1:
            fractions.append(remaining)
        else:
            void_ratio = voids[i] / (voids[i] + voids[i + 1]) if (voids[i] + voids[i + 1]) > 0 else 0.5
            frac = remaining * void_ratio
            fractions.append(frac)
            remaining -= frac

    for comp, frac in zip(sorted_comp, fractions):
        comp["volume_fraction"] = round(frac, 4)

    return sorted_comp


def volume_method(
    target_strength: float,
    wc_ratio: float,
    water_content: float = 185.0,
    cement_sg: float = 3.15,
    coarse_agg_sg: float = 2.65,
    fine_agg_sg: float = 2.60,
    coarse_agg_frac: float = 0.60,
    air_content: float = 2.0,
) -> dict:
    """Proportion concrete by absolute volume method (ACI 211.1).

    Args:
        target_strength: Target 28-day compressive strength (MPa).
        wc_ratio: Water-to-cement ratio.
        water_content: Estimated water content (kg/m³).
        cement_sg: Specific gravity of cement.
        coarse_agg_sg: Specific gravity of coarse aggregate.
        fine_agg_sg: Specific gravity of fine aggregate.
        coarse_agg_frac: Volume fraction of coarse aggregate in total aggregate.
        air_content: Air content (%).

    Returns:
        Dict with per-component masses (kg/m³) and volumes (m³).

    Raises:
        ValueError: if inputs are physically invalid (non-positive, out of range,
            or resulting in a negative aggregate volume).
    """
    if target_strength <= 0:
        raise ValueError("target_strength must be positive")
    if wc_ratio <= 0:
        raise ValueError("wc_ratio must be positive")
    if water_content <= 0:
        raise ValueError("water_content must be positive")
    if cement_sg <= 0 or coarse_agg_sg <= 0 or fine_agg_sg <= 0:
        raise ValueError("specific gravities must be positive")
    if not 0 <= coarse_agg_frac <= 1:
        raise ValueError("coarse_agg_frac must be between 0 and 1")
    if not 0 <= air_content < 100:
        raise ValueError("air_content must be between 0 and 100")

    cement_mass = water_content / wc_ratio
    air_volume = air_content / 100.0

    water_volume = water_content / 1000.0
    cement_volume = cement_mass / (cement_sg * 1000.0)

    total_agg_volume = 1.0 - water_volume - cement_volume - air_volume
    if total_agg_volume < 0:
        raise ValueError(
            f"aggregate volume is negative ({total_agg_volume:.4f} m³): "
            "reduce water content, wc_ratio, or air content"
        )
    coarse_volume = total_agg_volume * coarse_agg_frac
    fine_volume = total_agg_volume * (1.0 - coarse_agg_frac)

    coarse_mass = coarse_volume * coarse_agg_sg * 1000.0
    fine_mass = fine_volume * fine_agg_sg * 1000.0

    return {
        "target_strength_MPa": target_strength,
        "wc_ratio": wc_ratio,
        "components": {
            "water": {"mass_kg_m3": round(water_content, 1), "volume_m3": round(water_volume, 4)},
            "cement": {"mass_kg_m3": round(cement_mass, 1), "volume_m3": round(cement_volume, 4)},
            "coarse_aggregate": {"mass_kg_m3": round(coarse_mass, 1), "volume_m3": round(coarse_volume, 4)},
            "fine_aggregate": {"mass_kg_m3": round(fine_mass, 1), "volume_m3": round(fine_volume, 4)},
            "air": {"volume_m3": round(air_volume, 4)},
        },
        "total_volume_m3": round(water_volume + cement_volume + coarse_volume + fine_volume + air_volume, 4),
    }


def empirical_correction(
    base_mix: dict[str, float],
    corrections: dict[str, float],
) -> dict[str, float]:
    """Apply multiplicative corrections to a base mix.

    corrections: {component_name: factor} where factor > 1 means increase.
    """
    result = dict(base_mix)
    for comp, factor in corrections.items():
        if comp in result:
            result[comp] = round(result[comp] * factor, 1)
    return result


def _run_dense_packing(args):
    components = []
    for i in range(0, len(args.component), 4):
        components.append({
            "name": args.component[i],
            "size_min_mm": float(args.component[i + 1]),
            "size_max_mm": float(args.component[i + 2]),
            "packing_density": float(args.component[i + 3]),
        })
    result = dense_packing(components)
    print(json.dumps(result, indent=2, ensure_ascii=False))


def _run_volume_method(args):
    result = volume_method(
        target_strength=args.target_strength,
        wc_ratio=args.wc_ratio,
        water_content=args.water_content,
        cement_sg=args.cement_sg,
        coarse_agg_sg=args.coarse_agg_sg,
        fine_agg_sg=args.fine_agg_sg,
        coarse_agg_frac=args.coarse_agg_frac,
        air_content=args.air_content,
    )
    print(json.dumps(result, indent=2, ensure_ascii=False))


def main():
    parser = argparse.ArgumentParser(description="Mix design calculator")
    sub = parser.add_subparsers(dest="command")

    dp = sub.add_parser("dense-packing", help="Furnas dense packing calculation")
    dp.add_argument(
        "--component", "-c",
        nargs="+",
        required=True,
        help="Components as: name size_min_mm size_max_mm packing_density (repeat for each)",
    )

    vm = sub.add_parser("volume-method", help="ACI 211.1 volume method")
    vm.add_argument("--target-strength", type=float, required=True, help="Target 28-day strength (MPa)")
    vm.add_argument("--wc-ratio", type=float, required=True, help="Water-to-cement ratio")
    vm.add_argument("--water-content", type=float, default=185.0, help="Water content kg/m³ (default: 185)")
    vm.add_argument("--cement-sg", type=float, default=3.15, help="Cement specific gravity (default: 3.15)")
    vm.add_argument("--coarse-agg-sg", type=float, default=2.65, help="Coarse agg SG (default: 2.65)")
    vm.add_argument("--fine-agg-sg", type=float, default=2.60, help="Fine agg SG (default: 2.60)")
    vm.add_argument("--coarse-agg-frac", type=float, default=0.60, help="Coarse agg volume fraction (default: 0.60)")
    vm.add_argument("--air-content", type=float, default=2.0, help="Air content %% (default: 2.0)")

    args = parser.parse_args()
    if args.command == "dense-packing":
        _run_dense_packing(args)
    elif args.command == "volume-method":
        _run_volume_method(args)
    else:
        parser.print_help()
        sys.exit(1)


if __name__ == "__main__":
    main()
