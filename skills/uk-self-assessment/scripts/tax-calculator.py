#!/usr/bin/env python3
"""
UK Self Assessment Tax Calculator

Accepts JSON input with income/deduction data via stdin or file argument.
Calculates income tax, NIC, student loans, CGT, and outputs JSON breakdown.

Usage:
    echo '{"tax_year": "2024-25", "employment": [{"gross_pay": 45000, "tax_deducted": 6486}]}' | python3 tax-calculator.py
    python3 tax-calculator.py input.json
"""

import json
import sys
from dataclasses import dataclass, field
from typing import Optional

# ─── Tax rates by year ────────────────────────────────────────────────────────

TAX_RATES = {
    "2024-25": {
        "personal_allowance": 12570,
        "pa_taper_threshold": 100000,
        "basic_rate_limit": 37700,  # 12571 to 50270
        "higher_rate_limit": 87440,  # 50271 to 125140 (125140 - 37700 = 87440 taxable)
        "basic_rate": 0.20,
        "higher_rate": 0.40,
        "additional_rate": 0.45,
        "basic_rate_ceiling": 50270,  # PA + basic_rate_limit
        "additional_rate_floor": 125140,
        "dividend_allowance": 500,
        "dividend_basic": 0.0875,
        "dividend_higher": 0.3375,
        "dividend_additional": 0.3935,
        "savings_starting_rate_limit": 5000,
        "psa_basic": 1000,
        "psa_higher": 500,
        "psa_additional": 0,
        "marriage_allowance": 1260,
        "blind_persons_allowance": 2870,
        "trading_allowance": 1000,
        "property_allowance": 1000,
        # NIC Class 1 (employee)
        "nic1_primary_threshold": 12570,
        "nic1_upper_earnings_limit": 50270,
        "nic1_main_rate": 0.08,
        "nic1_additional_rate": 0.02,
        # NIC Class 4 (self-employed)
        "nic4_lower_profits": 12570,
        "nic4_upper_profits": 50270,
        "nic4_main_rate": 0.06,
        "nic4_additional_rate": 0.02,
        # Student loans
        "student_loan_plan1_threshold": 22015,
        "student_loan_plan2_threshold": 27295,
        "student_loan_plan4_threshold": 27660,
        "student_loan_plan5_threshold": 25000,
        "student_loan_postgrad_threshold": 21000,
        "student_loan_rate": 0.09,
        "postgrad_loan_rate": 0.06,
        # CGT
        "cgt_annual_exempt": 3000,
        "cgt_basic_rate": 0.18,  # post-Oct 2024 unified rate
        "cgt_higher_rate": 0.24,
        "cgt_property_basic_rate": 0.18,
        "cgt_property_higher_rate": 0.24,
        "cgt_badr_rate": 0.10,
        # Child benefit
        "child_benefit_threshold": 60000,
        "child_benefit_taper_end": 80000,
        "child_benefit_eldest": 1331.20,
        "child_benefit_other": 881.40,
        # Pension
        "pension_annual_allowance": 60000,
    },
    "2025-26": {
        "personal_allowance": 12570,
        "pa_taper_threshold": 100000,
        "basic_rate_limit": 37700,
        "higher_rate_limit": 87440,
        "basic_rate": 0.20,
        "higher_rate": 0.40,
        "additional_rate": 0.45,
        "basic_rate_ceiling": 50270,
        "additional_rate_floor": 125140,
        "dividend_allowance": 500,
        "dividend_basic": 0.0875,
        "dividend_higher": 0.3375,
        "dividend_additional": 0.3935,
        "savings_starting_rate_limit": 5000,
        "psa_basic": 1000,
        "psa_higher": 500,
        "psa_additional": 0,
        "marriage_allowance": 1260,
        "blind_persons_allowance": 3070,
        "trading_allowance": 1000,
        "property_allowance": 1000,
        # NIC Class 1
        "nic1_primary_threshold": 12570,
        "nic1_upper_earnings_limit": 50270,
        "nic1_main_rate": 0.08,
        "nic1_additional_rate": 0.02,
        # NIC Class 4
        "nic4_lower_profits": 12570,
        "nic4_upper_profits": 50270,
        "nic4_main_rate": 0.06,
        "nic4_additional_rate": 0.02,
        # Student loans
        "student_loan_plan1_threshold": 26065,
        "student_loan_plan2_threshold": 28470,
        "student_loan_plan4_threshold": 32745,
        "student_loan_plan5_threshold": 25000,
        "student_loan_postgrad_threshold": 21000,
        "student_loan_rate": 0.09,
        "postgrad_loan_rate": 0.06,
        # CGT
        "cgt_annual_exempt": 3000,
        "cgt_basic_rate": 0.18,
        "cgt_higher_rate": 0.24,
        "cgt_property_basic_rate": 0.18,
        "cgt_property_higher_rate": 0.24,
        "cgt_badr_rate": 0.14,
        # Child benefit
        "child_benefit_threshold": 60000,
        "child_benefit_taper_end": 80000,
        "child_benefit_eldest": 1354.60,
        "child_benefit_other": 897.00,
        # Pension
        "pension_annual_allowance": 60000,
    },
}


def round_tax(amount: float) -> float:
    """Round to 2 decimal places."""
    return round(amount, 2)


def calculate_personal_allowance(total_income: float, rates: dict, blind: bool = False, marriage_allowance_received: bool = False, marriage_allowance_given: bool = False) -> float:
    """Calculate personal allowance after taper and adjustments."""
    pa = rates["personal_allowance"]

    # Blind Person's Allowance
    if blind:
        pa += rates["blind_persons_allowance"]

    # Marriage Allowance
    if marriage_allowance_received:
        pa += rates["marriage_allowance"]
    if marriage_allowance_given:
        pa -= rates["marriage_allowance"]

    # Taper for income over £100,000
    if total_income > rates["pa_taper_threshold"]:
        excess = total_income - rates["pa_taper_threshold"]
        reduction = excess / 2
        pa = max(0, pa - reduction)

    return pa


def calculate_income_tax(non_savings: float, savings: float, dividends: float, rates: dict, personal_allowance: float, pension_relief_gross: float = 0) -> dict:
    """
    Calculate income tax using the correct stacking order:
    non-savings income → savings income → dividend income.

    Pension contributions extend the basic rate band.
    """
    # Extend basic rate band by gross pension contributions
    extended_basic_limit = rates["basic_rate_limit"] + pension_relief_gross

    # Total income for band allocation
    total_income = non_savings + savings + dividends

    # Apply personal allowance — allocated against non-savings first, then savings, then dividends
    remaining_pa = personal_allowance

    taxable_non_savings = max(0, non_savings - remaining_pa)
    remaining_pa = max(0, remaining_pa - non_savings)

    taxable_savings = max(0, savings - remaining_pa)
    remaining_pa = max(0, remaining_pa - savings)

    taxable_dividends = max(0, dividends - remaining_pa)

    # ─── Non-savings income tax ───
    ns_tax = 0
    ns_basic = 0
    ns_higher = 0
    ns_additional = 0
    band_used = 0  # how much of the basic rate band has been used

    if taxable_non_savings > 0:
        # Basic rate
        basic_amount = min(taxable_non_savings, extended_basic_limit)
        ns_basic = basic_amount
        ns_tax += basic_amount * rates["basic_rate"]
        band_used += basic_amount

        # Higher rate
        remaining = taxable_non_savings - basic_amount
        if remaining > 0:
            higher_limit = rates["additional_rate_floor"] - rates["personal_allowance"] - extended_basic_limit
            higher_amount = min(remaining, max(0, higher_limit))
            ns_higher = higher_amount
            ns_tax += higher_amount * rates["higher_rate"]

            # Additional rate
            additional_amount = remaining - higher_amount
            if additional_amount > 0:
                ns_additional = additional_amount
                ns_tax += additional_amount * rates["additional_rate"]

    # ─── Savings income tax ───
    sav_tax = 0
    sav_basic = 0
    sav_higher = 0
    sav_additional = 0

    # Starting rate for savings (0% on up to £5,000 if non-savings income < PA + £5,000)
    savings_starting_rate_available = max(0, rates["savings_starting_rate_limit"] - max(0, taxable_non_savings))

    # Personal Savings Allowance
    # Determine taxpayer band based on total taxable income for PSA
    total_taxable = taxable_non_savings + taxable_savings + taxable_dividends
    if total_taxable <= extended_basic_limit:
        psa = rates["psa_basic"]
    elif total_taxable <= (rates["additional_rate_floor"] - rates["personal_allowance"]):
        psa = rates["psa_higher"]
    else:
        psa = rates["psa_additional"]

    if taxable_savings > 0:
        remaining_savings = taxable_savings

        # Starting rate for savings (0%)
        starting_rate_amount = min(remaining_savings, savings_starting_rate_available)
        remaining_savings -= starting_rate_amount
        band_used_for_savings = band_used + starting_rate_amount

        # PSA (0%)
        psa_amount = min(remaining_savings, psa)
        remaining_savings -= psa_amount
        band_used_for_savings += psa_amount

        # Basic rate
        basic_remaining = max(0, extended_basic_limit - band_used_for_savings)
        sav_basic_amount = min(remaining_savings, basic_remaining)
        sav_basic = sav_basic_amount
        sav_tax += sav_basic_amount * rates["basic_rate"]
        remaining_savings -= sav_basic_amount
        band_used_for_savings += sav_basic_amount

        # Higher rate
        if remaining_savings > 0:
            higher_limit = rates["additional_rate_floor"] - rates["personal_allowance"] - extended_basic_limit
            # Adjust for non-savings that already used higher band
            higher_used_by_ns = max(0, taxable_non_savings - extended_basic_limit)
            higher_remaining = max(0, higher_limit - higher_used_by_ns)
            sav_higher_amount = min(remaining_savings, higher_remaining)
            sav_higher = sav_higher_amount
            sav_tax += sav_higher_amount * rates["higher_rate"]
            remaining_savings -= sav_higher_amount

            # Additional rate
            if remaining_savings > 0:
                sav_additional = remaining_savings
                sav_tax += remaining_savings * rates["additional_rate"]

    # ─── Dividend income tax ───
    div_tax = 0
    div_basic = 0
    div_higher = 0
    div_additional = 0

    if taxable_dividends > 0:
        remaining_divs = taxable_dividends

        # Dividend allowance (£500 at 0%)
        div_allowance_used = min(remaining_divs, rates["dividend_allowance"])
        remaining_divs -= div_allowance_used

        # Determine which band dividends fall into
        income_before_divs = taxable_non_savings + taxable_savings
        total_band_used = income_before_divs + div_allowance_used

        # Basic rate band remaining
        basic_remaining = max(0, extended_basic_limit - total_band_used)
        div_basic_amount = min(remaining_divs, basic_remaining)
        div_basic = div_basic_amount
        div_tax += div_basic_amount * rates["dividend_basic"]
        remaining_divs -= div_basic_amount
        total_band_used += div_basic_amount

        # Higher rate
        if remaining_divs > 0:
            higher_ceiling = rates["additional_rate_floor"] - rates["personal_allowance"]
            higher_remaining = max(0, higher_ceiling - total_band_used)
            div_higher_amount = min(remaining_divs, higher_remaining)
            div_higher = div_higher_amount
            div_tax += div_higher_amount * rates["dividend_higher"]
            remaining_divs -= div_higher_amount

            # Additional rate
            if remaining_divs > 0:
                div_additional = remaining_divs
                div_tax += remaining_divs * rates["dividend_additional"]

    total_tax = round_tax(ns_tax + sav_tax + div_tax)

    return {
        "non_savings_income": round_tax(non_savings),
        "taxable_non_savings": round_tax(taxable_non_savings),
        "savings_income": round_tax(savings),
        "taxable_savings": round_tax(taxable_savings),
        "dividend_income": round_tax(dividends),
        "taxable_dividends": round_tax(taxable_dividends),
        "personal_allowance_used": round_tax(personal_allowance),
        "non_savings_tax": round_tax(ns_tax),
        "non_savings_breakdown": {
            "basic_rate": round_tax(ns_basic),
            "higher_rate": round_tax(ns_higher),
            "additional_rate": round_tax(ns_additional),
        },
        "savings_tax": round_tax(sav_tax),
        "savings_breakdown": {
            "starting_rate_0pc": round_tax(min(taxable_savings, savings_starting_rate_available) if taxable_savings > 0 else 0),
            "psa_0pc": round_tax(min(max(0, taxable_savings - savings_starting_rate_available), psa) if taxable_savings > 0 else 0),
            "basic_rate": round_tax(sav_basic),
            "higher_rate": round_tax(sav_higher),
            "additional_rate": round_tax(sav_additional),
        },
        "dividend_tax": round_tax(div_tax),
        "dividend_breakdown": {
            "allowance_0pc": round_tax(min(taxable_dividends, rates["dividend_allowance"]) if taxable_dividends > 0 else 0),
            "basic_rate": round_tax(div_basic),
            "higher_rate": round_tax(div_higher),
            "additional_rate": round_tax(div_additional),
        },
        "total_income_tax": total_tax,
    }


def calculate_nic_class4(self_employment_profit: float, rates: dict) -> dict:
    """Calculate Class 4 NIC on self-employment profits."""
    if self_employment_profit <= rates["nic4_lower_profits"]:
        return {"class4_nic": 0, "main_rate_amount": 0, "additional_rate_amount": 0}

    main_rate_amount = min(
        max(0, self_employment_profit - rates["nic4_lower_profits"]),
        rates["nic4_upper_profits"] - rates["nic4_lower_profits"],
    )
    additional_rate_amount = max(0, self_employment_profit - rates["nic4_upper_profits"])

    class4 = (main_rate_amount * rates["nic4_main_rate"]) + (additional_rate_amount * rates["nic4_additional_rate"])

    return {
        "class4_nic": round_tax(class4),
        "main_rate_amount": round_tax(main_rate_amount),
        "additional_rate_amount": round_tax(additional_rate_amount),
    }


def calculate_student_loan(gross_income: float, plans: list, rates: dict) -> dict:
    """Calculate student loan repayments."""
    result = {}
    total = 0

    for plan in plans:
        plan_lower = plan.lower().replace(" ", "")
        if plan_lower in ("plan1", "1"):
            threshold = rates["student_loan_plan1_threshold"]
            rate = rates["student_loan_rate"]
            key = "plan1"
        elif plan_lower in ("plan2", "2"):
            threshold = rates["student_loan_plan2_threshold"]
            rate = rates["student_loan_rate"]
            key = "plan2"
        elif plan_lower in ("plan4", "4"):
            threshold = rates["student_loan_plan4_threshold"]
            rate = rates["student_loan_rate"]
            key = "plan4"
        elif plan_lower in ("plan5", "5"):
            threshold = rates["student_loan_plan5_threshold"]
            rate = rates["student_loan_rate"]
            key = "plan5"
        elif plan_lower in ("postgraduate", "postgrad", "pg"):
            threshold = rates["student_loan_postgrad_threshold"]
            rate = rates["postgrad_loan_rate"]
            key = "postgraduate"
        else:
            continue

        repayment = max(0, (gross_income - threshold) * rate)
        result[key] = {
            "threshold": threshold,
            "rate": rate,
            "repayment": round_tax(repayment),
        }
        total += repayment

    result["total_student_loan"] = round_tax(total)
    return result


def calculate_cgt(gains: list, rates: dict, remaining_basic_band: float) -> dict:
    """
    Calculate Capital Gains Tax.

    gains: list of {"proceeds": float, "cost": float, "type": "shares"|"property"|"other", "badr": bool}
    remaining_basic_band: how much of the basic rate band is unused after income tax
    """
    total_gains = 0
    total_losses = 0
    gains_by_type = {"shares": 0, "property": 0, "other": 0, "badr": 0}

    for g in gains:
        gain = g.get("proceeds", 0) - g.get("cost", 0)
        if gain > 0:
            if g.get("badr"):
                gains_by_type["badr"] += gain
            else:
                gains_by_type[g.get("type", "other")] += gain
            total_gains += gain
        else:
            total_losses += abs(gain)

    # Apply losses
    net_gains = max(0, total_gains - total_losses)

    # Apply annual exempt amount
    exempt_used = min(net_gains, rates["cgt_annual_exempt"])
    taxable_gains = max(0, net_gains - exempt_used)

    # Calculate CGT
    cgt = 0
    remaining_band = remaining_basic_band

    # BADR gains first (flat rate)
    badr_gains = min(gains_by_type["badr"], taxable_gains)
    if badr_gains > 0:
        cgt += badr_gains * rates["cgt_badr_rate"]
        taxable_gains -= badr_gains

    # Remaining gains: basic rate then higher rate
    if taxable_gains > 0:
        basic_amount = min(taxable_gains, max(0, remaining_band))
        higher_amount = taxable_gains - basic_amount

        # Use property rates for property gains, standard rates for others
        # Simplified: use the unified rates (post Oct 2024 they're the same)
        cgt += basic_amount * rates["cgt_basic_rate"]
        cgt += higher_amount * rates["cgt_higher_rate"]

    return {
        "total_gains": round_tax(total_gains),
        "total_losses": round_tax(total_losses),
        "net_gains": round_tax(net_gains),
        "annual_exempt_used": round_tax(exempt_used),
        "taxable_gains": round_tax(max(0, net_gains - exempt_used)),
        "badr_gains": round_tax(gains_by_type["badr"]),
        "cgt_due": round_tax(cgt),
    }


def calculate_child_benefit_charge(adjusted_net_income: float, num_children: int, rates: dict) -> dict:
    """Calculate High Income Child Benefit Charge."""
    if num_children <= 0 or adjusted_net_income <= rates["child_benefit_threshold"]:
        return {"charge": 0, "total_benefit": 0, "percentage_clawed_back": 0}

    # Total benefit
    benefit = rates["child_benefit_eldest"]
    if num_children > 1:
        benefit += (num_children - 1) * rates["child_benefit_other"]

    # Charge: 1% per £200 over threshold
    excess = adjusted_net_income - rates["child_benefit_threshold"]
    percentage = min(100, (excess / 200))  # 1% per £200
    charge = benefit * (percentage / 100)

    return {
        "total_benefit": round_tax(benefit),
        "percentage_clawed_back": round(percentage, 1),
        "charge": round_tax(charge),
    }


def calculate_payment_on_account(sa_liability: float, tax_deducted_at_source: float) -> dict:
    """Calculate payments on account for next year."""
    # POA required if SA liability > £1,000 AND less than 80% was deducted at source
    total_liability = sa_liability
    if total_liability <= 1000:
        return {"poa_required": False, "each_payment": 0, "reason": "Liability is £1,000 or less"}

    source_percentage = (tax_deducted_at_source / total_liability * 100) if total_liability > 0 else 100
    if source_percentage >= 80:
        return {"poa_required": False, "each_payment": 0, "reason": "80% or more was deducted at source"}

    each_payment = round_tax(total_liability / 2)
    return {
        "poa_required": True,
        "each_payment": each_payment,
        "total_poa": round_tax(total_liability),
        "reason": f"SA liability of £{total_liability:,.2f} with {source_percentage:.1f}% deducted at source",
    }


def calculate_tax(data: dict) -> dict:
    """Main calculation entry point."""
    tax_year = data.get("tax_year", "2024-25")
    if tax_year not in TAX_RATES:
        return {"error": f"Unsupported tax year: {tax_year}. Supported: {list(TAX_RATES.keys())}"}

    rates = TAX_RATES[tax_year]

    # ─── Gather income ───
    # Employment
    employments = data.get("employment", [])
    total_employment_gross = sum(e.get("gross_pay", 0) for e in employments)
    total_employment_tax = sum(e.get("tax_deducted", 0) for e in employments)
    total_benefits = sum(e.get("benefits", 0) for e in employments)

    # Self-employment
    self_employments = data.get("self_employment", [])
    total_se_profit = sum(se.get("profit", 0) for se in self_employments)

    # Savings
    savings_interest = data.get("savings_interest", 0)

    # Dividends
    dividends = data.get("dividends", 0)

    # Rental
    rental = data.get("rental", {})
    rental_profit = rental.get("profit", 0)
    rental_finance_costs = rental.get("finance_costs", 0)  # mortgage interest for tax reducer

    # Pension contributions
    pension = data.get("pension", {})
    personal_pension_gross = pension.get("personal_gross", 0)  # gross amount (already includes basic rate relief)
    employer_pension = pension.get("employer", 0)

    # Other
    other_income = data.get("other_income", 0)

    # ─── Personal circumstances ───
    blind = data.get("blind_persons_allowance", False)
    marriage_allowance_received = data.get("marriage_allowance_received", False)
    marriage_allowance_given = data.get("marriage_allowance_given", False)
    student_loan_plans = data.get("student_loan_plans", [])
    child_benefit = data.get("child_benefit", {})
    gift_aid = data.get("gift_aid", 0)
    previous_year_liability = data.get("previous_year_sa_liability", 0)

    # ─── Calculate totals ───
    non_savings_income = total_employment_gross + total_benefits + total_se_profit + rental_profit + other_income
    total_income = non_savings_income + savings_interest + dividends

    # Adjusted net income (for PA taper and child benefit): total income minus pension and gift aid
    # Pension contributions extend the basic rate band and reduce adjusted net income
    # Gift Aid extends the basic rate band too
    adjusted_net_income = total_income - personal_pension_gross - (gift_aid * 1.25)  # gross up gift aid

    # Personal allowance
    pa = calculate_personal_allowance(
        adjusted_net_income, rates, blind, marriage_allowance_received, marriage_allowance_given
    )

    # Pension relief extends basic rate band
    pension_relief_gross = personal_pension_gross + (gift_aid * 1.25)

    # ─── Income tax ───
    income_tax = calculate_income_tax(
        non_savings_income, savings_interest, dividends, rates, pa, pension_relief_gross
    )

    # ─── Rental finance costs tax reducer (20%) ───
    finance_cost_reducer = round_tax(rental_finance_costs * 0.20)

    # ─── Marriage Allowance tax reducer ───
    marriage_allowance_reducer = 0
    if marriage_allowance_received:
        marriage_allowance_reducer = round_tax(rates["marriage_allowance"] * 0.20)

    # Total income tax after reducers
    income_tax_after_reducers = round_tax(
        max(0, income_tax["total_income_tax"] - finance_cost_reducer - marriage_allowance_reducer)
    )

    # ─── NIC ───
    nic4 = calculate_nic_class4(total_se_profit, rates) if total_se_profit > 0 else {"class4_nic": 0}

    # ─── Student loans ───
    # Student loan is calculated on total relevant income
    student_loan_income = total_employment_gross + total_se_profit
    student_loans = calculate_student_loan(student_loan_income, student_loan_plans, rates) if student_loan_plans else {"total_student_loan": 0}

    # ─── CGT ───
    capital_gains = data.get("capital_gains", [])
    remaining_basic_band = max(0, rates["basic_rate_limit"] + pension_relief_gross - max(0, non_savings_income + savings_interest + dividends - pa))
    cgt = calculate_cgt(capital_gains, rates, remaining_basic_band) if capital_gains else {"cgt_due": 0, "total_gains": 0, "taxable_gains": 0}

    # ─── Child benefit charge ───
    num_children = child_benefit.get("num_children", 0)
    child_benefit_charge = calculate_child_benefit_charge(adjusted_net_income, num_children, rates)

    # ─── Total liability ───
    total_tax_due = round_tax(
        income_tax_after_reducers
        + nic4.get("class4_nic", 0)
        + student_loans.get("total_student_loan", 0)
        + cgt.get("cgt_due", 0)
        + child_benefit_charge.get("charge", 0)
    )

    # Tax already paid
    tax_already_paid = round_tax(total_employment_tax)
    # Could also include tax deducted from savings, CGT already paid, etc.
    tax_already_paid += data.get("other_tax_paid", 0)

    amount_owed = round_tax(total_tax_due - tax_already_paid)

    # ─── Payment on account ───
    sa_liability_for_poa = round_tax(total_tax_due - total_employment_tax)  # SA liability excluding PAYE
    poa = calculate_payment_on_account(sa_liability_for_poa, 0)  # POA based on SA-only liability

    # ─── Build result ───
    result = {
        "tax_year": tax_year,
        "income_summary": {
            "employment_gross": round_tax(total_employment_gross),
            "employment_benefits": round_tax(total_benefits),
            "self_employment_profit": round_tax(total_se_profit),
            "savings_interest": round_tax(savings_interest),
            "dividends": round_tax(dividends),
            "rental_profit": round_tax(rental_profit),
            "other_income": round_tax(other_income),
            "total_income": round_tax(total_income),
            "adjusted_net_income": round_tax(adjusted_net_income),
        },
        "personal_allowance": round_tax(pa),
        "income_tax": income_tax,
        "tax_reducers": {
            "finance_cost_reducer": finance_cost_reducer,
            "marriage_allowance_reducer": marriage_allowance_reducer,
        },
        "income_tax_after_reducers": income_tax_after_reducers,
        "national_insurance": nic4,
        "student_loans": student_loans,
        "capital_gains_tax": cgt,
        "child_benefit_charge": child_benefit_charge,
        "headline": {
            "total_income": round_tax(total_income),
            "total_tax_due": total_tax_due,
            "tax_already_paid": tax_already_paid,
            "amount_owed": amount_owed,
            "amount_refund": round_tax(abs(amount_owed)) if amount_owed < 0 else 0,
        },
        "payment_on_account": poa,
    }

    return result


def main():
    # Read input
    if len(sys.argv) > 1:
        with open(sys.argv[1], "r") as f:
            data = json.load(f)
    else:
        data = json.load(sys.stdin)

    result = calculate_tax(data)
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
