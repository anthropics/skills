
use typenum::*;
use core::ops::*;
use core::cmp::Ordering;

#[test]
#[allow(non_snake_case)]
fn test_0_BitAnd_0() {
    type A = UTerm;
    type B = UTerm;
    type U0 = UTerm;

    #[allow(non_camel_case_types)]
    type U0BitAndU0 = <<A as BitAnd<B>>::Output as Same<U0>>::Output;

    assert_eq!(<U0BitAndU0 as Unsigned>::to_u64(), <U0 as Unsigned>::to_u64());
}
#[test]
#[allow(non_snake_case)]
fn test_0_BitOr_0() {
    type A = UTerm;
    type B = UTerm;
    type U0 = UTerm;

    #[allow(non_camel_case_types)]
    type U0BitOrU0 = <<A as BitOr<B>>::Output as Same<U0>>::Output;

    assert_eq!(<U0BitOrU0 as Unsigned>::to_u64(), <U0 as Unsigned>::to_u64());
}
#[test]
#[allow(non_snake_case)]
fn test_0_BitXor_0() {
    type A = UTerm;
    type B = UTerm;
    type U0 = UTerm;

    #[allow(non_camel_case_types)]
    type U0BitXorU0 = <<A as BitXor<B>>::Output as Same<U0>>::Output;

    assert_eq!(<U0BitXorU0 as Unsigned>::to_u64(), <U0 as Unsigned>::to_u64());
}
#[test]
#[allow(non_snake_case)]
fn test_0_Shl_0() {
    type A = UTerm;
    type B = UTerm;
    type U0 = UTerm;

    #[allow(non_camel_case_types)]
    type U0ShlU0 = <<A as Shl<B>>::Output as Same<U0>>::Output;

    assert_eq!(<U0ShlU0 as Unsigned>::to_u64(), <U0 as Unsigned>::to_u64());
}
#[test]
#[allow(non_snake_case)]
fn test_0_Shr_0() {
    type A = UTerm;
    type B = UTerm;
    type U0 = UTerm;

    #[allow(non_camel_case_types)]
    type U0ShrU0 = <<A as Shr<B>>::Output as Same<U0>>::Output;

    assert_eq!(<U0ShrU0 as Unsigned>::to_u64(), <U0 as Unsigned>::to_u64());
}
#[test]
#[allow(non_snake_case)]
fn test_0_Add_0() {
    type A = UTerm;
    type B = UTerm;
    type U0 = UTerm;

    #[allow(non_camel_case_types)]
    type U0AddU0 = <<A as Add<B>>::Output as Same<U0>>::Output;

    assert_eq!(<U0AddU0 as Unsigned>::to_u64(), <U0 as Unsigned>::to_u64());
}
#[test]
#[allow(non_snake_case)]
fn test_0_Mul_0() {
    type A = UTerm;
    type B = UTerm;
    type U0 = UTerm;

    #[allow(non_camel_case_types)]
    type U0MulU0 = <<A as Mul<B>>::Output as Same<U0>>::Output;

    assert_eq!(<U0MulU0 as Unsigned>::to_u64(), <U0 as Unsigned>::to_u64());
}
#[test]
#[allow(non_snake_case)]
fn test_0_Pow_0() {
    type A = UTerm;
    type B = UTerm;
    type U1 = UInt<UTerm, B1>;

    #[allow(non_camel_case_types)]
    type U0PowU0 = <<A as Pow<B>>::Output as Same<U1>>::Output;

    assert_eq!(<U0PowU0 as Unsigned>::to_u64(), <U1 as Unsigned>::to_u64());
}
#[test]
#[allow(non_snake_case)]
fn test_0_Min_0() {
    type A = UTerm;
    type B = UTerm;
    type U0 = UTerm;

    #[allow(non_camel_case_types)]
    type U0MinU0 = <<A as Min<B>>::Output as Same<U0>>::Output;

    assert_eq!(<U0MinU0 as Unsigned>::to_u64(), <U0 as Unsigned>::to_u64());
}
#[test]
#[allow(non_snake_case)]
fn test_0_Max_0() {
    type A = UTerm;
    type B = UTerm;
    type U0 = UTerm;

    #[allow(non_camel_case_types)]
    type U0MaxU0 = <<A as Max<B>>::Output as Same<U0>>::Output;

    assert_eq!(<U0MaxU0 as Unsigned>::to_u64(), <U0 as Unsigned>::to_u64());
}
#[test]
#[allow(non_snake_case)]
fn test_0_Gcd_0() {
    type A = UTerm;
    type B = UTerm;
    type U0 = UTerm;

    #[allow(non_camel_case_types)]
    type U0GcdU0 = <<A as Gcd<B>>::Output as Same<U0>>::Output;

    assert_eq!(<U0GcdU0 as Unsigned>::to_u64(), <U0 as Unsigned>::to_u64());
}
#[test]
#[allow(non_snake_case)]
fn test_0_Sub_0() {
    type A = UTerm;
    type B = UTerm;
    type U0 = UTerm;

    #[allow(non_camel_case_types)]
    type U0SubU0 = <<A as Sub<B>>::Output as Same<U0>>::Output;

    assert_eq!(<U0SubU0 as Unsigned>::to_u64(), <U0 as Unsigned>::to_u64());
}
#[test]
#[allow(non_snake_case)]
fn test_0_Cmp_0() {
    type A = UTerm;
    type B = UTerm;

    #[allow(non_camel_case_types)]
    type U0CmpU0 = <A as Cmp<B>>::Output;
    assert_eq!(<U0CmpU0 as Ord>::to_ordering(), Ordering::Equal);
}
#[test]
#[allow(non_snake_case)]
fn test_0_BitAnd_1() {
    type A = UTerm;
    type B = UInt<UTerm, B1>;
    type U0 = UTerm;

    #[allow(non_camel_case_types)]
    type U0BitAndU1 = <<A as BitAnd<B>>::Output as Same<U0>>::Output;

    assert_eq!(<U0BitAndU1 as Unsigned>::to_u64(), <U0 as Unsigned>::to_u64());
}
#[test]
#[allow(non_snake_case)]
fn test_0_BitOr_1() {
    type A = UTerm;
    type B = UInt<UTerm, B1>;
    type U1 = UInt<UTerm, B1>;

    #[allow(non_camel_case_types)]
    type U0BitOrU1 = <<A as BitOr<B>>::Output as Same<U1>>::Output;

    assert_eq!(<U0BitOrU1 as Unsigned>::to_u64(), <U1 as Unsigned>::to_u64());
}
#[test]
#[allow(non_snake_case)]
fn test_0_BitXor_1() {
    type A = UTerm;
    type B = UInt<UTerm, B1>;
    type U1 = UInt<UTerm, B1>;

    #[allow(non_camel_case_types)]
    type U0BitXorU1 = <<A as BitXor<B>>::Output as Same<U1>>::Output;

    assert_eq!(<U0BitXorU1 as Unsigned>::to_u64(), <U1 as Unsigned>::to_u64());
}
#[test]
#[allow(non_snake_case)]
fn test_0_Shl_1() {
    type A = UTerm;
    type B = UInt<UTerm, B1>;
    type U0 = UTerm;

    #[allow(non_camel_case_types)]
    type U0ShlU1 = <<A as Shl<B>>::Output as Same<U0>>::Output;

    assert_eq!(<U0ShlU1 as Unsigned>::to_u64(), <U0 as Unsigned>::to_u64());
}
#[test]
#[allow(non_snake_case)]
fn test_0_Shr_1() {
    type A = UTerm;
    type B = UInt<UTerm, B1>;
    type U0 = UTerm;

    #[allow(non_camel_case_types)]
    type U0ShrU1 = <<A as Shr<B>>::Output as Same<U0>>::Output;

    assert_eq!(<U0ShrU1 as Unsigned>::to_u64(), <U0 as Unsigned>::to_u64());
}
#[test]
#[allow(non_snake_case)]
fn test_0_Add_1() {
    type A = UTerm;
    type B = UInt<UTerm, B1>;
    type U1 = UInt<UTerm, B1>;

    #[allow(non_camel_case_types)]
    type U0AddU1 = <<A as Add<B>>::Output as Same<U1>>::Output;

    assert_eq!(<U0AddU1 as Unsigned>::to_u64(), <U1 as Unsigned>::to_u64());
}
#[test]
#[allow(non_snake_case)]
fn test_0_Mul_1() {
    type A = UTerm;
    type B = UInt<UTerm, B1>;
    type U0 = UTerm;

    #[allow(non_camel_case_types)]
    type U0MulU1 = <<A as Mul<B>>::Output as Same<U0>>::Output;

    assert_eq!(<U0MulU1 as Unsigned>::to_u64(), <U0 as Unsigned>::to_u64());
}
#[test]
#[allow(non_snake_case)]
fn test_0_Pow_1() {
    type A = UTerm;
    type B = UInt<UTerm, B1>;
    type U0 = UTerm;

    #[allow(non_camel_case_types)]
    type U0PowU1 = <<A as Pow<B>>::Output as Same<U0>>::Output;

    assert_eq!(<U0PowU1 as Unsigned>::to_u64(), <U0 as Unsigned>::to_u64());
}
#[test]
#[allow(non_snake_case)]
fn test_0_Min_1() {
    type A = UTerm;
    type B = UInt<UTerm, B1>;
    type U0 = UTerm;

    #[allow(non_camel_case_types)]
    type U0MinU1 = <<A as Min<B>>::Output as Same<U0>>::Output;

    assert_eq!(<U0MinU1 as Unsigned>::to_u64(), <U0 as Unsigned>::to_u64());
}
#[test]
#[allow(non_snake_case)]
fn test_0_Max_1() {
    type A = UTerm;
    type B = UInt<UTerm, B1>;
    type U1 = UInt<UTerm, B1>;

    #[allow(non_camel_case_types)]
    type U0MaxU1 = <<A as Max<B>>::Output as Same<U1>>::Output;

    assert_eq!(<U0MaxU1 as Unsigned>::to_u64(), <U1 as Unsigned>::to_u64());
}
#[test]
#[allow(non_snake_case)]
fn test_0_Gcd_1() {
    type A = UTerm;
    type B = UInt<UTerm, B1>;
    type U1 = UInt<UTerm, B1>;

    #[allow(non_camel_case_types)]
    type U0GcdU1 = <<A as Gcd<B>>::Output as Same<U1>>::Output;

    assert_eq!(<U0GcdU1 as Unsigned>::to_u64(), <U1 as Unsigned>::to_u64());
}
#[test]
#[allow(non_snake_case)]
fn test_0_Div_1() {
    type A = UTerm;
    type B = UInt<UTerm, B1>;
    type U0 = UTerm;

    #[allow(non_camel_case_types)]
    type U0DivU1 = <<A as Div<B>>::Output as Same<U0>>::Output;

    assert_eq!(<U0DivU1 as Unsigned>::to_u64(), <U0 as Unsigned>::to_u64());
}
#[test]
#[allow(non_snake_case)]
fn test_0_Rem_1() {
    type A = UTerm;
    type B = UInt<UTerm, B1>;
    type U0 = UTerm;

    #[allow(non_camel_case_types)]
    type U0RemU1 = <<A as Rem<B>>::Output as Same<U0>>::Output;

    assert_eq!(<U0RemU1 as Unsigned>::to_u64(), <U0 as Unsigned>::to_u64());
}
#[test]
#[allow(non_snake_case)]
fn test_0_PartialDiv_1() {
    type A = UTerm;
    type B = UInt<UTerm, B1>;
    type U0 = UTerm;

    #[allow(non_camel_case_types)]
    type U0PartialDivU1 = <<A as PartialDiv<B>>::Output as Same<U0>>::Output;

    assert_eq!(<U0PartialDivU1 as Unsigned>::to_u64(), <U0 as Unsigned>::to_u64());
}
#[test]
#[allow(non_snake_case)]
fn test_0_Cmp_1() {
    type A = UTerm;
    type B = UInt<UTerm, B1>;

    #[allow(non_camel_case_types)]
    type U0CmpU1 = <A as Cmp<B>>::Output;
    assert_eq!(<U0CmpU1 as Ord>::to_ordering(), Ordering::Less);
}
#[test]
#[allow(non_snake_case)]
fn test_0_BitAnd_2() {
    type A = UTerm;
    type B = UInt<UInt<UTerm, B1>, B0>;
    type U0 = UTerm;

    #[allow(non_camel_case_types)]
    type U0BitAndU2 = <<A as BitAnd<B>>::Output as Same<U0>>::Output;

    assert_eq!(<U0BitAndU2 as Unsigned>::to_u64(), <U0 as Unsigned>::to_u64());
}
#[test]
#[allow(non_snake_case)]
fn test_0_BitOr_2() {
    type A = UTerm;
    type B = UInt<UInt<UTerm, B1>, B0>;
    type U2 = UInt<UInt<UTerm, B1>, B0>;

    #[allow(non_camel_case_types)]
    type U0BitOrU2 = <<A as BitOr<B>>::Output as Same<U2>>::Output;

    assert_eq!(<U0BitOrU2 as Unsigned>::to_u64(), <U2 as Unsigned>::to_u64());
}
#[test]
#[allow(non_snake_case)]
fn test_0_BitXor_2() {
    type A = UTerm;
    type B = UInt<UInt<UTerm, B1>, B0>;
    type U2 = UInt<UInt<UTerm, B1>, B0>;

    #[allow(non_camel_case_types)]
    type U0BitXorU2 = <<A as BitXor<B>>::Output as Same<U2>>::Output;

    assert_eq!(<U0BitXorU2 as Unsigned>::to_u64(), <U2 as Unsigned>::to_u64());
}
#[test]
#[allow(non_snake_case)]
fn test_0_Shl_2() {
    type A = UTerm;
    type B = UInt<UInt<UTerm, B1>, B0>;
    type U0 = UTerm;

    #[allow(non_camel_case_types)]
    type U0ShlU2 = <<A as Shl<B>>::Output as Same<U0>>::Output;

    assert_eq!(<U0ShlU2 as Unsigned>::to_u64(), <U0 as Unsigned>::to_u64());
}
#[test]
#[allow(non_snake_case)]
fn test_0_Shr_2() {
    type A = UTerm;
    type B = UInt<UInt<UTerm, B1>, B0>;
    type U0 = UTerm;

    #[allow(non_camel_case_types)]
    type U0ShrU2 = <<A as Shr<B>>::Output as Same<U0>>::Output;

    assert_eq!(<U0ShrU2 as Unsigned>::to_u64(), <U0 as Unsigned>::to_u64());
}
#[test]
#[allow(non_snake_case)]
fn test_0_Add_2() {
    type A = UTerm;
    type B = UInt<UInt<UTerm, B1>, B0>;
    type U2 = UInt<UInt<UTerm, B1>, B0>;

    #[allow(non_camel_case_types)]
    type U0AddU2 = <<A as Add<B>>::Output as Same<U2>>::Output;

    assert_eq!(<U0AddU2 as Unsigned>::to_u64(), <U2 as Unsigned>::to_u64());
}
#[test]
#[allow(non_snake_case)]
fn test_0_Mul_2() {
    type A = UTerm;
    type B = UInt<UInt<UTerm, B1>, B0>;
    type U0 = UTerm;

    #[allow(non_camel_case_types)]
    type U0MulU2 = <<A as Mul<B>>::Output as Same<U0>>::Output;

    assert_eq!(<U0MulU2 as Unsigned>::to_u64(), <U0 as Unsigned>::to_u64());
}
#[test]
#[allow(non_snake_case)]
fn test_0_Pow_2() {
    type A = UTerm;
    type B = UInt<UInt<UTerm, B1>, B0>;
    type U0 = UTerm;

    #[allow(non_camel_case_types)]
    type U0PowU2 = <<A as Pow<B>>::Output as Same<U0>>::Output;

    assert_eq!(<U0PowU2 as Unsigned>::to_u64(), <U0 as Unsigned>::to_u64());
}
#[test]
#[allow(non_snake_case)]
fn test_0_Min_2() {
    type A = UTerm;
    type B = UInt<UInt<UTerm, B1>, B0>;
    type U0 = UTerm;

    #[allow(non_camel_case_types)]
    type U0MinU2 = <<A as Min<B>>::Output as Same<U0>>::Output;

    assert_eq!(<U0MinU2 as Unsigned>::to_u64(), <U0 as Unsigned>::to_u64());
}
#[test]
#[allow(non_snake_case)]
fn test_0_Max_2() {
    type A = UTerm;
    type B = UInt<UInt<UTerm, B1>, B0>;
    type U2 = UInt<UInt<UTerm, B1>, B0>;

    #[allow(non_camel_case_types)]
    type U0MaxU2 = <<A as Max<B>>::Output as Same<U2>>::Output;

    assert_eq!(<U0MaxU2 as Unsigned>::to_u64(), <U2 as Unsigned>::to_u64());
}
#[test]
#[allow(non_snake_case)]
fn test_0_Gcd_2() {
    type A = UTerm;
    type B = UInt<UInt<UTerm, B1>, B0>;
    type U2 = UInt<UInt<UTerm, B1>, B0>;

    #[allow(non_camel_case_types)]
    type U0GcdU2 = <<A as Gcd<B>>::Output as Same<U2>>::Output;

    assert_eq!(<U0GcdU2 as Unsigned>::to_u64(), <U2 as Unsigned>::to_u64());
}
#[test]
#[allow(non_snake_case)]
fn test_0_Div_2() {
    type A = UTerm;
    type B = UInt<UInt<UTerm, B1>, B0>;
    type U0 = UTerm;

    #[allow(non_camel_case_types)]
    type U0DivU2 = <<A as Div<B>>::Output as Same<U0>>::Output;

    assert_eq!(<U0DivU2 as Unsigned>::to_u64(), <U0 as Unsigned>::to_u64());
}
#[test]
#[allow(non_snake_case)]
fn test_0_Rem_2() {
    type A = UTerm;
    type B = UInt<UInt<UTerm, B1>, B0>;
    type U0 = UTerm;

    #[allow(non_camel_case_types)]
    type U0RemU2 = <<A as Rem<B>>::Output as Same<U0>>::Output;

    assert_eq!(<U0RemU2 as Unsigned>::to_u64(), <U0 as Unsigned>::to_u64());
}
#[test]
#[allow(non_snake_case)]
fn test_0_PartialDiv_2() {
    type A = UTerm;
    type B = UInt<UInt<UTerm, B1>, B0>;
    type U0 = UTerm;

    #[allow(non_camel_case_types)]
    type U0PartialDivU2 = <<A as PartialDiv<B>>::Output as Same<U0>>::Output;

    assert_eq!(<U0PartialDivU2 as Unsigned>::to_u64(), <U0 as Unsigned>::to_u64());
}
#[test]
#[allow(non_snake_case)]
fn test_0_Cmp_2() {
    type A = UTerm;
    type B = UInt<UInt<UTerm, B1>, B0>;

    #[allow(non_camel_case_types)]
    type U0CmpU2 = <A as Cmp<B>>::Output;
    assert_eq!(<U0CmpU2 as Ord>::to_ordering(), Ordering::Less);
}
#[test]
#[allow(non_snake_case)]
fn test_0_BitAnd_3() {
    type A = UTerm;
    type B = UInt<UInt<UTerm, B1>, B1>;
    type U0 = UTerm;

    #[allow(non_camel_case_types)]
    type U0BitAndU3 = <<A as BitAnd<B>>::Output as Same<U0>>::Output;

    assert_eq!(<U0BitAndU3 as Unsigned>::to_u64(), <U0 as Unsigned>::to_u64());
}
#[test]
#[allow(non_snake_case)]
fn test_0_BitOr_3() {
    type A = UTerm;
    type B = UInt<UInt<UTerm, B1>, B1>;
    type U3 = UInt<UInt<UTerm, B1>, B1>;

    #[allow(non_camel_case_types)]
    type U0BitOrU3 = <<A as BitOr<B>>::Output as Same<U3>>::Output;

    assert_eq!(<U0BitOrU3 as Unsigned>::to_u64(), <U3 as Unsigned>::to_u64());
}
#[test]
#[allow(non_snake_case)]
fn test_0_BitXor_3() {
    type A = UTerm;
    type B = UInt<UInt<UTerm, B1>, B1>;
    type U3 = UInt<UInt<UTerm, B1>, B1>;

    #[allow(non_camel_case_types)]
    type U0BitXorU3 = <<A as BitXor<B>>::Output as Same<U3>>::Output;

    assert_eq!(<U0BitXorU3 as Unsigned>::to_u64(), <U3 as Unsigned>::to_u64());
}
#[test]
#[allow(non_snake_case)]
fn test_0_Shl_3() {
    type A = UTerm;
    type B = UInt<UInt<UTerm, B1>, B1>;
    type U0 = UTerm;

    #[allow(non_camel_case_types)]
    type U0ShlU3 = <<A as Shl<B>>::Output as Same<U0>>::Output;

    assert_eq!(<U0ShlU3 as Unsigned>::to_u64(), <U0 as Unsigned>::to_u64());
}
#[test]
#[allow(non_snake_case)]
fn test_0_Shr_3() {
    type A = UTerm;
    type B = UInt<UInt<UTerm, B1>, B1>;
    type U0 = UTerm;

    #[allow(non_camel_case_types)]
    type U0ShrU3 = <<A as Shr<B>>::Output as Same<U0>>::Output;

    assert_eq!(<U0ShrU3 as Unsigned>::to_u64(), <U0 as Unsigned>::to_u64());
}
#[test]
#[allow(non_snake_case)]
fn test_0_Add_3() {
    type A = UTerm;
    type B = UInt<UInt<UTerm, B1>, B1>;
    type U3 = UInt<UInt<UTerm, B1>, B1>;

    #[allow(non_camel_case_types)]
    type U0AddU3 = <<A as Add<B>>::Output as Same<U3>>::Output;

    assert_eq!(<U0AddU3 as Unsigned>::to_u64(), <U3 as Unsigned>::to_u64());
}
#[test]
#[allow(non_snake_case)]
fn test_0_Mul_3() {
    type A = UTerm;
    type B = UInt<UInt<UTerm, B1>, B1>;
    type U0 = UTerm;

    #[allow(non_camel_case_types)]
    type U0MulU3 = <<A as Mul<B>>::Output as Same<U0>>::Output;

    assert_eq!(<U0MulU3 as Unsigned>::to_u64(), <U0 as Unsigned>::to_u64());
}
#[test]
#[allow(non_snake_case)]
fn test_0_Pow_3() {
    type A = UTerm;
    type B = UInt<UInt<UTerm, B1>, B1>;
    type U0 = UTerm;

    #[allow(non_camel_case_types)]
    type U0PowU3 = <<A as Pow<B>>::Output as Same<U0>>::Output;

    assert_eq!(<U0PowU3 as Unsigned>::to_u64(), <U0 as Unsigned>::to_u64());
}
#[test]
#[allow(non_snake_case)]
fn test_0_Min_3() {
    type A = UTerm;
    type B = UInt<UInt<UTerm, B1>, B1>;
    type U0 = UTerm;

    #[allow(non_camel_case_types)]
    type U0MinU3 = <<A as Min<B>>::Output as Same<U0>>::Output;

    assert_eq!(<U0MinU3 as Unsigned>::to_u64(), <U0 as Unsigned>::to_u64());
}
#[test]
#[allow(non_snake_case)]
fn test_0_Max_3() {
    type A = UTerm;
    type B = UInt<UInt<UTerm, B1>, B1>;
    type U3 = UInt<UInt<UTerm, B1>, B1>;

    #[allow(non_camel_case_types)]
    type U0MaxU3 = <<A as Max<B>>::Output as Same<U3>>::Output;

    assert_eq!(<U0MaxU3 as Unsigned>::to_u64(), <U3 as Unsigned>::to_u64());
}
#[test]
#[allow(non_snake_case)]
fn test_0_Gcd_3() {
    type A = UTerm;
    type B = UInt<UInt<UTerm, B1>, B1>;
    type U3 = UInt<UInt<UTerm, B1>, B1>;

    #[allow(non_camel_case_types)]
    type U0GcdU3 = <<A as Gcd<B>>::Output as Same<U3>>::Output;

    assert_eq!(<U0GcdU3 as Unsigned>::to_u64(), <U3 as Unsigned>::to_u64());
}
#[test]
#[allow(non_snake_case)]
fn test_0_Div_3() {
    type A = UTerm;
    type B = UInt<UInt<UTerm, B1>, B1>;
    type U0 = UTerm;

    #[allow(non_camel_case_types)]
    type U0DivU3 = <<A as Div<B>>::Output as Same<U0>>::Output;

    assert_eq!(<U0DivU3 as Unsigned>::to_u64(), <U0 as Unsigned>::to_u64());
}
#[test]
#[allow(non_snake_case)]
fn test_0_Rem_3() {
    type A = UTerm;
    type B = UInt<UInt<UTerm, B1>, B1>;
    type U0 = UTerm;

    #[allow(non_camel_case_types)]
    type U0RemU3 = <<A as Rem<B>>::Output as Same<U0>>::Output;

    assert_eq!(<U0RemU3 as Unsigned>::to_u64(), <U0 as Unsigned>::to_u64());
}
#[test]
#[allow(non_snake_case)]
fn test_0_PartialDiv_3() {
    type A = UTerm;
    type B = UInt<UInt<UTerm, B1>, B1>;
    type U0 = UTerm;

    #[allow(non_camel_case_types)]
    type U0PartialDivU3 = <<A as PartialDiv<B>>::Output as Same<U0>>::Output;

    assert_eq!(<U0PartialDivU3 as Unsigned>::to_u64(), <U0 as Unsigned>::to_u64());
}
#[test]
#[allow(non_snake_case)]
fn test_0_Cmp_3() {
    type A = UTerm;
    type B = UInt<UInt<UTerm, B1>, B1>;

    #[allow(non_camel_case_types)]
    type U0CmpU3 = <A as Cmp<B>>::Output;
    assert_eq!(<U0CmpU3 as Ord>::to_ordering(), Ordering::Less);
}
#[test]
#[allow(non_snake_case)]
fn test_0_BitAnd_4() {
    type A = UTerm;
    type B = UInt<UInt<UInt<UTerm, B1>, B0>, B0>;
    type U0 = UTerm;

    #[allow(non_camel_case_types)]
    type U0BitAndU4 = <<A as BitAnd<B>>::Output as Same<U0>>::Output;

    assert_eq!(<U0BitAndU4 as Unsigned>::to_u64(), <U0 as Unsigned>::to_u64());
}
#[test]
#[allow(non_snake_case)]
fn test_0_BitOr_4() {
    type A = UTerm;
    type B = UInt<UInt<UInt<UTerm, B1>, B0>, B0>;
    type U4 = UInt<UInt<UInt<UTerm, B1>, B0>, B0>;

    #[allow(non_camel_case_types)]
    type U0BitOrU4 = <<A as BitOr<B>>::Output as Same<U4>>::Output;

    assert_eq!(<U0BitOrU4 as Unsigned>::to_u64(), <U4 as Unsigned>::to_u64());
}
#[test]
#[allow(non_snake_case)]
fn test_0_BitXor_4() {
    type A = UTerm;
    type B = UInt<UInt<UInt<UTerm, B1>, B0>, B0>;
    type U4 = UInt<UInt<UInt<UTerm, B1>, B0>, B0>;

    #[allow(non_camel_case_types)]
    type U0BitXorU4 = <<A as BitXor<B>>::Output as Same<U4>>::Output;

    assert_eq!(<U0BitXorU4 as Unsigned>::to_u64(), <U4 as Unsigned>::to_u64());
}
#[test]
#[allow(non_snake_case)]
fn test_0_Shl_4() {
    type A = UTerm;
    type B = UInt<UInt<UInt<UTerm, B1>, B0>, B0>;
    type U0 = UTerm;

    #[allow(non_camel_case_types)]
    type U0ShlU4 = <<A as Shl<B>>::Output as Same<U0>>::Output;

    assert_eq!(<U0ShlU4 as Unsigned>::to_u64(), <U0 as Unsigned>::to_u64());
}
#[test]
#[allow(non_snake_case)]
fn test_0_Shr_4() {
    type A = UTerm;
    type B = UInt<UInt<UInt<UTerm, B1>, B0>, B0>;
    type U0 = UTerm;

    #[allow(non_camel_case_types)]
    type U0ShrU4 = <<A as Shr<B>>::Output as Same<U0>>::Output;

    assert_eq!(<U0ShrU4 as Unsigned>::to_u64(), <U0 as Unsigned>::to_u64());
}
#[test]
#[allow(non_snake_case)]
fn test_0_Add_4() {
    type A = UTerm;
    type B = UInt<UInt<UInt<UTerm, B1>, B0>, B0>;
    type U4 = UInt<UInt<UInt<UTerm, B1>, B0>, B0>;

    #[allow(non_camel_case_types)]
    type U0AddU4 = <<A as Add<B>>::Output as Same<U4>>::Output;

    assert_eq!(<U0AddU4 as Unsigned>::to_u64(), <U4 as Unsigned>::to_u64());
}
#[test]
#[allow(non_snake_case)]
fn test_0_Mul_4() {
    type A = UTerm;
    type B = UInt<UInt<UInt<UTerm, B1>, B0>, B0>;
    type U0 = UTerm;

    #[allow(non_camel_case_types)]
    type U0MulU4 = <<A as Mul<B>>::Output as Same<U0>>::Output;

    assert_eq!(<U0MulU4 as Unsigned>::to_u64(), <U0 as Unsigned>::to_u64());
}
#[test]
#[allow(non_snake_case)]
fn test_0_Pow_4() {
    type A = UTerm;
    type B = UInt<UInt<UInt<UTerm, B1>, B0>, B0>;
    type U0 = UTerm;

    #[allow(non_camel_case_types)]
    type U0PowU4 = <<A as Pow<B>>::Output as Same<U0>>::Output;

    assert_eq!(<U0PowU4 as Unsigned>::to_u64(), <U0 as Unsigned>::to_u64());
}
#[test]
#[allow(non_snake_case)]
fn test_0_Min_4() {
    type A = UTerm;
    type B = UInt<UInt<UInt<UTerm, B1>, B0>, B0>;
    type U0 = UTerm;

    #[allow(non_camel_case_types)]
    type U0MinU4 = <<A as Min<B>>::Output as Same<U0>>::Output;

    assert_eq!(<U0MinU4 as Unsigned>::to_u64(), <U0 as Unsigned>::to_u64());
}
#[test]
#[allow(non_snake_case)]
fn test_0_Max_4() {
    type A = UTerm;
    type B = UInt<UInt<UInt<UTerm, B1>, B0>, B0>;
    type U4 = UInt<UInt<UInt<UTerm, B1>, B0>, B0>;

    #[allow(non_camel_case_types)]
    type U0MaxU4 = <<A as Max<B>>::Output as Same<U4>>::Output;

    assert_eq!(<U0MaxU4 as Unsigned>::to_u64(), <U4 as Unsigned>::to_u64());
}
#[test]
#[allow(non_snake_case)]
fn test_0_Gcd_4() {
    type A = UTerm;
    type B = UInt<UInt<UInt<UTerm, B1>, B0>, B0>;
    type U4 = UInt<UInt<UInt<UTerm, B1>, B0>, B0>;

    #[allow(non_camel_case_types)]
    type U0GcdU4 = <<A as Gcd<B>>::Output as Same<U4>>::Output;

    assert_eq!(<U0GcdU4 as Unsigned>::to_u64(), <U4 as Unsigned>::to_u64());
}
#[test]
#[allow(non_snake_case)]
fn test_0_Div_4() {
    type A = UTerm;
    type B = UInt<UInt<UInt<UTerm, B1>, B0>, B0>;
    type U0 = UTerm;

    #[allow(non_camel_case_types)]
    type U0DivU4 = <<A as Div<B>>::Output as Same<U0>>::Output;

    assert_eq!(<U0DivU4 as Unsigned>::to_u64(), <U0 as Unsigned>::to_u64());
}
#[test]
#[allow(non_snake_case)]
fn test_0_Rem_4() {
    type A = UTerm;
    type B = UInt<UInt<UInt<UTerm, B1>, B0>, B0>;
    type U0 = UTerm;

    #[allow(non_camel_case_types)]
    type U0RemU4 = <<A as Rem<B>>::Output as Same<U0>>::Output;

    assert_eq!(<U0RemU4 as Unsigned>::to_u64(), <U0 as Unsigned>::to_u64());
}
#[test]
#[allow(non_snake_case)]
fn test_0_PartialDiv_4() {
    type A = UTerm;
    type B = UInt<UInt<UInt<UTerm, B1>, B0>, B0>;
    type U0 = UTerm;

    #[allow(non_camel_case_types)]
    type U0PartialDivU4 = <<A as PartialDiv<B>>::Output as Same<U0>>::Output;

    assert_eq!(<U0PartialDivU4 as Unsigned>::to_u64(), <U0 as Unsigned>::to_u64());
}
#[test]
#[allow(non_snake_case)]
fn test_0_Cmp_4() {
    type A = UTerm;
    type B = UInt<UInt<UInt<UTerm, B1>, B0>, B0>;

    #[allow(non_camel_case_types)]
    type U0CmpU4 = <A as Cmp<B>>::Output;
    assert_eq!(<U0CmpU4 as Ord>::to_ordering(), Ordering::Less);
}
#[test]
#[allow(non_snake_case)]
fn test_0_BitAnd_5() {
    type A = UTerm;
    type B = UInt<UInt<UInt<UTerm, B1>, B0>, B1>;
    type U0 = UTerm;

    #[allow(non_camel_case_types)]
    type U0BitAndU5 = <<A as BitAnd<B>>::Output as Same<U0>>::Output;

    assert_eq!(<U0BitAndU5 as Unsigned>::to_u64(), <U0 as Unsigned>::to_u64());
}
#[test]
#[allow(non_snake_case)]
fn test_0_BitOr_5() {
    type A = UTerm;
    type B = UInt<UInt<UInt<UTerm, B1>, B0>, B1>;
    type U5 = UInt<UInt<UInt<UTerm, B1>, B0>, B1>;

    #[allow(non_camel_case_types)]
    type U0BitOrU5 = <<A as BitOr<B>>::Output as Same<U5>>::Output;

    assert_eq!(<U0BitOrU5 as Unsigned>::to_u64(), <U5 as Unsigned>::to_u64());
}
#[test]
#[allow(non_snake_case)]
fn test_0_BitXor_5() {
    type A = UTerm;
    type B = UInt<UInt<UInt<UTerm, B1>, B0>, B1>;
    type U5 = UInt<UInt<UInt<UTerm, B1>, B0>, B1>;

    #[allow(non_camel_case_types)]
    type U0BitXorU5 = <<A as BitXor<B>>::Output as Same<U5>>::Output;

    assert_eq!(<U0BitXorU5 as Unsigned>::to_u64(), <U5 as Unsigned>::to_u64());
}
#[test]
#[allow(non_snake_case)]
fn test_0_Shl_5() {
    type A = UTerm;
    type B = UInt<UInt<UInt<UTerm, B1>, B0>, B1>;
    type U0 = UTerm;

    #[allow(non_camel_case_types)]
    type U0ShlU5 = <<A as Shl<B>>::Output as Same<U0>>::Output;

    assert_eq!(<U0ShlU5 as Unsigned>::to_u64(), <U0 as Unsigned>::to_u64());
}
#[test]
#[allow(non_snake_case)]
fn test_0_Shr_5() {
    type A = UTerm;
    type B = UInt<UInt<UInt<UTerm, B1>, B0>, B1>;
    type U0 = UTerm;

    #[allow(non_camel_case_types)]
    type U0ShrU5 = <<A as Shr<B>>::Output as Same<U0>>::Output;

    assert_eq!(<U0ShrU5 as Unsigned>::to_u64(), <U0 as Unsigned>::to_u64());
}
#[test]
#[allow(non_snake_case)]
fn test_0_Add_5() {
    type A = UTerm;
    type B = UInt<UInt<UInt<UTerm, B1>, B0>, B1>;
    type U5 = UInt<UInt<UInt<UTerm, B1>, B0>, B1>;

    #[allow(non_camel_case_types)]
    type U0AddU5 = <<A as Add<B>>::Output as Same<U5>>::Output;

    assert_eq!(<U0AddU5 as Unsigned>::to_u64(), <U5 as Unsigned>::to_u64());
}
#[test]
#[allow(non_snake_case)]
fn test_0_Mul_5() {
    type A = UTerm;
    type B = UInt<UInt<UInt<UTerm, B1>, B0>, B1>;
    type U0 = UTerm;

    #[allow(non_camel_case_types)]
    type U0MulU5 = <<A as Mul<B>>::Output as Same<U0>>::Output;

    assert_eq!(<U0MulU5 as Unsigned>::to_u64(), <U0 as Unsigned>::to_u64());
}
#[test]
#[allow(non_snake_case)]
fn test_0_Pow_5() {
    type A = UTerm;
    type B = UInt<UInt<UInt<UTerm, B1>, B0>, B1>;
    type U0 = UTerm;

    #[allow(non_camel_case_types)]
    type U0PowU5 = <<A as Pow<B>>::Output as Same<U0>>::Output;

    assert_eq!(<U0PowU5 as Unsigned>::to_u64(), <U0 as Unsigned>::to_u64());
}
#[test]
#[allow(non_snake_case)]
fn test_0_Min_5() {
    type A = UTerm;
    type B = UInt<UInt<UInt<UTerm, B1>, B0>, B1>;
    type U0 = UTerm;

    #[allow(non_camel_case_types)]
    type U0MinU5 = <<A as Min<B>>::Output as Same<U0>>::Output;

    assert_eq!(<U0MinU5 as Unsigned>::to_u64(), <U0 as Unsigned>::to_u64());
}
#[test]
#[allow(non_snake_case)]
fn test_0_Max_5() {
    type A = UTerm;
    type B = UInt<UInt<UInt<UTerm, B1>, B0>, B1>;
    type U5 = UInt<UInt<UInt<UTerm, B1>, B0>, B1>;

    #[allow(non_camel_case_types)]
    type U0MaxU5 = <<A as Max<B>>::Output as Same<U5>>::Output;

    assert_eq!(<U0MaxU5 as Unsigned>::to_u64(), <U5 as Unsigned>::to_u64());
}
#[test]
#[allow(non_snake_case)]
fn test_0_Gcd_5() {
    type A = UTerm;
    type B = UInt<UInt<UInt<UTerm, B1>, B0>, B1>;
    type U5 = UInt<UInt<UInt<UTerm, B1>, B0>, B1>;

    #[allow(non_camel_case_types)]
    type U0GcdU5 = <<A as Gcd<B>>::Output as Same<U5>>::Output;

    assert_eq!(<U0GcdU5 as Unsigned>::to_u64(), <U5 as Unsigned>::to_u64());
}
#[test]
#[allow(non_snake_case)]
fn test_0_Div_5() {
    type A = UTerm;
    type B = UInt<UInt<UInt<UTerm, B1>, B0>, B1>;
    type U0 = UTerm;

    #[allow(non_camel_case_types)]
    type U0DivU5 = <<A as Div<B>>::Output as Same<U0>>::Output;

    assert_eq!(<U0DivU5 as Unsigned>::to_u64(), <U0 as Unsigned>::to_u64());
}
#[test]
#[allow(non_snake_case)]
fn test_0_Rem_5() {
    type A = UTerm;
    type B = UInt<UInt<UInt<UTerm, B1>, B0>, B1>;
    type U0 = UTerm;

    #[allow(non_camel_case_types)]
    type U0RemU5 = <<A as Rem<B>>::Output as Same<U0>>::Output;

    assert_eq!(<U0RemU5 as Unsigned>::to_u64(), <U0 as Unsigned>::to_u64());
}
#[test]
#[allow(non_snake_case)]
fn test_0_PartialDiv_5() {
    type A = UTerm;
    type B = UInt<UInt<UInt<UTerm, B1>, B0>, B1>;
    type U0 = UTerm;

    #[allow(non_camel_case_types)]
    type U0PartialDivU5 = <<A as PartialDiv<B>>::Output as Same<U0>>::Output;

    assert_eq!(<U0PartialDivU5 as Unsigned>::to_u64(), <U0 as Unsigned>::to_u64());
}
#[test]
#[allow(non_snake_case)]
fn test_0_Cmp_5() {
    type A = UTerm;
    type B = UInt<UInt<UInt<UTerm, B1>, B0>, B1>;

    #[allow(non_camel_case_types)]
    type U0CmpU5 = <A as Cmp<B>>::Output;
    assert_eq!(<U0CmpU5 as Ord>::to_ordering(), Ordering::Less);
}
#[test]
#[allow(non_snake_case)]
fn test_1_BitAnd_0() {
    type A = UInt<UTerm, B1>;
    type B = UTerm;
    type U0 = UTerm;

    #[allow(non_camel_case_types)]
    type U1BitAndU0 = <<A as BitAnd<B>>::Output as Same<U0>>::Output;

    assert_eq!(<U1BitAndU0 as Unsigned>::to_u64(), <U0 as Unsigned>::to_u64());
}
#[test]
#[allow(non_snake_case)]
fn test_1_BitOr_0() {
    type A = UInt<UTerm, B1>;
    type B = UTerm;
    type U1 = UInt<UTerm, B1>;

    #[allow(non_camel_case_types)]
    type U1BitOrU0 = <<A as BitOr<B>>::Output as Same<U1>>::Output;

    assert_eq!(<U1BitOrU0 as Unsigned>::to_u64(), <U1 as Unsigned>::to_u64());
}
#[test]
#[allow(non_snake_case)]
fn test_1_BitXor_0() {
    type A = UInt<UTerm, B1>;
    type B = UTerm;
    type U1 = UInt<UTerm, B1>;

    #[allow(non_camel_case_types)]
    type U1BitXorU0 = <<A as BitXor<B>>::Output as Same<U1>>::Output;

    assert_eq!(<U1BitXorU0 as Unsigned>::to_u64(), <U1 as Unsigned>::to_u64());
}
#[test]
#[allow(non_snake_case)]
fn test_1_Shl_0() {
    type A = UInt<UTerm, B1>;
    type B = UTerm;
    type U1 = UInt<UTerm, B1>;

    #[allow(non_camel_case_types)]
    type U1ShlU0 = <<A as Shl<B>>::Output as Same<U1>>::Output;

    assert_eq!(<U1ShlU0 as Unsigned>::to_u64(), <U1 as Unsigned>::to_u64());
}
#[test]
#[allow(non_snake_case)]
fn test_1_Shr_0() {
    type A = UInt<UTerm, B1>;
    type B = UTerm;
    type U1 = UInt<UTerm, B1>;

    #[allow(non_camel_case_types)]
    type U1ShrU0 = <<A as Shr<B>>::Output as Same<U1>>::Output;

    assert_eq!(<U1ShrU0 as Unsigned>::to_u64(), <U1 as Unsigned>::to_u64());
}
#[test]
#[allow(non_snake_case)]
fn test_1_Add_0() {
    type A = UInt<UTerm, B1>;
    type B = UTerm;
    type U1 = UInt<UTerm, B1>;

    #[allow(non_camel_case_types)]
    type U1AddU0 = <<A as Add<B>>::Output as Same<U1>>::Output;

    assert_eq!(<U1AddU0 as Unsigned>::to_u64(), <U1 as Unsigned>::to_u64());
}
#[test]
#[allow(non_snake_case)]
fn test_1_Mul_0() {
    type A = UInt<UTerm, B1>;
    type B = UTerm;
    type U0 = UTerm;

    #[allow(non_camel_case_types)]
    type U1MulU0 = <<A as Mul<B>>::Output as Same<U0>>::Output;

    assert_eq!(<U1MulU0 as Unsigned>::to_u64(), <U0 as Unsigned>::to_u64());
}
#[test]
#[allow(non_snake_case)]
fn test_1_Pow_0() {
    type A = UInt<UTerm, B1>;
    type B = UTerm;
    type U1 = UInt<UTerm, B1>;

    #[allow(non_camel_case_types)]
    type U1PowU0 = <<A as Pow<B>>::Output as Same<U1>>::Output;

    assert_eq!(<U1PowU0 as Unsigned>::to_u64(), <U1 as Unsigned>::to_u64());
}
#[test]
#[allow(non_snake_case)]
fn test_1_Min_0() {
    type A = UInt<UTerm, B1>;
    type B = UTerm;
    type U0 = UTerm;

    #[allow(non_camel_case_types)]
    type U1MinU0 = <<A as Min<B>>::Output as Same<U0>>::Output;

    assert_eq!(<U1MinU0 as Unsigned>::to_u64(), <U0 as Unsigned>::to_u64());
}
#[test]
#[allow(non_snake_case)]
fn test_1_Max_0() {
    type A = UInt<UTerm, B1>;
    type B = UTerm;
    type U1 = UInt<UTerm, B1>;

    #[allow(non_camel_case_types)]
    type U1MaxU0 = <<A as Max<B>>::Output as Same<U1>>::Output;

    assert_eq!(<U1MaxU0 as Unsigned>::to_u64(), <U1 as Unsigned>::to_u64());
}
#[test]
#[allow(non_snake_case)]
fn test_1_Gcd_0() {
    type A = UInt<UTerm, B1>;
    type B = UTerm;
    type U1 = UInt<UTerm, B1>;

    #[allow(non_camel_case_types)]
    type U1GcdU0 = <<A as Gcd<B>>::Output as Same<U1>>::Output;

    assert_eq!(<U1GcdU0 as Unsigned>::to_u64(), <U1 as Unsigned>::to_u64());
}
#[test]
#[allow(non_snake_case)]
fn test_1_Sub_0() {
    type A = UInt<UTerm, B1>;
    type B = UTerm;
    type U1 = UInt<UTerm, B1>;

    #[allow(non_camel_case_types)]
    type U1SubU0 = <<A as Sub<B>>::Output as Same<U1>>::Output;

    assert_eq!(<U1SubU0 as Unsigned>::to_u64(), <U1 as Unsigned>::to_u64());
}
#[test]
#[allow(non_snake_case)]
fn test_1_Cmp_0() {
    type A = UInt<UTerm, B1>;
    type B = UTerm;

    #[allow(non_camel_case_types)]
    type U1CmpU0 = <A as Cmp<B>>::Output;
    assert_eq!(<U1CmpU0 as Ord>::to_ordering(), Ordering::Greater);
}
#[test]
#[allow(non_snake_case)]
fn test_1_BitAnd_1() {
    type A = UInt<UTerm, B1>;
    type B = UInt<UTerm, B1>;
    type U1 = UInt<UTerm, B1>;

    #[allow(non_camel_case_types)]
    type U1BitAndU1 = <<A as BitAnd<B>>::Output as Same<U1>>::Output;

    assert_eq!(<U1BitAndU1 as Unsigned>::to_u64(), <U1 as Unsigned>::to_u64());
}
#[test]
#[allow(non_snake_case)]
fn test_1_BitOr_1() {
    type A = UInt<UTerm, B1>;
    type B = UInt<UTerm, B1>;
    type U1 = UInt<UTerm, B1>;

    #[allow(non_camel_case_types)]
    type U1BitOrU1 = <<A as BitOr<B>>::Output as Same<U1>>::Output;

    assert_eq!(<U1BitOrU1 as Unsigned>::to_u64(), <U1 as Unsigned>::to_u64());
}
#[test]
#[allow(non_snake_case)]
fn test_1_BitXor_1() {
    type A = UInt<UTerm, B1>;
    type B = UInt<UTerm, B1>;
    type U0 = UTerm;

    #[allow(non_camel_case_types)]
    type U1BitXorU1 = <<A as BitXor<B>>::Output as Same<U0>>::Output;

    assert_eq!(<U1BitXorU1 as Unsigned>::to_u64(), <U0 as Unsigned>::to_u64());
}
#[test]
#[allow(non_snake_case)]
fn test_1_Shl_1() {
    type A = UInt<UTerm, B1>;
    type B = UInt<UTerm, B1>;
    type U2 = UInt<UInt<UTerm, B1>, B0>;

    #[allow(non_camel_case_types)]
    type U1ShlU1 = <<A as Shl<B>>::Output as Same<U2>>::Output;

    assert_eq!(<U1ShlU1 as Unsigned>::to_u64(), <U2 as Unsigned>::to_u64());
}
#[test]
#[allow(non_snake_case)]
fn test_1_Shr_1() {
    type A = UInt<UTerm, B1>;
    type B = UInt<UTerm, B1>;
    type U0 = UTerm;

    #[allow(non_camel_case_types)]
    type U1ShrU1 = <<A as Shr<B>>::Output as Same<U0>>::Output;

    assert_eq!(<U1ShrU1 as Unsigned>::to_u64(), <U0 as Unsigned>::to_u64());
}
#[test]
#[allow(non_snake_case)]
fn test_1_Add_1() {
    type A = UInt<UTerm, B1>;
    type B = UInt<UTerm, B1>;
    type U2 = UInt<UInt<UTerm, B1>, B0>;

    #[allow(non_camel_case_types)]
    type U1AddU1 = <<A as Add<B>>::Output as Same<U2>>::Output;

    assert_eq!(<U1AddU1 as Unsigned>::to_u64(), <U2 as Unsigned>::to_u64());
}
#[test]
#[allow(non_snake_case)]
fn test_1_Mul_1() {
    type A = UInt<UTerm, B1>;
    type B = UInt<UTerm, B1>;
    type U1 = UInt<UTerm, B1>;

    #[allow(non_camel_case_types)]
    type U1MulU1 = <<A as Mul<B>>::Output as Same<U1>>::Output;

    assert_eq!(<U1MulU1 as Unsigned>::to_u64(), <U1 as Unsigned>::to_u64());
}
#[test]
#[allow(non_snake_case)]
fn test_1_Pow_1() {
    type A = UInt<UTerm, B1>;
    type B = UInt<UTerm, B1>;
    type U1 = UInt<UTerm, B1>;

    #[allow(non_camel_case_types)]
    type U1PowU1 = <<A as Pow<B>>::Output as Same<U1>>::Output;

    assert_eq!(<U1PowU1 as Unsigned>::to_u64(), <U1 as Unsigned>::to_u64());
}
#[test]
#[allow(non_snake_case)]
fn test_1_Min_1() {
    type A = UInt<UTerm, B1>;
    type B = UInt<UTerm, B1>;
    type U1 = UInt<UTerm, B1>;

    #[allow(non_camel_case_types)]
    type U1MinU1 = <<A as Min<B>>::Output as Same<U1>>::Output;

    assert_eq!(<U1MinU1 as Unsigned>::to_u64(), <U1 as Unsigned>::to_u64());
}
#[test]
#[allow(non_snake_case)]
fn test_1_Max_1() {
    type A = UInt<UTerm, B1>;
    type B = UInt<UTerm, B1>;
    type U1 = UInt<UTerm, B1>;

    #[allow(non_camel_case_types)]
    type U1MaxU1 = <<A as Max<B>>::Output as Same<U1>>::Output;

    assert_eq!(<U1MaxU1 as Unsigned>::to_u64(), <U1 as Unsigned>::to_u64());
}
#[test]
#[allow(non_snake_case)]
fn test_1_Gcd_1() {
    type A = UInt<UTerm, B1>;
    type B = UInt<UTerm, B1>;
    type U1 = UInt<UTerm, B1>;

    #[allow(non_camel_case_types)]
    type U1GcdU1 = <<A as Gcd<B>>::Output as Same<U1>>::Output;

    assert_eq!(<U1GcdU1 as Unsigned>::to_u64(), <U1 as Unsigned>::to_u64());
}
#[test]
#[allow(non_snake_case)]
fn test_1_Sub_1() {
    type A = UInt<UTerm, B1>;
    type B = UInt<UTerm, B1>;
    type U0 = UTerm;

    #[allow(non_camel_case_types)]
    type U1SubU1 = <<A as Sub<B>>::Output as Same<U0>>::Output;

    assert_eq!(<U1SubU1 as Unsigned>::to_u64(), <U0 as Unsigned>::to_u64());
}
#[test]
#[allow(non_snake_case)]
fn test_1_Div_1() {
    type A = UInt<UTerm, B1>;
    type B = UInt<UTerm, B1>;
    type U1 = UInt<UTerm, B1>;

    #[allow(non_camel_case_types)]
    type U1DivU1 = <<A as Div<B>>::Output as Same<U1>>::Output;

    assert_eq!(<U1DivU1 as Unsigned>::to_u64(), <U1 as Unsigned>::to_u64());
}
#[test]
#[allow(non_snake_case)]
fn test_1_Rem_1() {
    type A = UInt<UTerm, B1>;
    type B = UInt<UTerm, B1>;
    type U0 = UTerm;

    #[allow(non_camel_case_types)]
    type U1RemU1 = <<A as Rem<B>>::Output as Same<U0>>::Output;

    assert_eq!(<U1RemU1 as Unsigned>::to_u64(), <U0 as Unsigned>::to_u64());
}
#[test]
#[allow(non_snake_case)]
fn test_1_PartialDiv_1() {
    type A = UInt<UTerm, B1>;
    type B = UInt<UTerm, B1>;
    type U1 = UInt<UTerm, B1>;

    #[allow(non_camel_case_types)]
    type U1PartialDivU1 = <<A as PartialDiv<B>>::Output as Same<U1>>::Output;

    assert_eq!(<U1PartialDivU1 as Unsigned>::to_u64(), <U1 as Unsigned>::to_u64());
}
#[test]
#[allow(non_snake_case)]
fn test_1_Cmp_1() {
    type A = UInt<UTerm, B1>;
    type B = UInt<UTerm, B1>;

    #[allow(non_camel_case_types)]
    type U1CmpU1 = <A as Cmp<B>>::Output;
    assert_eq!(<U1CmpU1 as Ord>::to_ordering(), Ordering::Equal);
}
#[test]
#[allow(non_snake_case)]
fn test_1_BitAnd_2() {
    type A = UInt<UTerm, B1>;
    type B = UInt<UInt<UTerm, B1>, B0>;
    type U0 = UTerm;

    #[allow(non_camel_case_types)]
    type U1BitAndU2 = <<A as BitAnd<B>>::Output as Same<U0>>::Output;

    assert_eq!(<U1BitAndU2 as Unsigned>::to_u64(), <U0 as Unsigned>::to_u64());
}
#[test]
#[allow(non_snake_case)]
fn test_1_BitOr_2() {
    type A = UInt<UTerm, B1>;
    type B = UInt<UInt<UTerm, B1>, B0>;
    type U3 = UInt<UInt<UTerm, B1>, B1>;

    #[allow(non_camel_case_types)]
    type U1BitOrU2 = <<A as BitOr<B>>::Output as Same<U3>>::Output;

    assert_eq!(<U1BitOrU2 as Unsigned>::to_u64(), <U3 as Unsigned>::to_u64());
}
#[test]
#[allow(non_snake_case)]
fn test_1_BitXor_2() {
    type A = UInt<UTerm, B1>;
    type B = UInt<UInt<UTerm, B1>, B0>;
    type U3 = UInt<UInt<UTerm, B1>, B1>;

    #[allow(non_camel_case_types)]
    type U1BitXorU2 = <<A as BitXor<B>>::Output as Same<U3>>::Output;

    assert_eq!(<U1BitXorU2 as Unsigned>::to_u64(), <U3 as Unsigned>::to_u64());
}
#[test]
#[allow(non_snake_case)]
fn test_1_Shl_2() {
    type A = UInt<UTerm, B1>;
    type B = UInt<UInt<UTerm, B1>, B0>;
    type U4 = UInt<UInt<UInt<UTerm, B1>, B0>, B0>;

    #[allow(non_camel_case_types)]
    type U1ShlU2 = <<A as Shl<B>>::Output as Same<U4>>::Output;

    assert_eq!(<U1ShlU2 as Unsigned>::to_u64(), <U4 as Unsigned>::to_u64());
}
#[test]
#[allow(non_snake_case)]
fn test_1_Shr_2() {
    type A = UInt<UTerm, B1>;
    type B = UInt<UInt<UTerm, B1>, B0>;
    type U0 = UTerm;

    #[allow(non_camel_case_types)]
    type U1ShrU2 = <<A as Shr<B>>::Output as Same<U0>>::Output;

    assert_eq!(<U1ShrU2 as Unsigned>::to_u64(), <U0 as Unsigned>::to_u64());
}
#[test]
#[allow(non_snake_case)]
fn test_1_Add_2() {
    type A = UInt<UTerm, B1>;
    type B = UInt<UInt<UTerm, B1>, B0>;
    type U3 = UInt<UInt<UTerm, B1>, B1>;

    #[allow(non_camel_case_types)]
    type U1AddU2 = <<A as Add<B>>::Output as Same<U3>>::Output;

    assert_eq!(<U1AddU2 as Unsigned>::to_u64(), <U3 as Unsigned>::to_u64());
}
#[test]
#[allow(non_snake_case)]
fn test_1_Mul_2() {
    type A = UInt<UTerm, B1>;
    type B = UInt<UInt<UTerm, B1>, B0>;
    type U2 = UInt<UInt<UTerm, B1>, B0>;

    #[allow(non_camel_case_types)]
    type U1MulU2 = <<A as Mul<B>>::Output as Same<U2>>::Output;

    assert_eq!(<U1MulU2 as Unsigned>::to_u64(), <U2 as Unsigned>::to_u64());
}
#[test]
#[allow(non_snake_case)]
fn test_1_Pow_2() {
    type A = UInt<UTerm, B1>;
    type B = UInt<UInt<UTerm, B1>, B0>;
    type U1 = UInt<UTerm, B1>;

    #[allow(non_camel_case_types)]
    type U1PowU2 = <<A as Pow<B>>::Output as Same<U1>>::Output;

    assert_eq!(<U1PowU2 as Unsigned>::to_u64(), <U1 as Unsigned>::to_u64());
}
#[test]
#[allow(non_snake_case)]
fn test_1_Min_2() {
    type A = UInt<UTerm, B1>;
    type B = UInt<UInt<UTerm, B1>, B0>;
    type U1 = UInt<UTerm, B1>;

    #[allow(non_camel_case_types)]
    type U1MinU2 = <<A as Min<B>>::Output as Same<U1>>::Output;

    assert_eq!(<U1MinU2 as Unsigned>::to_u64(), <U1 as Unsigned>::to_u64());
}
#[test]
#[allow(non_snake_case)]
fn test_1_Max_2() {
    type A = UInt<UTerm, B1>;
    type B = UInt<UInt<UTerm, B1>, B0>;
    type U2 = UInt<UInt<UTerm, B1>, B0>;

    #[allow(non_camel_case_types)]
    type U1MaxU2 = <<A as Max<B>>::Output as Same<U2>>::Output;

    assert_eq!(<U1MaxU2 as Unsigned>::to_u64(), <U2 as Unsigned>::to_u64());
}
#[test]
#[allow(non_snake_case)]
fn test_1_Gcd_2() {
    type A = UInt<UTerm, B1>;
    type B = UInt<UInt<UTerm, B1>, B0>;
    type U1 = UInt<UTerm, B1>;

    #[allow(non_camel_case_types)]
    type U1GcdU2 = <<A as Gcd<B>>::Output as Same<U1>>::Output;

    assert_eq!(<U1GcdU2 as Unsigned>::to_u64(), <U1 as Unsigned>::to_u64());
}
#[test]
#[allow(non_snake_case)]
fn test_1_Div_2() {
    type A = UInt<UTerm, B1>;
    type B = UInt<UInt<UTerm, B1>, B0>;
    type U0 = UTerm;

    #[allow(non_camel_case_types)]
    type U1DivU2 = <<A as Div<B>>::Output as Same<U0>>::Output;

    assert_eq!(<U1DivU2 as Unsigned>::to_u64(), <U0 as Unsigned>::to_u64());
}
#[test]
#[allow(non_snake_case)]
fn test_1_Rem_2() {
    type A = UInt<UTerm, B1>;
    type B = UInt<UInt<UTerm, B1>, B0>;
    type U1 = UInt<UTerm, B1>;

    #[allow(non_camel_case_types)]
    type U1RemU2 = <<A as Rem<B>>::Output as Same<U1>>::Output;

    assert_eq!(<U1RemU2 as Unsigned>::to_u64(), <U1 as Unsigned>::to_u64());
}
#[test]
#[allow(non_snake_case)]
fn test_1_Cmp_2() {
    type A = UInt<UTerm, B1>;
    type B = UInt<UInt<UTerm, B1>, B0>;

    #[allow(non_camel_case_types)]
    type U1CmpU2 = <A as Cmp<B>>::Output;
    assert_eq!(<U1CmpU2 as Ord>::to_ordering(), Ordering::Less);
}
#[test]
#[allow(non_snake_case)]
fn test_1_BitAnd_3() {
    type A = UInt<UTerm, B1>;
    type B = UInt<UInt<UTerm, B1>, B1>;
    type U1 = UInt<UTerm, B1>;

    #[allow(non_camel_case_types)]
    type U1BitAndU3 = <<A as BitAnd<B>>::Output as Same<U1>>::Output;

    assert_eq!(<U1BitAndU3 as Unsigned>::to_u64(), <U1 as Unsigned>::to_u64());
}
#[test]
#[allow(non_snake_case)]
fn test_1_BitOr_3() {
    type A = UInt<UTerm, B1>;
    type B = UInt<UInt<UTerm, B1>, B1>;
    type U3 = UInt<UInt<UTerm, B1>, B1>;

    #[allow(non_camel_case_types)]
    type U1BitOrU3 = <<A as BitOr<B>>::Output as Same<U3>>::Output;

    assert_eq!(<U1BitOrU3 as Unsigned>::to_u64(), <U3 as Unsigned>::to_u64());
}
#[test]
#[allow(non_snake_case)]
fn test_1_BitXor_3() {
    type A = UInt<UTerm, B1>;
    type B = UInt<UInt<UTerm, B1>, B1>;
    type U2 = UInt<UInt<UTerm, B1>, B0>;

    #[allow(non_camel_case_types)]
    type U1BitXorU3 = <<A as BitXor<B>>::Output as Same<U2>>::Output;

    assert_eq!(<U1BitXorU3 as Unsigned>::to_u64(), <U2 as Unsigned>::to_u64());
}
#[test]
#[allow(non_snake_case)]
fn test_1_Shl_3() {
    type A = UInt<UTerm, B1>;
    type B = UInt<UInt<UTerm, B1>, B1>;
    type U8 = UInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>, B0>;

    #[allow(non_camel_case_types)]
    type U1ShlU3 = <<A as Shl<B>>::Output as Same<U8>>::Output;

    assert_eq!(<U1ShlU3 as Unsigned>::to_u64(), <U8 as Unsigned>::to_u64());
}
#[test]
#[allow(non_snake_case)]
fn test_1_Shr_3() {
    type A = UInt<UTerm, B1>;
    type B = UInt<UInt<UTerm, B1>, B1>;
    type U0 = UTerm;

    #[allow(non_camel_case_types)]
    type U1ShrU3 = <<A as Shr<B>>::Output as Same<U0>>::Output;

    assert_eq!(<U1ShrU3 as Unsigned>::to_u64(), <U0 as Unsigned>::to_u64());
}
#[test]
#[allow(non_snake_case)]
fn test_1_Add_3() {
    type A = UInt<UTerm, B1>;
    type B = UInt<UInt<UTerm, B1>, B1>;
    type U4 = UInt<UInt<UInt<UTerm, B1>, B0>, B0>;

    #[allow(non_camel_case_types)]
    type U1AddU3 = <<A as Add<B>>::Output as Same<U4>>::Output;

    assert_eq!(<U1AddU3 as Unsigned>::to_u64(), <U4 as Unsigned>::to_u64());
}
#[test]
#[allow(non_snake_case)]
fn test_1_Mul_3() {
    type A = UInt<UTerm, B1>;
    type B = UInt<UInt<UTerm, B1>, B1>;
    type U3 = UInt<UInt<UTerm, B1>, B1>;

    #[allow(non_camel_case_types)]
    type U1MulU3 = <<A as Mul<B>>::Output as Same<U3>>::Output;

    assert_eq!(<U1MulU3 as Unsigned>::to_u64(), <U3 as Unsigned>::to_u64());
}
#[test]
#[allow(non_snake_case)]
fn test_1_Pow_3() {
    type A = UInt<UTerm, B1>;
    type B = UInt<UInt<UTerm, B1>, B1>;
    type U1 = UInt<UTerm, B1>;

    #[allow(non_camel_case_types)]
    type U1PowU3 = <<A as Pow<B>>::Output as Same<U1>>::Output;

    assert_eq!(<U1PowU3 as Unsigned>::to_u64(), <U1 as Unsigned>::to_u64());
}
#[test]
#[allow(non_snake_case)]
fn test_1_Min_3() {
    type A = UInt<UTerm, B1>;
    type B = UInt<UInt<UTerm, B1>, B1>;
    type U1 = UInt<UTerm, B1>;

    #[allow(non_camel_case_types)]
    type U1MinU3 = <<A as Min<B>>::Output as Same<U1>>::Output;

    assert_eq!(<U1MinU3 as Unsigned>::to_u64(), <U1 as Unsigned>::to_u64());
}
#[test]
#[allow(non_snake_case)]
fn test_1_Max_3() {
    type A = UInt<UTerm, B1>;
    type B = UInt<UInt<UTerm, B1>, B1>;
    type U3 = UInt<UInt<UTerm, B1>, B1>;

    #[allow(non_camel_case_types)]
    type U1MaxU3 = <<A as Max<B>>::Output as Same<U3>>::Output;

    assert_eq!(<U1MaxU3 as Unsigned>::to_u64(), <U3 as Unsigned>::to_u64());
}
#[test]
#[allow(non_snake_case)]
fn test_1_Gcd_3() {
    type A = UInt<UTerm, B1>;
    type B = UInt<UInt<UTerm, B1>, B1>;
    type U1 = UInt<UTerm, B1>;

    #[allow(non_camel_case_types)]
    type U1GcdU3 = <<A as Gcd<B>>::Output as Same<U1>>::Output;

    assert_eq!(<U1GcdU3 as Unsigned>::to_u64(), <U1 as Unsigned>::to_u64());
}
#[test]
#[allow(non_snake_case)]
fn test_1_Div_3() {
    type A = UInt<UTerm, B1>;
    type B = UInt<UInt<UTerm, B1>, B1>;
    type U0 = UTerm;

    #[allow(non_camel_case_types)]
    type U1DivU3 = <<A as Div<B>>::Output as Same<U0>>::Output;

    assert_eq!(<U1DivU3 as Unsigned>::to_u64(), <U0 as Unsigned>::to_u64());
}
#[test]
#[allow(non_snake_case)]
fn test_1_Rem_3() {
    type A = UInt<UTerm, B1>;
    type B = UInt<UInt<UTerm, B1>, B1>;
    type U1 = UInt<UTerm, B1>;

    #[allow(non_camel_case_types)]
    type U1RemU3 = <<A as Rem<B>>::Output as Same<U1>>::Output;

    assert_eq!(<U1RemU3 as Unsigned>::to_u64(), <U1 as Unsigned>::to_u64());
}
#[test]
#[allow(non_snake_case)]
fn test_1_Cmp_3() {
    type A = UInt<UTerm, B1>;
    type B = UInt<UInt<UTerm, B1>, B1>;

    #[allow(non_camel_case_types)]
    type U1CmpU3 = <A as Cmp<B>>::Output;
    assert_eq!(<U1CmpU3 as Ord>::to_ordering(), Ordering::Less);
}
#[test]
#[allow(non_snake_case)]
fn test_1_BitAnd_4() {
    type A = UInt<UTerm, B1>;
    type B = UInt<UInt<UInt<UTerm, B1>, B0>, B0>;
    type U0 = UTerm;

    #[allow(non_camel_case_types)]
    type U1BitAndU4 = <<A as BitAnd<B>>::Output as Same<U0>>::Output;

    assert_eq!(<U1BitAndU4 as Unsigned>::to_u64(), <U0 as Unsigned>::to_u64());
}
#[test]
#[allow(non_snake_case)]
fn test_1_BitOr_4() {
    type A = UInt<UTerm, B1>;
    type B = UInt<UInt<UInt<UTerm, B1>, B0>, B0>;
    type U5 = UInt<UInt<UInt<UTerm, B1>, B0>, B1>;

    #[allow(non_camel_case_types)]
    type U1BitOrU4 = <<A as BitOr<B>>::Output as Same<U5>>::Output;

    assert_eq!(<U1BitOrU4 as Unsigned>::to_u64(), <U5 as Unsigned>::to_u64());
}
#[test]
#[allow(non_snake_case)]
fn test_1_BitXor_4() {
    type A = UInt<UTerm, B1>;
    type B = UInt<UInt<UInt<UTerm, B1>, B0>, B0>;
    type U5 = UInt<UInt<UInt<UTerm, B1>, B0>, B1>;

    #[allow(non_camel_case_types)]
    type U1BitXorU4 = <<A as BitXor<B>>::Output as Same<U5>>::Output;

    assert_eq!(<U1BitXorU4 as Unsigned>::to_u64(), <U5 as Unsigned>::to_u64());
}
#[test]
#[allow(non_snake_case)]
fn test_1_Shl_4() {
    type A = UInt<UTerm, B1>;
    type B = UInt<UInt<UInt<UTerm, B1>, B0>, B0>;
    type U16 = UInt<UInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>, B0>, B0>;

    #[allow(non_camel_case_types)]
    type U1ShlU4 = <<A as Shl<B>>::Output as Same<U16>>::Output;

    assert_eq!(<U1ShlU4 as Unsigned>::to_u64(), <U16 as Unsigned>::to_u64());
}
#[test]
#[allow(non_snake_case)]
fn test_1_Shr_4() {
    type A = UInt<UTerm, B1>;
    type B = UInt<UInt<UInt<UTerm, B1>, B0>, B0>;
    type U0 = UTerm;

    #[allow(non_camel_case_types)]
    type U1ShrU4 = <<A as Shr<B>>::Output as Same<U0>>::Output;

    assert_eq!(<U1ShrU4 as Unsigned>::to_u64(), <U0 as Unsigned>::to_u64());
}
#[test]
#[allow(non_snake_case)]
fn test_1_Add_4() {
    type A = UInt<UTerm, B1>;
    type B = UInt<UInt<UInt<UTerm, B1>, B0>, B0>;
    type U5 = UInt<UInt<UInt<UTerm, B1>, B0>, B1>;

    #[allow(non_camel_case_types)]
    type U1AddU4 = <<A as Add<B>>::Output as Same<U5>>::Output;

    assert_eq!(<U1AddU4 as Unsigned>::to_u64(), <U5 as Unsigned>::to_u64());
}
#[test]
#[allow(non_snake_case)]
fn test_1_Mul_4() {
    type A = UInt<UTerm, B1>;
    type B = UInt<UInt<UInt<UTerm, B1>, B0>, B0>;
    type U4 = UInt<UInt<UInt<UTerm, B1>, B0>, B0>;

    #[allow(non_camel_case_types)]
    type U1MulU4 = <<A as Mul<B>>::Output as Same<U4>>::Output;

    assert_eq!(<U1MulU4 as Unsigned>::to_u64(), <U4 as Unsigned>::to_u64());
}
#[test]
#[allow(non_snake_case)]
fn test_1_Pow_4() {
    type A = UInt<UTerm, B1>;
    type B = UInt<UInt<UInt<UTerm, B1>, B0>, B0>;
    type U1 = UInt<UTerm, B1>;

    #[allow(non_camel_case_types)]
    type U1PowU4 = <<A as Pow<B>>::Output as Same<U1>>::Output;

    assert_eq!(<U1PowU4 as Unsigned>::to_u64(), <U1 as Unsigned>::to_u64());
}
#[test]
#[allow(non_snake_case)]
fn test_1_Min_4() {
    type A = UInt<UTerm, B1>;
    type B = UInt<UInt<UInt<UTerm, B1>, B0>, B0>;
    type U1 = UInt<UTerm, B1>;

    #[allow(non_camel_case_types)]
    type U1MinU4 = <<A as Min<B>>::Output as Same<U1>>::Output;

    assert_eq!(<U1MinU4 as Unsigned>::to_u64(), <U1 as Unsigned>::to_u64());
}
#[test]
#[allow(non_snake_case)]
fn test_1_Max_4() {
    type A = UInt<UTerm, B1>;
    type B = UInt<UInt<UInt<UTerm, B1>, B0>, B0>;
    type U4 = UInt<UInt<UInt<UTerm, B1>, B0>, B0>;

    #[allow(non_camel_case_types)]
    type U1MaxU4 = <<A as Max<B>>::Output as Same<U4>>::Output;

    assert_eq!(<U1MaxU4 as Unsigned>::to_u64(), <U4 as Unsigned>::to_u64());
}
#[test]
#[allow(non_snake_case)]
fn test_1_Gcd_4() {
    type A = UInt<UTerm, B1>;
    type B = UInt<UInt<UInt<UTerm, B1>, B0>, B0>;
    type U1 = UInt<UTerm, B1>;

    #[allow(non_camel_case_types)]
    type U1GcdU4 = <<A as Gcd<B>>::Output as Same<U1>>::Output;

    assert_eq!(<U1GcdU4 as Unsigned>::to_u64(), <U1 as Unsigned>::to_u64());
}
#[test]
#[allow(non_snake_case)]
fn test_1_Div_4() {
    type A = UInt<UTerm, B1>;
    type B = UInt<UInt<UInt<UTerm, B1>, B0>, B0>;
    type U0 = UTerm;

    #[allow(non_camel_case_types)]
    type U1DivU4 = <<A as Div<B>>::Output as Same<U0>>::Output;

    assert_eq!(<U1DivU4 as Unsigned>::to_u64(), <U0 as Unsigned>::to_u64());
}
#[test]
#[allow(non_snake_case)]
fn test_1_Rem_4() {
    type A = UInt<UTerm, B1>;
    type B = UInt<UInt<UInt<UTerm, B1>, B0>, B0>;
    type U1 = UInt<UTerm, B1>;

    #[allow(non_camel_case_types)]
    type U1RemU4 = <<A as Rem<B>>::Output as Same<U1>>::Output;

    assert_eq!(<U1RemU4 as Unsigned>::to_u64(), <U1 as Unsigned>::to_u64());
}
#[test]
#[allow(non_snake_case)]
fn test_1_Cmp_4() {
    type A = UInt<UTerm, B1>;
    type B = UInt<UInt<UInt<UTerm, B1>, B0>, B0>;

    #[allow(non_camel_case_types)]
    type U1CmpU4 = <A as Cmp<B>>::Output;
    assert_eq!(<U1CmpU4 as Ord>::to_ordering(), Ordering::Less);
}
#[test]
#[allow(non_snake_case)]
fn test_1_BitAnd_5() {
    type A = UInt<UTerm, B1>;
    type B = UInt<UInt<UInt<UTerm, B1>, B0>, B1>;
    type U1 = UInt<UTerm, B1>;

    #[allow(non_camel_case_types)]
    type U1BitAndU5 = <<A as BitAnd<B>>::Output as Same<U1>>::Output;

    assert_eq!(<U1BitAndU5 as Unsigned>::to_u64(), <U1 as Unsigned>::to_u64());
}
#[test]
#[allow(non_snake_case)]
fn test_1_BitOr_5() {
    type A = UInt<UTerm, B1>;
    type B = UInt<UInt<UInt<UTerm, B1>, B0>, B1>;
    type U5 = UInt<UInt<UInt<UTerm, B1>, B0>, B1>;

    #[allow(non_camel_case_types)]
    type U1BitOrU5 = <<A as BitOr<B>>::Output as Same<U5>>::Output;

    assert_eq!(<U1BitOrU5 as Unsigned>::to_u64(), <U5 as Unsigned>::to_u64());
}
#[test]
#[allow(non_snake_case)]
fn test_1_BitXor_5() {
    type A = UInt<UTerm, B1>;
    type B = UInt<UInt<UInt<UTerm, B1>, B0>, B1>;
    type U4 = UInt<UInt<UInt<UTerm, B1>, B0>, B0>;

    #[allow(non_camel_case_types)]
    type U1BitXorU5 = <<A as BitXor<B>>::Output as Same<U4>>::Output;

    assert_eq!(<U1BitXorU5 as Unsigned>::to_u64(), <U4 as Unsigned>::to_u64());
}
#[test]
#[allow(non_snake_case)]
fn test_1_Shl_5() {
    type A = UInt<UTerm, B1>;
    type B = UInt<UInt<UInt<UTerm, B1>, B0>, B1>;
    type U32 = UInt<UInt<UInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>, B0>, B0>, B0>;

    #[allow(non_camel_case_types)]
    type U1ShlU5 = <<A as Shl<B>>::Output as Same<U32>>::Output;

    assert_eq!(<U1ShlU5 as Unsigned>::to_u64(), <U32 as Unsigned>::to_u64());
}
#[test]
#[allow(non_snake_case)]
fn test_1_Shr_5() {
    type A = UInt<UTerm, B1>;
    type B = UInt<UInt<UInt<UTerm, B1>, B0>, B1>;
    type U0 = UTerm;

    #[allow(non_camel_case_types)]
    type U1ShrU5 = <<A as Shr<B>>::Output as Same<U0>>::Output;

    assert_eq!(<U1ShrU5 as Unsigned>::to_u64(), <U0 as Unsigned>::to_u64());
}
#[test]
#[allow(non_snake_case)]
fn test_1_Add_5() {
    type A = UInt<UTerm, B1>;
    type B = UInt<UInt<UInt<UTerm, B1>, B0>, B1>;
    type U6 = UInt<UInt<UInt<UTerm, B1>, B1>, B0>;

    #[allow(non_camel_case_types)]
    type U1AddU5 = <<A as Add<B>>::Output as Same<U6>>::Output;

    assert_eq!(<U1AddU5 as Unsigned>::to_u64(), <U6 as Unsigned>::to_u64());
}
#[test]
#[allow(non_snake_case)]
fn test_1_Mul_5() {
    type A = UInt<UTerm, B1>;
    type B = UInt<UInt<UInt<UTerm, B1>, B0>, B1>;
    type U5 = UInt<UInt<UInt<UTerm, B1>, B0>, B1>;

    #[allow(non_camel_case_types)]
    type U1MulU5 = <<A as Mul<B>>::Output as Same<U5>>::Output;

    assert_eq!(<U1MulU5 as Unsigned>::to_u64(), <U5 as Unsigned>::to_u64());
}
#[test]
#[allow(non_snake_case)]
fn test_1_Pow_5() {
    type A = UInt<UTerm, B1>;
    type B = UInt<UInt<UInt<UTerm, B1>, B0>, B1>;
    type U1 = UInt<UTerm, B1>;

    #[allow(non_camel_case_types)]
    type U1PowU5 = <<A as Pow<B>>::Output as Same<U1>>::Output;

    assert_eq!(<U1PowU5 as Unsigned>::to_u64(), <U1 as Unsigned>::to_u64());
}
#[test]
#[allow(non_snake_case)]
fn test_1_Min_5() {
    type A = UInt<UTerm, B1>;
    type B = UInt<UInt<UInt<UTerm, B1>, B0>, B1>;
    type U1 = UInt<UTerm, B1>;

    #[allow(non_camel_case_types)]
    type U1MinU5 = <<A as Min<B>>::Output as Same<U1>>::Output;

    assert_eq!(<U1MinU5 as Unsigned>::to_u64(), <U1 as Unsigned>::to_u64());
}
#[test]
#[allow(non_snake_case)]
fn test_1_Max_5() {
    type A = UInt<UTerm, B1>;
    type B = UInt<UInt<UInt<UTerm, B1>, B0>, B1>;
    type U5 = UInt<UInt<UInt<UTerm, B1>, B0>, B1>;

    #[allow(non_camel_case_types)]
    type U1MaxU5 = <<A as Max<B>>::Output as Same<U5>>::Output;

    assert_eq!(<U1MaxU5 as Unsigned>::to_u64(), <U5 as Unsigned>::to_u64());
}
#[test]
#[allow(non_snake_case)]
fn test_1_Gcd_5() {
    type A = UInt<UTerm, B1>;
    type B = UInt<UInt<UInt<UTerm, B1>, B0>, B1>;
    type U1 = UInt<UTerm, B1>;

    #[allow(non_camel_case_types)]
    type U1GcdU5 = <<A as Gcd<B>>::Output as Same<U1>>::Output;

    assert_eq!(<U1GcdU5 as Unsigned>::to_u64(), <U1 as Unsigned>::to_u64());
}
#[test]
#[allow(non_snake_case)]
fn test_1_Div_5() {
    type A = UInt<UTerm, B1>;
    type B = UInt<UInt<UInt<UTerm, B1>, B0>, B1>;
    type U0 = UTerm;

    #[allow(non_camel_case_types)]
    type U1DivU5 = <<A as Div<B>>::Output as Same<U0>>::Output;

    assert_eq!(<U1DivU5 as Unsigned>::to_u64(), <U0 as Unsigned>::to_u64());
}
#[test]
#[allow(non_snake_case)]
fn test_1_Rem_5() {
    type A = UInt<UTerm, B1>;
    type B = UInt<UInt<UInt<UTerm, B1>, B0>, B1>;
    type U1 = UInt<UTerm, B1>;

    #[allow(non_camel_case_types)]
    type U1RemU5 = <<A as Rem<B>>::Output as Same<U1>>::Output;

    assert_eq!(<U1RemU5 as Unsigned>::to_u64(), <U1 as Unsigned>::to_u64());
}
#[test]
#[allow(non_snake_case)]
fn test_1_Cmp_5() {
    type A = UInt<UTerm, B1>;
    type B = UInt<UInt<UInt<UTerm, B1>, B0>, B1>;

    #[allow(non_camel_case_types)]
    type U1CmpU5 = <A as Cmp<B>>::Output;
    assert_eq!(<U1CmpU5 as Ord>::to_ordering(), Ordering::Less);
}
#[test]
#[allow(non_snake_case)]
fn test_2_BitAnd_0() {
    type A = UInt<UInt<UTerm, B1>, B0>;
    type B = UTerm;
    type U0 = UTerm;

    #[allow(non_camel_case_types)]
    type U2BitAndU0 = <<A as BitAnd<B>>::Output as Same<U0>>::Output;

    assert_eq!(<U2BitAndU0 as Unsigned>::to_u64(), <U0 as Unsigned>::to_u64());
}
#[test]
#[allow(non_snake_case)]
fn test_2_BitOr_0() {
    type A = UInt<UInt<UTerm, B1>, B0>;
    type B = UTerm;
    type U2 = UInt<UInt<UTerm, B1>, B0>;

    #[allow(non_camel_case_types)]
    type U2BitOrU0 = <<A as BitOr<B>>::Output as Same<U2>>::Output;

    assert_eq!(<U2BitOrU0 as Unsigned>::to_u64(), <U2 as Unsigned>::to_u64());
}
#[test]
#[allow(non_snake_case)]
fn test_2_BitXor_0() {
    type A = UInt<UInt<UTerm, B1>, B0>;
    type B = UTerm;
    type U2 = UInt<UInt<UTerm, B1>, B0>;

    #[allow(non_camel_case_types)]
    type U2BitXorU0 = <<A as BitXor<B>>::Output as Same<U2>>::Output;

    assert_eq!(<U2BitXorU0 as Unsigned>::to_u64(), <U2 as Unsigned>::to_u64());
}
#[test]
#[allow(non_snake_case)]
fn test_2_Shl_0() {
    type A = UInt<UInt<UTerm, B1>, B0>;
    type B = UTerm;
    type U2 = UInt<UInt<UTerm, B1>, B0>;

    #[allow(non_camel_case_types)]
    type U2ShlU0 = <<A as Shl<B>>::Output as Same<U2>>::Output;

    assert_eq!(<U2ShlU0 as Unsigned>::to_u64(), <U2 as Unsigned>::to_u64());
}
#[test]
#[allow(non_snake_case)]
fn test_2_Shr_0() {
    type A = UInt<UInt<UTerm, B1>, B0>;
    type B = UTerm;
    type U2 = UInt<UInt<UTerm, B1>, B0>;

    #[allow(non_camel_case_types)]
    type U2ShrU0 = <<A as Shr<B>>::Output as Same<U2>>::Output;

    assert_eq!(<U2ShrU0 as Unsigned>::to_u64(), <U2 as Unsigned>::to_u64());
}
#[test]
#[allow(non_snake_case)]
fn test_2_Add_0() {
    type A = UInt<UInt<UTerm, B1>, B0>;
    type B = UTerm;
    type U2 = UInt<UInt<UTerm, B1>, B0>;

    #[allow(non_camel_case_types)]
    type U2AddU0 = <<A as Add<B>>::Output as Same<U2>>::Output;

    assert_eq!(<U2AddU0 as Unsigned>::to_u64(), <U2 as Unsigned>::to_u64());
}
#[test]
#[allow(non_snake_case)]
fn test_2_Mul_0() {
    type A = UInt<UInt<UTerm, B1>, B0>;
    type B = UTerm;
    type U0 = UTerm;

    #[allow(non_camel_case_types)]
    type U2MulU0 = <<A as Mul<B>>::Output as Same<U0>>::Output;

    assert_eq!(<U2MulU0 as Unsigned>::to_u64(), <U0 as Unsigned>::to_u64());
}
#[test]
#[allow(non_snake_case)]
fn test_2_Pow_0() {
    type A = UInt<UInt<UTerm, B1>, B0>;
    type B = UTerm;
    type U1 = UInt<UTerm, B1>;

    #[allow(non_camel_case_types)]
    type U2PowU0 = <<A as Pow<B>>::Output as Same<U1>>::Output;

    assert_eq!(<U2PowU0 as Unsigned>::to_u64(), <U1 as Unsigned>::to_u64());
}
#[test]
#[allow(non_snake_case)]
fn test_2_Min_0() {
    type A = UInt<UInt<UTerm, B1>, B0>;
    type B = UTerm;
    type U0 = UTerm;

    #[allow(non_camel_case_types)]
    type U2MinU0 = <<A as Min<B>>::Output as Same<U0>>::Output;

    assert_eq!(<U2MinU0 as Unsigned>::to_u64(), <U0 as Unsigned>::to_u64());
}
#[test]
#[allow(non_snake_case)]
fn test_2_Max_0() {
    type A = UInt<UInt<UTerm, B1>, B0>;
    type B = UTerm;
    type U2 = UInt<UInt<UTerm, B1>, B0>;

    #[allow(non_camel_case_types)]
    type U2MaxU0 = <<A as Max<B>>::Output as Same<U2>>::Output;

    assert_eq!(<U2MaxU0 as Unsigned>::to_u64(), <U2 as Unsigned>::to_u64());
}
#[test]
#[allow(non_snake_case)]
fn test_2_Gcd_0() {
    type A = UInt<UInt<UTerm, B1>, B0>;
    type B = UTerm;
    type U2 = UInt<UInt<UTerm, B1>, B0>;

    #[allow(non_camel_case_types)]
    type U2GcdU0 = <<A as Gcd<B>>::Output as Same<U2>>::Output;

    assert_eq!(<U2GcdU0 as Unsigned>::to_u64(), <U2 as Unsigned>::to_u64());
}
#[test]
#[allow(non_snake_case)]
fn test_2_Sub_0() {
    type A = UInt<UInt<UTerm, B1>, B0>;
    type B = UTerm;
    type U2 = UInt<UInt<UTerm, B1>, B0>;

    #[allow(non_camel_case_types)]
    type U2SubU0 = <<A as Sub<B>>::Output as Same<U2>>::Output;

    assert_eq!(<U2SubU0 as Unsigned>::to_u64(), <U2 as Unsigned>::to_u64());
}
#[test]
#[allow(non_snake_case)]
fn test_2_Cmp_0() {
    type A = UInt<UInt<UTerm, B1>, B0>;
    type B = UTerm;

    #[allow(non_camel_case_types)]
    type U2CmpU0 = <A as Cmp<B>>::Output;
    assert_eq!(<U2CmpU0 as Ord>::to_ordering(), Ordering::Greater);
}
#[test]
#[allow(non_snake_case)]
fn test_2_BitAnd_1() {
    type A = UInt<UInt<UTerm, B1>, B0>;
    type B = UInt<UTerm, B1>;
    type U0 = UTerm;

    #[allow(non_camel_case_types)]
    type U2BitAndU1 = <<A as BitAnd<B>>::Output as Same<U0>>::Output;

    assert_eq!(<U2BitAndU1 as Unsigned>::to_u64(), <U0 as Unsigned>::to_u64());
}
#[test]
#[allow(non_snake_case)]
fn test_2_BitOr_1() {
    type A = UInt<UInt<UTerm, B1>, B0>;
    type B = UInt<UTerm, B1>;
    type U3 = UInt<UInt<UTerm, B1>, B1>;

    #[allow(non_camel_case_types)]
    type U2BitOrU1 = <<A as BitOr<B>>::Output as Same<U3>>::Output;

    assert_eq!(<U2BitOrU1 as Unsigned>::to_u64(), <U3 as Unsigned>::to_u64());
}
#[test]
#[allow(non_snake_case)]
fn test_2_BitXor_1() {
    type A = UInt<UInt<UTerm, B1>, B0>;
    type B = UInt<UTerm, B1>;
    type U3 = UInt<UInt<UTerm, B1>, B1>;

    #[allow(non_camel_case_types)]
    type U2BitXorU1 = <<A as BitXor<B>>::Output as Same<U3>>::Output;

    assert_eq!(<U2BitXorU1 as Unsigned>::to_u64(), <U3 as Unsigned>::to_u64());
}
#[test]
#[allow(non_snake_case)]
fn test_2_Shl_1() {
    type A = UInt<UInt<UTerm, B1>, B0>;
    type B = UInt<UTerm, B1>;
    type U4 = UInt<UInt<UInt<UTerm, B1>, B0>, B0>;

    #[allow(non_camel_case_types)]
    type U2ShlU1 = <<A as Shl<B>>::Output as Same<U4>>::Output;

    assert_eq!(<U2ShlU1 as Unsigned>::to_u64(), <U4 as Unsigned>::to_u64());
}
#[test]
#[allow(non_snake_case)]
fn test_2_Shr_1() {
    type A = UInt<UInt<UTerm, B1>, B0>;
    type B = UInt<UTerm, B1>;
    type U1 = UInt<UTerm, B1>;

    #[allow(non_camel_case_types)]
    type U2ShrU1 = <<A as Shr<B>>::Output as Same<U1>>::Output;

    assert_eq!(<U2ShrU1 as Unsigned>::to_u64(), <U1 as Unsigned>::to_u64());
}
#[test]
#[allow(non_snake_case)]
fn test_2_Add_1() {
    type A = UInt<UInt<UTerm, B1>, B0>;
    type B = UInt<UTerm, B1>;
    type U3 = UInt<UInt<UTerm, B1>, B1>;

    #[allow(non_camel_case_types)]
    type U2AddU1 = <<A as Add<B>>::Output as Same<U3>>::Output;

    assert_eq!(<U2AddU1 as Unsigned>::to_u64(), <U3 as Unsigned>::to_u64());
}
#[test]
#[allow(non_snake_case)]
fn test_2_Mul_1() {
    type A = UInt<UInt<UTerm, B1>, B0>;
    type B = UInt<UTerm, B1>;
    type U2 = UInt<UInt<UTerm, B1>, B0>;

    #[allow(non_camel_case_types)]
    type U2MulU1 = <<A as Mul<B>>::Output as Same<U2>>::Output;

    assert_eq!(<U2MulU1 as Unsigned>::to_u64(), <U2 as Unsigned>::to_u64());
}
#[test]
#[allow(non_snake_case)]
fn test_2_Pow_1() {
    type A = UInt<UInt<UTerm, B1>, B0>;
    type B = UInt<UTerm, B1>;
    type U2 = UInt<UInt<UTerm, B1>, B0>;

    #[allow(non_camel_case_types)]
    type U2PowU1 = <<A as Pow<B>>::Output as Same<U2>>::Output;

    assert_eq!(<U2PowU1 as Unsigned>::to_u64(), <U2 as Unsigned>::to_u64());
}
#[test]
#[allow(non_snake_case)]
fn test_2_Min_1() {
    type A = UInt<UInt<UTerm, B1>, B0>;
    type B = UInt<UTerm, B1>;
    type U1 = UInt<UTerm, B1>;

    #[allow(non_camel_case_types)]
    type U2MinU1 = <<A as Min<B>>::Output as Same<U1>>::Output;

    assert_eq!(<U2MinU1 as Unsigned>::to_u64(), <U1 as Unsigned>::to_u64());
}
#[test]
#[allow(non_snake_case)]
fn test_2_Max_1() {
    type A = UInt<UInt<UTerm, B1>, B0>;
    type B = UInt<UTerm, B1>;
    type U2 = UInt<UInt<UTerm, B1>, B0>;

    #[allow(non_camel_case_types)]
    type U2MaxU1 = <<A as Max<B>>::Output as Same<U2>>::Output;

    assert_eq!(<U2MaxU1 as Unsigned>::to_u64(), <U2 as Unsigned>::to_u64());
}
#[test]
#[allow(non_snake_case)]
fn test_2_Gcd_1() {
    type A = UInt<UInt<UTerm, B1>, B0>;
    type B = UInt<UTerm, B1>;
    type U1 = UInt<UTerm, B1>;

    #[allow(non_camel_case_types)]
    type U2GcdU1 = <<A as Gcd<B>>::Output as Same<U1>>::Output;

    assert_eq!(<U2GcdU1 as Unsigned>::to_u64(), <U1 as Unsigned>::to_u64());
}
#[test]
#[allow(non_snake_case)]
fn test_2_Sub_1() {
    type A = UInt<UInt<UTerm, B1>, B0>;
    type B = UInt<UTerm, B1>;
    type U1 = UInt<UTerm, B1>;

    #[allow(non_camel_case_types)]
    type U2SubU1 = <<A as Sub<B>>::Output as Same<U1>>::Output;

    assert_eq!(<U2SubU1 as Unsigned>::to_u64(), <U1 as Unsigned>::to_u64());
}
#[test]
#[allow(non_snake_case)]
fn test_2_Div_1() {
    type A = UInt<UInt<UTerm, B1>, B0>;
    type B = UInt<UTerm, B1>;
    type U2 = UInt<UInt<UTerm, B1>, B0>;

    #[allow(non_camel_case_types)]
    type U2DivU1 = <<A as Div<B>>::Output as Same<U2>>::Output;

    assert_eq!(<U2DivU1 as Unsigned>::to_u64(), <U2 as Unsigned>::to_u64());
}
#[test]
#[allow(non_snake_case)]
fn test_2_Rem_1() {
    type A = UInt<UInt<UTerm, B1>, B0>;
    type B = UInt<UTerm, B1>;
    type U0 = UTerm;

    #[allow(non_camel_case_types)]
    type U2RemU1 = <<A as Rem<B>>::Output as Same<U0>>::Output;

    assert_eq!(<U2RemU1 as Unsigned>::to_u64(), <U0 as Unsigned>::to_u64());
}
#[test]
#[allow(non_snake_case)]
fn test_2_PartialDiv_1() {
    type A = UInt<UInt<UTerm, B1>, B0>;
    type B = UInt<UTerm, B1>;
    type U2 = UInt<UInt<UTerm, B1>, B0>;

    #[allow(non_camel_case_types)]
    type U2PartialDivU1 = <<A as PartialDiv<B>>::Output as Same<U2>>::Output;

    assert_eq!(<U2PartialDivU1 as Unsigned>::to_u64(), <U2 as Unsigned>::to_u64());
}
#[test]
#[allow(non_snake_case)]
fn test_2_Cmp_1() {
    type A = UInt<UInt<UTerm, B1>, B0>;
    type B = UInt<UTerm, B1>;

    #[allow(non_camel_case_types)]
    type U2CmpU1 = <A as Cmp<B>>::Output;
    assert_eq!(<U2CmpU1 as Ord>::to_ordering(), Ordering::Greater);
}
#[test]
#[allow(non_snake_case)]
fn test_2_BitAnd_2() {
    type A = UInt<UInt<UTerm, B1>, B0>;
    type B = UInt<UInt<UTerm, B1>, B0>;
    type U2 = UInt<UInt<UTerm, B1>, B0>;

    #[allow(non_camel_case_types)]
    type U2BitAndU2 = <<A as BitAnd<B>>::Output as Same<U2>>::Output;

    assert_eq!(<U2BitAndU2 as Unsigned>::to_u64(), <U2 as Unsigned>::to_u64());
}
#[test]
#[allow(non_snake_case)]
fn test_2_BitOr_2() {
    type A = UInt<UInt<UTerm, B1>, B0>;
    type B = UInt<UInt<UTerm, B1>, B0>;
    type U2 = UInt<UInt<UTerm, B1>, B0>;

    #[allow(non_camel_case_types)]
    type U2BitOrU2 = <<A as BitOr<B>>::Output as Same<U2>>::Output;

    assert_eq!(<U2BitOrU2 as Unsigned>::to_u64(), <U2 as Unsigned>::to_u64());
}
#[test]
#[allow(non_snake_case)]
fn test_2_BitXor_2() {
    type A = UInt<UInt<UTerm, B1>, B0>;
    type B = UInt<UInt<UTerm, B1>, B0>;
    type U0 = UTerm;

    #[allow(non_camel_case_types)]
    type U2BitXorU2 = <<A as BitXor<B>>::Output as Same<U0>>::Output;

    assert_eq!(<U2BitXorU2 as Unsigned>::to_u64(), <U0 as Unsigned>::to_u64());
}
#[test]
#[allow(non_snake_case)]
fn test_2_Shl_2() {
    type A = UInt<UInt<UTerm, B1>, B0>;
    type B = UInt<UInt<UTerm, B1>, B0>;
    type U8 = UInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>, B0>;

    #[allow(non_camel_case_types)]
    type U2ShlU2 = <<A as Shl<B>>::Output as Same<U8>>::Output;

    assert_eq!(<U2ShlU2 as Unsigned>::to_u64(), <U8 as Unsigned>::to_u64());
}
#[test]
#[allow(non_snake_case)]
fn test_2_Shr_2() {
    type A = UInt<UInt<UTerm, B1>, B0>;
    type B = UInt<UInt<UTerm, B1>, B0>;
    type U0 = UTerm;

    #[allow(non_camel_case_types)]
    type U2ShrU2 = <<A as Shr<B>>::Output as Same<U0>>::Output;

    assert_eq!(<U2ShrU2 as Unsigned>::to_u64(), <U0 as Unsigned>::to_u64());
}
#[test]
#[allow(non_snake_case)]
fn test_2_Add_2() {
    type A = UInt<UInt<UTerm, B1>, B0>;
    type B = UInt<UInt<UTerm, B1>, B0>;
    type U4 = UInt<UInt<UInt<UTerm, B1>, B0>, B0>;

    #[allow(non_camel_case_types)]
    type U2AddU2 = <<A as Add<B>>::Output as Same<U4>>::Output;

    assert_eq!(<U2AddU2 as Unsigned>::to_u64(), <U4 as Unsigned>::to_u64());
}
#[test]
#[allow(non_snake_case)]
fn test_2_Mul_2() {
    type A = UInt<UInt<UTerm, B1>, B0>;
    type B = UInt<UInt<UTerm, B1>, B0>;
    type U4 = UInt<UInt<UInt<UTerm, B1>, B0>, B0>;

    #[allow(non_camel_case_types)]
    type U2MulU2 = <<A as Mul<B>>::Output as Same<U4>>::Output;

    assert_eq!(<U2MulU2 as Unsigned>::to_u64(), <U4 as Unsigned>::to_u64());
}
#[test]
#[allow(non_snake_case)]
fn test_2_Pow_2() {
    type A = UInt<UInt<UTerm, B1>, B0>;
    type B = UInt<UInt<UTerm, B1>, B0>;
    type U4 = UInt<UInt<UInt<UTerm, B1>, B0>, B0>;

    #[allow(non_camel_case_types)]
    type U2PowU2 = <<A as Pow<B>>::Output as Same<U4>>::Output;

    assert_eq!(<U2PowU2 as Unsigned>::to_u64(), <U4 as Unsigned>::to_u64());
}
#[test]
#[allow(non_snake_case)]
fn test_2_Min_2() {
    type A = UInt<UInt<UTerm, B1>, B0>;
    type B = UInt<UInt<UTerm, B1>, B0>;
    type U2 = UInt<UInt<UTerm, B1>, B0>;

    #[allow(non_camel_case_types)]
    type U2MinU2 = <<A as Min<B>>::Output as Same<U2>>::Output;

    assert_eq!(<U2MinU2 as Unsigned>::to_u64(), <U2 as Unsigned>::to_u64());
}
#[test]
#[allow(non_snake_case)]
fn test_2_Max_2() {
    type A = UInt<UInt<UTerm, B1>, B0>;
    type B = UInt<UInt<UTerm, B1>, B0>;
    type U2 = UInt<UInt<UTerm, B1>, B0>;

    #[allow(non_camel_case_types)]
    type U2MaxU2 = <<A as Max<B>>::Output as Same<U2>>::Output;

    assert_eq!(<U2MaxU2 as Unsigned>::to_u64(), <U2 as Unsigned>::to_u64());
}
#[test]
#[allow(non_snake_case)]
fn test_2_Gcd_2() {
    type A = UInt<UInt<UTerm, B1>, B0>;
    type B = UInt<UInt<UTerm, B1>, B0>;
    type U2 = UInt<UInt<UTerm, B1>, B0>;

    #[allow(non_camel_case_types)]
    type U2GcdU2 = <<A as Gcd<B>>::Output as Same<U2>>::Output;

    assert_eq!(<U2GcdU2 as Unsigned>::to_u64(), <U2 as Unsigned>::to_u64());
}
#[test]
#[allow(non_snake_case)]
fn test_2_Sub_2() {
    type A = UInt<UInt<UTerm, B1>, B0>;
    type B = UInt<UInt<UTerm, B1>, B0>;
    type U0 = UTerm;

    #[allow(non_camel_case_types)]
    type U2SubU2 = <<A as Sub<B>>::Output as Same<U0>>::Output;

    assert_eq!(<U2SubU2 as Unsigned>::to_u64(), <U0 as Unsigned>::to_u64());
}
#[test]
#[allow(non_snake_case)]
fn test_2_Div_2() {
    type A = UInt<UInt<UTerm, B1>, B0>;
    type B = UInt<UInt<UTerm, B1>, B0>;
    type U1 = UInt<UTerm, B1>;

    #[allow(non_camel_case_types)]
    type U2DivU2 = <<A as Div<B>>::Output as Same<U1>>::Output;

    assert_eq!(<U2DivU2 as Unsigned>::to_u64(), <U1 as Unsigned>::to_u64());
}
#[test]
#[allow(non_snake_case)]
fn test_2_Rem_2() {
    type A = UInt<UInt<UTerm, B1>, B0>;
    type B = UInt<UInt<UTerm, B1>, B0>;
    type U0 = UTerm;

    #[allow(non_camel_case_types)]
    type U2RemU2 = <<A as Rem<B>>::Output as Same<U0>>::Output;

    assert_eq!(<U2RemU2 as Unsigned>::to_u64(), <U0 as Unsigned>::to_u64());
}
#[test]
#[allow(non_snake_case)]
fn test_2_PartialDiv_2() {
    type A = UInt<UInt<UTerm, B1>, B0>;
    type B = UInt<UInt<UTerm, B1>, B0>;
    type U1 = UInt<UTerm, B1>;

    #[allow(non_camel_case_types)]
    type U2PartialDivU2 = <<A as PartialDiv<B>>::Output as Same<U1>>::Output;

    assert_eq!(<U2PartialDivU2 as Unsigned>::to_u64(), <U1 as Unsigned>::to_u64());
}
#[test]
#[allow(non_snake_case)]
fn test_2_Cmp_2() {
    type A = UInt<UInt<UTerm, B1>, B0>;
    type B = UInt<UInt<UTerm, B1>, B0>;

    #[allow(non_camel_case_types)]
    type U2CmpU2 = <A as Cmp<B>>::Output;
    assert_eq!(<U2CmpU2 as Ord>::to_ordering(), Ordering::Equal);
}
#[test]
#[allow(non_snake_case)]
fn test_2_BitAnd_3() {
    type A = UInt<UInt<UTerm, B1>, B0>;
    type B = UInt<UInt<UTerm, B1>, B1>;
    type U2 = UInt<UInt<UTerm, B1>, B0>;

    #[allow(non_camel_case_types)]
    type U2BitAndU3 = <<A as BitAnd<B>>::Output as Same<U2>>::Output;

    assert_eq!(<U2BitAndU3 as Unsigned>::to_u64(), <U2 as Unsigned>::to_u64());
}
#[test]
#[allow(non_snake_case)]
fn test_2_BitOr_3() {
    type A = UInt<UInt<UTerm, B1>, B0>;
    type B = UInt<UInt<UTerm, B1>, B1>;
    type U3 = UInt<UInt<UTerm, B1>, B1>;

    #[allow(non_camel_case_types)]
    type U2BitOrU3 = <<A as BitOr<B>>::Output as Same<U3>>::Output;

    assert_eq!(<U2BitOrU3 as Unsigned>::to_u64(), <U3 as Unsigned>::to_u64());
}
#[test]
#[allow(non_snake_case)]
fn test_2_BitXor_3() {
    type A = UInt<UInt<UTerm, B1>, B0>;
    type B = UInt<UInt<UTerm, B1>, B1>;
    type U1 = UInt<UTerm, B1>;

    #[allow(non_camel_case_types)]
    type U2BitXorU3 = <<A as BitXor<B>>::Output as Same<U1>>::Output;

    assert_eq!(<U2BitXorU3 as Unsigned>::to_u64(), <U1 as Unsigned>::to_u64());
}
#[test]
#[allow(non_snake_case)]
fn test_2_Shl_3() {
    type A = UInt<UInt<UTerm, B1>, B0>;
    type B = UInt<UInt<UTerm, B1>, B1>;
    type U16 = UInt<UInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>, B0>, B0>;

    #[allow(non_camel_case_types)]
    type U2ShlU3 = <<A as Shl<B>>::Output as Same<U16>>::Output;

    assert_eq!(<U2ShlU3 as Unsigned>::to_u64(), <U16 as Unsigned>::to_u64());
}
#[test]
#[allow(non_snake_case)]
fn test_2_Shr_3() {
    type A = UInt<UInt<UTerm, B1>, B0>;
    type B = UInt<UInt<UTerm, B1>, B1>;
    type U0 = UTerm;

    #[allow(non_camel_case_types)]
    type U2ShrU3 = <<A as Shr<B>>::Output as Same<U0>>::Output;

    assert_eq!(<U2ShrU3 as Unsigned>::to_u64(), <U0 as Unsigned>::to_u64());
}
#[test]
#[allow(non_snake_case)]
fn test_2_Add_3() {
    type A = UInt<UInt<UTerm, B1>, B0>;
    type B = UInt<UInt<UTerm, B1>, B1>;
    type U5 = UInt<UInt<UInt<UTerm, B1>, B0>, B1>;

    #[allow(non_camel_case_types)]
    type U2AddU3 = <<A as Add<B>>::Output as Same<U5>>::Output;

    assert_eq!(<U2AddU3 as Unsigned>::to_u64(), <U5 as Unsigned>::to_u64());
}
#[test]
#[allow(non_snake_case)]
fn test_2_Mul_3() {
    type A = UInt<UInt<UTerm, B1>, B0>;
    type B = UInt<UInt<UTerm, B1>, B1>;
    type U6 = UInt<UInt<UInt<UTerm, B1>, B1>, B0>;

    #[allow(non_camel_case_types)]
    type U2MulU3 = <<A as Mul<B>>::Output as Same<U6>>::Output;

    assert_eq!(<U2MulU3 as Unsigned>::to_u64(), <U6 as Unsigned>::to_u64());
}
#[test]
#[allow(non_snake_case)]
fn test_2_Pow_3() {
    type A = UInt<UInt<UTerm, B1>, B0>;
    type B = UInt<UInt<UTerm, B1>, B1>;
    type U8 = UInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>, B0>;

    #[allow(non_camel_case_types)]
    type U2PowU3 = <<A as Pow<B>>::Output as Same<U8>>::Output;

    assert_eq!(<U2PowU3 as Unsigned>::to_u64(), <U8 as Unsigned>::to_u64());
}
#[test]
#[allow(non_snake_case)]
fn test_2_Min_3() {
    type A = UInt<UInt<UTerm, B1>, B0>;
    type B = UInt<UInt<UTerm, B1>, B1>;
    type U2 = UInt<UInt<UTerm, B1>, B0>;

    #[allow(non_camel_case_types)]
    type U2MinU3 = <<A as Min<B>>::Output as Same<U2>>::Output;

    assert_eq!(<U2MinU3 as Unsigned>::to_u64(), <U2 as Unsigned>::to_u64());
}
#[test]
#[allow(non_snake_case)]
fn test_2_Max_3() {
    type A = UInt<UInt<UTerm, B1>, B0>;
    type B = UInt<UInt<UTerm, B1>, B1>;
    type U3 = UInt<UInt<UTerm, B1>, B1>;

    #[allow(non_camel_case_types)]
    type U2MaxU3 = <<A as Max<B>>::Output as Same<U3>>::Output;

    assert_eq!(<U2MaxU3 as Unsigned>::to_u64(), <U3 as Unsigned>::to_u64());
}
#[test]
#[allow(non_snake_case)]
fn test_2_Gcd_3() {
    type A = UInt<UInt<UTerm, B1>, B0>;
    type B = UInt<UInt<UTerm, B1>, B1>;
    type U1 = UInt<UTerm, B1>;

    #[allow(non_camel_case_types)]
    type U2GcdU3 = <<A as Gcd<B>>::Output as Same<U1>>::Output;

    assert_eq!(<U2GcdU3 as Unsigned>::to_u64(), <U1 as Unsigned>::to_u64());
}
#[test]
#[allow(non_snake_case)]
fn test_2_Div_3() {
    type A = UInt<UInt<UTerm, B1>, B0>;
    type B = UInt<UInt<UTerm, B1>, B1>;
    type U0 = UTerm;

    #[allow(non_camel_case_types)]
    type U2DivU3 = <<A as Div<B>>::Output as Same<U0>>::Output;

    assert_eq!(<U2DivU3 as Unsigned>::to_u64(), <U0 as Unsigned>::to_u64());
}
#[test]
#[allow(non_snake_case)]
fn test_2_Rem_3() {
    type A = UInt<UInt<UTerm, B1>, B0>;
    type B = UInt<UInt<UTerm, B1>, B1>;
    type U2 = UInt<UInt<UTerm, B1>, B0>;

    #[allow(non_camel_case_types)]
    type U2RemU3 = <<A as Rem<B>>::Output as Same<U2>>::Output;

    assert_eq!(<U2RemU3 as Unsigned>::to_u64(), <U2 as Unsigned>::to_u64());
}
#[test]
#[allow(non_snake_case)]
fn test_2_Cmp_3() {
    type A = UInt<UInt<UTerm, B1>, B0>;
    type B = UInt<UInt<UTerm, B1>, B1>;

    #[allow(non_camel_case_types)]
    type U2CmpU3 = <A as Cmp<B>>::Output;
    assert_eq!(<U2CmpU3 as Ord>::to_ordering(), Ordering::Less);
}
#[test]
#[allow(non_snake_case)]
fn test_2_BitAnd_4() {
    type A = UInt<UInt<UTerm, B1>, B0>;
    type B = UInt<UInt<UInt<UTerm, B1>, B0>, B0>;
    type U0 = UTerm;

    #[allow(non_camel_case_types)]
    type U2BitAndU4 = <<A as BitAnd<B>>::Output as Same<U0>>::Output;

    assert_eq!(<U2BitAndU4 as Unsigned>::to_u64(), <U0 as Unsigned>::to_u64());
}
#[test]
#[allow(non_snake_case)]
fn test_2_BitOr_4() {
    type A = UInt<UInt<UTerm, B1>, B0>;
    type B = UInt<UInt<UInt<UTerm, B1>, B0>, B0>;
    type U6 = UInt<UInt<UInt<UTerm, B1>, B1>, B0>;

    #[allow(non_camel_case_types)]
    type U2BitOrU4 = <<A as BitOr<B>>::Output as Same<U6>>::Output;

    assert_eq!(<U2BitOrU4 as Unsigned>::to_u64(), <U6 as Unsigned>::to_u64());
}
#[test]
#[allow(non_snake_case)]
fn test_2_BitXor_4() {
    type A = UInt<UInt<UTerm, B1>, B0>;
    type B = UInt<UInt<UInt<UTerm, B1>, B0>, B0>;
    type U6 = UInt<UInt<UInt<UTerm, B1>, B1>, B0>;

    #[allow(non_camel_case_types)]
    type U2BitXorU4 = <<A as BitXor<B>>::Output as Same<U6>>::Output;

    assert_eq!(<U2BitXorU4 as Unsigned>::to_u64(), <U6 as Unsigned>::to_u64());
}
#[test]
#[allow(non_snake_case)]
fn test_2_Shl_4() {
    type A = UInt<UInt<UTerm, B1>, B0>;
    type B = UInt<UInt<UInt<UTerm, B1>, B0>, B0>;
    type U32 = UInt<UInt<UInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>, B0>, B0>, B0>;

    #[allow(non_camel_case_types)]
    type U2ShlU4 = <<A as Shl<B>>::Output as Same<U32>>::Output;

    assert_eq!(<U2ShlU4 as Unsigned>::to_u64(), <U32 as Unsigned>::to_u64());
}
#[test]
#[allow(non_snake_case)]
fn test_2_Shr_4() {
    type A = UInt<UInt<UTerm, B1>, B0>;
    type B = UInt<UInt<UInt<UTerm, B1>, B0>, B0>;
    type U0 = UTerm;

    #[allow(non_camel_case_types)]
    type U2ShrU4 = <<A as Shr<B>>::Output as Same<U0>>::Output;

    assert_eq!(<U2ShrU4 as Unsigned>::to_u64(), <U0 as Unsigned>::to_u64());
}
#[test]
#[allow(non_snake_case)]
fn test_2_Add_4() {
    type A = UInt<UInt<UTerm, B1>, B0>;
    type B = UInt<UInt<UInt<UTerm, B1>, B0>, B0>;
    type U6 = UInt<UInt<UInt<UTerm, B1>, B1>, B0>;

    #[allow(non_camel_case_types)]
    type U2AddU4 = <<A as Add<B>>::Output as Same<U6>>::Output;

    assert_eq!(<U2AddU4 as Unsigned>::to_u64(), <U6 as Unsigned>::to_u64());
}
#[test]
#[allow(non_snake_case)]
fn test_2_Mul_4() {
    type A = UInt<UInt<UTerm, B1>, B0>;
    type B = UInt<UInt<UInt<UTerm, B1>, B0>, B0>;
    type U8 = UInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>, B0>;

    #[allow(non_camel_case_types)]
    type U2MulU4 = <<A as Mul<B>>::Output as Same<U8>>::Output;

    assert_eq!(<U2MulU4 as Unsigned>::to_u64(), <U8 as Unsigned>::to_u64());
}
#[test]
#[allow(non_snake_case)]
fn test_2_Pow_4() {
    type A = UInt<UInt<UTerm, B1>, B0>;
    type B = UInt<UInt<UInt<UTerm, B1>, B0>, B0>;
    type U16 = UInt<UInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>, B0>, B0>;

    #[allow(non_camel_case_types)]
    type U2PowU4 = <<A as Pow<B>>::Output as Same<U16>>::Output;

    assert_eq!(<U2PowU4 as Unsigned>::to_u64(), <U16 as Unsigned>::to_u64());
}
#[test]
#[allow(non_snake_case)]
fn test_2_Min_4() {
    type A = UInt<UInt<UTerm, B1>, B0>;
    type B = UInt<UInt<UInt<UTerm, B1>, B0>, B0>;
    type U2 = UInt<UInt<UTerm, B1>, B0>;

    #[allow(non_camel_case_types)]
    type U2MinU4 = <<A as Min<B>>::Output as Same<U2>>::Output;

    assert_eq!(<U2MinU4 as Unsigned>::to_u64(), <U2 as Unsigned>::to_u64());
}
#[test]
#[allow(non_snake_case)]
fn test_2_Max_4() {
    type A = UInt<UInt<UTerm, B1>, B0>;
    type B = UInt<UInt<UInt<UTerm, B1>, B0>, B0>;
    type U4 = UInt<UInt<UInt<UTerm, B1>, B0>, B0>;

    #[allow(non_camel_case_types)]
    type U2MaxU4 = <<A as Max<B>>::Output as Same<U4>>::Output;

    assert_eq!(<U2MaxU4 as Unsigned>::to_u64(), <U4 as Unsigned>::to_u64());
}
#[test]
#[allow(non_snake_case)]
fn test_2_Gcd_4() {
    type A = UInt<UInt<UTerm, B1>, B0>;
    type B = UInt<UInt<UInt<UTerm, B1>, B0>, B0>;
    type U2 = UInt<UInt<UTerm, B1>, B0>;

    #[allow(non_camel_case_types)]
    type U2GcdU4 = <<A as Gcd<B>>::Output as Same<U2>>::Output;

    assert_eq!(<U2GcdU4 as Unsigned>::to_u64(), <U2 as Unsigned>::to_u64());
}
#[test]
#[allow(non_snake_case)]
fn test_2_Div_4() {
    type A = UInt<UInt<UTerm, B1>, B0>;
    type B = UInt<UInt<UInt<UTerm, B1>, B0>, B0>;
    type U0 = UTerm;

    #[allow(non_camel_case_types)]
    type U2DivU4 = <<A as Div<B>>::Output as Same<U0>>::Output;

    assert_eq!(<U2DivU4 as Unsigned>::to_u64(), <U0 as Unsigned>::to_u64());
}
#[test]
#[allow(non_snake_case)]
fn test_2_Rem_4() {
    type A = UInt<UInt<UTerm, B1>, B0>;
    type B = UInt<UInt<UInt<UTerm, B1>, B0>, B0>;
    type U2 = UInt<UInt<UTerm, B1>, B0>;

    #[allow(non_camel_case_types)]
    type U2RemU4 = <<A as Rem<B>>::Output as Same<U2>>::Output;

    assert_eq!(<U2RemU4 as Unsigned>::to_u64(), <U2 as Unsigned>::to_u64());
}
#[test]
#[allow(non_snake_case)]
fn test_2_Cmp_4() {
    type A = UInt<UInt<UTerm, B1>, B0>;
    type B = UInt<UInt<UInt<UTerm, B1>, B0>, B0>;

    #[allow(non_camel_case_types)]
    type U2CmpU4 = <A as Cmp<B>>::Output;
    assert_eq!(<U2CmpU4 as Ord>::to_ordering(), Ordering::Less);
}
#[test]
#[allow(non_snake_case)]
fn test_2_BitAnd_5() {
    type A = UInt<UInt<UTerm, B1>, B0>;
    type B = UInt<UInt<UInt<UTerm, B1>, B0>, B1>;
    type U0 = UTerm;

    #[allow(non_camel_case_types)]
    type U2BitAndU5 = <<A as BitAnd<B>>::Output as Same<U0>>::Output;

    assert_eq!(<U2BitAndU5 as Unsigned>::to_u64(), <U0 as Unsigned>::to_u64());
}
#[test]
#[allow(non_snake_case)]
fn test_2_BitOr_5() {
    type A = UInt<UInt<UTerm, B1>, B0>;
    type B = UInt<UInt<UInt<UTerm, B1>, B0>, B1>;
    type U7 = UInt<UInt<UInt<UTerm, B1>, B1>, B1>;

    #[allow(non_camel_case_types)]
    type U2BitOrU5 = <<A as BitOr<B>>::Output as Same<U7>>::Output;

    assert_eq!(<U2BitOrU5 as Unsigned>::to_u64(), <U7 as Unsigned>::to_u64());
}
#[test]
#[allow(non_snake_case)]
fn test_2_BitXor_5() {
    type A = UInt<UInt<UTerm, B1>, B0>;
    type B = UInt<UInt<UInt<UTerm, B1>, B0>, B1>;
    type U7 = UInt<UInt<UInt<UTerm, B1>, B1>, B1>;

    #[allow(non_camel_case_types)]
    type U2BitXorU5 = <<A as BitXor<B>>::Output as Same<U7>>::Output;

    assert_eq!(<U2BitXorU5 as Unsigned>::to_u64(), <U7 as Unsigned>::to_u64());
}
#[test]
#[allow(non_snake_case)]
fn test_2_Shl_5() {
    type A = UInt<UInt<UTerm, B1>, B0>;
    type B = UInt<UInt<UInt<UTerm, B1>, B0>, B1>;
    type U64 = UInt<UInt<UInt<UInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>, B0>, B0>, B0>, B0>;

    #[allow(non_camel_case_types)]
    type U2ShlU5 = <<A as Shl<B>>::Output as Same<U64>>::Output;

    assert_eq!(<U2ShlU5 as Unsigned>::to_u64(), <U64 as Unsigned>::to_u64());
}
#[test]
#[allow(non_snake_case)]
fn test_2_Shr_5() {
    type A = UInt<UInt<UTerm, B1>, B0>;
    type B = UInt<UInt<UInt<UTerm, B1>, B0>, B1>;
    type U0 = UTerm;

    #[allow(non_camel_case_types)]
    type U2ShrU5 = <<A as Shr<B>>::Output as Same<U0>>::Output;

    assert_eq!(<U2ShrU5 as Unsigned>::to_u64(), <U0 as Unsigned>::to_u64());
}
#[test]
#[allow(non_snake_case)]
fn test_2_Add_5() {
    type A = UInt<UInt<UTerm, B1>, B0>;
    type B = UInt<UInt<UInt<UTerm, B1>, B0>, B1>;
    type U7 = UInt<UInt<UInt<UTerm, B1>, B1>, B1>;

    #[allow(non_camel_case_types)]
    type U2AddU5 = <<A as Add<B>>::Output as Same<U7>>::Output;

    assert_eq!(<U2AddU5 as Unsigned>::to_u64(), <U7 as Unsigned>::to_u64());
}
#[test]
#[allow(non_snake_case)]
fn test_2_Mul_5() {
    type A = UInt<UInt<UTerm, B1>, B0>;
    type B = UInt<UInt<UInt<UTerm, B1>, B0>, B1>;
    type U10 = UInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>, B0>;

    #[allow(non_camel_case_types)]
    type U2MulU5 = <<A as Mul<B>>::Output as Same<U10>>::Output;

    assert_eq!(<U2MulU5 as Unsigned>::to_u64(), <U10 as Unsigned>::to_u64());
}
#[test]
#[allow(non_snake_case)]
fn test_2_Pow_5() {
    type A = UInt<UInt<UTerm, B1>, B0>;
    type B = UInt<UInt<UInt<UTerm, B1>, B0>, B1>;
    type U32 = UInt<UInt<UInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>, B0>, B0>, B0>;

    #[allow(non_camel_case_types)]
    type U2PowU5 = <<A as Pow<B>>::Output as Same<U32>>::Output;

    assert_eq!(<U2PowU5 as Unsigned>::to_u64(), <U32 as Unsigned>::to_u64());
}
#[test]
#[allow(non_snake_case)]
fn test_2_Min_5() {
    type A = UInt<UInt<UTerm, B1>, B0>;
    type B = UInt<UInt<UInt<UTerm, B1>, B0>, B1>;
    type U2 = UInt<UInt<UTerm, B1>, B0>;

    #[allow(non_camel_case_types)]
    type U2MinU5 = <<A as Min<B>>::Output as Same<U2>>::Output;

    assert_eq!(<U2MinU5 as Unsigned>::to_u64(), <U2 as Unsigned>::to_u64());
}
#[test]
#[allow(non_snake_case)]
fn test_2_Max_5() {
    type A = UInt<UInt<UTerm, B1>, B0>;
    type B = UInt<UInt<UInt<UTerm, B1>, B0>, B1>;
    type U5 = UInt<UInt<UInt<UTerm, B1>, B0>, B1>;

    #[allow(non_camel_case_types)]
    type U2MaxU5 = <<A as Max<B>>::Output as Same<U5>>::Output;

    assert_eq!(<U2MaxU5 as Unsigned>::to_u64(), <U5 as Unsigned>::to_u64());
}
#[test]
#[allow(non_snake_case)]
fn test_2_Gcd_5() {
    type A = UInt<UInt<UTerm, B1>, B0>;
    type B = UInt<UInt<UInt<UTerm, B1>, B0>, B1>;
    type U1 = UInt<UTerm, B1>;

    #[allow(non_camel_case_types)]
    type U2GcdU5 = <<A as Gcd<B>>::Output as Same<U1>>::Output;

    assert_eq!(<U2GcdU5 as Unsigned>::to_u64(), <U1 as Unsigned>::to_u64());
}
#[test]
#[allow(non_snake_case)]
fn test_2_Div_5() {
    type A = UInt<UInt<UTerm, B1>, B0>;
    type B = UInt<UInt<UInt<UTerm, B1>, B0>, B1>;
    type U0 = UTerm;

    #[allow(non_camel_case_types)]
    type U2DivU5 = <<A as Div<B>>::Output as Same<U0>>::Output;

    assert_eq!(<U2DivU5 as Unsigned>::to_u64(), <U0 as Unsigned>::to_u64());
}
#[test]
#[allow(non_snake_case)]
fn test_2_Rem_5() {
    type A = UInt<UInt<UTerm, B1>, B0>;
    type B = UInt<UInt<UInt<UTerm, B1>, B0>, B1>;
    type U2 = UInt<UInt<UTerm, B1>, B0>;

    #[allow(non_camel_case_types)]
    type U2RemU5 = <<A as Rem<B>>::Output as Same<U2>>::Output;

    assert_eq!(<U2RemU5 as Unsigned>::to_u64(), <U2 as Unsigned>::to_u64());
}
#[test]
#[allow(non_snake_case)]
fn test_2_Cmp_5() {
    type A = UInt<UInt<UTerm, B1>, B0>;
    type B = UInt<UInt<UInt<UTerm, B1>, B0>, B1>;

    #[allow(non_camel_case_types)]
    type U2CmpU5 = <A as Cmp<B>>::Output;
    assert_eq!(<U2CmpU5 as Ord>::to_ordering(), Ordering::Less);
}
#[test]
#[allow(non_snake_case)]
fn test_3_BitAnd_0() {
    type A = UInt<UInt<UTerm, B1>, B1>;
    type B = UTerm;
    type U0 = UTerm;

    #[allow(non_camel_case_types)]
    type U3BitAndU0 = <<A as BitAnd<B>>::Output as Same<U0>>::Output;

    assert_eq!(<U3BitAndU0 as Unsigned>::to_u64(), <U0 as Unsigned>::to_u64());
}
#[test]
#[allow(non_snake_case)]
fn test_3_BitOr_0() {
    type A = UInt<UInt<UTerm, B1>, B1>;
    type B = UTerm;
    type U3 = UInt<UInt<UTerm, B1>, B1>;

    #[allow(non_camel_case_types)]
    type U3BitOrU0 = <<A as BitOr<B>>::Output as Same<U3>>::Output;

    assert_eq!(<U3BitOrU0 as Unsigned>::to_u64(), <U3 as Unsigned>::to_u64());
}
#[test]
#[allow(non_snake_case)]
fn test_3_BitXor_0() {
    type A = UInt<UInt<UTerm, B1>, B1>;
    type B = UTerm;
    type U3 = UInt<UInt<UTerm, B1>, B1>;

    #[allow(non_camel_case_types)]
    type U3BitXorU0 = <<A as BitXor<B>>::Output as Same<U3>>::Output;

    assert_eq!(<U3BitXorU0 as Unsigned>::to_u64(), <U3 as Unsigned>::to_u64());
}
#[test]
#[allow(non_snake_case)]
fn test_3_Shl_0() {
    type A = UInt<UInt<UTerm, B1>, B1>;
    type B = UTerm;
    type U3 = UInt<UInt<UTerm, B1>, B1>;

    #[allow(non_camel_case_types)]
    type U3ShlU0 = <<A as Shl<B>>::Output as Same<U3>>::Output;

    assert_eq!(<U3ShlU0 as Unsigned>::to_u64(), <U3 as Unsigned>::to_u64());
}
#[test]
#[allow(non_snake_case)]
fn test_3_Shr_0() {
    type A = UInt<UInt<UTerm, B1>, B1>;
    type B = UTerm;
    type U3 = UInt<UInt<UTerm, B1>, B1>;

    #[allow(non_camel_case_types)]
    type U3ShrU0 = <<A as Shr<B>>::Output as Same<U3>>::Output;

    assert_eq!(<U3ShrU0 as Unsigned>::to_u64(), <U3 as Unsigned>::to_u64());
}
#[test]
#[allow(non_snake_case)]
fn test_3_Add_0() {
    type A = UInt<UInt<UTerm, B1>, B1>;
    type B = UTerm;
    type U3 = UInt<UInt<UTerm, B1>, B1>;

    #[allow(non_camel_case_types)]
    type U3AddU0 = <<A as Add<B>>::Output as Same<U3>>::Output;

    assert_eq!(<U3AddU0 as Unsigned>::to_u64(), <U3 as Unsigned>::to_u64());
}
#[test]
#[allow(non_snake_case)]
fn test_3_Mul_0() {
    type A = UInt<UInt<UTerm, B1>, B1>;
    type B = UTerm;
    type U0 = UTerm;

    #[allow(non_camel_case_types)]
    type U3MulU0 = <<A as Mul<B>>::Output as Same<U0>>::Output;

    assert_eq!(<U3MulU0 as Unsigned>::to_u64(), <U0 as Unsigned>::to_u64());
}
#[test]
#[allow(non_snake_case)]
fn test_3_Pow_0() {
    type A = UInt<UInt<UTerm, B1>, B1>;
    type B = UTerm;
    type U1 = UInt<UTerm, B1>;

    #[allow(non_camel_case_types)]
    type U3PowU0 = <<A as Pow<B>>::Output as Same<U1>>::Output;

    assert_eq!(<U3PowU0 as Unsigned>::to_u64(), <U1 as Unsigned>::to_u64());
}
#[test]
#[allow(non_snake_case)]
fn test_3_Min_0() {
    type A = UInt<UInt<UTerm, B1>, B1>;
    type B = UTerm;
    type U0 = UTerm;

    #[allow(non_camel_case_types)]
    type U3MinU0 = <<A as Min<B>>::Output as Same<U0>>::Output;

    assert_eq!(<U3MinU0 as Unsigned>::to_u64(), <U0 as Unsigned>::to_u64());
}
#[test]
#[allow(non_snake_case)]
fn test_3_Max_0() {
    type A = UInt<UInt<UTerm, B1>, B1>;
    type B = UTerm;
    type U3 = UInt<UInt<UTerm, B1>, B1>;

    #[allow(non_camel_case_types)]
    type U3MaxU0 = <<A as Max<B>>::Output as Same<U3>>::Output;

    assert_eq!(<U3MaxU0 as Unsigned>::to_u64(), <U3 as Unsigned>::to_u64());
}
#[test]
#[allow(non_snake_case)]
fn test_3_Gcd_0() {
    type A = UInt<UInt<UTerm, B1>, B1>;
    type B = UTerm;
    type U3 = UInt<UInt<UTerm, B1>, B1>;

    #[allow(non_camel_case_types)]
    type U3GcdU0 = <<A as Gcd<B>>::Output as Same<U3>>::Output;

    assert_eq!(<U3GcdU0 as Unsigned>::to_u64(), <U3 as Unsigned>::to_u64());
}
#[test]
#[allow(non_snake_case)]
fn test_3_Sub_0() {
    type A = UInt<UInt<UTerm, B1>, B1>;
    type B = UTerm;
    type U3 = UInt<UInt<UTerm, B1>, B1>;

    #[allow(non_camel_case_types)]
    type U3SubU0 = <<A as Sub<B>>::Output as Same<U3>>::Output;

    assert_eq!(<U3SubU0 as Unsigned>::to_u64(), <U3 as Unsigned>::to_u64());
}
#[test]
#[allow(non_snake_case)]
fn test_3_Cmp_0() {
    type A = UInt<UInt<UTerm, B1>, B1>;
    type B = UTerm;

    #[allow(non_camel_case_types)]
    type U3CmpU0 = <A as Cmp<B>>::Output;
    assert_eq!(<U3CmpU0 as Ord>::to_ordering(), Ordering::Greater);
}
#[test]
#[allow(non_snake_case)]
fn test_3_BitAnd_1() {
    type A = UInt<UInt<UTerm, B1>, B1>;
    type B = UInt<UTerm, B1>;
    type U1 = UInt<UTerm, B1>;

    #[allow(non_camel_case_types)]
    type U3BitAndU1 = <<A as BitAnd<B>>::Output as Same<U1>>::Output;

    assert_eq!(<U3BitAndU1 as Unsigned>::to_u64(), <U1 as Unsigned>::to_u64());
}
#[test]
#[allow(non_snake_case)]
fn test_3_BitOr_1() {
    type A = UInt<UInt<UTerm, B1>, B1>;
    type B = UInt<UTerm, B1>;
    type U3 = UInt<UInt<UTerm, B1>, B1>;

    #[allow(non_camel_case_types)]
    type U3BitOrU1 = <<A as BitOr<B>>::Output as Same<U3>>::Output;

    assert_eq!(<U3BitOrU1 as Unsigned>::to_u64(), <U3 as Unsigned>::to_u64());
}
#[test]
#[allow(non_snake_case)]
fn test_3_BitXor_1() {
    type A = UInt<UInt<UTerm, B1>, B1>;
    type B = UInt<UTerm, B1>;
    type U2 = UInt<UInt<UTerm, B1>, B0>;

    #[allow(non_camel_case_types)]
    type U3BitXorU1 = <<A as BitXor<B>>::Output as Same<U2>>::Output;

    assert_eq!(<U3BitXorU1 as Unsigned>::to_u64(), <U2 as Unsigned>::to_u64());
}
#[test]
#[allow(non_snake_case)]
fn test_3_Shl_1() {
    type A = UInt<UInt<UTerm, B1>, B1>;
    type B = UInt<UTerm, B1>;
    type U6 = UInt<UInt<UInt<UTerm, B1>, B1>, B0>;

    #[allow(non_camel_case_types)]
    type U3ShlU1 = <<A as Shl<B>>::Output as Same<U6>>::Output;

    assert_eq!(<U3ShlU1 as Unsigned>::to_u64(), <U6 as Unsigned>::to_u64());
}
#[test]
#[allow(non_snake_case)]
fn test_3_Shr_1() {
    type A = UInt<UInt<UTerm, B1>, B1>;
    type B = UInt<UTerm, B1>;
    type U1 = UInt<UTerm, B1>;

    #[allow(non_camel_case_types)]
    type U3ShrU1 = <<A as Shr<B>>::Output as Same<U1>>::Output;

    assert_eq!(<U3ShrU1 as Unsigned>::to_u64(), <U1 as Unsigned>::to_u64());
}
#[test]
#[allow(non_snake_case)]
fn test_3_Add_1() {
    type A = UInt<UInt<UTerm, B1>, B1>;
    type B = UInt<UTerm, B1>;
    type U4 = UInt<UInt<UInt<UTerm, B1>, B0>, B0>;

    #[allow(non_camel_case_types)]
    type U3AddU1 = <<A as Add<B>>::Output as Same<U4>>::Output;

    assert_eq!(<U3AddU1 as Unsigned>::to_u64(), <U4 as Unsigned>::to_u64());
}
#[test]
#[allow(non_snake_case)]
fn test_3_Mul_1() {
    type A = UInt<UInt<UTerm, B1>, B1>;
    type B = UInt<UTerm, B1>;
    type U3 = UInt<UInt<UTerm, B1>, B1>;

    #[allow(non_camel_case_types)]
    type U3MulU1 = <<A as Mul<B>>::Output as Same<U3>>::Output;

    assert_eq!(<U3MulU1 as Unsigned>::to_u64(), <U3 as Unsigned>::to_u64());
}
#[test]
#[allow(non_snake_case)]
fn test_3_Pow_1() {
    type A = UInt<UInt<UTerm, B1>, B1>;
    type B = UInt<UTerm, B1>;
    type U3 = UInt<UInt<UTerm, B1>, B1>;

    #[allow(non_camel_case_types)]
    type U3PowU1 = <<A as Pow<B>>::Output as Same<U3>>::Output;

    assert_eq!(<U3PowU1 as Unsigned>::to_u64(), <U3 as Unsigned>::to_u64());
}
#[test]
#[allow(non_snake_case)]
fn test_3_Min_1() {
    type A = UInt<UInt<UTerm, B1>, B1>;
    type B = UInt<UTerm, B1>;
    type U1 = UInt<UTerm, B1>;

    #[allow(non_camel_case_types)]
    type U3MinU1 = <<A as Min<B>>::Output as Same<U1>>::Output;

    assert_eq!(<U3MinU1 as Unsigned>::to_u64(), <U1 as Unsigned>::to_u64());
}
#[test]
#[allow(non_snake_case)]
fn test_3_Max_1() {
    type A = UInt<UInt<UTerm, B1>, B1>;
    type B = UInt<UTerm, B1>;
    type U3 = UInt<UInt<UTerm, B1>, B1>;

    #[allow(non_camel_case_types)]
    type U3MaxU1 = <<A as Max<B>>::Output as Same<U3>>::Output;

    assert_eq!(<U3MaxU1 as Unsigned>::to_u64(), <U3 as Unsigned>::to_u64());
}
#[test]
#[allow(non_snake_case)]
fn test_3_Gcd_1() {
    type A = UInt<UInt<UTerm, B1>, B1>;
    type B = UInt<UTerm, B1>;
    type U1 = UInt<UTerm, B1>;

    #[allow(non_camel_case_types)]
    type U3GcdU1 = <<A as Gcd<B>>::Output as Same<U1>>::Output;

    assert_eq!(<U3GcdU1 as Unsigned>::to_u64(), <U1 as Unsigned>::to_u64());
}
#[test]
#[allow(non_snake_case)]
fn test_3_Sub_1() {
    type A = UInt<UInt<UTerm, B1>, B1>;
    type B = UInt<UTerm, B1>;
    type U2 = UInt<UInt<UTerm, B1>, B0>;

    #[allow(non_camel_case_types)]
    type U3SubU1 = <<A as Sub<B>>::Output as Same<U2>>::Output;

    assert_eq!(<U3SubU1 as Unsigned>::to_u64(), <U2 as Unsigned>::to_u64());
}
#[test]
#[allow(non_snake_case)]
fn test_3_Div_1() {
    type A = UInt<UInt<UTerm, B1>, B1>;
    type B = UInt<UTerm, B1>;
    type U3 = UInt<UInt<UTerm, B1>, B1>;

    #[allow(non_camel_case_types)]
    type U3DivU1 = <<A as Div<B>>::Output as Same<U3>>::Output;

    assert_eq!(<U3DivU1 as Unsigned>::to_u64(), <U3 as Unsigned>::to_u64());
}
#[test]
#[allow(non_snake_case)]
fn test_3_Rem_1() {
    type A = UInt<UInt<UTerm, B1>, B1>;
    type B = UInt<UTerm, B1>;
    type U0 = UTerm;

    #[allow(non_camel_case_types)]
    type U3RemU1 = <<A as Rem<B>>::Output as Same<U0>>::Output;

    assert_eq!(<U3RemU1 as Unsigned>::to_u64(), <U0 as Unsigned>::to_u64());
}
#[test]
#[allow(non_snake_case)]
fn test_3_PartialDiv_1() {
    type A = UInt<UInt<UTerm, B1>, B1>;
    type B = UInt<UTerm, B1>;
    type U3 = UInt<UInt<UTerm, B1>, B1>;

    #[allow(non_camel_case_types)]
    type U3PartialDivU1 = <<A as PartialDiv<B>>::Output as Same<U3>>::Output;

    assert_eq!(<U3PartialDivU1 as Unsigned>::to_u64(), <U3 as Unsigned>::to_u64());
}
#[test]
#[allow(non_snake_case)]
fn test_3_Cmp_1() {
    type A = UInt<UInt<UTerm, B1>, B1>;
    type B = UInt<UTerm, B1>;

    #[allow(non_camel_case_types)]
    type U3CmpU1 = <A as Cmp<B>>::Output;
    assert_eq!(<U3CmpU1 as Ord>::to_ordering(), Ordering::Greater);
}
#[test]
#[allow(non_snake_case)]
fn test_3_BitAnd_2() {
    type A = UInt<UInt<UTerm, B1>, B1>;
    type B = UInt<UInt<UTerm, B1>, B0>;
    type U2 = UInt<UInt<UTerm, B1>, B0>;

    #[allow(non_camel_case_types)]
    type U3BitAndU2 = <<A as BitAnd<B>>::Output as Same<U2>>::Output;

    assert_eq!(<U3BitAndU2 as Unsigned>::to_u64(), <U2 as Unsigned>::to_u64());
}
#[test]
#[allow(non_snake_case)]
fn test_3_BitOr_2() {
    type A = UInt<UInt<UTerm, B1>, B1>;
    type B = UInt<UInt<UTerm, B1>, B0>;
    type U3 = UInt<UInt<UTerm, B1>, B1>;

    #[allow(non_camel_case_types)]
    type U3BitOrU2 = <<A as BitOr<B>>::Output as Same<U3>>::Output;

    assert_eq!(<U3BitOrU2 as Unsigned>::to_u64(), <U3 as Unsigned>::to_u64());
}
#[test]
#[allow(non_snake_case)]
fn test_3_BitXor_2() {
    type A = UInt<UInt<UTerm, B1>, B1>;
    type B = UInt<UInt<UTerm, B1>, B0>;
    type U1 = UInt<UTerm, B1>;

    #[allow(non_camel_case_types)]
    type U3BitXorU2 = <<A as BitXor<B>>::Output as Same<U1>>::Output;

    assert_eq!(<U3BitXorU2 as Unsigned>::to_u64(), <U1 as Unsigned>::to_u64());
}
#[test]
#[allow(non_snake_case)]
fn test_3_Shl_2() {
    type A = UInt<UInt<UTerm, B1>, B1>;
    type B = UInt<UInt<UTerm, B1>, B0>;
    type U12 = UInt<UInt<UInt<UInt<UTerm, B1>, B1>, B0>, B0>;

    #[allow(non_camel_case_types)]
    type U3ShlU2 = <<A as Shl<B>>::Output as Same<U12>>::Output;

    assert_eq!(<U3ShlU2 as Unsigned>::to_u64(), <U12 as Unsigned>::to_u64());
}
#[test]
#[allow(non_snake_case)]
fn test_3_Shr_2() {
    type A = UInt<UInt<UTerm, B1>, B1>;
    type B = UInt<UInt<UTerm, B1>, B0>;
    type U0 = UTerm;

    #[allow(non_camel_case_types)]
    type U3ShrU2 = <<A as Shr<B>>::Output as Same<U0>>::Output;

    assert_eq!(<U3ShrU2 as Unsigned>::to_u64(), <U0 as Unsigned>::to_u64());
}
#[test]
#[allow(non_snake_case)]
fn test_3_Add_2() {
    type A = UInt<UInt<UTerm, B1>, B1>;
    type B = UInt<UInt<UTerm, B1>, B0>;
    type U5 = UInt<UInt<UInt<UTerm, B1>, B0>, B1>;

    #[allow(non_camel_case_types)]
    type U3AddU2 = <<A as Add<B>>::Output as Same<U5>>::Output;

    assert_eq!(<U3AddU2 as Unsigned>::to_u64(), <U5 as Unsigned>::to_u64());
}
#[test]
#[allow(non_snake_case)]
fn test_3_Mul_2() {
    type A = UInt<UInt<UTerm, B1>, B1>;
    type B = UInt<UInt<UTerm, B1>, B0>;
    type U6 = UInt<UInt<UInt<UTerm, B1>, B1>, B0>;

    #[allow(non_camel_case_types)]
    type U3MulU2 = <<A as Mul<B>>::Output as Same<U6>>::Output;

    assert_eq!(<U3MulU2 as Unsigned>::to_u64(), <U6 as Unsigned>::to_u64());
}
#[test]
#[allow(non_snake_case)]
fn test_3_Pow_2() {
    type A = UInt<UInt<UTerm, B1>, B1>;
    type B = UInt<UInt<UTerm, B1>, B0>;
    type U9 = UInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>, B1>;

    #[allow(non_camel_case_types)]
    type U3PowU2 = <<A as Pow<B>>::Output as Same<U9>>::Output;

    assert_eq!(<U3PowU2 as Unsigned>::to_u64(), <U9 as Unsigned>::to_u64());
}
#[test]
#[allow(non_snake_case)]
fn test_3_Min_2() {
    type A = UInt<UInt<UTerm, B1>, B1>;
    type B = UInt<UInt<UTerm, B1>, B0>;
    type U2 = UInt<UInt<UTerm, B1>, B0>;

    #[allow(non_camel_case_types)]
    type U3MinU2 = <<A as Min<B>>::Output as Same<U2>>::Output;

    assert_eq!(<U3MinU2 as Unsigned>::to_u64(), <U2 as Unsigned>::to_u64());
}
#[test]
#[allow(non_snake_case)]
fn test_3_Max_2() {
    type A = UInt<UInt<UTerm, B1>, B1>;
    type B = UInt<UInt<UTerm, B1>, B0>;
    type U3 = UInt<UInt<UTerm, B1>, B1>;

    #[allow(non_camel_case_types)]
    type U3MaxU2 = <<A as Max<B>>::Output as Same<U3>>::Output;

    assert_eq!(<U3MaxU2 as Unsigned>::to_u64(), <U3 as Unsigned>::to_u64());
}
#[test]
#[allow(non_snake_case)]
fn test_3_Gcd_2() {
    type A = UInt<UInt<UTerm, B1>, B1>;
    type B = UInt<UInt<UTerm, B1>, B0>;
    type U1 = UInt<UTerm, B1>;

    #[allow(non_camel_case_types)]
    type U3GcdU2 = <<A as Gcd<B>>::Output as Same<U1>>::Output;

    assert_eq!(<U3GcdU2 as Unsigned>::to_u64(), <U1 as Unsigned>::to_u64());
}
#[test]
#[allow(non_snake_case)]
fn test_3_Sub_2() {
    type A = UInt<UInt<UTerm, B1>, B1>;
    type B = UInt<UInt<UTerm, B1>, B0>;
    type U1 = UInt<UTerm, B1>;

    #[allow(non_camel_case_types)]
    type U3SubU2 = <<A as Sub<B>>::Output as Same<U1>>::Output;

    assert_eq!(<U3SubU2 as Unsigned>::to_u64(), <U1 as Unsigned>::to_u64());
}
#[test]
#[allow(non_snake_case)]
fn test_3_Div_2() {
    type A = UInt<UInt<UTerm, B1>, B1>;
    type B = UInt<UInt<UTerm, B1>, B0>;
    type U1 = UInt<UTerm, B1>;

    #[allow(non_camel_case_types)]
    type U3DivU2 = <<A as Div<B>>::Output as Same<U1>>::Output;

    assert_eq!(<U3DivU2 as Unsigned>::to_u64(), <U1 as Unsigned>::to_u64());
}
#[test]
#[allow(non_snake_case)]
fn test_3_Rem_2() {
    type A = UInt<UInt<UTerm, B1>, B1>;
    type B = UInt<UInt<UTerm, B1>, B0>;
    type U1 = UInt<UTerm, B1>;

    #[allow(non_camel_case_types)]
    type U3RemU2 = <<A as Rem<B>>::Output as Same<U1>>::Output;

    assert_eq!(<U3RemU2 as Unsigned>::to_u64(), <U1 as Unsigned>::to_u64());
}
#[test]
#[allow(non_snake_case)]
fn test_3_Cmp_2() {
    type A = UInt<UInt<UTerm, B1>, B1>;
    type B = UInt<UInt<UTerm, B1>, B0>;

    #[allow(non_camel_case_types)]
    type U3CmpU2 = <A as Cmp<B>>::Output;
    assert_eq!(<U3CmpU2 as Ord>::to_ordering(), Ordering::Greater);
}
#[test]
#[allow(non_snake_case)]
fn test_3_BitAnd_3() {
    type A = UInt<UInt<UTerm, B1>, B1>;
    type B = UInt<UInt<UTerm, B1>, B1>;
    type U3 = UInt<UInt<UTerm, B1>, B1>;

    #[allow(non_camel_case_types)]
    type U3BitAndU3 = <<A as BitAnd<B>>::Output as Same<U3>>::Output;

    assert_eq!(<U3BitAndU3 as Unsigned>::to_u64(), <U3 as Unsigned>::to_u64());
}
#[test]
#[allow(non_snake_case)]
fn test_3_BitOr_3() {
    type A = UInt<UInt<UTerm, B1>, B1>;
    type B = UInt<UInt<UTerm, B1>, B1>;
    type U3 = UInt<UInt<UTerm, B1>, B1>;

    #[allow(non_camel_case_types)]
    type U3BitOrU3 = <<A as BitOr<B>>::Output as Same<U3>>::Output;

    assert_eq!(<U3BitOrU3 as Unsigned>::to_u64(), <U3 as Unsigned>::to_u64());
}
#[test]
#[allow(non_snake_case)]
fn test_3_BitXor_3() {
    type A = UInt<UInt<UTerm, B1>, B1>;
    type B = UInt<UInt<UTerm, B1>, B1>;
    type U0 = UTerm;

    #[allow(non_camel_case_types)]
    type U3BitXorU3 = <<A as BitXor<B>>::Output as Same<U0>>::Output;

    assert_eq!(<U3BitXorU3 as Unsigned>::to_u64(), <U0 as Unsigned>::to_u64());
}
#[test]
#[allow(non_snake_case)]
fn test_3_Shl_3() {
    type A = UInt<UInt<UTerm, B1>, B1>;
    type B = UInt<UInt<UTerm, B1>, B1>;
    type U24 = UInt<UInt<UInt<UInt<UInt<UTerm, B1>, B1>, B0>, B0>, B0>;

    #[allow(non_camel_case_types)]
    type U3ShlU3 = <<A as Shl<B>>::Output as Same<U24>>::Output;

    assert_eq!(<U3ShlU3 as Unsigned>::to_u64(), <U24 as Unsigned>::to_u64());
}
#[test]
#[allow(non_snake_case)]
fn test_3_Shr_3() {
    type A = UInt<UInt<UTerm, B1>, B1>;
    type B = UInt<UInt<UTerm, B1>, B1>;
    type U0 = UTerm;

    #[allow(non_camel_case_types)]
    type U3ShrU3 = <<A as Shr<B>>::Output as Same<U0>>::Output;

    assert_eq!(<U3ShrU3 as Unsigned>::to_u64(), <U0 as Unsigned>::to_u64());
}
#[test]
#[allow(non_snake_case)]
fn test_3_Add_3() {
    type A = UInt<UInt<UTerm, B1>, B1>;
    type B = UInt<UInt<UTerm, B1>, B1>;
    type U6 = UInt<UInt<UInt<UTerm, B1>, B1>, B0>;

    #[allow(non_camel_case_types)]
    type U3AddU3 = <<A as Add<B>>::Output as Same<U6>>::Output;

    assert_eq!(<U3AddU3 as Unsigned>::to_u64(), <U6 as Unsigned>::to_u64());
}
#[test]
#[allow(non_snake_case)]
fn test_3_Mul_3() {
    type A = UInt<UInt<UTerm, B1>, B1>;
    type B = UInt<UInt<UTerm, B1>, B1>;
    type U9 = UInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>, B1>;

    #[allow(non_camel_case_types)]
    type U3MulU3 = <<A as Mul<B>>::Output as Same<U9>>::Output;

    assert_eq!(<U3MulU3 as Unsigned>::to_u64(), <U9 as Unsigned>::to_u64());
}
#[test]
#[allow(non_snake_case)]
fn test_3_Pow_3() {
    type A = UInt<UInt<UTerm, B1>, B1>;
    type B = UInt<UInt<UTerm, B1>, B1>;
    type U27 = UInt<UInt<UInt<UInt<UInt<UTerm, B1>, B1>, B0>, B1>, B1>;

    #[allow(non_camel_case_types)]
    type U3PowU3 = <<A as Pow<B>>::Output as Same<U27>>::Output;

    assert_eq!(<U3PowU3 as Unsigned>::to_u64(), <U27 as Unsigned>::to_u64());
}
#[test]
#[allow(non_snake_case)]
fn test_3_Min_3() {
    type A = UInt<UInt<UTerm, B1>, B1>;
    type B = UInt<UInt<UTerm, B1>, B1>;
    type U3 = UInt<UInt<UTerm, B1>, B1>;

    #[allow(non_camel_case_types)]
    type U3MinU3 = <<A as Min<B>>::Output as Same<U3>>::Output;

    assert_eq!(<U3MinU3 as Unsigned>::to_u64(), <U3 as Unsigned>::to_u64());
}
#[test]
#[allow(non_snake_case)]
fn test_3_Max_3() {
    type A = UInt<UInt<UTerm, B1>, B1>;
    type B = UInt<UInt<UTerm, B1>, B1>;
    type U3 = UInt<UInt<UTerm, B1>, B1>;

    #[allow(non_camel_case_types)]
    type U3MaxU3 = <<A as Max<B>>::Output as Same<U3>>::Output;

    assert_eq!(<U3MaxU3 as Unsigned>::to_u64(), <U3 as Unsigned>::to_u64());
}
#[test]
#[allow(non_snake_case)]
fn test_3_Gcd_3() {
    type A = UInt<UInt<UTerm, B1>, B1>;
    type B = UInt<UInt<UTerm, B1>, B1>;
    type U3 = UInt<UInt<UTerm, B1>, B1>;

    #[allow(non_camel_case_types)]
    type U3GcdU3 = <<A as Gcd<B>>::Output as Same<U3>>::Output;

    assert_eq!(<U3GcdU3 as Unsigned>::to_u64(), <U3 as Unsigned>::to_u64());
}
#[test]
#[allow(non_snake_case)]
fn test_3_Sub_3() {
    type A = UInt<UInt<UTerm, B1>, B1>;
    type B = UInt<UInt<UTerm, B1>, B1>;
    type U0 = UTerm;

    #[allow(non_camel_case_types)]
    type U3SubU3 = <<A as Sub<B>>::Output as Same<U0>>::Output;

    assert_eq!(<U3SubU3 as Unsigned>::to_u64(), <U0 as Unsigned>::to_u64());
}
#[test]
#[allow(non_snake_case)]
fn test_3_Div_3() {
    type A = UInt<UInt<UTerm, B1>, B1>;
    type B = UInt<UInt<UTerm, B1>, B1>;
    type U1 = UInt<UTerm, B1>;

    #[allow(non_camel_case_types)]
    type U3DivU3 = <<A as Div<B>>::Output as Same<U1>>::Output;

    assert_eq!(<U3DivU3 as Unsigned>::to_u64(), <U1 as Unsigned>::to_u64());
}
#[test]
#[allow(non_snake_case)]
fn test_3_Rem_3() {
    type A = UInt<UInt<UTerm, B1>, B1>;
    type B = UInt<UInt<UTerm, B1>, B1>;
    type U0 = UTerm;

    #[allow(non_camel_case_types)]
    type U3RemU3 = <<A as Rem<B>>::Output as Same<U0>>::Output;

    assert_eq!(<U3RemU3 as Unsigned>::to_u64(), <U0 as Unsigned>::to_u64());
}
#[test]
#[allow(non_snake_case)]
fn test_3_PartialDiv_3() {
    type A = UInt<UInt<UTerm, B1>, B1>;
    type B = UInt<UInt<UTerm, B1>, B1>;
    type U1 = UInt<UTerm, B1>;

    #[allow(non_camel_case_types)]
    type U3PartialDivU3 = <<A as PartialDiv<B>>::Output as Same<U1>>::Output;

    assert_eq!(<U3PartialDivU3 as Unsigned>::to_u64(), <U1 as Unsigned>::to_u64());
}
#[test]
#[allow(non_snake_case)]
fn test_3_Cmp_3() {
    type A = UInt<UInt<UTerm, B1>, B1>;
    type B = UInt<UInt<UTerm, B1>, B1>;

    #[allow(non_camel_case_types)]
    type U3CmpU3 = <A as Cmp<B>>::Output;
    assert_eq!(<U3CmpU3 as Ord>::to_ordering(), Ordering::Equal);
}
#[test]
#[allow(non_snake_case)]
fn test_3_BitAnd_4() {
    type A = UInt<UInt<UTerm, B1>, B1>;
    type B = UInt<UInt<UInt<UTerm, B1>, B0>, B0>;
    type U0 = UTerm;

    #[allow(non_camel_case_types)]
    type U3BitAndU4 = <<A as BitAnd<B>>::Output as Same<U0>>::Output;

    assert_eq!(<U3BitAndU4 as Unsigned>::to_u64(), <U0 as Unsigned>::to_u64());
}
#[test]
#[allow(non_snake_case)]
fn test_3_BitOr_4() {
    type A = UInt<UInt<UTerm, B1>, B1>;
    type B = UInt<UInt<UInt<UTerm, B1>, B0>, B0>;
    type U7 = UInt<UInt<UInt<UTerm, B1>, B1>, B1>;

    #[allow(non_camel_case_types)]
    type U3BitOrU4 = <<A as BitOr<B>>::Output as Same<U7>>::Output;

    assert_eq!(<U3BitOrU4 as Unsigned>::to_u64(), <U7 as Unsigned>::to_u64());
}
#[test]
#[allow(non_snake_case)]
fn test_3_BitXor_4() {
    type A = UInt<UInt<UTerm, B1>, B1>;
    type B = UInt<UInt<UInt<UTerm, B1>, B0>, B0>;
    type U7 = UInt<UInt<UInt<UTerm, B1>, B1>, B1>;

    #[allow(non_camel_case_types)]
    type U3BitXorU4 = <<A as BitXor<B>>::Output as Same<U7>>::Output;

    assert_eq!(<U3BitXorU4 as Unsigned>::to_u64(), <U7 as Unsigned>::to_u64());
}
#[test]
#[allow(non_snake_case)]
fn test_3_Shl_4() {
    type A = UInt<UInt<UTerm, B1>, B1>;
    type B = UInt<UInt<UInt<UTerm, B1>, B0>, B0>;
    type U48 = UInt<UInt<UInt<UInt<UInt<UInt<UTerm, B1>, B1>, B0>, B0>, B0>, B0>;

    #[allow(non_camel_case_types)]
    type U3ShlU4 = <<A as Shl<B>>::Output as Same<U48>>::Output;

    assert_eq!(<U3ShlU4 as Unsigned>::to_u64(), <U48 as Unsigned>::to_u64());
}
#[test]
#[allow(non_snake_case)]
fn test_3_Shr_4() {
    type A = UInt<UInt<UTerm, B1>, B1>;
    type B = UInt<UInt<UInt<UTerm, B1>, B0>, B0>;
    type U0 = UTerm;

    #[allow(non_camel_case_types)]
    type U3ShrU4 = <<A as Shr<B>>::Output as Same<U0>>::Output;

    assert_eq!(<U3ShrU4 as Unsigned>::to_u64(), <U0 as Unsigned>::to_u64());
}
#[test]
#[allow(non_snake_case)]
fn test_3_Add_4() {
    type A = UInt<UInt<UTerm, B1>, B1>;
    type B = UInt<UInt<UInt<UTerm, B1>, B0>, B0>;
    type U7 = UInt<UInt<UInt<UTerm, B1>, B1>, B1>;

    #[allow(non_camel_case_types)]
    type U3AddU4 = <<A as Add<B>>::Output as Same<U7>>::Output;

    assert_eq!(<U3AddU4 as Unsigned>::to_u64(), <U7 as Unsigned>::to_u64());
}
#[test]
#[allow(non_snake_case)]
fn test_3_Mul_4() {
    type A = UInt<UInt<UTerm, B1>, B1>;
    type B = UInt<UInt<UInt<UTerm, B1>, B0>, B0>;
    type U12 = UInt<UInt<UInt<UInt<UTerm, B1>, B1>, B0>, B0>;

    #[allow(non_camel_case_types)]
    type U3MulU4 = <<A as Mul<B>>::Output as Same<U12>>::Output;

    assert_eq!(<U3MulU4 as Unsigned>::to_u64(), <U12 as Unsigned>::to_u64());
}
#[test]
#[allow(non_snake_case)]
fn test_3_Pow_4() {
    type A = UInt<UInt<UTerm, B1>, B1>;
    type B = UInt<UInt<UInt<UTerm, B1>, B0>, B0>;
    type U81 = UInt<UInt<UInt<UInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>, B0>, B0>, B0>, B1>;

    #[allow(non_camel_case_types)]
    type U3PowU4 = <<A as Pow<B>>::Output as Same<U81>>::Output;

    assert_eq!(<U3PowU4 as Unsigned>::to_u64(), <U81 as Unsigned>::to_u64());
}
#[test]
#[allow(non_snake_case)]
fn test_3_Min_4() {
    type A = UInt<UInt<UTerm, B1>, B1>;
    type B = UInt<UInt<UInt<UTerm, B1>, B0>, B0>;
    type U3 = UInt<UInt<UTerm, B1>, B1>;

    #[allow(non_camel_case_types)]
    type U3MinU4 = <<A as Min<B>>::Output as Same<U3>>::Output;

    assert_eq!(<U3MinU4 as Unsigned>::to_u64(), <U3 as Unsigned>::to_u64());
}
#[test]
#[allow(non_snake_case)]
fn test_3_Max_4() {
    type A = UInt<UInt<UTerm, B1>, B1>;
    type B = UInt<UInt<UInt<UTerm, B1>, B0>, B0>;
    type U4 = UInt<UInt<UInt<UTerm, B1>, B0>, B0>;

    #[allow(non_camel_case_types)]
    type U3MaxU4 = <<A as Max<B>>::Output as Same<U4>>::Output;

    assert_eq!(<U3MaxU4 as Unsigned>::to_u64(), <U4 as Unsigned>::to_u64());
}
#[test]
#[allow(non_snake_case)]
fn test_3_Gcd_4() {
    type A = UInt<UInt<UTerm, B1>, B1>;
    type B = UInt<UInt<UInt<UTerm, B1>, B0>, B0>;
    type U1 = UInt<UTerm, B1>;

    #[allow(non_camel_case_types)]
    type U3GcdU4 = <<A as Gcd<B>>::Output as Same<U1>>::Output;

    assert_eq!(<U3GcdU4 as Unsigned>::to_u64(), <U1 as Unsigned>::to_u64());
}
#[test]
#[allow(non_snake_case)]
fn test_3_Div_4() {
    type A = UInt<UInt<UTerm, B1>, B1>;
    type B = UInt<UInt<UInt<UTerm, B1>, B0>, B0>;
    type U0 = UTerm;

    #[allow(non_camel_case_types)]
    type U3DivU4 = <<A as Div<B>>::Output as Same<U0>>::Output;

    assert_eq!(<U3DivU4 as Unsigned>::to_u64(), <U0 as Unsigned>::to_u64());
}
#[test]
#[allow(non_snake_case)]
fn test_3_Rem_4() {
    type A = UInt<UInt<UTerm, B1>, B1>;
    type B = UInt<UInt<UInt<UTerm, B1>, B0>, B0>;
    type U3 = UInt<UInt<UTerm, B1>, B1>;

    #[allow(non_camel_case_types)]
    type U3RemU4 = <<A as Rem<B>>::Output as Same<U3>>::Output;

    assert_eq!(<U3RemU4 as Unsigned>::to_u64(), <U3 as Unsigned>::to_u64());
}
#[test]
#[allow(non_snake_case)]
fn test_3_Cmp_4() {
    type A = UInt<UInt<UTerm, B1>, B1>;
    type B = UInt<UInt<UInt<UTerm, B1>, B0>, B0>;

    #[allow(non_camel_case_types)]
    type U3CmpU4 = <A as Cmp<B>>::Output;
    assert_eq!(<U3CmpU4 as Ord>::to_ordering(), Ordering::Less);
}
#[test]
#[allow(non_snake_case)]
fn test_3_BitAnd_5() {
    type A = UInt<UInt<UTerm, B1>, B1>;
    type B = UInt<UInt<UInt<UTerm, B1>, B0>, B1>;
    type U1 = UInt<UTerm, B1>;

    #[allow(non_camel_case_types)]
    type U3BitAndU5 = <<A as BitAnd<B>>::Output as Same<U1>>::Output;

    assert_eq!(<U3BitAndU5 as Unsigned>::to_u64(), <U1 as Unsigned>::to_u64());
}
#[test]
#[allow(non_snake_case)]
fn test_3_BitOr_5() {
    type A = UInt<UInt<UTerm, B1>, B1>;
    type B = UInt<UInt<UInt<UTerm, B1>, B0>, B1>;
    type U7 = UInt<UInt<UInt<UTerm, B1>, B1>, B1>;

    #[allow(non_camel_case_types)]
    type U3BitOrU5 = <<A as BitOr<B>>::Output as Same<U7>>::Output;

    assert_eq!(<U3BitOrU5 as Unsigned>::to_u64(), <U7 as Unsigned>::to_u64());
}
#[test]
#[allow(non_snake_case)]
fn test_3_BitXor_5() {
    type A = UInt<UInt<UTerm, B1>, B1>;
    type B = UInt<UInt<UInt<UTerm, B1>, B0>, B1>;
    type U6 = UInt<UInt<UInt<UTerm, B1>, B1>, B0>;

    #[allow(non_camel_case_types)]
    type U3BitXorU5 = <<A as BitXor<B>>::Output as Same<U6>>::Output;

    assert_eq!(<U3BitXorU5 as Unsigned>::to_u64(), <U6 as Unsigned>::to_u64());
}
#[test]
#[allow(non_snake_case)]
fn test_3_Shl_5() {
    type A = UInt<UInt<UTerm, B1>, B1>;
    type B = UInt<UInt<UInt<UTerm, B1>, B0>, B1>;
    type U96 = UInt<UInt<UInt<UInt<UInt<UInt<UInt<UTerm, B1>, B1>, B0>, B0>, B0>, B0>, B0>;

    #[allow(non_camel_case_types)]
    type U3ShlU5 = <<A as Shl<B>>::Output as Same<U96>>::Output;

    assert_eq!(<U3ShlU5 as Unsigned>::to_u64(), <U96 as Unsigned>::to_u64());
}
#[test]
#[allow(non_snake_case)]
fn test_3_Shr_5() {
    type A = UInt<UInt<UTerm, B1>, B1>;
    type B = UInt<UInt<UInt<UTerm, B1>, B0>, B1>;
    type U0 = UTerm;

    #[allow(non_camel_case_types)]
    type U3ShrU5 = <<A as Shr<B>>::Output as Same<U0>>::Output;

    assert_eq!(<U3ShrU5 as Unsigned>::to_u64(), <U0 as Unsigned>::to_u64());
}
#[test]
#[allow(non_snake_case)]
fn test_3_Add_5() {
    type A = UInt<UInt<UTerm, B1>, B1>;
    type B = UInt<UInt<UInt<UTerm, B1>, B0>, B1>;
    type U8 = UInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>, B0>;

    #[allow(non_camel_case_types)]
    type U3AddU5 = <<A as Add<B>>::Output as Same<U8>>::Output;

    assert_eq!(<U3AddU5 as Unsigned>::to_u64(), <U8 as Unsigned>::to_u64());
}
#[test]
#[allow(non_snake_case)]
fn test_3_Mul_5() {
    type A = UInt<UInt<UTerm, B1>, B1>;
    type B = UInt<UInt<UInt<UTerm, B1>, B0>, B1>;
    type U15 = UInt<UInt<UInt<UInt<UTerm, B1>, B1>, B1>, B1>;

    #[allow(non_camel_case_types)]
    type U3MulU5 = <<A as Mul<B>>::Output as Same<U15>>::Output;

    assert_eq!(<U3MulU5 as Unsigned>::to_u64(), <U15 as Unsigned>::to_u64());
}
#[test]
#[allow(non_snake_case)]
fn test_3_Pow_5() {
    type A = UInt<UInt<UTerm, B1>, B1>;
    type B = UInt<UInt<UInt<UTerm, B1>, B0>, B1>;
    type U243 = UInt<UInt<UInt<UInt<UInt<UInt<UInt<UInt<UTerm, B1>, B1>, B1>, B1>, B0>, B0>, B1>, B1>;

    #[allow(non_camel_case_types)]
    type U3PowU5 = <<A as Pow<B>>::Output as Same<U243>>::Output;

    assert_eq!(<U3PowU5 as Unsigned>::to_u64(), <U243 as Unsigned>::to_u64());
}
#[test]
#[allow(non_snake_case)]
fn test_3_Min_5() {
    type A = UInt<UInt<UTerm, B1>, B1>;
    type B = UInt<UInt<UInt<UTerm, B1>, B0>, B1>;
    type U3 = UInt<UInt<UTerm, B1>, B1>;

    #[allow(non_camel_case_types)]
    type U3MinU5 = <<A as Min<B>>::Output as Same<U3>>::Output;

    assert_eq!(<U3MinU5 as Unsigned>::to_u64(), <U3 as Unsigned>::to_u64());
}
#[test]
#[allow(non_snake_case)]
fn test_3_Max_5() {
    type A = UInt<UInt<UTerm, B1>, B1>;
    type B = UInt<UInt<UInt<UTerm, B1>, B0>, B1>;
    type U5 = UInt<UInt<UInt<UTerm, B1>, B0>, B1>;

    #[allow(non_camel_case_types)]
    type U3MaxU5 = <<A as Max<B>>::Output as Same<U5>>::Output;

    assert_eq!(<U3MaxU5 as Unsigned>::to_u64(), <U5 as Unsigned>::to_u64());
}
#[test]
#[allow(non_snake_case)]
fn test_3_Gcd_5() {
    type A = UInt<UInt<UTerm, B1>, B1>;
    type B = UInt<UInt<UInt<UTerm, B1>, B0>, B1>;
    type U1 = UInt<UTerm, B1>;

    #[allow(non_camel_case_types)]
    type U3GcdU5 = <<A as Gcd<B>>::Output as Same<U1>>::Output;

    assert_eq!(<U3GcdU5 as Unsigned>::to_u64(), <U1 as Unsigned>::to_u64());
}
#[test]
#[allow(non_snake_case)]
fn test_3_Div_5() {
    type A = UInt<UInt<UTerm, B1>, B1>;
    type B = UInt<UInt<UInt<UTerm, B1>, B0>, B1>;
    type U0 = UTerm;

    #[allow(non_camel_case_types)]
    type U3DivU5 = <<A as Div<B>>::Output as Same<U0>>::Output;

    assert_eq!(<U3DivU5 as Unsigned>::to_u64(), <U0 as Unsigned>::to_u64());
}
#[test]
#[allow(non_snake_case)]
fn test_3_Rem_5() {
    type A = UInt<UInt<UTerm, B1>, B1>;
    type B = UInt<UInt<UInt<UTerm, B1>, B0>, B1>;
    type U3 = UInt<UInt<UTerm, B1>, B1>;

    #[allow(non_camel_case_types)]
    type U3RemU5 = <<A as Rem<B>>::Output as Same<U3>>::Output;

    assert_eq!(<U3RemU5 as Unsigned>::to_u64(), <U3 as Unsigned>::to_u64());
}
#[test]
#[allow(non_snake_case)]
fn test_3_Cmp_5() {
    type A = UInt<UInt<UTerm, B1>, B1>;
    type B = UInt<UInt<UInt<UTerm, B1>, B0>, B1>;

    #[allow(non_camel_case_types)]
    type U3CmpU5 = <A as Cmp<B>>::Output;
    assert_eq!(<U3CmpU5 as Ord>::to_ordering(), Ordering::Less);
}
#[test]
#[allow(non_snake_case)]
fn test_4_BitAnd_0() {
    type A = UInt<UInt<UInt<UTerm, B1>, B0>, B0>;
    type B = UTerm;
    type U0 = UTerm;

    #[allow(non_camel_case_types)]
    type U4BitAndU0 = <<A as BitAnd<B>>::Output as Same<U0>>::Output;

    assert_eq!(<U4BitAndU0 as Unsigned>::to_u64(), <U0 as Unsigned>::to_u64());
}
#[test]
#[allow(non_snake_case)]
fn test_4_BitOr_0() {
    type A = UInt<UInt<UInt<UTerm, B1>, B0>, B0>;
    type B = UTerm;
    type U4 = UInt<UInt<UInt<UTerm, B1>, B0>, B0>;

    #[allow(non_camel_case_types)]
    type U4BitOrU0 = <<A as BitOr<B>>::Output as Same<U4>>::Output;

    assert_eq!(<U4BitOrU0 as Unsigned>::to_u64(), <U4 as Unsigned>::to_u64());
}
#[test]
#[allow(non_snake_case)]
fn test_4_BitXor_0() {
    type A = UInt<UInt<UInt<UTerm, B1>, B0>, B0>;
    type B = UTerm;
    type U4 = UInt<UInt<UInt<UTerm, B1>, B0>, B0>;

    #[allow(non_camel_case_types)]
    type U4BitXorU0 = <<A as BitXor<B>>::Output as Same<U4>>::Output;

    assert_eq!(<U4BitXorU0 as Unsigned>::to_u64(), <U4 as Unsigned>::to_u64());
}
#[test]
#[allow(non_snake_case)]
fn test_4_Shl_0() {
    type A = UInt<UInt<UInt<UTerm, B1>, B0>, B0>;
    type B = UTerm;
    type U4 = UInt<UInt<UInt<UTerm, B1>, B0>, B0>;

    #[allow(non_camel_case_types)]
    type U4ShlU0 = <<A as Shl<B>>::Output as Same<U4>>::Output;

    assert_eq!(<U4ShlU0 as Unsigned>::to_u64(), <U4 as Unsigned>::to_u64());
}
#[test]
#[allow(non_snake_case)]
fn test_4_Shr_0() {
    type A = UInt<UInt<UInt<UTerm, B1>, B0>, B0>;
    type B = UTerm;
    type U4 = UInt<UInt<UInt<UTerm, B1>, B0>, B0>;

    #[allow(non_camel_case_types)]
    type U4ShrU0 = <<A as Shr<B>>::Output as Same<U4>>::Output;

    assert_eq!(<U4ShrU0 as Unsigned>::to_u64(), <U4 as Unsigned>::to_u64());
}
#[test]
#[allow(non_snake_case)]
fn test_4_Add_0() {
    type A = UInt<UInt<UInt<UTerm, B1>, B0>, B0>;
    type B = UTerm;
    type U4 = UInt<UInt<UInt<UTerm, B1>, B0>, B0>;

    #[allow(non_camel_case_types)]
    type U4AddU0 = <<A as Add<B>>::Output as Same<U4>>::Output;

    assert_eq!(<U4AddU0 as Unsigned>::to_u64(), <U4 as Unsigned>::to_u64());
}
#[test]
#[allow(non_snake_case)]
fn test_4_Mul_0() {
    type A = UInt<UInt<UInt<UTerm, B1>, B0>, B0>;
    type B = UTerm;
    type U0 = UTerm;

    #[allow(non_camel_case_types)]
    type U4MulU0 = <<A as Mul<B>>::Output as Same<U0>>::Output;

    assert_eq!(<U4MulU0 as Unsigned>::to_u64(), <U0 as Unsigned>::to_u64());
}
#[test]
#[allow(non_snake_case)]
fn test_4_Pow_0() {
    type A = UInt<UInt<UInt<UTerm, B1>, B0>, B0>;
    type B = UTerm;
    type U1 = UInt<UTerm, B1>;

    #[allow(non_camel_case_types)]
    type U4PowU0 = <<A as Pow<B>>::Output as Same<U1>>::Output;

    assert_eq!(<U4PowU0 as Unsigned>::to_u64(), <U1 as Unsigned>::to_u64());
}
#[test]
#[allow(non_snake_case)]
fn test_4_Min_0() {
    type A = UInt<UInt<UInt<UTerm, B1>, B0>, B0>;
    type B = UTerm;
    type U0 = UTerm;

    #[allow(non_camel_case_types)]
    type U4MinU0 = <<A as Min<B>>::Output as Same<U0>>::Output;

    assert_eq!(<U4MinU0 as Unsigned>::to_u64(), <U0 as Unsigned>::to_u64());
}
#[test]
#[allow(non_snake_case)]
fn test_4_Max_0() {
    type A = UInt<UInt<UInt<UTerm, B1>, B0>, B0>;
    type B = UTerm;
    type U4 = UInt<UInt<UInt<UTerm, B1>, B0>, B0>;

    #[allow(non_camel_case_types)]
    type U4MaxU0 = <<A as Max<B>>::Output as Same<U4>>::Output;

    assert_eq!(<U4MaxU0 as Unsigned>::to_u64(), <U4 as Unsigned>::to_u64());
}
#[test]
#[allow(non_snake_case)]
fn test_4_Gcd_0() {
    type A = UInt<UInt<UInt<UTerm, B1>, B0>, B0>;
    type B = UTerm;
    type U4 = UInt<UInt<UInt<UTerm, B1>, B0>, B0>;

    #[allow(non_camel_case_types)]
    type U4GcdU0 = <<A as Gcd<B>>::Output as Same<U4>>::Output;

    assert_eq!(<U4GcdU0 as Unsigned>::to_u64(), <U4 as Unsigned>::to_u64());
}
#[test]
#[allow(non_snake_case)]
fn test_4_Sub_0() {
    type A = UInt<UInt<UInt<UTerm, B1>, B0>, B0>;
    type B = UTerm;
    type U4 = UInt<UInt<UInt<UTerm, B1>, B0>, B0>;

    #[allow(non_camel_case_types)]
    type U4SubU0 = <<A as Sub<B>>::Output as Same<U4>>::Output;

    assert_eq!(<U4SubU0 as Unsigned>::to_u64(), <U4 as Unsigned>::to_u64());
}
#[test]
#[allow(non_snake_case)]
fn test_4_Cmp_0() {
    type A = UInt<UInt<UInt<UTerm, B1>, B0>, B0>;
    type B = UTerm;

    #[allow(non_camel_case_types)]
    type U4CmpU0 = <A as Cmp<B>>::Output;
    assert_eq!(<U4CmpU0 as Ord>::to_ordering(), Ordering::Greater);
}
#[test]
#[allow(non_snake_case)]
fn test_4_BitAnd_1() {
    type A = UInt<UInt<UInt<UTerm, B1>, B0>, B0>;
    type B = UInt<UTerm, B1>;
    type U0 = UTerm;

    #[allow(non_camel_case_types)]
    type U4BitAndU1 = <<A as BitAnd<B>>::Output as Same<U0>>::Output;

    assert_eq!(<U4BitAndU1 as Unsigned>::to_u64(), <U0 as Unsigned>::to_u64());
}
#[test]
#[allow(non_snake_case)]
fn test_4_BitOr_1() {
    type A = UInt<UInt<UInt<UTerm, B1>, B0>, B0>;
    type B = UInt<UTerm, B1>;
    type U5 = UInt<UInt<UInt<UTerm, B1>, B0>, B1>;

    #[allow(non_camel_case_types)]
    type U4BitOrU1 = <<A as BitOr<B>>::Output as Same<U5>>::Output;

    assert_eq!(<U4BitOrU1 as Unsigned>::to_u64(), <U5 as Unsigned>::to_u64());
}
#[test]
#[allow(non_snake_case)]
fn test_4_BitXor_1() {
    type A = UInt<UInt<UInt<UTerm, B1>, B0>, B0>;
    type B = UInt<UTerm, B1>;
    type U5 = UInt<UInt<UInt<UTerm, B1>, B0>, B1>;

    #[allow(non_camel_case_types)]
    type U4BitXorU1 = <<A as BitXor<B>>::Output as Same<U5>>::Output;

    assert_eq!(<U4BitXorU1 as Unsigned>::to_u64(), <U5 as Unsigned>::to_u64());
}
#[test]
#[allow(non_snake_case)]
fn test_4_Shl_1() {
    type A = UInt<UInt<UInt<UTerm, B1>, B0>, B0>;
    type B = UInt<UTerm, B1>;
    type U8 = UInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>, B0>;

    #[allow(non_camel_case_types)]
    type U4ShlU1 = <<A as Shl<B>>::Output as Same<U8>>::Output;

    assert_eq!(<U4ShlU1 as Unsigned>::to_u64(), <U8 as Unsigned>::to_u64());
}
#[test]
#[allow(non_snake_case)]
fn test_4_Shr_1() {
    type A = UInt<UInt<UInt<UTerm, B1>, B0>, B0>;
    type B = UInt<UTerm, B1>;
    type U2 = UInt<UInt<UTerm, B1>, B0>;

    #[allow(non_camel_case_types)]
    type U4ShrU1 = <<A as Shr<B>>::Output as Same<U2>>::Output;

    assert_eq!(<U4ShrU1 as Unsigned>::to_u64(), <U2 as Unsigned>::to_u64());
}
#[test]
#[allow(non_snake_case)]
fn test_4_Add_1() {
    type A = UInt<UInt<UInt<UTerm, B1>, B0>, B0>;
    type B = UInt<UTerm, B1>;
    type U5 = UInt<UInt<UInt<UTerm, B1>, B0>, B1>;

    #[allow(non_camel_case_types)]
    type U4AddU1 = <<A as Add<B>>::Output as Same<U5>>::Output;

    assert_eq!(<U4AddU1 as Unsigned>::to_u64(), <U5 as Unsigned>::to_u64());
}
#[test]
#[allow(non_snake_case)]
fn test_4_Mul_1() {
    type A = UInt<UInt<UInt<UTerm, B1>, B0>, B0>;
    type B = UInt<UTerm, B1>;
    type U4 = UInt<UInt<UInt<UTerm, B1>, B0>, B0>;

    #[allow(non_camel_case_types)]
    type U4MulU1 = <<A as Mul<B>>::Output as Same<U4>>::Output;

    assert_eq!(<U4MulU1 as Unsigned>::to_u64(), <U4 as Unsigned>::to_u64());
}
#[test]
#[allow(non_snake_case)]
fn test_4_Pow_1() {
    type A = UInt<UInt<UInt<UTerm, B1>, B0>, B0>;
    type B = UInt<UTerm, B1>;
    type U4 = UInt<UInt<UInt<UTerm, B1>, B0>, B0>;

    #[allow(non_camel_case_types)]
    type U4PowU1 = <<A as Pow<B>>::Output as Same<U4>>::Output;

    assert_eq!(<U4PowU1 as Unsigned>::to_u64(), <U4 as Unsigned>::to_u64());
}
#[test]
#[allow(non_snake_case)]
fn test_4_Min_1() {
    type A = UInt<UInt<UInt<UTerm, B1>, B0>, B0>;
    type B = UInt<UTerm, B1>;
    type U1 = UInt<UTerm, B1>;

    #[allow(non_camel_case_types)]
    type U4MinU1 = <<A as Min<B>>::Output as Same<U1>>::Output;

    assert_eq!(<U4MinU1 as Unsigned>::to_u64(), <U1 as Unsigned>::to_u64());
}
#[test]
#[allow(non_snake_case)]
fn test_4_Max_1() {
    type A = UInt<UInt<UInt<UTerm, B1>, B0>, B0>;
    type B = UInt<UTerm, B1>;
    type U4 = UInt<UInt<UInt<UTerm, B1>, B0>, B0>;

    #[allow(non_camel_case_types)]
    type U4MaxU1 = <<A as Max<B>>::Output as Same<U4>>::Output;

    assert_eq!(<U4MaxU1 as Unsigned>::to_u64(), <U4 as Unsigned>::to_u64());
}
#[test]
#[allow(non_snake_case)]
fn test_4_Gcd_1() {
    type A = UInt<UInt<UInt<UTerm, B1>, B0>, B0>;
    type B = UInt<UTerm, B1>;
    type U1 = UInt<UTerm, B1>;

    #[allow(non_camel_case_types)]
    type U4GcdU1 = <<A as Gcd<B>>::Output as Same<U1>>::Output;

    assert_eq!(<U4GcdU1 as Unsigned>::to_u64(), <U1 as Unsigned>::to_u64());
}
#[test]
#[allow(non_snake_case)]
fn test_4_Sub_1() {
    type A = UInt<UInt<UInt<UTerm, B1>, B0>, B0>;
    type B = UInt<UTerm, B1>;
    type U3 = UInt<UInt<UTerm, B1>, B1>;

    #[allow(non_camel_case_types)]
    type U4SubU1 = <<A as Sub<B>>::Output as Same<U3>>::Output;

    assert_eq!(<U4SubU1 as Unsigned>::to_u64(), <U3 as Unsigned>::to_u64());
}
#[test]
#[allow(non_snake_case)]
fn test_4_Div_1() {
    type A = UInt<UInt<UInt<UTerm, B1>, B0>, B0>;
    type B = UInt<UTerm, B1>;
    type U4 = UInt<UInt<UInt<UTerm, B1>, B0>, B0>;

    #[allow(non_camel_case_types)]
    type U4DivU1 = <<A as Div<B>>::Output as Same<U4>>::Output;

    assert_eq!(<U4DivU1 as Unsigned>::to_u64(), <U4 as Unsigned>::to_u64());
}
#[test]
#[allow(non_snake_case)]
fn test_4_Rem_1() {
    type A = UInt<UInt<UInt<UTerm, B1>, B0>, B0>;
    type B = UInt<UTerm, B1>;
    type U0 = UTerm;

    #[allow(non_camel_case_types)]
    type U4RemU1 = <<A as Rem<B>>::Output as Same<U0>>::Output;

    assert_eq!(<U4RemU1 as Unsigned>::to_u64(), <U0 as Unsigned>::to_u64());
}
#[test]
#[allow(non_snake_case)]
fn test_4_PartialDiv_1() {
    type A = UInt<UInt<UInt<UTerm, B1>, B0>, B0>;
    type B = UInt<UTerm, B1>;
    type U4 = UInt<UInt<UInt<UTerm, B1>, B0>, B0>;

    #[allow(non_camel_case_types)]
    type U4PartialDivU1 = <<A as PartialDiv<B>>::Output as Same<U4>>::Output;

    assert_eq!(<U4PartialDivU1 as Unsigned>::to_u64(), <U4 as Unsigned>::to_u64());
}
#[test]
#[allow(non_snake_case)]
fn test_4_Cmp_1() {
    type A = UInt<UInt<UInt<UTerm, B1>, B0>, B0>;
    type B = UInt<UTerm, B1>;

    #[allow(non_camel_case_types)]
    type U4CmpU1 = <A as Cmp<B>>::Output;
    assert_eq!(<U4CmpU1 as Ord>::to_ordering(), Ordering::Greater);
}
#[test]
#[allow(non_snake_case)]
fn test_4_BitAnd_2() {
    type A = UInt<UInt<UInt<UTerm, B1>, B0>, B0>;
    type B = UInt<UInt<UTerm, B1>, B0>;
    type U0 = UTerm;

    #[allow(non_camel_case_types)]
    type U4BitAndU2 = <<A as BitAnd<B>>::Output as Same<U0>>::Output;

    assert_eq!(<U4BitAndU2 as Unsigned>::to_u64(), <U0 as Unsigned>::to_u64());
}
#[test]
#[allow(non_snake_case)]
fn test_4_BitOr_2() {
    type A = UInt<UInt<UInt<UTerm, B1>, B0>, B0>;
    type B = UInt<UInt<UTerm, B1>, B0>;
    type U6 = UInt<UInt<UInt<UTerm, B1>, B1>, B0>;

    #[allow(non_camel_case_types)]
    type U4BitOrU2 = <<A as BitOr<B>>::Output as Same<U6>>::Output;

    assert_eq!(<U4BitOrU2 as Unsigned>::to_u64(), <U6 as Unsigned>::to_u64());
}
#[test]
#[allow(non_snake_case)]
fn test_4_BitXor_2() {
    type A = UInt<UInt<UInt<UTerm, B1>, B0>, B0>;
    type B = UInt<UInt<UTerm, B1>, B0>;
    type U6 = UInt<UInt<UInt<UTerm, B1>, B1>, B0>;

    #[allow(non_camel_case_types)]
    type U4BitXorU2 = <<A as BitXor<B>>::Output as Same<U6>>::Output;

    assert_eq!(<U4BitXorU2 as Unsigned>::to_u64(), <U6 as Unsigned>::to_u64());
}
#[test]
#[allow(non_snake_case)]
fn test_4_Shl_2() {
    type A = UInt<UInt<UInt<UTerm, B1>, B0>, B0>;
    type B = UInt<UInt<UTerm, B1>, B0>;
    type U16 = UInt<UInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>, B0>, B0>;

    #[allow(non_camel_case_types)]
    type U4ShlU2 = <<A as Shl<B>>::Output as Same<U16>>::Output;

    assert_eq!(<U4ShlU2 as Unsigned>::to_u64(), <U16 as Unsigned>::to_u64());
}
#[test]
#[allow(non_snake_case)]
fn test_4_Shr_2() {
    type A = UInt<UInt<UInt<UTerm, B1>, B0>, B0>;
    type B = UInt<UInt<UTerm, B1>, B0>;
    type U1 = UInt<UTerm, B1>;

    #[allow(non_camel_case_types)]
    type U4ShrU2 = <<A as Shr<B>>::Output as Same<U1>>::Output;

    assert_eq!(<U4ShrU2 as Unsigned>::to_u64(), <U1 as Unsigned>::to_u64());
}
#[test]
#[allow(non_snake_case)]
fn test_4_Add_2() {
    type A = UInt<UInt<UInt<UTerm, B1>, B0>, B0>;
    type B = UInt<UInt<UTerm, B1>, B0>;
    type U6 = UInt<UInt<UInt<UTerm, B1>, B1>, B0>;

    #[allow(non_camel_case_types)]
    type U4AddU2 = <<A as Add<B>>::Output as Same<U6>>::Output;

    assert_eq!(<U4AddU2 as Unsigned>::to_u64(), <U6 as Unsigned>::to_u64());
}
#[test]
#[allow(non_snake_case)]
fn test_4_Mul_2() {
    type A = UInt<UInt<UInt<UTerm, B1>, B0>, B0>;
    type B = UInt<UInt<UTerm, B1>, B0>;
    type U8 = UInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>, B0>;

    #[allow(non_camel_case_types)]
    type U4MulU2 = <<A as Mul<B>>::Output as Same<U8>>::Output;

    assert_eq!(<U4MulU2 as Unsigned>::to_u64(), <U8 as Unsigned>::to_u64());
}
#[test]
#[allow(non_snake_case)]
fn test_4_Pow_2() {
    type A = UInt<UInt<UInt<UTerm, B1>, B0>, B0>;
    type B = UInt<UInt<UTerm, B1>, B0>;
    type U16 = UInt<UInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>, B0>, B0>;

    #[allow(non_camel_case_types)]
    type U4PowU2 = <<A as Pow<B>>::Output as Same<U16>>::Output;

    assert_eq!(<U4PowU2 as Unsigned>::to_u64(), <U16 as Unsigned>::to_u64());
}
#[test]
#[allow(non_snake_case)]
fn test_4_Min_2() {
    type A = UInt<UInt<UInt<UTerm, B1>, B0>, B0>;
    type B = UInt<UInt<UTerm, B1>, B0>;
    type U2 = UInt<UInt<UTerm, B1>, B0>;

    #[allow(non_camel_case_types)]
    type U4MinU2 = <<A as Min<B>>::Output as Same<U2>>::Output;

    assert_eq!(<U4MinU2 as Unsigned>::to_u64(), <U2 as Unsigned>::to_u64());
}
#[test]
#[allow(non_snake_case)]
fn test_4_Max_2() {
    type A = UInt<UInt<UInt<UTerm, B1>, B0>, B0>;
    type B = UInt<UInt<UTerm, B1>, B0>;
    type U4 = UInt<UInt<UInt<UTerm, B1>, B0>, B0>;

    #[allow(non_camel_case_types)]
    type U4MaxU2 = <<A as Max<B>>::Output as Same<U4>>::Output;

    assert_eq!(<U4MaxU2 as Unsigned>::to_u64(), <U4 as Unsigned>::to_u64());
}
#[test]
#[allow(non_snake_case)]
fn test_4_Gcd_2() {
    type A = UInt<UInt<UInt<UTerm, B1>, B0>, B0>;
    type B = UInt<UInt<UTerm, B1>, B0>;
    type U2 = UInt<UInt<UTerm, B1>, B0>;

    #[allow(non_camel_case_types)]
    type U4GcdU2 = <<A as Gcd<B>>::Output as Same<U2>>::Output;

    assert_eq!(<U4GcdU2 as Unsigned>::to_u64(), <U2 as Unsigned>::to_u64());
}
#[test]
#[allow(non_snake_case)]
fn test_4_Sub_2() {
    type A = UInt<UInt<UInt<UTerm, B1>, B0>, B0>;
    type B = UInt<UInt<UTerm, B1>, B0>;
    type U2 = UInt<UInt<UTerm, B1>, B0>;

    #[allow(non_camel_case_types)]
    type U4SubU2 = <<A as Sub<B>>::Output as Same<U2>>::Output;

    assert_eq!(<U4SubU2 as Unsigned>::to_u64(), <U2 as Unsigned>::to_u64());
}
#[test]
#[allow(non_snake_case)]
fn test_4_Div_2() {
    type A = UInt<UInt<UInt<UTerm, B1>, B0>, B0>;
    type B = UInt<UInt<UTerm, B1>, B0>;
    type U2 = UInt<UInt<UTerm, B1>, B0>;

    #[allow(non_camel_case_types)]
    type U4DivU2 = <<A as Div<B>>::Output as Same<U2>>::Output;

    assert_eq!(<U4DivU2 as Unsigned>::to_u64(), <U2 as Unsigned>::to_u64());
}
#[test]
#[allow(non_snake_case)]
fn test_4_Rem_2() {
    type A = UInt<UInt<UInt<UTerm, B1>, B0>, B0>;
    type B = UInt<UInt<UTerm, B1>, B0>;
    type U0 = UTerm;

    #[allow(non_camel_case_types)]
    type U4RemU2 = <<A as Rem<B>>::Output as Same<U0>>::Output;

    assert_eq!(<U4RemU2 as Unsigned>::to_u64(), <U0 as Unsigned>::to_u64());
}
#[test]
#[allow(non_snake_case)]
fn test_4_PartialDiv_2() {
    type A = UInt<UInt<UInt<UTerm, B1>, B0>, B0>;
    type B = UInt<UInt<UTerm, B1>, B0>;
    type U2 = UInt<UInt<UTerm, B1>, B0>;

    #[allow(non_camel_case_types)]
    type U4PartialDivU2 = <<A as PartialDiv<B>>::Output as Same<U2>>::Output;

    assert_eq!(<U4PartialDivU2 as Unsigned>::to_u64(), <U2 as Unsigned>::to_u64());
}
#[test]
#[allow(non_snake_case)]
fn test_4_Cmp_2() {
    type A = UInt<UInt<UInt<UTerm, B1>, B0>, B0>;
    type B = UInt<UInt<UTerm, B1>, B0>;

    #[allow(non_camel_case_types)]
    type U4CmpU2 = <A as Cmp<B>>::Output;
    assert_eq!(<U4CmpU2 as Ord>::to_ordering(), Ordering::Greater);
}
#[test]
#[allow(non_snake_case)]
fn test_4_BitAnd_3() {
    type A = UInt<UInt<UInt<UTerm, B1>, B0>, B0>;
    type B = UInt<UInt<UTerm, B1>, B1>;
    type U0 = UTerm;

    #[allow(non_camel_case_types)]
    type U4BitAndU3 = <<A as BitAnd<B>>::Output as Same<U0>>::Output;

    assert_eq!(<U4BitAndU3 as Unsigned>::to_u64(), <U0 as Unsigned>::to_u64());
}
#[test]
#[allow(non_snake_case)]
fn test_4_BitOr_3() {
    type A = UInt<UInt<UInt<UTerm, B1>, B0>, B0>;
    type B = UInt<UInt<UTerm, B1>, B1>;
    type U7 = UInt<UInt<UInt<UTerm, B1>, B1>, B1>;

    #[allow(non_camel_case_types)]
    type U4BitOrU3 = <<A as BitOr<B>>::Output as Same<U7>>::Output;

    assert_eq!(<U4BitOrU3 as Unsigned>::to_u64(), <U7 as Unsigned>::to_u64());
}
#[test]
#[allow(non_snake_case)]
fn test_4_BitXor_3() {
    type A = UInt<UInt<UInt<UTerm, B1>, B0>, B0>;
    type B = UInt<UInt<UTerm, B1>, B1>;
    type U7 = UInt<UInt<UInt<UTerm, B1>, B1>, B1>;

    #[allow(non_camel_case_types)]
    type U4BitXorU3 = <<A as BitXor<B>>::Output as Same<U7>>::Output;

    assert_eq!(<U4BitXorU3 as Unsigned>::to_u64(), <U7 as Unsigned>::to_u64());
}
#[test]
#[allow(non_snake_case)]
fn test_4_Shl_3() {
    type A = UInt<UInt<UInt<UTerm, B1>, B0>, B0>;
    type B = UInt<UInt<UTerm, B1>, B1>;
    type U32 = UInt<UInt<UInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>, B0>, B0>, B0>;

    #[allow(non_camel_case_types)]
    type U4ShlU3 = <<A as Shl<B>>::Output as Same<U32>>::Output;

    assert_eq!(<U4ShlU3 as Unsigned>::to_u64(), <U32 as Unsigned>::to_u64());
}
#[test]
#[allow(non_snake_case)]
fn test_4_Shr_3() {
    type A = UInt<UInt<UInt<UTerm, B1>, B0>, B0>;
    type B = UInt<UInt<UTerm, B1>, B1>;
    type U0 = UTerm;

    #[allow(non_camel_case_types)]
    type U4ShrU3 = <<A as Shr<B>>::Output as Same<U0>>::Output;

    assert_eq!(<U4ShrU3 as Unsigned>::to_u64(), <U0 as Unsigned>::to_u64());
}
#[test]
#[allow(non_snake_case)]
fn test_4_Add_3() {
    type A = UInt<UInt<UInt<UTerm, B1>, B0>, B0>;
    type B = UInt<UInt<UTerm, B1>, B1>;
    type U7 = UInt<UInt<UInt<UTerm, B1>, B1>, B1>;

    #[allow(non_camel_case_types)]
    type U4AddU3 = <<A as Add<B>>::Output as Same<U7>>::Output;

    assert_eq!(<U4AddU3 as Unsigned>::to_u64(), <U7 as Unsigned>::to_u64());
}
#[test]
#[allow(non_snake_case)]
fn test_4_Mul_3() {
    type A = UInt<UInt<UInt<UTerm, B1>, B0>, B0>;
    type B = UInt<UInt<UTerm, B1>, B1>;
    type U12 = UInt<UInt<UInt<UInt<UTerm, B1>, B1>, B0>, B0>;

    #[allow(non_camel_case_types)]
    type U4MulU3 = <<A as Mul<B>>::Output as Same<U12>>::Output;

    assert_eq!(<U4MulU3 as Unsigned>::to_u64(), <U12 as Unsigned>::to_u64());
}
#[test]
#[allow(non_snake_case)]
fn test_4_Pow_3() {
    type A = UInt<UInt<UInt<UTerm, B1>, B0>, B0>;
    type B = UInt<UInt<UTerm, B1>, B1>;
    type U64 = UInt<UInt<UInt<UInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>, B0>, B0>, B0>, B0>;

    #[allow(non_camel_case_types)]
    type U4PowU3 = <<A as Pow<B>>::Output as Same<U64>>::Output;

    assert_eq!(<U4PowU3 as Unsigned>::to_u64(), <U64 as Unsigned>::to_u64());
}
#[test]
#[allow(non_snake_case)]
fn test_4_Min_3() {
    type A = UInt<UInt<UInt<UTerm, B1>, B0>, B0>;
    type B = UInt<UInt<UTerm, B1>, B1>;
    type U3 = UInt<UInt<UTerm, B1>, B1>;

    #[allow(non_camel_case_types)]
    type U4MinU3 = <<A as Min<B>>::Output as Same<U3>>::Output;

    assert_eq!(<U4MinU3 as Unsigned>::to_u64(), <U3 as Unsigned>::to_u64());
}
#[test]
#[allow(non_snake_case)]
fn test_4_Max_3() {
    type A = UInt<UInt<UInt<UTerm, B1>, B0>, B0>;
    type B = UInt<UInt<UTerm, B1>, B1>;
    type U4 = UInt<UInt<UInt<UTerm, B1>, B0>, B0>;

    #[allow(non_camel_case_types)]
    type U4MaxU3 = <<A as Max<B>>::Output as Same<U4>>::Output;

    assert_eq!(<U4MaxU3 as Unsigned>::to_u64(), <U4 as Unsigned>::to_u64());
}
#[test]
#[allow(non_snake_case)]
fn test_4_Gcd_3() {
    type A = UInt<UInt<UInt<UTerm, B1>, B0>, B0>;
    type B = UInt<UInt<UTerm, B1>, B1>;
    type U1 = UInt<UTerm, B1>;

    #[allow(non_camel_case_types)]
    type U4GcdU3 = <<A as Gcd<B>>::Output as Same<U1>>::Output;

    assert_eq!(<U4GcdU3 as Unsigned>::to_u64(), <U1 as Unsigned>::to_u64());
}
#[test]
#[allow(non_snake_case)]
fn test_4_Sub_3() {
    type A = UInt<UInt<UInt<UTerm, B1>, B0>, B0>;
    type B = UInt<UInt<UTerm, B1>, B1>;
    type U1 = UInt<UTerm, B1>;

    #[allow(non_camel_case_types)]
    type U4SubU3 = <<A as Sub<B>>::Output as Same<U1>>::Output;

    assert_eq!(<U4SubU3 as Unsigned>::to_u64(), <U1 as Unsigned>::to_u64());
}
#[test]
#[allow(non_snake_case)]
fn test_4_Div_3() {
    type A = UInt<UInt<UInt<UTerm, B1>, B0>, B0>;
    type B = UInt<UInt<UTerm, B1>, B1>;
    type U1 = UInt<UTerm, B1>;

    #[allow(non_camel_case_types)]
    type U4DivU3 = <<A as Div<B>>::Output as Same<U1>>::Output;

    assert_eq!(<U4DivU3 as Unsigned>::to_u64(), <U1 as Unsigned>::to_u64());
}
#[test]
#[allow(non_snake_case)]
fn test_4_Rem_3() {
    type A = UInt<UInt<UInt<UTerm, B1>, B0>, B0>;
    type B = UInt<UInt<UTerm, B1>, B1>;
    type U1 = UInt<UTerm, B1>;

    #[allow(non_camel_case_types)]
    type U4RemU3 = <<A as Rem<B>>::Output as Same<U1>>::Output;

    assert_eq!(<U4RemU3 as Unsigned>::to_u64(), <U1 as Unsigned>::to_u64());
}
#[test]
#[allow(non_snake_case)]
fn test_4_Cmp_3() {
    type A = UInt<UInt<UInt<UTerm, B1>, B0>, B0>;
    type B = UInt<UInt<UTerm, B1>, B1>;

    #[allow(non_camel_case_types)]
    type U4CmpU3 = <A as Cmp<B>>::Output;
    assert_eq!(<U4CmpU3 as Ord>::to_ordering(), Ordering::Greater);
}
#[test]
#[allow(non_snake_case)]
fn test_4_BitAnd_4() {
    type A = UInt<UInt<UInt<UTerm, B1>, B0>, B0>;
    type B = UInt<UInt<UInt<UTerm, B1>, B0>, B0>;
    type U4 = UInt<UInt<UInt<UTerm, B1>, B0>, B0>;

    #[allow(non_camel_case_types)]
    type U4BitAndU4 = <<A as BitAnd<B>>::Output as Same<U4>>::Output;

    assert_eq!(<U4BitAndU4 as Unsigned>::to_u64(), <U4 as Unsigned>::to_u64());
}
#[test]
#[allow(non_snake_case)]
fn test_4_BitOr_4() {
    type A = UInt<UInt<UInt<UTerm, B1>, B0>, B0>;
    type B = UInt<UInt<UInt<UTerm, B1>, B0>, B0>;
    type U4 = UInt<UInt<UInt<UTerm, B1>, B0>, B0>;

    #[allow(non_camel_case_types)]
    type U4BitOrU4 = <<A as BitOr<B>>::Output as Same<U4>>::Output;

    assert_eq!(<U4BitOrU4 as Unsigned>::to_u64(), <U4 as Unsigned>::to_u64());
}
#[test]
#[allow(non_snake_case)]
fn test_4_BitXor_4() {
    type A = UInt<UInt<UInt<UTerm, B1>, B0>, B0>;
    type B = UInt<UInt<UInt<UTerm, B1>, B0>, B0>;
    type U0 = UTerm;

    #[allow(non_camel_case_types)]
    type U4BitXorU4 = <<A as BitXor<B>>::Output as Same<U0>>::Output;

    assert_eq!(<U4BitXorU4 as Unsigned>::to_u64(), <U0 as Unsigned>::to_u64());
}
#[test]
#[allow(non_snake_case)]
fn test_4_Shl_4() {
    type A = UInt<UInt<UInt<UTerm, B1>, B0>, B0>;
    type B = UInt<UInt<UInt<UTerm, B1>, B0>, B0>;
    type U64 = UInt<UInt<UInt<UInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>, B0>, B0>, B0>, B0>;

    #[allow(non_camel_case_types)]
    type U4ShlU4 = <<A as Shl<B>>::Output as Same<U64>>::Output;

    assert_eq!(<U4ShlU4 as Unsigned>::to_u64(), <U64 as Unsigned>::to_u64());
}
#[test]
#[allow(non_snake_case)]
fn test_4_Shr_4() {
    type A = UInt<UInt<UInt<UTerm, B1>, B0>, B0>;
    type B = UInt<UInt<UInt<UTerm, B1>, B0>, B0>;
    type U0 = UTerm;

    #[allow(non_camel_case_types)]
    type U4ShrU4 = <<A as Shr<B>>::Output as Same<U0>>::Output;

    assert_eq!(<U4ShrU4 as Unsigned>::to_u64(), <U0 as Unsigned>::to_u64());
}
#[test]
#[allow(non_snake_case)]
fn test_4_Add_4() {
    type A = UInt<UInt<UInt<UTerm, B1>, B0>, B0>;
    type B = UInt<UInt<UInt<UTerm, B1>, B0>, B0>;
    type U8 = UInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>, B0>;

    #[allow(non_camel_case_types)]
    type U4AddU4 = <<A as Add<B>>::Output as Same<U8>>::Output;

    assert_eq!(<U4AddU4 as Unsigned>::to_u64(), <U8 as Unsigned>::to_u64());
}
#[test]
#[allow(non_snake_case)]
fn test_4_Mul_4() {
    type A = UInt<UInt<UInt<UTerm, B1>, B0>, B0>;
    type B = UInt<UInt<UInt<UTerm, B1>, B0>, B0>;
    type U16 = UInt<UInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>, B0>, B0>;

    #[allow(non_camel_case_types)]
    type U4MulU4 = <<A as Mul<B>>::Output as Same<U16>>::Output;

    assert_eq!(<U4MulU4 as Unsigned>::to_u64(), <U16 as Unsigned>::to_u64());
}
#[test]
#[allow(non_snake_case)]
fn test_4_Pow_4() {
    type A = UInt<UInt<UInt<UTerm, B1>, B0>, B0>;
    type B = UInt<UInt<UInt<UTerm, B1>, B0>, B0>;
    type U256 = UInt<UInt<UInt<UInt<UInt<UInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>, B0>, B0>, B0>, B0>, B0>, B0>;

    #[allow(non_camel_case_types)]
    type U4PowU4 = <<A as Pow<B>>::Output as Same<U256>>::Output;

    assert_eq!(<U4PowU4 as Unsigned>::to_u64(), <U256 as Unsigned>::to_u64());
}
#[test]
#[allow(non_snake_case)]
fn test_4_Min_4() {
    type A = UInt<UInt<UInt<UTerm, B1>, B0>, B0>;
    type B = UInt<UInt<UInt<UTerm, B1>, B0>, B0>;
    type U4 = UInt<UInt<UInt<UTerm, B1>, B0>, B0>;

    #[allow(non_camel_case_types)]
    type U4MinU4 = <<A as Min<B>>::Output as Same<U4>>::Output;

    assert_eq!(<U4MinU4 as Unsigned>::to_u64(), <U4 as Unsigned>::to_u64());
}
#[test]
#[allow(non_snake_case)]
fn test_4_Max_4() {
    type A = UInt<UInt<UInt<UTerm, B1>, B0>, B0>;
    type B = UInt<UInt<UInt<UTerm, B1>, B0>, B0>;
    type U4 = UInt<UInt<UInt<UTerm, B1>, B0>, B0>;

    #[allow(non_camel_case_types)]
    type U4MaxU4 = <<A as Max<B>>::Output as Same<U4>>::Output;

    assert_eq!(<U4MaxU4 as Unsigned>::to_u64(), <U4 as Unsigned>::to_u64());
}
#[test]
#[allow(non_snake_case)]
fn test_4_Gcd_4() {
    type A = UInt<UInt<UInt<UTerm, B1>, B0>, B0>;
    type B = UInt<UInt<UInt<UTerm, B1>, B0>, B0>;
    type U4 = UInt<UInt<UInt<UTerm, B1>, B0>, B0>;

    #[allow(non_camel_case_types)]
    type U4GcdU4 = <<A as Gcd<B>>::Output as Same<U4>>::Output;

    assert_eq!(<U4GcdU4 as Unsigned>::to_u64(), <U4 as Unsigned>::to_u64());
}
#[test]
#[allow(non_snake_case)]
fn test_4_Sub_4() {
    type A = UInt<UInt<UInt<UTerm, B1>, B0>, B0>;
    type B = UInt<UInt<UInt<UTerm, B1>, B0>, B0>;
    type U0 = UTerm;

    #[allow(non_camel_case_types)]
    type U4SubU4 = <<A as Sub<B>>::Output as Same<U0>>::Output;

    assert_eq!(<U4SubU4 as Unsigned>::to_u64(), <U0 as Unsigned>::to_u64());
}
#[test]
#[allow(non_snake_case)]
fn test_4_Div_4() {
    type A = UInt<UInt<UInt<UTerm, B1>, B0>, B0>;
    type B = UInt<UInt<UInt<UTerm, B1>, B0>, B0>;
    type U1 = UInt<UTerm, B1>;

    #[allow(non_camel_case_types)]
    type U4DivU4 = <<A as Div<B>>::Output as Same<U1>>::Output;

    assert_eq!(<U4DivU4 as Unsigned>::to_u64(), <U1 as Unsigned>::to_u64());
}
#[test]
#[allow(non_snake_case)]
fn test_4_Rem_4() {
    type A = UInt<UInt<UInt<UTerm, B1>, B0>, B0>;
    type B = UInt<UInt<UInt<UTerm, B1>, B0>, B0>;
    type U0 = UTerm;

    #[allow(non_camel_case_types)]
    type U4RemU4 = <<A as Rem<B>>::Output as Same<U0>>::Output;

    assert_eq!(<U4RemU4 as Unsigned>::to_u64(), <U0 as Unsigned>::to_u64());
}
#[test]
#[allow(non_snake_case)]
fn test_4_PartialDiv_4() {
    type A = UInt<UInt<UInt<UTerm, B1>, B0>, B0>;
    type B = UInt<UInt<UInt<UTerm, B1>, B0>, B0>;
    type U1 = UInt<UTerm, B1>;

    #[allow(non_camel_case_types)]
    type U4PartialDivU4 = <<A as PartialDiv<B>>::Output as Same<U1>>::Output;

    assert_eq!(<U4PartialDivU4 as Unsigned>::to_u64(), <U1 as Unsigned>::to_u64());
}
#[test]
#[allow(non_snake_case)]
fn test_4_Cmp_4() {
    type A = UInt<UInt<UInt<UTerm, B1>, B0>, B0>;
    type B = UInt<UInt<UInt<UTerm, B1>, B0>, B0>;

    #[allow(non_camel_case_types)]
    type U4CmpU4 = <A as Cmp<B>>::Output;
    assert_eq!(<U4CmpU4 as Ord>::to_ordering(), Ordering::Equal);
}
#[test]
#[allow(non_snake_case)]
fn test_4_BitAnd_5() {
    type A = UInt<UInt<UInt<UTerm, B1>, B0>, B0>;
    type B = UInt<UInt<UInt<UTerm, B1>, B0>, B1>;
    type U4 = UInt<UInt<UInt<UTerm, B1>, B0>, B0>;

    #[allow(non_camel_case_types)]
    type U4BitAndU5 = <<A as BitAnd<B>>::Output as Same<U4>>::Output;

    assert_eq!(<U4BitAndU5 as Unsigned>::to_u64(), <U4 as Unsigned>::to_u64());
}
#[test]
#[allow(non_snake_case)]
fn test_4_BitOr_5() {
    type A = UInt<UInt<UInt<UTerm, B1>, B0>, B0>;
    type B = UInt<UInt<UInt<UTerm, B1>, B0>, B1>;
    type U5 = UInt<UInt<UInt<UTerm, B1>, B0>, B1>;

    #[allow(non_camel_case_types)]
    type U4BitOrU5 = <<A as BitOr<B>>::Output as Same<U5>>::Output;

    assert_eq!(<U4BitOrU5 as Unsigned>::to_u64(), <U5 as Unsigned>::to_u64());
}
#[test]
#[allow(non_snake_case)]
fn test_4_BitXor_5() {
    type A = UInt<UInt<UInt<UTerm, B1>, B0>, B0>;
    type B = UInt<UInt<UInt<UTerm, B1>, B0>, B1>;
    type U1 = UInt<UTerm, B1>;

    #[allow(non_camel_case_types)]
    type U4BitXorU5 = <<A as BitXor<B>>::Output as Same<U1>>::Output;

    assert_eq!(<U4BitXorU5 as Unsigned>::to_u64(), <U1 as Unsigned>::to_u64());
}
#[test]
#[allow(non_snake_case)]
fn test_4_Shl_5() {
    type A = UInt<UInt<UInt<UTerm, B1>, B0>, B0>;
    type B = UInt<UInt<UInt<UTerm, B1>, B0>, B1>;
    type U128 = UInt<UInt<UInt<UInt<UInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>, B0>, B0>, B0>, B0>, B0>;

    #[allow(non_camel_case_types)]
    type U4ShlU5 = <<A as Shl<B>>::Output as Same<U128>>::Output;

    assert_eq!(<U4ShlU5 as Unsigned>::to_u64(), <U128 as Unsigned>::to_u64());
}
#[test]
#[allow(non_snake_case)]
fn test_4_Shr_5() {
    type A = UInt<UInt<UInt<UTerm, B1>, B0>, B0>;
    type B = UInt<UInt<UInt<UTerm, B1>, B0>, B1>;
    type U0 = UTerm;

    #[allow(non_camel_case_types)]
    type U4ShrU5 = <<A as Shr<B>>::Output as Same<U0>>::Output;

    assert_eq!(<U4ShrU5 as Unsigned>::to_u64(), <U0 as Unsigned>::to_u64());
}
#[test]
#[allow(non_snake_case)]
fn test_4_Add_5() {
    type A = UInt<UInt<UInt<UTerm, B1>, B0>, B0>;
    type B = UInt<UInt<UInt<UTerm, B1>, B0>, B1>;
    type U9 = UInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>, B1>;

    #[allow(non_camel_case_types)]
    type U4AddU5 = <<A as Add<B>>::Output as Same<U9>>::Output;

    assert_eq!(<U4AddU5 as Unsigned>::to_u64(), <U9 as Unsigned>::to_u64());
}
#[test]
#[allow(non_snake_case)]
fn test_4_Mul_5() {
    type A = UInt<UInt<UInt<UTerm, B1>, B0>, B0>;
    type B = UInt<UInt<UInt<UTerm, B1>, B0>, B1>;
    type U20 = UInt<UInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>, B0>, B0>;

    #[allow(non_camel_case_types)]
    type U4MulU5 = <<A as Mul<B>>::Output as Same<U20>>::Output;

    assert_eq!(<U4MulU5 as Unsigned>::to_u64(), <U20 as Unsigned>::to_u64());
}
#[test]
#[allow(non_snake_case)]
fn test_4_Pow_5() {
    type A = UInt<UInt<UInt<UTerm, B1>, B0>, B0>;
    type B = UInt<UInt<UInt<UTerm, B1>, B0>, B1>;
    type U1024 = UInt<UInt<UInt<UInt<UInt<UInt<UInt<UInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>, B0>, B0>, B0>, B0>, B0>, B0>, B0>, B0>;

    #[allow(non_camel_case_types)]
    type U4PowU5 = <<A as Pow<B>>::Output as Same<U1024>>::Output;

    assert_eq!(<U4PowU5 as Unsigned>::to_u64(), <U1024 as Unsigned>::to_u64());
}
#[test]
#[allow(non_snake_case)]
fn test_4_Min_5() {
    type A = UInt<UInt<UInt<UTerm, B1>, B0>, B0>;
    type B = UInt<UInt<UInt<UTerm, B1>, B0>, B1>;
    type U4 = UInt<UInt<UInt<UTerm, B1>, B0>, B0>;

    #[allow(non_camel_case_types)]
    type U4MinU5 = <<A as Min<B>>::Output as Same<U4>>::Output;

    assert_eq!(<U4MinU5 as Unsigned>::to_u64(), <U4 as Unsigned>::to_u64());
}
#[test]
#[allow(non_snake_case)]
fn test_4_Max_5() {
    type A = UInt<UInt<UInt<UTerm, B1>, B0>, B0>;
    type B = UInt<UInt<UInt<UTerm, B1>, B0>, B1>;
    type U5 = UInt<UInt<UInt<UTerm, B1>, B0>, B1>;

    #[allow(non_camel_case_types)]
    type U4MaxU5 = <<A as Max<B>>::Output as Same<U5>>::Output;

    assert_eq!(<U4MaxU5 as Unsigned>::to_u64(), <U5 as Unsigned>::to_u64());
}
#[test]
#[allow(non_snake_case)]
fn test_4_Gcd_5() {
    type A = UInt<UInt<UInt<UTerm, B1>, B0>, B0>;
    type B = UInt<UInt<UInt<UTerm, B1>, B0>, B1>;
    type U1 = UInt<UTerm, B1>;

    #[allow(non_camel_case_types)]
    type U4GcdU5 = <<A as Gcd<B>>::Output as Same<U1>>::Output;

    assert_eq!(<U4GcdU5 as Unsigned>::to_u64(), <U1 as Unsigned>::to_u64());
}
#[test]
#[allow(non_snake_case)]
fn test_4_Div_5() {
    type A = UInt<UInt<UInt<UTerm, B1>, B0>, B0>;
    type B = UInt<UInt<UInt<UTerm, B1>, B0>, B1>;
    type U0 = UTerm;

    #[allow(non_camel_case_types)]
    type U4DivU5 = <<A as Div<B>>::Output as Same<U0>>::Output;

    assert_eq!(<U4DivU5 as Unsigned>::to_u64(), <U0 as Unsigned>::to_u64());
}
#[test]
#[allow(non_snake_case)]
fn test_4_Rem_5() {
    type A = UInt<UInt<UInt<UTerm, B1>, B0>, B0>;
    type B = UInt<UInt<UInt<UTerm, B1>, B0>, B1>;
    type U4 = UInt<UInt<UInt<UTerm, B1>, B0>, B0>;

    #[allow(non_camel_case_types)]
    type U4RemU5 = <<A as Rem<B>>::Output as Same<U4>>::Output;

    assert_eq!(<U4RemU5 as Unsigned>::to_u64(), <U4 as Unsigned>::to_u64());
}
#[test]
#[allow(non_snake_case)]
fn test_4_Cmp_5() {
    type A = UInt<UInt<UInt<UTerm, B1>, B0>, B0>;
    type B = UInt<UInt<UInt<UTerm, B1>, B0>, B1>;

    #[allow(non_camel_case_types)]
    type U4CmpU5 = <A as Cmp<B>>::Output;
    assert_eq!(<U4CmpU5 as Ord>::to_ordering(), Ordering::Less);
}
#[test]
#[allow(non_snake_case)]
fn test_5_BitAnd_0() {
    type A = UInt<UInt<UInt<UTerm, B1>, B0>, B1>;
    type B = UTerm;
    type U0 = UTerm;

    #[allow(non_camel_case_types)]
    type U5BitAndU0 = <<A as BitAnd<B>>::Output as Same<U0>>::Output;

    assert_eq!(<U5BitAndU0 as Unsigned>::to_u64(), <U0 as Unsigned>::to_u64());
}
#[test]
#[allow(non_snake_case)]
fn test_5_BitOr_0() {
    type A = UInt<UInt<UInt<UTerm, B1>, B0>, B1>;
    type B = UTerm;
    type U5 = UInt<UInt<UInt<UTerm, B1>, B0>, B1>;

    #[allow(non_camel_case_types)]
    type U5BitOrU0 = <<A as BitOr<B>>::Output as Same<U5>>::Output;

    assert_eq!(<U5BitOrU0 as Unsigned>::to_u64(), <U5 as Unsigned>::to_u64());
}
#[test]
#[allow(non_snake_case)]
fn test_5_BitXor_0() {
    type A = UInt<UInt<UInt<UTerm, B1>, B0>, B1>;
    type B = UTerm;
    type U5 = UInt<UInt<UInt<UTerm, B1>, B0>, B1>;

    #[allow(non_camel_case_types)]
    type U5BitXorU0 = <<A as BitXor<B>>::Output as Same<U5>>::Output;

    assert_eq!(<U5BitXorU0 as Unsigned>::to_u64(), <U5 as Unsigned>::to_u64());
}
#[test]
#[allow(non_snake_case)]
fn test_5_Shl_0() {
    type A = UInt<UInt<UInt<UTerm, B1>, B0>, B1>;
    type B = UTerm;
    type U5 = UInt<UInt<UInt<UTerm, B1>, B0>, B1>;

    #[allow(non_camel_case_types)]
    type U5ShlU0 = <<A as Shl<B>>::Output as Same<U5>>::Output;

    assert_eq!(<U5ShlU0 as Unsigned>::to_u64(), <U5 as Unsigned>::to_u64());
}
#[test]
#[allow(non_snake_case)]
fn test_5_Shr_0() {
    type A = UInt<UInt<UInt<UTerm, B1>, B0>, B1>;
    type B = UTerm;
    type U5 = UInt<UInt<UInt<UTerm, B1>, B0>, B1>;

    #[allow(non_camel_case_types)]
    type U5ShrU0 = <<A as Shr<B>>::Output as Same<U5>>::Output;

    assert_eq!(<U5ShrU0 as Unsigned>::to_u64(), <U5 as Unsigned>::to_u64());
}
#[test]
#[allow(non_snake_case)]
fn test_5_Add_0() {
    type A = UInt<UInt<UInt<UTerm, B1>, B0>, B1>;
    type B = UTerm;
    type U5 = UInt<UInt<UInt<UTerm, B1>, B0>, B1>;

    #[allow(non_camel_case_types)]
    type U5AddU0 = <<A as Add<B>>::Output as Same<U5>>::Output;

    assert_eq!(<U5AddU0 as Unsigned>::to_u64(), <U5 as Unsigned>::to_u64());
}
#[test]
#[allow(non_snake_case)]
fn test_5_Mul_0() {
    type A = UInt<UInt<UInt<UTerm, B1>, B0>, B1>;
    type B = UTerm;
    type U0 = UTerm;

    #[allow(non_camel_case_types)]
    type U5MulU0 = <<A as Mul<B>>::Output as Same<U0>>::Output;

    assert_eq!(<U5MulU0 as Unsigned>::to_u64(), <U0 as Unsigned>::to_u64());
}
#[test]
#[allow(non_snake_case)]
fn test_5_Pow_0() {
    type A = UInt<UInt<UInt<UTerm, B1>, B0>, B1>;
    type B = UTerm;
    type U1 = UInt<UTerm, B1>;

    #[allow(non_camel_case_types)]
    type U5PowU0 = <<A as Pow<B>>::Output as Same<U1>>::Output;

    assert_eq!(<U5PowU0 as Unsigned>::to_u64(), <U1 as Unsigned>::to_u64());
}
#[test]
#[allow(non_snake_case)]
fn test_5_Min_0() {
    type A = UInt<UInt<UInt<UTerm, B1>, B0>, B1>;
    type B = UTerm;
    type U0 = UTerm;

    #[allow(non_camel_case_types)]
    type U5MinU0 = <<A as Min<B>>::Output as Same<U0>>::Output;

    assert_eq!(<U5MinU0 as Unsigned>::to_u64(), <U0 as Unsigned>::to_u64());
}
#[test]
#[allow(non_snake_case)]
fn test_5_Max_0() {
    type A = UInt<UInt<UInt<UTerm, B1>, B0>, B1>;
    type B = UTerm;
    type U5 = UInt<UInt<UInt<UTerm, B1>, B0>, B1>;

    #[allow(non_camel_case_types)]
    type U5MaxU0 = <<A as Max<B>>::Output as Same<U5>>::Output;

    assert_eq!(<U5MaxU0 as Unsigned>::to_u64(), <U5 as Unsigned>::to_u64());
}
#[test]
#[allow(non_snake_case)]
fn test_5_Gcd_0() {
    type A = UInt<UInt<UInt<UTerm, B1>, B0>, B1>;
    type B = UTerm;
    type U5 = UInt<UInt<UInt<UTerm, B1>, B0>, B1>;

    #[allow(non_camel_case_types)]
    type U5GcdU0 = <<A as Gcd<B>>::Output as Same<U5>>::Output;

    assert_eq!(<U5GcdU0 as Unsigned>::to_u64(), <U5 as Unsigned>::to_u64());
}
#[test]
#[allow(non_snake_case)]
fn test_5_Sub_0() {
    type A = UInt<UInt<UInt<UTerm, B1>, B0>, B1>;
    type B = UTerm;
    type U5 = UInt<UInt<UInt<UTerm, B1>, B0>, B1>;

    #[allow(non_camel_case_types)]
    type U5SubU0 = <<A as Sub<B>>::Output as Same<U5>>::Output;

    assert_eq!(<U5SubU0 as Unsigned>::to_u64(), <U5 as Unsigned>::to_u64());
}
#[test]
#[allow(non_snake_case)]
fn test_5_Cmp_0() {
    type A = UInt<UInt<UInt<UTerm, B1>, B0>, B1>;
    type B = UTerm;

    #[allow(non_camel_case_types)]
    type U5CmpU0 = <A as Cmp<B>>::Output;
    assert_eq!(<U5CmpU0 as Ord>::to_ordering(), Ordering::Greater);
}
#[test]
#[allow(non_snake_case)]
fn test_5_BitAnd_1() {
    type A = UInt<UInt<UInt<UTerm, B1>, B0>, B1>;
    type B = UInt<UTerm, B1>;
    type U1 = UInt<UTerm, B1>;

    #[allow(non_camel_case_types)]
    type U5BitAndU1 = <<A as BitAnd<B>>::Output as Same<U1>>::Output;

    assert_eq!(<U5BitAndU1 as Unsigned>::to_u64(), <U1 as Unsigned>::to_u64());
}
#[test]
#[allow(non_snake_case)]
fn test_5_BitOr_1() {
    type A = UInt<UInt<UInt<UTerm, B1>, B0>, B1>;
    type B = UInt<UTerm, B1>;
    type U5 = UInt<UInt<UInt<UTerm, B1>, B0>, B1>;

    #[allow(non_camel_case_types)]
    type U5BitOrU1 = <<A as BitOr<B>>::Output as Same<U5>>::Output;

    assert_eq!(<U5BitOrU1 as Unsigned>::to_u64(), <U5 as Unsigned>::to_u64());
}
#[test]
#[allow(non_snake_case)]
fn test_5_BitXor_1() {
    type A = UInt<UInt<UInt<UTerm, B1>, B0>, B1>;
    type B = UInt<UTerm, B1>;
    type U4 = UInt<UInt<UInt<UTerm, B1>, B0>, B0>;

    #[allow(non_camel_case_types)]
    type U5BitXorU1 = <<A as BitXor<B>>::Output as Same<U4>>::Output;

    assert_eq!(<U5BitXorU1 as Unsigned>::to_u64(), <U4 as Unsigned>::to_u64());
}
#[test]
#[allow(non_snake_case)]
fn test_5_Shl_1() {
    type A = UInt<UInt<UInt<UTerm, B1>, B0>, B1>;
    type B = UInt<UTerm, B1>;
    type U10 = UInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>, B0>;

    #[allow(non_camel_case_types)]
    type U5ShlU1 = <<A as Shl<B>>::Output as Same<U10>>::Output;

    assert_eq!(<U5ShlU1 as Unsigned>::to_u64(), <U10 as Unsigned>::to_u64());
}
#[test]
#[allow(non_snake_case)]
fn test_5_Shr_1() {
    type A = UInt<UInt<UInt<UTerm, B1>, B0>, B1>;
    type B = UInt<UTerm, B1>;
    type U2 = UInt<UInt<UTerm, B1>, B0>;

    #[allow(non_camel_case_types)]
    type U5ShrU1 = <<A as Shr<B>>::Output as Same<U2>>::Output;

    assert_eq!(<U5ShrU1 as Unsigned>::to_u64(), <U2 as Unsigned>::to_u64());
}
#[test]
#[allow(non_snake_case)]
fn test_5_Add_1() {
    type A = UInt<UInt<UInt<UTerm, B1>, B0>, B1>;
    type B = UInt<UTerm, B1>;
    type U6 = UInt<UInt<UInt<UTerm, B1>, B1>, B0>;

    #[allow(non_camel_case_types)]
    type U5AddU1 = <<A as Add<B>>::Output as Same<U6>>::Output;

    assert_eq!(<U5AddU1 as Unsigned>::to_u64(), <U6 as Unsigned>::to_u64());
}
#[test]
#[allow(non_snake_case)]
fn test_5_Mul_1() {
    type A = UInt<UInt<UInt<UTerm, B1>, B0>, B1>;
    type B = UInt<UTerm, B1>;
    type U5 = UInt<UInt<UInt<UTerm, B1>, B0>, B1>;

    #[allow(non_camel_case_types)]
    type U5MulU1 = <<A as Mul<B>>::Output as Same<U5>>::Output;

    assert_eq!(<U5MulU1 as Unsigned>::to_u64(), <U5 as Unsigned>::to_u64());
}
#[test]
#[allow(non_snake_case)]
fn test_5_Pow_1() {
    type A = UInt<UInt<UInt<UTerm, B1>, B0>, B1>;
    type B = UInt<UTerm, B1>;
    type U5 = UInt<UInt<UInt<UTerm, B1>, B0>, B1>;

    #[allow(non_camel_case_types)]
    type U5PowU1 = <<A as Pow<B>>::Output as Same<U5>>::Output;

    assert_eq!(<U5PowU1 as Unsigned>::to_u64(), <U5 as Unsigned>::to_u64());
}
#[test]
#[allow(non_snake_case)]
fn test_5_Min_1() {
    type A = UInt<UInt<UInt<UTerm, B1>, B0>, B1>;
    type B = UInt<UTerm, B1>;
    type U1 = UInt<UTerm, B1>;

    #[allow(non_camel_case_types)]
    type U5MinU1 = <<A as Min<B>>::Output as Same<U1>>::Output;

    assert_eq!(<U5MinU1 as Unsigned>::to_u64(), <U1 as Unsigned>::to_u64());
}
#[test]
#[allow(non_snake_case)]
fn test_5_Max_1() {
    type A = UInt<UInt<UInt<UTerm, B1>, B0>, B1>;
    type B = UInt<UTerm, B1>;
    type U5 = UInt<UInt<UInt<UTerm, B1>, B0>, B1>;

    #[allow(non_camel_case_types)]
    type U5MaxU1 = <<A as Max<B>>::Output as Same<U5>>::Output;

    assert_eq!(<U5MaxU1 as Unsigned>::to_u64(), <U5 as Unsigned>::to_u64());
}
#[test]
#[allow(non_snake_case)]
fn test_5_Gcd_1() {
    type A = UInt<UInt<UInt<UTerm, B1>, B0>, B1>;
    type B = UInt<UTerm, B1>;
    type U1 = UInt<UTerm, B1>;

    #[allow(non_camel_case_types)]
    type U5GcdU1 = <<A as Gcd<B>>::Output as Same<U1>>::Output;

    assert_eq!(<U5GcdU1 as Unsigned>::to_u64(), <U1 as Unsigned>::to_u64());
}
#[test]
#[allow(non_snake_case)]
fn test_5_Sub_1() {
    type A = UInt<UInt<UInt<UTerm, B1>, B0>, B1>;
    type B = UInt<UTerm, B1>;
    type U4 = UInt<UInt<UInt<UTerm, B1>, B0>, B0>;

    #[allow(non_camel_case_types)]
    type U5SubU1 = <<A as Sub<B>>::Output as Same<U4>>::Output;

    assert_eq!(<U5SubU1 as Unsigned>::to_u64(), <U4 as Unsigned>::to_u64());
}
#[test]
#[allow(non_snake_case)]
fn test_5_Div_1() {
    type A = UInt<UInt<UInt<UTerm, B1>, B0>, B1>;
    type B = UInt<UTerm, B1>;
    type U5 = UInt<UInt<UInt<UTerm, B1>, B0>, B1>;

    #[allow(non_camel_case_types)]
    type U5DivU1 = <<A as Div<B>>::Output as Same<U5>>::Output;

    assert_eq!(<U5DivU1 as Unsigned>::to_u64(), <U5 as Unsigned>::to_u64());
}
#[test]
#[allow(non_snake_case)]
fn test_5_Rem_1() {
    type A = UInt<UInt<UInt<UTerm, B1>, B0>, B1>;
    type B = UInt<UTerm, B1>;
    type U0 = UTerm;

    #[allow(non_camel_case_types)]
    type U5RemU1 = <<A as Rem<B>>::Output as Same<U0>>::Output;

    assert_eq!(<U5RemU1 as Unsigned>::to_u64(), <U0 as Unsigned>::to_u64());
}
#[test]
#[allow(non_snake_case)]
fn test_5_PartialDiv_1() {
    type A = UInt<UInt<UInt<UTerm, B1>, B0>, B1>;
    type B = UInt<UTerm, B1>;
    type U5 = UInt<UInt<UInt<UTerm, B1>, B0>, B1>;

    #[allow(non_camel_case_types)]
    type U5PartialDivU1 = <<A as PartialDiv<B>>::Output as Same<U5>>::Output;

    assert_eq!(<U5PartialDivU1 as Unsigned>::to_u64(), <U5 as Unsigned>::to_u64());
}
#[test]
#[allow(non_snake_case)]
fn test_5_Cmp_1() {
    type A = UInt<UInt<UInt<UTerm, B1>, B0>, B1>;
    type B = UInt<UTerm, B1>;

    #[allow(non_camel_case_types)]
    type U5CmpU1 = <A as Cmp<B>>::Output;
    assert_eq!(<U5CmpU1 as Ord>::to_ordering(), Ordering::Greater);
}
#[test]
#[allow(non_snake_case)]
fn test_5_BitAnd_2() {
    type A = UInt<UInt<UInt<UTerm, B1>, B0>, B1>;
    type B = UInt<UInt<UTerm, B1>, B0>;
    type U0 = UTerm;

    #[allow(non_camel_case_types)]
    type U5BitAndU2 = <<A as BitAnd<B>>::Output as Same<U0>>::Output;

    assert_eq!(<U5BitAndU2 as Unsigned>::to_u64(), <U0 as Unsigned>::to_u64());
}
#[test]
#[allow(non_snake_case)]
fn test_5_BitOr_2() {
    type A = UInt<UInt<UInt<UTerm, B1>, B0>, B1>;
    type B = UInt<UInt<UTerm, B1>, B0>;
    type U7 = UInt<UInt<UInt<UTerm, B1>, B1>, B1>;

    #[allow(non_camel_case_types)]
    type U5BitOrU2 = <<A as BitOr<B>>::Output as Same<U7>>::Output;

    assert_eq!(<U5BitOrU2 as Unsigned>::to_u64(), <U7 as Unsigned>::to_u64());
}
#[test]
#[allow(non_snake_case)]
fn test_5_BitXor_2() {
    type A = UInt<UInt<UInt<UTerm, B1>, B0>, B1>;
    type B = UInt<UInt<UTerm, B1>, B0>;
    type U7 = UInt<UInt<UInt<UTerm, B1>, B1>, B1>;

    #[allow(non_camel_case_types)]
    type U5BitXorU2 = <<A as BitXor<B>>::Output as Same<U7>>::Output;

    assert_eq!(<U5BitXorU2 as Unsigned>::to_u64(), <U7 as Unsigned>::to_u64());
}
#[test]
#[allow(non_snake_case)]
fn test_5_Shl_2() {
    type A = UInt<UInt<UInt<UTerm, B1>, B0>, B1>;
    type B = UInt<UInt<UTerm, B1>, B0>;
    type U20 = UInt<UInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>, B0>, B0>;

    #[allow(non_camel_case_types)]
    type U5ShlU2 = <<A as Shl<B>>::Output as Same<U20>>::Output;

    assert_eq!(<U5ShlU2 as Unsigned>::to_u64(), <U20 as Unsigned>::to_u64());
}
#[test]
#[allow(non_snake_case)]
fn test_5_Shr_2() {
    type A = UInt<UInt<UInt<UTerm, B1>, B0>, B1>;
    type B = UInt<UInt<UTerm, B1>, B0>;
    type U1 = UInt<UTerm, B1>;

    #[allow(non_camel_case_types)]
    type U5ShrU2 = <<A as Shr<B>>::Output as Same<U1>>::Output;

    assert_eq!(<U5ShrU2 as Unsigned>::to_u64(), <U1 as Unsigned>::to_u64());
}
#[test]
#[allow(non_snake_case)]
fn test_5_Add_2() {
    type A = UInt<UInt<UInt<UTerm, B1>, B0>, B1>;
    type B = UInt<UInt<UTerm, B1>, B0>;
    type U7 = UInt<UInt<UInt<UTerm, B1>, B1>, B1>;

    #[allow(non_camel_case_types)]
    type U5AddU2 = <<A as Add<B>>::Output as Same<U7>>::Output;

    assert_eq!(<U5AddU2 as Unsigned>::to_u64(), <U7 as Unsigned>::to_u64());
}
#[test]
#[allow(non_snake_case)]
fn test_5_Mul_2() {
    type A = UInt<UInt<UInt<UTerm, B1>, B0>, B1>;
    type B = UInt<UInt<UTerm, B1>, B0>;
    type U10 = UInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>, B0>;

    #[allow(non_camel_case_types)]
    type U5MulU2 = <<A as Mul<B>>::Output as Same<U10>>::Output;

    assert_eq!(<U5MulU2 as Unsigned>::to_u64(), <U10 as Unsigned>::to_u64());
}
#[test]
#[allow(non_snake_case)]
fn test_5_Pow_2() {
    type A = UInt<UInt<UInt<UTerm, B1>, B0>, B1>;
    type B = UInt<UInt<UTerm, B1>, B0>;
    type U25 = UInt<UInt<UInt<UInt<UInt<UTerm, B1>, B1>, B0>, B0>, B1>;

    #[allow(non_camel_case_types)]
    type U5PowU2 = <<A as Pow<B>>::Output as Same<U25>>::Output;

    assert_eq!(<U5PowU2 as Unsigned>::to_u64(), <U25 as Unsigned>::to_u64());
}
#[test]
#[allow(non_snake_case)]
fn test_5_Min_2() {
    type A = UInt<UInt<UInt<UTerm, B1>, B0>, B1>;
    type B = UInt<UInt<UTerm, B1>, B0>;
    type U2 = UInt<UInt<UTerm, B1>, B0>;

    #[allow(non_camel_case_types)]
    type U5MinU2 = <<A as Min<B>>::Output as Same<U2>>::Output;

    assert_eq!(<U5MinU2 as Unsigned>::to_u64(), <U2 as Unsigned>::to_u64());
}
#[test]
#[allow(non_snake_case)]
fn test_5_Max_2() {
    type A = UInt<UInt<UInt<UTerm, B1>, B0>, B1>;
    type B = UInt<UInt<UTerm, B1>, B0>;
    type U5 = UInt<UInt<UInt<UTerm, B1>, B0>, B1>;

    #[allow(non_camel_case_types)]
    type U5MaxU2 = <<A as Max<B>>::Output as Same<U5>>::Output;

    assert_eq!(<U5MaxU2 as Unsigned>::to_u64(), <U5 as Unsigned>::to_u64());
}
#[test]
#[allow(non_snake_case)]
fn test_5_Gcd_2() {
    type A = UInt<UInt<UInt<UTerm, B1>, B0>, B1>;
    type B = UInt<UInt<UTerm, B1>, B0>;
    type U1 = UInt<UTerm, B1>;

    #[allow(non_camel_case_types)]
    type U5GcdU2 = <<A as Gcd<B>>::Output as Same<U1>>::Output;

    assert_eq!(<U5GcdU2 as Unsigned>::to_u64(), <U1 as Unsigned>::to_u64());
}
#[test]
#[allow(non_snake_case)]
fn test_5_Sub_2() {
    type A = UInt<UInt<UInt<UTerm, B1>, B0>, B1>;
    type B = UInt<UInt<UTerm, B1>, B0>;
    type U3 = UInt<UInt<UTerm, B1>, B1>;

    #[allow(non_camel_case_types)]
    type U5SubU2 = <<A as Sub<B>>::Output as Same<U3>>::Output;

    assert_eq!(<U5SubU2 as Unsigned>::to_u64(), <U3 as Unsigned>::to_u64());
}
#[test]
#[allow(non_snake_case)]
fn test_5_Div_2() {
    type A = UInt<UInt<UInt<UTerm, B1>, B0>, B1>;
    type B = UInt<UInt<UTerm, B1>, B0>;
    type U2 = UInt<UInt<UTerm, B1>, B0>;

    #[allow(non_camel_case_types)]
    type U5DivU2 = <<A as Div<B>>::Output as Same<U2>>::Output;

    assert_eq!(<U5DivU2 as Unsigned>::to_u64(), <U2 as Unsigned>::to_u64());
}
#[test]
#[allow(non_snake_case)]
fn test_5_Rem_2() {
    type A = UInt<UInt<UInt<UTerm, B1>, B0>, B1>;
    type B = UInt<UInt<UTerm, B1>, B0>;
    type U1 = UInt<UTerm, B1>;

    #[allow(non_camel_case_types)]
    type U5RemU2 = <<A as Rem<B>>::Output as Same<U1>>::Output;

    assert_eq!(<U5RemU2 as Unsigned>::to_u64(), <U1 as Unsigned>::to_u64());
}
#[test]
#[allow(non_snake_case)]
fn test_5_Cmp_2() {
    type A = UInt<UInt<UInt<UTerm, B1>, B0>, B1>;
    type B = UInt<UInt<UTerm, B1>, B0>;

    #[allow(non_camel_case_types)]
    type U5CmpU2 = <A as Cmp<B>>::Output;
    assert_eq!(<U5CmpU2 as Ord>::to_ordering(), Ordering::Greater);
}
#[test]
#[allow(non_snake_case)]
fn test_5_BitAnd_3() {
    type A = UInt<UInt<UInt<UTerm, B1>, B0>, B1>;
    type B = UInt<UInt<UTerm, B1>, B1>;
    type U1 = UInt<UTerm, B1>;

    #[allow(non_camel_case_types)]
    type U5BitAndU3 = <<A as BitAnd<B>>::Output as Same<U1>>::Output;

    assert_eq!(<U5BitAndU3 as Unsigned>::to_u64(), <U1 as Unsigned>::to_u64());
}
#[test]
#[allow(non_snake_case)]
fn test_5_BitOr_3() {
    type A = UInt<UInt<UInt<UTerm, B1>, B0>, B1>;
    type B = UInt<UInt<UTerm, B1>, B1>;
    type U7 = UInt<UInt<UInt<UTerm, B1>, B1>, B1>;

    #[allow(non_camel_case_types)]
    type U5BitOrU3 = <<A as BitOr<B>>::Output as Same<U7>>::Output;

    assert_eq!(<U5BitOrU3 as Unsigned>::to_u64(), <U7 as Unsigned>::to_u64());
}
#[test]
#[allow(non_snake_case)]
fn test_5_BitXor_3() {
    type A = UInt<UInt<UInt<UTerm, B1>, B0>, B1>;
    type B = UInt<UInt<UTerm, B1>, B1>;
    type U6 = UInt<UInt<UInt<UTerm, B1>, B1>, B0>;

    #[allow(non_camel_case_types)]
    type U5BitXorU3 = <<A as BitXor<B>>::Output as Same<U6>>::Output;

    assert_eq!(<U5BitXorU3 as Unsigned>::to_u64(), <U6 as Unsigned>::to_u64());
}
#[test]
#[allow(non_snake_case)]
fn test_5_Shl_3() {
    type A = UInt<UInt<UInt<UTerm, B1>, B0>, B1>;
    type B = UInt<UInt<UTerm, B1>, B1>;
    type U40 = UInt<UInt<UInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>, B0>, B0>, B0>;

    #[allow(non_camel_case_types)]
    type U5ShlU3 = <<A as Shl<B>>::Output as Same<U40>>::Output;

    assert_eq!(<U5ShlU3 as Unsigned>::to_u64(), <U40 as Unsigned>::to_u64());
}
#[test]
#[allow(non_snake_case)]
fn test_5_Shr_3() {
    type A = UInt<UInt<UInt<UTerm, B1>, B0>, B1>;
    type B = UInt<UInt<UTerm, B1>, B1>;
    type U0 = UTerm;

    #[allow(non_camel_case_types)]
    type U5ShrU3 = <<A as Shr<B>>::Output as Same<U0>>::Output;

    assert_eq!(<U5ShrU3 as Unsigned>::to_u64(), <U0 as Unsigned>::to_u64());
}
#[test]
#[allow(non_snake_case)]
fn test_5_Add_3() {
    type A = UInt<UInt<UInt<UTerm, B1>, B0>, B1>;
    type B = UInt<UInt<UTerm, B1>, B1>;
    type U8 = UInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>, B0>;

    #[allow(non_camel_case_types)]
    type U5AddU3 = <<A as Add<B>>::Output as Same<U8>>::Output;

    assert_eq!(<U5AddU3 as Unsigned>::to_u64(), <U8 as Unsigned>::to_u64());
}
#[test]
#[allow(non_snake_case)]
fn test_5_Mul_3() {
    type A = UInt<UInt<UInt<UTerm, B1>, B0>, B1>;
    type B = UInt<UInt<UTerm, B1>, B1>;
    type U15 = UInt<UInt<UInt<UInt<UTerm, B1>, B1>, B1>, B1>;

    #[allow(non_camel_case_types)]
    type U5MulU3 = <<A as Mul<B>>::Output as Same<U15>>::Output;

    assert_eq!(<U5MulU3 as Unsigned>::to_u64(), <U15 as Unsigned>::to_u64());
}
#[test]
#[allow(non_snake_case)]
fn test_5_Pow_3() {
    type A = UInt<UInt<UInt<UTerm, B1>, B0>, B1>;
    type B = UInt<UInt<UTerm, B1>, B1>;
    type U125 = UInt<UInt<UInt<UInt<UInt<UInt<UInt<UTerm, B1>, B1>, B1>, B1>, B1>, B0>, B1>;

    #[allow(non_camel_case_types)]
    type U5PowU3 = <<A as Pow<B>>::Output as Same<U125>>::Output;

    assert_eq!(<U5PowU3 as Unsigned>::to_u64(), <U125 as Unsigned>::to_u64());
}
#[test]
#[allow(non_snake_case)]
fn test_5_Min_3() {
    type A = UInt<UInt<UInt<UTerm, B1>, B0>, B1>;
    type B = UInt<UInt<UTerm, B1>, B1>;
    type U3 = UInt<UInt<UTerm, B1>, B1>;

    #[allow(non_camel_case_types)]
    type U5MinU3 = <<A as Min<B>>::Output as Same<U3>>::Output;

    assert_eq!(<U5MinU3 as Unsigned>::to_u64(), <U3 as Unsigned>::to_u64());
}
#[test]
#[allow(non_snake_case)]
fn test_5_Max_3() {
    type A = UInt<UInt<UInt<UTerm, B1>, B0>, B1>;
    type B = UInt<UInt<UTerm, B1>, B1>;
    type U5 = UInt<UInt<UInt<UTerm, B1>, B0>, B1>;

    #[allow(non_camel_case_types)]
    type U5MaxU3 = <<A as Max<B>>::Output as Same<U5>>::Output;

    assert_eq!(<U5MaxU3 as Unsigned>::to_u64(), <U5 as Unsigned>::to_u64());
}
#[test]
#[allow(non_snake_case)]
fn test_5_Gcd_3() {
    type A = UInt<UInt<UInt<UTerm, B1>, B0>, B1>;
    type B = UInt<UInt<UTerm, B1>, B1>;
    type U1 = UInt<UTerm, B1>;

    #[allow(non_camel_case_types)]
    type U5GcdU3 = <<A as Gcd<B>>::Output as Same<U1>>::Output;

    assert_eq!(<U5GcdU3 as Unsigned>::to_u64(), <U1 as Unsigned>::to_u64());
}
#[test]
#[allow(non_snake_case)]
fn test_5_Sub_3() {
    type A = UInt<UInt<UInt<UTerm, B1>, B0>, B1>;
    type B = UInt<UInt<UTerm, B1>, B1>;
    type U2 = UInt<UInt<UTerm, B1>, B0>;

    #[allow(non_camel_case_types)]
    type U5SubU3 = <<A as Sub<B>>::Output as Same<U2>>::Output;

    assert_eq!(<U5SubU3 as Unsigned>::to_u64(), <U2 as Unsigned>::to_u64());
}
#[test]
#[allow(non_snake_case)]
fn test_5_Div_3() {
    type A = UInt<UInt<UInt<UTerm, B1>, B0>, B1>;
    type B = UInt<UInt<UTerm, B1>, B1>;
    type U1 = UInt<UTerm, B1>;

    #[allow(non_camel_case_types)]
    type U5DivU3 = <<A as Div<B>>::Output as Same<U1>>::Output;

    assert_eq!(<U5DivU3 as Unsigned>::to_u64(), <U1 as Unsigned>::to_u64());
}
#[test]
#[allow(non_snake_case)]
fn test_5_Rem_3() {
    type A = UInt<UInt<UInt<UTerm, B1>, B0>, B1>;
    type B = UInt<UInt<UTerm, B1>, B1>;
    type U2 = UInt<UInt<UTerm, B1>, B0>;

    #[allow(non_camel_case_types)]
    type U5RemU3 = <<A as Rem<B>>::Output as Same<U2>>::Output;

    assert_eq!(<U5RemU3 as Unsigned>::to_u64(), <U2 as Unsigned>::to_u64());
}
#[test]
#[allow(non_snake_case)]
fn test_5_Cmp_3() {
    type A = UInt<UInt<UInt<UTerm, B1>, B0>, B1>;
    type B = UInt<UInt<UTerm, B1>, B1>;

    #[allow(non_camel_case_types)]
    type U5CmpU3 = <A as Cmp<B>>::Output;
    assert_eq!(<U5CmpU3 as Ord>::to_ordering(), Ordering::Greater);
}
#[test]
#[allow(non_snake_case)]
fn test_5_BitAnd_4() {
    type A = UInt<UInt<UInt<UTerm, B1>, B0>, B1>;
    type B = UInt<UInt<UInt<UTerm, B1>, B0>, B0>;
    type U4 = UInt<UInt<UInt<UTerm, B1>, B0>, B0>;

    #[allow(non_camel_case_types)]
    type U5BitAndU4 = <<A as BitAnd<B>>::Output as Same<U4>>::Output;

    assert_eq!(<U5BitAndU4 as Unsigned>::to_u64(), <U4 as Unsigned>::to_u64());
}
#[test]
#[allow(non_snake_case)]
fn test_5_BitOr_4() {
    type A = UInt<UInt<UInt<UTerm, B1>, B0>, B1>;
    type B = UInt<UInt<UInt<UTerm, B1>, B0>, B0>;
    type U5 = UInt<UInt<UInt<UTerm, B1>, B0>, B1>;

    #[allow(non_camel_case_types)]
    type U5BitOrU4 = <<A as BitOr<B>>::Output as Same<U5>>::Output;

    assert_eq!(<U5BitOrU4 as Unsigned>::to_u64(), <U5 as Unsigned>::to_u64());
}
#[test]
#[allow(non_snake_case)]
fn test_5_BitXor_4() {
    type A = UInt<UInt<UInt<UTerm, B1>, B0>, B1>;
    type B = UInt<UInt<UInt<UTerm, B1>, B0>, B0>;
    type U1 = UInt<UTerm, B1>;

    #[allow(non_camel_case_types)]
    type U5BitXorU4 = <<A as BitXor<B>>::Output as Same<U1>>::Output;

    assert_eq!(<U5BitXorU4 as Unsigned>::to_u64(), <U1 as Unsigned>::to_u64());
}
#[test]
#[allow(non_snake_case)]
fn test_5_Shl_4() {
    type A = UInt<UInt<UInt<UTerm, B1>, B0>, B1>;
    type B = UInt<UInt<UInt<UTerm, B1>, B0>, B0>;
    type U80 = UInt<UInt<UInt<UInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>, B0>, B0>, B0>, B0>;

    #[allow(non_camel_case_types)]
    type U5ShlU4 = <<A as Shl<B>>::Output as Same<U80>>::Output;

    assert_eq!(<U5ShlU4 as Unsigned>::to_u64(), <U80 as Unsigned>::to_u64());
}
#[test]
#[allow(non_snake_case)]
fn test_5_Shr_4() {
    type A = UInt<UInt<UInt<UTerm, B1>, B0>, B1>;
    type B = UInt<UInt<UInt<UTerm, B1>, B0>, B0>;
    type U0 = UTerm;

    #[allow(non_camel_case_types)]
    type U5ShrU4 = <<A as Shr<B>>::Output as Same<U0>>::Output;

    assert_eq!(<U5ShrU4 as Unsigned>::to_u64(), <U0 as Unsigned>::to_u64());
}
#[test]
#[allow(non_snake_case)]
fn test_5_Add_4() {
    type A = UInt<UInt<UInt<UTerm, B1>, B0>, B1>;
    type B = UInt<UInt<UInt<UTerm, B1>, B0>, B0>;
    type U9 = UInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>, B1>;

    #[allow(non_camel_case_types)]
    type U5AddU4 = <<A as Add<B>>::Output as Same<U9>>::Output;

    assert_eq!(<U5AddU4 as Unsigned>::to_u64(), <U9 as Unsigned>::to_u64());
}
#[test]
#[allow(non_snake_case)]
fn test_5_Mul_4() {
    type A = UInt<UInt<UInt<UTerm, B1>, B0>, B1>;
    type B = UInt<UInt<UInt<UTerm, B1>, B0>, B0>;
    type U20 = UInt<UInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>, B0>, B0>;

    #[allow(non_camel_case_types)]
    type U5MulU4 = <<A as Mul<B>>::Output as Same<U20>>::Output;

    assert_eq!(<U5MulU4 as Unsigned>::to_u64(), <U20 as Unsigned>::to_u64());
}
#[test]
#[allow(non_snake_case)]
fn test_5_Pow_4() {
    type A = UInt<UInt<UInt<UTerm, B1>, B0>, B1>;
    type B = UInt<UInt<UInt<UTerm, B1>, B0>, B0>;
    type U625 = UInt<UInt<UInt<UInt<UInt<UInt<UInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>, B1>, B1>, B1>, B0>, B0>, B0>, B1>;

    #[allow(non_camel_case_types)]
    type U5PowU4 = <<A as Pow<B>>::Output as Same<U625>>::Output;

    assert_eq!(<U5PowU4 as Unsigned>::to_u64(), <U625 as Unsigned>::to_u64());
}
#[test]
#[allow(non_snake_case)]
fn test_5_Min_4() {
    type A = UInt<UInt<UInt<UTerm, B1>, B0>, B1>;
    type B = UInt<UInt<UInt<UTerm, B1>, B0>, B0>;
    type U4 = UInt<UInt<UInt<UTerm, B1>, B0>, B0>;

    #[allow(non_camel_case_types)]
    type U5MinU4 = <<A as Min<B>>::Output as Same<U4>>::Output;

    assert_eq!(<U5MinU4 as Unsigned>::to_u64(), <U4 as Unsigned>::to_u64());
}
#[test]
#[allow(non_snake_case)]
fn test_5_Max_4() {
    type A = UInt<UInt<UInt<UTerm, B1>, B0>, B1>;
    type B = UInt<UInt<UInt<UTerm, B1>, B0>, B0>;
    type U5 = UInt<UInt<UInt<UTerm, B1>, B0>, B1>;

    #[allow(non_camel_case_types)]
    type U5MaxU4 = <<A as Max<B>>::Output as Same<U5>>::Output;

    assert_eq!(<U5MaxU4 as Unsigned>::to_u64(), <U5 as Unsigned>::to_u64());
}
#[test]
#[allow(non_snake_case)]
fn test_5_Gcd_4() {
    type A = UInt<UInt<UInt<UTerm, B1>, B0>, B1>;
    type B = UInt<UInt<UInt<UTerm, B1>, B0>, B0>;
    type U1 = UInt<UTerm, B1>;

    #[allow(non_camel_case_types)]
    type U5GcdU4 = <<A as Gcd<B>>::Output as Same<U1>>::Output;

    assert_eq!(<U5GcdU4 as Unsigned>::to_u64(), <U1 as Unsigned>::to_u64());
}
#[test]
#[allow(non_snake_case)]
fn test_5_Sub_4() {
    type A = UInt<UInt<UInt<UTerm, B1>, B0>, B1>;
    type B = UInt<UInt<UInt<UTerm, B1>, B0>, B0>;
    type U1 = UInt<UTerm, B1>;

    #[allow(non_camel_case_types)]
    type U5SubU4 = <<A as Sub<B>>::Output as Same<U1>>::Output;

    assert_eq!(<U5SubU4 as Unsigned>::to_u64(), <U1 as Unsigned>::to_u64());
}
#[test]
#[allow(non_snake_case)]
fn test_5_Div_4() {
    type A = UInt<UInt<UInt<UTerm, B1>, B0>, B1>;
    type B = UInt<UInt<UInt<UTerm, B1>, B0>, B0>;
    type U1 = UInt<UTerm, B1>;

    #[allow(non_camel_case_types)]
    type U5DivU4 = <<A as Div<B>>::Output as Same<U1>>::Output;

    assert_eq!(<U5DivU4 as Unsigned>::to_u64(), <U1 as Unsigned>::to_u64());
}
#[test]
#[allow(non_snake_case)]
fn test_5_Rem_4() {
    type A = UInt<UInt<UInt<UTerm, B1>, B0>, B1>;
    type B = UInt<UInt<UInt<UTerm, B1>, B0>, B0>;
    type U1 = UInt<UTerm, B1>;

    #[allow(non_camel_case_types)]
    type U5RemU4 = <<A as Rem<B>>::Output as Same<U1>>::Output;

    assert_eq!(<U5RemU4 as Unsigned>::to_u64(), <U1 as Unsigned>::to_u64());
}
#[test]
#[allow(non_snake_case)]
fn test_5_Cmp_4() {
    type A = UInt<UInt<UInt<UTerm, B1>, B0>, B1>;
    type B = UInt<UInt<UInt<UTerm, B1>, B0>, B0>;

    #[allow(non_camel_case_types)]
    type U5CmpU4 = <A as Cmp<B>>::Output;
    assert_eq!(<U5CmpU4 as Ord>::to_ordering(), Ordering::Greater);
}
#[test]
#[allow(non_snake_case)]
fn test_5_BitAnd_5() {
    type A = UInt<UInt<UInt<UTerm, B1>, B0>, B1>;
    type B = UInt<UInt<UInt<UTerm, B1>, B0>, B1>;
    type U5 = UInt<UInt<UInt<UTerm, B1>, B0>, B1>;

    #[allow(non_camel_case_types)]
    type U5BitAndU5 = <<A as BitAnd<B>>::Output as Same<U5>>::Output;

    assert_eq!(<U5BitAndU5 as Unsigned>::to_u64(), <U5 as Unsigned>::to_u64());
}
#[test]
#[allow(non_snake_case)]
fn test_5_BitOr_5() {
    type A = UInt<UInt<UInt<UTerm, B1>, B0>, B1>;
    type B = UInt<UInt<UInt<UTerm, B1>, B0>, B1>;
    type U5 = UInt<UInt<UInt<UTerm, B1>, B0>, B1>;

    #[allow(non_camel_case_types)]
    type U5BitOrU5 = <<A as BitOr<B>>::Output as Same<U5>>::Output;

    assert_eq!(<U5BitOrU5 as Unsigned>::to_u64(), <U5 as Unsigned>::to_u64());
}
#[test]
#[allow(non_snake_case)]
fn test_5_BitXor_5() {
    type A = UInt<UInt<UInt<UTerm, B1>, B0>, B1>;
    type B = UInt<UInt<UInt<UTerm, B1>, B0>, B1>;
    type U0 = UTerm;

    #[allow(non_camel_case_types)]
    type U5BitXorU5 = <<A as BitXor<B>>::Output as Same<U0>>::Output;

    assert_eq!(<U5BitXorU5 as Unsigned>::to_u64(), <U0 as Unsigned>::to_u64());
}
#[test]
#[allow(non_snake_case)]
fn test_5_Shl_5() {
    type A = UInt<UInt<UInt<UTerm, B1>, B0>, B1>;
    type B = UInt<UInt<UInt<UTerm, B1>, B0>, B1>;
    type U160 = UInt<UInt<UInt<UInt<UInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>, B0>, B0>, B0>, B0>, B0>;

    #[allow(non_camel_case_types)]
    type U5ShlU5 = <<A as Shl<B>>::Output as Same<U160>>::Output;

    assert_eq!(<U5ShlU5 as Unsigned>::to_u64(), <U160 as Unsigned>::to_u64());
}
#[test]
#[allow(non_snake_case)]
fn test_5_Shr_5() {
    type A = UInt<UInt<UInt<UTerm, B1>, B0>, B1>;
    type B = UInt<UInt<UInt<UTerm, B1>, B0>, B1>;
    type U0 = UTerm;

    #[allow(non_camel_case_types)]
    type U5ShrU5 = <<A as Shr<B>>::Output as Same<U0>>::Output;

    assert_eq!(<U5ShrU5 as Unsigned>::to_u64(), <U0 as Unsigned>::to_u64());
}
#[test]
#[allow(non_snake_case)]
fn test_5_Add_5() {
    type A = UInt<UInt<UInt<UTerm, B1>, B0>, B1>;
    type B = UInt<UInt<UInt<UTerm, B1>, B0>, B1>;
    type U10 = UInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>, B0>;

    #[allow(non_camel_case_types)]
    type U5AddU5 = <<A as Add<B>>::Output as Same<U10>>::Output;

    assert_eq!(<U5AddU5 as Unsigned>::to_u64(), <U10 as Unsigned>::to_u64());
}
#[test]
#[allow(non_snake_case)]
fn test_5_Mul_5() {
    type A = UInt<UInt<UInt<UTerm, B1>, B0>, B1>;
    type B = UInt<UInt<UInt<UTerm, B1>, B0>, B1>;
    type U25 = UInt<UInt<UInt<UInt<UInt<UTerm, B1>, B1>, B0>, B0>, B1>;

    #[allow(non_camel_case_types)]
    type U5MulU5 = <<A as Mul<B>>::Output as Same<U25>>::Output;

    assert_eq!(<U5MulU5 as Unsigned>::to_u64(), <U25 as Unsigned>::to_u64());
}
#[test]
#[allow(non_snake_case)]
fn test_5_Pow_5() {
    type A = UInt<UInt<UInt<UTerm, B1>, B0>, B1>;
    type B = UInt<UInt<UInt<UTerm, B1>, B0>, B1>;
    type U3125 = UInt<UInt<UInt<UInt<UInt<UInt<UInt<UInt<UInt<UInt<UInt<UInt<UTerm, B1>, B1>, B0>, B0>, B0>, B0>, B1>, B1>, B0>, B1>, B0>, B1>;

    #[allow(non_camel_case_types)]
    type U5PowU5 = <<A as Pow<B>>::Output as Same<U3125>>::Output;

    assert_eq!(<U5PowU5 as Unsigned>::to_u64(), <U3125 as Unsigned>::to_u64());
}
#[test]
#[allow(non_snake_case)]
fn test_5_Min_5() {
    type A = UInt<UInt<UInt<UTerm, B1>, B0>, B1>;
    type B = UInt<UInt<UInt<UTerm, B1>, B0>, B1>;
    type U5 = UInt<UInt<UInt<UTerm, B1>, B0>, B1>;

    #[allow(non_camel_case_types)]
    type U5MinU5 = <<A as Min<B>>::Output as Same<U5>>::Output;

    assert_eq!(<U5MinU5 as Unsigned>::to_u64(), <U5 as Unsigned>::to_u64());
}
#[test]
#[allow(non_snake_case)]
fn test_5_Max_5() {
    type A = UInt<UInt<UInt<UTerm, B1>, B0>, B1>;
    type B = UInt<UInt<UInt<UTerm, B1>, B0>, B1>;
    type U5 = UInt<UInt<UInt<UTerm, B1>, B0>, B1>;

    #[allow(non_camel_case_types)]
    type U5MaxU5 = <<A as Max<B>>::Output as Same<U5>>::Output;

    assert_eq!(<U5MaxU5 as Unsigned>::to_u64(), <U5 as Unsigned>::to_u64());
}
#[test]
#[allow(non_snake_case)]
fn test_5_Gcd_5() {
    type A = UInt<UInt<UInt<UTerm, B1>, B0>, B1>;
    type B = UInt<UInt<UInt<UTerm, B1>, B0>, B1>;
    type U5 = UInt<UInt<UInt<UTerm, B1>, B0>, B1>;

    #[allow(non_camel_case_types)]
    type U5GcdU5 = <<A as Gcd<B>>::Output as Same<U5>>::Output;

    assert_eq!(<U5GcdU5 as Unsigned>::to_u64(), <U5 as Unsigned>::to_u64());
}
#[test]
#[allow(non_snake_case)]
fn test_5_Sub_5() {
    type A = UInt<UInt<UInt<UTerm, B1>, B0>, B1>;
    type B = UInt<UInt<UInt<UTerm, B1>, B0>, B1>;
    type U0 = UTerm;

    #[allow(non_camel_case_types)]
    type U5SubU5 = <<A as Sub<B>>::Output as Same<U0>>::Output;

    assert_eq!(<U5SubU5 as Unsigned>::to_u64(), <U0 as Unsigned>::to_u64());
}
#[test]
#[allow(non_snake_case)]
fn test_5_Div_5() {
    type A = UInt<UInt<UInt<UTerm, B1>, B0>, B1>;
    type B = UInt<UInt<UInt<UTerm, B1>, B0>, B1>;
    type U1 = UInt<UTerm, B1>;

    #[allow(non_camel_case_types)]
    type U5DivU5 = <<A as Div<B>>::Output as Same<U1>>::Output;

    assert_eq!(<U5DivU5 as Unsigned>::to_u64(), <U1 as Unsigned>::to_u64());
}
#[test]
#[allow(non_snake_case)]
fn test_5_Rem_5() {
    type A = UInt<UInt<UInt<UTerm, B1>, B0>, B1>;
    type B = UInt<UInt<UInt<UTerm, B1>, B0>, B1>;
    type U0 = UTerm;

    #[allow(non_camel_case_types)]
    type U5RemU5 = <<A as Rem<B>>::Output as Same<U0>>::Output;

    assert_eq!(<U5RemU5 as Unsigned>::to_u64(), <U0 as Unsigned>::to_u64());
}
#[test]
#[allow(non_snake_case)]
fn test_5_PartialDiv_5() {
    type A = UInt<UInt<UInt<UTerm, B1>, B0>, B1>;
    type B = UInt<UInt<UInt<UTerm, B1>, B0>, B1>;
    type U1 = UInt<UTerm, B1>;

    #[allow(non_camel_case_types)]
    type U5PartialDivU5 = <<A as PartialDiv<B>>::Output as Same<U1>>::Output;

    assert_eq!(<U5PartialDivU5 as Unsigned>::to_u64(), <U1 as Unsigned>::to_u64());
}
#[test]
#[allow(non_snake_case)]
fn test_5_Cmp_5() {
    type A = UInt<UInt<UInt<UTerm, B1>, B0>, B1>;
    type B = UInt<UInt<UInt<UTerm, B1>, B0>, B1>;

    #[allow(non_camel_case_types)]
    type U5CmpU5 = <A as Cmp<B>>::Output;
    assert_eq!(<U5CmpU5 as Ord>::to_ordering(), Ordering::Equal);
}
#[test]
#[allow(non_snake_case)]
fn test_N5_Add_N5() {
    type A = NInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>>;
    type B = NInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>>;
    type N10 = NInt<UInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>, B0>>;

    #[allow(non_camel_case_types)]
    type N5AddN5 = <<A as Add<B>>::Output as Same<N10>>::Output;

    assert_eq!(<N5AddN5 as Integer>::to_i64(), <N10 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_N5_Sub_N5() {
    type A = NInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>>;
    type B = NInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>>;
    type _0 = Z0;

    #[allow(non_camel_case_types)]
    type N5SubN5 = <<A as Sub<B>>::Output as Same<_0>>::Output;

    assert_eq!(<N5SubN5 as Integer>::to_i64(), <_0 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_N5_Mul_N5() {
    type A = NInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>>;
    type B = NInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>>;
    type P25 = PInt<UInt<UInt<UInt<UInt<UInt<UTerm, B1>, B1>, B0>, B0>, B1>>;

    #[allow(non_camel_case_types)]
    type N5MulN5 = <<A as Mul<B>>::Output as Same<P25>>::Output;

    assert_eq!(<N5MulN5 as Integer>::to_i64(), <P25 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_N5_Min_N5() {
    type A = NInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>>;
    type B = NInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>>;
    type N5 = NInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>>;

    #[allow(non_camel_case_types)]
    type N5MinN5 = <<A as Min<B>>::Output as Same<N5>>::Output;

    assert_eq!(<N5MinN5 as Integer>::to_i64(), <N5 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_N5_Max_N5() {
    type A = NInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>>;
    type B = NInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>>;
    type N5 = NInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>>;

    #[allow(non_camel_case_types)]
    type N5MaxN5 = <<A as Max<B>>::Output as Same<N5>>::Output;

    assert_eq!(<N5MaxN5 as Integer>::to_i64(), <N5 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_N5_Gcd_N5() {
    type A = NInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>>;
    type B = NInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>>;
    type P5 = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>>;

    #[allow(non_camel_case_types)]
    type N5GcdN5 = <<A as Gcd<B>>::Output as Same<P5>>::Output;

    assert_eq!(<N5GcdN5 as Integer>::to_i64(), <P5 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_N5_Div_N5() {
    type A = NInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>>;
    type B = NInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>>;
    type P1 = PInt<UInt<UTerm, B1>>;

    #[allow(non_camel_case_types)]
    type N5DivN5 = <<A as Div<B>>::Output as Same<P1>>::Output;

    assert_eq!(<N5DivN5 as Integer>::to_i64(), <P1 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_N5_Rem_N5() {
    type A = NInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>>;
    type B = NInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>>;
    type _0 = Z0;

    #[allow(non_camel_case_types)]
    type N5RemN5 = <<A as Rem<B>>::Output as Same<_0>>::Output;

    assert_eq!(<N5RemN5 as Integer>::to_i64(), <_0 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_N5_PartialDiv_N5() {
    type A = NInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>>;
    type B = NInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>>;
    type P1 = PInt<UInt<UTerm, B1>>;

    #[allow(non_camel_case_types)]
    type N5PartialDivN5 = <<A as PartialDiv<B>>::Output as Same<P1>>::Output;

    assert_eq!(<N5PartialDivN5 as Integer>::to_i64(), <P1 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_N5_Cmp_N5() {
    type A = NInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>>;
    type B = NInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>>;

    #[allow(non_camel_case_types)]
    type N5CmpN5 = <A as Cmp<B>>::Output;
    assert_eq!(<N5CmpN5 as Ord>::to_ordering(), Ordering::Equal);
}
#[test]
#[allow(non_snake_case)]
fn test_N5_Add_N4() {
    type A = NInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>>;
    type B = NInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>>;
    type N9 = NInt<UInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>, B1>>;

    #[allow(non_camel_case_types)]
    type N5AddN4 = <<A as Add<B>>::Output as Same<N9>>::Output;

    assert_eq!(<N5AddN4 as Integer>::to_i64(), <N9 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_N5_Sub_N4() {
    type A = NInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>>;
    type B = NInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>>;
    type N1 = NInt<UInt<UTerm, B1>>;

    #[allow(non_camel_case_types)]
    type N5SubN4 = <<A as Sub<B>>::Output as Same<N1>>::Output;

    assert_eq!(<N5SubN4 as Integer>::to_i64(), <N1 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_N5_Mul_N4() {
    type A = NInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>>;
    type B = NInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>>;
    type P20 = PInt<UInt<UInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>, B0>, B0>>;

    #[allow(non_camel_case_types)]
    type N5MulN4 = <<A as Mul<B>>::Output as Same<P20>>::Output;

    assert_eq!(<N5MulN4 as Integer>::to_i64(), <P20 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_N5_Min_N4() {
    type A = NInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>>;
    type B = NInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>>;
    type N5 = NInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>>;

    #[allow(non_camel_case_types)]
    type N5MinN4 = <<A as Min<B>>::Output as Same<N5>>::Output;

    assert_eq!(<N5MinN4 as Integer>::to_i64(), <N5 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_N5_Max_N4() {
    type A = NInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>>;
    type B = NInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>>;
    type N4 = NInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>>;

    #[allow(non_camel_case_types)]
    type N5MaxN4 = <<A as Max<B>>::Output as Same<N4>>::Output;

    assert_eq!(<N5MaxN4 as Integer>::to_i64(), <N4 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_N5_Gcd_N4() {
    type A = NInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>>;
    type B = NInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>>;
    type P1 = PInt<UInt<UTerm, B1>>;

    #[allow(non_camel_case_types)]
    type N5GcdN4 = <<A as Gcd<B>>::Output as Same<P1>>::Output;

    assert_eq!(<N5GcdN4 as Integer>::to_i64(), <P1 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_N5_Div_N4() {
    type A = NInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>>;
    type B = NInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>>;
    type P1 = PInt<UInt<UTerm, B1>>;

    #[allow(non_camel_case_types)]
    type N5DivN4 = <<A as Div<B>>::Output as Same<P1>>::Output;

    assert_eq!(<N5DivN4 as Integer>::to_i64(), <P1 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_N5_Rem_N4() {
    type A = NInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>>;
    type B = NInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>>;
    type N1 = NInt<UInt<UTerm, B1>>;

    #[allow(non_camel_case_types)]
    type N5RemN4 = <<A as Rem<B>>::Output as Same<N1>>::Output;

    assert_eq!(<N5RemN4 as Integer>::to_i64(), <N1 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_N5_Cmp_N4() {
    type A = NInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>>;
    type B = NInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>>;

    #[allow(non_camel_case_types)]
    type N5CmpN4 = <A as Cmp<B>>::Output;
    assert_eq!(<N5CmpN4 as Ord>::to_ordering(), Ordering::Less);
}
#[test]
#[allow(non_snake_case)]
fn test_N5_Add_N3() {
    type A = NInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>>;
    type B = NInt<UInt<UInt<UTerm, B1>, B1>>;
    type N8 = NInt<UInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>, B0>>;

    #[allow(non_camel_case_types)]
    type N5AddN3 = <<A as Add<B>>::Output as Same<N8>>::Output;

    assert_eq!(<N5AddN3 as Integer>::to_i64(), <N8 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_N5_Sub_N3() {
    type A = NInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>>;
    type B = NInt<UInt<UInt<UTerm, B1>, B1>>;
    type N2 = NInt<UInt<UInt<UTerm, B1>, B0>>;

    #[allow(non_camel_case_types)]
    type N5SubN3 = <<A as Sub<B>>::Output as Same<N2>>::Output;

    assert_eq!(<N5SubN3 as Integer>::to_i64(), <N2 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_N5_Mul_N3() {
    type A = NInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>>;
    type B = NInt<UInt<UInt<UTerm, B1>, B1>>;
    type P15 = PInt<UInt<UInt<UInt<UInt<UTerm, B1>, B1>, B1>, B1>>;

    #[allow(non_camel_case_types)]
    type N5MulN3 = <<A as Mul<B>>::Output as Same<P15>>::Output;

    assert_eq!(<N5MulN3 as Integer>::to_i64(), <P15 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_N5_Min_N3() {
    type A = NInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>>;
    type B = NInt<UInt<UInt<UTerm, B1>, B1>>;
    type N5 = NInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>>;

    #[allow(non_camel_case_types)]
    type N5MinN3 = <<A as Min<B>>::Output as Same<N5>>::Output;

    assert_eq!(<N5MinN3 as Integer>::to_i64(), <N5 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_N5_Max_N3() {
    type A = NInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>>;
    type B = NInt<UInt<UInt<UTerm, B1>, B1>>;
    type N3 = NInt<UInt<UInt<UTerm, B1>, B1>>;

    #[allow(non_camel_case_types)]
    type N5MaxN3 = <<A as Max<B>>::Output as Same<N3>>::Output;

    assert_eq!(<N5MaxN3 as Integer>::to_i64(), <N3 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_N5_Gcd_N3() {
    type A = NInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>>;
    type B = NInt<UInt<UInt<UTerm, B1>, B1>>;
    type P1 = PInt<UInt<UTerm, B1>>;

    #[allow(non_camel_case_types)]
    type N5GcdN3 = <<A as Gcd<B>>::Output as Same<P1>>::Output;

    assert_eq!(<N5GcdN3 as Integer>::to_i64(), <P1 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_N5_Div_N3() {
    type A = NInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>>;
    type B = NInt<UInt<UInt<UTerm, B1>, B1>>;
    type P1 = PInt<UInt<UTerm, B1>>;

    #[allow(non_camel_case_types)]
    type N5DivN3 = <<A as Div<B>>::Output as Same<P1>>::Output;

    assert_eq!(<N5DivN3 as Integer>::to_i64(), <P1 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_N5_Rem_N3() {
    type A = NInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>>;
    type B = NInt<UInt<UInt<UTerm, B1>, B1>>;
    type N2 = NInt<UInt<UInt<UTerm, B1>, B0>>;

    #[allow(non_camel_case_types)]
    type N5RemN3 = <<A as Rem<B>>::Output as Same<N2>>::Output;

    assert_eq!(<N5RemN3 as Integer>::to_i64(), <N2 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_N5_Cmp_N3() {
    type A = NInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>>;
    type B = NInt<UInt<UInt<UTerm, B1>, B1>>;

    #[allow(non_camel_case_types)]
    type N5CmpN3 = <A as Cmp<B>>::Output;
    assert_eq!(<N5CmpN3 as Ord>::to_ordering(), Ordering::Less);
}
#[test]
#[allow(non_snake_case)]
fn test_N5_Add_N2() {
    type A = NInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>>;
    type B = NInt<UInt<UInt<UTerm, B1>, B0>>;
    type N7 = NInt<UInt<UInt<UInt<UTerm, B1>, B1>, B1>>;

    #[allow(non_camel_case_types)]
    type N5AddN2 = <<A as Add<B>>::Output as Same<N7>>::Output;

    assert_eq!(<N5AddN2 as Integer>::to_i64(), <N7 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_N5_Sub_N2() {
    type A = NInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>>;
    type B = NInt<UInt<UInt<UTerm, B1>, B0>>;
    type N3 = NInt<UInt<UInt<UTerm, B1>, B1>>;

    #[allow(non_camel_case_types)]
    type N5SubN2 = <<A as Sub<B>>::Output as Same<N3>>::Output;

    assert_eq!(<N5SubN2 as Integer>::to_i64(), <N3 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_N5_Mul_N2() {
    type A = NInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>>;
    type B = NInt<UInt<UInt<UTerm, B1>, B0>>;
    type P10 = PInt<UInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>, B0>>;

    #[allow(non_camel_case_types)]
    type N5MulN2 = <<A as Mul<B>>::Output as Same<P10>>::Output;

    assert_eq!(<N5MulN2 as Integer>::to_i64(), <P10 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_N5_Min_N2() {
    type A = NInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>>;
    type B = NInt<UInt<UInt<UTerm, B1>, B0>>;
    type N5 = NInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>>;

    #[allow(non_camel_case_types)]
    type N5MinN2 = <<A as Min<B>>::Output as Same<N5>>::Output;

    assert_eq!(<N5MinN2 as Integer>::to_i64(), <N5 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_N5_Max_N2() {
    type A = NInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>>;
    type B = NInt<UInt<UInt<UTerm, B1>, B0>>;
    type N2 = NInt<UInt<UInt<UTerm, B1>, B0>>;

    #[allow(non_camel_case_types)]
    type N5MaxN2 = <<A as Max<B>>::Output as Same<N2>>::Output;

    assert_eq!(<N5MaxN2 as Integer>::to_i64(), <N2 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_N5_Gcd_N2() {
    type A = NInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>>;
    type B = NInt<UInt<UInt<UTerm, B1>, B0>>;
    type P1 = PInt<UInt<UTerm, B1>>;

    #[allow(non_camel_case_types)]
    type N5GcdN2 = <<A as Gcd<B>>::Output as Same<P1>>::Output;

    assert_eq!(<N5GcdN2 as Integer>::to_i64(), <P1 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_N5_Div_N2() {
    type A = NInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>>;
    type B = NInt<UInt<UInt<UTerm, B1>, B0>>;
    type P2 = PInt<UInt<UInt<UTerm, B1>, B0>>;

    #[allow(non_camel_case_types)]
    type N5DivN2 = <<A as Div<B>>::Output as Same<P2>>::Output;

    assert_eq!(<N5DivN2 as Integer>::to_i64(), <P2 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_N5_Rem_N2() {
    type A = NInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>>;
    type B = NInt<UInt<UInt<UTerm, B1>, B0>>;
    type N1 = NInt<UInt<UTerm, B1>>;

    #[allow(non_camel_case_types)]
    type N5RemN2 = <<A as Rem<B>>::Output as Same<N1>>::Output;

    assert_eq!(<N5RemN2 as Integer>::to_i64(), <N1 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_N5_Cmp_N2() {
    type A = NInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>>;
    type B = NInt<UInt<UInt<UTerm, B1>, B0>>;

    #[allow(non_camel_case_types)]
    type N5CmpN2 = <A as Cmp<B>>::Output;
    assert_eq!(<N5CmpN2 as Ord>::to_ordering(), Ordering::Less);
}
#[test]
#[allow(non_snake_case)]
fn test_N5_Add_N1() {
    type A = NInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>>;
    type B = NInt<UInt<UTerm, B1>>;
    type N6 = NInt<UInt<UInt<UInt<UTerm, B1>, B1>, B0>>;

    #[allow(non_camel_case_types)]
    type N5AddN1 = <<A as Add<B>>::Output as Same<N6>>::Output;

    assert_eq!(<N5AddN1 as Integer>::to_i64(), <N6 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_N5_Sub_N1() {
    type A = NInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>>;
    type B = NInt<UInt<UTerm, B1>>;
    type N4 = NInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>>;

    #[allow(non_camel_case_types)]
    type N5SubN1 = <<A as Sub<B>>::Output as Same<N4>>::Output;

    assert_eq!(<N5SubN1 as Integer>::to_i64(), <N4 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_N5_Mul_N1() {
    type A = NInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>>;
    type B = NInt<UInt<UTerm, B1>>;
    type P5 = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>>;

    #[allow(non_camel_case_types)]
    type N5MulN1 = <<A as Mul<B>>::Output as Same<P5>>::Output;

    assert_eq!(<N5MulN1 as Integer>::to_i64(), <P5 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_N5_Min_N1() {
    type A = NInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>>;
    type B = NInt<UInt<UTerm, B1>>;
    type N5 = NInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>>;

    #[allow(non_camel_case_types)]
    type N5MinN1 = <<A as Min<B>>::Output as Same<N5>>::Output;

    assert_eq!(<N5MinN1 as Integer>::to_i64(), <N5 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_N5_Max_N1() {
    type A = NInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>>;
    type B = NInt<UInt<UTerm, B1>>;
    type N1 = NInt<UInt<UTerm, B1>>;

    #[allow(non_camel_case_types)]
    type N5MaxN1 = <<A as Max<B>>::Output as Same<N1>>::Output;

    assert_eq!(<N5MaxN1 as Integer>::to_i64(), <N1 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_N5_Gcd_N1() {
    type A = NInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>>;
    type B = NInt<UInt<UTerm, B1>>;
    type P1 = PInt<UInt<UTerm, B1>>;

    #[allow(non_camel_case_types)]
    type N5GcdN1 = <<A as Gcd<B>>::Output as Same<P1>>::Output;

    assert_eq!(<N5GcdN1 as Integer>::to_i64(), <P1 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_N5_Div_N1() {
    type A = NInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>>;
    type B = NInt<UInt<UTerm, B1>>;
    type P5 = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>>;

    #[allow(non_camel_case_types)]
    type N5DivN1 = <<A as Div<B>>::Output as Same<P5>>::Output;

    assert_eq!(<N5DivN1 as Integer>::to_i64(), <P5 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_N5_Rem_N1() {
    type A = NInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>>;
    type B = NInt<UInt<UTerm, B1>>;
    type _0 = Z0;

    #[allow(non_camel_case_types)]
    type N5RemN1 = <<A as Rem<B>>::Output as Same<_0>>::Output;

    assert_eq!(<N5RemN1 as Integer>::to_i64(), <_0 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_N5_PartialDiv_N1() {
    type A = NInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>>;
    type B = NInt<UInt<UTerm, B1>>;
    type P5 = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>>;

    #[allow(non_camel_case_types)]
    type N5PartialDivN1 = <<A as PartialDiv<B>>::Output as Same<P5>>::Output;

    assert_eq!(<N5PartialDivN1 as Integer>::to_i64(), <P5 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_N5_Cmp_N1() {
    type A = NInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>>;
    type B = NInt<UInt<UTerm, B1>>;

    #[allow(non_camel_case_types)]
    type N5CmpN1 = <A as Cmp<B>>::Output;
    assert_eq!(<N5CmpN1 as Ord>::to_ordering(), Ordering::Less);
}
#[test]
#[allow(non_snake_case)]
fn test_N5_Add__0() {
    type A = NInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>>;
    type B = Z0;
    type N5 = NInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>>;

    #[allow(non_camel_case_types)]
    type N5Add_0 = <<A as Add<B>>::Output as Same<N5>>::Output;

    assert_eq!(<N5Add_0 as Integer>::to_i64(), <N5 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_N5_Sub__0() {
    type A = NInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>>;
    type B = Z0;
    type N5 = NInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>>;

    #[allow(non_camel_case_types)]
    type N5Sub_0 = <<A as Sub<B>>::Output as Same<N5>>::Output;

    assert_eq!(<N5Sub_0 as Integer>::to_i64(), <N5 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_N5_Mul__0() {
    type A = NInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>>;
    type B = Z0;
    type _0 = Z0;

    #[allow(non_camel_case_types)]
    type N5Mul_0 = <<A as Mul<B>>::Output as Same<_0>>::Output;

    assert_eq!(<N5Mul_0 as Integer>::to_i64(), <_0 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_N5_Min__0() {
    type A = NInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>>;
    type B = Z0;
    type N5 = NInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>>;

    #[allow(non_camel_case_types)]
    type N5Min_0 = <<A as Min<B>>::Output as Same<N5>>::Output;

    assert_eq!(<N5Min_0 as Integer>::to_i64(), <N5 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_N5_Max__0() {
    type A = NInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>>;
    type B = Z0;
    type _0 = Z0;

    #[allow(non_camel_case_types)]
    type N5Max_0 = <<A as Max<B>>::Output as Same<_0>>::Output;

    assert_eq!(<N5Max_0 as Integer>::to_i64(), <_0 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_N5_Gcd__0() {
    type A = NInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>>;
    type B = Z0;
    type P5 = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>>;

    #[allow(non_camel_case_types)]
    type N5Gcd_0 = <<A as Gcd<B>>::Output as Same<P5>>::Output;

    assert_eq!(<N5Gcd_0 as Integer>::to_i64(), <P5 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_N5_Pow__0() {
    type A = NInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>>;
    type B = Z0;
    type P1 = PInt<UInt<UTerm, B1>>;

    #[allow(non_camel_case_types)]
    type N5Pow_0 = <<A as Pow<B>>::Output as Same<P1>>::Output;

    assert_eq!(<N5Pow_0 as Integer>::to_i64(), <P1 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_N5_Cmp__0() {
    type A = NInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>>;
    type B = Z0;

    #[allow(non_camel_case_types)]
    type N5Cmp_0 = <A as Cmp<B>>::Output;
    assert_eq!(<N5Cmp_0 as Ord>::to_ordering(), Ordering::Less);
}
#[test]
#[allow(non_snake_case)]
fn test_N5_Add_P1() {
    type A = NInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>>;
    type B = PInt<UInt<UTerm, B1>>;
    type N4 = NInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>>;

    #[allow(non_camel_case_types)]
    type N5AddP1 = <<A as Add<B>>::Output as Same<N4>>::Output;

    assert_eq!(<N5AddP1 as Integer>::to_i64(), <N4 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_N5_Sub_P1() {
    type A = NInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>>;
    type B = PInt<UInt<UTerm, B1>>;
    type N6 = NInt<UInt<UInt<UInt<UTerm, B1>, B1>, B0>>;

    #[allow(non_camel_case_types)]
    type N5SubP1 = <<A as Sub<B>>::Output as Same<N6>>::Output;

    assert_eq!(<N5SubP1 as Integer>::to_i64(), <N6 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_N5_Mul_P1() {
    type A = NInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>>;
    type B = PInt<UInt<UTerm, B1>>;
    type N5 = NInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>>;

    #[allow(non_camel_case_types)]
    type N5MulP1 = <<A as Mul<B>>::Output as Same<N5>>::Output;

    assert_eq!(<N5MulP1 as Integer>::to_i64(), <N5 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_N5_Min_P1() {
    type A = NInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>>;
    type B = PInt<UInt<UTerm, B1>>;
    type N5 = NInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>>;

    #[allow(non_camel_case_types)]
    type N5MinP1 = <<A as Min<B>>::Output as Same<N5>>::Output;

    assert_eq!(<N5MinP1 as Integer>::to_i64(), <N5 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_N5_Max_P1() {
    type A = NInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>>;
    type B = PInt<UInt<UTerm, B1>>;
    type P1 = PInt<UInt<UTerm, B1>>;

    #[allow(non_camel_case_types)]
    type N5MaxP1 = <<A as Max<B>>::Output as Same<P1>>::Output;

    assert_eq!(<N5MaxP1 as Integer>::to_i64(), <P1 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_N5_Gcd_P1() {
    type A = NInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>>;
    type B = PInt<UInt<UTerm, B1>>;
    type P1 = PInt<UInt<UTerm, B1>>;

    #[allow(non_camel_case_types)]
    type N5GcdP1 = <<A as Gcd<B>>::Output as Same<P1>>::Output;

    assert_eq!(<N5GcdP1 as Integer>::to_i64(), <P1 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_N5_Div_P1() {
    type A = NInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>>;
    type B = PInt<UInt<UTerm, B1>>;
    type N5 = NInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>>;

    #[allow(non_camel_case_types)]
    type N5DivP1 = <<A as Div<B>>::Output as Same<N5>>::Output;

    assert_eq!(<N5DivP1 as Integer>::to_i64(), <N5 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_N5_Rem_P1() {
    type A = NInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>>;
    type B = PInt<UInt<UTerm, B1>>;
    type _0 = Z0;

    #[allow(non_camel_case_types)]
    type N5RemP1 = <<A as Rem<B>>::Output as Same<_0>>::Output;

    assert_eq!(<N5RemP1 as Integer>::to_i64(), <_0 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_N5_PartialDiv_P1() {
    type A = NInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>>;
    type B = PInt<UInt<UTerm, B1>>;
    type N5 = NInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>>;

    #[allow(non_camel_case_types)]
    type N5PartialDivP1 = <<A as PartialDiv<B>>::Output as Same<N5>>::Output;

    assert_eq!(<N5PartialDivP1 as Integer>::to_i64(), <N5 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_N5_Pow_P1() {
    type A = NInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>>;
    type B = PInt<UInt<UTerm, B1>>;
    type N5 = NInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>>;

    #[allow(non_camel_case_types)]
    type N5PowP1 = <<A as Pow<B>>::Output as Same<N5>>::Output;

    assert_eq!(<N5PowP1 as Integer>::to_i64(), <N5 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_N5_Cmp_P1() {
    type A = NInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>>;
    type B = PInt<UInt<UTerm, B1>>;

    #[allow(non_camel_case_types)]
    type N5CmpP1 = <A as Cmp<B>>::Output;
    assert_eq!(<N5CmpP1 as Ord>::to_ordering(), Ordering::Less);
}
#[test]
#[allow(non_snake_case)]
fn test_N5_Add_P2() {
    type A = NInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>>;
    type B = PInt<UInt<UInt<UTerm, B1>, B0>>;
    type N3 = NInt<UInt<UInt<UTerm, B1>, B1>>;

    #[allow(non_camel_case_types)]
    type N5AddP2 = <<A as Add<B>>::Output as Same<N3>>::Output;

    assert_eq!(<N5AddP2 as Integer>::to_i64(), <N3 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_N5_Sub_P2() {
    type A = NInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>>;
    type B = PInt<UInt<UInt<UTerm, B1>, B0>>;
    type N7 = NInt<UInt<UInt<UInt<UTerm, B1>, B1>, B1>>;

    #[allow(non_camel_case_types)]
    type N5SubP2 = <<A as Sub<B>>::Output as Same<N7>>::Output;

    assert_eq!(<N5SubP2 as Integer>::to_i64(), <N7 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_N5_Mul_P2() {
    type A = NInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>>;
    type B = PInt<UInt<UInt<UTerm, B1>, B0>>;
    type N10 = NInt<UInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>, B0>>;

    #[allow(non_camel_case_types)]
    type N5MulP2 = <<A as Mul<B>>::Output as Same<N10>>::Output;

    assert_eq!(<N5MulP2 as Integer>::to_i64(), <N10 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_N5_Min_P2() {
    type A = NInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>>;
    type B = PInt<UInt<UInt<UTerm, B1>, B0>>;
    type N5 = NInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>>;

    #[allow(non_camel_case_types)]
    type N5MinP2 = <<A as Min<B>>::Output as Same<N5>>::Output;

    assert_eq!(<N5MinP2 as Integer>::to_i64(), <N5 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_N5_Max_P2() {
    type A = NInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>>;
    type B = PInt<UInt<UInt<UTerm, B1>, B0>>;
    type P2 = PInt<UInt<UInt<UTerm, B1>, B0>>;

    #[allow(non_camel_case_types)]
    type N5MaxP2 = <<A as Max<B>>::Output as Same<P2>>::Output;

    assert_eq!(<N5MaxP2 as Integer>::to_i64(), <P2 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_N5_Gcd_P2() {
    type A = NInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>>;
    type B = PInt<UInt<UInt<UTerm, B1>, B0>>;
    type P1 = PInt<UInt<UTerm, B1>>;

    #[allow(non_camel_case_types)]
    type N5GcdP2 = <<A as Gcd<B>>::Output as Same<P1>>::Output;

    assert_eq!(<N5GcdP2 as Integer>::to_i64(), <P1 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_N5_Div_P2() {
    type A = NInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>>;
    type B = PInt<UInt<UInt<UTerm, B1>, B0>>;
    type N2 = NInt<UInt<UInt<UTerm, B1>, B0>>;

    #[allow(non_camel_case_types)]
    type N5DivP2 = <<A as Div<B>>::Output as Same<N2>>::Output;

    assert_eq!(<N5DivP2 as Integer>::to_i64(), <N2 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_N5_Rem_P2() {
    type A = NInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>>;
    type B = PInt<UInt<UInt<UTerm, B1>, B0>>;
    type N1 = NInt<UInt<UTerm, B1>>;

    #[allow(non_camel_case_types)]
    type N5RemP2 = <<A as Rem<B>>::Output as Same<N1>>::Output;

    assert_eq!(<N5RemP2 as Integer>::to_i64(), <N1 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_N5_Pow_P2() {
    type A = NInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>>;
    type B = PInt<UInt<UInt<UTerm, B1>, B0>>;
    type P25 = PInt<UInt<UInt<UInt<UInt<UInt<UTerm, B1>, B1>, B0>, B0>, B1>>;

    #[allow(non_camel_case_types)]
    type N5PowP2 = <<A as Pow<B>>::Output as Same<P25>>::Output;

    assert_eq!(<N5PowP2 as Integer>::to_i64(), <P25 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_N5_Cmp_P2() {
    type A = NInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>>;
    type B = PInt<UInt<UInt<UTerm, B1>, B0>>;

    #[allow(non_camel_case_types)]
    type N5CmpP2 = <A as Cmp<B>>::Output;
    assert_eq!(<N5CmpP2 as Ord>::to_ordering(), Ordering::Less);
}
#[test]
#[allow(non_snake_case)]
fn test_N5_Add_P3() {
    type A = NInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>>;
    type B = PInt<UInt<UInt<UTerm, B1>, B1>>;
    type N2 = NInt<UInt<UInt<UTerm, B1>, B0>>;

    #[allow(non_camel_case_types)]
    type N5AddP3 = <<A as Add<B>>::Output as Same<N2>>::Output;

    assert_eq!(<N5AddP3 as Integer>::to_i64(), <N2 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_N5_Sub_P3() {
    type A = NInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>>;
    type B = PInt<UInt<UInt<UTerm, B1>, B1>>;
    type N8 = NInt<UInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>, B0>>;

    #[allow(non_camel_case_types)]
    type N5SubP3 = <<A as Sub<B>>::Output as Same<N8>>::Output;

    assert_eq!(<N5SubP3 as Integer>::to_i64(), <N8 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_N5_Mul_P3() {
    type A = NInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>>;
    type B = PInt<UInt<UInt<UTerm, B1>, B1>>;
    type N15 = NInt<UInt<UInt<UInt<UInt<UTerm, B1>, B1>, B1>, B1>>;

    #[allow(non_camel_case_types)]
    type N5MulP3 = <<A as Mul<B>>::Output as Same<N15>>::Output;

    assert_eq!(<N5MulP3 as Integer>::to_i64(), <N15 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_N5_Min_P3() {
    type A = NInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>>;
    type B = PInt<UInt<UInt<UTerm, B1>, B1>>;
    type N5 = NInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>>;

    #[allow(non_camel_case_types)]
    type N5MinP3 = <<A as Min<B>>::Output as Same<N5>>::Output;

    assert_eq!(<N5MinP3 as Integer>::to_i64(), <N5 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_N5_Max_P3() {
    type A = NInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>>;
    type B = PInt<UInt<UInt<UTerm, B1>, B1>>;
    type P3 = PInt<UInt<UInt<UTerm, B1>, B1>>;

    #[allow(non_camel_case_types)]
    type N5MaxP3 = <<A as Max<B>>::Output as Same<P3>>::Output;

    assert_eq!(<N5MaxP3 as Integer>::to_i64(), <P3 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_N5_Gcd_P3() {
    type A = NInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>>;
    type B = PInt<UInt<UInt<UTerm, B1>, B1>>;
    type P1 = PInt<UInt<UTerm, B1>>;

    #[allow(non_camel_case_types)]
    type N5GcdP3 = <<A as Gcd<B>>::Output as Same<P1>>::Output;

    assert_eq!(<N5GcdP3 as Integer>::to_i64(), <P1 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_N5_Div_P3() {
    type A = NInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>>;
    type B = PInt<UInt<UInt<UTerm, B1>, B1>>;
    type N1 = NInt<UInt<UTerm, B1>>;

    #[allow(non_camel_case_types)]
    type N5DivP3 = <<A as Div<B>>::Output as Same<N1>>::Output;

    assert_eq!(<N5DivP3 as Integer>::to_i64(), <N1 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_N5_Rem_P3() {
    type A = NInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>>;
    type B = PInt<UInt<UInt<UTerm, B1>, B1>>;
    type N2 = NInt<UInt<UInt<UTerm, B1>, B0>>;

    #[allow(non_camel_case_types)]
    type N5RemP3 = <<A as Rem<B>>::Output as Same<N2>>::Output;

    assert_eq!(<N5RemP3 as Integer>::to_i64(), <N2 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_N5_Pow_P3() {
    type A = NInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>>;
    type B = PInt<UInt<UInt<UTerm, B1>, B1>>;
    type N125 = NInt<UInt<UInt<UInt<UInt<UInt<UInt<UInt<UTerm, B1>, B1>, B1>, B1>, B1>, B0>, B1>>;

    #[allow(non_camel_case_types)]
    type N5PowP3 = <<A as Pow<B>>::Output as Same<N125>>::Output;

    assert_eq!(<N5PowP3 as Integer>::to_i64(), <N125 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_N5_Cmp_P3() {
    type A = NInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>>;
    type B = PInt<UInt<UInt<UTerm, B1>, B1>>;

    #[allow(non_camel_case_types)]
    type N5CmpP3 = <A as Cmp<B>>::Output;
    assert_eq!(<N5CmpP3 as Ord>::to_ordering(), Ordering::Less);
}
#[test]
#[allow(non_snake_case)]
fn test_N5_Add_P4() {
    type A = NInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>>;
    type B = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>>;
    type N1 = NInt<UInt<UTerm, B1>>;

    #[allow(non_camel_case_types)]
    type N5AddP4 = <<A as Add<B>>::Output as Same<N1>>::Output;

    assert_eq!(<N5AddP4 as Integer>::to_i64(), <N1 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_N5_Sub_P4() {
    type A = NInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>>;
    type B = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>>;
    type N9 = NInt<UInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>, B1>>;

    #[allow(non_camel_case_types)]
    type N5SubP4 = <<A as Sub<B>>::Output as Same<N9>>::Output;

    assert_eq!(<N5SubP4 as Integer>::to_i64(), <N9 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_N5_Mul_P4() {
    type A = NInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>>;
    type B = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>>;
    type N20 = NInt<UInt<UInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>, B0>, B0>>;

    #[allow(non_camel_case_types)]
    type N5MulP4 = <<A as Mul<B>>::Output as Same<N20>>::Output;

    assert_eq!(<N5MulP4 as Integer>::to_i64(), <N20 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_N5_Min_P4() {
    type A = NInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>>;
    type B = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>>;
    type N5 = NInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>>;

    #[allow(non_camel_case_types)]
    type N5MinP4 = <<A as Min<B>>::Output as Same<N5>>::Output;

    assert_eq!(<N5MinP4 as Integer>::to_i64(), <N5 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_N5_Max_P4() {
    type A = NInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>>;
    type B = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>>;
    type P4 = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>>;

    #[allow(non_camel_case_types)]
    type N5MaxP4 = <<A as Max<B>>::Output as Same<P4>>::Output;

    assert_eq!(<N5MaxP4 as Integer>::to_i64(), <P4 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_N5_Gcd_P4() {
    type A = NInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>>;
    type B = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>>;
    type P1 = PInt<UInt<UTerm, B1>>;

    #[allow(non_camel_case_types)]
    type N5GcdP4 = <<A as Gcd<B>>::Output as Same<P1>>::Output;

    assert_eq!(<N5GcdP4 as Integer>::to_i64(), <P1 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_N5_Div_P4() {
    type A = NInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>>;
    type B = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>>;
    type N1 = NInt<UInt<UTerm, B1>>;

    #[allow(non_camel_case_types)]
    type N5DivP4 = <<A as Div<B>>::Output as Same<N1>>::Output;

    assert_eq!(<N5DivP4 as Integer>::to_i64(), <N1 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_N5_Rem_P4() {
    type A = NInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>>;
    type B = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>>;
    type N1 = NInt<UInt<UTerm, B1>>;

    #[allow(non_camel_case_types)]
    type N5RemP4 = <<A as Rem<B>>::Output as Same<N1>>::Output;

    assert_eq!(<N5RemP4 as Integer>::to_i64(), <N1 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_N5_Pow_P4() {
    type A = NInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>>;
    type B = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>>;
    type P625 = PInt<UInt<UInt<UInt<UInt<UInt<UInt<UInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>, B1>, B1>, B1>, B0>, B0>, B0>, B1>>;

    #[allow(non_camel_case_types)]
    type N5PowP4 = <<A as Pow<B>>::Output as Same<P625>>::Output;

    assert_eq!(<N5PowP4 as Integer>::to_i64(), <P625 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_N5_Cmp_P4() {
    type A = NInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>>;
    type B = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>>;

    #[allow(non_camel_case_types)]
    type N5CmpP4 = <A as Cmp<B>>::Output;
    assert_eq!(<N5CmpP4 as Ord>::to_ordering(), Ordering::Less);
}
#[test]
#[allow(non_snake_case)]
fn test_N5_Add_P5() {
    type A = NInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>>;
    type B = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>>;
    type _0 = Z0;

    #[allow(non_camel_case_types)]
    type N5AddP5 = <<A as Add<B>>::Output as Same<_0>>::Output;

    assert_eq!(<N5AddP5 as Integer>::to_i64(), <_0 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_N5_Sub_P5() {
    type A = NInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>>;
    type B = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>>;
    type N10 = NInt<UInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>, B0>>;

    #[allow(non_camel_case_types)]
    type N5SubP5 = <<A as Sub<B>>::Output as Same<N10>>::Output;

    assert_eq!(<N5SubP5 as Integer>::to_i64(), <N10 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_N5_Mul_P5() {
    type A = NInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>>;
    type B = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>>;
    type N25 = NInt<UInt<UInt<UInt<UInt<UInt<UTerm, B1>, B1>, B0>, B0>, B1>>;

    #[allow(non_camel_case_types)]
    type N5MulP5 = <<A as Mul<B>>::Output as Same<N25>>::Output;

    assert_eq!(<N5MulP5 as Integer>::to_i64(), <N25 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_N5_Min_P5() {
    type A = NInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>>;
    type B = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>>;
    type N5 = NInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>>;

    #[allow(non_camel_case_types)]
    type N5MinP5 = <<A as Min<B>>::Output as Same<N5>>::Output;

    assert_eq!(<N5MinP5 as Integer>::to_i64(), <N5 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_N5_Max_P5() {
    type A = NInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>>;
    type B = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>>;
    type P5 = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>>;

    #[allow(non_camel_case_types)]
    type N5MaxP5 = <<A as Max<B>>::Output as Same<P5>>::Output;

    assert_eq!(<N5MaxP5 as Integer>::to_i64(), <P5 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_N5_Gcd_P5() {
    type A = NInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>>;
    type B = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>>;
    type P5 = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>>;

    #[allow(non_camel_case_types)]
    type N5GcdP5 = <<A as Gcd<B>>::Output as Same<P5>>::Output;

    assert_eq!(<N5GcdP5 as Integer>::to_i64(), <P5 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_N5_Div_P5() {
    type A = NInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>>;
    type B = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>>;
    type N1 = NInt<UInt<UTerm, B1>>;

    #[allow(non_camel_case_types)]
    type N5DivP5 = <<A as Div<B>>::Output as Same<N1>>::Output;

    assert_eq!(<N5DivP5 as Integer>::to_i64(), <N1 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_N5_Rem_P5() {
    type A = NInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>>;
    type B = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>>;
    type _0 = Z0;

    #[allow(non_camel_case_types)]
    type N5RemP5 = <<A as Rem<B>>::Output as Same<_0>>::Output;

    assert_eq!(<N5RemP5 as Integer>::to_i64(), <_0 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_N5_PartialDiv_P5() {
    type A = NInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>>;
    type B = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>>;
    type N1 = NInt<UInt<UTerm, B1>>;

    #[allow(non_camel_case_types)]
    type N5PartialDivP5 = <<A as PartialDiv<B>>::Output as Same<N1>>::Output;

    assert_eq!(<N5PartialDivP5 as Integer>::to_i64(), <N1 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_N5_Pow_P5() {
    type A = NInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>>;
    type B = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>>;
    type N3125 = NInt<UInt<UInt<UInt<UInt<UInt<UInt<UInt<UInt<UInt<UInt<UInt<UInt<UTerm, B1>, B1>, B0>, B0>, B0>, B0>, B1>, B1>, B0>, B1>, B0>, B1>>;

    #[allow(non_camel_case_types)]
    type N5PowP5 = <<A as Pow<B>>::Output as Same<N3125>>::Output;

    assert_eq!(<N5PowP5 as Integer>::to_i64(), <N3125 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_N5_Cmp_P5() {
    type A = NInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>>;
    type B = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>>;

    #[allow(non_camel_case_types)]
    type N5CmpP5 = <A as Cmp<B>>::Output;
    assert_eq!(<N5CmpP5 as Ord>::to_ordering(), Ordering::Less);
}
#[test]
#[allow(non_snake_case)]
fn test_N4_Add_N5() {
    type A = NInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>>;
    type B = NInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>>;
    type N9 = NInt<UInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>, B1>>;

    #[allow(non_camel_case_types)]
    type N4AddN5 = <<A as Add<B>>::Output as Same<N9>>::Output;

    assert_eq!(<N4AddN5 as Integer>::to_i64(), <N9 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_N4_Sub_N5() {
    type A = NInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>>;
    type B = NInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>>;
    type P1 = PInt<UInt<UTerm, B1>>;

    #[allow(non_camel_case_types)]
    type N4SubN5 = <<A as Sub<B>>::Output as Same<P1>>::Output;

    assert_eq!(<N4SubN5 as Integer>::to_i64(), <P1 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_N4_Mul_N5() {
    type A = NInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>>;
    type B = NInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>>;
    type P20 = PInt<UInt<UInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>, B0>, B0>>;

    #[allow(non_camel_case_types)]
    type N4MulN5 = <<A as Mul<B>>::Output as Same<P20>>::Output;

    assert_eq!(<N4MulN5 as Integer>::to_i64(), <P20 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_N4_Min_N5() {
    type A = NInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>>;
    type B = NInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>>;
    type N5 = NInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>>;

    #[allow(non_camel_case_types)]
    type N4MinN5 = <<A as Min<B>>::Output as Same<N5>>::Output;

    assert_eq!(<N4MinN5 as Integer>::to_i64(), <N5 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_N4_Max_N5() {
    type A = NInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>>;
    type B = NInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>>;
    type N4 = NInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>>;

    #[allow(non_camel_case_types)]
    type N4MaxN5 = <<A as Max<B>>::Output as Same<N4>>::Output;

    assert_eq!(<N4MaxN5 as Integer>::to_i64(), <N4 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_N4_Gcd_N5() {
    type A = NInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>>;
    type B = NInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>>;
    type P1 = PInt<UInt<UTerm, B1>>;

    #[allow(non_camel_case_types)]
    type N4GcdN5 = <<A as Gcd<B>>::Output as Same<P1>>::Output;

    assert_eq!(<N4GcdN5 as Integer>::to_i64(), <P1 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_N4_Div_N5() {
    type A = NInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>>;
    type B = NInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>>;
    type _0 = Z0;

    #[allow(non_camel_case_types)]
    type N4DivN5 = <<A as Div<B>>::Output as Same<_0>>::Output;

    assert_eq!(<N4DivN5 as Integer>::to_i64(), <_0 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_N4_Rem_N5() {
    type A = NInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>>;
    type B = NInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>>;
    type N4 = NInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>>;

    #[allow(non_camel_case_types)]
    type N4RemN5 = <<A as Rem<B>>::Output as Same<N4>>::Output;

    assert_eq!(<N4RemN5 as Integer>::to_i64(), <N4 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_N4_Cmp_N5() {
    type A = NInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>>;
    type B = NInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>>;

    #[allow(non_camel_case_types)]
    type N4CmpN5 = <A as Cmp<B>>::Output;
    assert_eq!(<N4CmpN5 as Ord>::to_ordering(), Ordering::Greater);
}
#[test]
#[allow(non_snake_case)]
fn test_N4_Add_N4() {
    type A = NInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>>;
    type B = NInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>>;
    type N8 = NInt<UInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>, B0>>;

    #[allow(non_camel_case_types)]
    type N4AddN4 = <<A as Add<B>>::Output as Same<N8>>::Output;

    assert_eq!(<N4AddN4 as Integer>::to_i64(), <N8 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_N4_Sub_N4() {
    type A = NInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>>;
    type B = NInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>>;
    type _0 = Z0;

    #[allow(non_camel_case_types)]
    type N4SubN4 = <<A as Sub<B>>::Output as Same<_0>>::Output;

    assert_eq!(<N4SubN4 as Integer>::to_i64(), <_0 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_N4_Mul_N4() {
    type A = NInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>>;
    type B = NInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>>;
    type P16 = PInt<UInt<UInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>, B0>, B0>>;

    #[allow(non_camel_case_types)]
    type N4MulN4 = <<A as Mul<B>>::Output as Same<P16>>::Output;

    assert_eq!(<N4MulN4 as Integer>::to_i64(), <P16 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_N4_Min_N4() {
    type A = NInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>>;
    type B = NInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>>;
    type N4 = NInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>>;

    #[allow(non_camel_case_types)]
    type N4MinN4 = <<A as Min<B>>::Output as Same<N4>>::Output;

    assert_eq!(<N4MinN4 as Integer>::to_i64(), <N4 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_N4_Max_N4() {
    type A = NInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>>;
    type B = NInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>>;
    type N4 = NInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>>;

    #[allow(non_camel_case_types)]
    type N4MaxN4 = <<A as Max<B>>::Output as Same<N4>>::Output;

    assert_eq!(<N4MaxN4 as Integer>::to_i64(), <N4 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_N4_Gcd_N4() {
    type A = NInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>>;
    type B = NInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>>;
    type P4 = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>>;

    #[allow(non_camel_case_types)]
    type N4GcdN4 = <<A as Gcd<B>>::Output as Same<P4>>::Output;

    assert_eq!(<N4GcdN4 as Integer>::to_i64(), <P4 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_N4_Div_N4() {
    type A = NInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>>;
    type B = NInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>>;
    type P1 = PInt<UInt<UTerm, B1>>;

    #[allow(non_camel_case_types)]
    type N4DivN4 = <<A as Div<B>>::Output as Same<P1>>::Output;

    assert_eq!(<N4DivN4 as Integer>::to_i64(), <P1 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_N4_Rem_N4() {
    type A = NInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>>;
    type B = NInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>>;
    type _0 = Z0;

    #[allow(non_camel_case_types)]
    type N4RemN4 = <<A as Rem<B>>::Output as Same<_0>>::Output;

    assert_eq!(<N4RemN4 as Integer>::to_i64(), <_0 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_N4_PartialDiv_N4() {
    type A = NInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>>;
    type B = NInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>>;
    type P1 = PInt<UInt<UTerm, B1>>;

    #[allow(non_camel_case_types)]
    type N4PartialDivN4 = <<A as PartialDiv<B>>::Output as Same<P1>>::Output;

    assert_eq!(<N4PartialDivN4 as Integer>::to_i64(), <P1 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_N4_Cmp_N4() {
    type A = NInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>>;
    type B = NInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>>;

    #[allow(non_camel_case_types)]
    type N4CmpN4 = <A as Cmp<B>>::Output;
    assert_eq!(<N4CmpN4 as Ord>::to_ordering(), Ordering::Equal);
}
#[test]
#[allow(non_snake_case)]
fn test_N4_Add_N3() {
    type A = NInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>>;
    type B = NInt<UInt<UInt<UTerm, B1>, B1>>;
    type N7 = NInt<UInt<UInt<UInt<UTerm, B1>, B1>, B1>>;

    #[allow(non_camel_case_types)]
    type N4AddN3 = <<A as Add<B>>::Output as Same<N7>>::Output;

    assert_eq!(<N4AddN3 as Integer>::to_i64(), <N7 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_N4_Sub_N3() {
    type A = NInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>>;
    type B = NInt<UInt<UInt<UTerm, B1>, B1>>;
    type N1 = NInt<UInt<UTerm, B1>>;

    #[allow(non_camel_case_types)]
    type N4SubN3 = <<A as Sub<B>>::Output as Same<N1>>::Output;

    assert_eq!(<N4SubN3 as Integer>::to_i64(), <N1 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_N4_Mul_N3() {
    type A = NInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>>;
    type B = NInt<UInt<UInt<UTerm, B1>, B1>>;
    type P12 = PInt<UInt<UInt<UInt<UInt<UTerm, B1>, B1>, B0>, B0>>;

    #[allow(non_camel_case_types)]
    type N4MulN3 = <<A as Mul<B>>::Output as Same<P12>>::Output;

    assert_eq!(<N4MulN3 as Integer>::to_i64(), <P12 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_N4_Min_N3() {
    type A = NInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>>;
    type B = NInt<UInt<UInt<UTerm, B1>, B1>>;
    type N4 = NInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>>;

    #[allow(non_camel_case_types)]
    type N4MinN3 = <<A as Min<B>>::Output as Same<N4>>::Output;

    assert_eq!(<N4MinN3 as Integer>::to_i64(), <N4 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_N4_Max_N3() {
    type A = NInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>>;
    type B = NInt<UInt<UInt<UTerm, B1>, B1>>;
    type N3 = NInt<UInt<UInt<UTerm, B1>, B1>>;

    #[allow(non_camel_case_types)]
    type N4MaxN3 = <<A as Max<B>>::Output as Same<N3>>::Output;

    assert_eq!(<N4MaxN3 as Integer>::to_i64(), <N3 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_N4_Gcd_N3() {
    type A = NInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>>;
    type B = NInt<UInt<UInt<UTerm, B1>, B1>>;
    type P1 = PInt<UInt<UTerm, B1>>;

    #[allow(non_camel_case_types)]
    type N4GcdN3 = <<A as Gcd<B>>::Output as Same<P1>>::Output;

    assert_eq!(<N4GcdN3 as Integer>::to_i64(), <P1 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_N4_Div_N3() {
    type A = NInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>>;
    type B = NInt<UInt<UInt<UTerm, B1>, B1>>;
    type P1 = PInt<UInt<UTerm, B1>>;

    #[allow(non_camel_case_types)]
    type N4DivN3 = <<A as Div<B>>::Output as Same<P1>>::Output;

    assert_eq!(<N4DivN3 as Integer>::to_i64(), <P1 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_N4_Rem_N3() {
    type A = NInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>>;
    type B = NInt<UInt<UInt<UTerm, B1>, B1>>;
    type N1 = NInt<UInt<UTerm, B1>>;

    #[allow(non_camel_case_types)]
    type N4RemN3 = <<A as Rem<B>>::Output as Same<N1>>::Output;

    assert_eq!(<N4RemN3 as Integer>::to_i64(), <N1 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_N4_Cmp_N3() {
    type A = NInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>>;
    type B = NInt<UInt<UInt<UTerm, B1>, B1>>;

    #[allow(non_camel_case_types)]
    type N4CmpN3 = <A as Cmp<B>>::Output;
    assert_eq!(<N4CmpN3 as Ord>::to_ordering(), Ordering::Less);
}
#[test]
#[allow(non_snake_case)]
fn test_N4_Add_N2() {
    type A = NInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>>;
    type B = NInt<UInt<UInt<UTerm, B1>, B0>>;
    type N6 = NInt<UInt<UInt<UInt<UTerm, B1>, B1>, B0>>;

    #[allow(non_camel_case_types)]
    type N4AddN2 = <<A as Add<B>>::Output as Same<N6>>::Output;

    assert_eq!(<N4AddN2 as Integer>::to_i64(), <N6 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_N4_Sub_N2() {
    type A = NInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>>;
    type B = NInt<UInt<UInt<UTerm, B1>, B0>>;
    type N2 = NInt<UInt<UInt<UTerm, B1>, B0>>;

    #[allow(non_camel_case_types)]
    type N4SubN2 = <<A as Sub<B>>::Output as Same<N2>>::Output;

    assert_eq!(<N4SubN2 as Integer>::to_i64(), <N2 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_N4_Mul_N2() {
    type A = NInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>>;
    type B = NInt<UInt<UInt<UTerm, B1>, B0>>;
    type P8 = PInt<UInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>, B0>>;

    #[allow(non_camel_case_types)]
    type N4MulN2 = <<A as Mul<B>>::Output as Same<P8>>::Output;

    assert_eq!(<N4MulN2 as Integer>::to_i64(), <P8 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_N4_Min_N2() {
    type A = NInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>>;
    type B = NInt<UInt<UInt<UTerm, B1>, B0>>;
    type N4 = NInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>>;

    #[allow(non_camel_case_types)]
    type N4MinN2 = <<A as Min<B>>::Output as Same<N4>>::Output;

    assert_eq!(<N4MinN2 as Integer>::to_i64(), <N4 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_N4_Max_N2() {
    type A = NInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>>;
    type B = NInt<UInt<UInt<UTerm, B1>, B0>>;
    type N2 = NInt<UInt<UInt<UTerm, B1>, B0>>;

    #[allow(non_camel_case_types)]
    type N4MaxN2 = <<A as Max<B>>::Output as Same<N2>>::Output;

    assert_eq!(<N4MaxN2 as Integer>::to_i64(), <N2 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_N4_Gcd_N2() {
    type A = NInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>>;
    type B = NInt<UInt<UInt<UTerm, B1>, B0>>;
    type P2 = PInt<UInt<UInt<UTerm, B1>, B0>>;

    #[allow(non_camel_case_types)]
    type N4GcdN2 = <<A as Gcd<B>>::Output as Same<P2>>::Output;

    assert_eq!(<N4GcdN2 as Integer>::to_i64(), <P2 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_N4_Div_N2() {
    type A = NInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>>;
    type B = NInt<UInt<UInt<UTerm, B1>, B0>>;
    type P2 = PInt<UInt<UInt<UTerm, B1>, B0>>;

    #[allow(non_camel_case_types)]
    type N4DivN2 = <<A as Div<B>>::Output as Same<P2>>::Output;

    assert_eq!(<N4DivN2 as Integer>::to_i64(), <P2 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_N4_Rem_N2() {
    type A = NInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>>;
    type B = NInt<UInt<UInt<UTerm, B1>, B0>>;
    type _0 = Z0;

    #[allow(non_camel_case_types)]
    type N4RemN2 = <<A as Rem<B>>::Output as Same<_0>>::Output;

    assert_eq!(<N4RemN2 as Integer>::to_i64(), <_0 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_N4_PartialDiv_N2() {
    type A = NInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>>;
    type B = NInt<UInt<UInt<UTerm, B1>, B0>>;
    type P2 = PInt<UInt<UInt<UTerm, B1>, B0>>;

    #[allow(non_camel_case_types)]
    type N4PartialDivN2 = <<A as PartialDiv<B>>::Output as Same<P2>>::Output;

    assert_eq!(<N4PartialDivN2 as Integer>::to_i64(), <P2 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_N4_Cmp_N2() {
    type A = NInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>>;
    type B = NInt<UInt<UInt<UTerm, B1>, B0>>;

    #[allow(non_camel_case_types)]
    type N4CmpN2 = <A as Cmp<B>>::Output;
    assert_eq!(<N4CmpN2 as Ord>::to_ordering(), Ordering::Less);
}
#[test]
#[allow(non_snake_case)]
fn test_N4_Add_N1() {
    type A = NInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>>;
    type B = NInt<UInt<UTerm, B1>>;
    type N5 = NInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>>;

    #[allow(non_camel_case_types)]
    type N4AddN1 = <<A as Add<B>>::Output as Same<N5>>::Output;

    assert_eq!(<N4AddN1 as Integer>::to_i64(), <N5 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_N4_Sub_N1() {
    type A = NInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>>;
    type B = NInt<UInt<UTerm, B1>>;
    type N3 = NInt<UInt<UInt<UTerm, B1>, B1>>;

    #[allow(non_camel_case_types)]
    type N4SubN1 = <<A as Sub<B>>::Output as Same<N3>>::Output;

    assert_eq!(<N4SubN1 as Integer>::to_i64(), <N3 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_N4_Mul_N1() {
    type A = NInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>>;
    type B = NInt<UInt<UTerm, B1>>;
    type P4 = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>>;

    #[allow(non_camel_case_types)]
    type N4MulN1 = <<A as Mul<B>>::Output as Same<P4>>::Output;

    assert_eq!(<N4MulN1 as Integer>::to_i64(), <P4 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_N4_Min_N1() {
    type A = NInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>>;
    type B = NInt<UInt<UTerm, B1>>;
    type N4 = NInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>>;

    #[allow(non_camel_case_types)]
    type N4MinN1 = <<A as Min<B>>::Output as Same<N4>>::Output;

    assert_eq!(<N4MinN1 as Integer>::to_i64(), <N4 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_N4_Max_N1() {
    type A = NInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>>;
    type B = NInt<UInt<UTerm, B1>>;
    type N1 = NInt<UInt<UTerm, B1>>;

    #[allow(non_camel_case_types)]
    type N4MaxN1 = <<A as Max<B>>::Output as Same<N1>>::Output;

    assert_eq!(<N4MaxN1 as Integer>::to_i64(), <N1 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_N4_Gcd_N1() {
    type A = NInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>>;
    type B = NInt<UInt<UTerm, B1>>;
    type P1 = PInt<UInt<UTerm, B1>>;

    #[allow(non_camel_case_types)]
    type N4GcdN1 = <<A as Gcd<B>>::Output as Same<P1>>::Output;

    assert_eq!(<N4GcdN1 as Integer>::to_i64(), <P1 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_N4_Div_N1() {
    type A = NInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>>;
    type B = NInt<UInt<UTerm, B1>>;
    type P4 = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>>;

    #[allow(non_camel_case_types)]
    type N4DivN1 = <<A as Div<B>>::Output as Same<P4>>::Output;

    assert_eq!(<N4DivN1 as Integer>::to_i64(), <P4 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_N4_Rem_N1() {
    type A = NInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>>;
    type B = NInt<UInt<UTerm, B1>>;
    type _0 = Z0;

    #[allow(non_camel_case_types)]
    type N4RemN1 = <<A as Rem<B>>::Output as Same<_0>>::Output;

    assert_eq!(<N4RemN1 as Integer>::to_i64(), <_0 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_N4_PartialDiv_N1() {
    type A = NInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>>;
    type B = NInt<UInt<UTerm, B1>>;
    type P4 = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>>;

    #[allow(non_camel_case_types)]
    type N4PartialDivN1 = <<A as PartialDiv<B>>::Output as Same<P4>>::Output;

    assert_eq!(<N4PartialDivN1 as Integer>::to_i64(), <P4 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_N4_Cmp_N1() {
    type A = NInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>>;
    type B = NInt<UInt<UTerm, B1>>;

    #[allow(non_camel_case_types)]
    type N4CmpN1 = <A as Cmp<B>>::Output;
    assert_eq!(<N4CmpN1 as Ord>::to_ordering(), Ordering::Less);
}
#[test]
#[allow(non_snake_case)]
fn test_N4_Add__0() {
    type A = NInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>>;
    type B = Z0;
    type N4 = NInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>>;

    #[allow(non_camel_case_types)]
    type N4Add_0 = <<A as Add<B>>::Output as Same<N4>>::Output;

    assert_eq!(<N4Add_0 as Integer>::to_i64(), <N4 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_N4_Sub__0() {
    type A = NInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>>;
    type B = Z0;
    type N4 = NInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>>;

    #[allow(non_camel_case_types)]
    type N4Sub_0 = <<A as Sub<B>>::Output as Same<N4>>::Output;

    assert_eq!(<N4Sub_0 as Integer>::to_i64(), <N4 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_N4_Mul__0() {
    type A = NInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>>;
    type B = Z0;
    type _0 = Z0;

    #[allow(non_camel_case_types)]
    type N4Mul_0 = <<A as Mul<B>>::Output as Same<_0>>::Output;

    assert_eq!(<N4Mul_0 as Integer>::to_i64(), <_0 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_N4_Min__0() {
    type A = NInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>>;
    type B = Z0;
    type N4 = NInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>>;

    #[allow(non_camel_case_types)]
    type N4Min_0 = <<A as Min<B>>::Output as Same<N4>>::Output;

    assert_eq!(<N4Min_0 as Integer>::to_i64(), <N4 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_N4_Max__0() {
    type A = NInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>>;
    type B = Z0;
    type _0 = Z0;

    #[allow(non_camel_case_types)]
    type N4Max_0 = <<A as Max<B>>::Output as Same<_0>>::Output;

    assert_eq!(<N4Max_0 as Integer>::to_i64(), <_0 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_N4_Gcd__0() {
    type A = NInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>>;
    type B = Z0;
    type P4 = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>>;

    #[allow(non_camel_case_types)]
    type N4Gcd_0 = <<A as Gcd<B>>::Output as Same<P4>>::Output;

    assert_eq!(<N4Gcd_0 as Integer>::to_i64(), <P4 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_N4_Pow__0() {
    type A = NInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>>;
    type B = Z0;
    type P1 = PInt<UInt<UTerm, B1>>;

    #[allow(non_camel_case_types)]
    type N4Pow_0 = <<A as Pow<B>>::Output as Same<P1>>::Output;

    assert_eq!(<N4Pow_0 as Integer>::to_i64(), <P1 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_N4_Cmp__0() {
    type A = NInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>>;
    type B = Z0;

    #[allow(non_camel_case_types)]
    type N4Cmp_0 = <A as Cmp<B>>::Output;
    assert_eq!(<N4Cmp_0 as Ord>::to_ordering(), Ordering::Less);
}
#[test]
#[allow(non_snake_case)]
fn test_N4_Add_P1() {
    type A = NInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>>;
    type B = PInt<UInt<UTerm, B1>>;
    type N3 = NInt<UInt<UInt<UTerm, B1>, B1>>;

    #[allow(non_camel_case_types)]
    type N4AddP1 = <<A as Add<B>>::Output as Same<N3>>::Output;

    assert_eq!(<N4AddP1 as Integer>::to_i64(), <N3 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_N4_Sub_P1() {
    type A = NInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>>;
    type B = PInt<UInt<UTerm, B1>>;
    type N5 = NInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>>;

    #[allow(non_camel_case_types)]
    type N4SubP1 = <<A as Sub<B>>::Output as Same<N5>>::Output;

    assert_eq!(<N4SubP1 as Integer>::to_i64(), <N5 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_N4_Mul_P1() {
    type A = NInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>>;
    type B = PInt<UInt<UTerm, B1>>;
    type N4 = NInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>>;

    #[allow(non_camel_case_types)]
    type N4MulP1 = <<A as Mul<B>>::Output as Same<N4>>::Output;

    assert_eq!(<N4MulP1 as Integer>::to_i64(), <N4 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_N4_Min_P1() {
    type A = NInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>>;
    type B = PInt<UInt<UTerm, B1>>;
    type N4 = NInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>>;

    #[allow(non_camel_case_types)]
    type N4MinP1 = <<A as Min<B>>::Output as Same<N4>>::Output;

    assert_eq!(<N4MinP1 as Integer>::to_i64(), <N4 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_N4_Max_P1() {
    type A = NInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>>;
    type B = PInt<UInt<UTerm, B1>>;
    type P1 = PInt<UInt<UTerm, B1>>;

    #[allow(non_camel_case_types)]
    type N4MaxP1 = <<A as Max<B>>::Output as Same<P1>>::Output;

    assert_eq!(<N4MaxP1 as Integer>::to_i64(), <P1 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_N4_Gcd_P1() {
    type A = NInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>>;
    type B = PInt<UInt<UTerm, B1>>;
    type P1 = PInt<UInt<UTerm, B1>>;

    #[allow(non_camel_case_types)]
    type N4GcdP1 = <<A as Gcd<B>>::Output as Same<P1>>::Output;

    assert_eq!(<N4GcdP1 as Integer>::to_i64(), <P1 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_N4_Div_P1() {
    type A = NInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>>;
    type B = PInt<UInt<UTerm, B1>>;
    type N4 = NInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>>;

    #[allow(non_camel_case_types)]
    type N4DivP1 = <<A as Div<B>>::Output as Same<N4>>::Output;

    assert_eq!(<N4DivP1 as Integer>::to_i64(), <N4 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_N4_Rem_P1() {
    type A = NInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>>;
    type B = PInt<UInt<UTerm, B1>>;
    type _0 = Z0;

    #[allow(non_camel_case_types)]
    type N4RemP1 = <<A as Rem<B>>::Output as Same<_0>>::Output;

    assert_eq!(<N4RemP1 as Integer>::to_i64(), <_0 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_N4_PartialDiv_P1() {
    type A = NInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>>;
    type B = PInt<UInt<UTerm, B1>>;
    type N4 = NInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>>;

    #[allow(non_camel_case_types)]
    type N4PartialDivP1 = <<A as PartialDiv<B>>::Output as Same<N4>>::Output;

    assert_eq!(<N4PartialDivP1 as Integer>::to_i64(), <N4 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_N4_Pow_P1() {
    type A = NInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>>;
    type B = PInt<UInt<UTerm, B1>>;
    type N4 = NInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>>;

    #[allow(non_camel_case_types)]
    type N4PowP1 = <<A as Pow<B>>::Output as Same<N4>>::Output;

    assert_eq!(<N4PowP1 as Integer>::to_i64(), <N4 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_N4_Cmp_P1() {
    type A = NInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>>;
    type B = PInt<UInt<UTerm, B1>>;

    #[allow(non_camel_case_types)]
    type N4CmpP1 = <A as Cmp<B>>::Output;
    assert_eq!(<N4CmpP1 as Ord>::to_ordering(), Ordering::Less);
}
#[test]
#[allow(non_snake_case)]
fn test_N4_Add_P2() {
    type A = NInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>>;
    type B = PInt<UInt<UInt<UTerm, B1>, B0>>;
    type N2 = NInt<UInt<UInt<UTerm, B1>, B0>>;

    #[allow(non_camel_case_types)]
    type N4AddP2 = <<A as Add<B>>::Output as Same<N2>>::Output;

    assert_eq!(<N4AddP2 as Integer>::to_i64(), <N2 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_N4_Sub_P2() {
    type A = NInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>>;
    type B = PInt<UInt<UInt<UTerm, B1>, B0>>;
    type N6 = NInt<UInt<UInt<UInt<UTerm, B1>, B1>, B0>>;

    #[allow(non_camel_case_types)]
    type N4SubP2 = <<A as Sub<B>>::Output as Same<N6>>::Output;

    assert_eq!(<N4SubP2 as Integer>::to_i64(), <N6 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_N4_Mul_P2() {
    type A = NInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>>;
    type B = PInt<UInt<UInt<UTerm, B1>, B0>>;
    type N8 = NInt<UInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>, B0>>;

    #[allow(non_camel_case_types)]
    type N4MulP2 = <<A as Mul<B>>::Output as Same<N8>>::Output;

    assert_eq!(<N4MulP2 as Integer>::to_i64(), <N8 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_N4_Min_P2() {
    type A = NInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>>;
    type B = PInt<UInt<UInt<UTerm, B1>, B0>>;
    type N4 = NInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>>;

    #[allow(non_camel_case_types)]
    type N4MinP2 = <<A as Min<B>>::Output as Same<N4>>::Output;

    assert_eq!(<N4MinP2 as Integer>::to_i64(), <N4 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_N4_Max_P2() {
    type A = NInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>>;
    type B = PInt<UInt<UInt<UTerm, B1>, B0>>;
    type P2 = PInt<UInt<UInt<UTerm, B1>, B0>>;

    #[allow(non_camel_case_types)]
    type N4MaxP2 = <<A as Max<B>>::Output as Same<P2>>::Output;

    assert_eq!(<N4MaxP2 as Integer>::to_i64(), <P2 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_N4_Gcd_P2() {
    type A = NInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>>;
    type B = PInt<UInt<UInt<UTerm, B1>, B0>>;
    type P2 = PInt<UInt<UInt<UTerm, B1>, B0>>;

    #[allow(non_camel_case_types)]
    type N4GcdP2 = <<A as Gcd<B>>::Output as Same<P2>>::Output;

    assert_eq!(<N4GcdP2 as Integer>::to_i64(), <P2 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_N4_Div_P2() {
    type A = NInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>>;
    type B = PInt<UInt<UInt<UTerm, B1>, B0>>;
    type N2 = NInt<UInt<UInt<UTerm, B1>, B0>>;

    #[allow(non_camel_case_types)]
    type N4DivP2 = <<A as Div<B>>::Output as Same<N2>>::Output;

    assert_eq!(<N4DivP2 as Integer>::to_i64(), <N2 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_N4_Rem_P2() {
    type A = NInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>>;
    type B = PInt<UInt<UInt<UTerm, B1>, B0>>;
    type _0 = Z0;

    #[allow(non_camel_case_types)]
    type N4RemP2 = <<A as Rem<B>>::Output as Same<_0>>::Output;

    assert_eq!(<N4RemP2 as Integer>::to_i64(), <_0 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_N4_PartialDiv_P2() {
    type A = NInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>>;
    type B = PInt<UInt<UInt<UTerm, B1>, B0>>;
    type N2 = NInt<UInt<UInt<UTerm, B1>, B0>>;

    #[allow(non_camel_case_types)]
    type N4PartialDivP2 = <<A as PartialDiv<B>>::Output as Same<N2>>::Output;

    assert_eq!(<N4PartialDivP2 as Integer>::to_i64(), <N2 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_N4_Pow_P2() {
    type A = NInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>>;
    type B = PInt<UInt<UInt<UTerm, B1>, B0>>;
    type P16 = PInt<UInt<UInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>, B0>, B0>>;

    #[allow(non_camel_case_types)]
    type N4PowP2 = <<A as Pow<B>>::Output as Same<P16>>::Output;

    assert_eq!(<N4PowP2 as Integer>::to_i64(), <P16 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_N4_Cmp_P2() {
    type A = NInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>>;
    type B = PInt<UInt<UInt<UTerm, B1>, B0>>;

    #[allow(non_camel_case_types)]
    type N4CmpP2 = <A as Cmp<B>>::Output;
    assert_eq!(<N4CmpP2 as Ord>::to_ordering(), Ordering::Less);
}
#[test]
#[allow(non_snake_case)]
fn test_N4_Add_P3() {
    type A = NInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>>;
    type B = PInt<UInt<UInt<UTerm, B1>, B1>>;
    type N1 = NInt<UInt<UTerm, B1>>;

    #[allow(non_camel_case_types)]
    type N4AddP3 = <<A as Add<B>>::Output as Same<N1>>::Output;

    assert_eq!(<N4AddP3 as Integer>::to_i64(), <N1 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_N4_Sub_P3() {
    type A = NInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>>;
    type B = PInt<UInt<UInt<UTerm, B1>, B1>>;
    type N7 = NInt<UInt<UInt<UInt<UTerm, B1>, B1>, B1>>;

    #[allow(non_camel_case_types)]
    type N4SubP3 = <<A as Sub<B>>::Output as Same<N7>>::Output;

    assert_eq!(<N4SubP3 as Integer>::to_i64(), <N7 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_N4_Mul_P3() {
    type A = NInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>>;
    type B = PInt<UInt<UInt<UTerm, B1>, B1>>;
    type N12 = NInt<UInt<UInt<UInt<UInt<UTerm, B1>, B1>, B0>, B0>>;

    #[allow(non_camel_case_types)]
    type N4MulP3 = <<A as Mul<B>>::Output as Same<N12>>::Output;

    assert_eq!(<N4MulP3 as Integer>::to_i64(), <N12 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_N4_Min_P3() {
    type A = NInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>>;
    type B = PInt<UInt<UInt<UTerm, B1>, B1>>;
    type N4 = NInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>>;

    #[allow(non_camel_case_types)]
    type N4MinP3 = <<A as Min<B>>::Output as Same<N4>>::Output;

    assert_eq!(<N4MinP3 as Integer>::to_i64(), <N4 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_N4_Max_P3() {
    type A = NInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>>;
    type B = PInt<UInt<UInt<UTerm, B1>, B1>>;
    type P3 = PInt<UInt<UInt<UTerm, B1>, B1>>;

    #[allow(non_camel_case_types)]
    type N4MaxP3 = <<A as Max<B>>::Output as Same<P3>>::Output;

    assert_eq!(<N4MaxP3 as Integer>::to_i64(), <P3 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_N4_Gcd_P3() {
    type A = NInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>>;
    type B = PInt<UInt<UInt<UTerm, B1>, B1>>;
    type P1 = PInt<UInt<UTerm, B1>>;

    #[allow(non_camel_case_types)]
    type N4GcdP3 = <<A as Gcd<B>>::Output as Same<P1>>::Output;

    assert_eq!(<N4GcdP3 as Integer>::to_i64(), <P1 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_N4_Div_P3() {
    type A = NInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>>;
    type B = PInt<UInt<UInt<UTerm, B1>, B1>>;
    type N1 = NInt<UInt<UTerm, B1>>;

    #[allow(non_camel_case_types)]
    type N4DivP3 = <<A as Div<B>>::Output as Same<N1>>::Output;

    assert_eq!(<N4DivP3 as Integer>::to_i64(), <N1 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_N4_Rem_P3() {
    type A = NInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>>;
    type B = PInt<UInt<UInt<UTerm, B1>, B1>>;
    type N1 = NInt<UInt<UTerm, B1>>;

    #[allow(non_camel_case_types)]
    type N4RemP3 = <<A as Rem<B>>::Output as Same<N1>>::Output;

    assert_eq!(<N4RemP3 as Integer>::to_i64(), <N1 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_N4_Pow_P3() {
    type A = NInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>>;
    type B = PInt<UInt<UInt<UTerm, B1>, B1>>;
    type N64 = NInt<UInt<UInt<UInt<UInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>, B0>, B0>, B0>, B0>>;

    #[allow(non_camel_case_types)]
    type N4PowP3 = <<A as Pow<B>>::Output as Same<N64>>::Output;

    assert_eq!(<N4PowP3 as Integer>::to_i64(), <N64 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_N4_Cmp_P3() {
    type A = NInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>>;
    type B = PInt<UInt<UInt<UTerm, B1>, B1>>;

    #[allow(non_camel_case_types)]
    type N4CmpP3 = <A as Cmp<B>>::Output;
    assert_eq!(<N4CmpP3 as Ord>::to_ordering(), Ordering::Less);
}
#[test]
#[allow(non_snake_case)]
fn test_N4_Add_P4() {
    type A = NInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>>;
    type B = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>>;
    type _0 = Z0;

    #[allow(non_camel_case_types)]
    type N4AddP4 = <<A as Add<B>>::Output as Same<_0>>::Output;

    assert_eq!(<N4AddP4 as Integer>::to_i64(), <_0 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_N4_Sub_P4() {
    type A = NInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>>;
    type B = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>>;
    type N8 = NInt<UInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>, B0>>;

    #[allow(non_camel_case_types)]
    type N4SubP4 = <<A as Sub<B>>::Output as Same<N8>>::Output;

    assert_eq!(<N4SubP4 as Integer>::to_i64(), <N8 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_N4_Mul_P4() {
    type A = NInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>>;
    type B = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>>;
    type N16 = NInt<UInt<UInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>, B0>, B0>>;

    #[allow(non_camel_case_types)]
    type N4MulP4 = <<A as Mul<B>>::Output as Same<N16>>::Output;

    assert_eq!(<N4MulP4 as Integer>::to_i64(), <N16 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_N4_Min_P4() {
    type A = NInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>>;
    type B = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>>;
    type N4 = NInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>>;

    #[allow(non_camel_case_types)]
    type N4MinP4 = <<A as Min<B>>::Output as Same<N4>>::Output;

    assert_eq!(<N4MinP4 as Integer>::to_i64(), <N4 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_N4_Max_P4() {
    type A = NInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>>;
    type B = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>>;
    type P4 = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>>;

    #[allow(non_camel_case_types)]
    type N4MaxP4 = <<A as Max<B>>::Output as Same<P4>>::Output;

    assert_eq!(<N4MaxP4 as Integer>::to_i64(), <P4 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_N4_Gcd_P4() {
    type A = NInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>>;
    type B = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>>;
    type P4 = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>>;

    #[allow(non_camel_case_types)]
    type N4GcdP4 = <<A as Gcd<B>>::Output as Same<P4>>::Output;

    assert_eq!(<N4GcdP4 as Integer>::to_i64(), <P4 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_N4_Div_P4() {
    type A = NInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>>;
    type B = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>>;
    type N1 = NInt<UInt<UTerm, B1>>;

    #[allow(non_camel_case_types)]
    type N4DivP4 = <<A as Div<B>>::Output as Same<N1>>::Output;

    assert_eq!(<N4DivP4 as Integer>::to_i64(), <N1 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_N4_Rem_P4() {
    type A = NInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>>;
    type B = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>>;
    type _0 = Z0;

    #[allow(non_camel_case_types)]
    type N4RemP4 = <<A as Rem<B>>::Output as Same<_0>>::Output;

    assert_eq!(<N4RemP4 as Integer>::to_i64(), <_0 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_N4_PartialDiv_P4() {
    type A = NInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>>;
    type B = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>>;
    type N1 = NInt<UInt<UTerm, B1>>;

    #[allow(non_camel_case_types)]
    type N4PartialDivP4 = <<A as PartialDiv<B>>::Output as Same<N1>>::Output;

    assert_eq!(<N4PartialDivP4 as Integer>::to_i64(), <N1 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_N4_Pow_P4() {
    type A = NInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>>;
    type B = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>>;
    type P256 = PInt<UInt<UInt<UInt<UInt<UInt<UInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>, B0>, B0>, B0>, B0>, B0>, B0>>;

    #[allow(non_camel_case_types)]
    type N4PowP4 = <<A as Pow<B>>::Output as Same<P256>>::Output;

    assert_eq!(<N4PowP4 as Integer>::to_i64(), <P256 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_N4_Cmp_P4() {
    type A = NInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>>;
    type B = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>>;

    #[allow(non_camel_case_types)]
    type N4CmpP4 = <A as Cmp<B>>::Output;
    assert_eq!(<N4CmpP4 as Ord>::to_ordering(), Ordering::Less);
}
#[test]
#[allow(non_snake_case)]
fn test_N4_Add_P5() {
    type A = NInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>>;
    type B = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>>;
    type P1 = PInt<UInt<UTerm, B1>>;

    #[allow(non_camel_case_types)]
    type N4AddP5 = <<A as Add<B>>::Output as Same<P1>>::Output;

    assert_eq!(<N4AddP5 as Integer>::to_i64(), <P1 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_N4_Sub_P5() {
    type A = NInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>>;
    type B = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>>;
    type N9 = NInt<UInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>, B1>>;

    #[allow(non_camel_case_types)]
    type N4SubP5 = <<A as Sub<B>>::Output as Same<N9>>::Output;

    assert_eq!(<N4SubP5 as Integer>::to_i64(), <N9 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_N4_Mul_P5() {
    type A = NInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>>;
    type B = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>>;
    type N20 = NInt<UInt<UInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>, B0>, B0>>;

    #[allow(non_camel_case_types)]
    type N4MulP5 = <<A as Mul<B>>::Output as Same<N20>>::Output;

    assert_eq!(<N4MulP5 as Integer>::to_i64(), <N20 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_N4_Min_P5() {
    type A = NInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>>;
    type B = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>>;
    type N4 = NInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>>;

    #[allow(non_camel_case_types)]
    type N4MinP5 = <<A as Min<B>>::Output as Same<N4>>::Output;

    assert_eq!(<N4MinP5 as Integer>::to_i64(), <N4 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_N4_Max_P5() {
    type A = NInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>>;
    type B = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>>;
    type P5 = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>>;

    #[allow(non_camel_case_types)]
    type N4MaxP5 = <<A as Max<B>>::Output as Same<P5>>::Output;

    assert_eq!(<N4MaxP5 as Integer>::to_i64(), <P5 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_N4_Gcd_P5() {
    type A = NInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>>;
    type B = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>>;
    type P1 = PInt<UInt<UTerm, B1>>;

    #[allow(non_camel_case_types)]
    type N4GcdP5 = <<A as Gcd<B>>::Output as Same<P1>>::Output;

    assert_eq!(<N4GcdP5 as Integer>::to_i64(), <P1 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_N4_Div_P5() {
    type A = NInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>>;
    type B = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>>;
    type _0 = Z0;

    #[allow(non_camel_case_types)]
    type N4DivP5 = <<A as Div<B>>::Output as Same<_0>>::Output;

    assert_eq!(<N4DivP5 as Integer>::to_i64(), <_0 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_N4_Rem_P5() {
    type A = NInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>>;
    type B = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>>;
    type N4 = NInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>>;

    #[allow(non_camel_case_types)]
    type N4RemP5 = <<A as Rem<B>>::Output as Same<N4>>::Output;

    assert_eq!(<N4RemP5 as Integer>::to_i64(), <N4 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_N4_Pow_P5() {
    type A = NInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>>;
    type B = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>>;
    type N1024 = NInt<UInt<UInt<UInt<UInt<UInt<UInt<UInt<UInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>, B0>, B0>, B0>, B0>, B0>, B0>, B0>, B0>>;

    #[allow(non_camel_case_types)]
    type N4PowP5 = <<A as Pow<B>>::Output as Same<N1024>>::Output;

    assert_eq!(<N4PowP5 as Integer>::to_i64(), <N1024 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_N4_Cmp_P5() {
    type A = NInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>>;
    type B = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>>;

    #[allow(non_camel_case_types)]
    type N4CmpP5 = <A as Cmp<B>>::Output;
    assert_eq!(<N4CmpP5 as Ord>::to_ordering(), Ordering::Less);
}
#[test]
#[allow(non_snake_case)]
fn test_N3_Add_N5() {
    type A = NInt<UInt<UInt<UTerm, B1>, B1>>;
    type B = NInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>>;
    type N8 = NInt<UInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>, B0>>;

    #[allow(non_camel_case_types)]
    type N3AddN5 = <<A as Add<B>>::Output as Same<N8>>::Output;

    assert_eq!(<N3AddN5 as Integer>::to_i64(), <N8 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_N3_Sub_N5() {
    type A = NInt<UInt<UInt<UTerm, B1>, B1>>;
    type B = NInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>>;
    type P2 = PInt<UInt<UInt<UTerm, B1>, B0>>;

    #[allow(non_camel_case_types)]
    type N3SubN5 = <<A as Sub<B>>::Output as Same<P2>>::Output;

    assert_eq!(<N3SubN5 as Integer>::to_i64(), <P2 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_N3_Mul_N5() {
    type A = NInt<UInt<UInt<UTerm, B1>, B1>>;
    type B = NInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>>;
    type P15 = PInt<UInt<UInt<UInt<UInt<UTerm, B1>, B1>, B1>, B1>>;

    #[allow(non_camel_case_types)]
    type N3MulN5 = <<A as Mul<B>>::Output as Same<P15>>::Output;

    assert_eq!(<N3MulN5 as Integer>::to_i64(), <P15 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_N3_Min_N5() {
    type A = NInt<UInt<UInt<UTerm, B1>, B1>>;
    type B = NInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>>;
    type N5 = NInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>>;

    #[allow(non_camel_case_types)]
    type N3MinN5 = <<A as Min<B>>::Output as Same<N5>>::Output;

    assert_eq!(<N3MinN5 as Integer>::to_i64(), <N5 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_N3_Max_N5() {
    type A = NInt<UInt<UInt<UTerm, B1>, B1>>;
    type B = NInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>>;
    type N3 = NInt<UInt<UInt<UTerm, B1>, B1>>;

    #[allow(non_camel_case_types)]
    type N3MaxN5 = <<A as Max<B>>::Output as Same<N3>>::Output;

    assert_eq!(<N3MaxN5 as Integer>::to_i64(), <N3 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_N3_Gcd_N5() {
    type A = NInt<UInt<UInt<UTerm, B1>, B1>>;
    type B = NInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>>;
    type P1 = PInt<UInt<UTerm, B1>>;

    #[allow(non_camel_case_types)]
    type N3GcdN5 = <<A as Gcd<B>>::Output as Same<P1>>::Output;

    assert_eq!(<N3GcdN5 as Integer>::to_i64(), <P1 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_N3_Div_N5() {
    type A = NInt<UInt<UInt<UTerm, B1>, B1>>;
    type B = NInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>>;
    type _0 = Z0;

    #[allow(non_camel_case_types)]
    type N3DivN5 = <<A as Div<B>>::Output as Same<_0>>::Output;

    assert_eq!(<N3DivN5 as Integer>::to_i64(), <_0 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_N3_Rem_N5() {
    type A = NInt<UInt<UInt<UTerm, B1>, B1>>;
    type B = NInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>>;
    type N3 = NInt<UInt<UInt<UTerm, B1>, B1>>;

    #[allow(non_camel_case_types)]
    type N3RemN5 = <<A as Rem<B>>::Output as Same<N3>>::Output;

    assert_eq!(<N3RemN5 as Integer>::to_i64(), <N3 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_N3_Cmp_N5() {
    type A = NInt<UInt<UInt<UTerm, B1>, B1>>;
    type B = NInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>>;

    #[allow(non_camel_case_types)]
    type N3CmpN5 = <A as Cmp<B>>::Output;
    assert_eq!(<N3CmpN5 as Ord>::to_ordering(), Ordering::Greater);
}
#[test]
#[allow(non_snake_case)]
fn test_N3_Add_N4() {
    type A = NInt<UInt<UInt<UTerm, B1>, B1>>;
    type B = NInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>>;
    type N7 = NInt<UInt<UInt<UInt<UTerm, B1>, B1>, B1>>;

    #[allow(non_camel_case_types)]
    type N3AddN4 = <<A as Add<B>>::Output as Same<N7>>::Output;

    assert_eq!(<N3AddN4 as Integer>::to_i64(), <N7 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_N3_Sub_N4() {
    type A = NInt<UInt<UInt<UTerm, B1>, B1>>;
    type B = NInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>>;
    type P1 = PInt<UInt<UTerm, B1>>;

    #[allow(non_camel_case_types)]
    type N3SubN4 = <<A as Sub<B>>::Output as Same<P1>>::Output;

    assert_eq!(<N3SubN4 as Integer>::to_i64(), <P1 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_N3_Mul_N4() {
    type A = NInt<UInt<UInt<UTerm, B1>, B1>>;
    type B = NInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>>;
    type P12 = PInt<UInt<UInt<UInt<UInt<UTerm, B1>, B1>, B0>, B0>>;

    #[allow(non_camel_case_types)]
    type N3MulN4 = <<A as Mul<B>>::Output as Same<P12>>::Output;

    assert_eq!(<N3MulN4 as Integer>::to_i64(), <P12 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_N3_Min_N4() {
    type A = NInt<UInt<UInt<UTerm, B1>, B1>>;
    type B = NInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>>;
    type N4 = NInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>>;

    #[allow(non_camel_case_types)]
    type N3MinN4 = <<A as Min<B>>::Output as Same<N4>>::Output;

    assert_eq!(<N3MinN4 as Integer>::to_i64(), <N4 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_N3_Max_N4() {
    type A = NInt<UInt<UInt<UTerm, B1>, B1>>;
    type B = NInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>>;
    type N3 = NInt<UInt<UInt<UTerm, B1>, B1>>;

    #[allow(non_camel_case_types)]
    type N3MaxN4 = <<A as Max<B>>::Output as Same<N3>>::Output;

    assert_eq!(<N3MaxN4 as Integer>::to_i64(), <N3 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_N3_Gcd_N4() {
    type A = NInt<UInt<UInt<UTerm, B1>, B1>>;
    type B = NInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>>;
    type P1 = PInt<UInt<UTerm, B1>>;

    #[allow(non_camel_case_types)]
    type N3GcdN4 = <<A as Gcd<B>>::Output as Same<P1>>::Output;

    assert_eq!(<N3GcdN4 as Integer>::to_i64(), <P1 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_N3_Div_N4() {
    type A = NInt<UInt<UInt<UTerm, B1>, B1>>;
    type B = NInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>>;
    type _0 = Z0;

    #[allow(non_camel_case_types)]
    type N3DivN4 = <<A as Div<B>>::Output as Same<_0>>::Output;

    assert_eq!(<N3DivN4 as Integer>::to_i64(), <_0 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_N3_Rem_N4() {
    type A = NInt<UInt<UInt<UTerm, B1>, B1>>;
    type B = NInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>>;
    type N3 = NInt<UInt<UInt<UTerm, B1>, B1>>;

    #[allow(non_camel_case_types)]
    type N3RemN4 = <<A as Rem<B>>::Output as Same<N3>>::Output;

    assert_eq!(<N3RemN4 as Integer>::to_i64(), <N3 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_N3_Cmp_N4() {
    type A = NInt<UInt<UInt<UTerm, B1>, B1>>;
    type B = NInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>>;

    #[allow(non_camel_case_types)]
    type N3CmpN4 = <A as Cmp<B>>::Output;
    assert_eq!(<N3CmpN4 as Ord>::to_ordering(), Ordering::Greater);
}
#[test]
#[allow(non_snake_case)]
fn test_N3_Add_N3() {
    type A = NInt<UInt<UInt<UTerm, B1>, B1>>;
    type B = NInt<UInt<UInt<UTerm, B1>, B1>>;
    type N6 = NInt<UInt<UInt<UInt<UTerm, B1>, B1>, B0>>;

    #[allow(non_camel_case_types)]
    type N3AddN3 = <<A as Add<B>>::Output as Same<N6>>::Output;

    assert_eq!(<N3AddN3 as Integer>::to_i64(), <N6 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_N3_Sub_N3() {
    type A = NInt<UInt<UInt<UTerm, B1>, B1>>;
    type B = NInt<UInt<UInt<UTerm, B1>, B1>>;
    type _0 = Z0;

    #[allow(non_camel_case_types)]
    type N3SubN3 = <<A as Sub<B>>::Output as Same<_0>>::Output;

    assert_eq!(<N3SubN3 as Integer>::to_i64(), <_0 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_N3_Mul_N3() {
    type A = NInt<UInt<UInt<UTerm, B1>, B1>>;
    type B = NInt<UInt<UInt<UTerm, B1>, B1>>;
    type P9 = PInt<UInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>, B1>>;

    #[allow(non_camel_case_types)]
    type N3MulN3 = <<A as Mul<B>>::Output as Same<P9>>::Output;

    assert_eq!(<N3MulN3 as Integer>::to_i64(), <P9 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_N3_Min_N3() {
    type A = NInt<UInt<UInt<UTerm, B1>, B1>>;
    type B = NInt<UInt<UInt<UTerm, B1>, B1>>;
    type N3 = NInt<UInt<UInt<UTerm, B1>, B1>>;

    #[allow(non_camel_case_types)]
    type N3MinN3 = <<A as Min<B>>::Output as Same<N3>>::Output;

    assert_eq!(<N3MinN3 as Integer>::to_i64(), <N3 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_N3_Max_N3() {
    type A = NInt<UInt<UInt<UTerm, B1>, B1>>;
    type B = NInt<UInt<UInt<UTerm, B1>, B1>>;
    type N3 = NInt<UInt<UInt<UTerm, B1>, B1>>;

    #[allow(non_camel_case_types)]
    type N3MaxN3 = <<A as Max<B>>::Output as Same<N3>>::Output;

    assert_eq!(<N3MaxN3 as Integer>::to_i64(), <N3 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_N3_Gcd_N3() {
    type A = NInt<UInt<UInt<UTerm, B1>, B1>>;
    type B = NInt<UInt<UInt<UTerm, B1>, B1>>;
    type P3 = PInt<UInt<UInt<UTerm, B1>, B1>>;

    #[allow(non_camel_case_types)]
    type N3GcdN3 = <<A as Gcd<B>>::Output as Same<P3>>::Output;

    assert_eq!(<N3GcdN3 as Integer>::to_i64(), <P3 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_N3_Div_N3() {
    type A = NInt<UInt<UInt<UTerm, B1>, B1>>;
    type B = NInt<UInt<UInt<UTerm, B1>, B1>>;
    type P1 = PInt<UInt<UTerm, B1>>;

    #[allow(non_camel_case_types)]
    type N3DivN3 = <<A as Div<B>>::Output as Same<P1>>::Output;

    assert_eq!(<N3DivN3 as Integer>::to_i64(), <P1 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_N3_Rem_N3() {
    type A = NInt<UInt<UInt<UTerm, B1>, B1>>;
    type B = NInt<UInt<UInt<UTerm, B1>, B1>>;
    type _0 = Z0;

    #[allow(non_camel_case_types)]
    type N3RemN3 = <<A as Rem<B>>::Output as Same<_0>>::Output;

    assert_eq!(<N3RemN3 as Integer>::to_i64(), <_0 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_N3_PartialDiv_N3() {
    type A = NInt<UInt<UInt<UTerm, B1>, B1>>;
    type B = NInt<UInt<UInt<UTerm, B1>, B1>>;
    type P1 = PInt<UInt<UTerm, B1>>;

    #[allow(non_camel_case_types)]
    type N3PartialDivN3 = <<A as PartialDiv<B>>::Output as Same<P1>>::Output;

    assert_eq!(<N3PartialDivN3 as Integer>::to_i64(), <P1 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_N3_Cmp_N3() {
    type A = NInt<UInt<UInt<UTerm, B1>, B1>>;
    type B = NInt<UInt<UInt<UTerm, B1>, B1>>;

    #[allow(non_camel_case_types)]
    type N3CmpN3 = <A as Cmp<B>>::Output;
    assert_eq!(<N3CmpN3 as Ord>::to_ordering(), Ordering::Equal);
}
#[test]
#[allow(non_snake_case)]
fn test_N3_Add_N2() {
    type A = NInt<UInt<UInt<UTerm, B1>, B1>>;
    type B = NInt<UInt<UInt<UTerm, B1>, B0>>;
    type N5 = NInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>>;

    #[allow(non_camel_case_types)]
    type N3AddN2 = <<A as Add<B>>::Output as Same<N5>>::Output;

    assert_eq!(<N3AddN2 as Integer>::to_i64(), <N5 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_N3_Sub_N2() {
    type A = NInt<UInt<UInt<UTerm, B1>, B1>>;
    type B = NInt<UInt<UInt<UTerm, B1>, B0>>;
    type N1 = NInt<UInt<UTerm, B1>>;

    #[allow(non_camel_case_types)]
    type N3SubN2 = <<A as Sub<B>>::Output as Same<N1>>::Output;

    assert_eq!(<N3SubN2 as Integer>::to_i64(), <N1 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_N3_Mul_N2() {
    type A = NInt<UInt<UInt<UTerm, B1>, B1>>;
    type B = NInt<UInt<UInt<UTerm, B1>, B0>>;
    type P6 = PInt<UInt<UInt<UInt<UTerm, B1>, B1>, B0>>;

    #[allow(non_camel_case_types)]
    type N3MulN2 = <<A as Mul<B>>::Output as Same<P6>>::Output;

    assert_eq!(<N3MulN2 as Integer>::to_i64(), <P6 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_N3_Min_N2() {
    type A = NInt<UInt<UInt<UTerm, B1>, B1>>;
    type B = NInt<UInt<UInt<UTerm, B1>, B0>>;
    type N3 = NInt<UInt<UInt<UTerm, B1>, B1>>;

    #[allow(non_camel_case_types)]
    type N3MinN2 = <<A as Min<B>>::Output as Same<N3>>::Output;

    assert_eq!(<N3MinN2 as Integer>::to_i64(), <N3 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_N3_Max_N2() {
    type A = NInt<UInt<UInt<UTerm, B1>, B1>>;
    type B = NInt<UInt<UInt<UTerm, B1>, B0>>;
    type N2 = NInt<UInt<UInt<UTerm, B1>, B0>>;

    #[allow(non_camel_case_types)]
    type N3MaxN2 = <<A as Max<B>>::Output as Same<N2>>::Output;

    assert_eq!(<N3MaxN2 as Integer>::to_i64(), <N2 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_N3_Gcd_N2() {
    type A = NInt<UInt<UInt<UTerm, B1>, B1>>;
    type B = NInt<UInt<UInt<UTerm, B1>, B0>>;
    type P1 = PInt<UInt<UTerm, B1>>;

    #[allow(non_camel_case_types)]
    type N3GcdN2 = <<A as Gcd<B>>::Output as Same<P1>>::Output;

    assert_eq!(<N3GcdN2 as Integer>::to_i64(), <P1 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_N3_Div_N2() {
    type A = NInt<UInt<UInt<UTerm, B1>, B1>>;
    type B = NInt<UInt<UInt<UTerm, B1>, B0>>;
    type P1 = PInt<UInt<UTerm, B1>>;

    #[allow(non_camel_case_types)]
    type N3DivN2 = <<A as Div<B>>::Output as Same<P1>>::Output;

    assert_eq!(<N3DivN2 as Integer>::to_i64(), <P1 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_N3_Rem_N2() {
    type A = NInt<UInt<UInt<UTerm, B1>, B1>>;
    type B = NInt<UInt<UInt<UTerm, B1>, B0>>;
    type N1 = NInt<UInt<UTerm, B1>>;

    #[allow(non_camel_case_types)]
    type N3RemN2 = <<A as Rem<B>>::Output as Same<N1>>::Output;

    assert_eq!(<N3RemN2 as Integer>::to_i64(), <N1 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_N3_Cmp_N2() {
    type A = NInt<UInt<UInt<UTerm, B1>, B1>>;
    type B = NInt<UInt<UInt<UTerm, B1>, B0>>;

    #[allow(non_camel_case_types)]
    type N3CmpN2 = <A as Cmp<B>>::Output;
    assert_eq!(<N3CmpN2 as Ord>::to_ordering(), Ordering::Less);
}
#[test]
#[allow(non_snake_case)]
fn test_N3_Add_N1() {
    type A = NInt<UInt<UInt<UTerm, B1>, B1>>;
    type B = NInt<UInt<UTerm, B1>>;
    type N4 = NInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>>;

    #[allow(non_camel_case_types)]
    type N3AddN1 = <<A as Add<B>>::Output as Same<N4>>::Output;

    assert_eq!(<N3AddN1 as Integer>::to_i64(), <N4 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_N3_Sub_N1() {
    type A = NInt<UInt<UInt<UTerm, B1>, B1>>;
    type B = NInt<UInt<UTerm, B1>>;
    type N2 = NInt<UInt<UInt<UTerm, B1>, B0>>;

    #[allow(non_camel_case_types)]
    type N3SubN1 = <<A as Sub<B>>::Output as Same<N2>>::Output;

    assert_eq!(<N3SubN1 as Integer>::to_i64(), <N2 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_N3_Mul_N1() {
    type A = NInt<UInt<UInt<UTerm, B1>, B1>>;
    type B = NInt<UInt<UTerm, B1>>;
    type P3 = PInt<UInt<UInt<UTerm, B1>, B1>>;

    #[allow(non_camel_case_types)]
    type N3MulN1 = <<A as Mul<B>>::Output as Same<P3>>::Output;

    assert_eq!(<N3MulN1 as Integer>::to_i64(), <P3 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_N3_Min_N1() {
    type A = NInt<UInt<UInt<UTerm, B1>, B1>>;
    type B = NInt<UInt<UTerm, B1>>;
    type N3 = NInt<UInt<UInt<UTerm, B1>, B1>>;

    #[allow(non_camel_case_types)]
    type N3MinN1 = <<A as Min<B>>::Output as Same<N3>>::Output;

    assert_eq!(<N3MinN1 as Integer>::to_i64(), <N3 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_N3_Max_N1() {
    type A = NInt<UInt<UInt<UTerm, B1>, B1>>;
    type B = NInt<UInt<UTerm, B1>>;
    type N1 = NInt<UInt<UTerm, B1>>;

    #[allow(non_camel_case_types)]
    type N3MaxN1 = <<A as Max<B>>::Output as Same<N1>>::Output;

    assert_eq!(<N3MaxN1 as Integer>::to_i64(), <N1 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_N3_Gcd_N1() {
    type A = NInt<UInt<UInt<UTerm, B1>, B1>>;
    type B = NInt<UInt<UTerm, B1>>;
    type P1 = PInt<UInt<UTerm, B1>>;

    #[allow(non_camel_case_types)]
    type N3GcdN1 = <<A as Gcd<B>>::Output as Same<P1>>::Output;

    assert_eq!(<N3GcdN1 as Integer>::to_i64(), <P1 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_N3_Div_N1() {
    type A = NInt<UInt<UInt<UTerm, B1>, B1>>;
    type B = NInt<UInt<UTerm, B1>>;
    type P3 = PInt<UInt<UInt<UTerm, B1>, B1>>;

    #[allow(non_camel_case_types)]
    type N3DivN1 = <<A as Div<B>>::Output as Same<P3>>::Output;

    assert_eq!(<N3DivN1 as Integer>::to_i64(), <P3 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_N3_Rem_N1() {
    type A = NInt<UInt<UInt<UTerm, B1>, B1>>;
    type B = NInt<UInt<UTerm, B1>>;
    type _0 = Z0;

    #[allow(non_camel_case_types)]
    type N3RemN1 = <<A as Rem<B>>::Output as Same<_0>>::Output;

    assert_eq!(<N3RemN1 as Integer>::to_i64(), <_0 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_N3_PartialDiv_N1() {
    type A = NInt<UInt<UInt<UTerm, B1>, B1>>;
    type B = NInt<UInt<UTerm, B1>>;
    type P3 = PInt<UInt<UInt<UTerm, B1>, B1>>;

    #[allow(non_camel_case_types)]
    type N3PartialDivN1 = <<A as PartialDiv<B>>::Output as Same<P3>>::Output;

    assert_eq!(<N3PartialDivN1 as Integer>::to_i64(), <P3 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_N3_Cmp_N1() {
    type A = NInt<UInt<UInt<UTerm, B1>, B1>>;
    type B = NInt<UInt<UTerm, B1>>;

    #[allow(non_camel_case_types)]
    type N3CmpN1 = <A as Cmp<B>>::Output;
    assert_eq!(<N3CmpN1 as Ord>::to_ordering(), Ordering::Less);
}
#[test]
#[allow(non_snake_case)]
fn test_N3_Add__0() {
    type A = NInt<UInt<UInt<UTerm, B1>, B1>>;
    type B = Z0;
    type N3 = NInt<UInt<UInt<UTerm, B1>, B1>>;

    #[allow(non_camel_case_types)]
    type N3Add_0 = <<A as Add<B>>::Output as Same<N3>>::Output;

    assert_eq!(<N3Add_0 as Integer>::to_i64(), <N3 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_N3_Sub__0() {
    type A = NInt<UInt<UInt<UTerm, B1>, B1>>;
    type B = Z0;
    type N3 = NInt<UInt<UInt<UTerm, B1>, B1>>;

    #[allow(non_camel_case_types)]
    type N3Sub_0 = <<A as Sub<B>>::Output as Same<N3>>::Output;

    assert_eq!(<N3Sub_0 as Integer>::to_i64(), <N3 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_N3_Mul__0() {
    type A = NInt<UInt<UInt<UTerm, B1>, B1>>;
    type B = Z0;
    type _0 = Z0;

    #[allow(non_camel_case_types)]
    type N3Mul_0 = <<A as Mul<B>>::Output as Same<_0>>::Output;

    assert_eq!(<N3Mul_0 as Integer>::to_i64(), <_0 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_N3_Min__0() {
    type A = NInt<UInt<UInt<UTerm, B1>, B1>>;
    type B = Z0;
    type N3 = NInt<UInt<UInt<UTerm, B1>, B1>>;

    #[allow(non_camel_case_types)]
    type N3Min_0 = <<A as Min<B>>::Output as Same<N3>>::Output;

    assert_eq!(<N3Min_0 as Integer>::to_i64(), <N3 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_N3_Max__0() {
    type A = NInt<UInt<UInt<UTerm, B1>, B1>>;
    type B = Z0;
    type _0 = Z0;

    #[allow(non_camel_case_types)]
    type N3Max_0 = <<A as Max<B>>::Output as Same<_0>>::Output;

    assert_eq!(<N3Max_0 as Integer>::to_i64(), <_0 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_N3_Gcd__0() {
    type A = NInt<UInt<UInt<UTerm, B1>, B1>>;
    type B = Z0;
    type P3 = PInt<UInt<UInt<UTerm, B1>, B1>>;

    #[allow(non_camel_case_types)]
    type N3Gcd_0 = <<A as Gcd<B>>::Output as Same<P3>>::Output;

    assert_eq!(<N3Gcd_0 as Integer>::to_i64(), <P3 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_N3_Pow__0() {
    type A = NInt<UInt<UInt<UTerm, B1>, B1>>;
    type B = Z0;
    type P1 = PInt<UInt<UTerm, B1>>;

    #[allow(non_camel_case_types)]
    type N3Pow_0 = <<A as Pow<B>>::Output as Same<P1>>::Output;

    assert_eq!(<N3Pow_0 as Integer>::to_i64(), <P1 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_N3_Cmp__0() {
    type A = NInt<UInt<UInt<UTerm, B1>, B1>>;
    type B = Z0;

    #[allow(non_camel_case_types)]
    type N3Cmp_0 = <A as Cmp<B>>::Output;
    assert_eq!(<N3Cmp_0 as Ord>::to_ordering(), Ordering::Less);
}
#[test]
#[allow(non_snake_case)]
fn test_N3_Add_P1() {
    type A = NInt<UInt<UInt<UTerm, B1>, B1>>;
    type B = PInt<UInt<UTerm, B1>>;
    type N2 = NInt<UInt<UInt<UTerm, B1>, B0>>;

    #[allow(non_camel_case_types)]
    type N3AddP1 = <<A as Add<B>>::Output as Same<N2>>::Output;

    assert_eq!(<N3AddP1 as Integer>::to_i64(), <N2 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_N3_Sub_P1() {
    type A = NInt<UInt<UInt<UTerm, B1>, B1>>;
    type B = PInt<UInt<UTerm, B1>>;
    type N4 = NInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>>;

    #[allow(non_camel_case_types)]
    type N3SubP1 = <<A as Sub<B>>::Output as Same<N4>>::Output;

    assert_eq!(<N3SubP1 as Integer>::to_i64(), <N4 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_N3_Mul_P1() {
    type A = NInt<UInt<UInt<UTerm, B1>, B1>>;
    type B = PInt<UInt<UTerm, B1>>;
    type N3 = NInt<UInt<UInt<UTerm, B1>, B1>>;

    #[allow(non_camel_case_types)]
    type N3MulP1 = <<A as Mul<B>>::Output as Same<N3>>::Output;

    assert_eq!(<N3MulP1 as Integer>::to_i64(), <N3 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_N3_Min_P1() {
    type A = NInt<UInt<UInt<UTerm, B1>, B1>>;
    type B = PInt<UInt<UTerm, B1>>;
    type N3 = NInt<UInt<UInt<UTerm, B1>, B1>>;

    #[allow(non_camel_case_types)]
    type N3MinP1 = <<A as Min<B>>::Output as Same<N3>>::Output;

    assert_eq!(<N3MinP1 as Integer>::to_i64(), <N3 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_N3_Max_P1() {
    type A = NInt<UInt<UInt<UTerm, B1>, B1>>;
    type B = PInt<UInt<UTerm, B1>>;
    type P1 = PInt<UInt<UTerm, B1>>;

    #[allow(non_camel_case_types)]
    type N3MaxP1 = <<A as Max<B>>::Output as Same<P1>>::Output;

    assert_eq!(<N3MaxP1 as Integer>::to_i64(), <P1 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_N3_Gcd_P1() {
    type A = NInt<UInt<UInt<UTerm, B1>, B1>>;
    type B = PInt<UInt<UTerm, B1>>;
    type P1 = PInt<UInt<UTerm, B1>>;

    #[allow(non_camel_case_types)]
    type N3GcdP1 = <<A as Gcd<B>>::Output as Same<P1>>::Output;

    assert_eq!(<N3GcdP1 as Integer>::to_i64(), <P1 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_N3_Div_P1() {
    type A = NInt<UInt<UInt<UTerm, B1>, B1>>;
    type B = PInt<UInt<UTerm, B1>>;
    type N3 = NInt<UInt<UInt<UTerm, B1>, B1>>;

    #[allow(non_camel_case_types)]
    type N3DivP1 = <<A as Div<B>>::Output as Same<N3>>::Output;

    assert_eq!(<N3DivP1 as Integer>::to_i64(), <N3 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_N3_Rem_P1() {
    type A = NInt<UInt<UInt<UTerm, B1>, B1>>;
    type B = PInt<UInt<UTerm, B1>>;
    type _0 = Z0;

    #[allow(non_camel_case_types)]
    type N3RemP1 = <<A as Rem<B>>::Output as Same<_0>>::Output;

    assert_eq!(<N3RemP1 as Integer>::to_i64(), <_0 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_N3_PartialDiv_P1() {
    type A = NInt<UInt<UInt<UTerm, B1>, B1>>;
    type B = PInt<UInt<UTerm, B1>>;
    type N3 = NInt<UInt<UInt<UTerm, B1>, B1>>;

    #[allow(non_camel_case_types)]
    type N3PartialDivP1 = <<A as PartialDiv<B>>::Output as Same<N3>>::Output;

    assert_eq!(<N3PartialDivP1 as Integer>::to_i64(), <N3 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_N3_Pow_P1() {
    type A = NInt<UInt<UInt<UTerm, B1>, B1>>;
    type B = PInt<UInt<UTerm, B1>>;
    type N3 = NInt<UInt<UInt<UTerm, B1>, B1>>;

    #[allow(non_camel_case_types)]
    type N3PowP1 = <<A as Pow<B>>::Output as Same<N3>>::Output;

    assert_eq!(<N3PowP1 as Integer>::to_i64(), <N3 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_N3_Cmp_P1() {
    type A = NInt<UInt<UInt<UTerm, B1>, B1>>;
    type B = PInt<UInt<UTerm, B1>>;

    #[allow(non_camel_case_types)]
    type N3CmpP1 = <A as Cmp<B>>::Output;
    assert_eq!(<N3CmpP1 as Ord>::to_ordering(), Ordering::Less);
}
#[test]
#[allow(non_snake_case)]
fn test_N3_Add_P2() {
    type A = NInt<UInt<UInt<UTerm, B1>, B1>>;
    type B = PInt<UInt<UInt<UTerm, B1>, B0>>;
    type N1 = NInt<UInt<UTerm, B1>>;

    #[allow(non_camel_case_types)]
    type N3AddP2 = <<A as Add<B>>::Output as Same<N1>>::Output;

    assert_eq!(<N3AddP2 as Integer>::to_i64(), <N1 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_N3_Sub_P2() {
    type A = NInt<UInt<UInt<UTerm, B1>, B1>>;
    type B = PInt<UInt<UInt<UTerm, B1>, B0>>;
    type N5 = NInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>>;

    #[allow(non_camel_case_types)]
    type N3SubP2 = <<A as Sub<B>>::Output as Same<N5>>::Output;

    assert_eq!(<N3SubP2 as Integer>::to_i64(), <N5 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_N3_Mul_P2() {
    type A = NInt<UInt<UInt<UTerm, B1>, B1>>;
    type B = PInt<UInt<UInt<UTerm, B1>, B0>>;
    type N6 = NInt<UInt<UInt<UInt<UTerm, B1>, B1>, B0>>;

    #[allow(non_camel_case_types)]
    type N3MulP2 = <<A as Mul<B>>::Output as Same<N6>>::Output;

    assert_eq!(<N3MulP2 as Integer>::to_i64(), <N6 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_N3_Min_P2() {
    type A = NInt<UInt<UInt<UTerm, B1>, B1>>;
    type B = PInt<UInt<UInt<UTerm, B1>, B0>>;
    type N3 = NInt<UInt<UInt<UTerm, B1>, B1>>;

    #[allow(non_camel_case_types)]
    type N3MinP2 = <<A as Min<B>>::Output as Same<N3>>::Output;

    assert_eq!(<N3MinP2 as Integer>::to_i64(), <N3 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_N3_Max_P2() {
    type A = NInt<UInt<UInt<UTerm, B1>, B1>>;
    type B = PInt<UInt<UInt<UTerm, B1>, B0>>;
    type P2 = PInt<UInt<UInt<UTerm, B1>, B0>>;

    #[allow(non_camel_case_types)]
    type N3MaxP2 = <<A as Max<B>>::Output as Same<P2>>::Output;

    assert_eq!(<N3MaxP2 as Integer>::to_i64(), <P2 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_N3_Gcd_P2() {
    type A = NInt<UInt<UInt<UTerm, B1>, B1>>;
    type B = PInt<UInt<UInt<UTerm, B1>, B0>>;
    type P1 = PInt<UInt<UTerm, B1>>;

    #[allow(non_camel_case_types)]
    type N3GcdP2 = <<A as Gcd<B>>::Output as Same<P1>>::Output;

    assert_eq!(<N3GcdP2 as Integer>::to_i64(), <P1 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_N3_Div_P2() {
    type A = NInt<UInt<UInt<UTerm, B1>, B1>>;
    type B = PInt<UInt<UInt<UTerm, B1>, B0>>;
    type N1 = NInt<UInt<UTerm, B1>>;

    #[allow(non_camel_case_types)]
    type N3DivP2 = <<A as Div<B>>::Output as Same<N1>>::Output;

    assert_eq!(<N3DivP2 as Integer>::to_i64(), <N1 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_N3_Rem_P2() {
    type A = NInt<UInt<UInt<UTerm, B1>, B1>>;
    type B = PInt<UInt<UInt<UTerm, B1>, B0>>;
    type N1 = NInt<UInt<UTerm, B1>>;

    #[allow(non_camel_case_types)]
    type N3RemP2 = <<A as Rem<B>>::Output as Same<N1>>::Output;

    assert_eq!(<N3RemP2 as Integer>::to_i64(), <N1 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_N3_Pow_P2() {
    type A = NInt<UInt<UInt<UTerm, B1>, B1>>;
    type B = PInt<UInt<UInt<UTerm, B1>, B0>>;
    type P9 = PInt<UInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>, B1>>;

    #[allow(non_camel_case_types)]
    type N3PowP2 = <<A as Pow<B>>::Output as Same<P9>>::Output;

    assert_eq!(<N3PowP2 as Integer>::to_i64(), <P9 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_N3_Cmp_P2() {
    type A = NInt<UInt<UInt<UTerm, B1>, B1>>;
    type B = PInt<UInt<UInt<UTerm, B1>, B0>>;

    #[allow(non_camel_case_types)]
    type N3CmpP2 = <A as Cmp<B>>::Output;
    assert_eq!(<N3CmpP2 as Ord>::to_ordering(), Ordering::Less);
}
#[test]
#[allow(non_snake_case)]
fn test_N3_Add_P3() {
    type A = NInt<UInt<UInt<UTerm, B1>, B1>>;
    type B = PInt<UInt<UInt<UTerm, B1>, B1>>;
    type _0 = Z0;

    #[allow(non_camel_case_types)]
    type N3AddP3 = <<A as Add<B>>::Output as Same<_0>>::Output;

    assert_eq!(<N3AddP3 as Integer>::to_i64(), <_0 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_N3_Sub_P3() {
    type A = NInt<UInt<UInt<UTerm, B1>, B1>>;
    type B = PInt<UInt<UInt<UTerm, B1>, B1>>;
    type N6 = NInt<UInt<UInt<UInt<UTerm, B1>, B1>, B0>>;

    #[allow(non_camel_case_types)]
    type N3SubP3 = <<A as Sub<B>>::Output as Same<N6>>::Output;

    assert_eq!(<N3SubP3 as Integer>::to_i64(), <N6 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_N3_Mul_P3() {
    type A = NInt<UInt<UInt<UTerm, B1>, B1>>;
    type B = PInt<UInt<UInt<UTerm, B1>, B1>>;
    type N9 = NInt<UInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>, B1>>;

    #[allow(non_camel_case_types)]
    type N3MulP3 = <<A as Mul<B>>::Output as Same<N9>>::Output;

    assert_eq!(<N3MulP3 as Integer>::to_i64(), <N9 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_N3_Min_P3() {
    type A = NInt<UInt<UInt<UTerm, B1>, B1>>;
    type B = PInt<UInt<UInt<UTerm, B1>, B1>>;
    type N3 = NInt<UInt<UInt<UTerm, B1>, B1>>;

    #[allow(non_camel_case_types)]
    type N3MinP3 = <<A as Min<B>>::Output as Same<N3>>::Output;

    assert_eq!(<N3MinP3 as Integer>::to_i64(), <N3 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_N3_Max_P3() {
    type A = NInt<UInt<UInt<UTerm, B1>, B1>>;
    type B = PInt<UInt<UInt<UTerm, B1>, B1>>;
    type P3 = PInt<UInt<UInt<UTerm, B1>, B1>>;

    #[allow(non_camel_case_types)]
    type N3MaxP3 = <<A as Max<B>>::Output as Same<P3>>::Output;

    assert_eq!(<N3MaxP3 as Integer>::to_i64(), <P3 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_N3_Gcd_P3() {
    type A = NInt<UInt<UInt<UTerm, B1>, B1>>;
    type B = PInt<UInt<UInt<UTerm, B1>, B1>>;
    type P3 = PInt<UInt<UInt<UTerm, B1>, B1>>;

    #[allow(non_camel_case_types)]
    type N3GcdP3 = <<A as Gcd<B>>::Output as Same<P3>>::Output;

    assert_eq!(<N3GcdP3 as Integer>::to_i64(), <P3 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_N3_Div_P3() {
    type A = NInt<UInt<UInt<UTerm, B1>, B1>>;
    type B = PInt<UInt<UInt<UTerm, B1>, B1>>;
    type N1 = NInt<UInt<UTerm, B1>>;

    #[allow(non_camel_case_types)]
    type N3DivP3 = <<A as Div<B>>::Output as Same<N1>>::Output;

    assert_eq!(<N3DivP3 as Integer>::to_i64(), <N1 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_N3_Rem_P3() {
    type A = NInt<UInt<UInt<UTerm, B1>, B1>>;
    type B = PInt<UInt<UInt<UTerm, B1>, B1>>;
    type _0 = Z0;

    #[allow(non_camel_case_types)]
    type N3RemP3 = <<A as Rem<B>>::Output as Same<_0>>::Output;

    assert_eq!(<N3RemP3 as Integer>::to_i64(), <_0 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_N3_PartialDiv_P3() {
    type A = NInt<UInt<UInt<UTerm, B1>, B1>>;
    type B = PInt<UInt<UInt<UTerm, B1>, B1>>;
    type N1 = NInt<UInt<UTerm, B1>>;

    #[allow(non_camel_case_types)]
    type N3PartialDivP3 = <<A as PartialDiv<B>>::Output as Same<N1>>::Output;

    assert_eq!(<N3PartialDivP3 as Integer>::to_i64(), <N1 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_N3_Pow_P3() {
    type A = NInt<UInt<UInt<UTerm, B1>, B1>>;
    type B = PInt<UInt<UInt<UTerm, B1>, B1>>;
    type N27 = NInt<UInt<UInt<UInt<UInt<UInt<UTerm, B1>, B1>, B0>, B1>, B1>>;

    #[allow(non_camel_case_types)]
    type N3PowP3 = <<A as Pow<B>>::Output as Same<N27>>::Output;

    assert_eq!(<N3PowP3 as Integer>::to_i64(), <N27 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_N3_Cmp_P3() {
    type A = NInt<UInt<UInt<UTerm, B1>, B1>>;
    type B = PInt<UInt<UInt<UTerm, B1>, B1>>;

    #[allow(non_camel_case_types)]
    type N3CmpP3 = <A as Cmp<B>>::Output;
    assert_eq!(<N3CmpP3 as Ord>::to_ordering(), Ordering::Less);
}
#[test]
#[allow(non_snake_case)]
fn test_N3_Add_P4() {
    type A = NInt<UInt<UInt<UTerm, B1>, B1>>;
    type B = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>>;
    type P1 = PInt<UInt<UTerm, B1>>;

    #[allow(non_camel_case_types)]
    type N3AddP4 = <<A as Add<B>>::Output as Same<P1>>::Output;

    assert_eq!(<N3AddP4 as Integer>::to_i64(), <P1 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_N3_Sub_P4() {
    type A = NInt<UInt<UInt<UTerm, B1>, B1>>;
    type B = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>>;
    type N7 = NInt<UInt<UInt<UInt<UTerm, B1>, B1>, B1>>;

    #[allow(non_camel_case_types)]
    type N3SubP4 = <<A as Sub<B>>::Output as Same<N7>>::Output;

    assert_eq!(<N3SubP4 as Integer>::to_i64(), <N7 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_N3_Mul_P4() {
    type A = NInt<UInt<UInt<UTerm, B1>, B1>>;
    type B = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>>;
    type N12 = NInt<UInt<UInt<UInt<UInt<UTerm, B1>, B1>, B0>, B0>>;

    #[allow(non_camel_case_types)]
    type N3MulP4 = <<A as Mul<B>>::Output as Same<N12>>::Output;

    assert_eq!(<N3MulP4 as Integer>::to_i64(), <N12 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_N3_Min_P4() {
    type A = NInt<UInt<UInt<UTerm, B1>, B1>>;
    type B = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>>;
    type N3 = NInt<UInt<UInt<UTerm, B1>, B1>>;

    #[allow(non_camel_case_types)]
    type N3MinP4 = <<A as Min<B>>::Output as Same<N3>>::Output;

    assert_eq!(<N3MinP4 as Integer>::to_i64(), <N3 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_N3_Max_P4() {
    type A = NInt<UInt<UInt<UTerm, B1>, B1>>;
    type B = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>>;
    type P4 = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>>;

    #[allow(non_camel_case_types)]
    type N3MaxP4 = <<A as Max<B>>::Output as Same<P4>>::Output;

    assert_eq!(<N3MaxP4 as Integer>::to_i64(), <P4 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_N3_Gcd_P4() {
    type A = NInt<UInt<UInt<UTerm, B1>, B1>>;
    type B = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>>;
    type P1 = PInt<UInt<UTerm, B1>>;

    #[allow(non_camel_case_types)]
    type N3GcdP4 = <<A as Gcd<B>>::Output as Same<P1>>::Output;

    assert_eq!(<N3GcdP4 as Integer>::to_i64(), <P1 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_N3_Div_P4() {
    type A = NInt<UInt<UInt<UTerm, B1>, B1>>;
    type B = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>>;
    type _0 = Z0;

    #[allow(non_camel_case_types)]
    type N3DivP4 = <<A as Div<B>>::Output as Same<_0>>::Output;

    assert_eq!(<N3DivP4 as Integer>::to_i64(), <_0 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_N3_Rem_P4() {
    type A = NInt<UInt<UInt<UTerm, B1>, B1>>;
    type B = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>>;
    type N3 = NInt<UInt<UInt<UTerm, B1>, B1>>;

    #[allow(non_camel_case_types)]
    type N3RemP4 = <<A as Rem<B>>::Output as Same<N3>>::Output;

    assert_eq!(<N3RemP4 as Integer>::to_i64(), <N3 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_N3_Pow_P4() {
    type A = NInt<UInt<UInt<UTerm, B1>, B1>>;
    type B = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>>;
    type P81 = PInt<UInt<UInt<UInt<UInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>, B0>, B0>, B0>, B1>>;

    #[allow(non_camel_case_types)]
    type N3PowP4 = <<A as Pow<B>>::Output as Same<P81>>::Output;

    assert_eq!(<N3PowP4 as Integer>::to_i64(), <P81 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_N3_Cmp_P4() {
    type A = NInt<UInt<UInt<UTerm, B1>, B1>>;
    type B = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>>;

    #[allow(non_camel_case_types)]
    type N3CmpP4 = <A as Cmp<B>>::Output;
    assert_eq!(<N3CmpP4 as Ord>::to_ordering(), Ordering::Less);
}
#[test]
#[allow(non_snake_case)]
fn test_N3_Add_P5() {
    type A = NInt<UInt<UInt<UTerm, B1>, B1>>;
    type B = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>>;
    type P2 = PInt<UInt<UInt<UTerm, B1>, B0>>;

    #[allow(non_camel_case_types)]
    type N3AddP5 = <<A as Add<B>>::Output as Same<P2>>::Output;

    assert_eq!(<N3AddP5 as Integer>::to_i64(), <P2 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_N3_Sub_P5() {
    type A = NInt<UInt<UInt<UTerm, B1>, B1>>;
    type B = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>>;
    type N8 = NInt<UInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>, B0>>;

    #[allow(non_camel_case_types)]
    type N3SubP5 = <<A as Sub<B>>::Output as Same<N8>>::Output;

    assert_eq!(<N3SubP5 as Integer>::to_i64(), <N8 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_N3_Mul_P5() {
    type A = NInt<UInt<UInt<UTerm, B1>, B1>>;
    type B = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>>;
    type N15 = NInt<UInt<UInt<UInt<UInt<UTerm, B1>, B1>, B1>, B1>>;

    #[allow(non_camel_case_types)]
    type N3MulP5 = <<A as Mul<B>>::Output as Same<N15>>::Output;

    assert_eq!(<N3MulP5 as Integer>::to_i64(), <N15 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_N3_Min_P5() {
    type A = NInt<UInt<UInt<UTerm, B1>, B1>>;
    type B = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>>;
    type N3 = NInt<UInt<UInt<UTerm, B1>, B1>>;

    #[allow(non_camel_case_types)]
    type N3MinP5 = <<A as Min<B>>::Output as Same<N3>>::Output;

    assert_eq!(<N3MinP5 as Integer>::to_i64(), <N3 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_N3_Max_P5() {
    type A = NInt<UInt<UInt<UTerm, B1>, B1>>;
    type B = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>>;
    type P5 = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>>;

    #[allow(non_camel_case_types)]
    type N3MaxP5 = <<A as Max<B>>::Output as Same<P5>>::Output;

    assert_eq!(<N3MaxP5 as Integer>::to_i64(), <P5 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_N3_Gcd_P5() {
    type A = NInt<UInt<UInt<UTerm, B1>, B1>>;
    type B = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>>;
    type P1 = PInt<UInt<UTerm, B1>>;

    #[allow(non_camel_case_types)]
    type N3GcdP5 = <<A as Gcd<B>>::Output as Same<P1>>::Output;

    assert_eq!(<N3GcdP5 as Integer>::to_i64(), <P1 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_N3_Div_P5() {
    type A = NInt<UInt<UInt<UTerm, B1>, B1>>;
    type B = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>>;
    type _0 = Z0;

    #[allow(non_camel_case_types)]
    type N3DivP5 = <<A as Div<B>>::Output as Same<_0>>::Output;

    assert_eq!(<N3DivP5 as Integer>::to_i64(), <_0 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_N3_Rem_P5() {
    type A = NInt<UInt<UInt<UTerm, B1>, B1>>;
    type B = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>>;
    type N3 = NInt<UInt<UInt<UTerm, B1>, B1>>;

    #[allow(non_camel_case_types)]
    type N3RemP5 = <<A as Rem<B>>::Output as Same<N3>>::Output;

    assert_eq!(<N3RemP5 as Integer>::to_i64(), <N3 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_N3_Pow_P5() {
    type A = NInt<UInt<UInt<UTerm, B1>, B1>>;
    type B = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>>;
    type N243 = NInt<UInt<UInt<UInt<UInt<UInt<UInt<UInt<UInt<UTerm, B1>, B1>, B1>, B1>, B0>, B0>, B1>, B1>>;

    #[allow(non_camel_case_types)]
    type N3PowP5 = <<A as Pow<B>>::Output as Same<N243>>::Output;

    assert_eq!(<N3PowP5 as Integer>::to_i64(), <N243 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_N3_Cmp_P5() {
    type A = NInt<UInt<UInt<UTerm, B1>, B1>>;
    type B = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>>;

    #[allow(non_camel_case_types)]
    type N3CmpP5 = <A as Cmp<B>>::Output;
    assert_eq!(<N3CmpP5 as Ord>::to_ordering(), Ordering::Less);
}
#[test]
#[allow(non_snake_case)]
fn test_N2_Add_N5() {
    type A = NInt<UInt<UInt<UTerm, B1>, B0>>;
    type B = NInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>>;
    type N7 = NInt<UInt<UInt<UInt<UTerm, B1>, B1>, B1>>;

    #[allow(non_camel_case_types)]
    type N2AddN5 = <<A as Add<B>>::Output as Same<N7>>::Output;

    assert_eq!(<N2AddN5 as Integer>::to_i64(), <N7 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_N2_Sub_N5() {
    type A = NInt<UInt<UInt<UTerm, B1>, B0>>;
    type B = NInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>>;
    type P3 = PInt<UInt<UInt<UTerm, B1>, B1>>;

    #[allow(non_camel_case_types)]
    type N2SubN5 = <<A as Sub<B>>::Output as Same<P3>>::Output;

    assert_eq!(<N2SubN5 as Integer>::to_i64(), <P3 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_N2_Mul_N5() {
    type A = NInt<UInt<UInt<UTerm, B1>, B0>>;
    type B = NInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>>;
    type P10 = PInt<UInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>, B0>>;

    #[allow(non_camel_case_types)]
    type N2MulN5 = <<A as Mul<B>>::Output as Same<P10>>::Output;

    assert_eq!(<N2MulN5 as Integer>::to_i64(), <P10 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_N2_Min_N5() {
    type A = NInt<UInt<UInt<UTerm, B1>, B0>>;
    type B = NInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>>;
    type N5 = NInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>>;

    #[allow(non_camel_case_types)]
    type N2MinN5 = <<A as Min<B>>::Output as Same<N5>>::Output;

    assert_eq!(<N2MinN5 as Integer>::to_i64(), <N5 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_N2_Max_N5() {
    type A = NInt<UInt<UInt<UTerm, B1>, B0>>;
    type B = NInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>>;
    type N2 = NInt<UInt<UInt<UTerm, B1>, B0>>;

    #[allow(non_camel_case_types)]
    type N2MaxN5 = <<A as Max<B>>::Output as Same<N2>>::Output;

    assert_eq!(<N2MaxN5 as Integer>::to_i64(), <N2 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_N2_Gcd_N5() {
    type A = NInt<UInt<UInt<UTerm, B1>, B0>>;
    type B = NInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>>;
    type P1 = PInt<UInt<UTerm, B1>>;

    #[allow(non_camel_case_types)]
    type N2GcdN5 = <<A as Gcd<B>>::Output as Same<P1>>::Output;

    assert_eq!(<N2GcdN5 as Integer>::to_i64(), <P1 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_N2_Div_N5() {
    type A = NInt<UInt<UInt<UTerm, B1>, B0>>;
    type B = NInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>>;
    type _0 = Z0;

    #[allow(non_camel_case_types)]
    type N2DivN5 = <<A as Div<B>>::Output as Same<_0>>::Output;

    assert_eq!(<N2DivN5 as Integer>::to_i64(), <_0 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_N2_Rem_N5() {
    type A = NInt<UInt<UInt<UTerm, B1>, B0>>;
    type B = NInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>>;
    type N2 = NInt<UInt<UInt<UTerm, B1>, B0>>;

    #[allow(non_camel_case_types)]
    type N2RemN5 = <<A as Rem<B>>::Output as Same<N2>>::Output;

    assert_eq!(<N2RemN5 as Integer>::to_i64(), <N2 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_N2_Cmp_N5() {
    type A = NInt<UInt<UInt<UTerm, B1>, B0>>;
    type B = NInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>>;

    #[allow(non_camel_case_types)]
    type N2CmpN5 = <A as Cmp<B>>::Output;
    assert_eq!(<N2CmpN5 as Ord>::to_ordering(), Ordering::Greater);
}
#[test]
#[allow(non_snake_case)]
fn test_N2_Add_N4() {
    type A = NInt<UInt<UInt<UTerm, B1>, B0>>;
    type B = NInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>>;
    type N6 = NInt<UInt<UInt<UInt<UTerm, B1>, B1>, B0>>;

    #[allow(non_camel_case_types)]
    type N2AddN4 = <<A as Add<B>>::Output as Same<N6>>::Output;

    assert_eq!(<N2AddN4 as Integer>::to_i64(), <N6 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_N2_Sub_N4() {
    type A = NInt<UInt<UInt<UTerm, B1>, B0>>;
    type B = NInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>>;
    type P2 = PInt<UInt<UInt<UTerm, B1>, B0>>;

    #[allow(non_camel_case_types)]
    type N2SubN4 = <<A as Sub<B>>::Output as Same<P2>>::Output;

    assert_eq!(<N2SubN4 as Integer>::to_i64(), <P2 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_N2_Mul_N4() {
    type A = NInt<UInt<UInt<UTerm, B1>, B0>>;
    type B = NInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>>;
    type P8 = PInt<UInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>, B0>>;

    #[allow(non_camel_case_types)]
    type N2MulN4 = <<A as Mul<B>>::Output as Same<P8>>::Output;

    assert_eq!(<N2MulN4 as Integer>::to_i64(), <P8 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_N2_Min_N4() {
    type A = NInt<UInt<UInt<UTerm, B1>, B0>>;
    type B = NInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>>;
    type N4 = NInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>>;

    #[allow(non_camel_case_types)]
    type N2MinN4 = <<A as Min<B>>::Output as Same<N4>>::Output;

    assert_eq!(<N2MinN4 as Integer>::to_i64(), <N4 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_N2_Max_N4() {
    type A = NInt<UInt<UInt<UTerm, B1>, B0>>;
    type B = NInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>>;
    type N2 = NInt<UInt<UInt<UTerm, B1>, B0>>;

    #[allow(non_camel_case_types)]
    type N2MaxN4 = <<A as Max<B>>::Output as Same<N2>>::Output;

    assert_eq!(<N2MaxN4 as Integer>::to_i64(), <N2 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_N2_Gcd_N4() {
    type A = NInt<UInt<UInt<UTerm, B1>, B0>>;
    type B = NInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>>;
    type P2 = PInt<UInt<UInt<UTerm, B1>, B0>>;

    #[allow(non_camel_case_types)]
    type N2GcdN4 = <<A as Gcd<B>>::Output as Same<P2>>::Output;

    assert_eq!(<N2GcdN4 as Integer>::to_i64(), <P2 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_N2_Div_N4() {
    type A = NInt<UInt<UInt<UTerm, B1>, B0>>;
    type B = NInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>>;
    type _0 = Z0;

    #[allow(non_camel_case_types)]
    type N2DivN4 = <<A as Div<B>>::Output as Same<_0>>::Output;

    assert_eq!(<N2DivN4 as Integer>::to_i64(), <_0 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_N2_Rem_N4() {
    type A = NInt<UInt<UInt<UTerm, B1>, B0>>;
    type B = NInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>>;
    type N2 = NInt<UInt<UInt<UTerm, B1>, B0>>;

    #[allow(non_camel_case_types)]
    type N2RemN4 = <<A as Rem<B>>::Output as Same<N2>>::Output;

    assert_eq!(<N2RemN4 as Integer>::to_i64(), <N2 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_N2_Cmp_N4() {
    type A = NInt<UInt<UInt<UTerm, B1>, B0>>;
    type B = NInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>>;

    #[allow(non_camel_case_types)]
    type N2CmpN4 = <A as Cmp<B>>::Output;
    assert_eq!(<N2CmpN4 as Ord>::to_ordering(), Ordering::Greater);
}
#[test]
#[allow(non_snake_case)]
fn test_N2_Add_N3() {
    type A = NInt<UInt<UInt<UTerm, B1>, B0>>;
    type B = NInt<UInt<UInt<UTerm, B1>, B1>>;
    type N5 = NInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>>;

    #[allow(non_camel_case_types)]
    type N2AddN3 = <<A as Add<B>>::Output as Same<N5>>::Output;

    assert_eq!(<N2AddN3 as Integer>::to_i64(), <N5 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_N2_Sub_N3() {
    type A = NInt<UInt<UInt<UTerm, B1>, B0>>;
    type B = NInt<UInt<UInt<UTerm, B1>, B1>>;
    type P1 = PInt<UInt<UTerm, B1>>;

    #[allow(non_camel_case_types)]
    type N2SubN3 = <<A as Sub<B>>::Output as Same<P1>>::Output;

    assert_eq!(<N2SubN3 as Integer>::to_i64(), <P1 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_N2_Mul_N3() {
    type A = NInt<UInt<UInt<UTerm, B1>, B0>>;
    type B = NInt<UInt<UInt<UTerm, B1>, B1>>;
    type P6 = PInt<UInt<UInt<UInt<UTerm, B1>, B1>, B0>>;

    #[allow(non_camel_case_types)]
    type N2MulN3 = <<A as Mul<B>>::Output as Same<P6>>::Output;

    assert_eq!(<N2MulN3 as Integer>::to_i64(), <P6 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_N2_Min_N3() {
    type A = NInt<UInt<UInt<UTerm, B1>, B0>>;
    type B = NInt<UInt<UInt<UTerm, B1>, B1>>;
    type N3 = NInt<UInt<UInt<UTerm, B1>, B1>>;

    #[allow(non_camel_case_types)]
    type N2MinN3 = <<A as Min<B>>::Output as Same<N3>>::Output;

    assert_eq!(<N2MinN3 as Integer>::to_i64(), <N3 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_N2_Max_N3() {
    type A = NInt<UInt<UInt<UTerm, B1>, B0>>;
    type B = NInt<UInt<UInt<UTerm, B1>, B1>>;
    type N2 = NInt<UInt<UInt<UTerm, B1>, B0>>;

    #[allow(non_camel_case_types)]
    type N2MaxN3 = <<A as Max<B>>::Output as Same<N2>>::Output;

    assert_eq!(<N2MaxN3 as Integer>::to_i64(), <N2 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_N2_Gcd_N3() {
    type A = NInt<UInt<UInt<UTerm, B1>, B0>>;
    type B = NInt<UInt<UInt<UTerm, B1>, B1>>;
    type P1 = PInt<UInt<UTerm, B1>>;

    #[allow(non_camel_case_types)]
    type N2GcdN3 = <<A as Gcd<B>>::Output as Same<P1>>::Output;

    assert_eq!(<N2GcdN3 as Integer>::to_i64(), <P1 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_N2_Div_N3() {
    type A = NInt<UInt<UInt<UTerm, B1>, B0>>;
    type B = NInt<UInt<UInt<UTerm, B1>, B1>>;
    type _0 = Z0;

    #[allow(non_camel_case_types)]
    type N2DivN3 = <<A as Div<B>>::Output as Same<_0>>::Output;

    assert_eq!(<N2DivN3 as Integer>::to_i64(), <_0 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_N2_Rem_N3() {
    type A = NInt<UInt<UInt<UTerm, B1>, B0>>;
    type B = NInt<UInt<UInt<UTerm, B1>, B1>>;
    type N2 = NInt<UInt<UInt<UTerm, B1>, B0>>;

    #[allow(non_camel_case_types)]
    type N2RemN3 = <<A as Rem<B>>::Output as Same<N2>>::Output;

    assert_eq!(<N2RemN3 as Integer>::to_i64(), <N2 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_N2_Cmp_N3() {
    type A = NInt<UInt<UInt<UTerm, B1>, B0>>;
    type B = NInt<UInt<UInt<UTerm, B1>, B1>>;

    #[allow(non_camel_case_types)]
    type N2CmpN3 = <A as Cmp<B>>::Output;
    assert_eq!(<N2CmpN3 as Ord>::to_ordering(), Ordering::Greater);
}
#[test]
#[allow(non_snake_case)]
fn test_N2_Add_N2() {
    type A = NInt<UInt<UInt<UTerm, B1>, B0>>;
    type B = NInt<UInt<UInt<UTerm, B1>, B0>>;
    type N4 = NInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>>;

    #[allow(non_camel_case_types)]
    type N2AddN2 = <<A as Add<B>>::Output as Same<N4>>::Output;

    assert_eq!(<N2AddN2 as Integer>::to_i64(), <N4 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_N2_Sub_N2() {
    type A = NInt<UInt<UInt<UTerm, B1>, B0>>;
    type B = NInt<UInt<UInt<UTerm, B1>, B0>>;
    type _0 = Z0;

    #[allow(non_camel_case_types)]
    type N2SubN2 = <<A as Sub<B>>::Output as Same<_0>>::Output;

    assert_eq!(<N2SubN2 as Integer>::to_i64(), <_0 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_N2_Mul_N2() {
    type A = NInt<UInt<UInt<UTerm, B1>, B0>>;
    type B = NInt<UInt<UInt<UTerm, B1>, B0>>;
    type P4 = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>>;

    #[allow(non_camel_case_types)]
    type N2MulN2 = <<A as Mul<B>>::Output as Same<P4>>::Output;

    assert_eq!(<N2MulN2 as Integer>::to_i64(), <P4 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_N2_Min_N2() {
    type A = NInt<UInt<UInt<UTerm, B1>, B0>>;
    type B = NInt<UInt<UInt<UTerm, B1>, B0>>;
    type N2 = NInt<UInt<UInt<UTerm, B1>, B0>>;

    #[allow(non_camel_case_types)]
    type N2MinN2 = <<A as Min<B>>::Output as Same<N2>>::Output;

    assert_eq!(<N2MinN2 as Integer>::to_i64(), <N2 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_N2_Max_N2() {
    type A = NInt<UInt<UInt<UTerm, B1>, B0>>;
    type B = NInt<UInt<UInt<UTerm, B1>, B0>>;
    type N2 = NInt<UInt<UInt<UTerm, B1>, B0>>;

    #[allow(non_camel_case_types)]
    type N2MaxN2 = <<A as Max<B>>::Output as Same<N2>>::Output;

    assert_eq!(<N2MaxN2 as Integer>::to_i64(), <N2 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_N2_Gcd_N2() {
    type A = NInt<UInt<UInt<UTerm, B1>, B0>>;
    type B = NInt<UInt<UInt<UTerm, B1>, B0>>;
    type P2 = PInt<UInt<UInt<UTerm, B1>, B0>>;

    #[allow(non_camel_case_types)]
    type N2GcdN2 = <<A as Gcd<B>>::Output as Same<P2>>::Output;

    assert_eq!(<N2GcdN2 as Integer>::to_i64(), <P2 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_N2_Div_N2() {
    type A = NInt<UInt<UInt<UTerm, B1>, B0>>;
    type B = NInt<UInt<UInt<UTerm, B1>, B0>>;
    type P1 = PInt<UInt<UTerm, B1>>;

    #[allow(non_camel_case_types)]
    type N2DivN2 = <<A as Div<B>>::Output as Same<P1>>::Output;

    assert_eq!(<N2DivN2 as Integer>::to_i64(), <P1 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_N2_Rem_N2() {
    type A = NInt<UInt<UInt<UTerm, B1>, B0>>;
    type B = NInt<UInt<UInt<UTerm, B1>, B0>>;
    type _0 = Z0;

    #[allow(non_camel_case_types)]
    type N2RemN2 = <<A as Rem<B>>::Output as Same<_0>>::Output;

    assert_eq!(<N2RemN2 as Integer>::to_i64(), <_0 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_N2_PartialDiv_N2() {
    type A = NInt<UInt<UInt<UTerm, B1>, B0>>;
    type B = NInt<UInt<UInt<UTerm, B1>, B0>>;
    type P1 = PInt<UInt<UTerm, B1>>;

    #[allow(non_camel_case_types)]
    type N2PartialDivN2 = <<A as PartialDiv<B>>::Output as Same<P1>>::Output;

    assert_eq!(<N2PartialDivN2 as Integer>::to_i64(), <P1 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_N2_Cmp_N2() {
    type A = NInt<UInt<UInt<UTerm, B1>, B0>>;
    type B = NInt<UInt<UInt<UTerm, B1>, B0>>;

    #[allow(non_camel_case_types)]
    type N2CmpN2 = <A as Cmp<B>>::Output;
    assert_eq!(<N2CmpN2 as Ord>::to_ordering(), Ordering::Equal);
}
#[test]
#[allow(non_snake_case)]
fn test_N2_Add_N1() {
    type A = NInt<UInt<UInt<UTerm, B1>, B0>>;
    type B = NInt<UInt<UTerm, B1>>;
    type N3 = NInt<UInt<UInt<UTerm, B1>, B1>>;

    #[allow(non_camel_case_types)]
    type N2AddN1 = <<A as Add<B>>::Output as Same<N3>>::Output;

    assert_eq!(<N2AddN1 as Integer>::to_i64(), <N3 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_N2_Sub_N1() {
    type A = NInt<UInt<UInt<UTerm, B1>, B0>>;
    type B = NInt<UInt<UTerm, B1>>;
    type N1 = NInt<UInt<UTerm, B1>>;

    #[allow(non_camel_case_types)]
    type N2SubN1 = <<A as Sub<B>>::Output as Same<N1>>::Output;

    assert_eq!(<N2SubN1 as Integer>::to_i64(), <N1 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_N2_Mul_N1() {
    type A = NInt<UInt<UInt<UTerm, B1>, B0>>;
    type B = NInt<UInt<UTerm, B1>>;
    type P2 = PInt<UInt<UInt<UTerm, B1>, B0>>;

    #[allow(non_camel_case_types)]
    type N2MulN1 = <<A as Mul<B>>::Output as Same<P2>>::Output;

    assert_eq!(<N2MulN1 as Integer>::to_i64(), <P2 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_N2_Min_N1() {
    type A = NInt<UInt<UInt<UTerm, B1>, B0>>;
    type B = NInt<UInt<UTerm, B1>>;
    type N2 = NInt<UInt<UInt<UTerm, B1>, B0>>;

    #[allow(non_camel_case_types)]
    type N2MinN1 = <<A as Min<B>>::Output as Same<N2>>::Output;

    assert_eq!(<N2MinN1 as Integer>::to_i64(), <N2 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_N2_Max_N1() {
    type A = NInt<UInt<UInt<UTerm, B1>, B0>>;
    type B = NInt<UInt<UTerm, B1>>;
    type N1 = NInt<UInt<UTerm, B1>>;

    #[allow(non_camel_case_types)]
    type N2MaxN1 = <<A as Max<B>>::Output as Same<N1>>::Output;

    assert_eq!(<N2MaxN1 as Integer>::to_i64(), <N1 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_N2_Gcd_N1() {
    type A = NInt<UInt<UInt<UTerm, B1>, B0>>;
    type B = NInt<UInt<UTerm, B1>>;
    type P1 = PInt<UInt<UTerm, B1>>;

    #[allow(non_camel_case_types)]
    type N2GcdN1 = <<A as Gcd<B>>::Output as Same<P1>>::Output;

    assert_eq!(<N2GcdN1 as Integer>::to_i64(), <P1 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_N2_Div_N1() {
    type A = NInt<UInt<UInt<UTerm, B1>, B0>>;
    type B = NInt<UInt<UTerm, B1>>;
    type P2 = PInt<UInt<UInt<UTerm, B1>, B0>>;

    #[allow(non_camel_case_types)]
    type N2DivN1 = <<A as Div<B>>::Output as Same<P2>>::Output;

    assert_eq!(<N2DivN1 as Integer>::to_i64(), <P2 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_N2_Rem_N1() {
    type A = NInt<UInt<UInt<UTerm, B1>, B0>>;
    type B = NInt<UInt<UTerm, B1>>;
    type _0 = Z0;

    #[allow(non_camel_case_types)]
    type N2RemN1 = <<A as Rem<B>>::Output as Same<_0>>::Output;

    assert_eq!(<N2RemN1 as Integer>::to_i64(), <_0 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_N2_PartialDiv_N1() {
    type A = NInt<UInt<UInt<UTerm, B1>, B0>>;
    type B = NInt<UInt<UTerm, B1>>;
    type P2 = PInt<UInt<UInt<UTerm, B1>, B0>>;

    #[allow(non_camel_case_types)]
    type N2PartialDivN1 = <<A as PartialDiv<B>>::Output as Same<P2>>::Output;

    assert_eq!(<N2PartialDivN1 as Integer>::to_i64(), <P2 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_N2_Cmp_N1() {
    type A = NInt<UInt<UInt<UTerm, B1>, B0>>;
    type B = NInt<UInt<UTerm, B1>>;

    #[allow(non_camel_case_types)]
    type N2CmpN1 = <A as Cmp<B>>::Output;
    assert_eq!(<N2CmpN1 as Ord>::to_ordering(), Ordering::Less);
}
#[test]
#[allow(non_snake_case)]
fn test_N2_Add__0() {
    type A = NInt<UInt<UInt<UTerm, B1>, B0>>;
    type B = Z0;
    type N2 = NInt<UInt<UInt<UTerm, B1>, B0>>;

    #[allow(non_camel_case_types)]
    type N2Add_0 = <<A as Add<B>>::Output as Same<N2>>::Output;

    assert_eq!(<N2Add_0 as Integer>::to_i64(), <N2 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_N2_Sub__0() {
    type A = NInt<UInt<UInt<UTerm, B1>, B0>>;
    type B = Z0;
    type N2 = NInt<UInt<UInt<UTerm, B1>, B0>>;

    #[allow(non_camel_case_types)]
    type N2Sub_0 = <<A as Sub<B>>::Output as Same<N2>>::Output;

    assert_eq!(<N2Sub_0 as Integer>::to_i64(), <N2 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_N2_Mul__0() {
    type A = NInt<UInt<UInt<UTerm, B1>, B0>>;
    type B = Z0;
    type _0 = Z0;

    #[allow(non_camel_case_types)]
    type N2Mul_0 = <<A as Mul<B>>::Output as Same<_0>>::Output;

    assert_eq!(<N2Mul_0 as Integer>::to_i64(), <_0 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_N2_Min__0() {
    type A = NInt<UInt<UInt<UTerm, B1>, B0>>;
    type B = Z0;
    type N2 = NInt<UInt<UInt<UTerm, B1>, B0>>;

    #[allow(non_camel_case_types)]
    type N2Min_0 = <<A as Min<B>>::Output as Same<N2>>::Output;

    assert_eq!(<N2Min_0 as Integer>::to_i64(), <N2 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_N2_Max__0() {
    type A = NInt<UInt<UInt<UTerm, B1>, B0>>;
    type B = Z0;
    type _0 = Z0;

    #[allow(non_camel_case_types)]
    type N2Max_0 = <<A as Max<B>>::Output as Same<_0>>::Output;

    assert_eq!(<N2Max_0 as Integer>::to_i64(), <_0 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_N2_Gcd__0() {
    type A = NInt<UInt<UInt<UTerm, B1>, B0>>;
    type B = Z0;
    type P2 = PInt<UInt<UInt<UTerm, B1>, B0>>;

    #[allow(non_camel_case_types)]
    type N2Gcd_0 = <<A as Gcd<B>>::Output as Same<P2>>::Output;

    assert_eq!(<N2Gcd_0 as Integer>::to_i64(), <P2 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_N2_Pow__0() {
    type A = NInt<UInt<UInt<UTerm, B1>, B0>>;
    type B = Z0;
    type P1 = PInt<UInt<UTerm, B1>>;

    #[allow(non_camel_case_types)]
    type N2Pow_0 = <<A as Pow<B>>::Output as Same<P1>>::Output;

    assert_eq!(<N2Pow_0 as Integer>::to_i64(), <P1 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_N2_Cmp__0() {
    type A = NInt<UInt<UInt<UTerm, B1>, B0>>;
    type B = Z0;

    #[allow(non_camel_case_types)]
    type N2Cmp_0 = <A as Cmp<B>>::Output;
    assert_eq!(<N2Cmp_0 as Ord>::to_ordering(), Ordering::Less);
}
#[test]
#[allow(non_snake_case)]
fn test_N2_Add_P1() {
    type A = NInt<UInt<UInt<UTerm, B1>, B0>>;
    type B = PInt<UInt<UTerm, B1>>;
    type N1 = NInt<UInt<UTerm, B1>>;

    #[allow(non_camel_case_types)]
    type N2AddP1 = <<A as Add<B>>::Output as Same<N1>>::Output;

    assert_eq!(<N2AddP1 as Integer>::to_i64(), <N1 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_N2_Sub_P1() {
    type A = NInt<UInt<UInt<UTerm, B1>, B0>>;
    type B = PInt<UInt<UTerm, B1>>;
    type N3 = NInt<UInt<UInt<UTerm, B1>, B1>>;

    #[allow(non_camel_case_types)]
    type N2SubP1 = <<A as Sub<B>>::Output as Same<N3>>::Output;

    assert_eq!(<N2SubP1 as Integer>::to_i64(), <N3 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_N2_Mul_P1() {
    type A = NInt<UInt<UInt<UTerm, B1>, B0>>;
    type B = PInt<UInt<UTerm, B1>>;
    type N2 = NInt<UInt<UInt<UTerm, B1>, B0>>;

    #[allow(non_camel_case_types)]
    type N2MulP1 = <<A as Mul<B>>::Output as Same<N2>>::Output;

    assert_eq!(<N2MulP1 as Integer>::to_i64(), <N2 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_N2_Min_P1() {
    type A = NInt<UInt<UInt<UTerm, B1>, B0>>;
    type B = PInt<UInt<UTerm, B1>>;
    type N2 = NInt<UInt<UInt<UTerm, B1>, B0>>;

    #[allow(non_camel_case_types)]
    type N2MinP1 = <<A as Min<B>>::Output as Same<N2>>::Output;

    assert_eq!(<N2MinP1 as Integer>::to_i64(), <N2 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_N2_Max_P1() {
    type A = NInt<UInt<UInt<UTerm, B1>, B0>>;
    type B = PInt<UInt<UTerm, B1>>;
    type P1 = PInt<UInt<UTerm, B1>>;

    #[allow(non_camel_case_types)]
    type N2MaxP1 = <<A as Max<B>>::Output as Same<P1>>::Output;

    assert_eq!(<N2MaxP1 as Integer>::to_i64(), <P1 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_N2_Gcd_P1() {
    type A = NInt<UInt<UInt<UTerm, B1>, B0>>;
    type B = PInt<UInt<UTerm, B1>>;
    type P1 = PInt<UInt<UTerm, B1>>;

    #[allow(non_camel_case_types)]
    type N2GcdP1 = <<A as Gcd<B>>::Output as Same<P1>>::Output;

    assert_eq!(<N2GcdP1 as Integer>::to_i64(), <P1 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_N2_Div_P1() {
    type A = NInt<UInt<UInt<UTerm, B1>, B0>>;
    type B = PInt<UInt<UTerm, B1>>;
    type N2 = NInt<UInt<UInt<UTerm, B1>, B0>>;

    #[allow(non_camel_case_types)]
    type N2DivP1 = <<A as Div<B>>::Output as Same<N2>>::Output;

    assert_eq!(<N2DivP1 as Integer>::to_i64(), <N2 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_N2_Rem_P1() {
    type A = NInt<UInt<UInt<UTerm, B1>, B0>>;
    type B = PInt<UInt<UTerm, B1>>;
    type _0 = Z0;

    #[allow(non_camel_case_types)]
    type N2RemP1 = <<A as Rem<B>>::Output as Same<_0>>::Output;

    assert_eq!(<N2RemP1 as Integer>::to_i64(), <_0 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_N2_PartialDiv_P1() {
    type A = NInt<UInt<UInt<UTerm, B1>, B0>>;
    type B = PInt<UInt<UTerm, B1>>;
    type N2 = NInt<UInt<UInt<UTerm, B1>, B0>>;

    #[allow(non_camel_case_types)]
    type N2PartialDivP1 = <<A as PartialDiv<B>>::Output as Same<N2>>::Output;

    assert_eq!(<N2PartialDivP1 as Integer>::to_i64(), <N2 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_N2_Pow_P1() {
    type A = NInt<UInt<UInt<UTerm, B1>, B0>>;
    type B = PInt<UInt<UTerm, B1>>;
    type N2 = NInt<UInt<UInt<UTerm, B1>, B0>>;

    #[allow(non_camel_case_types)]
    type N2PowP1 = <<A as Pow<B>>::Output as Same<N2>>::Output;

    assert_eq!(<N2PowP1 as Integer>::to_i64(), <N2 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_N2_Cmp_P1() {
    type A = NInt<UInt<UInt<UTerm, B1>, B0>>;
    type B = PInt<UInt<UTerm, B1>>;

    #[allow(non_camel_case_types)]
    type N2CmpP1 = <A as Cmp<B>>::Output;
    assert_eq!(<N2CmpP1 as Ord>::to_ordering(), Ordering::Less);
}
#[test]
#[allow(non_snake_case)]
fn test_N2_Add_P2() {
    type A = NInt<UInt<UInt<UTerm, B1>, B0>>;
    type B = PInt<UInt<UInt<UTerm, B1>, B0>>;
    type _0 = Z0;

    #[allow(non_camel_case_types)]
    type N2AddP2 = <<A as Add<B>>::Output as Same<_0>>::Output;

    assert_eq!(<N2AddP2 as Integer>::to_i64(), <_0 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_N2_Sub_P2() {
    type A = NInt<UInt<UInt<UTerm, B1>, B0>>;
    type B = PInt<UInt<UInt<UTerm, B1>, B0>>;
    type N4 = NInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>>;

    #[allow(non_camel_case_types)]
    type N2SubP2 = <<A as Sub<B>>::Output as Same<N4>>::Output;

    assert_eq!(<N2SubP2 as Integer>::to_i64(), <N4 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_N2_Mul_P2() {
    type A = NInt<UInt<UInt<UTerm, B1>, B0>>;
    type B = PInt<UInt<UInt<UTerm, B1>, B0>>;
    type N4 = NInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>>;

    #[allow(non_camel_case_types)]
    type N2MulP2 = <<A as Mul<B>>::Output as Same<N4>>::Output;

    assert_eq!(<N2MulP2 as Integer>::to_i64(), <N4 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_N2_Min_P2() {
    type A = NInt<UInt<UInt<UTerm, B1>, B0>>;
    type B = PInt<UInt<UInt<UTerm, B1>, B0>>;
    type N2 = NInt<UInt<UInt<UTerm, B1>, B0>>;

    #[allow(non_camel_case_types)]
    type N2MinP2 = <<A as Min<B>>::Output as Same<N2>>::Output;

    assert_eq!(<N2MinP2 as Integer>::to_i64(), <N2 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_N2_Max_P2() {
    type A = NInt<UInt<UInt<UTerm, B1>, B0>>;
    type B = PInt<UInt<UInt<UTerm, B1>, B0>>;
    type P2 = PInt<UInt<UInt<UTerm, B1>, B0>>;

    #[allow(non_camel_case_types)]
    type N2MaxP2 = <<A as Max<B>>::Output as Same<P2>>::Output;

    assert_eq!(<N2MaxP2 as Integer>::to_i64(), <P2 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_N2_Gcd_P2() {
    type A = NInt<UInt<UInt<UTerm, B1>, B0>>;
    type B = PInt<UInt<UInt<UTerm, B1>, B0>>;
    type P2 = PInt<UInt<UInt<UTerm, B1>, B0>>;

    #[allow(non_camel_case_types)]
    type N2GcdP2 = <<A as Gcd<B>>::Output as Same<P2>>::Output;

    assert_eq!(<N2GcdP2 as Integer>::to_i64(), <P2 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_N2_Div_P2() {
    type A = NInt<UInt<UInt<UTerm, B1>, B0>>;
    type B = PInt<UInt<UInt<UTerm, B1>, B0>>;
    type N1 = NInt<UInt<UTerm, B1>>;

    #[allow(non_camel_case_types)]
    type N2DivP2 = <<A as Div<B>>::Output as Same<N1>>::Output;

    assert_eq!(<N2DivP2 as Integer>::to_i64(), <N1 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_N2_Rem_P2() {
    type A = NInt<UInt<UInt<UTerm, B1>, B0>>;
    type B = PInt<UInt<UInt<UTerm, B1>, B0>>;
    type _0 = Z0;

    #[allow(non_camel_case_types)]
    type N2RemP2 = <<A as Rem<B>>::Output as Same<_0>>::Output;

    assert_eq!(<N2RemP2 as Integer>::to_i64(), <_0 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_N2_PartialDiv_P2() {
    type A = NInt<UInt<UInt<UTerm, B1>, B0>>;
    type B = PInt<UInt<UInt<UTerm, B1>, B0>>;
    type N1 = NInt<UInt<UTerm, B1>>;

    #[allow(non_camel_case_types)]
    type N2PartialDivP2 = <<A as PartialDiv<B>>::Output as Same<N1>>::Output;

    assert_eq!(<N2PartialDivP2 as Integer>::to_i64(), <N1 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_N2_Pow_P2() {
    type A = NInt<UInt<UInt<UTerm, B1>, B0>>;
    type B = PInt<UInt<UInt<UTerm, B1>, B0>>;
    type P4 = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>>;

    #[allow(non_camel_case_types)]
    type N2PowP2 = <<A as Pow<B>>::Output as Same<P4>>::Output;

    assert_eq!(<N2PowP2 as Integer>::to_i64(), <P4 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_N2_Cmp_P2() {
    type A = NInt<UInt<UInt<UTerm, B1>, B0>>;
    type B = PInt<UInt<UInt<UTerm, B1>, B0>>;

    #[allow(non_camel_case_types)]
    type N2CmpP2 = <A as Cmp<B>>::Output;
    assert_eq!(<N2CmpP2 as Ord>::to_ordering(), Ordering::Less);
}
#[test]
#[allow(non_snake_case)]
fn test_N2_Add_P3() {
    type A = NInt<UInt<UInt<UTerm, B1>, B0>>;
    type B = PInt<UInt<UInt<UTerm, B1>, B1>>;
    type P1 = PInt<UInt<UTerm, B1>>;

    #[allow(non_camel_case_types)]
    type N2AddP3 = <<A as Add<B>>::Output as Same<P1>>::Output;

    assert_eq!(<N2AddP3 as Integer>::to_i64(), <P1 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_N2_Sub_P3() {
    type A = NInt<UInt<UInt<UTerm, B1>, B0>>;
    type B = PInt<UInt<UInt<UTerm, B1>, B1>>;
    type N5 = NInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>>;

    #[allow(non_camel_case_types)]
    type N2SubP3 = <<A as Sub<B>>::Output as Same<N5>>::Output;

    assert_eq!(<N2SubP3 as Integer>::to_i64(), <N5 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_N2_Mul_P3() {
    type A = NInt<UInt<UInt<UTerm, B1>, B0>>;
    type B = PInt<UInt<UInt<UTerm, B1>, B1>>;
    type N6 = NInt<UInt<UInt<UInt<UTerm, B1>, B1>, B0>>;

    #[allow(non_camel_case_types)]
    type N2MulP3 = <<A as Mul<B>>::Output as Same<N6>>::Output;

    assert_eq!(<N2MulP3 as Integer>::to_i64(), <N6 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_N2_Min_P3() {
    type A = NInt<UInt<UInt<UTerm, B1>, B0>>;
    type B = PInt<UInt<UInt<UTerm, B1>, B1>>;
    type N2 = NInt<UInt<UInt<UTerm, B1>, B0>>;

    #[allow(non_camel_case_types)]
    type N2MinP3 = <<A as Min<B>>::Output as Same<N2>>::Output;

    assert_eq!(<N2MinP3 as Integer>::to_i64(), <N2 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_N2_Max_P3() {
    type A = NInt<UInt<UInt<UTerm, B1>, B0>>;
    type B = PInt<UInt<UInt<UTerm, B1>, B1>>;
    type P3 = PInt<UInt<UInt<UTerm, B1>, B1>>;

    #[allow(non_camel_case_types)]
    type N2MaxP3 = <<A as Max<B>>::Output as Same<P3>>::Output;

    assert_eq!(<N2MaxP3 as Integer>::to_i64(), <P3 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_N2_Gcd_P3() {
    type A = NInt<UInt<UInt<UTerm, B1>, B0>>;
    type B = PInt<UInt<UInt<UTerm, B1>, B1>>;
    type P1 = PInt<UInt<UTerm, B1>>;

    #[allow(non_camel_case_types)]
    type N2GcdP3 = <<A as Gcd<B>>::Output as Same<P1>>::Output;

    assert_eq!(<N2GcdP3 as Integer>::to_i64(), <P1 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_N2_Div_P3() {
    type A = NInt<UInt<UInt<UTerm, B1>, B0>>;
    type B = PInt<UInt<UInt<UTerm, B1>, B1>>;
    type _0 = Z0;

    #[allow(non_camel_case_types)]
    type N2DivP3 = <<A as Div<B>>::Output as Same<_0>>::Output;

    assert_eq!(<N2DivP3 as Integer>::to_i64(), <_0 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_N2_Rem_P3() {
    type A = NInt<UInt<UInt<UTerm, B1>, B0>>;
    type B = PInt<UInt<UInt<UTerm, B1>, B1>>;
    type N2 = NInt<UInt<UInt<UTerm, B1>, B0>>;

    #[allow(non_camel_case_types)]
    type N2RemP3 = <<A as Rem<B>>::Output as Same<N2>>::Output;

    assert_eq!(<N2RemP3 as Integer>::to_i64(), <N2 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_N2_Pow_P3() {
    type A = NInt<UInt<UInt<UTerm, B1>, B0>>;
    type B = PInt<UInt<UInt<UTerm, B1>, B1>>;
    type N8 = NInt<UInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>, B0>>;

    #[allow(non_camel_case_types)]
    type N2PowP3 = <<A as Pow<B>>::Output as Same<N8>>::Output;

    assert_eq!(<N2PowP3 as Integer>::to_i64(), <N8 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_N2_Cmp_P3() {
    type A = NInt<UInt<UInt<UTerm, B1>, B0>>;
    type B = PInt<UInt<UInt<UTerm, B1>, B1>>;

    #[allow(non_camel_case_types)]
    type N2CmpP3 = <A as Cmp<B>>::Output;
    assert_eq!(<N2CmpP3 as Ord>::to_ordering(), Ordering::Less);
}
#[test]
#[allow(non_snake_case)]
fn test_N2_Add_P4() {
    type A = NInt<UInt<UInt<UTerm, B1>, B0>>;
    type B = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>>;
    type P2 = PInt<UInt<UInt<UTerm, B1>, B0>>;

    #[allow(non_camel_case_types)]
    type N2AddP4 = <<A as Add<B>>::Output as Same<P2>>::Output;

    assert_eq!(<N2AddP4 as Integer>::to_i64(), <P2 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_N2_Sub_P4() {
    type A = NInt<UInt<UInt<UTerm, B1>, B0>>;
    type B = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>>;
    type N6 = NInt<UInt<UInt<UInt<UTerm, B1>, B1>, B0>>;

    #[allow(non_camel_case_types)]
    type N2SubP4 = <<A as Sub<B>>::Output as Same<N6>>::Output;

    assert_eq!(<N2SubP4 as Integer>::to_i64(), <N6 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_N2_Mul_P4() {
    type A = NInt<UInt<UInt<UTerm, B1>, B0>>;
    type B = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>>;
    type N8 = NInt<UInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>, B0>>;

    #[allow(non_camel_case_types)]
    type N2MulP4 = <<A as Mul<B>>::Output as Same<N8>>::Output;

    assert_eq!(<N2MulP4 as Integer>::to_i64(), <N8 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_N2_Min_P4() {
    type A = NInt<UInt<UInt<UTerm, B1>, B0>>;
    type B = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>>;
    type N2 = NInt<UInt<UInt<UTerm, B1>, B0>>;

    #[allow(non_camel_case_types)]
    type N2MinP4 = <<A as Min<B>>::Output as Same<N2>>::Output;

    assert_eq!(<N2MinP4 as Integer>::to_i64(), <N2 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_N2_Max_P4() {
    type A = NInt<UInt<UInt<UTerm, B1>, B0>>;
    type B = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>>;
    type P4 = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>>;

    #[allow(non_camel_case_types)]
    type N2MaxP4 = <<A as Max<B>>::Output as Same<P4>>::Output;

    assert_eq!(<N2MaxP4 as Integer>::to_i64(), <P4 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_N2_Gcd_P4() {
    type A = NInt<UInt<UInt<UTerm, B1>, B0>>;
    type B = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>>;
    type P2 = PInt<UInt<UInt<UTerm, B1>, B0>>;

    #[allow(non_camel_case_types)]
    type N2GcdP4 = <<A as Gcd<B>>::Output as Same<P2>>::Output;

    assert_eq!(<N2GcdP4 as Integer>::to_i64(), <P2 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_N2_Div_P4() {
    type A = NInt<UInt<UInt<UTerm, B1>, B0>>;
    type B = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>>;
    type _0 = Z0;

    #[allow(non_camel_case_types)]
    type N2DivP4 = <<A as Div<B>>::Output as Same<_0>>::Output;

    assert_eq!(<N2DivP4 as Integer>::to_i64(), <_0 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_N2_Rem_P4() {
    type A = NInt<UInt<UInt<UTerm, B1>, B0>>;
    type B = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>>;
    type N2 = NInt<UInt<UInt<UTerm, B1>, B0>>;

    #[allow(non_camel_case_types)]
    type N2RemP4 = <<A as Rem<B>>::Output as Same<N2>>::Output;

    assert_eq!(<N2RemP4 as Integer>::to_i64(), <N2 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_N2_Pow_P4() {
    type A = NInt<UInt<UInt<UTerm, B1>, B0>>;
    type B = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>>;
    type P16 = PInt<UInt<UInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>, B0>, B0>>;

    #[allow(non_camel_case_types)]
    type N2PowP4 = <<A as Pow<B>>::Output as Same<P16>>::Output;

    assert_eq!(<N2PowP4 as Integer>::to_i64(), <P16 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_N2_Cmp_P4() {
    type A = NInt<UInt<UInt<UTerm, B1>, B0>>;
    type B = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>>;

    #[allow(non_camel_case_types)]
    type N2CmpP4 = <A as Cmp<B>>::Output;
    assert_eq!(<N2CmpP4 as Ord>::to_ordering(), Ordering::Less);
}
#[test]
#[allow(non_snake_case)]
fn test_N2_Add_P5() {
    type A = NInt<UInt<UInt<UTerm, B1>, B0>>;
    type B = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>>;
    type P3 = PInt<UInt<UInt<UTerm, B1>, B1>>;

    #[allow(non_camel_case_types)]
    type N2AddP5 = <<A as Add<B>>::Output as Same<P3>>::Output;

    assert_eq!(<N2AddP5 as Integer>::to_i64(), <P3 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_N2_Sub_P5() {
    type A = NInt<UInt<UInt<UTerm, B1>, B0>>;
    type B = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>>;
    type N7 = NInt<UInt<UInt<UInt<UTerm, B1>, B1>, B1>>;

    #[allow(non_camel_case_types)]
    type N2SubP5 = <<A as Sub<B>>::Output as Same<N7>>::Output;

    assert_eq!(<N2SubP5 as Integer>::to_i64(), <N7 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_N2_Mul_P5() {
    type A = NInt<UInt<UInt<UTerm, B1>, B0>>;
    type B = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>>;
    type N10 = NInt<UInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>, B0>>;

    #[allow(non_camel_case_types)]
    type N2MulP5 = <<A as Mul<B>>::Output as Same<N10>>::Output;

    assert_eq!(<N2MulP5 as Integer>::to_i64(), <N10 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_N2_Min_P5() {
    type A = NInt<UInt<UInt<UTerm, B1>, B0>>;
    type B = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>>;
    type N2 = NInt<UInt<UInt<UTerm, B1>, B0>>;

    #[allow(non_camel_case_types)]
    type N2MinP5 = <<A as Min<B>>::Output as Same<N2>>::Output;

    assert_eq!(<N2MinP5 as Integer>::to_i64(), <N2 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_N2_Max_P5() {
    type A = NInt<UInt<UInt<UTerm, B1>, B0>>;
    type B = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>>;
    type P5 = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>>;

    #[allow(non_camel_case_types)]
    type N2MaxP5 = <<A as Max<B>>::Output as Same<P5>>::Output;

    assert_eq!(<N2MaxP5 as Integer>::to_i64(), <P5 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_N2_Gcd_P5() {
    type A = NInt<UInt<UInt<UTerm, B1>, B0>>;
    type B = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>>;
    type P1 = PInt<UInt<UTerm, B1>>;

    #[allow(non_camel_case_types)]
    type N2GcdP5 = <<A as Gcd<B>>::Output as Same<P1>>::Output;

    assert_eq!(<N2GcdP5 as Integer>::to_i64(), <P1 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_N2_Div_P5() {
    type A = NInt<UInt<UInt<UTerm, B1>, B0>>;
    type B = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>>;
    type _0 = Z0;

    #[allow(non_camel_case_types)]
    type N2DivP5 = <<A as Div<B>>::Output as Same<_0>>::Output;

    assert_eq!(<N2DivP5 as Integer>::to_i64(), <_0 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_N2_Rem_P5() {
    type A = NInt<UInt<UInt<UTerm, B1>, B0>>;
    type B = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>>;
    type N2 = NInt<UInt<UInt<UTerm, B1>, B0>>;

    #[allow(non_camel_case_types)]
    type N2RemP5 = <<A as Rem<B>>::Output as Same<N2>>::Output;

    assert_eq!(<N2RemP5 as Integer>::to_i64(), <N2 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_N2_Pow_P5() {
    type A = NInt<UInt<UInt<UTerm, B1>, B0>>;
    type B = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>>;
    type N32 = NInt<UInt<UInt<UInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>, B0>, B0>, B0>>;

    #[allow(non_camel_case_types)]
    type N2PowP5 = <<A as Pow<B>>::Output as Same<N32>>::Output;

    assert_eq!(<N2PowP5 as Integer>::to_i64(), <N32 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_N2_Cmp_P5() {
    type A = NInt<UInt<UInt<UTerm, B1>, B0>>;
    type B = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>>;

    #[allow(non_camel_case_types)]
    type N2CmpP5 = <A as Cmp<B>>::Output;
    assert_eq!(<N2CmpP5 as Ord>::to_ordering(), Ordering::Less);
}
#[test]
#[allow(non_snake_case)]
fn test_N1_Add_N5() {
    type A = NInt<UInt<UTerm, B1>>;
    type B = NInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>>;
    type N6 = NInt<UInt<UInt<UInt<UTerm, B1>, B1>, B0>>;

    #[allow(non_camel_case_types)]
    type N1AddN5 = <<A as Add<B>>::Output as Same<N6>>::Output;

    assert_eq!(<N1AddN5 as Integer>::to_i64(), <N6 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_N1_Sub_N5() {
    type A = NInt<UInt<UTerm, B1>>;
    type B = NInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>>;
    type P4 = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>>;

    #[allow(non_camel_case_types)]
    type N1SubN5 = <<A as Sub<B>>::Output as Same<P4>>::Output;

    assert_eq!(<N1SubN5 as Integer>::to_i64(), <P4 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_N1_Mul_N5() {
    type A = NInt<UInt<UTerm, B1>>;
    type B = NInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>>;
    type P5 = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>>;

    #[allow(non_camel_case_types)]
    type N1MulN5 = <<A as Mul<B>>::Output as Same<P5>>::Output;

    assert_eq!(<N1MulN5 as Integer>::to_i64(), <P5 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_N1_Min_N5() {
    type A = NInt<UInt<UTerm, B1>>;
    type B = NInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>>;
    type N5 = NInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>>;

    #[allow(non_camel_case_types)]
    type N1MinN5 = <<A as Min<B>>::Output as Same<N5>>::Output;

    assert_eq!(<N1MinN5 as Integer>::to_i64(), <N5 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_N1_Max_N5() {
    type A = NInt<UInt<UTerm, B1>>;
    type B = NInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>>;
    type N1 = NInt<UInt<UTerm, B1>>;

    #[allow(non_camel_case_types)]
    type N1MaxN5 = <<A as Max<B>>::Output as Same<N1>>::Output;

    assert_eq!(<N1MaxN5 as Integer>::to_i64(), <N1 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_N1_Gcd_N5() {
    type A = NInt<UInt<UTerm, B1>>;
    type B = NInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>>;
    type P1 = PInt<UInt<UTerm, B1>>;

    #[allow(non_camel_case_types)]
    type N1GcdN5 = <<A as Gcd<B>>::Output as Same<P1>>::Output;

    assert_eq!(<N1GcdN5 as Integer>::to_i64(), <P1 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_N1_Div_N5() {
    type A = NInt<UInt<UTerm, B1>>;
    type B = NInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>>;
    type _0 = Z0;

    #[allow(non_camel_case_types)]
    type N1DivN5 = <<A as Div<B>>::Output as Same<_0>>::Output;

    assert_eq!(<N1DivN5 as Integer>::to_i64(), <_0 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_N1_Rem_N5() {
    type A = NInt<UInt<UTerm, B1>>;
    type B = NInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>>;
    type N1 = NInt<UInt<UTerm, B1>>;

    #[allow(non_camel_case_types)]
    type N1RemN5 = <<A as Rem<B>>::Output as Same<N1>>::Output;

    assert_eq!(<N1RemN5 as Integer>::to_i64(), <N1 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_N1_Pow_N5() {
    type A = NInt<UInt<UTerm, B1>>;
    type B = NInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>>;
    type N1 = NInt<UInt<UTerm, B1>>;

    #[allow(non_camel_case_types)]
    type N1PowN5 = <<A as Pow<B>>::Output as Same<N1>>::Output;

    assert_eq!(<N1PowN5 as Integer>::to_i64(), <N1 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_N1_Cmp_N5() {
    type A = NInt<UInt<UTerm, B1>>;
    type B = NInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>>;

    #[allow(non_camel_case_types)]
    type N1CmpN5 = <A as Cmp<B>>::Output;
    assert_eq!(<N1CmpN5 as Ord>::to_ordering(), Ordering::Greater);
}
#[test]
#[allow(non_snake_case)]
fn test_N1_Add_N4() {
    type A = NInt<UInt<UTerm, B1>>;
    type B = NInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>>;
    type N5 = NInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>>;

    #[allow(non_camel_case_types)]
    type N1AddN4 = <<A as Add<B>>::Output as Same<N5>>::Output;

    assert_eq!(<N1AddN4 as Integer>::to_i64(), <N5 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_N1_Sub_N4() {
    type A = NInt<UInt<UTerm, B1>>;
    type B = NInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>>;
    type P3 = PInt<UInt<UInt<UTerm, B1>, B1>>;

    #[allow(non_camel_case_types)]
    type N1SubN4 = <<A as Sub<B>>::Output as Same<P3>>::Output;

    assert_eq!(<N1SubN4 as Integer>::to_i64(), <P3 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_N1_Mul_N4() {
    type A = NInt<UInt<UTerm, B1>>;
    type B = NInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>>;
    type P4 = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>>;

    #[allow(non_camel_case_types)]
    type N1MulN4 = <<A as Mul<B>>::Output as Same<P4>>::Output;

    assert_eq!(<N1MulN4 as Integer>::to_i64(), <P4 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_N1_Min_N4() {
    type A = NInt<UInt<UTerm, B1>>;
    type B = NInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>>;
    type N4 = NInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>>;

    #[allow(non_camel_case_types)]
    type N1MinN4 = <<A as Min<B>>::Output as Same<N4>>::Output;

    assert_eq!(<N1MinN4 as Integer>::to_i64(), <N4 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_N1_Max_N4() {
    type A = NInt<UInt<UTerm, B1>>;
    type B = NInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>>;
    type N1 = NInt<UInt<UTerm, B1>>;

    #[allow(non_camel_case_types)]
    type N1MaxN4 = <<A as Max<B>>::Output as Same<N1>>::Output;

    assert_eq!(<N1MaxN4 as Integer>::to_i64(), <N1 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_N1_Gcd_N4() {
    type A = NInt<UInt<UTerm, B1>>;
    type B = NInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>>;
    type P1 = PInt<UInt<UTerm, B1>>;

    #[allow(non_camel_case_types)]
    type N1GcdN4 = <<A as Gcd<B>>::Output as Same<P1>>::Output;

    assert_eq!(<N1GcdN4 as Integer>::to_i64(), <P1 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_N1_Div_N4() {
    type A = NInt<UInt<UTerm, B1>>;
    type B = NInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>>;
    type _0 = Z0;

    #[allow(non_camel_case_types)]
    type N1DivN4 = <<A as Div<B>>::Output as Same<_0>>::Output;

    assert_eq!(<N1DivN4 as Integer>::to_i64(), <_0 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_N1_Rem_N4() {
    type A = NInt<UInt<UTerm, B1>>;
    type B = NInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>>;
    type N1 = NInt<UInt<UTerm, B1>>;

    #[allow(non_camel_case_types)]
    type N1RemN4 = <<A as Rem<B>>::Output as Same<N1>>::Output;

    assert_eq!(<N1RemN4 as Integer>::to_i64(), <N1 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_N1_Pow_N4() {
    type A = NInt<UInt<UTerm, B1>>;
    type B = NInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>>;
    type P1 = PInt<UInt<UTerm, B1>>;

    #[allow(non_camel_case_types)]
    type N1PowN4 = <<A as Pow<B>>::Output as Same<P1>>::Output;

    assert_eq!(<N1PowN4 as Integer>::to_i64(), <P1 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_N1_Cmp_N4() {
    type A = NInt<UInt<UTerm, B1>>;
    type B = NInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>>;

    #[allow(non_camel_case_types)]
    type N1CmpN4 = <A as Cmp<B>>::Output;
    assert_eq!(<N1CmpN4 as Ord>::to_ordering(), Ordering::Greater);
}
#[test]
#[allow(non_snake_case)]
fn test_N1_Add_N3() {
    type A = NInt<UInt<UTerm, B1>>;
    type B = NInt<UInt<UInt<UTerm, B1>, B1>>;
    type N4 = NInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>>;

    #[allow(non_camel_case_types)]
    type N1AddN3 = <<A as Add<B>>::Output as Same<N4>>::Output;

    assert_eq!(<N1AddN3 as Integer>::to_i64(), <N4 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_N1_Sub_N3() {
    type A = NInt<UInt<UTerm, B1>>;
    type B = NInt<UInt<UInt<UTerm, B1>, B1>>;
    type P2 = PInt<UInt<UInt<UTerm, B1>, B0>>;

    #[allow(non_camel_case_types)]
    type N1SubN3 = <<A as Sub<B>>::Output as Same<P2>>::Output;

    assert_eq!(<N1SubN3 as Integer>::to_i64(), <P2 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_N1_Mul_N3() {
    type A = NInt<UInt<UTerm, B1>>;
    type B = NInt<UInt<UInt<UTerm, B1>, B1>>;
    type P3 = PInt<UInt<UInt<UTerm, B1>, B1>>;

    #[allow(non_camel_case_types)]
    type N1MulN3 = <<A as Mul<B>>::Output as Same<P3>>::Output;

    assert_eq!(<N1MulN3 as Integer>::to_i64(), <P3 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_N1_Min_N3() {
    type A = NInt<UInt<UTerm, B1>>;
    type B = NInt<UInt<UInt<UTerm, B1>, B1>>;
    type N3 = NInt<UInt<UInt<UTerm, B1>, B1>>;

    #[allow(non_camel_case_types)]
    type N1MinN3 = <<A as Min<B>>::Output as Same<N3>>::Output;

    assert_eq!(<N1MinN3 as Integer>::to_i64(), <N3 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_N1_Max_N3() {
    type A = NInt<UInt<UTerm, B1>>;
    type B = NInt<UInt<UInt<UTerm, B1>, B1>>;
    type N1 = NInt<UInt<UTerm, B1>>;

    #[allow(non_camel_case_types)]
    type N1MaxN3 = <<A as Max<B>>::Output as Same<N1>>::Output;

    assert_eq!(<N1MaxN3 as Integer>::to_i64(), <N1 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_N1_Gcd_N3() {
    type A = NInt<UInt<UTerm, B1>>;
    type B = NInt<UInt<UInt<UTerm, B1>, B1>>;
    type P1 = PInt<UInt<UTerm, B1>>;

    #[allow(non_camel_case_types)]
    type N1GcdN3 = <<A as Gcd<B>>::Output as Same<P1>>::Output;

    assert_eq!(<N1GcdN3 as Integer>::to_i64(), <P1 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_N1_Div_N3() {
    type A = NInt<UInt<UTerm, B1>>;
    type B = NInt<UInt<UInt<UTerm, B1>, B1>>;
    type _0 = Z0;

    #[allow(non_camel_case_types)]
    type N1DivN3 = <<A as Div<B>>::Output as Same<_0>>::Output;

    assert_eq!(<N1DivN3 as Integer>::to_i64(), <_0 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_N1_Rem_N3() {
    type A = NInt<UInt<UTerm, B1>>;
    type B = NInt<UInt<UInt<UTerm, B1>, B1>>;
    type N1 = NInt<UInt<UTerm, B1>>;

    #[allow(non_camel_case_types)]
    type N1RemN3 = <<A as Rem<B>>::Output as Same<N1>>::Output;

    assert_eq!(<N1RemN3 as Integer>::to_i64(), <N1 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_N1_Pow_N3() {
    type A = NInt<UInt<UTerm, B1>>;
    type B = NInt<UInt<UInt<UTerm, B1>, B1>>;
    type N1 = NInt<UInt<UTerm, B1>>;

    #[allow(non_camel_case_types)]
    type N1PowN3 = <<A as Pow<B>>::Output as Same<N1>>::Output;

    assert_eq!(<N1PowN3 as Integer>::to_i64(), <N1 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_N1_Cmp_N3() {
    type A = NInt<UInt<UTerm, B1>>;
    type B = NInt<UInt<UInt<UTerm, B1>, B1>>;

    #[allow(non_camel_case_types)]
    type N1CmpN3 = <A as Cmp<B>>::Output;
    assert_eq!(<N1CmpN3 as Ord>::to_ordering(), Ordering::Greater);
}
#[test]
#[allow(non_snake_case)]
fn test_N1_Add_N2() {
    type A = NInt<UInt<UTerm, B1>>;
    type B = NInt<UInt<UInt<UTerm, B1>, B0>>;
    type N3 = NInt<UInt<UInt<UTerm, B1>, B1>>;

    #[allow(non_camel_case_types)]
    type N1AddN2 = <<A as Add<B>>::Output as Same<N3>>::Output;

    assert_eq!(<N1AddN2 as Integer>::to_i64(), <N3 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_N1_Sub_N2() {
    type A = NInt<UInt<UTerm, B1>>;
    type B = NInt<UInt<UInt<UTerm, B1>, B0>>;
    type P1 = PInt<UInt<UTerm, B1>>;

    #[allow(non_camel_case_types)]
    type N1SubN2 = <<A as Sub<B>>::Output as Same<P1>>::Output;

    assert_eq!(<N1SubN2 as Integer>::to_i64(), <P1 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_N1_Mul_N2() {
    type A = NInt<UInt<UTerm, B1>>;
    type B = NInt<UInt<UInt<UTerm, B1>, B0>>;
    type P2 = PInt<UInt<UInt<UTerm, B1>, B0>>;

    #[allow(non_camel_case_types)]
    type N1MulN2 = <<A as Mul<B>>::Output as Same<P2>>::Output;

    assert_eq!(<N1MulN2 as Integer>::to_i64(), <P2 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_N1_Min_N2() {
    type A = NInt<UInt<UTerm, B1>>;
    type B = NInt<UInt<UInt<UTerm, B1>, B0>>;
    type N2 = NInt<UInt<UInt<UTerm, B1>, B0>>;

    #[allow(non_camel_case_types)]
    type N1MinN2 = <<A as Min<B>>::Output as Same<N2>>::Output;

    assert_eq!(<N1MinN2 as Integer>::to_i64(), <N2 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_N1_Max_N2() {
    type A = NInt<UInt<UTerm, B1>>;
    type B = NInt<UInt<UInt<UTerm, B1>, B0>>;
    type N1 = NInt<UInt<UTerm, B1>>;

    #[allow(non_camel_case_types)]
    type N1MaxN2 = <<A as Max<B>>::Output as Same<N1>>::Output;

    assert_eq!(<N1MaxN2 as Integer>::to_i64(), <N1 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_N1_Gcd_N2() {
    type A = NInt<UInt<UTerm, B1>>;
    type B = NInt<UInt<UInt<UTerm, B1>, B0>>;
    type P1 = PInt<UInt<UTerm, B1>>;

    #[allow(non_camel_case_types)]
    type N1GcdN2 = <<A as Gcd<B>>::Output as Same<P1>>::Output;

    assert_eq!(<N1GcdN2 as Integer>::to_i64(), <P1 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_N1_Div_N2() {
    type A = NInt<UInt<UTerm, B1>>;
    type B = NInt<UInt<UInt<UTerm, B1>, B0>>;
    type _0 = Z0;

    #[allow(non_camel_case_types)]
    type N1DivN2 = <<A as Div<B>>::Output as Same<_0>>::Output;

    assert_eq!(<N1DivN2 as Integer>::to_i64(), <_0 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_N1_Rem_N2() {
    type A = NInt<UInt<UTerm, B1>>;
    type B = NInt<UInt<UInt<UTerm, B1>, B0>>;
    type N1 = NInt<UInt<UTerm, B1>>;

    #[allow(non_camel_case_types)]
    type N1RemN2 = <<A as Rem<B>>::Output as Same<N1>>::Output;

    assert_eq!(<N1RemN2 as Integer>::to_i64(), <N1 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_N1_Pow_N2() {
    type A = NInt<UInt<UTerm, B1>>;
    type B = NInt<UInt<UInt<UTerm, B1>, B0>>;
    type P1 = PInt<UInt<UTerm, B1>>;

    #[allow(non_camel_case_types)]
    type N1PowN2 = <<A as Pow<B>>::Output as Same<P1>>::Output;

    assert_eq!(<N1PowN2 as Integer>::to_i64(), <P1 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_N1_Cmp_N2() {
    type A = NInt<UInt<UTerm, B1>>;
    type B = NInt<UInt<UInt<UTerm, B1>, B0>>;

    #[allow(non_camel_case_types)]
    type N1CmpN2 = <A as Cmp<B>>::Output;
    assert_eq!(<N1CmpN2 as Ord>::to_ordering(), Ordering::Greater);
}
#[test]
#[allow(non_snake_case)]
fn test_N1_Add_N1() {
    type A = NInt<UInt<UTerm, B1>>;
    type B = NInt<UInt<UTerm, B1>>;
    type N2 = NInt<UInt<UInt<UTerm, B1>, B0>>;

    #[allow(non_camel_case_types)]
    type N1AddN1 = <<A as Add<B>>::Output as Same<N2>>::Output;

    assert_eq!(<N1AddN1 as Integer>::to_i64(), <N2 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_N1_Sub_N1() {
    type A = NInt<UInt<UTerm, B1>>;
    type B = NInt<UInt<UTerm, B1>>;
    type _0 = Z0;

    #[allow(non_camel_case_types)]
    type N1SubN1 = <<A as Sub<B>>::Output as Same<_0>>::Output;

    assert_eq!(<N1SubN1 as Integer>::to_i64(), <_0 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_N1_Mul_N1() {
    type A = NInt<UInt<UTerm, B1>>;
    type B = NInt<UInt<UTerm, B1>>;
    type P1 = PInt<UInt<UTerm, B1>>;

    #[allow(non_camel_case_types)]
    type N1MulN1 = <<A as Mul<B>>::Output as Same<P1>>::Output;

    assert_eq!(<N1MulN1 as Integer>::to_i64(), <P1 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_N1_Min_N1() {
    type A = NInt<UInt<UTerm, B1>>;
    type B = NInt<UInt<UTerm, B1>>;
    type N1 = NInt<UInt<UTerm, B1>>;

    #[allow(non_camel_case_types)]
    type N1MinN1 = <<A as Min<B>>::Output as Same<N1>>::Output;

    assert_eq!(<N1MinN1 as Integer>::to_i64(), <N1 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_N1_Max_N1() {
    type A = NInt<UInt<UTerm, B1>>;
    type B = NInt<UInt<UTerm, B1>>;
    type N1 = NInt<UInt<UTerm, B1>>;

    #[allow(non_camel_case_types)]
    type N1MaxN1 = <<A as Max<B>>::Output as Same<N1>>::Output;

    assert_eq!(<N1MaxN1 as Integer>::to_i64(), <N1 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_N1_Gcd_N1() {
    type A = NInt<UInt<UTerm, B1>>;
    type B = NInt<UInt<UTerm, B1>>;
    type P1 = PInt<UInt<UTerm, B1>>;

    #[allow(non_camel_case_types)]
    type N1GcdN1 = <<A as Gcd<B>>::Output as Same<P1>>::Output;

    assert_eq!(<N1GcdN1 as Integer>::to_i64(), <P1 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_N1_Div_N1() {
    type A = NInt<UInt<UTerm, B1>>;
    type B = NInt<UInt<UTerm, B1>>;
    type P1 = PInt<UInt<UTerm, B1>>;

    #[allow(non_camel_case_types)]
    type N1DivN1 = <<A as Div<B>>::Output as Same<P1>>::Output;

    assert_eq!(<N1DivN1 as Integer>::to_i64(), <P1 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_N1_Rem_N1() {
    type A = NInt<UInt<UTerm, B1>>;
    type B = NInt<UInt<UTerm, B1>>;
    type _0 = Z0;

    #[allow(non_camel_case_types)]
    type N1RemN1 = <<A as Rem<B>>::Output as Same<_0>>::Output;

    assert_eq!(<N1RemN1 as Integer>::to_i64(), <_0 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_N1_PartialDiv_N1() {
    type A = NInt<UInt<UTerm, B1>>;
    type B = NInt<UInt<UTerm, B1>>;
    type P1 = PInt<UInt<UTerm, B1>>;

    #[allow(non_camel_case_types)]
    type N1PartialDivN1 = <<A as PartialDiv<B>>::Output as Same<P1>>::Output;

    assert_eq!(<N1PartialDivN1 as Integer>::to_i64(), <P1 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_N1_Pow_N1() {
    type A = NInt<UInt<UTerm, B1>>;
    type B = NInt<UInt<UTerm, B1>>;
    type N1 = NInt<UInt<UTerm, B1>>;

    #[allow(non_camel_case_types)]
    type N1PowN1 = <<A as Pow<B>>::Output as Same<N1>>::Output;

    assert_eq!(<N1PowN1 as Integer>::to_i64(), <N1 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_N1_Cmp_N1() {
    type A = NInt<UInt<UTerm, B1>>;
    type B = NInt<UInt<UTerm, B1>>;

    #[allow(non_camel_case_types)]
    type N1CmpN1 = <A as Cmp<B>>::Output;
    assert_eq!(<N1CmpN1 as Ord>::to_ordering(), Ordering::Equal);
}
#[test]
#[allow(non_snake_case)]
fn test_N1_Add__0() {
    type A = NInt<UInt<UTerm, B1>>;
    type B = Z0;
    type N1 = NInt<UInt<UTerm, B1>>;

    #[allow(non_camel_case_types)]
    type N1Add_0 = <<A as Add<B>>::Output as Same<N1>>::Output;

    assert_eq!(<N1Add_0 as Integer>::to_i64(), <N1 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_N1_Sub__0() {
    type A = NInt<UInt<UTerm, B1>>;
    type B = Z0;
    type N1 = NInt<UInt<UTerm, B1>>;

    #[allow(non_camel_case_types)]
    type N1Sub_0 = <<A as Sub<B>>::Output as Same<N1>>::Output;

    assert_eq!(<N1Sub_0 as Integer>::to_i64(), <N1 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_N1_Mul__0() {
    type A = NInt<UInt<UTerm, B1>>;
    type B = Z0;
    type _0 = Z0;

    #[allow(non_camel_case_types)]
    type N1Mul_0 = <<A as Mul<B>>::Output as Same<_0>>::Output;

    assert_eq!(<N1Mul_0 as Integer>::to_i64(), <_0 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_N1_Min__0() {
    type A = NInt<UInt<UTerm, B1>>;
    type B = Z0;
    type N1 = NInt<UInt<UTerm, B1>>;

    #[allow(non_camel_case_types)]
    type N1Min_0 = <<A as Min<B>>::Output as Same<N1>>::Output;

    assert_eq!(<N1Min_0 as Integer>::to_i64(), <N1 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_N1_Max__0() {
    type A = NInt<UInt<UTerm, B1>>;
    type B = Z0;
    type _0 = Z0;

    #[allow(non_camel_case_types)]
    type N1Max_0 = <<A as Max<B>>::Output as Same<_0>>::Output;

    assert_eq!(<N1Max_0 as Integer>::to_i64(), <_0 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_N1_Gcd__0() {
    type A = NInt<UInt<UTerm, B1>>;
    type B = Z0;
    type P1 = PInt<UInt<UTerm, B1>>;

    #[allow(non_camel_case_types)]
    type N1Gcd_0 = <<A as Gcd<B>>::Output as Same<P1>>::Output;

    assert_eq!(<N1Gcd_0 as Integer>::to_i64(), <P1 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_N1_Pow__0() {
    type A = NInt<UInt<UTerm, B1>>;
    type B = Z0;
    type P1 = PInt<UInt<UTerm, B1>>;

    #[allow(non_camel_case_types)]
    type N1Pow_0 = <<A as Pow<B>>::Output as Same<P1>>::Output;

    assert_eq!(<N1Pow_0 as Integer>::to_i64(), <P1 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_N1_Cmp__0() {
    type A = NInt<UInt<UTerm, B1>>;
    type B = Z0;

    #[allow(non_camel_case_types)]
    type N1Cmp_0 = <A as Cmp<B>>::Output;
    assert_eq!(<N1Cmp_0 as Ord>::to_ordering(), Ordering::Less);
}
#[test]
#[allow(non_snake_case)]
fn test_N1_Add_P1() {
    type A = NInt<UInt<UTerm, B1>>;
    type B = PInt<UInt<UTerm, B1>>;
    type _0 = Z0;

    #[allow(non_camel_case_types)]
    type N1AddP1 = <<A as Add<B>>::Output as Same<_0>>::Output;

    assert_eq!(<N1AddP1 as Integer>::to_i64(), <_0 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_N1_Sub_P1() {
    type A = NInt<UInt<UTerm, B1>>;
    type B = PInt<UInt<UTerm, B1>>;
    type N2 = NInt<UInt<UInt<UTerm, B1>, B0>>;

    #[allow(non_camel_case_types)]
    type N1SubP1 = <<A as Sub<B>>::Output as Same<N2>>::Output;

    assert_eq!(<N1SubP1 as Integer>::to_i64(), <N2 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_N1_Mul_P1() {
    type A = NInt<UInt<UTerm, B1>>;
    type B = PInt<UInt<UTerm, B1>>;
    type N1 = NInt<UInt<UTerm, B1>>;

    #[allow(non_camel_case_types)]
    type N1MulP1 = <<A as Mul<B>>::Output as Same<N1>>::Output;

    assert_eq!(<N1MulP1 as Integer>::to_i64(), <N1 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_N1_Min_P1() {
    type A = NInt<UInt<UTerm, B1>>;
    type B = PInt<UInt<UTerm, B1>>;
    type N1 = NInt<UInt<UTerm, B1>>;

    #[allow(non_camel_case_types)]
    type N1MinP1 = <<A as Min<B>>::Output as Same<N1>>::Output;

    assert_eq!(<N1MinP1 as Integer>::to_i64(), <N1 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_N1_Max_P1() {
    type A = NInt<UInt<UTerm, B1>>;
    type B = PInt<UInt<UTerm, B1>>;
    type P1 = PInt<UInt<UTerm, B1>>;

    #[allow(non_camel_case_types)]
    type N1MaxP1 = <<A as Max<B>>::Output as Same<P1>>::Output;

    assert_eq!(<N1MaxP1 as Integer>::to_i64(), <P1 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_N1_Gcd_P1() {
    type A = NInt<UInt<UTerm, B1>>;
    type B = PInt<UInt<UTerm, B1>>;
    type P1 = PInt<UInt<UTerm, B1>>;

    #[allow(non_camel_case_types)]
    type N1GcdP1 = <<A as Gcd<B>>::Output as Same<P1>>::Output;

    assert_eq!(<N1GcdP1 as Integer>::to_i64(), <P1 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_N1_Div_P1() {
    type A = NInt<UInt<UTerm, B1>>;
    type B = PInt<UInt<UTerm, B1>>;
    type N1 = NInt<UInt<UTerm, B1>>;

    #[allow(non_camel_case_types)]
    type N1DivP1 = <<A as Div<B>>::Output as Same<N1>>::Output;

    assert_eq!(<N1DivP1 as Integer>::to_i64(), <N1 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_N1_Rem_P1() {
    type A = NInt<UInt<UTerm, B1>>;
    type B = PInt<UInt<UTerm, B1>>;
    type _0 = Z0;

    #[allow(non_camel_case_types)]
    type N1RemP1 = <<A as Rem<B>>::Output as Same<_0>>::Output;

    assert_eq!(<N1RemP1 as Integer>::to_i64(), <_0 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_N1_PartialDiv_P1() {
    type A = NInt<UInt<UTerm, B1>>;
    type B = PInt<UInt<UTerm, B1>>;
    type N1 = NInt<UInt<UTerm, B1>>;

    #[allow(non_camel_case_types)]
    type N1PartialDivP1 = <<A as PartialDiv<B>>::Output as Same<N1>>::Output;

    assert_eq!(<N1PartialDivP1 as Integer>::to_i64(), <N1 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_N1_Pow_P1() {
    type A = NInt<UInt<UTerm, B1>>;
    type B = PInt<UInt<UTerm, B1>>;
    type N1 = NInt<UInt<UTerm, B1>>;

    #[allow(non_camel_case_types)]
    type N1PowP1 = <<A as Pow<B>>::Output as Same<N1>>::Output;

    assert_eq!(<N1PowP1 as Integer>::to_i64(), <N1 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_N1_Cmp_P1() {
    type A = NInt<UInt<UTerm, B1>>;
    type B = PInt<UInt<UTerm, B1>>;

    #[allow(non_camel_case_types)]
    type N1CmpP1 = <A as Cmp<B>>::Output;
    assert_eq!(<N1CmpP1 as Ord>::to_ordering(), Ordering::Less);
}
#[test]
#[allow(non_snake_case)]
fn test_N1_Add_P2() {
    type A = NInt<UInt<UTerm, B1>>;
    type B = PInt<UInt<UInt<UTerm, B1>, B0>>;
    type P1 = PInt<UInt<UTerm, B1>>;

    #[allow(non_camel_case_types)]
    type N1AddP2 = <<A as Add<B>>::Output as Same<P1>>::Output;

    assert_eq!(<N1AddP2 as Integer>::to_i64(), <P1 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_N1_Sub_P2() {
    type A = NInt<UInt<UTerm, B1>>;
    type B = PInt<UInt<UInt<UTerm, B1>, B0>>;
    type N3 = NInt<UInt<UInt<UTerm, B1>, B1>>;

    #[allow(non_camel_case_types)]
    type N1SubP2 = <<A as Sub<B>>::Output as Same<N3>>::Output;

    assert_eq!(<N1SubP2 as Integer>::to_i64(), <N3 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_N1_Mul_P2() {
    type A = NInt<UInt<UTerm, B1>>;
    type B = PInt<UInt<UInt<UTerm, B1>, B0>>;
    type N2 = NInt<UInt<UInt<UTerm, B1>, B0>>;

    #[allow(non_camel_case_types)]
    type N1MulP2 = <<A as Mul<B>>::Output as Same<N2>>::Output;

    assert_eq!(<N1MulP2 as Integer>::to_i64(), <N2 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_N1_Min_P2() {
    type A = NInt<UInt<UTerm, B1>>;
    type B = PInt<UInt<UInt<UTerm, B1>, B0>>;
    type N1 = NInt<UInt<UTerm, B1>>;

    #[allow(non_camel_case_types)]
    type N1MinP2 = <<A as Min<B>>::Output as Same<N1>>::Output;

    assert_eq!(<N1MinP2 as Integer>::to_i64(), <N1 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_N1_Max_P2() {
    type A = NInt<UInt<UTerm, B1>>;
    type B = PInt<UInt<UInt<UTerm, B1>, B0>>;
    type P2 = PInt<UInt<UInt<UTerm, B1>, B0>>;

    #[allow(non_camel_case_types)]
    type N1MaxP2 = <<A as Max<B>>::Output as Same<P2>>::Output;

    assert_eq!(<N1MaxP2 as Integer>::to_i64(), <P2 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_N1_Gcd_P2() {
    type A = NInt<UInt<UTerm, B1>>;
    type B = PInt<UInt<UInt<UTerm, B1>, B0>>;
    type P1 = PInt<UInt<UTerm, B1>>;

    #[allow(non_camel_case_types)]
    type N1GcdP2 = <<A as Gcd<B>>::Output as Same<P1>>::Output;

    assert_eq!(<N1GcdP2 as Integer>::to_i64(), <P1 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_N1_Div_P2() {
    type A = NInt<UInt<UTerm, B1>>;
    type B = PInt<UInt<UInt<UTerm, B1>, B0>>;
    type _0 = Z0;

    #[allow(non_camel_case_types)]
    type N1DivP2 = <<A as Div<B>>::Output as Same<_0>>::Output;

    assert_eq!(<N1DivP2 as Integer>::to_i64(), <_0 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_N1_Rem_P2() {
    type A = NInt<UInt<UTerm, B1>>;
    type B = PInt<UInt<UInt<UTerm, B1>, B0>>;
    type N1 = NInt<UInt<UTerm, B1>>;

    #[allow(non_camel_case_types)]
    type N1RemP2 = <<A as Rem<B>>::Output as Same<N1>>::Output;

    assert_eq!(<N1RemP2 as Integer>::to_i64(), <N1 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_N1_Pow_P2() {
    type A = NInt<UInt<UTerm, B1>>;
    type B = PInt<UInt<UInt<UTerm, B1>, B0>>;
    type P1 = PInt<UInt<UTerm, B1>>;

    #[allow(non_camel_case_types)]
    type N1PowP2 = <<A as Pow<B>>::Output as Same<P1>>::Output;

    assert_eq!(<N1PowP2 as Integer>::to_i64(), <P1 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_N1_Cmp_P2() {
    type A = NInt<UInt<UTerm, B1>>;
    type B = PInt<UInt<UInt<UTerm, B1>, B0>>;

    #[allow(non_camel_case_types)]
    type N1CmpP2 = <A as Cmp<B>>::Output;
    assert_eq!(<N1CmpP2 as Ord>::to_ordering(), Ordering::Less);
}
#[test]
#[allow(non_snake_case)]
fn test_N1_Add_P3() {
    type A = NInt<UInt<UTerm, B1>>;
    type B = PInt<UInt<UInt<UTerm, B1>, B1>>;
    type P2 = PInt<UInt<UInt<UTerm, B1>, B0>>;

    #[allow(non_camel_case_types)]
    type N1AddP3 = <<A as Add<B>>::Output as Same<P2>>::Output;

    assert_eq!(<N1AddP3 as Integer>::to_i64(), <P2 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_N1_Sub_P3() {
    type A = NInt<UInt<UTerm, B1>>;
    type B = PInt<UInt<UInt<UTerm, B1>, B1>>;
    type N4 = NInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>>;

    #[allow(non_camel_case_types)]
    type N1SubP3 = <<A as Sub<B>>::Output as Same<N4>>::Output;

    assert_eq!(<N1SubP3 as Integer>::to_i64(), <N4 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_N1_Mul_P3() {
    type A = NInt<UInt<UTerm, B1>>;
    type B = PInt<UInt<UInt<UTerm, B1>, B1>>;
    type N3 = NInt<UInt<UInt<UTerm, B1>, B1>>;

    #[allow(non_camel_case_types)]
    type N1MulP3 = <<A as Mul<B>>::Output as Same<N3>>::Output;

    assert_eq!(<N1MulP3 as Integer>::to_i64(), <N3 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_N1_Min_P3() {
    type A = NInt<UInt<UTerm, B1>>;
    type B = PInt<UInt<UInt<UTerm, B1>, B1>>;
    type N1 = NInt<UInt<UTerm, B1>>;

    #[allow(non_camel_case_types)]
    type N1MinP3 = <<A as Min<B>>::Output as Same<N1>>::Output;

    assert_eq!(<N1MinP3 as Integer>::to_i64(), <N1 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_N1_Max_P3() {
    type A = NInt<UInt<UTerm, B1>>;
    type B = PInt<UInt<UInt<UTerm, B1>, B1>>;
    type P3 = PInt<UInt<UInt<UTerm, B1>, B1>>;

    #[allow(non_camel_case_types)]
    type N1MaxP3 = <<A as Max<B>>::Output as Same<P3>>::Output;

    assert_eq!(<N1MaxP3 as Integer>::to_i64(), <P3 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_N1_Gcd_P3() {
    type A = NInt<UInt<UTerm, B1>>;
    type B = PInt<UInt<UInt<UTerm, B1>, B1>>;
    type P1 = PInt<UInt<UTerm, B1>>;

    #[allow(non_camel_case_types)]
    type N1GcdP3 = <<A as Gcd<B>>::Output as Same<P1>>::Output;

    assert_eq!(<N1GcdP3 as Integer>::to_i64(), <P1 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_N1_Div_P3() {
    type A = NInt<UInt<UTerm, B1>>;
    type B = PInt<UInt<UInt<UTerm, B1>, B1>>;
    type _0 = Z0;

    #[allow(non_camel_case_types)]
    type N1DivP3 = <<A as Div<B>>::Output as Same<_0>>::Output;

    assert_eq!(<N1DivP3 as Integer>::to_i64(), <_0 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_N1_Rem_P3() {
    type A = NInt<UInt<UTerm, B1>>;
    type B = PInt<UInt<UInt<UTerm, B1>, B1>>;
    type N1 = NInt<UInt<UTerm, B1>>;

    #[allow(non_camel_case_types)]
    type N1RemP3 = <<A as Rem<B>>::Output as Same<N1>>::Output;

    assert_eq!(<N1RemP3 as Integer>::to_i64(), <N1 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_N1_Pow_P3() {
    type A = NInt<UInt<UTerm, B1>>;
    type B = PInt<UInt<UInt<UTerm, B1>, B1>>;
    type N1 = NInt<UInt<UTerm, B1>>;

    #[allow(non_camel_case_types)]
    type N1PowP3 = <<A as Pow<B>>::Output as Same<N1>>::Output;

    assert_eq!(<N1PowP3 as Integer>::to_i64(), <N1 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_N1_Cmp_P3() {
    type A = NInt<UInt<UTerm, B1>>;
    type B = PInt<UInt<UInt<UTerm, B1>, B1>>;

    #[allow(non_camel_case_types)]
    type N1CmpP3 = <A as Cmp<B>>::Output;
    assert_eq!(<N1CmpP3 as Ord>::to_ordering(), Ordering::Less);
}
#[test]
#[allow(non_snake_case)]
fn test_N1_Add_P4() {
    type A = NInt<UInt<UTerm, B1>>;
    type B = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>>;
    type P3 = PInt<UInt<UInt<UTerm, B1>, B1>>;

    #[allow(non_camel_case_types)]
    type N1AddP4 = <<A as Add<B>>::Output as Same<P3>>::Output;

    assert_eq!(<N1AddP4 as Integer>::to_i64(), <P3 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_N1_Sub_P4() {
    type A = NInt<UInt<UTerm, B1>>;
    type B = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>>;
    type N5 = NInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>>;

    #[allow(non_camel_case_types)]
    type N1SubP4 = <<A as Sub<B>>::Output as Same<N5>>::Output;

    assert_eq!(<N1SubP4 as Integer>::to_i64(), <N5 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_N1_Mul_P4() {
    type A = NInt<UInt<UTerm, B1>>;
    type B = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>>;
    type N4 = NInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>>;

    #[allow(non_camel_case_types)]
    type N1MulP4 = <<A as Mul<B>>::Output as Same<N4>>::Output;

    assert_eq!(<N1MulP4 as Integer>::to_i64(), <N4 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_N1_Min_P4() {
    type A = NInt<UInt<UTerm, B1>>;
    type B = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>>;
    type N1 = NInt<UInt<UTerm, B1>>;

    #[allow(non_camel_case_types)]
    type N1MinP4 = <<A as Min<B>>::Output as Same<N1>>::Output;

    assert_eq!(<N1MinP4 as Integer>::to_i64(), <N1 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_N1_Max_P4() {
    type A = NInt<UInt<UTerm, B1>>;
    type B = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>>;
    type P4 = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>>;

    #[allow(non_camel_case_types)]
    type N1MaxP4 = <<A as Max<B>>::Output as Same<P4>>::Output;

    assert_eq!(<N1MaxP4 as Integer>::to_i64(), <P4 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_N1_Gcd_P4() {
    type A = NInt<UInt<UTerm, B1>>;
    type B = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>>;
    type P1 = PInt<UInt<UTerm, B1>>;

    #[allow(non_camel_case_types)]
    type N1GcdP4 = <<A as Gcd<B>>::Output as Same<P1>>::Output;

    assert_eq!(<N1GcdP4 as Integer>::to_i64(), <P1 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_N1_Div_P4() {
    type A = NInt<UInt<UTerm, B1>>;
    type B = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>>;
    type _0 = Z0;

    #[allow(non_camel_case_types)]
    type N1DivP4 = <<A as Div<B>>::Output as Same<_0>>::Output;

    assert_eq!(<N1DivP4 as Integer>::to_i64(), <_0 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_N1_Rem_P4() {
    type A = NInt<UInt<UTerm, B1>>;
    type B = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>>;
    type N1 = NInt<UInt<UTerm, B1>>;

    #[allow(non_camel_case_types)]
    type N1RemP4 = <<A as Rem<B>>::Output as Same<N1>>::Output;

    assert_eq!(<N1RemP4 as Integer>::to_i64(), <N1 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_N1_Pow_P4() {
    type A = NInt<UInt<UTerm, B1>>;
    type B = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>>;
    type P1 = PInt<UInt<UTerm, B1>>;

    #[allow(non_camel_case_types)]
    type N1PowP4 = <<A as Pow<B>>::Output as Same<P1>>::Output;

    assert_eq!(<N1PowP4 as Integer>::to_i64(), <P1 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_N1_Cmp_P4() {
    type A = NInt<UInt<UTerm, B1>>;
    type B = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>>;

    #[allow(non_camel_case_types)]
    type N1CmpP4 = <A as Cmp<B>>::Output;
    assert_eq!(<N1CmpP4 as Ord>::to_ordering(), Ordering::Less);
}
#[test]
#[allow(non_snake_case)]
fn test_N1_Add_P5() {
    type A = NInt<UInt<UTerm, B1>>;
    type B = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>>;
    type P4 = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>>;

    #[allow(non_camel_case_types)]
    type N1AddP5 = <<A as Add<B>>::Output as Same<P4>>::Output;

    assert_eq!(<N1AddP5 as Integer>::to_i64(), <P4 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_N1_Sub_P5() {
    type A = NInt<UInt<UTerm, B1>>;
    type B = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>>;
    type N6 = NInt<UInt<UInt<UInt<UTerm, B1>, B1>, B0>>;

    #[allow(non_camel_case_types)]
    type N1SubP5 = <<A as Sub<B>>::Output as Same<N6>>::Output;

    assert_eq!(<N1SubP5 as Integer>::to_i64(), <N6 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_N1_Mul_P5() {
    type A = NInt<UInt<UTerm, B1>>;
    type B = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>>;
    type N5 = NInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>>;

    #[allow(non_camel_case_types)]
    type N1MulP5 = <<A as Mul<B>>::Output as Same<N5>>::Output;

    assert_eq!(<N1MulP5 as Integer>::to_i64(), <N5 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_N1_Min_P5() {
    type A = NInt<UInt<UTerm, B1>>;
    type B = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>>;
    type N1 = NInt<UInt<UTerm, B1>>;

    #[allow(non_camel_case_types)]
    type N1MinP5 = <<A as Min<B>>::Output as Same<N1>>::Output;

    assert_eq!(<N1MinP5 as Integer>::to_i64(), <N1 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_N1_Max_P5() {
    type A = NInt<UInt<UTerm, B1>>;
    type B = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>>;
    type P5 = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>>;

    #[allow(non_camel_case_types)]
    type N1MaxP5 = <<A as Max<B>>::Output as Same<P5>>::Output;

    assert_eq!(<N1MaxP5 as Integer>::to_i64(), <P5 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_N1_Gcd_P5() {
    type A = NInt<UInt<UTerm, B1>>;
    type B = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>>;
    type P1 = PInt<UInt<UTerm, B1>>;

    #[allow(non_camel_case_types)]
    type N1GcdP5 = <<A as Gcd<B>>::Output as Same<P1>>::Output;

    assert_eq!(<N1GcdP5 as Integer>::to_i64(), <P1 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_N1_Div_P5() {
    type A = NInt<UInt<UTerm, B1>>;
    type B = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>>;
    type _0 = Z0;

    #[allow(non_camel_case_types)]
    type N1DivP5 = <<A as Div<B>>::Output as Same<_0>>::Output;

    assert_eq!(<N1DivP5 as Integer>::to_i64(), <_0 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_N1_Rem_P5() {
    type A = NInt<UInt<UTerm, B1>>;
    type B = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>>;
    type N1 = NInt<UInt<UTerm, B1>>;

    #[allow(non_camel_case_types)]
    type N1RemP5 = <<A as Rem<B>>::Output as Same<N1>>::Output;

    assert_eq!(<N1RemP5 as Integer>::to_i64(), <N1 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_N1_Pow_P5() {
    type A = NInt<UInt<UTerm, B1>>;
    type B = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>>;
    type N1 = NInt<UInt<UTerm, B1>>;

    #[allow(non_camel_case_types)]
    type N1PowP5 = <<A as Pow<B>>::Output as Same<N1>>::Output;

    assert_eq!(<N1PowP5 as Integer>::to_i64(), <N1 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_N1_Cmp_P5() {
    type A = NInt<UInt<UTerm, B1>>;
    type B = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>>;

    #[allow(non_camel_case_types)]
    type N1CmpP5 = <A as Cmp<B>>::Output;
    assert_eq!(<N1CmpP5 as Ord>::to_ordering(), Ordering::Less);
}
#[test]
#[allow(non_snake_case)]
fn test__0_Add_N5() {
    type A = Z0;
    type B = NInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>>;
    type N5 = NInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>>;

    #[allow(non_camel_case_types)]
    type _0AddN5 = <<A as Add<B>>::Output as Same<N5>>::Output;

    assert_eq!(<_0AddN5 as Integer>::to_i64(), <N5 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test__0_Sub_N5() {
    type A = Z0;
    type B = NInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>>;
    type P5 = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>>;

    #[allow(non_camel_case_types)]
    type _0SubN5 = <<A as Sub<B>>::Output as Same<P5>>::Output;

    assert_eq!(<_0SubN5 as Integer>::to_i64(), <P5 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test__0_Mul_N5() {
    type A = Z0;
    type B = NInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>>;
    type _0 = Z0;

    #[allow(non_camel_case_types)]
    type _0MulN5 = <<A as Mul<B>>::Output as Same<_0>>::Output;

    assert_eq!(<_0MulN5 as Integer>::to_i64(), <_0 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test__0_Min_N5() {
    type A = Z0;
    type B = NInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>>;
    type N5 = NInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>>;

    #[allow(non_camel_case_types)]
    type _0MinN5 = <<A as Min<B>>::Output as Same<N5>>::Output;

    assert_eq!(<_0MinN5 as Integer>::to_i64(), <N5 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test__0_Max_N5() {
    type A = Z0;
    type B = NInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>>;
    type _0 = Z0;

    #[allow(non_camel_case_types)]
    type _0MaxN5 = <<A as Max<B>>::Output as Same<_0>>::Output;

    assert_eq!(<_0MaxN5 as Integer>::to_i64(), <_0 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test__0_Gcd_N5() {
    type A = Z0;
    type B = NInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>>;
    type P5 = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>>;

    #[allow(non_camel_case_types)]
    type _0GcdN5 = <<A as Gcd<B>>::Output as Same<P5>>::Output;

    assert_eq!(<_0GcdN5 as Integer>::to_i64(), <P5 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test__0_Div_N5() {
    type A = Z0;
    type B = NInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>>;
    type _0 = Z0;

    #[allow(non_camel_case_types)]
    type _0DivN5 = <<A as Div<B>>::Output as Same<_0>>::Output;

    assert_eq!(<_0DivN5 as Integer>::to_i64(), <_0 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test__0_Rem_N5() {
    type A = Z0;
    type B = NInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>>;
    type _0 = Z0;

    #[allow(non_camel_case_types)]
    type _0RemN5 = <<A as Rem<B>>::Output as Same<_0>>::Output;

    assert_eq!(<_0RemN5 as Integer>::to_i64(), <_0 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test__0_PartialDiv_N5() {
    type A = Z0;
    type B = NInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>>;
    type _0 = Z0;

    #[allow(non_camel_case_types)]
    type _0PartialDivN5 = <<A as PartialDiv<B>>::Output as Same<_0>>::Output;

    assert_eq!(<_0PartialDivN5 as Integer>::to_i64(), <_0 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test__0_Cmp_N5() {
    type A = Z0;
    type B = NInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>>;

    #[allow(non_camel_case_types)]
    type _0CmpN5 = <A as Cmp<B>>::Output;
    assert_eq!(<_0CmpN5 as Ord>::to_ordering(), Ordering::Greater);
}
#[test]
#[allow(non_snake_case)]
fn test__0_Add_N4() {
    type A = Z0;
    type B = NInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>>;
    type N4 = NInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>>;

    #[allow(non_camel_case_types)]
    type _0AddN4 = <<A as Add<B>>::Output as Same<N4>>::Output;

    assert_eq!(<_0AddN4 as Integer>::to_i64(), <N4 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test__0_Sub_N4() {
    type A = Z0;
    type B = NInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>>;
    type P4 = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>>;

    #[allow(non_camel_case_types)]
    type _0SubN4 = <<A as Sub<B>>::Output as Same<P4>>::Output;

    assert_eq!(<_0SubN4 as Integer>::to_i64(), <P4 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test__0_Mul_N4() {
    type A = Z0;
    type B = NInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>>;
    type _0 = Z0;

    #[allow(non_camel_case_types)]
    type _0MulN4 = <<A as Mul<B>>::Output as Same<_0>>::Output;

    assert_eq!(<_0MulN4 as Integer>::to_i64(), <_0 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test__0_Min_N4() {
    type A = Z0;
    type B = NInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>>;
    type N4 = NInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>>;

    #[allow(non_camel_case_types)]
    type _0MinN4 = <<A as Min<B>>::Output as Same<N4>>::Output;

    assert_eq!(<_0MinN4 as Integer>::to_i64(), <N4 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test__0_Max_N4() {
    type A = Z0;
    type B = NInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>>;
    type _0 = Z0;

    #[allow(non_camel_case_types)]
    type _0MaxN4 = <<A as Max<B>>::Output as Same<_0>>::Output;

    assert_eq!(<_0MaxN4 as Integer>::to_i64(), <_0 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test__0_Gcd_N4() {
    type A = Z0;
    type B = NInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>>;
    type P4 = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>>;

    #[allow(non_camel_case_types)]
    type _0GcdN4 = <<A as Gcd<B>>::Output as Same<P4>>::Output;

    assert_eq!(<_0GcdN4 as Integer>::to_i64(), <P4 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test__0_Div_N4() {
    type A = Z0;
    type B = NInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>>;
    type _0 = Z0;

    #[allow(non_camel_case_types)]
    type _0DivN4 = <<A as Div<B>>::Output as Same<_0>>::Output;

    assert_eq!(<_0DivN4 as Integer>::to_i64(), <_0 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test__0_Rem_N4() {
    type A = Z0;
    type B = NInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>>;
    type _0 = Z0;

    #[allow(non_camel_case_types)]
    type _0RemN4 = <<A as Rem<B>>::Output as Same<_0>>::Output;

    assert_eq!(<_0RemN4 as Integer>::to_i64(), <_0 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test__0_PartialDiv_N4() {
    type A = Z0;
    type B = NInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>>;
    type _0 = Z0;

    #[allow(non_camel_case_types)]
    type _0PartialDivN4 = <<A as PartialDiv<B>>::Output as Same<_0>>::Output;

    assert_eq!(<_0PartialDivN4 as Integer>::to_i64(), <_0 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test__0_Cmp_N4() {
    type A = Z0;
    type B = NInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>>;

    #[allow(non_camel_case_types)]
    type _0CmpN4 = <A as Cmp<B>>::Output;
    assert_eq!(<_0CmpN4 as Ord>::to_ordering(), Ordering::Greater);
}
#[test]
#[allow(non_snake_case)]
fn test__0_Add_N3() {
    type A = Z0;
    type B = NInt<UInt<UInt<UTerm, B1>, B1>>;
    type N3 = NInt<UInt<UInt<UTerm, B1>, B1>>;

    #[allow(non_camel_case_types)]
    type _0AddN3 = <<A as Add<B>>::Output as Same<N3>>::Output;

    assert_eq!(<_0AddN3 as Integer>::to_i64(), <N3 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test__0_Sub_N3() {
    type A = Z0;
    type B = NInt<UInt<UInt<UTerm, B1>, B1>>;
    type P3 = PInt<UInt<UInt<UTerm, B1>, B1>>;

    #[allow(non_camel_case_types)]
    type _0SubN3 = <<A as Sub<B>>::Output as Same<P3>>::Output;

    assert_eq!(<_0SubN3 as Integer>::to_i64(), <P3 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test__0_Mul_N3() {
    type A = Z0;
    type B = NInt<UInt<UInt<UTerm, B1>, B1>>;
    type _0 = Z0;

    #[allow(non_camel_case_types)]
    type _0MulN3 = <<A as Mul<B>>::Output as Same<_0>>::Output;

    assert_eq!(<_0MulN3 as Integer>::to_i64(), <_0 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test__0_Min_N3() {
    type A = Z0;
    type B = NInt<UInt<UInt<UTerm, B1>, B1>>;
    type N3 = NInt<UInt<UInt<UTerm, B1>, B1>>;

    #[allow(non_camel_case_types)]
    type _0MinN3 = <<A as Min<B>>::Output as Same<N3>>::Output;

    assert_eq!(<_0MinN3 as Integer>::to_i64(), <N3 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test__0_Max_N3() {
    type A = Z0;
    type B = NInt<UInt<UInt<UTerm, B1>, B1>>;
    type _0 = Z0;

    #[allow(non_camel_case_types)]
    type _0MaxN3 = <<A as Max<B>>::Output as Same<_0>>::Output;

    assert_eq!(<_0MaxN3 as Integer>::to_i64(), <_0 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test__0_Gcd_N3() {
    type A = Z0;
    type B = NInt<UInt<UInt<UTerm, B1>, B1>>;
    type P3 = PInt<UInt<UInt<UTerm, B1>, B1>>;

    #[allow(non_camel_case_types)]
    type _0GcdN3 = <<A as Gcd<B>>::Output as Same<P3>>::Output;

    assert_eq!(<_0GcdN3 as Integer>::to_i64(), <P3 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test__0_Div_N3() {
    type A = Z0;
    type B = NInt<UInt<UInt<UTerm, B1>, B1>>;
    type _0 = Z0;

    #[allow(non_camel_case_types)]
    type _0DivN3 = <<A as Div<B>>::Output as Same<_0>>::Output;

    assert_eq!(<_0DivN3 as Integer>::to_i64(), <_0 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test__0_Rem_N3() {
    type A = Z0;
    type B = NInt<UInt<UInt<UTerm, B1>, B1>>;
    type _0 = Z0;

    #[allow(non_camel_case_types)]
    type _0RemN3 = <<A as Rem<B>>::Output as Same<_0>>::Output;

    assert_eq!(<_0RemN3 as Integer>::to_i64(), <_0 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test__0_PartialDiv_N3() {
    type A = Z0;
    type B = NInt<UInt<UInt<UTerm, B1>, B1>>;
    type _0 = Z0;

    #[allow(non_camel_case_types)]
    type _0PartialDivN3 = <<A as PartialDiv<B>>::Output as Same<_0>>::Output;

    assert_eq!(<_0PartialDivN3 as Integer>::to_i64(), <_0 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test__0_Cmp_N3() {
    type A = Z0;
    type B = NInt<UInt<UInt<UTerm, B1>, B1>>;

    #[allow(non_camel_case_types)]
    type _0CmpN3 = <A as Cmp<B>>::Output;
    assert_eq!(<_0CmpN3 as Ord>::to_ordering(), Ordering::Greater);
}
#[test]
#[allow(non_snake_case)]
fn test__0_Add_N2() {
    type A = Z0;
    type B = NInt<UInt<UInt<UTerm, B1>, B0>>;
    type N2 = NInt<UInt<UInt<UTerm, B1>, B0>>;

    #[allow(non_camel_case_types)]
    type _0AddN2 = <<A as Add<B>>::Output as Same<N2>>::Output;

    assert_eq!(<_0AddN2 as Integer>::to_i64(), <N2 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test__0_Sub_N2() {
    type A = Z0;
    type B = NInt<UInt<UInt<UTerm, B1>, B0>>;
    type P2 = PInt<UInt<UInt<UTerm, B1>, B0>>;

    #[allow(non_camel_case_types)]
    type _0SubN2 = <<A as Sub<B>>::Output as Same<P2>>::Output;

    assert_eq!(<_0SubN2 as Integer>::to_i64(), <P2 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test__0_Mul_N2() {
    type A = Z0;
    type B = NInt<UInt<UInt<UTerm, B1>, B0>>;
    type _0 = Z0;

    #[allow(non_camel_case_types)]
    type _0MulN2 = <<A as Mul<B>>::Output as Same<_0>>::Output;

    assert_eq!(<_0MulN2 as Integer>::to_i64(), <_0 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test__0_Min_N2() {
    type A = Z0;
    type B = NInt<UInt<UInt<UTerm, B1>, B0>>;
    type N2 = NInt<UInt<UInt<UTerm, B1>, B0>>;

    #[allow(non_camel_case_types)]
    type _0MinN2 = <<A as Min<B>>::Output as Same<N2>>::Output;

    assert_eq!(<_0MinN2 as Integer>::to_i64(), <N2 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test__0_Max_N2() {
    type A = Z0;
    type B = NInt<UInt<UInt<UTerm, B1>, B0>>;
    type _0 = Z0;

    #[allow(non_camel_case_types)]
    type _0MaxN2 = <<A as Max<B>>::Output as Same<_0>>::Output;

    assert_eq!(<_0MaxN2 as Integer>::to_i64(), <_0 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test__0_Gcd_N2() {
    type A = Z0;
    type B = NInt<UInt<UInt<UTerm, B1>, B0>>;
    type P2 = PInt<UInt<UInt<UTerm, B1>, B0>>;

    #[allow(non_camel_case_types)]
    type _0GcdN2 = <<A as Gcd<B>>::Output as Same<P2>>::Output;

    assert_eq!(<_0GcdN2 as Integer>::to_i64(), <P2 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test__0_Div_N2() {
    type A = Z0;
    type B = NInt<UInt<UInt<UTerm, B1>, B0>>;
    type _0 = Z0;

    #[allow(non_camel_case_types)]
    type _0DivN2 = <<A as Div<B>>::Output as Same<_0>>::Output;

    assert_eq!(<_0DivN2 as Integer>::to_i64(), <_0 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test__0_Rem_N2() {
    type A = Z0;
    type B = NInt<UInt<UInt<UTerm, B1>, B0>>;
    type _0 = Z0;

    #[allow(non_camel_case_types)]
    type _0RemN2 = <<A as Rem<B>>::Output as Same<_0>>::Output;

    assert_eq!(<_0RemN2 as Integer>::to_i64(), <_0 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test__0_PartialDiv_N2() {
    type A = Z0;
    type B = NInt<UInt<UInt<UTerm, B1>, B0>>;
    type _0 = Z0;

    #[allow(non_camel_case_types)]
    type _0PartialDivN2 = <<A as PartialDiv<B>>::Output as Same<_0>>::Output;

    assert_eq!(<_0PartialDivN2 as Integer>::to_i64(), <_0 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test__0_Cmp_N2() {
    type A = Z0;
    type B = NInt<UInt<UInt<UTerm, B1>, B0>>;

    #[allow(non_camel_case_types)]
    type _0CmpN2 = <A as Cmp<B>>::Output;
    assert_eq!(<_0CmpN2 as Ord>::to_ordering(), Ordering::Greater);
}
#[test]
#[allow(non_snake_case)]
fn test__0_Add_N1() {
    type A = Z0;
    type B = NInt<UInt<UTerm, B1>>;
    type N1 = NInt<UInt<UTerm, B1>>;

    #[allow(non_camel_case_types)]
    type _0AddN1 = <<A as Add<B>>::Output as Same<N1>>::Output;

    assert_eq!(<_0AddN1 as Integer>::to_i64(), <N1 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test__0_Sub_N1() {
    type A = Z0;
    type B = NInt<UInt<UTerm, B1>>;
    type P1 = PInt<UInt<UTerm, B1>>;

    #[allow(non_camel_case_types)]
    type _0SubN1 = <<A as Sub<B>>::Output as Same<P1>>::Output;

    assert_eq!(<_0SubN1 as Integer>::to_i64(), <P1 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test__0_Mul_N1() {
    type A = Z0;
    type B = NInt<UInt<UTerm, B1>>;
    type _0 = Z0;

    #[allow(non_camel_case_types)]
    type _0MulN1 = <<A as Mul<B>>::Output as Same<_0>>::Output;

    assert_eq!(<_0MulN1 as Integer>::to_i64(), <_0 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test__0_Min_N1() {
    type A = Z0;
    type B = NInt<UInt<UTerm, B1>>;
    type N1 = NInt<UInt<UTerm, B1>>;

    #[allow(non_camel_case_types)]
    type _0MinN1 = <<A as Min<B>>::Output as Same<N1>>::Output;

    assert_eq!(<_0MinN1 as Integer>::to_i64(), <N1 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test__0_Max_N1() {
    type A = Z0;
    type B = NInt<UInt<UTerm, B1>>;
    type _0 = Z0;

    #[allow(non_camel_case_types)]
    type _0MaxN1 = <<A as Max<B>>::Output as Same<_0>>::Output;

    assert_eq!(<_0MaxN1 as Integer>::to_i64(), <_0 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test__0_Gcd_N1() {
    type A = Z0;
    type B = NInt<UInt<UTerm, B1>>;
    type P1 = PInt<UInt<UTerm, B1>>;

    #[allow(non_camel_case_types)]
    type _0GcdN1 = <<A as Gcd<B>>::Output as Same<P1>>::Output;

    assert_eq!(<_0GcdN1 as Integer>::to_i64(), <P1 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test__0_Div_N1() {
    type A = Z0;
    type B = NInt<UInt<UTerm, B1>>;
    type _0 = Z0;

    #[allow(non_camel_case_types)]
    type _0DivN1 = <<A as Div<B>>::Output as Same<_0>>::Output;

    assert_eq!(<_0DivN1 as Integer>::to_i64(), <_0 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test__0_Rem_N1() {
    type A = Z0;
    type B = NInt<UInt<UTerm, B1>>;
    type _0 = Z0;

    #[allow(non_camel_case_types)]
    type _0RemN1 = <<A as Rem<B>>::Output as Same<_0>>::Output;

    assert_eq!(<_0RemN1 as Integer>::to_i64(), <_0 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test__0_PartialDiv_N1() {
    type A = Z0;
    type B = NInt<UInt<UTerm, B1>>;
    type _0 = Z0;

    #[allow(non_camel_case_types)]
    type _0PartialDivN1 = <<A as PartialDiv<B>>::Output as Same<_0>>::Output;

    assert_eq!(<_0PartialDivN1 as Integer>::to_i64(), <_0 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test__0_Cmp_N1() {
    type A = Z0;
    type B = NInt<UInt<UTerm, B1>>;

    #[allow(non_camel_case_types)]
    type _0CmpN1 = <A as Cmp<B>>::Output;
    assert_eq!(<_0CmpN1 as Ord>::to_ordering(), Ordering::Greater);
}
#[test]
#[allow(non_snake_case)]
fn test__0_Add__0() {
    type A = Z0;
    type B = Z0;
    type _0 = Z0;

    #[allow(non_camel_case_types)]
    type _0Add_0 = <<A as Add<B>>::Output as Same<_0>>::Output;

    assert_eq!(<_0Add_0 as Integer>::to_i64(), <_0 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test__0_Sub__0() {
    type A = Z0;
    type B = Z0;
    type _0 = Z0;

    #[allow(non_camel_case_types)]
    type _0Sub_0 = <<A as Sub<B>>::Output as Same<_0>>::Output;

    assert_eq!(<_0Sub_0 as Integer>::to_i64(), <_0 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test__0_Mul__0() {
    type A = Z0;
    type B = Z0;
    type _0 = Z0;

    #[allow(non_camel_case_types)]
    type _0Mul_0 = <<A as Mul<B>>::Output as Same<_0>>::Output;

    assert_eq!(<_0Mul_0 as Integer>::to_i64(), <_0 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test__0_Min__0() {
    type A = Z0;
    type B = Z0;
    type _0 = Z0;

    #[allow(non_camel_case_types)]
    type _0Min_0 = <<A as Min<B>>::Output as Same<_0>>::Output;

    assert_eq!(<_0Min_0 as Integer>::to_i64(), <_0 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test__0_Max__0() {
    type A = Z0;
    type B = Z0;
    type _0 = Z0;

    #[allow(non_camel_case_types)]
    type _0Max_0 = <<A as Max<B>>::Output as Same<_0>>::Output;

    assert_eq!(<_0Max_0 as Integer>::to_i64(), <_0 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test__0_Gcd__0() {
    type A = Z0;
    type B = Z0;
    type _0 = Z0;

    #[allow(non_camel_case_types)]
    type _0Gcd_0 = <<A as Gcd<B>>::Output as Same<_0>>::Output;

    assert_eq!(<_0Gcd_0 as Integer>::to_i64(), <_0 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test__0_Pow__0() {
    type A = Z0;
    type B = Z0;
    type P1 = PInt<UInt<UTerm, B1>>;

    #[allow(non_camel_case_types)]
    type _0Pow_0 = <<A as Pow<B>>::Output as Same<P1>>::Output;

    assert_eq!(<_0Pow_0 as Integer>::to_i64(), <P1 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test__0_Cmp__0() {
    type A = Z0;
    type B = Z0;

    #[allow(non_camel_case_types)]
    type _0Cmp_0 = <A as Cmp<B>>::Output;
    assert_eq!(<_0Cmp_0 as Ord>::to_ordering(), Ordering::Equal);
}
#[test]
#[allow(non_snake_case)]
fn test__0_Add_P1() {
    type A = Z0;
    type B = PInt<UInt<UTerm, B1>>;
    type P1 = PInt<UInt<UTerm, B1>>;

    #[allow(non_camel_case_types)]
    type _0AddP1 = <<A as Add<B>>::Output as Same<P1>>::Output;

    assert_eq!(<_0AddP1 as Integer>::to_i64(), <P1 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test__0_Sub_P1() {
    type A = Z0;
    type B = PInt<UInt<UTerm, B1>>;
    type N1 = NInt<UInt<UTerm, B1>>;

    #[allow(non_camel_case_types)]
    type _0SubP1 = <<A as Sub<B>>::Output as Same<N1>>::Output;

    assert_eq!(<_0SubP1 as Integer>::to_i64(), <N1 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test__0_Mul_P1() {
    type A = Z0;
    type B = PInt<UInt<UTerm, B1>>;
    type _0 = Z0;

    #[allow(non_camel_case_types)]
    type _0MulP1 = <<A as Mul<B>>::Output as Same<_0>>::Output;

    assert_eq!(<_0MulP1 as Integer>::to_i64(), <_0 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test__0_Min_P1() {
    type A = Z0;
    type B = PInt<UInt<UTerm, B1>>;
    type _0 = Z0;

    #[allow(non_camel_case_types)]
    type _0MinP1 = <<A as Min<B>>::Output as Same<_0>>::Output;

    assert_eq!(<_0MinP1 as Integer>::to_i64(), <_0 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test__0_Max_P1() {
    type A = Z0;
    type B = PInt<UInt<UTerm, B1>>;
    type P1 = PInt<UInt<UTerm, B1>>;

    #[allow(non_camel_case_types)]
    type _0MaxP1 = <<A as Max<B>>::Output as Same<P1>>::Output;

    assert_eq!(<_0MaxP1 as Integer>::to_i64(), <P1 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test__0_Gcd_P1() {
    type A = Z0;
    type B = PInt<UInt<UTerm, B1>>;
    type P1 = PInt<UInt<UTerm, B1>>;

    #[allow(non_camel_case_types)]
    type _0GcdP1 = <<A as Gcd<B>>::Output as Same<P1>>::Output;

    assert_eq!(<_0GcdP1 as Integer>::to_i64(), <P1 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test__0_Div_P1() {
    type A = Z0;
    type B = PInt<UInt<UTerm, B1>>;
    type _0 = Z0;

    #[allow(non_camel_case_types)]
    type _0DivP1 = <<A as Div<B>>::Output as Same<_0>>::Output;

    assert_eq!(<_0DivP1 as Integer>::to_i64(), <_0 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test__0_Rem_P1() {
    type A = Z0;
    type B = PInt<UInt<UTerm, B1>>;
    type _0 = Z0;

    #[allow(non_camel_case_types)]
    type _0RemP1 = <<A as Rem<B>>::Output as Same<_0>>::Output;

    assert_eq!(<_0RemP1 as Integer>::to_i64(), <_0 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test__0_PartialDiv_P1() {
    type A = Z0;
    type B = PInt<UInt<UTerm, B1>>;
    type _0 = Z0;

    #[allow(non_camel_case_types)]
    type _0PartialDivP1 = <<A as PartialDiv<B>>::Output as Same<_0>>::Output;

    assert_eq!(<_0PartialDivP1 as Integer>::to_i64(), <_0 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test__0_Pow_P1() {
    type A = Z0;
    type B = PInt<UInt<UTerm, B1>>;
    type _0 = Z0;

    #[allow(non_camel_case_types)]
    type _0PowP1 = <<A as Pow<B>>::Output as Same<_0>>::Output;

    assert_eq!(<_0PowP1 as Integer>::to_i64(), <_0 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test__0_Cmp_P1() {
    type A = Z0;
    type B = PInt<UInt<UTerm, B1>>;

    #[allow(non_camel_case_types)]
    type _0CmpP1 = <A as Cmp<B>>::Output;
    assert_eq!(<_0CmpP1 as Ord>::to_ordering(), Ordering::Less);
}
#[test]
#[allow(non_snake_case)]
fn test__0_Add_P2() {
    type A = Z0;
    type B = PInt<UInt<UInt<UTerm, B1>, B0>>;
    type P2 = PInt<UInt<UInt<UTerm, B1>, B0>>;

    #[allow(non_camel_case_types)]
    type _0AddP2 = <<A as Add<B>>::Output as Same<P2>>::Output;

    assert_eq!(<_0AddP2 as Integer>::to_i64(), <P2 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test__0_Sub_P2() {
    type A = Z0;
    type B = PInt<UInt<UInt<UTerm, B1>, B0>>;
    type N2 = NInt<UInt<UInt<UTerm, B1>, B0>>;

    #[allow(non_camel_case_types)]
    type _0SubP2 = <<A as Sub<B>>::Output as Same<N2>>::Output;

    assert_eq!(<_0SubP2 as Integer>::to_i64(), <N2 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test__0_Mul_P2() {
    type A = Z0;
    type B = PInt<UInt<UInt<UTerm, B1>, B0>>;
    type _0 = Z0;

    #[allow(non_camel_case_types)]
    type _0MulP2 = <<A as Mul<B>>::Output as Same<_0>>::Output;

    assert_eq!(<_0MulP2 as Integer>::to_i64(), <_0 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test__0_Min_P2() {
    type A = Z0;
    type B = PInt<UInt<UInt<UTerm, B1>, B0>>;
    type _0 = Z0;

    #[allow(non_camel_case_types)]
    type _0MinP2 = <<A as Min<B>>::Output as Same<_0>>::Output;

    assert_eq!(<_0MinP2 as Integer>::to_i64(), <_0 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test__0_Max_P2() {
    type A = Z0;
    type B = PInt<UInt<UInt<UTerm, B1>, B0>>;
    type P2 = PInt<UInt<UInt<UTerm, B1>, B0>>;

    #[allow(non_camel_case_types)]
    type _0MaxP2 = <<A as Max<B>>::Output as Same<P2>>::Output;

    assert_eq!(<_0MaxP2 as Integer>::to_i64(), <P2 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test__0_Gcd_P2() {
    type A = Z0;
    type B = PInt<UInt<UInt<UTerm, B1>, B0>>;
    type P2 = PInt<UInt<UInt<UTerm, B1>, B0>>;

    #[allow(non_camel_case_types)]
    type _0GcdP2 = <<A as Gcd<B>>::Output as Same<P2>>::Output;

    assert_eq!(<_0GcdP2 as Integer>::to_i64(), <P2 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test__0_Div_P2() {
    type A = Z0;
    type B = PInt<UInt<UInt<UTerm, B1>, B0>>;
    type _0 = Z0;

    #[allow(non_camel_case_types)]
    type _0DivP2 = <<A as Div<B>>::Output as Same<_0>>::Output;

    assert_eq!(<_0DivP2 as Integer>::to_i64(), <_0 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test__0_Rem_P2() {
    type A = Z0;
    type B = PInt<UInt<UInt<UTerm, B1>, B0>>;
    type _0 = Z0;

    #[allow(non_camel_case_types)]
    type _0RemP2 = <<A as Rem<B>>::Output as Same<_0>>::Output;

    assert_eq!(<_0RemP2 as Integer>::to_i64(), <_0 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test__0_PartialDiv_P2() {
    type A = Z0;
    type B = PInt<UInt<UInt<UTerm, B1>, B0>>;
    type _0 = Z0;

    #[allow(non_camel_case_types)]
    type _0PartialDivP2 = <<A as PartialDiv<B>>::Output as Same<_0>>::Output;

    assert_eq!(<_0PartialDivP2 as Integer>::to_i64(), <_0 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test__0_Pow_P2() {
    type A = Z0;
    type B = PInt<UInt<UInt<UTerm, B1>, B0>>;
    type _0 = Z0;

    #[allow(non_camel_case_types)]
    type _0PowP2 = <<A as Pow<B>>::Output as Same<_0>>::Output;

    assert_eq!(<_0PowP2 as Integer>::to_i64(), <_0 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test__0_Cmp_P2() {
    type A = Z0;
    type B = PInt<UInt<UInt<UTerm, B1>, B0>>;

    #[allow(non_camel_case_types)]
    type _0CmpP2 = <A as Cmp<B>>::Output;
    assert_eq!(<_0CmpP2 as Ord>::to_ordering(), Ordering::Less);
}
#[test]
#[allow(non_snake_case)]
fn test__0_Add_P3() {
    type A = Z0;
    type B = PInt<UInt<UInt<UTerm, B1>, B1>>;
    type P3 = PInt<UInt<UInt<UTerm, B1>, B1>>;

    #[allow(non_camel_case_types)]
    type _0AddP3 = <<A as Add<B>>::Output as Same<P3>>::Output;

    assert_eq!(<_0AddP3 as Integer>::to_i64(), <P3 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test__0_Sub_P3() {
    type A = Z0;
    type B = PInt<UInt<UInt<UTerm, B1>, B1>>;
    type N3 = NInt<UInt<UInt<UTerm, B1>, B1>>;

    #[allow(non_camel_case_types)]
    type _0SubP3 = <<A as Sub<B>>::Output as Same<N3>>::Output;

    assert_eq!(<_0SubP3 as Integer>::to_i64(), <N3 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test__0_Mul_P3() {
    type A = Z0;
    type B = PInt<UInt<UInt<UTerm, B1>, B1>>;
    type _0 = Z0;

    #[allow(non_camel_case_types)]
    type _0MulP3 = <<A as Mul<B>>::Output as Same<_0>>::Output;

    assert_eq!(<_0MulP3 as Integer>::to_i64(), <_0 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test__0_Min_P3() {
    type A = Z0;
    type B = PInt<UInt<UInt<UTerm, B1>, B1>>;
    type _0 = Z0;

    #[allow(non_camel_case_types)]
    type _0MinP3 = <<A as Min<B>>::Output as Same<_0>>::Output;

    assert_eq!(<_0MinP3 as Integer>::to_i64(), <_0 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test__0_Max_P3() {
    type A = Z0;
    type B = PInt<UInt<UInt<UTerm, B1>, B1>>;
    type P3 = PInt<UInt<UInt<UTerm, B1>, B1>>;

    #[allow(non_camel_case_types)]
    type _0MaxP3 = <<A as Max<B>>::Output as Same<P3>>::Output;

    assert_eq!(<_0MaxP3 as Integer>::to_i64(), <P3 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test__0_Gcd_P3() {
    type A = Z0;
    type B = PInt<UInt<UInt<UTerm, B1>, B1>>;
    type P3 = PInt<UInt<UInt<UTerm, B1>, B1>>;

    #[allow(non_camel_case_types)]
    type _0GcdP3 = <<A as Gcd<B>>::Output as Same<P3>>::Output;

    assert_eq!(<_0GcdP3 as Integer>::to_i64(), <P3 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test__0_Div_P3() {
    type A = Z0;
    type B = PInt<UInt<UInt<UTerm, B1>, B1>>;
    type _0 = Z0;

    #[allow(non_camel_case_types)]
    type _0DivP3 = <<A as Div<B>>::Output as Same<_0>>::Output;

    assert_eq!(<_0DivP3 as Integer>::to_i64(), <_0 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test__0_Rem_P3() {
    type A = Z0;
    type B = PInt<UInt<UInt<UTerm, B1>, B1>>;
    type _0 = Z0;

    #[allow(non_camel_case_types)]
    type _0RemP3 = <<A as Rem<B>>::Output as Same<_0>>::Output;

    assert_eq!(<_0RemP3 as Integer>::to_i64(), <_0 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test__0_PartialDiv_P3() {
    type A = Z0;
    type B = PInt<UInt<UInt<UTerm, B1>, B1>>;
    type _0 = Z0;

    #[allow(non_camel_case_types)]
    type _0PartialDivP3 = <<A as PartialDiv<B>>::Output as Same<_0>>::Output;

    assert_eq!(<_0PartialDivP3 as Integer>::to_i64(), <_0 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test__0_Pow_P3() {
    type A = Z0;
    type B = PInt<UInt<UInt<UTerm, B1>, B1>>;
    type _0 = Z0;

    #[allow(non_camel_case_types)]
    type _0PowP3 = <<A as Pow<B>>::Output as Same<_0>>::Output;

    assert_eq!(<_0PowP3 as Integer>::to_i64(), <_0 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test__0_Cmp_P3() {
    type A = Z0;
    type B = PInt<UInt<UInt<UTerm, B1>, B1>>;

    #[allow(non_camel_case_types)]
    type _0CmpP3 = <A as Cmp<B>>::Output;
    assert_eq!(<_0CmpP3 as Ord>::to_ordering(), Ordering::Less);
}
#[test]
#[allow(non_snake_case)]
fn test__0_Add_P4() {
    type A = Z0;
    type B = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>>;
    type P4 = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>>;

    #[allow(non_camel_case_types)]
    type _0AddP4 = <<A as Add<B>>::Output as Same<P4>>::Output;

    assert_eq!(<_0AddP4 as Integer>::to_i64(), <P4 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test__0_Sub_P4() {
    type A = Z0;
    type B = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>>;
    type N4 = NInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>>;

    #[allow(non_camel_case_types)]
    type _0SubP4 = <<A as Sub<B>>::Output as Same<N4>>::Output;

    assert_eq!(<_0SubP4 as Integer>::to_i64(), <N4 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test__0_Mul_P4() {
    type A = Z0;
    type B = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>>;
    type _0 = Z0;

    #[allow(non_camel_case_types)]
    type _0MulP4 = <<A as Mul<B>>::Output as Same<_0>>::Output;

    assert_eq!(<_0MulP4 as Integer>::to_i64(), <_0 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test__0_Min_P4() {
    type A = Z0;
    type B = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>>;
    type _0 = Z0;

    #[allow(non_camel_case_types)]
    type _0MinP4 = <<A as Min<B>>::Output as Same<_0>>::Output;

    assert_eq!(<_0MinP4 as Integer>::to_i64(), <_0 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test__0_Max_P4() {
    type A = Z0;
    type B = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>>;
    type P4 = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>>;

    #[allow(non_camel_case_types)]
    type _0MaxP4 = <<A as Max<B>>::Output as Same<P4>>::Output;

    assert_eq!(<_0MaxP4 as Integer>::to_i64(), <P4 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test__0_Gcd_P4() {
    type A = Z0;
    type B = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>>;
    type P4 = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>>;

    #[allow(non_camel_case_types)]
    type _0GcdP4 = <<A as Gcd<B>>::Output as Same<P4>>::Output;

    assert_eq!(<_0GcdP4 as Integer>::to_i64(), <P4 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test__0_Div_P4() {
    type A = Z0;
    type B = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>>;
    type _0 = Z0;

    #[allow(non_camel_case_types)]
    type _0DivP4 = <<A as Div<B>>::Output as Same<_0>>::Output;

    assert_eq!(<_0DivP4 as Integer>::to_i64(), <_0 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test__0_Rem_P4() {
    type A = Z0;
    type B = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>>;
    type _0 = Z0;

    #[allow(non_camel_case_types)]
    type _0RemP4 = <<A as Rem<B>>::Output as Same<_0>>::Output;

    assert_eq!(<_0RemP4 as Integer>::to_i64(), <_0 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test__0_PartialDiv_P4() {
    type A = Z0;
    type B = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>>;
    type _0 = Z0;

    #[allow(non_camel_case_types)]
    type _0PartialDivP4 = <<A as PartialDiv<B>>::Output as Same<_0>>::Output;

    assert_eq!(<_0PartialDivP4 as Integer>::to_i64(), <_0 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test__0_Pow_P4() {
    type A = Z0;
    type B = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>>;
    type _0 = Z0;

    #[allow(non_camel_case_types)]
    type _0PowP4 = <<A as Pow<B>>::Output as Same<_0>>::Output;

    assert_eq!(<_0PowP4 as Integer>::to_i64(), <_0 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test__0_Cmp_P4() {
    type A = Z0;
    type B = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>>;

    #[allow(non_camel_case_types)]
    type _0CmpP4 = <A as Cmp<B>>::Output;
    assert_eq!(<_0CmpP4 as Ord>::to_ordering(), Ordering::Less);
}
#[test]
#[allow(non_snake_case)]
fn test__0_Add_P5() {
    type A = Z0;
    type B = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>>;
    type P5 = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>>;

    #[allow(non_camel_case_types)]
    type _0AddP5 = <<A as Add<B>>::Output as Same<P5>>::Output;

    assert_eq!(<_0AddP5 as Integer>::to_i64(), <P5 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test__0_Sub_P5() {
    type A = Z0;
    type B = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>>;
    type N5 = NInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>>;

    #[allow(non_camel_case_types)]
    type _0SubP5 = <<A as Sub<B>>::Output as Same<N5>>::Output;

    assert_eq!(<_0SubP5 as Integer>::to_i64(), <N5 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test__0_Mul_P5() {
    type A = Z0;
    type B = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>>;
    type _0 = Z0;

    #[allow(non_camel_case_types)]
    type _0MulP5 = <<A as Mul<B>>::Output as Same<_0>>::Output;

    assert_eq!(<_0MulP5 as Integer>::to_i64(), <_0 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test__0_Min_P5() {
    type A = Z0;
    type B = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>>;
    type _0 = Z0;

    #[allow(non_camel_case_types)]
    type _0MinP5 = <<A as Min<B>>::Output as Same<_0>>::Output;

    assert_eq!(<_0MinP5 as Integer>::to_i64(), <_0 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test__0_Max_P5() {
    type A = Z0;
    type B = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>>;
    type P5 = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>>;

    #[allow(non_camel_case_types)]
    type _0MaxP5 = <<A as Max<B>>::Output as Same<P5>>::Output;

    assert_eq!(<_0MaxP5 as Integer>::to_i64(), <P5 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test__0_Gcd_P5() {
    type A = Z0;
    type B = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>>;
    type P5 = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>>;

    #[allow(non_camel_case_types)]
    type _0GcdP5 = <<A as Gcd<B>>::Output as Same<P5>>::Output;

    assert_eq!(<_0GcdP5 as Integer>::to_i64(), <P5 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test__0_Div_P5() {
    type A = Z0;
    type B = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>>;
    type _0 = Z0;

    #[allow(non_camel_case_types)]
    type _0DivP5 = <<A as Div<B>>::Output as Same<_0>>::Output;

    assert_eq!(<_0DivP5 as Integer>::to_i64(), <_0 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test__0_Rem_P5() {
    type A = Z0;
    type B = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>>;
    type _0 = Z0;

    #[allow(non_camel_case_types)]
    type _0RemP5 = <<A as Rem<B>>::Output as Same<_0>>::Output;

    assert_eq!(<_0RemP5 as Integer>::to_i64(), <_0 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test__0_PartialDiv_P5() {
    type A = Z0;
    type B = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>>;
    type _0 = Z0;

    #[allow(non_camel_case_types)]
    type _0PartialDivP5 = <<A as PartialDiv<B>>::Output as Same<_0>>::Output;

    assert_eq!(<_0PartialDivP5 as Integer>::to_i64(), <_0 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test__0_Pow_P5() {
    type A = Z0;
    type B = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>>;
    type _0 = Z0;

    #[allow(non_camel_case_types)]
    type _0PowP5 = <<A as Pow<B>>::Output as Same<_0>>::Output;

    assert_eq!(<_0PowP5 as Integer>::to_i64(), <_0 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test__0_Cmp_P5() {
    type A = Z0;
    type B = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>>;

    #[allow(non_camel_case_types)]
    type _0CmpP5 = <A as Cmp<B>>::Output;
    assert_eq!(<_0CmpP5 as Ord>::to_ordering(), Ordering::Less);
}
#[test]
#[allow(non_snake_case)]
fn test_P1_Add_N5() {
    type A = PInt<UInt<UTerm, B1>>;
    type B = NInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>>;
    type N4 = NInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>>;

    #[allow(non_camel_case_types)]
    type P1AddN5 = <<A as Add<B>>::Output as Same<N4>>::Output;

    assert_eq!(<P1AddN5 as Integer>::to_i64(), <N4 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_P1_Sub_N5() {
    type A = PInt<UInt<UTerm, B1>>;
    type B = NInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>>;
    type P6 = PInt<UInt<UInt<UInt<UTerm, B1>, B1>, B0>>;

    #[allow(non_camel_case_types)]
    type P1SubN5 = <<A as Sub<B>>::Output as Same<P6>>::Output;

    assert_eq!(<P1SubN5 as Integer>::to_i64(), <P6 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_P1_Mul_N5() {
    type A = PInt<UInt<UTerm, B1>>;
    type B = NInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>>;
    type N5 = NInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>>;

    #[allow(non_camel_case_types)]
    type P1MulN5 = <<A as Mul<B>>::Output as Same<N5>>::Output;

    assert_eq!(<P1MulN5 as Integer>::to_i64(), <N5 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_P1_Min_N5() {
    type A = PInt<UInt<UTerm, B1>>;
    type B = NInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>>;
    type N5 = NInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>>;

    #[allow(non_camel_case_types)]
    type P1MinN5 = <<A as Min<B>>::Output as Same<N5>>::Output;

    assert_eq!(<P1MinN5 as Integer>::to_i64(), <N5 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_P1_Max_N5() {
    type A = PInt<UInt<UTerm, B1>>;
    type B = NInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>>;
    type P1 = PInt<UInt<UTerm, B1>>;

    #[allow(non_camel_case_types)]
    type P1MaxN5 = <<A as Max<B>>::Output as Same<P1>>::Output;

    assert_eq!(<P1MaxN5 as Integer>::to_i64(), <P1 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_P1_Gcd_N5() {
    type A = PInt<UInt<UTerm, B1>>;
    type B = NInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>>;
    type P1 = PInt<UInt<UTerm, B1>>;

    #[allow(non_camel_case_types)]
    type P1GcdN5 = <<A as Gcd<B>>::Output as Same<P1>>::Output;

    assert_eq!(<P1GcdN5 as Integer>::to_i64(), <P1 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_P1_Div_N5() {
    type A = PInt<UInt<UTerm, B1>>;
    type B = NInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>>;
    type _0 = Z0;

    #[allow(non_camel_case_types)]
    type P1DivN5 = <<A as Div<B>>::Output as Same<_0>>::Output;

    assert_eq!(<P1DivN5 as Integer>::to_i64(), <_0 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_P1_Rem_N5() {
    type A = PInt<UInt<UTerm, B1>>;
    type B = NInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>>;
    type P1 = PInt<UInt<UTerm, B1>>;

    #[allow(non_camel_case_types)]
    type P1RemN5 = <<A as Rem<B>>::Output as Same<P1>>::Output;

    assert_eq!(<P1RemN5 as Integer>::to_i64(), <P1 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_P1_Pow_N5() {
    type A = PInt<UInt<UTerm, B1>>;
    type B = NInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>>;
    type P1 = PInt<UInt<UTerm, B1>>;

    #[allow(non_camel_case_types)]
    type P1PowN5 = <<A as Pow<B>>::Output as Same<P1>>::Output;

    assert_eq!(<P1PowN5 as Integer>::to_i64(), <P1 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_P1_Cmp_N5() {
    type A = PInt<UInt<UTerm, B1>>;
    type B = NInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>>;

    #[allow(non_camel_case_types)]
    type P1CmpN5 = <A as Cmp<B>>::Output;
    assert_eq!(<P1CmpN5 as Ord>::to_ordering(), Ordering::Greater);
}
#[test]
#[allow(non_snake_case)]
fn test_P1_Add_N4() {
    type A = PInt<UInt<UTerm, B1>>;
    type B = NInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>>;
    type N3 = NInt<UInt<UInt<UTerm, B1>, B1>>;

    #[allow(non_camel_case_types)]
    type P1AddN4 = <<A as Add<B>>::Output as Same<N3>>::Output;

    assert_eq!(<P1AddN4 as Integer>::to_i64(), <N3 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_P1_Sub_N4() {
    type A = PInt<UInt<UTerm, B1>>;
    type B = NInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>>;
    type P5 = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>>;

    #[allow(non_camel_case_types)]
    type P1SubN4 = <<A as Sub<B>>::Output as Same<P5>>::Output;

    assert_eq!(<P1SubN4 as Integer>::to_i64(), <P5 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_P1_Mul_N4() {
    type A = PInt<UInt<UTerm, B1>>;
    type B = NInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>>;
    type N4 = NInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>>;

    #[allow(non_camel_case_types)]
    type P1MulN4 = <<A as Mul<B>>::Output as Same<N4>>::Output;

    assert_eq!(<P1MulN4 as Integer>::to_i64(), <N4 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_P1_Min_N4() {
    type A = PInt<UInt<UTerm, B1>>;
    type B = NInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>>;
    type N4 = NInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>>;

    #[allow(non_camel_case_types)]
    type P1MinN4 = <<A as Min<B>>::Output as Same<N4>>::Output;

    assert_eq!(<P1MinN4 as Integer>::to_i64(), <N4 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_P1_Max_N4() {
    type A = PInt<UInt<UTerm, B1>>;
    type B = NInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>>;
    type P1 = PInt<UInt<UTerm, B1>>;

    #[allow(non_camel_case_types)]
    type P1MaxN4 = <<A as Max<B>>::Output as Same<P1>>::Output;

    assert_eq!(<P1MaxN4 as Integer>::to_i64(), <P1 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_P1_Gcd_N4() {
    type A = PInt<UInt<UTerm, B1>>;
    type B = NInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>>;
    type P1 = PInt<UInt<UTerm, B1>>;

    #[allow(non_camel_case_types)]
    type P1GcdN4 = <<A as Gcd<B>>::Output as Same<P1>>::Output;

    assert_eq!(<P1GcdN4 as Integer>::to_i64(), <P1 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_P1_Div_N4() {
    type A = PInt<UInt<UTerm, B1>>;
    type B = NInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>>;
    type _0 = Z0;

    #[allow(non_camel_case_types)]
    type P1DivN4 = <<A as Div<B>>::Output as Same<_0>>::Output;

    assert_eq!(<P1DivN4 as Integer>::to_i64(), <_0 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_P1_Rem_N4() {
    type A = PInt<UInt<UTerm, B1>>;
    type B = NInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>>;
    type P1 = PInt<UInt<UTerm, B1>>;

    #[allow(non_camel_case_types)]
    type P1RemN4 = <<A as Rem<B>>::Output as Same<P1>>::Output;

    assert_eq!(<P1RemN4 as Integer>::to_i64(), <P1 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_P1_Pow_N4() {
    type A = PInt<UInt<UTerm, B1>>;
    type B = NInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>>;
    type P1 = PInt<UInt<UTerm, B1>>;

    #[allow(non_camel_case_types)]
    type P1PowN4 = <<A as Pow<B>>::Output as Same<P1>>::Output;

    assert_eq!(<P1PowN4 as Integer>::to_i64(), <P1 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_P1_Cmp_N4() {
    type A = PInt<UInt<UTerm, B1>>;
    type B = NInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>>;

    #[allow(non_camel_case_types)]
    type P1CmpN4 = <A as Cmp<B>>::Output;
    assert_eq!(<P1CmpN4 as Ord>::to_ordering(), Ordering::Greater);
}
#[test]
#[allow(non_snake_case)]
fn test_P1_Add_N3() {
    type A = PInt<UInt<UTerm, B1>>;
    type B = NInt<UInt<UInt<UTerm, B1>, B1>>;
    type N2 = NInt<UInt<UInt<UTerm, B1>, B0>>;

    #[allow(non_camel_case_types)]
    type P1AddN3 = <<A as Add<B>>::Output as Same<N2>>::Output;

    assert_eq!(<P1AddN3 as Integer>::to_i64(), <N2 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_P1_Sub_N3() {
    type A = PInt<UInt<UTerm, B1>>;
    type B = NInt<UInt<UInt<UTerm, B1>, B1>>;
    type P4 = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>>;

    #[allow(non_camel_case_types)]
    type P1SubN3 = <<A as Sub<B>>::Output as Same<P4>>::Output;

    assert_eq!(<P1SubN3 as Integer>::to_i64(), <P4 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_P1_Mul_N3() {
    type A = PInt<UInt<UTerm, B1>>;
    type B = NInt<UInt<UInt<UTerm, B1>, B1>>;
    type N3 = NInt<UInt<UInt<UTerm, B1>, B1>>;

    #[allow(non_camel_case_types)]
    type P1MulN3 = <<A as Mul<B>>::Output as Same<N3>>::Output;

    assert_eq!(<P1MulN3 as Integer>::to_i64(), <N3 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_P1_Min_N3() {
    type A = PInt<UInt<UTerm, B1>>;
    type B = NInt<UInt<UInt<UTerm, B1>, B1>>;
    type N3 = NInt<UInt<UInt<UTerm, B1>, B1>>;

    #[allow(non_camel_case_types)]
    type P1MinN3 = <<A as Min<B>>::Output as Same<N3>>::Output;

    assert_eq!(<P1MinN3 as Integer>::to_i64(), <N3 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_P1_Max_N3() {
    type A = PInt<UInt<UTerm, B1>>;
    type B = NInt<UInt<UInt<UTerm, B1>, B1>>;
    type P1 = PInt<UInt<UTerm, B1>>;

    #[allow(non_camel_case_types)]
    type P1MaxN3 = <<A as Max<B>>::Output as Same<P1>>::Output;

    assert_eq!(<P1MaxN3 as Integer>::to_i64(), <P1 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_P1_Gcd_N3() {
    type A = PInt<UInt<UTerm, B1>>;
    type B = NInt<UInt<UInt<UTerm, B1>, B1>>;
    type P1 = PInt<UInt<UTerm, B1>>;

    #[allow(non_camel_case_types)]
    type P1GcdN3 = <<A as Gcd<B>>::Output as Same<P1>>::Output;

    assert_eq!(<P1GcdN3 as Integer>::to_i64(), <P1 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_P1_Div_N3() {
    type A = PInt<UInt<UTerm, B1>>;
    type B = NInt<UInt<UInt<UTerm, B1>, B1>>;
    type _0 = Z0;

    #[allow(non_camel_case_types)]
    type P1DivN3 = <<A as Div<B>>::Output as Same<_0>>::Output;

    assert_eq!(<P1DivN3 as Integer>::to_i64(), <_0 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_P1_Rem_N3() {
    type A = PInt<UInt<UTerm, B1>>;
    type B = NInt<UInt<UInt<UTerm, B1>, B1>>;
    type P1 = PInt<UInt<UTerm, B1>>;

    #[allow(non_camel_case_types)]
    type P1RemN3 = <<A as Rem<B>>::Output as Same<P1>>::Output;

    assert_eq!(<P1RemN3 as Integer>::to_i64(), <P1 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_P1_Pow_N3() {
    type A = PInt<UInt<UTerm, B1>>;
    type B = NInt<UInt<UInt<UTerm, B1>, B1>>;
    type P1 = PInt<UInt<UTerm, B1>>;

    #[allow(non_camel_case_types)]
    type P1PowN3 = <<A as Pow<B>>::Output as Same<P1>>::Output;

    assert_eq!(<P1PowN3 as Integer>::to_i64(), <P1 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_P1_Cmp_N3() {
    type A = PInt<UInt<UTerm, B1>>;
    type B = NInt<UInt<UInt<UTerm, B1>, B1>>;

    #[allow(non_camel_case_types)]
    type P1CmpN3 = <A as Cmp<B>>::Output;
    assert_eq!(<P1CmpN3 as Ord>::to_ordering(), Ordering::Greater);
}
#[test]
#[allow(non_snake_case)]
fn test_P1_Add_N2() {
    type A = PInt<UInt<UTerm, B1>>;
    type B = NInt<UInt<UInt<UTerm, B1>, B0>>;
    type N1 = NInt<UInt<UTerm, B1>>;

    #[allow(non_camel_case_types)]
    type P1AddN2 = <<A as Add<B>>::Output as Same<N1>>::Output;

    assert_eq!(<P1AddN2 as Integer>::to_i64(), <N1 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_P1_Sub_N2() {
    type A = PInt<UInt<UTerm, B1>>;
    type B = NInt<UInt<UInt<UTerm, B1>, B0>>;
    type P3 = PInt<UInt<UInt<UTerm, B1>, B1>>;

    #[allow(non_camel_case_types)]
    type P1SubN2 = <<A as Sub<B>>::Output as Same<P3>>::Output;

    assert_eq!(<P1SubN2 as Integer>::to_i64(), <P3 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_P1_Mul_N2() {
    type A = PInt<UInt<UTerm, B1>>;
    type B = NInt<UInt<UInt<UTerm, B1>, B0>>;
    type N2 = NInt<UInt<UInt<UTerm, B1>, B0>>;

    #[allow(non_camel_case_types)]
    type P1MulN2 = <<A as Mul<B>>::Output as Same<N2>>::Output;

    assert_eq!(<P1MulN2 as Integer>::to_i64(), <N2 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_P1_Min_N2() {
    type A = PInt<UInt<UTerm, B1>>;
    type B = NInt<UInt<UInt<UTerm, B1>, B0>>;
    type N2 = NInt<UInt<UInt<UTerm, B1>, B0>>;

    #[allow(non_camel_case_types)]
    type P1MinN2 = <<A as Min<B>>::Output as Same<N2>>::Output;

    assert_eq!(<P1MinN2 as Integer>::to_i64(), <N2 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_P1_Max_N2() {
    type A = PInt<UInt<UTerm, B1>>;
    type B = NInt<UInt<UInt<UTerm, B1>, B0>>;
    type P1 = PInt<UInt<UTerm, B1>>;

    #[allow(non_camel_case_types)]
    type P1MaxN2 = <<A as Max<B>>::Output as Same<P1>>::Output;

    assert_eq!(<P1MaxN2 as Integer>::to_i64(), <P1 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_P1_Gcd_N2() {
    type A = PInt<UInt<UTerm, B1>>;
    type B = NInt<UInt<UInt<UTerm, B1>, B0>>;
    type P1 = PInt<UInt<UTerm, B1>>;

    #[allow(non_camel_case_types)]
    type P1GcdN2 = <<A as Gcd<B>>::Output as Same<P1>>::Output;

    assert_eq!(<P1GcdN2 as Integer>::to_i64(), <P1 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_P1_Div_N2() {
    type A = PInt<UInt<UTerm, B1>>;
    type B = NInt<UInt<UInt<UTerm, B1>, B0>>;
    type _0 = Z0;

    #[allow(non_camel_case_types)]
    type P1DivN2 = <<A as Div<B>>::Output as Same<_0>>::Output;

    assert_eq!(<P1DivN2 as Integer>::to_i64(), <_0 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_P1_Rem_N2() {
    type A = PInt<UInt<UTerm, B1>>;
    type B = NInt<UInt<UInt<UTerm, B1>, B0>>;
    type P1 = PInt<UInt<UTerm, B1>>;

    #[allow(non_camel_case_types)]
    type P1RemN2 = <<A as Rem<B>>::Output as Same<P1>>::Output;

    assert_eq!(<P1RemN2 as Integer>::to_i64(), <P1 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_P1_Pow_N2() {
    type A = PInt<UInt<UTerm, B1>>;
    type B = NInt<UInt<UInt<UTerm, B1>, B0>>;
    type P1 = PInt<UInt<UTerm, B1>>;

    #[allow(non_camel_case_types)]
    type P1PowN2 = <<A as Pow<B>>::Output as Same<P1>>::Output;

    assert_eq!(<P1PowN2 as Integer>::to_i64(), <P1 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_P1_Cmp_N2() {
    type A = PInt<UInt<UTerm, B1>>;
    type B = NInt<UInt<UInt<UTerm, B1>, B0>>;

    #[allow(non_camel_case_types)]
    type P1CmpN2 = <A as Cmp<B>>::Output;
    assert_eq!(<P1CmpN2 as Ord>::to_ordering(), Ordering::Greater);
}
#[test]
#[allow(non_snake_case)]
fn test_P1_Add_N1() {
    type A = PInt<UInt<UTerm, B1>>;
    type B = NInt<UInt<UTerm, B1>>;
    type _0 = Z0;

    #[allow(non_camel_case_types)]
    type P1AddN1 = <<A as Add<B>>::Output as Same<_0>>::Output;

    assert_eq!(<P1AddN1 as Integer>::to_i64(), <_0 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_P1_Sub_N1() {
    type A = PInt<UInt<UTerm, B1>>;
    type B = NInt<UInt<UTerm, B1>>;
    type P2 = PInt<UInt<UInt<UTerm, B1>, B0>>;

    #[allow(non_camel_case_types)]
    type P1SubN1 = <<A as Sub<B>>::Output as Same<P2>>::Output;

    assert_eq!(<P1SubN1 as Integer>::to_i64(), <P2 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_P1_Mul_N1() {
    type A = PInt<UInt<UTerm, B1>>;
    type B = NInt<UInt<UTerm, B1>>;
    type N1 = NInt<UInt<UTerm, B1>>;

    #[allow(non_camel_case_types)]
    type P1MulN1 = <<A as Mul<B>>::Output as Same<N1>>::Output;

    assert_eq!(<P1MulN1 as Integer>::to_i64(), <N1 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_P1_Min_N1() {
    type A = PInt<UInt<UTerm, B1>>;
    type B = NInt<UInt<UTerm, B1>>;
    type N1 = NInt<UInt<UTerm, B1>>;

    #[allow(non_camel_case_types)]
    type P1MinN1 = <<A as Min<B>>::Output as Same<N1>>::Output;

    assert_eq!(<P1MinN1 as Integer>::to_i64(), <N1 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_P1_Max_N1() {
    type A = PInt<UInt<UTerm, B1>>;
    type B = NInt<UInt<UTerm, B1>>;
    type P1 = PInt<UInt<UTerm, B1>>;

    #[allow(non_camel_case_types)]
    type P1MaxN1 = <<A as Max<B>>::Output as Same<P1>>::Output;

    assert_eq!(<P1MaxN1 as Integer>::to_i64(), <P1 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_P1_Gcd_N1() {
    type A = PInt<UInt<UTerm, B1>>;
    type B = NInt<UInt<UTerm, B1>>;
    type P1 = PInt<UInt<UTerm, B1>>;

    #[allow(non_camel_case_types)]
    type P1GcdN1 = <<A as Gcd<B>>::Output as Same<P1>>::Output;

    assert_eq!(<P1GcdN1 as Integer>::to_i64(), <P1 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_P1_Div_N1() {
    type A = PInt<UInt<UTerm, B1>>;
    type B = NInt<UInt<UTerm, B1>>;
    type N1 = NInt<UInt<UTerm, B1>>;

    #[allow(non_camel_case_types)]
    type P1DivN1 = <<A as Div<B>>::Output as Same<N1>>::Output;

    assert_eq!(<P1DivN1 as Integer>::to_i64(), <N1 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_P1_Rem_N1() {
    type A = PInt<UInt<UTerm, B1>>;
    type B = NInt<UInt<UTerm, B1>>;
    type _0 = Z0;

    #[allow(non_camel_case_types)]
    type P1RemN1 = <<A as Rem<B>>::Output as Same<_0>>::Output;

    assert_eq!(<P1RemN1 as Integer>::to_i64(), <_0 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_P1_PartialDiv_N1() {
    type A = PInt<UInt<UTerm, B1>>;
    type B = NInt<UInt<UTerm, B1>>;
    type N1 = NInt<UInt<UTerm, B1>>;

    #[allow(non_camel_case_types)]
    type P1PartialDivN1 = <<A as PartialDiv<B>>::Output as Same<N1>>::Output;

    assert_eq!(<P1PartialDivN1 as Integer>::to_i64(), <N1 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_P1_Pow_N1() {
    type A = PInt<UInt<UTerm, B1>>;
    type B = NInt<UInt<UTerm, B1>>;
    type P1 = PInt<UInt<UTerm, B1>>;

    #[allow(non_camel_case_types)]
    type P1PowN1 = <<A as Pow<B>>::Output as Same<P1>>::Output;

    assert_eq!(<P1PowN1 as Integer>::to_i64(), <P1 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_P1_Cmp_N1() {
    type A = PInt<UInt<UTerm, B1>>;
    type B = NInt<UInt<UTerm, B1>>;

    #[allow(non_camel_case_types)]
    type P1CmpN1 = <A as Cmp<B>>::Output;
    assert_eq!(<P1CmpN1 as Ord>::to_ordering(), Ordering::Greater);
}
#[test]
#[allow(non_snake_case)]
fn test_P1_Add__0() {
    type A = PInt<UInt<UTerm, B1>>;
    type B = Z0;
    type P1 = PInt<UInt<UTerm, B1>>;

    #[allow(non_camel_case_types)]
    type P1Add_0 = <<A as Add<B>>::Output as Same<P1>>::Output;

    assert_eq!(<P1Add_0 as Integer>::to_i64(), <P1 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_P1_Sub__0() {
    type A = PInt<UInt<UTerm, B1>>;
    type B = Z0;
    type P1 = PInt<UInt<UTerm, B1>>;

    #[allow(non_camel_case_types)]
    type P1Sub_0 = <<A as Sub<B>>::Output as Same<P1>>::Output;

    assert_eq!(<P1Sub_0 as Integer>::to_i64(), <P1 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_P1_Mul__0() {
    type A = PInt<UInt<UTerm, B1>>;
    type B = Z0;
    type _0 = Z0;

    #[allow(non_camel_case_types)]
    type P1Mul_0 = <<A as Mul<B>>::Output as Same<_0>>::Output;

    assert_eq!(<P1Mul_0 as Integer>::to_i64(), <_0 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_P1_Min__0() {
    type A = PInt<UInt<UTerm, B1>>;
    type B = Z0;
    type _0 = Z0;

    #[allow(non_camel_case_types)]
    type P1Min_0 = <<A as Min<B>>::Output as Same<_0>>::Output;

    assert_eq!(<P1Min_0 as Integer>::to_i64(), <_0 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_P1_Max__0() {
    type A = PInt<UInt<UTerm, B1>>;
    type B = Z0;
    type P1 = PInt<UInt<UTerm, B1>>;

    #[allow(non_camel_case_types)]
    type P1Max_0 = <<A as Max<B>>::Output as Same<P1>>::Output;

    assert_eq!(<P1Max_0 as Integer>::to_i64(), <P1 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_P1_Gcd__0() {
    type A = PInt<UInt<UTerm, B1>>;
    type B = Z0;
    type P1 = PInt<UInt<UTerm, B1>>;

    #[allow(non_camel_case_types)]
    type P1Gcd_0 = <<A as Gcd<B>>::Output as Same<P1>>::Output;

    assert_eq!(<P1Gcd_0 as Integer>::to_i64(), <P1 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_P1_Pow__0() {
    type A = PInt<UInt<UTerm, B1>>;
    type B = Z0;
    type P1 = PInt<UInt<UTerm, B1>>;

    #[allow(non_camel_case_types)]
    type P1Pow_0 = <<A as Pow<B>>::Output as Same<P1>>::Output;

    assert_eq!(<P1Pow_0 as Integer>::to_i64(), <P1 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_P1_Cmp__0() {
    type A = PInt<UInt<UTerm, B1>>;
    type B = Z0;

    #[allow(non_camel_case_types)]
    type P1Cmp_0 = <A as Cmp<B>>::Output;
    assert_eq!(<P1Cmp_0 as Ord>::to_ordering(), Ordering::Greater);
}
#[test]
#[allow(non_snake_case)]
fn test_P1_Add_P1() {
    type A = PInt<UInt<UTerm, B1>>;
    type B = PInt<UInt<UTerm, B1>>;
    type P2 = PInt<UInt<UInt<UTerm, B1>, B0>>;

    #[allow(non_camel_case_types)]
    type P1AddP1 = <<A as Add<B>>::Output as Same<P2>>::Output;

    assert_eq!(<P1AddP1 as Integer>::to_i64(), <P2 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_P1_Sub_P1() {
    type A = PInt<UInt<UTerm, B1>>;
    type B = PInt<UInt<UTerm, B1>>;
    type _0 = Z0;

    #[allow(non_camel_case_types)]
    type P1SubP1 = <<A as Sub<B>>::Output as Same<_0>>::Output;

    assert_eq!(<P1SubP1 as Integer>::to_i64(), <_0 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_P1_Mul_P1() {
    type A = PInt<UInt<UTerm, B1>>;
    type B = PInt<UInt<UTerm, B1>>;
    type P1 = PInt<UInt<UTerm, B1>>;

    #[allow(non_camel_case_types)]
    type P1MulP1 = <<A as Mul<B>>::Output as Same<P1>>::Output;

    assert_eq!(<P1MulP1 as Integer>::to_i64(), <P1 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_P1_Min_P1() {
    type A = PInt<UInt<UTerm, B1>>;
    type B = PInt<UInt<UTerm, B1>>;
    type P1 = PInt<UInt<UTerm, B1>>;

    #[allow(non_camel_case_types)]
    type P1MinP1 = <<A as Min<B>>::Output as Same<P1>>::Output;

    assert_eq!(<P1MinP1 as Integer>::to_i64(), <P1 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_P1_Max_P1() {
    type A = PInt<UInt<UTerm, B1>>;
    type B = PInt<UInt<UTerm, B1>>;
    type P1 = PInt<UInt<UTerm, B1>>;

    #[allow(non_camel_case_types)]
    type P1MaxP1 = <<A as Max<B>>::Output as Same<P1>>::Output;

    assert_eq!(<P1MaxP1 as Integer>::to_i64(), <P1 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_P1_Gcd_P1() {
    type A = PInt<UInt<UTerm, B1>>;
    type B = PInt<UInt<UTerm, B1>>;
    type P1 = PInt<UInt<UTerm, B1>>;

    #[allow(non_camel_case_types)]
    type P1GcdP1 = <<A as Gcd<B>>::Output as Same<P1>>::Output;

    assert_eq!(<P1GcdP1 as Integer>::to_i64(), <P1 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_P1_Div_P1() {
    type A = PInt<UInt<UTerm, B1>>;
    type B = PInt<UInt<UTerm, B1>>;
    type P1 = PInt<UInt<UTerm, B1>>;

    #[allow(non_camel_case_types)]
    type P1DivP1 = <<A as Div<B>>::Output as Same<P1>>::Output;

    assert_eq!(<P1DivP1 as Integer>::to_i64(), <P1 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_P1_Rem_P1() {
    type A = PInt<UInt<UTerm, B1>>;
    type B = PInt<UInt<UTerm, B1>>;
    type _0 = Z0;

    #[allow(non_camel_case_types)]
    type P1RemP1 = <<A as Rem<B>>::Output as Same<_0>>::Output;

    assert_eq!(<P1RemP1 as Integer>::to_i64(), <_0 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_P1_PartialDiv_P1() {
    type A = PInt<UInt<UTerm, B1>>;
    type B = PInt<UInt<UTerm, B1>>;
    type P1 = PInt<UInt<UTerm, B1>>;

    #[allow(non_camel_case_types)]
    type P1PartialDivP1 = <<A as PartialDiv<B>>::Output as Same<P1>>::Output;

    assert_eq!(<P1PartialDivP1 as Integer>::to_i64(), <P1 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_P1_Pow_P1() {
    type A = PInt<UInt<UTerm, B1>>;
    type B = PInt<UInt<UTerm, B1>>;
    type P1 = PInt<UInt<UTerm, B1>>;

    #[allow(non_camel_case_types)]
    type P1PowP1 = <<A as Pow<B>>::Output as Same<P1>>::Output;

    assert_eq!(<P1PowP1 as Integer>::to_i64(), <P1 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_P1_Cmp_P1() {
    type A = PInt<UInt<UTerm, B1>>;
    type B = PInt<UInt<UTerm, B1>>;

    #[allow(non_camel_case_types)]
    type P1CmpP1 = <A as Cmp<B>>::Output;
    assert_eq!(<P1CmpP1 as Ord>::to_ordering(), Ordering::Equal);
}
#[test]
#[allow(non_snake_case)]
fn test_P1_Add_P2() {
    type A = PInt<UInt<UTerm, B1>>;
    type B = PInt<UInt<UInt<UTerm, B1>, B0>>;
    type P3 = PInt<UInt<UInt<UTerm, B1>, B1>>;

    #[allow(non_camel_case_types)]
    type P1AddP2 = <<A as Add<B>>::Output as Same<P3>>::Output;

    assert_eq!(<P1AddP2 as Integer>::to_i64(), <P3 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_P1_Sub_P2() {
    type A = PInt<UInt<UTerm, B1>>;
    type B = PInt<UInt<UInt<UTerm, B1>, B0>>;
    type N1 = NInt<UInt<UTerm, B1>>;

    #[allow(non_camel_case_types)]
    type P1SubP2 = <<A as Sub<B>>::Output as Same<N1>>::Output;

    assert_eq!(<P1SubP2 as Integer>::to_i64(), <N1 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_P1_Mul_P2() {
    type A = PInt<UInt<UTerm, B1>>;
    type B = PInt<UInt<UInt<UTerm, B1>, B0>>;
    type P2 = PInt<UInt<UInt<UTerm, B1>, B0>>;

    #[allow(non_camel_case_types)]
    type P1MulP2 = <<A as Mul<B>>::Output as Same<P2>>::Output;

    assert_eq!(<P1MulP2 as Integer>::to_i64(), <P2 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_P1_Min_P2() {
    type A = PInt<UInt<UTerm, B1>>;
    type B = PInt<UInt<UInt<UTerm, B1>, B0>>;
    type P1 = PInt<UInt<UTerm, B1>>;

    #[allow(non_camel_case_types)]
    type P1MinP2 = <<A as Min<B>>::Output as Same<P1>>::Output;

    assert_eq!(<P1MinP2 as Integer>::to_i64(), <P1 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_P1_Max_P2() {
    type A = PInt<UInt<UTerm, B1>>;
    type B = PInt<UInt<UInt<UTerm, B1>, B0>>;
    type P2 = PInt<UInt<UInt<UTerm, B1>, B0>>;

    #[allow(non_camel_case_types)]
    type P1MaxP2 = <<A as Max<B>>::Output as Same<P2>>::Output;

    assert_eq!(<P1MaxP2 as Integer>::to_i64(), <P2 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_P1_Gcd_P2() {
    type A = PInt<UInt<UTerm, B1>>;
    type B = PInt<UInt<UInt<UTerm, B1>, B0>>;
    type P1 = PInt<UInt<UTerm, B1>>;

    #[allow(non_camel_case_types)]
    type P1GcdP2 = <<A as Gcd<B>>::Output as Same<P1>>::Output;

    assert_eq!(<P1GcdP2 as Integer>::to_i64(), <P1 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_P1_Div_P2() {
    type A = PInt<UInt<UTerm, B1>>;
    type B = PInt<UInt<UInt<UTerm, B1>, B0>>;
    type _0 = Z0;

    #[allow(non_camel_case_types)]
    type P1DivP2 = <<A as Div<B>>::Output as Same<_0>>::Output;

    assert_eq!(<P1DivP2 as Integer>::to_i64(), <_0 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_P1_Rem_P2() {
    type A = PInt<UInt<UTerm, B1>>;
    type B = PInt<UInt<UInt<UTerm, B1>, B0>>;
    type P1 = PInt<UInt<UTerm, B1>>;

    #[allow(non_camel_case_types)]
    type P1RemP2 = <<A as Rem<B>>::Output as Same<P1>>::Output;

    assert_eq!(<P1RemP2 as Integer>::to_i64(), <P1 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_P1_Pow_P2() {
    type A = PInt<UInt<UTerm, B1>>;
    type B = PInt<UInt<UInt<UTerm, B1>, B0>>;
    type P1 = PInt<UInt<UTerm, B1>>;

    #[allow(non_camel_case_types)]
    type P1PowP2 = <<A as Pow<B>>::Output as Same<P1>>::Output;

    assert_eq!(<P1PowP2 as Integer>::to_i64(), <P1 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_P1_Cmp_P2() {
    type A = PInt<UInt<UTerm, B1>>;
    type B = PInt<UInt<UInt<UTerm, B1>, B0>>;

    #[allow(non_camel_case_types)]
    type P1CmpP2 = <A as Cmp<B>>::Output;
    assert_eq!(<P1CmpP2 as Ord>::to_ordering(), Ordering::Less);
}
#[test]
#[allow(non_snake_case)]
fn test_P1_Add_P3() {
    type A = PInt<UInt<UTerm, B1>>;
    type B = PInt<UInt<UInt<UTerm, B1>, B1>>;
    type P4 = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>>;

    #[allow(non_camel_case_types)]
    type P1AddP3 = <<A as Add<B>>::Output as Same<P4>>::Output;

    assert_eq!(<P1AddP3 as Integer>::to_i64(), <P4 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_P1_Sub_P3() {
    type A = PInt<UInt<UTerm, B1>>;
    type B = PInt<UInt<UInt<UTerm, B1>, B1>>;
    type N2 = NInt<UInt<UInt<UTerm, B1>, B0>>;

    #[allow(non_camel_case_types)]
    type P1SubP3 = <<A as Sub<B>>::Output as Same<N2>>::Output;

    assert_eq!(<P1SubP3 as Integer>::to_i64(), <N2 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_P1_Mul_P3() {
    type A = PInt<UInt<UTerm, B1>>;
    type B = PInt<UInt<UInt<UTerm, B1>, B1>>;
    type P3 = PInt<UInt<UInt<UTerm, B1>, B1>>;

    #[allow(non_camel_case_types)]
    type P1MulP3 = <<A as Mul<B>>::Output as Same<P3>>::Output;

    assert_eq!(<P1MulP3 as Integer>::to_i64(), <P3 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_P1_Min_P3() {
    type A = PInt<UInt<UTerm, B1>>;
    type B = PInt<UInt<UInt<UTerm, B1>, B1>>;
    type P1 = PInt<UInt<UTerm, B1>>;

    #[allow(non_camel_case_types)]
    type P1MinP3 = <<A as Min<B>>::Output as Same<P1>>::Output;

    assert_eq!(<P1MinP3 as Integer>::to_i64(), <P1 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_P1_Max_P3() {
    type A = PInt<UInt<UTerm, B1>>;
    type B = PInt<UInt<UInt<UTerm, B1>, B1>>;
    type P3 = PInt<UInt<UInt<UTerm, B1>, B1>>;

    #[allow(non_camel_case_types)]
    type P1MaxP3 = <<A as Max<B>>::Output as Same<P3>>::Output;

    assert_eq!(<P1MaxP3 as Integer>::to_i64(), <P3 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_P1_Gcd_P3() {
    type A = PInt<UInt<UTerm, B1>>;
    type B = PInt<UInt<UInt<UTerm, B1>, B1>>;
    type P1 = PInt<UInt<UTerm, B1>>;

    #[allow(non_camel_case_types)]
    type P1GcdP3 = <<A as Gcd<B>>::Output as Same<P1>>::Output;

    assert_eq!(<P1GcdP3 as Integer>::to_i64(), <P1 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_P1_Div_P3() {
    type A = PInt<UInt<UTerm, B1>>;
    type B = PInt<UInt<UInt<UTerm, B1>, B1>>;
    type _0 = Z0;

    #[allow(non_camel_case_types)]
    type P1DivP3 = <<A as Div<B>>::Output as Same<_0>>::Output;

    assert_eq!(<P1DivP3 as Integer>::to_i64(), <_0 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_P1_Rem_P3() {
    type A = PInt<UInt<UTerm, B1>>;
    type B = PInt<UInt<UInt<UTerm, B1>, B1>>;
    type P1 = PInt<UInt<UTerm, B1>>;

    #[allow(non_camel_case_types)]
    type P1RemP3 = <<A as Rem<B>>::Output as Same<P1>>::Output;

    assert_eq!(<P1RemP3 as Integer>::to_i64(), <P1 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_P1_Pow_P3() {
    type A = PInt<UInt<UTerm, B1>>;
    type B = PInt<UInt<UInt<UTerm, B1>, B1>>;
    type P1 = PInt<UInt<UTerm, B1>>;

    #[allow(non_camel_case_types)]
    type P1PowP3 = <<A as Pow<B>>::Output as Same<P1>>::Output;

    assert_eq!(<P1PowP3 as Integer>::to_i64(), <P1 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_P1_Cmp_P3() {
    type A = PInt<UInt<UTerm, B1>>;
    type B = PInt<UInt<UInt<UTerm, B1>, B1>>;

    #[allow(non_camel_case_types)]
    type P1CmpP3 = <A as Cmp<B>>::Output;
    assert_eq!(<P1CmpP3 as Ord>::to_ordering(), Ordering::Less);
}
#[test]
#[allow(non_snake_case)]
fn test_P1_Add_P4() {
    type A = PInt<UInt<UTerm, B1>>;
    type B = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>>;
    type P5 = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>>;

    #[allow(non_camel_case_types)]
    type P1AddP4 = <<A as Add<B>>::Output as Same<P5>>::Output;

    assert_eq!(<P1AddP4 as Integer>::to_i64(), <P5 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_P1_Sub_P4() {
    type A = PInt<UInt<UTerm, B1>>;
    type B = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>>;
    type N3 = NInt<UInt<UInt<UTerm, B1>, B1>>;

    #[allow(non_camel_case_types)]
    type P1SubP4 = <<A as Sub<B>>::Output as Same<N3>>::Output;

    assert_eq!(<P1SubP4 as Integer>::to_i64(), <N3 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_P1_Mul_P4() {
    type A = PInt<UInt<UTerm, B1>>;
    type B = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>>;
    type P4 = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>>;

    #[allow(non_camel_case_types)]
    type P1MulP4 = <<A as Mul<B>>::Output as Same<P4>>::Output;

    assert_eq!(<P1MulP4 as Integer>::to_i64(), <P4 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_P1_Min_P4() {
    type A = PInt<UInt<UTerm, B1>>;
    type B = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>>;
    type P1 = PInt<UInt<UTerm, B1>>;

    #[allow(non_camel_case_types)]
    type P1MinP4 = <<A as Min<B>>::Output as Same<P1>>::Output;

    assert_eq!(<P1MinP4 as Integer>::to_i64(), <P1 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_P1_Max_P4() {
    type A = PInt<UInt<UTerm, B1>>;
    type B = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>>;
    type P4 = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>>;

    #[allow(non_camel_case_types)]
    type P1MaxP4 = <<A as Max<B>>::Output as Same<P4>>::Output;

    assert_eq!(<P1MaxP4 as Integer>::to_i64(), <P4 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_P1_Gcd_P4() {
    type A = PInt<UInt<UTerm, B1>>;
    type B = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>>;
    type P1 = PInt<UInt<UTerm, B1>>;

    #[allow(non_camel_case_types)]
    type P1GcdP4 = <<A as Gcd<B>>::Output as Same<P1>>::Output;

    assert_eq!(<P1GcdP4 as Integer>::to_i64(), <P1 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_P1_Div_P4() {
    type A = PInt<UInt<UTerm, B1>>;
    type B = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>>;
    type _0 = Z0;

    #[allow(non_camel_case_types)]
    type P1DivP4 = <<A as Div<B>>::Output as Same<_0>>::Output;

    assert_eq!(<P1DivP4 as Integer>::to_i64(), <_0 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_P1_Rem_P4() {
    type A = PInt<UInt<UTerm, B1>>;
    type B = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>>;
    type P1 = PInt<UInt<UTerm, B1>>;

    #[allow(non_camel_case_types)]
    type P1RemP4 = <<A as Rem<B>>::Output as Same<P1>>::Output;

    assert_eq!(<P1RemP4 as Integer>::to_i64(), <P1 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_P1_Pow_P4() {
    type A = PInt<UInt<UTerm, B1>>;
    type B = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>>;
    type P1 = PInt<UInt<UTerm, B1>>;

    #[allow(non_camel_case_types)]
    type P1PowP4 = <<A as Pow<B>>::Output as Same<P1>>::Output;

    assert_eq!(<P1PowP4 as Integer>::to_i64(), <P1 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_P1_Cmp_P4() {
    type A = PInt<UInt<UTerm, B1>>;
    type B = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>>;

    #[allow(non_camel_case_types)]
    type P1CmpP4 = <A as Cmp<B>>::Output;
    assert_eq!(<P1CmpP4 as Ord>::to_ordering(), Ordering::Less);
}
#[test]
#[allow(non_snake_case)]
fn test_P1_Add_P5() {
    type A = PInt<UInt<UTerm, B1>>;
    type B = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>>;
    type P6 = PInt<UInt<UInt<UInt<UTerm, B1>, B1>, B0>>;

    #[allow(non_camel_case_types)]
    type P1AddP5 = <<A as Add<B>>::Output as Same<P6>>::Output;

    assert_eq!(<P1AddP5 as Integer>::to_i64(), <P6 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_P1_Sub_P5() {
    type A = PInt<UInt<UTerm, B1>>;
    type B = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>>;
    type N4 = NInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>>;

    #[allow(non_camel_case_types)]
    type P1SubP5 = <<A as Sub<B>>::Output as Same<N4>>::Output;

    assert_eq!(<P1SubP5 as Integer>::to_i64(), <N4 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_P1_Mul_P5() {
    type A = PInt<UInt<UTerm, B1>>;
    type B = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>>;
    type P5 = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>>;

    #[allow(non_camel_case_types)]
    type P1MulP5 = <<A as Mul<B>>::Output as Same<P5>>::Output;

    assert_eq!(<P1MulP5 as Integer>::to_i64(), <P5 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_P1_Min_P5() {
    type A = PInt<UInt<UTerm, B1>>;
    type B = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>>;
    type P1 = PInt<UInt<UTerm, B1>>;

    #[allow(non_camel_case_types)]
    type P1MinP5 = <<A as Min<B>>::Output as Same<P1>>::Output;

    assert_eq!(<P1MinP5 as Integer>::to_i64(), <P1 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_P1_Max_P5() {
    type A = PInt<UInt<UTerm, B1>>;
    type B = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>>;
    type P5 = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>>;

    #[allow(non_camel_case_types)]
    type P1MaxP5 = <<A as Max<B>>::Output as Same<P5>>::Output;

    assert_eq!(<P1MaxP5 as Integer>::to_i64(), <P5 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_P1_Gcd_P5() {
    type A = PInt<UInt<UTerm, B1>>;
    type B = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>>;
    type P1 = PInt<UInt<UTerm, B1>>;

    #[allow(non_camel_case_types)]
    type P1GcdP5 = <<A as Gcd<B>>::Output as Same<P1>>::Output;

    assert_eq!(<P1GcdP5 as Integer>::to_i64(), <P1 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_P1_Div_P5() {
    type A = PInt<UInt<UTerm, B1>>;
    type B = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>>;
    type _0 = Z0;

    #[allow(non_camel_case_types)]
    type P1DivP5 = <<A as Div<B>>::Output as Same<_0>>::Output;

    assert_eq!(<P1DivP5 as Integer>::to_i64(), <_0 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_P1_Rem_P5() {
    type A = PInt<UInt<UTerm, B1>>;
    type B = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>>;
    type P1 = PInt<UInt<UTerm, B1>>;

    #[allow(non_camel_case_types)]
    type P1RemP5 = <<A as Rem<B>>::Output as Same<P1>>::Output;

    assert_eq!(<P1RemP5 as Integer>::to_i64(), <P1 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_P1_Pow_P5() {
    type A = PInt<UInt<UTerm, B1>>;
    type B = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>>;
    type P1 = PInt<UInt<UTerm, B1>>;

    #[allow(non_camel_case_types)]
    type P1PowP5 = <<A as Pow<B>>::Output as Same<P1>>::Output;

    assert_eq!(<P1PowP5 as Integer>::to_i64(), <P1 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_P1_Cmp_P5() {
    type A = PInt<UInt<UTerm, B1>>;
    type B = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>>;

    #[allow(non_camel_case_types)]
    type P1CmpP5 = <A as Cmp<B>>::Output;
    assert_eq!(<P1CmpP5 as Ord>::to_ordering(), Ordering::Less);
}
#[test]
#[allow(non_snake_case)]
fn test_P2_Add_N5() {
    type A = PInt<UInt<UInt<UTerm, B1>, B0>>;
    type B = NInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>>;
    type N3 = NInt<UInt<UInt<UTerm, B1>, B1>>;

    #[allow(non_camel_case_types)]
    type P2AddN5 = <<A as Add<B>>::Output as Same<N3>>::Output;

    assert_eq!(<P2AddN5 as Integer>::to_i64(), <N3 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_P2_Sub_N5() {
    type A = PInt<UInt<UInt<UTerm, B1>, B0>>;
    type B = NInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>>;
    type P7 = PInt<UInt<UInt<UInt<UTerm, B1>, B1>, B1>>;

    #[allow(non_camel_case_types)]
    type P2SubN5 = <<A as Sub<B>>::Output as Same<P7>>::Output;

    assert_eq!(<P2SubN5 as Integer>::to_i64(), <P7 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_P2_Mul_N5() {
    type A = PInt<UInt<UInt<UTerm, B1>, B0>>;
    type B = NInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>>;
    type N10 = NInt<UInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>, B0>>;

    #[allow(non_camel_case_types)]
    type P2MulN5 = <<A as Mul<B>>::Output as Same<N10>>::Output;

    assert_eq!(<P2MulN5 as Integer>::to_i64(), <N10 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_P2_Min_N5() {
    type A = PInt<UInt<UInt<UTerm, B1>, B0>>;
    type B = NInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>>;
    type N5 = NInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>>;

    #[allow(non_camel_case_types)]
    type P2MinN5 = <<A as Min<B>>::Output as Same<N5>>::Output;

    assert_eq!(<P2MinN5 as Integer>::to_i64(), <N5 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_P2_Max_N5() {
    type A = PInt<UInt<UInt<UTerm, B1>, B0>>;
    type B = NInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>>;
    type P2 = PInt<UInt<UInt<UTerm, B1>, B0>>;

    #[allow(non_camel_case_types)]
    type P2MaxN5 = <<A as Max<B>>::Output as Same<P2>>::Output;

    assert_eq!(<P2MaxN5 as Integer>::to_i64(), <P2 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_P2_Gcd_N5() {
    type A = PInt<UInt<UInt<UTerm, B1>, B0>>;
    type B = NInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>>;
    type P1 = PInt<UInt<UTerm, B1>>;

    #[allow(non_camel_case_types)]
    type P2GcdN5 = <<A as Gcd<B>>::Output as Same<P1>>::Output;

    assert_eq!(<P2GcdN5 as Integer>::to_i64(), <P1 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_P2_Div_N5() {
    type A = PInt<UInt<UInt<UTerm, B1>, B0>>;
    type B = NInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>>;
    type _0 = Z0;

    #[allow(non_camel_case_types)]
    type P2DivN5 = <<A as Div<B>>::Output as Same<_0>>::Output;

    assert_eq!(<P2DivN5 as Integer>::to_i64(), <_0 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_P2_Rem_N5() {
    type A = PInt<UInt<UInt<UTerm, B1>, B0>>;
    type B = NInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>>;
    type P2 = PInt<UInt<UInt<UTerm, B1>, B0>>;

    #[allow(non_camel_case_types)]
    type P2RemN5 = <<A as Rem<B>>::Output as Same<P2>>::Output;

    assert_eq!(<P2RemN5 as Integer>::to_i64(), <P2 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_P2_Cmp_N5() {
    type A = PInt<UInt<UInt<UTerm, B1>, B0>>;
    type B = NInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>>;

    #[allow(non_camel_case_types)]
    type P2CmpN5 = <A as Cmp<B>>::Output;
    assert_eq!(<P2CmpN5 as Ord>::to_ordering(), Ordering::Greater);
}
#[test]
#[allow(non_snake_case)]
fn test_P2_Add_N4() {
    type A = PInt<UInt<UInt<UTerm, B1>, B0>>;
    type B = NInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>>;
    type N2 = NInt<UInt<UInt<UTerm, B1>, B0>>;

    #[allow(non_camel_case_types)]
    type P2AddN4 = <<A as Add<B>>::Output as Same<N2>>::Output;

    assert_eq!(<P2AddN4 as Integer>::to_i64(), <N2 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_P2_Sub_N4() {
    type A = PInt<UInt<UInt<UTerm, B1>, B0>>;
    type B = NInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>>;
    type P6 = PInt<UInt<UInt<UInt<UTerm, B1>, B1>, B0>>;

    #[allow(non_camel_case_types)]
    type P2SubN4 = <<A as Sub<B>>::Output as Same<P6>>::Output;

    assert_eq!(<P2SubN4 as Integer>::to_i64(), <P6 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_P2_Mul_N4() {
    type A = PInt<UInt<UInt<UTerm, B1>, B0>>;
    type B = NInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>>;
    type N8 = NInt<UInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>, B0>>;

    #[allow(non_camel_case_types)]
    type P2MulN4 = <<A as Mul<B>>::Output as Same<N8>>::Output;

    assert_eq!(<P2MulN4 as Integer>::to_i64(), <N8 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_P2_Min_N4() {
    type A = PInt<UInt<UInt<UTerm, B1>, B0>>;
    type B = NInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>>;
    type N4 = NInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>>;

    #[allow(non_camel_case_types)]
    type P2MinN4 = <<A as Min<B>>::Output as Same<N4>>::Output;

    assert_eq!(<P2MinN4 as Integer>::to_i64(), <N4 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_P2_Max_N4() {
    type A = PInt<UInt<UInt<UTerm, B1>, B0>>;
    type B = NInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>>;
    type P2 = PInt<UInt<UInt<UTerm, B1>, B0>>;

    #[allow(non_camel_case_types)]
    type P2MaxN4 = <<A as Max<B>>::Output as Same<P2>>::Output;

    assert_eq!(<P2MaxN4 as Integer>::to_i64(), <P2 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_P2_Gcd_N4() {
    type A = PInt<UInt<UInt<UTerm, B1>, B0>>;
    type B = NInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>>;
    type P2 = PInt<UInt<UInt<UTerm, B1>, B0>>;

    #[allow(non_camel_case_types)]
    type P2GcdN4 = <<A as Gcd<B>>::Output as Same<P2>>::Output;

    assert_eq!(<P2GcdN4 as Integer>::to_i64(), <P2 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_P2_Div_N4() {
    type A = PInt<UInt<UInt<UTerm, B1>, B0>>;
    type B = NInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>>;
    type _0 = Z0;

    #[allow(non_camel_case_types)]
    type P2DivN4 = <<A as Div<B>>::Output as Same<_0>>::Output;

    assert_eq!(<P2DivN4 as Integer>::to_i64(), <_0 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_P2_Rem_N4() {
    type A = PInt<UInt<UInt<UTerm, B1>, B0>>;
    type B = NInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>>;
    type P2 = PInt<UInt<UInt<UTerm, B1>, B0>>;

    #[allow(non_camel_case_types)]
    type P2RemN4 = <<A as Rem<B>>::Output as Same<P2>>::Output;

    assert_eq!(<P2RemN4 as Integer>::to_i64(), <P2 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_P2_Cmp_N4() {
    type A = PInt<UInt<UInt<UTerm, B1>, B0>>;
    type B = NInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>>;

    #[allow(non_camel_case_types)]
    type P2CmpN4 = <A as Cmp<B>>::Output;
    assert_eq!(<P2CmpN4 as Ord>::to_ordering(), Ordering::Greater);
}
#[test]
#[allow(non_snake_case)]
fn test_P2_Add_N3() {
    type A = PInt<UInt<UInt<UTerm, B1>, B0>>;
    type B = NInt<UInt<UInt<UTerm, B1>, B1>>;
    type N1 = NInt<UInt<UTerm, B1>>;

    #[allow(non_camel_case_types)]
    type P2AddN3 = <<A as Add<B>>::Output as Same<N1>>::Output;

    assert_eq!(<P2AddN3 as Integer>::to_i64(), <N1 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_P2_Sub_N3() {
    type A = PInt<UInt<UInt<UTerm, B1>, B0>>;
    type B = NInt<UInt<UInt<UTerm, B1>, B1>>;
    type P5 = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>>;

    #[allow(non_camel_case_types)]
    type P2SubN3 = <<A as Sub<B>>::Output as Same<P5>>::Output;

    assert_eq!(<P2SubN3 as Integer>::to_i64(), <P5 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_P2_Mul_N3() {
    type A = PInt<UInt<UInt<UTerm, B1>, B0>>;
    type B = NInt<UInt<UInt<UTerm, B1>, B1>>;
    type N6 = NInt<UInt<UInt<UInt<UTerm, B1>, B1>, B0>>;

    #[allow(non_camel_case_types)]
    type P2MulN3 = <<A as Mul<B>>::Output as Same<N6>>::Output;

    assert_eq!(<P2MulN3 as Integer>::to_i64(), <N6 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_P2_Min_N3() {
    type A = PInt<UInt<UInt<UTerm, B1>, B0>>;
    type B = NInt<UInt<UInt<UTerm, B1>, B1>>;
    type N3 = NInt<UInt<UInt<UTerm, B1>, B1>>;

    #[allow(non_camel_case_types)]
    type P2MinN3 = <<A as Min<B>>::Output as Same<N3>>::Output;

    assert_eq!(<P2MinN3 as Integer>::to_i64(), <N3 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_P2_Max_N3() {
    type A = PInt<UInt<UInt<UTerm, B1>, B0>>;
    type B = NInt<UInt<UInt<UTerm, B1>, B1>>;
    type P2 = PInt<UInt<UInt<UTerm, B1>, B0>>;

    #[allow(non_camel_case_types)]
    type P2MaxN3 = <<A as Max<B>>::Output as Same<P2>>::Output;

    assert_eq!(<P2MaxN3 as Integer>::to_i64(), <P2 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_P2_Gcd_N3() {
    type A = PInt<UInt<UInt<UTerm, B1>, B0>>;
    type B = NInt<UInt<UInt<UTerm, B1>, B1>>;
    type P1 = PInt<UInt<UTerm, B1>>;

    #[allow(non_camel_case_types)]
    type P2GcdN3 = <<A as Gcd<B>>::Output as Same<P1>>::Output;

    assert_eq!(<P2GcdN3 as Integer>::to_i64(), <P1 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_P2_Div_N3() {
    type A = PInt<UInt<UInt<UTerm, B1>, B0>>;
    type B = NInt<UInt<UInt<UTerm, B1>, B1>>;
    type _0 = Z0;

    #[allow(non_camel_case_types)]
    type P2DivN3 = <<A as Div<B>>::Output as Same<_0>>::Output;

    assert_eq!(<P2DivN3 as Integer>::to_i64(), <_0 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_P2_Rem_N3() {
    type A = PInt<UInt<UInt<UTerm, B1>, B0>>;
    type B = NInt<UInt<UInt<UTerm, B1>, B1>>;
    type P2 = PInt<UInt<UInt<UTerm, B1>, B0>>;

    #[allow(non_camel_case_types)]
    type P2RemN3 = <<A as Rem<B>>::Output as Same<P2>>::Output;

    assert_eq!(<P2RemN3 as Integer>::to_i64(), <P2 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_P2_Cmp_N3() {
    type A = PInt<UInt<UInt<UTerm, B1>, B0>>;
    type B = NInt<UInt<UInt<UTerm, B1>, B1>>;

    #[allow(non_camel_case_types)]
    type P2CmpN3 = <A as Cmp<B>>::Output;
    assert_eq!(<P2CmpN3 as Ord>::to_ordering(), Ordering::Greater);
}
#[test]
#[allow(non_snake_case)]
fn test_P2_Add_N2() {
    type A = PInt<UInt<UInt<UTerm, B1>, B0>>;
    type B = NInt<UInt<UInt<UTerm, B1>, B0>>;
    type _0 = Z0;

    #[allow(non_camel_case_types)]
    type P2AddN2 = <<A as Add<B>>::Output as Same<_0>>::Output;

    assert_eq!(<P2AddN2 as Integer>::to_i64(), <_0 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_P2_Sub_N2() {
    type A = PInt<UInt<UInt<UTerm, B1>, B0>>;
    type B = NInt<UInt<UInt<UTerm, B1>, B0>>;
    type P4 = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>>;

    #[allow(non_camel_case_types)]
    type P2SubN2 = <<A as Sub<B>>::Output as Same<P4>>::Output;

    assert_eq!(<P2SubN2 as Integer>::to_i64(), <P4 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_P2_Mul_N2() {
    type A = PInt<UInt<UInt<UTerm, B1>, B0>>;
    type B = NInt<UInt<UInt<UTerm, B1>, B0>>;
    type N4 = NInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>>;

    #[allow(non_camel_case_types)]
    type P2MulN2 = <<A as Mul<B>>::Output as Same<N4>>::Output;

    assert_eq!(<P2MulN2 as Integer>::to_i64(), <N4 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_P2_Min_N2() {
    type A = PInt<UInt<UInt<UTerm, B1>, B0>>;
    type B = NInt<UInt<UInt<UTerm, B1>, B0>>;
    type N2 = NInt<UInt<UInt<UTerm, B1>, B0>>;

    #[allow(non_camel_case_types)]
    type P2MinN2 = <<A as Min<B>>::Output as Same<N2>>::Output;

    assert_eq!(<P2MinN2 as Integer>::to_i64(), <N2 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_P2_Max_N2() {
    type A = PInt<UInt<UInt<UTerm, B1>, B0>>;
    type B = NInt<UInt<UInt<UTerm, B1>, B0>>;
    type P2 = PInt<UInt<UInt<UTerm, B1>, B0>>;

    #[allow(non_camel_case_types)]
    type P2MaxN2 = <<A as Max<B>>::Output as Same<P2>>::Output;

    assert_eq!(<P2MaxN2 as Integer>::to_i64(), <P2 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_P2_Gcd_N2() {
    type A = PInt<UInt<UInt<UTerm, B1>, B0>>;
    type B = NInt<UInt<UInt<UTerm, B1>, B0>>;
    type P2 = PInt<UInt<UInt<UTerm, B1>, B0>>;

    #[allow(non_camel_case_types)]
    type P2GcdN2 = <<A as Gcd<B>>::Output as Same<P2>>::Output;

    assert_eq!(<P2GcdN2 as Integer>::to_i64(), <P2 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_P2_Div_N2() {
    type A = PInt<UInt<UInt<UTerm, B1>, B0>>;
    type B = NInt<UInt<UInt<UTerm, B1>, B0>>;
    type N1 = NInt<UInt<UTerm, B1>>;

    #[allow(non_camel_case_types)]
    type P2DivN2 = <<A as Div<B>>::Output as Same<N1>>::Output;

    assert_eq!(<P2DivN2 as Integer>::to_i64(), <N1 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_P2_Rem_N2() {
    type A = PInt<UInt<UInt<UTerm, B1>, B0>>;
    type B = NInt<UInt<UInt<UTerm, B1>, B0>>;
    type _0 = Z0;

    #[allow(non_camel_case_types)]
    type P2RemN2 = <<A as Rem<B>>::Output as Same<_0>>::Output;

    assert_eq!(<P2RemN2 as Integer>::to_i64(), <_0 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_P2_PartialDiv_N2() {
    type A = PInt<UInt<UInt<UTerm, B1>, B0>>;
    type B = NInt<UInt<UInt<UTerm, B1>, B0>>;
    type N1 = NInt<UInt<UTerm, B1>>;

    #[allow(non_camel_case_types)]
    type P2PartialDivN2 = <<A as PartialDiv<B>>::Output as Same<N1>>::Output;

    assert_eq!(<P2PartialDivN2 as Integer>::to_i64(), <N1 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_P2_Cmp_N2() {
    type A = PInt<UInt<UInt<UTerm, B1>, B0>>;
    type B = NInt<UInt<UInt<UTerm, B1>, B0>>;

    #[allow(non_camel_case_types)]
    type P2CmpN2 = <A as Cmp<B>>::Output;
    assert_eq!(<P2CmpN2 as Ord>::to_ordering(), Ordering::Greater);
}
#[test]
#[allow(non_snake_case)]
fn test_P2_Add_N1() {
    type A = PInt<UInt<UInt<UTerm, B1>, B0>>;
    type B = NInt<UInt<UTerm, B1>>;
    type P1 = PInt<UInt<UTerm, B1>>;

    #[allow(non_camel_case_types)]
    type P2AddN1 = <<A as Add<B>>::Output as Same<P1>>::Output;

    assert_eq!(<P2AddN1 as Integer>::to_i64(), <P1 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_P2_Sub_N1() {
    type A = PInt<UInt<UInt<UTerm, B1>, B0>>;
    type B = NInt<UInt<UTerm, B1>>;
    type P3 = PInt<UInt<UInt<UTerm, B1>, B1>>;

    #[allow(non_camel_case_types)]
    type P2SubN1 = <<A as Sub<B>>::Output as Same<P3>>::Output;

    assert_eq!(<P2SubN1 as Integer>::to_i64(), <P3 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_P2_Mul_N1() {
    type A = PInt<UInt<UInt<UTerm, B1>, B0>>;
    type B = NInt<UInt<UTerm, B1>>;
    type N2 = NInt<UInt<UInt<UTerm, B1>, B0>>;

    #[allow(non_camel_case_types)]
    type P2MulN1 = <<A as Mul<B>>::Output as Same<N2>>::Output;

    assert_eq!(<P2MulN1 as Integer>::to_i64(), <N2 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_P2_Min_N1() {
    type A = PInt<UInt<UInt<UTerm, B1>, B0>>;
    type B = NInt<UInt<UTerm, B1>>;
    type N1 = NInt<UInt<UTerm, B1>>;

    #[allow(non_camel_case_types)]
    type P2MinN1 = <<A as Min<B>>::Output as Same<N1>>::Output;

    assert_eq!(<P2MinN1 as Integer>::to_i64(), <N1 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_P2_Max_N1() {
    type A = PInt<UInt<UInt<UTerm, B1>, B0>>;
    type B = NInt<UInt<UTerm, B1>>;
    type P2 = PInt<UInt<UInt<UTerm, B1>, B0>>;

    #[allow(non_camel_case_types)]
    type P2MaxN1 = <<A as Max<B>>::Output as Same<P2>>::Output;

    assert_eq!(<P2MaxN1 as Integer>::to_i64(), <P2 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_P2_Gcd_N1() {
    type A = PInt<UInt<UInt<UTerm, B1>, B0>>;
    type B = NInt<UInt<UTerm, B1>>;
    type P1 = PInt<UInt<UTerm, B1>>;

    #[allow(non_camel_case_types)]
    type P2GcdN1 = <<A as Gcd<B>>::Output as Same<P1>>::Output;

    assert_eq!(<P2GcdN1 as Integer>::to_i64(), <P1 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_P2_Div_N1() {
    type A = PInt<UInt<UInt<UTerm, B1>, B0>>;
    type B = NInt<UInt<UTerm, B1>>;
    type N2 = NInt<UInt<UInt<UTerm, B1>, B0>>;

    #[allow(non_camel_case_types)]
    type P2DivN1 = <<A as Div<B>>::Output as Same<N2>>::Output;

    assert_eq!(<P2DivN1 as Integer>::to_i64(), <N2 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_P2_Rem_N1() {
    type A = PInt<UInt<UInt<UTerm, B1>, B0>>;
    type B = NInt<UInt<UTerm, B1>>;
    type _0 = Z0;

    #[allow(non_camel_case_types)]
    type P2RemN1 = <<A as Rem<B>>::Output as Same<_0>>::Output;

    assert_eq!(<P2RemN1 as Integer>::to_i64(), <_0 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_P2_PartialDiv_N1() {
    type A = PInt<UInt<UInt<UTerm, B1>, B0>>;
    type B = NInt<UInt<UTerm, B1>>;
    type N2 = NInt<UInt<UInt<UTerm, B1>, B0>>;

    #[allow(non_camel_case_types)]
    type P2PartialDivN1 = <<A as PartialDiv<B>>::Output as Same<N2>>::Output;

    assert_eq!(<P2PartialDivN1 as Integer>::to_i64(), <N2 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_P2_Cmp_N1() {
    type A = PInt<UInt<UInt<UTerm, B1>, B0>>;
    type B = NInt<UInt<UTerm, B1>>;

    #[allow(non_camel_case_types)]
    type P2CmpN1 = <A as Cmp<B>>::Output;
    assert_eq!(<P2CmpN1 as Ord>::to_ordering(), Ordering::Greater);
}
#[test]
#[allow(non_snake_case)]
fn test_P2_Add__0() {
    type A = PInt<UInt<UInt<UTerm, B1>, B0>>;
    type B = Z0;
    type P2 = PInt<UInt<UInt<UTerm, B1>, B0>>;

    #[allow(non_camel_case_types)]
    type P2Add_0 = <<A as Add<B>>::Output as Same<P2>>::Output;

    assert_eq!(<P2Add_0 as Integer>::to_i64(), <P2 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_P2_Sub__0() {
    type A = PInt<UInt<UInt<UTerm, B1>, B0>>;
    type B = Z0;
    type P2 = PInt<UInt<UInt<UTerm, B1>, B0>>;

    #[allow(non_camel_case_types)]
    type P2Sub_0 = <<A as Sub<B>>::Output as Same<P2>>::Output;

    assert_eq!(<P2Sub_0 as Integer>::to_i64(), <P2 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_P2_Mul__0() {
    type A = PInt<UInt<UInt<UTerm, B1>, B0>>;
    type B = Z0;
    type _0 = Z0;

    #[allow(non_camel_case_types)]
    type P2Mul_0 = <<A as Mul<B>>::Output as Same<_0>>::Output;

    assert_eq!(<P2Mul_0 as Integer>::to_i64(), <_0 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_P2_Min__0() {
    type A = PInt<UInt<UInt<UTerm, B1>, B0>>;
    type B = Z0;
    type _0 = Z0;

    #[allow(non_camel_case_types)]
    type P2Min_0 = <<A as Min<B>>::Output as Same<_0>>::Output;

    assert_eq!(<P2Min_0 as Integer>::to_i64(), <_0 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_P2_Max__0() {
    type A = PInt<UInt<UInt<UTerm, B1>, B0>>;
    type B = Z0;
    type P2 = PInt<UInt<UInt<UTerm, B1>, B0>>;

    #[allow(non_camel_case_types)]
    type P2Max_0 = <<A as Max<B>>::Output as Same<P2>>::Output;

    assert_eq!(<P2Max_0 as Integer>::to_i64(), <P2 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_P2_Gcd__0() {
    type A = PInt<UInt<UInt<UTerm, B1>, B0>>;
    type B = Z0;
    type P2 = PInt<UInt<UInt<UTerm, B1>, B0>>;

    #[allow(non_camel_case_types)]
    type P2Gcd_0 = <<A as Gcd<B>>::Output as Same<P2>>::Output;

    assert_eq!(<P2Gcd_0 as Integer>::to_i64(), <P2 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_P2_Pow__0() {
    type A = PInt<UInt<UInt<UTerm, B1>, B0>>;
    type B = Z0;
    type P1 = PInt<UInt<UTerm, B1>>;

    #[allow(non_camel_case_types)]
    type P2Pow_0 = <<A as Pow<B>>::Output as Same<P1>>::Output;

    assert_eq!(<P2Pow_0 as Integer>::to_i64(), <P1 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_P2_Cmp__0() {
    type A = PInt<UInt<UInt<UTerm, B1>, B0>>;
    type B = Z0;

    #[allow(non_camel_case_types)]
    type P2Cmp_0 = <A as Cmp<B>>::Output;
    assert_eq!(<P2Cmp_0 as Ord>::to_ordering(), Ordering::Greater);
}
#[test]
#[allow(non_snake_case)]
fn test_P2_Add_P1() {
    type A = PInt<UInt<UInt<UTerm, B1>, B0>>;
    type B = PInt<UInt<UTerm, B1>>;
    type P3 = PInt<UInt<UInt<UTerm, B1>, B1>>;

    #[allow(non_camel_case_types)]
    type P2AddP1 = <<A as Add<B>>::Output as Same<P3>>::Output;

    assert_eq!(<P2AddP1 as Integer>::to_i64(), <P3 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_P2_Sub_P1() {
    type A = PInt<UInt<UInt<UTerm, B1>, B0>>;
    type B = PInt<UInt<UTerm, B1>>;
    type P1 = PInt<UInt<UTerm, B1>>;

    #[allow(non_camel_case_types)]
    type P2SubP1 = <<A as Sub<B>>::Output as Same<P1>>::Output;

    assert_eq!(<P2SubP1 as Integer>::to_i64(), <P1 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_P2_Mul_P1() {
    type A = PInt<UInt<UInt<UTerm, B1>, B0>>;
    type B = PInt<UInt<UTerm, B1>>;
    type P2 = PInt<UInt<UInt<UTerm, B1>, B0>>;

    #[allow(non_camel_case_types)]
    type P2MulP1 = <<A as Mul<B>>::Output as Same<P2>>::Output;

    assert_eq!(<P2MulP1 as Integer>::to_i64(), <P2 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_P2_Min_P1() {
    type A = PInt<UInt<UInt<UTerm, B1>, B0>>;
    type B = PInt<UInt<UTerm, B1>>;
    type P1 = PInt<UInt<UTerm, B1>>;

    #[allow(non_camel_case_types)]
    type P2MinP1 = <<A as Min<B>>::Output as Same<P1>>::Output;

    assert_eq!(<P2MinP1 as Integer>::to_i64(), <P1 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_P2_Max_P1() {
    type A = PInt<UInt<UInt<UTerm, B1>, B0>>;
    type B = PInt<UInt<UTerm, B1>>;
    type P2 = PInt<UInt<UInt<UTerm, B1>, B0>>;

    #[allow(non_camel_case_types)]
    type P2MaxP1 = <<A as Max<B>>::Output as Same<P2>>::Output;

    assert_eq!(<P2MaxP1 as Integer>::to_i64(), <P2 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_P2_Gcd_P1() {
    type A = PInt<UInt<UInt<UTerm, B1>, B0>>;
    type B = PInt<UInt<UTerm, B1>>;
    type P1 = PInt<UInt<UTerm, B1>>;

    #[allow(non_camel_case_types)]
    type P2GcdP1 = <<A as Gcd<B>>::Output as Same<P1>>::Output;

    assert_eq!(<P2GcdP1 as Integer>::to_i64(), <P1 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_P2_Div_P1() {
    type A = PInt<UInt<UInt<UTerm, B1>, B0>>;
    type B = PInt<UInt<UTerm, B1>>;
    type P2 = PInt<UInt<UInt<UTerm, B1>, B0>>;

    #[allow(non_camel_case_types)]
    type P2DivP1 = <<A as Div<B>>::Output as Same<P2>>::Output;

    assert_eq!(<P2DivP1 as Integer>::to_i64(), <P2 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_P2_Rem_P1() {
    type A = PInt<UInt<UInt<UTerm, B1>, B0>>;
    type B = PInt<UInt<UTerm, B1>>;
    type _0 = Z0;

    #[allow(non_camel_case_types)]
    type P2RemP1 = <<A as Rem<B>>::Output as Same<_0>>::Output;

    assert_eq!(<P2RemP1 as Integer>::to_i64(), <_0 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_P2_PartialDiv_P1() {
    type A = PInt<UInt<UInt<UTerm, B1>, B0>>;
    type B = PInt<UInt<UTerm, B1>>;
    type P2 = PInt<UInt<UInt<UTerm, B1>, B0>>;

    #[allow(non_camel_case_types)]
    type P2PartialDivP1 = <<A as PartialDiv<B>>::Output as Same<P2>>::Output;

    assert_eq!(<P2PartialDivP1 as Integer>::to_i64(), <P2 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_P2_Pow_P1() {
    type A = PInt<UInt<UInt<UTerm, B1>, B0>>;
    type B = PInt<UInt<UTerm, B1>>;
    type P2 = PInt<UInt<UInt<UTerm, B1>, B0>>;

    #[allow(non_camel_case_types)]
    type P2PowP1 = <<A as Pow<B>>::Output as Same<P2>>::Output;

    assert_eq!(<P2PowP1 as Integer>::to_i64(), <P2 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_P2_Cmp_P1() {
    type A = PInt<UInt<UInt<UTerm, B1>, B0>>;
    type B = PInt<UInt<UTerm, B1>>;

    #[allow(non_camel_case_types)]
    type P2CmpP1 = <A as Cmp<B>>::Output;
    assert_eq!(<P2CmpP1 as Ord>::to_ordering(), Ordering::Greater);
}
#[test]
#[allow(non_snake_case)]
fn test_P2_Add_P2() {
    type A = PInt<UInt<UInt<UTerm, B1>, B0>>;
    type B = PInt<UInt<UInt<UTerm, B1>, B0>>;
    type P4 = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>>;

    #[allow(non_camel_case_types)]
    type P2AddP2 = <<A as Add<B>>::Output as Same<P4>>::Output;

    assert_eq!(<P2AddP2 as Integer>::to_i64(), <P4 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_P2_Sub_P2() {
    type A = PInt<UInt<UInt<UTerm, B1>, B0>>;
    type B = PInt<UInt<UInt<UTerm, B1>, B0>>;
    type _0 = Z0;

    #[allow(non_camel_case_types)]
    type P2SubP2 = <<A as Sub<B>>::Output as Same<_0>>::Output;

    assert_eq!(<P2SubP2 as Integer>::to_i64(), <_0 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_P2_Mul_P2() {
    type A = PInt<UInt<UInt<UTerm, B1>, B0>>;
    type B = PInt<UInt<UInt<UTerm, B1>, B0>>;
    type P4 = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>>;

    #[allow(non_camel_case_types)]
    type P2MulP2 = <<A as Mul<B>>::Output as Same<P4>>::Output;

    assert_eq!(<P2MulP2 as Integer>::to_i64(), <P4 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_P2_Min_P2() {
    type A = PInt<UInt<UInt<UTerm, B1>, B0>>;
    type B = PInt<UInt<UInt<UTerm, B1>, B0>>;
    type P2 = PInt<UInt<UInt<UTerm, B1>, B0>>;

    #[allow(non_camel_case_types)]
    type P2MinP2 = <<A as Min<B>>::Output as Same<P2>>::Output;

    assert_eq!(<P2MinP2 as Integer>::to_i64(), <P2 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_P2_Max_P2() {
    type A = PInt<UInt<UInt<UTerm, B1>, B0>>;
    type B = PInt<UInt<UInt<UTerm, B1>, B0>>;
    type P2 = PInt<UInt<UInt<UTerm, B1>, B0>>;

    #[allow(non_camel_case_types)]
    type P2MaxP2 = <<A as Max<B>>::Output as Same<P2>>::Output;

    assert_eq!(<P2MaxP2 as Integer>::to_i64(), <P2 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_P2_Gcd_P2() {
    type A = PInt<UInt<UInt<UTerm, B1>, B0>>;
    type B = PInt<UInt<UInt<UTerm, B1>, B0>>;
    type P2 = PInt<UInt<UInt<UTerm, B1>, B0>>;

    #[allow(non_camel_case_types)]
    type P2GcdP2 = <<A as Gcd<B>>::Output as Same<P2>>::Output;

    assert_eq!(<P2GcdP2 as Integer>::to_i64(), <P2 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_P2_Div_P2() {
    type A = PInt<UInt<UInt<UTerm, B1>, B0>>;
    type B = PInt<UInt<UInt<UTerm, B1>, B0>>;
    type P1 = PInt<UInt<UTerm, B1>>;

    #[allow(non_camel_case_types)]
    type P2DivP2 = <<A as Div<B>>::Output as Same<P1>>::Output;

    assert_eq!(<P2DivP2 as Integer>::to_i64(), <P1 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_P2_Rem_P2() {
    type A = PInt<UInt<UInt<UTerm, B1>, B0>>;
    type B = PInt<UInt<UInt<UTerm, B1>, B0>>;
    type _0 = Z0;

    #[allow(non_camel_case_types)]
    type P2RemP2 = <<A as Rem<B>>::Output as Same<_0>>::Output;

    assert_eq!(<P2RemP2 as Integer>::to_i64(), <_0 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_P2_PartialDiv_P2() {
    type A = PInt<UInt<UInt<UTerm, B1>, B0>>;
    type B = PInt<UInt<UInt<UTerm, B1>, B0>>;
    type P1 = PInt<UInt<UTerm, B1>>;

    #[allow(non_camel_case_types)]
    type P2PartialDivP2 = <<A as PartialDiv<B>>::Output as Same<P1>>::Output;

    assert_eq!(<P2PartialDivP2 as Integer>::to_i64(), <P1 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_P2_Pow_P2() {
    type A = PInt<UInt<UInt<UTerm, B1>, B0>>;
    type B = PInt<UInt<UInt<UTerm, B1>, B0>>;
    type P4 = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>>;

    #[allow(non_camel_case_types)]
    type P2PowP2 = <<A as Pow<B>>::Output as Same<P4>>::Output;

    assert_eq!(<P2PowP2 as Integer>::to_i64(), <P4 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_P2_Cmp_P2() {
    type A = PInt<UInt<UInt<UTerm, B1>, B0>>;
    type B = PInt<UInt<UInt<UTerm, B1>, B0>>;

    #[allow(non_camel_case_types)]
    type P2CmpP2 = <A as Cmp<B>>::Output;
    assert_eq!(<P2CmpP2 as Ord>::to_ordering(), Ordering::Equal);
}
#[test]
#[allow(non_snake_case)]
fn test_P2_Add_P3() {
    type A = PInt<UInt<UInt<UTerm, B1>, B0>>;
    type B = PInt<UInt<UInt<UTerm, B1>, B1>>;
    type P5 = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>>;

    #[allow(non_camel_case_types)]
    type P2AddP3 = <<A as Add<B>>::Output as Same<P5>>::Output;

    assert_eq!(<P2AddP3 as Integer>::to_i64(), <P5 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_P2_Sub_P3() {
    type A = PInt<UInt<UInt<UTerm, B1>, B0>>;
    type B = PInt<UInt<UInt<UTerm, B1>, B1>>;
    type N1 = NInt<UInt<UTerm, B1>>;

    #[allow(non_camel_case_types)]
    type P2SubP3 = <<A as Sub<B>>::Output as Same<N1>>::Output;

    assert_eq!(<P2SubP3 as Integer>::to_i64(), <N1 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_P2_Mul_P3() {
    type A = PInt<UInt<UInt<UTerm, B1>, B0>>;
    type B = PInt<UInt<UInt<UTerm, B1>, B1>>;
    type P6 = PInt<UInt<UInt<UInt<UTerm, B1>, B1>, B0>>;

    #[allow(non_camel_case_types)]
    type P2MulP3 = <<A as Mul<B>>::Output as Same<P6>>::Output;

    assert_eq!(<P2MulP3 as Integer>::to_i64(), <P6 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_P2_Min_P3() {
    type A = PInt<UInt<UInt<UTerm, B1>, B0>>;
    type B = PInt<UInt<UInt<UTerm, B1>, B1>>;
    type P2 = PInt<UInt<UInt<UTerm, B1>, B0>>;

    #[allow(non_camel_case_types)]
    type P2MinP3 = <<A as Min<B>>::Output as Same<P2>>::Output;

    assert_eq!(<P2MinP3 as Integer>::to_i64(), <P2 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_P2_Max_P3() {
    type A = PInt<UInt<UInt<UTerm, B1>, B0>>;
    type B = PInt<UInt<UInt<UTerm, B1>, B1>>;
    type P3 = PInt<UInt<UInt<UTerm, B1>, B1>>;

    #[allow(non_camel_case_types)]
    type P2MaxP3 = <<A as Max<B>>::Output as Same<P3>>::Output;

    assert_eq!(<P2MaxP3 as Integer>::to_i64(), <P3 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_P2_Gcd_P3() {
    type A = PInt<UInt<UInt<UTerm, B1>, B0>>;
    type B = PInt<UInt<UInt<UTerm, B1>, B1>>;
    type P1 = PInt<UInt<UTerm, B1>>;

    #[allow(non_camel_case_types)]
    type P2GcdP3 = <<A as Gcd<B>>::Output as Same<P1>>::Output;

    assert_eq!(<P2GcdP3 as Integer>::to_i64(), <P1 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_P2_Div_P3() {
    type A = PInt<UInt<UInt<UTerm, B1>, B0>>;
    type B = PInt<UInt<UInt<UTerm, B1>, B1>>;
    type _0 = Z0;

    #[allow(non_camel_case_types)]
    type P2DivP3 = <<A as Div<B>>::Output as Same<_0>>::Output;

    assert_eq!(<P2DivP3 as Integer>::to_i64(), <_0 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_P2_Rem_P3() {
    type A = PInt<UInt<UInt<UTerm, B1>, B0>>;
    type B = PInt<UInt<UInt<UTerm, B1>, B1>>;
    type P2 = PInt<UInt<UInt<UTerm, B1>, B0>>;

    #[allow(non_camel_case_types)]
    type P2RemP3 = <<A as Rem<B>>::Output as Same<P2>>::Output;

    assert_eq!(<P2RemP3 as Integer>::to_i64(), <P2 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_P2_Pow_P3() {
    type A = PInt<UInt<UInt<UTerm, B1>, B0>>;
    type B = PInt<UInt<UInt<UTerm, B1>, B1>>;
    type P8 = PInt<UInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>, B0>>;

    #[allow(non_camel_case_types)]
    type P2PowP3 = <<A as Pow<B>>::Output as Same<P8>>::Output;

    assert_eq!(<P2PowP3 as Integer>::to_i64(), <P8 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_P2_Cmp_P3() {
    type A = PInt<UInt<UInt<UTerm, B1>, B0>>;
    type B = PInt<UInt<UInt<UTerm, B1>, B1>>;

    #[allow(non_camel_case_types)]
    type P2CmpP3 = <A as Cmp<B>>::Output;
    assert_eq!(<P2CmpP3 as Ord>::to_ordering(), Ordering::Less);
}
#[test]
#[allow(non_snake_case)]
fn test_P2_Add_P4() {
    type A = PInt<UInt<UInt<UTerm, B1>, B0>>;
    type B = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>>;
    type P6 = PInt<UInt<UInt<UInt<UTerm, B1>, B1>, B0>>;

    #[allow(non_camel_case_types)]
    type P2AddP4 = <<A as Add<B>>::Output as Same<P6>>::Output;

    assert_eq!(<P2AddP4 as Integer>::to_i64(), <P6 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_P2_Sub_P4() {
    type A = PInt<UInt<UInt<UTerm, B1>, B0>>;
    type B = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>>;
    type N2 = NInt<UInt<UInt<UTerm, B1>, B0>>;

    #[allow(non_camel_case_types)]
    type P2SubP4 = <<A as Sub<B>>::Output as Same<N2>>::Output;

    assert_eq!(<P2SubP4 as Integer>::to_i64(), <N2 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_P2_Mul_P4() {
    type A = PInt<UInt<UInt<UTerm, B1>, B0>>;
    type B = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>>;
    type P8 = PInt<UInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>, B0>>;

    #[allow(non_camel_case_types)]
    type P2MulP4 = <<A as Mul<B>>::Output as Same<P8>>::Output;

    assert_eq!(<P2MulP4 as Integer>::to_i64(), <P8 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_P2_Min_P4() {
    type A = PInt<UInt<UInt<UTerm, B1>, B0>>;
    type B = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>>;
    type P2 = PInt<UInt<UInt<UTerm, B1>, B0>>;

    #[allow(non_camel_case_types)]
    type P2MinP4 = <<A as Min<B>>::Output as Same<P2>>::Output;

    assert_eq!(<P2MinP4 as Integer>::to_i64(), <P2 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_P2_Max_P4() {
    type A = PInt<UInt<UInt<UTerm, B1>, B0>>;
    type B = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>>;
    type P4 = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>>;

    #[allow(non_camel_case_types)]
    type P2MaxP4 = <<A as Max<B>>::Output as Same<P4>>::Output;

    assert_eq!(<P2MaxP4 as Integer>::to_i64(), <P4 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_P2_Gcd_P4() {
    type A = PInt<UInt<UInt<UTerm, B1>, B0>>;
    type B = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>>;
    type P2 = PInt<UInt<UInt<UTerm, B1>, B0>>;

    #[allow(non_camel_case_types)]
    type P2GcdP4 = <<A as Gcd<B>>::Output as Same<P2>>::Output;

    assert_eq!(<P2GcdP4 as Integer>::to_i64(), <P2 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_P2_Div_P4() {
    type A = PInt<UInt<UInt<UTerm, B1>, B0>>;
    type B = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>>;
    type _0 = Z0;

    #[allow(non_camel_case_types)]
    type P2DivP4 = <<A as Div<B>>::Output as Same<_0>>::Output;

    assert_eq!(<P2DivP4 as Integer>::to_i64(), <_0 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_P2_Rem_P4() {
    type A = PInt<UInt<UInt<UTerm, B1>, B0>>;
    type B = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>>;
    type P2 = PInt<UInt<UInt<UTerm, B1>, B0>>;

    #[allow(non_camel_case_types)]
    type P2RemP4 = <<A as Rem<B>>::Output as Same<P2>>::Output;

    assert_eq!(<P2RemP4 as Integer>::to_i64(), <P2 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_P2_Pow_P4() {
    type A = PInt<UInt<UInt<UTerm, B1>, B0>>;
    type B = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>>;
    type P16 = PInt<UInt<UInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>, B0>, B0>>;

    #[allow(non_camel_case_types)]
    type P2PowP4 = <<A as Pow<B>>::Output as Same<P16>>::Output;

    assert_eq!(<P2PowP4 as Integer>::to_i64(), <P16 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_P2_Cmp_P4() {
    type A = PInt<UInt<UInt<UTerm, B1>, B0>>;
    type B = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>>;

    #[allow(non_camel_case_types)]
    type P2CmpP4 = <A as Cmp<B>>::Output;
    assert_eq!(<P2CmpP4 as Ord>::to_ordering(), Ordering::Less);
}
#[test]
#[allow(non_snake_case)]
fn test_P2_Add_P5() {
    type A = PInt<UInt<UInt<UTerm, B1>, B0>>;
    type B = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>>;
    type P7 = PInt<UInt<UInt<UInt<UTerm, B1>, B1>, B1>>;

    #[allow(non_camel_case_types)]
    type P2AddP5 = <<A as Add<B>>::Output as Same<P7>>::Output;

    assert_eq!(<P2AddP5 as Integer>::to_i64(), <P7 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_P2_Sub_P5() {
    type A = PInt<UInt<UInt<UTerm, B1>, B0>>;
    type B = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>>;
    type N3 = NInt<UInt<UInt<UTerm, B1>, B1>>;

    #[allow(non_camel_case_types)]
    type P2SubP5 = <<A as Sub<B>>::Output as Same<N3>>::Output;

    assert_eq!(<P2SubP5 as Integer>::to_i64(), <N3 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_P2_Mul_P5() {
    type A = PInt<UInt<UInt<UTerm, B1>, B0>>;
    type B = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>>;
    type P10 = PInt<UInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>, B0>>;

    #[allow(non_camel_case_types)]
    type P2MulP5 = <<A as Mul<B>>::Output as Same<P10>>::Output;

    assert_eq!(<P2MulP5 as Integer>::to_i64(), <P10 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_P2_Min_P5() {
    type A = PInt<UInt<UInt<UTerm, B1>, B0>>;
    type B = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>>;
    type P2 = PInt<UInt<UInt<UTerm, B1>, B0>>;

    #[allow(non_camel_case_types)]
    type P2MinP5 = <<A as Min<B>>::Output as Same<P2>>::Output;

    assert_eq!(<P2MinP5 as Integer>::to_i64(), <P2 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_P2_Max_P5() {
    type A = PInt<UInt<UInt<UTerm, B1>, B0>>;
    type B = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>>;
    type P5 = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>>;

    #[allow(non_camel_case_types)]
    type P2MaxP5 = <<A as Max<B>>::Output as Same<P5>>::Output;

    assert_eq!(<P2MaxP5 as Integer>::to_i64(), <P5 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_P2_Gcd_P5() {
    type A = PInt<UInt<UInt<UTerm, B1>, B0>>;
    type B = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>>;
    type P1 = PInt<UInt<UTerm, B1>>;

    #[allow(non_camel_case_types)]
    type P2GcdP5 = <<A as Gcd<B>>::Output as Same<P1>>::Output;

    assert_eq!(<P2GcdP5 as Integer>::to_i64(), <P1 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_P2_Div_P5() {
    type A = PInt<UInt<UInt<UTerm, B1>, B0>>;
    type B = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>>;
    type _0 = Z0;

    #[allow(non_camel_case_types)]
    type P2DivP5 = <<A as Div<B>>::Output as Same<_0>>::Output;

    assert_eq!(<P2DivP5 as Integer>::to_i64(), <_0 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_P2_Rem_P5() {
    type A = PInt<UInt<UInt<UTerm, B1>, B0>>;
    type B = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>>;
    type P2 = PInt<UInt<UInt<UTerm, B1>, B0>>;

    #[allow(non_camel_case_types)]
    type P2RemP5 = <<A as Rem<B>>::Output as Same<P2>>::Output;

    assert_eq!(<P2RemP5 as Integer>::to_i64(), <P2 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_P2_Pow_P5() {
    type A = PInt<UInt<UInt<UTerm, B1>, B0>>;
    type B = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>>;
    type P32 = PInt<UInt<UInt<UInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>, B0>, B0>, B0>>;

    #[allow(non_camel_case_types)]
    type P2PowP5 = <<A as Pow<B>>::Output as Same<P32>>::Output;

    assert_eq!(<P2PowP5 as Integer>::to_i64(), <P32 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_P2_Cmp_P5() {
    type A = PInt<UInt<UInt<UTerm, B1>, B0>>;
    type B = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>>;

    #[allow(non_camel_case_types)]
    type P2CmpP5 = <A as Cmp<B>>::Output;
    assert_eq!(<P2CmpP5 as Ord>::to_ordering(), Ordering::Less);
}
#[test]
#[allow(non_snake_case)]
fn test_P3_Add_N5() {
    type A = PInt<UInt<UInt<UTerm, B1>, B1>>;
    type B = NInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>>;
    type N2 = NInt<UInt<UInt<UTerm, B1>, B0>>;

    #[allow(non_camel_case_types)]
    type P3AddN5 = <<A as Add<B>>::Output as Same<N2>>::Output;

    assert_eq!(<P3AddN5 as Integer>::to_i64(), <N2 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_P3_Sub_N5() {
    type A = PInt<UInt<UInt<UTerm, B1>, B1>>;
    type B = NInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>>;
    type P8 = PInt<UInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>, B0>>;

    #[allow(non_camel_case_types)]
    type P3SubN5 = <<A as Sub<B>>::Output as Same<P8>>::Output;

    assert_eq!(<P3SubN5 as Integer>::to_i64(), <P8 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_P3_Mul_N5() {
    type A = PInt<UInt<UInt<UTerm, B1>, B1>>;
    type B = NInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>>;
    type N15 = NInt<UInt<UInt<UInt<UInt<UTerm, B1>, B1>, B1>, B1>>;

    #[allow(non_camel_case_types)]
    type P3MulN5 = <<A as Mul<B>>::Output as Same<N15>>::Output;

    assert_eq!(<P3MulN5 as Integer>::to_i64(), <N15 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_P3_Min_N5() {
    type A = PInt<UInt<UInt<UTerm, B1>, B1>>;
    type B = NInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>>;
    type N5 = NInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>>;

    #[allow(non_camel_case_types)]
    type P3MinN5 = <<A as Min<B>>::Output as Same<N5>>::Output;

    assert_eq!(<P3MinN5 as Integer>::to_i64(), <N5 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_P3_Max_N5() {
    type A = PInt<UInt<UInt<UTerm, B1>, B1>>;
    type B = NInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>>;
    type P3 = PInt<UInt<UInt<UTerm, B1>, B1>>;

    #[allow(non_camel_case_types)]
    type P3MaxN5 = <<A as Max<B>>::Output as Same<P3>>::Output;

    assert_eq!(<P3MaxN5 as Integer>::to_i64(), <P3 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_P3_Gcd_N5() {
    type A = PInt<UInt<UInt<UTerm, B1>, B1>>;
    type B = NInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>>;
    type P1 = PInt<UInt<UTerm, B1>>;

    #[allow(non_camel_case_types)]
    type P3GcdN5 = <<A as Gcd<B>>::Output as Same<P1>>::Output;

    assert_eq!(<P3GcdN5 as Integer>::to_i64(), <P1 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_P3_Div_N5() {
    type A = PInt<UInt<UInt<UTerm, B1>, B1>>;
    type B = NInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>>;
    type _0 = Z0;

    #[allow(non_camel_case_types)]
    type P3DivN5 = <<A as Div<B>>::Output as Same<_0>>::Output;

    assert_eq!(<P3DivN5 as Integer>::to_i64(), <_0 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_P3_Rem_N5() {
    type A = PInt<UInt<UInt<UTerm, B1>, B1>>;
    type B = NInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>>;
    type P3 = PInt<UInt<UInt<UTerm, B1>, B1>>;

    #[allow(non_camel_case_types)]
    type P3RemN5 = <<A as Rem<B>>::Output as Same<P3>>::Output;

    assert_eq!(<P3RemN5 as Integer>::to_i64(), <P3 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_P3_Cmp_N5() {
    type A = PInt<UInt<UInt<UTerm, B1>, B1>>;
    type B = NInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>>;

    #[allow(non_camel_case_types)]
    type P3CmpN5 = <A as Cmp<B>>::Output;
    assert_eq!(<P3CmpN5 as Ord>::to_ordering(), Ordering::Greater);
}
#[test]
#[allow(non_snake_case)]
fn test_P3_Add_N4() {
    type A = PInt<UInt<UInt<UTerm, B1>, B1>>;
    type B = NInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>>;
    type N1 = NInt<UInt<UTerm, B1>>;

    #[allow(non_camel_case_types)]
    type P3AddN4 = <<A as Add<B>>::Output as Same<N1>>::Output;

    assert_eq!(<P3AddN4 as Integer>::to_i64(), <N1 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_P3_Sub_N4() {
    type A = PInt<UInt<UInt<UTerm, B1>, B1>>;
    type B = NInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>>;
    type P7 = PInt<UInt<UInt<UInt<UTerm, B1>, B1>, B1>>;

    #[allow(non_camel_case_types)]
    type P3SubN4 = <<A as Sub<B>>::Output as Same<P7>>::Output;

    assert_eq!(<P3SubN4 as Integer>::to_i64(), <P7 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_P3_Mul_N4() {
    type A = PInt<UInt<UInt<UTerm, B1>, B1>>;
    type B = NInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>>;
    type N12 = NInt<UInt<UInt<UInt<UInt<UTerm, B1>, B1>, B0>, B0>>;

    #[allow(non_camel_case_types)]
    type P3MulN4 = <<A as Mul<B>>::Output as Same<N12>>::Output;

    assert_eq!(<P3MulN4 as Integer>::to_i64(), <N12 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_P3_Min_N4() {
    type A = PInt<UInt<UInt<UTerm, B1>, B1>>;
    type B = NInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>>;
    type N4 = NInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>>;

    #[allow(non_camel_case_types)]
    type P3MinN4 = <<A as Min<B>>::Output as Same<N4>>::Output;

    assert_eq!(<P3MinN4 as Integer>::to_i64(), <N4 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_P3_Max_N4() {
    type A = PInt<UInt<UInt<UTerm, B1>, B1>>;
    type B = NInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>>;
    type P3 = PInt<UInt<UInt<UTerm, B1>, B1>>;

    #[allow(non_camel_case_types)]
    type P3MaxN4 = <<A as Max<B>>::Output as Same<P3>>::Output;

    assert_eq!(<P3MaxN4 as Integer>::to_i64(), <P3 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_P3_Gcd_N4() {
    type A = PInt<UInt<UInt<UTerm, B1>, B1>>;
    type B = NInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>>;
    type P1 = PInt<UInt<UTerm, B1>>;

    #[allow(non_camel_case_types)]
    type P3GcdN4 = <<A as Gcd<B>>::Output as Same<P1>>::Output;

    assert_eq!(<P3GcdN4 as Integer>::to_i64(), <P1 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_P3_Div_N4() {
    type A = PInt<UInt<UInt<UTerm, B1>, B1>>;
    type B = NInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>>;
    type _0 = Z0;

    #[allow(non_camel_case_types)]
    type P3DivN4 = <<A as Div<B>>::Output as Same<_0>>::Output;

    assert_eq!(<P3DivN4 as Integer>::to_i64(), <_0 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_P3_Rem_N4() {
    type A = PInt<UInt<UInt<UTerm, B1>, B1>>;
    type B = NInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>>;
    type P3 = PInt<UInt<UInt<UTerm, B1>, B1>>;

    #[allow(non_camel_case_types)]
    type P3RemN4 = <<A as Rem<B>>::Output as Same<P3>>::Output;

    assert_eq!(<P3RemN4 as Integer>::to_i64(), <P3 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_P3_Cmp_N4() {
    type A = PInt<UInt<UInt<UTerm, B1>, B1>>;
    type B = NInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>>;

    #[allow(non_camel_case_types)]
    type P3CmpN4 = <A as Cmp<B>>::Output;
    assert_eq!(<P3CmpN4 as Ord>::to_ordering(), Ordering::Greater);
}
#[test]
#[allow(non_snake_case)]
fn test_P3_Add_N3() {
    type A = PInt<UInt<UInt<UTerm, B1>, B1>>;
    type B = NInt<UInt<UInt<UTerm, B1>, B1>>;
    type _0 = Z0;

    #[allow(non_camel_case_types)]
    type P3AddN3 = <<A as Add<B>>::Output as Same<_0>>::Output;

    assert_eq!(<P3AddN3 as Integer>::to_i64(), <_0 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_P3_Sub_N3() {
    type A = PInt<UInt<UInt<UTerm, B1>, B1>>;
    type B = NInt<UInt<UInt<UTerm, B1>, B1>>;
    type P6 = PInt<UInt<UInt<UInt<UTerm, B1>, B1>, B0>>;

    #[allow(non_camel_case_types)]
    type P3SubN3 = <<A as Sub<B>>::Output as Same<P6>>::Output;

    assert_eq!(<P3SubN3 as Integer>::to_i64(), <P6 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_P3_Mul_N3() {
    type A = PInt<UInt<UInt<UTerm, B1>, B1>>;
    type B = NInt<UInt<UInt<UTerm, B1>, B1>>;
    type N9 = NInt<UInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>, B1>>;

    #[allow(non_camel_case_types)]
    type P3MulN3 = <<A as Mul<B>>::Output as Same<N9>>::Output;

    assert_eq!(<P3MulN3 as Integer>::to_i64(), <N9 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_P3_Min_N3() {
    type A = PInt<UInt<UInt<UTerm, B1>, B1>>;
    type B = NInt<UInt<UInt<UTerm, B1>, B1>>;
    type N3 = NInt<UInt<UInt<UTerm, B1>, B1>>;

    #[allow(non_camel_case_types)]
    type P3MinN3 = <<A as Min<B>>::Output as Same<N3>>::Output;

    assert_eq!(<P3MinN3 as Integer>::to_i64(), <N3 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_P3_Max_N3() {
    type A = PInt<UInt<UInt<UTerm, B1>, B1>>;
    type B = NInt<UInt<UInt<UTerm, B1>, B1>>;
    type P3 = PInt<UInt<UInt<UTerm, B1>, B1>>;

    #[allow(non_camel_case_types)]
    type P3MaxN3 = <<A as Max<B>>::Output as Same<P3>>::Output;

    assert_eq!(<P3MaxN3 as Integer>::to_i64(), <P3 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_P3_Gcd_N3() {
    type A = PInt<UInt<UInt<UTerm, B1>, B1>>;
    type B = NInt<UInt<UInt<UTerm, B1>, B1>>;
    type P3 = PInt<UInt<UInt<UTerm, B1>, B1>>;

    #[allow(non_camel_case_types)]
    type P3GcdN3 = <<A as Gcd<B>>::Output as Same<P3>>::Output;

    assert_eq!(<P3GcdN3 as Integer>::to_i64(), <P3 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_P3_Div_N3() {
    type A = PInt<UInt<UInt<UTerm, B1>, B1>>;
    type B = NInt<UInt<UInt<UTerm, B1>, B1>>;
    type N1 = NInt<UInt<UTerm, B1>>;

    #[allow(non_camel_case_types)]
    type P3DivN3 = <<A as Div<B>>::Output as Same<N1>>::Output;

    assert_eq!(<P3DivN3 as Integer>::to_i64(), <N1 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_P3_Rem_N3() {
    type A = PInt<UInt<UInt<UTerm, B1>, B1>>;
    type B = NInt<UInt<UInt<UTerm, B1>, B1>>;
    type _0 = Z0;

    #[allow(non_camel_case_types)]
    type P3RemN3 = <<A as Rem<B>>::Output as Same<_0>>::Output;

    assert_eq!(<P3RemN3 as Integer>::to_i64(), <_0 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_P3_PartialDiv_N3() {
    type A = PInt<UInt<UInt<UTerm, B1>, B1>>;
    type B = NInt<UInt<UInt<UTerm, B1>, B1>>;
    type N1 = NInt<UInt<UTerm, B1>>;

    #[allow(non_camel_case_types)]
    type P3PartialDivN3 = <<A as PartialDiv<B>>::Output as Same<N1>>::Output;

    assert_eq!(<P3PartialDivN3 as Integer>::to_i64(), <N1 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_P3_Cmp_N3() {
    type A = PInt<UInt<UInt<UTerm, B1>, B1>>;
    type B = NInt<UInt<UInt<UTerm, B1>, B1>>;

    #[allow(non_camel_case_types)]
    type P3CmpN3 = <A as Cmp<B>>::Output;
    assert_eq!(<P3CmpN3 as Ord>::to_ordering(), Ordering::Greater);
}
#[test]
#[allow(non_snake_case)]
fn test_P3_Add_N2() {
    type A = PInt<UInt<UInt<UTerm, B1>, B1>>;
    type B = NInt<UInt<UInt<UTerm, B1>, B0>>;
    type P1 = PInt<UInt<UTerm, B1>>;

    #[allow(non_camel_case_types)]
    type P3AddN2 = <<A as Add<B>>::Output as Same<P1>>::Output;

    assert_eq!(<P3AddN2 as Integer>::to_i64(), <P1 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_P3_Sub_N2() {
    type A = PInt<UInt<UInt<UTerm, B1>, B1>>;
    type B = NInt<UInt<UInt<UTerm, B1>, B0>>;
    type P5 = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>>;

    #[allow(non_camel_case_types)]
    type P3SubN2 = <<A as Sub<B>>::Output as Same<P5>>::Output;

    assert_eq!(<P3SubN2 as Integer>::to_i64(), <P5 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_P3_Mul_N2() {
    type A = PInt<UInt<UInt<UTerm, B1>, B1>>;
    type B = NInt<UInt<UInt<UTerm, B1>, B0>>;
    type N6 = NInt<UInt<UInt<UInt<UTerm, B1>, B1>, B0>>;

    #[allow(non_camel_case_types)]
    type P3MulN2 = <<A as Mul<B>>::Output as Same<N6>>::Output;

    assert_eq!(<P3MulN2 as Integer>::to_i64(), <N6 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_P3_Min_N2() {
    type A = PInt<UInt<UInt<UTerm, B1>, B1>>;
    type B = NInt<UInt<UInt<UTerm, B1>, B0>>;
    type N2 = NInt<UInt<UInt<UTerm, B1>, B0>>;

    #[allow(non_camel_case_types)]
    type P3MinN2 = <<A as Min<B>>::Output as Same<N2>>::Output;

    assert_eq!(<P3MinN2 as Integer>::to_i64(), <N2 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_P3_Max_N2() {
    type A = PInt<UInt<UInt<UTerm, B1>, B1>>;
    type B = NInt<UInt<UInt<UTerm, B1>, B0>>;
    type P3 = PInt<UInt<UInt<UTerm, B1>, B1>>;

    #[allow(non_camel_case_types)]
    type P3MaxN2 = <<A as Max<B>>::Output as Same<P3>>::Output;

    assert_eq!(<P3MaxN2 as Integer>::to_i64(), <P3 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_P3_Gcd_N2() {
    type A = PInt<UInt<UInt<UTerm, B1>, B1>>;
    type B = NInt<UInt<UInt<UTerm, B1>, B0>>;
    type P1 = PInt<UInt<UTerm, B1>>;

    #[allow(non_camel_case_types)]
    type P3GcdN2 = <<A as Gcd<B>>::Output as Same<P1>>::Output;

    assert_eq!(<P3GcdN2 as Integer>::to_i64(), <P1 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_P3_Div_N2() {
    type A = PInt<UInt<UInt<UTerm, B1>, B1>>;
    type B = NInt<UInt<UInt<UTerm, B1>, B0>>;
    type N1 = NInt<UInt<UTerm, B1>>;

    #[allow(non_camel_case_types)]
    type P3DivN2 = <<A as Div<B>>::Output as Same<N1>>::Output;

    assert_eq!(<P3DivN2 as Integer>::to_i64(), <N1 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_P3_Rem_N2() {
    type A = PInt<UInt<UInt<UTerm, B1>, B1>>;
    type B = NInt<UInt<UInt<UTerm, B1>, B0>>;
    type P1 = PInt<UInt<UTerm, B1>>;

    #[allow(non_camel_case_types)]
    type P3RemN2 = <<A as Rem<B>>::Output as Same<P1>>::Output;

    assert_eq!(<P3RemN2 as Integer>::to_i64(), <P1 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_P3_Cmp_N2() {
    type A = PInt<UInt<UInt<UTerm, B1>, B1>>;
    type B = NInt<UInt<UInt<UTerm, B1>, B0>>;

    #[allow(non_camel_case_types)]
    type P3CmpN2 = <A as Cmp<B>>::Output;
    assert_eq!(<P3CmpN2 as Ord>::to_ordering(), Ordering::Greater);
}
#[test]
#[allow(non_snake_case)]
fn test_P3_Add_N1() {
    type A = PInt<UInt<UInt<UTerm, B1>, B1>>;
    type B = NInt<UInt<UTerm, B1>>;
    type P2 = PInt<UInt<UInt<UTerm, B1>, B0>>;

    #[allow(non_camel_case_types)]
    type P3AddN1 = <<A as Add<B>>::Output as Same<P2>>::Output;

    assert_eq!(<P3AddN1 as Integer>::to_i64(), <P2 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_P3_Sub_N1() {
    type A = PInt<UInt<UInt<UTerm, B1>, B1>>;
    type B = NInt<UInt<UTerm, B1>>;
    type P4 = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>>;

    #[allow(non_camel_case_types)]
    type P3SubN1 = <<A as Sub<B>>::Output as Same<P4>>::Output;

    assert_eq!(<P3SubN1 as Integer>::to_i64(), <P4 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_P3_Mul_N1() {
    type A = PInt<UInt<UInt<UTerm, B1>, B1>>;
    type B = NInt<UInt<UTerm, B1>>;
    type N3 = NInt<UInt<UInt<UTerm, B1>, B1>>;

    #[allow(non_camel_case_types)]
    type P3MulN1 = <<A as Mul<B>>::Output as Same<N3>>::Output;

    assert_eq!(<P3MulN1 as Integer>::to_i64(), <N3 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_P3_Min_N1() {
    type A = PInt<UInt<UInt<UTerm, B1>, B1>>;
    type B = NInt<UInt<UTerm, B1>>;
    type N1 = NInt<UInt<UTerm, B1>>;

    #[allow(non_camel_case_types)]
    type P3MinN1 = <<A as Min<B>>::Output as Same<N1>>::Output;

    assert_eq!(<P3MinN1 as Integer>::to_i64(), <N1 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_P3_Max_N1() {
    type A = PInt<UInt<UInt<UTerm, B1>, B1>>;
    type B = NInt<UInt<UTerm, B1>>;
    type P3 = PInt<UInt<UInt<UTerm, B1>, B1>>;

    #[allow(non_camel_case_types)]
    type P3MaxN1 = <<A as Max<B>>::Output as Same<P3>>::Output;

    assert_eq!(<P3MaxN1 as Integer>::to_i64(), <P3 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_P3_Gcd_N1() {
    type A = PInt<UInt<UInt<UTerm, B1>, B1>>;
    type B = NInt<UInt<UTerm, B1>>;
    type P1 = PInt<UInt<UTerm, B1>>;

    #[allow(non_camel_case_types)]
    type P3GcdN1 = <<A as Gcd<B>>::Output as Same<P1>>::Output;

    assert_eq!(<P3GcdN1 as Integer>::to_i64(), <P1 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_P3_Div_N1() {
    type A = PInt<UInt<UInt<UTerm, B1>, B1>>;
    type B = NInt<UInt<UTerm, B1>>;
    type N3 = NInt<UInt<UInt<UTerm, B1>, B1>>;

    #[allow(non_camel_case_types)]
    type P3DivN1 = <<A as Div<B>>::Output as Same<N3>>::Output;

    assert_eq!(<P3DivN1 as Integer>::to_i64(), <N3 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_P3_Rem_N1() {
    type A = PInt<UInt<UInt<UTerm, B1>, B1>>;
    type B = NInt<UInt<UTerm, B1>>;
    type _0 = Z0;

    #[allow(non_camel_case_types)]
    type P3RemN1 = <<A as Rem<B>>::Output as Same<_0>>::Output;

    assert_eq!(<P3RemN1 as Integer>::to_i64(), <_0 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_P3_PartialDiv_N1() {
    type A = PInt<UInt<UInt<UTerm, B1>, B1>>;
    type B = NInt<UInt<UTerm, B1>>;
    type N3 = NInt<UInt<UInt<UTerm, B1>, B1>>;

    #[allow(non_camel_case_types)]
    type P3PartialDivN1 = <<A as PartialDiv<B>>::Output as Same<N3>>::Output;

    assert_eq!(<P3PartialDivN1 as Integer>::to_i64(), <N3 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_P3_Cmp_N1() {
    type A = PInt<UInt<UInt<UTerm, B1>, B1>>;
    type B = NInt<UInt<UTerm, B1>>;

    #[allow(non_camel_case_types)]
    type P3CmpN1 = <A as Cmp<B>>::Output;
    assert_eq!(<P3CmpN1 as Ord>::to_ordering(), Ordering::Greater);
}
#[test]
#[allow(non_snake_case)]
fn test_P3_Add__0() {
    type A = PInt<UInt<UInt<UTerm, B1>, B1>>;
    type B = Z0;
    type P3 = PInt<UInt<UInt<UTerm, B1>, B1>>;

    #[allow(non_camel_case_types)]
    type P3Add_0 = <<A as Add<B>>::Output as Same<P3>>::Output;

    assert_eq!(<P3Add_0 as Integer>::to_i64(), <P3 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_P3_Sub__0() {
    type A = PInt<UInt<UInt<UTerm, B1>, B1>>;
    type B = Z0;
    type P3 = PInt<UInt<UInt<UTerm, B1>, B1>>;

    #[allow(non_camel_case_types)]
    type P3Sub_0 = <<A as Sub<B>>::Output as Same<P3>>::Output;

    assert_eq!(<P3Sub_0 as Integer>::to_i64(), <P3 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_P3_Mul__0() {
    type A = PInt<UInt<UInt<UTerm, B1>, B1>>;
    type B = Z0;
    type _0 = Z0;

    #[allow(non_camel_case_types)]
    type P3Mul_0 = <<A as Mul<B>>::Output as Same<_0>>::Output;

    assert_eq!(<P3Mul_0 as Integer>::to_i64(), <_0 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_P3_Min__0() {
    type A = PInt<UInt<UInt<UTerm, B1>, B1>>;
    type B = Z0;
    type _0 = Z0;

    #[allow(non_camel_case_types)]
    type P3Min_0 = <<A as Min<B>>::Output as Same<_0>>::Output;

    assert_eq!(<P3Min_0 as Integer>::to_i64(), <_0 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_P3_Max__0() {
    type A = PInt<UInt<UInt<UTerm, B1>, B1>>;
    type B = Z0;
    type P3 = PInt<UInt<UInt<UTerm, B1>, B1>>;

    #[allow(non_camel_case_types)]
    type P3Max_0 = <<A as Max<B>>::Output as Same<P3>>::Output;

    assert_eq!(<P3Max_0 as Integer>::to_i64(), <P3 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_P3_Gcd__0() {
    type A = PInt<UInt<UInt<UTerm, B1>, B1>>;
    type B = Z0;
    type P3 = PInt<UInt<UInt<UTerm, B1>, B1>>;

    #[allow(non_camel_case_types)]
    type P3Gcd_0 = <<A as Gcd<B>>::Output as Same<P3>>::Output;

    assert_eq!(<P3Gcd_0 as Integer>::to_i64(), <P3 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_P3_Pow__0() {
    type A = PInt<UInt<UInt<UTerm, B1>, B1>>;
    type B = Z0;
    type P1 = PInt<UInt<UTerm, B1>>;

    #[allow(non_camel_case_types)]
    type P3Pow_0 = <<A as Pow<B>>::Output as Same<P1>>::Output;

    assert_eq!(<P3Pow_0 as Integer>::to_i64(), <P1 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_P3_Cmp__0() {
    type A = PInt<UInt<UInt<UTerm, B1>, B1>>;
    type B = Z0;

    #[allow(non_camel_case_types)]
    type P3Cmp_0 = <A as Cmp<B>>::Output;
    assert_eq!(<P3Cmp_0 as Ord>::to_ordering(), Ordering::Greater);
}
#[test]
#[allow(non_snake_case)]
fn test_P3_Add_P1() {
    type A = PInt<UInt<UInt<UTerm, B1>, B1>>;
    type B = PInt<UInt<UTerm, B1>>;
    type P4 = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>>;

    #[allow(non_camel_case_types)]
    type P3AddP1 = <<A as Add<B>>::Output as Same<P4>>::Output;

    assert_eq!(<P3AddP1 as Integer>::to_i64(), <P4 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_P3_Sub_P1() {
    type A = PInt<UInt<UInt<UTerm, B1>, B1>>;
    type B = PInt<UInt<UTerm, B1>>;
    type P2 = PInt<UInt<UInt<UTerm, B1>, B0>>;

    #[allow(non_camel_case_types)]
    type P3SubP1 = <<A as Sub<B>>::Output as Same<P2>>::Output;

    assert_eq!(<P3SubP1 as Integer>::to_i64(), <P2 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_P3_Mul_P1() {
    type A = PInt<UInt<UInt<UTerm, B1>, B1>>;
    type B = PInt<UInt<UTerm, B1>>;
    type P3 = PInt<UInt<UInt<UTerm, B1>, B1>>;

    #[allow(non_camel_case_types)]
    type P3MulP1 = <<A as Mul<B>>::Output as Same<P3>>::Output;

    assert_eq!(<P3MulP1 as Integer>::to_i64(), <P3 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_P3_Min_P1() {
    type A = PInt<UInt<UInt<UTerm, B1>, B1>>;
    type B = PInt<UInt<UTerm, B1>>;
    type P1 = PInt<UInt<UTerm, B1>>;

    #[allow(non_camel_case_types)]
    type P3MinP1 = <<A as Min<B>>::Output as Same<P1>>::Output;

    assert_eq!(<P3MinP1 as Integer>::to_i64(), <P1 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_P3_Max_P1() {
    type A = PInt<UInt<UInt<UTerm, B1>, B1>>;
    type B = PInt<UInt<UTerm, B1>>;
    type P3 = PInt<UInt<UInt<UTerm, B1>, B1>>;

    #[allow(non_camel_case_types)]
    type P3MaxP1 = <<A as Max<B>>::Output as Same<P3>>::Output;

    assert_eq!(<P3MaxP1 as Integer>::to_i64(), <P3 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_P3_Gcd_P1() {
    type A = PInt<UInt<UInt<UTerm, B1>, B1>>;
    type B = PInt<UInt<UTerm, B1>>;
    type P1 = PInt<UInt<UTerm, B1>>;

    #[allow(non_camel_case_types)]
    type P3GcdP1 = <<A as Gcd<B>>::Output as Same<P1>>::Output;

    assert_eq!(<P3GcdP1 as Integer>::to_i64(), <P1 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_P3_Div_P1() {
    type A = PInt<UInt<UInt<UTerm, B1>, B1>>;
    type B = PInt<UInt<UTerm, B1>>;
    type P3 = PInt<UInt<UInt<UTerm, B1>, B1>>;

    #[allow(non_camel_case_types)]
    type P3DivP1 = <<A as Div<B>>::Output as Same<P3>>::Output;

    assert_eq!(<P3DivP1 as Integer>::to_i64(), <P3 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_P3_Rem_P1() {
    type A = PInt<UInt<UInt<UTerm, B1>, B1>>;
    type B = PInt<UInt<UTerm, B1>>;
    type _0 = Z0;

    #[allow(non_camel_case_types)]
    type P3RemP1 = <<A as Rem<B>>::Output as Same<_0>>::Output;

    assert_eq!(<P3RemP1 as Integer>::to_i64(), <_0 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_P3_PartialDiv_P1() {
    type A = PInt<UInt<UInt<UTerm, B1>, B1>>;
    type B = PInt<UInt<UTerm, B1>>;
    type P3 = PInt<UInt<UInt<UTerm, B1>, B1>>;

    #[allow(non_camel_case_types)]
    type P3PartialDivP1 = <<A as PartialDiv<B>>::Output as Same<P3>>::Output;

    assert_eq!(<P3PartialDivP1 as Integer>::to_i64(), <P3 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_P3_Pow_P1() {
    type A = PInt<UInt<UInt<UTerm, B1>, B1>>;
    type B = PInt<UInt<UTerm, B1>>;
    type P3 = PInt<UInt<UInt<UTerm, B1>, B1>>;

    #[allow(non_camel_case_types)]
    type P3PowP1 = <<A as Pow<B>>::Output as Same<P3>>::Output;

    assert_eq!(<P3PowP1 as Integer>::to_i64(), <P3 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_P3_Cmp_P1() {
    type A = PInt<UInt<UInt<UTerm, B1>, B1>>;
    type B = PInt<UInt<UTerm, B1>>;

    #[allow(non_camel_case_types)]
    type P3CmpP1 = <A as Cmp<B>>::Output;
    assert_eq!(<P3CmpP1 as Ord>::to_ordering(), Ordering::Greater);
}
#[test]
#[allow(non_snake_case)]
fn test_P3_Add_P2() {
    type A = PInt<UInt<UInt<UTerm, B1>, B1>>;
    type B = PInt<UInt<UInt<UTerm, B1>, B0>>;
    type P5 = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>>;

    #[allow(non_camel_case_types)]
    type P3AddP2 = <<A as Add<B>>::Output as Same<P5>>::Output;

    assert_eq!(<P3AddP2 as Integer>::to_i64(), <P5 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_P3_Sub_P2() {
    type A = PInt<UInt<UInt<UTerm, B1>, B1>>;
    type B = PInt<UInt<UInt<UTerm, B1>, B0>>;
    type P1 = PInt<UInt<UTerm, B1>>;

    #[allow(non_camel_case_types)]
    type P3SubP2 = <<A as Sub<B>>::Output as Same<P1>>::Output;

    assert_eq!(<P3SubP2 as Integer>::to_i64(), <P1 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_P3_Mul_P2() {
    type A = PInt<UInt<UInt<UTerm, B1>, B1>>;
    type B = PInt<UInt<UInt<UTerm, B1>, B0>>;
    type P6 = PInt<UInt<UInt<UInt<UTerm, B1>, B1>, B0>>;

    #[allow(non_camel_case_types)]
    type P3MulP2 = <<A as Mul<B>>::Output as Same<P6>>::Output;

    assert_eq!(<P3MulP2 as Integer>::to_i64(), <P6 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_P3_Min_P2() {
    type A = PInt<UInt<UInt<UTerm, B1>, B1>>;
    type B = PInt<UInt<UInt<UTerm, B1>, B0>>;
    type P2 = PInt<UInt<UInt<UTerm, B1>, B0>>;

    #[allow(non_camel_case_types)]
    type P3MinP2 = <<A as Min<B>>::Output as Same<P2>>::Output;

    assert_eq!(<P3MinP2 as Integer>::to_i64(), <P2 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_P3_Max_P2() {
    type A = PInt<UInt<UInt<UTerm, B1>, B1>>;
    type B = PInt<UInt<UInt<UTerm, B1>, B0>>;
    type P3 = PInt<UInt<UInt<UTerm, B1>, B1>>;

    #[allow(non_camel_case_types)]
    type P3MaxP2 = <<A as Max<B>>::Output as Same<P3>>::Output;

    assert_eq!(<P3MaxP2 as Integer>::to_i64(), <P3 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_P3_Gcd_P2() {
    type A = PInt<UInt<UInt<UTerm, B1>, B1>>;
    type B = PInt<UInt<UInt<UTerm, B1>, B0>>;
    type P1 = PInt<UInt<UTerm, B1>>;

    #[allow(non_camel_case_types)]
    type P3GcdP2 = <<A as Gcd<B>>::Output as Same<P1>>::Output;

    assert_eq!(<P3GcdP2 as Integer>::to_i64(), <P1 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_P3_Div_P2() {
    type A = PInt<UInt<UInt<UTerm, B1>, B1>>;
    type B = PInt<UInt<UInt<UTerm, B1>, B0>>;
    type P1 = PInt<UInt<UTerm, B1>>;

    #[allow(non_camel_case_types)]
    type P3DivP2 = <<A as Div<B>>::Output as Same<P1>>::Output;

    assert_eq!(<P3DivP2 as Integer>::to_i64(), <P1 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_P3_Rem_P2() {
    type A = PInt<UInt<UInt<UTerm, B1>, B1>>;
    type B = PInt<UInt<UInt<UTerm, B1>, B0>>;
    type P1 = PInt<UInt<UTerm, B1>>;

    #[allow(non_camel_case_types)]
    type P3RemP2 = <<A as Rem<B>>::Output as Same<P1>>::Output;

    assert_eq!(<P3RemP2 as Integer>::to_i64(), <P1 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_P3_Pow_P2() {
    type A = PInt<UInt<UInt<UTerm, B1>, B1>>;
    type B = PInt<UInt<UInt<UTerm, B1>, B0>>;
    type P9 = PInt<UInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>, B1>>;

    #[allow(non_camel_case_types)]
    type P3PowP2 = <<A as Pow<B>>::Output as Same<P9>>::Output;

    assert_eq!(<P3PowP2 as Integer>::to_i64(), <P9 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_P3_Cmp_P2() {
    type A = PInt<UInt<UInt<UTerm, B1>, B1>>;
    type B = PInt<UInt<UInt<UTerm, B1>, B0>>;

    #[allow(non_camel_case_types)]
    type P3CmpP2 = <A as Cmp<B>>::Output;
    assert_eq!(<P3CmpP2 as Ord>::to_ordering(), Ordering::Greater);
}
#[test]
#[allow(non_snake_case)]
fn test_P3_Add_P3() {
    type A = PInt<UInt<UInt<UTerm, B1>, B1>>;
    type B = PInt<UInt<UInt<UTerm, B1>, B1>>;
    type P6 = PInt<UInt<UInt<UInt<UTerm, B1>, B1>, B0>>;

    #[allow(non_camel_case_types)]
    type P3AddP3 = <<A as Add<B>>::Output as Same<P6>>::Output;

    assert_eq!(<P3AddP3 as Integer>::to_i64(), <P6 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_P3_Sub_P3() {
    type A = PInt<UInt<UInt<UTerm, B1>, B1>>;
    type B = PInt<UInt<UInt<UTerm, B1>, B1>>;
    type _0 = Z0;

    #[allow(non_camel_case_types)]
    type P3SubP3 = <<A as Sub<B>>::Output as Same<_0>>::Output;

    assert_eq!(<P3SubP3 as Integer>::to_i64(), <_0 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_P3_Mul_P3() {
    type A = PInt<UInt<UInt<UTerm, B1>, B1>>;
    type B = PInt<UInt<UInt<UTerm, B1>, B1>>;
    type P9 = PInt<UInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>, B1>>;

    #[allow(non_camel_case_types)]
    type P3MulP3 = <<A as Mul<B>>::Output as Same<P9>>::Output;

    assert_eq!(<P3MulP3 as Integer>::to_i64(), <P9 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_P3_Min_P3() {
    type A = PInt<UInt<UInt<UTerm, B1>, B1>>;
    type B = PInt<UInt<UInt<UTerm, B1>, B1>>;
    type P3 = PInt<UInt<UInt<UTerm, B1>, B1>>;

    #[allow(non_camel_case_types)]
    type P3MinP3 = <<A as Min<B>>::Output as Same<P3>>::Output;

    assert_eq!(<P3MinP3 as Integer>::to_i64(), <P3 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_P3_Max_P3() {
    type A = PInt<UInt<UInt<UTerm, B1>, B1>>;
    type B = PInt<UInt<UInt<UTerm, B1>, B1>>;
    type P3 = PInt<UInt<UInt<UTerm, B1>, B1>>;

    #[allow(non_camel_case_types)]
    type P3MaxP3 = <<A as Max<B>>::Output as Same<P3>>::Output;

    assert_eq!(<P3MaxP3 as Integer>::to_i64(), <P3 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_P3_Gcd_P3() {
    type A = PInt<UInt<UInt<UTerm, B1>, B1>>;
    type B = PInt<UInt<UInt<UTerm, B1>, B1>>;
    type P3 = PInt<UInt<UInt<UTerm, B1>, B1>>;

    #[allow(non_camel_case_types)]
    type P3GcdP3 = <<A as Gcd<B>>::Output as Same<P3>>::Output;

    assert_eq!(<P3GcdP3 as Integer>::to_i64(), <P3 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_P3_Div_P3() {
    type A = PInt<UInt<UInt<UTerm, B1>, B1>>;
    type B = PInt<UInt<UInt<UTerm, B1>, B1>>;
    type P1 = PInt<UInt<UTerm, B1>>;

    #[allow(non_camel_case_types)]
    type P3DivP3 = <<A as Div<B>>::Output as Same<P1>>::Output;

    assert_eq!(<P3DivP3 as Integer>::to_i64(), <P1 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_P3_Rem_P3() {
    type A = PInt<UInt<UInt<UTerm, B1>, B1>>;
    type B = PInt<UInt<UInt<UTerm, B1>, B1>>;
    type _0 = Z0;

    #[allow(non_camel_case_types)]
    type P3RemP3 = <<A as Rem<B>>::Output as Same<_0>>::Output;

    assert_eq!(<P3RemP3 as Integer>::to_i64(), <_0 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_P3_PartialDiv_P3() {
    type A = PInt<UInt<UInt<UTerm, B1>, B1>>;
    type B = PInt<UInt<UInt<UTerm, B1>, B1>>;
    type P1 = PInt<UInt<UTerm, B1>>;

    #[allow(non_camel_case_types)]
    type P3PartialDivP3 = <<A as PartialDiv<B>>::Output as Same<P1>>::Output;

    assert_eq!(<P3PartialDivP3 as Integer>::to_i64(), <P1 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_P3_Pow_P3() {
    type A = PInt<UInt<UInt<UTerm, B1>, B1>>;
    type B = PInt<UInt<UInt<UTerm, B1>, B1>>;
    type P27 = PInt<UInt<UInt<UInt<UInt<UInt<UTerm, B1>, B1>, B0>, B1>, B1>>;

    #[allow(non_camel_case_types)]
    type P3PowP3 = <<A as Pow<B>>::Output as Same<P27>>::Output;

    assert_eq!(<P3PowP3 as Integer>::to_i64(), <P27 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_P3_Cmp_P3() {
    type A = PInt<UInt<UInt<UTerm, B1>, B1>>;
    type B = PInt<UInt<UInt<UTerm, B1>, B1>>;

    #[allow(non_camel_case_types)]
    type P3CmpP3 = <A as Cmp<B>>::Output;
    assert_eq!(<P3CmpP3 as Ord>::to_ordering(), Ordering::Equal);
}
#[test]
#[allow(non_snake_case)]
fn test_P3_Add_P4() {
    type A = PInt<UInt<UInt<UTerm, B1>, B1>>;
    type B = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>>;
    type P7 = PInt<UInt<UInt<UInt<UTerm, B1>, B1>, B1>>;

    #[allow(non_camel_case_types)]
    type P3AddP4 = <<A as Add<B>>::Output as Same<P7>>::Output;

    assert_eq!(<P3AddP4 as Integer>::to_i64(), <P7 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_P3_Sub_P4() {
    type A = PInt<UInt<UInt<UTerm, B1>, B1>>;
    type B = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>>;
    type N1 = NInt<UInt<UTerm, B1>>;

    #[allow(non_camel_case_types)]
    type P3SubP4 = <<A as Sub<B>>::Output as Same<N1>>::Output;

    assert_eq!(<P3SubP4 as Integer>::to_i64(), <N1 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_P3_Mul_P4() {
    type A = PInt<UInt<UInt<UTerm, B1>, B1>>;
    type B = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>>;
    type P12 = PInt<UInt<UInt<UInt<UInt<UTerm, B1>, B1>, B0>, B0>>;

    #[allow(non_camel_case_types)]
    type P3MulP4 = <<A as Mul<B>>::Output as Same<P12>>::Output;

    assert_eq!(<P3MulP4 as Integer>::to_i64(), <P12 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_P3_Min_P4() {
    type A = PInt<UInt<UInt<UTerm, B1>, B1>>;
    type B = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>>;
    type P3 = PInt<UInt<UInt<UTerm, B1>, B1>>;

    #[allow(non_camel_case_types)]
    type P3MinP4 = <<A as Min<B>>::Output as Same<P3>>::Output;

    assert_eq!(<P3MinP4 as Integer>::to_i64(), <P3 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_P3_Max_P4() {
    type A = PInt<UInt<UInt<UTerm, B1>, B1>>;
    type B = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>>;
    type P4 = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>>;

    #[allow(non_camel_case_types)]
    type P3MaxP4 = <<A as Max<B>>::Output as Same<P4>>::Output;

    assert_eq!(<P3MaxP4 as Integer>::to_i64(), <P4 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_P3_Gcd_P4() {
    type A = PInt<UInt<UInt<UTerm, B1>, B1>>;
    type B = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>>;
    type P1 = PInt<UInt<UTerm, B1>>;

    #[allow(non_camel_case_types)]
    type P3GcdP4 = <<A as Gcd<B>>::Output as Same<P1>>::Output;

    assert_eq!(<P3GcdP4 as Integer>::to_i64(), <P1 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_P3_Div_P4() {
    type A = PInt<UInt<UInt<UTerm, B1>, B1>>;
    type B = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>>;
    type _0 = Z0;

    #[allow(non_camel_case_types)]
    type P3DivP4 = <<A as Div<B>>::Output as Same<_0>>::Output;

    assert_eq!(<P3DivP4 as Integer>::to_i64(), <_0 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_P3_Rem_P4() {
    type A = PInt<UInt<UInt<UTerm, B1>, B1>>;
    type B = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>>;
    type P3 = PInt<UInt<UInt<UTerm, B1>, B1>>;

    #[allow(non_camel_case_types)]
    type P3RemP4 = <<A as Rem<B>>::Output as Same<P3>>::Output;

    assert_eq!(<P3RemP4 as Integer>::to_i64(), <P3 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_P3_Pow_P4() {
    type A = PInt<UInt<UInt<UTerm, B1>, B1>>;
    type B = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>>;
    type P81 = PInt<UInt<UInt<UInt<UInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>, B0>, B0>, B0>, B1>>;

    #[allow(non_camel_case_types)]
    type P3PowP4 = <<A as Pow<B>>::Output as Same<P81>>::Output;

    assert_eq!(<P3PowP4 as Integer>::to_i64(), <P81 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_P3_Cmp_P4() {
    type A = PInt<UInt<UInt<UTerm, B1>, B1>>;
    type B = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>>;

    #[allow(non_camel_case_types)]
    type P3CmpP4 = <A as Cmp<B>>::Output;
    assert_eq!(<P3CmpP4 as Ord>::to_ordering(), Ordering::Less);
}
#[test]
#[allow(non_snake_case)]
fn test_P3_Add_P5() {
    type A = PInt<UInt<UInt<UTerm, B1>, B1>>;
    type B = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>>;
    type P8 = PInt<UInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>, B0>>;

    #[allow(non_camel_case_types)]
    type P3AddP5 = <<A as Add<B>>::Output as Same<P8>>::Output;

    assert_eq!(<P3AddP5 as Integer>::to_i64(), <P8 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_P3_Sub_P5() {
    type A = PInt<UInt<UInt<UTerm, B1>, B1>>;
    type B = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>>;
    type N2 = NInt<UInt<UInt<UTerm, B1>, B0>>;

    #[allow(non_camel_case_types)]
    type P3SubP5 = <<A as Sub<B>>::Output as Same<N2>>::Output;

    assert_eq!(<P3SubP5 as Integer>::to_i64(), <N2 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_P3_Mul_P5() {
    type A = PInt<UInt<UInt<UTerm, B1>, B1>>;
    type B = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>>;
    type P15 = PInt<UInt<UInt<UInt<UInt<UTerm, B1>, B1>, B1>, B1>>;

    #[allow(non_camel_case_types)]
    type P3MulP5 = <<A as Mul<B>>::Output as Same<P15>>::Output;

    assert_eq!(<P3MulP5 as Integer>::to_i64(), <P15 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_P3_Min_P5() {
    type A = PInt<UInt<UInt<UTerm, B1>, B1>>;
    type B = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>>;
    type P3 = PInt<UInt<UInt<UTerm, B1>, B1>>;

    #[allow(non_camel_case_types)]
    type P3MinP5 = <<A as Min<B>>::Output as Same<P3>>::Output;

    assert_eq!(<P3MinP5 as Integer>::to_i64(), <P3 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_P3_Max_P5() {
    type A = PInt<UInt<UInt<UTerm, B1>, B1>>;
    type B = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>>;
    type P5 = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>>;

    #[allow(non_camel_case_types)]
    type P3MaxP5 = <<A as Max<B>>::Output as Same<P5>>::Output;

    assert_eq!(<P3MaxP5 as Integer>::to_i64(), <P5 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_P3_Gcd_P5() {
    type A = PInt<UInt<UInt<UTerm, B1>, B1>>;
    type B = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>>;
    type P1 = PInt<UInt<UTerm, B1>>;

    #[allow(non_camel_case_types)]
    type P3GcdP5 = <<A as Gcd<B>>::Output as Same<P1>>::Output;

    assert_eq!(<P3GcdP5 as Integer>::to_i64(), <P1 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_P3_Div_P5() {
    type A = PInt<UInt<UInt<UTerm, B1>, B1>>;
    type B = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>>;
    type _0 = Z0;

    #[allow(non_camel_case_types)]
    type P3DivP5 = <<A as Div<B>>::Output as Same<_0>>::Output;

    assert_eq!(<P3DivP5 as Integer>::to_i64(), <_0 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_P3_Rem_P5() {
    type A = PInt<UInt<UInt<UTerm, B1>, B1>>;
    type B = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>>;
    type P3 = PInt<UInt<UInt<UTerm, B1>, B1>>;

    #[allow(non_camel_case_types)]
    type P3RemP5 = <<A as Rem<B>>::Output as Same<P3>>::Output;

    assert_eq!(<P3RemP5 as Integer>::to_i64(), <P3 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_P3_Pow_P5() {
    type A = PInt<UInt<UInt<UTerm, B1>, B1>>;
    type B = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>>;
    type P243 = PInt<UInt<UInt<UInt<UInt<UInt<UInt<UInt<UInt<UTerm, B1>, B1>, B1>, B1>, B0>, B0>, B1>, B1>>;

    #[allow(non_camel_case_types)]
    type P3PowP5 = <<A as Pow<B>>::Output as Same<P243>>::Output;

    assert_eq!(<P3PowP5 as Integer>::to_i64(), <P243 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_P3_Cmp_P5() {
    type A = PInt<UInt<UInt<UTerm, B1>, B1>>;
    type B = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>>;

    #[allow(non_camel_case_types)]
    type P3CmpP5 = <A as Cmp<B>>::Output;
    assert_eq!(<P3CmpP5 as Ord>::to_ordering(), Ordering::Less);
}
#[test]
#[allow(non_snake_case)]
fn test_P4_Add_N5() {
    type A = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>>;
    type B = NInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>>;
    type N1 = NInt<UInt<UTerm, B1>>;

    #[allow(non_camel_case_types)]
    type P4AddN5 = <<A as Add<B>>::Output as Same<N1>>::Output;

    assert_eq!(<P4AddN5 as Integer>::to_i64(), <N1 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_P4_Sub_N5() {
    type A = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>>;
    type B = NInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>>;
    type P9 = PInt<UInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>, B1>>;

    #[allow(non_camel_case_types)]
    type P4SubN5 = <<A as Sub<B>>::Output as Same<P9>>::Output;

    assert_eq!(<P4SubN5 as Integer>::to_i64(), <P9 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_P4_Mul_N5() {
    type A = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>>;
    type B = NInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>>;
    type N20 = NInt<UInt<UInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>, B0>, B0>>;

    #[allow(non_camel_case_types)]
    type P4MulN5 = <<A as Mul<B>>::Output as Same<N20>>::Output;

    assert_eq!(<P4MulN5 as Integer>::to_i64(), <N20 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_P4_Min_N5() {
    type A = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>>;
    type B = NInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>>;
    type N5 = NInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>>;

    #[allow(non_camel_case_types)]
    type P4MinN5 = <<A as Min<B>>::Output as Same<N5>>::Output;

    assert_eq!(<P4MinN5 as Integer>::to_i64(), <N5 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_P4_Max_N5() {
    type A = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>>;
    type B = NInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>>;
    type P4 = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>>;

    #[allow(non_camel_case_types)]
    type P4MaxN5 = <<A as Max<B>>::Output as Same<P4>>::Output;

    assert_eq!(<P4MaxN5 as Integer>::to_i64(), <P4 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_P4_Gcd_N5() {
    type A = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>>;
    type B = NInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>>;
    type P1 = PInt<UInt<UTerm, B1>>;

    #[allow(non_camel_case_types)]
    type P4GcdN5 = <<A as Gcd<B>>::Output as Same<P1>>::Output;

    assert_eq!(<P4GcdN5 as Integer>::to_i64(), <P1 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_P4_Div_N5() {
    type A = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>>;
    type B = NInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>>;
    type _0 = Z0;

    #[allow(non_camel_case_types)]
    type P4DivN5 = <<A as Div<B>>::Output as Same<_0>>::Output;

    assert_eq!(<P4DivN5 as Integer>::to_i64(), <_0 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_P4_Rem_N5() {
    type A = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>>;
    type B = NInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>>;
    type P4 = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>>;

    #[allow(non_camel_case_types)]
    type P4RemN5 = <<A as Rem<B>>::Output as Same<P4>>::Output;

    assert_eq!(<P4RemN5 as Integer>::to_i64(), <P4 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_P4_Cmp_N5() {
    type A = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>>;
    type B = NInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>>;

    #[allow(non_camel_case_types)]
    type P4CmpN5 = <A as Cmp<B>>::Output;
    assert_eq!(<P4CmpN5 as Ord>::to_ordering(), Ordering::Greater);
}
#[test]
#[allow(non_snake_case)]
fn test_P4_Add_N4() {
    type A = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>>;
    type B = NInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>>;
    type _0 = Z0;

    #[allow(non_camel_case_types)]
    type P4AddN4 = <<A as Add<B>>::Output as Same<_0>>::Output;

    assert_eq!(<P4AddN4 as Integer>::to_i64(), <_0 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_P4_Sub_N4() {
    type A = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>>;
    type B = NInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>>;
    type P8 = PInt<UInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>, B0>>;

    #[allow(non_camel_case_types)]
    type P4SubN4 = <<A as Sub<B>>::Output as Same<P8>>::Output;

    assert_eq!(<P4SubN4 as Integer>::to_i64(), <P8 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_P4_Mul_N4() {
    type A = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>>;
    type B = NInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>>;
    type N16 = NInt<UInt<UInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>, B0>, B0>>;

    #[allow(non_camel_case_types)]
    type P4MulN4 = <<A as Mul<B>>::Output as Same<N16>>::Output;

    assert_eq!(<P4MulN4 as Integer>::to_i64(), <N16 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_P4_Min_N4() {
    type A = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>>;
    type B = NInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>>;
    type N4 = NInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>>;

    #[allow(non_camel_case_types)]
    type P4MinN4 = <<A as Min<B>>::Output as Same<N4>>::Output;

    assert_eq!(<P4MinN4 as Integer>::to_i64(), <N4 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_P4_Max_N4() {
    type A = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>>;
    type B = NInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>>;
    type P4 = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>>;

    #[allow(non_camel_case_types)]
    type P4MaxN4 = <<A as Max<B>>::Output as Same<P4>>::Output;

    assert_eq!(<P4MaxN4 as Integer>::to_i64(), <P4 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_P4_Gcd_N4() {
    type A = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>>;
    type B = NInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>>;
    type P4 = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>>;

    #[allow(non_camel_case_types)]
    type P4GcdN4 = <<A as Gcd<B>>::Output as Same<P4>>::Output;

    assert_eq!(<P4GcdN4 as Integer>::to_i64(), <P4 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_P4_Div_N4() {
    type A = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>>;
    type B = NInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>>;
    type N1 = NInt<UInt<UTerm, B1>>;

    #[allow(non_camel_case_types)]
    type P4DivN4 = <<A as Div<B>>::Output as Same<N1>>::Output;

    assert_eq!(<P4DivN4 as Integer>::to_i64(), <N1 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_P4_Rem_N4() {
    type A = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>>;
    type B = NInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>>;
    type _0 = Z0;

    #[allow(non_camel_case_types)]
    type P4RemN4 = <<A as Rem<B>>::Output as Same<_0>>::Output;

    assert_eq!(<P4RemN4 as Integer>::to_i64(), <_0 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_P4_PartialDiv_N4() {
    type A = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>>;
    type B = NInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>>;
    type N1 = NInt<UInt<UTerm, B1>>;

    #[allow(non_camel_case_types)]
    type P4PartialDivN4 = <<A as PartialDiv<B>>::Output as Same<N1>>::Output;

    assert_eq!(<P4PartialDivN4 as Integer>::to_i64(), <N1 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_P4_Cmp_N4() {
    type A = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>>;
    type B = NInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>>;

    #[allow(non_camel_case_types)]
    type P4CmpN4 = <A as Cmp<B>>::Output;
    assert_eq!(<P4CmpN4 as Ord>::to_ordering(), Ordering::Greater);
}
#[test]
#[allow(non_snake_case)]
fn test_P4_Add_N3() {
    type A = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>>;
    type B = NInt<UInt<UInt<UTerm, B1>, B1>>;
    type P1 = PInt<UInt<UTerm, B1>>;

    #[allow(non_camel_case_types)]
    type P4AddN3 = <<A as Add<B>>::Output as Same<P1>>::Output;

    assert_eq!(<P4AddN3 as Integer>::to_i64(), <P1 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_P4_Sub_N3() {
    type A = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>>;
    type B = NInt<UInt<UInt<UTerm, B1>, B1>>;
    type P7 = PInt<UInt<UInt<UInt<UTerm, B1>, B1>, B1>>;

    #[allow(non_camel_case_types)]
    type P4SubN3 = <<A as Sub<B>>::Output as Same<P7>>::Output;

    assert_eq!(<P4SubN3 as Integer>::to_i64(), <P7 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_P4_Mul_N3() {
    type A = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>>;
    type B = NInt<UInt<UInt<UTerm, B1>, B1>>;
    type N12 = NInt<UInt<UInt<UInt<UInt<UTerm, B1>, B1>, B0>, B0>>;

    #[allow(non_camel_case_types)]
    type P4MulN3 = <<A as Mul<B>>::Output as Same<N12>>::Output;

    assert_eq!(<P4MulN3 as Integer>::to_i64(), <N12 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_P4_Min_N3() {
    type A = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>>;
    type B = NInt<UInt<UInt<UTerm, B1>, B1>>;
    type N3 = NInt<UInt<UInt<UTerm, B1>, B1>>;

    #[allow(non_camel_case_types)]
    type P4MinN3 = <<A as Min<B>>::Output as Same<N3>>::Output;

    assert_eq!(<P4MinN3 as Integer>::to_i64(), <N3 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_P4_Max_N3() {
    type A = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>>;
    type B = NInt<UInt<UInt<UTerm, B1>, B1>>;
    type P4 = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>>;

    #[allow(non_camel_case_types)]
    type P4MaxN3 = <<A as Max<B>>::Output as Same<P4>>::Output;

    assert_eq!(<P4MaxN3 as Integer>::to_i64(), <P4 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_P4_Gcd_N3() {
    type A = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>>;
    type B = NInt<UInt<UInt<UTerm, B1>, B1>>;
    type P1 = PInt<UInt<UTerm, B1>>;

    #[allow(non_camel_case_types)]
    type P4GcdN3 = <<A as Gcd<B>>::Output as Same<P1>>::Output;

    assert_eq!(<P4GcdN3 as Integer>::to_i64(), <P1 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_P4_Div_N3() {
    type A = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>>;
    type B = NInt<UInt<UInt<UTerm, B1>, B1>>;
    type N1 = NInt<UInt<UTerm, B1>>;

    #[allow(non_camel_case_types)]
    type P4DivN3 = <<A as Div<B>>::Output as Same<N1>>::Output;

    assert_eq!(<P4DivN3 as Integer>::to_i64(), <N1 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_P4_Rem_N3() {
    type A = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>>;
    type B = NInt<UInt<UInt<UTerm, B1>, B1>>;
    type P1 = PInt<UInt<UTerm, B1>>;

    #[allow(non_camel_case_types)]
    type P4RemN3 = <<A as Rem<B>>::Output as Same<P1>>::Output;

    assert_eq!(<P4RemN3 as Integer>::to_i64(), <P1 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_P4_Cmp_N3() {
    type A = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>>;
    type B = NInt<UInt<UInt<UTerm, B1>, B1>>;

    #[allow(non_camel_case_types)]
    type P4CmpN3 = <A as Cmp<B>>::Output;
    assert_eq!(<P4CmpN3 as Ord>::to_ordering(), Ordering::Greater);
}
#[test]
#[allow(non_snake_case)]
fn test_P4_Add_N2() {
    type A = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>>;
    type B = NInt<UInt<UInt<UTerm, B1>, B0>>;
    type P2 = PInt<UInt<UInt<UTerm, B1>, B0>>;

    #[allow(non_camel_case_types)]
    type P4AddN2 = <<A as Add<B>>::Output as Same<P2>>::Output;

    assert_eq!(<P4AddN2 as Integer>::to_i64(), <P2 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_P4_Sub_N2() {
    type A = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>>;
    type B = NInt<UInt<UInt<UTerm, B1>, B0>>;
    type P6 = PInt<UInt<UInt<UInt<UTerm, B1>, B1>, B0>>;

    #[allow(non_camel_case_types)]
    type P4SubN2 = <<A as Sub<B>>::Output as Same<P6>>::Output;

    assert_eq!(<P4SubN2 as Integer>::to_i64(), <P6 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_P4_Mul_N2() {
    type A = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>>;
    type B = NInt<UInt<UInt<UTerm, B1>, B0>>;
    type N8 = NInt<UInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>, B0>>;

    #[allow(non_camel_case_types)]
    type P4MulN2 = <<A as Mul<B>>::Output as Same<N8>>::Output;

    assert_eq!(<P4MulN2 as Integer>::to_i64(), <N8 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_P4_Min_N2() {
    type A = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>>;
    type B = NInt<UInt<UInt<UTerm, B1>, B0>>;
    type N2 = NInt<UInt<UInt<UTerm, B1>, B0>>;

    #[allow(non_camel_case_types)]
    type P4MinN2 = <<A as Min<B>>::Output as Same<N2>>::Output;

    assert_eq!(<P4MinN2 as Integer>::to_i64(), <N2 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_P4_Max_N2() {
    type A = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>>;
    type B = NInt<UInt<UInt<UTerm, B1>, B0>>;
    type P4 = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>>;

    #[allow(non_camel_case_types)]
    type P4MaxN2 = <<A as Max<B>>::Output as Same<P4>>::Output;

    assert_eq!(<P4MaxN2 as Integer>::to_i64(), <P4 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_P4_Gcd_N2() {
    type A = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>>;
    type B = NInt<UInt<UInt<UTerm, B1>, B0>>;
    type P2 = PInt<UInt<UInt<UTerm, B1>, B0>>;

    #[allow(non_camel_case_types)]
    type P4GcdN2 = <<A as Gcd<B>>::Output as Same<P2>>::Output;

    assert_eq!(<P4GcdN2 as Integer>::to_i64(), <P2 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_P4_Div_N2() {
    type A = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>>;
    type B = NInt<UInt<UInt<UTerm, B1>, B0>>;
    type N2 = NInt<UInt<UInt<UTerm, B1>, B0>>;

    #[allow(non_camel_case_types)]
    type P4DivN2 = <<A as Div<B>>::Output as Same<N2>>::Output;

    assert_eq!(<P4DivN2 as Integer>::to_i64(), <N2 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_P4_Rem_N2() {
    type A = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>>;
    type B = NInt<UInt<UInt<UTerm, B1>, B0>>;
    type _0 = Z0;

    #[allow(non_camel_case_types)]
    type P4RemN2 = <<A as Rem<B>>::Output as Same<_0>>::Output;

    assert_eq!(<P4RemN2 as Integer>::to_i64(), <_0 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_P4_PartialDiv_N2() {
    type A = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>>;
    type B = NInt<UInt<UInt<UTerm, B1>, B0>>;
    type N2 = NInt<UInt<UInt<UTerm, B1>, B0>>;

    #[allow(non_camel_case_types)]
    type P4PartialDivN2 = <<A as PartialDiv<B>>::Output as Same<N2>>::Output;

    assert_eq!(<P4PartialDivN2 as Integer>::to_i64(), <N2 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_P4_Cmp_N2() {
    type A = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>>;
    type B = NInt<UInt<UInt<UTerm, B1>, B0>>;

    #[allow(non_camel_case_types)]
    type P4CmpN2 = <A as Cmp<B>>::Output;
    assert_eq!(<P4CmpN2 as Ord>::to_ordering(), Ordering::Greater);
}
#[test]
#[allow(non_snake_case)]
fn test_P4_Add_N1() {
    type A = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>>;
    type B = NInt<UInt<UTerm, B1>>;
    type P3 = PInt<UInt<UInt<UTerm, B1>, B1>>;

    #[allow(non_camel_case_types)]
    type P4AddN1 = <<A as Add<B>>::Output as Same<P3>>::Output;

    assert_eq!(<P4AddN1 as Integer>::to_i64(), <P3 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_P4_Sub_N1() {
    type A = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>>;
    type B = NInt<UInt<UTerm, B1>>;
    type P5 = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>>;

    #[allow(non_camel_case_types)]
    type P4SubN1 = <<A as Sub<B>>::Output as Same<P5>>::Output;

    assert_eq!(<P4SubN1 as Integer>::to_i64(), <P5 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_P4_Mul_N1() {
    type A = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>>;
    type B = NInt<UInt<UTerm, B1>>;
    type N4 = NInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>>;

    #[allow(non_camel_case_types)]
    type P4MulN1 = <<A as Mul<B>>::Output as Same<N4>>::Output;

    assert_eq!(<P4MulN1 as Integer>::to_i64(), <N4 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_P4_Min_N1() {
    type A = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>>;
    type B = NInt<UInt<UTerm, B1>>;
    type N1 = NInt<UInt<UTerm, B1>>;

    #[allow(non_camel_case_types)]
    type P4MinN1 = <<A as Min<B>>::Output as Same<N1>>::Output;

    assert_eq!(<P4MinN1 as Integer>::to_i64(), <N1 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_P4_Max_N1() {
    type A = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>>;
    type B = NInt<UInt<UTerm, B1>>;
    type P4 = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>>;

    #[allow(non_camel_case_types)]
    type P4MaxN1 = <<A as Max<B>>::Output as Same<P4>>::Output;

    assert_eq!(<P4MaxN1 as Integer>::to_i64(), <P4 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_P4_Gcd_N1() {
    type A = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>>;
    type B = NInt<UInt<UTerm, B1>>;
    type P1 = PInt<UInt<UTerm, B1>>;

    #[allow(non_camel_case_types)]
    type P4GcdN1 = <<A as Gcd<B>>::Output as Same<P1>>::Output;

    assert_eq!(<P4GcdN1 as Integer>::to_i64(), <P1 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_P4_Div_N1() {
    type A = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>>;
    type B = NInt<UInt<UTerm, B1>>;
    type N4 = NInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>>;

    #[allow(non_camel_case_types)]
    type P4DivN1 = <<A as Div<B>>::Output as Same<N4>>::Output;

    assert_eq!(<P4DivN1 as Integer>::to_i64(), <N4 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_P4_Rem_N1() {
    type A = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>>;
    type B = NInt<UInt<UTerm, B1>>;
    type _0 = Z0;

    #[allow(non_camel_case_types)]
    type P4RemN1 = <<A as Rem<B>>::Output as Same<_0>>::Output;

    assert_eq!(<P4RemN1 as Integer>::to_i64(), <_0 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_P4_PartialDiv_N1() {
    type A = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>>;
    type B = NInt<UInt<UTerm, B1>>;
    type N4 = NInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>>;

    #[allow(non_camel_case_types)]
    type P4PartialDivN1 = <<A as PartialDiv<B>>::Output as Same<N4>>::Output;

    assert_eq!(<P4PartialDivN1 as Integer>::to_i64(), <N4 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_P4_Cmp_N1() {
    type A = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>>;
    type B = NInt<UInt<UTerm, B1>>;

    #[allow(non_camel_case_types)]
    type P4CmpN1 = <A as Cmp<B>>::Output;
    assert_eq!(<P4CmpN1 as Ord>::to_ordering(), Ordering::Greater);
}
#[test]
#[allow(non_snake_case)]
fn test_P4_Add__0() {
    type A = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>>;
    type B = Z0;
    type P4 = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>>;

    #[allow(non_camel_case_types)]
    type P4Add_0 = <<A as Add<B>>::Output as Same<P4>>::Output;

    assert_eq!(<P4Add_0 as Integer>::to_i64(), <P4 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_P4_Sub__0() {
    type A = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>>;
    type B = Z0;
    type P4 = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>>;

    #[allow(non_camel_case_types)]
    type P4Sub_0 = <<A as Sub<B>>::Output as Same<P4>>::Output;

    assert_eq!(<P4Sub_0 as Integer>::to_i64(), <P4 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_P4_Mul__0() {
    type A = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>>;
    type B = Z0;
    type _0 = Z0;

    #[allow(non_camel_case_types)]
    type P4Mul_0 = <<A as Mul<B>>::Output as Same<_0>>::Output;

    assert_eq!(<P4Mul_0 as Integer>::to_i64(), <_0 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_P4_Min__0() {
    type A = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>>;
    type B = Z0;
    type _0 = Z0;

    #[allow(non_camel_case_types)]
    type P4Min_0 = <<A as Min<B>>::Output as Same<_0>>::Output;

    assert_eq!(<P4Min_0 as Integer>::to_i64(), <_0 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_P4_Max__0() {
    type A = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>>;
    type B = Z0;
    type P4 = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>>;

    #[allow(non_camel_case_types)]
    type P4Max_0 = <<A as Max<B>>::Output as Same<P4>>::Output;

    assert_eq!(<P4Max_0 as Integer>::to_i64(), <P4 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_P4_Gcd__0() {
    type A = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>>;
    type B = Z0;
    type P4 = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>>;

    #[allow(non_camel_case_types)]
    type P4Gcd_0 = <<A as Gcd<B>>::Output as Same<P4>>::Output;

    assert_eq!(<P4Gcd_0 as Integer>::to_i64(), <P4 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_P4_Pow__0() {
    type A = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>>;
    type B = Z0;
    type P1 = PInt<UInt<UTerm, B1>>;

    #[allow(non_camel_case_types)]
    type P4Pow_0 = <<A as Pow<B>>::Output as Same<P1>>::Output;

    assert_eq!(<P4Pow_0 as Integer>::to_i64(), <P1 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_P4_Cmp__0() {
    type A = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>>;
    type B = Z0;

    #[allow(non_camel_case_types)]
    type P4Cmp_0 = <A as Cmp<B>>::Output;
    assert_eq!(<P4Cmp_0 as Ord>::to_ordering(), Ordering::Greater);
}
#[test]
#[allow(non_snake_case)]
fn test_P4_Add_P1() {
    type A = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>>;
    type B = PInt<UInt<UTerm, B1>>;
    type P5 = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>>;

    #[allow(non_camel_case_types)]
    type P4AddP1 = <<A as Add<B>>::Output as Same<P5>>::Output;

    assert_eq!(<P4AddP1 as Integer>::to_i64(), <P5 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_P4_Sub_P1() {
    type A = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>>;
    type B = PInt<UInt<UTerm, B1>>;
    type P3 = PInt<UInt<UInt<UTerm, B1>, B1>>;

    #[allow(non_camel_case_types)]
    type P4SubP1 = <<A as Sub<B>>::Output as Same<P3>>::Output;

    assert_eq!(<P4SubP1 as Integer>::to_i64(), <P3 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_P4_Mul_P1() {
    type A = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>>;
    type B = PInt<UInt<UTerm, B1>>;
    type P4 = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>>;

    #[allow(non_camel_case_types)]
    type P4MulP1 = <<A as Mul<B>>::Output as Same<P4>>::Output;

    assert_eq!(<P4MulP1 as Integer>::to_i64(), <P4 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_P4_Min_P1() {
    type A = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>>;
    type B = PInt<UInt<UTerm, B1>>;
    type P1 = PInt<UInt<UTerm, B1>>;

    #[allow(non_camel_case_types)]
    type P4MinP1 = <<A as Min<B>>::Output as Same<P1>>::Output;

    assert_eq!(<P4MinP1 as Integer>::to_i64(), <P1 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_P4_Max_P1() {
    type A = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>>;
    type B = PInt<UInt<UTerm, B1>>;
    type P4 = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>>;

    #[allow(non_camel_case_types)]
    type P4MaxP1 = <<A as Max<B>>::Output as Same<P4>>::Output;

    assert_eq!(<P4MaxP1 as Integer>::to_i64(), <P4 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_P4_Gcd_P1() {
    type A = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>>;
    type B = PInt<UInt<UTerm, B1>>;
    type P1 = PInt<UInt<UTerm, B1>>;

    #[allow(non_camel_case_types)]
    type P4GcdP1 = <<A as Gcd<B>>::Output as Same<P1>>::Output;

    assert_eq!(<P4GcdP1 as Integer>::to_i64(), <P1 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_P4_Div_P1() {
    type A = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>>;
    type B = PInt<UInt<UTerm, B1>>;
    type P4 = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>>;

    #[allow(non_camel_case_types)]
    type P4DivP1 = <<A as Div<B>>::Output as Same<P4>>::Output;

    assert_eq!(<P4DivP1 as Integer>::to_i64(), <P4 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_P4_Rem_P1() {
    type A = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>>;
    type B = PInt<UInt<UTerm, B1>>;
    type _0 = Z0;

    #[allow(non_camel_case_types)]
    type P4RemP1 = <<A as Rem<B>>::Output as Same<_0>>::Output;

    assert_eq!(<P4RemP1 as Integer>::to_i64(), <_0 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_P4_PartialDiv_P1() {
    type A = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>>;
    type B = PInt<UInt<UTerm, B1>>;
    type P4 = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>>;

    #[allow(non_camel_case_types)]
    type P4PartialDivP1 = <<A as PartialDiv<B>>::Output as Same<P4>>::Output;

    assert_eq!(<P4PartialDivP1 as Integer>::to_i64(), <P4 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_P4_Pow_P1() {
    type A = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>>;
    type B = PInt<UInt<UTerm, B1>>;
    type P4 = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>>;

    #[allow(non_camel_case_types)]
    type P4PowP1 = <<A as Pow<B>>::Output as Same<P4>>::Output;

    assert_eq!(<P4PowP1 as Integer>::to_i64(), <P4 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_P4_Cmp_P1() {
    type A = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>>;
    type B = PInt<UInt<UTerm, B1>>;

    #[allow(non_camel_case_types)]
    type P4CmpP1 = <A as Cmp<B>>::Output;
    assert_eq!(<P4CmpP1 as Ord>::to_ordering(), Ordering::Greater);
}
#[test]
#[allow(non_snake_case)]
fn test_P4_Add_P2() {
    type A = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>>;
    type B = PInt<UInt<UInt<UTerm, B1>, B0>>;
    type P6 = PInt<UInt<UInt<UInt<UTerm, B1>, B1>, B0>>;

    #[allow(non_camel_case_types)]
    type P4AddP2 = <<A as Add<B>>::Output as Same<P6>>::Output;

    assert_eq!(<P4AddP2 as Integer>::to_i64(), <P6 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_P4_Sub_P2() {
    type A = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>>;
    type B = PInt<UInt<UInt<UTerm, B1>, B0>>;
    type P2 = PInt<UInt<UInt<UTerm, B1>, B0>>;

    #[allow(non_camel_case_types)]
    type P4SubP2 = <<A as Sub<B>>::Output as Same<P2>>::Output;

    assert_eq!(<P4SubP2 as Integer>::to_i64(), <P2 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_P4_Mul_P2() {
    type A = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>>;
    type B = PInt<UInt<UInt<UTerm, B1>, B0>>;
    type P8 = PInt<UInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>, B0>>;

    #[allow(non_camel_case_types)]
    type P4MulP2 = <<A as Mul<B>>::Output as Same<P8>>::Output;

    assert_eq!(<P4MulP2 as Integer>::to_i64(), <P8 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_P4_Min_P2() {
    type A = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>>;
    type B = PInt<UInt<UInt<UTerm, B1>, B0>>;
    type P2 = PInt<UInt<UInt<UTerm, B1>, B0>>;

    #[allow(non_camel_case_types)]
    type P4MinP2 = <<A as Min<B>>::Output as Same<P2>>::Output;

    assert_eq!(<P4MinP2 as Integer>::to_i64(), <P2 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_P4_Max_P2() {
    type A = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>>;
    type B = PInt<UInt<UInt<UTerm, B1>, B0>>;
    type P4 = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>>;

    #[allow(non_camel_case_types)]
    type P4MaxP2 = <<A as Max<B>>::Output as Same<P4>>::Output;

    assert_eq!(<P4MaxP2 as Integer>::to_i64(), <P4 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_P4_Gcd_P2() {
    type A = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>>;
    type B = PInt<UInt<UInt<UTerm, B1>, B0>>;
    type P2 = PInt<UInt<UInt<UTerm, B1>, B0>>;

    #[allow(non_camel_case_types)]
    type P4GcdP2 = <<A as Gcd<B>>::Output as Same<P2>>::Output;

    assert_eq!(<P4GcdP2 as Integer>::to_i64(), <P2 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_P4_Div_P2() {
    type A = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>>;
    type B = PInt<UInt<UInt<UTerm, B1>, B0>>;
    type P2 = PInt<UInt<UInt<UTerm, B1>, B0>>;

    #[allow(non_camel_case_types)]
    type P4DivP2 = <<A as Div<B>>::Output as Same<P2>>::Output;

    assert_eq!(<P4DivP2 as Integer>::to_i64(), <P2 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_P4_Rem_P2() {
    type A = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>>;
    type B = PInt<UInt<UInt<UTerm, B1>, B0>>;
    type _0 = Z0;

    #[allow(non_camel_case_types)]
    type P4RemP2 = <<A as Rem<B>>::Output as Same<_0>>::Output;

    assert_eq!(<P4RemP2 as Integer>::to_i64(), <_0 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_P4_PartialDiv_P2() {
    type A = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>>;
    type B = PInt<UInt<UInt<UTerm, B1>, B0>>;
    type P2 = PInt<UInt<UInt<UTerm, B1>, B0>>;

    #[allow(non_camel_case_types)]
    type P4PartialDivP2 = <<A as PartialDiv<B>>::Output as Same<P2>>::Output;

    assert_eq!(<P4PartialDivP2 as Integer>::to_i64(), <P2 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_P4_Pow_P2() {
    type A = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>>;
    type B = PInt<UInt<UInt<UTerm, B1>, B0>>;
    type P16 = PInt<UInt<UInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>, B0>, B0>>;

    #[allow(non_camel_case_types)]
    type P4PowP2 = <<A as Pow<B>>::Output as Same<P16>>::Output;

    assert_eq!(<P4PowP2 as Integer>::to_i64(), <P16 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_P4_Cmp_P2() {
    type A = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>>;
    type B = PInt<UInt<UInt<UTerm, B1>, B0>>;

    #[allow(non_camel_case_types)]
    type P4CmpP2 = <A as Cmp<B>>::Output;
    assert_eq!(<P4CmpP2 as Ord>::to_ordering(), Ordering::Greater);
}
#[test]
#[allow(non_snake_case)]
fn test_P4_Add_P3() {
    type A = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>>;
    type B = PInt<UInt<UInt<UTerm, B1>, B1>>;
    type P7 = PInt<UInt<UInt<UInt<UTerm, B1>, B1>, B1>>;

    #[allow(non_camel_case_types)]
    type P4AddP3 = <<A as Add<B>>::Output as Same<P7>>::Output;

    assert_eq!(<P4AddP3 as Integer>::to_i64(), <P7 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_P4_Sub_P3() {
    type A = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>>;
    type B = PInt<UInt<UInt<UTerm, B1>, B1>>;
    type P1 = PInt<UInt<UTerm, B1>>;

    #[allow(non_camel_case_types)]
    type P4SubP3 = <<A as Sub<B>>::Output as Same<P1>>::Output;

    assert_eq!(<P4SubP3 as Integer>::to_i64(), <P1 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_P4_Mul_P3() {
    type A = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>>;
    type B = PInt<UInt<UInt<UTerm, B1>, B1>>;
    type P12 = PInt<UInt<UInt<UInt<UInt<UTerm, B1>, B1>, B0>, B0>>;

    #[allow(non_camel_case_types)]
    type P4MulP3 = <<A as Mul<B>>::Output as Same<P12>>::Output;

    assert_eq!(<P4MulP3 as Integer>::to_i64(), <P12 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_P4_Min_P3() {
    type A = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>>;
    type B = PInt<UInt<UInt<UTerm, B1>, B1>>;
    type P3 = PInt<UInt<UInt<UTerm, B1>, B1>>;

    #[allow(non_camel_case_types)]
    type P4MinP3 = <<A as Min<B>>::Output as Same<P3>>::Output;

    assert_eq!(<P4MinP3 as Integer>::to_i64(), <P3 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_P4_Max_P3() {
    type A = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>>;
    type B = PInt<UInt<UInt<UTerm, B1>, B1>>;
    type P4 = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>>;

    #[allow(non_camel_case_types)]
    type P4MaxP3 = <<A as Max<B>>::Output as Same<P4>>::Output;

    assert_eq!(<P4MaxP3 as Integer>::to_i64(), <P4 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_P4_Gcd_P3() {
    type A = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>>;
    type B = PInt<UInt<UInt<UTerm, B1>, B1>>;
    type P1 = PInt<UInt<UTerm, B1>>;

    #[allow(non_camel_case_types)]
    type P4GcdP3 = <<A as Gcd<B>>::Output as Same<P1>>::Output;

    assert_eq!(<P4GcdP3 as Integer>::to_i64(), <P1 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_P4_Div_P3() {
    type A = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>>;
    type B = PInt<UInt<UInt<UTerm, B1>, B1>>;
    type P1 = PInt<UInt<UTerm, B1>>;

    #[allow(non_camel_case_types)]
    type P4DivP3 = <<A as Div<B>>::Output as Same<P1>>::Output;

    assert_eq!(<P4DivP3 as Integer>::to_i64(), <P1 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_P4_Rem_P3() {
    type A = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>>;
    type B = PInt<UInt<UInt<UTerm, B1>, B1>>;
    type P1 = PInt<UInt<UTerm, B1>>;

    #[allow(non_camel_case_types)]
    type P4RemP3 = <<A as Rem<B>>::Output as Same<P1>>::Output;

    assert_eq!(<P4RemP3 as Integer>::to_i64(), <P1 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_P4_Pow_P3() {
    type A = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>>;
    type B = PInt<UInt<UInt<UTerm, B1>, B1>>;
    type P64 = PInt<UInt<UInt<UInt<UInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>, B0>, B0>, B0>, B0>>;

    #[allow(non_camel_case_types)]
    type P4PowP3 = <<A as Pow<B>>::Output as Same<P64>>::Output;

    assert_eq!(<P4PowP3 as Integer>::to_i64(), <P64 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_P4_Cmp_P3() {
    type A = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>>;
    type B = PInt<UInt<UInt<UTerm, B1>, B1>>;

    #[allow(non_camel_case_types)]
    type P4CmpP3 = <A as Cmp<B>>::Output;
    assert_eq!(<P4CmpP3 as Ord>::to_ordering(), Ordering::Greater);
}
#[test]
#[allow(non_snake_case)]
fn test_P4_Add_P4() {
    type A = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>>;
    type B = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>>;
    type P8 = PInt<UInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>, B0>>;

    #[allow(non_camel_case_types)]
    type P4AddP4 = <<A as Add<B>>::Output as Same<P8>>::Output;

    assert_eq!(<P4AddP4 as Integer>::to_i64(), <P8 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_P4_Sub_P4() {
    type A = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>>;
    type B = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>>;
    type _0 = Z0;

    #[allow(non_camel_case_types)]
    type P4SubP4 = <<A as Sub<B>>::Output as Same<_0>>::Output;

    assert_eq!(<P4SubP4 as Integer>::to_i64(), <_0 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_P4_Mul_P4() {
    type A = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>>;
    type B = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>>;
    type P16 = PInt<UInt<UInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>, B0>, B0>>;

    #[allow(non_camel_case_types)]
    type P4MulP4 = <<A as Mul<B>>::Output as Same<P16>>::Output;

    assert_eq!(<P4MulP4 as Integer>::to_i64(), <P16 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_P4_Min_P4() {
    type A = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>>;
    type B = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>>;
    type P4 = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>>;

    #[allow(non_camel_case_types)]
    type P4MinP4 = <<A as Min<B>>::Output as Same<P4>>::Output;

    assert_eq!(<P4MinP4 as Integer>::to_i64(), <P4 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_P4_Max_P4() {
    type A = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>>;
    type B = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>>;
    type P4 = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>>;

    #[allow(non_camel_case_types)]
    type P4MaxP4 = <<A as Max<B>>::Output as Same<P4>>::Output;

    assert_eq!(<P4MaxP4 as Integer>::to_i64(), <P4 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_P4_Gcd_P4() {
    type A = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>>;
    type B = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>>;
    type P4 = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>>;

    #[allow(non_camel_case_types)]
    type P4GcdP4 = <<A as Gcd<B>>::Output as Same<P4>>::Output;

    assert_eq!(<P4GcdP4 as Integer>::to_i64(), <P4 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_P4_Div_P4() {
    type A = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>>;
    type B = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>>;
    type P1 = PInt<UInt<UTerm, B1>>;

    #[allow(non_camel_case_types)]
    type P4DivP4 = <<A as Div<B>>::Output as Same<P1>>::Output;

    assert_eq!(<P4DivP4 as Integer>::to_i64(), <P1 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_P4_Rem_P4() {
    type A = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>>;
    type B = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>>;
    type _0 = Z0;

    #[allow(non_camel_case_types)]
    type P4RemP4 = <<A as Rem<B>>::Output as Same<_0>>::Output;

    assert_eq!(<P4RemP4 as Integer>::to_i64(), <_0 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_P4_PartialDiv_P4() {
    type A = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>>;
    type B = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>>;
    type P1 = PInt<UInt<UTerm, B1>>;

    #[allow(non_camel_case_types)]
    type P4PartialDivP4 = <<A as PartialDiv<B>>::Output as Same<P1>>::Output;

    assert_eq!(<P4PartialDivP4 as Integer>::to_i64(), <P1 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_P4_Pow_P4() {
    type A = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>>;
    type B = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>>;
    type P256 = PInt<UInt<UInt<UInt<UInt<UInt<UInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>, B0>, B0>, B0>, B0>, B0>, B0>>;

    #[allow(non_camel_case_types)]
    type P4PowP4 = <<A as Pow<B>>::Output as Same<P256>>::Output;

    assert_eq!(<P4PowP4 as Integer>::to_i64(), <P256 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_P4_Cmp_P4() {
    type A = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>>;
    type B = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>>;

    #[allow(non_camel_case_types)]
    type P4CmpP4 = <A as Cmp<B>>::Output;
    assert_eq!(<P4CmpP4 as Ord>::to_ordering(), Ordering::Equal);
}
#[test]
#[allow(non_snake_case)]
fn test_P4_Add_P5() {
    type A = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>>;
    type B = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>>;
    type P9 = PInt<UInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>, B1>>;

    #[allow(non_camel_case_types)]
    type P4AddP5 = <<A as Add<B>>::Output as Same<P9>>::Output;

    assert_eq!(<P4AddP5 as Integer>::to_i64(), <P9 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_P4_Sub_P5() {
    type A = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>>;
    type B = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>>;
    type N1 = NInt<UInt<UTerm, B1>>;

    #[allow(non_camel_case_types)]
    type P4SubP5 = <<A as Sub<B>>::Output as Same<N1>>::Output;

    assert_eq!(<P4SubP5 as Integer>::to_i64(), <N1 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_P4_Mul_P5() {
    type A = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>>;
    type B = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>>;
    type P20 = PInt<UInt<UInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>, B0>, B0>>;

    #[allow(non_camel_case_types)]
    type P4MulP5 = <<A as Mul<B>>::Output as Same<P20>>::Output;

    assert_eq!(<P4MulP5 as Integer>::to_i64(), <P20 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_P4_Min_P5() {
    type A = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>>;
    type B = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>>;
    type P4 = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>>;

    #[allow(non_camel_case_types)]
    type P4MinP5 = <<A as Min<B>>::Output as Same<P4>>::Output;

    assert_eq!(<P4MinP5 as Integer>::to_i64(), <P4 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_P4_Max_P5() {
    type A = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>>;
    type B = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>>;
    type P5 = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>>;

    #[allow(non_camel_case_types)]
    type P4MaxP5 = <<A as Max<B>>::Output as Same<P5>>::Output;

    assert_eq!(<P4MaxP5 as Integer>::to_i64(), <P5 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_P4_Gcd_P5() {
    type A = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>>;
    type B = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>>;
    type P1 = PInt<UInt<UTerm, B1>>;

    #[allow(non_camel_case_types)]
    type P4GcdP5 = <<A as Gcd<B>>::Output as Same<P1>>::Output;

    assert_eq!(<P4GcdP5 as Integer>::to_i64(), <P1 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_P4_Div_P5() {
    type A = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>>;
    type B = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>>;
    type _0 = Z0;

    #[allow(non_camel_case_types)]
    type P4DivP5 = <<A as Div<B>>::Output as Same<_0>>::Output;

    assert_eq!(<P4DivP5 as Integer>::to_i64(), <_0 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_P4_Rem_P5() {
    type A = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>>;
    type B = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>>;
    type P4 = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>>;

    #[allow(non_camel_case_types)]
    type P4RemP5 = <<A as Rem<B>>::Output as Same<P4>>::Output;

    assert_eq!(<P4RemP5 as Integer>::to_i64(), <P4 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_P4_Pow_P5() {
    type A = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>>;
    type B = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>>;
    type P1024 = PInt<UInt<UInt<UInt<UInt<UInt<UInt<UInt<UInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>, B0>, B0>, B0>, B0>, B0>, B0>, B0>, B0>>;

    #[allow(non_camel_case_types)]
    type P4PowP5 = <<A as Pow<B>>::Output as Same<P1024>>::Output;

    assert_eq!(<P4PowP5 as Integer>::to_i64(), <P1024 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_P4_Cmp_P5() {
    type A = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>>;
    type B = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>>;

    #[allow(non_camel_case_types)]
    type P4CmpP5 = <A as Cmp<B>>::Output;
    assert_eq!(<P4CmpP5 as Ord>::to_ordering(), Ordering::Less);
}
#[test]
#[allow(non_snake_case)]
fn test_P5_Add_N5() {
    type A = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>>;
    type B = NInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>>;
    type _0 = Z0;

    #[allow(non_camel_case_types)]
    type P5AddN5 = <<A as Add<B>>::Output as Same<_0>>::Output;

    assert_eq!(<P5AddN5 as Integer>::to_i64(), <_0 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_P5_Sub_N5() {
    type A = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>>;
    type B = NInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>>;
    type P10 = PInt<UInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>, B0>>;

    #[allow(non_camel_case_types)]
    type P5SubN5 = <<A as Sub<B>>::Output as Same<P10>>::Output;

    assert_eq!(<P5SubN5 as Integer>::to_i64(), <P10 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_P5_Mul_N5() {
    type A = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>>;
    type B = NInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>>;
    type N25 = NInt<UInt<UInt<UInt<UInt<UInt<UTerm, B1>, B1>, B0>, B0>, B1>>;

    #[allow(non_camel_case_types)]
    type P5MulN5 = <<A as Mul<B>>::Output as Same<N25>>::Output;

    assert_eq!(<P5MulN5 as Integer>::to_i64(), <N25 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_P5_Min_N5() {
    type A = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>>;
    type B = NInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>>;
    type N5 = NInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>>;

    #[allow(non_camel_case_types)]
    type P5MinN5 = <<A as Min<B>>::Output as Same<N5>>::Output;

    assert_eq!(<P5MinN5 as Integer>::to_i64(), <N5 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_P5_Max_N5() {
    type A = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>>;
    type B = NInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>>;
    type P5 = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>>;

    #[allow(non_camel_case_types)]
    type P5MaxN5 = <<A as Max<B>>::Output as Same<P5>>::Output;

    assert_eq!(<P5MaxN5 as Integer>::to_i64(), <P5 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_P5_Gcd_N5() {
    type A = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>>;
    type B = NInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>>;
    type P5 = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>>;

    #[allow(non_camel_case_types)]
    type P5GcdN5 = <<A as Gcd<B>>::Output as Same<P5>>::Output;

    assert_eq!(<P5GcdN5 as Integer>::to_i64(), <P5 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_P5_Div_N5() {
    type A = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>>;
    type B = NInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>>;
    type N1 = NInt<UInt<UTerm, B1>>;

    #[allow(non_camel_case_types)]
    type P5DivN5 = <<A as Div<B>>::Output as Same<N1>>::Output;

    assert_eq!(<P5DivN5 as Integer>::to_i64(), <N1 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_P5_Rem_N5() {
    type A = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>>;
    type B = NInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>>;
    type _0 = Z0;

    #[allow(non_camel_case_types)]
    type P5RemN5 = <<A as Rem<B>>::Output as Same<_0>>::Output;

    assert_eq!(<P5RemN5 as Integer>::to_i64(), <_0 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_P5_PartialDiv_N5() {
    type A = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>>;
    type B = NInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>>;
    type N1 = NInt<UInt<UTerm, B1>>;

    #[allow(non_camel_case_types)]
    type P5PartialDivN5 = <<A as PartialDiv<B>>::Output as Same<N1>>::Output;

    assert_eq!(<P5PartialDivN5 as Integer>::to_i64(), <N1 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_P5_Cmp_N5() {
    type A = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>>;
    type B = NInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>>;

    #[allow(non_camel_case_types)]
    type P5CmpN5 = <A as Cmp<B>>::Output;
    assert_eq!(<P5CmpN5 as Ord>::to_ordering(), Ordering::Greater);
}
#[test]
#[allow(non_snake_case)]
fn test_P5_Add_N4() {
    type A = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>>;
    type B = NInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>>;
    type P1 = PInt<UInt<UTerm, B1>>;

    #[allow(non_camel_case_types)]
    type P5AddN4 = <<A as Add<B>>::Output as Same<P1>>::Output;

    assert_eq!(<P5AddN4 as Integer>::to_i64(), <P1 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_P5_Sub_N4() {
    type A = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>>;
    type B = NInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>>;
    type P9 = PInt<UInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>, B1>>;

    #[allow(non_camel_case_types)]
    type P5SubN4 = <<A as Sub<B>>::Output as Same<P9>>::Output;

    assert_eq!(<P5SubN4 as Integer>::to_i64(), <P9 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_P5_Mul_N4() {
    type A = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>>;
    type B = NInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>>;
    type N20 = NInt<UInt<UInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>, B0>, B0>>;

    #[allow(non_camel_case_types)]
    type P5MulN4 = <<A as Mul<B>>::Output as Same<N20>>::Output;

    assert_eq!(<P5MulN4 as Integer>::to_i64(), <N20 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_P5_Min_N4() {
    type A = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>>;
    type B = NInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>>;
    type N4 = NInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>>;

    #[allow(non_camel_case_types)]
    type P5MinN4 = <<A as Min<B>>::Output as Same<N4>>::Output;

    assert_eq!(<P5MinN4 as Integer>::to_i64(), <N4 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_P5_Max_N4() {
    type A = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>>;
    type B = NInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>>;
    type P5 = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>>;

    #[allow(non_camel_case_types)]
    type P5MaxN4 = <<A as Max<B>>::Output as Same<P5>>::Output;

    assert_eq!(<P5MaxN4 as Integer>::to_i64(), <P5 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_P5_Gcd_N4() {
    type A = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>>;
    type B = NInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>>;
    type P1 = PInt<UInt<UTerm, B1>>;

    #[allow(non_camel_case_types)]
    type P5GcdN4 = <<A as Gcd<B>>::Output as Same<P1>>::Output;

    assert_eq!(<P5GcdN4 as Integer>::to_i64(), <P1 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_P5_Div_N4() {
    type A = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>>;
    type B = NInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>>;
    type N1 = NInt<UInt<UTerm, B1>>;

    #[allow(non_camel_case_types)]
    type P5DivN4 = <<A as Div<B>>::Output as Same<N1>>::Output;

    assert_eq!(<P5DivN4 as Integer>::to_i64(), <N1 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_P5_Rem_N4() {
    type A = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>>;
    type B = NInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>>;
    type P1 = PInt<UInt<UTerm, B1>>;

    #[allow(non_camel_case_types)]
    type P5RemN4 = <<A as Rem<B>>::Output as Same<P1>>::Output;

    assert_eq!(<P5RemN4 as Integer>::to_i64(), <P1 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_P5_Cmp_N4() {
    type A = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>>;
    type B = NInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>>;

    #[allow(non_camel_case_types)]
    type P5CmpN4 = <A as Cmp<B>>::Output;
    assert_eq!(<P5CmpN4 as Ord>::to_ordering(), Ordering::Greater);
}
#[test]
#[allow(non_snake_case)]
fn test_P5_Add_N3() {
    type A = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>>;
    type B = NInt<UInt<UInt<UTerm, B1>, B1>>;
    type P2 = PInt<UInt<UInt<UTerm, B1>, B0>>;

    #[allow(non_camel_case_types)]
    type P5AddN3 = <<A as Add<B>>::Output as Same<P2>>::Output;

    assert_eq!(<P5AddN3 as Integer>::to_i64(), <P2 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_P5_Sub_N3() {
    type A = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>>;
    type B = NInt<UInt<UInt<UTerm, B1>, B1>>;
    type P8 = PInt<UInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>, B0>>;

    #[allow(non_camel_case_types)]
    type P5SubN3 = <<A as Sub<B>>::Output as Same<P8>>::Output;

    assert_eq!(<P5SubN3 as Integer>::to_i64(), <P8 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_P5_Mul_N3() {
    type A = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>>;
    type B = NInt<UInt<UInt<UTerm, B1>, B1>>;
    type N15 = NInt<UInt<UInt<UInt<UInt<UTerm, B1>, B1>, B1>, B1>>;

    #[allow(non_camel_case_types)]
    type P5MulN3 = <<A as Mul<B>>::Output as Same<N15>>::Output;

    assert_eq!(<P5MulN3 as Integer>::to_i64(), <N15 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_P5_Min_N3() {
    type A = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>>;
    type B = NInt<UInt<UInt<UTerm, B1>, B1>>;
    type N3 = NInt<UInt<UInt<UTerm, B1>, B1>>;

    #[allow(non_camel_case_types)]
    type P5MinN3 = <<A as Min<B>>::Output as Same<N3>>::Output;

    assert_eq!(<P5MinN3 as Integer>::to_i64(), <N3 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_P5_Max_N3() {
    type A = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>>;
    type B = NInt<UInt<UInt<UTerm, B1>, B1>>;
    type P5 = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>>;

    #[allow(non_camel_case_types)]
    type P5MaxN3 = <<A as Max<B>>::Output as Same<P5>>::Output;

    assert_eq!(<P5MaxN3 as Integer>::to_i64(), <P5 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_P5_Gcd_N3() {
    type A = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>>;
    type B = NInt<UInt<UInt<UTerm, B1>, B1>>;
    type P1 = PInt<UInt<UTerm, B1>>;

    #[allow(non_camel_case_types)]
    type P5GcdN3 = <<A as Gcd<B>>::Output as Same<P1>>::Output;

    assert_eq!(<P5GcdN3 as Integer>::to_i64(), <P1 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_P5_Div_N3() {
    type A = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>>;
    type B = NInt<UInt<UInt<UTerm, B1>, B1>>;
    type N1 = NInt<UInt<UTerm, B1>>;

    #[allow(non_camel_case_types)]
    type P5DivN3 = <<A as Div<B>>::Output as Same<N1>>::Output;

    assert_eq!(<P5DivN3 as Integer>::to_i64(), <N1 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_P5_Rem_N3() {
    type A = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>>;
    type B = NInt<UInt<UInt<UTerm, B1>, B1>>;
    type P2 = PInt<UInt<UInt<UTerm, B1>, B0>>;

    #[allow(non_camel_case_types)]
    type P5RemN3 = <<A as Rem<B>>::Output as Same<P2>>::Output;

    assert_eq!(<P5RemN3 as Integer>::to_i64(), <P2 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_P5_Cmp_N3() {
    type A = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>>;
    type B = NInt<UInt<UInt<UTerm, B1>, B1>>;

    #[allow(non_camel_case_types)]
    type P5CmpN3 = <A as Cmp<B>>::Output;
    assert_eq!(<P5CmpN3 as Ord>::to_ordering(), Ordering::Greater);
}
#[test]
#[allow(non_snake_case)]
fn test_P5_Add_N2() {
    type A = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>>;
    type B = NInt<UInt<UInt<UTerm, B1>, B0>>;
    type P3 = PInt<UInt<UInt<UTerm, B1>, B1>>;

    #[allow(non_camel_case_types)]
    type P5AddN2 = <<A as Add<B>>::Output as Same<P3>>::Output;

    assert_eq!(<P5AddN2 as Integer>::to_i64(), <P3 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_P5_Sub_N2() {
    type A = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>>;
    type B = NInt<UInt<UInt<UTerm, B1>, B0>>;
    type P7 = PInt<UInt<UInt<UInt<UTerm, B1>, B1>, B1>>;

    #[allow(non_camel_case_types)]
    type P5SubN2 = <<A as Sub<B>>::Output as Same<P7>>::Output;

    assert_eq!(<P5SubN2 as Integer>::to_i64(), <P7 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_P5_Mul_N2() {
    type A = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>>;
    type B = NInt<UInt<UInt<UTerm, B1>, B0>>;
    type N10 = NInt<UInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>, B0>>;

    #[allow(non_camel_case_types)]
    type P5MulN2 = <<A as Mul<B>>::Output as Same<N10>>::Output;

    assert_eq!(<P5MulN2 as Integer>::to_i64(), <N10 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_P5_Min_N2() {
    type A = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>>;
    type B = NInt<UInt<UInt<UTerm, B1>, B0>>;
    type N2 = NInt<UInt<UInt<UTerm, B1>, B0>>;

    #[allow(non_camel_case_types)]
    type P5MinN2 = <<A as Min<B>>::Output as Same<N2>>::Output;

    assert_eq!(<P5MinN2 as Integer>::to_i64(), <N2 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_P5_Max_N2() {
    type A = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>>;
    type B = NInt<UInt<UInt<UTerm, B1>, B0>>;
    type P5 = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>>;

    #[allow(non_camel_case_types)]
    type P5MaxN2 = <<A as Max<B>>::Output as Same<P5>>::Output;

    assert_eq!(<P5MaxN2 as Integer>::to_i64(), <P5 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_P5_Gcd_N2() {
    type A = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>>;
    type B = NInt<UInt<UInt<UTerm, B1>, B0>>;
    type P1 = PInt<UInt<UTerm, B1>>;

    #[allow(non_camel_case_types)]
    type P5GcdN2 = <<A as Gcd<B>>::Output as Same<P1>>::Output;

    assert_eq!(<P5GcdN2 as Integer>::to_i64(), <P1 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_P5_Div_N2() {
    type A = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>>;
    type B = NInt<UInt<UInt<UTerm, B1>, B0>>;
    type N2 = NInt<UInt<UInt<UTerm, B1>, B0>>;

    #[allow(non_camel_case_types)]
    type P5DivN2 = <<A as Div<B>>::Output as Same<N2>>::Output;

    assert_eq!(<P5DivN2 as Integer>::to_i64(), <N2 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_P5_Rem_N2() {
    type A = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>>;
    type B = NInt<UInt<UInt<UTerm, B1>, B0>>;
    type P1 = PInt<UInt<UTerm, B1>>;

    #[allow(non_camel_case_types)]
    type P5RemN2 = <<A as Rem<B>>::Output as Same<P1>>::Output;

    assert_eq!(<P5RemN2 as Integer>::to_i64(), <P1 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_P5_Cmp_N2() {
    type A = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>>;
    type B = NInt<UInt<UInt<UTerm, B1>, B0>>;

    #[allow(non_camel_case_types)]
    type P5CmpN2 = <A as Cmp<B>>::Output;
    assert_eq!(<P5CmpN2 as Ord>::to_ordering(), Ordering::Greater);
}
#[test]
#[allow(non_snake_case)]
fn test_P5_Add_N1() {
    type A = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>>;
    type B = NInt<UInt<UTerm, B1>>;
    type P4 = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>>;

    #[allow(non_camel_case_types)]
    type P5AddN1 = <<A as Add<B>>::Output as Same<P4>>::Output;

    assert_eq!(<P5AddN1 as Integer>::to_i64(), <P4 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_P5_Sub_N1() {
    type A = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>>;
    type B = NInt<UInt<UTerm, B1>>;
    type P6 = PInt<UInt<UInt<UInt<UTerm, B1>, B1>, B0>>;

    #[allow(non_camel_case_types)]
    type P5SubN1 = <<A as Sub<B>>::Output as Same<P6>>::Output;

    assert_eq!(<P5SubN1 as Integer>::to_i64(), <P6 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_P5_Mul_N1() {
    type A = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>>;
    type B = NInt<UInt<UTerm, B1>>;
    type N5 = NInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>>;

    #[allow(non_camel_case_types)]
    type P5MulN1 = <<A as Mul<B>>::Output as Same<N5>>::Output;

    assert_eq!(<P5MulN1 as Integer>::to_i64(), <N5 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_P5_Min_N1() {
    type A = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>>;
    type B = NInt<UInt<UTerm, B1>>;
    type N1 = NInt<UInt<UTerm, B1>>;

    #[allow(non_camel_case_types)]
    type P5MinN1 = <<A as Min<B>>::Output as Same<N1>>::Output;

    assert_eq!(<P5MinN1 as Integer>::to_i64(), <N1 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_P5_Max_N1() {
    type A = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>>;
    type B = NInt<UInt<UTerm, B1>>;
    type P5 = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>>;

    #[allow(non_camel_case_types)]
    type P5MaxN1 = <<A as Max<B>>::Output as Same<P5>>::Output;

    assert_eq!(<P5MaxN1 as Integer>::to_i64(), <P5 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_P5_Gcd_N1() {
    type A = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>>;
    type B = NInt<UInt<UTerm, B1>>;
    type P1 = PInt<UInt<UTerm, B1>>;

    #[allow(non_camel_case_types)]
    type P5GcdN1 = <<A as Gcd<B>>::Output as Same<P1>>::Output;

    assert_eq!(<P5GcdN1 as Integer>::to_i64(), <P1 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_P5_Div_N1() {
    type A = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>>;
    type B = NInt<UInt<UTerm, B1>>;
    type N5 = NInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>>;

    #[allow(non_camel_case_types)]
    type P5DivN1 = <<A as Div<B>>::Output as Same<N5>>::Output;

    assert_eq!(<P5DivN1 as Integer>::to_i64(), <N5 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_P5_Rem_N1() {
    type A = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>>;
    type B = NInt<UInt<UTerm, B1>>;
    type _0 = Z0;

    #[allow(non_camel_case_types)]
    type P5RemN1 = <<A as Rem<B>>::Output as Same<_0>>::Output;

    assert_eq!(<P5RemN1 as Integer>::to_i64(), <_0 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_P5_PartialDiv_N1() {
    type A = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>>;
    type B = NInt<UInt<UTerm, B1>>;
    type N5 = NInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>>;

    #[allow(non_camel_case_types)]
    type P5PartialDivN1 = <<A as PartialDiv<B>>::Output as Same<N5>>::Output;

    assert_eq!(<P5PartialDivN1 as Integer>::to_i64(), <N5 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_P5_Cmp_N1() {
    type A = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>>;
    type B = NInt<UInt<UTerm, B1>>;

    #[allow(non_camel_case_types)]
    type P5CmpN1 = <A as Cmp<B>>::Output;
    assert_eq!(<P5CmpN1 as Ord>::to_ordering(), Ordering::Greater);
}
#[test]
#[allow(non_snake_case)]
fn test_P5_Add__0() {
    type A = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>>;
    type B = Z0;
    type P5 = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>>;

    #[allow(non_camel_case_types)]
    type P5Add_0 = <<A as Add<B>>::Output as Same<P5>>::Output;

    assert_eq!(<P5Add_0 as Integer>::to_i64(), <P5 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_P5_Sub__0() {
    type A = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>>;
    type B = Z0;
    type P5 = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>>;

    #[allow(non_camel_case_types)]
    type P5Sub_0 = <<A as Sub<B>>::Output as Same<P5>>::Output;

    assert_eq!(<P5Sub_0 as Integer>::to_i64(), <P5 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_P5_Mul__0() {
    type A = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>>;
    type B = Z0;
    type _0 = Z0;

    #[allow(non_camel_case_types)]
    type P5Mul_0 = <<A as Mul<B>>::Output as Same<_0>>::Output;

    assert_eq!(<P5Mul_0 as Integer>::to_i64(), <_0 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_P5_Min__0() {
    type A = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>>;
    type B = Z0;
    type _0 = Z0;

    #[allow(non_camel_case_types)]
    type P5Min_0 = <<A as Min<B>>::Output as Same<_0>>::Output;

    assert_eq!(<P5Min_0 as Integer>::to_i64(), <_0 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_P5_Max__0() {
    type A = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>>;
    type B = Z0;
    type P5 = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>>;

    #[allow(non_camel_case_types)]
    type P5Max_0 = <<A as Max<B>>::Output as Same<P5>>::Output;

    assert_eq!(<P5Max_0 as Integer>::to_i64(), <P5 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_P5_Gcd__0() {
    type A = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>>;
    type B = Z0;
    type P5 = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>>;

    #[allow(non_camel_case_types)]
    type P5Gcd_0 = <<A as Gcd<B>>::Output as Same<P5>>::Output;

    assert_eq!(<P5Gcd_0 as Integer>::to_i64(), <P5 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_P5_Pow__0() {
    type A = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>>;
    type B = Z0;
    type P1 = PInt<UInt<UTerm, B1>>;

    #[allow(non_camel_case_types)]
    type P5Pow_0 = <<A as Pow<B>>::Output as Same<P1>>::Output;

    assert_eq!(<P5Pow_0 as Integer>::to_i64(), <P1 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_P5_Cmp__0() {
    type A = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>>;
    type B = Z0;

    #[allow(non_camel_case_types)]
    type P5Cmp_0 = <A as Cmp<B>>::Output;
    assert_eq!(<P5Cmp_0 as Ord>::to_ordering(), Ordering::Greater);
}
#[test]
#[allow(non_snake_case)]
fn test_P5_Add_P1() {
    type A = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>>;
    type B = PInt<UInt<UTerm, B1>>;
    type P6 = PInt<UInt<UInt<UInt<UTerm, B1>, B1>, B0>>;

    #[allow(non_camel_case_types)]
    type P5AddP1 = <<A as Add<B>>::Output as Same<P6>>::Output;

    assert_eq!(<P5AddP1 as Integer>::to_i64(), <P6 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_P5_Sub_P1() {
    type A = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>>;
    type B = PInt<UInt<UTerm, B1>>;
    type P4 = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>>;

    #[allow(non_camel_case_types)]
    type P5SubP1 = <<A as Sub<B>>::Output as Same<P4>>::Output;

    assert_eq!(<P5SubP1 as Integer>::to_i64(), <P4 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_P5_Mul_P1() {
    type A = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>>;
    type B = PInt<UInt<UTerm, B1>>;
    type P5 = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>>;

    #[allow(non_camel_case_types)]
    type P5MulP1 = <<A as Mul<B>>::Output as Same<P5>>::Output;

    assert_eq!(<P5MulP1 as Integer>::to_i64(), <P5 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_P5_Min_P1() {
    type A = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>>;
    type B = PInt<UInt<UTerm, B1>>;
    type P1 = PInt<UInt<UTerm, B1>>;

    #[allow(non_camel_case_types)]
    type P5MinP1 = <<A as Min<B>>::Output as Same<P1>>::Output;

    assert_eq!(<P5MinP1 as Integer>::to_i64(), <P1 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_P5_Max_P1() {
    type A = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>>;
    type B = PInt<UInt<UTerm, B1>>;
    type P5 = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>>;

    #[allow(non_camel_case_types)]
    type P5MaxP1 = <<A as Max<B>>::Output as Same<P5>>::Output;

    assert_eq!(<P5MaxP1 as Integer>::to_i64(), <P5 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_P5_Gcd_P1() {
    type A = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>>;
    type B = PInt<UInt<UTerm, B1>>;
    type P1 = PInt<UInt<UTerm, B1>>;

    #[allow(non_camel_case_types)]
    type P5GcdP1 = <<A as Gcd<B>>::Output as Same<P1>>::Output;

    assert_eq!(<P5GcdP1 as Integer>::to_i64(), <P1 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_P5_Div_P1() {
    type A = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>>;
    type B = PInt<UInt<UTerm, B1>>;
    type P5 = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>>;

    #[allow(non_camel_case_types)]
    type P5DivP1 = <<A as Div<B>>::Output as Same<P5>>::Output;

    assert_eq!(<P5DivP1 as Integer>::to_i64(), <P5 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_P5_Rem_P1() {
    type A = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>>;
    type B = PInt<UInt<UTerm, B1>>;
    type _0 = Z0;

    #[allow(non_camel_case_types)]
    type P5RemP1 = <<A as Rem<B>>::Output as Same<_0>>::Output;

    assert_eq!(<P5RemP1 as Integer>::to_i64(), <_0 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_P5_PartialDiv_P1() {
    type A = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>>;
    type B = PInt<UInt<UTerm, B1>>;
    type P5 = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>>;

    #[allow(non_camel_case_types)]
    type P5PartialDivP1 = <<A as PartialDiv<B>>::Output as Same<P5>>::Output;

    assert_eq!(<P5PartialDivP1 as Integer>::to_i64(), <P5 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_P5_Pow_P1() {
    type A = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>>;
    type B = PInt<UInt<UTerm, B1>>;
    type P5 = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>>;

    #[allow(non_camel_case_types)]
    type P5PowP1 = <<A as Pow<B>>::Output as Same<P5>>::Output;

    assert_eq!(<P5PowP1 as Integer>::to_i64(), <P5 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_P5_Cmp_P1() {
    type A = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>>;
    type B = PInt<UInt<UTerm, B1>>;

    #[allow(non_camel_case_types)]
    type P5CmpP1 = <A as Cmp<B>>::Output;
    assert_eq!(<P5CmpP1 as Ord>::to_ordering(), Ordering::Greater);
}
#[test]
#[allow(non_snake_case)]
fn test_P5_Add_P2() {
    type A = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>>;
    type B = PInt<UInt<UInt<UTerm, B1>, B0>>;
    type P7 = PInt<UInt<UInt<UInt<UTerm, B1>, B1>, B1>>;

    #[allow(non_camel_case_types)]
    type P5AddP2 = <<A as Add<B>>::Output as Same<P7>>::Output;

    assert_eq!(<P5AddP2 as Integer>::to_i64(), <P7 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_P5_Sub_P2() {
    type A = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>>;
    type B = PInt<UInt<UInt<UTerm, B1>, B0>>;
    type P3 = PInt<UInt<UInt<UTerm, B1>, B1>>;

    #[allow(non_camel_case_types)]
    type P5SubP2 = <<A as Sub<B>>::Output as Same<P3>>::Output;

    assert_eq!(<P5SubP2 as Integer>::to_i64(), <P3 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_P5_Mul_P2() {
    type A = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>>;
    type B = PInt<UInt<UInt<UTerm, B1>, B0>>;
    type P10 = PInt<UInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>, B0>>;

    #[allow(non_camel_case_types)]
    type P5MulP2 = <<A as Mul<B>>::Output as Same<P10>>::Output;

    assert_eq!(<P5MulP2 as Integer>::to_i64(), <P10 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_P5_Min_P2() {
    type A = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>>;
    type B = PInt<UInt<UInt<UTerm, B1>, B0>>;
    type P2 = PInt<UInt<UInt<UTerm, B1>, B0>>;

    #[allow(non_camel_case_types)]
    type P5MinP2 = <<A as Min<B>>::Output as Same<P2>>::Output;

    assert_eq!(<P5MinP2 as Integer>::to_i64(), <P2 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_P5_Max_P2() {
    type A = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>>;
    type B = PInt<UInt<UInt<UTerm, B1>, B0>>;
    type P5 = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>>;

    #[allow(non_camel_case_types)]
    type P5MaxP2 = <<A as Max<B>>::Output as Same<P5>>::Output;

    assert_eq!(<P5MaxP2 as Integer>::to_i64(), <P5 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_P5_Gcd_P2() {
    type A = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>>;
    type B = PInt<UInt<UInt<UTerm, B1>, B0>>;
    type P1 = PInt<UInt<UTerm, B1>>;

    #[allow(non_camel_case_types)]
    type P5GcdP2 = <<A as Gcd<B>>::Output as Same<P1>>::Output;

    assert_eq!(<P5GcdP2 as Integer>::to_i64(), <P1 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_P5_Div_P2() {
    type A = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>>;
    type B = PInt<UInt<UInt<UTerm, B1>, B0>>;
    type P2 = PInt<UInt<UInt<UTerm, B1>, B0>>;

    #[allow(non_camel_case_types)]
    type P5DivP2 = <<A as Div<B>>::Output as Same<P2>>::Output;

    assert_eq!(<P5DivP2 as Integer>::to_i64(), <P2 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_P5_Rem_P2() {
    type A = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>>;
    type B = PInt<UInt<UInt<UTerm, B1>, B0>>;
    type P1 = PInt<UInt<UTerm, B1>>;

    #[allow(non_camel_case_types)]
    type P5RemP2 = <<A as Rem<B>>::Output as Same<P1>>::Output;

    assert_eq!(<P5RemP2 as Integer>::to_i64(), <P1 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_P5_Pow_P2() {
    type A = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>>;
    type B = PInt<UInt<UInt<UTerm, B1>, B0>>;
    type P25 = PInt<UInt<UInt<UInt<UInt<UInt<UTerm, B1>, B1>, B0>, B0>, B1>>;

    #[allow(non_camel_case_types)]
    type P5PowP2 = <<A as Pow<B>>::Output as Same<P25>>::Output;

    assert_eq!(<P5PowP2 as Integer>::to_i64(), <P25 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_P5_Cmp_P2() {
    type A = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>>;
    type B = PInt<UInt<UInt<UTerm, B1>, B0>>;

    #[allow(non_camel_case_types)]
    type P5CmpP2 = <A as Cmp<B>>::Output;
    assert_eq!(<P5CmpP2 as Ord>::to_ordering(), Ordering::Greater);
}
#[test]
#[allow(non_snake_case)]
fn test_P5_Add_P3() {
    type A = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>>;
    type B = PInt<UInt<UInt<UTerm, B1>, B1>>;
    type P8 = PInt<UInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>, B0>>;

    #[allow(non_camel_case_types)]
    type P5AddP3 = <<A as Add<B>>::Output as Same<P8>>::Output;

    assert_eq!(<P5AddP3 as Integer>::to_i64(), <P8 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_P5_Sub_P3() {
    type A = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>>;
    type B = PInt<UInt<UInt<UTerm, B1>, B1>>;
    type P2 = PInt<UInt<UInt<UTerm, B1>, B0>>;

    #[allow(non_camel_case_types)]
    type P5SubP3 = <<A as Sub<B>>::Output as Same<P2>>::Output;

    assert_eq!(<P5SubP3 as Integer>::to_i64(), <P2 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_P5_Mul_P3() {
    type A = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>>;
    type B = PInt<UInt<UInt<UTerm, B1>, B1>>;
    type P15 = PInt<UInt<UInt<UInt<UInt<UTerm, B1>, B1>, B1>, B1>>;

    #[allow(non_camel_case_types)]
    type P5MulP3 = <<A as Mul<B>>::Output as Same<P15>>::Output;

    assert_eq!(<P5MulP3 as Integer>::to_i64(), <P15 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_P5_Min_P3() {
    type A = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>>;
    type B = PInt<UInt<UInt<UTerm, B1>, B1>>;
    type P3 = PInt<UInt<UInt<UTerm, B1>, B1>>;

    #[allow(non_camel_case_types)]
    type P5MinP3 = <<A as Min<B>>::Output as Same<P3>>::Output;

    assert_eq!(<P5MinP3 as Integer>::to_i64(), <P3 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_P5_Max_P3() {
    type A = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>>;
    type B = PInt<UInt<UInt<UTerm, B1>, B1>>;
    type P5 = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>>;

    #[allow(non_camel_case_types)]
    type P5MaxP3 = <<A as Max<B>>::Output as Same<P5>>::Output;

    assert_eq!(<P5MaxP3 as Integer>::to_i64(), <P5 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_P5_Gcd_P3() {
    type A = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>>;
    type B = PInt<UInt<UInt<UTerm, B1>, B1>>;
    type P1 = PInt<UInt<UTerm, B1>>;

    #[allow(non_camel_case_types)]
    type P5GcdP3 = <<A as Gcd<B>>::Output as Same<P1>>::Output;

    assert_eq!(<P5GcdP3 as Integer>::to_i64(), <P1 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_P5_Div_P3() {
    type A = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>>;
    type B = PInt<UInt<UInt<UTerm, B1>, B1>>;
    type P1 = PInt<UInt<UTerm, B1>>;

    #[allow(non_camel_case_types)]
    type P5DivP3 = <<A as Div<B>>::Output as Same<P1>>::Output;

    assert_eq!(<P5DivP3 as Integer>::to_i64(), <P1 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_P5_Rem_P3() {
    type A = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>>;
    type B = PInt<UInt<UInt<UTerm, B1>, B1>>;
    type P2 = PInt<UInt<UInt<UTerm, B1>, B0>>;

    #[allow(non_camel_case_types)]
    type P5RemP3 = <<A as Rem<B>>::Output as Same<P2>>::Output;

    assert_eq!(<P5RemP3 as Integer>::to_i64(), <P2 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_P5_Pow_P3() {
    type A = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>>;
    type B = PInt<UInt<UInt<UTerm, B1>, B1>>;
    type P125 = PInt<UInt<UInt<UInt<UInt<UInt<UInt<UInt<UTerm, B1>, B1>, B1>, B1>, B1>, B0>, B1>>;

    #[allow(non_camel_case_types)]
    type P5PowP3 = <<A as Pow<B>>::Output as Same<P125>>::Output;

    assert_eq!(<P5PowP3 as Integer>::to_i64(), <P125 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_P5_Cmp_P3() {
    type A = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>>;
    type B = PInt<UInt<UInt<UTerm, B1>, B1>>;

    #[allow(non_camel_case_types)]
    type P5CmpP3 = <A as Cmp<B>>::Output;
    assert_eq!(<P5CmpP3 as Ord>::to_ordering(), Ordering::Greater);
}
#[test]
#[allow(non_snake_case)]
fn test_P5_Add_P4() {
    type A = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>>;
    type B = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>>;
    type P9 = PInt<UInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>, B1>>;

    #[allow(non_camel_case_types)]
    type P5AddP4 = <<A as Add<B>>::Output as Same<P9>>::Output;

    assert_eq!(<P5AddP4 as Integer>::to_i64(), <P9 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_P5_Sub_P4() {
    type A = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>>;
    type B = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>>;
    type P1 = PInt<UInt<UTerm, B1>>;

    #[allow(non_camel_case_types)]
    type P5SubP4 = <<A as Sub<B>>::Output as Same<P1>>::Output;

    assert_eq!(<P5SubP4 as Integer>::to_i64(), <P1 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_P5_Mul_P4() {
    type A = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>>;
    type B = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>>;
    type P20 = PInt<UInt<UInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>, B0>, B0>>;

    #[allow(non_camel_case_types)]
    type P5MulP4 = <<A as Mul<B>>::Output as Same<P20>>::Output;

    assert_eq!(<P5MulP4 as Integer>::to_i64(), <P20 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_P5_Min_P4() {
    type A = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>>;
    type B = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>>;
    type P4 = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>>;

    #[allow(non_camel_case_types)]
    type P5MinP4 = <<A as Min<B>>::Output as Same<P4>>::Output;

    assert_eq!(<P5MinP4 as Integer>::to_i64(), <P4 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_P5_Max_P4() {
    type A = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>>;
    type B = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>>;
    type P5 = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>>;

    #[allow(non_camel_case_types)]
    type P5MaxP4 = <<A as Max<B>>::Output as Same<P5>>::Output;

    assert_eq!(<P5MaxP4 as Integer>::to_i64(), <P5 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_P5_Gcd_P4() {
    type A = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>>;
    type B = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>>;
    type P1 = PInt<UInt<UTerm, B1>>;

    #[allow(non_camel_case_types)]
    type P5GcdP4 = <<A as Gcd<B>>::Output as Same<P1>>::Output;

    assert_eq!(<P5GcdP4 as Integer>::to_i64(), <P1 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_P5_Div_P4() {
    type A = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>>;
    type B = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>>;
    type P1 = PInt<UInt<UTerm, B1>>;

    #[allow(non_camel_case_types)]
    type P5DivP4 = <<A as Div<B>>::Output as Same<P1>>::Output;

    assert_eq!(<P5DivP4 as Integer>::to_i64(), <P1 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_P5_Rem_P4() {
    type A = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>>;
    type B = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>>;
    type P1 = PInt<UInt<UTerm, B1>>;

    #[allow(non_camel_case_types)]
    type P5RemP4 = <<A as Rem<B>>::Output as Same<P1>>::Output;

    assert_eq!(<P5RemP4 as Integer>::to_i64(), <P1 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_P5_Pow_P4() {
    type A = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>>;
    type B = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>>;
    type P625 = PInt<UInt<UInt<UInt<UInt<UInt<UInt<UInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>, B1>, B1>, B1>, B0>, B0>, B0>, B1>>;

    #[allow(non_camel_case_types)]
    type P5PowP4 = <<A as Pow<B>>::Output as Same<P625>>::Output;

    assert_eq!(<P5PowP4 as Integer>::to_i64(), <P625 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_P5_Cmp_P4() {
    type A = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>>;
    type B = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>>;

    #[allow(non_camel_case_types)]
    type P5CmpP4 = <A as Cmp<B>>::Output;
    assert_eq!(<P5CmpP4 as Ord>::to_ordering(), Ordering::Greater);
}
#[test]
#[allow(non_snake_case)]
fn test_P5_Add_P5() {
    type A = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>>;
    type B = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>>;
    type P10 = PInt<UInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>, B0>>;

    #[allow(non_camel_case_types)]
    type P5AddP5 = <<A as Add<B>>::Output as Same<P10>>::Output;

    assert_eq!(<P5AddP5 as Integer>::to_i64(), <P10 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_P5_Sub_P5() {
    type A = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>>;
    type B = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>>;
    type _0 = Z0;

    #[allow(non_camel_case_types)]
    type P5SubP5 = <<A as Sub<B>>::Output as Same<_0>>::Output;

    assert_eq!(<P5SubP5 as Integer>::to_i64(), <_0 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_P5_Mul_P5() {
    type A = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>>;
    type B = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>>;
    type P25 = PInt<UInt<UInt<UInt<UInt<UInt<UTerm, B1>, B1>, B0>, B0>, B1>>;

    #[allow(non_camel_case_types)]
    type P5MulP5 = <<A as Mul<B>>::Output as Same<P25>>::Output;

    assert_eq!(<P5MulP5 as Integer>::to_i64(), <P25 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_P5_Min_P5() {
    type A = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>>;
    type B = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>>;
    type P5 = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>>;

    #[allow(non_camel_case_types)]
    type P5MinP5 = <<A as Min<B>>::Output as Same<P5>>::Output;

    assert_eq!(<P5MinP5 as Integer>::to_i64(), <P5 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_P5_Max_P5() {
    type A = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>>;
    type B = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>>;
    type P5 = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>>;

    #[allow(non_camel_case_types)]
    type P5MaxP5 = <<A as Max<B>>::Output as Same<P5>>::Output;

    assert_eq!(<P5MaxP5 as Integer>::to_i64(), <P5 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_P5_Gcd_P5() {
    type A = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>>;
    type B = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>>;
    type P5 = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>>;

    #[allow(non_camel_case_types)]
    type P5GcdP5 = <<A as Gcd<B>>::Output as Same<P5>>::Output;

    assert_eq!(<P5GcdP5 as Integer>::to_i64(), <P5 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_P5_Div_P5() {
    type A = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>>;
    type B = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>>;
    type P1 = PInt<UInt<UTerm, B1>>;

    #[allow(non_camel_case_types)]
    type P5DivP5 = <<A as Div<B>>::Output as Same<P1>>::Output;

    assert_eq!(<P5DivP5 as Integer>::to_i64(), <P1 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_P5_Rem_P5() {
    type A = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>>;
    type B = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>>;
    type _0 = Z0;

    #[allow(non_camel_case_types)]
    type P5RemP5 = <<A as Rem<B>>::Output as Same<_0>>::Output;

    assert_eq!(<P5RemP5 as Integer>::to_i64(), <_0 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_P5_PartialDiv_P5() {
    type A = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>>;
    type B = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>>;
    type P1 = PInt<UInt<UTerm, B1>>;

    #[allow(non_camel_case_types)]
    type P5PartialDivP5 = <<A as PartialDiv<B>>::Output as Same<P1>>::Output;

    assert_eq!(<P5PartialDivP5 as Integer>::to_i64(), <P1 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_P5_Pow_P5() {
    type A = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>>;
    type B = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>>;
    type P3125 = PInt<UInt<UInt<UInt<UInt<UInt<UInt<UInt<UInt<UInt<UInt<UInt<UInt<UTerm, B1>, B1>, B0>, B0>, B0>, B0>, B1>, B1>, B0>, B1>, B0>, B1>>;

    #[allow(non_camel_case_types)]
    type P5PowP5 = <<A as Pow<B>>::Output as Same<P3125>>::Output;

    assert_eq!(<P5PowP5 as Integer>::to_i64(), <P3125 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_P5_Cmp_P5() {
    type A = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>>;
    type B = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>>;

    #[allow(non_camel_case_types)]
    type P5CmpP5 = <A as Cmp<B>>::Output;
    assert_eq!(<P5CmpP5 as Ord>::to_ordering(), Ordering::Equal);
}
#[test]
#[allow(non_snake_case)]
fn test_N5_Neg() {
    type A = NInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>>;
    type P5 = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>>;

    #[allow(non_camel_case_types)]
    type NegN5 = <<A as Neg>::Output as Same<P5>>::Output;
    assert_eq!(<NegN5 as Integer>::to_i64(), <P5 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_N5_Abs() {
    type A = NInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>>;
    type P5 = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>>;

    #[allow(non_camel_case_types)]
    type AbsN5 = <<A as Abs>::Output as Same<P5>>::Output;
    assert_eq!(<AbsN5 as Integer>::to_i64(), <P5 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_N4_Neg() {
    type A = NInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>>;
    type P4 = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>>;

    #[allow(non_camel_case_types)]
    type NegN4 = <<A as Neg>::Output as Same<P4>>::Output;
    assert_eq!(<NegN4 as Integer>::to_i64(), <P4 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_N4_Abs() {
    type A = NInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>>;
    type P4 = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>>;

    #[allow(non_camel_case_types)]
    type AbsN4 = <<A as Abs>::Output as Same<P4>>::Output;
    assert_eq!(<AbsN4 as Integer>::to_i64(), <P4 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_N3_Neg() {
    type A = NInt<UInt<UInt<UTerm, B1>, B1>>;
    type P3 = PInt<UInt<UInt<UTerm, B1>, B1>>;

    #[allow(non_camel_case_types)]
    type NegN3 = <<A as Neg>::Output as Same<P3>>::Output;
    assert_eq!(<NegN3 as Integer>::to_i64(), <P3 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_N3_Abs() {
    type A = NInt<UInt<UInt<UTerm, B1>, B1>>;
    type P3 = PInt<UInt<UInt<UTerm, B1>, B1>>;

    #[allow(non_camel_case_types)]
    type AbsN3 = <<A as Abs>::Output as Same<P3>>::Output;
    assert_eq!(<AbsN3 as Integer>::to_i64(), <P3 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_N2_Neg() {
    type A = NInt<UInt<UInt<UTerm, B1>, B0>>;
    type P2 = PInt<UInt<UInt<UTerm, B1>, B0>>;

    #[allow(non_camel_case_types)]
    type NegN2 = <<A as Neg>::Output as Same<P2>>::Output;
    assert_eq!(<NegN2 as Integer>::to_i64(), <P2 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_N2_Abs() {
    type A = NInt<UInt<UInt<UTerm, B1>, B0>>;
    type P2 = PInt<UInt<UInt<UTerm, B1>, B0>>;

    #[allow(non_camel_case_types)]
    type AbsN2 = <<A as Abs>::Output as Same<P2>>::Output;
    assert_eq!(<AbsN2 as Integer>::to_i64(), <P2 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_N1_Neg() {
    type A = NInt<UInt<UTerm, B1>>;
    type P1 = PInt<UInt<UTerm, B1>>;

    #[allow(non_camel_case_types)]
    type NegN1 = <<A as Neg>::Output as Same<P1>>::Output;
    assert_eq!(<NegN1 as Integer>::to_i64(), <P1 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_N1_Abs() {
    type A = NInt<UInt<UTerm, B1>>;
    type P1 = PInt<UInt<UTerm, B1>>;

    #[allow(non_camel_case_types)]
    type AbsN1 = <<A as Abs>::Output as Same<P1>>::Output;
    assert_eq!(<AbsN1 as Integer>::to_i64(), <P1 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test__0_Neg() {
    type A = Z0;
    type _0 = Z0;

    #[allow(non_camel_case_types)]
    type Neg_0 = <<A as Neg>::Output as Same<_0>>::Output;
    assert_eq!(<Neg_0 as Integer>::to_i64(), <_0 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test__0_Abs() {
    type A = Z0;
    type _0 = Z0;

    #[allow(non_camel_case_types)]
    type Abs_0 = <<A as Abs>::Output as Same<_0>>::Output;
    assert_eq!(<Abs_0 as Integer>::to_i64(), <_0 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_P1_Neg() {
    type A = PInt<UInt<UTerm, B1>>;
    type N1 = NInt<UInt<UTerm, B1>>;

    #[allow(non_camel_case_types)]
    type NegP1 = <<A as Neg>::Output as Same<N1>>::Output;
    assert_eq!(<NegP1 as Integer>::to_i64(), <N1 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_P1_Abs() {
    type A = PInt<UInt<UTerm, B1>>;
    type P1 = PInt<UInt<UTerm, B1>>;

    #[allow(non_camel_case_types)]
    type AbsP1 = <<A as Abs>::Output as Same<P1>>::Output;
    assert_eq!(<AbsP1 as Integer>::to_i64(), <P1 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_P2_Neg() {
    type A = PInt<UInt<UInt<UTerm, B1>, B0>>;
    type N2 = NInt<UInt<UInt<UTerm, B1>, B0>>;

    #[allow(non_camel_case_types)]
    type NegP2 = <<A as Neg>::Output as Same<N2>>::Output;
    assert_eq!(<NegP2 as Integer>::to_i64(), <N2 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_P2_Abs() {
    type A = PInt<UInt<UInt<UTerm, B1>, B0>>;
    type P2 = PInt<UInt<UInt<UTerm, B1>, B0>>;

    #[allow(non_camel_case_types)]
    type AbsP2 = <<A as Abs>::Output as Same<P2>>::Output;
    assert_eq!(<AbsP2 as Integer>::to_i64(), <P2 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_P3_Neg() {
    type A = PInt<UInt<UInt<UTerm, B1>, B1>>;
    type N3 = NInt<UInt<UInt<UTerm, B1>, B1>>;

    #[allow(non_camel_case_types)]
    type NegP3 = <<A as Neg>::Output as Same<N3>>::Output;
    assert_eq!(<NegP3 as Integer>::to_i64(), <N3 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_P3_Abs() {
    type A = PInt<UInt<UInt<UTerm, B1>, B1>>;
    type P3 = PInt<UInt<UInt<UTerm, B1>, B1>>;

    #[allow(non_camel_case_types)]
    type AbsP3 = <<A as Abs>::Output as Same<P3>>::Output;
    assert_eq!(<AbsP3 as Integer>::to_i64(), <P3 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_P4_Neg() {
    type A = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>>;
    type N4 = NInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>>;

    #[allow(non_camel_case_types)]
    type NegP4 = <<A as Neg>::Output as Same<N4>>::Output;
    assert_eq!(<NegP4 as Integer>::to_i64(), <N4 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_P4_Abs() {
    type A = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>>;
    type P4 = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>>;

    #[allow(non_camel_case_types)]
    type AbsP4 = <<A as Abs>::Output as Same<P4>>::Output;
    assert_eq!(<AbsP4 as Integer>::to_i64(), <P4 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_P5_Neg() {
    type A = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>>;
    type N5 = NInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>>;

    #[allow(non_camel_case_types)]
    type NegP5 = <<A as Neg>::Output as Same<N5>>::Output;
    assert_eq!(<NegP5 as Integer>::to_i64(), <N5 as Integer>::to_i64());
}
#[test]
#[allow(non_snake_case)]
fn test_P5_Abs() {
    type A = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>>;
    type P5 = PInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>>;

    #[allow(non_camel_case_types)]
    type AbsP5 = <<A as Abs>::Output as Same<P5>>::Output;
    assert_eq!(<AbsP5 as Integer>::to_i64(), <P5 as Integer>::to_i64());
}