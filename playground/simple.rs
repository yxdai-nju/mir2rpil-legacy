#![no_main]

use ThreeVariants::*;

struct TwoMembers {
    p1: isize,
    p2: isize,
}

enum ThreeVariants {
    Variant0(i8, i8, i8),
    Variant1(i8, i8),
    Variant2(u8, u8, u8, u8, Option<TwoMembers>),
}

pub fn do_something() -> isize {
    let a0 = TwoMembers { p1: 42, p2: 43 };
    let a = TwoMembers { p1: 44, ..a0 };
    let b = Some(a);
    let c = Variant2(45, 46, 47, 48, b);
    match c {
        Variant2(_, _, _, _, x) => x,
        _ => unreachable!(),
    }
    .unwrap()
    .p1
}
