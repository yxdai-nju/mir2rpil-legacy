#![no_main]

struct TwoMembers {
    p1: isize,
    p2: isize,
}

pub fn do_something() -> isize {
    let a0 = TwoMembers { p1: 42, p2: 43 };
    let a = TwoMembers { p1: 44, ..a0 };
    let b = Some(a);
    let c = Some(b);
    c.unwrap().unwrap().p1
}
