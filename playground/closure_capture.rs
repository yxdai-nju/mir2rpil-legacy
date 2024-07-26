#![no_main]

pub fn return_captured_ref<'a, T>(ref_1: &'a mut T, ref_2: &'a mut T) -> &'a mut T {
    let boxed_ref_1 = Box::new(ref_1);
    let boxed_ref_2 = Box::new(ref_2);
    let val = 100;
    let closure = move |x| {
        if x == 42 { *boxed_ref_1 } else { *boxed_ref_2 }
    };
    closure(val)
}
