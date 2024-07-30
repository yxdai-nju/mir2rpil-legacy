#![no_main]

// pub fn return_captured_ref<'a, T>(ref_1: &'a mut T, ref_2: &'a mut T, val: i32) -> &'a mut T {
//     let boxed_ref_1 = Box::new(ref_1);
//     let boxed_ref_2 = Box::new(ref_2);
//     let closure = move |x| {
//         if x == 42 { *boxed_ref_1 } else { *boxed_ref_2 }
//     };
//     closure(val)
// }

pub fn return_captured_ref<'a, T>(
    ref_1: &'a mut T,
    ref_2: &'a mut T,
    ref_3: &'a mut T,
    ref_4: &'a mut T,
    val: i32,
) -> &'a mut T {
    let boxed_ref_1 = Box::new(ref_1);
    let boxed_ref_2 = Box::new(ref_2);

    let closure1 = move |x| {
        if x == 42 { *boxed_ref_1 } else { *boxed_ref_2 }
    };

    let closure2 = move |x| {
        if x == 42 { ref_3 } else { ref_4 }
    };

    if val == 42 { closure1(val) } else { closure2(val) }
}
