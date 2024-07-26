#![no_main]

pub fn return_captured_value(value: i32) -> i32 {
    let boxed = Box::new(value);
    let closure = move || *boxed;
    closure()
}
