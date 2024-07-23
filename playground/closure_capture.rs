#![no_main]

pub fn return_captured_value(value: Box<i32>) -> i32 {
    let boxed = Box::new(42);
    let closure = move || *boxed;
    closure()
}
