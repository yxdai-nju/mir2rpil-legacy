#![no_main]

use core::cell::RefCell;
use core::pin::Pin;

pub fn rc_as_pinmut<T>(rc: Pin<&mut RefCell<T>>) -> Pin<&mut T> {
    unsafe { rc.map_unchecked_mut(|this| this.get_mut()) }
}
