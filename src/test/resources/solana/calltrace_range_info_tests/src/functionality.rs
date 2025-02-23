//! This module contains functions that will be called from other modules for test purposes.
use super::intrinsics::*;

pub fn assert_false() {
    unsafe {
        CVT_assert(CVT_nondet_u64() < 10);
    }
}

pub fn print_location() {
    print_location!()
}

pub fn assert_false_with_attach_location() {
    cvt_assert_with_location!(false);
}

pub fn print_tag_with_attach_location() {
    cvt_print_tag_with_location!("tag_from_functionality_1")
}

pub fn print_value_with_attach_location() {
    cvt_print_value_with_location!("tag_from_functionality_2", 2)
}
