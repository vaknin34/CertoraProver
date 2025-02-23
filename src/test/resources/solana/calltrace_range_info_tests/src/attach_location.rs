use super::intrinsics::*;

#[no_mangle]
pub fn rule_attach_location_assert_main_body() {
    cvt_assert_with_location!(false);
}

#[no_mangle]
pub fn rule_attach_location_assert_nested_call() {
    assert_false();
}

fn assert_false() {
    cvt_assert_with_location!(false);
}

#[no_mangle]
pub fn rule_attach_location_assert_other_module() {
    super::functionality::assert_false_with_attach_location();
}

#[no_mangle]
pub fn rule_attach_location_print_tag_main_body() {
    cvt_print_tag_with_location!("tag1");
    cvt_assert_with_location!(false);
}

#[no_mangle]
pub fn rule_attach_location_print_tag_nested_call() {
    print_tag();
    cvt_assert_with_location!(false);
}

fn print_tag() {
    cvt_print_tag_with_location!("tag2");
}

#[no_mangle]
pub fn rule_attach_location_print_tag_other_module() {
    print_tag(); // Call this to make sure that the first attach_location does not override the second.
    super::functionality::print_tag_with_attach_location();
    cvt_assert_with_location!(false);
}

#[no_mangle]
pub fn rule_attach_location_print_value_main_body() {
    cvt_print_value_with_location!("tag1", CVT_nondet_u64());
    cvt_assert_with_location!(false);
}

#[no_mangle]
pub fn rule_attach_location_print_value_nested_call() {
    print_value();
    cvt_assert_with_location!(false);
}

fn print_value() {
    cvt_print_value_with_location!("tag2", 1);
}

#[no_mangle]
pub fn rule_attach_location_print_value_other_module() {
    super::functionality::print_value_with_attach_location();
    print_value(); // Call this to make sure that this attach_location does not override the previous.
    cvt_assert_with_location!(false);
}
