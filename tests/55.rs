fn f<'a, 'b>(x : &'a mut i32) -> &'b mut i32 {
    x // BAD : 'a and 'b are arbitrary, so we cannot cast [&'a mut i32] into [&'b mut i32]
}
