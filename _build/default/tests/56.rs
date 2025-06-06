fn f<'a, 'b>(x : &'a mut i32) -> &'b mut i32 where 'b: 'a {
    x // BAD : we only know 'b: 'a, so we cannot cast [&'a mut i32] into [&'b mut i32]
}
