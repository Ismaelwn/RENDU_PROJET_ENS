fn f<'a>(x: i32) -> &'a i32 {
    &x // BAD : when returning, x will be deallocated, but the borrow should still be valid.
}