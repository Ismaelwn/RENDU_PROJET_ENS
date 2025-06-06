fn f<'a>() -> &'a i32 {
    let x : i32 = 12i32;
    &x // BAD : x is deallocated before the end of the borrow
}
