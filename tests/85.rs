fn f<'a>(mut a: &'a mut i32) {
    let mut x : i32 = 12i32;
    a = &mut x; // BAD: because it is stored in `a``, this borrow should have lifetime 'a, which lasts
                // during all the execution of f. But local `x` is deallocated before the end of `f`.
}
