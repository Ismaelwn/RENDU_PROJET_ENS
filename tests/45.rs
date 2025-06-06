struct S<'a> {
    x: i32,
    y: &'a mut i32
}

fn create_s<'a>() -> S<'a> {
    loop {}
}

fn f(mut x : i32, cond: bool) -> i32 {
    let mut b : S = S { x: 12i32, y: &mut x };

    let y : i32 = x; // BAD : borrow in x is still active

    if cond {
        b = create_s(); // Override b, so b is no longer live above, hence we can
                        // consider that the borrow in b.y is not active ...
    } else {
        // ... however, in contrary to test 44.rs, this branch does not kill b.
    }

    y + b.x // using b
}
