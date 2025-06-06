struct S<'a> {
    x: i32,
    y: &'a mut i32
}

fn f(mut x : i32) {
    let mut b : S = S { x: 12i32, y: &mut x };

    let y : i32 = x; // BAD : cannot use x, because it is still borrowed.

    let mut bb : &mut i32 = &mut b.x; // Borrowing part of b is like using it.
}
