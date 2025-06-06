struct S<'a> {
    x: i32,
    y: &'a mut i32
}

fn f(mut x : i32) -> i32 {
    let b : S = S { x: 12i32, y: &mut x };

    let y : i32 = x; // BAD : cannot use x, because it is still borrowed.

    y + b.x // b is still live (even though b.y is not)
}
