struct S<'a> {
    x: i32,
    y: &'a i32
}

fn f(x : i32) -> i32 {
    let b : S = S { x: 12i32, y: &x };

    let y : i32 = x; // can use x, because it is borrowed in shared mode.

    y + b.x // b is still live (even though b.y is not)
}
