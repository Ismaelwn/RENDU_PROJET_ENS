struct S<'a> {
    x: i32,
    y: &'a mut i32
}

fn g<'a>(s: S<'a>) {}

fn f(mut x : i32) {
    let b : S = S { x: 12i32, y: &mut x };

    let y : i32 = x; // BAD : cannot use x, because it is still borrowed.

    g(b); // using b.
}
