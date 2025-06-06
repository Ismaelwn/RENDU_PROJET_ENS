struct S1 {
    f1: i32,
    f2: bool,
}

struct S2 {
    f3: i32,
    f4: S1
}

fn f() {
    let x : S1 = S1 { f1: 12i32, f2: false };
    let mut y : S2 = S2 { f3: 13i32, f4: x };
    let b : &mut S1 = &mut y.f4;
    let bb : &mut bool = &mut (*b).f2;
    & y.f4.f1; // BAD: borrow b is still active via bb, so this is a conflicting borrow
    *bb;
}