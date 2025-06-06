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
    let mut r : i32 = 0i32;

    let b : &mut S1 = &mut y.f4;
    let bb : &mut i32 = &mut (*b).f1;
    r = r + y.f3;
    let u : &mut i32 = &mut y.f3;
    r = r + *bb + *u;


    let b : &mut i32 = &mut y.f3;
    let n : i32 = y.f4.f1;
    let u : &mut S1 = &mut y.f4;
    r = r + n + (*u).f1;
    r = r + *b;

    let b : & S1 = & y.f4;
    let bb : & i32 = & (*b).f1;
    let u : &S1 = & y.f4;
    r = r + y.f4.f1 + (*u).f1;
    r = r + *bb;
}