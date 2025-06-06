fn f<'a>() -> &'a mut i32 {
    loop {}
}

fn g() {
    let mut x : i32 = 18i32;
    let mut y : &mut i32 = &mut x;
    let mut z : &mut i32 = &mut *y;
    y = f();
    *z = 1i32;
}