fn f() {
    let mut x : i32 = 12i32;
    let a : &mut i32 = {
        let mut y : &mut i32 = &mut x;
        &mut *y
    };

    a;
}