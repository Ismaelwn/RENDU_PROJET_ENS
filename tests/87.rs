fn f<'a>(a: &'a i32) {
    let mut x : i32 = 1i32;
    let mut b : &mut i32 = &mut x;
    let mut bb : &mut &mut i32 = &mut b;

    *bb = &mut *a; //BAD : a is a shared borrow, so immutable
}
