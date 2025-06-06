fn f() {
    let mut n : i32 = 3i32;
    let b : &mut i32 = &mut n;
    n; // BAD: copying n, which is mutably borrowed
    (*b);
}
