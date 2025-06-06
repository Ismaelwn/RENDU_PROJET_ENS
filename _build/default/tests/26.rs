struct S1 {
    s : i32
}

struct S2<'a> {
    t : &'a mut S1
}

fn h<'a>(x : &'a mut S1) -> &'a mut i32 {
    &mut (*x).s
}

fn f<'a>(x : S2<'a>) {
    (*x.t).s = 12i32;
    *h(&mut *x.t) = 13i32
}
