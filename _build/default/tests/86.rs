struct S {
    x: i32
}

fn f<'a>(a: &'a S) {
    (*a).x = 1i32 // BAD: a is a shared borrow
}
