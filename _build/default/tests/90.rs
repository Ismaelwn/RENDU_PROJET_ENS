struct S<'a> {
    b: &'a mut i32
}

fn f<'a, 'b>(s: S<'a>) -> &'b mut i32 {
    &mut *s.b // BAD : lifetime 'a is not longer than 'b
}
