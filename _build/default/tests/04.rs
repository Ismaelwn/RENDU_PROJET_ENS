fn f() -> () {
    return ()
}

fn g<'a, 'b>(x: (), y: &'a mut (), z: &'b ()) {
    *y = *z;
    *y = x;
    if false || false {
        return x;
    }
}
