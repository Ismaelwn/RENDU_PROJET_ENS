fn f<'a>() -> &'a mut i32 {
    loop {}
}

fn g() -> () {
    loop {
        if false { break }
    }
}
