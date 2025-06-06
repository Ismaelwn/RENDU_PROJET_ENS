fn f() -> i32 {
    loop {  // BAD : the loop has type (), but expected i32
        if false { break }
    }
}
