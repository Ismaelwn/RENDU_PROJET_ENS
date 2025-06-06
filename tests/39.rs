fn f(b : bool) {
    let mut x : i32;
    if b {
        x = 12i32
    } else {

    }

    if b {
        x = x + 1i32 // BAD : the dataflow analysis is not able to discover
                     // that x is necessarilly initialized here.
    }
}
