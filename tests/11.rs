fn sum<'aaa>(n : i32, acc : &'aaa mut i32) {
    let mut i : i32 = 0i32;
    while i < n {
        *acc = *acc + i;
        i = i + 1i32;
    }
}
