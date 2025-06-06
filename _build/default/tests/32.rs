struct Box {}

struct S {
    x : Box,
    y : Box
}


fn g() {
    let mut x : S;
    x.x = Box {}; // BAD : x should be initialized before writing to its field x.x
}
