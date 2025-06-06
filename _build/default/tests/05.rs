struct Box {}

fn consume_box(x : Box) -> bool {
    return true
}

fn f(x : Box) {
    if 1i32 == 1i32 && consume_box(x) {
       consume_box(x); // BAD : use of x which has been consumed
    }
}