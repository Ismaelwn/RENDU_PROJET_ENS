struct NotCopy {}

fn f<'a>(y: NotCopy, b1: &'a mut NotCopy, b2: &'a mut NotCopy) {
    *b1 = y;
    *b2 = y; // BAD : y is not copy, and has been used above
}
