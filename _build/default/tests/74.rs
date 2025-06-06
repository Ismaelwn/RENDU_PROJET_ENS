struct Box{}

fn f<'a>(x: &'a mut Box) -> Box {
    *x // BAD: moving a non-Copy value out of a borrow
}