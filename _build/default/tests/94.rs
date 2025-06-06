struct Box {}

struct S {x: Box}

fn f() {
    let mut b : Box = Box {};
    let bb : &mut Box = &mut b;
    S { x: *bb }; // BAD : *bb is moved out of borrow bb
}