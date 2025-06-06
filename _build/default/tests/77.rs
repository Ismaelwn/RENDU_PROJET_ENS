struct Box { f: i32 }

fn use_box(b: Box) {}

fn f() {
    let bo : Box = Box { f : 3i32 };
    let b : &Box = &bo;
    use_box(bo); // BAD : consuming bo, which is borrowed
    (*b).f;
}
