struct Box { }

fn use_box(b : Box) {}

fn f(b : bool) {
    let x : Box = Box { };
    if b {
        use_box(x)
    } else {

    }

    use_box(x) // BAD : x is consumed in the first branch above
}
