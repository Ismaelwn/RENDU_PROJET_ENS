struct S {}

fn f() {
    // BAD: S is not a function
    S()
}