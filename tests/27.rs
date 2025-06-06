
struct S {}

fn f(s: S) {
    s.x; // BAD: unknown field x
}