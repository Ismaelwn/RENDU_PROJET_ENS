// BAD : duplicated lifetime variable name
struct S<'a, 'a> {
    x: &'a i32,
}
