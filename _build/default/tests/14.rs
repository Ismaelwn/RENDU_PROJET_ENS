#[derive(Copy, Clone)]
struct S<'a> {
    x : &'a mut i32 // BAD : x has non-Copy type
}
