// BAD: unknown lifetime 'b
fn f<'a> (x : &'a i32) where 'a: 'b {}
