fn f<'a, 'b>(x : &'a mut i32) -> &'b mut i32 where 'b: 'a, 'a: 'b {
    x
}
