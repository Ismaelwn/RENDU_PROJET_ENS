fn f<'a, 'b, 'c>(s: &'a mut &'b mut &'c mut i32) -> &'a mut &'c mut i32 {
    &mut (**s)
}
