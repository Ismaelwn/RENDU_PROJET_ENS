fn f<'a, 'b>(x: &'a mut &'b mut i32, y: &'a mut i32, z: &'b mut i32) {}

fn g<'a, 'b, 'c>(x: &'c mut &'b mut i32, y: &'a mut i32, z: &'b mut i32)
where 'c : 'a {
    f(&mut *x, y, z) // When creating the borrow, we need 'c : 'a
}