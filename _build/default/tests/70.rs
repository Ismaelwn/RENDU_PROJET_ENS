fn f<'a, 'o>(x: &'o mut &'a mut i32, y: &'o mut &'a mut i32) {}

fn g<'a>(mut x: &'a mut i32) {
    let mut y: i32 = 12i32;
    let mut b: &mut i32 = &mut y; // BAD: that borrow must have livetime 'a, but variable x disappears at the end of the function.
    f(&mut x, &mut b);
}
