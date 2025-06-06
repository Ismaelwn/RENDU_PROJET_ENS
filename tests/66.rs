fn f<'a, 'b, 'c>(mut x : &'a mut &'b &'c mut i32) {
    ***x = 12i32 // BAD : ***x is read-only, because one of the borrows is non-mutable
}
