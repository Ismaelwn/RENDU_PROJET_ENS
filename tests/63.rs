fn rebor<'a, 'b, 'c, 'd>(x: &'a mut &'b &'c mut i32) -> &'d mut i32
where
    'a: 'd,
{
    &mut ***x // BAD: the second deref is the deref of a shared borrow,
              // so the borrow cannot be mut
}
