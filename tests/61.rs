fn rebor<'a, 'b, 'c, 'd>(x: &'a mut &'b mut &'c mut i32) -> &'d mut i32
where
    'b: 'd,
    'd: 'a,
{
    &mut ***x // BAD 'd should be shorter than 'a (i.e., 'a: 'd)
}
