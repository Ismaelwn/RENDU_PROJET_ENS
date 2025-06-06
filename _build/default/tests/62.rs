fn rebor<'a, 'b, 'c, 'd>(x: &'a mut &'b mut &'c mut i32) -> &'d mut i32
where
    'a: 'd,
{
    &mut ***x
}
