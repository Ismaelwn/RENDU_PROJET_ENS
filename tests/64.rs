fn rebor<'a, 'b, 'c, 'd>(x: &'a mut &'b &'c mut i32) -> &'d i32
where
    'a: 'd,
{
    & ***x
}
