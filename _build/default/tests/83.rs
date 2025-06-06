struct S<'a, 'b> {
    x: &'a mut i32,
    y: &'b mut i32,
}

fn f<'a, 'b, 'c>(s: S<'a, 'b>) -> &'c mut i32
where
    'a: 'c,
{
    &mut *s.x
}
