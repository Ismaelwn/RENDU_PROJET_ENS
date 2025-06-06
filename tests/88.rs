struct Bor<'a, 'b> {
    x: &'a mut &'b mut i32,
}

fn constrain_box<'a, 'b, 'c>(a: Bor<'a, 'b>, b: Bor<'a, 'c>)
where
    'b: 'c,
{
}

fn f<'a, 'b, 'c>(a: Bor<'a, 'b>, b: Bor<'a, 'c>) {
    constrain_box(a, b); // BAD
}
