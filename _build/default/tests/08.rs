fn f1<'a, 'b>(x: &'a i32, y: &'b i32) -> &'a i32
where
    'b: 'a,
{
    x
}

fn f2<'a, 'b>(x: &'a i32, y: &'b i32)
where
    'a: 'b,
{
}

fn g<'a>(x: &'a i32, y: &'a i32) {
    f1(x, f1(y, x));
}

fn h<'a, 'b>(x: &'b i32, y: &'a i32)
where
    'b: 'a,
{
    f2(f1(y, x), y);
}
