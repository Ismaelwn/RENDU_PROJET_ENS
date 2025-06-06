struct S<'a, 'b> { // Implicit : 'b : 'a
    x: &'a mut &'b i32,
}

fn f<'a, 'b>(x: &'a mut i32, y: S<'a, 'b>, z: S<'b, 'a>) -> &'b mut i32 {
    x
}

fn g<'a, 'b>(x: &'a mut i32, y: S<'a, 'b>) -> &'b mut i32
where
    'a: 'b,
{
    x
}

fn h<'a, 'b>(x: &'a mut i32, y: S<'b, 'a>) -> &'b mut i32
where
    'b: 'a,
{
    x
}
