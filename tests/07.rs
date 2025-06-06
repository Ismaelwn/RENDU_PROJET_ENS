struct S1 {
    x: i32
}

struct S2<'a> {
    y: &'a i32
}

struct S12<'a> {
    x: i32,
    y: &'a i32
}

fn f<'a>(s1: S1, s2: S2<'a>) -> S12<'a> {
    S12{ x: s1.x, y: s2.y }
}
