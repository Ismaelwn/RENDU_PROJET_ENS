fn f<'a>(x : &'a i32) -> &'a i32 { x }

struct S<'a>{
    f : &'a i32
}

fn g<'a, 'b>(x : &'a i32) -> & 'b i32 {
    let y : &i32 = x;
    let z : & &i32 = &y;
    let u : &i32 = *z;
    let v : S = S{f: u};
    let w : &i32 = v.f;
    let t : &i32 = f(w);
    t // BAD : t has type &'a i32 while we expect &'b i32
}
