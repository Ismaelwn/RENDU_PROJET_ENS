struct S<'a, 'b>{
  x: &'a mut i32,
  y: &'b mut i32
}

fn f<'a, 'b>(s: S<'a, 'b>) -> S<'a, 'b> {
  let t: S = s;
  t
}
