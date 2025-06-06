struct S<'a, 'b> {
    f: &'a mut i32,
    g: &'b mut i32
}

// BAD: in MiniRust, lifetime parameters (for S) are always all required in
// prototypes.
fn f<'a>(x: S<'a>) {}