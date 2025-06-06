#[derive(Copy, Clone)]
struct IsCopy {}

struct NotCopy {}

fn f<'a>(x: IsCopy, y: NotCopy, b1: &'a mut IsCopy, b2: &'a mut IsCopy, b3: &'a mut NotCopy) {
    *b1 = x;
    *b3 = y;
    *b2 = x;
}
