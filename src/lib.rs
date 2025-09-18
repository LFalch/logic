pub(crate) mod symtab;
pub mod propositional;
pub mod first_order;

pub fn emit_once<T>(thing: T) -> impl FnMut() -> T {
    let mut opt = Some(thing);
    move || opt.take().unwrap()
}
