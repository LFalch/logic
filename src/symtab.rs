use std::collections::{BTreeMap, HashMap};

pub trait Interpretation {
    fn get_symbol(&self, symbol: char) -> Option<bool>;
}

impl Interpretation for BTreeMap<char, bool> {
    fn get_symbol(&self, symbol: char) -> Option<bool> {
        self.get(&symbol).copied()
    }
}
impl Interpretation for HashMap<char, bool> {
    fn get_symbol(&self, symbol: char) -> Option<bool> {
        self.get(&symbol).copied()
    }
}
impl Interpretation for [(char, bool)] {
    fn get_symbol(&self, symbol: char) -> Option<bool> {
        for &(c, b) in self {
            if c == symbol {
                return  Some(b);
            } 
        }
        None
    }
}
