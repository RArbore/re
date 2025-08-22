use std::collections::HashMap;

use arena::Arena;

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct IdentifierId(u32);

impl IdentifierId {
    pub fn idx(&self) -> usize {
        self.0 as usize
    }
}

#[derive(Debug)]
pub struct StringInterner<'a, 'b> {
    str_to_id: HashMap<&'a str, IdentifierId>,
    id_to_str: Vec<&'a str>,
    arena: &'a Arena<'b>,
}

impl<'a, 'b> StringInterner<'a, 'b> {
    pub fn new(arena: &'a Arena<'b>) -> Self {
        Self {
            str_to_id: HashMap::new(),
            id_to_str: vec![],
            arena,
        }
    }

    pub fn intern(&mut self, string: &str) -> IdentifierId {
        if let Some(id) = self.str_to_id.get(string) {
            *id
        } else {
            let in_arena = self.arena.new_ref(string);
            let id = IdentifierId(self.id_to_str.len().try_into().unwrap());
            self.str_to_id.insert(in_arena, id);
            self.id_to_str.push(in_arena);
            id
        }
    }

    pub fn get(&self, id: IdentifierId) -> &'a str {
        self.id_to_str[id.0 as usize]
    }

    pub fn num_idens(&self) -> usize {
        self.id_to_str.len()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn intern_strings() {
        let mut buf: [u64; 4] = [0; 4];
        let arena = Arena::new_backed(&mut buf);
        let mut interner = StringInterner::new(&arena);
        let str1 = "short";
        let str2 = "quite a long string";
        let id1 = interner.intern(str1);
        let id2 = interner.intern(str2);
        assert_ne!(id1, id2);
        let id3 = interner.intern(str1);
        let id4 = interner.intern(str2);
        assert_ne!(id3, id4);
        assert_eq!(id1, id3);
        assert_eq!(id2, id4);
        assert_eq!(interner.get(id1), str1);
        assert_eq!(interner.get(id2), str2);
        assert_eq!(interner.get(id3), str1);
        assert_eq!(interner.get(id4), str2);
    }
}
