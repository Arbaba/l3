use crate::L3Value;

pub struct Memory {
    content: Vec<L3Value>,
    free_ix: usize,
}

fn header_pack(tag: L3Value, size: L3Value) -> L3Value {
    debug_assert!(0 <= size && size <= 0xFF_FFFF);
    debug_assert!(0 <= tag && tag <= 0xFF);

    (size << 8) | tag
}

fn header_unpack_tag(header: L3Value) -> L3Value {
    header & 0xFF
}

fn header_unpack_size(header: L3Value) -> L3Value {
    header >> 8
}

impl Memory {
    pub fn new(word_size: usize) -> Memory {
        Memory {
            content: vec![0; word_size],
            free_ix: 0
        }
    }

    pub fn set_heap_start(&mut self, heap_start_index: usize) {
        debug_assert!(heap_start_index < self.content.len());
        self.free_ix = heap_start_index
    }

    pub fn allocate(&mut self,
                    tag: L3Value,
                    size: L3Value,
                    _gc_roots: [usize; 4]) -> usize {
        debug_assert!(0 <= tag && tag <= 0xFF);
        debug_assert!(0 <= size);

        let header_ix = self.free_ix;
        self.free_ix += 1 + (size as usize);
        if self.free_ix >= self.content.len() {
            panic!("no more memory");
        };
        self[header_ix] = header_pack(tag, size);
        header_ix + 1
    }

    pub fn block_tag(&self, ix: usize) -> L3Value {
        header_unpack_tag(self.content[ix - 1])
    }

    pub fn block_size(&self, ix: usize) -> L3Value {
        header_unpack_size(self.content[ix - 1])
    }
}

use std::ops::{ Index, IndexMut };

impl Index<usize> for Memory {
    type Output = L3Value;
    fn index(&self, i: usize) -> &Self::Output {
        &self.content[i]
    }
}

impl IndexMut<usize> for Memory {
    fn index_mut(&mut self, i: usize) -> &mut Self::Output {
        &mut self.content[i]
    }
}
