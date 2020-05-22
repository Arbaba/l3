use crate::L3Value;

const NIL: L3Value = 0;
const BLOCK_SIZE_MIN: usize = 3;

pub struct Memory {
    content: Vec<L3Value>,
    head: usize, // = list head
    bitmap: Vec<bool>,
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
            head: 0,
            bitmap: vec![false; word_size],
        }
    }

    pub fn set_heap_start(&mut self, heap_start_index: usize) {
        debug_assert!(heap_start_index < self.content.len());
        //set head after header and set header to size of whole block.
        self.head = heap_start_index + 2;
        self[heap_start_index] = header_pack(0, (self.content.len()-1) as i32);
        self[heap_start_index+1] = NIL;
        //set minimum size of a block to store header and 
    }

    pub fn get_next_pointer(&mut self, block: usize) -> usize { 
        return self.content[block - 1] as usize;
    }

    pub fn set_next_pointer(&mut self, block: usize, next_block: usize) {
        self.content[block - 1] = next_block as i32;
    }

    pub fn allocate(&mut self,
                    tag: L3Value,
                    size: L3Value,
                    _gc_roots: [usize; 4]) -> usize {
        /*
            look for next big enough block address
        */
        let mut current_free_size = self.block_size(self.head) ;
        let target_size = size + 1;
        let mut p = self.head;
        let nil: usize = 0; // Unboxed 0 pointer
        let mut prev = nil;
        while current_free_size < (size + 1) && p != nil {
            prev = p;
            p = self.get_next_pointer(p);
            if p == nil {
                panic!("no more memory");
            }
            current_free_size = self.block_size(p);
        }
        /*
            break block and mark it
        */
        //mark new block
        let res = p;
        //p += (size + 2) as usize; // + 2 accounts for the header of the new  block
        self.content[res - 2] = header_pack(tag, size);
        //mark new free block
        let new_head = res + (size) as usize + 2;
        self.head = new_head;

        let free_size = current_free_size - (size + 2); // + 2 is the header size of the new block
        //check that the block is big enough
        self[new_head-2] = header_pack(0, free_size);
        //self[self.head-1] = 
        //self.content[p] = header_pack(0, free_size - 2);
        //self.content[p] = self.content[res+1]; // old next pointer
        //clear old next pointer
        //set old next pointer to new block
        /*if prev != nil {
            self.content[(prev + 1) as usize] = p;
        }*/
        /*let full_mem = true;
        if full_mem {
          println!("GC");
          println!("traversing");
          for root in _gc_roots.iter() {
            self.traverse(root);
          }
          self.sweep();
        }
        self[header_ix] = header_pack(tag, size);*/
        res
    }

    pub fn traverse(&mut self, address: &usize) {
      //check if address is a pointer
      if self[*address] & 0b11 != 0 {
        println!("chasing pointer");
      }
    }

    pub fn sweep(&mut self) {
      println!("sweeping");
    }

    pub fn block_tag(&self, ix: usize) -> L3Value {
        header_unpack_tag(self.content[ix - 2])
    }

    pub fn block_size(&self, ix: usize) -> L3Value {
        header_unpack_size(self.content[ix - 2])
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
