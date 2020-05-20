use crate::L3Value;


pub struct Memory {
    content: Vec<L3Value>,
    HEAD: usize, // = list head
    MINSIZE: usize,
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
            HEAD: 0,
            MINSIZE: 0,
            bitmap: vec![0; word_size],
        }
    }

    pub fn set_heap_start(&mut self, heap_start_index: usize) {
        debug_assert!(heap_start_index < self.content.len());
        //set HEAD after header and set header to size of whole block.
        self.HEAD = heap_start_index + 1;
        self[HEAD] = header_pack(0, self.content.len()-1);
        //set minimum size of a block to store header and 
        self.MINSIZE = 3 // header + pointer + ???
    }

    pub fn allocate(&mut self,
                    tag: L3Value,
                    size: L3Value,
                    _gc_roots: [usize; 4]) -> usize {
        let block_size = header_unpack_size(self.HEAD);
        let full_mem = false;
        let header_ix = self.HEAD;
        if block_size >  size && block_size > self.MINSIZE {
          //split block
          //check if there is a "next" block
          let tail = self[self.HEAD+1];
          //move head to after allocate block
          self.HEAD += (size as usize) + 1;
          //compute new size and set header
          self[self.HEAD] = header_pack(0, block_size - (size + 1));
          //put back tail of list
          self[self.HEAD+1] = tail
        } else {
          full_mem = true;
          //get next pointer 
          //allocate in the middle
        }
        /*
        Look for next block.  
        */
        
        /*
        tag
        */
        
        if full_mem {
          println!("GC");
          println!("traversing");
          for root in _gc_roots.iter() {
            self.traverse(root);
          }
          /*
              sweep
          */
          self.sweep();
        }
        self[header_ix] = header_pack(tag, size);
        header_ix + 1
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
