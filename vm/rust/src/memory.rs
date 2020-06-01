use crate::L3Value;

const NIL_TARGET: L3Value = 0;
const NIL: usize = 0;
const BLOCK_SIZE_MIN: usize = 3;

pub struct Memory {
    heap_start: usize,
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

fn index_to_address(index: usize) -> L3Value {
    (index << 2) as L3Value
}

fn address_to_index(addr: L3Value) -> usize {
    debug_assert!(addr & ((1 << 2) - 1) == 0,
                  "invalid address: {} (16#{:x})", addr, addr);
    (addr >> 2) as usize
}

impl Memory {
    pub fn new(word_size: usize) -> Memory {
        //println!("[MEM] word-size:{}", word_size);
        Memory {
            heap_start: 0,
            content: vec![0; word_size],
            head: 0,
            bitmap: vec![false; word_size],
        }
    }

    pub fn get_next_pointer(&mut self, block: usize) -> usize { 
        return address_to_index(self.content[block - 1]);
    }

    pub fn set_next_pointer(&mut self, block: usize, next_block: usize) {
        self.content[block - 1] = index_to_address(next_block);
    }

    pub fn set_heap_start(&mut self, heap_start_index: usize) {
        debug_assert!(heap_start_index < self.content.len());
        //set head after header and set header to size of whole block.
        self.head = heap_start_index + 2;
        self.heap_start = heap_start_index + 2;
        let heap_size = (self.content.len()-1-heap_start_index) as i32;
        self[heap_start_index] = header_pack(0, heap_size);
        self[heap_start_index+1] = NIL_TARGET;
        
        //set minimum size of a block to store header and 
    }




    pub fn scan_block(&mut self, address: usize) {
        let size = self.block_size(address) as usize;
        for i in 0..size {
            if self[address+i] & 0b11 == 0 {
                let real_address = address_to_index(self[address+i]);
                if real_address < self.content.len() && real_address >= self.heap_start {
                    ////println!("chasing pointer @{} -> block [{}]", real_address, self.block_size(real_address));
                    self.traverse(&real_address);
                }
            }
        }
    }

    pub fn traverse(&mut self, root: &usize) {
        //check if address is a pointer
        if self[*root] & 0b11 == 0 && self.bitmap[*root] {
          self.bitmap[*root] = false;
          let real_address: usize = address_to_index(self[*root]);
          if real_address < self.content.len() && real_address >= self.heap_start {
              //println!("chasing pointer @{} -> block [{}]", real_address, self.block_size(real_address));
              self.scan_block(real_address);
          }
        }
      }

    pub fn mark(&mut self, _gc_roots: [usize; 4] ) {
        for root in _gc_roots.iter() {
            self.traverse(root);
        }
    }
    
    //Returns the next free block given the previous (current) and next block in the free list
    //Also coalesces adjacent free blocks
    pub fn sweep(&mut self, prev: usize, mut next: usize ) -> usize{

        let mut insert = prev;
        for i in self.heap_start..self.content.len() {
            if self.bitmap[i] { // this address is the start of a block and it is free
                if next == NIL { // set next to first non-nil block
                    next = i;
                }
                //println!("[MEM] recovered free  block @{} [{}]", i, self.block_size(i));
                let previous_size = if insert != NIL { self.block_size(insert) } else { 0 };
                if i == insert + previous_size as usize + 2 {
                    /*Coalesce with previous block*/
                    //println!("[MEM] coalesced {} w/ {}", i, insert);
                    self[insert-2] = header_pack(0, previous_size + self.block_size(i) + 2);
                    self[i - 1] = 0;
                    self[i - 2] = 0;
                }
                else {
                    /*Add new block*/
                    if insert != NIL {
                        debug_assert!(self.valid_pointer(insert));
                        self.set_next_pointer(insert, i);
                    }
                    //println!("[MEM] link block @{} -> @{}", insert, i);
                    insert = i;
                }
                self.bitmap[i] = false; // unnecessary really
            }
            
        }
        self.set_next_pointer(insert, NIL); // setting last free block's next to nil

        return next
    }


    pub fn allocate(&mut self,
                    tag: L3Value,
                    size: L3Value,
                    _gc_roots: [usize; 4]) -> usize { 
        //println!("[MEM] HEAD@{}", self.head);
        let mut current_free_size = if self.head != NIL { self.block_size(self.head) } else { 0 };
        let mut p = self.head;
        let mut prev = NIL;
        let mut next = NIL;
        //bootstrap next
        if p != NIL {
            next = self.get_next_pointer(p);
        }
        /*
            look for next big enough block address
        */
        let mut used_gc = false;
        while current_free_size < (size + 1) || p == NIL {
            prev = p;
            p = next;

            if p == NIL {
                if used_gc {
                    panic!("Tried to used GC twice in a row");
                }
                self.mark(_gc_roots);
                next = self.sweep(prev, NIL);
                current_free_size = 0;
                //println!("all blocks marked, looking for {} bytes, \"HEAD\" is {}", size, p);
                if next == NIL {
                    panic!("Could not free memory");
                }

                used_gc = true;

            }else{
                current_free_size = self.block_size(p);
                next = self.get_next_pointer(p);
            }
           
            //println!("[MEM] sizeof {}={}", p, current_free_size);
        }
        //println!("[MEM] found block {}@{} for {}b, next is {}", self.block_size(p), p, size, self.get_next_pointer(p));
        /*
            break block and mark it
        */
        //mark new block
        self.bitmap[p] = true;
        self[p - 2] = header_pack(tag, size);

        let free_size = current_free_size - (size + 2); // + 2 is the header size of the new block
        let mut new_head: usize = 0;
        if free_size > BLOCK_SIZE_MIN as i32 {
            new_head = p + (size as usize) + 2;
            //println!("[MEM] new({}) old({})", new_head, self.head);
            //do even if prev is not nil
            let new_next = self.get_next_pointer(p);
            self.set_next_pointer(new_head, new_next);
            //check that the block is big enough
            //println!("[MEM] free size |{}", free_size);
            self[new_head-2] = header_pack(254, free_size);
        } else {
            new_head = next;
        }
        if prev == NIL {
            //println!("[MEM] update head from {} to {}", self.head, new_head);
            debug_assert!(self.valid_pointer(new_head));
            self.head = new_head;
        } else {
            self.set_next_pointer(prev, new_head);
        }
        debug_assert!(self.block_tag(p) == tag);
        debug_assert!(self.block_size(p) == size);
        debug_assert!(self.valid_pointer(p));
        //println!("allocate {} {} {} {}", tag, size, p ,self.head);
        p
    }

    pub fn valid_pointer(&mut self, address: usize) -> bool {
        return address >= self.heap_start && address < self.content.len()
    }

    pub fn block_tag(&self, ix: usize) -> L3Value {
        //println!("tagof {}", ix);
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
