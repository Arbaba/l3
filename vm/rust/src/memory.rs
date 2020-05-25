use crate::L3Value;

const NIL: L3Value = 0;
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

impl Memory {
    pub fn new(word_size: usize) -> Memory {
        println!("[MEM] word-size:{}", word_size);
        Memory {
            heap_start: 0,
            content: vec![0; word_size],
            head: 0,
            bitmap: vec![false; word_size],
        }
    }

    pub fn set_heap_start(&mut self, heap_start_index: usize) {
        debug_assert!(heap_start_index < self.content.len());
        //set head after header and set header to size of whole block.
        self.head = heap_start_index + 2;
        self.heap_start = heap_start_index + 2;
        let heap_size = (self.content.len()-1-heap_start_index) as i32;
        self[heap_start_index] = header_pack(0, heap_size);
        self[heap_start_index+1] = NIL;
        //set minimum size of a block to store header and 
    }

    pub fn get_next_pointer(&mut self, block: usize) -> usize { 
        return (self.content[block - 1] >> 2) as usize;
    }

    pub fn set_next_pointer(&mut self, block: usize, next_block: usize) {
        println!("[MEM] translating {} to {} @{}", next_block, (next_block << 2), block);
        self.content[block - 1] = (next_block << 2) as i32;
    }

    pub fn allocate(&mut self,
                    tag: L3Value,
                    size: L3Value,
                    _gc_roots: [usize; 4]) -> usize { 
        /*
            look for next big enough block address
        */
        println!("[MEM] HEAD@{}", self.head);
        let mut current_free_size = self.block_size(self.head) ;
        let target_size = size + 1;
        let mut p = self.head;
        let nil: usize = 0; // Unboxed 0 pointer
        let mut prev = nil;
        while current_free_size < (size + 1) || p == nil {
            prev = p;
            p = self.get_next_pointer(p);

            println!("[MEM] {}=>{}", prev, p);
            if p == nil {
                /*Garbage collect*/
                for root in _gc_roots.iter() {
                    self.traverse(root);
                }
                let mut insert = prev;
                for i in self.heap_start..self.content.len() {
                    if self.bitmap[i] { // this address is the start of a block and it is free
                        println!("[MEM] recovered free  block @{} [{}]", i, self.block_size(i));
                        self.set_next_pointer(insert, i);
                        println!("[MEM] link block @{} -> @{}", insert, i);
                        insert = i;
                        self.bitmap[i] = false; // unnecessary really
                        if p == nil {
                            p = i;
                        }
                    }
                    
                }
                self.set_next_pointer(insert, nil); // setting last free block's next to nil
                println!("all blocks marked, looking for {} bytes", size);
                current_free_size = 0;
                p = prev;
                //panic!("no more memory");
            }
            else {
                current_free_size = self.block_size(p);
                println!("[MEM] sizeof {}={}", p, current_free_size);
            }
        }
        println!("[MEM] found block {}@{} for {}b, next is {}", self.block_size(p), p, target_size, self.get_next_pointer(p));
        /*
            break block and mark it
        */
        //mark new block
        let res = p;
        self.bitmap[res] = true;
        //p += (size + 2) as usize; // + 2 accounts for the header of the new  block
        self[res - 2] = header_pack(tag, size);
        let free_size = current_free_size - (size + 2); // + 2 is the header size of the new block
        if free_size > BLOCK_SIZE_MIN as i32 {
            let new_head = res + (size) as usize + 2;
            println!("[MEM] new({}) old({})", new_head, self.head);
            self.head = new_head;
            let new_next = self.get_next_pointer(res);
            self.set_next_pointer(new_head, new_next);
            //check that the block is big enough
            println!("[MEM] free size |{}", free_size);
            self[new_head-2] = header_pack(0, free_size);
        } else {
            let old = self.head;
            /*check if there is a next block*/
            self.head = self.get_next_pointer(res);
            /*if not: mark this block as size 0*/
            println!("[MEM] old:{} new:{}", old, self.head);
        }
        res
    }

    pub fn traverse(&mut self, root: &usize) {
      //check if address is a pointer
      if self[*root] & 0b11 == 0 && self.bitmap[*root] {
        self.bitmap[*root] = false;
        let real_address: usize = (self[*root] >> 2) as usize;
        if real_address < self.content.len() && real_address > self.heap_start {
            println!("chasing pointer @{} -> block [{}]", real_address, self.block_size(real_address));
            self.scan_block(real_address);
        }
      }
    }
    pub fn scan_block(&mut self, address: usize) {
        let size = self.block_size(address) as usize;
        for i in 0..size {
            if self[address+i] & 0b11 == 0 {
                let real_address: usize = (self[address+i] >> 2) as usize;
                if real_address < self.content.len() && real_address > self.heap_start {
                    println!("chasing pointer @{} -> block [{}]", real_address, self.block_size(real_address));
                    self.traverse(&real_address);
                }
            }
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
