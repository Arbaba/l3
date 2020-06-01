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
fn log(msg : std::string::String){
    //println!("{}",msg);
}

impl Memory {
    pub fn new(word_size: usize) -> Memory {
        Memory {
            heap_start: 0,
            content: vec![0; word_size],
            head: 0,
            bitmap: vec![false; word_size],
        }
    }


    pub fn set_heap_start(&mut self, heap_start_index: usize) {
        println!("HEAP SIZE: {}", self.content.len());
        debug_assert!(heap_start_index < self.content.len());
        //set head after header and set header to size of whole block.
        self.head = heap_start_index + 2;
        self.heap_start = heap_start_index + 2;
        let heap_size = (self.content.len()-1-heap_start_index) as i32;
        self[heap_start_index] = header_pack(0, heap_size);
        self[heap_start_index+1] = NIL_TARGET;
        //set minimum size of a block to store header and 
    }

    pub fn get_next_pointer(&mut self, block: usize) -> usize { 
        return address_to_index(self.content[block - 1]);
    }

    pub fn set_next_pointer(&mut self, block: usize, next_block: usize) {
        self.content[block - 1] = index_to_address(next_block);
    }

    pub fn scan_block(&mut self, address: usize) {
        let size = self.block_size(address) as usize;
        for i in 0..size {
            if self[address+i] & 0b11 == 0 {
                let real_address = address_to_index(self[address+i]);
                if real_address < self.content.len() && real_address >= self.heap_start {
                    //println!("chasing pointer @{} -> block [{}]", real_address, self.block_size(real_address));
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
              log(format!("chasing pointer @{} -> block [{}]", real_address, self.block_size(real_address)));
              self.scan_block(real_address);
          }
        }
      }

      
    pub fn mark(&mut self, _gc_roots: [usize; 4] ) {
        for root in _gc_roots.iter() {
            self.traverse(root);
        }
    }
    pub fn sweep(&mut self) -> usize{

        let mut insert = NIL;
        let mut next = NIL;
        let mut counter = 0;
        for i in self.heap_start..self.content.len() {
      
            if self.bitmap[i] { // this address is the start of a block and it is free
                if next == NIL { // set next to first non-nil block
                    next = i;
                }
                
                counter += 1;
                /*Add new block*/
                if insert != NIL && self.block_size(insert) >= BLOCK_SIZE_MIN as i32{
                    debug_assert!(self.valid_pointer(insert));
                    self.set_next_pointer(insert, i);
                }
                insert = i;
                self.bitmap[i] = false; // unnecessary really
            }
            
        }
        println!("Sweep: Recovered {} blocks", counter);
        debug_assert!(insert != NIL);
        self.set_next_pointer(insert, NIL); // setting last free block's next to nil
        return next
    }
    pub fn validate_free_list(&mut self){
        let mut counter = 0;
        let mut current : usize = self.head;
        println!("Validate free list");

       loop{
            if current == NIL {
               break;
            }
            debug_assert!(self.valid_pointer(current));
            let next_pointer = self.get_next_pointer(current);
            
            //debug_assert!(next_pointer == NIL || self.valid_pointer(next_pointer));

            current = self.get_next_pointer(current);
            counter += 1;
        }
        println!("{} blocks in the free list ", counter);
    }
    pub fn gc(&mut self, _gc_roots: [usize; 4] )->usize{
        self.mark( _gc_roots);
        return self.sweep();
    }
    pub fn allocate(&mut self,
                    tag: L3Value,
                    size: L3Value,
                    _gc_roots: [usize; 4]) -> usize {
        debug_assert!(0 <= tag && tag <= 0xFF);
        debug_assert!(0 <= size);
        println!("[MEM] allocating {} {}", tag, size);

                        
        let mut current_node = self.head;
        let mut previous_node =  NIL;
        let mut current_node_size = if self.head != NIL {self.block_size(self.head)} else {0};
        let mut used_gc = false;


        while current_node_size < size || current_node == NIL {
            previous_node = current_node;
            if current_node == NIL{
                self.head = self.gc(_gc_roots);
                current_node = self.head;
                if used_gc {
                    panic!("Tried to used GC twice in a row");
                }
                used_gc = true;
                if current_node == NIL{
                    panic!("Could not free memory");
                }
            }else {
                current_node_size = self.block_size(current_node);
                current_node = self.get_next_pointer(current_node);
            }
        } 

        self[current_node - 2] = header_pack(tag, size);
        self.bitmap[current_node] = true;
        if current_node == self.head {
            self.head = self.get_next_pointer(current_node)
        }
        return current_node;
    }

    pub fn valid_pointer(&mut self, address: usize) -> bool {
        return address >= self.heap_start && address < self.content.len()
    }

    pub fn block_tag(&self, ix: usize) -> L3Value {
        log(format!("tagof {}", ix));
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
