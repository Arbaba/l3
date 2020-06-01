use crate::L3Value;

const NIL_TARGET: L3Value = 0;
const NIL: usize = 0;
const BLOCK_SIZE_MIN: usize = 3;
const FREE_BLOCK_TAG: L3Value = 254;

pub struct Memory {
    heap_start: usize,
    content: Vec<L3Value>,
    free_list: Vec<usize>,
    allocated: Vec<bool>,
    unreachable: Vec<bool>,
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
  //debug_assert!(addr & ((1 << 2) - 1) == 0,
  //              "invalid address: {} (16#{:x})", addr, addr);
  (addr >> 2) as usize
}

impl Memory {
  pub fn new(word_size: usize) -> Memory {
      Memory {
          content: vec![0; word_size],
          heap_start: 0,
          free_list: Vec::new(),
          allocated: vec![false;  word_size],
          unreachable: vec![false; word_size],
      }
  }

  pub fn set_heap_start(&mut self, heap_start_index: usize) {
      debug_assert!(heap_start_index < self.content.len());
      self.heap_start = heap_start_index + 2;
      let first_block_size = self.content.len() - heap_start_index;
      self[heap_start_index] = header_pack(FREE_BLOCK_TAG, first_block_size as L3Value);
      self.free_list.push(self.heap_start);
  }

  pub fn is_valid_ptr(&self, ptr: usize) -> bool {
    ptr >= self.heap_start && ptr < self.content.len()
  }

  pub fn walk(&mut self, addr: L3Value) {
    if addr & 0b11 == 0 {
      let root = address_to_index(addr);
      if self.is_valid_ptr(root) && self.unreachable[root] {
        self.unreachable[root] = false;
        let block_size = self.block_size(root);
        for i in 0..(block_size as usize) {
          self.walk(self[i + root]);
        }
      }
    }
  }

  pub fn try_coalesce(&mut self, block: usize, annex: usize) {
    let prev_size = self.block_size(block);
    let next_size = self.block_size(annex);
    if (prev_size as usize) + block + 2 == annex {
      debug_assert!(self.block_tag(block) == FREE_BLOCK_TAG);
      self.write_header(block, FREE_BLOCK_TAG, prev_size + next_size + 2);
    } else {
      self.write_header(annex, FREE_BLOCK_TAG, next_size);
      self.free_list.push(annex);
    }
  }

  pub fn sweep(&mut self) {
    self.free_list.truncate(0);
    for ix in self.heap_start..self.content.len() {
      if self.unreachable[ix] {
        //recovered free block
        self.allocated[ix] = false;
        self.write_header(ix, FREE_BLOCK_TAG, self.block_size(ix));
        match self.free_list.last() {
          None => self.free_list.push(ix),
          Some(&addr) => self.try_coalesce(addr, ix),
        }
      }
    }
  }

  pub fn mark_n_sweep(&mut self, _gc_roots: [usize; 4]) {
    //marking
    for (i, val) in self.allocated.iter().enumerate() {
      self.unreachable[i] = *val;
    }
    for root in _gc_roots.iter() {
      self.walk(index_to_address(*root));
    }
    self.sweep();
  }

  pub fn find_first(&mut self, size: L3Value, _gc_roots: [usize; 4]) -> usize {
    let mut found = false;
    let mut id = 0;
    let mut res = 0;
    for (i, ix) in self.free_list.iter().enumerate() {
      if self.block_size(*ix) > size {
        found = true;
        res = *ix;
        id = i;
        break;
      }
    }
    if found {
      debug_assert!(self.block_tag(res) == FREE_BLOCK_TAG, "block tag {} at {} (@{}) was not free" ,self.block_tag(res), id, res);
      debug_assert!(!self.allocated[res]);
      self.free_list.remove(id);
      return res;
    }
    self.mark_n_sweep(_gc_roots);
    self.find_first(size, _gc_roots)
  }

  pub fn write_header(&mut self, p: usize, tag: L3Value, size: L3Value) {
    let b = self.block_tag(p-2);
    debug_assert!(!self.allocated[p], "Tried to rewrite header @{} to {}/{}", p, tag, size);
    self[p - 2] = header_pack(tag, size);
  }

  pub fn split(&mut self, p: usize, target_size: L3Value) {
    let available_size = self.block_size(p) - 2 - target_size;
    if available_size > BLOCK_SIZE_MIN as L3Value {
      let new_block_address = p + (target_size as usize) + 2;
      self.write_header(new_block_address, FREE_BLOCK_TAG, available_size);
      self.free_list.push(new_block_address);
    }
  }

  pub fn allocate(&mut self,
                  tag: L3Value,
                  size: L3Value,
                  _gc_roots: [usize; 4]) -> usize {
      let copy = _gc_roots.clone();
      let res = self.find_first(size, _gc_roots);
      //println!("alloc=@{}", res);
      self.split(res, size);
      self.write_header(res, tag, size);
      self.allocated[res] = true;
      debug_assert!(copy == _gc_roots);
      res
  }

  pub fn block_tag(&self, ix: usize) -> L3Value {
      //debug_assert!(self.is_valid_ptr(ix), "block-tag: invalid ptr {}", ix);
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
