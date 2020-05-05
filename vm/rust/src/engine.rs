use std::io;

use crate::memory_nofree::Memory;
use crate::{L3Value, LOG2_VALUE_BYTES, TAG_REGISTER_FRAME};

const ADD     : L3Value =  0;
const SUB     : L3Value =  1;
const MUL     : L3Value =  2;
const DIV     : L3Value =  3;
const MOD     : L3Value =  4;
const LSL     : L3Value =  5;
const LSR     : L3Value =  6;
const AND     : L3Value =  7;
const OR      : L3Value =  8;
const XOR     : L3Value =  9;
const JLT     : L3Value = 10;
const JLE     : L3Value = 11;
const JEQ     : L3Value = 12;
const JNE     : L3Value = 13;
const JI      : L3Value = 14;
const CALL_NI : L3Value = 15;
const CALL_ND : L3Value = 16;
const CALL_TI : L3Value = 17;
const CALL_TD : L3Value = 18;
const RET     : L3Value = 19;
const HALT    : L3Value = 20;
const LDLO    : L3Value = 21;
const LDHI    : L3Value = 22;
const MOVE    : L3Value = 23;
const RALO    : L3Value = 24;
const BALO    : L3Value = 25;
const BSIZ    : L3Value = 26;
const BTAG    : L3Value = 27;
const BGET    : L3Value = 28;
const BSET    : L3Value = 29;
const BREA    : L3Value = 30;
const BWRI    : L3Value = 31;

enum RegBank { Cb, Ib, Lb, _Lb1, _Lb2, _Lb3, Lb4, Ob }

pub struct Engine {
    base_regs: [usize; 8],
    mem: Memory,
}

fn extract_u(instr: L3Value, start: u32, len: u32) -> L3Value {
    (instr >> start) & ((1 << len) - 1)
}

fn extract_s(instr: L3Value, start: u32, len: u32) -> L3Value {
    let bits = extract_u(instr, start, len);
    let m = 1 << (len - 1);
    (bits ^ m) - m
}

fn opcode(instr: L3Value) -> L3Value {
    extract_u(instr, 27, 5)
}

fn index_to_address(index: usize) -> L3Value {
    (index << LOG2_VALUE_BYTES) as L3Value
}

fn address_to_index(addr: L3Value) -> usize {
    debug_assert!(addr & ((1 << LOG2_VALUE_BYTES) - 1) == 0,
                  "invalid address: {} (16#{:x})", addr, addr);
    (addr >> LOG2_VALUE_BYTES) as usize
}

fn offset_pc(pc: usize, offset: L3Value) -> usize {
    ((pc as L3Value) + offset) as usize
}

impl Engine {
    pub fn new(mem: Memory) -> Engine {
        Engine { base_regs: [0; 8], mem: mem }
    }

    fn cb(&self) -> usize { self.base_regs[RegBank::Cb as usize] }
    fn ib(&self) -> usize { self.base_regs[RegBank::Ib as usize] }
    fn lb(&self) -> usize { self.base_regs[RegBank::Lb as usize] }
    fn ob(&self) -> usize { self.base_regs[RegBank::Ob as usize] }

    pub fn set_cb(&mut self, v: usize) {
        self.base_regs[RegBank::Cb as usize] = v
    }
    fn set_ib(&mut self, v: usize) {
        self.base_regs[RegBank::Ib as usize] = v
    }
    fn set_lb(&mut self, v: usize) {
        for i in (RegBank::Lb as usize)..=(RegBank::Lb4 as usize) {
            self.base_regs[i as usize] = v + (i - RegBank::Lb as usize) * 32
        }
    }
    fn set_ob(&mut self, v: usize) {
        self.base_regs[RegBank::Ob as usize] = v
    }

    fn gc_roots(&self) -> [usize; 4] {
        [ self.cb(), self.ib(), self.lb(), self.ob() ]
    }

    fn reg_ix(&self, r: usize) -> usize {
        self.base_regs[r >> 5] + (r & 0b11111)
    }

    fn ra_ix(&self, instr: L3Value) -> usize {
        self.reg_ix(extract_u(instr, 0, 8) as usize)
    }

    fn rb_ix(&self, instr: L3Value) -> usize {
        self.reg_ix(extract_u(instr, 8, 8) as usize)
    }

    fn rc_ix(&self, instr: L3Value) -> usize {
        self.reg_ix(extract_u(instr, 16, 8) as usize)
    }

    fn ra(&self, instr: L3Value) -> L3Value {
        self.mem[self.ra_ix(instr)]
    }

    fn rb(&self, instr: L3Value) -> L3Value {
        self.mem[self.rb_ix(instr)]
    }

    fn rc(&self, instr: L3Value) -> L3Value {
        self.mem[self.rc_ix(instr)]
    }

    fn arith<F>(&mut self, instr: L3Value, op: F)
        where F: Fn(L3Value, L3Value) -> L3Value {
        let ra_ix = self.ra_ix(instr);
        let l = self.rb(instr);
        let r = self.rc(instr);
        self.mem[ra_ix] = op(l, r)
    }

    fn cond_pc<F>(&mut self, pc: usize, instr: L3Value, op: F) -> usize
        where F: Fn(L3Value, L3Value) -> bool {
        let l = self.ra(instr);
        let r = self.rb(instr);
        offset_pc(pc, if op(l, r) { extract_s(instr, 16, 11) } else { 1 })
    }

    fn call(&mut self,
            target_pc: usize,
            ib: L3Value,
            lb: L3Value,
            ob: L3Value,
            ret_pc: L3Value) -> usize {
        let new_ib = self.ob();
        self.mem[new_ib + 0] = ib;
        self.mem[new_ib + 1] = lb;
        self.mem[new_ib + 2] = ob;
        self.mem[new_ib + 3] = ret_pc;
        self.set_ib(new_ib);
        self.set_lb(0);
        self.set_ob(0);
        return target_pc;
    }

    fn ret(&mut self, ret_value: L3Value) -> usize {
        let ret_pc = address_to_index(self.mem[self.ib() + 3]);
        let new_ob = address_to_index(self.mem[self.ib() + 2]);
        let new_lb = address_to_index(self.mem[self.ib() + 1]);
        let new_ib = address_to_index(self.mem[self.ib() + 0]);
        self.set_ob(new_ob);
        self.set_lb(new_lb);
        self.set_ib(new_ib);
        self.mem[new_ob] = ret_value;
        return ret_pc;
    }

    pub fn run(&mut self) -> L3Value {
        let mut pc: usize = 0;

        loop {
            let inst = self.mem[pc];
            let opcode = opcode(inst);

            match opcode {
                ADD => {
                    self.arith(inst, |x, y| x.wrapping_add(y));
                    pc += 1;
                }
                SUB => {
                    self.arith(inst, |x, y| x.wrapping_sub(y));
                    pc += 1;
                }
                MUL => {
                    self.arith(inst, |x, y| x.wrapping_mul(y));
                    pc += 1;
                }
                DIV => {
                    self.arith(inst, |x, y| x.wrapping_div(y));
                    pc += 1;
                }
                MOD => {
                    self.arith(inst, |x, y| x.wrapping_rem(y));
                    pc += 1;
                }
                LSL => {
                    self.arith(inst, |x, y| x.wrapping_shl(y as u32));
                    pc += 1;
                }
                LSR => {
                    self.arith(inst, |x, y| x.wrapping_shr(y as u32));
                    pc += 1;
                }
                AND => {
                    self.arith(inst, |x, y| x & y);
                    pc += 1;
                }
                OR => {
                    self.arith(inst, |x, y| x | y);
                    pc += 1;
                }
                XOR => {
                    self.arith(inst, |x, y| x ^ y);
                    pc += 1;
                }
                JLT => {
                    pc = self.cond_pc(pc, inst, |x, y| x < y)
                }
                JLE => {
                    pc = self.cond_pc(pc, inst, |x, y| x <= y)
                }
                JEQ => {
                    pc = self.cond_pc(pc, inst, |x, y| x == y)
                }
                JNE => {
                    pc = self.cond_pc(pc, inst, |x, y| x != y)
                }
                JI => {
                    pc = offset_pc(pc, extract_s(inst, 0, 27))
                }
                CALL_NI => {
                    pc = self.call(address_to_index(self.ra(inst)),
                                   index_to_address(self.ib()),
                                   index_to_address(self.lb()),
                                   index_to_address(self.ob()),
                                   index_to_address(pc + 1));
                }
                CALL_ND => {
                    pc = self.call(offset_pc(pc, extract_s(inst, 0, 27)),
                                   index_to_address(self.ib()),
                                   index_to_address(self.lb()),
                                   index_to_address(self.ob()),
                                   index_to_address(pc + 1));
                }
                CALL_TI => {
                    pc = self.call(address_to_index(self.ra(inst)),
                                   self.mem[self.ib() + 0],
                                   self.mem[self.ib() + 1],
                                   self.mem[self.ib() + 2],
                                   self.mem[self.ib() + 3]);
                }
                CALL_TD => {
                    pc = self.call(offset_pc(pc, extract_s(inst, 0, 27)),
                                   self.mem[self.ib() + 0],
                                   self.mem[self.ib() + 1],
                                   self.mem[self.ib() + 2],
                                   self.mem[self.ib() + 3]);
                }
                RET => {
                    pc = self.ret(self.ra(inst));
                }
                HALT => {
                    return self.ra(inst);
                }
                LDLO => {
                    let ra_ix = self.ra_ix(inst);
                    self.mem[ra_ix] = extract_s(inst, 8, 19);
                    pc += 1;
                }
                LDHI => {
                    let ra_ix = self.ra_ix(inst);
                    let hi = extract_u(inst, 8, 16) << 16;
                    let lo = self.mem[ra_ix] & 0xFFFF;
                    self.mem[ra_ix] = hi | lo;
                    pc += 1;
                }
                MOVE => {
                    let ra_ix = self.ra_ix(inst);
                    self.mem[ra_ix] = self.rb(inst);
                    pc += 1;
                }
                RALO => {
                    let l_size = extract_u(inst, 0, 8);
                    if l_size > 0 {
                        let lb = self.mem.allocate(TAG_REGISTER_FRAME,
                                                   l_size,
                                                   self.gc_roots());
                        self.set_lb(lb)
                    }
                    let o_size = extract_u(inst, 8, 8);
                    if o_size > 0 {
                        let ob = self.mem.allocate(TAG_REGISTER_FRAME,
                                                   o_size,
                                                   self.gc_roots());
                        self.set_ob(ob)
                    }
                    pc += 1;
                }
                BALO => {
                    let tag = extract_u(inst, 16, 8);
                    let size = self.rb(inst);
                    let block_ix = self.mem.allocate(tag, size,self.gc_roots());
                    let ra_ix = self.ra_ix(inst);
                    self.mem[ra_ix] = index_to_address(block_ix);
                    pc += 1;
                }
                BSIZ => {
                    let block_ix = address_to_index(self.rb(inst));
                    let ra_ix = self.ra_ix(inst);
                    self.mem[ra_ix] = self.mem.block_size(block_ix);
                    pc += 1;
                }
                BTAG => {
                    let block_ix = address_to_index(self.rb(inst));
                    let ra_ix = self.ra_ix(inst);
                    self.mem[ra_ix] = self.mem.block_tag(block_ix);
                    pc += 1;
                }
                BGET => {
                    let block_ix = address_to_index(self.rb(inst));
                    let index = self.rc(inst) as usize;
                    let ra_ix = self.ra_ix(inst);
                    self.mem[ra_ix] = self.mem[block_ix + index];
                    pc += 1;
                }
                BSET => {
                    let block_ix = address_to_index(self.rb(inst));
                    let index = self.rc(inst) as usize;
                    self.mem[block_ix + index] = self.ra(inst);
                    pc += 1;
                }
                BREA => {
                    use std::io::{Read,Write};

                    io::stdout().flush().expect("flush error");

                    let ra_ix = self.ra_ix(inst);
                    let mut byte = [0u8; 1];
                    match io::stdin().read(&mut byte) {
                        Ok(1) => self.mem[ra_ix] = byte[0] as L3Value,
                        _     => self.mem[ra_ix] = -1
                    };
                    pc += 1;
                }
                BWRI => {
                    use std::io::Write;

                    let byte = [self.ra(inst) as u8; 1];
                    io::stdout().write(&byte).expect("write error");
                    pc += 1;
                }
                _ =>
                    panic!("unknown opcode {}", opcode)
            }
        }
    }
}
