#![allow(unused_variables)]

use std::collections::BTreeMap;
use std::convert::TryInto;
use std::env;
use std::error;
use std::fmt::{self, Display, Formatter};
use std::fs::File;
use std::io::{BufReader, Read};
use std::ops::{Index, IndexMut, Range};

use object::{
    read::{ObjectSymbol, ObjectSymbolTable},
    Object, ObjectSection,
};

#[derive(Debug)]
struct RegisterFile {
    x: [u32; 32],
    // f: [f32, 32],
    pc: u32,
    mepc: u32,
    mtvec: u32,
}

impl RegisterFile {
    fn new() -> Self {
        Self {
            x: [
                0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
                0, 0, 0, 0,
            ],
            pc: 0,
            mepc: 0,
            mtvec: 0,
        }
    }

    fn csr(&self, address: u16) -> u32 {
        match address {
            0x108 => 0xff,       // satp - Supervisor address translation and protection
            0x305 => self.mtvec, // mtvec
            0x341 => self.mepc,  // mepc
            0xf14 => 0,          // mhartid
            _ => panic!("reading invalid csr at address {}", address),
        }
    }

    fn set_csr(&mut self, address: u16, val: u32) {
        match address {
            0x305 => {
                self.mtvec = val;
            }
            0x341 => {
                self.mepc = val;
            } // mepc
            0x3a0 => {} // ignore pmpcfg0
            0x3b0 => {} // ignore pmpaddr0
            _ => panic!("setting invalid csr at address {}", address),
        }
    }
}

impl Index<usize> for RegisterFile {
    type Output = u32;

    fn index(&self, index: usize) -> &Self::Output {
        if index == 0 {
            &0 // always return zero, never return a value which is actually written to this register
        } else if index < self.x.len() {
            &self.x[index]
        } else {
            panic!("invalid register index {}", index);
        }
    }
}

impl IndexMut<usize> for RegisterFile {
    fn index_mut(&mut self, index: usize) -> &mut Self::Output {
        if index < self.x.len() {
            &mut self.x[index]
        } else {
            panic!("invalid register index {}", index);
        }
    }
}

impl Display for RegisterFile {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result<(), fmt::Error> {
        for x in self.x {
            write!(f, "{:#x}, ", x)?;
        }

        write!(f, "pc: {:#x}", self.pc)?;

        Ok(())
    }
}

type RegisterIdx = u32;
type Imm = i32;

#[derive(Debug)]
struct Memory {
    map: BTreeMap<u32, Vec<u8>>,
}

impl Memory {
    fn new() -> Self {
        Self {
            map: BTreeMap::new(),
        }
    }

    fn insert(&mut self, start_addr: u32, data: &[u8]) {
        let mut v = Vec::new();
        v.extend_from_slice(data);
        self.map.insert(start_addr, v);
    }
}

impl Index<u32> for Memory {
    type Output = u8;

    fn index(&self, index: u32) -> &Self::Output {
        if let Some((k, v)) = self.map.range(..=index).next_back() {
            if *k <= index && ((index - *k) as usize) < v.len() {
                &v[(index - *k) as usize]
            } else {
                panic!("unknown memory map for {:#x}", index);
            }
        } else {
            panic!("unknown memory map at all for {:#x}", index);
        }
    }
}

// impl<'a> Index<Range<usize>> for Memory<'a> {
//     type Output = [u8];

//     fn index(&self, range: Range<usize>) -> &Self::Output {
//         &&self.x[range.start..range.end]
//     }
// }

impl IndexMut<u32> for Memory {
    fn index_mut(&mut self, index: u32) -> &mut Self::Output {
        let mem_entry = if let Some((k, v)) = self.map.range(..=index).next_back() {
            if *k <= index && ((index - *k) as usize) < v.len() {
                *k
            } else {
                panic!("unknown memory map for {:#x}", index);
            }
        } else {
            panic!("unknown memory map at all for {:#x}", index);
        };

        &mut self.map.get_mut(&mem_entry).unwrap()[(index - mem_entry) as usize]
    }
}

struct Hart<'a, M>
where
    M: Index<u32, Output = u8> + IndexMut<u32, Output = u8>,
{
    register_file: RegisterFile,
    memory: &'a mut M,
    reset_vector: u32,
}

impl<'a, M> Hart<'a, M>
where
    M: Index<u32, Output = u8> + IndexMut<u32, Output = u8>,
{
    fn new(register_file: RegisterFile, memory: &'a mut M, reset_vector: u32) -> Self {
        // representing memory as a slice is still not what we want,
        // because slices are a "view into a contiguous sequence". But
        // memory might have holes. What we want instead is, that we
        // accept arrays, slices and anything which is indexable.

        Self {
            register_file,
            memory,
            reset_vector,
        }
    }

    fn execute_next_inst(&mut self) {
        // read next instruction at PC
        // let inst_slice =
        //     &self.memory[(self.register_file.pc as usize)..((self.register_file.pc as usize) + 4)];
        // let (u32_bytes, _rest) = inst_slice.split_at(std::mem::size_of::<u32>());
        // let inst = u32::from_le_bytes(u32_bytes.try_into().unwrap());

        let inst = {
            let mut inst: u32 = self.memory[self.register_file.pc] as u32;
            inst |= (self.memory[self.register_file.pc + 1] as u32) << 8;
            inst |= (self.memory[self.register_file.pc + 2] as u32) << 16;
            inst |= (self.memory[self.register_file.pc + 3] as u32) << 24;

            inst
        };

        match self.decode(inst) {
            Some(Inst::Lui { rd, imm }) => {
                self.register_file[rd as usize] = (imm as u32);
                self.register_file.pc += 4;
            }
            Some(Inst::Auipc { rd, imm }) => {
                if imm.is_negative() {
                    self.register_file[rd as usize] =
                        self.register_file.pc.wrapping_sub(imm.unsigned_abs());
                } else {
                    self.register_file[rd as usize] =
                        self.register_file.pc.wrapping_add(imm.unsigned_abs());
                }

                self.register_file.pc += 4;
            }
            Some(Inst::Addi { rd, rs1, imm }) => {
                if imm.is_negative() {
                    self.register_file[rd as usize] =
                        self.register_file[rs1 as usize].wrapping_sub(imm.unsigned_abs());
                } else {
                    self.register_file[rd as usize] =
                        self.register_file[rs1 as usize].wrapping_add(imm.unsigned_abs());
                }

                self.register_file.pc += 4;
            }
            Some(Inst::Slti { rd, rs1, imm }) => {
                self.register_file[rd as usize] = if (self.register_file[rs1 as usize] as i32) < imm
                {
                    1
                } else {
                    0
                };
                self.register_file.pc += 4;
            }
            Some(Inst::Sltiu { rd, rs1, imm }) => {
                self.register_file[rd as usize] = if self.register_file[rs1 as usize] < imm as u32 {
                    1
                } else {
                    0
                };
                self.register_file.pc += 4;
            }
            Some(Inst::Xori { rd, rs1, imm }) => {
                self.register_file[rd as usize] = self.register_file[rs1 as usize] ^ imm as u32;
                self.register_file.pc += 4;
            }
            Some(Inst::Ori { rd, rs1, imm }) => {
                self.register_file[rd as usize] = self.register_file[rs1 as usize] | imm as u32;
                self.register_file.pc += 4;
            }
            Some(Inst::Andi { rd, rs1, imm }) => {
                self.register_file[rd as usize] = self.register_file[rs1 as usize] & imm as u32;
                self.register_file.pc += 4;
            }
            Some(Inst::Slli { rd, rs1, shamt_i }) => {
                self.register_file[rd as usize] = self.register_file[rs1 as usize] << shamt_i;
                self.register_file.pc += 4;
            }
            Some(Inst::Beq { rs1, rs2, imm }) => {
                if self.register_file[rs1 as usize] == self.register_file[rs2 as usize] {
                    if imm.is_negative() {
                        self.register_file.pc =
                            self.register_file.pc.wrapping_sub(imm.unsigned_abs());
                    } else {
                        self.register_file.pc =
                            self.register_file.pc.wrapping_add(imm.unsigned_abs());
                    }
                } else {
                    self.register_file.pc += 4;
                }
            }
            Some(Inst::Bge { rs1, rs2, imm }) => {
                if self.register_file[rs1 as usize] as i32
                    >= self.register_file[rs2 as usize] as i32
                {
                    if imm.is_negative() {
                        self.register_file.pc =
                            self.register_file.pc.wrapping_sub(imm.unsigned_abs());
                    } else {
                        self.register_file.pc =
                            self.register_file.pc.wrapping_add(imm.unsigned_abs());
                    }
                } else {
                    self.register_file.pc += 4;
                }
            }
            Some(Inst::Bgeu { rs1, rs2, imm }) => {
                if self.register_file[rs1 as usize] <= self.register_file[rs2 as usize] {
                    if imm.is_negative() {
                        self.register_file.pc =
                            self.register_file.pc.wrapping_sub(imm.unsigned_abs());
                    } else {
                        self.register_file.pc =
                            self.register_file.pc.wrapping_add(imm.unsigned_abs());
                    }
                } else {
                    self.register_file.pc += 4;
                }
            }
            Some(Inst::Blt { rs1, rs2, imm }) => {
                if (self.register_file[rs1 as usize] as i32)
                    < self.register_file[rs2 as usize] as i32
                {
                    if imm.is_negative() {
                        self.register_file.pc =
                            self.register_file.pc.wrapping_sub(imm.unsigned_abs());
                    } else {
                        self.register_file.pc =
                            self.register_file.pc.wrapping_add(imm.unsigned_abs());
                    }
                } else {
                    self.register_file.pc += 4;
                }
            }
            Some(Inst::Bltu { rs1, rs2, imm }) => {
                if self.register_file[rs1 as usize] < self.register_file[rs2 as usize] {
                    if imm.is_negative() {
                        self.register_file.pc =
                            self.register_file.pc.wrapping_sub(imm.unsigned_abs());
                    } else {
                        self.register_file.pc =
                            self.register_file.pc.wrapping_add(imm.unsigned_abs());
                    }
                } else {
                    self.register_file.pc += 4;
                }
            }
            Some(Inst::Bne { rs1, rs2, imm }) => {
                if self.register_file[rs1 as usize] != self.register_file[rs2 as usize] {
                    if imm.is_negative() {
                        self.register_file.pc =
                            self.register_file.pc.wrapping_sub(imm.unsigned_abs());
                    } else {
                        self.register_file.pc =
                            self.register_file.pc.wrapping_add(imm.unsigned_abs());
                    }
                } else {
                    self.register_file.pc += 4;
                }
            }
            Some(Inst::Lw { rd, rs1, imm }) => {
                let address = if imm.is_negative() {
                    self.register_file[rs1 as usize].wrapping_sub(imm.unsigned_abs())
                } else {
                    self.register_file[rs1 as usize].wrapping_add(imm.unsigned_abs())
                };

                self.register_file[rd as usize] = {
                    let mut word = self.memory[address] as u32;
                    word |= (self.memory[address + 1] as u32) << 8;
                    word |= (self.memory[address + 2] as u32) << 16;
                    word |= (self.memory[address + 3] as u32) << 24;

                    word
                };

                self.register_file.pc += 4;
            }
            Some(Inst::Jal { rd, imm }) => {
                self.register_file[rd as usize] = self.register_file.pc + 4;
                if rd == 0 {
                    assert_eq!(self.register_file[0], 0x0);
                }
                if imm.is_negative() {
                    self.register_file.pc -= imm.unsigned_abs();
                } else {
                    self.register_file.pc += imm.unsigned_abs();
                }
            }
            Some(Inst::Add { rd, rs1, rs2 }) => {
                self.register_file[rd as usize] =
                    self.register_file[rs1 as usize].wrapping_add(self.register_file[rs2 as usize]);
                self.register_file.pc += 4;
            }
            Some(Inst::Sub { rd, rs1, rs2 }) => {
                self.register_file[rd as usize] =
                    self.register_file[rs1 as usize].wrapping_sub(self.register_file[rs2 as usize]);
                self.register_file.pc += 4;
            }
            Some(Inst::Sll { rd, rs1, rs2 }) => {
                self.register_file[rd as usize] =
                    self.register_file[rs1 as usize] << (self.register_file[rs2 as usize] & 0x1f);
                self.register_file.pc += 4;
            }
            Some(Inst::Slt { rd, rs1, rs2 }) => {
                self.register_file[rd as usize] = if (self.register_file[rs1 as usize] as i32)
                    < self.register_file[rs2 as usize] as i32
                {
                    1
                } else {
                    0
                };
                self.register_file.pc += 4;
            }
            Some(Inst::Sltu { rd, rs1, rs2 }) => {
                self.register_file[rd as usize] =
                    if self.register_file[rs1 as usize] < self.register_file[rs2 as usize] {
                        1
                    } else {
                        0
                    };
                self.register_file.pc += 4;
            }
            Some(Inst::Xor { rd, rs1, rs2 }) => {
                self.register_file[rd as usize] =
                    self.register_file[rs1 as usize] ^ self.register_file[rs2 as usize];
                self.register_file.pc += 4;
            }
            Some(Inst::Srl { rd, rs1, rs2 }) => {
                self.register_file[rd as usize] =
                    self.register_file[rs1 as usize] >> (self.register_file[rs2 as usize] & 0x1f);
                self.register_file.pc += 4;
            }
            Some(Inst::Sra { rd, rs1, rs2 }) => {
                self.register_file[rd as usize] = ((self.register_file[rs1 as usize] as i32)
                    >> (self.register_file[rs2 as usize] & 0x1f))
                    as u32;
                self.register_file.pc += 4;
            }
            Some(Inst::Or { rd, rs1, rs2 }) => {
                self.register_file[rd as usize] =
                    self.register_file[rs1 as usize] | self.register_file[rs2 as usize];
                self.register_file.pc += 4;
            }
            Some(Inst::And { rd, rs1, rs2 }) => {
                self.register_file[rd as usize] =
                    self.register_file[rs1 as usize] & self.register_file[rs2 as usize];
                self.register_file.pc += 4;
            }
            Some(Inst::Csrrw { rd: _rd, rs1, csr }) => {
                // ignore
                self.register_file
                    .set_csr(csr, self.register_file[rs1 as usize]);
                self.register_file.pc += 4;
            }
            Some(Inst::Csrrwi { rd, uimm, csr }) => {
                // ignore
                self.register_file.pc += 4;
            }
            Some(Inst::Csrrs { rd, rs1, csr }) => {
                self.register_file[rd as usize] = self.register_file.csr(csr);
                if rs1 != 0 {
                    unimplemented!(
                        "atomic read and set bits in CSR not implemented for rs1 == {}",
                        rs1
                    );
                }
                self.register_file.pc += 4;
            }
            Some(Inst::Mret) => {
                self.register_file.pc = self.register_file.mepc;
            }
            Some(Inst::Fence) => {
                // ignore
                self.register_file.pc += 4;
            }
            Some(Inst::Ecall) => {
                println!("call into environment => gp {}", self.register_file[3] >> 1);
            }
            Some(inst) => {
                self.register_file.pc += 4;
                panic!("not able to decode {:?} yet", inst);
            }
            _ => {
                panic!("invalid instruction");
            }
        }
    }

    fn reset(&mut self) {
        // set pc to an implementation-defined reset vector

        self.register_file.pc = self.reset_vector; // set it to zero for now
    }

    /// This function decodes the instruction and fetches registers.
    fn decode(&self, raw_inst: u32) -> Option<Inst> {
        let opcode = 0x7f & raw_inst;

        let mut inst = None;
        if opcode == 0x33 {
            // R-type (Integer Register-Register Operations)
            let rd = (0xf80 & raw_inst) >> 7;
            assert!(rd < 32);
            let funct3 = (0x7000 & raw_inst) >> 12;
            let rs1 = (0xf8000 & raw_inst) >> 15;
            assert!(rs1 < 32);
            let rs2 = (0x1f00000 & raw_inst) >> 20;
            assert!(rs2 < 32);
            let funct7 = (0xfe000000 & raw_inst) >> 25;

            inst = if funct3 == 0x0 {
                if funct7 == 0x0 {
                    Some(Inst::Add { rd, rs1, rs2 })
                } else if funct7 == 0x20 {
                    Some(Inst::Sub { rd, rs1, rs2 })
                } else {
                    None
                }
            } else if funct3 == 0x1 && funct7 == 0x0 {
                Some(Inst::Sll { rd, rs1, rs2 })
            } else if funct3 == 0x2 && funct7 == 0x0 {
                Some(Inst::Slt { rd, rs1, rs2 })
            } else if funct3 == 0x3 && funct7 == 0x0 {
                Some(Inst::Sltu { rd, rs1, rs2 })
            } else if funct3 == 0x4 && funct7 == 0x0 {
                Some(Inst::Xor { rd, rs1, rs2 })
            } else if funct3 == 0x5 {
                if funct7 == 0x0 {
                    Some(Inst::Srl { rd, rs1, rs2 })
                } else if funct7 == 0x20 {
                    Some(Inst::Sra { rd, rs1, rs2 })
                } else {
                    None
                }
            } else if funct3 == 0x6 && funct7 == 0x0 {
                Some(Inst::Or { rd, rs1, rs2 })
            } else if funct3 == 0x7 && funct7 == 0x0 {
                Some(Inst::And { rd, rs1, rs2 })
            } else {
                None
            };
        } else if opcode == 0x3 {
            // I-type, load
            let rd = (0xf80 & raw_inst) >> 7;
            assert!(rd < 32);
            let funct3 = (0x7000 & raw_inst) >> 12;
            let rs1 = (0xf8000 & raw_inst) >> 15;
            assert!(rs1 < 32);
            let imm = (0xfff00000 & raw_inst) as i32 >> 20;

            inst = if funct3 == 0x0 {
                Some(Inst::Lb { rd, rs1, imm })
            } else if funct3 == 0x1 {
                Some(Inst::Lh { rd, rs1, imm })
            } else if funct3 == 0x2 {
                Some(Inst::Lw { rd, rs1, imm })
            } else if funct3 == 0x4 {
                Some(Inst::Lbu { rd, rs1, imm })
            } else if funct3 == 0x5 {
                Some(Inst::Lhu { rd, rs1, imm })
            } else {
                None
            }
        } else if opcode == 0x13 {
            // I-type, non-load
            let rd = (0xf80 & raw_inst) >> 7;
            assert!(rd < 32);
            let funct3 = (0x7000 & raw_inst) >> 12;
            let rs1 = (0xf8000 & raw_inst) >> 15;
            let shamt = ((0x1f00000 & raw_inst) >> 20) as u8;
            let funct7 = (0xfe000000 & raw_inst) >> 25;
            let imm = (0xfff00000 & raw_inst) as i32 >> 20;

            inst = if funct3 == 0x0 {
                Some(Inst::Addi { rd, rs1, imm })
            } else if funct3 == 0x2 {
                Some(Inst::Slti { rd, rs1, imm })
            } else if funct3 == 0x3 {
                Some(Inst::Sltiu { rd, rs1, imm })
            } else if funct3 == 0x4 {
                Some(Inst::Xori { rd, rs1, imm })
            } else if funct3 == 0x6 {
                Some(Inst::Ori { rd, rs1, imm })
            } else if funct3 == 0x7 {
                Some(Inst::Andi { rd, rs1, imm })
            } else if funct3 == 0x1 && funct7 == 0x0 {
                Some(Inst::Slli {
                    rd,
                    rs1,
                    shamt_i: shamt,
                })
            } else if funct3 == 0x5 {
                if funct7 == 0x0 {
                    Some(Inst::Srli {
                        rd,
                        rs1,
                        shamt_i: shamt,
                    })
                } else if funct7 == 0x20 {
                    Some(Inst::Srai {
                        rd,
                        rs1,
                        shamt_i: shamt,
                    })
                } else {
                    None
                }
            } else {
                None
            };
        } else if opcode == 0x23 {
            // S-type (store operations)
            let funct3 = (0x7000 & raw_inst) >> 12;
            let rs1 = (0xf8000 & raw_inst) >> 15;
            assert!(rs1 < 32);
            let rs2 = (0x1f00000 & raw_inst) >> 20;
            assert!(rs2 < 32);
            let imm = ((0xfe000000 & raw_inst) as i32 >> 20) | (((0xf80 & raw_inst) >> 7) as i32);

            inst = if funct3 == 0x0 {
                Some(Inst::Sb { rs1, rs2, imm })
            } else if funct3 == 0x1 {
                Some(Inst::Sh { rs1, rs2, imm })
            } else if funct3 == 0x2 {
                Some(Inst::Sw { rs1, rs2, imm })
            } else {
                None
            }
        } else if opcode == 0x63 {
            // B-type
            let funct3 = (0x7000 & raw_inst) >> 12;
            let rs1 = (0xf8000 & raw_inst) >> 15;
            assert!(rs1 < 32);
            let rs2 = (0x1f00000 & raw_inst) >> 20;
            assert!(rs2 < 32);
            let imm = ((0xfe00_0000 & raw_inst) as i32 >> 20)
                | (((0xf00 & raw_inst) >> 7) as i32)
                | (((0x80 & raw_inst) << 4) as i32);

            inst = if funct3 == 0x0 {
                Some(Inst::Beq { rs1, rs2, imm })
            } else if funct3 == 0x1 {
                Some(Inst::Bne { rs1, rs2, imm })
            } else if funct3 == 0x4 {
                Some(Inst::Blt { rs1, rs2, imm })
            } else if funct3 == 0x5 {
                Some(Inst::Bge { rs1, rs2, imm })
            } else if funct3 == 0x6 {
                Some(Inst::Bltu { rs1, rs2, imm })
            } else if funct3 == 0x7 {
                Some(Inst::Bgeu { rs1, rs2, imm })
            } else {
                None
            };
        } else if opcode == 0x17 || opcode == 0x37 {
            // U-type
            let rd = (0xf80 & raw_inst) >> 7;
            assert!(rd < 32);
            let imm = (0xffff_f000 & raw_inst) as i32;

            inst = if opcode == 0x17 {
                Some(Inst::Auipc { rd, imm })
            } else if opcode == 0x37 {
                Some(Inst::Lui { rd, imm })
            } else {
                None
            };
        } else if opcode == 0x6f {
            // J-type
            let rd = (0xf80 & raw_inst) >> 7;
            let imm = ((0xffe0_0000 & raw_inst) as i32 >> 20)
                | ((0x10_0000 & raw_inst) as i32 >> 9)
                | ((0xf_f000 & raw_inst) as i32);
            assert!(rd < 32, "raw_inst: {:#x}", raw_inst);

            eprintln!("rd = {}, imm = {}", rd, imm);

            inst = Some(Inst::Jal { rd, imm });
        } else if opcode == 0x67 {
            // J-type & I-type -> jump with immediate
            let rd = (0xf80 & raw_inst) >> 7;
            assert!(rd < 32);
            let funct3 = (0x7000 & raw_inst) >> 12;
            let rs1 = (0xf8000 & raw_inst) >> 15;
            let imm = (0xfff00000 & raw_inst) as i32 >> 20;

            eprintln!("rd = {}, rs1 = {}, imm = {}", rd, rs1, imm);

            inst = if funct3 == 0x0 {
                Some(Inst::Jalr { rd, rs1, imm })
            } else {
                None
            };
        } else if opcode == 0x73 {
            // SYSTEM
            let rd = (0xf80 & raw_inst) >> 7;
            let rs1 = (0xf8000 & raw_inst) >> 15;
            let funct3 = (0x7000 & raw_inst) >> 12;
            let uimm = ((0xf8000 & raw_inst) >> 15) as u8;
            let csr = ((0xfff00000 & raw_inst) >> 20) as u16;

            inst = if raw_inst == 0x0000_0073 {
                Some(Inst::Ecall)
            } else if raw_inst == 0x0010_0073 {
                Some(Inst::Ebreak)
            } else if raw_inst == 0x3020_0073 {
                Some(Inst::Mret)
            } else if raw_inst == 0x1020_0073 {
                Some(Inst::Sret)
            } else if raw_inst == 0x0020_0073 {
                Some(Inst::Uret)
            } else if funct3 == 0x1 {
                Some(Inst::Csrrw { rd, rs1, csr })
            } else if funct3 == 0x2 {
                Some(Inst::Csrrs { rd, rs1, csr }) // HERE!!! (mhartid 0xf14)
            } else if funct3 == 0x3 {
                Some(Inst::Csrrc { rd, rs1, csr })
            } else if funct3 == 0x5 {
                Some(Inst::Csrrwi { rd, uimm, csr })
            } else if funct3 == 0x6 {
                Some(Inst::Csrrsi)
            } else if funct3 == 0x7 {
                Some(Inst::Csrrci)
            } else {
                None
            }
        } else if opcode == 0xf {
            // fence
            let funct3 = (0x7000 & raw_inst) >> 12;

            // fence without parameters stands for "fence iorw, iorw",
            // a simple hart implementation may interpret a fence as
            // NOP

            inst = if funct3 == 0x0 {
                Some(Inst::Fence)
            } else {
                None
            }
        } else {
            // error
            panic!("not implemented opcode {:#x}", opcode);
        }

        eprintln!("inst: {:?} {:#x}", inst, raw_inst);

        inst
    }
}

impl<'a, M> Display for Hart<'a, M>
where
    M: Index<u32, Output = u8> + IndexMut<u32, Output = u8>,
{
    fn fmt(&self, f: &mut Formatter<'_>) -> Result<(), fmt::Error> {
        write!(f, "{}", self.register_file)
    }
}

type Register = u32;

#[derive(Debug)]
enum Inst {
    Lui {
        rd: RegisterIdx,
        imm: Imm,
    },
    Auipc {
        rd: RegisterIdx,
        imm: Imm,
    },
    Jal {
        rd: RegisterIdx,
        imm: Imm,
    },
    Jalr {
        rd: RegisterIdx,
        rs1: RegisterIdx,
        imm: Imm,
    },
    Beq {
        rs1: RegisterIdx,
        rs2: RegisterIdx,
        imm: Imm,
    },
    Bne {
        rs1: RegisterIdx,
        rs2: RegisterIdx,
        imm: Imm,
    },
    Blt {
        rs1: RegisterIdx,
        rs2: RegisterIdx,
        imm: Imm,
    },
    Bge {
        rs1: RegisterIdx,
        rs2: RegisterIdx,
        imm: Imm,
    },
    Bltu {
        rs1: RegisterIdx,
        rs2: RegisterIdx,
        imm: Imm,
    },
    Bgeu {
        rs1: RegisterIdx,
        rs2: RegisterIdx,
        imm: Imm,
    },
    Lb {
        rd: RegisterIdx,
        rs1: RegisterIdx,
        imm: Imm,
    },
    Lh {
        rd: RegisterIdx,
        rs1: RegisterIdx,
        imm: Imm,
    },
    Lw {
        rd: RegisterIdx,
        rs1: RegisterIdx,
        imm: Imm,
    },
    Lbu {
        rd: RegisterIdx,
        rs1: RegisterIdx,
        imm: Imm,
    },
    Lhu {
        rd: RegisterIdx,
        rs1: RegisterIdx,
        imm: Imm,
    },
    Sb {
        rs1: RegisterIdx,
        rs2: RegisterIdx,
        imm: Imm,
    },
    Sh {
        rs1: RegisterIdx,
        rs2: RegisterIdx,
        imm: Imm,
    },
    Sw {
        rs1: RegisterIdx,
        rs2: RegisterIdx,
        imm: Imm,
    },
    Addi {
        rd: RegisterIdx,
        rs1: RegisterIdx,
        imm: Imm,
    },
    Slti {
        rd: RegisterIdx,
        rs1: RegisterIdx,
        imm: Imm,
    },
    Sltiu {
        rd: RegisterIdx,
        rs1: RegisterIdx,
        imm: Imm,
    },
    Xori {
        rd: RegisterIdx,
        rs1: RegisterIdx,
        imm: Imm,
    },
    Ori {
        rd: RegisterIdx,
        rs1: RegisterIdx,
        imm: Imm,
    },
    Andi {
        rd: RegisterIdx,
        rs1: RegisterIdx,
        imm: Imm,
    },
    Slli {
        rd: RegisterIdx,
        rs1: RegisterIdx,
        shamt_i: u8,
    },
    Srli {
        rd: RegisterIdx,
        rs1: RegisterIdx,
        shamt_i: u8,
    },
    Srai {
        rd: RegisterIdx,
        rs1: RegisterIdx,
        shamt_i: u8,
    },
    Add {
        rd: RegisterIdx,
        rs1: RegisterIdx,
        rs2: RegisterIdx,
    },
    Sub {
        rd: RegisterIdx,
        rs1: RegisterIdx,
        rs2: RegisterIdx,
    },
    Sll {
        rd: RegisterIdx,
        rs1: RegisterIdx,
        rs2: RegisterIdx,
    },
    Slt {
        rd: RegisterIdx,
        rs1: RegisterIdx,
        rs2: RegisterIdx,
    },
    Sltu {
        rd: RegisterIdx,
        rs1: RegisterIdx,
        rs2: RegisterIdx,
    },
    Xor {
        rd: RegisterIdx,
        rs1: RegisterIdx,
        rs2: RegisterIdx,
    },
    Srl {
        rd: RegisterIdx,
        rs1: RegisterIdx,
        rs2: RegisterIdx,
    },
    Sra {
        rd: RegisterIdx,
        rs1: RegisterIdx,
        rs2: RegisterIdx,
    },
    Or {
        rd: RegisterIdx,
        rs1: RegisterIdx,
        rs2: RegisterIdx,
    },
    And {
        rd: RegisterIdx,
        rs1: RegisterIdx,
        rs2: RegisterIdx,
    },
    Ecall,
    Ebreak,
    Fence,
    Csrrw {
        rd: RegisterIdx,
        rs1: RegisterIdx,
        csr: u16,
    },
    Csrrs {
        rd: RegisterIdx,
        rs1: RegisterIdx,
        csr: u16,
    },
    Csrrc {
        rd: RegisterIdx,
        rs1: RegisterIdx,
        csr: u16,
    },
    Csrrwi {
        rd: RegisterIdx,
        uimm: u8,
        csr: u16,
    },
    Csrrsi,
    Csrrci,
    Mret,
    Sret,
    Uret,
}

enum Funct3 {
    Add = 0,
}

impl Funct3 {
    const Addi: Funct3 = Funct3::Add;
}

fn main() -> Result<(), Box<dyn error::Error>> {
    let filename = if let Some(filename) = env::args().nth(1) {
        filename
    } else {
        "/home/stephan/rotate".to_string()
    };

    eprintln!("filename: {}", filename);
    let f = File::open(filename)?;

    let mut reader = BufReader::new(f);
    let mut buffer = Vec::new();

    // Read file into vector.
    reader.read_to_end(&mut buffer)?;

    let obj_file = object::File::parse(&*buffer)?;

    println!(
        "architecture {:?}, endianness {:?}",
        obj_file.architecture(),
        obj_file.endianness()
    );

    // read symbols, might be used to find the start symbol later
    if let Some(symbol_table) = obj_file.symbol_table() {
        for symbol in symbol_table.symbols() {
            println!("symbol: {}", symbol.name()?);
        }
    }

    let mut memory = Memory::new();

    for section in obj_file.sections() {
        println!(
            "{:#x?}, address = {:#x}, name = \"{}\"",
            section.data()?,
            section.address(),
            section.name()?
        );

        if !section.data()?.is_empty() {
            memory.insert(
                section
                    .address()
                    .try_into()
                    .expect("must be a 32 bit address"),
                section.data()?,
            );

            eprintln!("memory {:?}", memory);
            memory[section.address().try_into().unwrap()];
        }
    }

    let mut hart = Hart::new(RegisterFile::new(), &mut memory, 0x80000000);
    hart.reset();
    for i in 0..550 {
        hart.execute_next_inst();
        println!("{}", hart);
    }

    Ok(())
}

#[cfg(test)]
mod tests {
    #[test]
    fn test_register_file_always_returns_zero_for_x0() {
        let mut register_file = super::RegisterFile::new();

        register_file[0] = 0xdeadbeaf;

        assert_eq!(register_file[0], 0x0);
    }

    #[test]
    fn test_register_file_always_returns_last_value_for_registers_other_than_x0() {
        let mut register_file = super::RegisterFile::new();

        for x in 1..32 {
            register_file[x] = 0xdeadbeaf;
            assert_eq!(register_file[x], 0xdeadbeaf);
        }
    }
}
