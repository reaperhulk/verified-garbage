import VerifiedGarbage.TCB.X86_64.Isa
import VerifiedGarbage.TCB.Print

/-!
# Intel-syntax printer for the x86-64 model

**Trusted.** Emits Intel syntax without register prefixes, which is the
default dialect of Rust's `asm!`/`naked_asm!` on x86-64.
-/

namespace VG.X86_64

def Reg.name : Reg → String
  | .rax => "rax" | .rcx => "rcx" | .rdx => "rdx" | .rbx => "rbx"
  | .rsp => "rsp" | .rbp => "rbp" | .rsi => "rsi" | .rdi => "rdi"
  | .r8 => "r8" | .r9 => "r9" | .r10 => "r10" | .r11 => "r11"
  | .r12 => "r12" | .r13 => "r13" | .r14 => "r14" | .r15 => "r15"

/-- The 32-bit name of a register (its low 32 bits). -/
def Reg.name32 : Reg → String
  | .rax => "eax" | .rcx => "ecx" | .rdx => "edx" | .rbx => "ebx"
  | .rsp => "esp" | .rbp => "ebp" | .rsi => "esi" | .rdi => "edi"
  | .r8 => "r8d" | .r9 => "r9d" | .r10 => "r10d" | .r11 => "r11d"
  | .r12 => "r12d" | .r13 => "r13d" | .r14 => "r14d" | .r15 => "r15d"

/-- `[base+index*scale+disp]` -/
def MemOp.addr (m : MemOp) : String :=
  let idx := match m.index with
    | none => ""
    | some i => s!"+{i.name}*{m.scale}"
  let d := if m.disp = 0 then "" else if m.disp > 0 then s!"+{m.disp}" else s!"{m.disp}"
  s!"[{m.base.name}{idx}{d}]"

def MemOp.str (m : MemOp) : String := s!"QWORD PTR {m.addr}"

def MemOp.str32 (m : MemOp) : String := s!"DWORD PTR {m.addr}"

def Src.str : Src → String
  | .reg r => r.name
  | .imm v => toString v.toInt
  | .mem m => m.str

/-- A 32-bit source operand. -/
def Src.str32 : Src → String
  | .reg r => r.name32
  | .imm v => toString v.toInt
  | .mem m => m.str32

def AluOp.name : AluOp → String
  | .add => "add" | .adc => "adc" | .sub => "sub" | .sbb => "sbb" | .and => "and"
  | .or => "or" | .xor => "xor" | .cmp => "cmp" | .test => "test"

def ShiftOp.name : ShiftOp → String
  | .ror => "ror" | .shr => "shr"

def Instr.asm : Instr → List String
  | .mov d s => [s!"mov {d.name}, {s.str}"]
  | .store m r => [s!"mov {m.str}, {r.name}"]
  | .alu op d s => [s!"{op.name} {d.name}, {s.str}"]
  | .mov32 d s => [s!"mov {d.name32}, {s.str32}"]
  | .store32 m r => [s!"mov {m.str32}, {r.name32}"]
  | .alu32 op d s => [s!"{op.name} {d.name32}, {s.str32}"]
  | .shift32 op d n => [s!"{op.name} {d.name32}, {n}"]
  | .bswap32 d => [s!"bswap {d.name32}"]
  | .shift op d n => [s!"{op.name} {d.name}, {n}"]
  | .bswap d => [s!"bswap {d.name}"]
  -- `movabs` always selects the `REX.W + B8+rd io` encoding, whatever the value.
  | .movImm64 d v => [s!"movabs {d.name}, {v.toInt}"]

def Cond.name : Cond → String
  | .e => "e" | .ne => "ne" | .b => "b" | .ae => "ae"

def printer : Printer isa where
  instr := Instr.asm
  branch c l := s!"j{c.name} {l}"
  jump l := s!"jmp {l}"
  ret := ["ret"]

end VG.X86_64
