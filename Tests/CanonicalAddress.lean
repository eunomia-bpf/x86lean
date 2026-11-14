/-
# Paging-canonical address selection through the existing x86 step

These are post-decode AST checks, not encoded-form/hardware comparisons. The
existing model-stop convention and LOOP counter-write order remain; this does
not model precise architectural exceptions or ordinary data permissions.
-/
import X86

namespace X86.Tests.CanonicalAddress
open X86

private def bounds : List (Val × Bool × Bool) := [
  (0x0000000000000000, true, true),
  (0x0000000000000001, true, true),
  (0x00007fffffffffff, true, true),
  (0x0000800000000000, false, true),
  (0x0000ffffffffffff, false, true),
  (0x0001000000000000, false, true),
  (0x00ffffffffffffff, false, true),
  (0x0100000000000000, false, false),
  (0x7fffffffffffffff, false, false),
  (0x8000000000000000, false, false),
  (0xfeffffffffffffff, false, false),
  (0xff00000000000000, false, true),
  (0xff7fffffffffffff, false, true),
  (0xffff000000000000, false, true),
  (0xffff7fffffffffff, false, true),
  (0xffff800000000000, true, true),
  (0xfffffffffffffffe, true, true),
  (0xffffffffffffffff, true, true)
]

example : bounds.all (fun (v,lo,hi) =>
    canonical v == lo && canonical v .la48 == lo && canonical v .la57 == hi) = true := by decide

private def entry (target : Val) : Cpu :=
  { regs :=
      { rax := target, rbx := 0x8000, rsp := 0x9000, rcx := 0,
        rdx := 0x1122334455667788, r15 := 0xfedcba9876543210 },
    rip := 0x4000, flags := { cf := true, zf := true, df := true },
    mem := (Mem.empty.writeSize .q 0x8000 target).writeSize .q 0x9000 target,
    xmm := { xmm0 := 0x112233445566778899aabbccddeeff00, xmm15 := 0x8877665544332211 },
    fsBase := 0x12340000, gsBase := 0x56780000,
    oracle := { bits := fun n => n % 2 == 1, cursor := 3 } }

private def fixed (s t : Cpu) : Bool :=
  t.flags == s.flags && t.xmm == s.xmm && t.mxcsr == s.mxcsr &&
  t.fsBase == s.fsBase && t.gsBase == s.gsBase &&
  t.oracle.cursor == s.oracle.cursor &&
  (List.range 4).all (fun n => t.oracle.bits n == s.oracle.bits n)

private def stoppedAsExpected (t : Cpu) (accept : Bool) : Bool :=
  match t.ms with | none => accept | some (.unimplemented _) => !accept | _ => false

private def ea (r : GPR) : Ea := { base := some r }

private def jump (target : Val) (width : LinearAddressWidth) (accept : Bool) : Bool :=
  let s := entry target
  ([.jmp (.rel (target - 0x4002)), .jmp (.indirect (.reg .rax)),
    .jmp (.indirect (.mem (ea .rbx)))] : List Op).all (fun op =>
      let t := step { op, len := 2 } s width
      stoppedAsExpected t accept && t.rip == (if accept then target else s.rip) &&
      t.regs == s.regs && t.mem == s.mem && fixed s t)

private def callRet (target : Val) (width : LinearAddressWidth) (accept : Bool) : Bool :=
  let s := entry target
  let calls : List Op := [.call (.rel (target - 0x4002)), .call (.indirect (.reg .rax)),
    .call (.indirect (.mem (ea .rbx))), .call (.indirect (.mem (ea .rsp)))]
  calls.all (fun op =>
    let t := step { op, len := 2 } s width
    stoppedAsExpected t accept && t.rip == (if accept then target else s.rip) &&
    t.regs == (if accept then s.regs.set .rsp 0x8ff8 else s.regs) &&
    t.mem == (if accept then s.mem.writeSize .q 0x8ff8 0x4002 else s.mem) && fixed s t) &&
  (let t := step { op := .ret, len := 1 } s width;
    stoppedAsExpected t accept && t.rip == (if accept then target else s.rip) &&
    t.regs == (if accept then s.regs.set .rsp 0x9008 else s.regs) && t.mem == s.mem && fixed s t)

private def conditional (target : Val) (width : LinearAddressWidth) (accept : Bool) : Bool :=
  let s := entry target
  [true,false].all (fun take =>
    let s := { s with flags := { s.flags with zf := take } }
    let t := step { op := .jcc .e (target - 0x4002), len := 2 } s width
    let u := step { op := .jcxz false (target - 0x4002), len := 2 }
      { s with regs := s.regs.set .rcx (if take then 0 else 1) } width
    let valid := !take || accept
    stoppedAsExpected t valid && t.rip == (if take then (if accept then target else s.rip) else 0x4002) &&
    t.regs == s.regs && t.mem == s.mem && fixed s t &&
    stoppedAsExpected u valid && u.rip == t.rip &&
    u.regs == s.regs.set .rcx (if take then 0 else 1) && u.mem == s.mem && fixed s u)

private def counted (target : Val) (width : LinearAddressWidth) (accept : Bool) : Bool :=
  let s := entry target
  [true,false].all (fun take =>
    let s := { s with regs := s.regs.set .rcx (if take then 2 else 1) }
    let t := step { op := .loop .loop false (target - 0x4002), len := 2 } s width
    stoppedAsExpected t (!take || accept) &&
    t.rip == (if take then (if accept then target else s.rip) else 0x4002) &&
    t.regs == s.regs.set .rcx (if take then 1 else 0) && t.mem == s.mem && fixed s t)

private def bitAddress (address : Val) (width : LinearAddressWidth) (accept : Bool) : Bool :=
  [false,true].all (fun negative =>
    let s := entry 0
    let regs := (s.regs.set .rbx (if negative then address + 1 else address)).set .rcx
      (if negative then 0xfffffffffffffff8 else 0)
    let s := { s with regs, mem := s.mem.write address 1 }
    let t := step { op := .bit .bt .q (.mem (ea .rbx)) (.reg .rcx), len := 3 } s width
    stoppedAsExpected t accept && t.rip == (if accept then 0x4003 else s.rip) &&
    t.regs == s.regs && t.mem == s.mem && t.xmm == s.xmm &&
    t.flags.zf == s.flags.zf && t.flags.df == s.flags.df && t.flags.cf &&
    t.oracle.cursor == (if accept then 7 else 3) &&
    (if accept then true else t.flags == s.flags))

example : bounds.all (fun (v,lo,hi) =>
    [(LinearAddressWidth.la48,lo),(.la57,hi)].all (fun (width,ok) => jump v width ok)) = true := by decide
example : bounds.all (fun (v,lo,hi) =>
    [(LinearAddressWidth.la48,lo),(.la57,hi)].all (fun (width,ok) => callRet v width ok)) = true := by decide
example : bounds.all (fun (v,lo,hi) =>
    [(LinearAddressWidth.la48,lo),(.la57,hi)].all (fun (width,ok) => conditional v width ok)) = true := by decide
example : bounds.all (fun (v,lo,hi) =>
    [(LinearAddressWidth.la48,lo),(.la57,hi)].all (fun (width,ok) => counted v width ok)) = true := by decide
example : bounds.all (fun (v,lo,hi) =>
    [(LinearAddressWidth.la48,lo),(.la57,hi)].all (fun (width,ok) => bitAddress v width ok)) = true := by decide

-- run forwards its selected width rather than falling back to48 per instruction.
example : (let s := entry 0x0000800000000000;
    let i : Instr := { op := .jmp (.indirect (.reg .rax)), len := 2 };
    (run [i] s).ms.isSome && (run [i] s .la57).ms.isNone &&
    (run [i] s .la57).rip == 0x0000800000000000) = true := by decide

-- Stopped-state stability holds for the added profile as for the default.
example : (let s := { entry 0x0000800000000000 with ms := some (.unimplemented "prior stop") };
    let t := step { op := .call (.indirect (.reg .rax)), len := 2 } s .la57;
    t.rip == s.rip && t.ms == s.ms && t.regs == s.regs && t.mem == s.mem && fixed s t) = true := by decide

end X86.Tests.CanonicalAddress
