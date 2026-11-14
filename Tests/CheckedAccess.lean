/-
# Checked scalar access regressions

Numerical execution is compared with the existing step, with separate literal
load/store goldens. Fault/event/permission/initialization expectations are
provided independently of the checked planner. All checks use kernel decide.
-/
import X86

namespace X86.Tests.CheckedAccess
open X86

private def address : Val := 0x1000
private def ea : Ea := { base := some .rbx }
private def memory : Operand := .mem ea
private def initial : Val := 0x8877665544332211
private def input : Val := 0x1122334455667788
private def prior : MemoryAccessEvent := .memory .read 0x9000 [9] true

private def entry (base data : Val) (zf : Bool := true) : Cpu :=
  let regs := GPR.all.foldl (fun regs r => regs.set r (0xaabbccdd00000000 + BitVec.ofNat 64 r.index.val)) ({} : Regs)
  { regs := ((regs.set .rax input).set .rbx address).set .rcx 1,
    rip := 0x4000, flags := { cf := true, zf, df := true },
    mem := ((Mem.empty.writeSize .q base data).write (base - 1) 0xa5).write (base + 8) 0x5a,
    xmm := { xmm0 := 0x112233445566778899aabbccddeeff00, xmm15 := 0xfedcba9876543210 },
    fsBase := 0x2000, gsBase := 0x3000,
    oracle := { bits := fun n => n % 2 == 1, cursor := 3 } }

private def sameCpu (s t : Cpu) : Bool :=
  s.regs == t.regs && s.rip == t.rip && s.flags == t.flags && s.mem == t.mem && s.ms == t.ms &&
  s.xmm == t.xmm && s.mxcsr == t.mxcsr && s.fsBase == t.fsBase && s.gsBase == t.gsBase &&
  s.oracle.cursor == t.oracle.cursor && (List.range 8).all (fun i => s.oracle.bits i == t.oracle.bits i)

private def bytes (n : Nat) (value : Val) : List (BitVec 8) :=
  (List.range n).map (fun i => (value >>> (i*8)).setWidth 8)

private structure Case where
  op : Op
  readBytes : Nat := 0
  writeBytes : Nat := 0
  data : Val := initial
  stored : Val := 0
  rax : Option Val := none
  base : Val := address
  zf : Bool := true

private def profile (c : Case) (ci : Nat) : MemoryProfile :=
  let readLast := c.base + BitVec.ofNat 64 (c.readBytes - 1)
  let writeLast := c.base + BitVec.ofNat 64 (c.writeBytes - 1)
  { readable := fun a => !((ci == 1 || ci == 2 || ci == 5) && a == (if ci == 2 then readLast else c.base)),
    writable := fun a => !((ci == 3 || ci == 4 || ci == 5) && a == (if ci == 4 then writeLast else c.base)),
    initialized := fun a => ci != 6 && (ci != 7 || a == c.base) }

private def check (c : Case) (ci : Nat) : Bool :=
  let cpu := entry c.base c.data c.zf
  let p := profile c ci
  let s : CheckedState := { cpu, profile := some p, events := [prior] }
  let i : Instr := { op := c.op, len := 3 }
  let t := stepChecked i s
  let readDenied := c.readBytes > 0 && (ci == 1 || ci == 2 || ci == 5)
  let writeDenied := c.writeBytes > 0 && (ci == 3 || ci == 4 || ci == 5)
  let fault := if readDenied then some (ExecutionFault.read c.base c.readBytes)
    else if writeDenied then some (.write c.base c.writeBytes) else none
  let success := fault.isNone
  let readEvents := if c.readBytes > 0 && !readDenied then
    [MemoryAccessEvent.memory .read c.base (bytes c.readBytes c.data)
      (ci != 6 && (ci != 7 || c.readBytes == 1))] else []
  let tail := match fault with
    | some f => [MemoryAccessEvent.fault f]
    | none => if c.writeBytes > 0 then [.memory .write c.base (bytes c.writeBytes c.stored) true] else []
  t.fault == fault && t.cpu.ms.isNone && t.events == [prior] ++ readEvents ++ tail &&
  sameCpu t.cpu (if success then step i cpu else cpu) &&
  (if success then match c.rax with | none => true | some value => t.cpu.regs.rax == value else true) &&
  (List.range 10).all (fun n =>
    let a := c.base - 1 + BitVec.ofNat 64 n
    t.cpu.mem.read a == (if success && 1 <= n && n <= c.writeBytes then
      (c.stored >>> (8*(n-1))).setWidth 8 else cpu.mem.read a)) &&
  (match t.profile with
    | none => false
    | some after => (List.range 10).all (fun n =>
      let a := c.base - 1 + BitVec.ofNat 64 n
      after.readable a == p.readable a && after.writable a == p.writable a &&
      after.initialized a == (if success && 1 <= n && n <= c.writeBytes then true else p.initialized a)))

-- The result and six arithmetic flags are independent oracle bits. Literal
-- projections detect draw order, cursor, byte ordering and surrounding-state
-- corruption without treating the default harness refusal as an oracle.
private def undefinedMemoryResult (kind : DShiftKind) (count : BitVec 8) (cl : Bool)
    (pattern : Val) (mode : Nat) (target : Val := 0x1000)
    (operand : Ea := { base := some .rbx }) : Bool :=
  let cpu := entry target initial
  let cpu := { cpu with
    regs := cpu.regs.set .rcx (if cl then count.setWidth 64 else 0xdeadbeef)
    oracle := { bits := fun n => pattern.getLsbD (n-9), cursor := 9 } }
  let p := profile { op := .nop none, base := target, readBytes := 2, writeBytes := 2 } mode
  let amount := if cl then ShiftAmt.cl else .imm8 count
  let i : Instr := { op := .dshift kind .w (.mem operand) .rax amount, len := 3 }
  let t := stepChecked i { cpu, profile := some p, events := [prior] }
  let rd := mode == 1 || mode == 2 || mode == 5
  let wr := mode == 3 || mode == 4 || mode == 5
  let fault := if rd then some (ExecutionFault.read target 2) else if wr then some (.write target 2) else none
  let value := pattern >>> 6
  let want := { cpu with
    flags := { cpu.flags with
      cf := pattern.getLsbD 0
      pf := pattern.getLsbD 1
      af := pattern.getLsbD 2
      zf := pattern.getLsbD 3
      sf := pattern.getLsbD 4
      of := pattern.getLsbD 5 }
    oracle := { cpu.oracle with cursor := 31 }
    mem := cpu.mem.writeSize .w target value
    rip := 0x4003 }
  let reads := if rd then [] else [MemoryAccessEvent.memory .read target [0x11,0x22] (mode != 6 && mode != 7)]
  let tail := match fault with | some f => [.fault f] | none => [.memory .write target (bytes 2 value) true]
  t.fault == fault && t.cpu.ms.isNone && sameCpu t.cpu (if fault.isNone then want else cpu) &&
  t.events == [prior] ++ reads ++ tail &&
  (List.range 32).all (fun n => t.cpu.oracle.bits n == cpu.oracle.bits n) &&
  (match t.profile with | none => false | some after => (List.range 5).all (fun n =>
    let a := target-1+BitVec.ofNat 64 n
    after.readable a == p.readable a && after.writable a == p.writable a &&
    after.initialized a == (if fault.isNone && 1 <= n && n <= 2 then true else p.initialized a)))

-- Every undefined 16-bit masked count, both instructions and CL/immediate,
-- with first/last-byte read/write failures and actual uninitialized bytes.
example : (List.range 15).all (fun n => [false,true].all (fun cl =>
    (List.range 8).all (undefinedMemoryResult .shld (BitVec.ofNat 8 (n+17)) cl 0x2aaaaa))) = true := by decide
example : (List.range 15).all (fun n => [false,true].all (fun cl =>
    (List.range 8).all (undefinedMemoryResult .shrd (BitVec.ofNat 8 (n+17)) cl 0x155555))) = true := by decide

-- One independent bit at each of the six flag and sixteen result positions.
example : (List.range 22).all (fun n => [DShiftKind.shld,.shrd].all (fun k =>
    [false,true].all (fun cl => undefinedMemoryResult k 17 cl (1 <<< n) 0))) = true := by decide
example : ([0,0x3fffff,0x2aaaaa,0x155555] : List Val).all (fun bits =>
    [DShiftKind.shld,.shrd].all (fun k => [false,true].all (fun cl =>
      undefinedMemoryResult k 31 cl bits 6))) = true := by decide

-- High count bits are masked; RIP/FS/GS and unaligned addresses use pre-state EA.
example : ([49,63,145,159,241,255] : List (BitVec 8)).all (fun count =>
    [DShiftKind.shld,.shrd].all (fun k => [false,true].all (fun cl =>
      undefinedMemoryResult k count cl 0x2aaaaa 0))) = true := by decide
example : (([({ base := some .rbx, seg := some .fs } : Ea),
    { base := some .rbx, seg := some .gs }, { ripRel := true, disp := 16 },
    { base := some .rbx, disp := 1 }] : List Ea).zip [0x3000,0x4000,0x4013,0x1001] |>.all (fun (operand,target) =>
      [DShiftKind.shld,.shrd].all (fun k => [false,true].all (fun cl =>
        undefinedMemoryResult k 17 cl 0x155555 7 target operand)))) = true := by decide

-- Earlier canonicality/missing-profile/illegal-LOCK checks neither draw bits
-- nor turn undefined results into a successful zero/default store.
example : [DShiftKind.shld,.shrd].all (fun k =>
    let cpu := entry address initial
    let i : Instr := { op := .dshift k .w memory .rax (.imm8 17), len := 3 }
    let t := stepChecked i { cpu, events := [prior] }
    t.cpu.ms.isSome && t.fault.isNone && sameCpu { t.cpu with ms := none } cpu && t.events == [prior]) = true := by decide
example : [DShiftKind.shld,.shrd].all (fun k =>
    let a : Val := 0x7fffffffffff
    let cpu := { entry a initial with regs := (entry a initial).regs.set .rbx a }
    let i : Instr := { op := .dshift k .w memory .rax (.imm8 31), len := 3 }
    let t := stepChecked i { cpu, profile := some {}, events := [prior] }
    t.fault == some (.nonCanonical a) && t.cpu.ms.isNone && sameCpu t.cpu cpu &&
    t.events == [prior,.fault (.nonCanonical a)]) = true := by decide
example : [DShiftKind.shld,.shrd].all (fun k =>
    let cpu := entry address initial
    let i : Instr := { op := .dshift k .w (.mem { ea with lock := true }) .rax (.imm8 17), len := 3 }
    let t := stepChecked i { cpu, profile := some {}, events := [prior] }
    t.fault == some .invalidOpcode && t.cpu.ms.isNone && sameCpu t.cpu cpu &&
    t.events == [prior,.fault .invalidOpcode]) = true := by decide


private def moves : List Case := [
  { op := .mov .b (.reg .rax) memory, readBytes := 1, rax := some 0x1122334455667711 },
  { op := .mov .b memory (.reg .rax), writeBytes := 1, stored := input },
  { op := .mov .w (.reg .rax) memory, readBytes := 2, rax := some 0x1122334455662211 },
  { op := .mov .w memory (.reg .rax), writeBytes := 2, stored := input },
  { op := .mov .d (.reg .rax) memory, readBytes := 4, rax := some 0x44332211 },
  { op := .mov .d memory (.reg .rax), writeBytes := 4, stored := input },
  { op := .mov .q (.reg .rax) memory, readBytes := 8, rax := some 0x8877665544332211 },
  { op := .mov .q memory (.reg .rax), writeBytes := 8, stored := input },
  { op := .mov .b (.reg .rax true) memory, readBytes := 1, rax := some 0x1122334455661188 },
  { op := .mov .q memory (.reg .rbx), writeBytes := 8, stored := 0x1000 },
  { op := .mov .q (.reg .rax) (.mem { base := some .rbx, seg := some .fs }), readBytes := 8, base := 0x3000, rax := some initial },
  { op := .mov .q (.mem { base := some .rbx, seg := some .gs }) (.reg .rax), writeBytes := 8, base := 0x4000, stored := input },
  { op := .mov .q (.reg .rbx) memory, readBytes := 8 },
  { op := .mov .q (.reg .rax) (.mem { ripRel := true, disp := 16 }), readBytes := 8, base := 0x4013, rax := some initial }
]

private def binary : List Case := [
  { op := .bin .add .b memory (.reg .rcx), readBytes := 1, writeBytes := 1, stored := 0x8877665544332212 },
  { op := .bin .sub .b memory (.reg .rcx), readBytes := 1, writeBytes := 1, stored := 0x8877665544332210 },
  { op := .bin .and .b memory (.reg .rcx), readBytes := 1, writeBytes := 1, stored := 0x1 },
  { op := .bin .or .b memory (.reg .rcx), readBytes := 1, writeBytes := 1, stored := 0x8877665544332211 },
  { op := .bin .xor .b memory (.reg .rcx), readBytes := 1, writeBytes := 1, stored := 0x8877665544332210 },
  { op := .bin .adc .b memory (.reg .rcx), readBytes := 1, writeBytes := 1, stored := 0x8877665544332213 },
  { op := .bin .sbb .b memory (.reg .rcx), readBytes := 1, writeBytes := 1, stored := 0x887766554433220f },
  { op := .bin .cmp .b memory (.reg .rcx), readBytes := 1, writeBytes := 0, stored := 0x0 },
  { op := .bin .test .b memory (.reg .rcx), readBytes := 1, writeBytes := 0, stored := 0x0 },
  { op := .bin .add .b memory (.reg .rcx), readBytes := 1, writeBytes := 1, data := 0xff, stored := 0 },
  { op := .bin .add .w memory (.reg .rcx), readBytes := 2, writeBytes := 2, stored := 0x8877665544332212 },
  { op := .bin .sub .w memory (.reg .rcx), readBytes := 2, writeBytes := 2, stored := 0x8877665544332210 },
  { op := .bin .and .w memory (.reg .rcx), readBytes := 2, writeBytes := 2, stored := 0x1 },
  { op := .bin .or .w memory (.reg .rcx), readBytes := 2, writeBytes := 2, stored := 0x8877665544332211 },
  { op := .bin .xor .w memory (.reg .rcx), readBytes := 2, writeBytes := 2, stored := 0x8877665544332210 },
  { op := .bin .adc .w memory (.reg .rcx), readBytes := 2, writeBytes := 2, stored := 0x8877665544332213 },
  { op := .bin .sbb .w memory (.reg .rcx), readBytes := 2, writeBytes := 2, stored := 0x887766554433220f },
  { op := .bin .cmp .w memory (.reg .rcx), readBytes := 2, writeBytes := 0, stored := 0x0 },
  { op := .bin .test .w memory (.reg .rcx), readBytes := 2, writeBytes := 0, stored := 0x0 },
  { op := .bin .add .w memory (.reg .rcx), readBytes := 2, writeBytes := 2, data := 0xffff, stored := 0 },
  { op := .bin .add .d memory (.reg .rcx), readBytes := 4, writeBytes := 4, stored := 0x8877665544332212 },
  { op := .bin .sub .d memory (.reg .rcx), readBytes := 4, writeBytes := 4, stored := 0x8877665544332210 },
  { op := .bin .and .d memory (.reg .rcx), readBytes := 4, writeBytes := 4, stored := 0x1 },
  { op := .bin .or .d memory (.reg .rcx), readBytes := 4, writeBytes := 4, stored := 0x8877665544332211 },
  { op := .bin .xor .d memory (.reg .rcx), readBytes := 4, writeBytes := 4, stored := 0x8877665544332210 },
  { op := .bin .adc .d memory (.reg .rcx), readBytes := 4, writeBytes := 4, stored := 0x8877665544332213 },
  { op := .bin .sbb .d memory (.reg .rcx), readBytes := 4, writeBytes := 4, stored := 0x887766554433220f },
  { op := .bin .cmp .d memory (.reg .rcx), readBytes := 4, writeBytes := 0, stored := 0x0 },
  { op := .bin .test .d memory (.reg .rcx), readBytes := 4, writeBytes := 0, stored := 0x0 },
  { op := .bin .add .d memory (.reg .rcx), readBytes := 4, writeBytes := 4, data := 0xffffffff, stored := 0 },
  { op := .bin .add .q memory (.reg .rcx), readBytes := 8, writeBytes := 8, stored := 0x8877665544332212 },
  { op := .bin .sub .q memory (.reg .rcx), readBytes := 8, writeBytes := 8, stored := 0x8877665544332210 },
  { op := .bin .and .q memory (.reg .rcx), readBytes := 8, writeBytes := 8, stored := 0x1 },
  { op := .bin .or .q memory (.reg .rcx), readBytes := 8, writeBytes := 8, stored := 0x8877665544332211 },
  { op := .bin .xor .q memory (.reg .rcx), readBytes := 8, writeBytes := 8, stored := 0x8877665544332210 },
  { op := .bin .adc .q memory (.reg .rcx), readBytes := 8, writeBytes := 8, stored := 0x8877665544332213 },
  { op := .bin .sbb .q memory (.reg .rcx), readBytes := 8, writeBytes := 8, stored := 0x887766554433220f },
  { op := .bin .cmp .q memory (.reg .rcx), readBytes := 8, writeBytes := 0, stored := 0x0 },
  { op := .bin .test .q memory (.reg .rcx), readBytes := 8, writeBytes := 0, stored := 0x0 },
  { op := .bin .add .q memory (.reg .rcx), readBytes := 8, writeBytes := 8, data := 0xffffffffffffffff, stored := 0 }
]

private def unary : List Case := [
  { op := .un .inc .b memory, readBytes := 1, writeBytes := 1, stored := 0x8877665544332212 },
  { op := .un .dec .b memory, readBytes := 1, writeBytes := 1, stored := 0x8877665544332210 },
  { op := .un .neg .b memory, readBytes := 1, writeBytes := 1, stored := 0x778899aabbccddef },
  { op := .un .not .b memory, readBytes := 1, writeBytes := 1, stored := 0x778899aabbccddee },
  { op := .un .inc .w memory, readBytes := 2, writeBytes := 2, stored := 0x8877665544332212 },
  { op := .un .dec .w memory, readBytes := 2, writeBytes := 2, stored := 0x8877665544332210 },
  { op := .un .neg .w memory, readBytes := 2, writeBytes := 2, stored := 0x778899aabbccddef },
  { op := .un .not .w memory, readBytes := 2, writeBytes := 2, stored := 0x778899aabbccddee },
  { op := .un .inc .d memory, readBytes := 4, writeBytes := 4, stored := 0x8877665544332212 },
  { op := .un .dec .d memory, readBytes := 4, writeBytes := 4, stored := 0x8877665544332210 },
  { op := .un .neg .d memory, readBytes := 4, writeBytes := 4, stored := 0x778899aabbccddef },
  { op := .un .not .d memory, readBytes := 4, writeBytes := 4, stored := 0x778899aabbccddee },
  { op := .un .inc .q memory, readBytes := 8, writeBytes := 8, stored := 0x8877665544332212 },
  { op := .un .dec .q memory, readBytes := 8, writeBytes := 8, stored := 0x8877665544332210 },
  { op := .un .neg .q memory, readBytes := 8, writeBytes := 8, stored := 0x778899aabbccddef },
  { op := .un .not .q memory, readBytes := 8, writeBytes := 8, stored := 0x778899aabbccddee }
]

private def extended : List Case := [
  { op := .movx .sign .q .b .rax memory, readBytes := 1, data := 0x80ff, rax := some 0xffffffffffffffff },
  { op := .movx .sign .q .w .rax memory, readBytes := 2, data := 0x80ff, rax := some 0xffffffffffff80ff },
  { op := .movx .sign .q .d .rax memory, readBytes := 4, data := 0x800180ff, rax := some 0xffffffff800180ff },
  { op := .movx .zero .d .b .rax memory, readBytes := 1, data := 0x80ff, rax := some 0xff },
  { op := .movx .zero .q .w .rax memory, readBytes := 2, data := 0x80ff, rax := some 0x80ff },
  { op := .movx .zero .w .b .rax memory, readBytes := 1, data := 0x80ff, rax := some 0x11223344556600ff }
]

private def conditional : List Case := [
  { op := .cmov .e .w .rax memory, readBytes := 2, zf := false, rax := some input },
  { op := .cmov .e .d .rax memory, readBytes := 4, zf := false, rax := some 0x55667788 },
  { op := .cmov .e .q .rax memory, readBytes := 8, zf := false, rax := some input },
  { op := .cmov .e .w .rax memory, readBytes := 2, rax := some 0x1122334455662211 },
  { op := .cmov .e .d .rax memory, readBytes := 4, rax := some 0x44332211 },
  { op := .cmov .e .q .rax memory, readBytes := 8, rax := some initial },
  { op := .setcc .e memory, writeBytes := 1, stored := 1 },
  { op := .setcc .e memory, writeBytes := 1, stored := 0, zf := false }
]

private def registerSources : List Case := [
  { op := .bin .add .b (.reg .rax) memory, readBytes := 1, rax := some 0x1122334455667799 },
  { op := .bin .add .w (.reg .rax) memory, readBytes := 2, rax := some 0x1122334455669999 },
  { op := .bin .add .d (.reg .rax) memory, readBytes := 4, rax := some 0x99999999 },
  { op := .bin .add .q (.reg .rax) memory, readBytes := 8, rax := some 0x9999999999999999 },
  { op := .bin .cmp .q (.reg .rax) memory, readBytes := 8, rax := some input }
]

example : moves.all (fun c => (List.range 8).all (check c)) = true := by decide
example : binary.all (fun c => (List.range 8).all (check c)) = true := by decide
example : unary.all (fun c => (List.range 8).all (check c)) = true := by decide
example : extended.all (fun c => (List.range 8).all (check c)) = true := by decide
example : conditional.all (fun c => (List.range 8).all (check c)) = true := by decide
example : registerSources.all (fun c => (List.range 8).all (check c)) = true := by decide

-- All bytes are canonical before permission checking. Wrapping stays within
-- this flat profile; this is not a full MMU/cross-boundary hardware claim.
private def spans : List (Val × Bool × Bool) := [
  (0x00007ffffffffff8, true, true),
  (0x00007fffffffffff, false, true),
  (0x0000800000000000, false, true),
  (0x00ffffffffffffff, false, false),
  (0xff00000000000000, false, true),
  (0xfffffffffffffff8, true, true),
  (0xffffffffffffffff, true, true)
]

example : spans.all (fun (base,lo,hi) =>
    [(LinearAddressWidth.la48,lo),(.la57,hi)].all (fun (width,valid) =>
      [false,true].all (fun store => [false,true].all (fun deny =>
        let cpu := { entry base initial with regs := (entry base initial).regs.set .rbx base }
        let p : MemoryProfile := { readable := fun _ => !deny, writable := fun _ => !deny }
        let s : CheckedState := { cpu, addressWidth := width, profile := some p, events := [prior] }
        let i : Instr := { op := if store then .mov .q memory (.reg .rax) else .mov .q (.reg .rax) memory, len := 3 }
        let t := stepChecked i s
        let fault := if !valid then some (ExecutionFault.nonCanonical base)
          else if deny then some (if store then .write base 8 else .read base 8) else none
        t.fault == fault && t.cpu.ms.isNone &&
        sameCpu t.cpu (if fault.isNone then step i cpu width else cpu) &&
        t.events == [prior] ++ (match fault with
          | some f => [.fault f]
          | none => [.memory (if store then .write else .read) base (bytes 8 (if store then input else initial)) store]) &&
        (match t.profile with
          | none => false
          | some after => (List.range 10).all (fun n =>
            after.initialized (base - 1 + BitVec.ofNat 64 n) == (fault.isNone && store && 1 <= n && n <= 8))))))) = true := by decide

-- Missing or unsupported capabilities never invoke the numeric step as a
-- fallback. Register-only MOV/LEA and memory-shaped NOP need no profile.
example : ([.mov .q (.reg .rax) memory, .push .q (.reg .rax),
    .bin .add .q (.mem { base := some .rbx, lock := true }) (.reg .rax)] : List Op).all (fun op =>
    let cpu := entry address initial
    let t := stepChecked { op, len := 3 } { cpu, events := [prior] }
    t.cpu.ms.isSome && sameCpu { t.cpu with ms := none } cpu &&
    t.fault.isNone && t.events == [prior]) = true := by decide

example : ([.mov .q (.reg .rdx) (.reg .rax),
    .lea .q .rax { base := some .rbx, disp := 16, seg := some .fs },
    .nop (some (.mem { disp := 0x8000000000000000 }))] : List Op).all (fun op =>
    let cpu := entry address initial
    let i : Instr := { op, len := 3 }
    let t := stepChecked i { cpu, events := [prior] }
    t.fault.isNone && t.profile.isNone && t.events == [prior] && sameCpu t.cpu (step i cpu)) = true := by decide

-- Malformed AST operands are model errors before any permission observation.
example : ([.mov .q memory memory, .bin .add .q memory memory,
    .mov .q (.imm 0) memory, .bin .add .q (.imm 0) memory,
    .un .inc .q (.imm 0), .movx .zero .q .b .rax (.imm 0),
    .cmov .e .q .rax (.imm 0), .setcc .e (.imm 0)] : List Op).all (fun op =>
    [false,true].all (fun bound =>
      let cpu := entry address initial
      let p : MemoryProfile := { readable := fun _ => false, writable := fun _ => false }
      let t := stepChecked { op, len := 3 }
        { cpu, profile := if bound then some p else none, events := [prior] }
      (match t.cpu.ms with | some (.illegalOperands _) => true | _ => false) &&
      sameCpu { t.cpu with ms := none } cpu && t.fault.isNone && t.events == [prior])) = true := by decide

-- #UD outcomes are distinct from a model refusal and are terminal.
example : ([.ud2, .mov .q (.mem { base := some .rbx, lock := true }) (.reg .rax)] : List Op).all (fun op =>
    let cpu := entry address initial
    let s := stepChecked { op, len := 3 } { cpu, events := [prior] }
    let t := stepChecked { op := .nop none, len := 1 } s
    s.fault == some .invalidOpcode && s.cpu.ms.isNone && sameCpu s.cpu cpu &&
    t.fault == s.fault && sameCpu t.cpu s.cpu && t.events == [prior,.fault .invalidOpcode]) = true := by decide

-- Successful stores initialize the exact range. A later denied RMW keeps its
-- read prefix and all prior effects but commits no flags/oracle/register/PC.
example : (let cpu := entry address initial
    let p : MemoryProfile := {}
    let start : CheckedState := { cpu, profile := some p, events := [prior] }
    let s := runChecked [ { op := .mov .q memory (.reg .rax), len := 3 },
      { op := .mov .q (.reg .rdx) memory, len := 3 } ] start
    let s := { s with profile := s.profile.map (fun p => { p with writable := fun _ => false }) }
    let t := runChecked [ { op := .bin .add .q memory (.reg .rcx), len := 3 },
      { op := .mov .q (.reg .rax) memory, len := 3 } ] s
    t.fault == some (.write address 8) && t.cpu.ms.isNone && sameCpu t.cpu s.cpu &&
    t.cpu.rip == 0x4006 && t.cpu.regs.rdx == input &&
    t.events == [prior, .memory .write address (bytes 8 input) true,
      .memory .read address (bytes 8 input) true, .memory .read address (bytes 8 input) true,
      .fault (.write address 8)]) = true := by decide


-- Width-specific, literal values for count-one shifts and rotations. The same
-- permission/init harness checks CL and immediate forms, including zero counts.
private def shiftRows : List (Size × Val × Val × Val × Val × Val × Val) := [
  (.b, 0x22, 0x8, 0x8, 0x22, 0x88, 0x23),
  (.w, 0x4422, 0x1108, 0x1108, 0x4422, 0x9108, 0x4423),
  (.d, 0x88664422, 0x22199108, 0x22199108, 0x88664422, 0xa2199108, 0x88664423),
  (.q, 0x10eeccaa88664422, 0x443bb32aa2199108, 0xc43bb32aa2199108,
    0x10eeccaa88664423, 0xc43bb32aa2199108, 0x10eeccaa88664423)
]

private def checkShiftRow : (Size × Val × Val × Val × Val × Val × Val) -> Bool
  | (sz,sl,sr,sa,rl,rr,cl) =>
    let cases : List Case :=
      [(ShiftKind.shl,sl),(.shr,sr),(.sar,sa)].flatMap (fun (k,v) =>
        [ShiftAmt.imm8 1,.cl].map (fun amt =>
          { op := .shift k sz memory amt, readBytes := sz.bytes, writeBytes := sz.bytes, stored := v })) ++
      [(RotKind.rol,rl),(.ror,rr),(.rcl,cl),(.rcr,rr)].flatMap (fun (k,v) =>
        [ShiftAmt.imm8 1,.cl].map (fun amt =>
          { op := .rot k sz memory amt, readBytes := sz.bytes, writeBytes := sz.bytes, stored := v })) ++
      [0, if sz == .q then 64 else 32].flatMap (fun n =>
        ([ShiftKind.shl,.shr,.sar].map (fun k =>
          { op := .shift k sz memory (.imm8 n), readBytes := sz.bytes, writeBytes := sz.bytes, stored := initial }) ++
        [RotKind.rol,.ror,.rcl,.rcr].map (fun k =>
          { op := .rot k sz memory (.imm8 n), readBytes := sz.bytes, writeBytes := sz.bytes, stored := initial })))
    cases.all (fun c => (List.range 8).all (check c))

example : checkShiftRow shiftRows[0] = true := by decide
example : checkShiftRow shiftRows[1] = true := by decide
example : checkShiftRow shiftRows[2] = true := by decide
example : checkShiftRow shiftRows[3] = true := by decide

example : ([(Size.w,0x4422,0x9108),(Size.d,0x88664422,0xa2199108),
    (Size.q,0x10eeccaa88664422,0xc43bb32aa2199108)] : List (Size × Val × Val)).all (fun (sz,left,right) =>
    [ShiftAmt.imm8 1,.cl].all (fun amt =>
      [(DShiftKind.shld,left),(.shrd,right)].all (fun (k,value) =>
        (List.range 8).all (check { op := .dshift k sz memory .rcx amt, readBytes := sz.bytes, writeBytes := sz.bytes, stored := value }))) &&
    [DShiftKind.shld,.shrd].all (fun k =>
      (List.range 8).all (check { op := .dshift k sz memory .rcx (.imm8 0), readBytes := sz.bytes, writeBytes := sz.bytes, stored := initial }) &&
      (List.range 8).all (check { op := .dshift k sz memory .rcx (.imm8 (BitVec.ofNat 8 sz.bits)), readBytes := sz.bytes, writeBytes := sz.bytes, stored := if sz == .w then 1 else initial }))) = true := by decide

private def scalarSources : List Case := [
  { op := .bitcnt .popcnt .w .rax memory, readBytes := 2, rax := some 0x1122334455660004 },
  { op := .bitcnt .lzcnt .w .rax memory, readBytes := 2, rax := some 0x1122334455660002 },
  { op := .bitcnt .tzcnt .w .rax memory, readBytes := 2, rax := some 0x1122334455660000 },
  { op := .bitcnt .bsf .w .rax memory, readBytes := 2, rax := some 0x1122334455660000 },
  { op := .bitcnt .bsr .w .rax memory, readBytes := 2, rax := some 0x112233445566000d },
  { op := .bitcnt .popcnt .w .rax memory, readBytes := 2, data := 0, rax := some 0x1122334455660000 },
  { op := .bitcnt .lzcnt .w .rax memory, readBytes := 2, data := 0, rax := some 0x1122334455660010 },
  { op := .bitcnt .tzcnt .w .rax memory, readBytes := 2, data := 0, rax := some 0x1122334455660010 },
  { op := .bitcnt .bsf .w .rax memory, readBytes := 2, data := 0, rax := some 0x1122334455667788 },
  { op := .bitcnt .bsr .w .rax memory, readBytes := 2, data := 0, rax := some 0x1122334455667788 },
  { op := .movbe .w (.reg .rax) memory, readBytes := 2, rax := some 0x1122334455661122 },
  { op := .movbe .w memory (.reg .rax), writeBytes := 2, stored := 0x8877 },
  { op := .imulr .w .rax memory (some 2), readBytes := 2, rax := some 0x1122334455664422 },
  { op := .imulr .w .rax memory none, readBytes := 2, rax := some 0x1122334455660008 },
  { op := .bitcnt .popcnt .d .rax memory, readBytes := 4, rax := some 0xa },
  { op := .bitcnt .lzcnt .d .rax memory, readBytes := 4, rax := some 0x1 },
  { op := .bitcnt .tzcnt .d .rax memory, readBytes := 4, rax := some 0x0 },
  { op := .bitcnt .bsf .d .rax memory, readBytes := 4, rax := some 0x0 },
  { op := .bitcnt .bsr .d .rax memory, readBytes := 4, rax := some 0x1e },
  { op := .bitcnt .blsi .d .rax memory, readBytes := 4, rax := some 0x1 },
  { op := .bitcnt .popcnt .d .rax memory, readBytes := 4, data := 0, rax := some 0x0 },
  { op := .bitcnt .lzcnt .d .rax memory, readBytes := 4, data := 0, rax := some 0x20 },
  { op := .bitcnt .tzcnt .d .rax memory, readBytes := 4, data := 0, rax := some 0x20 },
  { op := .bitcnt .bsf .d .rax memory, readBytes := 4, data := 0, rax := some 0x1122334455667788 },
  { op := .bitcnt .bsr .d .rax memory, readBytes := 4, data := 0, rax := some 0x1122334455667788 },
  { op := .movbe .d (.reg .rax) memory, readBytes := 4, rax := some 0x11223344 },
  { op := .movbe .d memory (.reg .rax), writeBytes := 4, stored := 0x88776655 },
  { op := .imulr .d .rax memory (some 2), readBytes := 4, rax := some 0x88664422 },
  { op := .imulr .d .rax memory none, readBytes := 4, rax := some 0x37c60008 },
  { op := .shiftx .shl .d .rax memory .rcx, readBytes := 4, rax := some 0x88664422 },
  { op := .shiftx .shr .d .rax memory .rcx, readBytes := 4, rax := some 0x22199108 },
  { op := .shiftx .sar .d .rax memory .rcx, readBytes := 4, rax := some 0x22199108 },
  { op := .rorx .d .rax memory 0, readBytes := 4, rax := some 0x44332211 },
  { op := .rorx .d .rax memory 1, readBytes := 4, rax := some 0xa2199108 },
  { op := .bzhi .d .rax memory .rcx, readBytes := 4, rax := some 1 },
  { op := .andn .d .rax .rcx memory, readBytes := 4, rax := some 0x44332210 },
  { op := .mulx .d .rax .rdx memory, readBytes := 4 },
  { op := .bitcnt .popcnt .q .rax memory, readBytes := 8, rax := some 0x1a },
  { op := .bitcnt .lzcnt .q .rax memory, readBytes := 8, rax := some 0x0 },
  { op := .bitcnt .tzcnt .q .rax memory, readBytes := 8, rax := some 0x0 },
  { op := .bitcnt .bsf .q .rax memory, readBytes := 8, rax := some 0x0 },
  { op := .bitcnt .bsr .q .rax memory, readBytes := 8, rax := some 0x3f },
  { op := .bitcnt .blsi .q .rax memory, readBytes := 8, rax := some 0x1 },
  { op := .bitcnt .popcnt .q .rax memory, readBytes := 8, data := 0, rax := some 0x0 },
  { op := .bitcnt .lzcnt .q .rax memory, readBytes := 8, data := 0, rax := some 0x40 },
  { op := .bitcnt .tzcnt .q .rax memory, readBytes := 8, data := 0, rax := some 0x40 },
  { op := .bitcnt .bsf .q .rax memory, readBytes := 8, data := 0, rax := some 0x1122334455667788 },
  { op := .bitcnt .bsr .q .rax memory, readBytes := 8, data := 0, rax := some 0x1122334455667788 },
  { op := .movbe .q (.reg .rax) memory, readBytes := 8, rax := some 0x1122334455667788 },
  { op := .movbe .q memory (.reg .rax), writeBytes := 8, stored := 0x8877665544332211 },
  { op := .imulr .q .rax memory (some 2), readBytes := 8, rax := some 0x10eeccaa88664422 },
  { op := .imulr .q .rax memory none, readBytes := 8, rax := some 0xa3e963337c60008 },
  { op := .shiftx .shl .q .rax memory .rcx, readBytes := 8, rax := some 0x10eeccaa88664422 },
  { op := .shiftx .shr .q .rax memory .rcx, readBytes := 8, rax := some 0x443bb32aa2199108 },
  { op := .shiftx .sar .q .rax memory .rcx, readBytes := 8, rax := some 0xc43bb32aa2199108 },
  { op := .rorx .q .rax memory 0, readBytes := 8, rax := some 0x8877665544332211 },
  { op := .rorx .q .rax memory 1, readBytes := 8, rax := some 0xc43bb32aa2199108 },
  { op := .bzhi .q .rax memory .rcx, readBytes := 8, rax := some 1 },
  { op := .andn .q .rax .rcx memory, readBytes := 8, rax := some 0x8877665544332210 },
  { op := .mulx .q .rax .rdx memory, readBytes := 8 }
]
example : (scalarSources.take 20).all (fun c => (List.range 8).all (check c)) = true := by decide
example : ((scalarSources.drop 20).take 20).all (fun c => (List.range 8).all (check c)) = true := by decide
example : (scalarSources.drop 40).all (fun c => (List.range 8).all (check c)) = true := by decide

-- A source can alias the destination's address register; sources are captured
-- before either numerical write. Register-only forms require no memory profile.
example : ([(Op.shiftx .shl .q .rbx memory .rcx), .rorx .q .rbx memory 1,
    .bzhi .q .rbx memory .rcx, .andn .q .rbx .rcx memory,
    .mulx .q .rbx .rbx memory, .bitcnt .popcnt .q .rbx memory,
    .imulr .q .rbx memory (some 2)] : List Op).all (fun op =>
      (List.range 8).all (check { op, readBytes := 8 })) = true := by decide

example : ([.shift .shl .d (.reg .rax) (.imm8 0), .rot .rcr .d (.reg .rax) (.imm8 0),
    .dshift .shld .d (.reg .rax) .rdx (.imm8 0),
    .shiftx .shl .d .rax (.reg .rax) .rcx, .rorx .d .rax (.reg .rax) 0,
    .bzhi .d .rax (.reg .rax) .rcx, .andn .d .rax .rcx (.reg .rax),
    .mulx .d .rax .rax (.reg .rax), .bitcnt .popcnt .q .rax (.reg .rax),
    .imulr .q .rax (.reg .rax) (some 2), .bswap .d .rax, .bswap .q .rax] : List Op).all (fun op =>
      let cpu := entry address initial
      let i : Instr := { op, len := 3 }
      let t := stepChecked i { cpu, events := [prior] }
      t.fault.isNone && t.cpu.ms.isNone && t.profile.isNone && t.events == [prior] &&
      sameCpu t.cpu (step i cpu)) = true := by decide

-- Undefined-result double shifts validate the final store after the read.
-- Denied stores preserve CPU/oracle state and the successful read prefix.
example : [DShiftKind.shld,.shrd].all (fun k => [17,31].all (fun count =>
    [false,true].all (fun deny =>
      let cpu := entry address initial
      let p : MemoryProfile := { readable := fun _ => !deny, writable := fun _ => false }
      let i : Instr := { op := .dshift k .w memory .rcx (.imm8 count), len := 3 }
      let t := stepChecked i { cpu, profile := some p, events := [prior] }
      if deny then t.fault == some (.read address 2) && t.cpu.ms.isNone && sameCpu t.cpu cpu &&
        t.events == [prior,.fault (.read address 2)]
      else t.cpu.ms.isNone && t.fault == some (.write address 2) && sameCpu t.cpu cpu &&
        t.events == [prior,.memory .read address [0x11,0x22] false,.fault (.write address 2)]))) = true := by decide

-- Invalid encodings/ASTs are refused before looking up capabilities.
example : ([.shift .shl .q (.imm 0) (.imm8 1), .rot .ror .q (.imm 0) (.imm8 1),
    .dshift .shld .b memory .rcx (.imm8 1), .dshift .shrd .q (.imm 0) .rcx (.imm8 1),
    .shiftx .shl .w .rax memory .rcx, .rorx .w .rax memory 1, .bzhi .w .rax memory .rcx,
    .andn .b .rax .rcx memory, .mulx .w .rax .rdx memory,
    .bitcnt .popcnt .b .rax memory, .bitcnt .blsi .w .rax memory,
    .imulr .b .rax memory none, .muldiv .div .q (.imm 0),
    .movbe .b (.reg .rax) memory, .movbe .q (.reg .rax) (.reg .rdx),
    .movbe .q memory memory] : List Op).all (fun op => [false,true].all (fun bound =>
      let cpu := entry address initial
      let p : MemoryProfile := { readable := fun _ => false, writable := fun _ => false }
      let t := stepChecked { op, len := 3 }
        { cpu, profile := if bound then some p else none, events := [prior] }
      (match t.cpu.ms with | some (.illegalOperands _) => true | _ => false) &&
      sameCpu { t.cpu with ms := none } cpu && t.fault.isNone && t.events == [prior])) = true := by decide

-- Independent quotient/remainder goldens, including AX byte pairing, source
-- permission priority, zero divisor, and signed/unsigned quotient overflow.
private def divide (sz : Size) (signed : Bool) (scene : Nat) (mem : Bool) (mode : Nat) : Bool :=
  let mask : Val := BitVec.ofNat 64 (2^sz.bits-1)
  let negative : Val := mask - 12
  let lo : Val := if scene == 0 then (if signed then negative else 13)
    else if scene == 2 && signed then BitVec.ofNat 64 (2^(sz.bits-1)) else 0
  let hi : Val := if scene == 0 && signed || scene == 2 && signed then mask
    else if scene == 2 then 1 else 0
  let divisor : Val := if scene == 1 then 0 else if scene == 2 then (if signed then mask else 1) else 3
  let cpu := ((entry address divisor).setMdPair sz lo hi).setReg .q .rcx divisor
  let src : Operand := if mem then memory else .reg .rcx
  let i : Instr := { op := .muldiv (if signed then .idiv else .div) sz src, len := 3 }
  let p : MemoryProfile :=
    { readable := fun a => !(mode == 1 && a == address + BitVec.ofNat 64 (sz.bytes-1)),
      writable := fun _ => false, initialized := fun _ => true }
  let t := stepChecked i { cpu, profile := if mode == 2 then none else some p, events := [prior] }
  let missing := mem && mode == 2
  let denied := mem && mode == 1
  let fault := if denied then some (ExecutionFault.read address sz.bytes)
    else if !missing && scene != 0 then some .divideError else none
  let events := [prior] ++ (if mem && !missing && !denied then
    [.memory .read address (bytes sz.bytes divisor) true] else []) ++
    (match fault with | none => [] | some f => [.fault f])
  t.fault == fault && t.events == events &&
  if missing then (match t.cpu.ms with | some (.unimplemented _) => true | _ => false) &&
    sameCpu { t.cpu with ms := none } cpu
  else t.cpu.ms.isNone && if fault.isSome then sameCpu t.cpu cpu
    else sameCpu t.cpu (step i cpu) &&
      t.cpu.getReg sz .rax == (if signed then mask-3 else 4) &&
      t.cpu.mdHi sz == (if signed then mask else 1)

example : [Size.b,.w,.d,.q].all (fun sz => [false,true].all (fun signed =>
    (List.range 3).all (fun scene => [false,true].all (fun mem =>
      (List.range 3).all (divide sz signed scene mem))))) = true := by decide

-- Multiplication shares the pair calculation too; it must not become a #DE.
example : [Size.b,.w,.d,.q].all (fun sz => [MulDivKind.mul,.imul].all (fun k =>
    let cpu := ((entry address 3).setMdPair sz 7 0)
    let p : MemoryProfile := { initialized := fun _ => true }
    let i : Instr := { op := .muldiv k sz memory, len := 3 }
    let t := stepChecked i { cpu, profile := some p, events := [prior] }
    t.cpu.ms.isNone && t.fault.isNone && sameCpu t.cpu (step i cpu) &&
    t.cpu.getReg sz .rax == 21 && t.cpu.mdHi sz == 0 &&
    t.events == [prior,.memory .read address (bytes sz.bytes 3) true])) = true := by decide


private def stackEntry (sp : Val := 0x2000) : Cpu :=
  let cpu := entry address initial
  { cpu with
    regs := cpu.regs.set .rsp sp,
    mem := ((cpu.mem.writeSize .q sp 0x6000).writeSize .q (sp-8) 0x7000).write (sp+16) 0x5a }

private structure StackCase where
  op : Op
  cpu : Cpu := stackEntry 0x2000
  size : Size := .q
  readAddress : Option Val := none
  writeAddress : Option Val := none
  readValue : Val := 0x6000
  writeValue : Val := input
  rsp : Val
  rax : Option Val := none
  rip : Val := 0x4003

private def checkStack (c : StackCase) (mode : Nat) : Bool :=
  let ra := c.readAddress.getD 0
  let wa := c.writeAddress.getD 0
  let p : MemoryProfile :=
    { readable := fun a => !((mode == 1 || mode == 2 || mode == 5) && a == ra + (if mode == 2 then BitVec.ofNat 64 (c.size.bytes-1) else 0)),
      writable := fun a => !((mode == 3 || mode == 4 || mode == 5) && a == wa + (if mode == 4 then BitVec.ofNat 64 (c.size.bytes-1) else 0)),
      initialized := fun a => mode != 7 && (mode != 8 || a == ra) }
  let i : Instr := { op := c.op, len := 3 }
  let t := stepChecked i { cpu := c.cpu, profile := if mode == 6 then none else some p, events := [prior] }
  let deniedRead := c.readAddress.isSome && (mode == 1 || mode == 2 || mode == 5)
  let deniedWrite := c.writeAddress.isSome && (mode == 3 || mode == 4 || mode == 5)
  let fault := if mode == 6 then none else if deniedRead then some (ExecutionFault.read ra c.size.bytes)
    else if deniedWrite then some (.write wa c.size.bytes) else none
  let success := mode != 6 && fault.isNone
  let readEvents := if mode != 6 && c.readAddress.isSome && !deniedRead then
    [MemoryAccessEvent.memory .read ra (bytes c.size.bytes c.readValue) (mode != 7 && mode != 8)] else []
  let tail := match fault with
    | some f => [MemoryAccessEvent.fault f]
    | none => if success && c.writeAddress.isSome then [.memory .write wa (bytes c.size.bytes c.writeValue) true] else []
  t.fault == fault && t.events == [prior] ++ readEvents ++ tail &&
  if mode == 6 then t.cpu.ms.isSome && sameCpu { t.cpu with ms := none } c.cpu && t.profile.isNone
  else t.cpu.ms.isNone && sameCpu t.cpu (if success then step i c.cpu else c.cpu) &&
    (if success then t.cpu.regs.rsp == c.rsp && t.cpu.rip == c.rip &&
      (match c.rax with | none => true | some value => t.cpu.regs.rax == value) else true) &&
    (if c.writeAddress.isSome then (List.range (c.size.bytes+2)).all (fun n =>
      let a := wa-1+BitVec.ofNat 64 n
      t.cpu.mem.read a == (if success && 1 <= n && n <= c.size.bytes then
        (c.writeValue >>> (8*(n-1))).setWidth 8 else c.cpu.mem.read a) &&
      (match t.profile with | none => false | some after => after.readable a == p.readable a && after.writable a == p.writable a && after.initialized a == (if success && 1 <= n && n <= c.size.bytes then true else p.initialized a))) else true)

private def stackCases : List StackCase := [
  { op := .push .q (.reg .rax), writeAddress := some 0x1ff8, rsp := 0x1ff8 },
  { op := .push .w (.reg .rax), size := .w, writeAddress := some 0x1ffe, rsp := 0x1ffe },
  { op := .push .q (.imm 0x8899), writeAddress := some 0x1ff8, writeValue := 0x8899, rsp := 0x1ff8 },
  { op := .push .q (.reg .rsp), writeAddress := some 0x1ff8, writeValue := 0x2000, rsp := 0x1ff8 },
  { op := .push .q (.mem { base := some .rsp }), readAddress := some 0x2000, writeAddress := some 0x1ff8, writeValue := 0x6000, rsp := 0x1ff8 },
  { op := .push .q (.mem { base := some .rsp, disp := -8 }), readAddress := some 0x1ff8, readValue := 0x7000, writeAddress := some 0x1ff8, writeValue := 0x7000, rsp := 0x1ff8 },
  { op := .pop .q (.reg .rax), readAddress := some 0x2000, rsp := 0x2008, rax := some 0x6000 },
  { op := .pop .w (.reg .rax), size := .w, readAddress := some 0x2000, rsp := 0x2002, rax := some 0x1122334455666000 },
  { op := .pop .q (.reg .rsp), readAddress := some 0x2000, rsp := 0x6000 },
  { op := .pop .w (.reg .rsp), size := .w, readAddress := some 0x2000, rsp := 0x6000 },
  { op := .pop .w (.reg .rsp), cpu := stackEntry 0xffff, size := .w, readAddress := some 0xffff, rsp := 0x16000 },
  { op := .pop .w (.reg .rsp), cpu := stackEntry 0xffff800000002000, size := .w, readAddress := some 0xffff800000002000, rsp := 0xffff800000006000 },
  { op := .pop .q (.mem { base := some .rsp }), readAddress := some 0x2000, writeAddress := some 0x2008, writeValue := 0x6000, rsp := 0x2008 },
  { op := .pop .w (.mem { base := some .rsp }), size := .w, readAddress := some 0x2000, writeAddress := some 0x2002, writeValue := 0x6000, rsp := 0x2002 },
  { op := .pop .q (.mem { base := some .rsp, disp := -8 }), readAddress := some 0x2000, writeAddress := some 0x2000, writeValue := 0x6000, rsp := 0x2008 },
  { op := .call (.rel 0x1ffd), writeAddress := some 0x1ff8, writeValue := 0x4003, rsp := 0x1ff8, rip := 0x6000 },
  { op := .call (.indirect (.reg .rsp)), writeAddress := some 0x1ff8, writeValue := 0x4003, rsp := 0x1ff8, rip := 0x2000 },
  { op := .call (.indirect (.mem { base := some .rsp })), readAddress := some 0x2000, writeAddress := some 0x1ff8, writeValue := 0x4003, rsp := 0x1ff8, rip := 0x6000 },
  { op := .call (.indirect (.mem { base := some .rsp, disp := -8 })), readAddress := some 0x1ff8, readValue := 0x7000, writeAddress := some 0x1ff8, writeValue := 0x4003, rsp := 0x1ff8, rip := 0x7000 },
  { op := .ret, readAddress := some 0x2000, rsp := 0x2008, rip := 0x6000 }
]
example : (stackCases.take 10).all (fun c => (List.range 9).all (checkStack c)) = true := by decide
example : (stackCases.drop 10).all (fun c => (List.range 9).all (checkStack c)) = true := by decide

private def targets : List (Val × Bool × Bool) := [
  (0,true,true), (0x00007fffffffffff,true,true), (0x0000800000000000,false,true),
  (0x00ffffffffffffff,false,true), (0x0100000000000000,false,false),
  (0xff00000000000000,false,true), (0xffff800000000000,true,true), (0xffffffffffffffff,true,true)
]

private def checkControl (kind : Nat) : Bool := targets.all (fun (target,lo,hi) =>
  [(LinearAddressWidth.la48,lo),(.la57,hi)].all (fun (width,valid) =>
    [false,true].all (fun taken => (List.range 4).all (fun mode =>
      let cpu := stackEntry 0x2000
      let cpu :=
        { cpu with
          regs := ((cpu.regs.set .rdx target).set .rcx (if kind == 8 then (if taken then 0 else 1) else if taken then 2 else 1)),
          flags := { cpu.flags with zf := taken },
          mem := (cpu.mem.writeSize .q address target).writeSize .q 0x2000 target }
      let op := match kind with
        | 0 => Op.jmp (.rel (target-0x4003))
        | 1 => .jmp (.indirect (.reg .rdx))
        | 2 => .jmp (.indirect memory)
        | 3 => .call (.rel (target-0x4003))
        | 4 => .call (.indirect (.reg .rdx))
        | 5 => .call (.indirect memory)
        | 6 => .ret
        | 7 => .jcc .e (target-0x4003)
        | 8 => .jcxz false (target-0x4003)
        | _ => .loop .loop false (target-0x4003)
      let read := kind == 2 || kind == 5 || kind == 6
      let store := kind == 3 || kind == 4 || kind == 5
      let ra : Val := if kind == 6 then 0x2000 else address
      let p : MemoryProfile := { readable := fun _ => mode != 1, writable := fun _ => mode != 2 }
      let i : Instr := { op, len := 3 }
      let t := stepChecked i { cpu, addressWidth := width, profile := if mode == 3 then none else some p, events := [prior] }
      let readMissing := read && mode == 3
      let readDenied := read && mode == 1
      let badTarget := !readMissing && !readDenied && (kind < 7 || taken) && !valid
      let storeMissing := !readMissing && !readDenied && !badTarget && store && mode == 3
      let storeDenied := !readMissing && !readDenied && !badTarget && store && mode == 2
      let modelRefusal := readMissing || storeMissing
      let fault := if readDenied then some (ExecutionFault.read ra 8)
        else if badTarget then some (.nonCanonical target)
        else if storeDenied then some (.write 0x1ff8 8) else none
      let success := !modelRefusal && fault.isNone
      let events := [prior] ++ (if read && !readMissing && !readDenied then
          [.memory .read ra (bytes 8 target) false] else []) ++
        (match fault with | some f => [.fault f] | none => if success && store then [.memory .write 0x1ff8 (bytes 8 0x4003) true] else [])
      t.events == events && t.fault == fault &&
      if modelRefusal then t.cpu.ms.isSome && sameCpu { t.cpu with ms := none } cpu
      else t.cpu.ms.isNone && sameCpu t.cpu (if success then step i cpu width else cpu) &&
        (if success then t.cpu.rip == (if kind < 7 || taken then target else 0x4003) &&
          t.cpu.regs.rsp == (if store then 0x1ff8 else if kind == 6 then 0x2008 else 0x2000) else true)))))

example : checkControl 0 = true := by decide
example : checkControl 1 = true := by decide
example : checkControl 2 = true := by decide
example : checkControl 3 = true := by decide
example : checkControl 4 = true := by decide
example : checkControl 5 = true := by decide
example : checkControl 6 = true := by decide
example : checkControl 7 = true := by decide
example : checkControl 8 = true := by decide
example : checkControl 9 = true := by decide

-- LOOP's fault boundary must not commit its speculative counter decrement.
-- On success the 32-bit count write zero-extends, including not-taken branches.
private def checkLoop (kind : LoopKind) : Bool := [false,true].all (fun addr32 =>
  [false,true].all (fun zf => ([0,1,2,0x100000000,0x100000001] : List Val).all (fun count =>
    [false,true].all (fun bad =>
      let base := stackEntry 0x2000
      let cpu := { base with regs := base.regs.set .rcx count, flags := { zf } }
      let after : Val := if addr32 then (count-1) % 0x100000000 else count-1
      let taken : Bool := after != 0 && (match kind with | .loop => true | .loope => zf | .loopne => !zf)
      let target : Val := if bad then 0x0100000000000000 else 0x7000
      let i : Instr := { op := .loop kind addr32 (target-0x4003), len := 3 }
      let t := stepChecked i { cpu, events := [prior] }
      let fault := if taken && bad then some (ExecutionFault.nonCanonical target) else none
      t.fault == fault && t.cpu.ms.isNone &&
      sameCpu t.cpu (if fault.isNone then step i cpu else cpu) &&
      t.events == [prior] ++ (match fault with | none => [] | some f => [.fault f]) &&
      (if fault.isNone then t.cpu.regs.rcx == after else t.cpu.regs.rcx == count)))))
example : checkLoop .loop = true := by decide
example : checkLoop .loope = true := by decide
example : checkLoop .loopne = true := by decide

-- ECX zero with nonzero RCX is the address-size distinction for JECXZ.
example : [false,true].all (fun addr32 =>
    ([0,1,0x100000000,0x100000001] : List Val).all (fun count => [false,true].all (fun bad =>
      let base := stackEntry 0x2000
      let cpu := { base with regs := base.regs.set .rcx count }
      let take := (if addr32 then count % 0x100000000 else count) == 0
      let target : Val := if bad then 0x0100000000000000 else 0x7000
      let i : Instr := { op := .jcxz addr32 (target-0x4003), len := 3 }
      let t := stepChecked i { cpu, events := [prior] }
      let fault := if take && bad then some (ExecutionFault.nonCanonical target) else none
      t.fault == fault && t.cpu.ms.isNone && t.cpu.regs.rcx == count &&
      sameCpu t.cpu (if fault.isNone then step i cpu else cpu) &&
      t.events == [prior] ++ (match fault with | none => [] | some f => [.fault f])))) = true := by decide

private def stackBounds : List (Val × Bool × Bool × Bool × Bool) := [
  (0,true,true,true,true), (0x7ffffffffff8,true,true,true,true),
  (0x7fffffffffff,true,false,true,true), (0x800000000000,true,false,true,true),
  (0x800000000008,false,false,true,true), (0x00ffffffffffffff,false,false,true,false),
  (0x0100000000000000,false,false,true,false), (0xffff800000000000,false,true,true,true),
  (0xffffffffffffffff,true,true,true,true)
]
example : stackBounds.all (fun (sp,p48,r48,p57,r57) =>
    [(LinearAddressWidth.la48,p48,r48),(.la57,p57,r57)].all (fun (width,pushValid,popValid) =>
      [false,true].all (fun push => [false,true].all (fun deny =>
        let cpu := stackEntry sp
        let base := if push then sp-8 else sp
        let valid := if push then pushValid else popValid
        let p : MemoryProfile := { readable := fun _ => !deny, writable := fun _ => !deny }
        let i : Instr := { op := if push then .push .q (.reg .rax) else .pop .q (.reg .rax), len := 3 }
        let t := stepChecked i { cpu, addressWidth := width, profile := some p, events := [prior] }
        let fault := if !valid then some (ExecutionFault.nonCanonical base)
          else if deny then some (if push then .write base 8 else .read base 8) else none
        t.fault == fault && t.cpu.ms.isNone && sameCpu t.cpu (if fault.isNone then step i cpu width else cpu) &&
        t.events == [prior] ++ (match fault with | some f => [.fault f] | none => [.memory (if push then .write else .read) base (bytes 8 (if push then input else 0x6000)) push]))))) = true := by decide

example : ([Op.push .b (.reg .rax), .push .d (.reg .rax), .pop .b (.reg .rax),
    .pop .d (.reg .rax), .pop .q (.imm 0), .pop .w (.imm 0),
    .jmp (.indirect (.imm 0)), .call (.indirect (.imm 0))] : List Op).all (fun op =>
      [false,true].all (fun bound =>
        let cpu := stackEntry 0x2000
        let p : MemoryProfile := { readable := fun _ => false, writable := fun _ => false }
        let t := stepChecked { op, len := 3 } { cpu, profile := if bound then some p else none, events := [prior] }
        (match t.cpu.ms with | some (.illegalOperands _) => true | _ => false) &&
        sameCpu { t.cpu with ms := none } cpu && t.fault.isNone && t.events == [prior])) = true := by decide

example : [false,true].all (fun denyReturn =>
    let cpu := stackEntry 0x2000
    let p : MemoryProfile := {}
    let call : Instr := { op := .call (.rel 0x1ffd), len := 3 }
    let ret : Instr := { op := .ret, len := 1 }
    let s := stepChecked call { cpu, profile := some p, events := [prior] }
    let s := { s with profile := s.profile.map (fun p => { p with readable := fun _ => !denyReturn }) }
    let t := runChecked [ret,{ op := .nop none, len := 1 }] s
    let fault := if denyReturn then some (ExecutionFault.read 0x1ff8 8) else none
    t.fault == fault && t.cpu.ms.isNone &&
    sameCpu t.cpu (if denyReturn then step call cpu else step { op := .nop none, len := 1 } (step ret (step call cpu))) &&
    t.cpu.regs.rsp == (if denyReturn then 0x1ff8 else 0x2000) &&
    t.cpu.rip == (if denyReturn then 0x6000 else 0x4004) &&
    t.events == [prior,.memory .write 0x1ff8 (bytes 8 0x4003) true] ++
      (if denyReturn then [.fault (.read 0x1ff8 8)] else [.memory .read 0x1ff8 (bytes 8 0x4003) true])) = true := by decide


-- Register bit indices use the fork's actual selected-byte access, including
-- signed offsets. Literal address/result rows keep this separate from planning.
private def bitRows : List (Val × Int × Bool × Val × Val × Val) := [
  (0,0,true,0x81,0x80,0x80), (1,0,false,0x83,0x81,0x83),
  (7,0,true,0x81,1,1), (8,1,true,0x81,0x80,0x80),
  (-1,-1,true,0x81,1,1), (-8,-1,true,0x81,0x80,0x80), (-9,-2,true,0x81,1,1)
]
private def checkBit (sz : Size) : Bool := bitRows.all (fun (index,delta,cf,set,clear,flip) =>
  [BitKind.bt,.bts,.btr,.btc].all (fun k => (List.range 8).all (fun mode =>
    let base := address + BitVec.ofInt 64 delta
    let cpu := entry base 0x81
    let cpu := { cpu with regs := cpu.regs.set .rcx index }
    let i : Instr := { op := .bit k sz memory (.reg .rcx), len := 3 }
    let p := profile { op := i.op, base, readBytes := 1, writeBytes := if k == .bt then 0 else 1 } mode
    let t := stepChecked i { cpu, profile := some p, events := [prior] }
    let readDenied := mode == 1 || mode == 2 || mode == 5
    let writeDenied := k != .bt && (mode == 3 || mode == 4 || mode == 5)
    let fault := if readDenied then some (ExecutionFault.read base 1)
      else if writeDenied then some (.write base 1) else none
    let value : Val := match k with | .bt => 0x81 | .bts => set | .btr => clear | .btc => flip
    let events := [prior] ++ (if readDenied then [] else [.memory .read base [0x81] (mode != 6)]) ++
      (match fault with | some f => [.fault f] | none => if k == .bt then [] else [.memory .write base [value.setWidth 8] true])
    t.fault == fault && t.events == events && t.cpu.ms.isNone &&
    sameCpu t.cpu (if fault.isNone then step i cpu else cpu) &&
    (if fault.isNone then t.cpu.flags.cf == cf && t.cpu.flags.zf && t.cpu.oracle.cursor == 7 &&
      t.cpu.mem.read base == value.setWidth 8 else true) &&
    (match t.profile with | none => false | some after => after.initialized base == (if fault.isNone && k != .bt then true else p.initialized base)))))
example : checkBit .w = true := by decide
example : checkBit .d = true := by decide
example : checkBit .q = true := by decide

private def bitImmediateCases : List Case := [
  { op := .bit .bt .w memory (.imm 0), readBytes := 2, writeBytes := 0, stored := 0x8877665544332211 },
  { op := .bit .bts .w memory (.imm 0), readBytes := 2, writeBytes := 2, stored := 0x8877665544332211 },
  { op := .bit .btr .w memory (.imm 0), readBytes := 2, writeBytes := 2, stored := 0x8877665544332210 },
  { op := .bit .btc .w memory (.imm 0), readBytes := 2, writeBytes := 2, stored := 0x8877665544332210 },
  { op := .bit .bt .w memory (.imm 1), readBytes := 2, writeBytes := 0, stored := 0x8877665544332211 },
  { op := .bit .bts .w memory (.imm 1), readBytes := 2, writeBytes := 2, stored := 0x8877665544332213 },
  { op := .bit .btr .w memory (.imm 1), readBytes := 2, writeBytes := 2, stored := 0x8877665544332211 },
  { op := .bit .btc .w memory (.imm 1), readBytes := 2, writeBytes := 2, stored := 0x8877665544332213 },
  { op := .bit .bt .w memory (.imm 15), readBytes := 2, writeBytes := 0, stored := 0x8877665544332211 },
  { op := .bit .bts .w memory (.imm 15), readBytes := 2, writeBytes := 2, stored := 0x887766554433a211 },
  { op := .bit .btr .w memory (.imm 15), readBytes := 2, writeBytes := 2, stored := 0x8877665544332211 },
  { op := .bit .btc .w memory (.imm 15), readBytes := 2, writeBytes := 2, stored := 0x887766554433a211 },
  { op := .bit .bt .d memory (.imm 0), readBytes := 4, writeBytes := 0, stored := 0x8877665544332211 },
  { op := .bit .bts .d memory (.imm 0), readBytes := 4, writeBytes := 4, stored := 0x8877665544332211 },
  { op := .bit .btr .d memory (.imm 0), readBytes := 4, writeBytes := 4, stored := 0x8877665544332210 },
  { op := .bit .btc .d memory (.imm 0), readBytes := 4, writeBytes := 4, stored := 0x8877665544332210 },
  { op := .bit .bt .d memory (.imm 1), readBytes := 4, writeBytes := 0, stored := 0x8877665544332211 },
  { op := .bit .bts .d memory (.imm 1), readBytes := 4, writeBytes := 4, stored := 0x8877665544332213 },
  { op := .bit .btr .d memory (.imm 1), readBytes := 4, writeBytes := 4, stored := 0x8877665544332211 },
  { op := .bit .btc .d memory (.imm 1), readBytes := 4, writeBytes := 4, stored := 0x8877665544332213 },
  { op := .bit .bt .d memory (.imm 31), readBytes := 4, writeBytes := 0, stored := 0x8877665544332211 },
  { op := .bit .bts .d memory (.imm 31), readBytes := 4, writeBytes := 4, stored := 0x88776655c4332211 },
  { op := .bit .btr .d memory (.imm 31), readBytes := 4, writeBytes := 4, stored := 0x8877665544332211 },
  { op := .bit .btc .d memory (.imm 31), readBytes := 4, writeBytes := 4, stored := 0x88776655c4332211 },
  { op := .bit .bt .q memory (.imm 0), readBytes := 8, writeBytes := 0, stored := 0x8877665544332211 },
  { op := .bit .bts .q memory (.imm 0), readBytes := 8, writeBytes := 8, stored := 0x8877665544332211 },
  { op := .bit .btr .q memory (.imm 0), readBytes := 8, writeBytes := 8, stored := 0x8877665544332210 },
  { op := .bit .btc .q memory (.imm 0), readBytes := 8, writeBytes := 8, stored := 0x8877665544332210 },
  { op := .bit .bt .q memory (.imm 1), readBytes := 8, writeBytes := 0, stored := 0x8877665544332211 },
  { op := .bit .bts .q memory (.imm 1), readBytes := 8, writeBytes := 8, stored := 0x8877665544332213 },
  { op := .bit .btr .q memory (.imm 1), readBytes := 8, writeBytes := 8, stored := 0x8877665544332211 },
  { op := .bit .btc .q memory (.imm 1), readBytes := 8, writeBytes := 8, stored := 0x8877665544332213 },
  { op := .bit .bt .q memory (.imm 63), readBytes := 8, writeBytes := 0, stored := 0x8877665544332211 },
  { op := .bit .bts .q memory (.imm 63), readBytes := 8, writeBytes := 8, stored := 0x8877665544332211 },
  { op := .bit .btr .q memory (.imm 63), readBytes := 8, writeBytes := 8, stored := 0x877665544332211 },
  { op := .bit .btc .q memory (.imm 63), readBytes := 8, writeBytes := 8, stored := 0x877665544332211 }
]
example : (bitImmediateCases.take 18).all (fun c => (List.range 8).all (check c)) = true := by decide
example : (bitImmediateCases.drop 18).all (fun c => (List.range 8).all (check c)) = true := by decide

private def vector : BitVec 128 := 0x8877665544332211ffeeddccbbaa9988
private def xmmInput : BitVec 128 := 0x112233445566778899aabbccddeeff00
private def vbytes (n : Nat) (v : BitVec 128) : List (BitVec 8) :=
  (List.range n).map (fun i => (v >>> (8*i)).setWidth 8)
private def vectorEntry (a : Val) : Cpu :=
  let cpu := (entry a 0).setYmm .x0 xmmInput 0xdecafbad
  { cpu with
    regs := cpu.regs.set .rbx a,
    mem := ((((Mem.empty.writeN a 0xffeeddccbbaa9988 8).writeN (a+8) 0x8877665544332211 8).write (a-1) 0xa5).write (a+16) 0x5a) }

private def checkVector (op : Op) (a : Val) (n : Nat) (store aligned : Bool)
    (gold : BitVec 128) (mode : Nat) : Bool :=
  let cpu := vectorEntry a
  let p : MemoryProfile :=
    { readable := fun b => !((mode == 1 || mode == 2 || mode == 5) && b == (if mode == 2 then a+BitVec.ofNat 64 (n-1) else a)),
      writable := fun b => !((mode == 3 || mode == 4 || mode == 5) && b == (if mode == 4 then a+BitVec.ofNat 64 (n-1) else a)),
      initialized := fun b => mode != 6 && (mode != 7 || b == a) }
  let i : Instr := { op, len := 3 }
  let t := stepChecked i { cpu, profile := some p, events := [prior] }
  let denied := if store then mode == 3 || mode == 4 || mode == 5 else mode == 1 || mode == 2 || mode == 5
  let fault := if aligned && a.toNat % 16 != 0 then some (ExecutionFault.misaligned a 16)
    else if denied then some (if store then .write a n else .read a n) else none
  let payload := if store then gold else vector
  t.fault == fault && t.cpu.ms.isNone && sameCpu t.cpu (if fault.isNone then step i cpu else cpu) &&
  t.events == [prior] ++ (match fault with | some f => [.fault f] | none => [.memory (if store then .write else .read) a (vbytes n payload) (store || mode != 6 && mode != 7)]) &&
  t.cpu.getYmmHi .x0 == 0xdecafbad &&
  (if fault.isNone && !store then t.cpu.getXmm .x0 == gold else t.cpu.getXmm .x0 == xmmInput) &&
  (List.range 18).all (fun offset =>
    let b := a-1+BitVec.ofNat 64 offset
    let written := fault.isNone && store && 1 <= offset && offset <= n
    t.cpu.mem.read b == (if written then (gold >>> (8*(offset-1))).setWidth 8 else cpu.mem.read b) &&
    (match t.profile with | none => false | some after => after.readable b == p.readable b && after.writable b == p.writable b && after.initialized b == (if written then true else p.initialized b)))

private def checkPacked (kind : VMovKind) (aligned : Bool) : Bool :=
  [address,address+1].all (fun a => [false,true].all (fun store => (List.range 8).all (fun mode =>
    checkVector (if store then .vstore kind { base := some .rbx } .x0 else .vload kind .x0 { base := some .rbx })
      a 16 store aligned (if store then xmmInput else vector) mode)))
example : checkPacked .dqa true = true := by decide
example : checkPacked .dqu false = true := by decide
example : checkPacked .aps true = true := by decide
example : checkPacked .ups false = true := by decide
example : checkPacked .apd true = true := by decide
example : checkPacked .upd false = true := by decide

private def checkHalf (kind : VQuadKind) : Bool := [address,address+1].all (fun a =>
  [VHalf.lo,.hi].all (fun half => [false,true].all (fun store => (List.range 8).all (fun mode =>
    checkVector (if store then .vstoreq half kind { base := some .rbx } .x0 else .vloadq half kind .x0 { base := some .rbx })
      a 8 store false (if store then (if half = .lo then 0x99aabbccddeeff00 else 0x1122334455667788)
        else if half = .lo then 0x1122334455667788ffeeddccbbaa9988 else 0xffeeddccbbaa998899aabbccddeeff00) mode))))
example : checkHalf .ps = true := by decide
example : checkHalf .pd = true := by decide

private def checkVectorScalar (sz : Size) : Bool := [address,address+1].all (fun a =>
  [false,true].all (fun g => [false,true].all (fun store => (List.range 8).all (fun mode =>
    let ea : Ea := { base := some .rbx }
    let op := if store then (if g then Op.vmovgst sz ea .x0 else .vmovsst sz ea .x0)
      else if g then .vmovgld sz .x0 ea else .vmovsld sz .x0 ea
    checkVector op a sz.bytes store false (if store then xmmInput else if sz == .d then 0xbbaa9988 else 0xffeeddccbbaa9988) mode))))
example : checkVectorScalar .d = true := by decide
example : checkVectorScalar .q = true := by decide

example : ([(0x7ffffffffff0,true,true),(0x7ffffffffff8,false,true),
    (0x00fffffffffffff0,false,true),(0x00fffffffffffff8,false,false),
    (0xff00000000000000,false,true),(0xfffffffffffffff0,true,true),
    (0xfffffffffffffff8,true,true)] : List (Val × Bool × Bool)).all (fun (a,lo,hi) =>
      [(LinearAddressWidth.la48,lo),(.la57,hi)].all (fun (width,valid) =>
        [false,true].all (fun store => [false,true].all (fun deny =>
          let cpu := vectorEntry a
          let p : MemoryProfile := { readable := fun _ => !deny, writable := fun _ => !deny }
          let i : Instr := { op := if store then .vstore .dqu { base := some .rbx } .x0 else .vload .dqu .x0 { base := some .rbx }, len := 3 }
          let t := stepChecked i { cpu, addressWidth := width, profile := some p, events := [prior] }
          let fault := if !valid then some (ExecutionFault.nonCanonical a)
            else if deny then some (if store then .write a 16 else .read a 16) else none
          t.fault == fault && t.cpu.ms.isNone && sameCpu t.cpu (if fault.isNone then step i cpu width else cpu) &&
          t.events == [prior] ++ (match fault with | some f => [.fault f] | none => [.memory (if store then .write else .read) a (vbytes 16 (if store then xmmInput else vector)) store]))))) = true := by decide

-- MOVS exposes one real iteration. Completed earlier iterations remain committed.
private def checkMovs (sz : Size) : Bool := [false,true].all (fun repeated =>
  [false,true].all (fun backward => ([0,1,2] : List Val).all (fun count => (List.range 9).all (fun mode =>
    let base := entry address initial
    let cpu := { base with regs := ((base.regs.set .rsi address).set .rdi 0x2000).set .rcx count, flags := { base.flags with df := backward } }
    let p : MemoryProfile :=
      { readable := fun a => !((mode == 1 || mode == 2 || mode == 5) && a == (if mode == 2 then address+BitVec.ofNat 64 (sz.bytes-1) else address)),
        writable := fun a => !((mode == 3 || mode == 4 || mode == 5) && a == (if mode == 4 then 0x2000+BitVec.ofNat 64 (sz.bytes-1) else 0x2000)),
        initialized := fun a => mode != 6 && (mode != 7 || a == address) }
    let i : Instr := { op := if repeated then .repstrop .rep .movs sz else .strop .movs sz, len := 3 }
    let t := stepChecked i { cpu, profile := if mode == 8 then none else some p, events := [prior] }
    let access := !repeated || count != 0
    let missing := access && mode == 8
    let deniedRead := access && (mode == 1 || mode == 2 || mode == 5)
    let deniedWrite := access && (mode == 3 || mode == 4 || mode == 5)
    let fault := if missing then none else if deniedRead then some (ExecutionFault.read address sz.bytes)
      else if deniedWrite then some (.write 0x2000 sz.bytes) else none
    let success := !missing && fault.isNone
    let delta : Val := if backward then 0-BitVec.ofNat 64 sz.bytes else BitVec.ofNat 64 sz.bytes
    let events := [prior] ++ (if access && !missing && !deniedRead then
        [.memory .read address (bytes sz.bytes initial) (mode != 6 && (mode != 7 || sz == .b))] else []) ++
      (match fault with | some f => [.fault f] | none => if success && access then [.memory .write 0x2000 (bytes sz.bytes initial) true] else [])
    t.fault == fault && t.events == events &&
    if missing then t.cpu.ms.isSome && sameCpu { t.cpu with ms := none } cpu
    else t.cpu.ms.isNone && sameCpu t.cpu (if success then step i cpu else cpu) &&
      t.cpu.regs.rsi == (if success && access then address+delta else address) &&
      t.cpu.regs.rdi == (if success && access then 0x2000+delta else 0x2000) &&
      t.cpu.regs.rcx == (if success && repeated && access then count-1 else count) &&
      t.cpu.rip == (if success then (if repeated && access then 0x4000 else 0x4003) else 0x4000) &&
      (List.range 10).all (fun n =>
        let a := 0x1fff+BitVec.ofNat 64 n
        let written := success && access && 1 <= n && n <= sz.bytes
        t.cpu.mem.read a == (if written then (initial >>> (8*(n-1))).setWidth 8 else cpu.mem.read a) &&
        (match t.profile with | none => mode == 8 | some after => after.initialized a == (if written then true else p.initialized a)))))))
example : checkMovs .b = true := by decide
example : checkMovs .w = true := by decide
example : checkMovs .d = true := by decide
example : checkMovs .q = true := by decide

private def checkMovsSequence (sz : Size) : Bool := [false,true].all (fun backward =>
  (List.range 3).all (fun scene =>
    let delta : Val := if backward then 0-BitVec.ofNat 64 sz.bytes else BitVec.ofNat 64 sz.bytes
    let si : Val := address+delta
    let di : Val := 0x2000+delta
    let base := entry address 0
    let cpu := { base with
      regs := ((base.regs.set .rsi address).set .rdi 0x2000).set .rcx 2,
      flags := { base.flags with df := backward },
      mem := (Mem.empty.writeSize sz address 1).writeSize sz si 2 }
    let p : MemoryProfile := { readable := fun a => !(scene == 1 && a == si), writable := fun a => !(scene == 2 && a == di) }
    let i : Instr := { op := .repstrop .rep .movs sz, len := 3 }
    let t := runChecked [i,i,i] { cpu, profile := some p, events := [prior] }
    let fault := if scene == 1 then some (ExecutionFault.read si sz.bytes) else if scene == 2 then some (.write di sz.bytes) else none
    let second := (if scene == 1 then [] else [.memory .read si (bytes sz.bytes 2) false]) ++
      (match fault with | some f => [.fault f] | none => [.memory .write di (bytes sz.bytes 2) true])
    t.fault == fault && t.cpu.ms.isNone && sameCpu t.cpu (if scene == 0 then run [i,i,i] cpu else step i cpu) &&
    t.cpu.regs.rcx == (if scene == 0 then 0 else 1) && t.cpu.rip == (if scene == 0 then 0x4003 else 0x4000) &&
    t.cpu.mem.readSize sz 0x2000 == 1 && t.cpu.mem.readSize sz di == (if scene == 0 then 2 else 0) &&
    t.events == [prior,.memory .read address (bytes sz.bytes 1) false,.memory .write 0x2000 (bytes sz.bytes 1) true] ++ second))
example : checkMovsSequence .b = true := by decide
example : checkMovsSequence .w = true := by decide
example : checkMovsSequence .d = true := by decide
example : checkMovsSequence .q = true := by decide

example : [false,true].all (fun backward =>
    let base := entry address 0
    let cpu := { base with
      regs := ((base.regs.set .rsi (if backward then 0x1002 else address)).set .rdi 0x1001).set .rcx 2,
      flags := { base.flags with df := backward }, mem := Mem.empty.writeSize .d address 0x04030201 }
    let p : MemoryProfile := {}
    let i : Instr := { op := .repstrop .rep .movs .b, len := 3 }
    let t := runChecked [i,i,i] { cpu, profile := some p, events := [prior] }
    let first : Val := if backward then 0x1002 else address
    let last : Val := if backward then address else 0x1002
    let value : BitVec 8 := if backward then 3 else 1
    t.fault.isNone && t.cpu.ms.isNone && sameCpu t.cpu (run [i,i,i] cpu) &&
    t.cpu.mem.readSize .d address == (if backward then 0x04030303 else 0x04010101) &&
    t.events == [prior,.memory .read first [value] false,.memory .write 0x1001 [value] true,
      .memory .read 0x1001 [value] true,.memory .write last [value] true]) = true := by decide

example : ([Op.bit .bt .q (.reg .rax) (.imm 1), .vmov .dqa .x0 .x15,
    .vmovs .d .x0 .x15, .vmovs .q .x0 .x15] : List Op).all (fun op =>
      let cpu := vectorEntry address
      let i : Instr := { op, len := 3 }
      let t := stepChecked i { cpu, events := [prior] }
      t.fault.isNone && t.cpu.ms.isNone && t.profile.isNone && t.events == [prior] && sameCpu t.cpu (step i cpu)) = true := by decide

example : ([Op.bit .bt .b memory (.imm 0), .bit .bt .q (.imm 0) (.imm 0), .bit .bt .q memory memory,
    .vmovsld .b .x0 { base := some .rbx }, .vmovsst .w { base := some .rbx } .x0,
    .vmovs .w .x0 .x15] : List Op).all (fun op =>
      let cpu := vectorEntry address
      let t := stepChecked { op, len := 3 } { cpu, events := [prior] }
      (match t.cpu.ms with | some (.illegalOperands _) => true | _ => false) &&
      t.fault.isNone && t.events == [prior] && sameCpu { t.cpu with ms := none } cpu) = true := by decide

example : ([Op.vload .dqu .x0 { base := some .rbx }, .vstore .dqa { base := some .rbx } .x0,
    .vloadq .lo .ps .x0 { base := some .rbx }, .vmovsld .q .x0 { base := some .rbx }] : List Op).all (fun op =>
      let cpu := vectorEntry address
      let t := stepChecked { op, len := 3 } { cpu, events := [prior] }
      t.cpu.ms.isSome && t.fault.isNone && t.events == [prior] && sameCpu { t.cpu with ms := none } cpu) = true := by decide


-- Successful atomic transfers are one old/new observation. A denied store
-- keeps its successful read prefix and commits no CPU/memory/ghost update.
private def checkRmw (op : Op) (cpu : Cpu) (a : Val) (n : Nat) (old new : Val)
    (rax : Option Val) (mode : Nat) : Bool :=
  let p := profile { op, base := a, readBytes := n, writeBytes := n } mode
  let i : Instr := { op, len := 3 }
  let t := stepChecked i { cpu, profile := some p, events := [prior] }
  let readDenied := mode == 1 || mode == 2 || mode == 5
  let writeDenied := mode == 3 || mode == 4 || mode == 5
  let fault := if readDenied then some (ExecutionFault.read a n)
    else if writeDenied then some (.write a n) else none
  let initialized := mode != 6 && (mode != 7 || n == 1)
  let events := [prior] ++ (match fault with
    | none => [.rmw a (bytes n old) (bytes n new) initialized]
    | some f => (if readDenied then [] else [.memory .read a (bytes n old) initialized]) ++ [.fault f])
  t.fault == fault && t.cpu.ms.isNone && t.events == events &&
  sameCpu t.cpu (if fault.isNone then step i cpu else cpu) &&
  (if fault.isNone then match rax with | none => true | some value => t.cpu.regs.rax == value else true) &&
  (List.range (n+2)).all (fun offset =>
    let b := a-1+BitVec.ofNat 64 offset
    let written := fault.isNone && 1 <= offset && offset <= n
    t.cpu.mem.read b == (if written then (new >>> (8*(offset-1))).setWidth 8 else cpu.mem.read b) &&
    (match t.profile with | none => false | some after => after.readable b == p.readable b && after.writable b == p.writable b && after.initialized b == (if written then true else p.initialized b)))

private def lockedCases : List Case := [
  { op := .bin .add .b (.mem { base := some .rbx, lock := true }) (.reg .rcx), readBytes := 1, stored := 0x12 },
  { op := .bin .sub .b (.mem { base := some .rbx, lock := true }) (.reg .rcx), readBytes := 1, stored := 0x10 },
  { op := .bin .adc .b (.mem { base := some .rbx, lock := true }) (.reg .rcx), readBytes := 1, stored := 0x13 },
  { op := .bin .sbb .b (.mem { base := some .rbx, lock := true }) (.reg .rcx), readBytes := 1, stored := 0xf },
  { op := .bin .and .b (.mem { base := some .rbx, lock := true }) (.reg .rcx), readBytes := 1, stored := 0x1 },
  { op := .bin .or .b (.mem { base := some .rbx, lock := true }) (.reg .rcx), readBytes := 1, stored := 0x11 },
  { op := .bin .xor .b (.mem { base := some .rbx, lock := true }) (.reg .rcx), readBytes := 1, stored := 0x10 },
  { op := .un .inc .b (.mem { base := some .rbx, lock := true }), readBytes := 1, stored := 0x12 },
  { op := .un .dec .b (.mem { base := some .rbx, lock := true }), readBytes := 1, stored := 0x10 },
  { op := .un .neg .b (.mem { base := some .rbx, lock := true }), readBytes := 1, stored := 0xef },
  { op := .un .not .b (.mem { base := some .rbx, lock := true }), readBytes := 1, stored := 0xee },
  { op := .bin .add .w (.mem { base := some .rbx, lock := true }) (.reg .rcx), readBytes := 2, stored := 0x2212 },
  { op := .bin .sub .w (.mem { base := some .rbx, lock := true }) (.reg .rcx), readBytes := 2, stored := 0x2210 },
  { op := .bin .adc .w (.mem { base := some .rbx, lock := true }) (.reg .rcx), readBytes := 2, stored := 0x2213 },
  { op := .bin .sbb .w (.mem { base := some .rbx, lock := true }) (.reg .rcx), readBytes := 2, stored := 0x220f },
  { op := .bin .and .w (.mem { base := some .rbx, lock := true }) (.reg .rcx), readBytes := 2, stored := 0x1 },
  { op := .bin .or .w (.mem { base := some .rbx, lock := true }) (.reg .rcx), readBytes := 2, stored := 0x2211 },
  { op := .bin .xor .w (.mem { base := some .rbx, lock := true }) (.reg .rcx), readBytes := 2, stored := 0x2210 },
  { op := .un .inc .w (.mem { base := some .rbx, lock := true }), readBytes := 2, stored := 0x2212 },
  { op := .un .dec .w (.mem { base := some .rbx, lock := true }), readBytes := 2, stored := 0x2210 },
  { op := .un .neg .w (.mem { base := some .rbx, lock := true }), readBytes := 2, stored := 0xddef },
  { op := .un .not .w (.mem { base := some .rbx, lock := true }), readBytes := 2, stored := 0xddee },
  { op := .bit .bts .w (.mem { base := some .rbx, lock := true }) (.imm 1), readBytes := 2, stored := 0x2213 },
  { op := .bit .btr .w (.mem { base := some .rbx, lock := true }) (.imm 1), readBytes := 2, stored := 0x2211 },
  { op := .bit .btc .w (.mem { base := some .rbx, lock := true }) (.imm 1), readBytes := 2, stored := 0x2213 },
  { op := .bin .add .d (.mem { base := some .rbx, lock := true }) (.reg .rcx), readBytes := 4, stored := 0x44332212 },
  { op := .bin .sub .d (.mem { base := some .rbx, lock := true }) (.reg .rcx), readBytes := 4, stored := 0x44332210 },
  { op := .bin .adc .d (.mem { base := some .rbx, lock := true }) (.reg .rcx), readBytes := 4, stored := 0x44332213 },
  { op := .bin .sbb .d (.mem { base := some .rbx, lock := true }) (.reg .rcx), readBytes := 4, stored := 0x4433220f },
  { op := .bin .and .d (.mem { base := some .rbx, lock := true }) (.reg .rcx), readBytes := 4, stored := 0x1 },
  { op := .bin .or .d (.mem { base := some .rbx, lock := true }) (.reg .rcx), readBytes := 4, stored := 0x44332211 },
  { op := .bin .xor .d (.mem { base := some .rbx, lock := true }) (.reg .rcx), readBytes := 4, stored := 0x44332210 },
  { op := .un .inc .d (.mem { base := some .rbx, lock := true }), readBytes := 4, stored := 0x44332212 },
  { op := .un .dec .d (.mem { base := some .rbx, lock := true }), readBytes := 4, stored := 0x44332210 },
  { op := .un .neg .d (.mem { base := some .rbx, lock := true }), readBytes := 4, stored := 0xbbccddef },
  { op := .un .not .d (.mem { base := some .rbx, lock := true }), readBytes := 4, stored := 0xbbccddee },
  { op := .bit .bts .d (.mem { base := some .rbx, lock := true }) (.imm 1), readBytes := 4, stored := 0x44332213 },
  { op := .bit .btr .d (.mem { base := some .rbx, lock := true }) (.imm 1), readBytes := 4, stored := 0x44332211 },
  { op := .bit .btc .d (.mem { base := some .rbx, lock := true }) (.imm 1), readBytes := 4, stored := 0x44332213 },
  { op := .bin .add .q (.mem { base := some .rbx, lock := true }) (.reg .rcx), readBytes := 8, stored := 0x8877665544332212 },
  { op := .bin .sub .q (.mem { base := some .rbx, lock := true }) (.reg .rcx), readBytes := 8, stored := 0x8877665544332210 },
  { op := .bin .adc .q (.mem { base := some .rbx, lock := true }) (.reg .rcx), readBytes := 8, stored := 0x8877665544332213 },
  { op := .bin .sbb .q (.mem { base := some .rbx, lock := true }) (.reg .rcx), readBytes := 8, stored := 0x887766554433220f },
  { op := .bin .and .q (.mem { base := some .rbx, lock := true }) (.reg .rcx), readBytes := 8, stored := 0x1 },
  { op := .bin .or .q (.mem { base := some .rbx, lock := true }) (.reg .rcx), readBytes := 8, stored := 0x8877665544332211 },
  { op := .bin .xor .q (.mem { base := some .rbx, lock := true }) (.reg .rcx), readBytes := 8, stored := 0x8877665544332210 },
  { op := .un .inc .q (.mem { base := some .rbx, lock := true }), readBytes := 8, stored := 0x8877665544332212 },
  { op := .un .dec .q (.mem { base := some .rbx, lock := true }), readBytes := 8, stored := 0x8877665544332210 },
  { op := .un .neg .q (.mem { base := some .rbx, lock := true }), readBytes := 8, stored := 0x778899aabbccddef },
  { op := .un .not .q (.mem { base := some .rbx, lock := true }), readBytes := 8, stored := 0x778899aabbccddee },
  { op := .bit .bts .q (.mem { base := some .rbx, lock := true }) (.imm 1), readBytes := 8, stored := 0x8877665544332213 },
  { op := .bit .btr .q (.mem { base := some .rbx, lock := true }) (.imm 1), readBytes := 8, stored := 0x8877665544332211 },
  { op := .bit .btc .q (.mem { base := some .rbx, lock := true }) (.imm 1), readBytes := 8, stored := 0x8877665544332213 }
]
private def checkLocked (cases : List Case) : Bool := cases.all (fun c => (List.range 8).all (fun mode =>
  checkRmw c.op (entry address initial) address c.readBytes initial c.stored (some input) mode))
example : checkLocked (lockedCases.take 14) = true := by decide
example : checkLocked ((lockedCases.drop 14).take 14) = true := by decide
example : checkLocked ((lockedCases.drop 28).take 14) = true := by decide
example : checkLocked (lockedCases.drop 42) = true := by decide

example : [Size.w,.d,.q].all (fun sz => [BitKind.bts,.btr,.btc].all (fun k =>
    (List.range 8).all (fun mode =>
      let base : Val := 0xfff
      let cpu := entry base 0x81
      let cpu := { cpu with regs := cpu.regs.set .rcx (-1) }
      checkRmw (.bit k sz (.mem { base := some .rbx, lock := true }) (.reg .rcx)) cpu base 1 0x81
        (if k == .bts then 0x81 else 1) (some input) mode))) = true := by decide

private def checkXchg (sz : Size) : Bool := [address,address+1].all (fun a =>
  [false,true].all (fun reverse => [false,true].all (fun locked => (List.range 8).all (fun mode =>
    let base := entry a initial
    let cpu := { base with regs := base.regs.set .rbx a }
    let mem : Operand := .mem { base := some .rbx, lock := locked }
    let op := if reverse then Op.xchg sz mem (.reg .rax) else .xchg sz (.reg .rax) mem
    let gold : Val := match sz with
      | .b => 0x1122334455667711 | .w => 0x1122334455662211
      | .d => 0x44332211 | .q => initial
    checkRmw op cpu a sz.bytes initial input (some gold) mode))))
example : checkXchg .b = true := by decide
example : checkXchg .w = true := by decide
example : checkXchg .d = true := by decide
example : checkXchg .q = true := by decide

private structure XchgAlias where
  size : Size := .q
  high : Bool := false
  before : Val := 0x1000
  address : Val := 0x1000
  ea : Ea := { base := some .rax }
  source : Val := 0x6000
  after : Val := 0x6000
  stored : Val := 0x1000

private def xchgAliases : List XchgAlias := [
  { size := .b, source := 0x44, after := 0x1044, stored := 0 },
  { size := .w, source := 0x3344, after := 0x3344 },
  { size := .d, source := 0x11223344, after := 0x11223344 },
  {},
  { size := .b, high := true, source := 0x44, after := 0x4400, stored := 0x10 },
  { before := 0xffff800000001000, address := 0xffff800000001000, stored := 0xffff800000001000 },
  { address := 0x3000, ea := { base := some .rbx, index := some .rax, scale := .s2 } },
  { address := 0x4013, ea := { ripRel := true, disp := 16 } },
  { address := 0x3000, ea := { base := some .rax, seg := some .fs } }
]
private def checkXchgAlias (c : XchgAlias) : Bool :=
  [false,true].all (fun reverse => [false,true].all (fun locked => (List.range 8).all (fun mode =>
    let seed := entry c.address c.source
    let cpu := { seed with regs := seed.regs.set .rax c.before, mem := seed.mem.writeSize .q c.after 0xaabbccddeeff7788 }
    let mem : Operand := .mem { c.ea with lock := locked }
    let reg : Operand := .reg .rax c.high
    let op := if reverse then Op.xchg c.size mem reg else .xchg c.size reg mem
    checkRmw op cpu c.address c.size.bytes c.source c.stored (some c.after) mode &&
      (stepChecked { op, len := 3 } { cpu, profile := some (profile { op, base := c.address, readBytes := c.size.bytes, writeBytes := c.size.bytes } mode) }).cpu.mem.readSize .q c.after == 0xaabbccddeeff7788)))
example : (xchgAliases.take 5).all checkXchgAlias = true := by decide
example : (xchgAliases.drop 5).all checkXchgAlias = true := by decide

-- Register-only ModR/M XCHG, including same-register and AH/AL views; a 90h
-- encoding is separately decoded as NOP and is not what these ASTs assert.
example : ([(Op.xchg .b (.reg .rax) (.reg .rbx),0x1122334455667700,0x1088),
    (.xchg .w (.reg .rax) (.reg .rbx),0x1122334455661000,0x7788),
    (.xchg .d (.reg .rax) (.reg .rbx),0x1000,0x55667788),
    (.xchg .q (.reg .rax) (.reg .rbx),0x1000,input),
    (.xchg .b (.reg .rax) (.reg .rax true),0x1122334455668877,0x1000),
    (.xchg .d (.reg .rax) (.reg .rax),0x55667788,0x1000),
    (.xchg .q (.reg .rax) (.reg .rax),input,0x1000)] : List (Op × Val × Val)).all (fun (op,rax,rbx) =>
      let cpu := entry address initial
      let i : Instr := { op, len := 3 }
      let t := stepChecked i { cpu, events := [prior] }
      t.fault.isNone && t.cpu.ms.isNone && t.profile.isNone && t.events == [prior] &&
      sameCpu t.cpu (step i cpu) && t.cpu.regs.rax == rax && t.cpu.regs.rbx == rbx) = true := by decide

example : spans.all (fun (a,lo,hi) => [(LinearAddressWidth.la48,lo),(.la57,hi)].all (fun (width,valid) =>
    [false,true].all (fun reverse => [false,true].all (fun locked => (List.range 3).all (fun mode =>
      let seed := entry a initial
      let cpu := { seed with regs := seed.regs.set .rbx a }
      let mem : Operand := .mem { base := some .rbx, lock := locked }
      let op := if reverse then Op.xchg .q mem (.reg .rax) else .xchg .q (.reg .rax) mem
      let p : MemoryProfile := { readable := fun _ => mode != 1, writable := fun _ => mode != 2 }
      let i : Instr := { op, len := 3 }
      let t := stepChecked i { cpu, addressWidth := width, profile := some p, events := [prior] }
      let fault := if !valid then some (ExecutionFault.nonCanonical a)
        else if mode == 1 then some (.read a 8) else if mode == 2 then some (.write a 8) else none
      let events := [prior] ++ (match fault with
        | none => [.rmw a (bytes 8 initial) (bytes 8 input) false]
        | some f => (if valid && mode == 2 then [.memory .read a (bytes 8 initial) false] else []) ++ [.fault f])
      t.fault == fault && t.cpu.ms.isNone && t.events == events &&
      sameCpu t.cpu (if fault.isNone then step i cpu width else cpu)))))) = true := by decide

example : ([Op.xchg .q (.imm 1) (.reg .rax), .xchg .q (.reg .rax) (.imm 1),
    .xchg .q memory memory, .xchg .b (.imm 1) memory] : List Op).all (fun op =>
      [false,true].all (fun bound =>
        let cpu := entry address initial
        let p : MemoryProfile := { readable := fun _ => false, writable := fun _ => false }
        let t := stepChecked { op, len := 3 } { cpu, profile := if bound then some p else none, events := [prior] }
        (match t.cpu.ms with | some (.illegalOperands _) => true | _ => false) &&
        t.fault.isNone && t.events == [prior] && sameCpu { t.cpu with ms := none } cpu)) = true := by decide

example : [false,true].all (fun reverse => [false,true].all (fun locked =>
    let cpu := entry address initial
    let mem : Operand := .mem { base := some .rbx, lock := locked }
    let op := if reverse then Op.xchg .q mem (.reg .rax) else .xchg .q (.reg .rax) mem
    let t := stepChecked { op, len := 3 } { cpu, events := [prior] }
    t.cpu.ms.isSome && t.fault.isNone && t.events == [prior] && sameCpu { t.cpu with ms := none } cpu)) = true := by decide

example : (List.range 3).all (fun scene =>
    let cpu := entry address initial
    let p : MemoryProfile := {}
    let i : Instr := { op := .xchg .q (.reg .rax) memory, len := 3 }
    let s := stepChecked i { cpu, profile := some p, events := [prior] }
    let s := { s with profile := s.profile.map (fun p => { p with readable := fun _ => scene != 1, writable := fun _ => scene != 2 }) }
    let t := runChecked [i,{ op := .nop none, len := 1 }] s
    let fault := if scene == 1 then some (ExecutionFault.read address 8) else if scene == 2 then some (.write address 8) else none
    let events := [prior,.rmw address (bytes 8 initial) (bytes 8 input) false] ++
      (match fault with
        | none => [.rmw address (bytes 8 input) (bytes 8 initial) true]
        | some f => (if scene == 2 then [.memory .read address (bytes 8 input) true] else []) ++ [.fault f])
    t.fault == fault && t.cpu.ms.isNone && t.events == events &&
    sameCpu t.cpu (if scene == 0 then step { op := .nop none, len := 1 } (step i (step i cpu)) else step i cpu) &&
    t.cpu.regs.rax == (if scene == 0 then input else initial) &&
    t.cpu.mem.readSize .q address == (if scene == 0 then initial else input) &&
    t.cpu.rip == (if scene == 0 then 0x4007 else 0x4003)) = true := by decide


end X86.Tests.CheckedAccess
