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

-- Double-shift undefined memory results remain a MODEL refusal after the read,
-- even with write permission denied. An earlier read fault takes precedence.
example : [DShiftKind.shld,.shrd].all (fun k => [17,31].all (fun count =>
    [false,true].all (fun deny =>
      let cpu := entry address initial
      let p : MemoryProfile := { readable := fun _ => !deny, writable := fun _ => false }
      let i : Instr := { op := .dshift k .w memory .rcx (.imm8 count), len := 3 }
      let t := stepChecked i { cpu, profile := some p, events := [prior] }
      if deny then t.fault == some (.read address 2) && t.cpu.ms.isNone && sameCpu t.cpu cpu &&
        t.events == [prior,.fault (.read address 2)]
      else (match t.cpu.ms with | some (.unimplemented _) => true | _ => false) &&
        t.fault.isNone && sameCpu { t.cpu with ms := none } cpu &&
        t.events == [prior,.memory .read address [0x11,0x22] false]))) = true := by decide

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

end X86.Tests.CheckedAccess
