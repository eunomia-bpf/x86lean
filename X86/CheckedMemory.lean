/-
# Checked flat-memory execution over the existing numeric step

The access layer validates and observes transfers; arithmetic/register/flag
semantics are executed by X86.step and its shared double-shift result helper. The original Cpu and step domain
are unchanged. This is not MMU translation, concurrency or exception entry.
-/
import X86.Semantics

namespace X86

/-- Effective byte permissions and initialization, supplied explicitly by the
platform. An uninitialized byte retains its actual Mem value. -/
structure MemoryProfile where
  readable : Val → Bool := fun _ => true
  writable : Val → Bool := fun _ => true
  initialized : Val → Bool := fun _ => false

/-- Faults at the flat access boundary, distinct from MsErr model refusals.
The address names the whole denied access, not an x86 CR2/error-code model. -/
inductive ExecutionFault where
  | read (address : Val) (bytes : Nat)
  | write (address : Val) (bytes : Nat)
  | nonCanonical (address : Val)
  | invalidOpcode
  | divideError
  | misaligned (address : Val) (bytes : Nat)
  deriving DecidableEq, BEq, Repr

inductive MemoryAccessKind where
  | read | write
  deriving DecidableEq, BEq, Repr

inductive MemoryAccessEvent where
  | memory (kind : MemoryAccessKind) (address : Val) (value : List (BitVec 8)) (initialized : Bool)
  | rmw (address : Val) (before after : List (BitVec 8)) (initialized : Bool)
  | fault (reason : ExecutionFault)
  deriving DecidableEq, BEq, Repr

/-- Checked metadata surrounds the original Cpu rather than altering its
characterization domain. No missing profile silently becomes total memory. -/
structure CheckedState where
  cpu : Cpu
  profile : Option MemoryProfile := none
  addressWidth : LinearAddressWidth := .la48
  events : List MemoryAccessEvent := []
  fault : Option ExecutionFault := none

namespace CheckedState

def stopped (s : CheckedState) : Bool := s.fault.isSome || s.cpu.stopped

end CheckedState

private structure AccessSpan where
  address : Val
  bytes : Nat
  aligned : Bool := false

/-- Supported scalar forms have reads followed by at most one final store.
Instructions with intermediate commits need their own shared iteration seam. -/
private structure AccessPlan where
  reads : List AccessSpan := []
  store : Option AccessSpan := none
  target : Option Val := none
  rmw : Bool := false

private def spanFor (s : Cpu) (nr : Val) (size : Size) : Operand → Option AccessSpan
  | .mem ea => some { address := ea.addr s nr, bytes := size.bytes }
  | _ => none

private def sourcePlan (valid : Bool) (s : Cpu) (nr : Val) (size : Size)
    (src : Operand) : Except MsErr AccessPlan :=
  if !valid || src.isImm then .error (.illegalOperands "Invalid checked scalar source/width")
  else .ok { reads := (spanFor s nr size src).toList }

/-- Operand effects only: no duplicate numeric or flag interpretation.
CMOV memory sources are read even when the value is not selected (Intel SDM
CMOVcc operation: the source read precedes condition evaluation). -/
private def accessPlan (i : Instr) (s : Cpu) : Except MsErr AccessPlan :=
  let nr := s.rip + BitVec.ofNat 64 i.len
  match i.op with
  | .nop _ | .lea .. | .cext _ => .ok {}
  | .mov sz dst src =>
    if !wellFormed2 dst src || dst.isImm then .error (.illegalOperands "Invalid checked MOV operands")
    else .ok { reads := (spanFor s nr sz src).toList, store := spanFor s nr sz dst }
  | .bin k sz dst src =>
    if !wellFormed2 dst src || dst.isImm then .error (.illegalOperands "Invalid checked binary operands")
    else .ok
      { reads := (spanFor s nr sz dst).toList ++ (spanFor s nr sz src).toList,
        store := if k == .cmp || k == .test then none else spanFor s nr sz dst, rmw := i.op.anyLocked }
  | .un _ sz dst =>
    if dst.isImm then .error (.illegalOperands "Invalid checked unary destination")
    else .ok { reads := (spanFor s nr sz dst).toList, store := spanFor s nr sz dst, rmw := i.op.anyLocked }
  | .movx _ _ ssz _ src =>
    if src.isImm then .error (.illegalOperands "Invalid checked extending-load source")
    else .ok { reads := (spanFor s nr ssz src).toList }
  | .cmov _ _ _ (.imm _) => .error (.illegalOperands "Invalid checked CMOV source")
  | .cmov _ sz _ src => .ok { reads := (spanFor s nr sz src).toList }
  | .setcc _ dst =>
    if dst.isImm then .error (.illegalOperands "Invalid checked SETcc destination")
    else .ok { store := spanFor s nr .b dst }
  | .xchg sz a b =>
    if a.isImm || b.isImm || !wellFormed2 a b then .error (.illegalOperands "Invalid checked XCHG operands")
    else .ok { reads := (spanFor s nr sz a).toList ++ (spanFor s nr sz b).toList, store := (spanFor s nr sz a).orElse (fun _ => spanFor s nr sz b), rmw := a.isMem || b.isMem }
  | .bswap .. => .ok {} -- The numeric step retains its undefined-width refusal.
  | .shift _ sz dst _ | .rot _ sz dst _ =>
    if dst.isImm then .error (.illegalOperands "Invalid checked shift/rotate destination")
    else .ok { reads := (spanFor s nr sz dst).toList, store := spanFor s nr sz dst }
  | .dshift _ sz dst _ _ =>
    if !dshiftEncodable sz || dst.isImm then
      .error (.illegalOperands "Invalid checked double-shift destination/width")
    else .ok { reads := (spanFor s nr sz dst).toList, store := spanFor s nr sz dst }
  | .shiftx _ sz _ src _ | .rorx sz _ src _ | .bzhi sz _ src _
  | .andn sz _ _ src | .mulx sz _ _ src =>
    sourcePlan (sz == .d || sz == .q) s nr sz src
  | .bitcnt k sz _ src => sourcePlan (bitcntEncodable k sz) s nr sz src
  | .imulr sz _ src _ => sourcePlan (imulrEncodable sz) s nr sz src
  | .muldiv _ sz src => sourcePlan true s nr sz src
  | .movbe sz dst src =>
    if sz == .b || !(dst.isMem != src.isMem) || dst.isImm || src.isImm then
      .error (.illegalOperands "Invalid checked MOVBE operands/width")
    else .ok { reads := (spanFor s nr sz src).toList, store := spanFor s nr sz dst }
  | .push sz src =>
    if sz != .w && sz != .q then .error (.illegalOperands "Invalid checked PUSH width")
    else .ok { reads := (spanFor s nr sz src).toList, store := some { address := s.regs.get .rsp - BitVec.ofNat 64 sz.bytes, bytes := sz.bytes } }
  | .pop sz dst =>
    if (sz != .w && sz != .q) || dst.isImm then .error (.illegalOperands "Invalid checked POP operands/width")
    else .ok { reads := [{ address := s.regs.get .rsp, bytes := sz.bytes }], store := spanFor (s.popValue sz).2 nr sz dst }
  | .jmp target | .call target =>
    match target with
    | .indirect (.imm _) => .error (.illegalOperands "Invalid checked indirect target")
    | _ =>
      let reads := match target with | .rel _ => [] | .indirect src => (spanFor s nr .q src).toList
      let store := match i.op with
        | .call _ => some { address := s.regs.get .rsp - 8, bytes := 8 }
        | _ => none
      .ok { reads, store, target := some (target.resolve s nr) }
  | .ret => .ok { reads := [{ address := s.regs.get .rsp, bytes := 8 }], target := some (s.readMem .q (s.regs.get .rsp)) }
  | .jcc condition displacement => .ok { target := if condition.eval s.flags then some (nr + displacement) else none }
  | .jcxz addr32 displacement => .ok { target := if s.jcxzTaken addr32 then some (nr + displacement) else none }
  | .loop kind addr32 displacement =>
    .ok { target := if kind.taken (s.loopCount addr32) s.flags.zf then some (nr + displacement) else none }
  | .bit k sz (.mem ea) (.reg reg high) =>
    if sz == .b then .error (.illegalOperands "Invalid checked bit-test width")
    else
      let span : AccessSpan := { address := bitStringByte s sz ea reg high nr, bytes := 1 }
      .ok { reads := [span], store := if k == .bt then none else some span, rmw := i.op.anyLocked }
  | .bit k sz dst offset =>
    if sz == .b || dst.isImm || offset.isMem then .error (.illegalOperands "Invalid checked bit-test operands/width")
    else .ok { reads := (spanFor s nr sz dst).toList, store := if k == .bt then none else spanFor s nr sz dst, rmw := i.op.anyLocked }
  | .vmov .. => .ok {}
  | .vmovs sz .. =>
    if vmovsEncodable sz then .ok {} else .error (.illegalOperands "Invalid checked scalar vector width")
  | .vload kind _ ea =>
    .ok { reads := [{ address := ea.addr s nr, bytes := 16, aligned := kind.aligned }] }
  | .vstore kind ea _ =>
    .ok { store := some { address := ea.addr s nr, bytes := 16, aligned := kind.aligned } }
  | .vloadq _ _ _ ea => .ok { reads := [{ address := ea.addr s nr, bytes := 8 }] }
  | .vstoreq _ _ ea _ => .ok { store := some { address := ea.addr s nr, bytes := 8 } }
  | .vmovsld sz _ ea | .vmovgld sz _ ea =>
    if !vmovsEncodable sz then .error (.illegalOperands "Invalid checked scalar vector width")
    else .ok { reads := [{ address := ea.addr s nr, bytes := sz.bytes }] }
  | .vmovsst sz ea _ | .vmovgst sz ea _ =>
    if !vmovsEncodable sz then .error (.illegalOperands "Invalid checked scalar vector width")
    else .ok { store := some { address := ea.addr s nr, bytes := sz.bytes } }
  | .strop .movs sz =>
    .ok { reads := [{ address := s.regs.get .rsi, bytes := sz.bytes }], store := some { address := s.regs.get .rdi, bytes := sz.bytes } }
  | .repstrop .rep .movs sz =>
    if s.regs.get .rcx == 0 then .ok {} else
    .ok { reads := [{ address := s.regs.get .rsi, bytes := sz.bytes }], store := some { address := s.regs.get .rdi, bytes := sz.bytes } }
  | _ => .error (.unimplemented "Checked access is not yet supported for this instruction class")

/-- Potential input bytes for a platform memory view, using the very same
access plan as checked execution. This does not grant access: stepChecked must
still check canonicality, alignment and permissions, and recompute targets from
the supplied bytes. An adapter can materialize arbitrary functional memory into
the finite Mem representation without duplicating instruction footprints. -/
def plannedReadAddresses (i : Instr) (s : Cpu) : Except MsErr (List Val) :=
  if s.stopped || i.op.lockIllegal then .ok [] else
  match i.op with
  | .ud2 => .ok []
  | _ => do
    let plan ← accessPlan i s
    pure (plan.reads.flatMap (fun span =>
      (List.range span.bytes).map (fun offset => span.address + BitVec.ofNat 64 offset)))

private def permitted (p : Val → Bool) (span : AccessSpan) : Bool :=
  (List.range span.bytes |>.map (fun offset => span.address + BitVec.ofNat 64 offset)).all p

private def bytesAt (m : Mem) (span : AccessSpan) : List (BitVec 8) :=
  (List.range span.bytes |>.map (fun offset => span.address + BitVec.ofNat 64 offset)).map m.read

private def fail (s : CheckedState) (fault : ExecutionFault) : CheckedState :=
  { s with fault := some fault, events := s.events ++ [.fault fault] }

private def refuse (s : CheckedState) (reason : MsErr) : CheckedState :=
  { s with cpu := s.cpu.halt reason }

private def validate (kind : MemoryAccessKind) (span : AccessSpan) (s : CheckedState) : CheckedState :=
  match s.profile with
  | none => refuse s (.unimplemented "Checked memory requires an explicit platform profile")
  | some profile =>
    if !permitted (fun address => canonical address s.addressWidth) span then
      fail s (.nonCanonical span.address)
    else if span.aligned && !aligned16 span.address then fail s (.misaligned span.address 16)
    else
      let permission := match kind with | .read => profile.readable | .write => profile.writable
      if !permitted permission span then
        fail s (match kind with
          | .read => .read span.address span.bytes
          | .write => .write span.address span.bytes)
      else match kind with
        | .write => s -- Deferred until the actual numeric step succeeds.
        | .read =>
          let data := bytesAt s.cpu.mem span
          let initialized := permitted profile.initialized span
          { s with events := s.events ++ [.memory .read span.address data initialized] }

private def commit (plan : AccessPlan) (original before : CheckedState) (cpu : Cpu) : CheckedState :=
  -- MsErr still denotes model refusal, never a fabricated architectural fault.
  if cpu.stopped then { before with cpu } else
  match plan.store with
  | none => { before with cpu }
  | some span =>
    match before.profile with
    | none => refuse before (.unimplemented "Checked store lost its validated profile")
    | some profile =>
      let initialized := fun address =>
        if (address - span.address).toNat < span.bytes then true else profile.initialized address
      let event := if plan.rmw then
        MemoryAccessEvent.rmw span.address (bytesAt original.cpu.mem span) (bytesAt cpu.mem span) (permitted profile.initialized span)
        else .memory .write span.address (bytesAt cpu.mem span) true
      -- A successful RMW is one observation; its preflight read is retained
      -- separately only on fault. Every incoming public event is preserved.
      let history := if plan.rmw then original.events else before.events
      { before with cpu, profile := some { profile with initialized }, events := history ++ [event] }

/-- The same shared pair calculation used by the numeric step decides #DE.
Only the typed outcome is added here, after successful operand access. -/
private def divisionFault (i : Instr) (s : Cpu) : Bool :=
  match i.op with
  | .muldiv .div sz src =>
    (Value.divPairU sz (s.mdHi sz) (s.getReg sz .rax)
      (s.readOperand sz (s.rip + BitVec.ofNat 64 i.len) src)).isNone
  | .muldiv .idiv sz src =>
    (Value.divPairS sz (s.mdHi sz) (s.getReg sz .rax)
      (s.readOperand sz (s.rip + BitVec.ofNat 64 i.len) src)).isNone
  | _ => false

/-- Keep the original harness refusal in step, while exposing the same
oracle-driven result branch to checked memory. Access and encoding validation
precede this call. The numeric rule itself lives beside the default step. -/
private def checkedResult (i : Instr) (s : Cpu) (width : LinearAddressWidth) : Cpu :=
  match i.op with
  | .dshift k sz dst src amt =>
    let count := match amt with | .imm8 value => value | .cl => (s.getReg .b .rcx).setWidth 8
    let n := Flags.shiftCount sz count
    if dshiftMemUndefined sz dst.isMem n then
      dshiftResult k sz dst src n (s.rip + BitVec.ofNat 64 i.len) s
    else step i s width
  | _ => step i s width

/-- Execute a supported instruction with checked effects. Every successful
numeric result comes from the original step or its shared result helper. A denied final store retains the
read prefix, while registers/flags/memory/oracle/PC do not commit. A missing or
unported capability is MsErr, distinct from a checked access fault. -/
def stepChecked (i : Instr) (s : CheckedState) : CheckedState :=
  if s.stopped then s else
  if i.op.lockIllegal then fail s .invalidOpcode else
  match i.op with
  | .ud2 => fail s .invalidOpcode
  | _ =>
    match accessPlan i s.cpu with
    | .error reason => refuse s reason
    | .ok plan =>
      let checked := plan.reads.foldl (fun state span =>
        if state.stopped then state else validate .read span state) s
      -- CALL's stack-write access precedes target canonicality. In
      -- particular a denied return-slot write wins over a noncanonical target;
      -- it remains preflight only, with no committed bytes on either fault.
      let checked := if checked.stopped then checked else
        match plan.store with | none => checked | some span => validate .write span checked
      let checked := if checked.stopped then checked else
        match plan.target with
        | some target => if canonical target checked.addressWidth then checked else fail checked (.nonCanonical target)
        | none => checked
      if checked.stopped then checked else
      if divisionFault i checked.cpu then fail checked .divideError else
        commit plan s checked (checkedResult i checked.cpu checked.addressWidth)

def runChecked (instructions : List Instr) (s : CheckedState) : CheckedState :=
  instructions.foldl (fun state instruction => stepChecked instruction state) s

/-- A checked fault or model refusal is stable, including the entire profile
and event prefix, not just the register projections. -/
theorem stepChecked_stopped (i : Instr) (s : CheckedState) (h : s.stopped = true) :
    stepChecked i s = s := by
  simp [stepChecked, h]

end X86
