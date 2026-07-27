/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Complexitylib.Models.TuringMachine.Experimental.BinaryRoutine.SpaceBounds.Defs
public import Complexitylib.Models.TuringMachine.Experimental.BinaryRoutine.Arithmetic
public import Complexitylib.Models.TuringMachine.Experimental.BinaryRoutine.List

/-!
# Compositional width bounds for binary routines -- proof internals
-/

@[expose] public section

namespace Complexity

namespace BinaryRoutine

theorem SpaceBoundInLogAt.of_le_internal
    {routine : BinaryRoutine n} {initialSpace : ℕ → ℕ}
    {values : ℕ → BinaryValues n} {bound : ℕ → ℕ}
    (hle : ∀ inputLength,
      routine.spaceBound (initialSpace inputLength) (values inputLength) ≤
        bound inputLength)
    (hbound : bound =O (fun inputLength => Nat.log 2 inputLength)) :
    SpaceBoundInLogAt routine initialSpace values := by
  unfold SpaceBoundInLogAt
  exact (BigO.of_le hle).trans hbound

theorem SpaceBoundInLogAt.restrict_internal
    {routine : BinaryRoutine n} {requires : BinaryValues n → Prop}
    {initialSpace : ℕ → ℕ} {values : ℕ → BinaryValues n}
    (hspace : SpaceBoundInLogAt routine initialSpace values) :
    SpaceBoundInLogAt (routine.restrict requires) initialSpace values :=
  hspace

theorem SpaceBoundInLogAt.seq_internal
    {first second : BinaryRoutine n} {initialSpace : ℕ → ℕ}
    {values : ℕ → BinaryValues n}
    (hfirst : SpaceBoundInLogAt first initialSpace values)
    (hsecond : SpaceBoundInLogAt second initialSpace
      (fun inputLength => first.effect (values inputLength))) :
    SpaceBoundInLogAt (seq first second) initialSpace values := by
  unfold SpaceBoundInLogAt at *
  exact BigO.max_same hfirst hsecond

theorem SpaceBoundInLogAt.branchZero_internal
    {onZero onPositive : BinaryRoutine n} (idx : Fin n)
    {initialSpace : ℕ → ℕ} {values : ℕ → BinaryValues n}
    (hzero : SpaceBoundInLogAt onZero initialSpace values)
    (hpositive : SpaceBoundInLogAt onPositive initialSpace values) :
    SpaceBoundInLogAt (branchZero idx onZero onPositive) initialSpace values := by
  unfold SpaceBoundInLogAt at *
  exact BigO.max_same hzero hpositive

theorem SpaceBoundByWidthAt.mono_internal
    {routine : BinaryRoutine n} {initialSpace : ℕ → ℕ}
    {values : ℕ → BinaryValues n} {width width' : ℕ → ℕ}
    (hspace : SpaceBoundByWidthAt routine initialSpace values width)
    (hle : ∀ inputLength, width inputLength ≤ width' inputLength) :
    SpaceBoundByWidthAt routine initialSpace values width' := by
  obtain ⟨constant, hconstant⟩ := hspace
  refine ⟨constant, fun inputLength => ?_⟩
  exact (hconstant inputLength).trans (by
    have hsize := Nat.size_le_size (hle inputLength)
    have hscaled := Nat.mul_le_mul_left constant hsize
    omega)

theorem SpaceBoundByWidthAt.restrict_internal
    {routine : BinaryRoutine n} {requires : BinaryValues n → Prop}
    {initialSpace : ℕ → ℕ} {values : ℕ → BinaryValues n}
    {width : ℕ → ℕ}
    (hspace : SpaceBoundByWidthAt routine initialSpace values width) :
    SpaceBoundByWidthAt (routine.restrict requires) initialSpace values
      width :=
  hspace

theorem SpaceBoundByWidthAt.emitBits_internal
    (word : List Bool) {initialSpace : ℕ → ℕ}
    {values : ℕ → BinaryValues n} {width : ℕ → ℕ} :
    SpaceBoundByWidthAt (emitBits word) initialSpace values width := by
  refine ⟨word.length, fun inputLength => ?_⟩
  simp only [emitBits]
  omega

theorem SpaceBoundByWidthAt.identity_internal
    {initialSpace : ℕ → ℕ} {values : ℕ → BinaryValues n}
    {width : ℕ → ℕ} :
    SpaceBoundByWidthAt identity initialSpace values width := by
  exact SpaceBoundByWidthAt.emitBits_internal []

theorem SpaceBoundByWidthAt.clear_internal
    (idx : Fin n) {initialSpace : ℕ → ℕ}
    {values : ℕ → BinaryValues n} {width : ℕ → ℕ}
    (hvalue : ∀ inputLength, values inputLength idx ≤ width inputLength) :
    SpaceBoundByWidthAt (clear idx) initialSpace values width := by
  refine ⟨5, fun inputLength => ?_⟩
  have hsize := Nat.size_le_size (hvalue inputLength)
  have hbits : (values inputLength idx).bits.length =
      (values inputLength idx).size :=
    Nat.size_eq_bits_len (values inputLength idx)
  simp only [clear, TM.clearWorkTimeBound]
  rw [hbits]
  omega

theorem SpaceBoundByWidthAt.binarySucc_internal
    (idx : Fin n) {initialSpace : ℕ → ℕ}
    {values : ℕ → BinaryValues n} {width : ℕ → ℕ}
    (hvalue : ∀ inputLength, values inputLength idx ≤ width inputLength) :
    SpaceBoundByWidthAt (binarySucc idx) initialSpace values width := by
  refine ⟨3, fun inputLength => ?_⟩
  have hsize := Nat.size_le_size (hvalue inputLength)
  have htime := TM.binarySuccTime_le (values inputLength idx)
  simp only [binarySucc]
  omega

theorem SpaceBoundByWidthAt.binaryPred_internal
    (idx : Fin n) {initialSpace : ℕ → ℕ}
    {values : ℕ → BinaryValues n} {width : ℕ → ℕ}
    (hvalue : ∀ inputLength,
      values inputLength idx - 1 + 1 ≤ width inputLength) :
    SpaceBoundByWidthAt (binaryPred idx) initialSpace values width := by
  refine ⟨3, fun inputLength => ?_⟩
  have hsize := Nat.size_le_size (hvalue inputLength)
  simp only [binaryPred, TM.binaryPredSpace]
  omega

theorem SpaceBoundByWidthAt.binaryCopy_internal
    (srcIdx dstIdx counterIdx : Fin n) {initialSpace : ℕ → ℕ}
    {values : ℕ → BinaryValues n} {width : ℕ → ℕ}
    (hsrc : ∀ inputLength,
      values inputLength srcIdx ≤ width inputLength)
    (hdst : ∀ inputLength,
      values inputLength dstIdx ≤ width inputLength) :
    SpaceBoundByWidthAt (binaryCopy srcIdx dstIdx counterIdx) initialSpace
      values width := by
  refine ⟨16, fun inputLength => ?_⟩
  have hsrcSize := Nat.size_le_size (hsrc inputLength)
  have hdstSize := Nat.size_le_size (hdst inputLength)
  have hadd := TM.binaryRippleAddTime_le
    (values inputLength srcIdx) 0
  simp only [binaryCopy, TM.binaryCopySpace, TM.clearWorkTimeBound,
    max_le_iff]
  simp only [Nat.size_zero, Nat.add_zero] at hadd
  omega

theorem SpaceBoundByWidthAt.addConst_internal
    (idx : Fin n) (constant : ℕ) {initialSpace : ℕ → ℕ}
    {values : ℕ → BinaryValues n} {width : ℕ → ℕ}
    (hvalue : ∀ inputLength,
      values inputLength idx + constant ≤ width inputLength) :
    SpaceBoundByWidthAt (addConst idx constant) initialSpace values width := by
  refine ⟨3, fun inputLength => ?_⟩
  have hsize := Nat.size_le_size (hvalue inputLength)
  simp only [addConst, TM.binaryAddConstSpace]
  omega

theorem SpaceBoundByWidthAt.add_internal
    (srcIdx dstIdx counterIdx : Fin n) {initialSpace : ℕ → ℕ}
    {values : ℕ → BinaryValues n} {width : ℕ → ℕ}
    (hsrc : ∀ inputLength,
      values inputLength srcIdx ≤ width inputLength)
    (hsum : ∀ inputLength,
      values inputLength dstIdx + values inputLength srcIdx ≤
        width inputLength) :
    SpaceBoundByWidthAt (add srcIdx dstIdx counterIdx) initialSpace values
      width := by
  refine ⟨16, fun inputLength => ?_⟩
  have hsrcSize := Nat.size_le_size (hsrc inputLength)
  have hsumSize := Nat.size_le_size (hsum inputLength)
  simp only [add, TM.binaryAddSpace, TM.binaryAddLoopSpace,
    TM.clearWorkTimeBound]
  omega

theorem SpaceBoundByWidthAt.mulAdd_internal
    (leftIdx rightIdx accIdx mulCounterIdx addCounterIdx : Fin n)
    {initialSpace : ℕ → ℕ} {values : ℕ → BinaryValues n}
    {width : ℕ → ℕ}
    (hleft : ∀ inputLength,
      values inputLength leftIdx ≤ width inputLength)
    (hright : ∀ inputLength,
      values inputLength rightIdx ≤ width inputLength)
    (htotal : ∀ inputLength,
      values inputLength accIdx +
          values inputLength leftIdx * values inputLength rightIdx +
        values inputLength leftIdx ≤ width inputLength) :
    SpaceBoundByWidthAt
      (mulAdd leftIdx rightIdx accIdx mulCounterIdx addCounterIdx)
      initialSpace values width := by
  refine ⟨32, fun inputLength => ?_⟩
  have hleftSize := Nat.size_le_size (hleft inputLength)
  have hrightSize := Nat.size_le_size (hright inputLength)
  have htotalSize := Nat.size_le_size (htotal inputLength)
  simp only [mulAdd, TM.binaryMulAddSpace, TM.binaryMulAddLoopSpace,
    TM.binaryAddSpace, TM.binaryAddLoopSpace, TM.clearWorkTimeBound]
  omega

theorem SpaceBoundByWidthAt.evalPolynomial_internal
    (inputIdx resultIdx scratchIdx mulCounterIdx addCounterIdx : Fin n)
    (p : Polynomial ℕ) {initialSpace : ℕ → ℕ}
    {values : ℕ → BinaryValues n} {width : ℕ → ℕ}
    (hvalue : ∀ inputLength,
      2 * TM.binaryPolynomialValueCap p (values inputLength inputIdx) ≤
        width inputLength) :
    SpaceBoundByWidthAt
      (evalPolynomial inputIdx resultIdx scratchIdx mulCounterIdx
        addCounterIdx p) initialSpace values width := by
  refine ⟨17, fun inputLength => ?_⟩
  have hsize := Nat.size_le_size (hvalue inputLength)
  simp only [evalPolynomial, TM.binaryPolynomialSpace]
  omega

theorem SpaceBoundByWidthAt.emitNatCode_internal
    (counterIdx valueIdx : Fin n) {initialSpace : ℕ → ℕ}
    {values : ℕ → BinaryValues n} {width : ℕ → ℕ}
    (hvalue : ∀ inputLength,
      values inputLength valueIdx ≤ width inputLength) :
    SpaceBoundByWidthAt (emitNatCode counterIdx valueIdx) initialSpace values
      width := by
  refine ⟨5, fun inputLength => ?_⟩
  have hsize := Nat.size_le_size (hvalue inputLength)
  simp only [emitNatCode, CircuitCode.Machine.emitNatCodeSpace]
  omega

theorem SpaceBoundByWidthAt.emitRawGate_internal
    (op : AndOrOp) (negated₀ negated₁ : Bool)
    (emitCounterIdx input₀Idx input₁Idx : Fin n)
    {initialSpace : ℕ → ℕ} {values : ℕ → BinaryValues n}
    {width : ℕ → ℕ}
    (hinput₀ : ∀ inputLength,
      values inputLength input₀Idx ≤ width inputLength)
    (hinput₁ : ∀ inputLength,
      values inputLength input₁Idx ≤ width inputLength) :
    SpaceBoundByWidthAt
      (emitRawGate op negated₀ negated₁ emitCounterIdx input₀Idx input₁Idx)
      initialSpace values width := by
  refine ⟨5, fun inputLength => ?_⟩
  have hinput₀Size := Nat.size_le_size (hinput₀ inputLength)
  have hinput₁Size := Nat.size_le_size (hinput₁ inputLength)
  simp only [emitRawGate, CircuitCode.Machine.emitRawGateSpace]
  have hmax : max (values inputLength input₀Idx).size
      (values inputLength input₁Idx).size ≤ (width inputLength).size :=
    max_le hinput₀Size hinput₁Size
  omega

theorem SpaceBoundByWidthAt.emitRawGateStep_internal
    (op : AndOrOp) (negated₀ negated₁ : Bool)
    (emitCounterIdx availableIdx input₀Idx input₁Idx : Fin n)
    {initialSpace : ℕ → ℕ} {values : ℕ → BinaryValues n}
    {width : ℕ → ℕ}
    (havailable : ∀ inputLength,
      values inputLength availableIdx ≤ width inputLength)
    (hinput₀ : ∀ inputLength,
      values inputLength input₀Idx ≤ width inputLength)
    (hinput₁ : ∀ inputLength,
      values inputLength input₁Idx ≤ width inputLength) :
    SpaceBoundByWidthAt
      (emitRawGateStep op negated₀ negated₁ emitCounterIdx availableIdx
        input₀Idx input₁Idx) initialSpace values width := by
  refine ⟨8, fun inputLength => ?_⟩
  have havailableSize := Nat.size_le_size (havailable inputLength)
  have hinput₀Size := Nat.size_le_size (hinput₀ inputLength)
  have hinput₁Size := Nat.size_le_size (hinput₁ inputLength)
  have htime := TM.binarySuccTime_le (values inputLength availableIdx)
  simp only [emitRawGateStep, CircuitCode.Machine.emitRawGateStepSpace,
    CircuitCode.Machine.emitRawGateSpace, max_le_iff]
  constructor
  · have hmax : max (values inputLength input₀Idx).size
        (values inputLength input₁Idx).size ≤ (width inputLength).size :=
      max_le hinput₀Size hinput₁Size
    omega
  · omega

theorem SpaceBoundByWidthAt.seq_internal
    {first second : BinaryRoutine n} {initialSpace : ℕ → ℕ}
    {values : ℕ → BinaryValues n} {width : ℕ → ℕ}
    (hfirst : SpaceBoundByWidthAt first initialSpace values width)
    (hsecond : SpaceBoundByWidthAt second initialSpace
      (fun inputLength => first.effect (values inputLength)) width) :
    SpaceBoundByWidthAt (seq first second) initialSpace values width := by
  obtain ⟨firstConstant, hfirst⟩ := hfirst
  obtain ⟨secondConstant, hsecond⟩ := hsecond
  refine ⟨firstConstant + secondConstant, fun inputLength => ?_⟩
  simp only [seq]
  apply max_le
  · exact (hfirst inputLength).trans (by
      have hcoefficient : firstConstant ≤ firstConstant + secondConstant := by
        omega
      have hscaled := Nat.mul_le_mul_right (width inputLength).size
        hcoefficient
      omega)

  · exact (hsecond inputLength).trans (by
      have hcoefficient : secondConstant ≤ firstConstant + secondConstant := by
        omega
      have hscaled := Nat.mul_le_mul_right (width inputLength).size
        hcoefficient
      omega)

theorem SpaceBoundByWidthAt.set_internal
    (idx : Fin n) (value : ℕ) {initialSpace : ℕ → ℕ}
    {values : ℕ → BinaryValues n} {width : ℕ → ℕ}
    (hcurrent : ∀ inputLength,
      values inputLength idx ≤ width inputLength)
    (hvalue : ∀ inputLength, value ≤ width inputLength) :
    SpaceBoundByWidthAt (set idx value) initialSpace values width := by
  apply SpaceBoundByWidthAt.seq_internal
    (SpaceBoundByWidthAt.clear_internal idx hcurrent)
  apply SpaceBoundByWidthAt.addConst_internal
  intro inputLength
  simpa [clear] using hvalue inputLength

theorem SpaceBoundByWidthAt.seqList_internal
    (routines : List (BinaryRoutine n)) {initialSpace : ℕ → ℕ}
    {values : ℕ → BinaryValues n} {width : ℕ → ℕ}
    (hspace : SeqListSpaceBoundByWidthAt routines initialSpace values width) :
    SpaceBoundByWidthAt (seqList routines) initialSpace values width := by
  induction routines generalizing values with
  | nil =>
      simpa only [seqList] using
        (SpaceBoundByWidthAt.identity_internal (initialSpace := initialSpace)
          (values := values) (width := width))
  | cons routine routines ih =>
      simp only [SeqListSpaceBoundByWidthAt] at hspace
      simp only [seqList]
      exact SpaceBoundByWidthAt.seq_internal hspace.1 (ih hspace.2)

theorem SeqListSpaceBoundByWidthAt.append_internal
    (first second : List (BinaryRoutine n))
    {initialSpace : ℕ → ℕ} {values : ℕ → BinaryValues n}
    {width : ℕ → ℕ}
    (hfirst : SeqListSpaceBoundByWidthAt first initialSpace values width)
    (hsecond : SeqListSpaceBoundByWidthAt second initialSpace
      (fun inputLength => (seqList first).effect (values inputLength)) width) :
    SeqListSpaceBoundByWidthAt (first ++ second) initialSpace values width := by
  induction first generalizing values with
  | nil =>
      simpa [SeqListSpaceBoundByWidthAt, seqList, identity, emitBits] using
        hsecond
  | cons routine routines ih =>
      rcases hfirst with ⟨hroutine, hroutines⟩
      refine ⟨hroutine, ?_⟩
      apply ih hroutines
      simpa [seqList, seq] using hsecond

theorem SpaceBoundByWidthAt.repeatRoutine_of_invariant_internal
    (count : ℕ) (routine : BinaryRoutine n)
    (invariant : BinaryValues n → Prop) {initialSpace : ℕ → ℕ}
    {values : ℕ → BinaryValues n} {width : ℕ → ℕ}
    (hvalues : ∀ inputLength, invariant (values inputLength))
    (hspace : ∀ trajectory : ℕ → BinaryValues n,
      (∀ inputLength, invariant (trajectory inputLength)) →
        SpaceBoundByWidthAt routine initialSpace trajectory width)
    (heffect : ∀ current, invariant current →
      invariant (routine.effect current)) :
    SpaceBoundByWidthAt (repeatRoutine count routine) initialSpace values
      width := by
  induction count generalizing values with
  | zero =>
      simpa [repeatRoutine, seqList] using
        (SpaceBoundByWidthAt.identity_internal (initialSpace := initialSpace)
          (values := values) (width := width))
  | succ count ih =>
      rw [repeatRoutine, List.replicate_succ, seqList]
      apply SpaceBoundByWidthAt.seq_internal (hspace values hvalues)
      apply ih
      intro inputLength
      exact heffect (values inputLength) (hvalues inputLength)

theorem SpaceBoundByWidthAt.branchZero_internal
    {onZero onPositive : BinaryRoutine n} (idx : Fin n)
    {initialSpace : ℕ → ℕ} {values : ℕ → BinaryValues n}
    {width : ℕ → ℕ}
    (hzero : SpaceBoundByWidthAt onZero initialSpace values width)
    (hpositive : SpaceBoundByWidthAt onPositive initialSpace values width) :
    SpaceBoundByWidthAt (branchZero idx onZero onPositive) initialSpace values
      width := by
  obtain ⟨zeroConstant, hzero⟩ := hzero
  obtain ⟨positiveConstant, hpositive⟩ := hpositive
  refine ⟨zeroConstant + positiveConstant, fun inputLength => ?_⟩
  simp only [branchZero]
  apply max_le
  · exact (hzero inputLength).trans (by
      have hcoefficient : zeroConstant ≤ zeroConstant + positiveConstant := by
        omega
      have hscaled := Nat.mul_le_mul_right (width inputLength).size
        hcoefficient
      omega)
  · exact (hpositive inputLength).trans (by
      have hcoefficient : positiveConstant ≤
          zeroConstant + positiveConstant := by
        omega
      have hscaled := Nat.mul_le_mul_right (width inputLength).size
        hcoefficient
      omega)

theorem SpaceBoundByWidthAt.to_log_internal
    {routine : BinaryRoutine n} {initialSpace : ℕ → ℕ}
    {values : ℕ → BinaryValues n} {width : ℕ → ℕ}
    (hspace : SpaceBoundByWidthAt routine initialSpace values width)
    (hinitial : initialSpace =O (fun inputLength => Nat.log 2 inputLength))
    (p : Polynomial ℕ) (hwidth : ∀ inputLength,
      width inputLength ≤ p.eval inputLength) :
    SpaceBoundInLogAt routine initialSpace values := by
  obtain ⟨constant, hconstant⟩ := hspace
  apply SpaceBoundInLogAt.of_le_internal hconstant
  have hwidthLog := BigO.natSize_of_polynomial_bound p hwidth
  have hscaled := BigO.const_mul_left constant hwidthLog
  have hsum := BigO.add hinitial hscaled
  have hconstantLog := BigO.const_le_logTwo constant
  exact BigO.add hsum hconstantLog

theorem SpaceBoundInLogAt.emitBits_internal
    (word : List Bool) {initialSpace : ℕ → ℕ}
    {values : ℕ → BinaryValues n}
    (hinitial : initialSpace =O
      (fun inputLength => Nat.log 2 inputLength)) :
    SpaceBoundInLogAt (emitBits word) initialSpace values := by
  apply SpaceBoundByWidthAt.to_log_internal
    (width := fun _ => 0) (SpaceBoundByWidthAt.emitBits_internal word)
    hinitial (Polynomial.C 0)
  intro inputLength
  simp

theorem SpaceBoundInLogAt.identity_internal
    {initialSpace : ℕ → ℕ} {values : ℕ → BinaryValues n}
    (hinitial : initialSpace =O
      (fun inputLength => Nat.log 2 inputLength)) :
    SpaceBoundInLogAt identity initialSpace values := by
  exact SpaceBoundInLogAt.emitBits_internal [] hinitial

private theorem binaryForIterationSpaceMax_le_of_iteration
    (body : BinaryRoutine n) (counterIdx : Fin n) (initialSpace : ℕ)
    (initial : BinaryValues n) (bound : ℕ) : ∀ total,
    initialSpace ≤ bound →
      (∀ count, count < total →
        binaryForIterationSpace body counterIdx initialSpace initial count ≤
          bound) →
      binaryForIterationSpaceMax body counterIdx initialSpace initial total ≤
        bound := by
  intro total hinitial hiteration
  induction total with
  | zero =>
      simpa [binaryForIterationSpaceMax] using hinitial
  | succ total ih =>
      rw [binaryForIterationSpaceMax]
      apply max_le
      · exact ih fun count hcount => hiteration count (by omega)
      · exact hiteration total (by omega)

theorem BinaryForSpaceEnvelope.iterationSpaceMax_le_internal
    {body : BinaryRoutine n} {counterIdx limitIdx : Fin n}
    {initialSpace : ℕ} {initial : BinaryValues n} {bound : ℕ}
    (envelope : BinaryForSpaceEnvelope body counterIdx limitIdx initialSpace
      initial bound) :
    binaryForIterationSpaceMax body counterIdx initialSpace initial
        (binaryForCount counterIdx limitIdx initial) ≤ bound := by
  apply binaryForIterationSpaceMax_le_of_iteration body counterIdx initialSpace
    initial bound _ envelope.initialSpace_le
  intro count hcount
  rw [binaryForIterationSpace]
  exact max_le (envelope.bodySpace count hcount)
    (envelope.successorSpace count hcount)

theorem BinaryForSpaceEnvelope.binaryForSpace_le_internal
    {body : BinaryRoutine n} {counterIdx limitIdx : Fin n}
    {initialSpace : ℕ} {initial : BinaryValues n} {bound : ℕ}
    (envelope : BinaryForSpaceEnvelope body counterIdx limitIdx initialSpace
      initial bound) :
    binaryForSpace body counterIdx limitIdx initialSpace initial ≤ bound := by
  rw [binaryForSpace]
  exact max_le envelope.compareSpace envelope.iterationSpaceMax_le_internal

theorem BinaryForSpaceEnvelope.spaceBound_le_internal
    {body : BinaryRoutine n} {counterIdx limitIdx : Fin n}
    {initialSpace : ℕ} {initial : BinaryValues n} {bound : ℕ}
    (envelope : BinaryForSpaceEnvelope body counterIdx limitIdx initialSpace
      initial bound) :
    (binaryFor body counterIdx limitIdx).spaceBound initialSpace initial ≤
      bound :=
  envelope.binaryForSpace_le_internal

theorem SpaceBoundInLogAt.binaryFor_of_envelope_internal
    {body : BinaryRoutine n} {counterIdx limitIdx : Fin n}
    {initialSpace : ℕ → ℕ} {values : ℕ → BinaryValues n}
    {bound : ℕ → ℕ}
    (henvelope : ∀ inputLength,
      BinaryForSpaceEnvelope body counterIdx limitIdx
        (initialSpace inputLength) (values inputLength) (bound inputLength))
    (hbound : bound =O (fun inputLength => Nat.log 2 inputLength)) :
    SpaceBoundInLogAt (binaryFor body counterIdx limitIdx) initialSpace
      values := by
  apply SpaceBoundInLogAt.of_le_internal
  · intro inputLength
    exact (henvelope inputLength).spaceBound_le_internal
  · exact hbound

theorem SpaceBoundByWidthAt.binaryFor_of_envelope_internal
    {body : BinaryRoutine n} {counterIdx limitIdx : Fin n}
    {initialSpace : ℕ → ℕ} {values : ℕ → BinaryValues n}
    {width : ℕ → ℕ} (constant : ℕ)
    (henvelope : ∀ inputLength,
      BinaryForSpaceEnvelope body counterIdx limitIdx
        (initialSpace inputLength) (values inputLength)
        (initialSpace inputLength + constant * (width inputLength).size +
          constant)) :
    SpaceBoundByWidthAt (binaryFor body counterIdx limitIdx) initialSpace
      values width := by
  refine ⟨constant, fun inputLength => ?_⟩
  exact (henvelope inputLength).spaceBound_le_internal

theorem SpaceBoundByWidthAt.binaryFor_of_clamped_body_internal
    {body : BinaryRoutine n} {counterIdx limitIdx : Fin n}
    {initialSpace : ℕ → ℕ} {values : ℕ → BinaryValues n}
    {width : ℕ → ℕ}
    (hlimit : ∀ inputLength,
      values inputLength limitIdx ≤ width inputLength)
    (hcounter : ∀ inputLength count,
      count < binaryForCount counterIdx limitIdx (values inputLength) →
        (binaryForValues body counterIdx (values inputLength) count)
            counterIdx ≤ width inputLength)
    (hbody : SpaceBoundByWidthAt body
      (fun code => initialSpace (Nat.unpair code).1)
      (binaryForClampedValues body counterIdx limitIdx values)
      (fun code => width (Nat.unpair code).1)) :
    SpaceBoundByWidthAt (binaryFor body counterIdx limitIdx) initialSpace
      values width := by
  rcases hbody with ⟨constant, hbody⟩
  apply SpaceBoundByWidthAt.binaryFor_of_envelope_internal (constant + 2)
  intro inputLength
  refine
    { compareSpace := ?_
      initialSpace_le := by omega
      bodySpace := ?_
      successorSpace := ?_ }
  · have hsize := Nat.size_le_size (hlimit inputLength)
    have htwice := Nat.mul_le_mul_left 2 hsize
    have hcoefficient : 2 ≤ constant + 2 := by omega
    have hscaled := Nat.mul_le_mul_right (width inputLength).size
      hcoefficient
    simp only [TM.binaryForCompareTime]
    omega
  · intro count hcount
    have hcountLe : count ≤
        binaryForCount counterIdx limitIdx (values inputLength) - 1 := by
      omega
    have hbound := hbody (Nat.pair inputLength count)
    simp only [binaryForClampedValues, Nat.unpair_pair, hcountLe,
      min_eq_left] at hbound
    have hcoefficient : constant ≤ constant + 2 := by omega
    have hscaled := Nat.mul_le_mul_right (width inputLength).size
      hcoefficient
    exact hbound.trans (by omega)
  · intro count hcount
    have hcurrent := hcounter inputLength count hcount
    have hsize := Nat.size_le_size hcurrent
    have htime := TM.binarySuccTime_le
      ((binaryForValues body counterIdx (values inputLength) count)
        counterIdx)
    have htwice := Nat.mul_le_mul_left 2 hsize
    have hcoefficient : 2 ≤ constant + 2 := by omega
    have hscaled := Nat.mul_le_mul_right (width inputLength).size
      hcoefficient
    omega

end BinaryRoutine

end Complexity
