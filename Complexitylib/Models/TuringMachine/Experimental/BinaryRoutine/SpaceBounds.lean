/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Complexitylib.Models.TuringMachine.Experimental.BinaryRoutine.SpaceBounds.Defs
public import Complexitylib.Models.TuringMachine.Experimental.BinaryRoutine.SpaceBounds.Internal

/-!
# Compositional width bounds for binary routines

This module exposes pointwise width certificates for routine leaves,
sequential composition, fixed repetition, branches, and binary loops. Loop
certificates collapse the recursive maximum in `binaryForSpace` to four local
obligations, so the number of iterations does not appear additively in the
resulting auxiliary-space bound. A final polynomial width bound converts the
composed certificate to logarithmic space.
-/

@[expose] public section

namespace Complexity

namespace BinaryRoutine

/-- Updating one binary register preserves a common pointwise upper bound
when both the old vector and the replacement value satisfy that bound. -/
theorem values_update_le {values : BinaryValues n} {width value : ℕ}
    (index : Fin n) (hvalues : ∀ current, values current ≤ width)
    (hvalue : value ≤ width) :
    ∀ current, Function.update values index value current ≤ width := by
  intro current
  by_cases hcurrent : current = index
  · subst current
    simp [hvalue]
  · simpa [hcurrent] using hvalues current

/-- A pointwise logarithmic envelope proves logarithmic routine space along a
fixed input-indexed trajectory. -/
theorem SpaceBoundInLogAt.of_le
    {routine : BinaryRoutine n} {initialSpace : ℕ → ℕ}
    {values : ℕ → BinaryValues n} {bound : ℕ → ℕ}
    (hle : ∀ inputLength,
      routine.spaceBound (initialSpace inputLength) (values inputLength) ≤
        bound inputLength)
    (hbound : bound =O (fun inputLength => Nat.log 2 inputLength)) :
    SpaceBoundInLogAt routine initialSpace values :=
  SpaceBoundInLogAt.of_le_internal hle hbound

/-- Strengthening a precondition preserves an asymptotic space certificate. -/
theorem SpaceBoundInLogAt.restrict
    {routine : BinaryRoutine n} {requires : BinaryValues n → Prop}
    {initialSpace : ℕ → ℕ} {values : ℕ → BinaryValues n}
    (hspace : SpaceBoundInLogAt routine initialSpace values) :
    SpaceBoundInLogAt (routine.restrict requires) initialSpace values :=
  hspace.restrict_internal

/-- Sequential phases preserve logarithmic space when the second certificate
is stated along the first phase's exact pure effect. -/
theorem SpaceBoundInLogAt.seq
    {first second : BinaryRoutine n} {initialSpace : ℕ → ℕ}
    {values : ℕ → BinaryValues n}
    (hfirst : SpaceBoundInLogAt first initialSpace values)
    (hsecond : SpaceBoundInLogAt second initialSpace
      (fun inputLength => first.effect (values inputLength))) :
    SpaceBoundInLogAt (seq first second) initialSpace values :=
  hfirst.seq_internal hsecond

/-- Both branches sharing one logarithmic envelope make a zero branch
logarithmic, independently of which branch is selected at each input. -/
theorem SpaceBoundInLogAt.branchZero
    {onZero onPositive : BinaryRoutine n} (idx : Fin n)
    {initialSpace : ℕ → ℕ} {values : ℕ → BinaryValues n}
    (hzero : SpaceBoundInLogAt onZero initialSpace values)
    (hpositive : SpaceBoundInLogAt onPositive initialSpace values) :
    SpaceBoundInLogAt (branchZero idx onZero onPositive) initialSpace values :=
  SpaceBoundInLogAt.branchZero_internal idx hzero hpositive

/-- A logarithmic pointwise envelope for all reachable comparisons,
iterations, and successors proves logarithmic space for a binary loop. -/
theorem SpaceBoundInLogAt.binaryFor_of_envelope
    {body : BinaryRoutine n} {counterIdx limitIdx : Fin n}
    {initialSpace : ℕ → ℕ} {values : ℕ → BinaryValues n}
    {bound : ℕ → ℕ}
    (henvelope : ∀ inputLength,
      BinaryForSpaceEnvelope body counterIdx limitIdx
        (initialSpace inputLength) (values inputLength) (bound inputLength))
    (hbound : bound =O (fun inputLength => Nat.log 2 inputLength)) :
    SpaceBoundInLogAt (binaryFor body counterIdx limitIdx) initialSpace
      values :=
  SpaceBoundInLogAt.binaryFor_of_envelope_internal henvelope hbound

/-- Enlarging the controlling value preserves a pointwise width certificate. -/
theorem SpaceBoundByWidthAt.mono
    {routine : BinaryRoutine n} {initialSpace : ℕ → ℕ}
    {values : ℕ → BinaryValues n} {width width' : ℕ → ℕ}
    (hspace : SpaceBoundByWidthAt routine initialSpace values width)
    (hle : ∀ inputLength, width inputLength ≤ width' inputLength) :
    SpaceBoundByWidthAt routine initialSpace values width' :=
  hspace.mono_internal hle

/-- Strengthening a precondition preserves a pointwise width certificate. -/
theorem SpaceBoundByWidthAt.restrict
    {routine : BinaryRoutine n} {requires : BinaryValues n → Prop}
    {initialSpace : ℕ → ℕ} {values : ℕ → BinaryValues n}
    {width : ℕ → ℕ}
    (hspace : SpaceBoundByWidthAt routine initialSpace values width) :
    SpaceBoundByWidthAt (routine.restrict requires) initialSpace values
      width :=
  hspace.restrict_internal

/-- Fixed-word emission has a pointwise width certificate for every input
trajectory. -/
theorem SpaceBoundByWidthAt.emitBits
    (word : List Bool) {initialSpace : ℕ → ℕ}
    {values : ℕ → BinaryValues n} {width : ℕ → ℕ} :
    SpaceBoundByWidthAt (emitBits word) initialSpace values width :=
  SpaceBoundByWidthAt.emitBits_internal word

/-- The routine identity has a pointwise width certificate. -/
theorem SpaceBoundByWidthAt.identity
    {initialSpace : ℕ → ℕ} {values : ℕ → BinaryValues n}
    {width : ℕ → ℕ} :
    SpaceBoundByWidthAt identity initialSpace values width :=
  SpaceBoundByWidthAt.identity_internal

/-- Clearing a value bounded by the controlling width has a pointwise width
certificate. -/
theorem SpaceBoundByWidthAt.clear
    (idx : Fin n) {initialSpace : ℕ → ℕ}
    {values : ℕ → BinaryValues n} {width : ℕ → ℕ}
    (hvalue : ∀ inputLength, values inputLength idx ≤ width inputLength) :
    SpaceBoundByWidthAt (clear idx) initialSpace values width :=
  SpaceBoundByWidthAt.clear_internal idx hvalue

/-- Successor on a value bounded by the controlling width has a pointwise
width certificate. -/
theorem SpaceBoundByWidthAt.binarySucc
    (idx : Fin n) {initialSpace : ℕ → ℕ}
    {values : ℕ → BinaryValues n} {width : ℕ → ℕ}
    (hvalue : ∀ inputLength, values inputLength idx ≤ width inputLength) :
    SpaceBoundByWidthAt (binarySucc idx) initialSpace values width :=
  SpaceBoundByWidthAt.binarySucc_internal idx hvalue

/-- Predecessor has a pointwise width certificate when its exact positive
space argument is bounded by the controlling value. -/
theorem SpaceBoundByWidthAt.binaryPred
    (idx : Fin n) {initialSpace : ℕ → ℕ}
    {values : ℕ → BinaryValues n} {width : ℕ → ℕ}
    (hvalue : ∀ inputLength,
      values inputLength idx - 1 + 1 ≤ width inputLength) :
    SpaceBoundByWidthAt (binaryPred idx) initialSpace values width :=
  SpaceBoundByWidthAt.binaryPred_internal idx hvalue

/-- Copying two width-bounded values has a pointwise width certificate. -/
theorem SpaceBoundByWidthAt.binaryCopy
    (srcIdx dstIdx counterIdx : Fin n) {initialSpace : ℕ → ℕ}
    {values : ℕ → BinaryValues n} {width : ℕ → ℕ}
    (hsrc : ∀ inputLength,
      values inputLength srcIdx ≤ width inputLength)
    (hdst : ∀ inputLength,
      values inputLength dstIdx ≤ width inputLength) :
    SpaceBoundByWidthAt (binaryCopy srcIdx dstIdx counterIdx) initialSpace
      values width :=
  SpaceBoundByWidthAt.binaryCopy_internal srcIdx dstIdx counterIdx hsrc hdst

/-- Fixed addition has a pointwise width certificate when its result is
bounded by the controlling value. -/
theorem SpaceBoundByWidthAt.addConst
    (idx : Fin n) (constant : ℕ) {initialSpace : ℕ → ℕ}
    {values : ℕ → BinaryValues n} {width : ℕ → ℕ}
    (hvalue : ∀ inputLength,
      values inputLength idx + constant ≤ width inputLength) :
    SpaceBoundByWidthAt (addConst idx constant) initialSpace values width :=
  SpaceBoundByWidthAt.addConst_internal idx constant hvalue

/-- Setting a width-bounded value to another width-bounded value has a
pointwise width certificate. -/
theorem SpaceBoundByWidthAt.set
    (idx : Fin n) (value : ℕ) {initialSpace : ℕ → ℕ}
    {values : ℕ → BinaryValues n} {width : ℕ → ℕ}
    (hcurrent : ∀ inputLength,
      values inputLength idx ≤ width inputLength)
    (hvalue : ∀ inputLength, value ≤ width inputLength) :
    SpaceBoundByWidthAt (set idx value) initialSpace values width :=
  SpaceBoundByWidthAt.set_internal idx value hcurrent hvalue

/-- Preserved-source addition has a pointwise width certificate when its
source and result are bounded by the controlling value. -/
theorem SpaceBoundByWidthAt.add
    (srcIdx dstIdx counterIdx : Fin n) {initialSpace : ℕ → ℕ}
    {values : ℕ → BinaryValues n} {width : ℕ → ℕ}
    (hsrc : ∀ inputLength,
      values inputLength srcIdx ≤ width inputLength)
    (hsum : ∀ inputLength,
      values inputLength dstIdx + values inputLength srcIdx ≤
        width inputLength) :
    SpaceBoundByWidthAt (add srcIdx dstIdx counterIdx) initialSpace values
      width :=
  SpaceBoundByWidthAt.add_internal srcIdx dstIdx counterIdx hsrc hsum

/-- Multiply-add has a pointwise width certificate when both factors and the
largest addition intermediate are width-bounded. -/
theorem SpaceBoundByWidthAt.mulAdd
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
      initialSpace values width :=
  SpaceBoundByWidthAt.mulAdd_internal leftIdx rightIdx accIdx mulCounterIdx
    addCounterIdx hleft hright htotal

/-- Fixed-polynomial evaluation has a pointwise width certificate when its
explicit Horner-prefix cap is width-bounded. -/
theorem SpaceBoundByWidthAt.evalPolynomial
    (inputIdx resultIdx scratchIdx mulCounterIdx addCounterIdx : Fin n)
    (p : Polynomial ℕ) {initialSpace : ℕ → ℕ}
    {values : ℕ → BinaryValues n} {width : ℕ → ℕ}
    (hvalue : ∀ inputLength,
      2 * TM.binaryPolynomialValueCap p (values inputLength inputIdx) ≤
        width inputLength) :
    SpaceBoundByWidthAt
      (evalPolynomial inputIdx resultIdx scratchIdx mulCounterIdx
        addCounterIdx p) initialSpace values width :=
  SpaceBoundByWidthAt.evalPolynomial_internal inputIdx resultIdx scratchIdx
    mulCounterIdx addCounterIdx p hvalue

/-- Natural-code emission of a width-bounded value has a pointwise width
certificate. -/
theorem SpaceBoundByWidthAt.emitNatCode
    (counterIdx valueIdx : Fin n) {initialSpace : ℕ → ℕ}
    {values : ℕ → BinaryValues n} {width : ℕ → ℕ}
    (hvalue : ∀ inputLength,
      values inputLength valueIdx ≤ width inputLength) :
    SpaceBoundByWidthAt (emitNatCode counterIdx valueIdx) initialSpace values
      width :=
  SpaceBoundByWidthAt.emitNatCode_internal counterIdx valueIdx hvalue

/-- Raw-gate emission from two width-bounded references has a pointwise width
certificate. -/
theorem SpaceBoundByWidthAt.emitRawGate
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
      initialSpace values width :=
  SpaceBoundByWidthAt.emitRawGate_internal op negated₀ negated₁
    emitCounterIdx input₀Idx input₁Idx hinput₀ hinput₁

/-- Emitting and advancing one gate from width-bounded references and a
width-bounded frontier has a pointwise width certificate. -/
theorem SpaceBoundByWidthAt.emitRawGateStep
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
        input₀Idx input₁Idx) initialSpace values width :=
  SpaceBoundByWidthAt.emitRawGateStep_internal op negated₀ negated₁
    emitCounterIdx availableIdx input₀Idx input₁Idx havailable hinput₀ hinput₁

/-- Sequential pointwise width certificates compose along the first phase's
exact pure effect. -/
theorem SpaceBoundByWidthAt.seq
    {first second : BinaryRoutine n} {initialSpace : ℕ → ℕ}
    {values : ℕ → BinaryValues n} {width : ℕ → ℕ}
    (hfirst : SpaceBoundByWidthAt first initialSpace values width)
    (hsecond : SpaceBoundByWidthAt second initialSpace
      (fun inputLength => first.effect (values inputLength)) width) :
    SpaceBoundByWidthAt (seq first second) initialSpace values width :=
  hfirst.seq_internal hsecond

/-- A list of pointwise width certificates composes along its exact pure
prefix effects. -/
theorem SpaceBoundByWidthAt.seqList
    (routines : List (BinaryRoutine n)) {initialSpace : ℕ → ℕ}
    {values : ℕ → BinaryValues n} {width : ℕ → ℕ}
    (hspace : SeqListSpaceBoundByWidthAt routines initialSpace values width) :
    SpaceBoundByWidthAt (seqList routines) initialSpace values width :=
  SpaceBoundByWidthAt.seqList_internal routines hspace

/-- Width certificates for two routine lists compose when the second list is
certified along the first list's exact pure effect. -/
theorem SeqListSpaceBoundByWidthAt.append
    (first second : List (BinaryRoutine n))
    {initialSpace : ℕ → ℕ} {values : ℕ → BinaryValues n}
    {width : ℕ → ℕ}
    (hfirst : SeqListSpaceBoundByWidthAt first initialSpace values width)
    (hsecond : SeqListSpaceBoundByWidthAt second initialSpace
      (fun inputLength => (seqList first).effect (values inputLength)) width) :
    SeqListSpaceBoundByWidthAt (first ++ second) initialSpace values width :=
  SeqListSpaceBoundByWidthAt.append_internal first second hfirst hsecond

/-- Fixed repetition has a pointwise width certificate when one invariant
both supplies the body certificate and is preserved by its pure effect. -/
theorem SpaceBoundByWidthAt.repeatRoutine_of_invariant
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
      width :=
  SpaceBoundByWidthAt.repeatRoutine_of_invariant_internal count routine
    invariant hvalues hspace heffect

/-- Pointwise width certificates for both branches certify a zero branch. -/
theorem SpaceBoundByWidthAt.branchZero
    {onZero onPositive : BinaryRoutine n} (idx : Fin n)
    {initialSpace : ℕ → ℕ} {values : ℕ → BinaryValues n}
    {width : ℕ → ℕ}
    (hzero : SpaceBoundByWidthAt onZero initialSpace values width)
    (hpositive : SpaceBoundByWidthAt onPositive initialSpace values width) :
    SpaceBoundByWidthAt (branchZero idx onZero onPositive) initialSpace values
      width :=
  SpaceBoundByWidthAt.branchZero_internal idx hzero hpositive

/-- A polynomial upper bound on the controlling value turns a pointwise width
certificate into logarithmic space. -/
theorem SpaceBoundByWidthAt.to_log
    {routine : BinaryRoutine n} {initialSpace : ℕ → ℕ}
    {values : ℕ → BinaryValues n} {width : ℕ → ℕ}
    (hspace : SpaceBoundByWidthAt routine initialSpace values width)
    (hinitial : initialSpace =O (fun inputLength => Nat.log 2 inputLength))
    (p : Polynomial ℕ) (hwidth : ∀ inputLength,
      width inputLength ≤ p.eval inputLength) :
    SpaceBoundInLogAt routine initialSpace values :=
  hspace.to_log_internal hinitial p hwidth

/-- Fixed-word emission preserves logarithmic incoming space. -/
theorem SpaceBoundInLogAt.emitBits
    (word : List Bool) {initialSpace : ℕ → ℕ}
    {values : ℕ → BinaryValues n}
    (hinitial : initialSpace =O
      (fun inputLength => Nat.log 2 inputLength)) :
    SpaceBoundInLogAt (emitBits word) initialSpace values :=
  SpaceBoundInLogAt.emitBits_internal word hinitial

/-- The routine identity preserves logarithmic incoming space. -/
theorem SpaceBoundInLogAt.identity
    {initialSpace : ℕ → ℕ} {values : ℕ → BinaryValues n}
    (hinitial : initialSpace =O
      (fun inputLength => Nat.log 2 inputLength)) :
    SpaceBoundInLogAt identity initialSpace values :=
  SpaceBoundInLogAt.identity_internal hinitial

/-- A pointwise loop envelope of the standard width-controlled form certifies
the complete binary loop without exposing its recursive maximum. -/
theorem SpaceBoundByWidthAt.binaryFor_of_envelope
    {body : BinaryRoutine n} {counterIdx limitIdx : Fin n}
    {initialSpace : ℕ → ℕ} {values : ℕ → BinaryValues n}
    {width : ℕ → ℕ} (constant : ℕ)
    (henvelope : ∀ inputLength,
      BinaryForSpaceEnvelope body counterIdx limitIdx
        (initialSpace inputLength) (values inputLength)
        (initialSpace inputLength + constant * (width inputLength).size +
          constant)) :
    SpaceBoundByWidthAt (binaryFor body counterIdx limitIdx) initialSpace
      values width :=
  SpaceBoundByWidthAt.binaryFor_of_envelope_internal constant henvelope

/-- A width certificate over the canonical paired-and-clamped body trajectory
lifts to the complete binary loop. The limit and every reachable counter value
must fit the same width; the resulting constant is uniform in both the input
index and the loop iteration. -/
theorem SpaceBoundByWidthAt.binaryFor_of_clamped_body
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
      values width :=
  SpaceBoundByWidthAt.binaryFor_of_clamped_body_internal hlimit hcounter hbody

/-- A pointwise envelope bounds the recursive maximum over all reachable
iterations. -/
theorem BinaryForSpaceEnvelope.iterationSpaceMax_le
    {body : BinaryRoutine n} {counterIdx limitIdx : Fin n}
    {initialSpace : ℕ} {initial : BinaryValues n} {bound : ℕ}
    (envelope : BinaryForSpaceEnvelope body counterIdx limitIdx initialSpace
      initial bound) :
    binaryForIterationSpaceMax body counterIdx initialSpace initial
        (binaryForCount counterIdx limitIdx initial) ≤ bound :=
  envelope.iterationSpaceMax_le_internal

/-- A pointwise envelope bounds the complete comparison-plus-iteration space
formula of a binary count-up loop. -/
theorem BinaryForSpaceEnvelope.binaryForSpace_le
    {body : BinaryRoutine n} {counterIdx limitIdx : Fin n}
    {initialSpace : ℕ} {initial : BinaryValues n} {bound : ℕ}
    (envelope : BinaryForSpaceEnvelope body counterIdx limitIdx initialSpace
      initial bound) :
    binaryForSpace body counterIdx limitIdx initialSpace initial ≤ bound :=
  envelope.binaryForSpace_le_internal

/-- A pointwise envelope directly bounds the advertised space budget of the
corresponding proof-carrying binary loop. -/
theorem BinaryForSpaceEnvelope.spaceBound_le
    {body : BinaryRoutine n} {counterIdx limitIdx : Fin n}
    {initialSpace : ℕ} {initial : BinaryValues n} {bound : ℕ}
    (envelope : BinaryForSpaceEnvelope body counterIdx limitIdx initialSpace
      initial bound) :
    (binaryFor body counterIdx limitIdx).spaceBound initialSpace initial ≤
      bound :=
  envelope.spaceBound_le_internal

end BinaryRoutine

end Complexity
