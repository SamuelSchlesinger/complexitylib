/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.Basis.DeMorgan.Expression
public import Complexitylib.Algebraic.MassProduction.BinaryEncoding

/-!
# Fixed-divisor Boolean division

This module implements one transition of binary long division by a fixed
positive natural number.  The remainder is represented one-hot.  For a target
remainder `s`, the only possible pre-transition naturals are `s` and
`divisor + s`; consequently every next-state bit is the OR of exactly two
branches.  This gives a transition circuit linear in the divisor and avoids
introducing any finite-enumeration instances.
-/

@[expose] public section

namespace Algebraic
namespace MassProduction
namespace FixedDivision

/-- Natural value of one Boolean digit. -/
def boolNat : Bool -> Nat
  | false => 0
  | true => 1

/-- A Boolean digit regarded as an element of `Fin 2`. -/
def boolFin : Bool -> Fin 2
  | false => 0
  | true => 1

@[simp] theorem boolFin_val (bit : Bool) :
    (boolFin bit).val = boolNat bit := by
  cases bit <;> rfl

/-- The natural represented by a fixed-width little-endian bit vector. -/
def bitVectorIndex
    (bits : Fin width -> Bool) : Fin (2 ^ width) :=
  finFunctionFinEquiv fun bit => boolFin (bits bit)

theorem bitVectorIndex_val
    (bits : Fin width -> Bool) :
    (bitVectorIndex bits).val =
      ∑ bit : Fin width, boolNat (bits bit) * 2 ^ bit.val := by
  rw [bitVectorIndex, finFunctionFinEquiv_apply]
  apply Finset.sum_congr rfl
  intro bit _member
  rw [boolFin_val]

/-- Prepending a little-endian bit performs one binary `bit` step. -/
theorem bitVectorIndex_cons
    (bit : Bool)
    (bits : Fin width -> Bool) :
    (bitVectorIndex (Fin.cons bit bits)).val =
      boolNat bit + 2 * (bitVectorIndex bits).val := by
  rw [bitVectorIndex_val, bitVectorIndex_val, Fin.sum_univ_succ]
  simp only [Fin.cons_zero, Fin.val_zero, pow_zero, mul_one,
    Fin.cons_succ, Fin.val_succ, pow_succ]
  rw [Finset.mul_sum]
  apply congrArg (boolNat bit + ·)
  apply Finset.sum_congr rfl
  intro index _member
  ring

/-- One binary long-division transition before reducing modulo the divisor. -/
def transitionRaw (state : Fin divisor) (bit : Bool) : Nat :=
  2 * state.val + boolNat bit

theorem transitionRaw_lt_two_mul
    (state : Fin divisor)
    (bit : Bool) :
    transitionRaw state bit < 2 * divisor := by
  unfold transitionRaw
  have := state.isLt
  cases bit
  · simp [boolNat]
  · simp [boolNat]
    omega

/-- Next remainder, using the fact that one transition is below twice the
positive divisor and therefore needs at most one subtraction. -/
def transitionState
    (_divisorPositive : 0 < divisor)
    (state : Fin divisor)
    (bit : Bool) : Fin divisor :=
  if below : transitionRaw state bit < divisor then
    ⟨transitionRaw state bit, below⟩
  else
    ⟨transitionRaw state bit - divisor, by
      have := transitionRaw_lt_two_mul state bit
      omega⟩

@[simp] theorem transitionState_val
    (divisorPositive : 0 < divisor)
    (state : Fin divisor)
    (bit : Bool) :
    (transitionState divisorPositive state bit).val =
      if transitionRaw state bit < divisor then
        transitionRaw state bit
      else transitionRaw state bit - divisor := by
  unfold transitionState
  split <;> rfl

/-- The quotient digit emitted by one transition. -/
def transitionQuotientBit
    (state : Fin divisor)
    (bit : Bool) : Bool :=
  decide (divisor <= transitionRaw state bit)

/-- One transition decomposes its raw value into the emitted binary quotient
digit and the next remainder. -/
theorem transition_decompose
    (divisorPositive : 0 < divisor)
    (state : Fin divisor)
    (bit : Bool) :
    transitionRaw state bit =
      boolNat (transitionQuotientBit state bit) * divisor +
        (transitionState divisorPositive state bit).val := by
  unfold transitionQuotientBit
  rw [transitionState_val]
  split <;> rename_i below
  · have notLe : ¬divisor <= transitionRaw state bit := by omega
    simp [notLe, boolNat]
  · have divisorLe : divisor <= transitionRaw state bit := by omega
    simp [divisorLe, boolNat]

/-- Every raw value below twice the divisor has a predecessor-state half. -/
def rawState
    (_divisorPositive : 0 < divisor)
    (raw : Fin (2 * divisor)) : Fin divisor :=
  ⟨raw.val / 2, by
    have rawBound := raw.isLt
    exact (Nat.div_lt_iff_lt_mul (by omega : 0 < 2)).mpr (by
      simpa [Nat.mul_comm] using rawBound)⟩

/-- Low binary digit of a raw transition value. -/
def rawBit (raw : Fin (2 * divisor)) : Bool :=
  Nat.bodd raw.val

theorem raw_reconstruct
    (divisorPositive : 0 < divisor)
    (raw : Fin (2 * divisor)) :
    transitionRaw (rawState divisorPositive raw) (rawBit raw) = raw.val := by
  unfold transitionRaw rawState rawBit boolNat
  have reconstructed := Nat.bit_bodd_div2 raw.val
  cases h : Nat.bodd raw.val <;> simp [Nat.bit, h] at reconstructed ⊢
  · omega
  · omega

/-- The lower raw representative of a target next remainder. -/
def lowerRaw
    (divisorPositive : 0 < divisor)
    (target : Fin divisor) : Fin (2 * divisor) :=
  ⟨target.val, by omega⟩

/-- The upper raw representative of a target next remainder. -/
def upperRaw
    (_divisorPositive : 0 < divisor)
    (target : Fin divisor) : Fin (2 * divisor) :=
  ⟨divisor + target.val, by omega⟩

/-- State wires occupy the prefix of a `(state..., bit)` transition input. -/
def stateInputIndex
    (state : Fin divisor) : Fin (divisor + 1) :=
  Fin.castAdd 1 state

/-- The runtime bit is the final transition input. -/
def bitInputIndex (divisor : Nat) : Fin (divisor + 1) :=
  Fin.last divisor

/-- An input literal which is true exactly when the runtime bit has the
hardwired requested value. -/
def bitLiteralExpression
    (wanted : Bool) : DeMorgan.Expression (divisor + 1) :=
  if wanted then
    .input (bitInputIndex divisor)
  else
    .not (.input (bitInputIndex divisor))

/-- One predecessor branch for a raw transition value. -/
def branchExpression
    (divisorPositive : 0 < divisor)
    (raw : Fin (2 * divisor)) : DeMorgan.Expression (divisor + 1) :=
  .and (.input (stateInputIndex (rawState divisorPositive raw)))
    (bitLiteralExpression (divisor := divisor) (rawBit raw))

/-- One next-state bit is the OR of its lower and upper predecessors. -/
def nextStateExpression
    (divisorPositive : 0 < divisor)
    (target : Fin divisor) : DeMorgan.Expression (divisor + 1) :=
  .or (branchExpression divisorPositive
      (lowerRaw divisorPositive target))
    (branchExpression divisorPositive
      (upperRaw divisorPositive target))

/-- The emitted quotient bit is the OR of all upper-predecessor branches. -/
def quotientExpression
    (divisorPositive : 0 < divisor) :
    DeMorgan.Expression (divisor + 1) :=
  DeMorgan.Expression.finOr divisor fun target =>
    branchExpression divisorPositive (upperRaw divisorPositive target)

/-- Canonical transition input with a one-hot current remainder. -/
def oneHotTransitionInput
    (current : Fin divisor)
    (bit : Bool) : Fin (divisor + 1) -> Bool :=
  Fin.append (fun state => decide (state = current)) (fun _ => bit)

@[simp] theorem oneHotTransitionInput_state
    (current state : Fin divisor)
    (bit : Bool) :
    oneHotTransitionInput current bit (stateInputIndex state) =
      decide (state = current) := by
  simp [oneHotTransitionInput, stateInputIndex]

@[simp] theorem oneHotTransitionInput_bit
    (current : Fin divisor)
    (bit : Bool) :
    oneHotTransitionInput current bit (bitInputIndex divisor) = bit := by
  rw [oneHotTransitionInput, bitInputIndex]
  rw [show Fin.last divisor = Fin.natAdd divisor (0 : Fin 1) by
    apply Fin.ext
    simp]
  rw [Fin.append_right]

theorem bitLiteralExpression_eval_oneHot
    (_divisorPositive : 0 < divisor)
    (current : Fin divisor)
    (bit wanted : Bool) :
    (bitLiteralExpression (divisor := divisor) wanted).eval
        (oneHotTransitionInput current bit) =
      decide (bit = wanted) := by
  cases wanted <;> cases bit <;>
    simp [bitLiteralExpression, DeMorgan.Expression.eval]

theorem rawState_rawBit_eq_iff
    (divisorPositive : 0 < divisor)
    (raw : Fin (2 * divisor))
    (current : Fin divisor)
    (bit : Bool) :
    rawState divisorPositive raw = current ∧ rawBit raw = bit <->
      raw.val = transitionRaw current bit := by
  constructor
  · rintro ⟨stateEqual, bitEqual⟩
    rw [← stateEqual, ← bitEqual]
    exact (raw_reconstruct divisorPositive raw).symm
  · intro rawEqual
    have stateValEqual : raw.val / 2 = current.val := by
      rw [rawEqual]
      unfold transitionRaw
      cases bit
      · simp [boolNat]
      · simp [boolNat]
        omega
    have bitEqual : rawBit raw = bit := by
      unfold rawBit
      rw [rawEqual]
      unfold transitionRaw
      cases bit <;> simp [boolNat]
    exact ⟨Fin.ext stateValEqual, bitEqual⟩

theorem branchExpression_eval_oneHot_eq_true_iff
    (divisorPositive : 0 < divisor)
    (raw : Fin (2 * divisor))
    (current : Fin divisor)
    (bit : Bool) :
    (branchExpression divisorPositive raw).eval
        (oneHotTransitionInput current bit) = true <->
      raw.val = transitionRaw current bit := by
  simp only [branchExpression, DeMorgan.Expression.eval, Bool.and_eq_true]
  rw [
    oneHotTransitionInput_state,
    bitLiteralExpression_eval_oneHot divisorPositive]
  simp only [decide_eq_true_eq]
  constructor
  · rintro ⟨stateEqual, bitEqual⟩
    exact (rawState_rawBit_eq_iff divisorPositive raw current bit).mp
      ⟨stateEqual, bitEqual.symm⟩
  · intro rawEqual
    have pair :=
      (rawState_rawBit_eq_iff divisorPositive raw current bit).mpr rawEqual
    exact ⟨pair.1, pair.2.symm⟩

theorem nextStateExpression_eval_oneHot
    (divisorPositive : 0 < divisor)
    (current target : Fin divisor)
    (bit : Bool) :
    (nextStateExpression divisorPositive target).eval
        (oneHotTransitionInput current bit) =
      decide (target = transitionState divisorPositive current bit) := by
  apply Bool.eq_iff_iff.mpr
  rw [nextStateExpression, DeMorgan.Expression.eval, Bool.or_eq_true,
    branchExpression_eval_oneHot_eq_true_iff,
    branchExpression_eval_oneHot_eq_true_iff]
  simp only [decide_eq_true_eq]
  simp only [lowerRaw, upperRaw, Fin.ext_iff]
  rw [transitionState_val]
  split <;> omega

theorem quotientExpression_eval_oneHot
    (divisorPositive : 0 < divisor)
    (current : Fin divisor)
    (bit : Bool) :
    (quotientExpression divisorPositive).eval
        (oneHotTransitionInput current bit) =
      transitionQuotientBit current bit := by
  rw [quotientExpression, DeMorgan.Expression.finOr_eval]
  apply Bool.eq_iff_iff.mpr
  rw [DeMorgan.Expression.finOrValue_eq_true_iff]
  simp_rw [branchExpression_eval_oneHot_eq_true_iff]
  unfold transitionQuotientBit
  simp only [decide_eq_true_eq]
  constructor
  · rintro ⟨target, equal⟩
    change divisor + target.val = transitionRaw current bit at equal
    omega
  · intro divisorLe
    have rawBound := transitionRaw_lt_two_mul current bit
    let target : Fin divisor :=
      ⟨transitionRaw current bit - divisor, by omega⟩
    refine ⟨target, ?_⟩
    change divisor + (transitionRaw current bit - divisor) =
      transitionRaw current bit
    omega

/-- One expression for each next-state wire, followed by the quotient bit. -/
def transitionOutputExpression
    (divisorPositive : 0 < divisor)
    (output : Fin (divisor + 1)) :
    DeMorgan.Expression (divisor + 1) :=
  Fin.lastCases (quotientExpression divisorPositive)
    (fun target => nextStateExpression divisorPositive target) output

/-- Emitted gate count of the complete transition circuit. -/
@[reducible] def transitionGateCount
    (divisorPositive : 0 < divisor) : Nat :=
  ∑ output, (transitionOutputExpression divisorPositive output).gateCount

/-- One verified long-division transition. -/
def transitionCircuit
    (divisorPositive : 0 < divisor) :
    Circuit DeMorgan.signature (divisor + 1) (divisor + 1) :=
  Circuit.parallelFin (divisor + 1)
    (fun output =>
      (transitionOutputExpression divisorPositive output).circuit)

@[simp] theorem transitionCircuit_size
    (divisorPositive : 0 < divisor) :
    (transitionCircuit divisorPositive).size =
      transitionGateCount divisorPositive := by
  simp [transitionCircuit, transitionGateCount]

@[simp] theorem transitionCircuit_eval_state
    (divisorPositive : 0 < divisor)
    (current target : Fin divisor)
    (bit : Bool) :
    (transitionCircuit divisorPositive).eval DeMorgan.interpretation
        (oneHotTransitionInput current bit) target.castSucc =
      decide (target = transitionState divisorPositive current bit) := by
  rw [transitionCircuit, Circuit.eval_parallelFin,
    DeMorgan.Expression.circuit_eval]
  simp [transitionOutputExpression,
    nextStateExpression_eval_oneHot]

@[simp] theorem transitionCircuit_eval_quotient
    (divisorPositive : 0 < divisor)
    (current : Fin divisor)
    (bit : Bool) :
    (transitionCircuit divisorPositive).eval DeMorgan.interpretation
        (oneHotTransitionInput current bit) (Fin.last divisor) =
      transitionQuotientBit current bit := by
  rw [transitionCircuit, Circuit.eval_parallelFin,
    DeMorgan.Expression.circuit_eval]
  simp [transitionOutputExpression, quotientExpression_eval_oneHot]

/-! ## Unrolling transitions over a fixed-width input -/

/-- Initial one-hot remainder state, before any input bit is read. -/
def initialStateExpression
    (divisorPositive : 0 < divisor)
    (state : Fin divisor) : DeMorgan.Expression inputWidth :=
  .constant (decide (state = (⟨0, divisorPositive⟩ : Fin divisor)))

/-- Emitted gate count of the free-cost initial constant vector. -/
@[reducible] def initialStateGateCount
    (inputWidth : Nat)
    (divisorPositive : 0 < divisor) : Nat :=
  ∑ state, (initialStateExpression
    (inputWidth := inputWidth) divisorPositive state).gateCount

/-- Initial one-hot state as a circuit on the eventual input namespace. -/
def initialStateCircuit
    (inputWidth : Nat)
    (divisorPositive : 0 < divisor) :
    Circuit DeMorgan.signature inputWidth
      divisor :=
  Circuit.parallelFin divisor
    (fun state =>
      (initialStateExpression
        (inputWidth := inputWidth) divisorPositive state).circuit)

@[simp] theorem initialStateCircuit_size
    (inputWidth : Nat)
    (divisorPositive : 0 < divisor) :
    (initialStateCircuit inputWidth divisorPositive).size =
      initialStateGateCount (inputWidth := inputWidth) divisorPositive := by
  simp [initialStateCircuit, initialStateGateCount]

@[simp] theorem initialStateCircuit_eval
    (input : Fin inputWidth -> Bool)
    (divisorPositive : 0 < divisor)
    (state : Fin divisor) :
    (initialStateCircuit inputWidth divisorPositive).eval
        DeMorgan.interpretation input state =
      decide (state = (⟨0, divisorPositive⟩ : Fin divisor)) := by
  rw [initialStateCircuit, Circuit.eval_parallelFin,
    DeMorgan.Expression.circuit_eval]
  rfl

/-- Gate count after a fixed number of unrolled transition rounds. -/
@[reducible] def prefixGateCount
    (inputWidth : Nat)
    (divisorPositive : 0 < divisor) : Nat -> Nat
  | 0 => initialStateGateCount
      (inputWidth := inputWidth) divisorPositive
  | rounds + 1 =>
      prefixGateCount inputWidth divisorPositive rounds +
        transitionGateCount divisorPositive

/-- Input bit processed at the next big-endian round. -/
def roundInputIndex
    (inputWidth rounds : Nat)
    (roundFits : rounds + 1 <= inputWidth) : Fin inputWidth :=
  Fin.rev ⟨rounds, by omega⟩

/-- The zero-gate circuit selecting the next original input bit. -/
def roundInputCircuit
    (inputWidth rounds : Nat)
    (roundFits : rounds + 1 <= inputWidth) :
    Circuit DeMorgan.signature inputWidth 1 :=
  (Circuit.id DeMorgan.signature inputWidth).mapOutputs
    (fun _ => roundInputIndex inputWidth rounds roundFits)

@[simp] theorem roundInputCircuit_eval
    (input : Fin inputWidth -> Bool)
    (roundFits : rounds + 1 <= inputWidth) :
    (roundInputCircuit inputWidth rounds roundFits).eval
        DeMorgan.interpretation input 0 =
      input (roundInputIndex inputWidth rounds roundFits) := by
  simp [roundInputCircuit]

/-- Reorder `(state..., prior quotient..., current bit)` into the transition
circuit's `(state..., current bit)` input. -/
def transitionRoundInputIndex
    (divisor rounds : Nat) :
    Fin (divisor + 1) -> Fin ((divisor + rounds) + 1) :=
  Fin.lastCases (Fin.last (divisor + rounds))
    (fun state => ⟨state.val, by omega⟩)

@[simp] theorem transitionRoundInputIndex_state
    (state : Fin divisor) :
    transitionRoundInputIndex divisor rounds state.castSucc =
      ⟨state.val, by omega⟩ := by
  simp [transitionRoundInputIndex]

@[simp] theorem transitionRoundInputIndex_bit :
    transitionRoundInputIndex divisor rounds (Fin.last divisor) =
      Fin.last (divisor + rounds) := by
  simp [transitionRoundInputIndex]

theorem transitionRoundInput_oneHot
    (current : Fin divisor)
    (priorQuotient : Fin rounds -> Bool)
    (bit : Bool) :
    (Fin.append
        (Fin.append (fun state => decide (state = current)) priorQuotient)
        (fun _ => bit)) ∘
        transitionRoundInputIndex divisor rounds =
      oneHotTransitionInput current bit := by
  funext inputIndex
  induction inputIndex using Fin.lastCases with
  | last =>
      rw [Function.comp_apply, transitionRoundInputIndex_bit]
      rw [show Fin.last (divisor + rounds) =
          Fin.natAdd (divisor + rounds) (0 : Fin 1) by
        apply Fin.ext
        simp]
      rw [Fin.append_right]
      exact (oneHotTransitionInput_bit current bit).symm
  | cast state =>
      rw [Function.comp_apply, transitionRoundInputIndex_state]
      rw [show (⟨state.val, by omega⟩ : Fin ((divisor + rounds) + 1)) =
          Fin.castAdd 1 (Fin.castAdd rounds state) by
        apply Fin.ext
        rfl]
      rw [Fin.append_left, Fin.append_left]
      exact (oneHotTransitionInput_state current state bit).symm

/-- Select a retained little-endian quotient bit from the middle block. -/
def retainedQuotientInputIndex
    (divisor rounds : Nat)
    (bit : Fin rounds) : Fin ((divisor + rounds) + 1) :=
  ⟨divisor + bit.val, by omega⟩

/-- Update the remainder and prepend the new least-significant quotient bit,
while retaining all earlier quotient bits for free. -/
def divisionStepCircuit
    (divisorPositive : 0 < divisor)
    (rounds : Nat) :
    Circuit DeMorgan.signature ((divisor + rounds) + 1) (divisor + (rounds + 1)) :=
  let transition :=
    (transitionCircuit divisorPositive).mapInputs
      (transitionRoundInputIndex divisor rounds)
  let retained : Circuit DeMorgan.signature ((divisor + rounds) + 1) rounds :=
    (Circuit.id DeMorgan.signature ((divisor + rounds) + 1)).mapOutputs
      (retainedQuotientInputIndex divisor rounds)
  (transition.parallel retained).castCounts rfl (by omega)

@[simp] theorem divisionStepCircuit_size
    (divisorPositive : 0 < divisor)
    (rounds : Nat) :
    (divisionStepCircuit divisorPositive rounds).size =
      transitionGateCount divisorPositive := by
  simp [divisionStepCircuit, transitionGateCount]

theorem divisionStepCircuit_eval_state
    (divisorPositive : 0 < divisor)
    (current target : Fin divisor)
    (priorQuotient : Fin rounds -> Bool)
    (bit : Bool) :
    (divisionStepCircuit divisorPositive rounds).eval
        DeMorgan.interpretation
        (Fin.append
          (Fin.append (fun state => decide (state = current)) priorQuotient)
          (fun _ => bit))
        (Fin.castAdd (rounds + 1) target) =
      decide (target = transitionState divisorPositive current bit) := by
  rw [divisionStepCircuit, Circuit.eval_castCounts]
  simp only [Fin.cast_refl, Function.comp_id, Circuit.eval_parallel,
    Circuit.eval_mapInputs]
  rw [show Fin.cast (by omega : (divisor + 1) + rounds =
        divisor + (rounds + 1)).symm
        (Fin.castAdd (rounds + 1) target) =
      Fin.castAdd rounds target.castSucc by
    apply Fin.ext
    rfl]
  rw [Fin.append_left]
  rw [transitionRoundInput_oneHot]
  exact transitionCircuit_eval_state divisorPositive current target bit

theorem divisionStepCircuit_eval_newQuotient
    (divisorPositive : 0 < divisor)
    (current : Fin divisor)
    (priorQuotient : Fin rounds -> Bool)
    (bit : Bool) :
    (divisionStepCircuit divisorPositive rounds).eval
        DeMorgan.interpretation
        (Fin.append
          (Fin.append (fun state => decide (state = current)) priorQuotient)
          (fun _ => bit))
        (Fin.natAdd divisor (0 : Fin (rounds + 1))) =
      transitionQuotientBit current bit := by
  rw [divisionStepCircuit, Circuit.eval_castCounts]
  simp only [Fin.cast_refl, Function.comp_id, Circuit.eval_parallel,
    Circuit.eval_mapInputs]
  rw [show Fin.cast (by omega : (divisor + 1) + rounds =
        divisor + (rounds + 1)).symm
        (Fin.natAdd divisor (0 : Fin (rounds + 1))) =
      Fin.castAdd rounds (Fin.last divisor) by
    apply Fin.ext
    simp]
  rw [Fin.append_left]
  rw [transitionRoundInput_oneHot]
  exact transitionCircuit_eval_quotient divisorPositive current bit

theorem divisionStepCircuit_eval_priorQuotient
    (divisorPositive : 0 < divisor)
    (current : Fin divisor)
    (priorQuotient : Fin rounds -> Bool)
    (bit : Bool)
    (priorBit : Fin rounds) :
    (divisionStepCircuit divisorPositive rounds).eval
        DeMorgan.interpretation
        (Fin.append
          (Fin.append (fun state => decide (state = current)) priorQuotient)
          (fun _ => bit))
        (Fin.natAdd divisor priorBit.succ) =
      priorQuotient priorBit := by
  rw [divisionStepCircuit, Circuit.eval_castCounts]
  simp only [Fin.cast_refl, Function.comp_id, Circuit.eval_parallel,
    Circuit.eval_mapOutputs, Circuit.eval_id]
  rw [show Fin.cast (by omega : (divisor + 1) + rounds =
        divisor + (rounds + 1)).symm
        (Fin.natAdd divisor priorBit.succ) =
      Fin.natAdd (divisor + 1) priorBit by
    apply Fin.ext
    simp
    omega]
  rw [Fin.append_right]
  change
    Fin.append
      (Fin.append (fun state => decide (state = current)) priorQuotient)
      (fun _ => bit)
      (retainedQuotientInputIndex divisor rounds priorBit) = _
  rw [show retainedQuotientInputIndex divisor rounds priorBit =
      Fin.castAdd 1 (Fin.natAdd divisor priorBit) by
    apply Fin.ext
    rfl]
  rw [Fin.append_left, Fin.append_right]

/-- Remainder after a prefix of the big-endian input stream. -/
def streamState
    (divisorPositive : 0 < divisor)
    (input : Fin inputWidth -> Bool) :
    (rounds : Nat) -> rounds <= inputWidth -> Fin divisor
  | 0, _ => ⟨0, divisorPositive⟩
  | rounds + 1, fits =>
      transitionState divisorPositive
        (streamState divisorPositive input rounds (by omega))
        (input (roundInputIndex inputWidth rounds fits))

/-- Little-endian quotient bits accumulated after a stream prefix. -/
def streamQuotientBits
    (divisorPositive : 0 < divisor)
    (input : Fin inputWidth -> Bool) :
    (rounds : Nat) -> (fits : rounds <= inputWidth) -> Fin rounds -> Bool
  | 0, _, bit => Fin.elim0 bit
  | rounds + 1, fits, bit =>
      Fin.cases
        (transitionQuotientBit
          (streamState divisorPositive input rounds (by omega))
          (input (roundInputIndex inputWidth rounds fits)))
        (streamQuotientBits divisorPositive input rounds (by omega)) bit

/-- Gate count recurrence is the initial constant vector plus one transition
per processed bit. -/
noncomputable def divisionPrefixCircuit
    (inputWidth : Nat)
    (divisorPositive : 0 < divisor) :
    (rounds : Nat) -> (fits : rounds <= inputWidth) ->
    Circuit DeMorgan.signature inputWidth
      (divisor + rounds)
  | 0, _ =>
      (initialStateCircuit inputWidth divisorPositive).castCounts rfl
        (Nat.add_zero divisor).symm
  | rounds + 1, fits => by
      have priorFits : rounds <= inputWidth := by omega
      let prior := divisionPrefixCircuit inputWidth divisorPositive
        rounds priorFits
      let currentBit := roundInputCircuit inputWidth rounds fits
      let priorWithBit := prior.parallel currentBit
      exact ((divisionStepCircuit divisorPositive rounds).comp
        priorWithBit).castCounts rfl rfl

/-- The unrolled circuit emits exactly `prefixGateCount` gates. -/
@[simp] theorem divisionPrefixCircuit_size
    (inputWidth : Nat)
    (divisorPositive : 0 < divisor)
    (rounds : Nat)
    (fits : rounds <= inputWidth) :
    (divisionPrefixCircuit inputWidth divisorPositive rounds fits).size =
      prefixGateCount inputWidth divisorPositive rounds := by
  induction rounds with
  | zero =>
      simp [divisionPrefixCircuit, prefixGateCount, initialStateCircuit,
        initialStateGateCount]
  | succ rounds inductionHypothesis =>
      simp [divisionPrefixCircuit, prefixGateCount,
        inductionHypothesis (by omega), divisionStepCircuit, transitionCircuit,
        transitionGateCount, roundInputCircuit]

/-- The unrolled circuit exposes the exact one-hot remainder and accumulated
little-endian quotient after every processed prefix. -/
theorem divisionPrefixCircuit_eval
    (divisorPositive : 0 < divisor)
    (input : Fin inputWidth -> Bool)
    (rounds : Nat)
    (fits : rounds <= inputWidth) :
    (divisionPrefixCircuit inputWidth divisorPositive rounds fits).eval
        DeMorgan.interpretation input =
      Fin.append
        (fun state =>
          decide (state = streamState divisorPositive input rounds fits))
        (streamQuotientBits divisorPositive input rounds fits) := by
  induction rounds with
  | zero =>
      funext output
      rw [divisionPrefixCircuit, Circuit.eval_castCounts]
      simp only [Fin.cast_refl, Function.comp_id]
      rw [initialStateCircuit_eval]
      simp only [streamState]
      let state : Fin divisor := Fin.cast (Nat.add_zero divisor) output
      rw [show output = Fin.castAdd 0 state by
        apply Fin.ext
        rfl]
      rw [Fin.append_left]
      simp [Fin.ext_iff]
  | succ priorRounds inductionHypothesis =>
      have priorFits : priorRounds <= inputWidth := by omega
      rw [divisionPrefixCircuit, Circuit.eval_castCounts]
      simp only [Fin.cast_refl, Function.comp_id, Circuit.eval_comp]
      rw [Circuit.eval_parallel]
      rw [inductionHypothesis priorFits]
      have currentBitValue :
          (roundInputCircuit inputWidth priorRounds fits).eval
              DeMorgan.interpretation input =
            fun _ => input (roundInputIndex inputWidth priorRounds fits) := by
        funext singleton
        exact roundInputCircuit_eval input fits
      rw [currentBitValue]
      funext output
      refine Fin.addCases (fun state => ?_)
        (fun quotientBit => ?_) output
      · rw [Fin.append_left]
        change
          (divisionStepCircuit divisorPositive priorRounds).eval
              DeMorgan.interpretation
              (Fin.append
                (Fin.append
                  (fun state => decide
                    (state = streamState divisorPositive input
                      priorRounds priorFits))
                  (streamQuotientBits divisorPositive input
                    priorRounds priorFits))
                (fun _ => input
                  (roundInputIndex inputWidth priorRounds fits)))
              (Fin.castAdd (priorRounds + 1) state) = _
        rw [divisionStepCircuit_eval_state]
        rfl
      · rw [Fin.append_right]
        induction quotientBit using Fin.cases with
        | zero =>
            change
              (divisionStepCircuit divisorPositive priorRounds).eval
                  DeMorgan.interpretation
                  (Fin.append
                    (Fin.append
                      (fun state => decide
                        (state = streamState divisorPositive input
                          priorRounds priorFits))
                      (streamQuotientBits divisorPositive input
                        priorRounds priorFits))
                    (fun _ => input
                      (roundInputIndex inputWidth priorRounds fits)))
                  (Fin.natAdd divisor (0 : Fin (priorRounds + 1))) = _
            rw [divisionStepCircuit_eval_newQuotient]
            rfl
        | succ priorBit =>
            change
              (divisionStepCircuit divisorPositive priorRounds).eval
                  DeMorgan.interpretation
                  (Fin.append
                    (Fin.append
                      (fun state => decide
                        (state = streamState divisorPositive input
                          priorRounds priorFits))
                      (streamQuotientBits divisorPositive input
                        priorRounds priorFits))
                    (fun _ => input
                      (roundInputIndex inputWidth priorRounds fits)))
                  (Fin.natAdd divisor priorBit.succ) = _
            rw [divisionStepCircuit_eval_priorQuotient]
            rfl

/-! ## Arithmetic meaning of the stream state -/

/-- The sequence of original bits read in the first `rounds` big-endian
rounds. -/
def streamInputBits
    (input : Fin inputWidth -> Bool)
    (rounds : Nat)
    (fits : rounds <= inputWidth) : Fin rounds -> Bool :=
  fun round =>
    input (roundInputIndex inputWidth round.val (by omega))

theorem streamInputBits_succ
    (input : Fin inputWidth -> Bool)
    (fits : rounds + 1 <= inputWidth) :
    streamInputBits input (rounds + 1) fits =
      Fin.snoc (streamInputBits input rounds (by omega))
        (input (roundInputIndex inputWidth rounds fits)) := by
  funext round
  induction round using Fin.lastCases with
  | last =>
      simp [streamInputBits]
  | cast prior =>
      rw [Fin.snoc_castSucc]
      unfold streamInputBits
      congr 2

theorem streamInputBits_full
    (input : Fin inputWidth -> Bool) :
    streamInputBits input inputWidth (Nat.le_refl inputWidth) =
      input ∘ Fin.rev := by
  funext round
  unfold streamInputBits roundInputIndex
  congr 2

/-- Natural value of the big-endian prefix processed so far. -/
def streamValue
    (input : Fin inputWidth -> Bool)
    (rounds : Nat)
    (fits : rounds <= inputWidth) : Nat :=
  (bitVectorIndex
    (streamInputBits input rounds fits ∘ Fin.rev)).val

theorem streamValue_succ
    (input : Fin inputWidth -> Bool)
    (fits : rounds + 1 <= inputWidth) :
    streamValue input (rounds + 1) fits =
      boolNat (input (roundInputIndex inputWidth rounds fits)) +
        2 * streamValue input rounds (by omega) := by
  unfold streamValue
  rw [streamInputBits_succ]
  rw [Fin.snoc_comp_rev]
  exact bitVectorIndex_cons _ _

theorem streamValue_full
    (input : Fin inputWidth -> Bool) :
    streamValue input inputWidth (Nat.le_refl inputWidth) =
      (bitVectorIndex input).val := by
  unfold streamValue
  rw [streamInputBits_full]
  congr 2
  funext bit
  simp [Function.comp_apply]

/-- At every round, the processed prefix is quotient times divisor plus the
one-hot remainder state. -/
theorem stream_decomposition
    (divisorPositive : 0 < divisor)
    (input : Fin inputWidth -> Bool)
    (rounds : Nat)
    (fits : rounds <= inputWidth) :
    streamValue input rounds fits =
      (bitVectorIndex
          (streamQuotientBits divisorPositive input rounds fits)).val *
          divisor +
        (streamState divisorPositive input rounds fits).val := by
  induction rounds with
  | zero =>
      simp [streamValue, streamQuotientBits, streamState]
  | succ priorRounds inductionHypothesis =>
      have priorFits : priorRounds <= inputWidth := by omega
      let priorState :=
        streamState divisorPositive input priorRounds priorFits
      let currentBit :=
        input (roundInputIndex inputWidth priorRounds fits)
      have quotientBits :
          streamQuotientBits divisorPositive input (priorRounds + 1) fits =
            Fin.cons (transitionQuotientBit priorState currentBit)
              (streamQuotientBits divisorPositive input
                priorRounds priorFits) := by
        rfl
      rw [streamValue_succ]
      rw [inductionHypothesis priorFits]
      rw [quotientBits, bitVectorIndex_cons]
      change
        boolNat currentBit +
            2 * ((bitVectorIndex
              (streamQuotientBits divisorPositive input
                priorRounds priorFits)).val * divisor + priorState.val) =
          (boolNat (transitionQuotientBit priorState currentBit) +
              2 * (bitVectorIndex
                (streamQuotientBits divisorPositive input
                  priorRounds priorFits)).val) * divisor +
            (transitionState divisorPositive priorState currentBit).val
      have transitionEquality :=
        transition_decompose divisorPositive priorState currentBit
      unfold transitionRaw at transitionEquality
      calc
        boolNat currentBit +
              2 * ((bitVectorIndex
                (streamQuotientBits divisorPositive input
                  priorRounds priorFits)).val * divisor + priorState.val) =
            2 * (bitVectorIndex
                (streamQuotientBits divisorPositive input
                  priorRounds priorFits)).val * divisor +
              (2 * priorState.val + boolNat currentBit) := by ring
        _ = 2 * (bitVectorIndex
                (streamQuotientBits divisorPositive input
                  priorRounds priorFits)).val * divisor +
              (boolNat (transitionQuotientBit priorState currentBit) *
                  divisor +
                (transitionState divisorPositive priorState currentBit).val) := by
            rw [transitionEquality]
        _ = (boolNat (transitionQuotientBit priorState currentBit) +
                2 * (bitVectorIndex
                  (streamQuotientBits divisorPositive input
                    priorRounds priorFits)).val) * divisor +
              (transitionState divisorPositive priorState currentBit).val := by
            ring

/-- The completed quotient stream represents ordinary natural division. -/
theorem streamQuotientBits_value
    (divisorPositive : 0 < divisor)
    (input : Fin inputWidth -> Bool) :
    (bitVectorIndex
        (streamQuotientBits divisorPositive input inputWidth
          (Nat.le_refl inputWidth))).val =
      (bitVectorIndex input).val / divisor := by
  have decomposition := stream_decomposition divisorPositive input
    inputWidth (Nat.le_refl inputWidth)
  rw [streamValue_full] at decomposition
  let quotientValue :=
    (bitVectorIndex
      (streamQuotientBits divisorPositive input inputWidth
        (Nat.le_refl inputWidth))).val
  let remainderValue :=
    (streamState divisorPositive input inputWidth
      (Nat.le_refl inputWidth)).val
  have remainderLt : remainderValue < divisor :=
    (streamState divisorPositive input inputWidth
      (Nat.le_refl inputWidth)).isLt
  change quotientValue = (bitVectorIndex input).val / divisor
  rw [decomposition]
  symm
  calc
    (quotientValue * divisor + remainderValue) / divisor =
        (remainderValue + divisor * quotientValue) / divisor := by
      congr 1
      ring
    _ = remainderValue / divisor + quotientValue := by
      exact Nat.add_mul_div_left remainderValue quotientValue
        divisorPositive
    _ = quotientValue := by
      rw [Nat.div_eq_of_lt remainderLt]
      simp

/-- The completed one-hot state is ordinary natural remainder. -/
theorem streamState_value
    (divisorPositive : 0 < divisor)
    (input : Fin inputWidth -> Bool) :
    (streamState divisorPositive input inputWidth
        (Nat.le_refl inputWidth)).val =
      (bitVectorIndex input).val % divisor := by
  have decomposition := stream_decomposition divisorPositive input
    inputWidth (Nat.le_refl inputWidth)
  rw [streamValue_full] at decomposition
  let quotientValue :=
    (bitVectorIndex
      (streamQuotientBits divisorPositive input inputWidth
        (Nat.le_refl inputWidth))).val
  let remainderValue :=
    (streamState divisorPositive input inputWidth
      (Nat.le_refl inputWidth)).val
  have remainderLt : remainderValue < divisor :=
    (streamState divisorPositive input inputWidth
      (Nat.le_refl inputWidth)).isLt
  change remainderValue = (bitVectorIndex input).val % divisor
  rw [decomposition]
  rw [show quotientValue * divisor + remainderValue =
      remainderValue + divisor * quotientValue by ring]
  rw [Nat.add_mul_mod_self_left]
  exact (Nat.mod_eq_of_lt remainderLt).symm

/-! ## Public fixed-division circuit -/

/-- Reorder `(remainder one-hot..., quotient bits...)` into the public
`(quotient bits..., remainder one-hot...)` layout. -/
def divisionOutputIndex
    (inputWidth divisor : Nat) :
    Fin (inputWidth + divisor) -> Fin (divisor + inputWidth) :=
  Fin.addCases
    (fun quotientBit => ⟨divisor + quotientBit.val, by omega⟩)
    (fun remainder => ⟨remainder.val, by omega⟩)

/-- Fixed-divisor long division.  Quotient bits have the same width as the
input (with leading zeros), followed by a one-hot remainder vector. -/
noncomputable def circuit
    (inputWidth : Nat)
    (divisorPositive : 0 < divisor) :
    Circuit DeMorgan.signature inputWidth
      (inputWidth + divisor) :=
  (divisionPrefixCircuit inputWidth divisorPositive inputWidth
    (Nat.le_refl inputWidth)).mapOutputs
      (divisionOutputIndex inputWidth divisor)

/-- The public divider emits exactly `prefixGateCount` gates. -/
@[simp] theorem circuit_size
    (inputWidth : Nat)
    (divisorPositive : 0 < divisor) :
    (circuit inputWidth divisorPositive).size =
      prefixGateCount inputWidth divisorPositive inputWidth := by
  simp [circuit]

@[simp] theorem circuit_eval_quotient
    (divisorPositive : 0 < divisor)
    (input : Fin inputWidth -> Bool)
    (bit : Fin inputWidth) :
    (circuit inputWidth divisorPositive).eval DeMorgan.interpretation input
        (Fin.castAdd divisor bit) =
      streamQuotientBits divisorPositive input inputWidth
        (Nat.le_refl inputWidth) bit := by
  rw [circuit, Circuit.eval_mapOutputs, Function.comp_apply,
    divisionPrefixCircuit_eval]
  rw [show divisionOutputIndex inputWidth divisor
        (Fin.castAdd divisor bit) = Fin.natAdd divisor bit by
    apply Fin.ext
    simp [divisionOutputIndex]]
  rw [Fin.append_right]

@[simp] theorem circuit_eval_remainder
    (divisorPositive : 0 < divisor)
    (input : Fin inputWidth -> Bool)
    (remainder : Fin divisor) :
    (circuit inputWidth divisorPositive).eval DeMorgan.interpretation input
        (Fin.natAdd inputWidth remainder) =
      decide (remainder =
        streamState divisorPositive input inputWidth
          (Nat.le_refl inputWidth)) := by
  rw [circuit, Circuit.eval_mapOutputs, Function.comp_apply,
    divisionPrefixCircuit_eval]
  rw [show divisionOutputIndex inputWidth divisor
        (Fin.natAdd inputWidth remainder) =
      Fin.castAdd inputWidth remainder by
    apply Fin.ext
    simp [divisionOutputIndex]]
  rw [Fin.append_left]

/-- Reading the quotient block back as a natural gives exact division. -/
theorem circuit_quotient_value
    (divisorPositive : 0 < divisor)
    (input : Fin inputWidth -> Bool) :
    (bitVectorIndex fun bit =>
      (circuit inputWidth divisorPositive).eval DeMorgan.interpretation input
        (Fin.castAdd divisor bit)).val =
      (bitVectorIndex input).val / divisor := by
  rw [show (fun bit =>
      (circuit inputWidth divisorPositive).eval DeMorgan.interpretation input
        (Fin.castAdd divisor bit)) =
      streamQuotientBits divisorPositive input inputWidth
        (Nat.le_refl inputWidth) by
    funext bit
    exact circuit_eval_quotient divisorPositive input bit]
  exact streamQuotientBits_value divisorPositive input

/-- Canonical bounded remainder represented by the one-hot output block. -/
def remainder
    (divisorPositive : 0 < divisor)
    (input : Fin inputWidth -> Bool) : Fin divisor :=
  ⟨(bitVectorIndex input).val % divisor,
    Nat.mod_lt _ divisorPositive⟩

theorem streamState_eq_remainder
    (divisorPositive : 0 < divisor)
    (input : Fin inputWidth -> Bool) :
    streamState divisorPositive input inputWidth
        (Nat.le_refl inputWidth) =
      remainder divisorPositive input := by
  apply Fin.ext
  exact streamState_value divisorPositive input

/-- The remainder output is exactly one-hot at `input mod divisor`. -/
theorem circuit_remainder_oneHot
    (divisorPositive : 0 < divisor)
    (input : Fin inputWidth -> Bool)
    (candidate : Fin divisor) :
    (circuit inputWidth divisorPositive).eval DeMorgan.interpretation input
        (Fin.natAdd inputWidth candidate) =
      decide (candidate = remainder divisorPositive input) := by
  rw [circuit_eval_remainder, streamState_eq_remainder]

/-! ## Explicit cost bound -/

theorem bitLiteralExpression_standardCost_le
    (wanted : Bool) :
    (bitLiteralExpression
      (divisor := divisor) wanted).standardCost <= 1 := by
  cases wanted <;>
    simp [bitLiteralExpression, DeMorgan.Expression.standardCost]

theorem branchExpression_standardCost_le
    (divisorPositive : 0 < divisor)
    (raw : Fin (2 * divisor)) :
    (branchExpression divisorPositive raw).standardCost <= 2 := by
  have literal :=
    bitLiteralExpression_standardCost_le
      (divisor := divisor) (rawBit raw)
  simp only [branchExpression, DeMorgan.Expression.standardCost]
  omega

theorem nextStateExpression_standardCost_le
    (divisorPositive : 0 < divisor)
    (target : Fin divisor) :
    (nextStateExpression divisorPositive target).standardCost <= 5 := by
  unfold nextStateExpression DeMorgan.Expression.standardCost
  have lower := branchExpression_standardCost_le divisorPositive
    (lowerRaw divisorPositive target)
  have upper := branchExpression_standardCost_le divisorPositive
    (upperRaw divisorPositive target)
  omega

theorem quotientExpression_standardCost_le
    (divisorPositive : 0 < divisor) :
    (quotientExpression divisorPositive).standardCost <= 3 * divisor := by
  rw [quotientExpression, DeMorgan.Expression.finOr_standardCost]
  have branches :
      (∑ target : Fin divisor,
        (branchExpression divisorPositive
          (upperRaw divisorPositive target)).standardCost) <=
        ∑ _target : Fin divisor, 2 := by
    exact Finset.sum_le_sum fun target _member =>
      branchExpression_standardCost_le divisorPositive
        (upperRaw divisorPositive target)
  calc
    (∑ target : Fin divisor,
        (branchExpression divisorPositive
          (upperRaw divisorPositive target)).standardCost) + divisor <=
        (∑ _target : Fin divisor, 2) + divisor :=
      Nat.add_le_add_right branches divisor
    _ = 3 * divisor := by simp; omega

/-- One long-division transition costs at most eight gates per divisor
state. -/
theorem transitionCircuit_cost_le
    (divisorPositive : 0 < divisor) :
    (transitionCircuit divisorPositive).cost DeMorgan.standardCost <=
      8 * divisor := by
  rw [transitionCircuit, Circuit.cost_parallelFin]
  simp only [DeMorgan.Expression.circuit_cost]
  rw [Fin.sum_univ_castSucc]
  simp only [transitionOutputExpression, Fin.lastCases_castSucc,
    Fin.lastCases_last]
  have states :
      (∑ target : Fin divisor,
        (nextStateExpression divisorPositive target).standardCost) <=
        ∑ _target : Fin divisor, 5 := by
    exact Finset.sum_le_sum fun target _member =>
      nextStateExpression_standardCost_le divisorPositive target
  calc
    (∑ target : Fin divisor,
        (nextStateExpression divisorPositive target).standardCost) +
          (quotientExpression divisorPositive).standardCost <=
        (∑ _target : Fin divisor, 5) + 3 * divisor :=
      Nat.add_le_add states
        (quotientExpression_standardCost_le divisorPositive)
    _ = 8 * divisor := by simp; omega

@[simp] theorem initialStateCircuit_cost
    (divisorPositive : 0 < divisor) :
    (initialStateCircuit inputWidth divisorPositive).cost
        DeMorgan.standardCost = 0 := by
  rw [initialStateCircuit, Circuit.cost_parallelFin]
  simp [initialStateExpression]

@[simp] theorem divisionStepCircuit_cost
    (divisorPositive : 0 < divisor)
    (rounds : Nat) :
    (divisionStepCircuit divisorPositive rounds).cost
        DeMorgan.standardCost =
      (transitionCircuit divisorPositive).cost DeMorgan.standardCost := by
  simp [divisionStepCircuit]

/-- Unrolling charges exactly one transition cost per input bit. -/
theorem divisionPrefixCircuit_cost
    (divisorPositive : 0 < divisor)
    (rounds : Nat)
    (fits : rounds <= inputWidth) :
    (divisionPrefixCircuit inputWidth divisorPositive rounds fits).cost
        DeMorgan.standardCost =
      rounds * (transitionCircuit divisorPositive).cost
        DeMorgan.standardCost := by
  induction rounds with
  | zero =>
      simp [divisionPrefixCircuit]
  | succ priorRounds inductionHypothesis =>
      have priorFits : priorRounds <= inputWidth := by omega
      rw [divisionPrefixCircuit]
      simp only [Circuit.cost_castCounts, Circuit.cost_comp,
        Circuit.cost_parallel, divisionStepCircuit_cost]
      rw [inductionHypothesis priorFits]
      have roundCost :
          (roundInputCircuit inputWidth priorRounds fits).cost
              DeMorgan.standardCost = 0 := by
        simp [roundInputCircuit]
      rw [roundCost]
      ring

/-- The public divider has cost at most `8 * inputWidth * divisor`. -/
theorem circuit_cost_le
    (divisorPositive : 0 < divisor) :
    (circuit inputWidth divisorPositive).cost DeMorgan.standardCost <=
      inputWidth * (8 * divisor) := by
  rw [circuit, Circuit.cost_mapOutputs,
    divisionPrefixCircuit_cost divisorPositive]
  exact Nat.mul_le_mul_left inputWidth
    (transitionCircuit_cost_le divisorPositive)

end FixedDivision
end MassProduction
end Algebraic
