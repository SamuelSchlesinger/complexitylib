/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Complexitylib.Circuits.Encoding.Machine.NatCode
public import Complexitylib.Circuits.Encoding.Machine.RawGate.Defs

/-!
# Machine emission of raw circuit gates — proof internals

This module composes the fixed header emitter with two terminated-unary
emitters.  Both dynamic reference tapes and the reusable zero scratch are
restored literally at the endpoint.
-/

@[expose] public section

namespace Complexity

namespace CircuitCode

namespace Machine

open TM

variable {n : ℕ}

private theorem rawGate_encode_eq (op : AndOrOp) (negated₀ negated₁ : Bool)
    (input₀ input₁ : ℕ) :
    RawGate.encode
        { op := op
          input₀ := input₀
          input₁ := input₁
          negated₀ := negated₀
          negated₁ := negated₁ } =
      rawGateHeader op negated₀ negated₁ ++
        NatCode.encode input₀ ++ NatCode.encode input₁ := by
  cases op <;> rfl

private theorem rawGateInitialWork_parked
    (counterIdx input₀Idx input₁Idx : Fin n)
    (work₀ : Fin n → Tape) (input₀ input₁ : ℕ)
    (hcounter : (work₀ counterIdx).HasBinaryNat 0)
    (hinput₀ : (work₀ input₀Idx).HasBinaryNat input₀)
    (hinput₁ : (work₀ input₁Idx).HasBinaryNat input₁)
    (hother : ∀ i, i ≠ counterIdx → i ≠ input₀Idx → i ≠ input₁Idx →
      Parked (work₀ i)) :
    ∀ i, Parked (work₀ i) := by
  intro i
  by_cases hic : i = counterIdx
  · subst i
    refine ⟨by rw [hcounter.2.1], ?_⟩
    exact Tape.HasBinaryContent.cells_ne_start hcounter.2.2
  by_cases hi₀ : i = input₀Idx
  · subst i
    refine ⟨by rw [hinput₀.2.1], ?_⟩
    exact Tape.HasBinaryContent.cells_ne_start hinput₀.2.2
  by_cases hi₁ : i = input₁Idx
  · subst i
    refine ⟨by rw [hinput₁.2.1], ?_⟩
    exact Tape.HasBinaryContent.cells_ne_start hinput₁.2.2
  · exact hother i hic hi₀ hi₁

private theorem emitRawGateTailTM_hoareTime
    (counterIdx input₀Idx input₁Idx : Fin n)
    (hcounterInput₀ : counterIdx ≠ input₀Idx)
    (hcounterInput₁ : counterIdx ≠ input₁Idx)
    (input₀ input₁ : ℕ) (inp₀ : Tape) (work₀ : Fin n → Tape)
    (ys : List Bool) (hinp : Parked inp₀)
    (hcounter : (work₀ counterIdx).HasBinaryNat 0)
    (hinput₀ : (work₀ input₀Idx).HasBinaryNat input₀)
    (hinput₁ : (work₀ input₁Idx).HasBinaryNat input₁)
    (hwork : ∀ i, Parked (work₀ i)) :
    (seqTM (emitNatCodeTM counterIdx input₀Idx)
      (emitNatCodeTM counterIdx input₁Idx)).HoareTime
      (EmitPred inp₀ work₀ ys)
      (EmitPred inp₀ work₀
        ((ys ++ NatCode.encode input₀) ++ NatCode.encode input₁))
      (emitNatCodeTime input₀ + 1 + emitNatCodeTime input₁) := by
  exact seqTM_hoareTime
    (emitNatCodeTM counterIdx input₀Idx)
    (emitNatCodeTM counterIdx input₁Idx)
    (emitNatCodeTM_hoareTime counterIdx input₀Idx hcounterInput₀
      input₀ inp₀ work₀ ys hinp hcounter hinput₀
      (fun i _ _ => hwork i))
    (emitPred_transition hinp hwork (ys ++ NatCode.encode input₀))
    (emitNatCodeTM_hoareTime counterIdx input₁Idx hcounterInput₁
      input₁ inp₀ work₀ (ys ++ NatCode.encode input₀) hinp
      hcounter hinput₁ (fun i _ _ => hwork i))

private theorem emitRawGateTailTM_hoareTimeSpace
    (counterIdx input₀Idx input₁Idx : Fin n)
    (hcounterInput₀ : counterIdx ≠ input₀Idx)
    (hcounterInput₁ : counterIdx ≠ input₁Idx)
    (input₀ input₁ inputLength initialSpace : ℕ)
    (inp₀ : Tape) (work₀ : Fin n → Tape) (ys : List Bool)
    (hinp : Parked inp₀)
    (hcounter : (work₀ counterIdx).HasBinaryNat 0)
    (hinput₀ : (work₀ input₀Idx).HasBinaryNat input₀)
    (hinput₁ : (work₀ input₁Idx).HasBinaryNat input₁)
    (hwork : ∀ i, Parked (work₀ i))
    (hworkSpace : ∀ i, (work₀ i).head ≤ initialSpace)
    (hinputSpace : inp₀.head ≤ inputLength + initialSpace + 1) :
    (seqTM (emitNatCodeTM counterIdx input₀Idx)
      (emitNatCodeTM counterIdx input₁Idx)).HoareTimeSpace
      (EmitPred inp₀ work₀ ys)
      (EmitPred inp₀ work₀
        ((ys ++ NatCode.encode input₀) ++ NatCode.encode input₁))
      (emitNatCodeTime input₀ + 1 + emitNatCodeTime input₁)
      inputLength
      (max (emitNatCodeSpace initialSpace input₀)
        (emitNatCodeSpace initialSpace input₁)) := by
  exact seqTM_hoareTimeSpace
    (emitNatCodeTM counterIdx input₀Idx)
    (emitNatCodeTM counterIdx input₁Idx)
    (emitNatCodeTM_hoareTimeSpace counterIdx input₀Idx hcounterInput₀
      input₀ inputLength initialSpace inp₀ work₀ ys hinp hcounter
      hinput₀ (fun i _ _ => hwork i) hworkSpace hinputSpace)
    (emitPred_transition hinp hwork (ys ++ NatCode.encode input₀))
    (emitNatCodeTM_hoareTimeSpace counterIdx input₁Idx hcounterInput₁
      input₁ inputLength initialSpace inp₀ work₀
      (ys ++ NatCode.encode input₀) hinp hcounter hinput₁
      (fun i _ _ => hwork i) hworkSpace hinputSpace)

theorem emitRawGateTM_hoareTime_internal
    (op : AndOrOp) (negated₀ negated₁ : Bool)
    (counterIdx input₀Idx input₁Idx : Fin n)
    (hcounterInput₀ : counterIdx ≠ input₀Idx)
    (hcounterInput₁ : counterIdx ≠ input₁Idx)
    (input₀ input₁ : ℕ) (inp₀ : Tape) (work₀ : Fin n → Tape)
    (ys : List Bool) (hinp : Parked inp₀)
    (hcounter : (work₀ counterIdx).HasBinaryNat 0)
    (hinput₀ : (work₀ input₀Idx).HasBinaryNat input₀)
    (hinput₁ : (work₀ input₁Idx).HasBinaryNat input₁)
    (hother : ∀ i, i ≠ counterIdx → i ≠ input₀Idx → i ≠ input₁Idx →
      Parked (work₀ i)) :
    (emitRawGateTM op negated₀ negated₁ counterIdx input₀Idx
      input₁Idx).HoareTime
      (EmitPred inp₀ work₀ ys)
      (EmitPred inp₀ work₀
        (ys ++ RawGate.encode
          { op := op
            input₀ := input₀
            input₁ := input₁
            negated₀ := negated₀
            negated₁ := negated₁ }))
      (emitRawGateTime input₀ input₁) := by
  have hwork := rawGateInitialWork_parked counterIdx input₀Idx input₁Idx
    work₀ input₀ input₁ hcounter hinput₀ hinput₁ hother
  have hrun := seqTM_hoareTime
    (emitBitsTM (rawGateHeader op negated₀ negated₁))
    (seqTM (emitNatCodeTM counterIdx input₀Idx)
      (emitNatCodeTM counterIdx input₁Idx))
    (emitBitsTM_hoareTime (rawGateHeader op negated₀ negated₁)
      inp₀ work₀ ys hinp hwork)
    (emitPred_transition hinp hwork
      (ys ++ rawGateHeader op negated₀ negated₁))
    (emitRawGateTailTM_hoareTime counterIdx input₀Idx input₁Idx
      hcounterInput₀ hcounterInput₁ input₀ input₁ inp₀ work₀
      (ys ++ rawGateHeader op negated₀ negated₁) hinp hcounter
      hinput₀ hinput₁ hwork)
  refine hrun.consequence (fun _ _ _ h => h) (fun inp work out h => ?_) ?_
  · simpa [rawGate_encode_eq, List.append_assoc] using h
  · simp [emitRawGateTime, rawGateHeader]
    omega

theorem emitRawGateTM_hoareTimeSpace_internal
    (op : AndOrOp) (negated₀ negated₁ : Bool)
    (counterIdx input₀Idx input₁Idx : Fin n)
    (hcounterInput₀ : counterIdx ≠ input₀Idx)
    (hcounterInput₁ : counterIdx ≠ input₁Idx)
    (input₀ input₁ inputLength initialSpace : ℕ)
    (inp₀ : Tape) (work₀ : Fin n → Tape) (ys : List Bool)
    (hinp : Parked inp₀)
    (hcounter : (work₀ counterIdx).HasBinaryNat 0)
    (hinput₀ : (work₀ input₀Idx).HasBinaryNat input₀)
    (hinput₁ : (work₀ input₁Idx).HasBinaryNat input₁)
    (hother : ∀ i, i ≠ counterIdx → i ≠ input₀Idx → i ≠ input₁Idx →
      Parked (work₀ i))
    (hworkSpace : ∀ i, (work₀ i).head ≤ initialSpace)
    (hinputSpace : inp₀.head ≤ inputLength + initialSpace + 1) :
    (emitRawGateTM op negated₀ negated₁ counterIdx input₀Idx
      input₁Idx).HoareTimeSpace
      (EmitPred inp₀ work₀ ys)
      (EmitPred inp₀ work₀
        (ys ++ RawGate.encode
          { op := op
            input₀ := input₀
            input₁ := input₁
            negated₀ := negated₀
            negated₁ := negated₁ }))
      (emitRawGateTime input₀ input₁) inputLength
      (emitRawGateSpace initialSpace input₀ input₁) := by
  have hwork := rawGateInitialWork_parked counterIdx input₀Idx input₁Idx
    work₀ input₀ input₁ hcounter hinput₀ hinput₁ hother
  have hheaderTime :=
    emitBitsTM_hoareTime (rawGateHeader op negated₀ negated₁)
      inp₀ work₀ ys hinp hwork
  have hheader := hheaderTime.toHoareTimeSpace (fun inp work out h => by
    rcases h with ⟨rfl, rfl, -⟩
    exact ⟨hworkSpace, hinputSpace⟩)
  have hrun := seqTM_hoareTimeSpace
    (emitBitsTM (rawGateHeader op negated₀ negated₁))
    (seqTM (emitNatCodeTM counterIdx input₀Idx)
      (emitNatCodeTM counterIdx input₁Idx))
    hheader
    (emitPred_transition hinp hwork
      (ys ++ rawGateHeader op negated₀ negated₁))
    (emitRawGateTailTM_hoareTimeSpace counterIdx input₀Idx input₁Idx
      hcounterInput₀ hcounterInput₁ input₀ input₁ inputLength
      initialSpace inp₀ work₀
      (ys ++ rawGateHeader op negated₀ negated₁) hinp hcounter
      hinput₀ hinput₁ hwork hworkSpace hinputSpace)
  refine hrun.consequence (fun _ _ _ h => h) (fun inp work out h => ?_)
    ?_ le_rfl ?_
  · simpa [rawGate_encode_eq, List.append_assoc] using h
  · simp [emitRawGateTime, rawGateHeader]
    omega
  · simp only [emitRawGateSpace, rawGateHeader, List.length_cons,
      List.length_nil, emitNatCodeSpace]
    apply max_le
    · omega
    · apply max_le
      · have hmax := Nat.le_max_left input₀.size input₁.size
        omega
      · have hmax := Nat.le_max_right input₀.size input₁.size
        omega

theorem emitRawGateTM_isTransducer_internal
    (op : AndOrOp) (negated₀ negated₁ : Bool)
    (counterIdx input₀Idx input₁Idx : Fin n) :
    (emitRawGateTM op negated₀ negated₁ counterIdx input₀Idx
      input₁Idx).IsTransducer := by
  exact (emitBitsTM_isTransducer
    (rawGateHeader op negated₀ negated₁)).seqTM
      ((emitNatCodeTM_isTransducer counterIdx input₀Idx).seqTM
        (emitNatCodeTM_isTransducer counterIdx input₁Idx))

end Machine

end CircuitCode

end Complexity
