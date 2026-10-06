/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Circuits.Smolensky.Internal.Gates
public import Complexitylib.Circuits.Basic

/-!
# Smolensky's circuit approximation

Fix one gate approximator per gate of an AND/OR/`MOD_3` circuit, chosen for the
gate's true input vector. Composing them along the circuit gives, at every wire
of depth `e`, a function of degree at most `(2ℓ)^e`. It is correct at every
input on which every gate approximator is correct, so it errs on at most
`size · 2^n / 2^ℓ` inputs.
-/


public section

namespace Complexity

namespace Smolensky

open Finset

variable {n W : ℕ}

private theorem le_foldl_max (values : Fin k → ℕ) (index : Fin k) :
    values index ≤ Fin.foldl k (fun result i => max result (values i)) 0 := by
  induction k with
  | zero => exact Fin.elim0 index
  | succ k ih =>
    rw [Fin.foldl_succ_last]
    refine Fin.lastCases (le_max_right _ _) (fun prior => ?_) index
    exact (ih (fun i => values i.castSucc) prior).trans (le_max_left _ _)

/-- One gate of the approximation: approximators of the gate's inputs and a gate
approximator correct off `Bad` give an approximator of the gate. -/
theorem gate_step (wireValues : BitString n → BitString W)
    (gate : Gate (Basis.unboundedAndOrMod 3) W) (Bad : Finset (BitString n))
    (A : (Fin gate.fanIn → ZMod 3) → ZMod 3) (ℓ e : ℕ)
    (hdeg : ∀ (D : ℕ) (v : Fin gate.fanIn → BitString n → ZMod 3),
      (∀ k, v k ∈ lowDegree n D) → (fun x => A fun k => v k x) ∈ lowDegree n (2 * ℓ * D))
    (hbad : ∀ x ∉ Bad,
      A (fun k => bitVal ((gate.negated k).xor (wireValues x (gate.inputs k)))) =
        bitVal (gate.eval (wireValues x)))
    (hinputs : ∀ k, ∃ P ∈ lowDegree n e,
      ∀ x ∉ Bad, P x = bitVal (wireValues x (gate.inputs k))) :
    ∃ P ∈ lowDegree n (2 * ℓ * e), ∀ x ∉ Bad, P x = bitVal (gate.eval (wireValues x)) := by
  choose P hP hPx using hinputs
  let v : Fin gate.fanIn → BitString n → ZMod 3 := fun k =>
    if gate.negated k then 1 - P k else P k
  have hv : ∀ k, v k ∈ lowDegree n e := by
    intro k
    by_cases hk : gate.negated k
    · simp only [v, hk, ite_true]
      exact one_sub_mem_lowDegree (hP k)
    · simp only [v, hk]
      exact hP k
  refine ⟨fun x => A fun k => v k x, hdeg e v hv, fun x hx => ?_⟩
  show (A fun k => v k x) = _
  rw [← hbad x hx]
  congr 1
  funext k
  rw [bitVal_xor, ← hPx k x hx]
  by_cases hk : gate.negated k <;> simp [v, hk]

/-- Approximators of every wire, given gate approximators correct off `Bad`. -/
theorem exists_wire_approx {G M : ℕ} [NeZero n] [NeZero M]
    (C : Circuit (Basis.unboundedAndOrMod 3) n M G) {ℓ : ℕ} (hℓ : 1 ≤ ℓ)
    (Bad : Finset (BitString n))
    (A : ∀ i : Fin G, (Fin (C.gates i).fanIn → ZMod 3) → ZMod 3)
    (hdeg : ∀ (i : Fin G) (D : ℕ) (v : Fin (C.gates i).fanIn → BitString n → ZMod 3),
      (∀ k, v k ∈ lowDegree n D) →
        (fun x => A i fun k => v k x) ∈ lowDegree n (2 * ℓ * D))
    (hbad : ∀ (i : Fin G), ∀ x ∉ Bad,
      A i (fun k => bitVal (((C.gates i).negated k).xor
          (C.wireValue x ((C.gates i).inputs k)))) =
        bitVal ((C.gates i).eval (C.wireValue x))) :
    ∀ w : Fin (n + G), ∃ P ∈ lowDegree n ((2 * ℓ) ^ C.wireDepth w),
      ∀ x ∉ Bad, P x = bitVal (C.wireValue x w) := by
  have hpos : 0 < 2 * ℓ := by omega
  have key : ∀ t, ∀ w : Fin (n + G), w.val = t →
      ∃ P ∈ lowDegree n ((2 * ℓ) ^ C.wireDepth w),
        ∀ x ∉ Bad, P x = bitVal (C.wireValue x w) := by
    intro t
    induction t using Nat.strong_induction_on with
    | _ t ih =>
      intro w hw
      by_cases hlt : w.val < n
      · refine ⟨fun x => bitVal (x ⟨w.val, hlt⟩), ?_, fun x _ => ?_⟩
        · rw [C.wireDepth_of_lt w hlt, pow_zero]
          exact bitVal_mem_lowDegree _
        · rw [C.wireValue_of_lt x w hlt]
      · let i : Fin G := ⟨w.val - n, by omega⟩
        have hdepth : C.wireDepth w = 1 + Fin.foldl (C.gates i).fanIn
            (fun acc k => max acc (C.wireDepth ((C.gates i).inputs k))) 0 :=
          C.wireDepth_of_not_lt w hlt
        have hinputs : ∀ k, ∃ P ∈ lowDegree n ((2 * ℓ) ^ Fin.foldl (C.gates i).fanIn
              (fun acc k => max acc (C.wireDepth ((C.gates i).inputs k))) 0),
            ∀ x ∉ Bad, P x = bitVal (C.wireValue x ((C.gates i).inputs k)) := by
          intro k
          have hacyc : ((C.gates i).inputs k).val < n + (w.val - n) := C.acyclic i k
          obtain ⟨P, hP, hPx⟩ := ih ((C.gates i).inputs k).val (by omega)
            ((C.gates i).inputs k) rfl
          refine ⟨P, mem_lowDegree_of_le hP ?_, hPx⟩
          exact Nat.pow_le_pow_right hpos
            (le_foldl_max (fun k => C.wireDepth ((C.gates i).inputs k)) k)
        obtain ⟨P, hP, hPx⟩ := gate_step (fun x => C.wireValue x) (C.gates i) Bad (A i) ℓ
          _ (hdeg i) (hbad i) hinputs
        refine ⟨P, ?_, fun x hx => ?_⟩
        · rw [hdepth, pow_add, pow_one]
          exact hP
        · rw [hPx x hx, C.wireValue_of_not_lt x w hlt]
  exact fun w => key w.val w rfl

/-- The approximation theorem for a single output gate. -/
theorem exists_output_approx {G M : ℕ} [NeZero n] [NeZero M]
    (C : Circuit (Basis.unboundedAndOrMod 3) n M G) {ℓ : ℕ} (hℓ : 1 ≤ ℓ)
    (Bad : Finset (BitString n))
    (A : ∀ i : Fin G, (Fin (C.gates i).fanIn → ZMod 3) → ZMod 3)
    (hdeg : ∀ (i : Fin G) (D : ℕ) (v : Fin (C.gates i).fanIn → BitString n → ZMod 3),
      (∀ k, v k ∈ lowDegree n D) →
        (fun x => A i fun k => v k x) ∈ lowDegree n (2 * ℓ * D))
    (hbad : ∀ (i : Fin G), ∀ x ∉ Bad,
      A i (fun k => bitVal (((C.gates i).negated k).xor
          (C.wireValue x ((C.gates i).inputs k)))) =
        bitVal ((C.gates i).eval (C.wireValue x)))
    (j : Fin M) (Aout : (Fin (C.outputs j).fanIn → ZMod 3) → ZMod 3)
    (hdegOut : ∀ (D : ℕ) (v : Fin (C.outputs j).fanIn → BitString n → ZMod 3),
      (∀ k, v k ∈ lowDegree n D) →
        (fun x => Aout fun k => v k x) ∈ lowDegree n (2 * ℓ * D))
    (hbadOut : ∀ x ∉ Bad,
      Aout (fun k => bitVal (((C.outputs j).negated k).xor
          (C.wireValue x ((C.outputs j).inputs k)))) =
        bitVal ((C.outputs j).eval (C.wireValue x))) :
    ∃ P ∈ lowDegree n ((2 * ℓ) ^ C.outputDepth j),
      ∀ x ∉ Bad, P x = bitVal (C.eval x j) := by
  have hpos : 0 < 2 * ℓ := by omega
  have hwires := exists_wire_approx C hℓ Bad A hdeg hbad
  have hinputs : ∀ k, ∃ P ∈ lowDegree n ((2 * ℓ) ^ Fin.foldl (C.outputs j).fanIn
        (fun acc k => max acc (C.wireDepth ((C.outputs j).inputs k))) 0),
      ∀ x ∉ Bad, P x = bitVal (C.wireValue x ((C.outputs j).inputs k)) := by
    intro k
    obtain ⟨P, hP, hPx⟩ := hwires ((C.outputs j).inputs k)
    refine ⟨P, mem_lowDegree_of_le hP ?_, hPx⟩
    exact Nat.pow_le_pow_right hpos
      (le_foldl_max (fun k => C.wireDepth ((C.outputs j).inputs k)) k)
  obtain ⟨P, hP, hPx⟩ := gate_step (fun x => C.wireValue x) (C.outputs j) Bad Aout ℓ
    _ hdegOut hbadOut hinputs
  refine ⟨P, ?_, fun x hx => hPx x hx⟩
  have hdepth : C.outputDepth j = 1 + Fin.foldl (C.outputs j).fanIn
      (fun acc k => max acc (C.wireDepth ((C.outputs j).inputs k))) 0 := rfl
  rw [hdepth, pow_add, pow_one]
  exact hP

/-- **Smolensky's approximation theorem.** A single-output AND/OR/`MOD_3`
circuit of depth at most `d` agrees with some function of degree at most
`(2ℓ)^d` on all but at most `size · 2^n / 2^ℓ` inputs. -/
theorem exists_lowDegree_approx_internal {G d ℓ : ℕ} [NeZero n]
    (C : Circuit (Basis.unboundedAndOrMod 3) n 1 G) (hdepth : C.depth ≤ d)
    (hℓ : 1 ≤ ℓ) :
    ∃ P ∈ lowDegree n ((2 * ℓ) ^ d),
      (univ.filter fun x => P x ≠ bitVal (C.eval x 0)).card * 2 ^ ℓ ≤
        C.size * 2 ^ n := by
  classical
  let u : ∀ i : Fin G, BitString n → BitString (C.gates i).fanIn := fun i x k =>
    ((C.gates i).negated k).xor (C.wireValue x ((C.gates i).inputs k))
  choose A hdeg hcard using fun i : Fin G => exists_gate_approx hℓ (C.gates i).op (u i)
  let uOut : BitString n → BitString (C.outputs 0).fanIn := fun x k =>
    ((C.outputs 0).negated k).xor (C.wireValue x ((C.outputs 0).inputs k))
  obtain ⟨Aout, hdegOut, hcardOut⟩ := exists_gate_approx hℓ (C.outputs 0).op uOut
  let bad : Fin G → Finset (BitString n) := fun i =>
    univ.filter fun x =>
      A i (fun k => bitVal (u i x k)) ≠ bitVal ((C.gates i).op.eval 3 _ (u i x))
  let badOut : Finset (BitString n) :=
    univ.filter fun x =>
      Aout (fun k => bitVal (uOut x k)) ≠ bitVal ((C.outputs 0).op.eval 3 _ (uOut x))
  let Bad : Finset (BitString n) := (univ.biUnion bad) ∪ badOut
  have hBad : Bad.card * 2 ^ ℓ ≤ C.size * 2 ^ n := by
    calc
      Bad.card * 2 ^ ℓ ≤ ((univ.biUnion bad).card + badOut.card) * 2 ^ ℓ :=
        Nat.mul_le_mul_right _ (Finset.card_union_le _ _)
      _ ≤ ((∑ i, (bad i).card) + badOut.card) * 2 ^ ℓ :=
        Nat.mul_le_mul_right _ (Nat.add_le_add_right (Finset.card_biUnion_le) _)
      _ = (∑ i, (bad i).card * 2 ^ ℓ) + badOut.card * 2 ^ ℓ := by
        rw [Nat.add_mul, Finset.sum_mul]
      _ ≤ (∑ _i : Fin G, 2 ^ n) + 2 ^ n :=
        Nat.add_le_add (Finset.sum_le_sum fun i _ => hcard i) hcardOut
      _ = C.size * 2 ^ n := by
        simp [Circuit.size, Nat.add_mul]
  have hbad : ∀ (i : Fin G), ∀ x ∉ Bad,
      A i (fun k => bitVal (((C.gates i).negated k).xor
          (C.wireValue x ((C.gates i).inputs k)))) =
        bitVal ((C.gates i).eval (C.wireValue x)) := by
    intro i x hx
    have hxi : x ∉ bad i := fun hmem =>
      hx (Finset.mem_union_left _ (Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i, hmem⟩))
    simp only [bad, Finset.mem_filter, Finset.mem_univ, true_and, not_not] at hxi
    exact hxi
  have hbadOut : ∀ x ∉ Bad,
      Aout (fun k => bitVal (((C.outputs 0).negated k).xor
          (C.wireValue x ((C.outputs 0).inputs k)))) =
        bitVal ((C.outputs 0).eval (C.wireValue x)) := by
    intro x hx
    have hxo : x ∉ badOut := fun hmem => hx (Finset.mem_union_right _ hmem)
    simp only [badOut, Finset.mem_filter, Finset.mem_univ, true_and, not_not] at hxo
    exact hxo
  obtain ⟨P, hP, hPx⟩ := exists_output_approx C hℓ Bad A hdeg hbad 0 Aout hdegOut hbadOut
  have hdepth0 : C.outputDepth 0 ≤ d := by
    have : C.depth = C.outputDepth 0 := by
      simp [Circuit.depth, Fin.foldl_succ, Fin.foldl_zero]
    omega
  refine ⟨P, mem_lowDegree_of_le hP (Nat.pow_le_pow_right (by omega) hdepth0), ?_⟩
  calc
    (univ.filter fun x => P x ≠ bitVal (C.eval x 0)).card * 2 ^ ℓ ≤ Bad.card * 2 ^ ℓ := by
      apply Nat.mul_le_mul_right
      apply Finset.card_le_card
      intro x hx
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
      by_contra hxBad
      exact hx (hPx x hxBad)
    _ ≤ C.size * 2 ^ n := hBad

end Smolensky

end Complexity
