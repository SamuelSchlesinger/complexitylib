/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.KarchmerWigderson.Sharing.Circuit
public import Complexitylib.Algebraic.LowerBound.KarchmerWigderson.Sharing.Extended.Defs
import Complexitylib.Algebraic.LowerBound.KarchmerWigderson.Sharing.Extended.Internal

/-!
# Khrapchenko's bound for circuits with shared gates and XOR/EQUIV gates

This file extends the bounds of
`Complexitylib.Algebraic.LowerBound.KarchmerWigderson.Sharing.Circuit` from De Morgan circuits to
circuits over `Extended.signature`, the De Morgan basis together with binary XOR and EQUIV gates.

In `SharedProgram.sq_card_edges_le`, the Khrapchenko upper bound `(k + 1) · X · |A| · |B|` depends
on `X = P.inputLeaves n`, which counts only literal leaves on the original circuit inputs
`0, …, n - 1` and ignores literal leaves reading shared variables `z ≥ n`. Consequently, a
binary gadget built solely from shared variables `z₁, z₂ ≥ n`—the four-leaf De Morgan expansion
`Formula.xorGadget z₁ z₂` of `z₁ ⊕ z₂` or `Formula.equivGadget z₁ z₂` of `z₁ ↔ z₂`—has
`inputLeaves n = 0`. Allocating two shared values for the two input wires of each XOR/EQUIV gate
and substituting the gadget for the gate wire replaces every XOR/EQUIV gate by a zero-input-leaf
subformula while increasing the number of shared values by two, regardless of the gate's fan-out.

Hence a single-output circuit with `c_DM` AND and OR gates (`Extended.deMorganCost`), `r` XOR and
EQUIV gates (`Extended.xorCost`), and `k` gates of fan-out at least two (`sharedGateCount`) yields
a `SharedProgram n K` with `K ≤ k + 2r` and `P.inputLeaves n ≤ c_DM + k + 2r + 1`
(`Extended.exists_sharedProgram_of_circuit`). Thus:
* `|edges A B|² ≤ (k + 2r + 1) · (c_DM + k + 2r + 1) · |A| · |B|`
  (`Extended.sq_card_edges_le_cost`),
* `n² ≤ (k + 2r + 1) · (c_DM + k + 2r + 1)` for parity (`Extended.parity_sq_le_cost`),
* `(n + 1 - t) · t ≤ (k + 2r + 1) · (c_DM + k + 2r + 1)` for `threshold t`
  (`Extended.threshold_mul_le_cost`),
* `(n - ⌊n/2⌋) · (⌊n/2⌋ + 1) ≤ (k + 2r + 1) · (c_DM + k + 2r + 1)` for majority
  (`Extended.majority_mul_le_cost`),
and both parity and majority require a superlinear number `c_DM = ω(n)` of AND and OR gates
whenever `k(n) = o(n)` and `r(n) = o(n)` (`Extended.isLittleO_cost_of_parity`,
`Extended.isLittleO_cost_of_majority`).

The theorems here carry the names of their De Morgan counterparts in the `KW` namespace, under
`KW.Extended`; with `r = 0` their hypotheses specialize to those of the De Morgan versions. The
one difference is majority: `Extended.mul_le_cost_of_majority` takes `2m + 1` inputs, like
`KW.mul_le_cost_of_majority`, while
`Extended.mul_le_cost_of_majority_of_four_mul_le` and `Extended.isLittleO_cost_of_majority`
cover every input length `n`, at the price of the factor `4` in the hypothesis
`4 · (k + 2r + 1) · (C + 1) ≤ n`. (`KW.isLittleO_cost_of_majority` is stated for the odd
lengths `2m + 1` only.)
-/

@[expose] public section

namespace Algebraic
namespace KW
namespace Extended

/-- **Extended-basis circuits as programs with shared gates.** Every single-output circuit over the
extended De Morgan + XOR/EQUIV basis computing `f` with `k` gates of fan-out at least two and `r`
XOR/EQUIV gates yields a `SharedProgram n K` computing `f` with `K ≤ k + 2r` and
`P.inputLeaves n ≤ c_DM + k + 2r + 1`, where `c_DM` counts the AND and OR gates. -/
theorem exists_sharedProgram_of_circuit {n : Nat} (c : Circuit signature n 1)
    {f : Cslib.BooleanFunction n} (hc : c.ComputesWith interpretation fun x _ => f x) :
    ∃ K, ∃ P : SharedProgram n K,
      K ≤ sharedGateCount c + 2 * c.cost xorCost ∧
      P.Computes f ∧
      P.inputLeaves n ≤
        c.cost deMorganCost + sharedGateCount c + 2 * c.cost xorCost + 1 := by
  obtain ⟨K, P, hK, hP, hil⟩ := exists_sharedProgram_of_program f c.program
    (fun g => (Finset.univ.filter fun o => c.outputs o = Wire.gate g).card) (j := 0)
    (SharedProgram.output (.lit (c.outputs 0).index true))
    (fun x => by
      have := congrFun (hc x) 0
      simp only [Circuit.eval, Function.comp_apply, Program.trace] at this
      simp [wireValues, append_index, this])
    (fun g => by
      simp only [SharedProgram.occ, Formula.occ]
      split_ifs with h
      · exact Finset.card_pos.mpr ⟨0, by simpa using (index_val_eq_iff _ g).mp h⟩
      · exact Nat.zero_le _)
  have hinit : (SharedProgram.output (.lit (c.outputs 0).index true)).inputLeaves (n + c.size) =
      1 := by
    simp [SharedProgram.inputLeaves, Formula.inputLeaves, (c.outputs 0).index.isLt]
  rw [hinit] at hil
  simp only [Circuit.cost, sharedGateCount_eq, zero_add] at hK hil ⊢
  exact ⟨K, P, hK, hP, by omega⟩

/-! ### Khrapchenko, parity, threshold, and majority lower bounds -/

variable {n : Nat}

/-- **Khrapchenko bound for circuits with `k` shared gates and `r` XOR/EQUIV gates.** If an
extended-basis circuit computes `f`, at most `k` of its gates have fan-out at least two, and at
most `r` of its gates are XOR or EQUIV gates, then `f` satisfies Khrapchenko's bound with measure
`(k + 2r + 1) · (c_DM + k + 2r + 1)`, where `c_DM` counts the AND and OR gates. -/
theorem khrapchenkoBound_of_circuit {k r : Nat} (c : Circuit signature n 1)
    {f : Cslib.BooleanFunction n} (hc : c.ComputesWith interpretation fun x _ => f x)
    (hk : sharedGateCount c ≤ k) (hr : c.cost xorCost ≤ r) :
    KhrapchenkoBound f ((k + 2 * r + 1) * (c.cost deMorganCost + k + 2 * r + 1)) := by
  obtain ⟨K, P, hK, hP, hil⟩ := exists_sharedProgram_of_circuit c hc
  intro A B hA hB
  refine (SharedProgram.khrapchenkoBound hP A B hA hB).trans ?_
  exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (Nat.mul_le_mul (by omega) (by omega)))

/-- **Rectangle edge bound for circuits with `k` shared gates and `r` XOR/EQUIV gates.** If an
extended-basis circuit is `1` on `A` and `0` on `B`, then
`|edges A B|² ≤ (k + 2r + 1) · (c_DM + k + 2r + 1) · |A| · |B|`. -/
theorem sq_card_edges_le_cost {k r : Nat} (c : Circuit signature n 1)
    {f : Cslib.BooleanFunction n} (hc : c.ComputesWith interpretation fun x _ => f x)
    (hk : sharedGateCount c ≤ k) (hr : c.cost xorCost ≤ r)
    (A B : Finset (Fin n → Bool)) (hA : ∀ x ∈ A, f x = true) (hB : ∀ y ∈ B, f y = false) :
    (edges A B).card ^ 2 ≤
      (k + 2 * r + 1) * (c.cost deMorganCost + k + 2 * r + 1) * A.card * B.card :=
  khrapchenkoBound_of_circuit c hc hk hr A B hA hB

/-- **Parity in circuits with `k` shared gates and `r` XOR/EQUIV gates.** An extended-basis
circuit computing the parity of `n ≥ 1` bits satisfies
`n² ≤ (k + 2r + 1) · (c_DM + k + 2r + 1)`. -/
theorem parity_sq_le_cost [NeZero n] {k r : Nat} (c : Circuit signature n 1)
    (computes : c.ComputesWith interpretation (GateElimination.Xor.parityTarget n))
    (hk : sharedGateCount c ≤ k) (hr : c.cost xorCost ≤ r) :
    n ^ 2 ≤ (k + 2 * r + 1) * (c.cost deMorganCost + k + 2 * r + 1) :=
  (khrapchenkoBound_of_circuit c computes hk hr).parity_sq_le

/-- **Superlinear De Morgan cost for parity with few shared gates and few XOR/EQUIV gates.** If
`(k + 2r + 1) · (C + 1) ≤ n`, every extended-basis circuit computing the parity of `n` bits with at
most `k` gates of fan-out at least two and at most `r` XOR/EQUIV gates has at least `C · n` AND
and OR gates. -/
theorem mul_le_cost_of_parity {k r C : Nat} (hkrn : (k + 2 * r + 1) * (C + 1) ≤ n)
    (c : Circuit signature n 1)
    (computes : c.ComputesWith interpretation (GateElimination.Xor.parityTarget n))
    (hk : sharedGateCount c ≤ k) (hr : c.cost xorCost ≤ r) :
    C * n ≤ c.cost deMorganCost := by
  have hkr : k + 2 * r + 1 ≤ n := le_trans (Nat.le_mul_of_pos_right _ (Nat.succ_pos C)) hkrn
  have : NeZero n := ⟨by omega⟩
  have h : (k + 2 * r + 1) * (n * (C + 1)) ≤
      (k + 2 * r + 1) * (c.cost deMorganCost + k + 2 * r + 1) :=
    calc (k + 2 * r + 1) * (n * (C + 1)) = n * ((k + 2 * r + 1) * (C + 1)) := by ring
      _ ≤ n * n := Nat.mul_le_mul_left _ hkrn
      _ = n ^ 2 := (sq n).symm
      _ ≤ _ := parity_sq_le_cost c computes hk hr
  have h' := Nat.le_of_mul_le_mul_left h (Nat.succ_pos (k + 2 * r))
  nlinarith

/-- **Parity needs superlinear De Morgan gates when `k(n) = o(n)` and `r(n) = o(n)`.** If, for
every `n`, `c n` is an extended-basis circuit computing the parity of `n` bits with at most
`k n = o(n)` gates of fan-out at least two and at most `r n = o(n)` XOR/EQUIV gates, then the
number of AND and OR gates of `c n` grows faster than `n`. -/
theorem isLittleO_cost_of_parity {k r : ℕ → ℕ}
    (hk : (fun n => (k n : ℝ)) =o[Filter.atTop] fun n : ℕ => (n : ℝ))
    (hr : (fun n => (r n : ℝ)) =o[Filter.atTop] fun n : ℕ => (n : ℝ))
    (c : (n : ℕ) → Circuit signature n 1)
    (computes : ∀ n, (c n).ComputesWith interpretation (GateElimination.Xor.parityTarget n))
    (hshared : ∀ n, sharedGateCount (c n) ≤ k n)
    (hxor : ∀ n, (c n).cost xorCost ≤ r n) :
    (fun n : ℕ => (n : ℝ)) =o[Filter.atTop] fun n => ((c n).cost deMorganCost : ℝ) :=
  isLittleO_of_forall_mul_le_two (a := 1) (b := 2) (d := 0) hk hr fun n _ hkrn =>
    mul_le_cost_of_parity (by nlinarith) (c n) (computes n) (hshared n) (hxor n)

/-- **Threshold functions in circuits with `k` shared gates and `r` XOR/EQUIV gates.** For
`1 ≤ t ≤ n`, every extended-basis circuit computing `threshold t` satisfies
`(n + 1 - t) · t ≤ (k + 2r + 1) · (c_DM + k + 2r + 1)`. -/
theorem threshold_mul_le_cost {t k r : Nat} (ht : 1 ≤ t) (htn : t ≤ n)
    (c : Circuit signature n 1)
    (computes : c.ComputesWith interpretation (thresholdTarget n t))
    (hk : sharedGateCount c ≤ k) (hr : c.cost xorCost ≤ r) :
    (n + 1 - t) * t ≤ (k + 2 * r + 1) * (c.cost deMorganCost + k + 2 * r + 1) :=
  (khrapchenkoBound_of_circuit c computes hk hr).threshold_mul_le ht htn

/-- **Majority in circuits with `k` shared gates and `r` XOR/EQUIV gates.** Every extended-basis
circuit computing strict majority of `n ≥ 1` bits satisfies
`(n - ⌊n/2⌋) · (⌊n/2⌋ + 1) ≤ (k + 2r + 1) · (c_DM + k + 2r + 1)`. -/
theorem majority_mul_le_cost {k r : Nat} (hn : 1 ≤ n)
    (c : Circuit signature n 1)
    (computes : c.ComputesWith interpretation (majorityTarget n))
    (hk : sharedGateCount c ≤ k) (hr : c.cost xorCost ≤ r) :
    (n - n / 2) * (n / 2 + 1) ≤ (k + 2 * r + 1) * (c.cost deMorganCost + k + 2 * r + 1) :=
  (khrapchenkoBound_of_circuit c computes hk hr).majority_mul_le hn

/-- **Odd-input majority in circuits with `k` shared gates and `r` XOR/EQUIV gates.** For odd `n`,
every extended-basis circuit computing strict majority of `n` bits satisfies
`(⌊n/2⌋ + 1)² ≤ (k + 2r + 1) · (c_DM + k + 2r + 1)`. -/
theorem majority_sq_le_cost_of_odd {k r : Nat} (hodd : Odd n)
    (c : Circuit signature n 1)
    (computes : c.ComputesWith interpretation (majorityTarget n))
    (hk : sharedGateCount c ≤ k) (hr : c.cost xorCost ≤ r) :
    (n / 2 + 1) ^ 2 ≤ (k + 2 * r + 1) * (c.cost deMorganCost + k + 2 * r + 1) := by
  obtain ⟨m, rfl⟩ := hodd
  have hdiv : (2 * m + 1) / 2 = m := by omega
  have hsub : (2 * m + 1 - (2 * m + 1) / 2) * ((2 * m + 1) / 2 + 1) =
      ((2 * m + 1) / 2 + 1) ^ 2 := by
    rw [hdiv, sq]
    congr 1
    omega
  rw [← hsub]
  exact majority_mul_le_cost (by omega) c computes hk hr

/-- **Superlinear De Morgan cost for odd-input majority with few shared and XOR/EQUIV gates.** If
`(k + 2r + 1) · (C + 1) ≤ m`, every extended-basis circuit computing the majority of `2m + 1` bits
with at most `k` gates of fan-out at least two and at most `r` XOR/EQUIV gates has at least `C · m`
AND and OR gates. With `r = 0` this is the hypothesis of `KW.mul_le_cost_of_majority`; for every
input length see `mul_le_cost_of_majority_of_four_mul_le`. -/
theorem mul_le_cost_of_majority {m k r C : Nat} (hkrm : (k + 2 * r + 1) * (C + 1) ≤ m)
    (c : Circuit signature (2 * m + 1) 1)
    (computes : c.ComputesWith interpretation (majorityTarget (2 * m + 1)))
    (hk : sharedGateCount c ≤ k) (hr : c.cost xorCost ≤ r) :
    C * m ≤ c.cost deMorganCost := by
  have hodd : Odd (2 * m + 1) := ⟨m, rfl⟩
  have hsq := majority_sq_le_cost_of_odd hodd c computes hk hr
  have hdiv : (2 * m + 1) / 2 + 1 = m + 1 := by omega
  rw [hdiv] at hsq
  have h : (k + 2 * r + 1) * ((m + 1) * (C + 1)) ≤
      (k + 2 * r + 1) * (c.cost deMorganCost + k + 2 * r + 1) :=
    calc (k + 2 * r + 1) * ((m + 1) * (C + 1)) = (m + 1) * ((k + 2 * r + 1) * (C + 1)) := by ring
      _ ≤ (m + 1) * (m + 1) := Nat.mul_le_mul_left _ (by omega)
      _ = (m + 1) ^ 2 := (sq (m + 1)).symm
      _ ≤ _ := hsq
  have h' := Nat.le_of_mul_le_mul_left h (Nat.succ_pos (k + 2 * r))
  nlinarith

/-- **Superlinear De Morgan cost for majority of any length with few shared and XOR/EQUIV
gates.** The variant of `mul_le_cost_of_majority` for every input length `n`: if
`4 · (k + 2r + 1) · (C + 1) ≤ n`, every extended-basis circuit computing the majority of `n` bits
with at most `k` gates of fan-out at least two and at most `r` XOR/EQUIV gates has at least `C · n`
AND and OR gates. -/
theorem mul_le_cost_of_majority_of_four_mul_le {k r C : Nat}
    (hkrn : 4 * (k + 2 * r + 1) * (C + 1) ≤ n)
    (c : Circuit signature n 1)
    (computes : c.ComputesWith interpretation (majorityTarget n))
    (hk : sharedGateCount c ≤ k) (hr : c.cost xorCost ≤ r) :
    C * n ≤ c.cost deMorganCost := by
  rcases Nat.eq_zero_or_pos C with rfl | hC
  · simp
  have hn1 : 1 ≤ n := by nlinarith
  have hmaj := majority_mul_le_cost hn1 c computes hk hr
  set h := (n + 1) / 2
  have hh1 : h ≤ n - n / 2 := by omega
  have hh2 : h ≤ n / 2 + 1 := by omega
  have hnh : n ≤ 2 * h := by omega
  have hkh : (k + 2 * r + 1) * (2 * C + 1) ≤ h := by nlinarith
  have h : (k + 2 * r + 1) * (h * (2 * C + 1)) ≤
      (k + 2 * r + 1) * (c.cost deMorganCost + k + 2 * r + 1) :=
    calc (k + 2 * r + 1) * (h * (2 * C + 1)) = h * ((k + 2 * r + 1) * (2 * C + 1)) := by ring
      _ ≤ h * h := Nat.mul_le_mul_left _ hkh
      _ ≤ (n - n / 2) * (n / 2 + 1) := Nat.mul_le_mul hh1 hh2
      _ ≤ _ := hmaj
  have h' := Nat.le_of_mul_le_mul_left h (Nat.succ_pos (k + 2 * r))
  nlinarith

/-- **Majority needs superlinear De Morgan gates when `k(n) = o(n)` and `r(n) = o(n)`.** If, for
every input length `n`, `c n` is an extended-basis circuit computing the majority of `n` bits with
at most `k n = o(n)` gates of fan-out at least two and at most `r n = o(n)` XOR/EQUIV gates, then
the number of AND and OR gates of `c n` grows faster than `n`. Unlike
`KW.isLittleO_cost_of_majority`, which indexes the family by `m` with `2m + 1` inputs, the family
here ranges over all input lengths. -/
theorem isLittleO_cost_of_majority {k r : ℕ → ℕ}
    (hk : (fun n => (k n : ℝ)) =o[Filter.atTop] fun n : ℕ => (n : ℝ))
    (hr : (fun n => (r n : ℝ)) =o[Filter.atTop] fun n : ℕ => (n : ℝ))
    (c : (n : ℕ) → Circuit signature n 1)
    (computes : ∀ n, (c n).ComputesWith interpretation (majorityTarget n))
    (hshared : ∀ n, sharedGateCount (c n) ≤ k n)
    (hxor : ∀ n, (c n).cost xorCost ≤ r n) :
    (fun n : ℕ => (n : ℝ)) =o[Filter.atTop] fun n => ((c n).cost deMorganCost : ℝ) :=
  isLittleO_of_forall_mul_le_two (a := 4) (b := 8) (d := 3) hk hr fun n _ hkrn =>
    mul_le_cost_of_majority_of_four_mul_le (by nlinarith) (c n) (computes n) (hshared n)
      (hxor n)

end Extended
end KW
end Algebraic
