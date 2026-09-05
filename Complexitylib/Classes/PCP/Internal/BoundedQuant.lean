/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/
module
public import Complexitylib.Classes.PCP.Internal.BitwiseFP
public import Complexitylib.Classes.Containments

/-!
# Checking polynomially many conditions

An algorithm that has to verify a condition at every one of polynomially many
places is a loop, and a loop of polynomial length is still polynomial time. This
module states that as closure of `P` under quantification over an index bounded
by a polynomial-time unary length function.

The proof reuses the bit-by-bit construction: run the condition at each index,
collect the verdicts into a string, and compare it against the all-ones string
of the same length. The comparison is what turns a list of verdicts into a
single one, and it costs nothing beyond the string equality test already in the
toolkit.

## Main results

- `Complexity.forall_unary_mem_P` — a bounded conjunction of `P` conditions
- `Complexity.exists_unary_mem_P` — a bounded disjunction of `P` conditions
-/

@[expose] public section

namespace Complexity

/-- **A bounded conjunction of polynomial-time conditions is polynomial time.**
The index runs over `0, …, len x - 1` and is passed to the condition in unary. -/
theorem forall_unary_mem_P {L : Language} (hL : L ∈ P) {len : List Bool → ℕ}
    (hlen : (fun x => List.replicate (len x) true) ∈ FP) :
    {x : List Bool | ∀ i < len x, pair x (List.replicate i true) ∈ L} ∈ P := by
  obtain ⟨g, hgFP, hg⟩ := exists_decisionFn_of_mem_P hL
  have hmap : (fun x => (List.range (len x)).map
      (fun i => g (pair x (List.replicate i true)))) ∈ FP :=
    bitwise_mem_FP hlen hgFP fun _ _ => rfl
  refine mem_P_of_decisionFn (eqFlagFn_mem_FP hmap hlen) fun x => ?_
  simp only [Set.mem_ofPred_eq]
  set a := (List.range (len x)).map (fun i => g (pair x (List.replicate i true))) with ha
  set b := List.replicate (len x) true with hb
  have hiff : a = b ↔ ∀ i < len x, pair x (List.replicate i true) ∈ L := by
    rw [ha, hb, List.eq_replicate_iff]
    constructor
    · rintro ⟨-, hall⟩ i hi
      refine (hg _).2 (hall _ ?_)
      exact List.mem_map.2 ⟨i, List.mem_range.2 hi, rfl⟩
    · intro hall
      refine ⟨by simp, ?_⟩
      rintro c hc
      obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hc
      exact (hg _).1 (hall i (List.mem_range.1 hi))
  rw [← hiff]
  constructor
  · intro hab
    rw [(Cobham.eqFlag_eq_true_iff a b).mpr hab]
    exact ⟨true, by simp, rfl⟩
  · rintro ⟨c, hc, rfl⟩
    rcases Cobham.eqFlag_flag a b with h | h
    · exact (Cobham.eqFlag_eq_true_iff a b).mp h
    · rw [h] at hc
      simp at hc

/-- **A bounded disjunction of polynomial-time conditions is polynomial time.** -/
theorem exists_unary_mem_P {L : Language} (hL : L ∈ P) {len : List Bool → ℕ}
    (hlen : (fun x => List.replicate (len x) true) ∈ FP) :
    {x : List Bool | ∃ i < len x, pair x (List.replicate i true) ∈ L} ∈ P := by
  have hall := forall_unary_mem_P (P_compl hL) hlen
  have heq : {x : List Bool | ∃ i < len x, pair x (List.replicate i true) ∈ L}
      = {x : List Bool | ∀ i < len x, pair x (List.replicate i true) ∈ Lᶜ}ᶜ := by
    ext x
    constructor
    · rintro ⟨i, hi, hmem⟩ hall
      exact (hall i hi) hmem
    · intro h
      by_contra hc
      exact h fun i hi hmem => hc ⟨i, hi, hmem⟩
  rw [heq]
  exact P_compl hall

end Complexity
