/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/
module
public import Complexitylib.Classes.P.FinsetDomain
public import Complexitylib.Classes.P.DecisionFn
public import Complexitylib.Classes.PCP.Internal.PCPtoSAT
public import Complexitylib.Classes.Containments.Internal.FPBridge

/-!
# Decisions that depend on a bounded amount of data

A constraint of a constraint graph looks at two symbols and a little local data,
and says yes or no. The rule may be described by something noncomputable — an
alphabet embedding chosen by `Classical.choice`, say — but it still runs in
polynomial time, because it is a table lookup on a bounded key.

That is the content of this module: if a polynomial-time function extracts a key
of bounded length, then *any* predicate of that key is polynomial-time
decidable.

The same argument gives functions, not just decisions: a value that depends on
the key alone is a table lookup too, whatever wrote the table.

## Main results

- `Complexity.mem_P_of_bounded_key` — a bounded-key predicate is in `P`
- `Complexity.mem_FP_of_bounded_key` — a bounded-key value is in `FP`
- `Complexity.mem_FP_of_key_congr` — and so is a value that merely *agrees*
  wherever the key does
-/

@[expose] public section

namespace Complexity

open Classical in
/-- The strings of length at most `L` satisfying `P`. -/
noncomputable def keySet (L : ℕ) (Q : List Bool → Prop) : Finset (List Bool) :=
  (Finset.range (L + 1)).biUnion fun n =>
    ((allVecs n).filter fun s => Q s).toFinset

open Classical in
theorem mem_keySet {L : ℕ} {Q : List Bool → Prop} {s : List Bool} :
    s ∈ keySet L Q ↔ s.length ≤ L ∧ Q s := by
  classical
  rw [keySet, Finset.mem_biUnion]
  constructor
  · rintro ⟨n, hn, hs⟩
    rw [List.mem_toFinset, List.mem_filter] at hs
    rw [Finset.mem_range] at hn
    have hlen := (mem_allVecs_iff n s).mp hs.1
    exact ⟨by omega, by simpa using hs.2⟩
  · rintro ⟨hlen, hQ⟩
    refine ⟨s.length, Finset.mem_range.mpr (by omega), ?_⟩
    rw [List.mem_toFinset, List.mem_filter]
    exact ⟨(mem_allVecs_iff _ _).mpr rfl, by simpa using hQ⟩

/-- **A bounded-key predicate is in `P`.** The predicate itself need not be
computable; only the key extraction must be. -/
theorem mem_P_of_bounded_key {key : List Bool → List Bool} (hkey : key ∈ FP)
    {L : ℕ} (hL : ∀ z, (key z).length ≤ L) (Q : List Bool → Prop) :
    {z : List Bool | Q (key z)} ∈ P := by
  classical
  have hite : (fun s => if s ∈ keySet L Q then [true] else ([] : List Bool)) ∈ FP :=
    ite_mem_finset_mem_FP (fun _ => [true]) (keySet L Q)
  have hcomp : (fun z => if key z ∈ keySet L Q then [true] else ([] : List Bool)) ∈ FP := by
    have := mem_FP_comp hkey hite
    refine mem_FP_of_eq this fun z => ?_
    rw [Function.comp_apply]
  refine mem_P_of_decisionFn hcomp fun z => ?_
  show Q (key z) ↔ _
  by_cases h : Q (key z)
  · rw [ite_eq_left (mem_keySet.mpr ⟨hL z, h⟩)]
    exact ⟨fun _ => ⟨true, by simp, rfl⟩, fun _ => h⟩
  · rw [ite_eq_right (fun hcon => h (mem_keySet.mp hcon).2)]
    simp [h]

/-- **A bounded-key value is in `FP`.** The rule computing the value from the
key need not be computable; only the key extraction must be. -/
theorem mem_FP_of_bounded_key {key : List Bool → List Bool} (hkey : key ∈ FP)
    {L : ℕ} (hL : ∀ z, (key z).length ≤ L) (g : List Bool → List Bool) :
    (fun z => g (key z)) ∈ FP := by
  classical
  have hite : (fun s => if s ∈ keySet L (fun _ => True) then g s else ([] : List Bool)) ∈ FP :=
    ite_mem_finset_mem_FP g (keySet L (fun _ => True))
  have hcomp := mem_FP_comp hkey hite
  refine mem_FP_of_eq hcomp fun z => ?_
  rw [Function.comp_apply, ite_eq_left (mem_keySet.mpr ⟨hL z, trivial⟩)]

/-- **A value that depends on its input only through a bounded key is in `FP`.**
No rule computing the value from the key need be exhibited: agreeing wherever
the key agrees is enough. -/
theorem mem_FP_of_key_congr {key : List Bool → List Bool} (hkey : key ∈ FP)
    {L : ℕ} (hL : ∀ z, (key z).length ≤ L) {val : List Bool → List Bool}
    (hcongr : ∀ z z', key z = key z' → val z = val z') : val ∈ FP := by
  classical
  refine mem_FP_of_eq (mem_FP_of_bounded_key hkey hL
    (fun s => if h : ∃ z, key z = s then val (Classical.choose h) else [])) fun z => ?_
  have hex : ∃ w, key w = key z := ⟨z, rfl⟩
  rw [dite_eq_left hex]
  exact hcongr _ z (Classical.choose_spec hex)

end Complexity
