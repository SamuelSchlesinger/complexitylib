/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/

module
public import Complexitylib.Classes.P.FinsetDomain.Internal
public import Complexitylib.Classes.P.Composition
public import Complexitylib.Classes.P.Unary.Defs
public import Mathlib.Data.Fintype.Vector

/-!
# Finite-deviation functions are polynomial-time

A function that agrees with the constant empty-output function on all but
finitely many inputs is polynomial-time computable. Concretely, for any target
function `g` and finite set `S`, the function `fun s => if s ∈ S then g s else []`
belongs to `FP`: the finite lookup table can be hard-wired into the states of a
Turing machine that decides membership in `S` while scanning the input and then
emits the corresponding fixed output, all in linear time.

This is the base case for building up polynomial-time functions — every function
with finite support (relative to the empty output) is trivially in `FP`,
regardless of how the values `g s` are chosen.

The same lookup handles anything that depends on a *bounded key*: if a
polynomial-time function extracts a key of bounded length, then any value or
test of that key is polynomial-time, since there are only finitely many keys.
The rule applied to the key need not be computable; a constraint given by an
alphabet embedding chosen by `Classical.choice`, say, still runs in polynomial
time.

## Main definitions

- `Complexity.keySet` — the strings of bounded length satisfying a predicate

## Main results

- `ite_mem_finset_mem_FP` — `fun s => if s ∈ S then g s else []` belongs to `FP`
- `mem_FP_of_bounded_key` — a value of a bounded key is polynomial-time
- `FPPred.of_bounded_key` — so is a test of a bounded key
-/

public section

namespace Complexity

/-- A function that agrees with the constant empty-output function except on a
finite set `S` — that is, `fun s => if s ∈ S then g s else []` — is computable in
polynomial (indeed linear) time. The finite table of exceptional values is
hard-wired into the lookup machine's states. -/
theorem ite_mem_finset_mem_FP (g : List Bool → List Bool) (S : Finset (List Bool)) :
    (fun s => if s ∈ S then g s else []) ∈ FP :=
  ite_mem_finset_mem_FP_internal g S

/-! ## Bounded keys -/

open Classical in
/-- The strings of length at most `L` satisfying `Q`. -/
noncomputable def keySet (L : ℕ) (Q : List Bool → Prop) : Finset (List Bool) :=
  ((Finset.range (L + 1)).biUnion fun n =>
    (Finset.univ : Finset (List.Vector Bool n)).image List.Vector.toList).filter Q

theorem mem_keySet {L : ℕ} {Q : List Bool → Prop} {s : List Bool} :
    s ∈ keySet L Q ↔ s.length ≤ L ∧ Q s := by
  simp only [keySet, Finset.mem_filter, Finset.mem_biUnion, Finset.mem_range,
    Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨⟨n, hn, v, rfl⟩, hQ⟩
    exact ⟨by rw [List.Vector.toList_length]; omega, hQ⟩
  · rintro ⟨hlen, hQ⟩
    exact ⟨⟨s.length, by omega, ⟨s, rfl⟩, rfl⟩, hQ⟩

/-- **A value of a bounded key is polynomial-time.** If `key` is polynomial-time
and its outputs have length at most `L`, then `z ↦ g (key z)` is polynomial-time
for every `g`, computable or not. -/
theorem mem_FP_of_bounded_key {key : List Bool → List Bool} (hkey : key ∈ FP)
    {L : ℕ} (hL : ∀ z, (key z).length ≤ L) (g : List Bool → List Bool) :
    (fun z => g (key z)) ∈ FP := by
  have h := mem_FP_comp hkey (ite_mem_finset_mem_FP g (keySet L fun _ => True))
  have heq : ((fun s => if s ∈ keySet L (fun _ => True) then g s else []) ∘ key)
      = fun z => g (key z) :=
    funext fun z => by
      rw [Function.comp_apply, ite_eq_left (mem_keySet.mpr ⟨hL z, trivial⟩)]
  rwa [heq] at h

/-- **A test of a bounded key is polynomial-time.** If `key` is polynomial-time
and its outputs have length at most `L`, then `z ↦ Q (key z)` is a
polynomial-time test for every `Q`, decidable or not. -/
theorem FPPred.of_bounded_key {key : List Bool → List Bool} (hkey : key ∈ FP)
    {L : ℕ} (hL : ∀ z, (key z).length ≤ L) (Q : List Bool → Prop) :
    FPPred fun z => Q (key z) := by
  classical
  exact ⟨fun z => decide (Q (key z)),
    mem_FP_of_bounded_key hkey hL fun s => [decide (Q s)],
    fun _ => decide_eq_true_iff.symm⟩

end Complexity
