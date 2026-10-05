/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Aggregate.Compressed.Basic
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Aggregate.Components

/-!
# Large components from joint aggregate states

The compressed component key consists of the actual joint state and one partial
joint state. Its cardinality replaces the product of all special registers and outputs.
-/

@[expose] public section

namespace Algebraic.Cutwidth.Aggregate.Compressed

open scoped Classical
open MultiOutput SingleCut

/-- For a dense rectangle-free output, one component of any guessed erasure contains
almost all input coordinates. This includes guesses that are never realized by an input. -/
theorem exists_large_component {J : Type} {State : J → Type}
    [∀ j, CommMonoid (State j)] {M : Type} [CommMonoid M] [Fintype M]
    {n g K : Nat} (p : Program (Algebraic.Aggregate.signature State) n g)
    (compression : Algebraic.Aggregate.Compressed.Factorization p M)
    (out : Wire n g) (a : Algebraic.Aggregate.Guess p)
    (free : RectangleFree (fun x => p.trace Algebraic.Aggregate.interpretation x out) K)
    (dense : 2 ^ (n - 2) ≤
      (accepting fun x => p.trace Algebraic.Aggregate.interpretation x out).card)
    (big : 3 * (Algebraic.Aggregate.Compressed.budget M + Nat.clog 2 K + 3) ≤ n) :
    ∃ w : Wire n g, n - (Algebraic.Aggregate.Compressed.budget M + Nat.clog 2 K + 3) <
      (inputsIn (component (Algebraic.Aggregate.erase p a) w)).card := by
  classical
  let e := Algebraic.Aggregate.erase p a
  let color (w : Wire n g) := component e w
  have linked_color (gate : Fin g) (wire : Wire n g) (h : e.Reads gate wire) :
      color (.gate gate) = color wire := by
    exact component_eq_of_mem ((component_closed e wire gate wire h).mpr
      (mem_component_self e wire))
  have keys : ∀ S : Finset (Finset (Wire n g)),
      ∃ key : (Fin n → Bool) → M × M,
        ∀ x ∈ accepting (fun x => p.trace Algebraic.Aggregate.interpretation x out),
        ∀ y ∈ accepting (fun x => p.trace Algebraic.Aggregate.interpretation x out),
          key x = key y → (p.trace Algebraic.Aggregate.interpretation
            (mix (Finset.univ.filter fun i => color (.input i) ∈ S) x y) out) = true := by
    intro S
    let W := Finset.univ.filter fun w => color w ∈ S
    have closed : Algebraic.Aggregate.ClosedSet p W := by
      apply Algebraic.Aggregate.closedSet_of_erase_closed p a W
      intro gate wire h
      simp only [W, Finset.mem_filter, Finset.mem_univ, true_and, linked_color gate wire h]
    refine ⟨compression.componentKey W, ?_⟩
    intro x hx y hy key
    have hx : p.trace Algebraic.Aggregate.interpretation x out = true := by
      simpa [accepting] using hx
    have hy : p.trace Algebraic.Aggregate.interpretation y out = true := by
      simpa [accepting] using hy
    have hm := compression.accepts_mix_of_componentKey_eq W closed out x y hx hy key
    convert hm using 1
    congr 1
    funext i
    simp [mix, glue, SingleCut.mix, W]

  obtain ⟨part, hpart⟩ := exists_large_fibre_of_mixing
    (n := n) (K := K) (D := Algebraic.Aggregate.Compressed.budget M)
    (T := M × M) free dense
    (fun j => color (.input j)) (Algebraic.Aggregate.Compressed.card_key_le) keys big
  have nonempty : (Finset.univ.filter fun j => color (.input j) = part).Nonempty :=
    Finset.card_pos.mp (by lia)
  obtain ⟨j, hj⟩ := nonempty
  have hj := (Finset.mem_filter.mp hj).2
  refine ⟨.input j, ?_⟩
  have same : (Finset.univ.filter fun i => color (.input i) = part) =
      inputsIn (component e (.input j)) := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, inputsIn]
    rw [← hj]
    constructor
    · intro h
      change Wire.input i ∈ color (.input j)
      rw [← h]
      exact mem_component_self e (.input i)
    · exact component_eq_of_mem
  rwa [same] at hpart


end Algebraic.Cutwidth.Aggregate.Compressed
