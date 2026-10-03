/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.CorrelationBreaker.Advice.Internal.Invariant.Defs
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Probability
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity

/-!
# The initial witness for the actual advice chain

Before processing advice, the transcript is the original shared tag and
both current states are right-only. The witness records exactly the given
source factors and average envelopes. A full-width uniform Boolean source
also supplies an exactly uniform actual initial prefix, without enumerating
the Boolean alphabet.
-/

public section

namespace Algebraic.Cutwidth.Extractor.Internal

universe u

/-- Original factored sources construct the weak invariant before any advice is read. -/
@[expose] noncomputable def AdviceInvariant.initial (n m L : Nat) {Z A B : Type u}
    [Fintype Z] [Fintype A] [Fintype B]
    (w : Z → ℝ) (l : Z → A → ℝ) (r : Z → B → ℝ)
    (x : Z → A → Fin n → Bool) (y : Z → B → Fin m → Bool)
    (q q' : Z → B → Fin (matchedBlockOutputBits 64 L) → Bool) (μ ξ : Z → ℝ)
    {ρ : ℝ} (hw : IsProbabilityWeight w) (hl : ∀ z, IsProbabilityWeight (l z))
    (hr : ∀ z, IsProbabilityWeight (r z))
    (left_nonnegative : ∀ z, 0 ≤ μ z) (right_nonnegative : ∀ z, 0 ≤ ξ z)
    (left_cap : ∀ z x₀, w z * mapWeight (x z) (l z) x₀ ≤ μ z)
    (right_cap : ∀ z y₀, w z * mapWeight (y z) (r z) y₀ ≤ ξ z)
    (state : weightDist (retainedSeedWeight w r q)
      (uniformSecondWeight (retainedSeedWeight w r q)) ≤ ρ) :
    AdviceInvariant n m L (factoredWeight w l r) x y
      (fun a => q a.1.1 a.1.2) (fun a => q' a.1.1 a.1.2) False ρ
      (∑ z, μ z) (∑ z, ξ z) where
  Tag := Z
  origin := id
  observe := fun a => a.1.1
  origin_observe := fun _ => rfl
  w := w
  l := l
  r := r
  probability := hw
  left_probability := hl
  right_probability := hr
  factored := mapWeight_id (factoredWeight w l r)
  q := q
  q' := q'
  honest_eq := fun _ => rfl
  tampered_eq := fun _ => rfl
  fixedTampered := fun _ _ => false
  fixed := fun impossible => impossible.elim
  μ := μ
  ξ := ξ
  left_nonnegative := left_nonnegative
  right_nonnegative := right_nonnegative
  left_cap := left_cap
  right_cap := right_cap
  left_sum := le_rfl
  right_sum := le_rfl
  state := state

private def initialSplit (d r : Nat) :
    (Fin (d + r) → Bool) ≃ (Fin d → Bool) × (Fin r → Bool) :=
  ((finSumFinEquiv : Fin d ⊕ Fin r ≃ Fin (d + r)).symm.arrowCongr
    (Equiv.refl Bool)).trans (Equiv.sumArrowEquivProdArrow _ _ _)

private theorem initialPrefix_uniform (d r : Nat) :
    mapWeight (fun q : Fin (d + r) → Bool => fun i : Fin d => q (Fin.castAdd r i))
      (uniformWeight (Fin (d + r) → Bool)) = uniformWeight (Fin d → Bool) := by
  have split : mapWeight (initialSplit d r) (uniformWeight (Fin (d + r) → Bool)) =
      uniformWeight ((Fin d → Bool) × (Fin r → Bool)) := by
    funext y
    rw [mapWeight_equiv_apply]
    unfold uniformWeight
    rw [Fintype.card_congr (initialSplit d r)]
  have first := congrArg (mapWeight Prod.fst) split
  rw [mapWeight_comp] at first
  change mapWeight (fun q : Fin (d + r) → Bool => fun i : Fin d => q (Fin.castAdd r i))
    (uniformWeight (Fin (d + r) → Bool)) = _ at first
  rw [first, mapWeight_fst]
  have positive : (Fintype.card (Fin r → Bool) : ℝ) ≠ 0 := by positivity
  funext y
  simp only [firstWeight, uniformWeight, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul, Fintype.card_prod, Nat.cast_mul]
  field_simp

/-- The actual initial state is uniform whenever its prefix fits in the uniform source. -/
theorem adviceInitialState_uniform (m L : Nat) (size : matchedBlockOutputBits 64 L ≤ m) :
    mapWeight (adviceInitialState m L) (uniformWeight (Fin m → Bool)) =
      uniformWeight (Fin (matchedBlockOutputBits 64 L) → Bool) := by
  have prefixLaw : adviceInitialState m L =
      fun q : Fin m → Bool => fun i => q (Fin.castLE size i) := by
    funext q i
    have bound : i.val < (List.ofFn q).length := by
      simpa only [List.length_ofFn] using lt_of_lt_of_le i.isLt size
    simp only [adviceInitialState, List.getElem?_eq_getElem bound, List.getElem_ofFn,
      Option.getD_some]
    rfl
  rw [prefixLaw]
  obtain ⟨r, rfl⟩ := Nat.exists_eq_add_of_le size
  exact initialPrefix_uniform _ r

end Algebraic.Cutwidth.Extractor.Internal
