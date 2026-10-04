/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Aggregate.Family
public import Mathlib.Logic.Equiv.Bool

/-!
# Rectangle freeness for both output values

Coordinatewise Boolean bijections preserve rectangles and their side sizes. Flipping
the fresh bit of balanced padding negates the output, so the fixed balanced hard
family has the same rectangle threshold for both output values. Its stronger sumset
dispersion contract also bounds every monochromatic coset of an XOR-closed set.
-/

@[expose] public section

namespace Algebraic.Cutwidth

open scoped Classical

/-- Changing each input coordinate by a bijection preserves rectangle freeness. -/
theorem RectangleFree.coordinateEquiv {n K : Nat} {f : Cslib.BooleanFunction n}
    (free : RectangleFree f K) (e : Fin n → Equiv.Perm Bool) :
    RectangleFree (fun x => f (fun i => e i (x i))) K := by
  classical
  intro U P Q accepted
  let left (p : U → Bool) (i : U) := e i (p i)
  let right (q : ↥Uᶜ → Bool) (i : ↥Uᶜ) := e i (q i)
  have injP : Function.Injective left := by
    intro p p' h
    funext i
    exact (e i).injective (congrFun h i)
  have injQ : Function.Injective right := by
    intro q q' h
    funext i
    exact (e i).injective (congrFun h i)
  have same (p : U → Bool) (q : ↥Uᶜ → Bool) :
      glue U (left p) (right q) = fun i => e i (glue U p q i) := by
    funext i
    by_cases hi : i ∈ U <;> simp [glue, left, right, hi]
  have bound := free U (P.image left) (Q.image right) (by
    intro p hp q hq
    obtain ⟨p', hp', rfl⟩ := Finset.mem_image.mp hp
    obtain ⟨q', hq', rfl⟩ := Finset.mem_image.mp hq
    rw [same]
    exact accepted p' hp' q' hq')
  simpa only [Finset.card_image_of_injective _ injP,
    Finset.card_image_of_injective _ injQ] using bound

/-- Negating balanced padding is just a flip of its fresh input coordinate. -/
theorem RectangleFree.not_balancePad {n K : Nat} {f : Cslib.BooleanFunction n}
    (free : RectangleFree (balancePad f) K) :
    RectangleFree (fun x => !(balancePad f x)) K := by
  let e (i : Fin (n + 1)) : Equiv.Perm Bool :=
    if i = 0 then Equiv.boolNot else Equiv.refl Bool
  have same : (fun x => balancePad f (fun i => e i (x i))) =
      (fun x => !(balancePad f x)) := by
    funext x
    have tail : Fin.tail (fun i => e i (x i)) = Fin.tail x := by
      funext i
      simp [Fin.tail, e]
    simp only [balancePad, tail]
    simp [e]
  rw [← same]
  exact free.coordinateEquiv e

/-- A sumset disperser has no large monochromatic coset of an XOR-closed set.
In particular this applies to every affine subspace of the Boolean cube. -/
theorem FlatSumsetDisperser.card_lt_of_monochromatic_coset
    {n K : Nat} {f : Cslib.BooleanFunction n} (disperse : FlatSumsetDisperser f K)
    (V : Finset (Fin n → Bool)) (closed : ∀ x ∈ V, ∀ y ∈ V, xorInput x y ∈ V)
    (a : Fin n → Bool) (b : Bool) (mono : ∀ x ∈ V, f (xorInput a x) = b) :
    V.card < K := by
  classical
  have inj : Function.Injective (xorInput a) := by
    intro x y same
    funext i
    have h := congrFun same i
    cases ha : a i <;> cases hx : x i <;> cases hy : y i <;> simp_all [xorInput]
  by_contra small
  have large : K ≤ V.card := by lia
  obtain ⟨x, hx, y, hy, output⟩ := disperse (V.image (xorInput a)) V
    (by simpa only [Finset.card_image_of_injective _ inj] using large) large (!b)
  obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hx
  have assoc : xorInput (xorInput a z) y = xorInput a (xorInput z y) := by
    funext i
    exact Bool.xor_assoc _ _ _
  rw [assoc, mono _ (closed z hz y hy)] at output
  cases b <;> simp at output

namespace Aggregate

/-- The balanced hard family retains two-sided sumset dispersion, which is
stronger than the exclusion of monochromatic coordinate rectangles. -/
theorem family_eventually_sumsetDisperser :
    ∀ᶠ n in Filter.atTop,
      FlatSumsetDisperser (Extractor.sourceReductionHardFamily n) (familyThreshold n) := by
  filter_upwards [(Filter.tendsto_sub_atTop_nat 1).eventually
    Extractor.sourceReductionFamily_eventually_flat,
    Filter.eventually_ge_atTop 1] with n extract positive
  cases n with
  | zero => lia
  | succ n =>
    simp only [Nat.add_sub_cancel] at extract
    rw [Extractor.sourceReductionHardFamily_succ]
    exact (extract.disperser (by positivity) (by norm_num : (35 / 72 : ℝ) < 1 / 2)).balancePad

/-- The fixed polynomial-time family eventually excludes large rectangles of
either constant output value, at the same threshold. -/
theorem family_eventually_rectangleFree_both :
    ∀ᶠ n in Filter.atTop,
      RectangleFree (Extractor.sourceReductionHardFamily n) (familyThreshold n) ∧
      RectangleFree (fun x => !(Extractor.sourceReductionHardFamily n x))
        (familyThreshold n) := by
  filter_upwards [family_eventually_hard, Filter.eventually_ge_atTop 1] with n hard positive
  refine ⟨hard.1, ?_⟩
  cases n with
  | zero => lia
  | succ n =>
    rw [Extractor.sourceReductionHardFamily_succ] at hard ⊢
    exact hard.1.not_balancePad

end Aggregate
end Algebraic.Cutwidth
