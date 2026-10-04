/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Rectangle
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Data.Finset.Max

/-!
# Restricting rectangle-free functions

Fixing coordinates preserves the rectangle threshold. Among the restrictions fixing
all coordinates outside a set, one has at least the original acceptance density.
-/

@[expose] public section

namespace Algebraic.Cutwidth

open scoped Classical

variable {n m : Nat}

/-- Extend an assignment on `U`, reindexed by `e`, by the fixed outside assignment `z`. -/
noncomputable def subcubeInput (U : Finset (Fin n)) (e : U ≃ Fin m)
    (z : Fin n → Bool) (x : Fin m → Bool) : Fin n → Bool :=
  fun j => if hj : j ∈ U then x (e ⟨j, hj⟩) else z j

/-- A restriction with free coordinates `U`, reindexed by `e`. -/
noncomputable def restriction (f : Cslib.BooleanFunction n) (U : Finset (Fin n))
    (e : U ≃ Fin m) (z : Fin n → Bool) : Cslib.BooleanFunction m :=
  fun x => f (subcubeInput U e z x)

@[simp] theorem subcubeInput_apply_symm (U : Finset (Fin n)) (e : U ≃ Fin m)
    (z : Fin n → Bool) (x : Fin m → Bool) (i : Fin m) :
    subcubeInput U e z x (e.symm i) = x i := by
  simp [subcubeInput, (e.symm i).property]

/-- A restriction cannot introduce a new large one-rectangle. -/
theorem RectangleFree.restriction {f : Cslib.BooleanFunction n} {K : Nat}
    (hf : RectangleFree f K) (U : Finset (Fin n)) (e : U ≃ Fin m)
    (z : Fin n → Bool) : RectangleFree (restriction f U e z) K := by
  intro S P Q hone
  let T := S.image fun i => (e.symm i).val
  have memT (j : Fin n) : j ∈ T ↔ ∃ hj : j ∈ U, e ⟨j, hj⟩ ∈ S := by
    constructor
    · intro hj
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hj
      exact ⟨(e.symm i).property, by simpa using hi⟩
    · rintro ⟨hj, hi⟩
      exact Finset.mem_image.mpr ⟨e ⟨j, hj⟩, hi, by simp⟩
  have memT_symm (i : Fin m) : (e.symm i).val ∈ T ↔ i ∈ S := by
    rw [memT]
    simp
  let inside : (S → Bool) → Fin m → Bool :=
    fun p i => if hi : i ∈ S then p ⟨i, hi⟩ else false
  let outside : (↥Sᶜ → Bool) → Fin m → Bool :=
    fun q i => if hi : i ∈ S then false else q ⟨i, Finset.mem_compl.mpr hi⟩
  let liftP : (S → Bool) → (T → Bool) :=
    fun p j => subcubeInput U e (fun _ => false) (inside p) j
  let liftQ : (↥Sᶜ → Bool) → (↥Tᶜ → Bool) :=
    fun q j => subcubeInput U e z (outside q) j
  have injP : Function.Injective liftP := by
    intro p p' h
    funext i
    have hi : (e.symm i).val ∈ T := (memT_symm i).mpr i.property
    have := congrFun h ⟨(e.symm i).val, hi⟩
    simpa [liftP, inside, i.property] using this
  have injQ : Function.Injective liftQ := by
    intro q q' h
    funext i
    have hi : (e.symm i).val ∉ T := by
      rw [memT_symm]
      exact Finset.mem_compl.mp i.property
    have := congrFun h ⟨(e.symm i).val, Finset.mem_compl.mpr hi⟩
    simpa [liftQ, outside, Finset.mem_compl.mp i.property] using this
  have hglue (p : S → Bool) (q : ↥Sᶜ → Bool) :
      glue T (liftP p) (liftQ q) = subcubeInput U e z (glue S p q) := by
    funext j
    by_cases hj : j ∈ U
    · by_cases hi : e ⟨j, hj⟩ ∈ S
      · have hT : j ∈ T := (memT j).mpr ⟨hj, hi⟩
        simp [glue, hT, liftP, subcubeInput, hj, inside, hi]
      · have hT : j ∉ T := by
          rw [memT]
          rintro ⟨hj', hi'⟩
          exact hi hi'
        simp [glue, hT, liftQ, subcubeInput, hj, outside, hi]
    · have hT : j ∉ T := by
        rw [memT]
        simp [hj]
      simp [glue, hT, liftQ, subcubeInput, hj]
  have hrect := hf T (P.image liftP) (Q.image liftQ) (by
    intro p hp q hq
    obtain ⟨p, hpp, rfl⟩ := Finset.mem_image.mp hp
    obtain ⟨q, hqq, rfl⟩ := Finset.mem_image.mp hq
    rw [hglue]
    exact hone p hpp q hqq)
  simpa [Finset.card_image_of_injective, injP, injQ] using hrect

/-- Some restriction has at least the original acceptance density, expressed without
rational division. The fixed assignment is chosen by finite maximization. -/
theorem exists_card_accepting_le_card_restriction_mul
    (f : Cslib.BooleanFunction n) (U : Finset (Fin n)) (e : U ≃ Fin m) :
    ∃ z : Fin n → Bool,
      (accepting f).card ≤ (accepting (restriction f U e z)).card * 2 ^ (n - U.card) := by
  obtain ⟨z, _, hz⟩ := Finset.exists_max_image Finset.univ
    (fun z : Fin n → Bool => (accepting (restriction f U e z)).card)
    Finset.univ_nonempty
  refine ⟨z, ?_⟩
  let key : (Fin n → Bool) → (↥Uᶜ → Bool) := fun x j => x j
  have fiber : ∀ q ∈ (accepting f).image key,
      ((accepting f).filter fun x => key x = q).card ≤
        (accepting (restriction f U e z)).card := by
    intro q _
    set F := (accepting f).filter fun x => key x = q with hF
    rcases F.eq_empty_or_nonempty with hempty | ⟨x₁, hx₁⟩
    · rw [hempty, Finset.card_empty]
      exact Nat.zero_le _
    let φ : (Fin n → Bool) → (Fin m → Bool) := fun x i => x (e.symm i)
    have outside : ∀ x ∈ F, ∀ y ∈ F, ∀ j ∉ U, x j = y j := by
      intro x hx y hy j hj
      have h := (Finset.mem_filter.mp hx).2.trans (Finset.mem_filter.mp hy).2.symm
      exact congrFun h ⟨j, Finset.mem_compl.mpr hj⟩
    have maps : Set.MapsTo φ ↑F ↑(accepting (restriction f U e x₁)) := by
      intro x hx
      rw [Finset.mem_coe, mem_accepting]
      have hinput : subcubeInput U e x₁ (φ x) = x := by
        funext j
        by_cases hj : j ∈ U
        · simp [subcubeInput, hj, φ]
        · simpa [subcubeInput, hj] using (outside x₁ hx₁ x hx j hj)
      simpa [restriction, hinput] using
        (mem_accepting.mp (Finset.mem_filter.mp hx).1)
    have inj : Set.InjOn φ F := by
      intro x hx y hy h
      funext j
      by_cases hj : j ∈ U
      · have heq := congrFun h (e ⟨j, hj⟩)
        simpa [φ] using heq
      · exact outside x hx y hy j hj
    exact (Finset.card_le_card_of_injOn φ maps inj).trans (hz x₁ (Finset.mem_univ _))
  calc (accepting f).card
      ≤ (accepting (restriction f U e z)).card * ((accepting f).image key).card :=
        Finset.card_le_mul_card_image _ _ fiber
    _ ≤ (accepting (restriction f U e z)).card * Fintype.card (↥Uᶜ → Bool) :=
      Nat.mul_le_mul_left _ (Finset.card_le_univ _)
    _ = (accepting (restriction f U e z)).card * 2 ^ (n - U.card) := by
      simp [Fintype.card_bool]

/-- A one-quarter-dense function has a one-quarter-dense restriction to any set
of at least two free coordinates. -/
theorem exists_dense_restriction
    {f : Cslib.BooleanFunction n} (U : Finset (Fin n)) (e : U ≃ Fin m)
    (hm : 2 ≤ m) (hdense : 2 ^ (n - 2) ≤ (accepting f).card) :
    ∃ z : Fin n → Bool, 2 ^ (m - 2) ≤ (accepting (restriction f U e z)).card := by
  obtain ⟨z, hz⟩ := exists_card_accepting_le_card_restriction_mul f U e
  refine ⟨z, ?_⟩
  have hcard : U.card = m := by simpa using Fintype.card_congr e
  have hmn : m ≤ n := by simpa [hcard] using U.card_le_univ
  have hexp : n - 2 = (m - 2) + (n - m) := by lia
  have hmul := hdense.trans hz
  rw [hcard, hexp, Nat.pow_add] at hmul
  exact Nat.le_of_mul_le_mul_right hmul (Nat.two_pow_pos _)

end Algebraic.Cutwidth
