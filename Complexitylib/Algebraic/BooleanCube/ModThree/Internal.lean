/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.BooleanCube.ModThree.Defs
public import Mathlib.LinearAlgebra.LinearIndependent.Basic
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.Tactic.FinCases

/-!
# Character coefficients of constant Hamming residue

Dedekind's linear independence of characters isolates the signed multiplicity of
every nonzero linear coordinate form. In particular no such form occurs once.
-/

@[expose] public section

namespace Algebraic.BooleanCube.ModThree.Internal

open scoped BigOperators

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]

private theorem sign_add (x y : ZMod 2) : sign (x + y) = sign x * sign y := by
  fin_cases x <;> fin_cases y <;> decide

private theorem sign_injective : Function.Injective sign := by
  decide

private theorem sign_eq (x : ZMod 2) : sign x = 1 - 2 * bit x := by
  fin_cases x <;> decide

private theorem sign_ne_zero (x : ZMod 2) : sign x ≠ 0 := by
  fin_cases x <;> decide

/-- The character associated to a binary linear form. -/
def character (L : V →ₗ[ZMod 2] ZMod 2) : Multiplicative V →* ZMod 3 where
  toFun u := sign (L u.toAdd)
  map_one' := by simp [sign]
  map_mul' u v := by simpa using sign_add (L u.toAdd) (L v.toAdd)

private theorem character_injective : Function.Injective (character (V := V)) := by
  intro L K h
  ext u
  exact sign_injective (DFunLike.congr_fun h (Multiplicative.ofAdd u))

private theorem character_zero : character (0 : V →ₗ[ZMod 2] ZMod 2) = 1 := by
  ext u
  simp [character, sign]

open Classical in
/-- Constancy of the full residue cancels each nonzero character coefficient. -/
theorem signedMultiplicity_eq_zero {ι : Type*} [Fintype ι]
    (a : ι → ZMod 2) (L : ι → V →ₗ[ZMod 2] ZMod 2)
    (constant : ∀ u, residue (fun i => a i + L i u) = residue a)
    (K : V →ₗ[ZMod 2] ZMod 2) (nonzero : K ≠ 0) :
    (∑ i, if L i = K then sign (a i) else 0) = 0 := by
  classical
  have characters (u : V) : ∑ i, sign (a i) * sign (L i u) = ∑ i, sign (a i) := by
    simp_rw [← sign_add, sign_eq]
    simp only [Finset.sum_sub_distrib, ← Finset.mul_sum]
    rw [show (∑ i, bit (a i + L i u)) = ∑ i, bit (a i) from constant u]
  have coefficients :
      (∑ i, Finsupp.single (character (L i)) (sign (a i))) =
        Finsupp.single (1 : Multiplicative V →* ZMod 3) (∑ i, sign (a i)) := by
    apply linearIndependent_monoidHom (Multiplicative V) (ZMod 3)
    ext u
    simpa [map_sum, Finsupp.linearCombination_single, character] using characters u.toAdd
  have nontrivial : character K ≠ 1 := by
    rw [← character_zero]
    exact fun h => nonzero (character_injective h)
  have evaluated := congrArg (fun c => c (character K)) coefficients
  simpa [Finsupp.sum_apply, Finsupp.single_apply, character_injective.eq_iff,
    nontrivial, Ne.symm nontrivial] using evaluated


/-- Every nonzero form appearing in a constant-residue parametrization repeats. -/
theorem exists_duplicate {ι : Type*} [Fintype ι]
    (a : ι → ZMod 2) (L : ι → V →ₗ[ZMod 2] ZMod 2)
    (constant : ∀ u, residue (fun i => a i + L i u) = residue a)
    (i : ι) (nonzero : L i ≠ 0) : ∃ j, j ≠ i ∧ L j = L i := by
  classical
  by_contra missing
  have unique (j : ι) (equal : L j = L i) : j = i := by
    by_contra different
    exact missing ⟨j, different, equal⟩
  have cancelled := signedMultiplicity_eq_zero a L constant (L i) nonzero
  have single : (∑ j, if L j = L i then sign (a j) else 0) = sign (a i) := by
    rw [Finset.sum_eq_single i]
    · simp
    · intro j _ different
      exact ite_eq_right (fun equal => different (unique j equal))
    · simp
  rw [single] at cancelled
  exact sign_ne_zero (a i) cancelled

/-- Constant full residue forces at least two coordinates per parameter dimension. -/
theorem two_mul_finrank_le {ι : Type*} [Fintype ι]
    (a : ι → ZMod 2) (L : ι → V →ₗ[ZMod 2] ZMod 2)
    (injective : Function.Injective fun u => fun i => L i u)
    (constant : ∀ u, residue (fun i => a i + L i u) = residue a) :
    2 * Module.finrank (ZMod 2) V ≤ Fintype.card ι := by
  classical
  let forms := (Finset.univ.image L).erase 0
  have form_mem (i : ι) (h : L i ≠ 0) : L i ∈ forms := by
    simp [forms, h]
  let coordinates : V →ₗ[ZMod 2] (forms → ZMod 2) :=
    LinearMap.pi fun K => K.val
  have coordinates_injective : Function.Injective coordinates := by
    intro u v same
    apply injective
    funext i
    by_cases zero : L i = 0
    · simp [zero]
    · exact congrFun same ⟨L i, form_mem i zero⟩
  have dimension : Module.finrank (ZMod 2) V ≤ forms.card := by
    simpa using LinearMap.finrank_le_finrank_of_injective coordinates_injective
  have multiplicity (K) (mem : K ∈ forms) :
      2 ≤ (Finset.univ.filter fun i => L i = K).card := by
    obtain ⟨nonzero, image⟩ := Finset.mem_erase.mp mem
    obtain ⟨i, _, equal⟩ := Finset.mem_image.mp image
    obtain ⟨j, different, repeated⟩ := exists_duplicate a L constant i
      (by simpa [equal] using nonzero)
    have subset : {i, j} ⊆ Finset.univ.filter fun t => L t = K := by
      intro t ht
      simp only [Finset.mem_insert, Finset.mem_singleton] at ht
      rcases ht with rfl | rfl <;> simp [equal, repeated]
    have bound := Finset.card_le_card subset
    simpa [different, Ne.symm different] using bound
  have count : 2 * forms.card ≤ Fintype.card ι := by
    calc
      2 * forms.card = ∑ _K ∈ forms, 2 := by simp [Nat.mul_comm]
      _ ≤ ∑ K ∈ forms, (Finset.univ.filter fun i => L i = K).card :=
        Finset.sum_le_sum multiplicity
      _ = (Finset.univ.filter fun i => L i ∈ forms).card :=
        Finset.sum_card_fiberwise_eq_card_filter _ _ _
      _ ≤ Fintype.card ι := by simpa using Finset.card_filter_le Finset.univ _
  exact le_trans (Nat.mul_le_mul_left 2 dimension) count

end Algebraic.BooleanCube.ModThree.Internal
