/-
Copyright (c) 2025 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Classes.PPoly.Defs
public import Complexitylib.Circuits.Family

/-!
# P/poly and circuit-size classes

This module supplies the public API for nonuniform circuit classes. It relates
the exact pointwise-polynomial definition of `PPoly` to the big-O power
convention used elsewhere in the library.
-/


public section

namespace Complexity

namespace BoolFunFamily

/-- A list belongs to the language of a Boolean function family iff the
    length-indexed function evaluates to `true` on its entries. -/
@[simp] theorem mem_toLanguage {f : BoolFunFamily} {x : List Bool} :
    x ∈ f.toLanguage ↔ f x.length x.get = true := Iff.rfl

/-- The serialization of a length-`n` bitstring lies in `f.toLanguage` iff
    `f n` evaluates to `true` on that bitstring. -/
theorem mem_toLanguage_toList {f : BoolFunFamily} {n : ℕ}
    (x : BitString n) : x.toList ∈ f.toLanguage ↔ f n x = true := by
  change f x.toList.length x.toList.get = true ↔ f n x = true
  have h := List.equivSigmaTuple.apply_symm_apply
    (⟨n, x⟩ : Σ n, BitString n)
  have heval : f x.toList.length x.toList.get = f n x := by
    unfold BitString.toList
    exact congrArg (fun p : Σ n, BitString n => f p.1 p.2) h
  rw [heval]

/-- Distinct Boolean function families induce distinct languages: `toLanguage`
    is injective. -/
theorem toLanguage_injective : Function.Injective toLanguage := by
  intro f g hfg
  funext n x
  have hx := Set.ext_iff.mp hfg x.toList
  simp only [mem_toLanguage_toList] at hx
  cases hfx : f n x <;> cases hgx : g n x <;> simp_all

end BoolFunFamily

namespace CircuitFamily

variable {B : Basis}

/-- A list belongs to the language of a circuit family iff the circuit for its
    length evaluates to `true` on it. -/
@[simp] theorem mem_language {F : CircuitFamily B} {x : List Bool} :
    x ∈ F.language ↔ F.evalList x = true := Iff.rfl

/-- The empty string is in a circuit family's language iff the length-zero
    circuit outputs `true`. -/
theorem nil_mem_language {F : CircuitFamily B} :
    [] ∈ F.language ↔ F.emptyOutput = true := by
  rw [mem_language, F.evalList_nil]

/-- A circuit family decides `L` iff its list-level evaluation agrees with
    membership in `L` on every input. -/
theorem decides_iff (F : CircuitFamily B) (L : Language) :
    F.Decides L ↔ ∀ x, F.evalList x = true ↔ x ∈ L := by
  rw [Decides, Set.ext_iff]
  rfl

/-- `Decides` respects equality of languages: deciding `L` and deciding `K`
    are equivalent when `L = K`. -/
theorem decides_congr (F : CircuitFamily B) {L K : Language} (h : L = K) :
    F.Decides L ↔ F.Decides K := by
  subst K
  rfl

/-- A circuit family decides at most one language: if `F` decides both `L`
    and `K`, then `L = K`. -/
theorem decides_unique (F : CircuitFamily B) {L K : Language}
    (hL : F.Decides L) (hK : F.Decides K) : L = K :=
  hL.symm.trans hK

/-- If `F` decides `L`, then its list-level evaluation returns `true` exactly
    on members of `L`. -/
theorem Decides.evalList {F : CircuitFamily B} {L : Language}
    (h : F.Decides L) (x : List Bool) :
    F.evalList x = true ↔ x ∈ L :=
  (F.decides_iff L).mp h x

/-- A deciding family agrees with language membership on the canonical
    serialization of every fixed-length input. -/
theorem Decides.apply {F : CircuitFamily B} {L : Language}
    (h : F.Decides L) {n : ℕ} (x : BitString n) :
    F.function n x = true ↔ x.toList ∈ L := by
  rw [← F.evalList_toList]
  exact h.evalList x.toList

/-- A circuit family computing a Boolean function family decides the language
    induced by that family. -/
theorem Computes.decides {F : CircuitFamily B} {f : BoolFunFamily}
    (h : F.Computes f) : F.Decides f.toLanguage := by
  change F.function.toLanguage = f.toLanguage
  exact congrArg BoolFunFamily.toLanguage h

/-- Computing a Boolean function family is equivalent to deciding its induced
    language. -/
theorem decides_toLanguage_iff (F : CircuitFamily B) (f : BoolFunFamily) :
    F.Decides f.toLanguage ↔ F.Computes f := by
  constructor
  · intro h
    change F.function.toLanguage = f.toLanguage at h
    exact BoolFunFamily.toLanguage_injective h
  · exact fun h => h.decides

end CircuitFamily

/-- `SIZEWithBasis B` is monotone: pointwise enlarging the size bound only
    enlarges the class. -/
theorem SIZEWithBasis_mono (B : Basis) {s t : ℕ → ℕ}
    (hst : ∀ n, s n ≤ t n) :
    SIZEWithBasis B s ⊆ SIZEWithBasis B t := by
  rintro L ⟨F, hL, hs⟩
  exact ⟨F, hL, F.sizeBoundedBy_mono hs hst⟩

/-- `SIZE` is monotone: pointwise enlarging the size bound only enlarges the
    class. -/
theorem SIZE_mono {s t : ℕ → ℕ} (hst : ∀ n, s n ≤ t n) :
    SIZE s ⊆ SIZE t :=
  SIZEWithBasis_mono Basis.andOr2 hst

section BigO


/-- Big-O characterization of membership in `PPoly`. -/
theorem mem_PPoly_iff {L : Language} :
    L ∈ PPoly ↔
      ∃ (F : CircuitFamily Basis.andOr2) (k : ℕ),
        F.Decides L ∧ F.size =O ((· ^ k) : ℕ → ℕ) := by
  simp only [PPoly, SIZE, SIZEWithBasis, Set.mem_iUnion, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨p, F, hL, hp⟩
    exact ⟨F, p.natDegree, hL, Complexity.BigO.of_polynomial_bound p hp⟩
  · rintro ⟨F, k, hL, hk⟩
    obtain ⟨p, hp⟩ := Complexity.BigO.pow_polynomial_bound hk
    exact ⟨p, F, hL, hp⟩

end BigO

/-- `PPoly` is definitionally the union of the pointwise `SIZE` classes over
    all natural-coefficient polynomials. This is not the substantive
    advice-machine characterization of `P/poly`; that equivalence is exposed
    in `Complexitylib.Classes.PPoly.Advice`. -/
theorem PPoly_eq_iUnion_SIZE :
    PPoly = ⋃ p : Polynomial ℕ, SIZE fun n => p.eval n := rfl

end Complexity
