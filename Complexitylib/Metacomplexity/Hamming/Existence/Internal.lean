/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Metacomplexity.Hamming.Defs
import Complexitylib.Metacomplexity.Hamming.Internal

/-!
# Existence of separated Boolean codes -- proof internals
-/


public section

namespace Complexity

namespace BooleanHamming

private theorem isSeparated_insert
    {length minimumDistance : ℕ} {code : Finset (Word length)}
    (hcode : IsSeparated code minimumDistance) {word : Word length}
    (hword : word ∉ code)
    (hfar : ∀ center ∈ code, minimumDistance ≤ distance word center) :
    IsSeparated (insert word code) minimumDistance := by
  unfold IsSeparated
  rw [Finset.coe_insert]
  have hsymm : Std.Symm (fun left right : Word length =>
      minimumDistance ≤ distance left right) := by
    refine ⟨fun {left right} hdistance => ?_⟩
    rw [distance_comm_internal]
    exact hdistance
  exact (Set.pairwise_insert_of_symm_of_notMem
    (r := fun left right : Word length =>
      minimumDistance ≤ distance left right)
    (a := word) (s := (code : Set (Word length)))
    (by simpa using hword)).2 ⟨hcode, hfar⟩

theorem exists_isSeparated_and_covering_internal
    (length minimumDistance : ℕ) :
    ∃ code : Finset (Word length),
      IsSeparated code minimumDistance ∧
        ∀ word : Word length,
          ∃ center ∈ code,
            distance word center ≤ minimumDistance - 1 := by
  classical
  let family : Finset (Finset (Word length)) :=
    Finset.univ.filter fun code => IsSeparated code minimumDistance
  have hfamily : family.Nonempty := by
    refine ⟨∅, ?_⟩
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
    simp [IsSeparated]
  obtain ⟨code, hcodeFamily, hmaximum⟩ :=
    Finset.exists_max_image family Finset.card hfamily
  have hcode : IsSeparated code minimumDistance := by
    simpa [family] using hcodeFamily
  refine ⟨code, hcode, ?_⟩
  intro word
  by_cases hword : word ∈ code
  · exact ⟨word, hword, by simp [distance_refl_internal]⟩
  · by_contra hcover
    have hfar : ∀ center ∈ code,
        minimumDistance ≤ distance word center := by
      intro center hcenter
      have hnotClose : ¬distance word center ≤ minimumDistance - 1 := by
        intro hclose
        exact hcover ⟨center, hcenter, hclose⟩
      omega
    have hinsert : insert word code ∈ family := by
      simp only [family, Finset.mem_filter, Finset.mem_univ, true_and]
      exact isSeparated_insert hcode hword hfar
    have hcard := hmaximum (insert word code) hinsert
    rw [Finset.card_insert_of_notMem hword] at hcard
    omega

theorem gilbertVarshamov_bound_internal (length minimumDistance : ℕ) :
    ∃ code : Finset (Word length),
      IsSeparated code minimumDistance ∧
        2 ^ length ≤ code.card * volume length (minimumDistance - 1) := by
  obtain ⟨code, hcode, hcover⟩ :=
    exists_isSeparated_and_covering_internal length minimumDistance
  refine ⟨code, hcode, ?_⟩
  have hsubset :
      (Finset.univ : Finset (Word length)) ⊆
        code.biUnion (fun center => ball center (minimumDistance - 1)) := by
    intro word _
    obtain ⟨center, hcenter, hclose⟩ := hcover word
    exact Finset.mem_biUnion.mpr
      ⟨center, hcenter,
        (mem_ball_internal center word (minimumDistance - 1)).mpr hclose⟩
  calc
    2 ^ length = (Finset.univ : Finset (Word length)).card := by
      rw [Finset.card_univ, card_finArrowBool]
    _ ≤ (code.biUnion fun center =>
        ball center (minimumDistance - 1)).card :=
      Finset.card_le_card hsubset
    _ ≤ ∑ center ∈ code,
        (ball center (minimumDistance - 1)).card :=
      Finset.card_biUnion_le
    _ = code.card * volume length (minimumDistance - 1) := by
      simp [card_ball_internal]

end BooleanHamming

end Complexity
