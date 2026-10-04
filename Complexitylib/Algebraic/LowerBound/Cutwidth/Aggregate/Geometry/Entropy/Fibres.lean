/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Aggregate.OneWay
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Aggregate.Geometry.Entropy.Weighted

/-!
# Small fibres of two-sided rectangle-free messages

If the receiving side has at least `2K` assignments, every message fibre has fewer
than `K` assignments: one of the two colors appears in at least `K` columns.
-/

@[expose] public section

namespace Algebraic.Cutwidth.Aggregate.Geometry.Entropy

open scoped Classical

/-- Two-sided rectangle freeness bounds every fibre of an exact one-way message. -/
theorem card_fibre_lt_of_rectangleFree_both {n K : Nat} {f : Cslib.BooleanFunction n}
    (hK : 0 < K) (free : RectangleFree f K) (freeNot : RectangleFree (fun x => !(f x)) K)
    (U : Finset (Fin n)) (large : 2 * K ≤ 2 ^ Uᶜ.card) {T : Type*}
    (summary : OneWaySummary f U T) (message : T) :
    (Finset.univ.filter fun p => summary.key p = message).card < K := by
  classical
  let P := Finset.univ.filter fun p => summary.key p = message
  by_contra! hP
  obtain ⟨p, hp⟩ := Finset.card_pos.mp (lt_of_lt_of_le hK hP)
  let Q := Finset.univ.filter fun q : ↥Uᶜ → Bool => f (glue U p q) = true
  let R := Finset.univ.filter fun q : ↥Uᶜ → Bool => f (glue U p q) ≠ true
  have row (p' : U → Bool) (hp' : p' ∈ P) (q : ↥Uᶜ → Bool) :
      f (glue U p' q) = f (glue U p q) :=
    summary.rows_eq p' p ((Finset.mem_filter.mp hp').2.trans
      (Finset.mem_filter.mp hp).2.symm) q
  have hQ : Q.card < K := (free U P Q (by
    intro p' hp' q hq
    rw [row p' hp' q]
    exact (Finset.mem_filter.mp hq).2)).resolve_left (by lia)
  have hR : R.card < K := (freeNot U P R (by
    intro p' hp' q hq
    dsimp only
    rw [row p' hp' q]
    have h := (Finset.mem_filter.mp hq).2
    cases hval : f (glue U p q) <;> simp_all)).resolve_left (by lia)
  have total : Q.card + R.card = 2 ^ Uᶜ.card := by
    simpa only [Q, R, Finset.card_univ, Fintype.card_fun, Fintype.card_bool,
      Fintype.card_coe] using
      Finset.card_filter_add_card_filter_not (s := Finset.univ)
        (p := fun q : ↥Uᶜ → Bool => f (glue U p q) = true)
  lia

end Algebraic.Cutwidth.Aggregate.Geometry.Entropy
