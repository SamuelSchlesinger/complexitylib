/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/
module
public import Complexitylib.Classes.PCP.Internal.KilledWalk

/-!
# Splitting a walk at a step

The surgery behind the crossing decomposition: a walk of length `ℓ` and a
position `i < ℓ` split it into a prefix of length `i`, the label crossed at `i`,
and a suffix of length `ℓ - (i+1)`; gluing puts them back.

Dinur's first-moment count is organised around this. Conditioned on a killed
walk crossing a given dart at step `i`, what remains is exactly a free prefix
and a free suffix — and because the killed law makes their *lengths*
independent too, the count factorises into two copies of the plurality bound.

## Main definitions

- `RegGraph.segPre`, `RegGraph.segSuf` — the two pieces of a split walk
- `RegGraph.segGlue` — gluing them back with a crossing label

## Main results

- `RegGraph.segPre_segGlue`, `RegGraph.segMid_segGlue`, `RegGraph.segSuf_segGlue`
  — gluing then splitting is the identity
- `RegGraph.segGlue_split` — splitting then gluing is the identity
- `RegGraph.walkAt_segSuf`, `RegGraph.revWalk_segSuf` — the suffix walk tracks
  the original, and reversing it gives the reversed walk's prefix
- `RegGraph.card_crossing_eq` — the walks crossing a dart at a step, counted as
  independent prefix and suffix factors
- `RegGraph.card_label_fibre` — labels grouped by their effective walk
- `RegGraph.card_label_crossing` — the two combined: crossing labels counted as
  prefix times suffix times fibre weight
- `RegGraph.walkAt_preWalk` — a killed walk's crossings are the underlying
  fixed-length walk's crossings
-/

@[expose] public section

namespace Complexity

namespace RegGraph

variable (G : RegGraph)

/-- The first `i` steps of a walk. -/
def segPre {ℓ : ℕ} (W : Fin ℓ → G.D) {i : ℕ} (hi : i ≤ ℓ) : Fin i → G.D :=
  G.preWalk W hi

/-- The steps of a walk after position `i`. -/
def segSuf {ℓ : ℕ} (W : Fin ℓ → G.D) (i : ℕ) : Fin (ℓ - (i + 1)) → G.D :=
  fun k => W ⟨i + 1 + k.val, by have := k.isLt; omega⟩

/-- Glue a prefix, a crossing label and a suffix into one walk. -/
def segGlue {ℓ i : ℕ} (p : Fin i → G.D) (d : G.D) (s : Fin (ℓ - (i + 1)) → G.D) :
    Fin ℓ → G.D :=
  fun k =>
    if hk : k.val < i then p ⟨k.val, hk⟩
    else if hk2 : k.val = i then d
    else s ⟨k.val - (i + 1), by have := k.isLt; omega⟩

@[simp] theorem segPre_segGlue {ℓ i : ℕ} (hi : i ≤ ℓ) (p : Fin i → G.D) (d : G.D)
    (s : Fin (ℓ - (i + 1)) → G.D) :
    G.segPre (G.segGlue p d s) hi = p := by
  funext k
  simp [segPre, preWalk, segGlue, k.isLt]

@[simp] theorem segMid_segGlue {ℓ i : ℕ} (hi : i < ℓ) (p : Fin i → G.D) (d : G.D)
    (s : Fin (ℓ - (i + 1)) → G.D) :
    G.segGlue p d s ⟨i, hi⟩ = d := by
  simp [segGlue]

@[simp] theorem segSuf_segGlue {ℓ i : ℕ} (p : Fin i → G.D) (d : G.D)
    (s : Fin (ℓ - (i + 1)) → G.D) :
    G.segSuf (G.segGlue p d s) i = s := by
  funext k
  have hk := k.isLt
  have h1 : ¬ (i + 1 + k.val < i) := by omega
  have h2 : ¬ (i + 1 + k.val = i) := by omega
  simp only [segSuf, segGlue, dite_eq_right h1, dite_eq_right h2]
  congr 1
  have : i + 1 + k.val - (i + 1) = k.val := by omega
  exact Fin.ext this

/-- Splitting a walk and gluing it back returns the walk. -/
theorem segGlue_split {ℓ i : ℕ} (hi : i < ℓ) (W : Fin ℓ → G.D) :
    G.segGlue (G.segPre W (le_of_lt hi)) (W ⟨i, hi⟩) (G.segSuf W i) = W := by
  funext k
  rcases lt_trichotomy k.val i with hk | hk | hk
  · simp [segGlue, segPre, preWalk, hk]
  · have hkey : k = ⟨i, hi⟩ := Fin.ext hk
    subst hkey
    simp
  · have h1 : ¬ (k.val < i) := by omega
    have h2 : ¬ (k.val = i) := by omega
    simp only [segGlue, dite_eq_right h1, dite_eq_right h2, segSuf]
    congr 1
    have : i + 1 + (k.val - (i + 1)) = k.val := by omega
    exact Fin.ext this

/-- The suffix walk, started at the vertex the original walk reaches at step
`i + 1`, tracks the original walk. -/
theorem walkAt_segSuf {ℓ : ℕ} (v : G.V) (W : Fin ℓ → G.D) (i : ℕ) :
    ∀ m : ℕ, m ≤ ℓ - (i + 1) →
      G.walkAt (ℓ - (i + 1)) (G.walkAt ℓ v W (i + 1)) (G.segSuf W i) m
        = G.walkAt ℓ v W (i + 1 + m) := by
  intro m
  induction m with
  | zero => intro _; simp
  | succ m ih =>
      intro hm
      have hm' : m ≤ ℓ - (i + 1) := by omega
      have hmlt : m < ℓ - (i + 1) := by omega
      have hilt : i + 1 + m < ℓ := by omega
      have hidx : i + 1 + (m + 1) = (i + 1 + m) + 1 := by omega
      rw [walkAt, dite_eq_left hmlt, ih hm', hidx, G.walkAt_succ_of_lt v W hilt]
      exact congrArg (G.nbr (G.walkAt ℓ v W (i + 1 + m))) rfl

/-- **Reversal commutes with splitting.** Reversing the suffix of a walk gives
the prefix of the reversed walk: both are the walk that runs from the far end
back to the crossing point. This is what makes the suffix condition in the
powered constraint the same as a condition on walks out of the dart's head. -/
theorem revWalk_segSuf {ℓ : ℕ} (v : G.V) (W : Fin ℓ → G.D) {i : ℕ} (hi : i < ℓ) :
    G.revWalk (G.walkAt ℓ v W (i + 1)) (G.segSuf W i)
      = G.segPre (G.revWalk v W) (show ℓ - (i + 1) ≤ ℓ by omega) := by
  funext k
  have hkl : k.val < ℓ := by omega
  have hlt : ℓ - (k.val + 1) < ℓ := by omega
  have hrev : ((Fin.rev k : Fin (ℓ - (i + 1)))).val = ℓ - (i + 1) - (k.val + 1) :=
    Fin.val_rev k
  have hbound : (Fin.rev k : Fin (ℓ - (i + 1))).val ≤ ℓ - (i + 1) :=
    le_of_lt (Fin.rev k).isLt
  have hpairL : (G.walkAt (ℓ - (i + 1)) (G.walkAt ℓ v W (i + 1)) (G.segSuf W i)
        (Fin.rev k).val, G.segSuf W i (Fin.rev k))
      = (G.walkAt ℓ v W (ℓ - (k.val + 1)), W ⟨ℓ - (k.val + 1), hlt⟩) := by
    refine Prod.ext ?_ ?_
    · have hidx : i + 1 + (Fin.rev k : Fin (ℓ - (i + 1))).val = ℓ - (k.val + 1) := by
        rw [hrev]
        omega
      rw [G.walkAt_segSuf v W i _ hbound, hidx]
    · have hidx : i + 1 + (Fin.rev k : Fin (ℓ - (i + 1))).val = ℓ - (k.val + 1) := by
        rw [hrev]
        omega
      show G.segSuf W i (Fin.rev k) = W ⟨ℓ - (k.val + 1), hlt⟩
      rw [segSuf]
      apply congrArg
      exact Fin.ext hidx
  have hrev2 : ((Fin.rev (⟨k.val, hkl⟩ : Fin ℓ))).val = ℓ - (k.val + 1) :=
    Fin.val_rev _
  have hpairR : (G.walkAt ℓ v W (Fin.rev (⟨k.val, hkl⟩ : Fin ℓ)).val,
        W (Fin.rev (⟨k.val, hkl⟩ : Fin ℓ)))
      = (G.walkAt ℓ v W (ℓ - (k.val + 1)), W ⟨ℓ - (k.val + 1), hlt⟩) := by
    refine Prod.ext ?_ ?_
    · rw [hrev2]
    · exact congrArg W (Fin.ext hrev2)
  show G.revWalk (G.walkAt ℓ v W (i + 1)) (G.segSuf W i) k = G.revWalk v W ⟨k.val, hkl⟩
  simp only [revWalk, backLabel]
  rw [hpairL, hpairR]

/-! ### The crossing bijection -/

/-- **The crossing decomposition.** The walks of length `ℓ` that cross a given
dart `(a, d)` at step `i` are in bijection with pairs of a walk *out of* `a` of
length `i` — the reversed prefix — and a walk of length `ℓ - (i+1)` — the
suffix. Any conditions imposed on the two pieces therefore contribute
independent factors, which is what makes the first moment factorise. -/
theorem card_crossing_eq {ℓ i : ℕ} (hi : i < ℓ) (a : G.V) (d : G.D)
    (Pre : (Fin i → G.D) → Prop) [DecidablePred Pre]
    (Suf : (Fin (ℓ - (i + 1)) → G.D) → Prop) [DecidablePred Suf] :
    (Finset.univ.filter fun x : G.V × (Fin ℓ → G.D) =>
        G.walkAt ℓ x.1 x.2 i = a ∧ x.2 ⟨i, hi⟩ = d
          ∧ Pre (G.revWalk x.1 (G.segPre x.2 (le_of_lt hi))) ∧ Suf (G.segSuf x.2 i)).card
      = (Finset.univ.filter Pre).card * (Finset.univ.filter Suf).card := by
  classical
  rw [← Finset.card_product]
  refine Finset.card_bij'
    (fun x _ => (G.revWalk x.1 (G.segPre x.2 (le_of_lt hi)), G.segSuf x.2 i))
    (fun y _ => (G.walkEnd i a y.1, G.segGlue (G.revWalk a y.1) d y.2)) ?_ ?_ ?_ ?_
  · intro x hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
    simp only [Finset.mem_product, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨hx.2.2.1, hx.2.2.2⟩
  · intro y hy
    simp only [Finset.mem_product, Finset.mem_filter, Finset.mem_univ, true_and] at hy
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    have hp : G.segPre (G.segGlue (G.revWalk a y.1) d y.2) (le_of_lt hi)
        = G.revWalk a y.1 := G.segPre_segGlue (le_of_lt hi) _ d _
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [G.walkAt_eq_walkEnd_prefix _ _ i (le_of_lt hi)]
      have hpre : (fun j : Fin i =>
          G.segGlue (G.revWalk a y.1) d y.2 (Fin.castLE (le_of_lt hi) j))
          = G.revWalk a y.1 := hp
      rw [hpre]
      exact G.walkEnd_revWalk a y.1
    · exact G.segMid_segGlue hi _ d _
    · rw [hp, G.revWalk_revWalk]
      exact hy.1
    · rw [G.segSuf_segGlue]
      exact hy.2
  · intro x hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
    obtain ⟨hwalk, hmid, -, -⟩ := hx
    have ha : G.walkEnd i x.1 (G.segPre x.2 (le_of_lt hi)) = a := by
      rw [← hwalk, G.walkAt_eq_walkEnd_prefix _ _ i (le_of_lt hi)]
      rfl
    refine Prod.ext ?_ ?_
    · show G.walkEnd i a (G.revWalk x.1 (G.segPre x.2 (le_of_lt hi))) = x.1
      rw [← ha]
      exact G.walkEnd_revWalk x.1 (G.segPre x.2 (le_of_lt hi))
    · show G.segGlue (G.revWalk a (G.revWalk x.1 (G.segPre x.2 (le_of_lt hi)))) d
        (G.segSuf x.2 i) = x.2
      rw [← ha, G.revWalk_revWalk, ← hmid]
      exact G.segGlue_split hi x.2
  · intro y hy
    simp only [Finset.mem_product, Finset.mem_filter, Finset.mem_univ, true_and] at hy
    have hp : G.segPre (G.segGlue (G.revWalk a y.1) d y.2) (le_of_lt hi)
        = G.revWalk a y.1 := G.segPre_segGlue (le_of_lt hi) _ d _
    refine Prod.ext ?_ ?_
    · show G.revWalk (G.walkEnd i a y.1)
        (G.segPre (G.segGlue (G.revWalk a y.1) d y.2) (le_of_lt hi)) = y.1
      rw [hp, G.revWalk_revWalk]
    · show G.segSuf (G.segGlue (G.revWalk a y.1) d y.2) i = y.2
      exact G.segSuf_segGlue _ d _

/-! ### From labels to walks -/

/-- **Labels grouped by their effective walk.** Any condition on the starting
vertex and the effective walk is counted by counting *walks*, each weighted by
the number of labels carrying it. This is the step that turns a statement about
killed-walk labels into one about walks, where the crossing decomposition
applies. -/
theorem card_label_fibre {T q ℓ : ℕ} (hq : 0 < q) (hℓ : ℓ < T)
    (P : G.V × (Fin ℓ → G.D) → Prop) [DecidablePred P] :
    (Finset.univ.filter fun z : G.V × ((Fin T → G.D) × (Fin T → Fin q)) =>
        stopAt z.2.2 = ℓ ∧ P (z.1, G.preWalk z.2.1 (le_of_lt hℓ))).card
      = (Finset.univ.filter P).card
        * (G.deg ^ (T - ℓ) * ((q - 1) ^ ℓ * q ^ (T - ℓ - 1))) := by
  classical
  have hmaps : ∀ z ∈ (Finset.univ.filter fun z : G.V × ((Fin T → G.D) × (Fin T → Fin q)) =>
      stopAt z.2.2 = ℓ ∧ P (z.1, G.preWalk z.2.1 (le_of_lt hℓ))),
      (z.1, G.preWalk z.2.1 (le_of_lt hℓ)) ∈ Finset.univ.filter P := by
    intro z hz
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hz ⊢
    exact hz.2
  rw [Finset.card_eq_sum_card_fiberwise hmaps]
  have hfib : ∀ y ∈ Finset.univ.filter P,
      ((Finset.univ.filter fun z : G.V × ((Fin T → G.D) × (Fin T → Fin q)) =>
          stopAt z.2.2 = ℓ ∧ P (z.1, G.preWalk z.2.1 (le_of_lt hℓ))).filter
        fun z => (z.1, G.preWalk z.2.1 (le_of_lt hℓ)) = y).card
      = G.deg ^ (T - ℓ) * ((q - 1) ^ ℓ * q ^ (T - ℓ - 1)) := by
    intro y hy
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy
    have hset : ((Finset.univ.filter fun z : G.V × ((Fin T → G.D) × (Fin T → Fin q)) =>
        stopAt z.2.2 = ℓ ∧ P (z.1, G.preWalk z.2.1 (le_of_lt hℓ))).filter
          fun z => (z.1, G.preWalk z.2.1 (le_of_lt hℓ)) = y)
        = ({y.1} : Finset G.V) ×ˢ
          (Finset.univ.filter fun x : (Fin T → G.D) × (Fin T → Fin q) =>
            G.preWalk x.1 (le_of_lt hℓ) = y.2 ∧ stopAt x.2 = ℓ) := by
      ext z
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_product,
        Finset.mem_singleton, Prod.ext_iff]
      constructor
      · rintro ⟨⟨hlen, -⟩, hz1, hz2⟩
        exact ⟨hz1, hz2, hlen⟩
      · rintro ⟨hz1, hz2, hlen⟩
        refine ⟨⟨hlen, ?_⟩, hz1, hz2⟩
        have hpair : (z.1, G.preWalk z.2.1 (le_of_lt hℓ)) = y := Prod.ext hz1 hz2
        rw [hpair]
        exact hy
    rw [hset, Finset.card_product, Finset.card_singleton, one_mul,
      G.card_killed_fibre hq hℓ y.2]
  rw [Finset.sum_congr rfl hfib, Finset.sum_const, smul_eq_mul]

/-- **The crossing count, at the level of labels.** Chaining the two previous
lemmas: the killed-walk labels of effective length `ℓ` whose walk crosses the
dart `(a, d)` at step `i`, subject to any conditions on the reversed prefix and
on the suffix, number

`(prefix count) * (suffix count) * (fibre weight)`.

The two conditions never interact — that is the independence the killed law
buys, and the reason the first moment factorises into two plurality bounds. -/
theorem card_label_crossing {T q ℓ i : ℕ} (hq : 0 < q) (hℓ : ℓ < T) (hi : i < ℓ)
    (a : G.V) (d : G.D)
    (Pre : (Fin i → G.D) → Prop) [DecidablePred Pre]
    (Suf : (Fin (ℓ - (i + 1)) → G.D) → Prop) [DecidablePred Suf] :
    (Finset.univ.filter fun z : G.V × ((Fin T → G.D) × (Fin T → Fin q)) =>
        stopAt z.2.2 = ℓ ∧
          (G.walkAt ℓ z.1 (G.preWalk z.2.1 (le_of_lt hℓ)) i = a
            ∧ (G.preWalk z.2.1 (le_of_lt hℓ)) ⟨i, hi⟩ = d
            ∧ Pre (G.revWalk z.1 (G.segPre (G.preWalk z.2.1 (le_of_lt hℓ)) (le_of_lt hi)))
            ∧ Suf (G.segSuf (G.preWalk z.2.1 (le_of_lt hℓ)) i))).card
      = (Finset.univ.filter Pre).card * (Finset.univ.filter Suf).card
        * (G.deg ^ (T - ℓ) * ((q - 1) ^ ℓ * q ^ (T - ℓ - 1))) := by
  classical
  rw [G.card_label_fibre hq hℓ (fun y : G.V × (Fin ℓ → G.D) =>
      G.walkAt ℓ y.1 y.2 i = a ∧ y.2 ⟨i, hi⟩ = d
        ∧ Pre (G.revWalk y.1 (G.segPre y.2 (le_of_lt hi)))
        ∧ Suf (G.segSuf y.2 i)),
    G.card_crossing_eq hi a d Pre Suf]

/-- A walk following a prefix of a label sequence agrees with the full walk for
as long as the prefix lasts. This identifies the crossings of a *killed* walk
with those of the underlying fixed-length walk, which is what lets the
correlation bound — stated for fixed length — apply to them. -/
theorem walkAt_preWalk {T ℓ : ℕ} (h : ℓ ≤ T) (x : G.V) (s : Fin T → G.D) :
    ∀ k : ℕ, k ≤ ℓ → G.walkAt ℓ x (G.preWalk s h) k = G.walkAt T x s k := by
  intro k
  induction k with
  | zero => intro _; simp
  | succ k ih =>
      intro hk
      have hkl : k < ℓ := by omega
      have hkT : k < T := by omega
      rw [walkAt, dite_eq_left hkl, ih (by omega), walkAt, dite_eq_left hkT]
      congr 1

end RegGraph

end Complexity
