/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/
module
public import Complexitylib.Classes.PCP.Internal.KilledCSP
public import Complexitylib.Classes.PCP.Internal.FinsetPlurality

/-!
# Decoding a killed-power assignment

An assignment of the killed power labels each vertex with opinions that need not
be consistent with one another. Soundness decodes it into a single assignment of
the original system, by plurality, and counts the failed walk constraints against
that.

The opinion about `v` that a killed walk out of `v` reports is the one its far
end holds, read at the reversed walk — the walk that leads back from that end to
`v`. Letting the killed walk range over all `deg ^ T * q ^ T` labels gives a
multiset of opinions about `v`, and `kPlurality` picks a most frequent one.

This is the distribution the soundness argument needs, and the reason for the
killed walk law: conditioned on a walk crossing a given dart, its prefix and its
suffix are *independent* killed walks out of that dart's two ends, each governed
by exactly this law. So the plurality bound applies to both ends at once, and
the two bounds multiply.

## Main definitions

- `RegCSP.kOpinionAbout` — what the far end of a killed walk says about its start
- `RegCSP.kOpinionCount`, `RegCSP.kPlurality` — the decoded assignment
- `RegCSP.opinionOf` — the report as a function of the effective walk alone
- `RegCSP.card_fibre_opinion` — the reports of one effective length, counted as
  walks times the fibre weight
- `RegCSP.kOpinionCount_eq_sum` — the reports split by effective length
- `RegCSP.truthCount`, `RegCSP.card_le_mul_sum_truthCount` — plurality restated
  as a weighted sum over the walks out of a vertex

## Main results

- `RegCSP.card_le_card_mul_kOpinionCount` — the plurality is reported by at
  least a `1 / |α|` fraction of the killed walks out of a vertex
-/

@[expose] public section

namespace Complexity

namespace RegCSP

variable {α : Type} [Fintype α] [DecidableEq α] [Nonempty α]
variable (R : RegCSP α) (q T : ℕ) (hq : 0 < q)

/-- The label sequences of the killed power. -/
abbrev KLabels (R : RegCSP α) (q T : ℕ) : Type :=
  (Fin T → R.graph.D) × (Fin T → Fin q)

/-- What the far end of the killed walk `x` out of `v` says about `v`: its
opinion read at the reversed walk, which leads from that end back to `v`. -/
def kOpinionAbout (A : (R.killedPow q T hq).Assignment) (v : R.graph.V)
    (x : R.KLabels q T) : α :=
  A (R.graph.killedEnd v x.1 x.2)
    ⟨⟨R.graph.kLen x, by have := R.graph.kLen_le x; omega⟩,
      R.graph.revWalk v (R.graph.kWalk x)⟩

/-- The opinion reported by a killed walk, as a function of its effective length
and effective walk alone. Everything the report depends on — where the walk ends
and the reversed walk it is read at — is determined by those two, so the labels
past the stopping index are free. That is what makes each effective walk carry
the weight `card_killed_fibre` computes. -/
def opinionOf (A : (R.killedPow q T hq).Assignment) (v : R.graph.V) {m : ℕ} (hm : m ≤ T)
    (w : Fin m → R.graph.D) : α :=
  A (R.graph.walkEnd m v w) ⟨⟨m, by omega⟩, R.graph.revWalk v w⟩

omit [Fintype α] [DecidableEq α] [Nonempty α] in
theorem kOpinionAbout_eq_opinionOf (A : (R.killedPow q T hq).Assignment) (v : R.graph.V)
    (x : R.KLabels q T) :
    R.kOpinionAbout q T hq A v x
      = R.opinionOf q T hq A v (stopAt_le x.2) (R.graph.preWalk x.1 (stopAt_le x.2)) := rfl

omit [Fintype α] [DecidableEq α] [Nonempty α] in
/-- Two effective walks of the same length with the same labels give the same
report. Stated with the length as a hypothesis rather than by rewriting, since
the walk's type mentions it: `subst` does the transport that `rw` cannot. -/
theorem opinionOf_congr (A : (R.killedPow q T hq).Assignment) (v : R.graph.V)
    {m m' : ℕ} (hm : m ≤ T) (hm' : m' ≤ T) (hmm : m = m')
    (w : Fin m → R.graph.D) (w' : Fin m' → R.graph.D)
    (hw : ∀ (j : ℕ) (hj : j < m) (hj' : j < m'), w ⟨j, hj⟩ = w' ⟨j, hj'⟩) :
    R.opinionOf q T hq A v hm w = R.opinionOf q T hq A v hm' w' := by
  subst hmm
  have hww : w = w' := by
    funext j
    exact hw j.val j.isLt j.isLt
  subst hww
  rfl

omit [Fintype α] [DecidableEq α] [Nonempty α] in
/-- On the fibre of effective length `m`, the report is the one determined by
the length-`m` prefix. -/
theorem kOpinionAbout_eq_of_stopAt (A : (R.killedPow q T hq).Assignment) (v : R.graph.V)
    (x : R.KLabels q T) {m : ℕ} (hm : m ≤ T) (h : stopAt x.2 = m) :
    R.kOpinionAbout q T hq A v x
      = R.opinionOf q T hq A v hm (R.graph.preWalk x.1 hm) := by
  rw [kOpinionAbout_eq_opinionOf]
  exact R.opinionOf_congr q T hq A v (stopAt_le x.2) hm h _ _ fun j hj hj' => rfl

/-- How many killed walks out of `v` ascribe the value `a` to it. -/
noncomputable def kOpinionCount (A : (R.killedPow q T hq).Assignment) (v : R.graph.V)
    (a : α) : ℕ :=
  (Finset.univ.filter fun x : R.KLabels q T => R.kOpinionAbout q T hq A v x = a).card

omit [Fintype α] [Nonempty α] in
/-- **The fibre partition.** Among the killed walks of effective length `m`,
those reporting `val` are exactly the ones whose effective walk reports `val`,
each carrying the same weight. So the count splits into a count of *walks* times
that weight. -/
theorem card_fibre_opinion (A : (R.killedPow q T hq).Assignment) (v : R.graph.V)
    (val : α) {m : ℕ} (hm : m < T) :
    (Finset.univ.filter fun x : R.KLabels q T =>
        stopAt x.2 = m ∧ R.kOpinionAbout q T hq A v x = val).card
      = (Finset.univ.filter fun w : Fin m → R.graph.D =>
          R.opinionOf q T hq A v (le_of_lt hm) w = val).card
        * (R.graph.deg ^ (T - m) * ((q - 1) ^ m * q ^ (T - m - 1))) := by
  classical
  have hmaps : ∀ x ∈ (Finset.univ.filter fun x : R.KLabels q T =>
      stopAt x.2 = m ∧ R.kOpinionAbout q T hq A v x = val),
      R.graph.preWalk x.1 (le_of_lt hm) ∈ (Finset.univ.filter
        fun w : Fin m → R.graph.D => R.opinionOf q T hq A v (le_of_lt hm) w = val) := by
    intro x hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
    rw [← R.kOpinionAbout_eq_of_stopAt q T hq A v x (le_of_lt hm) hx.1]
    exact hx.2
  rw [Finset.card_eq_sum_card_fiberwise hmaps]
  have hfib : ∀ w ∈ (Finset.univ.filter fun w : Fin m → R.graph.D =>
      R.opinionOf q T hq A v (le_of_lt hm) w = val),
      ((Finset.univ.filter fun x : R.KLabels q T =>
          stopAt x.2 = m ∧ R.kOpinionAbout q T hq A v x = val).filter
        fun x => R.graph.preWalk x.1 (le_of_lt hm) = w).card
      = R.graph.deg ^ (T - m) * ((q - 1) ^ m * q ^ (T - m - 1)) := by
    intro w hw
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hw
    have hset : ((Finset.univ.filter fun x : R.KLabels q T =>
        stopAt x.2 = m ∧ R.kOpinionAbout q T hq A v x = val).filter
          fun x => R.graph.preWalk x.1 (le_of_lt hm) = w)
        = Finset.univ.filter fun x : R.KLabels q T =>
            R.graph.preWalk x.1 (le_of_lt hm) = w ∧ stopAt x.2 = m := by
      ext x
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨⟨hlen, -⟩, hpre⟩
        exact ⟨hpre, hlen⟩
      · rintro ⟨hpre, hlen⟩
        refine ⟨⟨hlen, ?_⟩, hpre⟩
        rw [R.kOpinionAbout_eq_of_stopAt q T hq A v x (le_of_lt hm) hlen, hpre]
        exact hw
    rw [hset, R.graph.card_killed_fibre hq hm w]
  rw [Finset.sum_congr rfl hfib, Finset.sum_const, smul_eq_mul]

/-- The plurality decoding: every vertex is given a value that the ends of the
killed walks out of it ascribe to it most often. -/
noncomputable def kPlurality (A : (R.killedPow q T hq).Assignment) (v : R.graph.V) : α :=
  Classical.choose (exists_plurality (Finset.univ : Finset (R.KLabels q T))
    (R.kOpinionAbout q T hq A v))

/-- **Pigeonhole.** At least a `1 / |α|` fraction of the killed walks out of `v`
report the decoded value. -/
theorem card_le_card_mul_kOpinionCount (A : (R.killedPow q T hq).Assignment)
    (v : R.graph.V) :
    Fintype.card (R.KLabels q T)
      ≤ Fintype.card α * R.kOpinionCount q T hq A v (R.kPlurality q T hq A v) := by
  have h := Classical.choose_spec (exists_plurality (Finset.univ : Finset (R.KLabels q T))
    (R.kOpinionAbout q T hq A v))
  exact h

omit [Fintype α] [Nonempty α] in
/-- The reports split by effective length. -/
theorem kOpinionCount_eq_sum (A : (R.killedPow q T hq).Assignment) (v : R.graph.V)
    (val : α) :
    R.kOpinionCount q T hq A v val
      = ∑ m ∈ Finset.range (T + 1),
          (Finset.univ.filter fun x : R.KLabels q T =>
            stopAt x.2 = m ∧ R.kOpinionAbout q T hq A v x = val).card := by
  classical
  have hmaps : ∀ x ∈ (Finset.univ.filter fun x : R.KLabels q T =>
      R.kOpinionAbout q T hq A v x = val), stopAt x.2 ∈ Finset.range (T + 1) := by
    intro x _
    simp only [Finset.mem_range]
    have := stopAt_le x.2
    omega
  rw [kOpinionCount, Finset.card_eq_sum_card_fiberwise hmaps]
  refine Finset.sum_congr rfl fun m _ => ?_
  congr 1
  ext x
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  tauto

/-- How many length-`m` walks out of `v` have a far end reporting the decoded
value. Total in `m`, so that sums over lengths need no side conditions. -/
noncomputable def truthCount (A : (R.killedPow q T hq).Assignment) (v : R.graph.V)
    (m : ℕ) : ℕ :=
  if hm : m ≤ T then
    (Finset.univ.filter fun w : Fin m → R.graph.D =>
      R.opinionOf q T hq A v hm w = R.kPlurality q T hq A v).card
  else 0

theorem card_fibre_truth (A : (R.killedPow q T hq).Assignment) (v : R.graph.V)
    {m : ℕ} (hm : m < T) :
    (Finset.univ.filter fun x : R.KLabels q T =>
        stopAt x.2 = m ∧ R.kOpinionAbout q T hq A v x = R.kPlurality q T hq A v).card
      = R.truthCount q T hq A v m
        * (R.graph.deg ^ (T - m) * ((q - 1) ^ m * q ^ (T - m - 1))) := by
  rw [R.card_fibre_opinion q T hq A v _ hm, truthCount, dite_eq_left (le_of_lt hm)]

omit [Fintype α] [DecidableEq α] [Nonempty α] in
theorem card_KLabels : Fintype.card (R.KLabels q T) = R.graph.deg ^ T * q ^ T := by
  rw [Fintype.card_prod, Fintype.card_fun, Fintype.card_fun, Fintype.card_fin,
    Fintype.card_fin]
  rfl

omit [Fintype α] [DecidableEq α] [Nonempty α] in
/-- The killed walks that never stop. This is the truncation term, and it is an
exponentially small fraction `((q-1)/q) ^ T` of all labels. -/
theorem card_stopAt_eq_top :
    (Finset.univ.filter fun x : R.KLabels q T => stopAt x.2 = T).card
      = R.graph.deg ^ T * (q - 1) ^ T := by
  classical
  have hsig : (Finset.univ.filter fun c : Fin T → Fin q => stopAt c = T).card
      = (q - 1) ^ T := by
    have hsame : (Finset.univ.filter fun c : Fin T → Fin q => stopAt c = T)
        = (Finset.univ.filter fun c : Fin T → Fin q => T ≤ stopAt c) := by
      ext c
      have := stopAt_le c
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      omega
    rw [hsame, card_le_stopAt (le_refl T)]
    simp
  have hset : (Finset.univ.filter fun x : R.KLabels q T => stopAt x.2 = T)
      = (Finset.univ : Finset (Fin T → R.graph.D))
        ×ˢ (Finset.univ.filter fun c : Fin T → Fin q => stopAt c = T) := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_product]
  rw [hset, Finset.card_product, hsig, Finset.card_univ, Fintype.card_fun,
    Fintype.card_fin]
  rfl

/-- **Plurality, in terms of walks.** At least a `1 / |α|` fraction of all
killed-walk labels report the decoded value, and splitting that count by
effective length turns it into a statement about the *walks* out of `v`: the
weighted sum of `truthCount` is large, up to the exponentially small truncation
term of walks that never stop.

This is the form the first moment consumes, since the crossing decomposition
produces exactly these weighted sums — one for the prefix and one for the
suffix, with independent lengths. -/
theorem card_le_mul_sum_truthCount (A : (R.killedPow q T hq).Assignment)
    (v : R.graph.V) :
    R.graph.deg ^ T * q ^ T
      ≤ Fintype.card α * ((∑ m ∈ Finset.range T,
          R.truthCount q T hq A v m
            * (R.graph.deg ^ (T - m) * ((q - 1) ^ m * q ^ (T - m - 1))))
        + R.graph.deg ^ T * (q - 1) ^ T) := by
  classical
  have h1 := R.card_le_card_mul_kOpinionCount q T hq A v
  rw [R.card_KLabels q T, R.kOpinionCount_eq_sum q T hq A v, Finset.sum_range_succ] at h1
  have h2 : ∀ m ∈ Finset.range T,
      (Finset.univ.filter fun x : R.KLabels q T =>
          stopAt x.2 = m ∧ R.kOpinionAbout q T hq A v x = R.kPlurality q T hq A v).card
        = R.truthCount q T hq A v m
          * (R.graph.deg ^ (T - m) * ((q - 1) ^ m * q ^ (T - m - 1))) := by
    intro m hm
    exact R.card_fibre_truth q T hq A v (Finset.mem_range.mp hm)
  rw [Finset.sum_congr rfl h2] at h1
  have h3 : (Finset.univ.filter fun x : R.KLabels q T =>
      stopAt x.2 = T ∧ R.kOpinionAbout q T hq A v x = R.kPlurality q T hq A v).card
      ≤ R.graph.deg ^ T * (q - 1) ^ T := by
    rw [← R.card_stopAt_eq_top q T]
    refine Finset.card_le_card ?_
    intro x hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
    exact hx.1
  exact le_trans h1 (Nat.mul_le_mul_left _ (Nat.add_le_add_left h3 _))

/-- The decoded assignment of the original system. -/
noncomputable def kDecode (A : (R.killedPow q T hq).Assignment) : R.Assignment :=
  fun v => R.kPlurality q T hq A v

end RegCSP

end Complexity
