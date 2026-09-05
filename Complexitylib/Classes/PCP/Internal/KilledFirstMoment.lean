/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/
module
public import Complexitylib.Classes.PCP.Internal.KilledPlurality
public import Complexitylib.Classes.PCP.Internal.WalkSplit
public import Complexitylib.Classes.PCP.Internal.DartCorrelation
public import Complexitylib.Classes.PCP.Internal.SecondMoment
public import Mathlib.Algebra.BigOperators.Intervals

/-!
# The first moment of Dinur's powering step

Counting, for a fixed faulty dart of `R` and a fixed crossing position, the
killed-power constraints that the dart breaks — those whose walk crosses it and
whose two ends both hold the decoded opinion about the dart's endpoints.

`WalkSplit.card_label_crossing` already counts such labels as
`(prefix count) * (suffix count) * (fibre weight)`, for *arbitrary* conditions
on the two pieces. Here the conditions are the ones the powered constraint
actually reads, and then each count is by definition a `truthCount` — the
quantity `KilledPlurality.card_le_mul_sum_truthCount` bounds from below.

That is the whole point of the killed walk law: the prefix and suffix conditions
concern different vertices and *independent* lengths, so summing over both
positions multiplies two plurality bounds instead of entangling them.

## Main results

- `RegCSP.opinionOf_eq_startIdx`, `RegCSP.opinionOf_eq_endIdx` — the counted
  conditions are the constraint's own two terms
- `RegCSP.card_good_crossing` — the count, as a product of two `truthCount`s and
  the fibre weight
- `RegCSP.not_satisfies_of_good_crossing` — every counted crossing breaks its
  constraint
- `weight_factor` — the crossing weight is the product of the two plurality
  weights, up to a fixed normaliser
- `sum_crossing_factor`, `sum_goodCount_factor` — hence the double sum over
  positions is a product of two weighted sums
- `geom_tail_le`, `RegCSP.truthCount_le` — the discarded positions carry
  geometrically little weight
- `RegCSP.card_le_mul_sum_truthCount_half` — plurality survives the restriction
  to half the range
- `RegCSP.card_good_crossing_sq` — the count indexed by the two lengths
- `RegCSP.halfSum`, `pluralityLoss`, `RegCSP.per_dart_lower` — the first moment
  for a single dart of `R`
- `RegCSP.sum_dart_lower` — summed over all the failed darts
- `RegCSP.goodCrossings`, `RegCSP.mem_unsatDarts_of_goodCrossings_nonempty` — the
  count the second-moment method uses, and its support condition
- `RegCSP.sum_sq_goodCrossings` — its second moment, as a sum over pairs
- `RegCSP.goodPos`, `RegCSP.card_pairs_goodPos` — the same positions indexed by
  naturals, so summation order can be exchanged
- `RegCSP.sum_card_pairs_eq` — that exchange, carried out
- `RegCSP.card_both_good_le` — two good crossings imply two failed crossings of
  the underlying walk
- `RegCSP.sum_pairs_bound` — the second moment's pair term, bounded
- `RegCSP.sum_sq_goodCrossings_le` — the second moment of the crossing count
- `RegCSP.sum_card_goodPos_eq` — the first moment, with counting exchanged
- `RegCSP.sum_over_len_le` — summing over effective lengths stays within the
  constraints good at a position
- `RegCSP.mem_goodPos_of_crossing` — a counted crossing of a failed dart is a
  good position
- `RegCSP.crossingSet`, `RegCSP.sum_crossingSet_le` — the counted sets, and that
  different darts contribute disjointly
- `RegCSP.sum_len_pos_le`, `RegCSP.sum_Cd_le_sum_goodCrossings` — the first
  moment is bounded by the total crossing count
- `RegCSP.crossCount`, `RegCSP.sum_goodCrossings_ge` — the first moment in closed
  form
- `RegCSP.card_unsatDarts_ge` — the second-moment bound on unsatisfied
  constraints
- `RegCSP.powering_soundness` — soundness of the killed powering step
- `RegCSP.unsatFrac_killedPow_ge`, `RegCSP.le_unsatVal_killedPow` — the same
  bound on the unsatisfied fraction, and on the value
-/

@[expose] public section

namespace Complexity

/-- **The weights factorise.** The fibre weight of a walk of length `i + j + 1`
is, up to the fixed normaliser `deg ^ (T+1) * q ^ T`, the product of the weights
of lengths `i` and `j` times `q - 1`.

This identity is why the first moment splits: summing a product
`truthCount a i * truthCount b j` against the crossing weight is the same as
multiplying two sums each weighted exactly as the plurality bound weights them.
Geometric weights are what make this work, and geometric weights are what the
killed walk law produces. -/
theorem weight_factor (deg q : ℕ) {T i j : ℕ} (h : i + j + 1 < T) :
    (deg ^ (T - (i + j + 1)) * ((q - 1) ^ (i + j + 1) * q ^ (T - (i + j + 1) - 1)))
        * (deg ^ (T + 1) * q ^ T)
      = (deg ^ (T - i) * ((q - 1) ^ i * q ^ (T - i - 1)))
        * (deg ^ (T - j) * ((q - 1) ^ j * q ^ (T - j - 1))) * (q - 1) := by
  have e1 : deg ^ (T - (i + j + 1)) * deg ^ (T + 1) = deg ^ (T - i) * deg ^ (T - j) := by
    rw [← pow_add, ← pow_add]
    congr 1
    omega
  have e2 : q ^ (T - (i + j + 1) - 1) * q ^ T = q ^ (T - i - 1) * q ^ (T - j - 1) := by
    rw [← pow_add, ← pow_add]
    congr 1
    omega
  have e3 : (q - 1) ^ (i + j + 1) = (q - 1) ^ i * (q - 1) ^ j * (q - 1) := by
    rw [pow_add, pow_add, pow_one]
  calc (deg ^ (T - (i + j + 1)) * ((q - 1) ^ (i + j + 1) * q ^ (T - (i + j + 1) - 1)))
        * (deg ^ (T + 1) * q ^ T)
      = (deg ^ (T - (i + j + 1)) * deg ^ (T + 1)) * (q - 1) ^ (i + j + 1)
        * (q ^ (T - (i + j + 1) - 1) * q ^ T) := by ring
    _ = (deg ^ (T - i) * deg ^ (T - j)) * ((q - 1) ^ i * (q - 1) ^ j * (q - 1))
        * (q ^ (T - i - 1) * q ^ (T - j - 1)) := by rw [e1, e2, e3]
    _ = (deg ^ (T - i) * ((q - 1) ^ i * q ^ (T - i - 1)))
        * (deg ^ (T - j) * ((q - 1) ^ j * q ^ (T - j - 1))) * (q - 1) := by ring

/-- **The double sum factorises.** Over a square of positions small enough that
`i + j + 1` never reaches the truncation `T`, the crossing sum is — up to the
normaliser — `(q-1)` times the product of the two weighted sums that the
plurality bound controls.

Restricting to a square rather than the full triangle `i + j + 1 < T` is what
makes this an identity: the triangle is not a product region. The tail thrown
away is geometrically small. -/
theorem sum_crossing_factor (deg q T H : ℕ) (hH : 2 * H + 1 < T) (f g : ℕ → ℕ) :
    (∑ i ∈ Finset.range (H + 1), ∑ j ∈ Finset.range (H + 1),
        f i * g j * (deg ^ (T - (i + j + 1))
          * ((q - 1) ^ (i + j + 1) * q ^ (T - (i + j + 1) - 1))))
        * (deg ^ (T + 1) * q ^ T)
      = (q - 1) * ((∑ i ∈ Finset.range (H + 1),
            f i * (deg ^ (T - i) * ((q - 1) ^ i * q ^ (T - i - 1))))
          * (∑ j ∈ Finset.range (H + 1),
            g j * (deg ^ (T - j) * ((q - 1) ^ j * q ^ (T - j - 1))))) := by
  have key : ∀ i ∈ Finset.range (H + 1), ∀ j ∈ Finset.range (H + 1),
      (f i * g j * (deg ^ (T - (i + j + 1))
          * ((q - 1) ^ (i + j + 1) * q ^ (T - (i + j + 1) - 1)))) * (deg ^ (T + 1) * q ^ T)
      = (q - 1) * ((f i * (deg ^ (T - i) * ((q - 1) ^ i * q ^ (T - i - 1))))
        * (g j * (deg ^ (T - j) * ((q - 1) ^ j * q ^ (T - j - 1))))) := by
    intro i hi j hj
    simp only [Finset.mem_range] at hi hj
    have hij : i + j + 1 < T := by omega
    have hw := weight_factor deg q hij
    calc (f i * g j * (deg ^ (T - (i + j + 1))
            * ((q - 1) ^ (i + j + 1) * q ^ (T - (i + j + 1) - 1)))) * (deg ^ (T + 1) * q ^ T)
        = f i * g j * ((deg ^ (T - (i + j + 1))
            * ((q - 1) ^ (i + j + 1) * q ^ (T - (i + j + 1) - 1)))
            * (deg ^ (T + 1) * q ^ T)) := by ring
      _ = f i * g j * ((deg ^ (T - i) * ((q - 1) ^ i * q ^ (T - i - 1)))
            * (deg ^ (T - j) * ((q - 1) ^ j * q ^ (T - j - 1))) * (q - 1)) := by rw [hw]
      _ = (q - 1) * ((f i * (deg ^ (T - i) * ((q - 1) ^ i * q ^ (T - i - 1))))
            * (g j * (deg ^ (T - j) * ((q - 1) ^ j * q ^ (T - j - 1))))) := by ring
  calc (∑ i ∈ Finset.range (H + 1), ∑ j ∈ Finset.range (H + 1),
        f i * g j * (deg ^ (T - (i + j + 1))
          * ((q - 1) ^ (i + j + 1) * q ^ (T - (i + j + 1) - 1))))
        * (deg ^ (T + 1) * q ^ T)
      = ∑ i ∈ Finset.range (H + 1), ∑ j ∈ Finset.range (H + 1),
        ((f i * g j * (deg ^ (T - (i + j + 1))
          * ((q - 1) ^ (i + j + 1) * q ^ (T - (i + j + 1) - 1))))
          * (deg ^ (T + 1) * q ^ T)) := by
        rw [Finset.sum_mul]
        exact Finset.sum_congr rfl fun i _ => Finset.sum_mul _ _ _
    _ = ∑ i ∈ Finset.range (H + 1), ∑ j ∈ Finset.range (H + 1),
        ((q - 1) * ((f i * (deg ^ (T - i) * ((q - 1) ^ i * q ^ (T - i - 1))))
          * (g j * (deg ^ (T - j) * ((q - 1) ^ j * q ^ (T - j - 1)))))) :=
        Finset.sum_congr rfl fun i hi => Finset.sum_congr rfl fun j hj => key i hi j hj
    _ = (q - 1) * ((∑ i ∈ Finset.range (H + 1),
            f i * (deg ^ (T - i) * ((q - 1) ^ i * q ^ (T - i - 1))))
          * (∑ j ∈ Finset.range (H + 1),
            g j * (deg ^ (T - j) * ((q - 1) ^ j * q ^ (T - j - 1))))) := by
        rw [Finset.sum_mul_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Finset.mul_sum]

/-- **The geometric tail.** The weights decay geometrically, so the positions
beyond `k` carry at most `(q-1)^k * q^(T-k)` — a `((q-1)/q)^k` fraction of the
total. This is what makes both the truncation term and the restriction to a
square of positions harmless. -/
theorem geom_tail_le {q : ℕ} (hq : 0 < q) (T : ℕ) : ∀ (n k : ℕ), T - k = n → k ≤ T →
    ∑ m ∈ Finset.Ico k T, (q - 1) ^ m * q ^ (T - 1 - m) ≤ (q - 1) ^ k * q ^ (T - k) := by
  intro n
  induction n with
  | zero =>
      intro k hk hkT
      have hkeq : k = T := by omega
      subst hkeq
      simp
  | succ n ih =>
      intro k hk hkT
      have hklt : k < T := by omega
      have hrec := ih (k + 1) (by omega) (by omega)
      rw [Finset.sum_eq_sum_Ico_succ_bot hklt]
      have hstep : (q - 1) ^ k * q ^ (T - 1 - k) + (q - 1) ^ (k + 1) * q ^ (T - (k + 1))
          = (q - 1) ^ k * q ^ (T - k) := by
        have hq1 : 1 + (q - 1) = q := by omega
        have hidx : T - k = (T - 1 - k) + 1 := by omega
        have hidx2 : T - (k + 1) = T - 1 - k := by omega
        rw [hidx, hidx2, pow_succ, pow_succ]
        calc (q - 1) ^ k * q ^ (T - 1 - k) + (q - 1) ^ k * (q - 1) * q ^ (T - 1 - k)
            = (q - 1) ^ k * q ^ (T - 1 - k) * (1 + (q - 1)) := by ring
          _ = (q - 1) ^ k * (q ^ (T - 1 - k) * q) := by rw [hq1]; ring
      calc (q - 1) ^ k * q ^ (T - 1 - k) + ∑ m ∈ Finset.Ico (k + 1) T,
            (q - 1) ^ m * q ^ (T - 1 - m)
          ≤ (q - 1) ^ k * q ^ (T - 1 - k) + (q - 1) ^ (k + 1) * q ^ (T - (k + 1)) :=
            Nat.add_le_add_left hrec _
        _ = (q - 1) ^ k * q ^ (T - k) := hstep

/-- `sum_crossing_factor` in the form callers can use: the counts are supplied
as an abstract function `C`, since the concrete count at position `(i, j)` is a
`Finset.card` whose very statement needs `i + j + 1 < T`, a fact only available
pointwise inside the sum. -/
theorem sum_goodCount_factor (deg q T H : ℕ) (hH : 2 * H + 1 < T) (f g : ℕ → ℕ)
    (C : ℕ → ℕ → ℕ)
    (hC : ∀ i ∈ Finset.range (H + 1), ∀ j ∈ Finset.range (H + 1),
      C i j = f i * g j * (deg ^ (T - (i + j + 1))
        * ((q - 1) ^ (i + j + 1) * q ^ (T - (i + j + 1) - 1)))) :
    (∑ i ∈ Finset.range (H + 1), ∑ j ∈ Finset.range (H + 1), C i j)
        * (deg ^ (T + 1) * q ^ T)
      = (q - 1) * ((∑ i ∈ Finset.range (H + 1),
            f i * (deg ^ (T - i) * ((q - 1) ^ i * q ^ (T - i - 1))))
          * (∑ j ∈ Finset.range (H + 1),
            g j * (deg ^ (T - j) * ((q - 1) ^ j * q ^ (T - j - 1))))) := by
  rw [Finset.sum_congr rfl fun i hi => Finset.sum_congr rfl fun j hj => hC i hi j hj]
  exact sum_crossing_factor deg q T H hH f g

namespace RegCSP

variable {α : Type} [Fintype α] [DecidableEq α] [Nonempty α]
variable (R : RegCSP α) (q T : ℕ) (hq : 0 < q)

omit [Fintype α] [DecidableEq α] [Nonempty α] in
/-- The prefix condition counted above is exactly the constraint's own
`startIdx` term: the opinion `v` holds about the walk's `i`-th vertex. -/
theorem opinionOf_eq_startIdx (A : (R.killedPow q T hq).Assignment) {ℓ : ℕ}
    (hℓ : ℓ ≤ T) (v : R.graph.V) (W : Fin ℓ → R.graph.D) (i : Fin ℓ)
    (hiT : i.val ≤ T) :
    R.opinionOf q T hq A (R.graph.walkAt ℓ v W i.val) hiT
        (R.graph.revWalk v (R.graph.segPre W (le_of_lt i.isLt)))
      = A v (R.graph.startIdx hℓ W i) := by
  have hP : R.graph.walkEnd i.val v (R.graph.segPre W (le_of_lt i.isLt))
      = R.graph.walkAt ℓ v W i.val :=
    (R.graph.walkAt_eq_walkEnd_prefix v W i.val (le_of_lt i.isLt)).symm
  rw [opinionOf, ← hP, R.graph.walkEnd_revWalk, R.graph.revWalk_revWalk]
  rfl

omit [Fintype α] [DecidableEq α] [Nonempty α] in
/-- The suffix condition counted above is exactly the constraint's own `endIdx`
term: the opinion the walk's far end holds about the `(i+1)`-st vertex. -/
theorem opinionOf_eq_endIdx (A : (R.killedPow q T hq).Assignment) {ℓ : ℕ}
    (hℓ : ℓ ≤ T) (v : R.graph.V) (W : Fin ℓ → R.graph.D) (i : Fin ℓ)
    (hjT : ℓ - (i.val + 1) ≤ T) :
    R.opinionOf q T hq A (R.graph.walkAt ℓ v W (i.val + 1)) hjT
        (R.graph.segSuf W i.val)
      = A (R.graph.walkEnd ℓ v W) (R.graph.endIdx hℓ v W i) := by
  have hend : R.graph.walkEnd (ℓ - (i.val + 1)) (R.graph.walkAt ℓ v W (i.val + 1))
      (R.graph.segSuf W i.val) = R.graph.walkEnd ℓ v W := by
    have hidx : i.val + 1 + (ℓ - (i.val + 1)) = ℓ := by
      have := i.isLt
      omega
    have h := R.graph.walkAt_segSuf v W i.val (ℓ - (i.val + 1)) (le_refl _)
    rw [hidx] at h
    simp only [R.graph.walkAt_self_eq_walkEnd] at h
    exact h
  rw [opinionOf, hend, R.graph.revWalk_segSuf v W i.isLt]
  rfl

/-- **The crossing count with the constraint's own conditions.** For a dart
`(a, d)` of `R` and a crossing position `i` inside an effective length `ℓ`, the
killed-power constraints crossing `(a, d)` at `i` with truthful opinions at both
ends number `truthCount a i * truthCount (nbr a d) (ℓ - (i+1))` times the fibre
weight. -/
theorem card_good_crossing (A : (R.killedPow q T hq).Assignment) (a : R.graph.V)
    (d : R.graph.D) {ℓ i : ℕ} (hℓ : ℓ < T) (hi : i < ℓ) (hiT : i ≤ T)
    (hjT : ℓ - (i + 1) ≤ T) :
    (Finset.univ.filter fun z : R.graph.V × ((Fin T → R.graph.D) × (Fin T → Fin q)) =>
        stopAt z.2.2 = ℓ ∧
          (R.graph.walkAt ℓ z.1 (R.graph.preWalk z.2.1 (le_of_lt hℓ)) i = a
            ∧ (R.graph.preWalk z.2.1 (le_of_lt hℓ)) ⟨i, hi⟩ = d
            ∧ R.opinionOf q T hq A a hiT (R.graph.revWalk z.1
                (R.graph.segPre (R.graph.preWalk z.2.1 (le_of_lt hℓ)) (le_of_lt hi)))
              = R.kPlurality q T hq A a
            ∧ R.opinionOf q T hq A (R.graph.nbr a d) hjT
                (R.graph.segSuf (R.graph.preWalk z.2.1 (le_of_lt hℓ)) i)
              = R.kPlurality q T hq A (R.graph.nbr a d))).card
      = R.truthCount q T hq A a i
        * R.truthCount q T hq A (R.graph.nbr a d) (ℓ - (i + 1))
        * (R.graph.deg ^ (T - ℓ) * ((q - 1) ^ ℓ * q ^ (T - ℓ - 1))) := by
  classical
  rw [R.graph.card_label_crossing hq hℓ hi a d
      (fun p => R.opinionOf q T hq A a hiT p = R.kPlurality q T hq A a)
      (fun s => R.opinionOf q T hq A (R.graph.nbr a d) hjT s
        = R.kPlurality q T hq A (R.graph.nbr a d)),
    truthCount, dite_eq_left hiT, truthCount, dite_eq_left hjT]

/-! ### Every counted crossing breaks its constraint -/

/-- **The counted darts really are unsatisfied.** A killed walk crossing a dart
that the decoded assignment fails, with both ends holding the decoded opinion
about that dart's two vertices, breaks its own constraint. The two hypotheses
are exactly the conditions `card_good_crossing` counts, turned into the
constraint's `startIdx` / `endIdx` terms by the two identification lemmas. -/
theorem not_satisfies_of_good_crossing (A : (R.killedPow q T hq).Assignment)
    (z : R.graph.V × R.KLabels q T) (i : Fin (R.graph.kLen z.2))
    (hiT : i.val ≤ T) (hjT : R.graph.kLen z.2 - (i.val + 1) ≤ T)
    (hfault : ¬ R.Satisfies (R.kDecode q T hq A)
      (R.graph.walkAt (R.graph.kLen z.2) z.1 (R.graph.kWalk z.2) i.val,
        R.graph.kWalk z.2 i))
    (hpre : R.opinionOf q T hq A
        (R.graph.walkAt (R.graph.kLen z.2) z.1 (R.graph.kWalk z.2) i.val) hiT
        (R.graph.revWalk z.1 (R.graph.segPre (R.graph.kWalk z.2) (le_of_lt i.isLt)))
      = R.kDecode q T hq A
        (R.graph.walkAt (R.graph.kLen z.2) z.1 (R.graph.kWalk z.2) i.val))
    (hsuf : R.opinionOf q T hq A
        (R.graph.walkAt (R.graph.kLen z.2) z.1 (R.graph.kWalk z.2) (i.val + 1)) hjT
        (R.graph.segSuf (R.graph.kWalk z.2) i.val)
      = R.kDecode q T hq A
        (R.graph.walkAt (R.graph.kLen z.2) z.1 (R.graph.kWalk z.2) (i.val + 1))) :
    ¬ (R.killedPow q T hq).Satisfies A z := by
  obtain ⟨v, y⟩ := z
  refine R.not_satisfies_killedPow_of_faulty q T hq A v y i hfault ?_ ?_
  · rw [← R.opinionOf_eq_startIdx q T hq A (R.graph.kLen_le y) v (R.graph.kWalk y) i hiT]
    exact hpre
  · show A (R.graph.walkEnd (R.graph.kLen y) v (R.graph.kWalk y))
      (R.graph.endIdx (R.graph.kLen_le y) v (R.graph.kWalk y) i) = _
    rw [← R.opinionOf_eq_endIdx q T hq A (R.graph.kLen_le y) v (R.graph.kWalk y) i hjT]
    exact hsuf

/-- A walk count never exceeds the number of walks. -/
theorem truthCount_le (A : (R.killedPow q T hq).Assignment) (v : R.graph.V) (m : ℕ) :
    R.truthCount q T hq A v m ≤ R.graph.deg ^ m := by
  rw [truthCount]
  split
  · calc (Finset.univ.filter fun w : Fin m → R.graph.D =>
          R.opinionOf q T hq A v _ w = R.kPlurality q T hq A v).card
        ≤ (Finset.univ : Finset (Fin m → R.graph.D)).card := Finset.card_filter_le _ _
      _ = R.graph.deg ^ m := by
          rw [Finset.card_univ, Fintype.card_fun, Fintype.card_fin]
          rfl
  · exact Nat.zero_le _

/-- **Plurality on half the range.** Restricting the weighted sum to positions
at most `H` costs only the geometric tail, so the plurality bound survives the
restriction to a square of positions that `sum_crossing_factor` needs. -/
theorem card_le_mul_sum_truthCount_half (A : (R.killedPow q T hq).Assignment)
    (v : R.graph.V) {H : ℕ} (hH : H + 1 ≤ T) :
    R.graph.deg ^ T * q ^ T
      ≤ Fintype.card α * ((∑ m ∈ Finset.range (H + 1),
            R.truthCount q T hq A v m
              * (R.graph.deg ^ (T - m) * ((q - 1) ^ m * q ^ (T - m - 1))))
          + R.graph.deg ^ T * (q - 1) ^ T
          + R.graph.deg ^ T * ((q - 1) ^ (H + 1) * q ^ (T - (H + 1)))) := by
  classical
  have hfull := R.card_le_mul_sum_truthCount q T hq A v
  have hsum : ∑ m ∈ Finset.range T, R.truthCount q T hq A v m
        * (R.graph.deg ^ (T - m) * ((q - 1) ^ m * q ^ (T - m - 1)))
      = (∑ m ∈ Finset.range (H + 1), R.truthCount q T hq A v m
          * (R.graph.deg ^ (T - m) * ((q - 1) ^ m * q ^ (T - m - 1))))
        + ∑ m ∈ Finset.Ico (H + 1) T, R.truthCount q T hq A v m
          * (R.graph.deg ^ (T - m) * ((q - 1) ^ m * q ^ (T - m - 1))) := by
    rw [Finset.range_eq_Ico, Finset.range_eq_Ico,
      ← Finset.sum_Ico_consecutive _ (Nat.zero_le (H + 1)) hH]
  have hterm : ∀ m ∈ Finset.Ico (H + 1) T,
      R.truthCount q T hq A v m
          * (R.graph.deg ^ (T - m) * ((q - 1) ^ m * q ^ (T - m - 1)))
        ≤ R.graph.deg ^ T * ((q - 1) ^ m * q ^ (T - 1 - m)) := by
    intro m hm
    simp only [Finset.mem_Ico] at hm
    have h1 : R.truthCount q T hq A v m ≤ R.graph.deg ^ m := R.truthCount_le q T hq A v m
    have h2 : R.graph.deg ^ m * R.graph.deg ^ (T - m) = R.graph.deg ^ T := by
      rw [← pow_add]
      congr 1
      omega
    have h3 : T - m - 1 = T - 1 - m := by omega
    calc R.truthCount q T hq A v m
          * (R.graph.deg ^ (T - m) * ((q - 1) ^ m * q ^ (T - m - 1)))
        ≤ R.graph.deg ^ m
          * (R.graph.deg ^ (T - m) * ((q - 1) ^ m * q ^ (T - m - 1))) :=
          Nat.mul_le_mul_right _ h1
      _ = R.graph.deg ^ T * ((q - 1) ^ m * q ^ (T - 1 - m)) := by
          rw [h3, ← mul_assoc, h2]
  have htail : ∑ m ∈ Finset.Ico (H + 1) T, R.truthCount q T hq A v m
        * (R.graph.deg ^ (T - m) * ((q - 1) ^ m * q ^ (T - m - 1)))
      ≤ R.graph.deg ^ T * ((q - 1) ^ (H + 1) * q ^ (T - (H + 1))) := by
    calc ∑ m ∈ Finset.Ico (H + 1) T, R.truthCount q T hq A v m
          * (R.graph.deg ^ (T - m) * ((q - 1) ^ m * q ^ (T - m - 1)))
        ≤ ∑ m ∈ Finset.Ico (H + 1) T, R.graph.deg ^ T * ((q - 1) ^ m * q ^ (T - 1 - m)) :=
          Finset.sum_le_sum hterm
      _ = R.graph.deg ^ T * ∑ m ∈ Finset.Ico (H + 1) T, (q - 1) ^ m * q ^ (T - 1 - m) := by
          rw [Finset.mul_sum]
      _ ≤ R.graph.deg ^ T * ((q - 1) ^ (H + 1) * q ^ (T - (H + 1))) :=
          Nat.mul_le_mul_left _ (geom_tail_le hq T (T - (H + 1)) (H + 1) rfl hH)
  rw [hsum] at hfull
  refine le_trans hfull (Nat.mul_le_mul_left _ ?_)
  omega

/-- The crossing count indexed by the two *lengths* rather than by length and
position — the form `sum_goodCount_factor` consumes. -/
theorem card_good_crossing_sq (A : (R.killedPow q T hq).Assignment) (a : R.graph.V)
    (d : R.graph.D) {i j : ℕ} (hij : i + j + 1 < T) (hiT : i ≤ T)
    (hjT : (i + j + 1) - (i + 1) ≤ T) :
    (Finset.univ.filter fun z : R.graph.V × ((Fin T → R.graph.D) × (Fin T → Fin q)) =>
        stopAt z.2.2 = i + j + 1 ∧
          (R.graph.walkAt (i + j + 1) z.1 (R.graph.preWalk z.2.1 (le_of_lt hij)) i = a
            ∧ (R.graph.preWalk z.2.1 (le_of_lt hij)) ⟨i, by omega⟩ = d
            ∧ R.opinionOf q T hq A a hiT (R.graph.revWalk z.1
                (R.graph.segPre (R.graph.preWalk z.2.1 (le_of_lt hij)) (by omega)))
              = R.kPlurality q T hq A a
            ∧ R.opinionOf q T hq A (R.graph.nbr a d) hjT
                (R.graph.segSuf (R.graph.preWalk z.2.1 (le_of_lt hij)) i)
              = R.kPlurality q T hq A (R.graph.nbr a d))).card
      = R.truthCount q T hq A a i * R.truthCount q T hq A (R.graph.nbr a d) j
        * (R.graph.deg ^ (T - (i + j + 1))
          * ((q - 1) ^ (i + j + 1) * q ^ (T - (i + j + 1) - 1))) := by
  have hsub : (i + j + 1) - (i + 1) = j := by omega
  rw [R.card_good_crossing q T hq A a d hij (by omega) hiT hjT, hsub]

/-! ### The per-dart bound -/

/-- The weighted count of truthful walks out of `v`, over positions at most
`H`. -/
noncomputable def halfSum (A : (R.killedPow q T hq).Assignment) (v : R.graph.V)
    (H : ℕ) : ℕ :=
  ∑ m ∈ Finset.range (H + 1), R.truthCount q T hq A v m
    * (R.graph.deg ^ (T - m) * ((q - 1) ^ m * q ^ (T - m - 1)))

/-- What plurality pays for truncation: the walks that never stop, and those
that stop after position `H`. Both are geometrically small next to
`deg ^ T * q ^ T`. -/
def pluralityLoss (deg q T H : ℕ) : ℕ :=
  deg ^ T * (q - 1) ^ T + deg ^ T * ((q - 1) ^ (H + 1) * q ^ (T - (H + 1)))

theorem card_le_mul_halfSum_add_loss (A : (R.killedPow q T hq).Assignment)
    (v : R.graph.V) {H : ℕ} (hH : H + 1 ≤ T) :
    R.graph.deg ^ T * q ^ T
      ≤ Fintype.card α * R.halfSum q T hq A v H
        + Fintype.card α * pluralityLoss R.graph.deg q T H := by
  have h := R.card_le_mul_sum_truthCount_half q T hq A v hH
  calc R.graph.deg ^ T * q ^ T
      ≤ Fintype.card α * ((∑ m ∈ Finset.range (H + 1), R.truthCount q T hq A v m
            * (R.graph.deg ^ (T - m) * ((q - 1) ^ m * q ^ (T - m - 1))))
          + R.graph.deg ^ T * (q - 1) ^ T
          + R.graph.deg ^ T * ((q - 1) ^ (H + 1) * q ^ (T - (H + 1)))) := h
    _ = Fintype.card α * R.halfSum q T hq A v H
        + Fintype.card α * pluralityLoss R.graph.deg q T H := by
        rw [halfSum, pluralityLoss]
        ring

/-- **The per-dart first moment.** For one dart of `R`, the killed-power
constraints crossing it with truthful opinions at both ends number at least

`(q-1) · (X - |α|·loss)²  /  (|α|² · normaliser)`,

with `X = deg^T · q^T`. The two plurality bounds multiply because the crossing
sum factorises — the payoff of the killed walk law. -/
theorem per_dart_lower (A : (R.killedPow q T hq).Assignment) (a : R.graph.V)
    (d : R.graph.D) {H : ℕ} (hH : 2 * H + 1 < T) (hHT : H + 1 ≤ T)
    (C : ℕ → ℕ → ℕ)
    (hC : ∀ i ∈ Finset.range (H + 1), ∀ j ∈ Finset.range (H + 1),
      C i j = R.truthCount q T hq A a i * R.truthCount q T hq A (R.graph.nbr a d) j
        * (R.graph.deg ^ (T - (i + j + 1))
          * ((q - 1) ^ (i + j + 1) * q ^ (T - (i + j + 1) - 1)))) :
    (q - 1) * ((R.graph.deg ^ T * q ^ T
          - Fintype.card α * pluralityLoss R.graph.deg q T H)
        * (R.graph.deg ^ T * q ^ T
          - Fintype.card α * pluralityLoss R.graph.deg q T H))
      ≤ Fintype.card α ^ 2
        * ((∑ i ∈ Finset.range (H + 1), ∑ j ∈ Finset.range (H + 1), C i j)
          * (R.graph.deg ^ (T + 1) * q ^ T)) := by
  have hid := sum_goodCount_factor R.graph.deg q T H hH
    (fun i => R.truthCount q T hq A a i)
    (fun j => R.truthCount q T hq A (R.graph.nbr a d) j) C hC
  have ha := R.card_le_mul_halfSum_add_loss q T hq A a hHT
  have hb := R.card_le_mul_halfSum_add_loss q T hq A (R.graph.nbr a d) hHT
  have ha' : R.graph.deg ^ T * q ^ T
      - Fintype.card α * pluralityLoss R.graph.deg q T H
      ≤ Fintype.card α * R.halfSum q T hq A a H := by omega
  have hb' : R.graph.deg ^ T * q ^ T
      - Fintype.card α * pluralityLoss R.graph.deg q T H
      ≤ Fintype.card α * R.halfSum q T hq A (R.graph.nbr a d) H := by omega
  calc (q - 1) * ((R.graph.deg ^ T * q ^ T
          - Fintype.card α * pluralityLoss R.graph.deg q T H)
        * (R.graph.deg ^ T * q ^ T
          - Fintype.card α * pluralityLoss R.graph.deg q T H))
      ≤ (q - 1) * ((Fintype.card α * R.halfSum q T hq A a H)
        * (Fintype.card α * R.halfSum q T hq A (R.graph.nbr a d) H)) :=
        Nat.mul_le_mul_left _ (Nat.mul_le_mul ha' hb')
    _ = Fintype.card α ^ 2 * ((q - 1) * (R.halfSum q T hq A a H
          * R.halfSum q T hq A (R.graph.nbr a d) H)) := by ring
    _ = Fintype.card α ^ 2
        * ((∑ i ∈ Finset.range (H + 1), ∑ j ∈ Finset.range (H + 1), C i j)
          * (R.graph.deg ^ (T + 1) * q ^ T)) := by
        rw [hid, halfSum, halfSum]

/-- **The first moment, summed over the failed darts.** Every dart of `R` that
the decoded assignment fails contributes its own crossings, and for a given
killed walk and position the dart crossed there is determined, so the
contributions never overlap. -/
theorem sum_dart_lower (A : (R.killedPow q T hq).Assignment) (F : Finset R.Dart)
    {H : ℕ} (hH : 2 * H + 1 < T) (hHT : H + 1 ≤ T)
    (Cd : R.Dart → ℕ → ℕ → ℕ)
    (hCd : ∀ p ∈ F, ∀ i ∈ Finset.range (H + 1), ∀ j ∈ Finset.range (H + 1),
      Cd p i j = R.truthCount q T hq A p.1 i
        * R.truthCount q T hq A (R.graph.nbr p.1 p.2) j
        * (R.graph.deg ^ (T - (i + j + 1))
          * ((q - 1) ^ (i + j + 1) * q ^ (T - (i + j + 1) - 1)))) :
    F.card * ((q - 1) * ((R.graph.deg ^ T * q ^ T
          - Fintype.card α * pluralityLoss R.graph.deg q T H)
        * (R.graph.deg ^ T * q ^ T
          - Fintype.card α * pluralityLoss R.graph.deg q T H)))
      ≤ Fintype.card α ^ 2
        * ((∑ p ∈ F, ∑ i ∈ Finset.range (H + 1), ∑ j ∈ Finset.range (H + 1), Cd p i j)
          * (R.graph.deg ^ (T + 1) * q ^ T)) := by
  have hstep : ∀ p ∈ F, (q - 1) * ((R.graph.deg ^ T * q ^ T
          - Fintype.card α * pluralityLoss R.graph.deg q T H)
        * (R.graph.deg ^ T * q ^ T
          - Fintype.card α * pluralityLoss R.graph.deg q T H))
      ≤ Fintype.card α ^ 2
        * ((∑ i ∈ Finset.range (H + 1), ∑ j ∈ Finset.range (H + 1), Cd p i j)
          * (R.graph.deg ^ (T + 1) * q ^ T)) := fun p hp =>
    R.per_dart_lower q T hq A p.1 p.2 hH hHT (Cd p) (hCd p hp)
  calc F.card * ((q - 1) * ((R.graph.deg ^ T * q ^ T
          - Fintype.card α * pluralityLoss R.graph.deg q T H)
        * (R.graph.deg ^ T * q ^ T
          - Fintype.card α * pluralityLoss R.graph.deg q T H)))
      = ∑ _p ∈ F, ((q - 1) * ((R.graph.deg ^ T * q ^ T
          - Fintype.card α * pluralityLoss R.graph.deg q T H)
        * (R.graph.deg ^ T * q ^ T
          - Fintype.card α * pluralityLoss R.graph.deg q T H))) := by
        rw [Finset.sum_const, smul_eq_mul]
    _ ≤ ∑ p ∈ F, (Fintype.card α ^ 2
        * ((∑ i ∈ Finset.range (H + 1), ∑ j ∈ Finset.range (H + 1), Cd p i j)
          * (R.graph.deg ^ (T + 1) * q ^ T))) := Finset.sum_le_sum hstep
    _ = Fintype.card α ^ 2
        * ((∑ p ∈ F, ∑ i ∈ Finset.range (H + 1), ∑ j ∈ Finset.range (H + 1), Cd p i j)
          * (R.graph.deg ^ (T + 1) * q ^ T)) := by
        rw [← Finset.mul_sum, ← Finset.sum_mul]

/-! ### The crossing count of a single constraint -/

/-- The steps at which a killed walk crosses a dart the decoded assignment
fails, with truthful opinions at both ends. Its cardinality is the count the
second-moment method is applied to. -/
noncomputable def goodCrossings (A : (R.killedPow q T hq).Assignment)
    (z : R.graph.V × R.KLabels q T) : Finset (Fin (R.graph.kLen z.2)) :=
  Finset.univ.filter fun i =>
    (¬ R.Satisfies (R.kDecode q T hq A)
        (R.graph.walkAt (R.graph.kLen z.2) z.1 (R.graph.kWalk z.2) i.val,
          R.graph.kWalk z.2 i))
      ∧ R.opinionOf q T hq A
          (R.graph.walkAt (R.graph.kLen z.2) z.1 (R.graph.kWalk z.2) i.val)
          (le_trans (le_of_lt i.isLt) (R.graph.kLen_le z.2))
          (R.graph.revWalk z.1 (R.graph.segPre (R.graph.kWalk z.2) (le_of_lt i.isLt)))
        = R.kDecode q T hq A
          (R.graph.walkAt (R.graph.kLen z.2) z.1 (R.graph.kWalk z.2) i.val)
      ∧ R.opinionOf q T hq A
          (R.graph.walkAt (R.graph.kLen z.2) z.1 (R.graph.kWalk z.2) (i.val + 1))
          (le_trans (Nat.sub_le _ _) (R.graph.kLen_le z.2))
          (R.graph.segSuf (R.graph.kWalk z.2) i.val)
        = R.kDecode q T hq A
          (R.graph.walkAt (R.graph.kLen z.2) z.1 (R.graph.kWalk z.2) (i.val + 1))

/-- **The support condition.** A constraint with any good crossing is
unsatisfied, so the second-moment method's support sits inside the unsatisfied
darts. -/
theorem mem_unsatDarts_of_goodCrossings_nonempty (A : (R.killedPow q T hq).Assignment)
    (z : R.graph.V × R.KLabels q T) (h : (R.goodCrossings q T hq A z).Nonempty) :
    z ∈ (R.killedPow q T hq).unsatDarts A := by
  obtain ⟨i, hi⟩ := h
  rw [goodCrossings, Finset.mem_filter] at hi
  have hns := R.not_satisfies_of_good_crossing q T hq A z i _ _ hi.2.1 hi.2.2.1 hi.2.2.2
  exact (RegCSP.mem_unsatDarts (R := R.killedPow q T hq) (a := A) (p := z)).mpr hns

/-- **The second moment, in terms of pairs of crossings.** Squaring the count
of good crossings and summing turns into the count itself plus twice the ordered
pairs — and pairs of crossings are what the correlation bound estimates. -/
theorem sum_sq_goodCrossings (A : (R.killedPow q T hq).Assignment) :
    ∑ z : R.graph.V × R.KLabels q T, ((R.goodCrossings q T hq A z).card : ℝ) ^ 2
      = (∑ z : R.graph.V × R.KLabels q T, ((R.goodCrossings q T hq A z).card : ℝ))
        + 2 * ∑ z : R.graph.V × R.KLabels q T,
          ((((R.goodCrossings q T hq A z) ×ˢ (R.goodCrossings q T hq A z)).filter
            fun p => p.1 < p.2).card : ℝ) := by
  classical
  have hpt : ∀ z : R.graph.V × R.KLabels q T,
      ((R.goodCrossings q T hq A z).card : ℝ) ^ 2
        = ((R.goodCrossings q T hq A z).card : ℝ)
          + 2 * ((((R.goodCrossings q T hq A z) ×ˢ (R.goodCrossings q T hq A z)).filter
            fun p => p.1 < p.2).card : ℝ) := by
    intro z
    have h := card_sq_eq_add_two_mul_pairs (R.goodCrossings q T hq A z)
    exact_mod_cast congrArg (fun n : ℕ => (n : ℝ)) h
  rw [Finset.sum_congr rfl fun z _ => hpt z, Finset.sum_add_distrib, Finset.mul_sum]

/-! ### Positions as naturals -/

/-- The good crossing positions of a constraint, as naturals. The `Fin` version
carries the constraint's own length in its type, which blocks the exchange of
summation order the second moment needs; this one does not. -/
noncomputable def goodPos (A : (R.killedPow q T hq).Assignment)
    (z : R.graph.V × R.KLabels q T) : Finset ℕ :=
  (R.goodCrossings q T hq A z).image Fin.val

theorem card_goodPos (A : (R.killedPow q T hq).Assignment)
    (z : R.graph.V × R.KLabels q T) :
    (R.goodPos q T hq A z).card = (R.goodCrossings q T hq A z).card :=
  Finset.card_image_of_injective _ Fin.val_injective

theorem mem_goodPos {A : (R.killedPow q T hq).Assignment}
    {z : R.graph.V × R.KLabels q T} {k : ℕ} :
    k ∈ R.goodPos q T hq A z
      ↔ ∃ h : k < R.graph.kLen z.2, (⟨k, h⟩ : Fin (R.graph.kLen z.2))
          ∈ R.goodCrossings q T hq A z := by
  classical
  rw [goodPos, Finset.mem_image]
  constructor
  · rintro ⟨i, hi, rfl⟩
    exact ⟨i.isLt, by simpa using hi⟩
  · rintro ⟨h, hmem⟩
    exact ⟨⟨k, h⟩, hmem, rfl⟩

/-- Counting ordered pairs of positions is the same in either indexing. -/
theorem card_pairs_goodPos (A : (R.killedPow q T hq).Assignment)
    (z : R.graph.V × R.KLabels q T) :
    (((R.goodPos q T hq A z) ×ˢ (R.goodPos q T hq A z)).filter fun p => p.1 < p.2).card
      = (((R.goodCrossings q T hq A z) ×ˢ (R.goodCrossings q T hq A z)).filter
          fun p => p.1 < p.2).card := by
  classical
  refine (Finset.card_bij (fun p _ => ((p.1.val : ℕ), (p.2.val : ℕ))) ?_ ?_ ?_).symm
  · intro p hp
    simp only [Finset.mem_filter, Finset.mem_product] at hp ⊢
    refine ⟨⟨?_, ?_⟩, hp.2⟩
    · exact Finset.mem_image_of_mem _ hp.1.1
    · exact Finset.mem_image_of_mem _ hp.1.2
  · intro p _ p' _ hpp
    have h1 : p.1.val = p'.1.val := congrArg Prod.fst hpp
    have h2 : p.2.val = p'.2.val := congrArg Prod.snd hpp
    exact Prod.ext (Fin.ext h1) (Fin.ext h2)
  · intro p hp
    simp only [Finset.mem_filter, Finset.mem_product] at hp
    obtain ⟨⟨h1, h2⟩, hlt⟩ := hp
    obtain ⟨hb1, hm1⟩ := (R.mem_goodPos q T hq).mp h1
    obtain ⟨hb2, hm2⟩ := (R.mem_goodPos q T hq).mp h2
    refine ⟨(⟨p.1, hb1⟩, ⟨p.2, hb2⟩), ?_, rfl⟩
    simp only [Finset.mem_filter, Finset.mem_product]
    exact ⟨⟨hm1, hm2⟩, hlt⟩

theorem lt_T_of_mem_goodPos {A : (R.killedPow q T hq).Assignment}
    {z : R.graph.V × R.KLabels q T} {k : ℕ} (h : k ∈ R.goodPos q T hq A z) : k < T := by
  obtain ⟨hb, -⟩ := (R.mem_goodPos q T hq).mp h
  exact lt_of_lt_of_le hb (R.graph.kLen_le z.2)

/-- **Exchanging the order of counting.** The pairs of good crossings, summed
over the constraints, are the same as the constraints with two good crossings,
summed over the pairs of positions. The right-hand side is the form the
correlation bound estimates. -/
theorem sum_card_pairs_eq (A : (R.killedPow q T hq).Assignment) :
    ∑ z : R.graph.V × R.KLabels q T,
        (((R.goodPos q T hq A z) ×ˢ (R.goodPos q T hq A z)).filter fun p => p.1 < p.2).card
      = ∑ p ∈ ((Finset.range T) ×ˢ (Finset.range T)).filter fun p => p.1 < p.2,
        (Finset.univ.filter fun z : R.graph.V × R.KLabels q T =>
          p.1 ∈ R.goodPos q T hq A z ∧ p.2 ∈ R.goodPos q T hq A z).card := by
  classical
  have hzcard : ∀ z : R.graph.V × R.KLabels q T,
      (((R.goodPos q T hq A z) ×ˢ (R.goodPos q T hq A z)).filter fun p => p.1 < p.2).card
        = ((((Finset.range T) ×ˢ (Finset.range T)).filter fun p => p.1 < p.2).filter
            fun p => p.1 ∈ R.goodPos q T hq A z ∧ p.2 ∈ R.goodPos q T hq A z).card := by
    intro z
    congr 1
    ext p
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range]
    constructor
    · rintro ⟨⟨h1, h2⟩, hlt⟩
      exact ⟨⟨⟨R.lt_T_of_mem_goodPos q T hq h1, R.lt_T_of_mem_goodPos q T hq h2⟩, hlt⟩, h1, h2⟩
    · rintro ⟨⟨-, hlt⟩, h1, h2⟩
      exact ⟨⟨h1, h2⟩, hlt⟩
  rw [Finset.sum_congr rfl fun z _ => hzcard z]
  simp only [Finset.card_filter]
  exact Finset.sum_comm

/-- **Dropping to the underlying walk.** Constraints with good crossings at two
positions are, after forgetting the truthfulness conditions and the stopping
signals, walks that cross a failed dart at both positions. Forgetting the
signals costs the factor `q ^ T`; both omissions only weaken an upper bound. -/
theorem card_both_good_le (A : (R.killedPow q T hq).Assignment) {k l : ℕ}
    (hk : k < T) (hl : l < T) :
    (Finset.univ.filter fun z : R.graph.V × R.KLabels q T =>
        k ∈ R.goodPos q T hq A z ∧ l ∈ R.goodPos q T hq A z).card
      ≤ q ^ T * (Finset.univ.filter fun w : R.graph.V × (Fin T → R.graph.D) =>
          (R.graph.walkAt T w.1 w.2 k, w.2 ⟨k, hk⟩) ∈ R.unsatDarts (R.kDecode q T hq A)
            ∧ (R.graph.walkAt T w.1 w.2 l, w.2 ⟨l, hl⟩)
              ∈ R.unsatDarts (R.kDecode q T hq A)).card := by
  classical
  have hfaulty : ∀ (z : R.graph.V × R.KLabels q T) (j : ℕ) (hj : j < T),
      j ∈ R.goodPos q T hq A z →
      (R.graph.walkAt T z.1 z.2.1 j, z.2.1 ⟨j, hj⟩)
        ∈ R.unsatDarts (R.kDecode q T hq A) := by
    intro z j hj hmem
    obtain ⟨hb, hgc⟩ := (R.mem_goodPos q T hq).mp hmem
    rw [goodCrossings, Finset.mem_filter] at hgc
    have hns := hgc.2.1
    have hwalk : R.graph.walkAt (R.graph.kLen z.2) z.1 (R.graph.kWalk z.2) j
        = R.graph.walkAt T z.1 z.2.1 j :=
      R.graph.walkAt_preWalk (R.graph.kLen_le z.2) z.1 z.2.1 j (le_of_lt hb)
    have hlab : R.graph.kWalk z.2 ⟨j, hb⟩ = z.2.1 ⟨j, hj⟩ := rfl
    rw [hwalk, hlab] at hns
    exact (RegCSP.mem_unsatDarts (R := R) (a := R.kDecode q T hq A)
      (p := (R.graph.walkAt T z.1 z.2.1 j, z.2.1 ⟨j, hj⟩))).mpr hns
  refine le_trans (Finset.card_le_mul_card_image_of_maps_to
    (f := fun z : R.graph.V × R.KLabels q T => (z.1, z.2.1))
    (t := Finset.univ.filter fun w : R.graph.V × (Fin T → R.graph.D) =>
      (R.graph.walkAt T w.1 w.2 k, w.2 ⟨k, hk⟩) ∈ R.unsatDarts (R.kDecode q T hq A)
        ∧ (R.graph.walkAt T w.1 w.2 l, w.2 ⟨l, hl⟩)
          ∈ R.unsatDarts (R.kDecode q T hq A)) ?_ (q ^ T) ?_) (le_refl _)
  · intro z hz
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hz ⊢
    exact ⟨hfaulty z k hk hz.1, hfaulty z l hl hz.2⟩
  · intro w _
    refine le_trans (Finset.card_le_card_of_injOn (fun z => z.2.2)
      (fun _ _ => Finset.mem_univ _) ?_) ?_
    · intro z hz z' hz' hzz
      simp only [Finset.coe_filter, Set.mem_ofPred_eq] at hz hz'
      have hz1 : z.1 = w.1 := congrArg Prod.fst hz.2
      have hz2 : z.2.1 = w.2 := congrArg Prod.snd hz.2
      have hz1' : z'.1 = w.1 := congrArg Prod.fst hz'.2
      have hz2' : z'.2.1 = w.2 := congrArg Prod.snd hz'.2
      exact Prod.ext (hz1.trans hz1'.symm) (Prod.ext (hz2.trans hz2'.symm) hzz)
    · rw [Finset.card_univ, Fintype.card_fun, Fintype.card_fin, Fintype.card_fin]

/-- **The second moment's pair term, bounded.** Chaining the drop to underlying
walks, the two-crossing identity and the correlation bound. -/
theorem sum_pairs_bound (A : (R.killedPow q T hq).Assignment) {lam : ℝ}
    (hlam0 : 0 ≤ lam) (hlam1 : lam < 1) (hspec : R.graph.SpectralBound lam)
    (hn : 0 < R.graph.order) :
    ∑ p ∈ ((Finset.range T) ×ˢ (Finset.range T)).filter fun p => p.1 < p.2,
        ((Finset.univ.filter fun z : R.graph.V × R.KLabels q T =>
          p.1 ∈ R.goodPos q T hq A z ∧ p.2 ∈ R.goodPos q T hq A z).card : ℝ)
      ≤ (q : ℝ) ^ T * ((R.graph.deg : ℝ) ^ (T - 2)
        * ((T : ℝ) * (T : ℝ) * (((R.unsatDarts (R.kDecode q T hq A)).card : ℝ)
              * ((R.unsatDarts (R.kDecode q T hq A)).card : ℝ) / (R.graph.order : ℝ))
          + (T : ℝ) * (1 / (1 - lam)) * ((R.graph.deg : ℝ)
              * ((R.unsatDarts (R.kDecode q T hq A)).card : ℝ)))) := by
  classical
  set F := R.unsatDarts (R.kDecode q T hq A) with hF
  set Cop : ℕ → ℕ → ℝ := fun k l => ∑ z : R.graph.V, (R.graph.headCount F z : ℝ)
    * R.graph.stepIter (l - k - 1) (fun w => (R.graph.dartCount F w : ℝ)) z with hCop
  have hterm : ∀ p ∈ ((Finset.range T) ×ˢ (Finset.range T)).filter fun p => p.1 < p.2,
      ((Finset.univ.filter fun z : R.graph.V × R.KLabels q T =>
          p.1 ∈ R.goodPos q T hq A z ∧ p.2 ∈ R.goodPos q T hq A z).card : ℝ)
        ≤ (q : ℝ) ^ T * ((R.graph.deg : ℝ) ^ (T - 2) * Cop p.1 p.2) := by
    intro p hp
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range] at hp
    obtain ⟨⟨hk, hl⟩, hlt⟩ := hp
    have h1 := R.card_both_good_le q T hq A hk hl
    have h1R : ((Finset.univ.filter fun z : R.graph.V × R.KLabels q T =>
          p.1 ∈ R.goodPos q T hq A z ∧ p.2 ∈ R.goodPos q T hq A z).card : ℝ)
        ≤ (q : ℝ) ^ T * ((Finset.univ.filter fun w : R.graph.V × (Fin T → R.graph.D) =>
            (R.graph.walkAt T w.1 w.2 p.1, w.2 ⟨p.1, hk⟩) ∈ F
              ∧ (R.graph.walkAt T w.1 w.2 p.2, w.2 ⟨p.2, hl⟩) ∈ F).card : ℝ) := by
      exact_mod_cast h1
    refine le_trans h1R ?_
    have hcount : ((Finset.univ.filter fun w : R.graph.V × (Fin T → R.graph.D) =>
          (R.graph.walkAt T w.1 w.2 p.1, w.2 ⟨p.1, hk⟩) ∈ F
            ∧ (R.graph.walkAt T w.1 w.2 p.2, w.2 ⟨p.2, hl⟩) ∈ F).card : ℝ)
        = (R.graph.deg : ℝ) ^ (T - 2) * Cop p.1 p.2 := by
      rw [card_filter_eq_sum_prod, Fintype.sum_prod_type, hCop]
      exact R.graph.sum_two_crossings F hlt hl
    rw [hcount]
  refine le_trans (Finset.sum_le_sum hterm) ?_
  have hfactor : ∑ p ∈ ((Finset.range T) ×ˢ (Finset.range T)).filter fun p => p.1 < p.2,
        (q : ℝ) ^ T * ((R.graph.deg : ℝ) ^ (T - 2) * Cop p.1 p.2)
      = (q : ℝ) ^ T * ((R.graph.deg : ℝ) ^ (T - 2)
        * ∑ k ∈ Finset.range T, ∑ l ∈ Finset.Ico (k + 1) T, Cop k l) := by
    rw [← sum_pairs_eq_sum_Ico T fun p => Cop p.1 p.2, Finset.mul_sum, Finset.mul_sum]
  rw [hfactor]
  have hnn : (0 : ℝ) ≤ (q : ℝ) ^ T * (R.graph.deg : ℝ) ^ (T - 2) := by positivity
  have hinner := R.graph.sum_pairs_le F hlam0 hlam1 hspec hn T Cop
    (fun k _ l _ => rfl)
  calc (q : ℝ) ^ T * ((R.graph.deg : ℝ) ^ (T - 2)
        * ∑ k ∈ Finset.range T, ∑ l ∈ Finset.Ico (k + 1) T, Cop k l)
      = ((q : ℝ) ^ T * (R.graph.deg : ℝ) ^ (T - 2))
        * ∑ k ∈ Finset.range T, ∑ l ∈ Finset.Ico (k + 1) T, Cop k l := by ring
    _ ≤ ((q : ℝ) ^ T * (R.graph.deg : ℝ) ^ (T - 2))
        * ((T : ℝ) * (T : ℝ) * ((F.card : ℝ) * (F.card : ℝ) / (R.graph.order : ℝ))
          + (T : ℝ) * (1 / (1 - lam)) * ((R.graph.deg : ℝ) * (F.card : ℝ))) :=
        mul_le_mul_of_nonneg_left hinner hnn
    _ = (q : ℝ) ^ T * ((R.graph.deg : ℝ) ^ (T - 2)
        * ((T : ℝ) * (T : ℝ) * ((F.card : ℝ) * (F.card : ℝ) / (R.graph.order : ℝ))
          + (T : ℝ) * (1 / (1 - lam)) * ((R.graph.deg : ℝ) * (F.card : ℝ)))) := by ring

/-- **The second moment of the crossing count.** Everything above, assembled:
the sum of squares is the sum plus twice a pair term, and the pair term is
controlled by the spectral gap. -/
theorem sum_sq_goodCrossings_le (A : (R.killedPow q T hq).Assignment) {lam : ℝ}
    (hlam0 : 0 ≤ lam) (hlam1 : lam < 1) (hspec : R.graph.SpectralBound lam)
    (hn : 0 < R.graph.order) :
    ∑ z : R.graph.V × R.KLabels q T, ((R.goodCrossings q T hq A z).card : ℝ) ^ 2
      ≤ (∑ z : R.graph.V × R.KLabels q T, ((R.goodCrossings q T hq A z).card : ℝ))
        + 2 * ((q : ℝ) ^ T * ((R.graph.deg : ℝ) ^ (T - 2)
          * ((T : ℝ) * (T : ℝ) * (((R.unsatDarts (R.kDecode q T hq A)).card : ℝ)
                * ((R.unsatDarts (R.kDecode q T hq A)).card : ℝ) / (R.graph.order : ℝ))
            + (T : ℝ) * (1 / (1 - lam)) * ((R.graph.deg : ℝ)
                * ((R.unsatDarts (R.kDecode q T hq A)).card : ℝ))))) := by
  classical
  rw [R.sum_sq_goodCrossings q T hq A]
  have hpair : ∑ z : R.graph.V × R.KLabels q T,
        ((((R.goodCrossings q T hq A z) ×ˢ (R.goodCrossings q T hq A z)).filter
          fun p => p.1 < p.2).card : ℝ)
      = ∑ p ∈ ((Finset.range T) ×ˢ (Finset.range T)).filter fun p => p.1 < p.2,
        ((Finset.univ.filter fun z : R.graph.V × R.KLabels q T =>
          p.1 ∈ R.goodPos q T hq A z ∧ p.2 ∈ R.goodPos q T hq A z).card : ℝ) := by
    rw [← Nat.cast_sum, ← Nat.cast_sum]
    congr 1
    rw [Finset.sum_congr rfl fun z _ => (R.card_pairs_goodPos q T hq A z).symm]
    exact R.sum_card_pairs_eq q T hq A
  rw [hpair]
  have hbound := R.sum_pairs_bound q T hq A hlam0 hlam1 hspec hn
  linarith [hbound]

/-- The first moment, with the order of counting exchanged: summing the good
crossings over the constraints is the same as counting, for each position, the
constraints good there. -/
theorem sum_card_goodPos_eq (A : (R.killedPow q T hq).Assignment) :
    ∑ z : R.graph.V × R.KLabels q T, (R.goodPos q T hq A z).card
      = ∑ k ∈ Finset.range T,
        (Finset.univ.filter fun z : R.graph.V × R.KLabels q T =>
          k ∈ R.goodPos q T hq A z).card := by
  classical
  have hzcard : ∀ z : R.graph.V × R.KLabels q T,
      (R.goodPos q T hq A z).card
        = ((Finset.range T).filter fun k => k ∈ R.goodPos q T hq A z).card := by
    intro z
    congr 1
    ext k
    simp only [Finset.mem_filter, Finset.mem_range]
    exact ⟨fun h => ⟨R.lt_T_of_mem_goodPos q T hq h, h⟩, fun h => h.2⟩
  rw [Finset.sum_congr rfl fun z _ => hzcard z]
  simp only [Finset.card_filter]
  exact Finset.sum_comm

/-- Constraints of different effective lengths are different constraints, so
summing over the suffix length `j` at a fixed crossing position stays within the
constraints good at that position. -/
theorem sum_over_len_le (A : (R.killedPow q T hq).Assignment) (i H : ℕ) :
    ∑ j ∈ Finset.range (H + 1),
        (Finset.univ.filter fun z : R.graph.V × R.KLabels q T =>
          stopAt z.2.2 = i + j + 1 ∧ i ∈ R.goodPos q T hq A z).card
      ≤ (Finset.univ.filter fun z : R.graph.V × R.KLabels q T =>
          i ∈ R.goodPos q T hq A z).card := by
  classical
  have hdisj : ∀ j ∈ Finset.range (H + 1), ∀ j' ∈ Finset.range (H + 1), j ≠ j' →
      Disjoint
        (Finset.univ.filter fun z : R.graph.V × R.KLabels q T =>
          stopAt z.2.2 = i + j + 1 ∧ i ∈ R.goodPos q T hq A z)
        (Finset.univ.filter fun z : R.graph.V × R.KLabels q T =>
          stopAt z.2.2 = i + j' + 1 ∧ i ∈ R.goodPos q T hq A z) := by
    intro j _ j' _ hjj
    refine Finset.disjoint_left.mpr fun z hz hz' => ?_
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hz hz'
    apply hjj
    have := hz.1.symm.trans hz'.1
    omega
  rw [← Finset.card_biUnion hdisj]
  refine Finset.card_le_card ?_
  intro z hz
  simp only [Finset.mem_biUnion, Finset.mem_filter, Finset.mem_univ, true_and] at hz ⊢
  obtain ⟨j, -, -, hgood⟩ := hz
  exact hgood

/-- **From a counted crossing to a good position.** A constraint counted by
`card_good_crossing_sq`, whose crossed dart the decoded assignment fails, is good
at that position. The two descriptions differ only in how the walk's length is
named — `i + j + 1` on one side, `kLen` on the other — which `walkAt_preWalk`
and `opinionOf_congr` reconcile without any transport. -/
theorem mem_goodPos_of_crossing (A : (R.killedPow q T hq).Assignment) (a : R.graph.V)
    (d : R.graph.D) {i j : ℕ} (hij : i + j + 1 < T) (hiT : i ≤ T)
    (hjT : (i + j + 1) - (i + 1) ≤ T)
    (hfault : ¬ R.Satisfies (R.kDecode q T hq A) (a, d))
    (z : R.graph.V × R.KLabels q T) (hlen : stopAt z.2.2 = i + j + 1)
    (hwalk : R.graph.walkAt (i + j + 1) z.1 (R.graph.preWalk z.2.1 (le_of_lt hij)) i = a)
    (hlab : R.graph.preWalk z.2.1 (le_of_lt hij) ⟨i, by omega⟩ = d)
    (hpre : R.opinionOf q T hq A a hiT (R.graph.revWalk z.1
        (R.graph.segPre (R.graph.preWalk z.2.1 (le_of_lt hij)) (by omega)))
      = R.kPlurality q T hq A a)
    (hsuf : R.opinionOf q T hq A (R.graph.nbr a d) hjT
        (R.graph.segSuf (R.graph.preWalk z.2.1 (le_of_lt hij)) i)
      = R.kPlurality q T hq A (R.graph.nbr a d)) :
    i ∈ R.goodPos q T hq A z := by
  classical
  have hkl : R.graph.kLen z.2 = i + j + 1 := hlen
  have hb : i < R.graph.kLen z.2 := by omega
  refine (R.mem_goodPos q T hq).mpr ⟨hb, ?_⟩
  -- the walk position, computed two ways
  have hA1 : R.graph.walkAt (R.graph.kLen z.2) z.1 (R.graph.kWalk z.2) i
      = R.graph.walkAt T z.1 z.2.1 i :=
    R.graph.walkAt_preWalk (R.graph.kLen_le z.2) z.1 z.2.1 i (le_of_lt hb)
  have hA2 : R.graph.walkAt (i + j + 1) z.1 (R.graph.preWalk z.2.1 (le_of_lt hij)) i
      = R.graph.walkAt T z.1 z.2.1 i :=
    R.graph.walkAt_preWalk (le_of_lt hij) z.1 z.2.1 i (by omega)
  have hvert : R.graph.walkAt (R.graph.kLen z.2) z.1 (R.graph.kWalk z.2) i = a := by
    rw [hA1, ← hA2, hwalk]
  have hlabel : R.graph.kWalk z.2 ⟨i, hb⟩ = d := hlab
  -- the prefix walk, pointwise equal on the nose
  have hprewalk : R.graph.segPre (R.graph.kWalk z.2) (le_of_lt hb)
      = R.graph.segPre (R.graph.preWalk z.2.1 (le_of_lt hij)) (by omega) := rfl
  rw [goodCrossings, Finset.mem_filter]
  refine ⟨Finset.mem_univ _, ?_, ?_, ?_⟩
  · rw [hvert, hlabel]
    exact hfault
  · rw [hvert, hprewalk]
    exact hpre
  · have hnext : R.graph.walkAt (R.graph.kLen z.2) z.1 (R.graph.kWalk z.2) (i + 1)
        = R.graph.nbr a d := by
      rw [R.graph.walkAt_succ_of_lt z.1 (R.graph.kWalk z.2) hb, hvert, hlabel]
    rw [hnext]
    refine Eq.trans ?_ hsuf
    have hsub : R.graph.kLen z.2 - ((⟨i, hb⟩ : Fin (R.graph.kLen z.2)).val + 1)
        = (i + j + 1) - (i + 1) := by
      dsimp only
      omega
    refine R.opinionOf_congr q T hq A (R.graph.nbr a d) _ hjT hsub _ _ ?_
    intro k hk hk'
    rfl

/-- The constraints counted by `card_good_crossing_sq`, packaged. -/
noncomputable def crossingSet (A : (R.killedPow q T hq).Assignment) (a : R.graph.V)
    (d : R.graph.D) {i j : ℕ} (hij : i + j + 1 < T) (hiT : i ≤ T)
    (hjT : (i + j + 1) - (i + 1) ≤ T) : Finset (R.graph.V × R.KLabels q T) :=
  Finset.univ.filter fun z =>
    stopAt z.2.2 = i + j + 1 ∧
      (R.graph.walkAt (i + j + 1) z.1 (R.graph.preWalk z.2.1 (le_of_lt hij)) i = a
        ∧ (R.graph.preWalk z.2.1 (le_of_lt hij)) ⟨i, by omega⟩ = d
        ∧ R.opinionOf q T hq A a hiT (R.graph.revWalk z.1
            (R.graph.segPre (R.graph.preWalk z.2.1 (le_of_lt hij)) (by omega)))
          = R.kPlurality q T hq A a
        ∧ R.opinionOf q T hq A (R.graph.nbr a d) hjT
            (R.graph.segSuf (R.graph.preWalk z.2.1 (le_of_lt hij)) i)
          = R.kPlurality q T hq A (R.graph.nbr a d))

theorem card_crossingSet (A : (R.killedPow q T hq).Assignment) (a : R.graph.V)
    (d : R.graph.D) {i j : ℕ} (hij : i + j + 1 < T) (hiT : i ≤ T)
    (hjT : (i + j + 1) - (i + 1) ≤ T) :
    (R.crossingSet q T hq A a d hij hiT hjT).card
      = R.truthCount q T hq A a i * R.truthCount q T hq A (R.graph.nbr a d) j
        * (R.graph.deg ^ (T - (i + j + 1))
          * ((q - 1) ^ (i + j + 1) * q ^ (T - (i + j + 1) - 1))) :=
  R.card_good_crossing_sq q T hq A a d hij hiT hjT

/-- **The crossings of different darts do not overlap.** At a fixed position the
dart a walk crosses is determined, so summing over the failed darts stays within
the constraints good at that position. -/
theorem sum_crossingSet_le (A : (R.killedPow q T hq).Assignment) {i j : ℕ}
    (hij : i + j + 1 < T) (hiT : i ≤ T) (hjT : (i + j + 1) - (i + 1) ≤ T) :
    ∑ p ∈ R.unsatDarts (R.kDecode q T hq A),
        (R.crossingSet q T hq A p.1 p.2 hij hiT hjT).card
      ≤ (Finset.univ.filter fun z : R.graph.V × R.KLabels q T =>
          stopAt z.2.2 = i + j + 1 ∧ i ∈ R.goodPos q T hq A z).card := by
  classical
  have hdisj : ∀ p ∈ R.unsatDarts (R.kDecode q T hq A),
      ∀ p' ∈ R.unsatDarts (R.kDecode q T hq A), p ≠ p' →
      Disjoint (R.crossingSet q T hq A p.1 p.2 hij hiT hjT)
        (R.crossingSet q T hq A p'.1 p'.2 hij hiT hjT) := by
    intro p _ p' _ hpp
    refine Finset.disjoint_left.mpr fun z hz hz' => ?_
    rw [crossingSet, Finset.mem_filter] at hz hz'
    apply hpp
    exact Prod.ext (hz.2.2.1.symm.trans hz'.2.2.1) (hz.2.2.2.1.symm.trans hz'.2.2.2.1)
  rw [← Finset.card_biUnion hdisj]
  refine Finset.card_le_card ?_
  intro z hz
  rw [Finset.mem_biUnion] at hz
  obtain ⟨p, hp, hzp⟩ := hz
  rw [crossingSet, Finset.mem_filter] at hzp
  obtain ⟨-, hlen, hwalk, hlab, hpre, hsuf⟩ := hzp
  have hfault : ¬ R.Satisfies (R.kDecode q T hq A) (p.1, p.2) := by
    have := (RegCSP.mem_unsatDarts (R := R) (a := R.kDecode q T hq A) (p := p)).mp hp
    exact this
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact ⟨hlen, R.mem_goodPos_of_crossing q T hq A p.1 p.2 hij hiT hjT hfault z hlen hwalk
    hlab hpre hsuf⟩

/-- Summed over both lengths, the constraints good at a position never exceed
the total crossing count. -/
theorem sum_len_pos_le (A : (R.killedPow q T hq).Assignment) {H : ℕ} (hHT : H + 1 ≤ T) :
    ∑ i ∈ Finset.range (H + 1), ∑ j ∈ Finset.range (H + 1),
        (Finset.univ.filter fun z : R.graph.V × R.KLabels q T =>
          stopAt z.2.2 = i + j + 1 ∧ i ∈ R.goodPos q T hq A z).card
      ≤ ∑ z : R.graph.V × R.KLabels q T, (R.goodCrossings q T hq A z).card := by
  classical
  calc ∑ i ∈ Finset.range (H + 1), ∑ j ∈ Finset.range (H + 1),
        (Finset.univ.filter fun z : R.graph.V × R.KLabels q T =>
          stopAt z.2.2 = i + j + 1 ∧ i ∈ R.goodPos q T hq A z).card
      ≤ ∑ i ∈ Finset.range (H + 1),
          (Finset.univ.filter fun z : R.graph.V × R.KLabels q T =>
            i ∈ R.goodPos q T hq A z).card :=
        Finset.sum_le_sum fun i _ => R.sum_over_len_le q T hq A i H
    _ ≤ ∑ k ∈ Finset.range T,
          (Finset.univ.filter fun z : R.graph.V × R.KLabels q T =>
            k ∈ R.goodPos q T hq A z).card := by
        refine Finset.sum_le_sum_of_subset ?_
        intro i hi
        simp only [Finset.mem_range] at hi ⊢
        omega
    _ = ∑ z : R.graph.V × R.KLabels q T, (R.goodPos q T hq A z).card :=
        (R.sum_card_goodPos_eq q T hq A).symm
    _ = ∑ z : R.graph.V × R.KLabels q T, (R.goodCrossings q T hq A z).card :=
        Finset.sum_congr rfl fun z _ => R.card_goodPos q T hq A z

/-- **The first moment, bounded by the crossing count.** The counts summed by
`sum_dart_lower` never exceed the total number of good crossings. -/
theorem sum_Cd_le_sum_goodCrossings (A : (R.killedPow q T hq).Assignment) {H : ℕ}
    (hHT : H + 1 ≤ T) (Cd : R.Dart → ℕ → ℕ → ℕ)
    (hCd : ∀ p ∈ R.unsatDarts (R.kDecode q T hq A), ∀ i ∈ Finset.range (H + 1),
      ∀ j ∈ Finset.range (H + 1), ∀ (hij : i + j + 1 < T) (hiT : i ≤ T)
        (hjT : (i + j + 1) - (i + 1) ≤ T),
      Cd p i j = (R.crossingSet q T hq A p.1 p.2 hij hiT hjT).card)
    (hsq : ∀ i ∈ Finset.range (H + 1), ∀ j ∈ Finset.range (H + 1), i + j + 1 < T) :
    ∑ p ∈ R.unsatDarts (R.kDecode q T hq A), ∑ i ∈ Finset.range (H + 1),
        ∑ j ∈ Finset.range (H + 1), Cd p i j
      ≤ ∑ z : R.graph.V × R.KLabels q T, (R.goodCrossings q T hq A z).card := by
  classical
  have hreorder : ∑ p ∈ R.unsatDarts (R.kDecode q T hq A), ∑ i ∈ Finset.range (H + 1),
        ∑ j ∈ Finset.range (H + 1), Cd p i j
      = ∑ i ∈ Finset.range (H + 1), ∑ j ∈ Finset.range (H + 1),
        ∑ p ∈ R.unsatDarts (R.kDecode q T hq A), Cd p i j := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_comm
  rw [hreorder]
  refine le_trans (Finset.sum_le_sum fun i hi => Finset.sum_le_sum fun j hj => ?_)
    (R.sum_len_pos_le q T hq A hHT)
  have hij : i + j + 1 < T := hsq i hi j hj
  have hiT : i ≤ T := by
    simp only [Finset.mem_range] at hi
    omega
  have hjT : (i + j + 1) - (i + 1) ≤ T := by omega
  calc ∑ p ∈ R.unsatDarts (R.kDecode q T hq A), Cd p i j
      = ∑ p ∈ R.unsatDarts (R.kDecode q T hq A),
          (R.crossingSet q T hq A p.1 p.2 hij hiT hjT).card :=
        Finset.sum_congr rfl fun p hp => hCd p hp i hi j hj hij hiT hjT
    _ ≤ (Finset.univ.filter fun z : R.graph.V × R.KLabels q T =>
          stopAt z.2.2 = i + j + 1 ∧ i ∈ R.goodPos q T hq A z).card :=
        R.sum_crossingSet_le q T hq A hij hiT hjT

/-! ### Powering soundness -/

/-- **The second-moment bound on unsatisfied constraints.** Given a lower bound
on the first moment of the crossing count and an upper bound on its second
moment, at least `Alb ^ 2 / Bub` of the powered constraints are unsatisfied. -/
theorem card_unsatDarts_ge (A : (R.killedPow q T hq).Assignment) {Alb Bub : ℝ}
    (hA0 : 0 ≤ Alb)
    (hA : Alb ≤ ∑ z : R.graph.V × R.KLabels q T, ((R.goodCrossings q T hq A z).card : ℝ))
    (hB : ∑ z : R.graph.V × R.KLabels q T, ((R.goodCrossings q T hq A z).card : ℝ) ^ 2
      ≤ Bub) (hB0 : 0 < Bub) :
    Alb ^ 2 / Bub ≤ (((R.killedPow q T hq).unsatDarts A).card : ℝ) := by
  classical
  refine card_ge_of_moments (fun z => ((R.goodCrossings q T hq A z).card : ℝ))
    ((R.killedPow q T hq).unsatDarts A) ?_ hA0 hA hB hB0
  intro z hz
  have hcard : (R.goodCrossings q T hq A z).card ≠ 0 := by
    intro h
    apply hz
    show ((R.goodCrossings q T hq A z).card : ℝ) = 0
    rw [h]
    norm_num
  exact R.mem_unsatDarts_of_goodCrossings_nonempty q T hq A z
    (Finset.card_pos.mp (Nat.pos_of_ne_zero hcard))

/-- The crossing count as a total function of the two lengths, so that it can be
summed without carrying the side conditions. -/
noncomputable def crossCount (A : (R.killedPow q T hq).Assignment) (p : R.Dart)
    (i j : ℕ) : ℕ :=
  if h : i + j + 1 < T then
    (R.crossingSet q T hq A p.1 p.2 h (by omega) (by omega)).card
  else 0

theorem crossCount_eq_card (A : (R.killedPow q T hq).Assignment) (p : R.Dart)
    {i j : ℕ} (hij : i + j + 1 < T) (hiT : i ≤ T) (hjT : (i + j + 1) - (i + 1) ≤ T) :
    R.crossCount q T hq A p i j = (R.crossingSet q T hq A p.1 p.2 hij hiT hjT).card := by
  rw [crossCount, dite_eq_left hij]

theorem crossCount_eq_prod (A : (R.killedPow q T hq).Assignment) (p : R.Dart)
    {i j : ℕ} (hij : i + j + 1 < T) :
    R.crossCount q T hq A p i j
      = R.truthCount q T hq A p.1 i * R.truthCount q T hq A (R.graph.nbr p.1 p.2) j
        * (R.graph.deg ^ (T - (i + j + 1))
          * ((q - 1) ^ (i + j + 1) * q ^ (T - (i + j + 1) - 1))) := by
  rw [R.crossCount_eq_card q T hq A p hij (by omega) (by omega),
    R.card_crossingSet q T hq A p.1 p.2 hij (by omega) (by omega)]

/-- **The first moment, in closed form.** Combining the per-dart bound with the
fact that the counted crossings are good crossings. -/
theorem sum_goodCrossings_ge (A : (R.killedPow q T hq).Assignment) {H : ℕ}
    (hH : 2 * H + 1 < T) (hHT : H + 1 ≤ T)
    (hsq : ∀ i ∈ Finset.range (H + 1), ∀ j ∈ Finset.range (H + 1), i + j + 1 < T) :
    (((R.unsatDarts (R.kDecode q T hq A)).card
        * ((q - 1) * ((R.graph.deg ^ T * q ^ T
              - Fintype.card α * pluralityLoss R.graph.deg q T H)
            * (R.graph.deg ^ T * q ^ T
              - Fintype.card α * pluralityLoss R.graph.deg q T H))) : ℕ) : ℝ)
      ≤ ((Fintype.card α ^ 2 * (R.graph.deg ^ (T + 1) * q ^ T) : ℕ) : ℝ)
        * ∑ z : R.graph.V × R.KLabels q T, ((R.goodCrossings q T hq A z).card : ℝ) := by
  classical
  have h1 := R.sum_dart_lower q T hq A (R.unsatDarts (R.kDecode q T hq A)) hH hHT
    (R.crossCount q T hq A)
    (fun p _ i hi j hj => R.crossCount_eq_prod q T hq A p (hsq i hi j hj))
  have h2 := R.sum_Cd_le_sum_goodCrossings q T hq A hHT (R.crossCount q T hq A)
    (fun p _ i _ j _ hij hiT hjT => R.crossCount_eq_card q T hq A p hij hiT hjT) hsq
  have h3 : (R.unsatDarts (R.kDecode q T hq A)).card
      * ((q - 1) * ((R.graph.deg ^ T * q ^ T
            - Fintype.card α * pluralityLoss R.graph.deg q T H)
          * (R.graph.deg ^ T * q ^ T
            - Fintype.card α * pluralityLoss R.graph.deg q T H)))
      ≤ Fintype.card α ^ 2 * (R.graph.deg ^ (T + 1) * q ^ T)
        * ∑ z : R.graph.V × R.KLabels q T, (R.goodCrossings q T hq A z).card := by
    refine le_trans h1 ?_
    have hmul : (∑ p ∈ R.unsatDarts (R.kDecode q T hq A), ∑ i ∈ Finset.range (H + 1),
          ∑ j ∈ Finset.range (H + 1), R.crossCount q T hq A p i j)
          * (R.graph.deg ^ (T + 1) * q ^ T)
        ≤ (∑ z : R.graph.V × R.KLabels q T, (R.goodCrossings q T hq A z).card)
          * (R.graph.deg ^ (T + 1) * q ^ T) :=
      Nat.mul_le_mul_right _ h2
    calc Fintype.card α ^ 2
          * ((∑ p ∈ R.unsatDarts (R.kDecode q T hq A), ∑ i ∈ Finset.range (H + 1),
              ∑ j ∈ Finset.range (H + 1), R.crossCount q T hq A p i j)
            * (R.graph.deg ^ (T + 1) * q ^ T))
        ≤ Fintype.card α ^ 2
          * ((∑ z : R.graph.V × R.KLabels q T, (R.goodCrossings q T hq A z).card)
            * (R.graph.deg ^ (T + 1) * q ^ T)) := Nat.mul_le_mul_left _ hmul
      _ = Fintype.card α ^ 2 * (R.graph.deg ^ (T + 1) * q ^ T)
          * ∑ z : R.graph.V × R.KLabels q T, (R.goodCrossings q T hq A z).card := by ring
  have h4 : (((R.unsatDarts (R.kDecode q T hq A)).card
        * ((q - 1) * ((R.graph.deg ^ T * q ^ T
              - Fintype.card α * pluralityLoss R.graph.deg q T H)
            * (R.graph.deg ^ T * q ^ T
              - Fintype.card α * pluralityLoss R.graph.deg q T H))) : ℕ) : ℝ)
      ≤ ((Fintype.card α ^ 2 * (R.graph.deg ^ (T + 1) * q ^ T)
        * ∑ z : R.graph.V × R.KLabels q T, (R.goodCrossings q T hq A z).card : ℕ) : ℝ) := by
    exact_mod_cast h3
  refine le_trans h4 ?_
  push_cast
  exact le_refl _

/-- **Soundness of the killed powering step.** Combining the first moment
(`sum_goodCrossings_ge`) with the second (`sum_sq_goodCrossings_le`) through
Paley–Zygmund: a constant fraction of the powered constraints fail, the constant
being the ratio of the squared first moment to the second.

The first moment is proportional to the number of darts the decoded assignment
fails, so this is the amplification: the powered system's value is bounded below
in terms of the original's. -/
theorem powering_soundness (A : (R.killedPow q T hq).Assignment) {H : ℕ}
    (hH : 2 * H + 1 < T) (hHT : H + 1 ≤ T)
    (hsq : ∀ i ∈ Finset.range (H + 1), ∀ j ∈ Finset.range (H + 1), i + j + 1 < T)
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlam1 : lam < 1) (hspec : R.graph.SpectralBound lam)
    (hn : 0 < R.graph.order)
    (hBub : 0 < (∑ z : R.graph.V × R.KLabels q T, ((R.goodCrossings q T hq A z).card : ℝ))
      + 2 * ((q : ℝ) ^ T * ((R.graph.deg : ℝ) ^ (T - 2)
        * ((T : ℝ) * (T : ℝ) * (((R.unsatDarts (R.kDecode q T hq A)).card : ℝ)
              * ((R.unsatDarts (R.kDecode q T hq A)).card : ℝ) / (R.graph.order : ℝ))
          + (T : ℝ) * (1 / (1 - lam)) * ((R.graph.deg : ℝ)
              * ((R.unsatDarts (R.kDecode q T hq A)).card : ℝ)))))) :
    ((((R.unsatDarts (R.kDecode q T hq A)).card
          * ((q - 1) * ((R.graph.deg ^ T * q ^ T
                - Fintype.card α * pluralityLoss R.graph.deg q T H)
              * (R.graph.deg ^ T * q ^ T
                - Fintype.card α * pluralityLoss R.graph.deg q T H))) : ℕ) : ℝ)
        / ((Fintype.card α ^ 2 * (R.graph.deg ^ (T + 1) * q ^ T) : ℕ) : ℝ)) ^ 2
      / ((∑ z : R.graph.V × R.KLabels q T, ((R.goodCrossings q T hq A z).card : ℝ))
        + 2 * ((q : ℝ) ^ T * ((R.graph.deg : ℝ) ^ (T - 2)
          * ((T : ℝ) * (T : ℝ) * (((R.unsatDarts (R.kDecode q T hq A)).card : ℝ)
                * ((R.unsatDarts (R.kDecode q T hq A)).card : ℝ) / (R.graph.order : ℝ))
            + (T : ℝ) * (1 / (1 - lam)) * ((R.graph.deg : ℝ)
                * ((R.unsatDarts (R.kDecode q T hq A)).card : ℝ))))))
      ≤ (((R.killedPow q T hq).unsatDarts A).card : ℝ) := by
  classical
  have hK : (0 : ℝ) < ((Fintype.card α ^ 2 * (R.graph.deg ^ (T + 1) * q ^ T) : ℕ) : ℝ) := by
    have hd : 0 < R.graph.deg := R.graph.deg_pos
    have : 0 < Fintype.card α ^ 2 * (R.graph.deg ^ (T + 1) * q ^ T) := by positivity
    exact_mod_cast this
  have hA0 : (0 : ℝ) ≤ (((R.unsatDarts (R.kDecode q T hq A)).card
        * ((q - 1) * ((R.graph.deg ^ T * q ^ T
              - Fintype.card α * pluralityLoss R.graph.deg q T H)
            * (R.graph.deg ^ T * q ^ T
              - Fintype.card α * pluralityLoss R.graph.deg q T H))) : ℕ) : ℝ)
      / ((Fintype.card α ^ 2 * (R.graph.deg ^ (T + 1) * q ^ T) : ℕ) : ℝ) := by positivity
  have hA : (((R.unsatDarts (R.kDecode q T hq A)).card
        * ((q - 1) * ((R.graph.deg ^ T * q ^ T
              - Fintype.card α * pluralityLoss R.graph.deg q T H)
            * (R.graph.deg ^ T * q ^ T
              - Fintype.card α * pluralityLoss R.graph.deg q T H))) : ℕ) : ℝ)
      / ((Fintype.card α ^ 2 * (R.graph.deg ^ (T + 1) * q ^ T) : ℕ) : ℝ)
      ≤ ∑ z : R.graph.V × R.KLabels q T, ((R.goodCrossings q T hq A z).card : ℝ) := by
    rw [div_le_iff₀ hK]
    have h := R.sum_goodCrossings_ge q T hq A hH hHT hsq
    linarith [h]
  exact R.card_unsatDarts_ge q T hq A hA0 hA
    (R.sum_sq_goodCrossings_le q T hq A hlam0 hlam1 hspec hn) hBub

omit [Fintype α] [DecidableEq α] [Nonempty α] in
/-- The powered system's constraint count. -/
theorem card_dart_killedPow :
    ((R.killedPow q T hq).graph.order * (R.killedPow q T hq).graph.deg : ℕ)
      = R.graph.order * (R.graph.deg ^ T * q ^ T) := by
  show ((R.graph.killedPower q T hq).order * (R.graph.killedPower q T hq).deg : ℕ) = _
  rw [R.graph.order_killedPower, R.graph.deg_killedPower]

omit [Fintype α] [DecidableEq α] [Nonempty α] in
/-- A lower bound on the unsatisfied constraints becomes one on the unsatisfied
*fraction*, which is what `unsatVal` and the amplification bookkeeping use. -/
theorem unsatFrac_killedPow_ge (A : (R.killedPow q T hq).Assignment) {LB : ℝ}
    (hLB : LB ≤ (((R.killedPow q T hq).unsatDarts A).card : ℝ)) (hn : 0 < R.graph.order) :
    LB / ((R.graph.order * (R.graph.deg ^ T * q ^ T) : ℕ) : ℝ)
      ≤ (((R.killedPow q T hq).unsatFrac A : ℚ) : ℝ) := by
  have hpos : (0 : ℝ) < ((R.graph.order * (R.graph.deg ^ T * q ^ T) : ℕ) : ℝ) := by
    have hd : 0 < R.graph.deg := R.graph.deg_pos
    have : 0 < R.graph.order * (R.graph.deg ^ T * q ^ T) := by positivity
    exact_mod_cast this
  have hfrac : (((R.killedPow q T hq).unsatFrac A : ℚ) : ℝ)
      = (((R.killedPow q T hq).unsatDarts A).card : ℝ)
        / ((R.graph.order * (R.graph.deg ^ T * q ^ T) : ℕ) : ℝ) := by
    rw [RegCSP.unsatFrac, R.card_dart_killedPow q T hq]
    push_cast
    field_simp
    norm_cast
  rw [hfrac]
  gcongr

omit [DecidableEq α] in
/-- A bound holding for every assignment holds for the value. -/
theorem le_unsatVal_killedPow {LB : ℝ}
    (h : ∀ A : (R.killedPow q T hq).Assignment,
      LB ≤ (((R.killedPow q T hq).unsatFrac A : ℚ) : ℝ)) :
    LB ≤ (((R.killedPow q T hq).unsatVal : ℚ) : ℝ) := by
  obtain ⟨A, hA⟩ := (R.killedPow q T hq).exists_assignment_unsatFrac_eq_unsatVal
  rw [← hA]
  exact h A

end RegCSP

end Complexity
