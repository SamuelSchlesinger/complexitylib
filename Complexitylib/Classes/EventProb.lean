/-
Copyright (c) 2025 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Classes.FiniteCounting
public import Complexitylib.Models.TuringMachine
public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Data.Nat.Choose.Sum
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Positivity.Finset

/-!
# Finite event probability

The uniform probability of a finite event over `T` random bits, `|E| / 2^T`,
defined once as `eventProb` and related to `Finset.card` and to the existing
rational PTM acceptance probability `NTM.acceptProb` (roadmap track N2).

## Main results

- `eventProb` with `eventProb_nonneg`, `eventProb_mono`, `eventProb_le_one`, `eventProb_empty`,
  `eventProb_univ`, the complement identity `eventProb_compl`, and the union
  bound `eventProb_union_le`
- `eventProb_le_uniformAverage_div` — finite-uniform Markov inequality
- `eventProb_biUnion`, `eventProb_eq_sum_fiberwise` — finite additivity and the
  conditioning-by-partition identity
- `eventProb_filter_of_constant_fibers`, `eventProb_repeatRandomSeed` — cancel
  uniformly ignored random bits, including the fixed-time repetition schedule
- `eventProb_block` — independence across blocks: a prefix/suffix-separable event's
  probability is the product of the two block probabilities
- `eventProb_blockMajority_eq_false` — the exact weighted binomial tail for
  majority failure across an odd number of independent blocks
- `eventProb_blockMajority_false_le_two_pow` — `12k + 1` independent repetitions
  reduce error from at most `1/3` to at most `1 / 2^k`
- `eventProb_blockMajority_true_ge_one_sub_two_pow`,
  `eventProb_blockMajority_true_le_two_pow` — the corresponding amplified
  yes- and no-instance bounds
- `exists_good_seed_of_sum_eventProb_lt_one`,
  `exists_good_seed_of_eventProb_le_two_pow_succ` — probabilistic-method
  adapters from bad-event bounds to one seed that works on every input
- `NTM.acceptProb_eq_eventProb` — the PTM acceptance probability *is* the event
  probability of its set of accepting choice sequences
- `NTM.traceEventProb_eq_of_le_of_allChoicesHalt` — extending an observation
  clock after every path has halted preserves every event on the final state;
  in particular, acceptance and output probabilities are clock-invariant
- `NTM.acceptProb_eq_eventProb_repeatRandomSeed` — remove administrative random
  bits when a machine's acceptance factors through the compact repetition seed
-/


@[expose] public section

namespace Complexity

/-- The uniform probability of a finite event `E ⊆ (Fin T → Bool)`: the fraction
    of the `2^T` random bit strings that lie in `E`. -/
def eventProb {T : ℕ} (E : Finset (Fin T → Bool)) : ℚ := (E.card : ℚ) / 2 ^ T

theorem eventProb_nonneg {T : ℕ} (E : Finset (Fin T → Bool)) : 0 ≤ eventProb E := by
  unfold eventProb; positivity

/-- Probability is monotone under event inclusion. -/
theorem eventProb_mono {T : ℕ} {E F : Finset (Fin T → Bool)} (h : E ⊆ F) :
    eventProb E ≤ eventProb F := by
  unfold eventProb
  gcongr

/-- Every finite event has cardinality at most the size of the sample space. -/
theorem card_le_pow {T : ℕ} (E : Finset (Fin T → Bool)) : E.card ≤ 2 ^ T := by
  have h := Finset.card_le_univ E
  rwa [card_finArrowBool] at h

theorem eventProb_le_one {T : ℕ} (E : Finset (Fin T → Bool)) : eventProb E ≤ 1 := by
  have hpos : ((2 : ℚ) ^ T) ≠ 0 := by positivity
  have h : (E.card : ℚ) ≤ 2 ^ T := by exact_mod_cast card_le_pow E
  calc eventProb E = (E.card : ℚ) / 2 ^ T := rfl
    _ ≤ (2 ^ T) / 2 ^ T := by gcongr
    _ = 1 := div_self hpos

/-- **Markov's inequality for the finite uniform sample space.** If every point
in `E` has nonnegative weight at least `threshold`, then the probability of
`E` is at most the uniform average weight divided by `threshold`. -/
theorem eventProb_le_uniformAverage_div {T : ℕ}
    (E : Finset (Fin T → Bool)) (weight : (Fin T → Bool) → ℚ)
    (threshold : ℚ) (hthreshold : 0 < threshold)
    (hweight : ∀ seed, 0 ≤ weight seed)
    (hlarge : ∀ seed ∈ E, threshold ≤ weight seed) :
    eventProb E ≤
      ((∑ seed : Fin T → Bool, weight seed) / (2 : ℚ) ^ T) / threshold := by
  rw [le_div_iff₀ hthreshold]
  unfold eventProb
  rw [div_mul_eq_mul_div]
  apply (div_le_div_iff_of_pos_right (by positivity : (0 : ℚ) < 2 ^ T)).2
  calc
    (E.card : ℚ) * threshold = ∑ _seed ∈ E, threshold := by simp
    _ ≤ ∑ seed ∈ E, weight seed := by
      exact Finset.sum_le_sum fun seed hseed => hlarge seed hseed
    _ ≤ ∑ seed : Fin T → Bool, weight seed := by
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ E)
        fun seed _ _ => hweight seed

/-! ### Good seeds from probability bounds -/

/-- **The probabilistic method in probability form.** If the sum, over a
    finite input set, of the probabilities of the corresponding bad-seed
    events is strictly below one, then one seed avoids every bad event. -/
theorem exists_good_seed_of_sum_eventProb_lt_one {S : ℕ} {ι : Type*}
    (inputs : Finset ι) (bad : ι → Finset (Fin S → Bool))
    (h : ∑ i ∈ inputs, eventProb (bad i) < 1) :
    ∃ seed : Fin S → Bool, ∀ i ∈ inputs, seed ∉ bad i := by
  apply exists_good_seed inputs bad
  rw [card_finArrowBool]
  have hden : (0 : ℚ) < 2 ^ S := by positivity
  unfold eventProb at h
  rw [← Finset.sum_div, div_lt_one hden] at h
  exact_mod_cast h

/-- A `2^-(n+1)` bad-seed bound for each `n`-bit input leaves a single seed
    that is good for all inputs simultaneously. The strict slack of one bit
    makes the argument uniform even when `n = 0` or `S = 0`. -/
theorem exists_good_seed_of_eventProb_le_two_pow_succ (n S : ℕ)
    (bad : (Fin n → Bool) → Finset (Fin S → Bool))
    (hbad : ∀ x, eventProb (bad x) ≤ 1 / (2 : ℚ) ^ (n + 1)) :
    ∃ seed : Fin S → Bool, ∀ x, seed ∉ bad x := by
  have hsum :
      ∑ x ∈ (Finset.univ : Finset (Fin n → Bool)), eventProb (bad x) < 1 := by
    calc
      ∑ x ∈ (Finset.univ : Finset (Fin n → Bool)), eventProb (bad x)
          ≤ ∑ _x ∈ (Finset.univ : Finset (Fin n → Bool)),
              1 / (2 : ℚ) ^ (n + 1) := by
            exact Finset.sum_le_sum fun x _ => hbad x
      _ = (((2 ^ n : ℕ) : ℚ) * (1 / (2 : ℚ) ^ (n + 1))) := by
        simp
      _ = 1 / 2 := by
        rw [show (((2 ^ n : ℕ) : ℚ)) = (2 : ℚ) ^ n by norm_cast, pow_succ]
        field_simp
      _ < 1 := by norm_num
  obtain ⟨seed, hseed⟩ :=
    exists_good_seed_of_sum_eventProb_lt_one Finset.univ bad hsum
  exact ⟨seed, fun x => hseed x (Finset.mem_univ x)⟩

@[simp] theorem eventProb_empty {T : ℕ} : eventProb (∅ : Finset (Fin T → Bool)) = 0 := by
  simp [eventProb]

@[simp] theorem eventProb_univ {T : ℕ} :
    eventProb (Finset.univ : Finset (Fin T → Bool)) = 1 := by
  have hpos : ((2 : ℚ) ^ T) ≠ 0 := by positivity
  simp only [eventProb, Finset.card_univ, card_finArrowBool]
  rw [show ((2 ^ T : ℕ) : ℚ) = (2 : ℚ) ^ T by norm_cast]
  exact div_self hpos

/-- The probability of the complement of an event is one minus its probability. -/
theorem eventProb_compl {T : ℕ} (E : Finset (Fin T → Bool)) :
    eventProb Eᶜ = 1 - eventProb E := by
  have hpos : ((2 : ℚ) ^ T) ≠ 0 := by positivity
  have hcard : (Eᶜ.card : ℚ) = 2 ^ T - E.card := by
    have h1 : Eᶜ.card = 2 ^ T - E.card := by
      rw [Finset.card_compl, card_finArrowBool]
    rw [h1, Nat.cast_sub (card_le_pow E)]
    norm_cast
  unfold eventProb
  rw [hcard, sub_div, div_self hpos]

/-- For a Boolean-valued experiment, success probability is one minus failure
probability. -/
theorem eventProb_filter_bool_true (T : ℕ)
    (f : (Fin T → Bool) → Bool) :
    eventProb (Finset.univ.filter (fun w => f w = true)) =
      1 - eventProb (Finset.univ.filter (fun w => f w = false)) := by
  rw [← eventProb_compl]
  congr 1
  ext w
  cases f w <;> simp

/-- The **union bound** in probability form: the probability of `E ∪ F` is at
    most the sum of their probabilities. -/
theorem eventProb_union_le {T : ℕ} (E F : Finset (Fin T → Bool)) :
    eventProb (E ∪ F) ≤ eventProb E + eventProb F := by
  unfold eventProb
  rw [← add_div]
  gcongr
  exact_mod_cast Finset.card_union_le E F

/-- **The union bound** over a finite family of events: the probability of the
    union `⋃ᵢ Eᵢ` is at most the sum of the individual probabilities. The
    amplification workhorse — bounding the failure probability across many bad
    events. -/
theorem eventProb_biUnion_le {T : ℕ} {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (E : ι → Finset (Fin T → Bool)) :
    eventProb (s.biUnion E) ≤ ∑ i ∈ s, eventProb (E i) := by
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.biUnion_insert, Finset.sum_insert ha]
    refine le_trans (eventProb_union_le _ _) ?_
    gcongr

/-- Finite additivity: the probability of a disjoint finite union is the sum of
    the probabilities of its events. -/
-- The signature mirrors the family this belongs to; the argument is part of
-- that shape even where this member does not consult it.
@[nolint unusedArguments]
theorem eventProb_biUnion {T : ℕ} {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (E : ι → Finset (Fin T → Bool))
    (h : (s : Set ι).PairwiseDisjoint E) :
    eventProb (s.biUnion E) = ∑ i ∈ s, eventProb (E i) := by
  unfold eventProb
  rw [Finset.card_biUnion h]
  push_cast
  rw [Finset.sum_div]

/-- **Conditioning by a finite partition.** If the statistic `f` maps every point
    of `E` into the finite index set `s`, then `E` is the disjoint union of its
    fibers and its probability is the sum of their probabilities. -/
theorem eventProb_eq_sum_fiberwise {T : ℕ} {ι : Type*} [DecidableEq ι]
    (E : Finset (Fin T → Bool)) (s : Finset ι) (f : (Fin T → Bool) → ι)
    (h : (E : Set (Fin T → Bool)).MapsTo f s) :
    eventProb E = ∑ i ∈ s, eventProb (E.filter fun w => f w = i) := by
  unfold eventProb
  rw [Finset.card_eq_sum_card_fiberwise h]
  push_cast
  rw [Finset.sum_div]

/-- **Uniformly ignored random bits cancel from event probability.** If an event
    on `total = compact + ignored` bits factors through a compact-seed projection
    whose fibers all have size `2 ^ ignored`, its probability is exactly the
    probability of the corresponding compact event. -/
theorem eventProb_filter_of_constant_fibers
    {total compact ignored : ℕ} (htotal : total = compact + ignored)
    (randomSeed : (Fin total → Bool) → (Fin compact → Bool))
    (Accept : (Fin total → Bool) → Prop)
    (Good : (Fin compact → Bool) → Prop)
    [DecidablePred Accept] [DecidablePred Good]
    (hfactor : ∀ w, Accept w ↔ Good (randomSeed w))
    (hfiber : ∀ seed,
      (Finset.univ.filter fun w => randomSeed w = seed).card = 2 ^ ignored) :
    eventProb (Finset.univ.filter Accept) =
      eventProb (Finset.univ.filter Good) := by
  unfold eventProb
  rw [card_filter_of_constant_fibers randomSeed Accept Good hfactor hfiber, htotal,
    pow_add]
  push_cast
  field_simp

/-- The fixed-time repetition schedule's administrative choices do not change
    the probability of an event depending only on its `k * T` simulation bits. -/
theorem eventProb_repeatRandomSeed (k T : ℕ)
    (P : (Fin (k * T) → Bool) → Prop) [DecidablePred P] :
    eventProb (Finset.univ.filter (fun w : Fin (2 + k * (2 * T + 2)) → Bool =>
      P (repeatRandomSeed k T w))) =
      eventProb (Finset.univ.filter P) := by
  apply eventProb_filter_of_constant_fibers
      (total := 2 + k * (2 * T + 2)) (compact := k * T)
      (ignored := 2 + k * (T + 2)) (randomSeed := repeatRandomSeed k T)
  · ring
  · intro w
    rfl
  · exact card_repeatRandomSeed_fiber k T

/-- **Independence across blocks (probability form).** For an event that constrains
    the prefix and suffix of a length-`a + b` random string separately, the joint
    probability is the product of the two block probabilities. This is the
    probability-level counterpart of `card_filter_block` and the quantitative engine
    behind error amplification: `k` independent runs multiply their success
    probabilities. -/
theorem eventProb_block {a b : ℕ}
    (P : (Fin a → Bool) → Prop) (Q : (Fin b → Bool) → Prop)
    [DecidablePred P] [DecidablePred Q] :
    eventProb (Finset.univ.filter
        (fun w : Fin (a + b) → Bool => P (blockFst a b w) ∧ Q (blockSnd a b w)))
      = eventProb (Finset.univ.filter P) * eventProb (Finset.univ.filter Q) := by
  unfold eventProb
  rw [card_filter_block, pow_add, div_mul_div_comm]
  push_cast
  rfl

private theorem weighted_term_normalize (T n j : ℕ)
    (E : Finset (Fin T → Bool)) (hj : j ≤ n) :
    ((n.choose j : ℚ) * (E.card : ℚ) ^ j *
        ((2 ^ T - E.card : ℕ) : ℚ) ^ (n - j) /
        (2 : ℚ) ^ (n * T)) =
      (n.choose j : ℚ) * eventProb E ^ j *
        (1 - eventProb E) ^ (n - j) := by
  have hcard : E.card ≤ 2 ^ T := card_le_pow E
  rw [eventProb, show (1 : ℚ) - (E.card : ℚ) / 2 ^ T =
      ((2 ^ T - E.card : ℕ) : ℚ) / 2 ^ T by
    rw [Nat.cast_sub hcard]
    norm_cast
    field_simp
    exact (Nat.cast_sub hcard).symm]
  rw [div_pow, div_pow, ← mul_div_assoc]
  field_simp
  have hden : ((2 : ℚ) ^ T) ^ j * ((2 : ℚ) ^ T) ^ (n - j) =
      (2 : ℚ) ^ (n * T) := by
    rw [← pow_add, Nat.add_sub_of_le hj, ← pow_mul, Nat.mul_comm T n]
  simp only [mul_assoc]
  rw [hden]

/-- **Exact majority-failure probability across independent blocks.** Splitting a
    uniform long seed into `2r + 1` blocks makes block-event membership independent,
    so the failure probability is the lower tail of the binomial distribution with
    success probability `eventProb E`. -/
theorem eventProb_blockMajority_eq_false
    (T r : ℕ) (E : Finset (Fin T → Bool)) :
    eventProb (Finset.univ.filter (fun w : Fin ((2 * r + 1) * T) → Bool =>
      blockMajority E w = false)) =
      ∑ j ∈ Finset.range (r + 1),
        ((2 * r + 1).choose j : ℚ) * eventProb E ^ j *
          (1 - eventProb E) ^ (2 * r + 1 - j) := by
  rw [eventProb, card_blockMajority_eq_false]
  push_cast
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro j hj
  apply weighted_term_normalize
  simp only [Finset.mem_range] at hj
  omega

/-- The lower tail of an odd binomial distribution with success probability at
    least `2/3` is at most `(1/3) * (8/9)^r`. This deliberately uses a coarse
    elementary bound rather than a Chernoff inequality: each failure term is
    bounded by `(1/3) * (2/9)^r`, and the lower-half binomial coefficients sum to
    `4^r`. -/
theorem binomial_lower_tail_le (r : ℕ) (p : ℚ)
    (hp_lower : 2 / 3 ≤ p) (hp_upper : p ≤ 1) :
    (∑ j ∈ Finset.range (r + 1),
        ((2 * r + 1).choose j : ℚ) * p ^ j *
          (1 - p) ^ (2 * r + 1 - j)) ≤
      (1 / 3) * (8 / 9) ^ r := by
  have hp_nonneg : 0 ≤ p := by linarith
  have hq_nonneg : 0 ≤ 1 - p := sub_nonneg.mpr hp_upper
  have hq_le_p : 1 - p ≤ p := by linarith
  have hq_le : 1 - p ≤ 1 / 3 := by linarith
  have hpq_le : p * (1 - p) ≤ 2 / 9 := by
    have hp_third : 1 / 3 ≤ p := by linarith
    have hprod : 0 ≤ (p - 2 / 3) * (p - 1 / 3) :=
      mul_nonneg (sub_nonneg.mpr hp_lower) (sub_nonneg.mpr hp_third)
    nlinarith
  calc
    (∑ j ∈ Finset.range (r + 1),
        ((2 * r + 1).choose j : ℚ) * p ^ j *
          (1 - p) ^ (2 * r + 1 - j)) ≤
        ∑ j ∈ Finset.range (r + 1),
          ((2 * r + 1).choose j : ℚ) * (p ^ r * (1 - p) ^ (r + 1)) := by
      apply Finset.sum_le_sum
      intro j hj
      simp only [Finset.mem_range] at hj
      have hjr : j ≤ r := by omega
      have hexp : 2 * r + 1 - j = (r - j) + (r + 1) := by omega
      have hpow : (1 - p) ^ (r - j) ≤ p ^ (r - j) :=
        pow_le_pow_left₀ hq_nonneg hq_le_p _
      calc
        ((2 * r + 1).choose j : ℚ) * p ^ j * (1 - p) ^ (2 * r + 1 - j) =
            ((2 * r + 1).choose j : ℚ) *
              (p ^ j * (1 - p) ^ (r - j)) * (1 - p) ^ (r + 1) := by
          rw [hexp, pow_add]
          ring
        _ ≤ ((2 * r + 1).choose j : ℚ) *
            (p ^ j * p ^ (r - j)) * (1 - p) ^ (r + 1) := by
          gcongr
        _ = ((2 * r + 1).choose j : ℚ) * (p ^ r * (1 - p) ^ (r + 1)) := by
          rw [← pow_add, Nat.add_sub_of_le hjr]
          ring
    _ = (4 : ℚ) ^ r * (p ^ r * (1 - p) ^ (r + 1)) := by
      rw [← Finset.sum_mul]
      congr 1
      rw [← Nat.cast_sum, Nat.sum_range_choose_halfway]
      norm_cast
    _ = (4 : ℚ) ^ r * ((1 - p) * (p * (1 - p)) ^ r) := by
      congr 1
      rw [pow_succ, mul_pow]
      ring
    _ ≤ (4 : ℚ) ^ r * ((1 / 3) * (2 / 9) ^ r) := by
      gcongr
    _ = (1 / 3) * (8 / 9) ^ r := by
      rw [show (8 / 9 : ℚ) = 4 * (2 / 9) by norm_num, mul_pow]
      ring

private theorem amplification_power_le (k : ℕ) :
    (1 / 3 : ℚ) * (8 / 9) ^ (6 * k) ≤ 1 / (2 : ℚ) ^ k := by
  have hbase : (8 / 9 : ℚ) ^ 6 ≤ 1 / 2 := by norm_num
  have hpow : (8 / 9 : ℚ) ^ (6 * k) ≤ (1 / 2) ^ k := by
    rw [pow_mul]
    exact pow_le_pow_left₀ (by positivity) hbase k
  calc
    (1 / 3 : ℚ) * (8 / 9) ^ (6 * k) ≤ 1 * (1 / 2) ^ k := by
      gcongr
      norm_num
    _ = 1 / (2 : ℚ) ^ k := by rw [one_mul, one_div_pow]

private theorem eventProb_blockMajority_false_le_two_pow_aux
    (T k : ℕ) (E : Finset (Fin T → Bool)) (hE : 2 / 3 ≤ eventProb E) :
    eventProb (Finset.univ.filter (fun w : Fin ((2 * (6 * k) + 1) * T) → Bool =>
      blockMajority E w = false)) ≤ 1 / (2 : ℚ) ^ k := by
  calc
    eventProb (Finset.univ.filter (fun w : Fin ((2 * (6 * k) + 1) * T) → Bool =>
      blockMajority E w = false)) =
        ∑ j ∈ Finset.range (6 * k + 1),
          ((2 * (6 * k) + 1).choose j : ℚ) * eventProb E ^ j *
            (1 - eventProb E) ^ (2 * (6 * k) + 1 - j) :=
      eventProb_blockMajority_eq_false T (6 * k) E
    _ ≤ (1 / 3 : ℚ) * (8 / 9) ^ (6 * k) :=
      binomial_lower_tail_le (6 * k) (eventProb E) hE (eventProb_le_one E)
    _ ≤ 1 / (2 : ℚ) ^ k := amplification_power_le k

/-- **Concrete error amplification.** If one `T`-bit trial succeeds with
    probability at least `2/3`, then the strict majority of `12k + 1` independent
    trials fails with probability at most `1 / 2^k`. The explicit odd repetition
    count avoids ties and is sufficient for later BPP and protocol amplification. -/
theorem eventProb_blockMajority_false_le_two_pow
    (T k : ℕ) (E : Finset (Fin T → Bool)) (hE : 2 / 3 ≤ eventProb E) :
    eventProb (Finset.univ.filter (fun w : Fin ((12 * k + 1) * T) → Bool =>
      blockMajority E w = false)) ≤ 1 / (2 : ℚ) ^ k := by
  have hreps : 2 * (6 * k) + 1 = 12 * k + 1 := by omega
  rw [← hreps]
  exact eventProb_blockMajority_false_le_two_pow_aux T k E hE

/-- Majority amplification on yes-instances: a source success probability at
least `2/3` becomes at least `1 - 2^-k` after `12k + 1` trials. -/
theorem eventProb_blockMajority_true_ge_one_sub_two_pow
    (T k : ℕ) (E : Finset (Fin T → Bool)) (hE : 2 / 3 ≤ eventProb E) :
    1 - 1 / (2 : ℚ) ^ k ≤
      eventProb (Finset.univ.filter
        (fun w : Fin ((12 * k + 1) * T) → Bool => blockMajority E w = true)) := by
  rw [eventProb_filter_bool_true]
  have hfail := eventProb_blockMajority_false_le_two_pow T k E hE
  linarith

/-- Majority amplification on no-instances: a source success probability at
most `1/3` becomes at most `2^-k` after `12k + 1` trials. -/
theorem eventProb_blockMajority_true_le_two_pow
    (T k : ℕ) (E : Finset (Fin T → Bool)) (hE : eventProb E ≤ 1 / 3) :
    eventProb (Finset.univ.filter
        (fun w : Fin ((12 * k + 1) * T) → Bool => blockMajority E w = true))
      ≤ 1 / (2 : ℚ) ^ k := by
  have hcompl : 2 / 3 ≤ eventProb Eᶜ := by
    rw [eventProb_compl]
    linarith
  have htail := eventProb_blockMajority_false_le_two_pow T k Eᶜ hcompl
  have hodd : Odd (12 * k + 1) := ⟨6 * k, by omega⟩
  have hset :
      Finset.univ.filter
          (fun w : Fin ((12 * k + 1) * T) → Bool => blockMajority E w = true) =
        Finset.univ.filter
          (fun w : Fin ((12 * k + 1) * T) → Bool => blockMajority Eᶜ w = false) := by
    ext w
    have hflip := blockMajority_compl_of_odd hodd E w
    cases h : blockMajority E w <;> simp_all
  rw [hset]
  exact htail

/-- Event probability is invariant under any relabeling of the sample space — in
    particular under permuting the bit positions (`Equiv.arrowCongr σ`) — since a
    bijection preserves cardinality. -/
theorem eventProb_map {T : ℕ} (e : (Fin T → Bool) ≃ (Fin T → Bool))
    (E : Finset (Fin T → Bool)) :
    eventProb (E.map e.toEmbedding) = eventProb E := by
  unfold eventProb
  rw [Finset.card_map]

/-- The PTM acceptance probability is exactly the event probability of the set of
    accepting choice sequences: this ties `NTM.acceptProb` to the abstract
    `eventProb` / `Finset.card` layer. -/
theorem NTM.acceptProb_eq_eventProb {n : ℕ} (tm : NTM n) (x : List Bool) (T : ℕ) :
    tm.acceptProb x T =
      eventProb (Finset.univ.filter fun choices : Fin T → Bool =>
        let c' := tm.trace T choices (tm.initCfg x)
        c'.state = tm.qhalt ∧ c'.output.cells 1 = Γ.one) := by
  rfl

/-- Once every path from `c` has halted by time `T`, extending the observation
clock to any `T' ≥ T` preserves the probability of every decidable event on the
final configuration. Halted traces are fixed, and every length-`T` choice
sequence has the same number of extensions, so the extra random bits cancel. -/
theorem NTM.traceEventProb_eq_of_le_of_allChoicesHalt {n T T' : ℕ}
    (tm : NTM n) (c : Cfg n tm.Q)
    (event : Cfg n tm.Q → Prop) [DecidablePred event] (hle : T ≤ T')
    (hhalt : ∀ choices : Fin T → Bool,
      tm.halted (tm.trace T choices c)) :
    eventProb (Finset.univ.filter fun choices : Fin T' → Bool =>
      event (tm.trace T' choices c)) =
      eventProb (Finset.univ.filter fun choices : Fin T → Bool =>
        event (tm.trace T choices c)) := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hle
  let occurs : (Fin T → Bool) → Prop := fun choices =>
    event (tm.trace T choices c)
  have hpredicate : ∀ choices : Fin (T + d) → Bool,
      event (tm.trace (T + d) choices c) ↔
        occurs (blockFst T d choices) := by
    intro choices
    have htrace := tm.trace_mono (Nat.le_add_right T d)
      (choices := blockFst T d choices) (choices' := choices)
      (c := c) (fun _ => rfl) (hhalt _)
    simp only [occurs]
    rw [htrace]
  rw [show
      (Finset.univ.filter fun choices : Fin (T + d) → Bool =>
        event (tm.trace (T + d) choices c)) =
        Finset.univ.filter
          (fun choices => occurs (blockFst T d choices) ∧ True) by
    ext choices
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, and_true]
    exact hpredicate choices]
  have hblock := eventProb_block occurs (fun _ : Fin d → Bool => True)
  simpa using hblock

/-- Once every path has halted by time `T`, extending the observation clock to
any `T' ≥ T` leaves acceptance probability unchanged. -/
theorem NTM.acceptProb_eq_of_le_of_allChoicesHalt {n T T' : ℕ}
    (tm : NTM n) (x : List Bool) (hle : T ≤ T')
    (hhalt : ∀ choices : Fin T → Bool,
      tm.halted (tm.trace T choices (tm.initCfg x))) :
    tm.acceptProb x T' = tm.acceptProb x T := by
  rw [NTM.acceptProb_eq_eventProb, NTM.acceptProb_eq_eventProb]
  exact tm.traceEventProb_eq_of_le_of_allChoicesHalt (tm.initCfg x)
    (fun c => c.state = tm.qhalt ∧ c.output.cells 1 = Γ.one) hle hhalt

/-- A pointwise-larger clock gives the same acceptance probability once the
machine satisfies `AllPathsHaltIn` for the smaller clock. -/
theorem NTM.acceptProb_eq_of_le_of_allPathsHaltIn {n : ℕ} {T T' : ℕ → ℕ}
    (tm : NTM n) (hle : ∀ m, T m ≤ T' m) (hhalt : tm.AllPathsHaltIn T)
    (x : List Bool) :
    tm.acceptProb x (T' x.length) = tm.acceptProb x (T x.length) :=
  tm.acceptProb_eq_of_le_of_allChoicesHalt x (hle x.length) (hhalt x)

/-- The PTM probability of output `y` is exactly the event probability of the
choice sequences that halt with that output. -/
theorem NTM.outputProb_eq_eventProb {n : ℕ} (tm : NTM n) (x : List Bool)
    (T : ℕ) (y : List Bool) :
    tm.outputProb x T y =
      eventProb (Finset.univ.filter fun choices : Fin T → Bool =>
        let c := tm.trace T choices (tm.initCfg x)
        c.state = tm.qhalt ∧ c.output.HasOutput y) := by
  rfl

/-- Once every path has halted by time `T`, extending the observation clock to
any `T' ≥ T` leaves every output probability unchanged. -/
theorem NTM.outputProb_eq_of_le_of_allChoicesHalt {n T T' : ℕ}
    (tm : NTM n) (x : List Bool) (y : List Bool) (hle : T ≤ T')
    (hhalt : ∀ choices : Fin T → Bool,
      tm.halted (tm.trace T choices (tm.initCfg x))) :
    tm.outputProb x T' y = tm.outputProb x T y := by
  rw [NTM.outputProb_eq_eventProb, NTM.outputProb_eq_eventProb]
  exact tm.traceEventProb_eq_of_le_of_allChoicesHalt (tm.initCfg x)
    (fun c => c.state = tm.qhalt ∧ c.output.HasOutput y) hle hhalt

/-- A pointwise-larger clock gives the same output probabilities once the
machine satisfies `AllPathsHaltIn` for the smaller clock. -/
theorem NTM.outputProb_eq_of_le_of_allPathsHaltIn {n : ℕ} {T T' : ℕ → ℕ}
    (tm : NTM n) (hle : ∀ m, T m ≤ T' m) (hhalt : tm.AllPathsHaltIn T)
    (x y : List Bool) :
    tm.outputProb x (T' x.length) y = tm.outputProb x (T x.length) y :=
  tm.outputProb_eq_of_le_of_allChoicesHalt x y (hle x.length) (hhalt x)

/-- A repeated machine's administrative random choices cancel from its acceptance
    probability whenever its accepting-path predicate factors through
    `repeatRandomSeed`. The result is the event probability on only the `k * T`
    simulation choices. -/
theorem NTM.acceptProb_eq_eventProb_repeatRandomSeed
    {n : ℕ} (tm : NTM n) (x : List Bool) (k T : ℕ)
    (P : (Fin (k * T) → Bool) → Prop) [DecidablePred P]
    (hfactor : ∀ choices : Fin (2 + k * (2 * T + 2)) → Bool,
      (let c' := tm.trace (2 + k * (2 * T + 2)) choices (tm.initCfg x)
       c'.state = tm.qhalt ∧ c'.output.cells 1 = Γ.one) ↔
        P (repeatRandomSeed k T choices)) :
    tm.acceptProb x (2 + k * (2 * T + 2)) =
      eventProb (Finset.univ.filter P) := by
  rw [NTM.acceptProb_eq_eventProb]
  apply eventProb_filter_of_constant_fibers
      (total := 2 + k * (2 * T + 2)) (compact := k * T)
      (ignored := 2 + k * (T + 2)) (randomSeed := repeatRandomSeed k T)
  · ring
  · exact hfactor
  · exact card_repeatRandomSeed_fiber k T

end Complexity
