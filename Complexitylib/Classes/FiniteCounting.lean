/-
Copyright (c) 2025 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Mathlib.Data.Fintype.Fin
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Data.Finset.Powerset
public import Mathlib.Logic.Equiv.Fin.Basic
public import Mathlib.Algebra.Ring.Parity
public import Mathlib.Order.Interval.Finset.Nat
public import Std.Tactic.BVDecide.Normalize.BitVec
public import Std.Tactic.BVDecide.Normalize.Prop

/-!
# Finite counting toolkit

Exact cardinality lemmas for the finite sample space `Fin T → Bool` used by the
probabilistic-machine semantics (`NTM.acceptCount`, `NTM.acceptProb`). These are
the reusable combinatorial facts underlying randomized classes, amplification,
and interactive proofs (roadmap track N2).

## Main results

- `card_finArrowBool` — `|Fin T → Bool| = 2 ^ T`
- `blockEquiv` — the split of a length-`a + b` random string into its length-`a`
  prefix and length-`b` suffix, packaged as an `Equiv` (so the projection and
  concatenation maps are inverse by construction)
- `card_filter_block` — block independence: the count of seeds whose prefix and
  suffix satisfy given predicates is the product of the two counts
- `card_filter_exists_le` — the finite union bound: the number of sample points
  satisfying *some* predicate in a finite family is at most the sum of the
  per-predicate counts
- `boolFunEquivFinset`, `card_filter_popCount_eq` — Boolean vectors as true
  supports and their exact binomial weight counts
- `finCountP_eq_popCount` — the bridge from the dependency-light `Fin.countP`
  used by circuit encoders to finite-set support counting
- `blocksEquiv`, `card_blockEventCount_eq` — a long machine seed as independent
  blocks and the exact weighted binomial count for any block event
- `tupleEventCount`, `card_tupleEventCount_eq` — the corresponding generic
  weighted binomial count for tuples over any finite type
- `repeatRandomSeed`, `card_repeatRandomSeed_fiber` — extract the actual simulation
  slots from a fixed-time repetition seed and count its ignored administrative bits
- `card_filter_of_constant_fibers` — transfer an event count through a projection
  whose fibers all have the same power-of-two cardinality
- `card_blockMajority_eq_false` — the exact weighted lower-tail count for failure
  across an odd number of blocks
- `blockEventCount_add_compl`, `blockMajority_compl_of_odd` — event-complement
  symmetry for block counts and odd strict majorities
- `card_majority_eq_true`, `card_majority_eq_false` — exact binomial-tail counts
  for strict-majority success and failure
- `majority_not_of_odd` — strict majority is antisymmetric under pointwise
  negation at odd length
-/


@[expose] public section

namespace Complexity

/-! ### Cardinality of the random-bit sample space -/

/-- The finite sample space of `T` random bits has `2 ^ T` points. This is the
    denominator in `NTM.acceptProb`. -/
theorem card_finArrowBool (T : ℕ) : Fintype.card (Fin T → Bool) = 2 ^ T := by
  simp

/-- Splitting `T = a + b` random bits multiplies the point counts. -/
theorem card_finArrowBool_add (a b : ℕ) :
    Fintype.card (Fin (a + b) → Bool) = 2 ^ a * 2 ^ b := by
  rw [card_finArrowBool, pow_add]

/-- There are exactly `2 ^ (2 ^ n)` Boolean functions on `n` bits — the number of
    distinct `2 ^ n`-entry truth tables. The base fact for property density in
    natural-proofs arguments. -/
theorem card_boolFunc (n : ℕ) :
    Fintype.card ((Fin n → Bool) → Bool) = 2 ^ (2 ^ n) := by
  rw [Fintype.card_fun, Fintype.card_bool, card_finArrowBool]

/-- There are exactly `2 ^ (n * n)` directed graphs (adjacency matrices) on `n`
    vertices — the number of `n × n` Boolean matrices. The size datum behind
    adjacency-matrix encodings of graph languages such as CLIQUE. -/
theorem card_adjMatrix (n : ℕ) :
    Fintype.card (Fin n → Fin n → Bool) = 2 ^ (n * n) := by
  rw [Fintype.card_fun, card_finArrowBool, Fintype.card_fin, ← pow_mul]

/-- An `n`-vertex adjacency matrix biject with `n²`-bit strings by row-major
    serialization. Packaging this as an `Equiv` gives a canonical encode
    (`adjMatrixEquivBitVec`) and decode (`.symm`) that are inverse by
    construction — the codec behind graph-language encodings. -/
def adjMatrixEquivBitVec (n : ℕ) :
    (Fin n → Fin n → Bool) ≃ (Fin (n * n) → Bool) :=
  (Equiv.curry (Fin n) (Fin n) Bool).symm.trans
    (Equiv.arrowCongr finProdFinEquiv (Equiv.refl Bool))

/-! ### Block projection and concatenation -/

/-- A length-`a + b` random string is equivalently its length-`a` prefix paired
    with its length-`b` suffix. The forward map is the pair of projections; the
    inverse is concatenation. Packaging this as an `Equiv` proves the projection
    and concatenation maps are mutually inverse. -/
def blockEquiv (a b : ℕ) :
    (Fin (a + b) → Bool) ≃ (Fin a → Bool) × (Fin b → Bool) :=
  (Equiv.arrowCongr finSumFinEquiv (Equiv.refl Bool)).symm.trans
    (Equiv.sumArrowEquivProdArrow (Fin a) (Fin b) Bool)

/-- The prefix projection of a length-`a + b` random string. -/
def blockFst (a b : ℕ) (w : Fin (a + b) → Bool) : Fin a → Bool := (blockEquiv a b w).1

/-- The suffix projection of a length-`a + b` random string. -/
def blockSnd (a b : ℕ) (w : Fin (a + b) → Bool) : Fin b → Bool := (blockEquiv a b w).2

/-- Suffix projection is restriction along the canonical shifted inclusion. -/
@[simp] theorem blockSnd_apply (a b : ℕ) (w : Fin (a + b) → Bool) (i : Fin b) :
    blockSnd a b w i = w (Fin.natAdd a i) := by
  rfl

/-- Concatenate a length-`a` prefix and length-`b` suffix into one random string. -/
def blockAppend (a b : ℕ) (u : Fin a → Bool) (v : Fin b → Bool) : Fin (a + b) → Bool :=
  (blockEquiv a b).symm (u, v)

@[simp] theorem blockFst_append (a b : ℕ) (u : Fin a → Bool) (v : Fin b → Bool) :
    blockFst a b (blockAppend a b u v) = u := by
  simp [blockFst, blockAppend]

@[simp] theorem blockSnd_append (a b : ℕ) (u : Fin a → Bool) (v : Fin b → Bool) :
    blockSnd a b (blockAppend a b u v) = v := by
  simp [blockSnd, blockAppend]

@[simp] theorem blockAppend_fst_snd (a b : ℕ) (w : Fin (a + b) → Bool) :
    blockAppend a b (blockFst a b w) (blockSnd a b w) = w := by
  simp [blockAppend, blockFst, blockSnd]

/-- **Block independence (exact counting form).** The number of length-`a + b` seeds
    whose prefix satisfies `P` and suffix satisfies `Q` is the product of the two
    individual counts. Because `blockEquiv` is a bijection onto the product sample
    space, the joint event factors — the exact-count statement of independence across
    blocks, and the combinatorial heart of relating a repeated machine's acceptance to
    its single-run acceptance (amplification, roadmap N2/M2). -/
theorem card_filter_block {a b : ℕ}
    (P : (Fin a → Bool) → Prop) (Q : (Fin b → Bool) → Prop)
    [DecidablePred P] [DecidablePred Q] :
    (Finset.univ.filter
        (fun w : Fin (a + b) → Bool => P (blockFst a b w) ∧ Q (blockSnd a b w))).card
      = (Finset.univ.filter P).card * (Finset.univ.filter Q).card := by
  rw [← Finset.card_product]
  apply Finset.card_bij' (fun w _ => blockEquiv a b w) (fun p _ => (blockEquiv a b).symm p)
  · intro w hw
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hw
    exact Finset.mem_product.mpr
      ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hw.1⟩,
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, hw.2⟩⟩
  · intro p hp
    simp only [Finset.mem_product, Finset.mem_filter, Finset.mem_univ, true_and] at hp
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    simp only [blockFst, blockSnd, Equiv.apply_symm_apply]
    exact ⟨hp.1, hp.2⟩
  · intro w _; simp [Equiv.symm_apply_apply]
  · intro p _; simp [Equiv.apply_symm_apply]

/-! ### Finite union bound -/

/-- The finite union bound: the number of sample points satisfying *some*
    predicate `p i` for `i` in a finite index set `s` is at most the sum over `s`
    of the per-predicate counts. The workhorse behind failure-probability bounds
    over many bad events. -/
theorem card_filter_exists_le {ι α : Type*} [Fintype α] [DecidableEq α]
    (s : Finset ι) (p : ι → α → Prop) [∀ i, DecidablePred (p i)] :
    (Finset.univ.filter (fun x => ∃ i ∈ s, p i x)).card
      ≤ ∑ i ∈ s, (Finset.univ.filter (p i)).card := by
  refine le_trans (Finset.card_le_card ?_) Finset.card_biUnion_le
  intro x hx
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
  obtain ⟨i, hi, hpix⟩ := hx
  simp only [Finset.mem_biUnion, Finset.mem_filter, Finset.mem_univ, true_and]
  exact ⟨i, hi, hpix⟩

/-- **The probabilistic method: a perfect seed exists.** If the total number of
    "bad" seeds summed over all inputs is strictly less than the number of seeds,
    then some single seed is good for *every* input simultaneously. This is the
    machine-independent counting core of `BPP ⊆ P/poly` (hardwiring one random
    string that works for all `2ⁿ` inputs of a given length). -/
theorem exists_good_seed {S ι : Type*} [Fintype S] [DecidableEq S]
    (inputs : Finset ι) (bad : ι → Finset S)
    (h : ∑ i ∈ inputs, (bad i).card < Fintype.card S) :
    ∃ s : S, ∀ i ∈ inputs, s ∉ bad i := by
  have hcard : (inputs.biUnion bad).card < Fintype.card S :=
    lt_of_le_of_lt Finset.card_biUnion_le h
  have hne : inputs.biUnion bad ≠ Finset.univ := by
    intro heq
    rw [heq, Finset.card_univ] at hcard
    exact lt_irrefl _ hcard
  obtain ⟨s, -, hs⟩ :=
    Finset.exists_of_ssubset (Finset.ssubset_univ_iff.mpr hne)
  exact ⟨s, fun i hi hbad => hs (Finset.mem_biUnion.mpr ⟨i, hi, hbad⟩)⟩

/-! ### Majority -/

/-- The number of `true` positions of a Boolean vector. -/
def popCount {k : ℕ} (f : Fin k → Bool) : ℕ :=
  (Finset.univ.filter (fun i => f i = true)).card

private theorem popCount_succ {k : ℕ} (f : Fin (k + 1) → Bool) :
    popCount f = (if f 0 = true then 1 else 0) +
      popCount (fun i : Fin k => f i.succ) := by
  unfold popCount
  rw [Fin.card_filter_univ_succ']

/-- Batteries' fold-based Boolean count agrees with the finite-set support
count used by the randomized-counting layer. -/
theorem finCountP_eq_popCount {k : ℕ} (f : Fin k → Bool) :
    Fin.countP f = popCount f := by
  induction k with
  | zero => simp [popCount]
  | succ k ih =>
      rw [Fin.countP_succ, popCount_succ, ih]
      cases f 0 <;> simp

/-- Boolean-valued functions are equivalent to their true supports. -/
def boolFunEquivFinset (α : Type*) [Fintype α] [DecidableEq α] :
    (α → Bool) ≃ Finset α where
  toFun f := Finset.univ.filter (fun i => f i = true)
  invFun s i := decide (i ∈ s)
  left_inv f := by
    funext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    cases f i <;> simp
  right_inv s := by
    ext i
    simp

@[simp] theorem mem_boolFunEquivFinset {α : Type*} [Fintype α] [DecidableEq α]
    (f : α → Bool) (i : α) : i ∈ boolFunEquivFinset α f ↔ f i = true := by
  simp [boolFunEquivFinset]

@[simp] theorem boolFunEquivFinset_card {k : ℕ} (f : Fin k → Bool) :
    (boolFunEquivFinset (Fin k) f).card = popCount f := rfl

/-- Exactly `k.choose r` Boolean vectors of length `k` have `r` true entries. -/
theorem card_filter_popCount_eq (k r : ℕ) :
    (Finset.univ.filter (fun f : Fin k → Bool => popCount f = r)).card =
      k.choose r := by
  calc
    _ = (Finset.powersetCard r (Finset.univ : Finset (Fin k))).card := by
      apply Finset.card_bij'
          (fun f _ => boolFunEquivFinset (Fin k) f)
          (fun s _ => (boolFunEquivFinset (Fin k)).symm s)
      · intro f hf
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hf
        rw [Finset.mem_powersetCard]
        exact ⟨Finset.subset_univ _, by simpa using hf⟩
      · intro s hs
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        rw [← boolFunEquivFinset_card, Equiv.apply_symm_apply]
        exact (Finset.mem_powersetCard.mp hs).2
      · intro f _
        exact Equiv.symm_apply_apply _ _
      · intro s _
        exact Equiv.apply_symm_apply _ _
    _ = k.choose r := by simp

/-- The number of vectors whose `popCount` lies in a finite set is the
    corresponding sum of binomial coefficients. -/
theorem card_filter_popCount_mem (k : ℕ) (s : Finset ℕ) :
    (Finset.univ.filter (fun f : Fin k → Bool => popCount f ∈ s)).card =
      ∑ r ∈ s, k.choose r := by
  rw [← Finset.sum_card_fiberwise_eq_card_filter]
  apply Finset.sum_congr rfl
  intro r _
  exact card_filter_popCount_eq k r

/-! ### Weighted event counts across blocks -/

/-- A length-`k * T` seed is equivalently a sequence of `k` blocks of length `T`.
    The product equivalence fixes the row-major schedule consumed by repeated
    randomized computations. -/
def blocksEquiv (k T : ℕ) :
    (Fin (k * T) → Bool) ≃ (Fin k → Fin T → Bool) :=
  (Equiv.arrowCongr finProdFinEquiv (Equiv.refl Bool)).symm.trans
    (Equiv.curry (Fin k) (Fin T) Bool)

@[simp] theorem blocksEquiv_apply (k T : ℕ) (w : Fin (k * T) → Bool)
    (i : Fin k) (t : Fin T) :
    blocksEquiv k T w i t = w (finProdFinEquiv (i, t)) := by
  rfl

@[simp] theorem blocksEquiv_symm_apply (k T : ℕ) (f : Fin k → Fin T → Bool)
    (p : Fin (k * T)) :
    (blocksEquiv k T).symm f p =
      f (finProdFinEquiv.symm p).1 (finProdFinEquiv.symm p).2 := by
  rfl

/-! ### Fixed-time repetition schedules -/

/-- Split stride positions into simulation slots and administrative slots. -/
def repeatStrideIndexEquiv (k T : ℕ) :
    Fin (k * T) ⊕ Fin (k * (T + 2)) ≃ Fin (k * (2 * T + 2)) :=
  (Equiv.sumCongr finProdFinEquiv.symm finProdFinEquiv.symm).trans <|
    (Equiv.prodSumDistrib (Fin k) (Fin T) (Fin (T + 2))).symm |>.trans <|
    (Equiv.prodCongr (Equiv.refl (Fin k)) finSumFinEquiv).trans <|
    finProdFinEquiv |>.trans <|
    finCongr (by
      congr 1
      omega)

/-- Split a full stride seed into simulation and administrative choices. -/
def repeatStrideSeedEquiv (k T : ℕ) :
    (Fin (k * (2 * T + 2)) → Bool) ≃
      (Fin (k * T) → Bool) × (Fin (k * (T + 2)) → Bool) :=
  (Equiv.arrowCongr (repeatStrideIndexEquiv k T) (Equiv.refl Bool)).symm.trans
    (Equiv.sumArrowEquivProdArrow (Fin (k * T)) (Fin (k * (T + 2))) Bool)

/-- Project a repetition stride onto its `k * T` genuine simulation choices. -/
def repeatStrideRandomSeed (k T : ℕ)
    (w : Fin (k * (2 * T + 2)) → Bool) : Fin (k * T) → Bool :=
  (repeatStrideSeedEquiv k T w).1

private theorem repeatStrideIndexEquiv_sim (k T : ℕ) (i : Fin k) (t : Fin T) :
    repeatStrideIndexEquiv k T (Sum.inl (finProdFinEquiv (i, t))) =
      finProdFinEquiv (i, Fin.castLE (by omega : T ≤ 2 * T + 2) t) := by
  simp only [repeatStrideIndexEquiv, Equiv.trans_apply, Equiv.sumCongr_apply,
    Sum.map_inl, Equiv.symm_apply_apply, Equiv.prodSumDistrib_symm_apply_left,
    Equiv.prodCongr_apply, Prod.map_apply, Equiv.coe_refl, id_eq,
    finSumFinEquiv_apply_left, finCongr_apply]
  apply Fin.ext
  change t.val + (T + (T + 2)) * i.val = t.val + (2 * T + 2) * i.val
  rw [show T + (T + 2) = 2 * T + 2 by omega]

private theorem repeatStrideRandomSeed_apply (k T : ℕ)
    (w : Fin (k * (2 * T + 2)) → Bool) (i : Fin k) (t : Fin T) :
    repeatStrideRandomSeed k T w (finProdFinEquiv (i, t)) =
      w (finProdFinEquiv (i, Fin.castLE (by omega : T ≤ 2 * T + 2) t)) := by
  simp only [repeatStrideRandomSeed, repeatStrideSeedEquiv,
    Equiv.trans_apply, Equiv.sumArrowEquivProdArrow_apply_fst]
  change w (repeatStrideIndexEquiv k T (Sum.inl (finProdFinEquiv (i, t)))) = _
  rw [repeatStrideIndexEquiv_sim]

private theorem card_filter_repeatStrideRandomSeed (k T : ℕ)
    (P : (Fin (k * T) → Bool) → Prop) [DecidablePred P] :
    (Finset.univ.filter (fun w : Fin (k * (2 * T + 2)) → Bool =>
      P (repeatStrideRandomSeed k T w))).card =
      (Finset.univ.filter P).card * 2 ^ (k * (T + 2)) := by
  rw [← card_finArrowBool (k * (T + 2))]
  change _ = (Finset.univ.filter P).card *
    (Finset.univ : Finset (Fin (k * (T + 2)) → Bool)).card
  rw [← Finset.card_product]
  apply Finset.card_bij'
      (fun w _ => repeatStrideSeedEquiv k T w)
      (fun p _ => (repeatStrideSeedEquiv k T).symm p)
  · intro w hw
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hw ⊢
    refine Finset.mem_product.mpr ⟨?_, Finset.mem_univ _⟩
    simpa [repeatStrideRandomSeed] using hw
  · intro p hp
    simp only [Finset.mem_product, Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢
    simpa [repeatStrideRandomSeed] using hp.1
  · intro w _
    exact Equiv.symm_apply_apply _ _
  · intro p _
    exact Equiv.apply_symm_apply _ _

/-- Extract the `k * T` genuinely random simulation choices from a repetition
    trace of length `2 + k * (2 * T + 2)`. The first two choices and the last
    `T + 2` choices of every repetition stride are administrative and ignored. -/
def repeatRandomSeed (k T : ℕ)
    (w : Fin (2 + k * (2 * T + 2)) → Bool) : Fin (k * T) → Bool :=
  repeatStrideRandomSeed k T (blockSnd 2 (k * (2 * T + 2)) w)

/-- The compact seed's `(i,t)` entry is the choice at simulation offset `t` in
    repetition stride `i`, after the two initial setup choices. -/
theorem repeatRandomSeed_apply (k T : ℕ)
    (w : Fin (2 + k * (2 * T + 2)) → Bool) (i : Fin k) (t : Fin T) :
    repeatRandomSeed k T w (finProdFinEquiv (i, t)) =
      w (Fin.natAdd 2
        (finProdFinEquiv (i, Fin.castLE (by omega : T ≤ 2 * T + 2) t))) := by
  rw [repeatRandomSeed, repeatStrideRandomSeed_apply, blockSnd_apply]

private theorem card_repeatStrideRandomSeed_fiber (k T : ℕ)
    (seed : Fin (k * T) → Bool) :
    (Finset.univ.filter (fun w : Fin (k * (2 * T + 2)) → Bool =>
      repeatStrideRandomSeed k T w = seed)).card = 2 ^ (k * (T + 2)) := by
  calc
    _ = (Finset.univ.filter (fun w : Fin (k * T) → Bool => w = seed)).card *
        2 ^ (k * (T + 2)) :=
      card_filter_repeatStrideRandomSeed k T (fun w => w = seed)
    _ = 2 ^ (k * (T + 2)) := by
      have hsingleton :
          Finset.univ.filter (fun w : Fin (k * T) → Bool => w = seed) = {seed} := by
        ext w
        simp [eq_comm]
      rw [hsingleton]
      simp

/-- Every compact repetition seed has exactly one freely chosen assignment to
    each administrative slot in its full-seed fiber. -/
theorem card_repeatRandomSeed_fiber (k T : ℕ) (seed : Fin (k * T) → Bool) :
    (Finset.univ.filter (fun w : Fin (2 + k * (2 * T + 2)) → Bool =>
      repeatRandomSeed k T w = seed)).card = 2 ^ (2 + k * (T + 2)) := by
  have h := card_filter_block (a := 2) (b := k * (2 * T + 2))
    (fun _ : Fin 2 → Bool => True)
    (fun w => repeatStrideRandomSeed k T w = seed)
  rw [card_repeatStrideRandomSeed_fiber] at h
  simp [repeatRandomSeed, pow_add] at h ⊢
  convert h using 3
  rfl

/-- If a finite Boolean-seed projection has constant fibers, then every event
    that factors through the projection gains exactly that common fiber factor. -/
theorem card_filter_of_constant_fibers
    {total compact ignored : ℕ}
    (randomSeed : (Fin total → Bool) → (Fin compact → Bool))
    (Accept : (Fin total → Bool) → Prop)
    (Good : (Fin compact → Bool) → Prop)
    [DecidablePred Accept] [DecidablePred Good]
    (hfactor : ∀ w, Accept w ↔ Good (randomSeed w))
    (hfiber : ∀ seed,
      (Finset.univ.filter fun w => randomSeed w = seed).card = 2 ^ ignored) :
    (Finset.univ.filter Accept).card =
      (Finset.univ.filter Good).card * 2 ^ ignored := by
  let fullEvent := Finset.univ.filter Accept
  let compactEvent := Finset.univ.filter Good
  have hmaps : (fullEvent : Set (Fin total → Bool)).MapsTo randomSeed compactEvent := by
    intro w hw
    simp only [fullEvent, compactEvent, Finset.coe_filter, Finset.mem_univ,
      Set.mem_ofPred_eq, true_and] at hw ⊢
    exact (hfactor w).mp hw
  rw [Finset.card_eq_sum_card_fiberwise hmaps]
  calc
    _ = ∑ seed ∈ compactEvent,
        (Finset.univ.filter fun w => randomSeed w = seed).card := by
      apply Finset.sum_congr rfl
      intro seed hseed
      congr 1
      ext w
      simp only [fullEvent, compactEvent, Finset.mem_filter, Finset.mem_univ,
        true_and] at hseed ⊢
      constructor
      · rintro ⟨haccept, hseedw⟩
        exact hseedw
      · intro hseedw
        exact ⟨(hfactor w).mpr (hseedw ▸ hseed), hseedw⟩
    _ = ∑ _seed ∈ compactEvent, 2 ^ ignored := by
      apply Finset.sum_congr rfl
      intro seed _
      exact hfiber seed
    _ = compactEvent.card * 2 ^ ignored := by simp

/-- An event depending only on the compact repetition seed has its count
    multiplied by the number of ignored administrative choice assignments. -/
theorem card_filter_repeatRandomSeed (k T : ℕ)
    (P : (Fin (k * T) → Bool) → Prop) [DecidablePred P] :
    (Finset.univ.filter (fun w : Fin (2 + k * (2 * T + 2)) → Bool =>
      P (repeatRandomSeed k T w))).card =
      (Finset.univ.filter P).card * 2 ^ (2 + k * (T + 2)) := by
  exact card_filter_of_constant_fibers (repeatRandomSeed k T) _ P
    (fun _ => Iff.rfl) (card_repeatRandomSeed_fiber k T)

/-- The number of blocks of a long seed that lie in the event `E`. -/
def blockEventCount {k T : ℕ} (E : Finset (Fin T → Bool))
    (w : Fin (k * T) → Bool) : ℕ :=
  (Finset.univ.filter (fun i : Fin k => blocksEquiv k T w i ∈ E)).card

/-- Every block lies in exactly one of an event and its complement. -/
theorem blockEventCount_add_compl {k T : ℕ} (E : Finset (Fin T → Bool))
    (w : Fin (k * T) → Bool) :
    blockEventCount E w + blockEventCount Eᶜ w = k := by
  unfold blockEventCount
  rw [show Finset.univ.filter (fun i : Fin k => blocksEquiv k T w i ∈ Eᶜ) =
      Finset.univ.filter (fun i : Fin k => ¬blocksEquiv k T w i ∈ E) by
    ext i
    simp]
  rw [Finset.card_filter_add_card_filter_not]
  simp

private theorem card_filter_blockEventCount_eq_iff (k T j : ℕ)
    (E : Finset (Fin T → Bool)) :
    (Finset.univ.filter (fun w : Fin (k * T) → Bool => blockEventCount E w = j)).card =
      (Finset.univ.filter (fun f : Fin k → Fin T → Bool =>
        (Finset.univ.filter (fun i : Fin k => f i ∈ E)).card = j)).card := by
  apply Finset.card_bij'
      (fun w _ => blocksEquiv k T w)
      (fun f _ => (blocksEquiv k T).symm f)
  · intro w hw
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hw ⊢
    simpa only [blockEventCount] using hw
  · intro f hf
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hf ⊢
    simpa only [blockEventCount, Equiv.apply_symm_apply] using hf
  · intro w _
    exact Equiv.symm_apply_apply _ _
  · intro f _
    exact Equiv.apply_symm_apply _ _

-- The signature mirrors the family this belongs to; the argument is part of
-- that shape even where this member does not consult it.
@[nolint unusedArguments]
private def eventBits {k : ℕ} {α : Type*} [Fintype α] [DecidableEq α]
    (E : Finset α) (f : Fin k → α) : Fin k → Bool :=
  fun i => decide (f i ∈ E)

-- The signature mirrors the family this belongs to; the argument is part of
-- that shape even where this member does not consult it.
@[nolint unusedArguments]
private def eventCount {k : ℕ} {α : Type*} [Fintype α] [DecidableEq α]
    (E : Finset α) (f : Fin k → α) : ℕ :=
  (Finset.univ.filter (fun i : Fin k => f i ∈ E)).card

private theorem card_filter_eventBits_eq {k : ℕ} {α : Type*}
    [Fintype α] [DecidableEq α] (E : Finset α) (b : Fin k → Bool) :
    (Finset.univ.filter (fun f : Fin k → α => eventBits E f = b)).card =
      E.card ^ popCount b * (Fintype.card α - E.card) ^ (k - popCount b) := by
  have hset :
      Finset.univ.filter (fun f : Fin k → α => eventBits E f = b) =
        Fintype.piFinset (fun i => if b i = true then E else Eᶜ) := by
    ext f
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fintype.mem_piFinset]
    rw [funext_iff]
    constructor
    · intro h i
      specialize h i
      change decide (f i ∈ E) = b i at h
      cases hb : b i <;> simp only [hb, Bool.false_eq_true, ↓reduceIte,
        Finset.mem_compl, decide_eq_false_iff_not, decide_eq_true_eq] at h ⊢
      · exact h
      · exact h
    · intro h i
      specialize h i
      change decide (f i ∈ E) = b i
      cases hb : b i <;> simp only [hb, Bool.false_eq_true, ↓reduceIte,
        Finset.mem_compl, decide_eq_false_iff_not, decide_eq_true_eq] at h ⊢
      · exact h
      · exact h
  rw [hset, Fintype.card_piFinset]
  simp only [apply_ite]
  rw [Finset.prod_ite]
  simp only [Finset.prod_const, Finset.card_compl]
  change E.card ^ popCount b * (Fintype.card α - E.card) ^ _ = _
  congr 2
  have h := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset (Fin k))) (fun i => b i = true)
  have h' : popCount b +
      (Finset.univ.filter (fun i : Fin k => ¬b i = true)).card = k := by
    simpa only [popCount, Finset.card_univ, Fintype.card_fin] using h
  omega

private theorem card_eventCount_eq {k : ℕ} {α : Type*}
    [Fintype α] [DecidableEq α] (E : Finset α) (j : ℕ) :
    (Finset.univ.filter (fun f : Fin k → α => eventCount E f = j)).card =
      k.choose j * E.card ^ j * (Fintype.card α - E.card) ^ (k - j) := by
  have hfilter :
      Finset.univ.filter (fun f : Fin k → α => eventCount E f = j) =
        Finset.univ.filter (fun f : Fin k → α => eventBits E f ∈
          Finset.univ.filter (fun b : Fin k → Bool => popCount b = j)) := by
    apply Finset.filter_congr
    intro f _
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    simp only [eventCount, popCount, eventBits, decide_eq_true_eq]
  rw [hfilter, ← Finset.sum_card_fiberwise_eq_card_filter
    (Finset.univ : Finset (Fin k → α))
    (Finset.univ.filter (fun b : Fin k → Bool => popCount b = j)) (eventBits E)]
  calc
    _ = ∑ b ∈ Finset.univ.filter (fun b : Fin k → Bool => popCount b = j),
        E.card ^ popCount b * (Fintype.card α - E.card) ^ (k - popCount b) := by
      apply Finset.sum_congr rfl
      intro b _
      exact card_filter_eventBits_eq E b
    _ = (Finset.univ.filter (fun b : Fin k → Bool => popCount b = j)).card *
        (E.card ^ j * (Fintype.card α - E.card) ^ (k - j)) := by
      apply Finset.sum_const_nat
      intro b hb
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hb
      rw [hb]
    _ = k.choose j * E.card ^ j * (Fintype.card α - E.card) ^ (k - j) := by
      rw [card_filter_popCount_eq]
      simp only [Nat.mul_assoc]

/-- Number of positions in a finite tuple whose value belongs to `E`. -/
def tupleEventCount {k : ℕ} {α : Type*} [DecidableEq α]
    (E : Finset α) (f : Fin k → α) : ℕ :=
  (Finset.univ.filter (fun i : Fin k => f i ∈ E)).card

/-- **Generic weighted binomial count.** Exactly the stated number of
`k`-tuples over `α` have `j` positions in `E`. -/
theorem card_tupleEventCount_eq {k : ℕ} {α : Type*}
    [Fintype α] [DecidableEq α] (E : Finset α) (j : ℕ) :
    (Finset.univ.filter
      (fun f : Fin k → α => tupleEventCount E f = j)).card =
        k.choose j * E.card ^ j *
          (Fintype.card α - E.card) ^ (k - j) := by
  exact card_eventCount_eq (k := k) E j

/-- The number of tuples whose event count lies in a finite set is the
corresponding weighted binomial sum. -/
theorem card_tupleEventCount_mem {k : ℕ} {α : Type*}
    [Fintype α] [DecidableEq α] (E : Finset α) (counts : Finset ℕ) :
    (Finset.univ.filter
      (fun f : Fin k → α => tupleEventCount E f ∈ counts)).card =
        ∑ j ∈ counts,
          k.choose j * E.card ^ j *
            (Fintype.card α - E.card) ^ (k - j) := by
  rw [← Finset.sum_card_fiberwise_eq_card_filter]
  apply Finset.sum_congr rfl
  intro j _
  exact card_tupleEventCount_eq E j

/-- **Weighted binomial count in the machine seed space.** Exactly the stated
    binomial number of long seeds have `j` blocks in `E`; the two weights are the
    counts of successful and unsuccessful `T`-bit blocks. -/
theorem card_blockEventCount_eq {T : ℕ} (E : Finset (Fin T → Bool)) (k j : ℕ) :
    (Finset.univ.filter (fun w : Fin (k * T) → Bool => blockEventCount E w = j)).card =
      k.choose j * E.card ^ j * (2 ^ T - E.card) ^ (k - j) := by
  rw [card_filter_blockEventCount_eq_iff]
  change (Finset.univ.filter (fun f : Fin k → Fin T → Bool => eventCount E f = j)).card = _
  rw [card_eventCount_eq, card_finArrowBool]

/-- Strict majority of the blocks of a long seed lying in the event `E`. -/
def blockMajority {k T : ℕ} (E : Finset (Fin T → Bool))
    (w : Fin (k * T) → Bool) : Bool :=
  decide (2 * blockEventCount E w > k)

/-- At an odd number of blocks, complementing the event flips the strict
majority verdict. -/
theorem blockMajority_compl_of_odd {k T : ℕ} (hk : Odd k)
    (E : Finset (Fin T → Bool)) (w : Fin (k * T) → Bool) :
    blockMajority Eᶜ w = !(blockMajority E w) := by
  obtain ⟨r, rfl⟩ := hk
  have hcount := blockEventCount_add_compl E w
  simp only [blockMajority]
  by_cases h : 2 * blockEventCount E w > 2 * r + 1
  · have hc : ¬2 * blockEventCount Eᶜ w > 2 * r + 1 := by omega
    rw [decide_eq_false hc, decide_eq_true h, Bool.not_true]
  · have hc : 2 * blockEventCount Eᶜ w > 2 * r + 1 := by omega
    rw [decide_eq_true hc, decide_eq_false h, Bool.not_false]

theorem blockMajority_eq_false_iff {k T : ℕ} (E : Finset (Fin T → Bool))
    (w : Fin (k * T) → Bool) :
    blockMajority E w = false ↔ blockEventCount E w ≤ k / 2 := by
  simp only [blockMajority, decide_eq_false_iff_not]
  omega

theorem blockMajority_eq_false_iff_mem_range {T r : ℕ}
    (E : Finset (Fin T → Bool)) (w : Fin ((2 * r + 1) * T) → Bool) :
    blockMajority E w = false ↔ blockEventCount E w ∈ Finset.range (r + 1) := by
  rw [blockMajority_eq_false_iff]
  simp only [Finset.mem_range]
  omega

/-- **Exact odd-majority failure count.** For `2r + 1` independent `T`-bit
    blocks, failure means at most `r` blocks lie in `E`; each summand is the
    corresponding weighted binomial fiber. -/
theorem card_blockMajority_eq_false (T r : ℕ) (E : Finset (Fin T → Bool)) :
    (Finset.univ.filter (fun w : Fin ((2 * r + 1) * T) → Bool =>
      blockMajority E w = false)).card =
      ∑ j ∈ Finset.range (r + 1),
        (2 * r + 1).choose j * E.card ^ j *
          (2 ^ T - E.card) ^ (2 * r + 1 - j) := by
  simp only [blockMajority_eq_false_iff_mem_range]
  rw [← Finset.sum_card_fiberwise_eq_card_filter]
  apply Finset.sum_congr rfl
  intro j _
  exact card_blockEventCount_eq E (2 * r + 1) j

/-- The strict majority vote of a Boolean vector: `true` iff more than half the
    positions are `true`. -/
def majority {k : ℕ} (f : Fin k → Bool) : Bool := decide (2 * popCount f > k)

/-- `popCount` is bounded by the length. -/
theorem popCount_le {k : ℕ} (f : Fin k → Bool) : popCount f ≤ k := by
  refine le_trans (Finset.card_filter_le _ _) ?_
  simp

theorem majority_eq_true_iff {k : ℕ} (f : Fin k → Bool) :
    majority f = true ↔ k / 2 < popCount f := by
  simp only [majority, decide_eq_true_eq]
  omega

theorem majority_eq_false_iff {k : ℕ} (f : Fin k → Bool) :
    majority f = false ↔ popCount f ≤ k / 2 := by
  simp only [majority, decide_eq_false_iff_not]
  omega

theorem majority_eq_true_iff_mem_Icc {k : ℕ} (f : Fin k → Bool) :
    majority f = true ↔ popCount f ∈ Finset.Icc (k / 2 + 1) k := by
  rw [majority_eq_true_iff]
  simp only [Finset.mem_Icc]
  exact ⟨fun h => ⟨by omega, popCount_le f⟩, fun h => by omega⟩

theorem majority_eq_false_iff_mem_range {k : ℕ} (f : Fin k → Bool) :
    majority f = false ↔ popCount f ∈ Finset.range (k / 2 + 1) := by
  rw [majority_eq_false_iff]
  simp only [Finset.mem_range]
  omega

/-- The exact binomial upper-tail count for strict-majority success. -/
theorem card_majority_eq_true (k : ℕ) :
    (Finset.univ.filter (fun f : Fin k → Bool => majority f = true)).card =
      ∑ r ∈ Finset.Icc (k / 2 + 1) k, k.choose r := by
  simpa only [majority_eq_true_iff_mem_Icc] using
    card_filter_popCount_mem k (Finset.Icc (k / 2 + 1) k)

/-- The exact binomial lower-tail count for strict-majority failure, including
    ties when the vector length is even. -/
theorem card_majority_eq_false (k : ℕ) :
    (Finset.univ.filter (fun f : Fin k → Bool => majority f = false)).card =
      ∑ r ∈ Finset.range (k / 2 + 1), k.choose r := by
  simpa only [majority_eq_false_iff_mem_range] using
    card_filter_popCount_mem k (Finset.range (k / 2 + 1))

/-- Failure phrased as not returning `true` has the same exact lower-tail count. -/
theorem card_majority_ne_true (k : ℕ) :
    (Finset.univ.filter (fun f : Fin k → Bool => majority f ≠ true)).card =
      ∑ r ∈ Finset.range (k / 2 + 1), k.choose r := by
  rw [show Finset.univ.filter (fun f : Fin k → Bool => majority f ≠ true) =
      Finset.univ.filter (fun f : Fin k → Bool => majority f = false) by
    apply Finset.filter_congr
    intro f _
    cases majority f <;> simp]
  exact card_majority_eq_false k

/-- A position is either `true` or `true`-after-negation, never both: the two
    `popCount`s sum to the length. -/
theorem popCount_add_popCount_not {k : ℕ} (f : Fin k → Bool) :
    popCount f + popCount (fun i => !f i) = k := by
  have hcongr : Finset.univ.filter (fun i : Fin k => (!f i) = true)
      = Finset.univ.filter (fun i : Fin k => ¬ (f i = true)) := by
    apply Finset.filter_congr
    intro i _
    cases f i <;> simp
  simp only [popCount]
  rw [hcongr, Finset.card_filter_add_card_filter_not]
  simp

/-- `popCount` of the pointwise negation is the complementary count. -/
theorem popCount_not {k : ℕ} (f : Fin k → Bool) :
    popCount (fun i => !f i) = k - popCount f := by
  have h := popCount_add_popCount_not f
  omega

/-- **Antisymmetry of majority under negation at odd length.** When the length
    `k` is odd there are no ties, so negating every bit flips the majority vote. -/
theorem majority_not_of_odd {k : ℕ} (hk : Odd k) (f : Fin k → Bool) :
    majority (fun i => !f i) = !(majority f) := by
  obtain ⟨m, hm⟩ := hk
  have hle := popCount_le f
  simp only [majority, popCount_not]
  by_cases h : 2 * popCount f > k
  · have h1 : ¬ (2 * (k - popCount f) > k) := by omega
    rw [decide_eq_false h1, decide_eq_true h, Bool.not_true]
  · have h1 : 2 * (k - popCount f) > k := by omega
    rw [decide_eq_true h1, decide_eq_false h, Bool.not_false]

end Complexity
