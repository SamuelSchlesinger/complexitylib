/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/
module
public import Complexitylib.Classes.PCP.Internal.WalkDart
public import Complexitylib.Classes.PCP.Internal.Mixing
public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Algebra.Ring.GeomSum

/-!
# Counting a dart set by tail and by head

The bookkeeping that turns `WalkDart.sum_two_darts_fixed` — the operator form of
"the walk crosses `F` at step `k` and again at step `l`" — into something
`Mixing.mixing_sq` can estimate.

Two counts of a dart set are needed. `dartCount F v` counts the `F`-darts
*leaving* `v`, and `headCount F z` counts those *arriving* at `z`. Both sum to
`F.card`, and each is at most the degree. The first is the function whose
`stepIter` the second crossing sees; the second is the measure the first
crossing leaves behind.

## Main definitions

- `RegGraph.dartCount`, `RegGraph.headCount`

## Main results

- `RegGraph.sum_dartCount`, `RegGraph.sum_headCount` — both count `F`
- `RegGraph.dartCount_le`, `RegGraph.headCount_le` — at most the degree
- `RegGraph.sum_indicator_nbr` — a sum over `F`-darts of a function of the head
  is a sum over vertices weighted by `headCount`
- `RegGraph.step_sum`, `RegGraph.stepIter_sum` — the walk operator is linear
  over finite sums
- `RegGraph.sum_indicator_dartCount`, `RegGraph.sum_indicator_mul` — indicator
  sums collapse to the two counts
- `RegGraph.sum_two_crossings` — two crossings of `F`, in operator form
- `RegGraph.sum_headCount_stepIter_le` — the correlation bound: two crossings
  `t` steps apart are independent up to `lam ^ t * deg * |F|`
- `geom_sum_le_inv`, `sum_pairs_geom_le` — summing that over all position pairs
  costs only `m / (1 - lam)`
- `RegGraph.sum_pairs_le` — the second moment: all pairs of crossings together
- `card_sq_eq_add_two_mul_pairs` — a squared count is the count plus twice the
  ordered pairs
- `card_filter_eq_sum_prod`, `sum_pairs_eq_sum_Ico` — index bookkeeping for the
  second moment
-/

@[expose] public section

namespace Complexity

/-! ### Geometric sums -/

/-- A truncated geometric series is bounded by its limit. -/
theorem geom_sum_le_inv {lam : ℝ} (h0 : 0 ≤ lam) (h1 : lam < 1) (n : ℕ) :
    ∑ i ∈ Finset.range n, lam ^ i ≤ 1 / (1 - lam) := by
  have hpos : (0 : ℝ) < 1 - lam := by linarith
  have hmul : (∑ i ∈ Finset.range n, lam ^ i) * (lam - 1) = lam ^ n - 1 := geom_sum_mul lam n
  have hmul' : (∑ i ∈ Finset.range n, lam ^ i) * (1 - lam) = 1 - lam ^ n := by
    nlinarith [hmul]
  have hpow : (0 : ℝ) ≤ lam ^ n := by positivity
  rw [le_div_iff₀ hpos]
  linarith [hmul']

/-- Summed over all pairs of positions, the separation weights `lam ^ (l-k-1)`
contribute at most `m / (1 - lam)`. -/
theorem sum_pairs_geom_le {lam : ℝ} (h0 : 0 ≤ lam) (h1 : lam < 1) (m : ℕ) :
    ∑ k ∈ Finset.range m, ∑ l ∈ Finset.Ico (k + 1) m, lam ^ (l - k - 1)
      ≤ (m : ℝ) * (1 / (1 - lam)) := by
  have hinner : ∀ k ∈ Finset.range m,
      ∑ l ∈ Finset.Ico (k + 1) m, lam ^ (l - k - 1) ≤ 1 / (1 - lam) := by
    intro k _
    have hre : ∑ l ∈ Finset.Ico (k + 1) m, lam ^ (l - k - 1)
        = ∑ i ∈ Finset.range (m - (k + 1)), lam ^ i := by
      rw [Finset.sum_Ico_eq_sum_range]
      refine Finset.sum_congr rfl fun i _ => ?_
      congr 1
      omega
    rw [hre]
    exact geom_sum_le_inv h0 h1 _
  calc ∑ k ∈ Finset.range m, ∑ l ∈ Finset.Ico (k + 1) m, lam ^ (l - k - 1)
      ≤ ∑ _k ∈ Finset.range m, (1 / (1 - lam)) := Finset.sum_le_sum hinner
    _ = (m : ℝ) * (1 / (1 - lam)) := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]

/-! ### Squares and ordered pairs -/

/-- The square of a count is the count plus twice the ordered pairs. This is how
`∑ N ^ 2` in the second-moment method becomes a sum over *pairs* of crossings,
which is what the correlation bound estimates. -/
theorem card_sq_eq_add_two_mul_pairs {ι : Type*} [LinearOrder ι] [DecidableEq ι]
    (S : Finset ι) :
    S.card ^ 2 = S.card + 2 * ((S ×ˢ S).filter fun p => p.1 < p.2).card := by
  classical
  have hswap : ((S ×ˢ S).filter fun p => p.1 < p.2).card
      = ((S ×ˢ S).filter fun p => p.2 < p.1).card := by
    refine Finset.card_bij (fun p _ => (p.2, p.1)) ?_ ?_ ?_
    · intro p hp
      simp only [Finset.mem_filter, Finset.mem_product] at hp ⊢
      exact ⟨⟨hp.1.2, hp.1.1⟩, hp.2⟩
    · intro p _ p' _ hpp
      have h1 : p.2 = p'.2 := congrArg Prod.fst hpp
      have h2 : p.1 = p'.1 := congrArg Prod.snd hpp
      exact Prod.ext h2 h1
    · intro p hp
      simp only [Finset.mem_filter, Finset.mem_product] at hp
      refine ⟨(p.2, p.1), ?_, rfl⟩
      simp only [Finset.mem_filter, Finset.mem_product]
      exact ⟨⟨hp.1.2, hp.1.1⟩, hp.2⟩
  have hdiag : ((S ×ˢ S).filter fun p => p.1 = p.2).card = S.card := by
    refine Finset.card_bij (fun p _ => p.1) ?_ ?_ ?_
    · intro p hp
      simp only [Finset.mem_filter, Finset.mem_product] at hp
      exact hp.1.1
    · intro p hp p' hp' hpp
      simp only [Finset.mem_filter, Finset.mem_product] at hp hp'
      refine Prod.ext hpp ?_
      rw [← hp.2, ← hp'.2]
      exact hpp
    · intro a ha
      refine ⟨(a, a), ?_, rfl⟩
      simp [ha]
  have hnotlt : ((S ×ˢ S).filter fun p => ¬ p.1 < p.2).card
      = ((S ×ˢ S).filter fun p => p.1 = p.2).card
        + ((S ×ˢ S).filter fun p => p.2 < p.1).card := by
    rw [← Finset.card_union_of_disjoint]
    · congr 1
      ext p
      simp only [Finset.mem_filter, Finset.mem_union, Finset.mem_product]
      constructor
      · rintro ⟨hmem, hlt⟩
        rcases lt_trichotomy p.1 p.2 with h | h | h
        · exact absurd h hlt
        · exact Or.inl ⟨hmem, h⟩
        · exact Or.inr ⟨hmem, h⟩
      · rintro (⟨hmem, heq⟩ | ⟨hmem, hgt⟩)
        · exact ⟨hmem, by rw [heq]; exact lt_irrefl _⟩
        · exact ⟨hmem, not_lt_of_gt hgt⟩
    · refine Finset.disjoint_left.mpr fun p hp hp' => ?_
      simp only [Finset.mem_filter] at hp hp'
      rw [hp.2] at hp'
      exact absurd hp'.2 (lt_irrefl _)
  have htotal : (S ×ˢ S).card
      = ((S ×ˢ S).filter fun p => p.1 < p.2).card
        + ((S ×ˢ S).filter fun p => ¬ p.1 < p.2).card :=
    (Finset.card_filter_add_card_filter_not _).symm
  rw [Finset.card_product] at htotal
  rw [sq]
  omega

/-- A count of a conjunction is a sum of products of indicators. -/
theorem card_filter_eq_sum_prod {ι : Type*} [Fintype ι] (P Q : ι → Prop)
    [DecidablePred P] [DecidablePred Q] :
    (((Finset.univ.filter fun i => P i ∧ Q i).card : ℕ) : ℝ)
      = ∑ i, (if P i then (1 : ℝ) else 0) * (if Q i then (1 : ℝ) else 0) := by
  classical
  rw [Finset.card_filter]
  push_cast
  refine Finset.sum_congr rfl fun i _ => ?_
  by_cases hp : P i <;> by_cases hq : Q i <;> simp [hp, hq]

/-- A sum over ordered pairs below `T`, as an iterated sum. -/
theorem sum_pairs_eq_sum_Ico {M : Type*} [AddCommMonoid M] (T : ℕ) (f : ℕ × ℕ → M) :
    ∑ p ∈ ((Finset.range T) ×ˢ (Finset.range T)).filter fun p => p.1 < p.2, f p
      = ∑ k ∈ Finset.range T, ∑ l ∈ Finset.Ico (k + 1) T, f (k, l) := by
  classical
  rw [Finset.sum_filter, Finset.sum_product]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [← Finset.sum_filter]
  congr 1
  ext l
  simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]
  omega

namespace RegGraph

variable (G : RegGraph)

/-! ### Linearity of the walk operator -/

theorem step_sum {ι : Type*} (s : Finset ι) (f : ι → G.V → ℝ) (v : G.V) :
    G.step (fun w => ∑ i ∈ s, f i w) v = ∑ i ∈ s, G.step (f i) v := by
  simp only [step]
  rw [← Finset.sum_div]
  congr 1
  exact Finset.sum_comm

theorem stepIter_sum {ι : Type*} (s : Finset ι) (f : ι → G.V → ℝ) (t : ℕ) (v : G.V) :
    G.stepIter t (fun w => ∑ i ∈ s, f i w) v = ∑ i ∈ s, G.stepIter t (f i) v := by
  induction t generalizing v with
  | zero => simp
  | succ t ih =>
      rw [stepIter_succ]
      have hfun : G.stepIter t (fun w => ∑ i ∈ s, f i w)
          = fun w => ∑ i ∈ s, G.stepIter t (f i) w := by
        funext w
        exact ih w
      rw [hfun, G.step_sum]
      exact Finset.sum_congr rfl fun i _ => by rw [← stepIter_succ]

/-- How many darts of `F` leave `v`. -/
def dartCount (F : Finset (G.V × G.D)) (v : G.V) : ℕ :=
  (F.filter fun p => p.1 = v).card

/-- How many darts of `F` arrive at `z`. -/
def headCount (F : Finset (G.V × G.D)) (z : G.V) : ℕ :=
  (F.filter fun p => G.nbr p.1 p.2 = z).card

theorem sum_dartCount (F : Finset (G.V × G.D)) :
    ∑ v : G.V, G.dartCount F v = F.card :=
  (Finset.card_eq_sum_card_fiberwise fun p _ => Finset.mem_univ p.1).symm

theorem sum_headCount (F : Finset (G.V × G.D)) :
    ∑ z : G.V, G.headCount F z = F.card :=
  (Finset.card_eq_sum_card_fiberwise fun p _ => Finset.mem_univ (G.nbr p.1 p.2)).symm

theorem dartCount_le (F : Finset (G.V × G.D)) (v : G.V) : G.dartCount F v ≤ G.deg := by
  classical
  have hsub : (F.filter fun p => p.1 = v) ⊆ ({v} : Finset G.V) ×ˢ (Finset.univ : Finset G.D) := by
    intro p hp
    simp only [Finset.mem_filter] at hp
    simp only [Finset.mem_product, Finset.mem_singleton, Finset.mem_univ, and_true]
    exact hp.2
  calc G.dartCount F v ≤ (({v} : Finset G.V) ×ˢ (Finset.univ : Finset G.D)).card :=
        Finset.card_le_card hsub
    _ = G.deg := by
        rw [Finset.card_product, Finset.card_singleton, one_mul, Finset.card_univ]
        rfl

/-- The darts arriving at `z` correspond, under reversal, to the darts leaving
`z`, so there are at most `deg` of them. -/
theorem headCount_le (F : Finset (G.V × G.D)) (z : G.V) : G.headCount F z ≤ G.deg := by
  classical
  have hinj : Set.InjOn (fun p : G.V × G.D => (G.rot p).2)
      (F.filter fun p => G.nbr p.1 p.2 = z) := by
    intro p hp p' hp' hval
    simp only [Finset.coe_filter, Set.mem_ofPred_eq] at hp hp'
    have hp1 : (G.rot p).1 = z := hp.2
    have hp'1 : (G.rot p').1 = z := hp'.2
    have hpair : G.rot p = G.rot p' := Prod.ext (hp1.trans hp'1.symm) hval
    have := congrArg G.rot hpair
    rwa [G.rot_involutive p, G.rot_involutive p'] at this
  calc G.headCount F z
      ≤ (Finset.univ : Finset G.D).card := by
        rw [headCount]
        exact Finset.card_le_card_of_injOn _ (fun p _ => Finset.mem_univ _) hinj
    _ = G.deg := by rw [Finset.card_univ]; rfl

/-- Summing a function of a dart's head over `F` is summing over vertices with
the multiplicity `headCount`. -/
theorem sum_indicator_nbr (F : Finset (G.V × G.D)) (h : G.V → ℝ) :
    ∑ p ∈ F, h (G.nbr p.1 p.2) = ∑ z : G.V, (G.headCount F z : ℝ) * h z := by
  classical
  rw [← Finset.sum_fiberwise_of_maps_to (fun p (_ : p ∈ F) => Finset.mem_univ (G.nbr p.1 p.2))
    (fun p => h (G.nbr p.1 p.2))]
  refine Finset.sum_congr rfl fun z _ => ?_
  have hconst : ∀ p ∈ F.filter fun p => G.nbr p.1 p.2 = z, h (G.nbr p.1 p.2) = h z := by
    intro p hp
    simp only [Finset.mem_filter] at hp
    rw [hp.2]
  rw [Finset.sum_congr rfl hconst, Finset.sum_const, nsmul_eq_mul]
  rfl

/-! ### Indicator sums -/

/-- Summing the `F`-indicator over the labels at a fixed vertex counts the
`F`-darts there. -/
theorem sum_indicator_dartCount (F : Finset (G.V × G.D)) (z : G.V) :
    ∑ b : G.D, (if (z, b) ∈ F then (1 : ℝ) else 0) = (G.dartCount F z : ℝ) := by
  classical
  rw [Finset.sum_boole]
  congr 1
  rw [dartCount]
  refine Finset.card_bij (fun b _ => (z, b)) ?_ ?_ ?_
  · intro b hb
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hb ⊢
    simpa using hb
  · intro b _ b' _ hbb
    exact (Prod.ext_iff.mp hbb).2
  · rintro ⟨y, b⟩ hp
    simp only [Finset.mem_filter] at hp
    obtain ⟨hmem, hy⟩ := hp
    subst hy
    exact ⟨b, by simpa using hmem, rfl⟩

/-- Summing an `F`-weighted function of a dart's head over all darts is summing
it over `F`. -/
theorem sum_indicator_mul (F : Finset (G.V × G.D)) (φ : G.V → ℝ) :
    ∑ a : G.D, ∑ y : G.V, (if (y, a) ∈ F then (1 : ℝ) else 0) * φ (G.nbr y a)
      = ∑ p ∈ F, φ (G.nbr p.1 p.2) := by
  classical
  have hswap : ∑ a : G.D, ∑ y : G.V, (if (y, a) ∈ F then (1 : ℝ) else 0) * φ (G.nbr y a)
      = ∑ p : G.V × G.D, (if p ∈ F then (1 : ℝ) else 0) * φ (G.nbr p.1 p.2) := by
    rw [Fintype.sum_prod_type]
    exact Finset.sum_comm
  rw [hswap]
  have hite : ∀ p : G.V × G.D, (if p ∈ F then (1 : ℝ) else 0) * φ (G.nbr p.1 p.2)
      = if p ∈ F then φ (G.nbr p.1 p.2) else 0 := by
    intro p
    split <;> simp
  rw [Finset.sum_congr rfl fun p _ => hite p, ← Finset.sum_filter]
  congr 1
  simp

/-! ### The two-crossing identity -/

/-- **Two crossings, in operator form.** Summed over all starts and all label
sequences, the walks that cross `F` at step `k` and again at step `l` are counted
by the walk operator applied to the dart counts: the first crossing leaves the
measure `headCount`, and the second is seen through `l - k - 1` steps of the
walk. `Mixing.mixing_sq` estimates exactly this expression. -/
theorem sum_two_crossings (F : Finset (G.V × G.D)) {k l m : ℕ} (hkl : k < l) (hl : l < m) :
    (∑ x : G.V, ∑ r : Fin m → G.D,
        (if (G.walkAt m x r k, r ⟨k, by omega⟩) ∈ F then (1 : ℝ) else 0)
          * (if (G.walkAt m x r l, r ⟨l, by omega⟩) ∈ F then (1 : ℝ) else 0))
      = (G.deg : ℝ) ^ (m - 2)
        * ∑ z : G.V, (G.headCount F z : ℝ)
          * G.stepIter (l - k - 1) (fun w => (G.dartCount F w : ℝ)) z := by
  classical
  set h : G.V → G.D → ℝ := fun y a => if (y, a) ∈ F then (1 : ℝ) else 0 with hh
  have hx : ∀ x : G.V, (∑ r : Fin m → G.D, h (G.walkAt m x r k) (r ⟨k, by omega⟩)
        * h (G.walkAt m x r l) (r ⟨l, by omega⟩))
      = (G.deg : ℝ) ^ (m - 2) * ∑ a : G.D, ∑ b : G.D,
          G.stepIter k (fun y => h y a
            * G.stepIter (l - k - 1) (fun z => h z b) (G.nbr y a)) x :=
    fun x => G.sum_two_darts_fixed h h k l m hkl hl x
  rw [Finset.sum_congr rfl fun x _ => hx x, ← Finset.mul_sum]
  congr 1
  have hswap : ∑ x : G.V, ∑ a : G.D, ∑ b : G.D,
        G.stepIter k (fun y => h y a
          * G.stepIter (l - k - 1) (fun z => h z b) (G.nbr y a)) x
      = ∑ a : G.D, ∑ b : G.D, ∑ x : G.V,
        G.stepIter k (fun y => h y a
          * G.stepIter (l - k - 1) (fun z => h z b) (G.nbr y a)) x := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun a _ => Finset.sum_comm
  rw [hswap]
  have hcollapse : ∀ a : G.D, ∀ b : G.D, ∑ x : G.V,
        G.stepIter k (fun y => h y a
          * G.stepIter (l - k - 1) (fun z => h z b) (G.nbr y a)) x
      = ∑ y : G.V, h y a * G.stepIter (l - k - 1) (fun z => h z b) (G.nbr y a) := by
    intro a b
    exact G.sum_stepIter k _
  rw [Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => hcollapse a b]
  have hby : ∀ a : G.D, ∑ b : G.D, ∑ y : G.V,
        h y a * G.stepIter (l - k - 1) (fun z => h z b) (G.nbr y a)
      = ∑ y : G.V, h y a
        * G.stepIter (l - k - 1) (fun w => (G.dartCount F w : ℝ)) (G.nbr y a) := by
    intro a
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [← Finset.mul_sum]
    congr 1
    rw [← G.stepIter_sum Finset.univ (fun b z => h z b) (l - k - 1) (G.nbr y a)]
    congr 1
    funext z
    exact G.sum_indicator_dartCount F z
  rw [Finset.sum_congr rfl fun a _ => hby a]
  rw [G.sum_indicator_mul F
    (fun w => G.stepIter (l - k - 1) (fun w' => (G.dartCount F w' : ℝ)) w)]
  exact G.sum_indicator_nbr F _

/-! ### Bounding the correlation -/

/-- The variance of a dart count is at most `deg * |F|`, since no vertex carries
more than `deg` darts of `F`. -/
theorem sum_sq_headCount_le (F : Finset (G.V × G.D)) :
    ∑ z : G.V, ((G.headCount F z : ℝ)) ^ 2 ≤ (G.deg : ℝ) * (F.card : ℝ) := by
  have hterm : ∀ z : G.V, ((G.headCount F z : ℝ)) ^ 2
      ≤ (G.deg : ℝ) * (G.headCount F z : ℝ) := by
    intro z
    have h := G.headCount_le F z
    have hR : (G.headCount F z : ℝ) ≤ (G.deg : ℝ) := by exact_mod_cast h
    nlinarith
  calc ∑ z : G.V, ((G.headCount F z : ℝ)) ^ 2
      ≤ ∑ z : G.V, (G.deg : ℝ) * (G.headCount F z : ℝ) := Finset.sum_le_sum fun z _ => hterm z
    _ = (G.deg : ℝ) * ∑ z : G.V, (G.headCount F z : ℝ) := by rw [Finset.mul_sum]
    _ = (G.deg : ℝ) * (F.card : ℝ) := by
        congr 1
        rw [← Nat.cast_sum, G.sum_headCount F]

theorem sum_sq_dartCount_le (F : Finset (G.V × G.D)) :
    ∑ v : G.V, ((G.dartCount F v : ℝ)) ^ 2 ≤ (G.deg : ℝ) * (F.card : ℝ) := by
  have hterm : ∀ v : G.V, ((G.dartCount F v : ℝ)) ^ 2
      ≤ (G.deg : ℝ) * (G.dartCount F v : ℝ) := by
    intro v
    have h := G.dartCount_le F v
    have hR : (G.dartCount F v : ℝ) ≤ (G.deg : ℝ) := by exact_mod_cast h
    nlinarith
  calc ∑ v : G.V, ((G.dartCount F v : ℝ)) ^ 2
      ≤ ∑ v : G.V, (G.deg : ℝ) * (G.dartCount F v : ℝ) := Finset.sum_le_sum fun v _ => hterm v
    _ = (G.deg : ℝ) * ∑ v : G.V, (G.dartCount F v : ℝ) := by rw [Finset.mul_sum]
    _ = (G.deg : ℝ) * (F.card : ℝ) := by
        congr 1
        rw [← Nat.cast_sum, G.sum_dartCount F]

/-- **The correlation bound.** On a graph with spectral bound `lam`, two
crossings of `F` separated by `t` steps are almost independent: the operator
expression exceeds the independent value `|F|² / n` by at most
`lam ^ t * deg * |F|`. -/
theorem sum_headCount_stepIter_le (F : Finset (G.V × G.D)) {lam : ℝ}
    (hlam : 0 ≤ lam) (hspec : G.SpectralBound lam) (hn : 0 < G.order) (t : ℕ) :
    ∑ z : G.V, (G.headCount F z : ℝ)
        * G.stepIter t (fun w => (G.dartCount F w : ℝ)) z
      ≤ (F.card : ℝ) * (F.card : ℝ) / (G.order : ℝ)
        + lam ^ t * ((G.deg : ℝ) * (F.card : ℝ)) := by
  have hmix := G.mixing_sq hspec hn t (fun z => (G.headCount F z : ℝ))
    (fun w => (G.dartCount F w : ℝ))
  have hsumf : ∑ z : G.V, (G.headCount F z : ℝ) = (F.card : ℝ) := by
    rw [← Nat.cast_sum, G.sum_headCount F]
  have hsumg : ∑ v : G.V, (G.dartCount F v : ℝ) = (F.card : ℝ) := by
    rw [← Nat.cast_sum, G.sum_dartCount F]
  rw [hsumf, hsumg] at hmix
  set X : ℝ := ∑ z : G.V, (G.headCount F z : ℝ)
    * G.stepIter t (fun w => (G.dartCount F w : ℝ)) z with hX
  set c : ℝ := (F.card : ℝ) * (F.card : ℝ) / (G.order : ℝ) with hc
  set D : ℝ := lam ^ t * ((G.deg : ℝ) * (F.card : ℝ)) with hD
  have hDnn : 0 ≤ D := by
    rw [hD]
    have : (0 : ℝ) ≤ lam ^ t := by positivity
    positivity
  have hbound : (X - c) ^ 2 ≤ D ^ 2 := by
    refine le_trans hmix ?_
    have hvf : (∑ z : G.V, (G.headCount F z : ℝ) ^ 2) - (F.card : ℝ) ^ 2 / (G.order : ℝ)
        ≤ (G.deg : ℝ) * (F.card : ℝ) := by
      have h1 := G.sum_sq_headCount_le F
      have h2 : (0 : ℝ) ≤ (F.card : ℝ) ^ 2 / (G.order : ℝ) := by positivity
      linarith
    have hvg : (∑ v : G.V, (G.dartCount F v : ℝ) ^ 2) - (F.card : ℝ) ^ 2 / (G.order : ℝ)
        ≤ (G.deg : ℝ) * (F.card : ℝ) := by
      have h1 := G.sum_sq_dartCount_le F
      have h2 : (0 : ℝ) ≤ (F.card : ℝ) ^ 2 / (G.order : ℝ) := by positivity
      linarith
    have hvfnn : (0 : ℝ) ≤ (∑ z : G.V, (G.headCount F z : ℝ) ^ 2)
        - (F.card : ℝ) ^ 2 / (G.order : ℝ) := by
      have := G.sum_sq_center_nonneg (fun z => (G.headCount F z : ℝ))
      rwa [G.sum_sq_center hn, hsumf] at this
    have hvgnn : (0 : ℝ) ≤ (∑ v : G.V, (G.dartCount F v : ℝ) ^ 2)
        - (F.card : ℝ) ^ 2 / (G.order : ℝ) := by
      have := G.sum_sq_center_nonneg (fun w => (G.dartCount F w : ℝ))
      rwa [G.sum_sq_center hn, hsumg] at this
    have hpow : (0 : ℝ) ≤ lam ^ (2 * t) := by positivity
    have hprod : lam ^ (2 * t)
        * ((∑ z : G.V, (G.headCount F z : ℝ) ^ 2) - (F.card : ℝ) ^ 2 / (G.order : ℝ))
        * ((∑ v : G.V, (G.dartCount F v : ℝ) ^ 2) - (F.card : ℝ) ^ 2 / (G.order : ℝ))
        ≤ lam ^ (2 * t) * ((G.deg : ℝ) * (F.card : ℝ)) * ((G.deg : ℝ) * (F.card : ℝ)) := by
      have hstep : lam ^ (2 * t)
          * ((∑ z : G.V, (G.headCount F z : ℝ) ^ 2) - (F.card : ℝ) ^ 2 / (G.order : ℝ))
          ≤ lam ^ (2 * t) * ((G.deg : ℝ) * (F.card : ℝ)) :=
        mul_le_mul_of_nonneg_left hvf hpow
      have hnn2 : (0 : ℝ) ≤ lam ^ (2 * t)
          * ((∑ z : G.V, (G.headCount F z : ℝ) ^ 2)
            - (F.card : ℝ) ^ 2 / (G.order : ℝ)) := by positivity
      nlinarith [hvgnn, hvg]
    refine le_trans hprod ?_
    rw [hD]
    have h2t : lam ^ (2 * t) = (lam ^ t) ^ 2 := by
      rw [← pow_mul, Nat.mul_comm]
    rw [h2t]
    ring_nf
    exact le_refl _
  have habs : X - c ≤ D := by
    nlinarith [hbound, hDnn]
  linarith

/-- **The second moment.** Summed over every pair of positions, the two-crossing
correlations exceed the independent value by at most `m / (1 - lam)` times
`deg * |F|`. The counts are supplied abstractly as `C`, since writing the
concrete one inside a sum would need the position bounds pointwise. -/
theorem sum_pairs_le (F : Finset (G.V × G.D)) {lam : ℝ} (hlam0 : 0 ≤ lam)
    (hlam1 : lam < 1) (hspec : G.SpectralBound lam) (hn : 0 < G.order) (m : ℕ)
    (C : ℕ → ℕ → ℝ)
    (hC : ∀ k ∈ Finset.range m, ∀ l ∈ Finset.Ico (k + 1) m,
      C k l = ∑ z : G.V, (G.headCount F z : ℝ)
        * G.stepIter (l - k - 1) (fun w => (G.dartCount F w : ℝ)) z) :
    ∑ k ∈ Finset.range m, ∑ l ∈ Finset.Ico (k + 1) m, C k l
      ≤ (m : ℝ) * (m : ℝ) * ((F.card : ℝ) * (F.card : ℝ) / (G.order : ℝ))
        + (m : ℝ) * (1 / (1 - lam)) * ((G.deg : ℝ) * (F.card : ℝ)) := by
  have hbound : ∀ k ∈ Finset.range m, ∀ l ∈ Finset.Ico (k + 1) m,
      C k l ≤ (F.card : ℝ) * (F.card : ℝ) / (G.order : ℝ)
        + lam ^ (l - k - 1) * ((G.deg : ℝ) * (F.card : ℝ)) := by
    intro k hk l hl
    rw [hC k hk l hl]
    exact G.sum_headCount_stepIter_le F hlam0 hspec hn _
  have hstep1 : ∑ k ∈ Finset.range m, ∑ l ∈ Finset.Ico (k + 1) m, C k l
      ≤ ∑ k ∈ Finset.range m, ∑ l ∈ Finset.Ico (k + 1) m,
        ((F.card : ℝ) * (F.card : ℝ) / (G.order : ℝ)
          + lam ^ (l - k - 1) * ((G.deg : ℝ) * (F.card : ℝ))) :=
    Finset.sum_le_sum fun k hk => Finset.sum_le_sum fun l hl => hbound k hk l hl
  have hsplit : ∑ k ∈ Finset.range m, ∑ l ∈ Finset.Ico (k + 1) m,
        ((F.card : ℝ) * (F.card : ℝ) / (G.order : ℝ)
          + lam ^ (l - k - 1) * ((G.deg : ℝ) * (F.card : ℝ)))
      = (∑ k ∈ Finset.range m, ∑ l ∈ Finset.Ico (k + 1) m,
            (F.card : ℝ) * (F.card : ℝ) / (G.order : ℝ))
        + (∑ k ∈ Finset.range m, ∑ l ∈ Finset.Ico (k + 1) m,
            lam ^ (l - k - 1) * ((G.deg : ℝ) * (F.card : ℝ))) := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun k _ => Finset.sum_add_distrib
  have hconst : ∑ k ∈ Finset.range m, ∑ l ∈ Finset.Ico (k + 1) m,
        (F.card : ℝ) * (F.card : ℝ) / (G.order : ℝ)
      ≤ (m : ℝ) * (m : ℝ) * ((F.card : ℝ) * (F.card : ℝ) / (G.order : ℝ)) := by
    have hnn : (0 : ℝ) ≤ (F.card : ℝ) * (F.card : ℝ) / (G.order : ℝ) := by positivity
    have hinner : ∀ k ∈ Finset.range m, ∑ l ∈ Finset.Ico (k + 1) m,
        (F.card : ℝ) * (F.card : ℝ) / (G.order : ℝ)
        ≤ (m : ℝ) * ((F.card : ℝ) * (F.card : ℝ) / (G.order : ℝ)) := by
      intro k _
      rw [Finset.sum_const, nsmul_eq_mul, Nat.card_Ico]
      have hcard : ((m - (k + 1) : ℕ) : ℝ) ≤ (m : ℝ) := by
        have : (m - (k + 1) : ℕ) ≤ m := by omega
        exact_mod_cast this
      exact mul_le_mul_of_nonneg_right hcard hnn
    calc ∑ k ∈ Finset.range m, ∑ l ∈ Finset.Ico (k + 1) m,
          (F.card : ℝ) * (F.card : ℝ) / (G.order : ℝ)
        ≤ ∑ _k ∈ Finset.range m, (m : ℝ) * ((F.card : ℝ) * (F.card : ℝ) / (G.order : ℝ)) :=
          Finset.sum_le_sum hinner
      _ = (m : ℝ) * (m : ℝ) * ((F.card : ℝ) * (F.card : ℝ) / (G.order : ℝ)) := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
          ring
  have hgeom : ∑ k ∈ Finset.range m, ∑ l ∈ Finset.Ico (k + 1) m,
        lam ^ (l - k - 1) * ((G.deg : ℝ) * (F.card : ℝ))
      ≤ (m : ℝ) * (1 / (1 - lam)) * ((G.deg : ℝ) * (F.card : ℝ)) := by
    have hfactor : ∑ k ∈ Finset.range m, ∑ l ∈ Finset.Ico (k + 1) m,
          lam ^ (l - k - 1) * ((G.deg : ℝ) * (F.card : ℝ))
        = (∑ k ∈ Finset.range m, ∑ l ∈ Finset.Ico (k + 1) m, lam ^ (l - k - 1))
          * ((G.deg : ℝ) * (F.card : ℝ)) := by
      rw [Finset.sum_mul]
      exact Finset.sum_congr rfl fun k _ => (Finset.sum_mul _ _ _).symm
    rw [hfactor]
    have hnn : (0 : ℝ) ≤ (G.deg : ℝ) * (F.card : ℝ) := by positivity
    exact mul_le_mul_of_nonneg_right (sum_pairs_geom_le hlam0 hlam1 m) hnn
  linarith [hstep1, hsplit.le, hsplit.ge, hconst, hgeom]

end RegGraph

end Complexity
