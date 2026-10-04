/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Defs
public import Complexitylib.Algebraic.LowerBound.Cutwidth.AverageCase
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Nondeterministic

/-!
# From sumset extraction to circuit hardness

Zero-padding the two sides of a coordinate rectangle gives independent flat
sources whose XOR is the glued input. Flat-source sumset extraction therefore
implies `Balanced`, then rectangle-freeness and the accepting-input bound.
These are the combinatorial bridges for the extractor route in Ryan Williams's
September 2026 working note. The cubic bisection and pathwidth theorems are
proved. The new deterministic, nondeterministic, and average-case endpoints
instantiate these graph bounds, leaving the extractor family as the remaining
application obligation. The generic interfaces with explicit graph bounds
are retained.
-/

@[expose] public section

namespace Algebraic
namespace Cutwidth

open scoped Classical

variable {n : Nat}

/-- Nontrivial extraction excludes singleton sources, so its support-size
threshold is at least two. -/
theorem FlatSumsetExtractor.one_lt {f : Cslib.BooleanFunction n} {K : Nat} {ν : ℝ}
    (extract : FlatSumsetExtractor f K ν) (hν : ν < 1 / 2) : 1 < K := by
  by_contra hK
  have hK' : K ≤ 1 := by lia
  have h := extract {fun _ => false} {fun _ => false}
    (by simpa using hK') (by simpa using hK')
  have hz : xorInput (fun _ : Fin n => false) (fun _ => false) = (fun _ => false) := rfl
  simp only [sumsetOnes, Finset.singleton_product_singleton, Finset.filter_singleton, hz] at h
  cases hf : f (fun _ => false) <;> simp [hf] at h <;> linarith

/-- On a single bit, XOR of two full-support uniform sources is exactly
uniform. This is a non-vacuous zero-error instance of the extractor contract. -/
theorem flatSumsetExtractor_singleBit :
    FlatSumsetExtractor (fun x : Fin 1 → Bool => x 0) 2 0 := by
  intro P Q hP hQ
  have card : Fintype.card (Fin 1 → Bool) = 2 := by simp
  have hPU : P = Finset.univ := P.eq_univ_of_card
    (le_antisymm P.card_le_univ (by simpa only [card] using hP))
  have hQU : Q = Finset.univ := Q.eq_univ_of_card
    (le_antisymm Q.card_le_univ (by simpa only [card] using hQ))
  subst P
  subst Q
  have hne : (fun _ : Fin 1 => false) ≠ (fun _ => true) := by
    intro h
    have := congrFun h 0
    contradiction
  have hones : (sumsetOnes (fun x : Fin 1 → Bool => x 0)
      Finset.univ Finset.univ).card = 2 := by
    have heq : sumsetOnes (fun x : Fin 1 → Bool => x 0) Finset.univ Finset.univ =
        {(fun _ => false, fun _ => true), (fun _ => true, fun _ => false)} := by
      ext ⟨x, y⟩
      simp only [sumsetOnes, Finset.mem_filter, Finset.mem_product,
        Finset.mem_univ, true_and, Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq]
      have hx : x = fun _ => x 0 := by funext i; rw [Fin.eq_zero i]
      have hy : y = fun _ => y 0 := by funext i; rw [Fin.eq_zero i]
      rw [hx, hy]
      cases x 0 <;> cases y 0 <;> simp [xorInput, hne, Ne.symm hne]
    rw [heq]
    simp [hne]
  simp [hones, Finset.card_univ, card]

private def padLeft (U : Finset (Fin n)) : (U → Bool) ↪ (Fin n → Bool) where
  toFun p := glue U p (fun _ => false)
  inj' := by
    intro p p' h
    funext i
    simpa using congrFun h i

private def padRight (U : Finset (Fin n)) : (↥Uᶜ → Bool) ↪ (Fin n → Bool) where
  toFun q := glue U (fun _ => false) q
  inj' := by
    intro q q' h
    funext i
    simpa using congrFun h i

private theorem xor_pad (U : Finset (Fin n)) (p : U → Bool) (q : ↥Uᶜ → Bool) :
    xorInput (padLeft U p) (padRight U q) = glue U p q := by
  funext i
  change Bool.xor (glue U p (fun _ => false) i)
    (glue U (fun _ => false) q i) = glue U p q i
  by_cases hi : i ∈ U <;> simp [glue, hi]

private theorem card_sumsetOnes_pad (f : Cslib.BooleanFunction n) (U : Finset (Fin n))
    (P : Finset (U → Bool)) (Q : Finset (↥Uᶜ → Bool)) :
    (sumsetOnes f (P.map (padLeft U)) (Q.map (padRight U))).card =
      (rectangleOnes f U P Q).card := by
  symm
  apply Finset.card_bij (fun pq _ => (padLeft U pq.1, padRight U pq.2))
  · intro pq hpq
    simp only [rectangleOnes, Finset.mem_filter, Finset.mem_product] at hpq
    simp only [sumsetOnes, Finset.mem_filter, Finset.mem_product, xor_pad]
    exact ⟨⟨Finset.mem_map.mpr ⟨pq.1, hpq.1.1, rfl⟩,
      Finset.mem_map.mpr ⟨pq.2, hpq.1.2, rfl⟩⟩, hpq.2⟩
  · intro pq _ pq' _ h
    exact Prod.ext ((padLeft U).injective (congrArg Prod.fst h))
      ((padRight U).injective (congrArg Prod.snd h))
  · intro xy hxy
    simp only [sumsetOnes, Finset.mem_filter, Finset.mem_product] at hxy
    obtain ⟨p, hp, hpx⟩ := Finset.mem_map.mp hxy.1.1
    obtain ⟨q, hq, hqy⟩ := Finset.mem_map.mp hxy.1.2
    refine ⟨(p, q), ?_, Prod.ext hpx hqy⟩
    simp only [rectangleOnes, Finset.mem_filter, Finset.mem_product]
    refine ⟨⟨hp, hq⟩, ?_⟩
    simpa only [← hpx, ← hqy, xor_pad] using hxy.2

/-- Independent uniform rectangle sides become flat sumset sources by
zero-padding their complementary coordinates. -/
theorem FlatSumsetExtractor.balanced {f : Cslib.BooleanFunction n} {K : Nat} {ν : ℝ}
    (extract : FlatSumsetExtractor f K ν) : Balanced f K ν := by
  intro U P Q hP hQ
  have h := extract (P.map (padLeft U)) (Q.map (padRight U))
    (by simpa using hP) (by simpa using hQ)
  simpa only [Finset.card_map, card_sumsetOnes_pad] using h

/-- Error strictly below one half excludes a monochromatic one-rectangle
with both sides at least the extraction threshold. -/
theorem Balanced.rectangleFree {f : Cslib.BooleanFunction n} {K : Nat} {ν : ℝ}
    (balanced : Balanced f K ν) (hK : 0 < K) (hν : ν < 1 / 2) : RectangleFree f K := by
  intro U P Q ones
  by_contra h
  push Not at h
  have hcount : (rectangleOnes f U P Q).card = P.card * Q.card := by
    rw [rectangleOnes, Finset.filter_eq_self.mpr]
    · exact Finset.card_product P Q
    · intro pq hpq
      exact ones pq.1 (Finset.mem_product.mp hpq).1 pq.2 (Finset.mem_product.mp hpq).2
  have upper := (balanced U P Q h.1 h.2).2
  rw [hcount] at upper
  push_cast at upper
  have hpos : (0 : ℝ) < P.card * Q.card := by
    exact_mod_cast Nat.mul_pos (hK.trans_le h.1) (hK.trans_le h.2)
  nlinarith

/-- A flat sumset extractor is rectangle-free at the same threshold. -/
theorem FlatSumsetExtractor.rectangleFree {f : Cslib.BooleanFunction n} {K : Nat} {ν : ℝ}
    (extract : FlatSumsetExtractor f K ν) (hK : 0 < K) (hν : ν < 1 / 2) :
    RectangleFree f K := extract.balanced.rectangleFree hK hν

/-- The full cube has accepting density within the extraction error of one
half, provided each half of its coordinates supports a large enough source. -/
theorem FlatSumsetExtractor.card_accepting_bounds {f : Cslib.BooleanFunction n}
    {K : Nat} {ν : ℝ} (extract : FlatSumsetExtractor f K ν)
    (hK : K ≤ 2 ^ (n / 2)) :
    (1 / 2 - ν) * 2 ^ n ≤ ((accepting f).card : ℝ) ∧
      ((accepting f).card : ℝ) ≤ (1 / 2 + ν) * 2 ^ n := by
  apply card_accepting_bounds_of_balanced extract.balanced (Nat.div_le_self _ _) hK
  exact hK.trans (Nat.pow_le_pow_right two_pos (by lia))

/-- Error at most one quarter gives the density required by the circuit
lower bound, including odd input lengths. -/
theorem FlatSumsetExtractor.card_accepting_ge {f : Cslib.BooleanFunction n}
    {K : Nat} {ν : ℝ} (extract : FlatSumsetExtractor f K ν)
    (hν : ν ≤ 1 / 4) (hn : 2 ≤ n) (hK : K ≤ 2 ^ (n / 2)) :
    2 ^ (n - 2) ≤ (accepting f).card := by
  have lower := (extract.card_accepting_bounds hK).1
  have hp : (2 : ℝ) ^ n = 4 * 2 ^ (n - 2) := by
    rw [show n = (n - 2) + 2 from (Nat.sub_add_cancel hn).symm, pow_add]
    norm_num
    ring
  have hpow : (0 : ℝ) ≤ 2 ^ n := by positivity
  have : (2 : ℝ) ^ (n - 2) ≤ (accepting f).card := by nlinarith
  exact_mod_cast this

/-- Sublinear source entropy and error at most one quarter supply both
hard-family hypotheses of the circuit lower bound for all large inputs. -/
theorem eventually_hard_of_flatSumsetExtractor
    {f : ∀ n, Cslib.BooleanFunction n} {K : Nat → Nat} {ν : ℝ} (hν : ν ≤ 1 / 4)
    (hK : (fun n => Real.logb 2 (K n)) =o[Filter.atTop] (fun n => (n : ℝ)))
    (extract : ∀ᶠ n in Filter.atTop, FlatSumsetExtractor (f n) (K n) ν) :
    ∀ᶠ n in Filter.atTop,
      RectangleFree (f n) (K n) ∧ 2 ^ (n - 2) ≤ (accepting (f n)).card := by
  filter_upwards [extract, eventually_le_pow_half_of_log hK, Filter.eventually_ge_atTop 2]
    with n hn hKn hn2
  exact ⟨hn.rectangleFree (by have := hn.one_lt (by linarith); lia) (by linarith),
    hn.card_accepting_ge hν hn2 hKn⟩

/-- The extractor route to the coefficient-four lower bound. Only
sublinear source entropy is needed, with any fixed error at most one quarter.
This generic interface keeps the graph-ordering bound as an explicit parameter. -/
theorem eventually_lt_size_of_flatSumsetExtractor
    (order : ∀ η : ℝ, 0 < η → ∃ C : ℝ, Multigraph.OrderingBound (1 / 3) η C)
    (f : ∀ n, Cslib.BooleanFunction n) (K : Nat → Nat) {ν : ℝ} (hν : ν ≤ 1 / 4)
    (hK : (fun n => Real.logb 2 (K n)) =o[Filter.atTop] (fun n => (n : ℝ)))
    (extract : ∀ᶠ n in Filter.atTop, FlatSumsetExtractor (f n) (K n) ν)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in Filter.atTop, ∀ circuit : Circuit Binary.signature n 1,
      circuit.Computes Binary.interpretation (fun x _ => f n x) →
        (4 - ε) * n < circuit.size := by
  have hard := eventually_hard_of_flatSumsetExtractor hν hK extract
  exact eventually_lt_size_of_log_sublinear order f K hK
    (hard.mono fun _ h => h.2) (hard.mono fun _ h => h.1) hε

/-- The extractor-to-circuit bridge with the cubic pathwidth
theorem as its graph-theoretic prerequisite. -/
theorem eventually_lt_size_of_pathwidthBound_of_flatSumsetExtractor
    (pathwidth : ∀ ξ : ℝ, 0 < ξ → ∃ N₀ : Nat, PathwidthBound (1 / 6) ξ N₀)
    (f : ∀ n, Cslib.BooleanFunction n) (K : Nat → Nat) {ν : ℝ} (hν : ν ≤ 1 / 4)
    (hK : (fun n => Real.logb 2 (K n)) =o[Filter.atTop] (fun n => (n : ℝ)))
    (extract : ∀ᶠ n in Filter.atTop, FlatSumsetExtractor (f n) (K n) ν)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in Filter.atTop, ∀ circuit : Circuit Binary.signature n 1,
      circuit.Computes Binary.interpretation (fun x _ => f n x) →
        (4 - ε) * n < circuit.size :=
  eventually_lt_size_of_flatSumsetExtractor
    (Multigraph.exists_orderingBound_one_third_of_pathwidthBound pathwidth) f K hν hK extract hε

/-- The generic extractor route with an explicit cubic bisection bound.
The extraction-to-rectangle and bisection-to-pathwidth reductions are proved. -/
theorem eventually_lt_size_of_bisectionBound_of_flatSumsetExtractor
    (bisection : ∀ ξ : ℝ, 0 < ξ → ∃ N₀ : Nat, BisectionBound ξ N₀)
    (f : ∀ n, Cslib.BooleanFunction n) (K : Nat → Nat) {ν : ℝ} (hν : ν ≤ 1 / 4)
    (hK : (fun n => Real.logb 2 (K n)) =o[Filter.atTop] (fun n => (n : ℝ)))
    (extract : ∀ᶠ n in Filter.atTop, FlatSumsetExtractor (f n) (K n) ν)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in Filter.atTop, ∀ circuit : Circuit Binary.signature n 1,
      circuit.Computes Binary.interpretation (fun x _ => f n x) →
        (4 - ε) * n < circuit.size :=
  eventually_lt_size_of_pathwidthBound_of_flatSumsetExtractor
    (pathwidthBound_of_bisectionBound bisection) f K hν hK extract hε

/-- Flat sumset extraction also gives the coefficient-four lower bound
against nondeterministic circuits with arbitrarily many witness inputs. -/
theorem nondet_eventually_lt_size_of_flatSumsetExtractor
    (order : ∀ η : ℝ, 0 < η → ∃ C : ℝ, Multigraph.OrderingBound (1 / 3) η C)
    (f : ∀ n, Cslib.BooleanFunction n) (K : Nat → Nat) {ν : ℝ} (hν : ν ≤ 1 / 4)
    (hK : (fun n => Real.logb 2 (K n)) =o[Filter.atTop] (fun n => (n : ℝ)))
    (extract : ∀ᶠ n in Filter.atTop, FlatSumsetExtractor (f n) (K n) ν)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in Filter.atTop, ∀ (m : Nat) (circuit : Circuit Binary.signature (n + m) 1),
      NondetComputes circuit (f n) → (4 - ε) * n < circuit.size := by
  have hard := eventually_hard_of_flatSumsetExtractor hν hK extract
  exact nondet_eventually_lt_size_of_log_sublinear order f K hK
    (hard.mono fun _ h => h.2) (hard.mono fun _ h => h.1) hε

/-- Flat sumset extraction at sublinear source entropy gives the deterministic
coefficient-four lower bound with all graph bounds instantiated. -/
theorem eventually_lt_size_of_flatSumsetExtractor_of_log_sublinear
    (f : ∀ n, Cslib.BooleanFunction n) (K : Nat → Nat) {ν : ℝ} (hν : ν ≤ 1 / 4)
    (hK : (fun n => Real.logb 2 (K n)) =o[Filter.atTop] (fun n => (n : ℝ)))
    (extract : ∀ᶠ n in Filter.atTop, FlatSumsetExtractor (f n) (K n) ν)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in Filter.atTop, ∀ circuit : Circuit Binary.signature n 1,
      circuit.Computes Binary.interpretation (fun x _ => f n x) →
        (4 - ε) * n < circuit.size := by
  have hard := eventually_hard_of_flatSumsetExtractor hν hK extract
  exact eventually_lt_size_of_rectangleFree f K hK
    (hard.mono fun _ h => h.2) (hard.mono fun _ h => h.1) hε

/-- Flat sumset extraction at sublinear source entropy gives the same lower
bound with unrestricted nondeterministic witnesses and no graph hypothesis. -/
theorem nondet_eventually_lt_size_of_flatSumsetExtractor_of_log_sublinear
    (f : ∀ n, Cslib.BooleanFunction n) (K : Nat → Nat) {ν : ℝ} (hν : ν ≤ 1 / 4)
    (hK : (fun n => Real.logb 2 (K n)) =o[Filter.atTop] (fun n => (n : ℝ)))
    (extract : ∀ᶠ n in Filter.atTop, FlatSumsetExtractor (f n) (K n) ν)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in Filter.atTop, ∀ (m : Nat) (circuit : Circuit Binary.signature (n + m) 1),
      NondetComputes circuit (f n) → (4 - ε) * n < circuit.size := by
  have hard := eventually_hard_of_flatSumsetExtractor hν hK extract
  exact nondet_eventually_lt_size_of_rectangleFree f K hK
    (hard.mono fun _ h => h.2) (hard.mono fun _ h => h.1) hε

/-- Polynomial-threshold flat sumset extraction gives the average-case
agreement bound using the proved graph theorems. -/
theorem eventually_card_agree_le_of_flatSumsetExtractor
    (f : ∀ n, Cslib.BooleanFunction n) (K : Nat → Nat) (c : Nat) {ν : ℝ} (hν : 0 ≤ ν)
    (hK : ∀ᶠ n in Filter.atTop, K n ≤ n ^ c)
    (extract : ∀ᶠ n in Filter.atTop, FlatSumsetExtractor (f n) (K n) ν)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in Filter.atTop, ∀ circuit : Circuit Binary.signature n 1,
      (circuit.size : ℝ) ≤ (4 - ε) * n →
        ((Finset.univ.filter fun x => circuit.eval Binary.interpretation x 0 = f n x).card : ℝ) ≤
          (1 / 2 + 3 * ν) * 2 ^ n + (2 : ℝ) ^ ((1 - ε / 24) * n) :=
  eventually_card_agree_le_of_balanced f K c hν hK
    (extract.mono fun _ h => h.balanced) hε

end Cutwidth
end Algebraic
