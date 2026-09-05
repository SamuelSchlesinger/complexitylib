/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/
module
public import Complexitylib.BooleanAnalysis.FourierExpansion
public import Mathlib.Logic.Equiv.Fin.Basic

/-!
# Blocks of a cube, and marginals

An assignment tester makes several reads, each with its own randomness. The
Fourier layer supplies probability over *one* cube point (`Pr`) and over a pair
(`Pr₂`), but not over `k` independent points, and building a `k`-fold product
measure would be a detour.

The alternative taken here is to bundle: the tester's whole random string is a
single point of a larger cube, and each read uses its own block. What makes this
work is that the uniform measure on the big cube restricts to the uniform measure
on each block — proved below — so the existing one-variable lemmas apply to each
read, and the existing union bound combines them.

## Main definitions

- `Complexity.leftBlock`, `Complexity.rightBlock` — the two halves of a point

## Main results

- `Complexity.prob_leftBlock`, `Complexity.prob_rightBlock` — a block is
  uniformly distributed
- `Complexity.prob_forall_ge` — the union bound combining many reads
- `Complexity.prob_leftBlock_rightBlock` — marginals compose, so any fixed
  number of blocks can be bundled
- `Complexity.prob₂_eq_prob_blocks` — a probability over a pair is a
  probability over one bundled point
- `Complexity.prob_le_of_imp_of_good` — transferring an observed acceptance
  probability along a likely good event
- `Complexity.prob_blocks`, `Complexity.prob_blocks_ge` — conditioning on an
  earlier block, so a read point may depend on earlier randomness
-/

@[expose] public section

namespace Complexity

open BooleanAnalysis

variable {a b : ℕ}

/-- The first block of a point of the combined cube. -/
def leftBlock (z : Cube (a + b)) : Cube a := fun i => z (Fin.castAdd b i)

/-- The second block of a point of the combined cube. -/
def rightBlock (z : Cube (a + b)) : Cube b := fun j => z (Fin.natAdd a j)

theorem leftBlock_append (x : Cube a) (y : Cube b) :
    leftBlock (Fin.append x y) = x := by
  funext i
  show Fin.append x y (Fin.castAdd b i) = x i
  rw [Fin.append_left]

theorem rightBlock_append (x : Cube a) (y : Cube b) :
    rightBlock (Fin.append x y) = y := by
  funext j
  show Fin.append x y (Fin.natAdd a j) = y j
  rw [Fin.append_right]

/-- Splitting a point of the combined cube into its blocks is a bijection. -/
noncomputable def cubeBlockEquiv (a b : ℕ) : Cube a × Cube b ≃ Cube (a + b) :=
  Fin.appendEquiv a b

theorem leftBlock_blockEquiv (p : Cube a × Cube b) :
    leftBlock (cubeBlockEquiv a b p) = p.1 := leftBlock_append p.1 p.2

theorem rightBlock_blockEquiv (p : Cube a × Cube b) :
    rightBlock (cubeBlockEquiv a b p) = p.2 := rightBlock_append p.1 p.2

/-- **The first block is uniform.** A predicate depending only on the first
block has the same probability over the combined cube as over its own. -/
theorem prob_leftBlock (P : Cube a → Prop) :
    Pr[fun z : Cube (a + b) => P (leftBlock z)] = Pr[P] := by
  classical
  rw [BooleanAnalysis.prob, BooleanAnalysis.prob, expect_unfold, expect_unfold]
  have hsum : ∑ z : Cube (a + b), indicator (fun z => P (leftBlock z)) z
      = ∑ p : Cube a × Cube b, indicator P p.1 := by
    refine Fintype.sum_equiv (cubeBlockEquiv a b).symm _ _ fun z => ?_
    show indicator (fun z => P (leftBlock z)) z
      = indicator P ((cubeBlockEquiv a b).symm z).1
    have hz : leftBlock z = ((cubeBlockEquiv a b).symm z).1 := by
      rw [← leftBlock_blockEquiv ((cubeBlockEquiv a b).symm z), Equiv.apply_symm_apply]
    simp only [indicator, hz]
  rw [hsum, Fintype.sum_prod_type]
  have hinner : ∀ x : Cube a, ∑ _y : Cube b, indicator P x
      = (2 : ℝ) ^ b * indicator P x := by
    intro x
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    have hcard : Fintype.card (Cube b) = 2 ^ b := by
      show Fintype.card (Fin b → ZMod 2) = 2 ^ b
      rw [Fintype.card_fun, ZMod.card, Fintype.card_fin]
    rw [hcard]
    norm_num
  rw [Finset.sum_congr rfl fun x _ => hinner x,
    ← Finset.mul_sum (s := Finset.univ) (a := (2 : ℝ) ^ b) (f := fun x : Cube a => 𝟙P x)]
  rw [pow_add]
  field_simp

/-- **The second block is uniform** too. -/
theorem prob_rightBlock (P : Cube b → Prop) :
    Pr[fun z : Cube (a + b) => P (rightBlock z)] = Pr[P] := by
  classical
  rw [BooleanAnalysis.prob, BooleanAnalysis.prob, expect_unfold, expect_unfold]
  have hsum : ∑ z : Cube (a + b), indicator (fun z => P (rightBlock z)) z
      = ∑ p : Cube a × Cube b, indicator P p.2 := by
    refine Fintype.sum_equiv (cubeBlockEquiv a b).symm _ _ fun z => ?_
    show indicator (fun z => P (rightBlock z)) z
      = indicator P ((cubeBlockEquiv a b).symm z).2
    have hz : rightBlock z = ((cubeBlockEquiv a b).symm z).2 := by
      rw [← rightBlock_blockEquiv ((cubeBlockEquiv a b).symm z), Equiv.apply_symm_apply]
    simp only [indicator, hz]
  rw [hsum, Fintype.sum_prod_type_right]
  have hinner : ∀ y : Cube b, ∑ _x : Cube a, indicator P y
      = (2 : ℝ) ^ a * indicator P y := by
    intro y
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    have hcard : Fintype.card (Cube a) = 2 ^ a := by
      show Fintype.card (Fin a → ZMod 2) = 2 ^ a
      rw [Fintype.card_fun, ZMod.card, Fintype.card_fin]
    rw [hcard]
    norm_num
  rw [Finset.sum_congr rfl fun y _ => hinner y,
    ← Finset.mul_sum (s := Finset.univ) (a := (2 : ℝ) ^ a) (f := fun y : Cube b => 𝟙P y)]
  rw [pow_add]
  field_simp

/-! ### A union bound over many reads -/

theorem prob_of_forall {m : ℕ} {P : Cube m → Prop} (h : ∀ x, P x) : Pr[P] = 1 := by
  classical
  have hc := BooleanAnalysis.Internal.prob_compl P
  have hzero : Pr[fun x => ¬ P x] = 0 := by
    rw [BooleanAnalysis.prob, expect_unfold]
    have hterm : ∀ x : Cube m, indicator (fun x => ¬ P x) x = 0 := by
      intro x
      simp [indicator, h x]
    rw [Finset.sum_congr rfl fun x _ => hterm x]
    simp
  linarith

/-- **Union bound over `k` events.** If each of `k` events holds except with
probability `ε`, all hold except with probability `k · ε`. With the tester's
randomness bundled into one point, each read's correctness is an event on that
point, so this is the bound that combines them. -/
theorem prob_forall_ge {m : ℕ} : ∀ (k : ℕ) (P : Fin k → Cube m → Prop) (ε : ℝ),
    (∀ i, 1 - ε ≤ Pr[P i]) → 1 - k * ε ≤ Pr[fun z => ∀ i, P i z] := by
  intro k
  induction k with
  | zero =>
      intro P ε _
      have hall : Pr[fun z : Cube m => ∀ i : Fin 0, P i z] = 1 :=
        prob_of_forall fun z i => absurd i.isLt (by omega)
      rw [hall]
      norm_num
  | succ k ih =>
      intro P ε hP
      have hrest := ih (fun i => P i.succ) ε fun i => hP i.succ
      have hcompl0 : Pr[fun z => ¬ P 0 z] ≤ ε := by
        have h1 := BooleanAnalysis.Internal.prob_compl (P 0)
        have h2 := hP 0
        linarith
      have hcomplr : Pr[fun z => ¬ (∀ i : Fin k, P i.succ z)] ≤ k * ε := by
        have h1 := BooleanAnalysis.Internal.prob_compl
          (fun z => ∀ i : Fin k, P i.succ z)
        linarith
      have hunion := BooleanAnalysis.Internal.prob_union_bound
        (P := fun z => ∀ i : Fin (k + 1), P i z)
        (Q := fun z => ¬ P 0 z)
        (R := fun z => ¬ (∀ i : Fin k, P i.succ z))
        (fun z hz => by
          by_contra hcon
          push Not at hcon
          exact hz fun i => Fin.cases hcon.1 (fun j => hcon.2 j) i)
      have hc := BooleanAnalysis.Internal.prob_compl (fun z => ∀ i : Fin (k + 1), P i z)
      push_cast
      linarith

/-! ### Composed blocks -/

/-- Marginals compose: a block of a block is still uniform. Iterating this gives
a bundled random string with any fixed number of independent blocks, which is all
a tester with constantly many reads needs. -/
theorem prob_leftBlock_rightBlock {a b c : ℕ} (P : Cube b → Prop) :
    Pr[fun z : Cube (a + (b + c)) => P (leftBlock (rightBlock z))] = Pr[P] := by
  have h1 : Pr[fun z : Cube (a + (b + c)) => P (leftBlock (rightBlock z))]
      = Pr[fun w : Cube (b + c) => P (leftBlock w)] :=
    prob_rightBlock (fun w : Cube (b + c) => P (leftBlock w))
  rw [h1]
  exact prob_leftBlock P

theorem prob_rightBlock_rightBlock {a b c : ℕ} (P : Cube c → Prop) :
    Pr[fun z : Cube (a + (b + c)) => P (rightBlock (rightBlock z))] = Pr[P] := by
  have h1 : Pr[fun z : Cube (a + (b + c)) => P (rightBlock (rightBlock z))]
      = Pr[fun w : Cube (b + c) => P (rightBlock w)] :=
    prob_rightBlock (fun w : Cube (b + c) => P (rightBlock w))
  rw [h1]
  exact prob_rightBlock P

/-! ### Pairs are two blocks -/

/-- **`Pr₂` is a bundled `Pr`.** The Fourier layer's probability over a pair of
independent points is the probability over a single point of the doubled cube,
read as two blocks.

This is the bridge that lets the pair-based statements (the consistency check)
and the block-based statements (the self-corrected reads) be combined: after
rewriting, both are probabilities over one cube, so a union bound applies. -/
theorem prob₂_eq_prob_blocks {n : ℕ} (P : Cube n → Cube n → Prop) :
    Pr₂[P] = Pr[fun z : Cube (n + n) => P (leftBlock z) (rightBlock z)] := by
  classical
  have hL : Pr₂[P]
      = 1 / 2 ^ n * ∑ x : Cube n, (1 / 2 ^ n * ∑ y : Cube n, indicator (P x) y) := by
    rw [BooleanAnalysis.prob₂,
      expect_unfold (f := fun x : Cube n => 𝔼[𝟙(P x)])]
    exact congrArg _ (Finset.sum_congr rfl fun x _ => expect_unfold _)
  have hR : Pr[fun z : Cube (n + n) => P (leftBlock z) (rightBlock z)]
      = 1 / 2 ^ (n + n) * ∑ p : Cube n × Cube n, indicator (P p.1) p.2 := by
    rw [BooleanAnalysis.prob, expect_unfold]
    refine congrArg _ (Fintype.sum_equiv (cubeBlockEquiv n n).symm _ _ fun z => ?_)
    show indicator (fun z => P (leftBlock z) (rightBlock z)) z
      = indicator (P ((cubeBlockEquiv n n).symm z).1) ((cubeBlockEquiv n n).symm z).2
    have h1 : leftBlock z = ((cubeBlockEquiv n n).symm z).1 := by
      rw [← leftBlock_blockEquiv ((cubeBlockEquiv n n).symm z), Equiv.apply_symm_apply]
    have h2 : rightBlock z = ((cubeBlockEquiv n n).symm z).2 := by
      rw [← rightBlock_blockEquiv ((cubeBlockEquiv n n).symm z), Equiv.apply_symm_apply]
    simp only [indicator, h1, h2]
  rw [hL, hR, Fintype.sum_prod_type, ← Finset.mul_sum, pow_add]
  field_simp

/-- A pair drawn from the first block of a bundled string is a uniform pair,
so a `Pr₂` statement can be read as a statement about the bundled randomness
that the tester's other reads also draw from. -/
theorem prob_pair_block {n c : ℕ} (P : Cube n → Cube n → Prop) :
    Pr[fun z : Cube ((n + n) + c) =>
      P (leftBlock (leftBlock z)) (rightBlock (leftBlock z))] = Pr₂[P] := by
  have h := prob_leftBlock (b := c) (fun w : Cube (n + n) => P (leftBlock w) (rightBlock w))
  rw [h, prob₂_eq_prob_blocks]

/-- **Transfer along a likely good event.** If `E` implies `F` whenever `A`
holds, then `E` is no likelier than `F` plus the chance that `A` fails.

This is how a tester's observed acceptance is converted into a statement about
the decoded tables: `E` is "the tester accepts", `A` is "every self-corrected
read returned the true value", and `F` is the check as made on the decoded
codewords. -/
theorem prob_le_of_imp_of_good {m : ℕ} {E F A : Cube m → Prop}
    (h : ∀ z, E z → A z → F z) : Pr[E] ≤ Pr[F] + (1 - Pr[A]) := by
  classical
  have hub : Pr[fun z => ¬ ¬ E z] ≤ Pr[F] + Pr[fun z => ¬ A z] :=
    BooleanAnalysis.Internal.prob_union_bound (P := fun z => ¬ E z) fun z hz => by
      have hE : E z := not_not.mp hz
      by_cases hA : A z
      · exact Or.inl (h z hE hA)
      · exact Or.inr hA
  have hfun : (fun z => ¬ ¬ E z) = E := by funext z; simp
  rw [hfun] at hub
  have hA := BooleanAnalysis.Internal.prob_compl A
  linarith

/-! ### Conditioning on an earlier block -/

/-- **Fubini for blocks.** A predicate reading both blocks has probability equal
to the average, over the first block, of its conditional probability in the
second.

This is what lets a tester choose *where* to read using early randomness and
still get a uniform correction string: the read point is fixed by `u`, and the
inner probability is the ordinary one-variable statement. -/
theorem prob_blocks {a b : ℕ} (Q : Cube a → Cube b → Prop) :
    Pr[fun z : Cube (a + b) => Q (leftBlock z) (rightBlock z)]
      = 𝔼[fun u : Cube a => Pr[Q u]] := by
  classical
  have hL : Pr[fun z : Cube (a + b) => Q (leftBlock z) (rightBlock z)]
      = 1 / 2 ^ (a + b) * ∑ p : Cube a × Cube b, indicator (Q p.1) p.2 := by
    rw [BooleanAnalysis.prob, expect_unfold]
    refine congrArg _ (Fintype.sum_equiv (cubeBlockEquiv a b).symm _ _ fun z => ?_)
    show indicator (fun z => Q (leftBlock z) (rightBlock z)) z
      = indicator (Q ((cubeBlockEquiv a b).symm z).1) ((cubeBlockEquiv a b).symm z).2
    have h1 : leftBlock z = ((cubeBlockEquiv a b).symm z).1 := by
      rw [← leftBlock_blockEquiv ((cubeBlockEquiv a b).symm z), Equiv.apply_symm_apply]
    have h2 : rightBlock z = ((cubeBlockEquiv a b).symm z).2 := by
      rw [← rightBlock_blockEquiv ((cubeBlockEquiv a b).symm z), Equiv.apply_symm_apply]
    simp only [indicator, h1, h2]
  have hR : 𝔼[fun u : Cube a => Pr[Q u]]
      = 1 / 2 ^ a * ∑ u : Cube a, (1 / 2 ^ b * ∑ v : Cube b, indicator (Q u) v) := by
    rw [expect_unfold (f := fun u : Cube a => Pr[Q u])]
    exact congrArg _ (Finset.sum_congr rfl fun u _ => expect_unfold _)
  rw [hL, hR, Fintype.sum_prod_type, ← Finset.mul_sum, pow_add]
  field_simp

/-- **A bound that holds for every earlier outcome holds overall.** -/
theorem prob_blocks_ge {a b : ℕ} (Q : Cube a → Cube b → Prop) (c : ℝ)
    (h : ∀ u, c ≤ Pr[Q u]) :
    c ≤ Pr[fun z : Cube (a + b) => Q (leftBlock z) (rightBlock z)] := by
  classical
  rw [prob_blocks, expect_unfold (f := fun u : Cube a => Pr[Q u])]
  have hcard : (Finset.univ : Finset (Cube a)).card = 2 ^ a := by
    rw [Finset.card_univ]
    show Fintype.card (Fin a → ZMod 2) = 2 ^ a
    rw [Fintype.card_fun, ZMod.card, Fintype.card_fin]
  have hsum : ∑ _u : Cube a, c ≤ ∑ u : Cube a, Pr[Q u] :=
    Finset.sum_le_sum fun u _ => h u
  rw [Finset.sum_const, hcard, nsmul_eq_mul] at hsum
  push_cast at hsum
  have hpa : (0 : ℝ) < 2 ^ a := by positivity
  rw [one_div, inv_mul_eq_div, le_div_iff₀ hpa, mul_comm]
  exact hsum

/-- **Two likely events are jointly likely.** The union bound in the form the
tester uses: each read fails with its own probability, and the failures add. -/
theorem prob_and_ge {m : ℕ} {P Q : Cube m → Prop} {p q : ℝ}
    (hP : 1 - p ≤ Pr[P]) (hQ : 1 - q ≤ Pr[Q]) :
    1 - (p + q) ≤ Pr[fun z => P z ∧ Q z] := by
  classical
  have hcP := BooleanAnalysis.Internal.prob_compl P
  have hcQ := BooleanAnalysis.Internal.prob_compl Q
  have hcPQ := BooleanAnalysis.Internal.prob_compl fun z => P z ∧ Q z
  have hunion := BooleanAnalysis.Internal.prob_union_bound
    (P := fun z => P z ∧ Q z) (Q := fun z => ¬ P z) (R := fun z => ¬ Q z)
    fun z hz => by
      by_cases hp : P z
      · exact Or.inr fun hq => hz ⟨hp, hq⟩
      · exact Or.inl hp
  linarith

/-- **A likely event happens.** Used to turn a probabilistic guarantee about a
tester's reads into a single random string on which every read is right — the
argument for a check whose conclusion is deterministic. -/
theorem exists_of_prob_pos {m : ℕ} {P : Cube m → Prop} (h : 0 < Pr[P]) : ∃ z, P z := by
  classical
  by_contra hcon
  push Not at hcon
  have hzero : Pr[P] = 0 := by
    rw [BooleanAnalysis.prob, expect_unfold]
    have hind : ∀ z : Cube m, indicator P z = 0 := fun z => by
      simp [indicator, hcon z]
    rw [Finset.sum_congr rfl fun z _ => hind z]
    simp
  linarith

/-- A probability is a count over the cube. -/
theorem prob_eq_card_div {m : ℕ} (P : Cube m → Prop) [DecidablePred P] :
    Pr[P] = ((Finset.univ.filter P).card : ℝ) / 2 ^ m := by
  classical
  rw [BooleanAnalysis.prob, expect_unfold]
  have h : ∑ z : Cube m, indicator P z = ((Finset.univ.filter P).card : ℝ) := by
    rw [Finset.card_filter]
    push_cast
    exact Finset.sum_congr rfl fun z _ => by
      simp only [indicator]
      split_ifs <;> rfl
  rw [h]
  ring

end Complexity
