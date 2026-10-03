/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Block
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Block.Splitting.Iterated.Defs
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Block.Splitting
import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Block.Splitting.Iterated.Internal
import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Block.Splitting.Iterated.Internal.Tuples

/-!
# Splitting every block into successive halves

A source on `t` pairs, with each pair having conditional point-mass cap
`2^(-k)` after all earlier pairs, becomes close to a source on `2*t`
successive half-blocks. If each half has `2^m` possible values,
`s ≤ m` and `m+s+e ≤ k` give output threshold `2^s` and distance at most
`t*2^(-e)`. The pairs can be dependent. Splitting uses no new random seed.

This is the finite power-of-two form of Chattopadhyay--Goodman--Liao,
Corollary 5.4 of *Affine Extractors for Almost Logarithmic Entropy*:
<https://eccc.weizmann.ac.il/report/2021/075/download/>. Their two-block
ingredient, Lemma 5.3, credits Goldreich--Wigderson (1997). Our proof uses
the explicit row repair and its preservation of the original joint cap,
followed by correlated head replacement and induction on conditional tails.

This statistical theorem supplies the splitting step of the recursive
extractor; the full recursive program and its parameter accounting are
separate constructions.
-/

public section

namespace Algebraic.Cutwidth.Extractor

/-- The first coordinate of a pair is retained at the pair's first output position. -/
theorem splitBlockEquiv_apply_fst {α : Type*} {t : Nat}
    (x : Fin t → α × α) (i : Fin t) :
    splitBlockEquiv α t x (splitBlockIndexEquiv t (i, 0)) = (x i).1 :=
  Internal.splitBlockEquiv_apply_fst x i

/-- The second coordinate immediately follows the first coordinate of its pair. -/
theorem splitBlockEquiv_apply_snd {α : Type*} {t : Nat}
    (x : Fin t → α × α) (i : Fin t) :
    splitBlockEquiv α t x (splitBlockIndexEquiv t (i, 1)) = (x i).2 :=
  Internal.splitBlockEquiv_apply_snd x i

/-- Split each conditional high-entropy pair into two consecutive blocks,
paying at most `2^(-e)` per original pair. No independence between pairs is needed. -/
theorem IsBlockSource.exists_split_pow_two {α : Type*} [Fintype α]
    {t m s k e : Nat} {p : (Fin t → α × α) → ℝ}
    (source : IsBlockSource p (2 ^ k)) (card : Fintype.card α = 2 ^ m)
    (width : s ≤ m) (entropy : m + s + e ≤ k) :
    ∃ q : (Fin (2 * t) → α) → ℝ, IsBlockSource q (2 ^ s) ∧
      weightDist (mapWeight (splitBlockEquiv α t) p) q ≤
        (t : ℝ) * ((2 : ℝ) ^ e)⁻¹ := by
  apply Internal.blockSource_split (2 ^ k) (2 ^ s) ((2 : ℝ) ^ e)⁻¹ _ source
  intro w hw cap
  obtain ⟨v, hv, vcap, vsource, _, error⟩ :=
    exists_twoBlock_repair_pow_two_capped w hw card cap width entropy
  exact ⟨v, hv, vcap, vsource, error⟩

end Algebraic.Cutwidth.Extractor
