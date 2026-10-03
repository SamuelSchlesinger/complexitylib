/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.CorrelationBreaker.Advice.Truncation.Defs
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Conditional.Defs
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Probability
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Conditional
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.LookAhead.UniformState
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Transcript
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity

/-!
# Balanced-prefix transport of the retained advice law

On valid widths the total prefix map takes uniform Boolean words to
uniform Boolean words. Existing balanced-state transport first contracts
the honest-output discrepancy; forgetting the unused tampered coordinates
then contracts the retained side information. Neither contraction requires
nonnegative or normalized input weights.
-/

public section

namespace Algebraic.Cutwidth.Extractor.Internal

theorem adviceOutputPrefix_eq_of_le {out d : Nat} (size : out ≤ d)
    (bits : Fin d → Bool) :
    adviceOutputPrefix out bits = fun i => bits (Fin.castLE size i) := by
  funext i
  have bound : i.val < (List.ofFn bits).length := by
    simpa only [List.length_ofFn] using lt_of_lt_of_le i.isLt size
  simp only [adviceOutputPrefix, List.getElem?_eq_getElem bound, List.getElem_ofFn,
    Option.getD_some]
  rfl

theorem adviceOutputPrefix_self {d : Nat} (bits : Fin d → Bool) :
    adviceOutputPrefix d bits = bits :=
  adviceOutputPrefix_eq_of_le le_rfl bits

theorem adviceOutputPrefix_apply_of_ge {out d : Nat} (bits : Fin d → Bool)
    (i : Fin out) (outside : d ≤ i.val) : adviceOutputPrefix out bits i = false := by
  have bound : (List.ofFn bits).length ≤ i.val := by
    simpa only [List.length_ofFn] using outside
  simp only [adviceOutputPrefix, List.getElem?_eq_none bound, Option.getD_none]

private def outputSplit (d r : Nat) :
    (Fin (d + r) → Bool) ≃ (Fin d → Bool) × (Fin r → Bool) :=
  ((finSumFinEquiv : Fin d ⊕ Fin r ≃ Fin (d + r)).symm.arrowCongr
    (Equiv.refl Bool)).trans (Equiv.sumArrowEquivProdArrow _ _ _)

private theorem outputPrefix_uniform (d r : Nat) :
    mapWeight (fun q : Fin (d + r) → Bool => fun i : Fin d => q (Fin.castAdd r i))
      (uniformWeight (Fin (d + r) → Bool)) = uniformWeight (Fin d → Bool) := by
  have split : mapWeight (outputSplit d r) (uniformWeight (Fin (d + r) → Bool)) =
      uniformWeight ((Fin d → Bool) × (Fin r → Bool)) := by
    funext y
    rw [mapWeight_equiv_apply]
    unfold uniformWeight
    rw [Fintype.card_congr (outputSplit d r)]
  have first := congrArg (mapWeight Prod.fst) split
  rw [mapWeight_comp] at first
  change mapWeight (fun q : Fin (d + r) → Bool => fun i : Fin d => q (Fin.castAdd r i))
    (uniformWeight (Fin (d + r) → Bool)) = _ at first
  rw [first, mapWeight_fst]
  have positive : (Fintype.card (Fin r → Bool) : ℝ) ≠ 0 := by positivity
  funext y
  simp only [firstWeight, uniformWeight, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul, Fintype.card_prod, Nat.cast_mul]
  field_simp

theorem adviceOutputPrefix_uniform {out d : Nat} (size : out ≤ d) :
    mapWeight (adviceOutputPrefix out) (uniformWeight (Fin d → Bool)) =
      uniformWeight (Fin out → Bool) := by
  have eq : adviceOutputPrefix out =
      fun bits : Fin d → Bool => fun i => bits (Fin.castLE size i) :=
    funext (adviceOutputPrefix_eq_of_le size)
  rw [eq]
  obtain ⟨r, rfl⟩ := Nat.exists_eq_add_of_le size
  exact outputPrefix_uniform _ r

private theorem balanced_output_dist_le {Tag Q Out : Type*}
    [Fintype Tag] [Fintype Q] [Fintype Out]
    (p : Tag × Q → ℝ) (f : Q → Out)
    (balanced : mapWeight f (uniformWeight Q) = uniformWeight Out) :
    weightDist (mapWeight (fun a => (a.1, f a.2)) p)
      (uniformSecondWeight (mapWeight (fun a => (a.1, f a.2)) p)) ≤
        weightDist p (uniformSecondWeight p) := by
  have bound := retainedSeedWeight_image_dist_le (fun _ : Tag => (1 : ℝ))
    (fun t q => p (t, q)) (fun _ q => q) f balanced
  simp only [retainedSeedWeight, one_mul] at bound
  change weightDist (mapWeight (fun a => (a.1, f a.2)) p)
    (uniformSecondWeight (mapWeight (fun a => (a.1, f a.2)) p)) ≤
      weightDist (mapWeight id p) (uniformSecondWeight (mapWeight id p)) at bound
  rw [mapWeight_id] at bound
  exact bound

theorem adviceTruncatedCorrelationBreakerWeight_eq_map (n m L e out : Nat)
    {Z A B : Type*} [Fintype Z] [Fintype A] [Fintype B]
    (w : Z → ℝ) (l : Z → A → ℝ) (r : Z → B → ℝ)
    (x x' : Z → A → Fin n → Bool) (y y' : Z → B → Fin m → Bool)
    (advice advice' : List Bool) :
    adviceTruncatedCorrelationBreakerWeight n m L e out w l r x x' y y' advice advice' =
      mapWeight (fun p => ((p.1.1, adviceOutputPrefix out p.1.2), adviceOutputPrefix out p.2))
        (adviceCorrelationBreakerWeight n m L e w l r x x' y y' advice advice') := by
  rw [adviceTruncatedCorrelationBreakerWeight, adviceCorrelationBreakerWeight, mapWeight_comp]
  simp only [adviceTruncatedCorrelationBreaker]

theorem adviceTruncatedCorrelationBreakerWeight_probability (n m L e out : Nat)
    {Z A B : Type*} [Fintype Z] [Fintype A] [Fintype B]
    (w : Z → ℝ) (l : Z → A → ℝ) (r : Z → B → ℝ)
    (x x' : Z → A → Fin n → Bool) (y y' : Z → B → Fin m → Bool)
    (advice advice' : List Bool) (hw : IsProbabilityWeight w)
    (hl : ∀ z, IsProbabilityWeight (l z)) (hr : ∀ z, IsProbabilityWeight (r z)) :
    IsProbabilityWeight
      (adviceTruncatedCorrelationBreakerWeight n m L e out w l r x x' y y' advice advice') :=
  (factoredWeight_probability w l r hw hl hr).map _

theorem adviceTruncatedCorrelationBreakerWeight_dist_le (n m L e out : Nat)
    {Z A B : Type*} [Fintype Z] [Fintype A] [Fintype B]
    (w : Z → ℝ) (l : Z → A → ℝ) (r : Z → B → ℝ)
    (x x' : Z → A → Fin n → Bool) (y y' : Z → B → Fin m → Bool)
    (advice advice' : List Bool) (size : out ≤ matchedBlockSeedBits L) :
    weightDist (adviceTruncatedCorrelationBreakerWeight n m L e out
      w l r x x' y y' advice advice')
      (uniformSecondWeight (adviceTruncatedCorrelationBreakerWeight n m L e out
        w l r x x' y y' advice advice')) ≤
      weightDist (adviceCorrelationBreakerWeight n m L e w l r x x' y y' advice advice')
        (uniformSecondWeight
          (adviceCorrelationBreakerWeight n m L e w l r x x' y y' advice advice')) := by
  let p := adviceCorrelationBreakerWeight n m L e w l r x x' y y' advice advice'
  have honest := balanced_output_dist_le p (adviceOutputPrefix out)
    (adviceOutputPrefix_uniform size)
  have tampered := weightDist_uniformSecond_map_first_le
    (mapWeight (fun a => (a.1, adviceOutputPrefix out a.2)) p)
    (fun a => (a.1, adviceOutputPrefix out a.2))
  rw [mapWeight_comp] at tampered
  rw [adviceTruncatedCorrelationBreakerWeight_eq_map]
  exact tampered.trans honest

end Algebraic.Cutwidth.Extractor.Internal
