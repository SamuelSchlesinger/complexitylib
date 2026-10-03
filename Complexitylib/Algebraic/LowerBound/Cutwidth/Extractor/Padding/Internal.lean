/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Padding.Defs
public import Complexitylib.Classes.P.StringAccess
public import Complexitylib.Circuits.BitString
import Complexitylib.Classes.P
import Complexitylib.Classes.P.Bridge

/-!
# Proofs for balanced padding

Fixing the fresh coordinate loses at most a factor two in source support.
The resulting padding has exact balance and preserves polynomial-time evaluation.
-/

public section

namespace Algebraic.Cutwidth.Extractor.Internal

open scoped Classical

/-- Tail strings in a fixed first-bit fibre of a source. -/
noncomputable def tailFiber {n : Nat} (P : Finset (Fin (n + 1) → Bool)) (b : Bool) :
    Finset (Fin n → Bool) :=
  (P.filter fun x => x 0 = b).image Fin.tail

theorem card_tailFiber {n : Nat} (P : Finset (Fin (n + 1) → Bool)) (b : Bool) :
    (tailFiber P b).card = (P.filter fun x => x 0 = b).card := by
  apply Finset.card_image_of_injOn
  intro x hx y hy htail
  have hhead : x 0 = y 0 :=
    (Finset.mem_filter.mp hx).2.trans (Finset.mem_filter.mp hy).2.symm
  rw [← Fin.cons_self_tail x, ← Fin.cons_self_tail y, hhead, htail]

theorem card_tailFiber_add {n : Nat} (P : Finset (Fin (n + 1) → Bool)) :
    (tailFiber P false).card + (tailFiber P true).card = P.card := by
  rw [card_tailFiber, card_tailFiber]
  have heq : P.filter (fun x => x 0 = true) = P.filter (fun x => ¬ x 0 = false) := by
    ext x
    cases x 0 <;> simp
  rw [heq]
  exact Finset.card_filter_add_card_filter_not _

theorem exists_large_tailFiber {n K : Nat} {P : Finset (Fin (n + 1) → Bool)}
    (hP : 2 * K ≤ P.card) : ∃ b, K ≤ (tailFiber P b).card := by
  have h := card_tailFiber_add P
  by_cases hf : K ≤ (tailFiber P false).card
  · exact ⟨false, hf⟩
  · exact ⟨true, by lia⟩

theorem exists_mem_of_mem_tailFiber {n : Nat} {P : Finset (Fin (n + 1) → Bool)}
    {b : Bool} {x : Fin n → Bool} (hx : x ∈ tailFiber P b) :
    ∃ z ∈ P, z 0 = b ∧ Fin.tail z = x := by
  obtain ⟨z, hz, hzx⟩ := Finset.mem_image.mp hx
  exact ⟨z, (Finset.mem_filter.mp hz).1, (Finset.mem_filter.mp hz).2, hzx⟩

private def padLeft {n : Nat} (U : Finset (Fin n)) : (U → Bool) ↪ (Fin n → Bool) where
  toFun p := glue U p (fun _ => false)
  inj' := by
    intro p p' h
    funext i
    simpa using congrFun h i

private def padRight {n : Nat} (U : Finset (Fin n)) : (↥Uᶜ → Bool) ↪ (Fin n → Bool) where
  toFun q := glue U (fun _ => false) q
  inj' := by
    intro q q' h
    funext i
    simpa using congrFun h i

private theorem xor_pad {n : Nat} (U : Finset (Fin n))
    (p : U → Bool) (q : ↥Uᶜ → Bool) :
    xorInput (padLeft U p) (padRight U q) = glue U p q := by
  funext i
  change Bool.xor (glue U p (fun _ => false) i)
    (glue U (fun _ => false) q i) = glue U p q i
  by_cases hi : i ∈ U <;> simp [glue, hi]

theorem rectangleFree_of_flatSumsetDisperser {n K : Nat} {f : Cslib.BooleanFunction n}
    (disperse : FlatSumsetDisperser f K) : RectangleFree f K := by
  intro U P Q hones
  by_contra hsmall
  push Not at hsmall
  obtain ⟨x, hx, y, hy, hzero⟩ := disperse
    (P.map (padLeft U)) (Q.map (padRight U))
    (by simpa using hsmall.1) (by simpa using hsmall.2) false
  obtain ⟨p, hp, rfl⟩ := Finset.mem_map.mp hx
  obtain ⟨q, hq, rfl⟩ := Finset.mem_map.mp hy
  rw [xor_pad, hones p hp q hq] at hzero
  contradiction


/-- Error strictly below one half guarantees both output values on every
large flat-source pair. -/
theorem flatSumsetExtractor_disperser {n K : Nat} {f : Cslib.BooleanFunction n} {ν : ℝ}
    (extract : FlatSumsetExtractor f K ν) (hK : 0 < K) (hν : ν < 1 / 2) :
    FlatSumsetDisperser f K := by
  intro P Q hP hQ b
  have hpos : (0 : ℝ) < P.card * Q.card := by
    exact_mod_cast Nat.mul_pos (hK.trans_le hP) (hK.trans_le hQ)
  have bounds := extract P Q hP hQ
  by_contra h
  push Not at h
  cases b with
  | false =>
    have heq : sumsetOnes f P Q = P ×ˢ Q := by
      apply Finset.filter_eq_self.mpr
      intro xy hxy
      have hb := h xy.1 (Finset.mem_product.mp hxy).1
        xy.2 (Finset.mem_product.mp hxy).2
      simpa using hb
    rw [heq, Finset.card_product] at bounds
    push_cast at bounds
    nlinarith
  | true =>
    have heq : sumsetOnes f P Q = ∅ := by
      apply Finset.filter_eq_empty_iff.mpr
      intro xy hxy
      exact h xy.1 (Finset.mem_product.mp hxy).1
        xy.2 (Finset.mem_product.mp hxy).2
    rw [heq, Finset.card_empty, Nat.cast_zero] at bounds
    nlinarith

/-- A two-sided sumset disperser remains one after balanced padding, with a
factor-two loss in support threshold. -/
theorem flatSumsetDisperser_balancePad {n K : Nat} {f : Cslib.BooleanFunction n}
    (disperse : FlatSumsetDisperser f K) : FlatSumsetDisperser (balancePad f) (2 * K) := by
  intro P Q hP hQ b
  obtain ⟨p, hp⟩ := exists_large_tailFiber hP
  obtain ⟨q, hq⟩ := exists_large_tailFiber hQ
  obtain ⟨x, hx, y, hy, hxy⟩ := disperse
    (tailFiber P p) (tailFiber Q q) hp hq (Bool.xor b (Bool.xor p q))
  obtain ⟨x', hx', hpx, rfl⟩ := exists_mem_of_mem_tailFiber hx
  obtain ⟨y', hy', hqy, rfl⟩ := exists_mem_of_mem_tailFiber hy
  refine ⟨x', hx', y', hy', ?_⟩
  change Bool.xor (f (xorInput (Fin.tail x') (Fin.tail y')))
    (Bool.xor (x' 0) (y' 0)) = b
  rw [hxy, hpx, hqy]
  cases b <;> cases p <;> cases q <;> rfl

/-- Dispersion excludes one-rectangles, without any accepting-density
assumption. -/
theorem flatSumsetDisperser_rectangleFree {n K : Nat} {f : Cslib.BooleanFunction n}
    (disperse : FlatSumsetDisperser f K) : RectangleFree f K :=
  rectangleFree_of_flatSumsetDisperser disperse

/-- Any extraction error strictly below one half yields a rectangle-free
balanced extension. -/
theorem flatSumsetExtractor_balancePad_rectangleFree
    {n K : Nat} {f : Cslib.BooleanFunction n} {ν : ℝ}
    (extract : FlatSumsetExtractor f K ν) (hK : 0 < K) (hν : ν < 1 / 2) :
    RectangleFree (balancePad f) (2 * K) :=
  flatSumsetDisperser_rectangleFree
    (flatSumsetDisperser_balancePad (flatSumsetExtractor_disperser extract hK hν))

/-- Exactly one fresh bit accepts for each old input, so balanced padding
accepts exactly half its input cube. -/
theorem card_accepting_balancePad {n : Nat} (f : Cslib.BooleanFunction n) :
    (accepting (balancePad f)).card = 2 ^ n := by
  have hcard : (Finset.univ : Finset (Fin n → Bool)).card =
      (accepting (balancePad f)).card := by
    apply Finset.card_bij (fun x _ => Fin.cons (!(f x)) x)
    · intro x _
      simp [accepting, balancePad]
    · intro x _ y _ h
      simpa using congrArg Fin.tail h
    · intro x hx
      refine ⟨Fin.tail x, Finset.mem_univ _, ?_⟩
      have hbit : (!(f (Fin.tail x))) = x 0 := by
        have hx' := mem_accepting.mp hx
        change Bool.xor (f (Fin.tail x)) (x 0) = true at hx'
        cases hf : f (Fin.tail x) <;> cases hb : x 0 <;> simp_all
      rw [hbit, Fin.cons_self_tail]
  simpa using hcard.symm

/-- The list evaluator agrees with the finite Boolean-function padding on
every positive input length. -/
theorem balancePadEval_toList {n : Nat} {f : Cslib.BooleanFunction n}
    {eval : List Bool → List Bool}
    (heval : ∀ x : Complexity.BitString n, eval x.toList = [f x])
    (x : Complexity.BitString (n + 1)) :
    balancePadEval eval x.toList = [balancePad f x] := by
  have htail : x.toList.tail = Complexity.BitString.toList (Fin.tail x) := by
    change (List.ofFn x).tail = List.ofFn (Fin.tail x)
    rw [List.ofFn_succ]
    rfl
  rw [balancePadEval, htail, heval]
  simp [balancePad, Complexity.BitString.toList, List.ofFn_succ]

/-- Balanced padding preserves a uniform polynomial-time evaluator. -/
theorem balancePadEval_mem_FP {eval : List Bool → List Bool} (heval : eval ∈ Complexity.FP) :
    balancePadEval eval ∈ Complexity.FP := by
  have htail : (fun x : List Bool => x.tail) ∈ Complexity.FP := by
    simpa [Complexity.dropOne] using Complexity.dropOneFn_mem_FP Complexity.id_mem_FP
  have hout := Complexity.FPPred.getBit (Complexity.mem_FP_comp htail heval)
    (Complexity.UnaryFn.const 0)
  have hin := Complexity.FPPred.getBit Complexity.id_mem_FP (Complexity.UnaryFn.const 0)
  have hxor := (hout.and hin.not).or (hout.not.and hin)
  apply Complexity.mem_FP_of_eq hxor.flag_mem_FP
  intro x
  simp only [balancePadEval]
  have head (z : List Bool) : z[0]?.getD false = z.headD false := by cases z <;> rfl
  simp only [head, Function.comp_apply, id_eq]
  cases (eval x.tail).headD false <;> cases x.headD false <;> rfl

end Algebraic.Cutwidth.Extractor.Internal
