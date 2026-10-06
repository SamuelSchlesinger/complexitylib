/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Complexitylib.Circuits.Frontier.Signals
public import Complexitylib.Mathlib.Frontier.SetCard

/-!
# Mixed input-output fibers

For an arbitrary map, specify some input coordinates and some output coordinates. The
largest remaining fiber measures ambiguity in this mixed observation. Equal frontier
values permit two complementary splices, embedding each frontier class in the product of
two mixed fibers. No linearity or algebra on the alphabet is needed.
-/

@[expose] public section

namespace Complexity.Frontier

open Set

variable {ι O U M : Type*}

/-- Inputs indistinguishable from `x` after observing the inputs in `X` and outputs in `Y`. -/
def mixedFiber (F : (ι → U) → (O → U)) (X : Set ι) (Y : Set O) (x : ι → U) :
    Set (ι → U) := {z | EqOn z x X ∧ EqOn (F z) (F x) Y}

/-- Largest nonempty fiber of a mixed input-output observation. Empty fibers do not affect
the maximum; indexing by an input therefore includes every relevant observation. -/
noncomputable def maxMixedFiber [Finite ι] [Finite U]
    (F : (ι → U) → (O → U)) (X : Set ι) (Y : Set O) : ℕ := by
  let := Fintype.ofFinite (ι → U)
  exact Finset.univ.sup fun x => (mixedFiber F X Y x).ncard

theorem ncard_mixedFiber_le [Finite ι] [Finite U]
    (F : (ι → U) → (O → U)) (X : Set ι) (Y : Set O) (x : ι → U) :
    (mixedFiber F X Y x).ncard ≤ maxMixedFiber F X Y := by
  classical
  let := Fintype.ofFinite (ι → U)
  exact Finset.le_sup (f := fun x => (mixedFiber F X Y x).ncard) (Finset.mem_univ x)

/-- A boundary code permits splicing the inputs on `X` while preserving the corresponding
outputs on `Y`. This is an observational property, not a causal evaluation order. -/
def OutputSplicing (F : (ι → U) → (O → U)) (X : Set ι) (Y : Set O)
    (message : (ι → U) → M) : Prop :=
  ∀ x y, message x = message y → ∀ z, EqOn z x X → EqOn z y Xᶜ →
    EqOn (F z) (F x) Y ∧ EqOn (F z) (F y) Yᶜ

namespace OutputSplicing

variable [Finite ι] [Finite U] {F : (ι → U) → (O → U)} {X : Set ι} {Y : Set O}
  {message : (ι → U) → M} (h : OutputSplicing F X Y message)

include h

/-- A message class embeds in the product of two complementary mixed fibers. -/
theorem ncard_class_le (x : ι → U) :
    {y | message y = message x}.ncard ≤
      (mixedFiber F X Y x).ncard * (mixedFiber F Xᶜ Yᶜ x).ncard := by
  classical
  rw [← ncard_prod]
  refine ncard_le_ncard_of_injOn
    (fun y => (X.piecewise x y, X.piecewise y x)) ?_ ?_
  · intro y hy
    have hxy := h x y hy.symm _ (X.piecewise_eqOn x y) (X.piecewise_eqOn_compl x y)
    have hyx := h y x hy _ (X.piecewise_eqOn y x) (X.piecewise_eqOn_compl y x)
    exact ⟨⟨X.piecewise_eqOn x y, hxy.1⟩, ⟨X.piecewise_eqOn_compl y x, hyx.2⟩⟩
  · intro y _ z _ he
    have he := Prod.mk.inj he
    funext i
    by_cases hi : i ∈ X
    · simpa [hi] using congrFun he.2 i
    · simpa [hi] using congrFun he.1 i

/-- **Mixed-fiber demand**, in cardinal form. The number of used messages, multiplied by
the two largest complementary fibers, must cover all inputs. -/
theorem card_le :
    Nat.card U ^ Nat.card ι ≤ (Set.range message).ncard *
      (maxMixedFiber F X Y * maxMixedFiber F Xᶜ Yᶜ) := by
  have hf (m : M) : ((univ : Set (ι → U)) ∩ message ⁻¹' {m}).ncard ≤
      maxMixedFiber F X Y * maxMixedFiber F Xᶜ Yᶜ := by
    rcases ((univ : Set (ι → U)) ∩ message ⁻¹' {m}).eq_empty_or_nonempty with he | ⟨x, hx⟩
    · simp [he]
    · have he : ((univ : Set (ι → U)) ∩ message ⁻¹' {m}) =
          {y | message y = message x} := by
        ext y
        simp only [mem_inter_iff, mem_univ, mem_preimage, mem_singleton_iff, true_and,
          mem_ofPred_eq]
        rw [hx.2]
      rw [he]
      exact (h.ncard_class_le x).trans
        (Nat.mul_le_mul (ncard_mixedFiber_le F X Y x) (ncard_mixedFiber_le F Xᶜ Yᶜ x))
  have H := ncard_le_mul_ncard_image (toFinite (univ : Set (ι → U))) message _ hf
  simpa only [ncard_univ, Nat.card_fun, image_univ, Nat.mul_comm] using H

omit [Finite ι] [Finite U] in
/-- When both mixed observations are injective, the boundary code determines the input. -/
theorem injective (hX : ∀ x y, EqOn x y X → EqOn (F x) (F y) Y → x = y)
    (hY : ∀ x y, EqOn x y Xᶜ → EqOn (F x) (F y) Yᶜ → x = y) :
    Function.Injective message := by
  classical
  intro x y hxy
  let z := X.piecewise x y
  have hz := h x y hxy z (X.piecewise_eqOn x y) (X.piecewise_eqOn_compl x y)
  exact (hX z x (X.piecewise_eqOn x y) hz.1).symm.trans
    (hY z y (X.piecewise_eqOn_compl x y) hz.2)

end OutputSplicing

namespace Compiler

open Cslib.Circuits

variable {σ : Signature} {n s : ℕ} [Finite O] {p : Program σ n s} {out : O → Wire n s}
  (I : Interpretation σ U)

/-- The signals on a cut, counted once each regardless of copy multiplicity. -/
def cutSignals (P : Set (Vertex p out)) : Set (Signal p out) :=
  Edge.signal '' (network p out I fun _ => univ).cut P

/-- Distinct signal values on a compiled cut satisfy the mixed-output splicing interface. -/
theorem outputSplicing (P : Set (Vertex p out)) :
    OutputSplicing (fun x o => p.trace I x (out o))
      ((network p out I fun _ => univ).readIn P) {o | Vertex.output o ∈ P}
      (fun (x : Fin n → U) (w : cutSignals I P) => p.trace I x w.1.1) := by
  intro x y hxy z hzx hzy
  have hcut : ∀ e ∈ (network p out I fun _ => univ).cut P,
      p.trace I x e.signal.1 = p.trace I y e.signal.1 :=
    fun e he => congrFun hxy ⟨e.signal, ⟨e, he, rfl⟩⟩
  have H := trace_out_of_cut I hcut hzx hzy
  exact ⟨fun o ho => (H o).1 ho, fun o ho => (H o).2 ho⟩

/-- **Pointwise frontier demand for arbitrary maps.** This bounds every cut by its mixed
input-output ambiguity. Taking logarithms gives the additive demand formulation. -/
theorem pow_le_cutSignals_mul_fibers [Finite U] (P : Set (Vertex p out)) :
    Nat.card U ^ n ≤ Nat.card U ^ (cutSignals I P).ncard *
      (maxMixedFiber (fun x o => p.trace I x (out o))
        ((network p out I fun _ => univ).readIn P) {o | Vertex.output o ∈ P} *
      maxMixedFiber (fun x o => p.trace I x (out o))
        ((network p out I fun _ => univ).readIn P)ᶜ {o | Vertex.output o ∈ P}ᶜ) := by
  have H := (outputSplicing I P).card_le
  rw [Nat.card_eq_fintype_card (α := Fin n), Fintype.card_fin] at H
  refine H.trans (Nat.mul_le_mul_right _ ?_)
  calc (range (fun (x : Fin n → U) (w : cutSignals I P) => p.trace I x w.1.1)).ncard
      ≤ Nat.card (cutSignals I P → U) := ncard_le_card _
    _ = Nat.card U ^ (cutSignals I P).ncard := by rw [Nat.card_fun, Nat.card_coe_set_eq]

end Compiler

end Complexity.Frontier
