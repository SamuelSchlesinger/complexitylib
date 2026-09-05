/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/
module
public import Complexitylib.Classes.PCP.Internal.Expander
public import Complexitylib.Classes.PCP.Internal.Mixing
public import Mathlib.Analysis.Real.Sqrt

/-!
# Relabelling darts and padding with loops

Two bookkeeping operations on regular graphs, both preserving the spectral
bound in an explicit way.

* **Relabelling** the dart type along an equivalence. Constructions produce
  structured dart types — pairs, functions, sums — while `ExpanderFamily`
  wants `Fin degree`. The step operator is unchanged, so the bound is.

* **Padding** with self-loops, to raise the degree of a graph to a prescribed
  value. The new step is a convex combination of the old step and the identity,
  so by Jensen the bound becomes `μ² = α λ² + (1 - α)` with `α` the fraction of
  real darts.

## Main definitions

- `Complexity.RegGraph.relabel` — the same graph with darts renamed
- `Complexity.RegGraph.padLoops` — the graph with `k` self-loops added at every
  vertex

## Main results

- `Complexity.RegGraph.spectralBound_relabel`
- `Complexity.RegGraph.spectralBound_padLoops`
- `Complexity.RegGraph.relabelV`, `Complexity.RegGraph.spectralBound_relabelV` —
  renaming vertices
- `Complexity.RegGraph.toFinForm` — the same graph with both types numbered
-/

@[expose] public section

namespace Complexity

namespace RegGraph

variable (G : RegGraph)

/-! ### Relabelling -/

/-- The same graph with its darts renamed along `e`. -/
def relabel {D' : Type} [DecidableEq D'] [Fintype D'] (e : G.D ≃ D') : RegGraph where
  V := G.V
  D := D'
  decEqV := G.decEqV
  decEqD := inferInstance
  fintypeV := G.fintypeV
  fintypeD := inferInstance
  nonemptyD := ⟨e (Classical.arbitrary G.D)⟩
  rot := fun p => ((G.rot (p.1, e.symm p.2)).1, e (G.rot (p.1, e.symm p.2)).2)
  rot_involutive := by
    intro p
    simp only [Equiv.symm_apply_apply]
    have h := G.rot_involutive (p.1, e.symm p.2)
    rw [show (G.rot (p.1, e.symm p.2)).1 = (G.rot (p.1, e.symm p.2)).1 from rfl]
    conv_lhs => rw [show ((G.rot (p.1, e.symm p.2)).1, (G.rot (p.1, e.symm p.2)).2)
      = G.rot (p.1, e.symm p.2) from rfl]
    rw [h]
    simp

@[simp] theorem order_relabel {D' : Type} [DecidableEq D'] [Fintype D'] (e : G.D ≃ D') :
    (G.relabel e).order = G.order := rfl

theorem deg_relabel {D' : Type} [DecidableEq D'] [Fintype D'] (e : G.D ≃ D') :
    (G.relabel e).deg = G.deg := by
  show Fintype.card D' = Fintype.card G.D
  exact (Fintype.card_congr e).symm

theorem step_relabel {D' : Type} [DecidableEq D'] [Fintype D'] (e : G.D ≃ D') (f : G.V → ℝ)
    (v : G.V) : (G.relabel e).step f v = G.step f v := by
  simp only [step, deg_relabel]
  congr 1
  show ∑ i : D', f (G.rot (v, e.symm i)).1 = ∑ i : G.D, f (G.rot (v, i)).1
  exact Fintype.sum_equiv e.symm _ _ fun i => rfl

theorem spectralBound_relabel {D' : Type} [DecidableEq D'] [Fintype D'] (e : G.D ≃ D')
    {lam : ℝ} (h : G.SpectralBound lam) : (G.relabel e).SpectralBound lam := by
  intro f hf
  have := h f hf
  have hs : ∀ v, (G.relabel e).step f v = G.step f v := fun v => step_relabel G e f v
  simp only [hs]
  exact this

/-! ### Padding with loops -/

/-- The graph with `k` self-loops added at every vertex. -/
def padLoops (k : ℕ) : RegGraph where
  V := G.V
  D := G.D ⊕ Fin k
  decEqV := G.decEqV
  decEqD := inferInstance
  fintypeV := G.fintypeV
  fintypeD := inferInstance
  nonemptyD := ⟨Sum.inl (Classical.arbitrary G.D)⟩
  rot := fun p =>
    match p.2 with
    | Sum.inl i => ((G.rot (p.1, i)).1, Sum.inl (G.rot (p.1, i)).2)
    | Sum.inr j => (p.1, Sum.inr j)
  rot_involutive := by
    intro p
    obtain ⟨v, i | j⟩ := p
    · simp only
      have h := G.rot_involutive (v, i)
      conv_lhs => rw [show ((G.rot (v, i)).1, (G.rot (v, i)).2) = G.rot (v, i) from rfl]
      rw [h]
    · rfl

@[simp] theorem order_padLoops (k : ℕ) : (G.padLoops k).order = G.order := rfl

theorem deg_padLoops (k : ℕ) : (G.padLoops k).deg = G.deg + k := by
  show Fintype.card (G.D ⊕ Fin k) = _
  rw [Fintype.card_sum, Fintype.card_fin]
  rfl

theorem step_padLoops (k : ℕ) (f : G.V → ℝ) (v : G.V) :
    (G.padLoops k).step f v
      = ((G.deg : ℝ) * G.step f v + (k : ℝ) * f v) / ((G.deg : ℝ) + k) := by
  have hd : (G.deg : ℝ) ≠ 0 := G.deg_ne_zero
  unfold step; erw [deg_padLoops]
  show (∑ i : G.D ⊕ Fin k, f ((G.padLoops k).nbr v i)) / ((G.deg + k : ℕ) : ℝ) = _
  rw [Fintype.sum_sum_type]
  have h1 : ∀ i : G.D, (G.padLoops k).nbr v (Sum.inl i) = G.nbr v i := fun i => rfl
  have h2 : ∀ j : Fin k, (G.padLoops k).nbr v (Sum.inr j) = v := fun j => rfl
  simp only [h1, h2, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  push_cast
  congr 1
  rw [mul_div_cancel₀ _ hd]

/-- **Padding keeps the bound**, with `μ² = α λ² + (1 - α)` for `α` the fraction of
real darts. -/
theorem spectralBound_padLoops (k : ℕ) {lam : ℝ} (h : G.SpectralBound lam) :
    (G.padLoops k).SpectralBound
      (Real.sqrt (((G.deg : ℝ) * lam ^ 2 + k) / ((G.deg : ℝ) + k))) := by
  intro f hf
  have hspec := h f hf
  have hd : (0 : ℝ) < G.deg := by exact_mod_cast G.deg_pos
  have hD : (0 : ℝ) < (G.deg : ℝ) + k := by positivity
  rw [Real.sq_sqrt (by positivity)]
  set a : ℝ := (G.deg : ℝ) / ((G.deg : ℝ) + k) with ha
  have ha0 : 0 ≤ a := by positivity
  have ha1 : a ≤ 1 := by rw [ha, div_le_one hD]; linarith
  have hb : (k : ℝ) / ((G.deg : ℝ) + k) = 1 - a := by
    rw [ha]; field_simp; ring
  -- Jensen for two terms
  have hpt : ∀ v, ((G.padLoops k).step f v) ^ 2 ≤ a * (G.step f v) ^ 2 + (1 - a) * (f v) ^ 2 := by
    intro v
    erw [step_padLoops]
    have hrw : ((G.deg : ℝ) * G.step f v + (k : ℝ) * f v) / ((G.deg : ℝ) + k)
        = a * G.step f v + (1 - a) * f v := by
      rw [← hb, ha]; field_simp
    rw [hrw]
    nlinarith [mul_nonneg ha0 (sub_nonneg.2 ha1), sq_nonneg (G.step f v - f v)]
  have hsum : ∑ v : G.V, ((G.padLoops k).step f v) ^ 2
      ≤ a * ∑ v : G.V, (G.step f v) ^ 2 + (1 - a) * ∑ v : G.V, (f v) ^ 2 := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_le_sum fun v _ => hpt v
  have hcoef : ((G.deg : ℝ) * lam ^ 2 + k) / ((G.deg : ℝ) + k) = a * lam ^ 2 + (1 - a) := by
    rw [← hb, ha]; field_simp
  rw [hcoef]
  show ∑ v : G.V, ((G.padLoops k).step f v) ^ 2 ≤ (a * lam ^ 2 + (1 - a)) * ∑ v : G.V, (f v) ^ 2
  nlinarith [hsum, mul_le_mul_of_nonneg_left hspec ha0]

/-! ### Renaming vertices -/

/-- The same graph with its vertices renamed along `e`. Constructions produce
structured vertex types — products, sums — while a family wants `Fin n`. -/
def relabelV {V' : Type} [DecidableEq V'] [Fintype V'] (e : G.V ≃ V') : RegGraph where
  V := V'
  D := G.D
  decEqV := inferInstance
  decEqD := G.decEqD
  fintypeV := inferInstance
  fintypeD := G.fintypeD
  nonemptyD := G.nonemptyD
  rot := fun p => (e (G.rot (e.symm p.1, p.2)).1, (G.rot (e.symm p.1, p.2)).2)
  rot_involutive := by
    intro p
    obtain ⟨v, i⟩ := p
    simp only [Equiv.symm_apply_apply]
    have h := G.rot_involutive (e.symm v, i)
    conv_lhs => rw [show ((G.rot (e.symm v, i)).1, (G.rot (e.symm v, i)).2)
      = G.rot (e.symm v, i) from rfl]
    rw [h]
    simp

@[simp] theorem deg_relabelV {V' : Type} [DecidableEq V'] [Fintype V'] (e : G.V ≃ V') :
    (G.relabelV e).deg = G.deg := rfl

theorem order_relabelV {V' : Type} [DecidableEq V'] [Fintype V'] (e : G.V ≃ V') :
    (G.relabelV e).order = G.order := (Fintype.card_congr e).symm

theorem step_relabelV {V' : Type} [DecidableEq V'] [Fintype V'] (e : G.V ≃ V')
    (f : V' → ℝ) (v : V') :
    (G.relabelV e).step f v = G.step (fun w => f (e w)) (e.symm v) := by
  simp only [step, deg_relabelV]
  congr 1

theorem spectralBound_relabelV {V' : Type} [DecidableEq V'] [Fintype V'] (e : G.V ≃ V')
    {lam : ℝ} (h : G.SpectralBound lam) : (G.relabelV e).SpectralBound lam := by
  intro f hf
  have hf' : ∑ w : G.V, f (e w) = 0 := by
    rw [Fintype.sum_equiv e (fun w => f (e w)) f fun w => rfl]
    exact hf
  have hb := h (fun w => f (e w)) hf'
  calc ∑ v : V', ((G.relabelV e).step f v) ^ 2
      = ∑ w : G.V, (G.step (fun w => f (e w)) w) ^ 2 :=
        (Fintype.sum_equiv e (fun w => (G.step (fun w => f (e w)) w) ^ 2)
          (fun v => ((G.relabelV e).step f v) ^ 2) fun w => by
            show (G.step (fun w => f (e w)) w) ^ 2 = ((G.relabelV e).step f (e w)) ^ 2
            rw [step_relabelV (G := G) (e := e) (f := f) (v := e w), Equiv.symm_apply_apply]).symm
    _ ≤ lam ^ 2 * ∑ w : G.V, (f (e w)) ^ 2 := hb
    _ = lam ^ 2 * ∑ v : V', (f v) ^ 2 := by
        congr 1
        exact Fintype.sum_equiv e (fun w => (f (e w)) ^ 2) (fun v => (f v) ^ 2) fun w => rfl

/-! ### Numbering both types -/

/-- The same graph with its vertices numbered `Fin order` and its darts
`Fin deg`. Constructions build structured types; the merge and the expander
families want numbered ones. -/
noncomputable def toFinForm : RegGraph :=
  (G.relabelV (Fintype.equivFin G.V)).relabel (Fintype.equivFin G.D)

@[simp] theorem order_toFinForm : G.toFinForm.order = G.order := by
  unfold toFinForm; erw [ order_relabel, order_relabelV]

@[simp] theorem deg_toFinForm : G.toFinForm.deg = G.deg := by
  unfold toFinForm; erw [ deg_relabel, deg_relabelV]

theorem spectralBound_toFinForm {lam : ℝ} (h : G.SpectralBound lam) :
    G.toFinForm.SpectralBound lam :=
  spectralBound_relabel _ _ (spectralBound_relabelV G (Fintype.equivFin G.V) h)

/-- The same graph numbered at sizes supplied by the caller, so that the
rotation map has the literal type `Fin N × Fin d → Fin N × Fin d` a numeric
construction expects, with no transport at the use site. -/
noncomputable def toFinFormOf (N d : ℕ) (hN : Fintype.card G.V = N)
    (hd : Fintype.card G.D = d) : RegGraph :=
  (G.relabelV ((Fintype.equivFin G.V).trans (finCongr hN))).relabel
    ((Fintype.equivFin G.D).trans (finCongr hd))

theorem toFinFormOf_V (N d : ℕ) (hN : Fintype.card G.V = N) (hd : Fintype.card G.D = d) :
    (G.toFinFormOf N d hN hd).V = Fin N := rfl

theorem toFinFormOf_D (N d : ℕ) (hN : Fintype.card G.V = N) (hd : Fintype.card G.D = d) :
    (G.toFinFormOf N d hN hd).D = Fin d := rfl

@[simp] theorem order_toFinFormOf (N d : ℕ) (hN : Fintype.card G.V = N)
    (hd : Fintype.card G.D = d) : (G.toFinFormOf N d hN hd).order = N := Fintype.card_fin N

@[simp] theorem deg_toFinFormOf (N d : ℕ) (hN : Fintype.card G.V = N)
    (hd : Fintype.card G.D = d) : (G.toFinFormOf N d hN hd).deg = d := Fintype.card_fin d

theorem spectralBound_toFinFormOf (N d : ℕ) (hN : Fintype.card G.V = N)
    (hd : Fintype.card G.D = d) {lam : ℝ} (h : G.SpectralBound lam) :
    (G.toFinFormOf N d hN hd).SpectralBound lam :=
  spectralBound_relabel _ _ (spectralBound_relabelV G _ h)

/-- Its vertices are literally numbered. -/
theorem toFinForm_V : G.toFinForm.V = Fin (Fintype.card G.V) := rfl

/-- And so are its darts. -/
theorem toFinForm_D : G.toFinForm.D = Fin (Fintype.card G.D) := rfl

end RegGraph

end Complexity
