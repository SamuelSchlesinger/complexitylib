/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/
module
public import Complexitylib.Classes.PCP.Internal.RegCSP
public import Complexitylib.Classes.PCP.Internal.Union
public import Complexitylib.Classes.PCP.Internal.WalkPath

/-!
# Adding self-loops

Powering names a vertex within distance `k ≤ h` of `v` by a length-`h` walk that
takes `k` real steps and then stays put, so the graph it runs on must have a
self-loop at every vertex (`RegGraph.Loops`). This module adds them.

A self-loop at every vertex is itself a `RegGraph` — `loopGraph`, of degree one,
whose rotation map is the identity — so adding loops is just `union` with it,
and the spectral bound comes free from `spectralBound_union`: the loops
contribute their full weight `1` and the original graph its `lam`, giving
`(1 + deg · lam) / (1 + deg)`, still below one.

On the constraint side the loops carry the trivially true constraint. They are
never violated, so the number of broken darts is unchanged while the number of
darts grows by a factor `(deg + 1) / deg`; the value is scaled by exactly
`deg / (deg + 1)`, which `unsatFrac_addLoops` records.

## Main definitions

- `RegGraph.loopGraph` — one self-loop at every vertex
- `RegGraph.addLoops`, `RegGraph.addLoopsLoops` — the graph with loops, and its
  canonical `Loops`
- `RegCSP.addLoops` — the constraint system with loops

## Main results

- `RegGraph.deg_addLoops`, `RegGraph.spectralBound_addLoops`
- `RegCSP.unsatFrac_addLoops`, `unsatVal_addLoops` — the value scales by
  `deg / (deg + 1)`
- `RegCSP.satisfiable_addLoops_iff`
-/

@[expose] public section

namespace Complexity

namespace RegGraph

/-- The graph with exactly one self-loop at each vertex. -/
def loopGraph (V : Type) [DecidableEq V] [Fintype V] : RegGraph where
  V := V
  D := Unit
  decEqV := inferInstance
  decEqD := inferInstance
  fintypeV := inferInstance
  fintypeD := inferInstance
  nonemptyD := ⟨()⟩
  rot p := p
  rot_involutive _ := rfl

@[simp] theorem V_loopGraph (V : Type) [DecidableEq V] [Fintype V] :
    (loopGraph V).V = V := rfl

@[simp] theorem deg_loopGraph (V : Type) [DecidableEq V] [Fintype V] :
    (loopGraph V).deg = 1 := Fintype.card_unit

variable (G : RegGraph)

/-- `G` with a self-loop added at every vertex. -/
def addLoops : RegGraph := union (loopGraph G.V) G (Equiv.refl G.V)

@[simp] theorem V_addLoops : G.addLoops.V = G.V := rfl

@[simp] theorem order_addLoops : G.addLoops.order = G.order := rfl

@[simp] theorem deg_addLoops : G.addLoops.deg = 1 + G.deg := by
  rw [addLoops, deg_union (G := loopGraph G.V) (H := G) (e := Equiv.refl G.V),
    deg_loopGraph]

/-- The canonical self-loop at each vertex of `G.addLoops`. -/
def addLoopsLoops : G.addLoops.Loops where
  loop _ := Sum.inl ()
  rot_loop _ := rfl

/-- Adding loops keeps a spectral bound below one. -/
theorem spectralBound_addLoops {lam : ℝ} (hlam : 0 ≤ lam) (h : G.SpectralBound lam) :
    G.addLoops.SpectralBound ((1 + (G.deg : ℝ) * lam) / (1 + (G.deg : ℝ))) := by
  have hu := spectralBound_union (loopGraph G.V) G (Equiv.refl G.V) hlam h
  rw [deg_loopGraph] at hu
  exact_mod_cast hu

theorem addLoops_bound_lt_one {lam : ℝ} (hlam1 : lam < 1) :
    (1 + (G.deg : ℝ) * lam) / (1 + (G.deg : ℝ)) < 1 := by
  have hd : (0 : ℝ) < (G.deg : ℝ) := by have := G.deg_pos; positivity
  rw [div_lt_one (by positivity)]
  nlinarith

end RegGraph

namespace RegCSP

variable {α : Type} (R : RegCSP α)

/-- `R` with a trivially satisfied self-loop added at every vertex. -/
def addLoops : RegCSP α where
  graph := R.graph.addLoops
  rel v d a b :=
    match d with
    | Sum.inl _ => true
    | Sum.inr i => R.rel v i a b

@[simp] theorem graph_addLoops : R.addLoops.graph = R.graph.addLoops := rfl

/-- The broken darts are unchanged: only the original constraints can fail. -/
theorem card_unsatDarts_addLoops (a : R.Assignment) :
    (R.addLoops.unsatDarts a).card = (R.unsatDarts a).card := by
  classical
  refine (Finset.card_bij (fun q _ => ((q.1, Sum.inr q.2) : R.addLoops.Dart)) ?_ ?_ ?_).symm
  · intro q hq
    exact (mem_unsatDarts (R := R.addLoops)).mpr ((mem_unsatDarts (R := R)).mp hq)
  · intro q _ q' _ heq
    have h1 : q.1 = q'.1 := congrArg (fun r => (r.1 : R.graph.V)) heq
    have h2 : Sum.inr q.2 = (Sum.inr q'.2 : Unit ⊕ R.graph.D) :=
      congrArg (fun r => (r.2 : Unit ⊕ R.graph.D)) heq
    exact Prod.ext h1 (Sum.inr.inj h2)
  · rintro ⟨v, _ | i⟩ hq
    · exact absurd rfl ((mem_unsatDarts (R := R.addLoops)).mp hq)
    · refine ⟨(v, i), ?_, rfl⟩
      exact (mem_unsatDarts (R := R)).mpr ((mem_unsatDarts (R := R.addLoops)).mp hq)

/-- Adding loops scales the value by `deg / (deg + 1)`. -/
theorem unsatFrac_addLoops (a : R.Assignment) :
    R.addLoops.unsatFrac a
      = R.unsatFrac a * (R.graph.deg : ℚ) / ((R.graph.deg : ℚ) + 1) := by
  have hd : (0 : ℚ) < (R.graph.deg : ℚ) := by
    have := R.graph.deg_pos
    exact_mod_cast this
  have hcards := R.card_unsatDarts_addLoops a
  rcases Nat.eq_zero_or_pos R.graph.order with hz | hz
  · -- no vertices: no darts at all
    have hempty : (R.unsatDarts a).card = 0 := by
      have hle : (R.unsatDarts a).card ≤ R.graph.order * R.graph.deg :=
        R.card_unsatDarts_le a
      rw [hz] at hle
      omega
    have hempty' : (R.addLoops.unsatDarts a).card = 0 := by rw [hcards, hempty]
    unfold unsatFrac
    rw [hempty, hempty']
    simp
  · have hzq : (0 : ℚ) < (R.graph.order : ℚ) := by exact_mod_cast hz
    unfold unsatFrac
    rw [hcards]
    have hden : ((R.addLoops.graph.order * R.addLoops.graph.deg : ℕ) : ℚ)
        = (R.graph.order : ℚ) * ((R.graph.deg : ℚ) + 1) := by
      rw [graph_addLoops, RegGraph.order_addLoops, RegGraph.deg_addLoops]
      push_cast
      ring
    rw [hden]
    field_simp
    push_cast
    ring

/-- The scaling passes to the value. -/
theorem unsatVal_addLoops [Fintype α] [Nonempty α] :
    R.addLoops.unsatVal = R.unsatVal * (R.graph.deg : ℚ) / ((R.graph.deg : ℚ) + 1) := by
  have hk : (0 : ℚ) ≤ (R.graph.deg : ℚ) / ((R.graph.deg : ℚ) + 1) := by positivity
  obtain ⟨a, ha⟩ := R.exists_assignment_unsatFrac_eq_unsatVal
  obtain ⟨b, hb⟩ := R.addLoops.exists_assignment_unsatFrac_eq_unsatVal
  refine le_antisymm ?_ ?_
  · calc R.addLoops.unsatVal ≤ R.addLoops.unsatFrac a := R.addLoops.unsatVal_le a
      _ = R.unsatFrac a * (R.graph.deg : ℚ) / ((R.graph.deg : ℚ) + 1) := R.unsatFrac_addLoops a
      _ = R.unsatVal * (R.graph.deg : ℚ) / ((R.graph.deg : ℚ) + 1) := by rw [ha]
  · rw [← hb, R.unsatFrac_addLoops b, mul_div_assoc, mul_div_assoc]
    exact mul_le_mul_of_nonneg_right (R.unsatVal_le b) hk

theorem satisfiable_addLoops_iff : R.addLoops.Satisfiable ↔ R.Satisfiable := by
  constructor
  · rintro ⟨a, ha⟩
    refine ⟨a, fun p => ?_⟩
    have h := ha (p.1, Sum.inr p.2)
    exact h
  · rintro ⟨a, ha⟩
    refine ⟨a, ?_⟩
    rintro ⟨v, _ | i⟩
    · rfl
    · have h := ha (v, i)
      exact h

end RegCSP

end Complexity
