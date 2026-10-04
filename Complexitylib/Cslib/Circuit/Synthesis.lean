/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Complexitylib.Cslib.Circuit.Wire
public import Cslib.Computability.Circuit.Synthesis
import Mathlib.Algebra.BigOperators.Fin

/-!
# Reusing circuits in synthesis arguments

Ordered families let each member of a synthesized family use all preceding members, with the
total budget given by the sum of the step budgets (`Synthesis.ordered_family`). Applied to the
gates of a program, they rebuild the program from gatewise bounds (`Program.synthesis_of_steps`).
In particular a concrete circuit supplies a synthesis bound for its designated outputs, which
connects circuit composition with constructions using shared wires.

The rules `Synthesis.with_sources`, `Synthesis.sequence` and `Synthesis.ordered_family`, and the
program lemmas `Program.wireFunction_mem_before`, `Program.synthesis_step` and
`Program.synthesis_of_steps`, come from `Cslib.Computability.Circuit.Synthesis` at commit
`2a4389b` of the author's CSLib fork (branch `complexitylib-integration`); upstream CSLib does not
have them.
-/

@[expose] public section

namespace Cslib.Circuits

namespace Synthesis

universe v u
variable {σ : Signature.{v}} {U : Type u} {n : ℕ} {I : Interpretation σ U}
variable {s t : Set ((Fin n → U) → U)} {a : ℕ}

/-- A synthesis retains its sources alongside its targets. -/
theorem with_sources (h : Synthesis I s t a) : Synthesis I s (s ∪ t) a := by
  intro g p hp
  obtain ⟨k, q, hsize, hkeep, ht⟩ := h g p hp
  exact ⟨k, q, hsize, hkeep, Set.union_subset (hp.trans hkeep) ht⟩

/-- Compose an indexed sequence of syntheses, adding their gate budgets. -/
theorem sequence {k : ℕ} (stages : Fin (k + 1) → Set ((Fin n → U) → U))
    (cost : Fin k → ℕ)
    (step : ∀ j, Synthesis I (stages j.castSucc) (stages j.succ) (cost j)) :
    Synthesis I (stages 0) (stages (Fin.last k)) (∑ j, cost j) := by
  induction k with
  | zero => simpa using (of_subset (I := I) (s := stages 0) Set.Subset.rfl)
  | succ k ih =>
      have first := ih (fun j => stages j.castSucc) (fun j => cost j.castSucc)
        (fun j => step j.castSucc)
      have last := step (Fin.last k)
      have result := first.trans (last.mono Set.subset_union_right Set.Subset.rfl le_rfl)
      simpa [Fin.sum_univ_castSucc] using result

/-- Synthesize a family in order, allowing each function to use all preceding ones. -/
theorem ordered_family {k : ℕ} (f : Fin k → (Fin n → U) → U)
    (cost : Fin k → ℕ)
    (step : ∀ j, Synthesis I (s ∪ f '' {i | i < j}) {f j} (cost j)) :
    Synthesis I s (Set.range f) (∑ j, cost j) := by
  let stages (j : Fin (k + 1)) := s ∪ f '' {i | i.val < j.val}
  have hstage (j : Fin k) : stages j.succ = stages j.castSucc ∪ {f j} := by
    ext value
    simp only [stages, Set.mem_union, Set.mem_image, Set.mem_ofPred_eq,
      Fin.val_succ, Fin.val_castSucc, Set.mem_singleton_iff]
    constructor
    · rintro (h | ⟨i, hi, rfl⟩)
      · exact Or.inl (Or.inl h)
      · by_cases hij : i = j
        · exact Or.inr (congrArg f hij)
        · have hne : i.val ≠ j.val := Fin.val_ne_of_ne hij
          exact Or.inl (Or.inr ⟨i, by omega, rfl⟩)
    · rintro ((h | ⟨i, hi, rfl⟩) | rfl)
      · exact Or.inl h
      · exact Or.inr ⟨i, by omega, rfl⟩
      · exact Or.inr ⟨j, by omega, rfl⟩
  have hseq := sequence stages cost (fun j => by
    rw [hstage]
    exact (step j).with_sources)
  have hzero : stages 0 = s := by simp [stages]
  have hlast : stages (Fin.last k) = s ∪ Set.range f := by
    ext value
    simp [stages]
  rw [hzero, hlast] at hseq
  exact hseq.mono Set.Subset.rfl Set.subset_union_right le_rfl

end Synthesis

section Program

universe v u
variable {σ : Signature.{v}} {U : Type u} {n : ℕ} {I : Interpretation σ U}

/-- A preceding wire is either an input or a preceding gate function. -/
theorem Program.wireFunction_mem_before {g : ℕ} (p : Program σ n g) (j : Fin g)
    (wire : Wire n g) (hwire : wire.index.val < n + j.val) :
    p.wireFunction I wire ∈ inputs n ∪ p.gateFunction I '' {i | i < j} := by
  cases wire with
  | input i => exact Or.inl ⟨i, (p.wireFunction_input I i).symm⟩
  | gate i =>
    simp only [Wire.index_gate, Fin.val_natAdd] at hwire
    exact Or.inr ⟨i, Fin.lt_def.mpr (by omega), (p.wireFunction_gate I i).symm⟩

/-- Each program gate can be synthesized from the inputs and preceding gates. -/
theorem Program.synthesis_step {g : ℕ} (p : Program σ n g) (j : Fin g) :
    Synthesis I (inputs n ∪ p.gateFunction I '' {i | i < j}) {p.gateFunction I j} 1 := by
  have h := Synthesis.gate (I := I) (p.lines j).op
    (fun a => p.wireFunction I ((p.lines j).wires a))
    (fun a => p.wireFunction_mem_before j _ (p.lines_wires_lt j a))
  have heq : (fun x => I (p.lines j).op
      (fun a => p.wireFunction I ((p.lines j).wires a) x)) = p.gateFunction I j := by
    funext x
    exact p.lines_eval I x j
  rwa [heq] at h

/-- Rebuild a program from gatewise synthesis bounds, retaining every wire function. -/
theorem Program.synthesis_of_steps {g : ℕ} (p : Program σ n g) (cost : Fin g → ℕ)
    (step : ∀ j, Synthesis I (inputs n ∪ p.gateFunction I '' {i | i < j})
      {p.gateFunction I j} (cost j)) :
    Synthesis I (inputs n) (available I p) (∑ j, cost j) := by
  have h := (Synthesis.ordered_family _ cost step).with_sources
  apply h.mono Set.Subset.rfl _ le_rfl
  rintro f ⟨wire, rfl⟩
  cases wire with
  | input i => exact Or.inl ⟨i, (p.wireFunction_input I i).symm⟩
  | gate j => exact Or.inr ⟨j, (p.wireFunction_gate I j).symm⟩

end Program

variable {σ : Signature} {U : Type} {n m : ℕ} {I : Interpretation σ U}

/-- Rebuild the circuit's outputs within its existing gate budget. -/
theorem Circuit.synthesis (c : Circuit σ n m) :
    Synthesis I (inputs n) (Set.range fun j x => c.eval I x j) c.size := by
  have h := c.program.synthesis_of_steps (I := I) (fun _ => 1)
    (fun j => c.program.synthesis_step j)
  apply h.mono Set.Subset.rfl ?_ (by simp)
  rintro f ⟨j, rfl⟩
  exact ⟨c.outputs j, rfl⟩

/-- A circuit computing `f` supplies a synthesis bound for all coordinates of `f`. -/
theorem Circuit.Computes.synthesis {c : Circuit σ n m}
    {f : (Fin n → U) → Fin m → U} (hc : c.Computes I f) :
    Synthesis I (inputs n) (Set.range fun j x => f x j) c.size := by
  have equal : (fun j x => c.eval I x j) = (fun j x => f x j) := by
    funext j x
    exact congrFun (hc x) j
  rw [← equal]
  exact c.synthesis

end Cslib.Circuits
