/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Classes.AverageCase.Ensemble.Defs
public import Mathlib.Data.Finset.Prod

/-!
# Finite uniform-seed distribution ensembles -- definitions

`FiniteEnsemble α` allows each parameter slice to use any nonempty finite uniform
seed type. This strictly generalizes fixed-length Boolean seeds and, crucially,
supports exact choices such as a uniform element of `Fin m` when `m` is not a
power of two.

The distribution remembers sampler multiplicity: probability is the fraction of
seeds whose samples satisfy an event, not the fraction of distinct outputs.
-/


@[expose] public section

universe u v w

namespace Complexity

/-- Uniform probability of an event in an arbitrary finite sample space. -/
def uniformProbability {Ω : Type u} [Fintype Ω] (event : Finset Ω) : ℚ :=
  (event.card : ℚ) / Fintype.card Ω

/-- Mean of a rational-valued statistic on a finite uniform sample space. -/
def uniformMean {Ω : Type u} [Fintype Ω] (value : Ω → ℚ) : ℚ :=
  (∑ sample, value sample) / Fintype.card Ω

/-- Samples in which at least one of `trials` independent uniform draws lands
in `event`. -/
def uniformAtLeastOneEvent {Ω : Type u} [Fintype Ω] [DecidableEq Ω]
    (event : Finset Ω) (trials : ℕ) : Finset (Fin trials → Ω) :=
  Finset.univ.filter fun draws => ∃ trial, draws trial ∈ event

/-- Probability that at least one of `trials` independent uniform draws lands
in `event`. -/
def uniformAtLeastOneProbability {Ω : Type u}
    [Fintype Ω] [DecidableEq Ω] (event : Finset Ω) (trials : ℕ) : ℚ :=
  uniformProbability (uniformAtLeastOneEvent event trials)

/-- A parameterized distribution represented by a nonempty finite uniform seed
space and deterministic sampler at every slice. -/
structure FiniteEnsemble (α : Type u) where
  /-- Seed type used at each parameter. -/
  Seed : ℕ → Type v
  /-- Every seed type is finite. -/
  seedFintype : ∀ n, Fintype (Seed n)
  /-- Seed equality is decidable, so events can be enumerated exactly. -/
  seedDecidableEq : ∀ n, DecidableEq (Seed n)
  /-- No slice has an empty sample space. -/
  seedNonempty : ∀ n, Nonempty (Seed n)
  /-- Deterministic output associated to each seed. -/
  sample : ∀ n, Seed n → α

namespace FiniteEnsemble

variable {α : Type u} {β : Type w}

/-- The seed event whose samples satisfy `P`. -/
def event (D : FiniteEnsemble α) (n : ℕ) (P : α → Prop)
    [DecidablePred P] : Finset (D.Seed n) := by
  letI := D.seedFintype n
  letI := D.seedDecidableEq n
  exact Finset.univ.filter fun seed => P (D.sample n seed)

/-- Exact uniform-seed probability of `P` in the `n`th slice. -/
def probability (D : FiniteEnsemble α) (n : ℕ) (P : α → Prop)
    [DecidablePred P] : ℚ := by
  letI := D.seedFintype n
  exact uniformProbability (D.event n P)

/-- Probability mass of one output in the `n`th slice. -/
def mass [DecidableEq α] (D : FiniteEnsemble α) (n : ℕ) (x : α) : ℚ :=
  D.probability n fun y => y = x

/-- Finite support of the `n`th slice. -/
def support [DecidableEq α] (D : FiniteEnsemble α) (n : ℕ) : Finset α := by
  letI := D.seedFintype n
  letI := D.seedDecidableEq n
  exact Finset.univ.image (D.sample n)

/-- Push an ensemble forward through a deterministic map. -/
def map (D : FiniteEnsemble α) (f : α → β) : FiniteEnsemble β where
  Seed := D.Seed
  seedFintype := D.seedFintype
  seedDecidableEq := D.seedDecidableEq
  seedNonempty := D.seedNonempty
  sample n seed := f (D.sample n seed)

/-- Independently sample two ensembles from the product of their seed spaces. -/
def product (D : FiniteEnsemble α) (E : FiniteEnsemble β) :
    FiniteEnsemble (α × β) where
  Seed n := D.Seed n × E.Seed n
  seedFintype n := by
    letI := D.seedFintype n
    letI := E.seedFintype n
    infer_instance
  seedDecidableEq n := by
    letI := D.seedDecidableEq n
    letI := E.seedDecidableEq n
    infer_instance
  seedNonempty n := by
    have := D.seedNonempty n
    have := E.seedNonempty n
    infer_instance
  sample n seed := (D.sample n seed.1, E.sample n seed.2)

/-- Point-mass ensemble. Its seed type is a singleton at every slice. -/
def dirac (x : ℕ → α) : FiniteEnsemble α where
  Seed _ := Unit
  seedFintype _ := inferInstance
  seedDecidableEq _ := inferInstance
  seedNonempty _ := inferInstance
  sample n _ := x n

end FiniteEnsemble

namespace DyadicEnsemble

variable {α : Type u}

/-- Regard a Boolean-seed ensemble as a general finite uniform-seed ensemble. -/
def toFinite (D : DyadicEnsemble α) : FiniteEnsemble α where
  Seed n := Fin (D.seedLength n) → Bool
  seedFintype _ := inferInstance
  seedDecidableEq _ := inferInstance
  seedNonempty _ := inferInstance
  sample := D.sample

end DyadicEnsemble

end Complexity
