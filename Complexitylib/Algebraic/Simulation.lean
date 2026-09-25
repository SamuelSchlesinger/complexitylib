/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.Translation

/-!
# Simultaneous changes of signature and carrier

A simulation combines a circuit translation with a map between universes.
It subsumes both ordinary homomorphisms and same-carrier realizations.
-/

@[expose] public section

namespace Algebraic

/-- A simulation is precisely a homomorphism from the source interpretation
to the target interpretation pulled back through the circuit translation. -/
abbrev Simulation
    (translation : Translation σ τ)
    (source : Interpretation σ U)
    (target : Interpretation τ V) :=
  Homomorphism source (translation.pull target)

namespace Simulation

/-- Identity simulation on an interpreted signature. -/
def id (interpretation : Interpretation σ U) :
    Simulation (Translation.id σ) interpretation interpretation where
  map := _root_.id
  homomorphic := by
    intro op input
    rw [Translation.pull_id]
    rfl

/-- Compose simultaneous changes of signature and carrier. -/
def comp
    {innerTranslation : Translation σ τ}
    {outerTranslation : Translation τ υ}
    {source : Interpretation σ U}
    {middle : Interpretation τ V}
    {target : Interpretation υ W}
    (outer : Simulation outerTranslation middle target)
    (inner : Simulation innerTranslation source middle) :
    Simulation (outerTranslation.comp innerTranslation) source target where
  map := outer.map ∘ inner.map
  homomorphic := by
    intro op input
    rw [Translation.pull_comp]
    exact ((innerTranslation.pullHomomorphism outer).comp inner).homomorphic
      op input

/-- Construct a simulation using the operation-circuit form of its
preservation law. -/
def ofPreserves
    {translation : Translation σ τ}
    {source : Interpretation σ U}
    {target : Interpretation τ V}
    (map : U → V)
    (preserves : ∀ (op : σ.Op) (input : Fin (σ.Arity op) → U),
      map (source op input) =
        (translation.operation op).eval target (map ∘ input) 0) :
    Simulation translation source target where
  map := map
  homomorphic := preserves

/-- The homomorphism law of a simulation, exposed in operation-circuit form. -/
theorem preserves
    {translation : Translation σ τ}
    {source : Interpretation σ U}
    {target : Interpretation τ V}
    (simulation : Simulation translation source target)
    (op : σ.Op)
    (input : Fin (σ.Arity op) → U) :
    simulation.map (source op input) =
      (translation.operation op).eval target
        (simulation.map ∘ input) 0 :=
  simulation.homomorphic op input

/-- Evaluation commutes with simultaneous signature compilation and carrier
mapping. -/
theorem map_compile_eval
    {translation : Translation σ τ}
    {source : Interpretation σ U}
    {target : Interpretation τ V}
    (simulation : Simulation translation source target)
    (circuit : Circuit σ n m)
    (input : Fin n → U) :
    simulation.map ∘ circuit.eval source input =
      (translation.compile circuit).eval target
        (simulation.map ∘ input) :=
  (circuit.map_eval simulation input).trans
    (translation.compile_eval circuit target
      (simulation.map ∘ input)).symm

end Simulation

/-- Every ordinary homomorphism is a simulation through the identity
translation. -/
def _root_.Cslib.Circuits.Homomorphism.toSimulation
    {source : Interpretation σ U}
    {target : Interpretation σ V}
    (homomorphism : Homomorphism source target) :
    Simulation (Translation.id σ) source target where
  map := homomorphism.map
  homomorphic := by
    intro op input
    rw [Translation.pull_id]
    exact homomorphism.homomorphic op input

export Cslib.Circuits (Homomorphism.toSimulation)

/-- Every same-carrier realization is a simulation with the identity carrier
map. -/
def Realization.toSimulation
    {source : Interpretation σ U}
    {target : Interpretation τ U}
    (realization : Realization σ τ source target) :
    Simulation realization.toTranslation source target where
  map := _root_.id
  homomorphic := by
    intro op input
    change source op input =
      (realization.toTranslation.pull target) op input
    rw [realization.realizes]

end Algebraic
