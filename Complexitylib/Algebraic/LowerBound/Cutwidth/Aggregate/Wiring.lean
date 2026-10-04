/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Aggregate.NetworkDefs
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Aggregate.Wiring.Graph
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Aggregate.Wiring.Reindex
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Aggregate.Wiring.Semantics

/-!
# Compiling observed signals into a monoid network

Each selected signal emits its contribution exactly once, at its own vertex. Copy vertices
emit the identity. A gate's value is computed from its input slots even when it has no
outgoing edge. Consequently arbitrary observation of sinks preserves the wire graph, its
degree-three bound, and its edge excess. The monoid need not have cancellation or inverses.
-/

@[expose] public section

namespace Algebraic.Cutwidth.Aggregate.Wiring

open scoped Classical
open MultiOutput.Internal WireGraph

variable {σ : Signature} {n s : Nat} {p : Program σ n s} (K : ClosedSet p)
  [Nonempty (Edge K)] (hinput : InputsHaveFanout K) (I : Interpretation σ Bool)
  {M : Type} [CommMonoid M] (φ : Signal K → Bool → M) (Accept : M → Prop)

/-- Each signal emits once; fanout copies contribute the identity. -/
noncomputable def contribution : Vertex K → (Edge K → Bool) → M
  | .inl w, α => φ w (localValue K I α w)
  | .inr _, _ => 1

/-- The closed wire graph compiled to an aggregate network. -/
noncomputable def aggregateNetwork : AggregateNetwork n (Vertex K) (Edge K) M where
  toNetwork := network K hinput I
  contribution := contribution K I φ
  contribution_local := by
    rintro (w | c) α β agree
    · exact congrArg (φ w) (localValue_congr K hinput I w α β agree)
    · rfl
  Accept := Accept

/-- The product at all vertices contains each selected signal exactly once. -/
theorem accumulated_eq (α : Edge K → Bool) :
    (aggregateNetwork K hinput I φ Accept).accumulated Finset.univ α =
      ∏ w : Signal K, φ w (localValue K I α w) := by
  simp [AggregateNetwork.accumulated, aggregateNetwork, contribution, Fintype.prod_sum_type]

/-- The global aggregate of a satisfying local evaluation is the aggregate of the trace. -/
theorem accumulated_eq_trace {x : Fin n → Bool} {α : Edge K → Bool}
    (hα : (network K hinput I).Satisfies x α) :
    (aggregateNetwork K hinput I φ Accept).accumulated Finset.univ α =
      ∏ w : Signal K, φ w (p.trace I x w.1) := by
  rw [accumulated_eq]
  apply Finset.prod_congr rfl
  intro w _
  rw [localValue_eq_trace_of_satisfies K hinput I hα]

/-- Exact compiler semantics for an arbitrary final predicate on the aggregate. -/
theorem exists_satisfies_iff (x : Fin n → Bool) :
    (∃ α, (aggregateNetwork K hinput I φ Accept).Satisfies x α) ↔
      Accept (∏ w : Signal K, φ w (p.trace I x w.1)) := by
  constructor
  · rintro ⟨α, hlocal, haccept⟩
    rwa [accumulated_eq_trace K hinput I φ Accept hlocal] at haccept
  · intro hx
    refine ⟨traceAssignment K I x, traceAssignment_satisfies K hinput I x, ?_⟩
    change Accept ((aggregateNetwork K hinput I φ Accept).accumulated _ _)
    rwa [accumulated_eq_trace K hinput I φ Accept (traceAssignment_satisfies K hinput I x)]

/-- The compiled network computes the Boolean predicate of the observed trace product. -/
theorem aggregateNetwork_computes :
    (aggregateNetwork K hinput I φ Accept).Computes
      (fun x => decide (Accept (∏ w : Signal K, φ w (p.trace I x w.1)))) := by
  intro x
  rw [exists_satisfies_iff]
  exact decide_eq_true_iff

/-- Observation adds no graph structure. -/
theorem aggregateNetwork_toMultigraph :
    (aggregateNetwork K hinput I φ Accept).toMultigraph = graph K := rfl

end Algebraic.Cutwidth.Aggregate.Wiring
