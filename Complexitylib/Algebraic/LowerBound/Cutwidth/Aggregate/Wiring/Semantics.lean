/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Aggregate.Wiring.Defs

/-!
# Exact semantics of local evaluation checks

Copy chains carry precisely the value computed at their signal vertex. Induction in program
order then identifies every locally computed value with the ordinary program trace, including
observed sinks, which need no additional outgoing edge.
-/

@[expose] public section

namespace Algebraic.Cutwidth.Aggregate.Wiring

open scoped Classical
open MultiOutput.Internal WireGraph

variable {σ : Signature} {n s : Nat} {p : Program σ n s} (K : ClosedSet p)
  [Nonempty (Edge K)] (hinput : InputsHaveFanout K) (I : Interpretation σ Bool)

omit [Nonempty (Edge K)] in
/-- A closed component's trace depends only on its own primary inputs. -/
theorem trace_eq_of_inputs_agree {x y : Fin n → Bool}
    (hxy : ∀ j ∈ SingleCut.inputsIn K.carrier, x j = y j)
    (w : Wire n s) (hw : w ∈ K.carrier) : p.trace I x w = p.trace I y w := by
  induction w using SingleCut.Internal.wire_induction p with
  | input j =>
    simpa only [Program.trace_input] using hxy j (by simpa [SingleCut.inputsIn] using hw)
  | gate g ih =>
    apply SingleCut.Internal.trace_gate_congr p I
    intro w hr
    exact ih w hr ((K.closed g w hr).mp hw)

omit [Nonempty (Edge K)] in
/-- The complementary trace depends only on inputs outside the component. -/
theorem trace_eq_of_outside_inputs_agree {x y : Fin n → Bool}
    (hxy : ∀ j, j ∉ SingleCut.inputsIn K.carrier → x j = y j)
    (w : Wire n s) (hw : w ∉ K.carrier) : p.trace I x w = p.trace I y w := by
  induction w using SingleCut.Internal.wire_induction p with
  | input j =>
    simpa only [Program.trace_input] using hxy j (by simpa [SingleCut.inputsIn] using hw)
  | gate g ih =>
    apply SingleCut.Internal.trace_gate_congr p I
    intro w hr
    exact ih w hr (fun h => hw ((K.closed g w hr).mpr h))

/-- Copy chains propagate their signal's locally computed value. -/
theorem copy_eq_localValue {α : Edge K → Bool} (hα : ∀ v, Check K I v α)
    (w : Signal K) (m : Nat) (hm : m < fanout K w - 1) :
    α (.inr ⟨w, ⟨m, hm⟩⟩) = localValue K I α w := by
  induction m with
  | zero => exact hα (.inl w) _ (fst_inr_zero K w hm)
  | succ m ih =>
    exact (hα (.inr ⟨w, ⟨m, by lia⟩⟩) _ (fst_inr_succ K w m hm)).trans (ih (by lia))

/-- Every edge carries the local value of its signal. -/
theorem edge_eq_localValue {α : Edge K → Bool} (hα : ∀ v, Check K I v α)
    (e : Edge K) : α e = localValue K I α (signal K e) := by
  rcases e with t | ⟨w, k⟩
  · by_cases h₂ : 2 ≤ fanout K (slotSignal K t)
    · exact (hα (.inr ⟨slotSignal K t, ⟨copyIndex K t, copyIndex_lt K t h₂⟩⟩)
        _ (fst_inl_of_two_le K t h₂)).trans (copy_eq_localValue K I hα _ _ _)
    · exact hα (.inl (slotSignal K t)) _ (fst_inl_of_not_two_le K t h₂)
  · exact copy_eq_localValue K I hα w k.val k.isLt

/-- A satisfying edge assignment computes the program trace at every selected signal. -/
theorem localValue_eq_trace_of_satisfies {x : Fin n → Bool} {α : Edge K → Bool}
    (hα : (network K hinput I).Satisfies x α) (w : Signal K) :
    localValue K I α w = p.trace I x w.1 := by
  suffices key : ∀ w : Wire n s, ∀ hw : w ∈ K.carrier,
      localValue K I α ⟨w, hw⟩ = p.trace I x w from key w.1 w.2
  intro w
  induction w using SingleCut.Internal.wire_induction p with
  | input j =>
    intro hw
    have hj : j ∈ (network K hinput I).read := by
      simpa [network, SingleCut.inputsIn] using hw
    have hport := hα.2 j hj
    simpa [network, portEdge, hw, localValue] using hport
  | gate g ih =>
    intro hw
    rw [SingleCut.Internal.trace_gate]
    change I (p.lines g).op _ = I (p.lines g).op _
    apply congrArg (I (p.lines g).op)
    funext a
    rw [edge_eq_localValue K I hα.1]
    exact ih _ ⟨a, rfl⟩ _

/-- A satisfying assignment puts the trace value on every edge. -/
theorem edge_eq_trace_of_satisfies {x : Fin n → Bool} {α : Edge K → Bool}
    (hα : (network K hinput I).Satisfies x α) (e : Edge K) :
    α e = p.trace I x (signal K e).1 :=
  (edge_eq_localValue K I hα.1 e).trans
    (localValue_eq_trace_of_satisfies K hinput I hα (signal K e))

/-- The canonical edge assignment induced by the program evaluation. -/
def traceAssignment (x : Fin n → Bool) (e : Edge K) : Bool :=
  p.trace I x (signal K e).1

include hinput in
/-- Local evaluation of the canonical assignment recovers even an unobserved sink. -/
theorem localValue_traceAssignment (x : Fin n → Bool) (w : Signal K) :
    localValue K I (traceAssignment K I x) w = p.trace I x w.1 := by
  obtain ⟨w, hw⟩ := w
  cases w with
  | input j =>
    change p.trace I x (signal K (firstOut K ⟨.input j, hw⟩)).1 = _
    rw [signal_firstOut K _ (hinput j hw)]
  | gate g =>
    rw [SingleCut.Internal.trace_gate]
    rfl

/-- Every program input induces a satisfying edge assignment. -/
theorem traceAssignment_satisfies (x : Fin n → Bool) :
    (network K hinput I).Satisfies x (traceAssignment K I x) := by
  constructor
  · rintro (w | c) e he
    · rw [localValue_traceAssignment K hinput I]
      exact congrArg (fun w : Signal K => p.trace I x w.1)
        (signal_eq_of_fst_eq_inl K he)
    · change p.trace I x (signal K e).1 = p.trace I x c.1.1
      rw [signal_eq_of_fst_eq_inr K he]
  · intro j hj
    have hj' : Wire.input j ∈ K.carrier := by
      simpa [network, SingleCut.inputsIn] using hj
    change traceAssignment K I x (portEdge K j) = x j
    simp only [portEdge, hj', ↓reduceDIte, traceAssignment,
      signal_firstOut K _ (hinput j hj'), Program.trace_input]

end Algebraic.Cutwidth.Aggregate.Wiring
