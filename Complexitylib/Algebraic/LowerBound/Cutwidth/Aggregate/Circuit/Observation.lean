/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Aggregate.Circuit.Mixing
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Aggregate.Circuit.Count
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Aggregate.Wiring.Semantics
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Algebra.BigOperators.Pi

/-!
# Special-gate consistency as a product of signal observations

Each signal emits all its contributions once, including repeated special-gate slots.
A two-state multiplicative output flag observes the designated output without adding
a graph edge. Values outside a closed component can be folded into the final predicate.
-/

@[expose] public section

namespace Algebraic.Aggregate

variable {J : Type} {State : J → Type} {n g : ℕ}

/-- All contributions emitted by one signal. Repeated occurrences multiply repeatedly. -/
def wireContribution [∀ j, CommMonoid (State j)]
    (p : Program (signature State) n g) (wire : Wire n g) (value : Bool) : Registers p :=
  fun gate => ∏ slot ∈ Finset.univ.filter (fun slot => (p.lines gate).wires slot = wire),
    (p.lines gate).op.slotContribution slot value

/-- Aggregate registers and a two-state output observation. -/
abbrev Observation (p : Program (signature State) n g) := Registers p × ZMod 2

/-- The flag is multiplicative: only the designated output emits a possibly zero value. -/
def outputFlag (out wire : Wire n g) (value : Bool) : ZMod 2 :=
  if wire = out then if value then 1 else 0 else 1

/-- The local observation emitted by a signal vertex. -/
def observe [∀ j, CommMonoid (State j)]
    (p : Program (signature State) n g) (out wire : Wire n g) (value : Bool) : Observation p :=
  (wireContribution p wire value, outputFlag out wire value)

/-- The final predicate tests all special readouts and the designated output. -/
def AcceptObservation (p : Program (signature State) n g) (a : Guess p)
    (state : Observation p) : Prop :=
  (∀ gate : SpecialGate p, (p.lines gate).op.readout (state.1 gate) = a gate) ∧ state.2 = 1

theorem prod_wireContribution [∀ j, CommMonoid (State j)]
    (p : Program (signature State) n g) (S : Finset (Wire n g)) (values : Wire n g → Bool)
    (gate : SpecialGate p) :
    (∏ wire ∈ S, wireContribution p wire (values wire)) gate =
      lineAggregate (p.lines gate) S values := by
  simp only [Finset.prod_apply, wireContribution, lineAggregate]
  calc
    _ = ∏ wire ∈ S, ∏ slot ∈ Finset.univ.filter
          (fun slot => (p.lines gate).wires slot = wire),
          (p.lines gate).op.slotContribution slot (values ((p.lines gate).wires slot)) := by
      apply Finset.prod_congr rfl
      intro wire _
      apply Finset.prod_congr rfl
      intro slot hslot
      rw [(Finset.mem_filter.mp hslot).2]
    _ = _ := Finset.prod_fiberwise_eq_prod_filter _ _ _ _

theorem prod_outputFlag (out : Wire n g) (values : Wire n g → Bool) :
    ∏ wire, outputFlag out wire (values wire) = if values out then 1 else 0 := by
  simp [outputFlag]

theorem special_eval_eq_readout [∀ j, CommMonoid (State j)]
    (line : Line (signature State) n g) (hs : line.op.isSpecial = true)
    (input : Fin n → Bool) (gates : Fin g → Bool) :
    line.eval interpretation input gates =
      line.op.readout (lineAggregate line Finset.univ (Wire.elim input gates)) := by
  rcases line with ⟨op, wires⟩
  cases op with
  | binary => simp [Op.isSpecial] at hs
  | special => simp [Line.eval, interpretation, Op.readout, lineAggregate, Op.slotContribution]

/-- For one fixed guess, the observation predicate is exactly the original consistency test
and the erased circuit's output test. -/
theorem acceptObservation_iff [∀ j, CommMonoid (State j)]
    (p : Program (signature State) n g) (a : Guess p) (out : Wire n g)
    (input : Fin n → Bool) :
    AcceptObservation p a
        (∏ wire, observe p out wire ((erase p a).trace ordinaryInterpretation input wire)) ↔
      Consistent p a input ∧ (erase p a).trace ordinaryInterpretation input out = true := by
  simp only [AcceptObservation, Prod.fst_prod, Prod.snd_prod, observe, prod_outputFlag]
  constructor
  · rintro ⟨checks, output⟩
    refine ⟨fun gate => ?_, ?_⟩
    · rw [special_eval_eq_readout _ gate.property]
      simpa only [prod_wireContribution, Program.trace] using checks gate
    · cases h : (erase p a).trace ordinaryInterpretation input out <;> simp_all
  · rintro ⟨checks, output⟩
    refine ⟨fun gate => ?_, ?_⟩
    · rw [prod_wireContribution]
      simpa only [special_eval_eq_readout _ gate.property, Program.trace] using checks gate
    · simp [output]

/-- All observations outside a component, evaluated at the fixed outside assignment. -/
def outsideObservation [∀ j, CommMonoid (State j)]
    (p : Program (signature State) n g) (a : Guess p) (S : Finset (Wire n g))
    (out : Wire n g) (fixed : Fin n → Bool) : Observation p :=
  ∏ wire ∈ Sᶜ, observe p out wire ((erase p a).trace ordinaryInterpretation fixed wire)

/-- The component's final predicate includes all fixed outside contributions. -/
def ComponentAccept [∀ j, CommMonoid (State j)]
    (p : Program (signature State) n g) (a : Guess p) (S : Finset (Wire n g))
    (out : Wire n g) (fixed : Fin n → Bool) (state : Observation p) : Prop :=
  AcceptObservation p a (state * outsideObservation p a S out fixed)

/-- A guessed computation accepts when all special equations and the output check pass. -/
def AcceptsGuess [∀ j, CommMonoid (State j)] (p : Program (signature State) n g)
    (a : Guess p) (out : Wire n g) (input : Fin n → Bool) : Prop :=
  Consistent p a input ∧ (erase p a).trace ordinaryInterpretation input out = true

/-- Exact component observation semantics after the outside primary inputs are fixed. -/
theorem componentAccept_iff [∀ j, CommMonoid (State j)]
    (p : Program (signature State) n g) (a : Guess p)
    (K : Cutwidth.MultiOutput.Internal.ClosedSet (erase p a)) (out : Wire n g)
    (fixed input : Fin n → Bool)
    (agree : ∀ j, j ∉ Cutwidth.SingleCut.inputsIn K.carrier → input j = fixed j) :
    ComponentAccept p a K.carrier out fixed
        (∏ wire : Cutwidth.MultiOutput.Internal.WireGraph.Signal K,
          observe p out wire ((erase p a).trace ordinaryInterpretation input wire)) ↔
      AcceptsGuess p a out input := by
  have outside : outsideObservation p a K.carrier out fixed =
      ∏ wire ∈ K.carrierᶜ,
        observe p out wire ((erase p a).trace ordinaryInterpretation input wire) := by
    apply Finset.prod_congr rfl
    intro wire hwire
    rw [Cutwidth.Aggregate.Wiring.trace_eq_of_outside_inputs_agree K ordinaryInterpretation
      agree wire (Finset.mem_compl.mp hwire)]
  have inside : (∏ wire : Cutwidth.MultiOutput.Internal.WireGraph.Signal K,
      observe p out wire ((erase p a).trace ordinaryInterpretation input wire)) =
      ∏ wire ∈ K.carrier,
        observe p out wire ((erase p a).trace ordinaryInterpretation input wire) := by
    exact Finset.prod_coe_sort K.carrier
      (fun wire => observe p out wire ((erase p a).trace ordinaryInterpretation input wire))
  rw [ComponentAccept, outside, inside, Finset.prod_mul_prod_compl]
  exact acceptObservation_iff p a out input

/-- Accepted guesses are precisely the true guess on originally accepted inputs. -/
theorem acceptsGuess_iff [∀ j, CommMonoid (State j)]
    (p : Program (signature State) n g) (a : Guess p) (out : Wire n g)
    (input : Fin n → Bool) :
    AcceptsGuess p a out input ↔
      a = actualGuess p input ∧ p.trace interpretation input out = true := by
  constructor
  · rintro ⟨h, output⟩
    refine ⟨(consistent_iff_eq_actualGuess p a input).mp h, ?_⟩
    simpa only [Program.trace, erase_eval_of_consistent p a input h] using output
  · rintro ⟨rfl, output⟩
    refine ⟨actualGuess_consistent p input, ?_⟩
    simpa only [Program.trace, erase_eval_actualGuess] using output

/-- Existentially guessing the special outputs preserves the accepted inputs exactly. -/
theorem accepts_iff_exists_guess [∀ j, CommMonoid (State j)]
    (p : Program (signature State) n g) (out : Wire n g) (input : Fin n → Bool) :
    p.trace interpretation input out = true ↔ ∃ a : Guess p, AcceptsGuess p a out input := by
  simp only [acceptsGuess_iff, exists_eq_left]

/-- The observation monoid uses just one additional bit beyond the aggregate registers. -/
theorem card_guess_mul_card_observation_le [∀ j, Fintype (State j)]
    (p : Program (signature State) n g) :
    Fintype.card (Guess p) * Fintype.card (Observation p) ≤ 2 ^ (budget p + 1) := by
  rw [show Fintype.card (Observation p) = Fintype.card (Registers p) * 2 by
    simp [Observation], pow_succ]
  simpa only [← mul_assoc, ← Fintype.card_prod] using
    Nat.mul_le_mul_right 2 (card_componentKey_le p)

end Algebraic.Aggregate
