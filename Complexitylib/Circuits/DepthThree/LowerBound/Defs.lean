/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module
public import Mathlib.Computability.TuringMachine.Tape
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Tactic

/-!
# Unrestricted depth-three lower bound: model

Adapted from OpenAI's formalization at revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
Source: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/DepthThree/Model.lean

Imports, namespaces, module visibility, documentation, and formatting are adapted
for complexitylib. The source theorem statements and mathematical proofs are retained.
-/

@[expose] public section

namespace Complexity

namespace DepthThreeLowerBound

universe uV uS uK uGamma uQ

/-- Boolean assignments to a set of input variables. -/
abbrev Cube (V : Type uV) := V → Bool
/-- An input variable paired with the value making its literal true. -/
abbrev Literal (V : Type uV) := V × Bool

variable {V : Type uV}

namespace Literal

/-- Evaluate a signed input literal. -/
def eval (l : Literal V) (x : Cube V) : Bool := decide (x l.1 = l.2)

end Literal

/-- A signed input literal or a Boolean constant. -/
abbrev GateInput (V : Type uV) := Sum (Literal V) Bool
/-- An OR gate represented by a list of signed literals and constants. -/
abbrev RawClause (V : Type uV) := List (GateInput V)

namespace GateInput

/-- Evaluate a literal or constant gate input. -/
def eval : GateInput V → Cube V → Bool
  | .inl l, x => l.eval x
  | .inr b, _ => b

end GateInput

namespace RawClause

/-- Evaluate the disjunction of a raw clause. -/
noncomputable def eval (C : RawClause V) (x : Cube V) : Bool := by
  classical
  exact decide (∃ l ∈ C, l.eval x = true)

end RawClause

/-- An OR-AND-OR circuit with arbitrary fan-in, constants, and shared lower gates. -/
structure Circuit3 (V : Type uV) where
  /-- The number of bottom OR gates. -/
  bottomCount : ℕ
  /-- The number of middle AND gates. -/
  middleCount : ℕ
  /-- The literals and constants feeding each bottom OR gate. -/
  bottom : Fin bottomCount → RawClause V
  /-- The bottom gates feeding each middle AND gate. -/
  middle : Fin middleCount → Finset (Fin bottomCount)
  /-- The middle gates feeding the top OR gate. -/
  top : Finset (Fin middleCount)

namespace Circuit3

/-- Count every bottom and middle gate and the single top OR gate. -/
def gateCount (C : Circuit3 V) : ℕ := C.bottomCount + C.middleCount + 1

/-- Evaluate one middle AND gate on its selected bottom gates. -/
noncomputable def middleEval (C : Circuit3 V) (j : Fin C.middleCount)
    (x : Cube V) : Bool := by
  classical
  exact decide (∀ i ∈ C.middle j, (C.bottom i).eval x = true)

/-- Evaluate the top OR of the selected middle AND gates. -/
noncomputable def eval (C : Circuit3 V) (x : Cube V) : Bool := by
  classical
  exact decide (∃ j ∈ C.top, C.middleEval j x = true)

/-- The circuit agrees with the specified Boolean function on every input. -/
def Computes (C : Circuit3 V) (f : Cube V → Bool) : Prop := ∀ x, C.eval x = f x

end Circuit3

/-- Iterate an optional transition, propagating `none` after halting. -/
def runSteps {S : Type uS} (step : S → Option S) (n : ℕ) (c : Option S) : Option S :=
  (fun oc => oc.bind step)^[n] c

/-- A left, stationary, or right move on a bilateral tape. -/
inductive HeadMove
  | left
  | stay
  | right

/-- Apply a head movement to a Mathlib bilateral tape. -/
def HeadMove.apply {Γ : Type uGamma} [Inhabited Γ] : HeadMove → Turing.Tape Γ → Turing.Tape Γ
  | .left, t => t.move Turing.Dir.left
  | .stay, t => t
  | .right, t => t.move Turing.Dir.right

/-- A control state and a tape for each tape index. -/
structure MultiTapeCfg (K : Type uK) (Γ : Type uGamma) (Q : Type uQ) [Inhabited Γ] where
  /-- The finite control state. -/
  q : Q
  /-- The bilateral tape contents and head positions. -/
  tapes : K → Turing.Tape Γ

/-- Read all heads, then halt or choose a state, writes, and head moves. -/
abbrev MultiTapeCode (K : Type uK) (Γ : Type uGamma) (Q : Type uQ) :=
  Q → (K → Γ) → Option (Q × (K → Γ) × (K → HeadMove))

/-- Write the scanned cells and then move every tape head. -/
def multiTapeUpdate {K : Type uK} {Γ : Type uGamma} {Q : Type uQ} [Inhabited Γ]
    (c : MultiTapeCfg K Γ Q) (q : Q) (writes : K → Γ) (moves : K → HeadMove) : MultiTapeCfg K Γ Q :=
  ⟨q, fun k => (moves k).apply ((c.tapes k).write (writes k))⟩

/-- Execute one transition of a multitape program. -/
def multiTapeStep {K : Type uK} {Γ : Type uGamma} {Q : Type uQ} [Inhabited Γ]
    (code : MultiTapeCode K Γ Q) (c : MultiTapeCfg K Γ Q) : Option (MultiTapeCfg K Γ Q) :=
  (code c.q (fun k => (c.tapes k).head)).map fun out =>
    multiTapeUpdate c out.1 out.2.1 out.2.2

/-- A multitape machine with finite control, alphabet, and tape set. The input occupies one
designated read-write tape; the default symbol is blank. -/
structure FiniteMultiTapeMachine where
  /-- Tape indices. -/
  K : Type
  [tapeFinite : Fintype K]
  [tapeDecidableEq : DecidableEq K]
  /-- The tape initially containing the input word. -/
  inputTape : K
  /-- The tape alphabet; its default value is blank. -/
  Γ : Type
  [alphabetInhabited : Inhabited Γ]
  [alphabetFinite : Fintype Γ]
  /-- Control states. -/
  Q : Type
  [stateFinite : Fintype Q]
  /-- The initial control state. -/
  initialState : Q
  /-- Encode input bits as tape symbols. -/
  inputSymbol : Bool → Γ
  input_injective : Function.Injective inputSymbol
  input_ne_blank : ∀ b, inputSymbol b ≠ default
  /-- The partial transition function; `none` halts. -/
  code : MultiTapeCode K Γ Q
  /-- The Boolean verdict read from a halting control state. -/
  accept : Q → Bool

attribute [instance] FiniteMultiTapeMachine.tapeFinite
  FiniteMultiTapeMachine.tapeDecidableEq FiniteMultiTapeMachine.alphabetInhabited
  FiniteMultiTapeMachine.alphabetFinite FiniteMultiTapeMachine.stateFinite

namespace FiniteMultiTapeMachine

/-- Configurations of the bundled finite multitape machine. -/
abbrev Cfg (M : FiniteMultiTapeMachine) := MultiTapeCfg M.K M.Γ M.Q

/-- The bundled machine's partial transition function. -/
abbrev step (M : FiniteMultiTapeMachine) : M.Cfg → Option M.Cfg :=
  multiTapeStep M.code

/-- Initialize the input tape at its first bit and all other tapes blank. -/
def init (M : FiniteMultiTapeMachine) (input : List Bool) : M.Cfg :=
  ⟨M.initialState, fun k =>
    if k = M.inputTape then Turing.Tape.mk₁ (input.map M.inputSymbol)
    else Turing.Tape.mk₁ []⟩

end FiniteMultiTapeMachine

/-- Within the stated time, reach a halting state with the specified Boolean verdict. -/
def MultiTapeHaltsIn (M : FiniteMultiTapeMachine) (input : List Bool)
    (output : Bool) (time : ℕ) : Prop :=
  ∃ k ≤ time, ∃ c : M.Cfg,
    runSteps M.step k (some (M.init input)) = some c ∧
    M.step c = none ∧ M.accept c.q = output

end DepthThreeLowerBound

end Complexity
