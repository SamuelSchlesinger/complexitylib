/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Circuits.AndOrNot.Defs
public import Complexitylib.Circuits.NormalForm.Defs

/-!
# Negation-normal unbounded formulas for AC0

`AC0Formula N` is an unbounded-fan-in formula over exactly `N` variables.
Negation occurs only in literal polarity, which is the representation needed
by restriction and switching-lemma arguments. Unlike a circuit, this syntax is
a tree and therefore records repeated subcomputations separately.

Children are stored in the mutually inductive `AC0Forest`. This gives Lean a
direct structural induction principle for unbounded formulas; `ofList` and
`toList` provide the usual list interface. Empty conjunctions and disjunctions
denote `true` and `false`, respectively.
-/


@[expose] public section

namespace Complexity

mutual

/-- A negation-normal Boolean formula with unbounded AND and OR gates. -/
inductive AC0Formula (N : ℕ) where
  /-- A Boolean constant. -/
  | const (value : Bool)
  /-- A signed input variable. -/
  | lit (literal : Literal N)
  /-- An unbounded conjunction. -/
  | and (children : AC0Forest N)
  /-- An unbounded disjunction. -/
  | or (children : AC0Forest N)

/-- A structurally recursive forest of unbounded-formula children. -/
inductive AC0Forest (N : ℕ) where
  /-- The empty forest. -/
  | nil
  /-- Add one formula to the front of a forest. -/
  | cons (head : AC0Formula N) (tail : AC0Forest N)

end

deriving instance Repr for AC0Formula
deriving instance Repr for AC0Forest
deriving instance DecidableEq for AC0Formula
deriving instance DecidableEq for AC0Forest

namespace AC0Forest

/-- Convert a list to the structurally recursive forest representation. -/
def ofList : List (AC0Formula N) → AC0Forest N
  | [] => .nil
  | formula :: formulas => .cons formula (ofList formulas)

/-- Convert a formula forest back to a list. -/
def toList : AC0Forest N → List (AC0Formula N)
  | .nil => []
  | .cons formula formulas => formula :: formulas.toList

/-- Number of formulas in a forest. -/
def length : AC0Forest N → ℕ
  | .nil => 0
  | .cons _ formulas => formulas.length + 1

@[simp] theorem toList_ofList (formulas : List (AC0Formula N)) :
    (ofList formulas).toList = formulas := by
  induction formulas with
  | nil => rfl
  | cons formula formulas ih =>
      simp [ofList, toList, ih]

/-- Converting a forest to a list and back is exact. -/
@[simp] theorem ofList_toList (formulas : AC0Forest N) :
    ofList formulas.toList = formulas := by
  cases formulas with
  | nil => rfl
  | cons formula formulas =>
      simp [ofList, toList, ofList_toList formulas]

@[simp] theorem length_ofList (formulas : List (AC0Formula N)) :
    (ofList formulas).length = formulas.length := by
  induction formulas with
  | nil => rfl
  | cons formula formulas ih =>
      simp [ofList, length, ih]

end AC0Forest

namespace AC0Formula

mutual

/-- Evaluate an unbounded formula on an `N`-bit input. -/
def eval (input : BitString N) : AC0Formula N → Bool
  | .const value => value
  | .lit literal => literal.eval input
  | .and children => evalAll input children
  | .or children => evalAny input children

/-- Evaluate a forest as a conjunction. -/
def evalAll (input : BitString N) : AC0Forest N → Bool
  | .nil => true
  | .cons formula formulas =>
      eval input formula && evalAll input formulas

/-- Evaluate a forest as a disjunction. -/
def evalAny (input : BitString N) : AC0Forest N → Bool
  | .nil => false
  | .cons formula formulas =>
      eval input formula || evalAny input formulas

end

mutual

/-- Total tree size, counting constants, literal occurrences, and gates. -/
def size : AC0Formula N → ℕ
  | .const _ => 1
  | .lit _ => 1
  | .and children => 1 + forestSize children
  | .or children => 1 + forestSize children

/-- Sum of the tree sizes in a forest. -/
def forestSize : AC0Forest N → ℕ
  | .nil => 0
  | .cons formula formulas => size formula + forestSize formulas

end

mutual

/-- Number of unbounded gates. Leaves are free and every AND/OR node costs
one. Only gates incur switching failures, so this is the sharp union-bound
measure for iterated switching; `gateCount_le_size` recovers any bound
previously stated with `size`. -/
def gateCount : AC0Formula N → ℕ
  | .const _ => 0
  | .lit _ => 0
  | .and children => 1 + forestGateCount children
  | .or children => 1 + forestGateCount children

/-- Sum of the gate counts of every formula in a forest. -/
def forestGateCount : AC0Forest N → ℕ
  | .nil => 0
  | .cons formula formulas => gateCount formula + forestGateCount formulas

end

mutual

/-- Gate count never exceeds tree size. -/
theorem gateCount_le_size : (formula : AC0Formula N) →
    formula.gateCount ≤ formula.size
  | .const _ => Nat.zero_le _
  | .lit _ => Nat.zero_le _
  | .and children =>
      Nat.add_le_add_left (forestGateCount_le_forestSize children) 1
  | .or children =>
      Nat.add_le_add_left (forestGateCount_le_forestSize children) 1

/-- Forest gate count never exceeds forest size. -/
theorem forestGateCount_le_forestSize : (formulas : AC0Forest N) →
    forestGateCount formulas ≤ forestSize formulas
  | .nil => Nat.le_refl 0
  | .cons formula formulas =>
      Nat.add_le_add (gateCount_le_size formula)
        (forestGateCount_le_forestSize formulas)

end

mutual

/-- Formula depth. Leaves have depth zero and every unbounded gate adds one. -/
def depth : AC0Formula N → ℕ
  | .const _ => 0
  | .lit _ => 0
  | .and children => 1 + forestDepth children
  | .or children => 1 + forestDepth children

/-- Maximum formula depth in a forest. -/
def forestDepth : AC0Forest N → ℕ
  | .nil => 0
  | .cons formula formulas => max formula.depth (forestDepth formulas)

end

/-- Every member of a forest has depth at most the forest maximum. -/
theorem depth_le_forestDepth_of_mem
    (formula : AC0Formula N) (formulas : AC0Forest N)
    (hmem : formula ∈ formulas.toList) :
    formula.depth ≤ forestDepth formulas := by
  cases formulas with
  | nil => simp [AC0Forest.toList] at hmem
  | cons head tail =>
      simp only [AC0Forest.toList, List.mem_cons] at hmem
      simp only [forestDepth]
      rcases hmem with rfl | hmem
      · exact le_max_left _ _
      · exact
          (depth_le_forestDepth_of_mem formula tail hmem).trans
            (le_max_right _ _)

mutual

/-- The finite set of input variables mentioned by a formula. -/
def vars : AC0Formula N → Finset (Fin N)
  | .const _ => ∅
  | .lit literal => {literal.var}
  | .and children => forestVars children
  | .or children => forestVars children

/-- Union of the variable supports of every formula in a forest. -/
def forestVars : AC0Forest N → Finset (Fin N)
  | .nil => ∅
  | .cons formula formulas => formula.vars ∪ forestVars formulas

end

mutual

/-- De Morgan negation, retaining negation-normal form. -/
def neg : AC0Formula N → AC0Formula N
  | .const value => .const (!value)
  | .lit literal => .lit literal.neg
  | .and children => .or (negForest children)
  | .or children => .and (negForest children)

/-- Negate every formula in a forest. -/
def negForest : AC0Forest N → AC0Forest N
  | .nil => .nil
  | .cons formula formulas => .cons formula.neg (negForest formulas)

end

/-- Build the gate selected by an AND/OR operation. -/
def ofOp (op : AndOrOp) (children : AC0Forest N) : AC0Formula N :=
  match op with
  | .and => .and children
  | .or => .or children

/-- Build an unbounded conjunction from an ordinary list. -/
def andList (children : List (AC0Formula N)) : AC0Formula N :=
  .and (.ofList children)

/-- Build an unbounded disjunction from an ordinary list. -/
def orList (children : List (AC0Formula N)) : AC0Formula N :=
  .or (.ofList children)

/-- Every AC0 formula has at least one syntax-tree node. -/
theorem one_le_size (formula : AC0Formula N) : 1 ≤ formula.size := by
  cases formula <;> simp [size]

end AC0Formula
end Complexity
