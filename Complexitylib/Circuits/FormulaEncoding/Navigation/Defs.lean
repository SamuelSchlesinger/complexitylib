/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import Complexitylib.Circuits.FormulaEncoding.Defs

/-!
# Navigation in postfix formula codes -- definitions

Scanning a postfix token stream backwards makes subtree boundaries visible
with one counter. The counter records how many child subtrees are still owed:
a leaf discharges one obligation, a unary node replaces it by one, and a
binary node replaces it by two.
-/

namespace Complexity

namespace FormulaCode

namespace Token

/-- Number of immediate formula children represented by a token. -/
def arity : Token → ℕ
  | .var _ | .tru | .fls => 0
  | .neg => 1
  | .conj | .disj => 2

end Token

/-- Scan tokens in root-to-left order until every owed subtree has been
consumed, returning the number of inspected tokens. -/
def backwardScan : List Token → ℕ → Option ℕ
  | _, 0 => some 0
  | [], _ + 1 => none
  | token :: rest, owed + 1 =>
      (backwardScan rest (owed + token.arity)).map (· + 1)

/-- Width in tokens of the postfix subtree ending at `root`. The scan uses
only the prefix through `root`, read backwards. -/
def subtreeWidth? (stream : List Token) (root : ℕ) : Option ℕ :=
  backwardScan (stream.take (root + 1)).reverse 1

/-- Start index of the postfix subtree ending at `root`. -/
def subtreeStart? (stream : List Token) (root : ℕ) : Option ℕ := do
  let width ← subtreeWidth? stream root
  if width ≤ root + 1 then some (root + 1 - width) else none

end FormulaCode

end Complexity
