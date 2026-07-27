/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Complexitylib.SAT.ThreeCNF

/-!
# Tseitin splitting from CNF to exact 3-CNF

This definitions layer gives a total fresh-variable-threaded transformation
from the existing unbounded-width `SAT.CNF` representation to exact 3-CNF.

Short nonempty clauses are padded by repeating literals. An empty clause is
replaced by a contradictory pair of width-three unit clauses. A clause of
width at least four is split by the standard chain

`(a ∨ b ∨ z) ∧ (¬z ∨ rest)`.

Fresh counters are threaded across clauses, beginning above the largest source
variable. Correctness and size theorems live in the internal and public layers.
-/

@[expose] public section

namespace Complexity

namespace SAT

namespace Lit

/-- Negate a literal without changing its variable. -/
def neg (ℓ : Lit) : Lit := ⟨!ℓ.sign, ℓ.var⟩

/-- Positive literal on variable `v`. -/
def pos (v : ℕ) : Lit := ⟨true, v⟩

/-- Negative literal on variable `v`. -/
def negVar (v : ℕ) : Lit := ⟨false, v⟩

end Lit

namespace Clause

/-- Number of fresh variables consumed while splitting one clause. Empty
clauses use one variable for a contradictory gadget; a clause of width `k ≥ 4`
uses `k - 3` chain variables. -/
def tseitinFreshCount (c : Clause) : ℕ :=
  if c = [] then 1 else c.length - 3

/-- Split one clause into exact-width-three clauses, drawing auxiliary
variables consecutively from `next`. -/
def to3CNF (next : ℕ) : Clause → CNF
  | [] =>
      [[Lit.pos next, Lit.pos next, Lit.pos next],
        [Lit.negVar next, Lit.negVar next, Lit.negVar next]]
  | [a] => [[a, a, a]]
  | [a, b] => [[a, b, b]]
  | [a, b, c] => [[a, b, c]]
  | a :: b :: c :: d :: rest =>
      [a, b, Lit.pos next] ::
        to3CNF (next + 1) (Lit.negVar next :: c :: d :: rest)
  termination_by c => c.length

end Clause

namespace CNF

/-- Total number of literal occurrences in a CNF. -/
def literalCount (φ : CNF) : ℕ :=
  φ.foldr (fun c total => c.length + total) 0

/-- Total number of fresh variables consumed by all clause splitters. -/
def tseitinFreshCount (φ : CNF) : ℕ :=
  φ.foldr (fun c total => c.tseitinFreshCount + total) 0

/-- Split every clause while threading the fresh-variable counter. The second
component is the first unused variable after the transformation. -/
def to3Aux : ℕ → CNF → CNF × ℕ
  | next, [] => ([], next)
  | next, c :: cs =>
      let next' := next + c.tseitinFreshCount
      let tail := to3Aux next' cs
      (c.to3CNF next ++ tail.1, tail.2)

/-- Convert an arbitrary CNF to exact 3-CNF. Auxiliary variables begin one
past the largest variable occurring in the source. -/
def to3 (φ : CNF) : CNF :=
  (to3Aux (φ.maxVar + 1) φ).1

end CNF

end SAT

end Complexity
