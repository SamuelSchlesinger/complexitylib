/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Circuits.Shallow.Negations
public import Mathlib.Algebra.BigOperators.Group.List.Basic

/-!
# Alternating layers for constructing shallow circuits

`Layer n d` is construction syntax: a signed input at depth zero, or a list of
children at the preceding depth. Evaluation alternates AND and OR, starting
with the supplied root operation. Its compiler produces an ordinary CSLib
circuit, with exactly the counted AND/OR gates and no extra literal layer.
Empty lists supply constants without introducing special constant gates.

This syntax records formulas, so duplicating a subtree duplicates its gates.
It supplies upper-bound witnesses in CSLib's shared circuit model.
-/

@[expose] public section

namespace Complexity.Shallow

/-- Alternating unbounded layers, with signed primary inputs at depth zero. -/
abbrev Layer (n : ℕ) : ℕ → Type
  | 0 => Fin n × Bool
  | d + 1 => List (Layer n d)

namespace Layer

/-- The number of AND/OR gates; literal occurrences are free. -/
def size {n : ℕ} : {d : ℕ} → Layer n d → ℕ
  | 0, _ => 0
  | _ + 1, fs => 1 + (fs.map size).sum

/-- Evaluate alternating layers, with `op` at the root. -/
def eval {n : ℕ} : {d : ℕ} → AndOrOp → Layer n d → BitString n → Bool
  | 0, _, l, x => l.2.xor (x l.1)
  | _ + 1, .and, fs, x => fs.all (fun f => eval .or f x)
  | _ + 1, .or, fs, x => fs.any (fun f => eval .and f x)

/-- Substitute signed inputs. This changes no gates or layers. -/
def mapInputs {n m : ℕ} (ρ : Fin n → Fin m × Bool) :
    {d : ℕ} → Layer n d → Layer m d
  | 0, l => ((ρ l.1).1, l.2.xor (ρ l.1).2)
  | _ + 1, fs => fs.map (mapInputs ρ)

/-- De Morgan negation flips the root operation and every input sign. -/
def neg {n d : ℕ} (f : Layer n d) : Layer n d :=
  mapInputs (fun i => (i, true)) f

end Layer
end Complexity.Shallow
