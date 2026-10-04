/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Aggregate.Geometry.Defs
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Aggregate.Capacity.Circuit.Defs

/-!
# Boolean one-way messages for signed gates

Each gate sends one bit determined only by selected primary inputs. Affine gates
send the partial parity and conjunctions send the conjunction of selected literals.
One spare coordinate covers a directly designated primary output.
-/

@[expose] public section

namespace Algebraic.Aggregate.Geometry

open Capacity (selected)

/-- Conjunction of selected primary literals. -/
def conjunctionSummary {r n g : ℕ} (polarity : Fin r → Bool)
    (wires : Fin r → Wire n g) (U : Finset (Fin n)) (x : Wire n g → Bool) : Bool :=
  decide (∀ i, selected U (wires i) → x (wires i) = polarity i)

/-- A gate sends only its partial aggregate of selected primary inputs. -/
def lineSummary {n g : ℕ} (line : Line signature n g) (U : Finset (Fin n))
    (x : Wire n g → Bool) : Bool :=
  match line with
  | ⟨.affine _ _ coefficient, wires⟩ =>
      xorSum fun i => if selected U (wires i) then coefficient i && x (wires i) else false
  | ⟨.conjunction _ polarity _, wires⟩ => conjunctionSummary polarity wires U x

/-- The vector of Boolean messages, one for each actual gate. -/
def key {n g : ℕ} (p : Program signature n g) (U : Finset (Fin n))
    (x : Fin n → Bool) : Fin g → Bool :=
  fun gate => lineSummary (p.lines gate) U (Wire.elim x (fun _ => false))

/-- The message includes at most one extra bit for a designated primary output. -/
def outputKey {n g : ℕ} (p : Program signature n g) (U : Finset (Fin n))
    (out : Wire n g) (x : Fin n → Bool) : Fin (g + 1) → Bool :=
  Fin.lastCases (if selected U out then Wire.elim x (fun _ => false) out else false)
    (key p U x)

end Algebraic.Aggregate.Geometry
