/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Circuits.KarchmerWigderson.Circuit.Internal

/-!
# Circuit depth and wires bound KW rounds and message alphabets

This is the general Karchmer--Wigderson translation for the library's
unbounded-fan-in AND/OR circuits, including free negation flags on gate inputs.
`totalFanIn` counts every gate-input occurrence, including output gates and
repeated wires. The protocol has no more rounds than the circuit has layers.
-/

public section

namespace Complexity.Circuit

/-- A depth-`d` unbounded AND/OR circuit gives a general KW protocol with
at most `d` messages, each drawn from an alphabet of size `totalFanIn`.
This holds for each output, including constants and negated internal wires. -/
theorem exists_roundProtocol {N M G : ℕ} [NeZero N] [NeZero M]
    (c : Circuit Basis.unboundedAndOr N M G) (d : ℕ) (hd : c.depth ≤ d) (j : Fin M) :
    ∃ P : KarchmerWigderson.RoundProtocol (Fin N) (Fin c.totalFanIn) d,
      P.SolvesKW (fun x => c.eval x j) := exists_roundProtocol_internal c d hd j

end Complexity.Circuit
