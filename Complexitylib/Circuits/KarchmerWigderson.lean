/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Complexitylib.Circuits.KarchmerWigderson.Defs
public import Complexitylib.Circuits.KarchmerWigderson.Internal

/-!
# The monotone Karchmer--Wigderson correspondence

The protocol model tracks its zero-input and one-input rectangles in the type.
Alice partitions the one-input side, Bob partitions the zero-input side, and a
leaf supplies one coordinate separating the whole remaining rectangle.

The translations are depth-exact:

* Alice nodes become disjunctions and Bob nodes become conjunctions.
* A monotone formula recursively gives a protocol of the same depth.

Consequently a Boolean function has a depth-`d` monotone formula exactly when
its root Karchmer--Wigderson relation has a depth-`d` protocol in this model.
No uniformity condition is present.
-/

@[expose] public section

namespace Complexity
namespace KarchmerWigderson
namespace Protocol

/-- A protocol's formula is false throughout its zero-input rectangle. -/
theorem eval_toFormula_eq_false
    {zeroInputs oneInputs : Set (BitString N)}
    (protocol : Protocol N zeroInputs oneInputs)
    {input : BitString N} (hinput : input ∈ zeroInputs) :
    protocol.toFormula.eval input = false :=
  eval_toFormula_eq_false_internal protocol hinput

/-- A protocol's formula is true throughout its one-input rectangle. -/
theorem eval_toFormula_eq_true
    {zeroInputs oneInputs : Set (BitString N)}
    (protocol : Protocol N zeroInputs oneInputs)
    {input : BitString N} (hinput : input ∈ oneInputs) :
    protocol.toFormula.eval input = true :=
  eval_toFormula_eq_true_internal protocol hinput

/-- Protocol-to-formula translation preserves depth exactly. -/
theorem depth_toFormula
    {zeroInputs oneInputs : Set (BitString N)}
    (protocol : Protocol N zeroInputs oneInputs) :
    protocol.toFormula.depth = protocol.depth :=
  depth_toFormula_internal protocol

/-- The formula extracted from a root protocol computes the underlying
function. -/
theorem toFormula_computes (function : BitString N → Bool)
    (protocol : RootProtocol function) :
    protocol.toFormula.Computes function :=
  toFormula_computes_internal function protocol

/-- Every monotone formula computing `function` yields a root protocol of
exactly the same depth. -/
theorem exists_protocol_of_formula
    (formula : MonotoneFormula N) (function : BitString N → Bool)
    (computes : formula.Computes function) :
    ∃ protocol : RootProtocol function,
      protocol.depth = formula.depth :=
  exists_protocol_of_formula_internal formula function computes

/-- Every root protocol yields a monotone formula of exactly the same depth. -/
theorem exists_formula_of_protocol
    (function : BitString N → Bool)
    (protocol : RootProtocol function) :
    ∃ formula : MonotoneFormula N,
      formula.Computes function ∧ formula.depth = protocol.depth :=
  exists_formula_of_protocol_internal function protocol

/-- **Monotone Karchmer--Wigderson correspondence.** A root protocol of depth
at most `depthBound` exists exactly when a monotone formula of that depth
exists. -/
theorem exists_protocol_depth_iff_formula_depth
    (function : BitString N → Bool) (depthBound : ℕ) :
    (∃ protocol : RootProtocol function,
      protocol.depth ≤ depthBound) ↔
    ∃ formula : MonotoneFormula N,
      formula.Computes function ∧ formula.depth ≤ depthBound :=
  exists_protocol_depth_iff_formula_depth_internal function depthBound

end Protocol
end KarchmerWigderson
end Complexity
