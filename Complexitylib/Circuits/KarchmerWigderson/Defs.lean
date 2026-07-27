/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Mathlib.Data.Set.Basic
public import Complexitylib.Circuits.Monotone.Defs

/-!
# Karchmer--Wigderson protocols -- definitions

A protocol is indexed by its current zero-input and one-input rectangles.
Alice partitions the one-input side and Bob partitions the zero-input side.
At a leaf, one coordinate separates every zero input from every one input in
the current rectangle.
-/

@[expose] public section

namespace Complexity
namespace KarchmerWigderson

/-- A protocol for finding a coordinate where a zero input has value `0` and
a one input has value `1`.

The two `Set` indices record the current combinatorial rectangle. An Alice node
partitions the one-input side; a Bob node partitions the zero-input side. -/
inductive Protocol (N : ℕ) :
    Set (BitString N) → Set (BitString N) → Type where
  /-- A coordinate separating the entire current rectangle. The conditions are
  stated separately on the two sides, including for empty rectangles. -/
  | leaf {zeroInputs oneInputs : Set (BitString N)}
      (index : Fin N)
      (zeroAt : ∀ input ∈ zeroInputs, input index = false)
      (oneAt : ∀ input ∈ oneInputs, input index = true) :
      Protocol N zeroInputs oneInputs
  /-- Alice partitions the one-input side according to `choice`. -/
  | alice {zeroInputs oneInputs : Set (BitString N)}
      (choice : BitString N → Bool)
      (ifFalse : Protocol N zeroInputs
        {input | input ∈ oneInputs ∧ choice input = false})
      (ifTrue : Protocol N zeroInputs
        {input | input ∈ oneInputs ∧ choice input = true}) :
      Protocol N zeroInputs oneInputs
  /-- Bob partitions the zero-input side according to `choice`. -/
  | bob {zeroInputs oneInputs : Set (BitString N)}
      (choice : BitString N → Bool)
      (ifFalse : Protocol N
        {input | input ∈ zeroInputs ∧ choice input = false} oneInputs)
      (ifTrue : Protocol N
        {input | input ∈ zeroInputs ∧ choice input = true} oneInputs) :
      Protocol N zeroInputs oneInputs

namespace Protocol

/-- Worst-case communication depth. Leaves have depth zero and every message
adds one. -/
def depth {zeroInputs oneInputs : Set (BitString N)} :
    Protocol N zeroInputs oneInputs → ℕ
  | .leaf _ _ _ => 0
  | .alice _ ifFalse ifTrue =>
      max ifFalse.depth ifTrue.depth + 1
  | .bob _ ifFalse ifTrue =>
      max ifFalse.depth ifTrue.depth + 1

/-- Translate a protocol tree to a monotone formula. Alice nodes become
disjunctions and Bob nodes become conjunctions. -/
def toFormula {zeroInputs oneInputs : Set (BitString N)} :
    Protocol N zeroInputs oneInputs → MonotoneFormula N
  | .leaf index _ _ => .var index
  | .alice _ ifFalse ifTrue =>
      .disj ifFalse.toFormula ifTrue.toFormula
  | .bob _ ifFalse ifTrue =>
      .conj ifFalse.toFormula ifTrue.toFormula

end Protocol

/-- The zero fiber of a Boolean function. -/
def zeroFiber (function : BitString N → Bool) : Set (BitString N) :=
  {input | function input = false}

/-- The one fiber of a Boolean function. -/
def oneFiber (function : BitString N → Bool) : Set (BitString N) :=
  {input | function input = true}

/-- A root protocol for the monotone Karchmer--Wigderson relation of
`function`. -/
abbrev RootProtocol (function : BitString N → Bool) :=
  Protocol N (zeroFiber function) (oneFiber function)

end KarchmerWigderson
end Complexity
