/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import Complexitylib.Circuits.FormulaEncoding.BitNavigation.Defs
import Complexitylib.Circuits.FormulaEncoding.Navigation.Defs

/-!
# Forward navigation in postfix formula codes -- definitions

A streaming machine decodes token bits from left to right. This navigation
state tracks the postfix evaluation-stack height and remembers the last token
and bit boundary at which that height was one. In the rootless body of a
binary formula, that last boundary is exactly the end of the left child.
-/

namespace Complexity

namespace FormulaCode

/-- Logarithmic numeric state retained by one forward postfix scan. -/
structure ForwardScanState where
  /-- Current number of completed formula values on the postfix stack. -/
  stackHeight : ℕ
  /-- Number of tokens consumed by this scan. -/
  tokenCount : ℕ
  /-- Number of encoded token bits consumed by this scan. -/
  bitOffset : ℕ
  /-- Most recent token count at which `stackHeight` became one. -/
  lastOneCount : ℕ
  /-- Matching encoded-bit offset at that same boundary. -/
  lastOneBitOffset : ℕ
  deriving DecidableEq

/-- Canonical zero state for scanning a complete postfix segment body. -/
def ForwardScanState.initial : ForwardScanState :=
  { stackHeight := 0
    tokenCount := 0
    bitOffset := 0
    lastOneCount := 0
    lastOneBitOffset := 0 }

/-- Consume one token, using saturated subtraction on malformed prefixes. -/
def ForwardScanState.step (state : ForwardScanState)
    (token : Token) : ForwardScanState :=
  let nextHeight := state.stackHeight + 1 - token.arity
  let nextCount := state.tokenCount + 1
  let nextBitOffset := state.bitOffset + token.codeLength
  { stackHeight := nextHeight
    tokenCount := nextCount
    bitOffset := nextBitOffset
    lastOneCount :=
      if nextHeight = 1 then nextCount else state.lastOneCount
    lastOneBitOffset :=
      if nextHeight = 1 then nextBitOffset else state.lastOneBitOffset }

/-- Stream a list of postfix tokens from an arbitrary retained state. -/
def forwardScan : List Token → ForwardScanState → ForwardScanState
  | [], state => state
  | token :: stream, state => forwardScan stream (state.step token)

/-- Closed form of scanning one canonical formula from an arbitrary stack
height. When the incoming height is zero, the formula's final boundary becomes
the last height-one boundary; above zero no height-one boundary is crossed. -/
def ForwardScanState.afterFormula (state : ForwardScanState)
    (formula : BoolFormula) : ForwardScanState :=
  let nextCount := state.tokenCount + formula.size
  let nextBitOffset := state.bitOffset + tokensCodeLength (tokens formula)
  { stackHeight := state.stackHeight + 1
    tokenCount := nextCount
    bitOffset := nextBitOffset
    lastOneCount :=
      if state.stackHeight = 0 then nextCount else state.lastOneCount
    lastOneBitOffset :=
      if state.stackHeight = 0 then nextBitOffset else state.lastOneBitOffset }

end FormulaCode

end Complexity
