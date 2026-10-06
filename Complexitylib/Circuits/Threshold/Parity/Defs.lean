/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Circuits.Family.Defs
public import Complexitylib.Circuits.Threshold.Defs

/-!
# Depth-two threshold circuits for parity -- definitions

On `N` inputs, internal gate `j < N` is the unweighted threshold gate "at least
`j + 1` of the inputs are true". If `w` inputs are true, gate `j` is true
exactly when `j < w`. The output gate reads every internal gate, negating the
odd-indexed ones through the free per-input flags, and fires when at least
`N / 2 + 1` of these signed inputs are true. Exactly `N / 2 + w % 2` of them
are true, so the output is the parity of `w`.

The circuit has `N` internal gates and one output gate, so its size is `N + 1`,
and its depth is two. The family answers `false` on the empty input, the parity
of the empty string.
-/


@[expose] public section

namespace Complexity

namespace Circuit

/-- Internal gate `j` of the parity circuit on `N` inputs: true exactly when at
least `j + 1` of the `N` primary inputs are true. -/
def thresholdParityLayerGate (N : ℕ) (j : Fin N) : Gate Basis.threshold (N + N) where
  op := ThresholdOp.mk (j.val + 1)
  fanIn := N
  arityOk := trivial
  inputs i := Fin.castAdd N i
  negated _ := false

/-- Output gate of the parity circuit on `N` inputs: it reads internal gate `j`
for every `j < N`, negated exactly when `j` is odd, and requires at least
`N / 2 + 1` true signed inputs. -/
def thresholdParityOutputGate (N : ℕ) : Gate Basis.threshold (N + N) where
  op := ThresholdOp.mk (N / 2 + 1)
  fanIn := N
  arityOk := trivial
  inputs j := Fin.natAdd N j
  negated j := decide (j.val % 2 = 1)

/-- The depth-two threshold circuit for `N`-input parity, with `N` internal
gates. -/
def thresholdParity (N : ℕ) [NeZero N] : Circuit Basis.threshold N 1 N where
  gates := thresholdParityLayerGate N
  outputs _ := thresholdParityOutputGate N
  acyclic i k := by
    have hk : k.val < N := k.isLt
    show k.val < N + i.val
    omega

end Circuit

/-- The threshold-circuit family for parity: `Circuit.thresholdParity n` at
every positive length `n`, and `false` on the empty input. -/
def CircuitFamily.thresholdParity : CircuitFamily Basis.threshold where
  emptyOutput := false
  circuits n _ := ⟨n, Circuit.thresholdParity n⟩

end Complexity
