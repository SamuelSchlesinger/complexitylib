/-
Copyright (c) 2025 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import Complexitylib.Circuits.Basic
import Complexitylib.Circuits.BitString
import Complexitylib.Circuits.DecisionTree
import Complexitylib.Circuits.Formula
import Complexitylib.Circuits.FormulaEncoding
import Complexitylib.Circuits.FormulaEncoding.Navigation
import Complexitylib.Circuits.FormulaEncoding.ForwardNavigation
import Complexitylib.Circuits.FormulaEncoding.BitNavigation
import Complexitylib.Circuits.FormulaEncoding.ProbeNavigation
import Complexitylib.Circuits.CircuitFormula
import Complexitylib.Circuits.Restriction
import Complexitylib.Circuits.BranchingProgram
import Complexitylib.Circuits.Barrington
import Complexitylib.Circuits.BarringtonS5
import Complexitylib.Circuits.BarringtonBridge
import Complexitylib.Circuits.BarringtonRepr
import Complexitylib.Circuits.BarringtonLength
import Complexitylib.Circuits.BarringtonCompiler
import Complexitylib.Circuits.BarringtonStreaming
import Complexitylib.Circuits.BarringtonSlots
import Complexitylib.Circuits.BarringtonSlotQuery
import Complexitylib.Circuits.BarringtonTokenQuery
import Complexitylib.Circuits.BarringtonBitQuery
import Complexitylib.Circuits.BarringtonBitSerializer
import Complexitylib.Circuits.BarringtonProbeQuery
import Complexitylib.Circuits.BarringtonProbeSerializer
import Complexitylib.Circuits.BranchingProgramEncoding
import Complexitylib.Circuits.BranchingProgramEncoding.Machine
import Complexitylib.Circuits.BarringtonCodeGenerator
import Complexitylib.Circuits.BarringtonFamily
import Complexitylib.Circuits.BarringtonConverse
import Complexitylib.Circuits.CircuitFormula.Family
import Complexitylib.Circuits.MultilinearExtension
import Complexitylib.Circuits.NormalForm
import Complexitylib.Circuits.AndOrNot
import Complexitylib.Circuits.Encoding
import Complexitylib.Circuits.Family
import Complexitylib.Circuits.Encoding.Family
import Complexitylib.Circuits.Encoding.Machine
import Complexitylib.Circuits.XOR
import Complexitylib.Circuits.EssentialInput
import Complexitylib.Circuits.Shannon
import Complexitylib.Circuits.LowerBound
import Complexitylib.Circuits.Schnorr
import Complexitylib.Circuits.DepthClasses
import Complexitylib.Circuits.AC0
import Complexitylib.Circuits.Nondeterminism
import Complexitylib.Circuits.Hardwiring
import Complexitylib.Circuits.Unrolling
import Complexitylib.Circuits.Valiant

/-! # Circuit Complexity Library

A Lean 4 formalization of classical results in Boolean circuit complexity,
built on Mathlib.

## The circuit model

A `Circuit B N M G` is an acyclic Boolean circuit over basis `B` with `N`
primary inputs, `M` outputs, and `G` internal gates. The circuit's `size`
is `G + M`: internal and output gates are counted, while primary-input
vertices and per-edge negation flags are not. The `sizeComplexity` of a
Boolean function is the minimum size of any circuit computing it under this
convention.

## Main results

* **Functional completeness** (`CompleteBasis Basis.unboundedAndOr`):
  Unbounded fan-in AND/OR (with free negation) can compute every Boolean
  function, via DNF construction.

* **Shannon counting lower bound** (`shannon_lower_bound_circuit`):
  For `N ≥ 6`, there exists a Boolean function on `N` inputs that cannot
  be computed by any fan-in-2 AND/OR circuit with fewer than `2^N / (5N)`
  gates.

* **Gate elimination lower bound** (`Circuit.card_essentialInputs_le_mul_size`,
  also stated as `Circuit.card_essentialInputs_le_mul_size`): Any circuit over
  bounded fan-in `k` AND/OR computing a function with `n'` essential inputs
  satisfies `n' ≤ k · size`, i.e. has size at least `n' / k`.

* **Schnorr's XOR lower bound** (`schnorr_lower_bound_circuit`):
  Any fan-in-2 AND/OR circuit computing N-input XOR (or its complement)
  requires at least `2(N − 1)` internal gates.

* **CNF/DNF lower bound for XOR** (`DNF.two_pow_le_complexity_of_xorBool`,
  `CNF.two_pow_le_complexity_of_xorBool`): Any DNF (resp. CNF) computing N-input XOR
  requires at least `2^{N-1}` terms (resp. clauses).

* **Nondeterministic quantification** (`sizeComplexity_existsQuantify_le`):
  If `f` has circuit complexity `s`, then `∃ x ∈ {0,1}^k, f(x,y)` has
  circuit complexity at most `2^k · (s + 1)`.  Combined with the Shannon
  upper bound (`sizeComplexity_existsQuantify_le_min`).

* **Valiant's depth reduction** (`Valiant.depth_reduction`):
  In any acyclic digraph with `S` edges and depth at most `2^k`, for any `r ≤ k`
  one can remove a set of at most `r · S / k` edges so that the remaining
  digraph has depth at most `2^k / 2^r`.

* **Barrington's theorem** (`barrington_equivalence`):
  Logarithmic-depth Boolean formula families are exactly polynomial-length
  width-`5` permutation branching-program families. The finite forward theorem
  `barrington_representation_depth_four` gives the textbook length bound
  `4 ^ depth`, and `barrington_quadratic_of_log_depth` specializes it to `n²`
  at depth at most `log₂ n`.
  `barringtonCompile_representation` supplies the same finite theorem through
  an explicit executable compiler rather than an existential choice.
  `BPCode.Program.decode?_encode` verifies the canonical serialized output
  format needed by the remaining log-space uniformity proof.
  `barringtonCompileCode_spec` then connects canonical formula bits to canonical
  program bits, exact semantics, and a serialized output-size bound.
  `barringtonCompileStream_instruction?` gives the corresponding exact
  random-access instruction view without constructing the complete program,
  while `barringtonCompileSlot?_eq_instruction?` follows one branch of the
  fixed `4^D` address schedule and returns exactly its selected instruction,
  while `barringtonCompileTokensSlot?_eq_instruction?` carries that query over
  canonical postfix tokens using stack-free child-span recovery, and
  `barringtonCompileBitsSlot?_eq_instruction?` performs the same query directly
  over canonical encoded formula bits. `barringtonCompileProbeSlot?_eq_instruction?`
  further replaces the complete bit list by a position-indexed source oracle,
  with explicit finite decoding fuel. `barringtonCompileBitsCode_eq` then proves
  the fixed-address two-pass serializer emits the exact canonical code.
  `BoolFunFamily.onTotalAssignments_mem_Width5BP` applies the theorem to the
  total-assignment view of an actual typed `NC1` circuit family.

## Module structure

Public modules (definitions a reviewer should read):

* `Complexitylib.Circuits.Basic` — `BitString`, `BoolFunFamily`, `Circuit`, `Basis`, `Gate`,
  `CompleteBasis`, `sizeComplexity`, `wireDepth`, `depth`
* `Complexitylib.Circuits.BitString` — canonical bridges between `BitString n`
  and `List Bool`
* `Complexitylib.Circuits.CircuitFormula` — exact selected-output unfolding from
  fan-in-two circuit DAGs to Boolean formulas, with a factor-two depth bound
* `Complexitylib.Circuits.FormulaEncoding` — canonical iterative postfix formula
  codec with exact round trips and code length
* `Complexitylib.Circuits.FormulaEncoding.ProbeNavigation` — exact token,
  subtree, and child-span navigation through a position-indexed bit oracle
* `Complexitylib.Circuits.CircuitFormula.Family` — family-level unfolding and
  the typed-`NC1` bridge to width-`5` branching programs
* `Complexitylib.Circuits.Family` — circuit families, list semantics, pointwise
  size/depth bounds, and the polynomial-size characterization
* `Complexitylib.Circuits.BarringtonConverse` — balanced branching-program
  evaluation and the nonuniform Barrington equivalence
* `Complexitylib.Circuits.BarringtonCompiler` — executable finite `S₅` search
  and formula-to-program compilation with the `4 ^ depth` bound
* `Complexitylib.Circuits.BarringtonStreaming` — random-access compilation by
  instruction index without materializing the complete recursive program
* `Complexitylib.Circuits.BarringtonSlots` — exact placement of compiled
  instructions in a depth-bounded fixed-address schedule
* `Complexitylib.Circuits.BarringtonSlotQuery` — structural first/last occupied
  addresses and exact direct lookup in that fixed schedule
* `Complexitylib.Circuits.BarringtonTokenQuery` — the same exact fixed-slot
  query over canonical postfix token streams, without reconstructing a formula
* `Complexitylib.Circuits.BarringtonBitQuery` — the fixed-slot query directly
  over canonical encoded formula bits, with bit-level child-span recovery
* `Complexitylib.Circuits.BarringtonBitSerializer` — exact two-pass canonical
  serialization by scanning the fixed encoded-bit address schedule
* `Complexitylib.Circuits.BarringtonProbeQuery` — exact fixed-address queries
  through restartable position-indexed formula-code probes
* `Complexitylib.Circuits.BranchingProgramEncoding` — canonical seven-bit
  permutation ranks, instruction/program codecs, and exact size bounds
* `Complexitylib.Circuits.BranchingProgramEncoding.Machine` — framed,
  one-way machine emission of canonical instruction codes from binary registers
* `Complexitylib.Circuits.BarringtonCodeGenerator` — the total bitstring-level
  formula-code-to-program-code reference for promised log-depth `FL` generation
* `Complexitylib.Circuits.Encoding` — canonical proof-free encoding, validation,
  and iterative evaluation of fan-in-two AND/OR circuits
* `Complexitylib.Circuits.Encoding.Family` — tagged encoding and evaluation at
  every input length, including the explicit empty-input answer
* `Complexitylib.Circuits.Encoding.Machine` — total linear-time validation and
  tape staging plus the verified end-to-end quadratic serialized circuit-family
  evaluator
* `Complexitylib.Circuits.Encoding.Machine.NatCode` — framed, one-way
  terminated-unary natural-code emission from a preserved binary value, with
  reusable zero scratch and explicit time/all-prefix-space bounds
* `Complexitylib.Circuits.AndOrNot.Defs` — `AndOrOp`, `Basis.unboundedAndOr`,
  `Basis.boundedAndOr`, `Basis.andOr2`
* `Complexitylib.Circuits.NormalForm.Defs` — `Literal`, `CNF`, `DNF`, `CNF.complexity`,
  `DNF.complexity`
* `Complexitylib.Circuits.NormalForm` — CNF/DNF lower bound for XOR
  (`two_pow_le_complexity_of_xorBool`)
* `Complexitylib.Circuits.XOR` — `Schnorr.xorBool` (N-input parity)
* `Complexitylib.Circuits.EssentialInput` — `IsEssentialInput`, `essentialInputs`
* `Complexitylib.Circuits.DepthClasses` — `DEPTH`, the nonuniform `NC` and `AC`
  hierarchies, and the aliases `NC0`, `NC1`, and `AC0`
* `Complexitylib.Circuits.AC0` — compatibility import for `AC0`
* `Complexitylib.Circuits.Nondeterminism.Defs` — `existsQuantify`, `forallQuantify`
* `Complexitylib.Circuits.Hardwiring` — exact-size prefix hardwiring
* `Complexitylib.Circuits.Unrolling` — bounded machine-configuration layouts,
  initialization, verified trace tiling, typed acceptance circuits, exact-size
  fixed-choice hardwiring, and parallel strict-majority amplification

Theorem modules (re-export definitions + main results):

* `Complexitylib.Circuits.AndOrNot` — functional completeness of AND/OR
* `Complexitylib.Circuits.Shannon` — Shannon counting lower bound
* `Complexitylib.Circuits.LowerBound` — gate elimination lower bound
* `Complexitylib.Circuits.Schnorr` — Schnorr's XOR lower bound
* `Complexitylib.Circuits.Nondeterminism` — nondeterministic quantification complexity bounds
* `Complexitylib.Circuits.Valiant` — Valiant's depth reduction lemma for digraphs

Internal modules contain proof machinery (CircDesc, DNF construction,
restriction/elimination arguments) and are not intended for direct use.
-/
