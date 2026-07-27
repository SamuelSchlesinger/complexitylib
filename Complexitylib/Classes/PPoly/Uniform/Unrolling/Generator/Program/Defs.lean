/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Complexitylib.Classes.PPoly.Uniform.Unrolling.Serializer.Bounds.Defs
public import Complexitylib.Models.TuringMachine.Experimental.BinaryRoutine.Arithmetic.Defs
public import Complexitylib.Models.TuringMachine.Experimental.BinaryRoutine.Control.Defs
public import Complexitylib.Models.TuringMachine.Experimental.BinaryRoutine.List.Defs

/-!
# Direct-unrolling generator program -- definitions

The final serializer uses one fixed work-vector layout. Its prefix evaluates
the normalized horizon, padded wire frontier, and gate-count header as fixed
polynomials of the unary input length. The zero-length family member is a
hardwired two-bit word; the positive tableau body remains a compositional
`BinaryRoutine` parameter at this layer.
-/

@[expose] public section

namespace Complexity

namespace CircuitUnrolling

namespace Serializer

namespace DirectGenerator

/-- Fixed number of binary work tapes used by the direct serializer. -/
abbrev WorkCount : ℕ := 32

/- Named positions in the serializer's canonical binary work vector. -/
namespace Work

/-- Unary input length in canonical binary. -/
def inputLength : Fin WorkCount := 0
/-- Normalized tableau horizon. -/
def horizon : Fin WorkCount := 1
/-- Closed padded raw-gate bound. -/
def gateBound : Fin WorkCount := 2
/-- First wire after all padded gates. -/
def frontier : Fin WorkCount := 3
/-- Positive member's encoded gate count. -/
def gateCount : Fin WorkCount := 4
/-- First currently unused circuit wire. -/
def available : Fin WorkCount := 5
/-- Base wire of the current tableau configuration. -/
def configBase : Fin WorkCount := 6
/-- First dynamically prepared gate reference. -/
def reference₀ : Fin WorkCount := 7
/-- Second dynamically prepared gate reference. -/
def reference₁ : Fin WorkCount := 8
/-- Reusable zero counter for code emission. -/
def emitCounter : Fin WorkCount := 9
/-- Reusable zero counter for binary copying. -/
def copyCounter : Fin WorkCount := 10
/-- Alternate accumulator for polynomial evaluation. -/
def polynomialScratch : Fin WorkCount := 11
/-- Reusable multiplication counter. -/
def multiplyCounter : Fin WorkCount := 12
/-- Reusable addition counter. -/
def addCounter : Fin WorkCount := 13
/-- Outermost dynamic loop counter. -/
def loop₀ : Fin WorkCount := 14
/-- Outermost dynamic loop limit. -/
def limit₀ : Fin WorkCount := 15
/-- Second dynamic loop counter. -/
def loop₁ : Fin WorkCount := 16
/-- Second dynamic loop limit. -/
def limit₁ : Fin WorkCount := 17
/-- Third dynamic loop counter. -/
def loop₂ : Fin WorkCount := 18
/-- Third dynamic loop limit. -/
def limit₂ : Fin WorkCount := 19
/-- Innermost dynamic loop counter. -/
def loop₃ : Fin WorkCount := 20
/-- Innermost dynamic loop limit. -/
def limit₃ : Fin WorkCount := 21
/-- First general arithmetic temporary. -/
def temporary₀ : Fin WorkCount := 22
/-- Second general arithmetic temporary. -/
def temporary₁ : Fin WorkCount := 23
/-- Third general arithmetic temporary. -/
def temporary₂ : Fin WorkCount := 24
/-- Fourth general arithmetic temporary. -/
def temporary₃ : Fin WorkCount := 25
/-- Original acceptance wire saved before padding. -/
def savedOutput : Fin WorkCount := 26
/-- Numeric movement-direction code. -/
def direction : Fin WorkCount := 27
/-- Numeric configuration-atom phase code. -/
def atomKind : Fin WorkCount := 28
/-- Numeric named-tape index. -/
def tapeIndex : Fin WorkCount := 29
/-- Numeric head or cell position. -/
def position : Fin WorkCount := 30
/-- Numeric four-symbol alphabet index. -/
def symbolIndex : Fin WorkCount := 31

end Work

/-- Pure work-vector state after evaluating the positive member's three
polynomial counters and initializing both running wire bases to the input
length. Scratch values are unchanged because every arithmetic leaf restores
them exactly. -/
noncomputable def preambleValues (tm : TM k) (q : Polynomial ℕ)
    (values : BinaryValues WorkCount) : BinaryValues WorkCount :=
  let values := Function.update values Work.horizon
    ((TM.directSerializerHorizonPolynomial q).eval
      (values Work.inputLength))
  let values := Function.update values Work.frontier
    ((TM.directSerializerFrontierPolynomial tm q).eval
      (values Work.inputLength))
  let values := Function.update values Work.gateCount
    ((TM.directSerializerGateCountPolynomial tm q).eval
      (values Work.inputLength))
  let values := Function.update values Work.available
    (values Work.inputLength)
  Function.update values Work.configBase (values Work.inputLength)

/-- Arithmetic and tagged-header prefix of every positive family member. -/
noncomputable def positivePreamble (tm : TM k) (q : Polynomial ℕ) :
    BinaryRoutine WorkCount :=
  BinaryRoutine.seqList
    [BinaryRoutine.evalPolynomial Work.inputLength Work.horizon
      Work.polynomialScratch Work.multiplyCounter Work.addCounter
      (TM.directSerializerHorizonPolynomial q),
     BinaryRoutine.evalPolynomial Work.inputLength Work.frontier
      Work.polynomialScratch Work.multiplyCounter Work.addCounter
      (TM.directSerializerFrontierPolynomial tm q),
     BinaryRoutine.evalPolynomial Work.inputLength Work.gateCount
      Work.polynomialScratch Work.multiplyCounter Work.addCounter
      (TM.directSerializerGateCountPolynomial tm q),
     BinaryRoutine.binaryCopy Work.inputLength Work.available Work.copyCounter,
     BinaryRoutine.binaryCopy Work.inputLength Work.configBase Work.copyCounter,
     BinaryRoutine.emitBits [true],
     BinaryRoutine.emitNatCode Work.emitCounter Work.gateCount]

/-- Prefix a positive tableau body with its tag and exact padded gate-count
header. -/
noncomputable def positiveMember (tm : TM k) (q : Polynomial ℕ)
    (body : BinaryRoutine WorkCount) : BinaryRoutine WorkCount :=
  BinaryRoutine.seq (positivePreamble tm q) body

/-- Hardwired tagged code of the unique length-zero family member. -/
noncomputable def zeroMember (tm : TM k) (q : Polynomial ℕ) :
    BinaryRoutine WorkCount :=
  BinaryRoutine.emitBits
    [false,
      boundedAcceptanceBit tm.toNTM
        ((TM.directSerializerHorizonPolynomial q).eval 0)
        (fun index => Fin.elim0 index) (fun _ => false)]

/-- Complete generator skeleton, branching on whether the loaded input length
is zero before entering the positive tableau body. -/
noncomputable def program (tm : TM k) (q : Polynomial ℕ)
    (positiveBody : BinaryRoutine WorkCount) : BinaryRoutine WorkCount :=
  BinaryRoutine.branchZero Work.inputLength (zeroMember tm q)
    (positiveMember tm q positiveBody)

end DirectGenerator

end Serializer

end CircuitUnrolling

end Complexity
