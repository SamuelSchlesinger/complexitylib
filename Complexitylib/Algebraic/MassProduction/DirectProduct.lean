/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.Complexity
public import Complexitylib.Algebraic.Parallel
public import Mathlib.Logic.Equiv.Fin.Basic

/-!
# Independent block evaluation

This file formalizes the direct-product operation used by circuit mass
production. Inputs are stored as consecutive row-major blocks. It also builds
the naive circuit obtained by placing independent copies of one circuit side
by side, with exact semantic and cost accounting.

The construction is generic in the signature, interpretation, carrier, and
number of outputs. Boolean mass-production theorems specialize the scalar
case later.
-/

@[expose] public section

namespace Algebraic
namespace MassProduction

/-- Regard a scalar function as a one-output target. -/
def scalarTarget
    (function : ScalarFunction U n) : Target U n 1 :=
  fun input _ => function input

/-- Embed an index from the initial `copies` blocks into a layout with one
additional final block. -/
def blockPrefixIndex
    {copies width : Nat}
    (index : Fin (copies * width)) : Fin (copies.succ * width) :=
  Fin.cast (Nat.succ_mul copies width).symm (Fin.castAdd width index)

/-- Embed an index from the final block into a layout with `copies` preceding
blocks. -/
def blockSuffixIndex
    {copies width : Nat}
    (index : Fin width) : Fin (copies.succ * width) :=
  Fin.cast (Nat.succ_mul copies width).symm
    (Fin.natAdd (copies * width) index)

/-- Read the initial `copies` blocks of a layout with one additional final
block. -/
def blockPrefix
    {copies width : Nat}
    {U : Type u}
    (input : Fin (copies.succ * width) -> U) : Fin (copies * width) -> U :=
  input ∘ blockPrefixIndex

/-- Read the final block of a layout with `copies` preceding blocks. -/
def blockSuffix
    {copies width : Nat}
    {U : Type u}
    (input : Fin (copies.succ * width) -> U) : Fin width -> U :=
  input ∘ blockSuffixIndex

/-- Select one row-major input block. -/
def directProductInput
    (input : Fin (copies * n) -> U)
    (copy : Fin copies) : Fin n -> U :=
  fun index => input (finProdFinEquiv (copy, index))

/-- Apply a vector-valued target independently to consecutive input blocks. -/
def blockMap
    (target : Target U n m)
    (copies : Nat) : Target U (copies * n) (copies * m) :=
  fun input flatOutput =>
    let output := finProdFinEquiv.symm flatOutput
    target (directProductInput input output.1) output.2

/-- Evaluate one scalar function independently on `copies` row-major input
blocks and return all answers. This is the target denoted `f^{× copies}` in
the mass-production manuscript. -/
def directProduct
    (function : ScalarFunction U n)
    (copies : Nat) : Target U (copies * n) copies :=
  fun input copy => function (directProductInput input copy)

@[simp] theorem directProductInput_apply
    (input : Fin (copies * n) -> U)
    (copy : Fin copies)
    (index : Fin n) :
    directProductInput input copy index =
      input (finProdFinEquiv (copy, index)) := rfl

@[simp] theorem blockMap_apply
    (target : Target U n m)
    (input : Fin (copies * n) -> U)
    (copy : Fin copies)
    (output : Fin m) :
    blockMap target copies input (finProdFinEquiv (copy, output)) =
      target (directProductInput input copy) output := by
  simp [blockMap]

@[simp] theorem directProduct_apply
    (function : ScalarFunction U n)
    (input : Fin (copies * n) -> U)
    (copy : Fin copies) :
    directProduct function copies input copy =
      function (directProductInput input copy) := rfl

end MassProduction

namespace Circuit

open MassProduction

/-- Place `copies` independent, disjoint-input copies of one circuit side by
side. Sharing internal to the original circuit is preserved within each copy. -/
def _root_.Cslib.Circuits.Circuit.replicate
    (circuit : Circuit σ n m) :
    (copies : Nat) -> Circuit σ (copies * n) (copies * m)
  | 0 =>
      (Circuit.id σ 0).castCounts
        (Nat.zero_mul n).symm (Nat.zero_mul m).symm
  | copies + 1 =>
      let prefixCircuit := (replicate circuit copies).mapInputs
        (blockPrefixIndex (copies := copies) (width := n))
      let suffixCircuit := circuit.mapInputs
        (blockSuffixIndex (copies := copies) (width := n))
      (prefixCircuit.parallel suffixCircuit).castCounts rfl
        (Nat.succ_mul copies m).symm

export Cslib.Circuits.Circuit (replicate)

/-- Replication evaluates one selected copy exactly as the original circuit
on the corresponding row-major input block. -/
theorem _root_.Cslib.Circuits.Circuit.eval_replicate_apply
    (circuit : Circuit σ n m)
    (copies : Nat)
    (interpretation : Interpretation σ U)
    (input : Fin (copies * n) -> U)
    (copy : Fin copies)
    (output : Fin m) :
    (circuit.replicate copies).eval interpretation input
        (finProdFinEquiv (copy, output)) =
      circuit.eval interpretation (directProductInput input copy) output := by
  induction copies with
  | zero => exact Fin.elim0 copy
  | succ copies ih =>
      simp only [replicate, Circuit.eval_castCounts,
        Fin.cast_refl, Circuit.eval_parallel]
      by_cases isPrefix : copy.val < copies
      · let prefixCopy : Fin copies := ⟨copy.val, isPrefix⟩
        rw [show Fin.cast (Nat.succ_mul copies m)
            (finProdFinEquiv (copy, output)) =
            Fin.castAdd m (finProdFinEquiv (prefixCopy, output)) by
          apply Fin.ext
          simp [finProdFinEquiv, prefixCopy]]
        rw [Fin.append_left, Circuit.eval_mapInputs, ih]
        apply congrArg (fun selectedInput =>
          circuit.eval interpretation selectedInput output)
        funext index
        apply congrArg input
        apply Fin.ext
        simp [blockPrefixIndex, finProdFinEquiv, prefixCopy]
      · have last : copy.val = copies := by omega
        rw [show Fin.cast (Nat.succ_mul copies m)
            (finProdFinEquiv (copy, output)) =
            Fin.natAdd (copies * m) output by
          apply Fin.ext
          simp [finProdFinEquiv, last, Nat.mul_comm, Nat.add_comm]]
        rw [Fin.append_right, Circuit.eval_mapInputs]
        apply congrArg (fun selectedInput =>
          circuit.eval interpretation selectedInput output)
        funext index
        apply congrArg input
        apply Fin.ext
        simp [blockSuffixIndex, finProdFinEquiv, last,
          Nat.mul_comm, Nat.add_comm]

export Cslib.Circuits.Circuit (eval_replicate_apply)

/-- Replication applies the original circuit independently to all consecutive
input blocks. -/
theorem _root_.Cslib.Circuits.Circuit.eval_replicate
    (circuit : Circuit σ n m)
    (copies : Nat)
    (interpretation : Interpretation σ U)
    (input : Fin (copies * n) -> U) :
    (circuit.replicate copies).eval interpretation input =
      blockMap (circuit.eval interpretation) copies input := by
  funext flatOutput
  obtain ⟨⟨copy, output⟩, rfl⟩ := finProdFinEquiv.surjective flatOutput
  simpa only [blockMap_apply] using
    circuit.eval_replicate_apply copies interpretation input
      copy output

export Cslib.Circuits.Circuit (eval_replicate)

/-- Replication has exactly multiplicative weighted cost. -/
@[simp] theorem _root_.Cslib.Circuits.Circuit.cost_replicate
    (circuit : Circuit σ n m)
    (copies : Nat)
    (operationCost : OperationCost σ) :
    (circuit.replicate copies).cost operationCost =
      copies * circuit.cost operationCost := by
  induction copies with
  | zero => simp [replicate]
  | succ copies ih =>
      simp [replicate, ih, Nat.succ_mul]

export Cslib.Circuits.Circuit (cost_replicate)

/-- Replication has exactly `copies` times the original gate count. -/
@[simp] theorem _root_.Cslib.Circuits.Circuit.size_replicate
    (circuit : Circuit σ n m)
    (copies : Nat) :
    (circuit.replicate copies).size = copies * circuit.size := by
  calc
    (circuit.replicate copies).size =
        (circuit.replicate copies).cost OperationCost.unit :=
      (Circuit.cost_unit (circuit.replicate copies)).symm
    _ = copies * circuit.cost OperationCost.unit :=
      circuit.cost_replicate copies OperationCost.unit
    _ = copies * circuit.size := by rw [Circuit.cost_unit]

export Cslib.Circuits.Circuit (size_replicate)

/-- A scalar circuit replicated on disjoint inputs has the manuscript's
direct-product semantics after removing the trivial `Fin 1` output factor. -/
def _root_.Cslib.Circuits.Circuit.replicateScalar
    (circuit : Circuit σ n 1)
    (copies : Nat) : Circuit σ (copies * n) copies :=
  (circuit.replicate copies).mapOutputs fun copy =>
    finProdFinEquiv (copy, (0 : Fin 1))

export Cslib.Circuits.Circuit (replicateScalar)

@[simp] theorem _root_.Cslib.Circuits.Circuit.eval_replicateScalar
    (circuit : Circuit σ n 1)
    (copies : Nat)
    (interpretation : Interpretation σ U)
    (input : Fin (copies * n) -> U) :
    (circuit.replicateScalar copies).eval interpretation input =
      directProduct (circuit.outputFunction interpretation 0) copies input := by
  funext copy
  change (circuit.replicate copies).eval interpretation input
      (finProdFinEquiv (copy, (0 : Fin 1))) =
    circuit.eval interpretation (directProductInput input copy) 0
  exact circuit.eval_replicate_apply copies interpretation input copy 0

export Cslib.Circuits.Circuit (eval_replicateScalar)

@[simp] theorem _root_.Cslib.Circuits.Circuit.cost_replicateScalar
    (circuit : Circuit σ n 1)
    (copies : Nat)
    (operationCost : OperationCost σ) :
    (circuit.replicateScalar copies).cost operationCost =
      copies * circuit.cost operationCost := by
  simp [replicateScalar]

export Cslib.Circuits.Circuit (cost_replicateScalar)

@[simp] theorem _root_.Cslib.Circuits.Circuit.size_replicateScalar
    (circuit : Circuit σ n 1)
    (copies : Nat) :
    (circuit.replicateScalar copies).size =
      copies * circuit.size := by
  simp [replicateScalar]

export Cslib.Circuits.Circuit (size_replicateScalar)

/-- The concrete naive upper bound: `copies` disjoint copies of a scalar
circuit compute the direct product at exactly multiplicative cost. -/
theorem _root_.Cslib.Circuits.Circuit.replicateScalar_computes_directProduct
    {circuit : Circuit σ n 1}
    {interpretation : Interpretation σ U}
    {function : ScalarFunction U n}
    (computes : circuit.outputFunction interpretation 0 = function)
    (copies : Nat) :
    (circuit.replicateScalar copies).ComputesWith interpretation
      (directProduct function copies) := by
  intro input
  rw [Circuit.eval_replicateScalar, computes]

export Cslib.Circuits.Circuit (replicateScalar_computes_directProduct)

/-- Computation of a one-output target identifies its scalar output
function. -/
theorem _root_.Cslib.Circuits.Circuit.outputFunction_eq_of_computes_scalarTarget
    {circuit : Circuit σ n 1}
    {interpretation : Interpretation σ U}
    {function : ScalarFunction U n}
    (computes : circuit.ComputesWith interpretation (scalarTarget function)) :
    circuit.outputFunction interpretation 0 = function := by
  funext input
  exact congrFun (computes input) 0

/-! ## Retaining an initial sub-batch -/

export Cslib.Circuits.Circuit (outputFunction_eq_of_computes_scalarTarget)

/-- Send a copy of a larger batch to the same copy of a smaller batch when
it exists, and to copy zero otherwise.  The positivity premise is explicit
rather than hidden in an instance. -/
def _root_.Cslib.Circuits.Circuit.prefixOrZeroCopy
    (small : Nat) (smallPositive : 0 < small) (copy : Fin large) : Fin small :=
  if bounded : copy.val < small then
    ⟨copy.val, bounded⟩
  else
    ⟨0, smallPositive⟩

export Cslib.Circuits.Circuit (prefixOrZeroCopy)

@[simp] theorem _root_.Cslib.Circuits.Circuit.prefixOrZeroCopy_castLE
    (smallPositive : 0 < small)
    (smallLeLarge : small <= large)
    (copy : Fin small) :
    prefixOrZeroCopy small smallPositive (Fin.castLE smallLeLarge copy) =
      copy := by
  apply Fin.ext
  simp [prefixOrZeroCopy]

export Cslib.Circuits.Circuit (prefixOrZeroCopy_castLE)

/-- Rewire the inputs expected by a larger batch circuit onto a smaller
batch.  Inputs belonging to discarded copies are harmlessly redirected to
the first retained block. -/
def _root_.Cslib.Circuits.Circuit.prefixBatchInputMap
    (width small large : Nat)
    (smallPositive : 0 < small) :
    Fin (large * width) -> Fin (small * width) :=
  fun flatInput =>
    let copyInput := finProdFinEquiv.symm flatInput
    finProdFinEquiv
      (prefixOrZeroCopy small smallPositive copyInput.1, copyInput.2)

export Cslib.Circuits.Circuit (prefixBatchInputMap)

theorem _root_.Cslib.Circuits.Circuit.directProductInput_prefixBatchInputMap
    (smallPositive : 0 < small)
    (smallLeLarge : small <= large)
    (input : Fin (small * width) -> U)
    (copy : Fin small) :
    directProductInput
        (input ∘ prefixBatchInputMap width small large smallPositive)
        (Fin.castLE smallLeLarge copy) =
      directProductInput input copy := by
  funext bit
  simp only [directProductInput_apply, Function.comp_apply]
  unfold prefixBatchInputMap
  rw [Equiv.symm_apply_apply]
  dsimp only
  rw [prefixOrZeroCopy_castLE smallPositive smallLeLarge]

export Cslib.Circuits.Circuit (directProductInput_prefixBatchInputMap)

/-- A circuit for `large` independent copies yields, without adding gates, a
circuit for every positive initial batch of at most `large` copies. -/
def _root_.Cslib.Circuits.Circuit.takeDirectProductPrefix
    (circuit : Circuit sigma (large * width) large)
    (small : Nat)
    (smallPositive : 0 < small)
    (smallLeLarge : small <= large) :
    Circuit sigma (small * width) small :=
  (circuit.mapInputs
      (prefixBatchInputMap width small large smallPositive)).mapOutputs
    (Fin.castLE smallLeLarge)

export Cslib.Circuits.Circuit (takeDirectProductPrefix)

@[simp] theorem _root_.Cslib.Circuits.Circuit.takeDirectProductPrefix_cost
    (circuit : Circuit sigma (large * width) large)
    (smallPositive : 0 < small)
    (smallLeLarge : small <= large)
    (operationCost : OperationCost sigma) :
    (circuit.takeDirectProductPrefix small smallPositive smallLeLarge).cost
        operationCost = circuit.cost operationCost := by
  simp [Circuit.takeDirectProductPrefix]

export Cslib.Circuits.Circuit (takeDirectProductPrefix_cost)

/-- Retaining an initial sub-batch adds no gates. -/
@[simp] theorem _root_.Cslib.Circuits.Circuit.takeDirectProductPrefix_size
    (circuit : Circuit sigma (large * width) large)
    (smallPositive : 0 < small)
    (smallLeLarge : small <= large) :
    (circuit.takeDirectProductPrefix small smallPositive smallLeLarge).size =
      circuit.size := rfl

export Cslib.Circuits.Circuit (takeDirectProductPrefix_size)

theorem _root_.Cslib.Circuits.Circuit.takeDirectProductPrefix_computes
    (circuit : Circuit sigma (large * width) large)
    (function : ScalarFunction U width)
    (computes : circuit.ComputesWith interpretation
      (directProduct function large))
    (smallPositive : 0 < small)
    (smallLeLarge : small <= large) :
    (circuit.takeDirectProductPrefix small smallPositive smallLeLarge).ComputesWith
      interpretation (directProduct function small) := by
  intro input
  funext copy
  rw [Circuit.takeDirectProductPrefix, Circuit.eval_mapOutputs,
    Circuit.eval_mapInputs, computes]
  exact congrArg function
    (directProductInput_prefixBatchInputMap smallPositive smallLeLarge
      input copy)

export Cslib.Circuits.Circuit (takeDirectProductPrefix_computes)

/-- Minimum direct-product complexity is monotone in the number of positive
copies.  This is the formal version of fixing unused inputs and discarding
unused outputs. -/
theorem _root_.Cslib.Circuits.Circuit.costComplexity_directProduct_mono_copies
    (interpretation : Interpretation sigma U)
    (operationCost : OperationCost sigma)
    (function : ScalarFunction U width)
    (smallPositive : 0 < small)
    (smallLeLarge : small <= large) :
    Circuit.costComplexity interpretation operationCost
        (directProduct function small) <=
      Circuit.costComplexity interpretation operationCost
        (directProduct function large) := by
  change Circuit.costComplexity interpretation operationCost
      (directProduct function small) <=
    (iInf fun circuit :
      Circuit sigma (large * width) large =>
        iInf fun _ : circuit.ComputesWith interpretation
          (directProduct function large) =>
            (circuit.cost operationCost : ENat))
  refine le_iInf fun circuit =>
    le_iInf fun computes => ?_
  have retainedComputes := circuit.takeDirectProductPrefix_computes function
    computes smallPositive smallLeLarge
  have upper :=
    (circuit.takeDirectProductPrefix small smallPositive smallLeLarge)
      |>.costComplexity_le operationCost retainedComputes
  simpa using upper

export Cslib.Circuits.Circuit (costComplexity_directProduct_mono_copies)

/-- The naive direct-product upper bound for minimum weighted complexity. It
is valid even when the one-copy function is not representable, in which case
the right side may be `⊤`. -/
theorem _root_.Cslib.Circuits.Circuit.costComplexity_directProduct_le
    (interpretation : Interpretation σ U)
    (operationCost : OperationCost σ)
    (function : ScalarFunction U n)
    (copies : Nat) :
    Circuit.costComplexity interpretation operationCost
        (directProduct function copies) ≤
      (copies : ℕ∞) * Circuit.costComplexity interpretation operationCost
        (scalarTarget function) := by
  cases copies with
  | zero =>
      let empty : Circuit σ (0 * n) 0 :=
        { program := .empty
          outputs := Fin.elim0 }
      have computes : empty.ComputesWith interpretation
          (directProduct function 0) := by
        intro input
        funext output
        exact Fin.elim0 output
      have upper := empty.costComplexity_le operationCost computes
      have zeroCost : empty.cost operationCost = 0 := rfl
      rw [zeroCost] at upper
      simpa only [Nat.cast_zero, zero_mul] using upper
  | succ copies =>
      let count := copies.succ
      have pointwise : ∀ (circuit : Circuit σ n 1),
          circuit.ComputesWith interpretation (scalarTarget function) ->
            Circuit.costComplexity interpretation operationCost
                (directProduct function count) ≤
              (count : ℕ∞) * circuit.cost operationCost := by
        intro circuit computes
        have outputFunction :
            circuit.outputFunction interpretation 0 = function :=
          circuit.outputFunction_eq_of_computes_scalarTarget computes
        have replicatedComputes :=
          circuit.replicateScalar_computes_directProduct
            outputFunction count
        have upper := (circuit.replicateScalar count).costComplexity_le
          operationCost replicatedComputes
        simpa [count] using upper
      change Circuit.costComplexity interpretation operationCost
          (directProduct function count) ≤
        (count : ℕ∞) *
          (⨅ circuit : Circuit σ n 1,
            ⨅ _ : circuit.ComputesWith interpretation (scalarTarget function),
              (circuit.cost operationCost : ℕ∞))
      have nonzero : (count : ℕ∞) ≠ 0 := by
        exact_mod_cast Nat.succ_ne_zero copies
      rw [ENat.mul_iInf_of_ne nonzero]
      refine le_iInf fun circuit => ?_
      rw [ENat.mul_iInf_of_ne nonzero]
      refine le_iInf fun computes => ?_
      simpa using pointwise circuit computes

export Cslib.Circuits.Circuit (costComplexity_directProduct_le)

/-- The naive direct-product upper bound for minimum gate count. -/
theorem _root_.Cslib.Circuits.Circuit.gateComplexity_directProduct_le
    (interpretation : Interpretation σ U)
    (function : ScalarFunction U n)
    (copies : Nat) :
    Circuit.gateComplexity interpretation (directProduct function copies) ≤
      (copies : ℕ∞) *
        Circuit.gateComplexity interpretation (scalarTarget function) := by
  exact Circuit.costComplexity_directProduct_le interpretation
    OperationCost.unit function copies

export Cslib.Circuits.Circuit (gateComplexity_directProduct_le)

end Circuit
end Algebraic
