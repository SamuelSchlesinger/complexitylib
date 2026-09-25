/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Counting.Basic
public import Complexitylib.Algebraic.LowerBound.Counting.Arity
public import Complexitylib.Algebraic.Fin
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Finset.Union
public import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Depth-sensitive counting

Instead of enumerating circuit syntax, this file closes the set of scalar
functions under one operation layer. Every depth-`d` circuit output belongs to
that closure, yielding interpretation-sensitive depth lower bounds.
-/

@[expose] public section

namespace Algebraic

/-! ## Semantic closure by depth -/

/-- Coordinate projections, which are the scalar functions available at depth zero. -/
noncomputable def Depth.projections [Fintype U] (n : Nat) :
    Finset (ScalarFunction U n) := by
  classical
  exact Finset.univ.image fun input : Fin n => fun values => values input

/-- Pointwise application of one interpreted operation to scalar functions. -/
def Depth.applyOperation
    (interpretation : Interpretation σ U)
    (op : σ.Op)
    (arguments : Fin (σ.Arity op) → ScalarFunction U n) :
    ScalarFunction U n :=
  fun input => interpretation op (fun k => arguments k input)

/-- Scalar functions obtained by applying one primitive operation to functions
from `prior`. -/
noncomputable def Depth.operationClosure
    [Fintype σ.Op] [Fintype U]
    (interpretation : Interpretation σ U)
    (prior : Finset (ScalarFunction U n)) : Finset (ScalarFunction U n) := by
  classical
  exact Finset.univ.biUnion fun op =>
    (Fintype.piFinset fun _ : Fin (σ.Arity op) => prior).image
      (Depth.applyOperation interpretation op)

/-- Scalar functions available by depth `d`, with projections retained at
every layer. -/
noncomputable def Depth.functions
    [Fintype σ.Op] [Fintype U]
    (interpretation : Interpretation σ U)
    (n : Nat) : Nat → Finset (ScalarFunction U n)
  | 0 => Depth.projections n
  | depth + 1 => by
      classical
      exact Depth.projections n ∪
        Depth.operationClosure interpretation
          (Depth.functions interpretation n depth)

@[simp] theorem Depth.card_projections_le [Fintype U] :
    (Depth.projections (U := U) n).card ≤ n := by
  classical
  simpa [Depth.projections] using
    (Finset.card_image_le (s := (Finset.univ : Finset (Fin n)))
      (f := fun input : Fin n => fun values : Fin n → U => values input))

theorem Depth.card_operationClosure_le
    [Fintype σ.Op] [Fintype U]
    (interpretation : Interpretation σ U)
    (prior : Finset (ScalarFunction U n)) :
    (Depth.operationClosure interpretation prior).card ≤
      σ.lineCount prior.card := by
  classical
  calc
    (Depth.operationClosure interpretation prior).card ≤
        ∑ op : σ.Op,
          ((Fintype.piFinset fun _ : Fin (σ.Arity op) => prior).image
            (Depth.applyOperation interpretation op)).card := by
      simpa [Depth.operationClosure] using Finset.card_biUnion_le
    _ ≤ ∑ op : σ.Op,
          (Fintype.piFinset fun _ : Fin (σ.Arity op) => prior).card :=
      Finset.sum_le_sum fun _ _ => Finset.card_image_le
    _ = σ.lineCount prior.card := by
      simp [Signature.lineCount, Fintype.card_piFinset]

theorem Depth.card_functions_succ_le
    [Fintype σ.Op] [Fintype U]
    (interpretation : Interpretation σ U)
    (n depth : Nat) :
    (Depth.functions interpretation n (depth + 1)).card ≤
      n + σ.lineCount (Depth.functions interpretation n depth).card := by
  classical
  rw [Depth.functions]
  exact (Finset.card_union_le _ _).trans <|
    Nat.add_le_add Depth.card_projections_le
      (Depth.card_operationClosure_le interpretation _)

theorem Depth.applyOperation_mem_operationClosure
    [Fintype σ.Op] [Fintype U]
    (interpretation : Interpretation σ U)
    (prior : Finset (ScalarFunction U n))
    (op : σ.Op)
    (arguments : Fin (σ.Arity op) → ScalarFunction U n)
    (present : ∀ k, arguments k ∈ prior) :
    Depth.applyOperation interpretation op arguments ∈
      Depth.operationClosure interpretation prior := by
  classical
  simp only [Depth.operationClosure, Finset.mem_biUnion, Finset.mem_univ,
    true_and, Finset.mem_image]
  refine ⟨op, arguments, ?_, rfl⟩
  exact Fintype.mem_piFinset.mpr present

/-- Applying an operation to depth-`d` functions produces a depth-`d + 1`
function. -/
theorem Depth.applyOperation_mem_functions_succ
    [Fintype σ.Op] [Fintype U]
    (interpretation : Interpretation σ U)
    (depth : Nat)
    (op : σ.Op)
    (arguments : Fin (σ.Arity op) → ScalarFunction U n)
    (present : ∀ k, arguments k ∈ Depth.functions interpretation n depth) :
    Depth.applyOperation interpretation op arguments ∈
      Depth.functions interpretation n (depth + 1) := by
  classical
  rw [Depth.functions, Finset.mem_union]
  exact Or.inr <|
    Depth.applyOperation_mem_operationClosure
      interpretation (Depth.functions interpretation n depth)
      op arguments present

theorem Depth.operationClosure_mono
    [Fintype σ.Op] [Fintype U]
    (interpretation : Interpretation σ U) :
    Monotone (Depth.operationClosure (n := n) interpretation) := by
  intro left right subset function present
  classical
  simp only [Depth.operationClosure, Finset.mem_biUnion, Finset.mem_univ,
    true_and, Finset.mem_image] at present ⊢
  obtain ⟨op, arguments, argumentsPresent, rfl⟩ := present
  exact ⟨op, arguments,
    Fintype.mem_piFinset.mpr fun k =>
      subset (Fintype.mem_piFinset.mp argumentsPresent k), rfl⟩

theorem Depth.projection_mem_functions
    [Fintype σ.Op] [Fintype U]
    (interpretation : Interpretation σ U)
    (input : Fin n)
    (depth : Nat) :
    (fun values : Fin n → U => values input) ∈
      Depth.functions interpretation n depth := by
  classical
  cases depth with
  | zero => simp [Depth.functions, Depth.projections]
  | succ depth =>
      simp only [Depth.functions, Finset.mem_union]
      exact Or.inl (by simp [Depth.projections])

theorem Depth.functions_subset_succ
    [Fintype σ.Op] [Fintype U]
    (interpretation : Interpretation σ U)
    (n depth : Nat) :
    Depth.functions interpretation n depth ⊆
      Depth.functions interpretation n (depth + 1) := by
  classical
  induction depth with
  | zero =>
      intro function present
      rw [Depth.functions, Finset.mem_union]
      exact Or.inl present
  | succ depth ih =>
      intro function present
      rw [Depth.functions] at present
      rw [show depth + 1 + 1 = (depth + 1) + 1 by omega, Depth.functions,
        Finset.mem_union]
      rcases Finset.mem_union.mp present with projection | operation
      · exact Or.inl projection
      · exact Or.inr (Depth.operationClosure_mono interpretation ih operation)

theorem Depth.functions_mono
    [Fintype σ.Op] [Fintype U]
    (interpretation : Interpretation σ U)
    (n : Nat) :
    Monotone (Depth.functions interpretation n) :=
  monotone_nat_of_le_succ (Depth.functions_subset_succ interpretation n)

/-! ## Soundness for programs and circuits -/

theorem _root_.Cslib.Circuits.Program.gateFunction_mem_depthFunctions
    [Fintype σ.Op] [Fintype U]
    (program : Program σ n g)
    (interpretation : Interpretation σ U)
    (gate : Fin g) :
    program.gateFunction interpretation gate ∈
      Depth.functions interpretation n (program.depths gate) := by
  classical
  induction program with
  | empty => exact Fin.elim0 gate
  | @gate g program line ih =>
      refine Fin.lastCases ?_ (fun priorGate => ?_) gate
      · unfold Program.gateFunction
        simp only [Program.eval, Program.depths, Fin.lastCases_last]
        let wireDepths : Wire n g → Nat :=
          Fin.addCases (fun _ => 0) program.depths
        let maxDepth := Fin.foldl (σ.Arity line.op)
          (fun result argument =>
            max result (wireDepths (line.wires argument))) 0
        let arguments : Fin (σ.Arity line.op) → ScalarFunction U n :=
          fun argument => program.wireFunction interpretation (line.wires argument)
        have wirePresent (wire : Wire n g) :
            program.wireFunction interpretation wire ∈
              Depth.functions interpretation n (wireDepths wire) := by
          unfold Program.wireFunction Program.trace
          refine Fin.addCases ?_ ?_ wire
          · intro input
            simp only [Fin.addCases_left, wireDepths]
            change (fun values : Fin n → U => values input) ∈
              Depth.functions interpretation n 0
            exact Depth.projection_mem_functions interpretation input 0
          · intro priorGate
            simp only [Fin.addCases_right, wireDepths]
            change program.gateFunction interpretation priorGate ∈
              Depth.functions interpretation n (program.depths priorGate)
            exact ih priorGate
        have argumentPresent (argument : Fin (σ.Arity line.op)) :
            arguments argument ∈ Depth.functions interpretation n maxDepth := by
          apply Depth.functions_mono interpretation n
            (Fin.le_foldl_max
              (fun argument => wireDepths (line.wires argument)) 0 argument)
          exact wirePresent (line.wires argument)
        have operationPresent := Depth.applyOperation_mem_functions_succ
          interpretation maxDepth line.op arguments argumentPresent
        rw [show line.depth wireDepths = maxDepth + 1 by rfl]
        unfold Depth.applyOperation at operationPresent
        simp only [arguments] at operationPresent
        unfold Program.wireFunction Program.trace at operationPresent
        simpa [arguments, Line.eval, Function.comp_def] using operationPresent
      · unfold Program.gateFunction
        simp only [Program.eval, Program.depths, Fin.lastCases_castSucc]
        exact ih priorGate

export Cslib.Circuits (Program.gateFunction_mem_depthFunctions)

theorem _root_.Cslib.Circuits.Program.wireFunction_mem_depthFunctions
    [Fintype σ.Op] [Fintype U]
    (program : Program σ n g)
    (interpretation : Interpretation σ U)
    (wire : Wire n g) :
    program.wireFunction interpretation wire ∈
      Depth.functions interpretation n (program.wireDepths wire) := by
  classical
  unfold Program.wireFunction Program.wireDepths Program.trace
  refine Fin.addCases ?_ ?_ wire
  · intro input
    simp only [Fin.addCases_left]
    change (fun values : Fin n → U => values input) ∈
      Depth.functions interpretation n 0
    exact Depth.projection_mem_functions interpretation input 0
  · intro gate
    simp only [Fin.addCases_right]
    change program.gateFunction interpretation gate ∈
      Depth.functions interpretation n (program.depths gate)
    exact program.gateFunction_mem_depthFunctions interpretation gate

export Cslib.Circuits (Program.wireFunction_mem_depthFunctions)

theorem _root_.Cslib.Circuits.Circuit.outputFunction_mem_depthFunctions
    [Fintype σ.Op] [Fintype U]
    (circuit : Circuit σ n g m)
    (interpretation : Interpretation σ U)
    (output : Fin m) :
    circuit.outputFunction interpretation output ∈
      Depth.functions interpretation n (circuit.outputDepths output) := by
  classical
  change circuit.program.wireFunction interpretation (circuit.outputs output) ∈
    Depth.functions interpretation n
      (circuit.program.wireDepths (circuit.outputs output))
  exact circuit.program.wireFunction_mem_depthFunctions interpretation
    (circuit.outputs output)

export Cslib.Circuits (Circuit.outputFunction_mem_depthFunctions)

/-- Multi-output targets assembled from scalar functions available by `depth`. -/
noncomputable def Depth.targets
    [Fintype σ.Op] [Fintype U]
    (interpretation : Interpretation σ U)
    (n m depth : Nat) : Finset (Target U n m) := by
  classical
  exact
    (Fintype.piFinset fun _ : Fin m =>
      Depth.functions interpretation n depth).image
        fun outputs input output => outputs output input

theorem Depth.card_targets_le
    [Fintype σ.Op] [Fintype U]
    (interpretation : Interpretation σ U)
    (n m depth : Nat) :
    (Depth.targets interpretation n m depth).card ≤
      (Depth.functions interpretation n depth).card ^ m := by
  classical
  exact Finset.card_image_le.trans_eq (by simp [Fintype.card_piFinset])

theorem _root_.Cslib.Circuits.Circuit.eval_mem_depth_targets
    [Fintype σ.Op] [Fintype U]
    (circuit : Circuit σ n g m)
    (interpretation : Interpretation σ U)
    {depth : Nat}
    (bounded : circuit.depth ≤ depth) :
    circuit.eval interpretation ∈ Depth.targets interpretation n m depth := by
  classical
  rw [Depth.targets, Finset.mem_image]
  let outputs : Fin m → ScalarFunction U n :=
    fun output => circuit.outputFunction interpretation output
  have outputsPresent : outputs ∈
      Fintype.piFinset fun _ : Fin m =>
        Depth.functions interpretation n depth := by
    apply Fintype.mem_piFinset.mpr
    intro output
    apply Depth.functions_mono interpretation n
      ((Fin.le_foldl_max circuit.outputDepths 0 output).trans bounded)
    exact circuit.outputFunction_mem_depthFunctions interpretation output
  refine ⟨outputs, outputsPresent, ?_⟩
  funext input output
  rfl

/-! ## Exact and numeric lower-bound criteria -/

export Cslib.Circuits (Circuit.eval_mem_depth_targets)

/-- Interpretation-independent numeric recurrence bounding the number of scalar
functions at each depth. -/
def Depth.countBound (σ : Signature) [Fintype σ.Op] (n : Nat) : Nat → Nat
  | 0 => n
  | depth + 1 => n + σ.lineCount (Depth.countBound σ n depth)

theorem Depth.card_functions_le_countBound
    [Fintype σ.Op] [Fintype U]
    (interpretation : Interpretation σ U)
    (n depth : Nat) :
    (Depth.functions interpretation n depth).card ≤
      Depth.countBound σ n depth := by
  induction depth with
  | zero => exact Depth.card_projections_le
  | succ depth ih =>
      exact (Depth.card_functions_succ_le interpretation n depth).trans <|
        Nat.add_le_add_left (Signature.lineCount_mono σ ih) n

theorem Depth.card_targets_le_countBound
    [Fintype σ.Op] [Fintype U]
    (interpretation : Interpretation σ U)
    (n m depth : Nat) :
    (Depth.targets interpretation n m depth).card ≤
      Depth.countBound σ n depth ^ m :=
  (Depth.card_targets_le interpretation n m depth).trans <|
    Nat.pow_le_pow_left
      (Depth.card_functions_le_countBound interpretation n depth) m

/-- A family exceeding the semantic closure count contains a depth-hard target. -/
theorem _root_.Cslib.Circuits.Circuit.exists_depth_hard_in_family
    [Fintype σ.Op] [Fintype U]
    (interpretation : Interpretation σ U)
    (family : Finset (Target U n m))
    {depth : Nat}
    (large :
      (Depth.functions interpretation n depth).card ^ m < family.card) :
    ∃ target ∈ family,
      Circuit.DepthHard interpretation depth target := by
  classical
  have targetCount := Depth.card_targets_le interpretation n m depth
  have small : (Depth.targets interpretation n m depth).card < family.card :=
    targetCount.trans_lt large
  obtain ⟨target, inFamily, notShallow⟩ :=
    Finset.exists_mem_notMem_of_card_lt_card small
  refine ⟨target, inFamily, ?_⟩
  unfold Circuit.DepthHard
  intro g circuit computes
  by_contra notDeep
  have bounded : circuit.depth ≤ depth := by omega
  apply notShallow
  have evaluated := circuit.eval_mem_depth_targets interpretation bounded
  rw [← computes.eval_eq]
  exact evaluated

export Cslib.Circuits (Circuit.exists_depth_hard_in_family)

/-- Purely numeric depth criterion, derived from `Depth.countBound`. -/
theorem _root_.Cslib.Circuits.Circuit.exists_depth_hard_in_family_of_countBound
    [Fintype σ.Op] [Fintype U]
    (interpretation : Interpretation σ U)
    (family : Finset (Target U n m))
    {depth : Nat}
    (large : Depth.countBound σ n depth ^ m < family.card) :
    ∃ target ∈ family,
      Circuit.DepthHard interpretation depth target :=
  Circuit.exists_depth_hard_in_family interpretation family <|
    (Nat.pow_le_pow_left
      (Depth.card_functions_le_countBound interpretation n depth) m).trans_lt large

export Cslib.Circuits (Circuit.exists_depth_hard_in_family_of_countBound)

/-- Full-universe depth lower bound from the exact semantic closure count. -/
theorem _root_.Cslib.Circuits.Circuit.exists_depth_hard
    [Fintype σ.Op] [Fintype U]
    (interpretation : Interpretation σ U)
    {depth : Nat}
    (large :
      (Depth.functions interpretation n depth).card ^ m <
        Target.count U n m) :
    ∃ target : Target U n m,
      Circuit.DepthHard interpretation depth target := by
  classical
  have targetCard : Fintype.card (Target U n m) =
      Target.count U n m := by
    rw [Target.count, Nat.card_eq_fintype_card]
  obtain ⟨target, _, hard⟩ := Circuit.exists_depth_hard_in_family
    interpretation (Finset.univ : Finset (Target U n m))
    (by simpa only [Finset.card_univ, targetCard] using large)
  exact ⟨target, hard⟩

export Cslib.Circuits (Circuit.exists_depth_hard)

/-- Full-universe depth lower bound from the numeric recurrence. -/
theorem _root_.Cslib.Circuits.Circuit.exists_depth_hard_of_countBound
    [Fintype σ.Op] [Fintype U]
    (interpretation : Interpretation σ U)
    {depth : Nat}
    (large :
      Depth.countBound σ n depth ^ m <
        Target.count U n m) :
    ∃ target : Target U n m,
      Circuit.DepthHard interpretation depth target := by
  apply Circuit.exists_depth_hard interpretation
  exact (Nat.pow_le_pow_left
    (Depth.card_functions_le_countBound interpretation n depth) m).trans_lt large

/-! ## Arity-only recurrence -/

export Cslib.Circuits (Circuit.exists_depth_hard_of_countBound)

/-- Arity-only recurrence bounding the interpretation-independent depth
closure. -/
def Depth.coarseCount
    (σ : Signature) [Fintype σ.Op]
    (r n : Nat) : Nat → Nat
  | 0 => n
  | depth + 1 =>
      n + Fintype.card σ.Op * (Depth.coarseCount σ r n depth + 1) ^ r

theorem Depth.countBound_le_coarseCount
    (σ : Signature) [Fintype σ.Op]
    {r : Nat}
    (arity : σ.ArityAtMost r)
    (n depth : Nat) :
    Depth.countBound σ n depth ≤ Depth.coarseCount σ r n depth := by
  induction depth with
  | zero => exact Nat.le_refl n
  | succ depth ih =>
      rw [Depth.countBound, Depth.coarseCount]
      exact Nat.add_le_add_left
        ((Signature.lineCount_mono σ ih).trans
          (σ.lineCount_le_card_mul_pow arity
            (Depth.coarseCount σ r n depth))) n

theorem _root_.Cslib.Circuits.Circuit.exists_depth_hard_in_family_coarse
    [Fintype σ.Op] [Fintype U]
    (interpretation : Interpretation σ U)
    (family : Finset (Target U n m))
    {r depth : Nat}
    (arity : σ.ArityAtMost r)
    (large : Depth.coarseCount σ r n depth ^ m < family.card) :
    ∃ target ∈ family,
      Circuit.DepthHard interpretation depth target :=
  Circuit.exists_depth_hard_in_family_of_countBound interpretation family <|
    (Nat.pow_le_pow_left
      (Depth.countBound_le_coarseCount σ arity n depth) m).trans_lt large

export Cslib.Circuits (Circuit.exists_depth_hard_in_family_coarse)

/-- Boolean specialization of the arity-only depth recurrence. -/
theorem _root_.Cslib.Circuits.Circuit.exists_boolean_depth_hard_coarse
    [Fintype σ.Op]
    (interpretation : Interpretation σ Bool)
    {r depth : Nat}
    (arity : σ.ArityAtMost r)
    (large :
      Depth.coarseCount σ r n depth ^ m < Target.count Bool n m) :
    ∃ target : Target Bool n m,
      Circuit.DepthHard interpretation depth target := by
  apply Circuit.exists_depth_hard_of_countBound interpretation
  exact (Nat.pow_le_pow_left
    (Depth.countBound_le_coarseCount σ arity n depth) m).trans_lt large

export Cslib.Circuits (Circuit.exists_boolean_depth_hard_coarse)

end Algebraic
