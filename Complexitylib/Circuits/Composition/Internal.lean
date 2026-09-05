/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Circuits.Composition.Defs

/-!
# Circuit composition -- proof internals
-/


public section

namespace Complexity

namespace Gate

theorem eval_rewire_internal {B : Basis} {W W' : ℕ}
    (gate : Gate B W) (mapWire : Fin W → Fin W')
    (wireValue : BitString W') :
    (gate.rewire mapWire).eval wireValue =
      gate.eval fun wire => wireValue (mapWire wire) :=
  rfl

end Gate

namespace Circuit

variable {B : Basis} {N K M G₁ G₂ : ℕ}
  [NeZero N] [NeZero K] [NeZero M]

private theorem composeGate_inner
    (outer : Circuit B K M G₂) (inner : Circuit B N K G₁)
    (index : Fin (G₁ + K + G₂)) (hinner : index.val < G₁) :
    (composeGate outer inner index).val =
      (inner.gates ⟨index.val, hinner⟩).rewire embedInnerWire := by
  simp [composeGate, hinner]

private theorem composeGate_innerOutput
    (outer : Circuit B K M G₂) (inner : Circuit B N K G₁)
    (index : Fin (G₁ + K + G₂))
    (hinner : ¬ index.val < G₁) (houtput : index.val < G₁ + K) :
    (composeGate outer inner index).val =
      (inner.outputs ⟨index.val - G₁, by omega⟩).rewire
        embedInnerWire := by
  simp [composeGate, hinner, houtput]

private theorem composeGate_outer
    (outer : Circuit B K M G₂) (inner : Circuit B N K G₁)
    (index : Fin (G₁ + K + G₂))
    (hinner : ¬ index.val < G₁) (houtput : ¬ index.val < G₁ + K) :
    (composeGate outer inner index).val =
      (outer.gates ⟨index.val - G₁ - K, by omega⟩).rewire
        embedOuterWire := by
  simp [composeGate, hinner, houtput]

theorem wireValue_compose_inner_internal
    (outer : Circuit B K M G₂) (inner : Circuit B N K G₁)
    (input : BitString N) (wire : Fin (N + G₁)) :
    (outer.compose inner).wireValue input (embedInnerWire wire) =
      inner.wireValue input wire := by
  induction hwire : wire.val using Nat.strong_induction_on
      generalizing wire with
  | h wireIndex ih =>
      by_cases hinput : wire.val < N
      · rw [Circuit.wireValue_of_lt (outer.compose inner) input
            (embedInnerWire wire) (by
              simpa only [embedInnerWire] using hinput),
          Circuit.wireValue_of_lt inner input wire hinput]
        rfl
      · rw [Circuit.wireValue_of_not_lt (outer.compose inner) input
            (embedInnerWire wire) (by
              simpa only [embedInnerWire] using hinput),
          Circuit.wireValue_of_not_lt inner input wire hinput]
        change
          (composeGate outer inner ⟨wire.val - N, by omega⟩).val.eval
              ((outer.compose inner).wireValue input) =
            (inner.gates ⟨wire.val - N, by omega⟩).eval
              (inner.wireValue input)
        have hgate : wire.val - N < G₁ := by
          have := wire.isLt
          omega
        rw [composeGate_inner outer inner _ hgate,
          Gate.eval_rewire_internal]
        unfold Gate.eval
        congr 1
        funext gateInput
        apply congrArg (fun value =>
          ((inner.gates ⟨wire.val - N, hgate⟩).negated gateInput).xor
            value)
        let source :=
          (inner.gates ⟨wire.val - N, hgate⟩).inputs gateInput
        apply ih source.val
        · have hacyclic :=
            inner.acyclic ⟨wire.val - N, hgate⟩ gateInput
          change source.val < N + (wire.val - N) at hacyclic
          omega
        · rfl

theorem wireValue_compose_innerOutput_internal
    (outer : Circuit B K M G₂) (inner : Circuit B N K G₁)
    (input : BitString N) (output : Fin K) :
    (outer.compose inner).wireValue input
        (embedInnerOutput output) =
      inner.eval input output := by
  rw [Circuit.wireValue_of_not_lt (outer.compose inner) input
    (embedInnerOutput output) (by
      change ¬ N + G₁ + output.val < N
      omega)]
  generalize hgateIndex :
    (⟨(embedInnerOutput output).val - N, by
        change N + G₁ + output.val - N < G₁ + K + G₂
        omega⟩ :
      Fin (G₁ + K + G₂)) = gateIndex
  have hgateIndexValue : gateIndex.val = G₁ + output.val := by
    rw [← hgateIndex]
    simp only [embedInnerOutput]
    omega
  have hgateIndexEq :
      gateIndex = (⟨G₁ + output.val, by omega⟩ :
        Fin (G₁ + K + G₂)) :=
    Fin.ext hgateIndexValue
  rw [hgateIndexEq]
  change
    (composeGate outer inner ⟨G₁ + output.val, by omega⟩).val.eval
        ((outer.compose inner).wireValue input) =
      inner.eval input output
  rw [composeGate_innerOutput outer inner _ (by omega) (by omega),
    Gate.eval_rewire_internal]
  unfold Circuit.eval
  congr 1
  · apply congrArg inner.outputs
    apply Fin.ext
    dsimp only
    omega
  · funext wire
    exact wireValue_compose_inner_internal outer inner input wire

theorem wireValue_compose_outer_internal
    (outer : Circuit B K M G₂) (inner : Circuit B N K G₁)
    (input : BitString N) (wire : Fin (K + G₂)) :
    (outer.compose inner).wireValue input (embedOuterWire wire) =
      outer.wireValue (inner.eval input) wire := by
  induction hwire : wire.val using Nat.strong_induction_on
      generalizing wire with
  | h wireIndex ih =>
      by_cases hinput : wire.val < K
      · rw [Circuit.wireValue_of_lt outer (inner.eval input) wire hinput]
        have hembed :
            embedOuterWire (N := N) (G₁ := G₁) wire =
              embedInnerOutput (N := N) (G₁ := G₁)
                (⟨wire.val, hinput⟩ : Fin K) := by
          apply Fin.ext
          simp [embedOuterWire, embedInnerOutput, hinput]
        rw [hembed]
        exact wireValue_compose_innerOutput_internal outer inner input _
      · rw [Circuit.wireValue_of_not_lt outer (inner.eval input) wire
          hinput]
        have hembedNotInput :
            ¬(embedOuterWire (N := N) (G₁ := G₁) wire).val < N := by
          simp only [embedOuterWire, hinput, dite_false]
          omega
        rw [Circuit.wireValue_of_not_lt (outer.compose inner) input
          (embedOuterWire wire) hembedNotInput]
        generalize hgateIndex :
          (⟨(embedOuterWire (N := N) (G₁ := G₁) wire).val - N,
              by omega⟩ : Fin (G₁ + K + G₂)) = gateIndex
        have hgateIndexValue :
            gateIndex.val = G₁ + K + (wire.val - K) := by
          rw [← hgateIndex]
          simp only [embedOuterWire, hinput, dite_false]
          omega
        have hgateIndexEq :
            gateIndex =
              (⟨G₁ + K + (wire.val - K), by omega⟩ :
                Fin (G₁ + K + G₂)) :=
          Fin.ext hgateIndexValue
        rw [hgateIndexEq]
        change
          (composeGate outer inner
              ⟨G₁ + K + (wire.val - K), by omega⟩).val.eval
                ((outer.compose inner).wireValue input) =
            (outer.gates ⟨wire.val - K, by omega⟩).eval
              (outer.wireValue (inner.eval input))
        rw [composeGate_outer outer inner _ (by omega) (by omega)]
        have houterIndex :
            (⟨(⟨G₁ + K + (wire.val - K), by omega⟩ :
                Fin (G₁ + K + G₂)).val - G₁ - K, by omega⟩ :
              Fin G₂) =
              ⟨wire.val - K, by omega⟩ := by
          apply Fin.ext
          dsimp only
          omega
        rw [houterIndex, Gate.eval_rewire_internal]
        unfold Gate.eval
        congr 1
        funext gateInput
        apply congrArg (fun value =>
          ((outer.gates ⟨wire.val - K, by omega⟩).negated
            gateInput).xor value)
        let source :=
          (outer.gates ⟨wire.val - K, by omega⟩).inputs gateInput
        apply ih source.val
        · have hacyclic :=
            outer.acyclic ⟨wire.val - K, by omega⟩ gateInput
          change source.val < K + (wire.val - K) at hacyclic
          omega
        · rfl

theorem eval_compose_internal
    (outer : Circuit B K M G₂) (inner : Circuit B N K G₁)
    (input : BitString N) :
    (outer.compose inner).eval input =
      outer.eval (inner.eval input) := by
  funext output
  unfold Circuit.eval
  change
    ((outer.outputs output).rewire
      (embedOuterWire (N := N) (G₁ := G₁))).eval
        ((outer.compose inner).wireValue input) =
      (outer.outputs output).eval
        (outer.wireValue fun innerOutput =>
          (inner.outputs innerOutput).eval (inner.wireValue input))
  rw [Gate.eval_rewire_internal]
  unfold Gate.eval
  congr 1
  funext gateInput
  apply congrArg (fun value =>
    ((outer.outputs output).negated gateInput).xor value)
  exact wireValue_compose_outer_internal outer inner input _

/-! ## Parallel composition -/

private theorem parallelGate_left
    (left : Circuit B N K G₁) (right : Circuit B N M G₂)
    (index : Fin (G₁ + G₂)) (hleft : index.val < G₁) :
    (parallelGate left right index).val =
      (left.gates ⟨index.val, hleft⟩).rewire
        embedParallelLeftWire := by
  simp [parallelGate, hleft]

private theorem parallelGate_right
    (left : Circuit B N K G₁) (right : Circuit B N M G₂)
    (index : Fin (G₁ + G₂)) (hleft : ¬ index.val < G₁) :
    (parallelGate left right index).val =
      (right.gates ⟨index.val - G₁, by omega⟩).rewire
        embedParallelRightWire := by
  simp [parallelGate, hleft]

theorem wireValue_parallel_left_internal
    (left : Circuit B N K G₁) (right : Circuit B N M G₂)
    (input : BitString N) (wire : Fin (N + G₁)) :
    (left.parallel right).wireValue input (embedParallelLeftWire wire) =
      left.wireValue input wire := by
  induction hwire : wire.val using Nat.strong_induction_on
      generalizing wire with
  | h wireIndex ih =>
      by_cases hinput : wire.val < N
      · rw [Circuit.wireValue_of_lt (left.parallel right) input
            (embedParallelLeftWire wire) (by
              simpa only [embedParallelLeftWire] using hinput),
          Circuit.wireValue_of_lt left input wire hinput]
        rfl
      · rw [Circuit.wireValue_of_not_lt (left.parallel right) input
            (embedParallelLeftWire wire) (by
              simpa only [embedParallelLeftWire] using hinput),
          Circuit.wireValue_of_not_lt left input wire hinput]
        change
          (parallelGate left right ⟨wire.val - N, by omega⟩).val.eval
              ((left.parallel right).wireValue input) =
            (left.gates ⟨wire.val - N, by omega⟩).eval
              (left.wireValue input)
        have hgate : wire.val - N < G₁ := by
          have := wire.isLt
          omega
        rw [parallelGate_left left right _ hgate,
          Gate.eval_rewire_internal]
        unfold Gate.eval
        congr 1
        funext gateInput
        apply congrArg (fun value =>
          ((left.gates ⟨wire.val - N, hgate⟩).negated gateInput).xor
            value)
        let source :=
          (left.gates ⟨wire.val - N, hgate⟩).inputs gateInput
        apply ih source.val
        · have hacyclic :=
            left.acyclic ⟨wire.val - N, hgate⟩ gateInput
          change source.val < N + (wire.val - N) at hacyclic
          omega
        · rfl

theorem wireValue_parallel_right_internal
    (left : Circuit B N K G₁) (right : Circuit B N M G₂)
    (input : BitString N) (wire : Fin (N + G₂)) :
    (left.parallel right).wireValue input (embedParallelRightWire wire) =
      right.wireValue input wire := by
  induction hwire : wire.val using Nat.strong_induction_on
      generalizing wire with
  | h wireIndex ih =>
      by_cases hinput : wire.val < N
      · rw [Circuit.wireValue_of_lt (left.parallel right) input
            (embedParallelRightWire wire)
              (by simp [embedParallelRightWire, hinput]),
          Circuit.wireValue_of_lt right input wire hinput]
        simp [embedParallelRightWire, hinput]
      · have hembedVal :
            (embedParallelRightWire (G₁ := G₁) wire).val =
              N + G₁ + (wire.val - N) := by
          simp [embedParallelRightWire, hinput]
        rw [Circuit.wireValue_of_not_lt (left.parallel right) input
            (embedParallelRightWire wire) (by
              rw [hembedVal]
              omega),
          Circuit.wireValue_of_not_lt right input wire hinput]
        change
          (parallelGate left right
              ⟨(embedParallelRightWire (G₁ := G₁) wire).val - N,
                by omega⟩).val.eval
                ((left.parallel right).wireValue input) =
            (right.gates ⟨wire.val - N, by omega⟩).eval
              (right.wireValue input)
        have hindex :
            (⟨(embedParallelRightWire (G₁ := G₁) wire).val - N,
                by omega⟩ : Fin (G₁ + G₂)) =
              ⟨G₁ + (wire.val - N), by omega⟩ := by
          apply Fin.ext
          change
            (embedParallelRightWire (G₁ := G₁) wire).val - N =
              G₁ + (wire.val - N)
          omega
        have hnotLeft :
            ¬ (⟨G₁ + (wire.val - N), by omega⟩ :
              Fin (G₁ + G₂)).val < G₁ := by
          dsimp only
          omega
        rw [hindex, parallelGate_right left right _ hnotLeft]
        have hrightIndex :
            (⟨(⟨G₁ + (wire.val - N), by omega⟩ :
                Fin (G₁ + G₂)).val - G₁, by omega⟩ : Fin G₂) =
              ⟨wire.val - N, by omega⟩ := by
          apply Fin.ext
          dsimp only
          omega
        rw [hrightIndex, Gate.eval_rewire_internal]
        unfold Gate.eval
        congr 1
        funext gateInput
        apply congrArg (fun value =>
          ((right.gates ⟨wire.val - N, by omega⟩).negated
            gateInput).xor value)
        let source :=
          (right.gates ⟨wire.val - N, by omega⟩).inputs gateInput
        apply ih source.val
        · have hacyclic :=
            right.acyclic ⟨wire.val - N, by omega⟩ gateInput
          change source.val < N + (wire.val - N) at hacyclic
          omega
        · rfl

theorem eval_parallel_internal
    (left : Circuit B N K G₁) (right : Circuit B N M G₂)
    (input : BitString N) :
    (left.parallel right).eval input =
      Fin.append (left.eval input) (right.eval input) := by
  funext output
  by_cases hleft : output.val < K
  · let leftOutput : Fin K := ⟨output.val, hleft⟩
    have houtput :
        (left.parallel right).outputs output =
          (left.outputs leftOutput).rewire embedParallelLeftWire := by
      simp [parallel, hleft, leftOutput]
    rw [Circuit.eval, houtput, Gate.eval_rewire_internal]
    change
      (left.outputs leftOutput).eval
          (fun wire => (left.parallel right).wireValue input
            (embedParallelLeftWire wire)) =
        Fin.append (left.eval input) (right.eval input) output
    rw [show output = Fin.castAdd M leftOutput by
      apply Fin.ext
      rfl, Fin.append_left]
    unfold Circuit.eval
    congr 1
    funext wire
    exact wireValue_parallel_left_internal left right input wire
  · let rightOutput : Fin M := ⟨output.val - K, by omega⟩
    have houtput :
        (left.parallel right).outputs output =
          (right.outputs rightOutput).rewire embedParallelRightWire := by
      simp [parallel, hleft, rightOutput]
    rw [Circuit.eval, houtput, Gate.eval_rewire_internal]
    change
      (right.outputs rightOutput).eval
          (fun wire => (left.parallel right).wireValue input
            (embedParallelRightWire wire)) =
        Fin.append (left.eval input) (right.eval input) output
    rw [show output = Fin.natAdd K rightOutput by
      apply Fin.ext
      simp only [Fin.val_natAdd]
      dsimp only [rightOutput]
      omega, Fin.append_right]
    unfold Circuit.eval
    congr 1
    funext wire
    exact wireValue_parallel_right_internal left right input wire

theorem size_parallel_internal
    (left : Circuit B N K G₁) (right : Circuit B N M G₂) :
    (left.parallel right).size = left.size + right.size := by
  simp only [Circuit.size]
  omega

private theorem exists_parallelFamily_succ_internal (count : ℕ)
    (circuits : Fin (count + 1) →
      Σ internalGates, Circuit B N 1 internalGates) :
    ∃ internalGates,
      ∃ packed : Circuit B N (count + 1) internalGates,
        packed.size = (∑ i, ((circuits i).2).size) ∧
          ∀ input i,
            packed.eval input i = ((circuits i).2.eval input) 0 := by
  induction count with
  | zero =>
      rcases hfirst : circuits 0 with ⟨internalGates, circuit⟩
      refine ⟨internalGates, circuit, ?_, ?_⟩
      · simpa using (congrArg (fun bundled => bundled.2.size) hfirst).symm
      · intro input output
        have houtput : output = 0 := by
          apply Fin.ext
          omega
        subst output
        rw [hfirst]
  | succ count ih =>
      let initialCircuits : Fin (count + 1) →
          Σ internalGates, Circuit B N 1 internalGates :=
        fun i => circuits i.castSucc
      obtain ⟨prefixGates, prefixCircuit, hprefixSize, hprefixEval⟩ :=
        ih initialCircuits
      rcases hlast : circuits (Fin.last (count + 1)) with
        ⟨lastGates, lastCircuit⟩
      refine
        ⟨prefixGates + lastGates,
          prefixCircuit.parallel lastCircuit, ?_, ?_⟩
      · rw [size_parallel_internal, hprefixSize,
          Fin.sum_univ_castSucc
            (fun i : Fin (count + 1 + 1) => ((circuits i).2).size)]
        have hlastSize :=
          congrArg (fun bundled => bundled.2.size) hlast
        simp only [initialCircuits]
        simpa only using congrArg
          (fun size =>
            (∑ i : Fin (count + 1), ((circuits i.castSucc).2).size) +
              size)
          hlastSize.symm
      · intro input output
        refine Fin.lastCases ?_ (fun prior => ?_) output
        · rw [eval_parallel_internal]
          rw [Fin.append_right_eq_snoc, Fin.snoc_last, hlast]
        · rw [eval_parallel_internal]
          rw [show prior.castSucc = Fin.castAdd 1 prior by rfl,
            Fin.append_left]
          exact hprefixEval input prior

theorem exists_parallelFamily_internal {count : ℕ} [NeZero count]
    (circuits : Fin count →
      Σ internalGates, Circuit B N 1 internalGates) :
    ∃ internalGates,
      ∃ packed : Circuit B N count internalGates,
        packed.size = (∑ i, ((circuits i).2).size) ∧
          ∀ input i,
            packed.eval input i = ((circuits i).2.eval input) 0 := by
  cases count with
  | zero => exact (NeZero.ne 0 rfl).elim
  | succ count => exact exists_parallelFamily_succ_internal count circuits

private theorem le_fold_max {n : ℕ} (f : Fin n → ℕ) (i : Fin n) :
    f i ≤ Fin.foldl n (fun acc j => max acc (f j)) 0 := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih =>
      rw [Fin.foldl_succ_last]
      refine Fin.lastCases ?_ (fun j => ?_) i
      · exact le_max_right _ _
      · exact (ih (fun k => f k.castSucc) j).trans
          (le_max_left _ _)

private theorem fold_max_le_add_fold_max
    (a : ℕ) {n : ℕ} (f g : Fin n → ℕ)
    (h : ∀ i, g i ≤ a + f i) :
    Fin.foldl n (fun acc i => max acc (g i)) 0 ≤
      a + Fin.foldl n (fun acc i => max acc (f i)) 0 := by
  induction n with
  | zero => simp [Fin.foldl_zero]
  | succ n ih =>
      rw [Fin.foldl_succ_last, Fin.foldl_succ_last]
      apply max_le
      · exact (ih (fun i => f i.castSucc) (fun i => g i.castSucc)
          (fun i => h i.castSucc)).trans
            (Nat.add_le_add_left (le_max_left _ _) a)
      · exact (h (Fin.last n)).trans
          (Nat.add_le_add_left (le_max_right _ _) a)

theorem wireDepth_compose_inner_internal
    (outer : Circuit B K M G₂) (inner : Circuit B N K G₁)
    (wire : Fin (N + G₁)) :
    (outer.compose inner).wireDepth (embedInnerWire wire) =
      inner.wireDepth wire := by
  induction hwire : wire.val using Nat.strong_induction_on
      generalizing wire with
  | h wireIndex ih =>
      by_cases hinput : wire.val < N
      · rw [Circuit.wireDepth_of_lt (outer.compose inner)
            (embedInnerWire wire) (by
              simpa only [embedInnerWire] using hinput),
          Circuit.wireDepth_of_lt inner wire hinput]
      · rw [Circuit.wireDepth_of_not_lt (outer.compose inner)
            (embedInnerWire wire) (by
              simpa only [embedInnerWire] using hinput),
          Circuit.wireDepth_of_not_lt inner wire hinput]
        have hgate : wire.val - N < G₁ := by
          have := wire.isLt
          omega
        have hcompositeGate : wire.val - N < G₁ + K + G₂ := by
          omega
        change
          1 + Fin.foldl
              (composeGate outer inner
                ⟨wire.val - N, hcompositeGate⟩).val.fanIn
              (fun acc gateInput => max acc
                ((outer.compose inner).wireDepth
                  ((composeGate outer inner
                    ⟨wire.val - N, hcompositeGate⟩).val.inputs
                      gateInput))) 0 =
            1 + Fin.foldl
              (inner.gates ⟨wire.val - N, hgate⟩).fanIn
              (fun acc gateInput => max acc
                (inner.wireDepth
                  ((inner.gates
                    ⟨wire.val - N, hgate⟩).inputs gateInput))) 0
        rw [composeGate_inner outer inner _ hgate]
        congr 1
        congr 1
        funext acc gateInput
        congr 1
        let source :=
          (inner.gates ⟨wire.val - N, hgate⟩).inputs gateInput
        exact ih source.val (by
          have hacyclic :=
            inner.acyclic ⟨wire.val - N, hgate⟩ gateInput
          change source.val < N + (wire.val - N) at hacyclic
          omega) source rfl

theorem wireDepth_compose_innerOutput_internal
    (outer : Circuit B K M G₂) (inner : Circuit B N K G₁)
    (output : Fin K) :
    (outer.compose inner).wireDepth (embedInnerOutput output) =
      inner.outputDepth output := by
  rw [Circuit.wireDepth_of_not_lt (outer.compose inner)
    (embedInnerOutput output) (by
      change ¬ N + G₁ + output.val < N
      omega)]
  generalize hgateIndex :
    (⟨(embedInnerOutput output).val - N, by
        change N + G₁ + output.val - N < G₁ + K + G₂
        omega⟩ : Fin (G₁ + K + G₂)) = gateIndex
  have hgateIndexValue : gateIndex.val = G₁ + output.val := by
    rw [← hgateIndex]
    simp only [embedInnerOutput]
    omega
  have hgateIndexEq :
      gateIndex = (⟨G₁ + output.val, by omega⟩ :
        Fin (G₁ + K + G₂)) :=
    Fin.ext hgateIndexValue
  rw [hgateIndexEq]
  change
    1 + Fin.foldl
        (composeGate outer inner
          ⟨G₁ + output.val, by omega⟩).val.fanIn
        (fun acc gateInput => max acc
          ((outer.compose inner).wireDepth
            ((composeGate outer inner
              ⟨G₁ + output.val, by omega⟩).val.inputs gateInput))) 0 =
      inner.outputDepth output
  rw [composeGate_innerOutput outer inner _ (by omega) (by omega)]
  have houtputIndex :
      (⟨(⟨G₁ + output.val, by omega⟩ :
          Fin (G₁ + K + G₂)).val - G₁, by omega⟩ : Fin K) =
        output := by
    apply Fin.ext
    dsimp only
    omega
  rw [houtputIndex]
  unfold Circuit.outputDepth
  congr 1
  congr 1
  funext acc gateInput
  congr 1
  exact wireDepth_compose_inner_internal outer inner _

theorem wireDepth_compose_outer_le_internal
    (outer : Circuit B K M G₂) (inner : Circuit B N K G₁)
    (wire : Fin (K + G₂)) :
    (outer.compose inner).wireDepth (embedOuterWire wire) ≤
      inner.depth + outer.wireDepth wire := by
  induction hwire : wire.val using Nat.strong_induction_on
      generalizing wire with
  | h wireIndex ih =>
      by_cases hinput : wire.val < K
      · rw [Circuit.wireDepth_of_lt outer wire hinput]
        have hembed :
            embedOuterWire (N := N) (G₁ := G₁) wire =
              embedInnerOutput (N := N) (G₁ := G₁)
                (⟨wire.val, hinput⟩ : Fin K) := by
          apply Fin.ext
          simp [embedOuterWire, embedInnerOutput, hinput]
        rw [hembed,
          wireDepth_compose_innerOutput_internal outer inner]
        have houtput :
            inner.outputDepth (⟨wire.val, hinput⟩ : Fin K) ≤
              inner.depth := by
          unfold Circuit.depth
          exact le_fold_max inner.outputDepth ⟨wire.val, hinput⟩
        omega
      · rw [Circuit.wireDepth_of_not_lt outer wire hinput]
        have hembedNotInput :
            ¬(embedOuterWire (N := N) (G₁ := G₁) wire).val < N := by
          simp only [embedOuterWire, hinput, dite_false]
          omega
        rw [Circuit.wireDepth_of_not_lt (outer.compose inner)
          (embedOuterWire wire) hembedNotInput]
        generalize hgateIndex :
          (⟨(embedOuterWire (N := N) (G₁ := G₁) wire).val - N,
              by omega⟩ : Fin (G₁ + K + G₂)) = gateIndex
        have hgateIndexValue :
            gateIndex.val = G₁ + K + (wire.val - K) := by
          rw [← hgateIndex]
          simp only [embedOuterWire, hinput, dite_false]
          omega
        have hgateIndexEq :
            gateIndex =
              (⟨G₁ + K + (wire.val - K), by omega⟩ :
                Fin (G₁ + K + G₂)) :=
          Fin.ext hgateIndexValue
        rw [hgateIndexEq]
        change
          1 + Fin.foldl
              (composeGate outer inner
                ⟨G₁ + K + (wire.val - K), by omega⟩).val.fanIn
              (fun acc gateInput => max acc
                ((outer.compose inner).wireDepth
                  ((composeGate outer inner
                    ⟨G₁ + K + (wire.val - K), by omega⟩).val.inputs
                      gateInput))) 0 ≤
            inner.depth +
              (1 + Fin.foldl
                (outer.gates ⟨wire.val - K, by omega⟩).fanIn
                (fun acc gateInput => max acc
                  (outer.wireDepth
                    ((outer.gates
                      ⟨wire.val - K, by omega⟩).inputs gateInput))) 0)
        rw [composeGate_outer outer inner _ (by omega) (by omega)]
        have houterIndex :
            (⟨(⟨G₁ + K + (wire.val - K), by omega⟩ :
                Fin (G₁ + K + G₂)).val - G₁ - K, by omega⟩ :
              Fin G₂) =
              ⟨wire.val - K, by omega⟩ := by
          apply Fin.ext
          dsimp only
          omega
        rw [houterIndex]
        simp only [Gate.rewire]
        have hfold := fold_max_le_add_fold_max inner.depth
          (fun gateInput =>
            outer.wireDepth
              ((outer.gates
                ⟨wire.val - K, by omega⟩).inputs gateInput))
          (fun gateInput =>
            (outer.compose inner).wireDepth
              (embedOuterWire
                ((outer.gates
                  ⟨wire.val - K, by omega⟩).inputs gateInput)))
          (fun gateInput => by
            let source :=
              (outer.gates
                ⟨wire.val - K, by omega⟩).inputs gateInput
            exact ih source.val (by
              have hacyclic :=
                outer.acyclic ⟨wire.val - K, by omega⟩ gateInput
              change source.val < K + (wire.val - K) at hacyclic
              omega) source rfl)
        omega

theorem depth_compose_le_internal
    (outer : Circuit B K M G₂) (inner : Circuit B N K G₁) :
    (outer.compose inner).depth ≤ inner.depth + outer.depth := by
  have houtput : ∀ output,
      (outer.compose inner).outputDepth output ≤
        inner.depth + outer.outputDepth output := by
    intro output
    unfold Circuit.outputDepth
    change
      1 + Fin.foldl (outer.outputs output).fanIn
          (fun acc gateInput => max acc
            ((outer.compose inner).wireDepth
              (embedOuterWire
                ((outer.outputs output).inputs gateInput)))) 0 ≤
        inner.depth +
          (1 + Fin.foldl (outer.outputs output).fanIn
            (fun acc gateInput => max acc
              (outer.wireDepth
                ((outer.outputs output).inputs gateInput))) 0)
    have hfold := fold_max_le_add_fold_max inner.depth
      (fun gateInput =>
        outer.wireDepth ((outer.outputs output).inputs gateInput))
      (fun gateInput =>
        (outer.compose inner).wireDepth
          (embedOuterWire ((outer.outputs output).inputs gateInput)))
      (fun gateInput =>
        wireDepth_compose_outer_le_internal outer inner
          ((outer.outputs output).inputs gateInput))
    omega
  unfold Circuit.depth
  exact fold_max_le_add_fold_max inner.depth
    outer.outputDepth (outer.compose inner).outputDepth houtput

end Circuit

end Complexity
