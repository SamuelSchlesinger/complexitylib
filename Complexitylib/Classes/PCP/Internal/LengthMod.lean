/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/
module
public import Complexitylib.Classes.P.Cobham.Internal
public import Complexitylib.Classes.P.FinsetDomain
public import Complexitylib.Classes.P.UnaryLength
public import Complexitylib.Classes.P.Composition
public import Complexitylib.Classes.P.DecisionFn
public import Complexitylib.Classes.Containments.Internal.FPBridge

/-!
# Counting an input's length modulo four

A single polynomial-time language, built because the analysis of the `PCP`
statement needs one concrete verdict that depends on the length of its input:
the strings whose length is divisible by four.

The construction is the obvious one, assembled from the existing toolkit rather
than from a machine. A counter with four states is a *finite* function, so
`ite_mem_finset_mem_FP` puts one step of it in `FP`; `unaryLength_mem_FP`
supplies one tick per input bit; and `iterate_mem_FP` runs the ticks.

## Main definitions

- `Complexity.ctrStep` — one step of a counter modulo four
- `Complexity.lenMod4` — the language of lengths divisible by four

## Main results

- `Complexity.lenMod4_mem_P` — it is polynomial-time decidable
-/

@[expose] public section

namespace Complexity

/-- The four states of the counter, as unary strings. -/
def ctrVals : Finset (List Bool) := {[], [true], [true, true], [true, true, true]}

/-- One step of a counter modulo four. Outside the four states it resets, which
keeps the function total without leaving the finite table. -/
def ctrStep (s : List Bool) : List Bool :=
  if s ∈ ctrVals then (if s.length = 3 then [] else s ++ [true]) else []

theorem ctrStep_mem_FP : ctrStep ∈ FP :=
  ite_mem_finset_mem_FP (fun s => if s.length = 3 then [] else s ++ [true]) ctrVals

theorem replicate_mem_ctrVals {k : ℕ} (hk : k < 4) :
    List.replicate k true ∈ ctrVals := by
  match k, hk with
  | 0, _ => decide
  | 1, _ => decide
  | 2, _ => decide
  | 3, _ => decide

/-- **The counter counts.** -/
theorem ctrStep_iterate (n : ℕ) : ctrStep^[n] [] = List.replicate (n % 4) true := by
  induction n with
  | zero => rfl
  | succ m ih =>
      rw [Function.iterate_succ_apply', ih, ctrStep,
        ite_eq_left (replicate_mem_ctrVals (Nat.mod_lt _ (by norm_num)))]
      have hlen : (List.replicate (m % 4) true).length = m % 4 := List.length_replicate
      rw [hlen]
      by_cases h3 : m % 4 = 3
      · rw [ite_eq_left h3]
        have : (m + 1) % 4 = 0 := by omega
        rw [this]
        rfl
      · rw [ite_eq_right h3]
        have hm : (m + 1) % 4 = m % 4 + 1 := by
          have := Nat.mod_lt m (show 0 < 4 by norm_num)
          omega
        rw [hm, List.replicate_succ']

theorem length_ctrStep_iterate_le (n : ℕ) : (ctrStep^[n] []).length ≤ 3 := by
  rw [ctrStep_iterate, List.length_replicate]
  omega

/-- The counter, run once per input bit. -/
def lenCtr (z : List Bool) : List Bool := ctrStep^[z.length] []

theorem lenCtr_mem_FP : lenCtr ∈ FP := by
  have hiter := Cobham.iterate_mem_FP (F := ctrStep) (init := fun _ : List Bool => [])
    (ruler := fun z : List Bool => List.replicate z.length true)
    (width := fun _ : List Bool => [true, true, true])
    ctrStep_mem_FP (constFn_mem_FP []) unaryLength_mem_FP
    (constFn_mem_FP [true, true, true])
    (fun z n _ => by
      have := length_ctrStep_iterate_le n
      simpa using this)
  refine mem_FP_of_eq hiter fun z => ?_
  rw [lenCtr, List.length_replicate]

/-- Reading the counter: it is zero exactly on the multiples of four. -/
def ctrIsZero (s : List Bool) : List Bool :=
  if s ∈ ctrVals then (if s = [] then [true] else [false]) else []

theorem ctrIsZero_mem_FP : ctrIsZero ∈ FP :=
  ite_mem_finset_mem_FP (fun s => if s = [] then [true] else [false]) ctrVals

/-- **The language of lengths divisible by four.** -/
def lenMod4 : Language := {z | z.length % 4 = 0}

theorem lenMod4_mem_P : lenMod4 ∈ P := by
  refine mem_P_of_decisionFn_bool (g := fun z => decide (z.length % 4 = 0)) ?_ ?_
  · refine mem_FP_of_eq (mem_FP_comp lenCtr_mem_FP ctrIsZero_mem_FP) fun z => ?_
    show ctrIsZero (lenCtr z) = _
    rw [lenCtr, ctrStep_iterate, ctrIsZero,
      ite_eq_left (replicate_mem_ctrVals (Nat.mod_lt _ (by norm_num)))]
    by_cases h : z.length % 4 = 0
    · rw [h]
      rfl
    · rw [ite_eq_right (by
        intro hnil
        exact h (by
          have := congrArg List.length hnil
          rw [List.length_replicate] at this
          simpa using this))]
      simp [h]
  · intro z
    show z ∈ lenMod4 ↔ _
    rw [lenMod4]
    simp

end Complexity
