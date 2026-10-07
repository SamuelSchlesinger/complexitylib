/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module
public import Complexitylib.Circuits.DepthThree.LowerBound.Internal.MachineBasic
public import Mathlib.Tactic.DeriveFintype

/-!
# Unrestricted depth-three lower bound: multi tape machine

Adapted from OpenAI's formalization at revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
Source: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/DepthThree/MultiTapeMachine.lean

Imports, namespaces, module visibility, documentation, and formatting are adapted
for complexitylib. The source theorem statements and mathematical proofs are retained.
-/

@[expose] public section

namespace Complexity

universe uDepth1 uDepth2 uDepth3 uDepth4 uDepth5 uDepth6 uDepth7 uDepth8 uDepth9

namespace DepthThreeLowerBound

deriving instance DecidableEq, Inhabited for HeadMove

instance : Fintype HeadMove where
  elems := { .left, .stay, .right }
  complete := by
    intro m
    cases m <;> simp

@[simp] theorem HeadMove.apply_left {Γ : Type uDepth1} [Inhabited Γ] (t : Turing.Tape Γ) :
    HeadMove.left.apply t = t.move Turing.Dir.left := rfl

@[simp] theorem HeadMove.apply_stay {Γ : Type uDepth2} [Inhabited Γ] (t : Turing.Tape Γ) :
    HeadMove.stay.apply t = t := rfl

@[simp] theorem HeadMove.apply_right {Γ : Type uDepth3} [Inhabited Γ] (t : Turing.Tape Γ) :
    HeadMove.right.apply t = t.move Turing.Dir.right := rfl

theorem multiTapeStep_eq_some {K : Type uDepth4} {Γ : Type uDepth5} {Q : Type uDepth6} [Inhabited Γ]
    {code : MultiTapeCode K Γ Q} {c : MultiTapeCfg K Γ Q}
    {q : Q} {writes : K → Γ} {moves : K → HeadMove}
    (h : code c.q (fun k => (c.tapes k).head) = some (q, writes, moves)) :
    multiTapeStep code c = some (multiTapeUpdate c q writes moves) := by
  simp only [multiTapeStep, h, Option.map_some]

@[simp] theorem multiTapeStep_eq_none_iff {K : Type uDepth7} {Γ : Type uDepth8} {Q : Type uDepth9}
  [Inhabited Γ]
    (code : MultiTapeCode K Γ Q) (c : MultiTapeCfg K Γ Q) :
    multiTapeStep code c = none ↔ code c.q (fun k => (c.tapes k).head) = none := by
  unfold multiTapeStep
  cases h : code c.q (fun k => (c.tapes k).head) <;> simp

namespace FiniteMultiTapeMachine

@[simp] theorem init_q (M : FiniteMultiTapeMachine) (input : List Bool) :
    (M.init input).q = M.initialState := rfl

@[simp] theorem init_inputTape (M : FiniteMultiTapeMachine) (input : List Bool) :
    (M.init input).tapes M.inputTape = Turing.Tape.mk₁ (input.map M.inputSymbol) := by
  simp [init]

theorem init_otherTape (M : FiniteMultiTapeMachine) (input : List Bool)
    (k : M.K) (hk : k ≠ M.inputTape) :
    (M.init input).tapes k = Turing.Tape.mk₁ [] := by
  simp [init, hk]

end FiniteMultiTapeMachine

theorem multiTapeHaltsIn_iff_runsIn (M : FiniteMultiTapeMachine) (input : List Bool)
    (output : Bool) (time : ℕ) :
    MultiTapeHaltsIn M input output time ↔
      ∃ c : M.Cfg, RunsIn M.step (M.init input) c time ∧
        M.step c = none ∧ M.accept c.q = output := by
  constructor
  · rintro ⟨k, hk, c, hrun, hhalt, hout⟩
    exact ⟨c, ⟨k, hk, hrun⟩, hhalt, hout⟩
  · rintro ⟨c, ⟨k, hk, hrun⟩, hhalt, hout⟩
    exact ⟨k, hk, c, hrun, hhalt, hout⟩

theorem MultiTapeHaltsIn.mono {M : FiniteMultiTapeMachine} {input : List Bool}
    {output : Bool} {m n : ℕ} (h : MultiTapeHaltsIn M input output m) (hmn : m ≤ n) :
    MultiTapeHaltsIn M input output n := by
  obtain ⟨k, hk, c, hrun, hhalt, hout⟩ := h
  exact ⟨k, hk.trans hmn, c, hrun, hhalt, hout⟩

/-- A fixed finite multitape machine decides the language in polynomial time. -/
def MultiTapePolynomialTimeDecider (f : List Bool → Bool) : Prop :=
  ∃ M : FiniteMultiTapeMachine, ∃ C a : ℕ, 0 < C ∧ 0 < a ∧
    ∀ w, MultiTapeHaltsIn M w (f w) (C * (w.length + 1) ^ a)

end DepthThreeLowerBound

end Complexity
