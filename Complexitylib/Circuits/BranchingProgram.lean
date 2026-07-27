/-
Copyright (c) 2025 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Mathlib.GroupTheory.Perm.Basic
public import Mathlib.Algebra.BigOperators.Group.List.Basic
public import Mathlib.Data.Finset.Basic

/-!
# Permutation branching programs

Width-`w` **permutation branching programs**: a program is a list of
instructions, each of which reads one input variable and applies one of two
permutations of `Fin w` accordingly; the program evaluates to the ordered
product of the selected permutations (roadmap track M3, toward Barrington's
theorem).

## Main definitions and results

- `BPInstr`, `BP` — instructions and programs
- `BP.eval` — the evaluated permutation
- `BP.eval_append`, `BP.eval_cons` — the product (append/cons) semantics that
  Barrington's inductive construction rests on
-/

@[expose] public section

namespace Complexity

/-- A single width-`w` branching-program instruction: read variable `var`, and
    apply `perm1` if it is `true`, `perm0` if it is `false`. -/
structure BPInstr (w : ℕ) where
  /-- The input variable this instruction reads. -/
  var : ℕ
  /-- The permutation applied when the variable is `false`. -/
  perm0 : Equiv.Perm (Fin w)
  /-- The permutation applied when the variable is `true`. -/
  perm1 : Equiv.Perm (Fin w)

/-- A width-`w` permutation branching program is a list of instructions. -/
abbrev BP (w : ℕ) := List (BPInstr w)

/-- The permutation an instruction selects under an assignment. -/
def BPInstr.eval {w : ℕ} (α : ℕ → Bool) (ins : BPInstr w) : Equiv.Perm (Fin w) :=
  if α ins.var then ins.perm1 else ins.perm0

namespace BP

/-- Evaluate a branching program to a permutation: the ordered product of its
    instructions' selected permutations. -/
def eval {w : ℕ} (α : ℕ → Bool) (p : BP w) : Equiv.Perm (Fin w) :=
  (p.map (BPInstr.eval α)).prod

@[simp] theorem eval_nil {w : ℕ} (α : ℕ → Bool) : eval α ([] : BP w) = 1 := rfl

/-- **Product semantics.** Concatenating programs multiplies their evaluated
    permutations — the compositional law underlying Barrington's construction. -/
theorem eval_append {w : ℕ} (α : ℕ → Bool) (p q : BP w) :
    eval α (p ++ q) = eval α p * eval α q := by
  simp only [eval, List.map_append, List.prod_append]

/-- Evaluating a `cons` prepends the head instruction's permutation. -/
theorem eval_cons {w : ℕ} (α : ℕ → Bool) (ins : BPInstr w) (p : BP w) :
    eval α (ins :: p) = BPInstr.eval α ins * eval α p := by
  simp only [eval, List.map_cons, List.prod_cons]

/-- A single-instruction program evaluates to that instruction's permutation. -/
theorem eval_singleton {w : ℕ} (α : ℕ → Bool) (ins : BPInstr w) :
    eval α [ins] = BPInstr.eval α ins := by
  rw [eval_cons, eval_nil, mul_one]

end BP

/-- Rename the input variables of an instruction along `σ`. -/
def BPInstr.rename {w : ℕ} (σ : ℕ → ℕ) (ins : BPInstr w) : BPInstr w :=
  { ins with var := σ ins.var }

/-- Rename the input variables throughout a program. -/
def BP.rename {w : ℕ} (σ : ℕ → ℕ) (p : BP w) : BP w := p.map (BPInstr.rename σ)

/-- Renaming an instruction's variables is a semantics-preserving relabeling:
    evaluating the renamed instruction at `α` equals evaluating the original at
    `α ∘ σ`. -/
theorem BPInstr.eval_rename {w : ℕ} (α : ℕ → Bool) (σ : ℕ → ℕ) (ins : BPInstr w) :
    BPInstr.eval α (BPInstr.rename σ ins) = BPInstr.eval (α ∘ σ) ins := rfl

/-- **Evaluation is invariant under a semantics-preserving variable rename**:
    evaluating the renamed program at `α` equals evaluating the original at
    `α ∘ σ`. -/
theorem BP.eval_rename {w : ℕ} (α : ℕ → Bool) (σ : ℕ → ℕ) (p : BP w) :
    BP.eval α (BP.rename σ p) = BP.eval (α ∘ σ) p := by
  simp only [BP.eval, BP.rename, List.map_map]
  rfl

/-- The set of input variables a branching program reads. -/
def BP.vars {w : ℕ} (p : BP w) : Finset ℕ := (p.map BPInstr.var).toFinset

/-- Agreement on an instruction's variable fixes the permutation it selects. -/
theorem BPInstr.eval_eq_of_agree {w : ℕ} (ins : BPInstr w) (α β : ℕ → Bool)
    (h : α ins.var = β ins.var) : BPInstr.eval α ins = BPInstr.eval β ins := by
  simp only [BPInstr.eval, h]

/-- **Locality.** A branching program's value depends only on the variables it
    reads: if two assignments agree on `BP.vars p`, they yield the same
    permutation. -/
theorem BP.eval_eq_of_agree {w : ℕ} (p : BP w) (α β : ℕ → Bool)
    (h : ∀ i ∈ BP.vars p, α i = β i) : BP.eval α p = BP.eval β p := by
  simp only [BP.eval]
  congr 1
  apply List.map_congr_left
  intro ins hins
  apply BPInstr.eval_eq_of_agree
  exact h ins.var (by
    simp only [BP.vars, List.mem_toFinset, List.mem_map]; exact ⟨ins, hins, rfl⟩)

end Complexity
