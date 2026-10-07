/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Nechiporuk.Sharing.Defs
public import Complexitylib.Algebraic.Support

/-!
# Internals of programs with shared gates over the full binary basis

Proof internals for `Complexitylib.Algebraic.LowerBound.Nechiporuk.Sharing`:

- leaf and occurrence bookkeeping for `Binary.Formula`, including reindexing (`mapIndex`) and
  substitution of a formula for a variable (`subst`, `substVarMap`);
- the block-advancing combinatorics of `SharedProgram.castBlock`, `snocBlock`, and `stepBlock`,
  and the gluing identities used to restrict a `share` step to a block
  (`SharedProgram.glue_castBlock`, `SharedProgram.glue_snocBlock`), which yield the one-step
  subfunction bounds `SharedProgram.card_subfunctions_share_le_of_leavesIn_eq_zero` and
  `SharedProgram.card_subfunctions_share_le_mul`;
- substitution of a formula for a shared variable (`SharedProgram.substVar`) and its effect on
  gates, occurrences, and active measures;
- the translation of a full-binary-basis program into a `SharedProgram`, processing gates from
  the last one down (`exists_sharedProgram_of_program`): a gate read at least twice becomes a
  shared gate, and any other gate is substituted into the program;
- the characterization of `gateActive` by the syntactic input support
  (`Internal.gateActive_eq_true_iff`), the resulting block-span bound over disjoint blocks
  (`Internal.gateBlockSpan_le_card_wireSupport`), and the counting of gate-argument uses behind
  `Internal.sharedFanOut_le_two_mul_size_add_one`.
-/

@[expose] public section

namespace Algebraic

namespace Binary
namespace Formula

variable {N : Nat}

/-- The variable leaves of a binary formula number at most its binary gates plus one. -/
theorem leaves_le_gates_add_one : ∀ F : Formula N, F.leaves ≤ F.gates + 1
  | var _ => le_rfl
  | const _ => Nat.zero_le _
  | gate _ l r => by
    simp only [leaves, gates]
    have := leaves_le_gates_add_one l
    have := leaves_le_gates_add_one r
    omega

/-- Reindex the variables of a formula. -/
def mapIndex {M : Nat} (φ : Fin N → Fin M) : Formula N → Formula M
  | var i => var (φ i)
  | const b => const b
  | gate op l r => gate op (l.mapIndex φ) (r.mapIndex φ)

/-- Evaluating a reindexed formula is evaluating the original on the reindexed assignment. -/
@[simp] theorem eval_mapIndex {M : Nat} (φ : Fin N → Fin M) :
    ∀ (F : Formula N) (x : Fin M → Bool), (F.mapIndex φ).eval x = F.eval (x ∘ φ)
  | var _, _ => rfl
  | const _, _ => rfl
  | gate op l r, x => by
    simp [mapIndex, eval_mapIndex φ l x, eval_mapIndex φ r x]

/-- Reindexing variables does not change the number of gates. -/
@[simp] theorem gates_mapIndex {M : Nat} (φ : Fin N → Fin M) :
    ∀ F : Formula N, (F.mapIndex φ).gates = F.gates
  | var _ => rfl
  | const _ => rfl
  | gate _ l r => by simp [mapIndex, gates, gates_mapIndex φ l, gates_mapIndex φ r]

/-- The leaves of a reindexed formula in `Y` are the leaves of the original in the preimage of
`Y`. -/
theorem leavesIn_mapIndex {M : Nat} (φ : Fin N → Fin M) (Y : Finset (Fin M)) :
    ∀ F : Formula N,
      (F.mapIndex φ).leavesIn Y = F.leavesIn (Finset.univ.filter fun i => φ i ∈ Y)
  | var _ => by simp [mapIndex, leavesIn]
  | const _ => rfl
  | gate _ l r => by
    simp [mapIndex, leavesIn, leavesIn_mapIndex φ Y l, leavesIn_mapIndex φ Y r]

/-- Substitute a formula for each variable. -/
def subst {M : Nat} (σ : Fin N → Formula M) : Formula N → Formula M
  | var i => σ i
  | const b => const b
  | gate op l r => gate op (l.subst σ) (r.subst σ)

/-- Evaluating a substituted formula evaluates the original on the values of the substitutes. -/
theorem eval_subst {M : Nat} (σ : Fin N → Formula M) :
    ∀ (F : Formula N) (x : Fin M → Bool),
      (F.subst σ).eval x = F.eval fun i => (σ i).eval x
  | var _, _ => rfl
  | const _, _ => rfl
  | gate op l r, x => by
    simp [subst, eval_subst σ l x, eval_subst σ r x]

/-- Embedding the variables with `Fin.castLE` preserves occurrence counts. -/
@[simp] theorem occ_mapIndex_castLE {M : Nat} (v : Nat) (h : N ≤ M) :
    ∀ F : Formula N, (F.mapIndex (Fin.castLE h)).occ v = F.occ v
  | var _ => rfl
  | const _ => rfl
  | gate _ l r => by simp [mapIndex, occ, occ_mapIndex_castLE v h l, occ_mapIndex_castLE v h r]

/-- A variable index at least `N` never occurs in a formula on `N` variables. -/
theorem occ_eq_zero_of_ge {v : Nat} (hv : N ≤ v) : ∀ F : Formula N, F.occ v = 0
  | var i => by
    have : i.val ≠ v := by omega
    simp [occ, this]
  | const _ => rfl
  | gate _ l r => by simp [occ, occ_eq_zero_of_ge hv l, occ_eq_zero_of_ge hv r]

/-- The input leaves are among all variable leaves. -/
theorem inputLeaves_le_leaves (m : Nat) : ∀ F : Formula N, F.inputLeaves m ≤ F.leaves
  | var _ => by
    simp only [inputLeaves, leaves]
    split <;> omega
  | const _ => Nat.zero_le _
  | gate _ l r => Nat.add_le_add (inputLeaves_le_leaves m l) (inputLeaves_le_leaves m r)

/-- The input leaves of a binary formula number at most its binary gates plus one. -/
theorem inputLeaves_le_gates_add_one (m : Nat) (F : Formula N) :
    F.inputLeaves m ≤ F.gates + 1 :=
  (F.inputLeaves_le_leaves m).trans F.leaves_le_gates_add_one

/-- A formula on `N` variables has no leaves on variables from `m ≥ N` on. -/
theorem sharedLeaves_eq_zero_of_le {m : Nat} (hm : N ≤ m) :
    ∀ F : Formula N, F.sharedLeaves m = 0
  | var i => by
    have : ¬ m ≤ i.val := by omega
    simp [sharedLeaves, this]
  | const _ => rfl
  | gate _ l r => by
    simp [sharedLeaves, sharedLeaves_eq_zero_of_le hm l, sharedLeaves_eq_zero_of_le hm r]

/-- Embedding the variables with `Fin.castLE` preserves shared-leaf counts. -/
@[simp] theorem sharedLeaves_mapIndex_castLE {M : Nat} (m : Nat) (h : N ≤ M) :
    ∀ F : Formula N, (F.mapIndex (Fin.castLE h)).sharedLeaves m = F.sharedLeaves m
  | var _ => rfl
  | const _ => rfl
  | gate _ l r => by
    simp [mapIndex, sharedLeaves, sharedLeaves_mapIndex_castLE m h l,
      sharedLeaves_mapIndex_castLE m h r]

/-- The shared leaves from `m` on split into the occurrences of `m` and the shared leaves from
`m + 1` on. -/
theorem sharedLeaves_eq_occ_add_sharedLeaves_succ (m : Nat) :
    ∀ F : Formula N, F.sharedLeaves m = F.occ m + F.sharedLeaves (m + 1)
  | var i => by
    simp only [sharedLeaves, occ]
    split_ifs <;> omega
  | const _ => rfl
  | gate _ l r => by
    simp only [sharedLeaves, occ, sharedLeaves_eq_occ_add_sharedLeaves_succ m l,
      sharedLeaves_eq_occ_add_sharedLeaves_succ m r]
    omega

/-- Over pairwise disjoint blocks of `Fin n`, `inputLeavesIn` sums to at most `inputLeaves n`. -/
theorem sum_inputLeavesIn_le_inputLeaves {m n : Nat} (Y : Fin m → Finset (Fin n))
    (disjoint : Pairwise fun i j => Disjoint (Y i) (Y j)) :
    ∀ F : Formula N, ∑ i, F.inputLeavesIn (Y i) ≤ F.inputLeaves n
  | var idx => by
    simp only [inputLeavesIn, inputLeaves]
    by_cases h : idx.val < n
    · simp only [h, ↓reduceDIte, ↓reduceIte]
      rw [Finset.sum_boole]
      apply Finset.card_le_one.mpr
      intro i hi j hj
      rw [Finset.mem_filter] at hi hj
      by_contra hne
      exact Finset.disjoint_left.mp (disjoint hne) hi.2 hj.2
    · simp [h]
  | const _ => by simp [inputLeavesIn, inputLeaves]
  | gate _ l r => by
    simp only [inputLeavesIn, inputLeaves, Finset.sum_add_distrib]
    exact Nat.add_le_add (sum_inputLeavesIn_le_inputLeaves Y disjoint l)
      (sum_inputLeavesIn_le_inputLeaves Y disjoint r)

/-- Extend a block `Y ⊆ Fin n` to `Fin N` by including all shared variables `i ≥ n`. -/
def extendBlock (N : Nat) {n : Nat} (Y : Finset (Fin n)) : Finset (Fin N) :=
  Finset.univ.filter fun i : Fin N => if h : i.val < n then ⟨i.val, h⟩ ∈ Y else True

/-- Extending a block of `Fin n` to `Fin n` itself does not change it. -/
theorem extendBlock_self {n : Nat} (Y : Finset (Fin n)) : extendBlock n Y = Y := by
  ext i
  simp [extendBlock]

/-- The leaves in the extended block are the input leaves in `Y` plus all shared leaves. -/
theorem leavesIn_extendBlock (N : Nat) {n : Nat} (Y : Finset (Fin n)) :
    ∀ F : Formula N, F.leavesIn (extendBlock N Y) = F.inputLeavesIn Y + F.sharedLeaves n
  | var i => by
    simp only [leavesIn, extendBlock, Finset.mem_filter, Finset.mem_univ, true_and,
      inputLeavesIn, sharedLeaves]
    by_cases h : i.val < n
    · have hnot : ¬ n ≤ i.val := by omega
      by_cases hy : ⟨i.val, h⟩ ∈ Y <;> simp [h, hnot, hy]
    · have hle : n ≤ i.val := by omega
      simp [h, hle]
  | const _ => rfl
  | gate _ l r => by
    simp only [leavesIn, inputLeavesIn, sharedLeaves,
      leavesIn_extendBlock N Y l, leavesIn_extendBlock N Y r]
    omega

/-- Decompose `F.leavesIn Y` into input leaves in `Y₀` and occurrences of shared variables in `Y`
when `Y` agrees with `Y₀` below `n`. -/
theorem leavesIn_eq_inputLeavesIn_add_sum_occ {n : Nat} (Y₀ : Finset (Fin n))
    (Y : Finset (Fin N)) (hY : ∀ (i : Fin N) (hi : i.val < n), i ∈ Y ↔ ⟨i.val, hi⟩ ∈ Y₀) :
    ∀ F : Formula N,
      F.leavesIn Y = F.inputLeavesIn Y₀ + ∑ i ∈ Y, if n ≤ i.val then F.occ i.val else 0
  | var idx => by
    simp only [leavesIn, inputLeavesIn, occ]
    by_cases h : idx.val < n
    · have hsum : (∑ i ∈ Y, if n ≤ i.val then (if idx.val = i.val then 1 else 0) else 0) = 0 := by
        refine Finset.sum_eq_zero fun i _ => ?_
        split_ifs <;> omega
      rw [hsum, add_zero, dite_eq_left h]
      by_cases hy : idx ∈ Y
      · have hy0 : ⟨idx.val, h⟩ ∈ Y₀ := (hY idx h).mp hy
        simp [hy, hy0]
      · have hy0 : ⟨idx.val, h⟩ ∉ Y₀ := fun h0 => hy ((hY idx h).mpr h0)
        simp [hy, hy0]
    · have hle : n ≤ idx.val := by omega
      rw [dite_eq_right h, zero_add]
      have hcongr : (∑ i ∈ Y, if n ≤ i.val then (if idx.val = i.val then 1 else 0) else 0) =
          ∑ i ∈ Y, if i = idx then 1 else 0 := by
        refine Finset.sum_congr rfl fun i _ => ?_
        by_cases heq : i = idx
        · subst heq; simp [hle]
        · have hne : idx.val ≠ i.val := fun hv => heq (Fin.ext hv.symm)
          simp [heq, hne]
      rw [hcongr, Finset.sum_ite_eq']
  | const _ => by simp [leavesIn, inputLeavesIn, occ]
  | gate _ l r => by
    simp only [leavesIn, inputLeavesIn, occ,
      leavesIn_eq_inputLeavesIn_add_sum_occ Y₀ Y hY l,
      leavesIn_eq_inputLeavesIn_add_sum_occ Y₀ Y hY r]
    have hdistrib : (∑ i ∈ Y, if n ≤ i.val then l.occ i.val + r.occ i.val else 0) =
        (∑ i ∈ Y, if n ≤ i.val then l.occ i.val else 0) +
          ∑ i ∈ Y, if n ≤ i.val then r.occ i.val else 0 := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      split_ifs <;> omega
    rw [hdistrib]
    omega

/-- Insert membership `b` at variable `N`, shifting variables `≥ N` up by one. -/
def liftBlock {d : Nat} (b : Bool) (W : Finset (Fin (N + d))) : Finset (Fin (N + 1 + d)) :=
  Finset.univ.filter fun i : Fin (N + 1 + d) =>
    if h : i.val < N then ⟨i.val, by omega⟩ ∈ W
    else if _ : i.val = N then b = true
    else ⟨i.val - 1, by omega⟩ ∈ W

/-- Including variable `N` in a lifted block adds exactly the occurrences of `N`. -/
theorem leavesIn_liftBlock_true (d : Nat) (W : Finset (Fin (N + d))) :
    ∀ F : Formula (N + 1 + d),
      F.leavesIn (liftBlock true W) = F.leavesIn (liftBlock false W) + F.occ N
  | var i => by
    simp only [leavesIn, liftBlock, Finset.mem_filter, Finset.mem_univ, true_and, occ]
    by_cases h1 : i.val < N
    · have h2 : i.val ≠ N := by omega
      simp [h1, h2]
    · by_cases h2 : i.val = N <;> simp [h1, h2]
  | const _ => rfl
  | gate _ l r => by
    simp only [leavesIn, occ, leavesIn_liftBlock_true d W l, leavesIn_liftBlock_true d W r]
    omega

/-- The substitution map replacing variable `N` by `φ`, keeping variables below `N`, and shifting
variables above `N` down by one. -/
def substVarMap (φ : Formula N) (d : Nat) (i : Fin (N + 1 + d)) : Formula (N + d) :=
  if h : i.val < N then var ⟨i.val, by omega⟩
  else if _ : i.val = N then φ.mapIndex (Fin.castLE (by omega))
  else var ⟨i.val - 1, by omega⟩

/-- Substituting `φ` for variable `N` adds `φ.gates` once per occurrence of `N`. -/
theorem gates_subst_substVarMap (φ : Formula N) (d : Nat) :
    ∀ F : Formula (N + 1 + d), (F.subst (substVarMap φ d)).gates = F.gates + F.occ N * φ.gates
  | var i => by
    have key : (substVarMap φ d i).gates = (if i.val = N then 1 else 0) * φ.gates := by
      unfold substVarMap
      split_ifs <;> first | omega | simp [gates]
    simp [subst, gates, occ, key]
  | const _ => by simp [subst, gates, occ]
  | gate _ l r => by
    simp only [subst, gates, occ, gates_subst_substVarMap φ d l, gates_subst_substVarMap φ d r]
    ring

/-- Substituting `φ` for variable `N` adds the occurrences of `w < N` in `φ` once per occurrence
of `N`. -/
theorem occ_subst_substVarMap (φ : Formula N) (d : Nat) {w : Nat} (hw : w < N) :
    ∀ F : Formula (N + 1 + d),
      (F.subst (substVarMap φ d)).occ w = F.occ w + F.occ N * φ.occ w
  | var i => by
    have key : (substVarMap φ d i).occ w =
        (if i.val = w then 1 else 0) + (if i.val = N then 1 else 0) * φ.occ w := by
      unfold substVarMap
      split_ifs <;> simp [occ] <;> omega
    simp [subst, occ, key]
  | const _ => by simp [subst, occ]
  | gate _ l r => by
    simp only [subst, occ, occ_subst_substVarMap φ d hw l, occ_subst_substVarMap φ d hw r]
    ring

/-- Substituting for variable `N` shifts the occurrences of variables above `N` down by one. -/
theorem occ_subst_substVarMap_ge (φ : Formula N) (d : Nat) {w : Nat} (hw : N ≤ w) :
    ∀ F : Formula (N + 1 + d),
      (F.subst (substVarMap φ d)).occ w = F.occ (w + 1)
  | var i => by
    dsimp only [subst, substVarMap]
    split_ifs with h1 h2
    · have h3 : i.val ≠ w := by omega
      have h4 : i.val ≠ w + 1 := by omega
      simp [occ, h3, h4]
    · have h4 : i.val ≠ w + 1 := by omega
      simp [occ, h4, occ_eq_zero_of_ge hw]
    · have h3 : (i.val - 1 = w) ↔ (i.val = w + 1) := by omega
      simp [occ, h3]
  | const _ => rfl
  | gate _ l r => by
    simp [subst, occ, occ_subst_substVarMap_ge φ d hw l, occ_subst_substVarMap_ge φ d hw r]

/-- The leaves of a substituted formula in `W` are the leaves of the original outside variable `N`
plus the leaves of `φ` once per occurrence of `N`. -/
theorem leavesIn_subst_substVarMap (φ : Formula N) (d : Nat) (W : Finset (Fin (N + d))) :
    ∀ F : Formula (N + 1 + d),
      (F.subst (substVarMap φ d)).leavesIn W =
        F.leavesIn (liftBlock false W) +
          F.occ N * φ.leavesIn (Finset.univ.filter fun j => Fin.castLE (by omega) j ∈ W)
  | var i => by
    dsimp only [subst, substVarMap]
    split_ifs with h1 h2
    · have hnot : i.val ≠ N := by omega
      simp [leavesIn, liftBlock, h1, hnot, occ]
    · simp [leavesIn, liftBlock, h2, occ, leavesIn_mapIndex]
    · simp [leavesIn, liftBlock, h1, h2, occ]
  | const _ => by simp [subst, leavesIn, occ]
  | gate _ l r => by
    simp only [subst, leavesIn, occ, leavesIn_subst_substVarMap φ d W l,
      leavesIn_subst_substVarMap φ d W r]
    ring

/-- A substituted formula has no leaves in `W` iff the original has none in the block lifted by
whether `φ` has leaves in `W`. -/
theorem leavesIn_subst_substVarMap_eq_zero_iff (φ : Formula N) (d : Nat)
    (W : Finset (Fin (N + d))) (F : Formula (N + 1 + d)) :
    (F.subst (substVarMap φ d)).leavesIn W = 0 ↔
      F.leavesIn (liftBlock (decide (φ.leavesIn
        (Finset.univ.filter fun j => Fin.castLE (by omega) j ∈ W) ≠ 0)) W) = 0 := by
  rw [leavesIn_subst_substVarMap]
  set L := φ.leavesIn (Finset.univ.filter fun j => Fin.castLE (by omega) j ∈ W)
  by_cases hL : L = 0
  · have hdec : decide (L ≠ 0) = false := decide_eq_false (not_not.mpr hL)
    rw [hdec, hL, Nat.mul_zero, Nat.add_zero]
  · have hdec : decide (L ≠ 0) = true := decide_eq_true hL
    rw [hdec, leavesIn_liftBlock_true]
    constructor <;> intro h
    · have : F.occ N * L = 0 := by omega
      have hocc : F.occ N = 0 := by
        rcases mul_eq_zero.mp this with h1 | h2
        · exact h1
        · exact absurd h2 hL
      omega
    · have hocc : F.occ N = 0 := by omega
      rw [hocc, Nat.zero_mul]
      omega

/-- Substituting a formula on `N` variables for variable `N` shifts the shared leaves down by
one. -/
theorem sharedLeaves_subst_substVarMap (φ : Formula N) (d : Nat) :
    ∀ F : Formula (N + 1 + d),
      (F.subst (substVarMap φ d)).sharedLeaves N = F.sharedLeaves (N + 1)
  | var i => by
    dsimp only [subst, substVarMap]
    split_ifs with h1 h2
    · have h3 : ¬ N ≤ i.val := by omega
      have h4 : ¬ N + 1 ≤ i.val := by omega
      simp [sharedLeaves, h3, h4]
    · have h4 : ¬ N + 1 ≤ i.val := by omega
      simp [sharedLeaves, h4, sharedLeaves_eq_zero_of_le le_rfl]
    · have h3 : N ≤ i.val - 1 := by omega
      have h4 : N + 1 ≤ i.val := by omega
      simp [sharedLeaves, h3, h4]
  | const _ => rfl
  | gate _ l r => by
    simp [subst, sharedLeaves, sharedLeaves_subst_substVarMap φ d l,
      sharedLeaves_subst_substVarMap φ d r]

/-- Evaluating a substituted formula evaluates the original with `φ`'s value inserted at `N`. -/
theorem eval_subst_substVarMap (φ : Formula N) (d : Nat) (F : Formula (N + 1 + d))
    (y : Fin (N + d) → Bool) :
    (F.subst (substVarMap φ d)).eval y =
      F.eval (KW.insertVal y (φ.eval fun j => y (Fin.castLE (by omega) j))) := by
  rw [eval_subst]
  congr 1
  funext i
  unfold substVarMap KW.insertVal
  split_ifs <;> simp [Function.comp_def]

end Formula
end Binary

namespace Nechiporuk

open scoped Classical
open Binary Cutwidth

namespace SharedProgram

variable {n N k : Nat}

/-! ### Subfunctions of a program with shared gates -/

/-- `castBlock Y` never contains the new last variable. -/
@[simp] theorem last_notMem_castBlock {N : Nat} (Y : Finset (Fin N)) :
    Fin.last N ∉ castBlock Y := by
  simp only [castBlock, Finset.mem_map, Fin.castSuccEmb_apply, not_exists, not_and]
  intro x _
  exact Fin.ne_of_lt x.isLt

/-- A lifted old variable lies in `castBlock Y` iff it lies in `Y`. -/
@[simp] theorem castSucc_mem_castBlock {N : Nat} (Y : Finset (Fin N)) (i : Fin N) :
    i.castSucc ∈ castBlock Y ↔ i ∈ Y := by
  simp [castBlock]

/-- `snocBlock Y` always contains the new last variable. -/
@[simp] theorem last_mem_snocBlock {N : Nat} (Y : Finset (Fin N)) :
    Fin.last N ∈ snocBlock Y :=
  Finset.mem_insert_self _ _

/-- A lifted old variable lies in `snocBlock Y` iff it lies in `Y`. -/
@[simp] theorem castSucc_mem_snocBlock {N : Nat} (Y : Finset (Fin N)) (i : Fin N) :
    i.castSucc ∈ snocBlock Y ↔ i ∈ Y := by
  have hne : i.castSucc ≠ Fin.last N := Fin.ne_of_lt i.isLt
  simp [snocBlock, hne]

/-- A lifted old variable lies in `stepBlock G Y` iff it lies in `Y`. -/
@[simp] theorem castSucc_mem_stepBlock {N : Nat} (G : Formula N) (Y : Finset (Fin N)) (i : Fin N) :
    i.castSucc ∈ stepBlock G Y ↔ i ∈ Y := by
  unfold stepBlock
  split_ifs <;> simp

/-- The new last variable lies in `stepBlock G Y` iff `G` has a leaf in `Y`. -/
@[simp] theorem last_mem_stepBlock {N : Nat} (G : Formula N) (Y : Finset (Fin N)) :
    Fin.last N ∈ stepBlock G Y ↔ G.leavesIn Y ≠ 0 := by
  unfold stepBlock
  split_ifs with h <;> simp [h]

/-- Adding the new last variable commutes with extending a block by all shared variables. -/
theorem snocBlock_extendBlock {n N : Nat} (hn : n ≤ N) (Y : Finset (Fin n)) :
    snocBlock (Formula.extendBlock N Y) = Formula.extendBlock (N + 1) Y := by
  ext j
  refine Fin.lastCases ?_ (fun i => ?_) j
  · have hnot : ¬ N < n := by omega
    simp [Formula.extendBlock, hnot]
  · simp [castSucc_mem_snocBlock, Formula.extendBlock]

/-- The block leaf count on an extended block is the input leaves in `Y` plus all shared leaves. -/
theorem leavesIn_extendBlock :
    ∀ {N k : Nat} (P : SharedProgram N k) {n : Nat} (_hn : n ≤ N) (Y : Finset (Fin n)),
      P.leavesIn (Formula.extendBlock N Y) = P.inputLeavesIn Y + P.sharedLeaves n
  | N, _, output F, _, _, Y => F.leavesIn_extendBlock N Y
  | N, _, share G P, _, hn, Y => by
    simp only [leavesIn, snocBlock_extendBlock hn Y, G.leavesIn_extendBlock N Y,
      leavesIn_extendBlock P (by omega) Y, inputLeavesIn, sharedLeaves]
    omega

/-- On a primary block, the block leaf count is the input leaves in `Y` plus all shared leaves. -/
theorem leavesIn_eq_inputLeavesIn_add_sharedLeaves (P : SharedProgram n k) (Y : Finset (Fin n)) :
    P.leavesIn Y = P.inputLeavesIn Y + P.sharedLeaves n := by
  have h := leavesIn_extendBlock P le_rfl Y
  rwa [Formula.extendBlock_self] at h

/-- The shared leaves from `m` on split into the occurrences of `m` and the shared leaves from
`m + 1` on. -/
theorem sharedLeaves_eq_occ_add_sharedLeaves_succ (m : Nat) :
    ∀ {N k : Nat} (P : SharedProgram N k),
      P.sharedLeaves m = P.occ m + P.sharedLeaves (m + 1)
  | _, _, output F => F.sharedLeaves_eq_occ_add_sharedLeaves_succ m
  | _, _, share G P => by
    simp only [sharedLeaves, occ, G.sharedLeaves_eq_occ_add_sharedLeaves_succ m,
      sharedLeaves_eq_occ_add_sharedLeaves_succ m P]
    omega

/-- Advancing a block through `stepBlock` adds the term of the new last variable exactly when `G`
is active. -/
private theorem sum_occ_stepBlock {n N : Nat} (hn : n ≤ N) (G : Formula N) (Y : Finset (Fin N))
    (f : Nat → Nat) :
    (∑ j ∈ stepBlock G Y, if n ≤ j.val then f j.val else 0) =
      (if G.leavesIn Y = 0 then 0 else f N) +
        ∑ i ∈ Y, if n ≤ i.val then f i.val else 0 := by
  have hcast : (∑ j ∈ castBlock Y, if n ≤ j.val then f j.val else 0) =
      ∑ i ∈ Y, if n ≤ i.val then f i.val else 0 := by
    rw [castBlock, Finset.sum_map]
    rfl
  unfold stepBlock
  split_ifs with hG
  · rw [hcast, zero_add]
  · rw [snocBlock, ← castBlock, Finset.sum_insert (last_notMem_castBlock Y), hcast]
    simp [hn]

/-- The active leaves of `P` on `Y` split into input leaves in `Y₀`, occurrences of the shared
variables in `Y`, and the active shared-variable leaves, when `Y` agrees with `Y₀` below `n`. -/
theorem activeLeavesIn_eq_inputLeavesIn_add_sum_occ :
    ∀ {N k : Nat} (P : SharedProgram N k) {n : Nat} (_hn : n ≤ N) (Y₀ : Finset (Fin n))
      (Y : Finset (Fin N)),
      (∀ (i : Fin N) (hi : i.val < n), i ∈ Y ↔ ⟨i.val, hi⟩ ∈ Y₀) →
      P.activeLeavesIn Y =
        P.inputLeavesIn Y₀ + (∑ i ∈ Y, if n ≤ i.val then P.occ i.val else 0) +
          P.activeSharedLeaves Y
  | _, 0, output F, _, _, Y₀, Y, hY => by
    simp [activeLeavesIn, inputLeavesIn, occ, activeSharedLeaves,
      F.leavesIn_eq_inputLeavesIn_add_sum_occ Y₀ Y hY]
  | N, _ + 1, share G P, n, hn, Y₀, Y, hY => by
    have hY' : ∀ (j : Fin (N + 1)) (hj : j.val < n), j ∈ stepBlock G Y ↔ ⟨j.val, hj⟩ ∈ Y₀ := by
      intro j hj
      have hjN : j.val < N := by omega
      let i : Fin N := ⟨j.val, hjN⟩
      have hcast : i.castSucc = j := Fin.ext rfl
      calc j ∈ stepBlock G Y
          ↔ i.castSucc ∈ stepBlock G Y := by rw [hcast]
        _ ↔ i ∈ Y := castSucc_mem_stepBlock G Y i
        _ ↔ ⟨j.val, hj⟩ ∈ Y₀ := hY i hj
    have ih := activeLeavesIn_eq_inputLeavesIn_add_sum_occ P (by omega) Y₀ (stepBlock G Y) hY'
    have hG := G.leavesIn_eq_inputLeavesIn_add_sum_occ Y₀ Y hY
    have hstep := sum_occ_stepBlock hn G Y (fun v => P.occ v)
    have hdistrib : (∑ i ∈ Y, if n ≤ i.val then G.occ i.val + P.occ i.val else 0) =
        (∑ i ∈ Y, if n ≤ i.val then G.occ i.val else 0) +
          ∑ i ∈ Y, if n ≤ i.val then P.occ i.val else 0 := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      split_ifs <;> omega
    simp only [activeLeavesIn, inputLeavesIn, occ, activeSharedLeaves, hG, ih, hstep, hdistrib]
    omega

/-- The active leaves of `P` on a primary block `Y ⊆ Fin n` equal `P.inputLeavesIn Y` plus
`P.activeSharedLeaves Y`. -/
theorem activeLeavesIn_eq_inputLeavesIn_add_activeSharedLeaves (P : SharedProgram n k)
    (Y : Finset (Fin n)) :
    P.activeLeavesIn Y = P.inputLeavesIn Y + P.activeSharedLeaves Y := by
  rw [activeLeavesIn_eq_inputLeavesIn_add_sum_occ P le_rfl Y Y (fun _ _ => Iff.rfl)]
  have hsum : (∑ i ∈ Y, if n ≤ i.val then P.occ i.val else 0) = 0 := by
    refine Finset.sum_eq_zero fun i _ => ?_
    have : ¬ n ≤ i.val := by omega
    simp [this]
  omega

/-- Project a coordinate in `castBlock Y` to `Y`. -/
def castBlockVal {N : Nat} {Y : Finset (Fin N)} (y : ↥Y → Bool) (j : ↥(castBlock Y)) : Bool :=
  y ⟨⟨j.1.val, by
    by_contra h
    have hjlt := j.1.isLt
    have hlast : j.1 = Fin.last N := Fin.ext (by simp [Fin.last]; omega)
    exact last_notMem_castBlock Y (hlast ▸ j.2)⟩,
   by
    have hlt : j.1.val < N := by
      by_contra h
      have hjlt := j.1.isLt
      have hlast : j.1 = Fin.last N := Fin.ext (by simp [Fin.last]; omega)
      exact last_notMem_castBlock Y (hlast ▸ j.2)
    have hcast : (⟨j.1.val, hlt⟩ : Fin N).castSucc = j.1 := Fin.ext rfl
    exact (castSucc_mem_castBlock Y _).mp (hcast.symm ▸ j.2)⟩

/-- Extend an outside assignment `z : ↥Yᶜ → Bool` by `b` on `Fin.last N`. -/
def snocComplVal {N : Nat} {Y : Finset (Fin N)} (z : ↥Yᶜ → Bool) (b : Bool)
    (j : ↥(castBlock Y)ᶜ) : Bool :=
  if h : j.1.val < N then
    z ⟨⟨j.1.val, h⟩, by
      rw [Finset.mem_compl]
      intro hi
      have hcast : (⟨j.1.val, h⟩ : Fin N).castSucc = j.1 := Fin.ext rfl
      exact (Finset.mem_compl.mp j.2) (hcast ▸ (castSucc_mem_castBlock Y _).mpr hi)⟩
  else b

/-- Appending a value outside the block: gluing over `Y` and appending `b` equals gluing over
`castBlock Y` with `b` among the outside coordinates. -/
theorem glue_castBlock {N : Nat} (Y : Finset (Fin N)) (y : ↥Y → Bool) (z : ↥Yᶜ → Bool)
    (b : Bool) :
    Fin.snoc (glue Y y z) b = glue (castBlock Y) (castBlockVal y) (snocComplVal z b) := by
  funext j
  refine Fin.lastCases ?_ (fun i => ?_) j
  · have hmem : Fin.last N ∉ castBlock Y := last_notMem_castBlock Y
    simp [glue, hmem, snocComplVal]
  · by_cases hi : i ∈ Y
    · have hmem : i.castSucc ∈ castBlock Y := (castSucc_mem_castBlock Y i).mpr hi
      simp [glue, hi, hmem, castBlockVal]
    · have hmem : i.castSucc ∉ castBlock Y := by
        simpa [castSucc_mem_castBlock] using hi
      simp [glue, hi, hmem, snocComplVal, i.isLt]

/-- Project a coordinate outside `snocBlock Y` to `Yᶜ`. -/
def uncastCompl {N : Nat} {Y : Finset (Fin N)} (j : ↥(snocBlock Y)ᶜ) : ↥Yᶜ :=
  ⟨⟨j.1.val, by
    by_contra h
    have hjlt := j.1.isLt
    have hlast : j.1 = Fin.last N := Fin.ext (by simp [Fin.last]; omega)
    exact (Finset.mem_compl.mp j.2) (hlast ▸ last_mem_snocBlock Y)⟩,
   by
    rw [Finset.mem_compl]
    intro hi
    have hlt : j.1.val < N := by
      by_contra h
      have hjlt := j.1.isLt
      have hlast : j.1 = Fin.last N := Fin.ext (by simp [Fin.last]; omega)
      exact (Finset.mem_compl.mp j.2) (hlast ▸ last_mem_snocBlock Y)
    have hcast : (⟨j.1.val, hlt⟩ : Fin N).castSucc = j.1 := Fin.ext rfl
    exact (Finset.mem_compl.mp j.2) (hcast ▸ (castSucc_mem_snocBlock Y _).mpr hi)⟩

/-- Extend a block assignment `y : ↥Y → Bool` by the value `b` on `Fin.last N`. -/
def snocBlockVal {N : Nat} {Y : Finset (Fin N)} (y : ↥Y → Bool) (b : Bool)
    (j : ↥(snocBlock Y)) : Bool :=
  if h : j.1.val < N then
    y ⟨⟨j.1.val, h⟩, by
      have hcast : (⟨j.1.val, h⟩ : Fin N).castSucc = j.1 := Fin.ext rfl
      exact (castSucc_mem_snocBlock Y _).mp (hcast.symm ▸ j.2)⟩
  else b

/-- Appending a value inside the block: gluing over `Y` and appending `b` equals gluing over
`snocBlock Y` with `b` among the block coordinates. -/
theorem glue_snocBlock {N : Nat} (Y : Finset (Fin N)) (y : ↥Y → Bool) (z : ↥Yᶜ → Bool)
    (b : Bool) :
    Fin.snoc (glue Y y z) b = glue (snocBlock Y) (snocBlockVal y b) (z ∘ uncastCompl) := by
  funext j
  refine Fin.lastCases ?_ (fun i => ?_) j
  · have hmem : Fin.last N ∈ snocBlock Y := last_mem_snocBlock Y
    simp [glue, hmem, snocBlockVal]
  · by_cases hi : i ∈ Y
    · have hmem : i.castSucc ∈ snocBlock Y := (castSucc_mem_snocBlock Y i).mpr hi
      simp [glue, hi, hmem, snocBlockVal, i.isLt]
    · have hmem : i.castSucc ∉ snocBlock Y := by
        simpa [castSucc_mem_snocBlock] using hi
      simp [glue, hi, hmem, uncastCompl]

/-- If the shared formula `G` has no leaves in `Y`, then `share G P` has at most as many
subfunctions on `Y` as `P` has on `castBlock Y`: the shared value is constant once the outside
coordinates are fixed. -/
theorem card_subfunctions_share_le_of_leavesIn_eq_zero (G : Formula N)
    (P : SharedProgram (N + 1) k) (Y : Finset (Fin N)) (hG : G.leavesIn Y = 0) :
    (subfunctions (share G P).eval Y).card ≤ (subfunctions P.eval (castBlock Y)).card := by
  let restrict : ((↥(castBlock Y) → Bool) → Bool) → ((↥Y → Bool) → Bool) :=
    fun q y => q (castBlockVal y)
  have hsub : subfunctions (share G P).eval Y ⊆
      (subfunctions P.eval (castBlock Y)).image restrict := by
    intro f hf
    obtain ⟨z, rfl⟩ := mem_subfunctions.mp hf
    let b₀ := G.eval (glue Y (fun _ => false) z)
    refine Finset.mem_image.mpr
      ⟨fun y' => P.eval (glue (castBlock Y) y' (snocComplVal z b₀)),
        restrict_mem_subfunctions P.eval (castBlock Y) (snocComplVal z b₀), ?_⟩
    funext y
    have hconst : G.eval (glue Y y z) = b₀ :=
      Formula.eval_eq_of_leavesIn_eq_zero (fun i hi => by simp [glue, hi]) G hG
    simp [restrict, eval_share, hconst, glue_castBlock]
  exact (Finset.card_le_card hsub).trans Finset.card_image_le

/-- The subfunctions of `share G P` on `Y` number at most the product of the subfunction counts of
`G` on `Y` and of `P` on `snocBlock Y`. -/
theorem card_subfunctions_share_le_mul (G : Formula N) (P : SharedProgram (N + 1) k)
    (Y : Finset (Fin N)) :
    (subfunctions (share G P).eval Y).card ≤
      (subfunctions G.eval Y).card * (subfunctions P.eval (snocBlock Y)).card := by
  let combine : ((↥Y → Bool) → Bool) × ((↥(snocBlock Y) → Bool) → Bool) →
      ((↥Y → Bool) → Bool) :=
    fun fq y => fq.2 (snocBlockVal y (fq.1 y))
  have hsub : subfunctions (share G P).eval Y ⊆
      (subfunctions G.eval Y ×ˢ subfunctions P.eval (snocBlock Y)).image combine := by
    intro f hf
    obtain ⟨z, rfl⟩ := mem_subfunctions.mp hf
    refine Finset.mem_image.mpr ⟨(fun y => G.eval (glue Y y z),
      fun y' => P.eval (glue (snocBlock Y) y' (z ∘ uncastCompl))),
      Finset.mem_product.mpr ⟨restrict_mem_subfunctions G.eval Y z,
        restrict_mem_subfunctions P.eval (snocBlock Y) (z ∘ uncastCompl)⟩, ?_⟩
    funext y
    simp [combine, eval_share, glue_snocBlock]
  calc (subfunctions (share G P).eval Y).card
      ≤ ((subfunctions G.eval Y ×ˢ subfunctions P.eval (snocBlock Y)).image combine).card :=
        Finset.card_le_card hsub
    _ ≤ (subfunctions G.eval Y ×ˢ subfunctions P.eval (snocBlock Y)).card :=
        Finset.card_image_le
    _ = (subfunctions G.eval Y).card * (subfunctions P.eval (snocBlock Y)).card :=
        Finset.card_product _ _

/-! ### Substitution of a variable in a `SharedProgram` -/

/-- Substitute the formula `φ` for variable `N` throughout a program on `N + 1 + d` variables. -/
def substVar (φ : Formula N) :
    {d k : Nat} → SharedProgram (N + 1 + d) k → SharedProgram (N + d) k
  | d, _, output F => output (F.subst (Formula.substVarMap φ d))
  | d, _, share G P => share (G.subst (Formula.substVarMap φ d)) (substVar φ (d := d + 1) P)

/-- Evaluating `substVar φ P` evaluates `P` with `φ`'s value inserted at variable `N`. -/
theorem eval_substVar (φ : Formula N) :
    ∀ {d k : Nat} (P : SharedProgram (N + 1 + d) k) (y : Fin (N + d) → Bool),
      (substVar φ P).eval y =
        P.eval (KW.insertVal y (φ.eval fun j => y (Fin.castLE (by omega) j)))
  | d, _, output F, y => by
    rw [substVar, eval_output, Formula.eval_subst_substVarMap, eval_output]
  | d, _, share G P, y => by
    rw [substVar, eval_share, eval_share, eval_substVar φ (d := d + 1) P,
      Formula.eval_subst_substVarMap]
    congr 1
    have hφ : (φ.eval fun j => Fin.snoc (α := fun _ => Bool) y
        (G.eval (KW.insertVal y (φ.eval fun j => y (Fin.castLE (by omega) j))))
          (Fin.castLE (by omega) j)) = φ.eval fun j => y (Fin.castLE (by omega) j) := by
      congr 1
      funext j
      have hj : (Fin.castLE (by omega) j : Fin (N + d + 1)) =
          (Fin.castLE (by omega) j : Fin (N + d)).castSucc := Fin.ext rfl
      rw [hj, Fin.snoc_castSucc]
    rw [hφ, KW.insertVal_snoc]

/-- Substituting `φ` adds `φ.gates` once per occurrence of variable `N`. -/
theorem gates_substVar (φ : Formula N) :
    ∀ {d k : Nat} (P : SharedProgram (N + 1 + d) k),
      (substVar φ P).gates = P.gates + P.occ N * φ.gates
  | d, _, output F => by
    rw [substVar]
    simp only [gates, occ, Formula.gates_subst_substVarMap]
  | d, _, share G P => by
    rw [substVar]
    simp only [gates, occ, Formula.gates_subst_substVarMap, gates_substVar φ (d := d + 1) P]
    ring

/-- Substituting `φ` adds the occurrences of `w < N` in `φ` once per occurrence of variable `N`. -/
theorem occ_substVar (φ : Formula N) {w : Nat} (hw : w < N) :
    ∀ {d k : Nat} (P : SharedProgram (N + 1 + d) k),
      (substVar φ P).occ w = P.occ w + P.occ N * φ.occ w
  | d, _, output F => by
    rw [substVar]
    simp only [occ, Formula.occ_subst_substVarMap φ d hw]
  | d, _, share G P => by
    rw [substVar]
    simp only [occ, Formula.occ_subst_substVarMap φ d hw, occ_substVar φ hw (d := d + 1) P]
    ring

/-- Substituting for variable `N` shifts the occurrences of variables above `N` down by one. -/
theorem occ_substVar_ge (φ : Formula N) {w : Nat} (hw : N ≤ w) :
    ∀ {d k : Nat} (P : SharedProgram (N + 1 + d) k),
      (substVar φ P).occ w = P.occ (w + 1)
  | d, _, output F => Formula.occ_subst_substVarMap_ge φ d hw F
  | d, _, share G P => by
    rw [substVar]
    simp only [occ, Formula.occ_subst_substVarMap_ge φ d hw, occ_substVar_ge φ hw (d := d + 1) P]

/-- Substituting for variable `N` shifts the shared leaves down by one. -/
theorem sharedLeaves_substVar (φ : Formula N) :
    ∀ {d k : Nat} (P : SharedProgram (N + 1 + d) k),
      (substVar φ P).sharedLeaves N = P.sharedLeaves (N + 1)
  | d, _, output F => by
    rw [substVar]
    simp only [sharedLeaves, Formula.sharedLeaves_subst_substVarMap φ d]
  | d, _, share G P => by
    rw [substVar]
    simp only [sharedLeaves, Formula.sharedLeaves_subst_substVarMap φ d,
      sharedLeaves_substVar φ (d := d + 1) P]

/-- Lifting a block commutes with advancing it through corresponding shared formulas. -/
private theorem liftBlock_stepBlock {d : Nat} (b : Bool) (W : Finset (Fin (N + d)))
    (G' : Formula (N + d)) (G : Formula (N + 1 + d))
    (hG : G'.leavesIn W = 0 ↔ G.leavesIn (Formula.liftBlock b W) = 0) :
    Formula.liftBlock (d := d + 1) b (stepBlock G' W) =
      stepBlock G (Formula.liftBlock (d := d) b W) := by
  ext j
  refine Fin.lastCases ?_ (fun i => ?_) j
  · change Fin.last (N + 1 + d) ∈ Formula.liftBlock (d := d + 1) b (stepBlock G' W) ↔
      Fin.last (N + 1 + d) ∈ stepBlock G (Formula.liftBlock (d := d) b W)
    rw [last_mem_stepBlock, ne_eq, ← not_iff_not.mpr hG, ← ne_eq, ← last_mem_stepBlock G' W]
    have h1 : ¬ (N + 1 + d < N) := by omega
    have h2 : ¬ (N + 1 + d = N) := by omega
    have h3 : (⟨N + 1 + d - 1, by omega⟩ : Fin (N + d + 1)) = Fin.last (N + d) :=
      Fin.ext (by simp)
    simp only [Formula.liftBlock, Finset.mem_filter, Finset.mem_univ, true_and, Fin.val_last,
      h1, h2, ↓reduceDIte]
    exact iff_of_eq (congrArg (· ∈ stepBlock G' W) h3)
  · have hi : i.val < N + 1 + d := i.isLt
    simp only [castSucc_mem_stepBlock, Formula.liftBlock, Finset.mem_filter, Finset.mem_univ,
      true_and, Fin.val_castSucc]
    split_ifs with h1 h2
    · have hc : (⟨i.val, by omega⟩ : Fin (N + d + 1)) =
          (⟨i.val, by omega⟩ : Fin (N + d)).castSucc :=
        Fin.ext rfl
      rw [hc, castSucc_mem_stepBlock]
    · rfl
    · have hc : (⟨i.val - 1, by omega⟩ : Fin (N + d + 1)) =
          (⟨i.val - 1, by omega⟩ : Fin (N + d)).castSucc := Fin.ext rfl
      rw [hc, castSucc_mem_stepBlock]

/-- Advancing a block does not change its trace on the first `N` variables. -/
private theorem filter_castLE_stepBlock {d : Nat} (G' : Formula (N + d))
    (W : Finset (Fin (N + d))) :
    (Finset.univ.filter fun j : Fin N => Fin.castLE (by omega) j ∈ stepBlock G' W) =
      Finset.univ.filter fun j : Fin N => Fin.castLE (by omega) j ∈ W := by
  ext j
  have hc : (Fin.castLE (by omega) j : Fin (N + d + 1)) =
      (Fin.castLE (by omega) j : Fin (N + d)).castSucc := Fin.ext rfl
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  rw [hc, castSucc_mem_stepBlock]

/-- With no variables above `N`, lifting by whether `φ` is active is advancing through `φ`. -/
private theorem liftBlock_zero (φ : Formula N) (Z : Finset (Fin N)) :
    Formula.liftBlock (d := 0) (decide (φ.leavesIn Z ≠ 0)) Z = stepBlock φ Z := by
  ext j
  refine Fin.lastCases ?_ (fun i => ?_) j
  · simp [Formula.liftBlock, last_mem_stepBlock]
  · simp [Formula.liftBlock, i.isLt, castSucc_mem_stepBlock]

/-- Substitution preserves active shared gates, measured on the lifted block. -/
theorem activeShared_substVar_aux (φ : Formula N) :
    ∀ {d k : Nat} (P : SharedProgram (N + 1 + d) k) (W : Finset (Fin (N + d))),
      (substVar φ P).activeShared W =
        P.activeShared (Formula.liftBlock
          (decide (φ.leavesIn (Finset.univ.filter fun j => Fin.castLE (by omega) j ∈ W) ≠ 0)) W)
  | _, 0, output _, _ => rfl
  | d, _ + 1, share G P, W => by
    set b := decide (φ.leavesIn (Finset.univ.filter fun j => Fin.castLE (by omega) j ∈ W) ≠ 0)
    have hiff := Formula.leavesIn_subst_substVarMap_eq_zero_iff φ d W G
    have hstep := liftBlock_stepBlock b W (G.subst (Formula.substVarMap φ d)) G hiff
    have hfilt := filter_castLE_stepBlock (G.subst (Formula.substVarMap φ d)) W
    rw [substVar, activeShared, activeShared, activeShared_substVar_aux φ (d := d + 1) P]
    simp only [b, hiff, hfilt, hstep]

/-- Substituting `φ` for the first shared variable preserves active shared gates once the block
is advanced through `φ`. -/
theorem activeShared_substVar (φ : Formula N) (P : SharedProgram (N + 1) k) (Z : Finset (Fin N)) :
    (substVar φ (d := 0) P).activeShared Z = P.activeShared (stepBlock φ Z) := by
  rw [activeShared_substVar_aux φ (d := 0) P Z]
  have hZ : (Finset.univ.filter fun j : Fin N => Fin.castLE (by omega) j ∈ Z) = Z := by
    ext j; simp
  rw [hZ, liftBlock_zero]

/-- Substitution preserves active shared-variable leaves, measured on the lifted block. -/
theorem activeSharedLeaves_substVar_aux (φ : Formula N) :
    ∀ {d k : Nat} (P : SharedProgram (N + 1 + d) k) (W : Finset (Fin (N + d))),
      (substVar φ P).activeSharedLeaves W =
        P.activeSharedLeaves (Formula.liftBlock
          (decide (φ.leavesIn (Finset.univ.filter fun j => Fin.castLE (by omega) j ∈ W) ≠ 0)) W)
  | _, 0, output _, _ => rfl
  | d, _ + 1, share G P, W => by
    set b := decide (φ.leavesIn (Finset.univ.filter fun j => Fin.castLE (by omega) j ∈ W) ≠ 0)
    have hiff := Formula.leavesIn_subst_substVarMap_eq_zero_iff φ d W G
    have hstep := liftBlock_stepBlock b W (G.subst (Formula.substVarMap φ d)) G hiff
    have hfilt := filter_castLE_stepBlock (G.subst (Formula.substVarMap φ d)) W
    have hocc : (substVar φ (d := d + 1) P).occ (N + d) = P.occ (N + 1 + d) := by
      have h := occ_substVar_ge φ (w := N + d) (by omega) (d := d + 1) P
      rwa [show N + d + 1 = N + 1 + d by omega] at h
    rw [substVar, activeSharedLeaves, activeSharedLeaves,
      activeSharedLeaves_substVar_aux φ (d := d + 1) P, hocc]
    simp only [b, hiff, hfilt, hstep]

/-- Substituting `φ` for the first shared variable preserves active shared-variable leaves once the
block is advanced through `φ`. -/
theorem activeSharedLeaves_substVar (φ : Formula N) (P : SharedProgram (N + 1) k)
    (Z : Finset (Fin N)) :
    (substVar φ (d := 0) P).activeSharedLeaves Z = P.activeSharedLeaves (stepBlock φ Z) := by
  rw [activeSharedLeaves_substVar_aux φ (d := 0) P Z]
  have hZ : (Finset.univ.filter fun j : Fin N => Fin.castLE (by omega) j ∈ Z) = Z := by
    ext j; simp
  rw [hZ, liftBlock_zero]

end SharedProgram

/-! ### Shared fan-out and translation from binary circuits to `SharedProgram` -/

section BinaryCircuits

variable {σ : Signature} {n m t : Nat}

/-- The total fan-out of the gates of `p` whose fan-out is at least two when gate `g` is read
`u g` more times. -/
def sharedFanOutCount (p : Program σ n t) (u : Fin t → Nat) : Nat :=
  ∑ g ∈ Finset.univ.filter (fun g => 2 ≤ KW.slotUses p g + u g), (KW.slotUses p g + u g)

/-- `sharedFanOut c` is `sharedFanOutCount` of its program with the output reads as extra uses. -/
theorem sharedFanOut_eq (c : Circuit σ n m) :
    sharedFanOut c = sharedFanOutCount c.program
      fun g => (Finset.univ.filter fun o => c.outputs o = Wire.gate g).card := rfl

/-- Peeling the last gate off a program: its shared fan-out is counted separately, and its reads
move into the extra uses of the earlier gates. -/
theorem sharedFanOutCount_gate (p : Program σ n t) (line : Line σ n t)
    (u : Fin (t + 1) → Nat) :
    sharedFanOutCount (p.gate line) u =
      (if 2 ≤ u (Fin.last t) then u (Fin.last t) else 0) +
        sharedFanOutCount p fun g => u g.castSucc + KW.argUses line g := by
  rw [sharedFanOutCount, sharedFanOutCount, Finset.sum_filter, Finset.sum_filter,
    Fin.sum_univ_castSucc, add_comm]
  simp only [KW.slotUses_gate_last, KW.slotUses_gate_castSucc, zero_add]
  congr 1
  refine Finset.sum_congr rfl fun g _ => ?_
  split_ifs <;> omega

/-- The last gate is active iff one of its argument wires is active. -/
theorem gateActive_gate_last (Y : Finset (Fin n)) (p : Program σ n t)
    (line : Line σ n t) :
    gateActive Y (p.gate line) (Fin.last t) =
      decide (∃ a, wireActive Y p (line.wires a) = true) := by
  simp only [gateActive, Fin.lastCases_last, decide_eq_decide]
  exact exists_congr fun a => by cases line.wires a <;> rfl

/-- Appending a gate does not change whether an earlier gate is active. -/
@[simp] theorem gateActive_gate_castSucc (Y : Finset (Fin n)) (p : Program σ n t)
    (line : Line σ n t) (g : Fin t) :
    gateActive Y (p.gate line) g.castSucc = gateActive Y p g := by
  simp [gateActive]

/-- The number of gates of `p` active on `Y` whose fan-out is at least two when gate `g` is read
`u g` more times. -/
def activeSharedCount (Y : Finset (Fin n)) (p : Program σ n t) (u : Fin t → Nat) : Nat :=
  (Finset.univ.filter fun g => 2 ≤ KW.slotUses p g + u g ∧ gateActive Y p g = true).card

/-- The total fan-out of the gates of `p` active on `Y` whose fan-out is at least two when gate `g`
is read `u g` more times. -/
def activeSharedFanOutCount (Y : Finset (Fin n)) (p : Program σ n t) (u : Fin t → Nat) : Nat :=
  ∑ g ∈ Finset.univ.filter (fun g => 2 ≤ KW.slotUses p g + u g ∧ gateActive Y p g = true),
    (KW.slotUses p g + u g)

/-- `activeSharedGateCount c Y` is `activeSharedCount` of its program with the output reads as
extra uses. -/
theorem activeSharedGateCount_eq (c : Circuit σ n m) (Y : Finset (Fin n)) :
    activeSharedGateCount c Y = activeSharedCount Y c.program
      fun g => (Finset.univ.filter fun o => c.outputs o = Wire.gate g).card := rfl

/-- `activeSharedFanOut c Y` is `activeSharedFanOutCount` of its program with the output reads as
extra uses. -/
theorem activeSharedFanOut_eq (c : Circuit σ n m) (Y : Finset (Fin n)) :
    activeSharedFanOut c Y = activeSharedFanOutCount Y c.program
      fun g => (Finset.univ.filter fun o => c.outputs o = Wire.gate g).card := rfl

/-- Peeling the last gate off a program for `activeSharedCount`. -/
theorem activeSharedCount_gate (Y : Finset (Fin n)) (p : Program σ n t) (line : Line σ n t)
    (u : Fin (t + 1) → Nat) :
    activeSharedCount Y (p.gate line) u =
      (if 2 ≤ u (Fin.last t) ∧ gateActive Y (p.gate line) (Fin.last t) = true then 1 else 0) +
        activeSharedCount Y p fun g => u g.castSucc + KW.argUses line g := by
  rw [activeSharedCount, activeSharedCount, Finset.card_filter, Finset.card_filter,
    Fin.sum_univ_castSucc, add_comm]
  simp only [KW.slotUses_gate_last, KW.slotUses_gate_castSucc, gateActive_gate_castSucc, zero_add]
  congr 1
  refine Finset.sum_congr rfl fun g _ => ?_
  by_cases h : gateActive Y p g = true
  · simp only [h, and_true]
    split_ifs <;> omega
  · simp [h]

/-- Peeling the last gate off a program for `activeSharedFanOutCount`. -/
theorem activeSharedFanOutCount_gate (Y : Finset (Fin n)) (p : Program σ n t) (line : Line σ n t)
    (u : Fin (t + 1) → Nat) :
    activeSharedFanOutCount Y (p.gate line) u =
      (if 2 ≤ u (Fin.last t) ∧ gateActive Y (p.gate line) (Fin.last t) = true then
        u (Fin.last t) else 0) +
        activeSharedFanOutCount Y p fun g => u g.castSucc + KW.argUses line g := by
  rw [activeSharedFanOutCount, activeSharedFanOutCount, Finset.sum_filter, Finset.sum_filter,
    Fin.sum_univ_castSucc, add_comm]
  simp only [KW.slotUses_gate_last, KW.slotUses_gate_castSucc, gateActive_gate_castSucc, zero_add]
  congr 1
  refine Finset.sum_congr rfl fun g _ => ?_
  by_cases h : gateActive Y p g = true
  · simp only [h, and_true]
    split_ifs <;> omega
  · simp [h]

/-- The subset of `Fin (n + t)` consisting of wires of `p` active on `Y`. -/
def activeWires (Y : Finset (Fin n)) (p : Program σ n t) : Finset (Fin (n + t)) :=
  Finset.univ.filter fun i : Fin (n + t) =>
    if h : i.val < n then ⟨i.val, h⟩ ∈ Y
    else gateActive Y p ⟨i.val - n, by omega⟩ = true

/-- The active wires of the empty program are the block itself. -/
@[simp] theorem activeWires_empty (Y : Finset (Fin n)) :
    activeWires Y (.empty : Program σ n 0) = Y := by
  ext i
  simp [activeWires]

/-- A wire's index is an active wire iff the wire is active. -/
@[simp] theorem index_mem_activeWires (Y : Finset (Fin n)) (p : Program σ n t) (w : Wire n t) :
    w.index ∈ activeWires Y p ↔ wireActive Y p w = true := by
  cases w with
  | input i => simp [activeWires, wireActive, i.isLt]
  | gate g =>
    have hnot : ¬ (n + g.val < n) := by omega
    simp [activeWires, wireActive, hnot]

/-- The formula of one full-binary-basis gate over the earlier wires, numbered by `Wire.index`. -/
def lineFormula (line : Line Binary.signature n t) : Formula (n + t) :=
  .gate line.op (.var (line.wires 0).index) (.var (line.wires 1).index)

/-- The formula of the last gate has no leaves among the active wires iff the gate is inactive. -/
theorem leavesIn_lineFormula_activeWires_eq_zero_iff (Y : Finset (Fin n))
    (p : Program Binary.signature n t) (line : Line Binary.signature n t) :
    (lineFormula line).leavesIn (activeWires Y p) = 0 ↔
      gateActive Y (p.gate line) (Fin.last t) = false := by
  obtain ⟨op, w⟩ := line
  rw [gateActive_gate_last, decide_eq_false_iff_not, Fin.exists_fin_two]
  simp only [lineFormula, Formula.leavesIn, index_mem_activeWires, not_or, Bool.not_eq_true]
  split_ifs <;> simp_all

/-- Advancing the active wires through the formula of a new gate gives the active wires of the
extended program. -/
theorem stepBlock_lineFormula_activeWires (Y : Finset (Fin n))
    (p : Program Binary.signature n t) (line : Line Binary.signature n t) :
    SharedProgram.stepBlock (lineFormula line) (activeWires Y p) =
      activeWires Y (p.gate line) := by
  ext j
  refine Fin.lastCases ?_ (fun i => ?_) j
  · have hnot : ¬ (n + t < n) := by omega
    have hsub : (⟨n + t - n, by omega⟩ : Fin (t + 1)) = Fin.last t := Fin.ext (by simp)
    rw [SharedProgram.last_mem_stepBlock, ne_eq, leavesIn_lineFormula_activeWires_eq_zero_iff,
      Bool.not_eq_false]
    simp only [activeWires, Finset.mem_filter, Finset.mem_univ, true_and, Fin.val_last, hnot,
      ↓reduceDIte, hsub]
  · rw [SharedProgram.castSucc_mem_stepBlock]
    simp only [activeWires, Finset.mem_filter, Finset.mem_univ, true_and, Fin.val_castSucc]
    split_ifs with h
    · rfl
    · have hc : (⟨i.val - n, by omega⟩ : Fin (t + 1)) =
          (⟨i.val - n, by omega⟩ : Fin t).castSucc := Fin.ext rfl
      rw [hc, gateActive_gate_castSucc]

/-- The values of the inputs and gates of a binary program, numbered by `Wire.index`. -/
def wireValues (p : Program Binary.signature n t) (x : Fin n → Bool) : Fin (n + t) → Bool :=
  Fin.append x (p.eval Binary.interpretation x)

/-- The formula of a gate evaluates as the gate. -/
theorem eval_lineFormula (line : Line Binary.signature n t) (x : Fin n → Bool)
    (vals : Fin t → Bool) :
    (lineFormula line).eval (Fin.append x vals) = line.eval Binary.interpretation x vals := by
  simp [lineFormula, Line.eval, Binary.interpretation, KW.append_index]

/-- The formula of a gate has exactly one binary gate. -/
theorem gates_lineFormula (line : Line Binary.signature n t) :
    (lineFormula line).gates = 1 := rfl

/-- The formula of a gate reads no variables beyond the existing wires. -/
theorem sharedLeaves_lineFormula (line : Line Binary.signature n t) :
    (lineFormula line).sharedLeaves (n + t) = 0 :=
  Formula.sharedLeaves_eq_zero_of_le le_rfl _

/-- The formula of a gate reads gate `g` at most as often as the gate's arguments do. -/
theorem occ_lineFormula_le (line : Line Binary.signature n t) (g : Fin t) :
    (lineFormula line).occ (n + g.val) ≤ KW.argUses line g := by
  obtain ⟨op, w⟩ := line
  rw [KW.argUses, Finset.card_filter]
  have hne : (0 : Fin 2) ≠ 1 := by decide
  have huniv : (Finset.univ : Finset (Fin 2)) = {0, 1} := by decide
  rw [huniv, Finset.sum_pair hne]
  simp only [lineFormula, Formula.occ, KW.index_val_eq_iff]
  split_ifs <;> simp_all

/-- Evaluating a program with an appended gate appends the gate's value. -/
theorem eval_gate (p : Program Binary.signature n t) (line : Line Binary.signature n t)
    (x : Fin n → Bool) :
    (p.gate line).eval Binary.interpretation x =
      Fin.snoc (p.eval Binary.interpretation x)
        (line.eval Binary.interpretation x (p.eval Binary.interpretation x)) := by
  funext g
  refine Fin.lastCases ?_ (fun g => ?_) g
  · rw [Program.eval_gate_last, Fin.snoc_last]
  · rw [Program.eval_gate_castSucc, Fin.snoc_castSucc]

/-- The wire values of an extended program append the value of the new gate's formula. -/
theorem wireValues_gate (p : Program Binary.signature n t) (line : Line Binary.signature n t)
    (x : Fin n → Bool) :
    wireValues (p.gate line) x =
      Fin.snoc (wireValues p x) ((lineFormula line).eval (wireValues p x)) := by
  rw [wireValues, eval_gate, Fin.append_snoc, wireValues, eval_lineFormula]

/-- The wire values of the empty program are the inputs. -/
theorem wireValues_empty (x : Fin n → Bool) :
    wireValues (.empty : Program Binary.signature n 0) x = x := by
  funext i
  change Fin.append x Fin.elim0 i = x i
  rw [Fin.append_elim0]
  rfl

/-- Build a `SharedProgram` from the last gate of a full-binary-basis program down, simultaneously
bounding both global and block-active shared gates and shared-variable leaves. -/
theorem exists_sharedProgram_of_program {n : Nat} (f : Cslib.BooleanFunction n) :
    ∀ {t : Nat} (p : Program Binary.signature n t) (u : Fin t → Nat) {j : Nat}
      (Q : SharedProgram (n + t) j),
      (∀ x, Q.eval (wireValues p x) = f x) → (∀ g : Fin t, Q.occ (n + g.val) ≤ u g) →
      ∃ k, ∃ P : SharedProgram n k,
        k ≤ j + KW.sharedCount p u ∧ P.Computes f ∧
          P.gates ≤ Q.gates + t ∧
          P.sharedLeaves n ≤ Q.sharedLeaves (n + t) + sharedFanOutCount p u ∧
          ∀ Y : Finset (Fin n),
            P.activeShared Y ≤ Q.activeShared (activeWires Y p) + activeSharedCount Y p u ∧
              P.activeSharedLeaves Y ≤
                Q.activeSharedLeaves (activeWires Y p) + activeSharedFanOutCount Y p u
  | _, .empty, u, j, Q, hQ, _ =>
    ⟨j, Q, by simp, fun x => by simpa [wireValues_empty] using hQ x, by simp,
      by simp [sharedFanOutCount],
      fun Y => by simp [activeSharedCount, activeSharedFanOutCount]⟩
  | _, .gate (gateCount := t) p line, u, j, Q, hQ, hocc => by
    have hφocc := occ_lineFormula_le line
    have hφgates := gates_lineFormula line
    have hφshared := sharedLeaves_lineFormula line
    have hcount := KW.sharedCount_gate p line u
    have hfanout := sharedFanOutCount_gate p line u
    have hlast : Q.occ (n + t) ≤ u (Fin.last t) := hocc (Fin.last t)
    by_cases hL : 2 ≤ u (Fin.last t)
    · obtain ⟨k, P, hk, hP, hgates, hshared, hact⟩ := exists_sharedProgram_of_program f p
        (fun g => u g.castSucc + KW.argUses line g) (SharedProgram.share (lineFormula line) Q)
        (fun x => by
          rw [SharedProgram.eval_share, ← wireValues_gate]
          exact hQ x)
        (fun g => by
          have h₁ : Q.occ (n + g.val) ≤ u g.castSucc := hocc g.castSucc
          have h₂ := hφocc g
          rw [SharedProgram.occ_share]
          omega)
      refine ⟨k, P, ?_, hP, ?_, ?_, fun Y => ?_⟩
      · rw [hcount, ite_eq_left hL]
        omega
      · rw [SharedProgram.gates_share, hφgates] at hgates
        omega
      · have hQshared := Q.sharedLeaves_eq_occ_add_sharedLeaves_succ (n + t)
        simp only [SharedProgram.sharedLeaves, hφshared, zero_add] at hshared
        change P.sharedLeaves n ≤ Q.sharedLeaves (n + t + 1) + sharedFanOutCount (p.gate line) u
        rw [hfanout, ite_eq_left hL]
        omega
      · obtain ⟨hact1, hact2⟩ := hact Y
        have hstep := stepBlock_lineFormula_activeWires Y p line
        have hzero := leavesIn_lineFormula_activeWires_eq_zero_iff Y p line
        simp only [SharedProgram.activeShared, SharedProgram.activeSharedLeaves, hstep,
          hzero] at hact1 hact2
        rw [activeSharedCount_gate, activeSharedFanOutCount_gate]
        rcases hgate : gateActive Y (p.gate line) (Fin.last t) with _ | _
        · have hne : ¬ (2 ≤ u (Fin.last t) ∧ false = true) := fun h => Bool.false_ne_true h.2
          rw [hgate, ite_eq_left rfl] at hact1 hact2
          rw [ite_eq_right hne, ite_eq_right hne]
          exact ⟨by omega, by omega⟩
        · have hpos : 2 ≤ u (Fin.last t) ∧ true = true := ⟨hL, rfl⟩
          have hne : ¬ (true = false) := by decide
          rw [hgate, ite_eq_right hne] at hact1 hact2
          rw [ite_eq_left hpos, ite_eq_left hpos]
          exact ⟨by omega, by omega⟩
    · have hL₁ : Q.occ (n + t) ≤ 1 := by omega
      obtain ⟨k, P, hk, hP, hgates, hshared, hact⟩ := exists_sharedProgram_of_program f p
        (fun g => u g.castSucc + KW.argUses line g)
        (SharedProgram.substVar (lineFormula line) (d := 0) Q)
        (fun x => by
          rw [SharedProgram.eval_substVar, KW.insertVal_zero]
          change Q.eval (Fin.snoc (wireValues p x) ((lineFormula line).eval (wireValues p x))) = _
          rw [← wireValues_gate]
          exact hQ x)
        (fun g => by
          rw [SharedProgram.occ_substVar _ (by omega)]
          have h₁ : Q.occ (n + g.val) ≤ u g.castSucc := hocc g.castSucc
          have h₂ := hφocc g
          have h₃ : Q.occ (n + t) * (lineFormula line).occ (n + g.val) ≤ KW.argUses line g :=
            le_trans ((Nat.mul_le_mul_right _ hL₁).trans_eq (one_mul _)) h₂
          omega)
      refine ⟨k, P, ?_, hP, ?_, ?_, fun Y => ?_⟩
      · rw [hcount, ite_eq_right hL]
        omega
      · rw [SharedProgram.gates_substVar, hφgates] at hgates
        omega
      · rw [SharedProgram.sharedLeaves_substVar] at hshared
        change P.sharedLeaves n ≤ Q.sharedLeaves (n + t + 1) + sharedFanOutCount (p.gate line) u
        rw [hfanout, ite_eq_right hL]
        omega
      · obtain ⟨hact1, hact2⟩ := hact Y
        rw [SharedProgram.activeShared_substVar, stepBlock_lineFormula_activeWires] at hact1
        rw [SharedProgram.activeSharedLeaves_substVar, stepBlock_lineFormula_activeWires] at hact2
        have hne : ¬ (2 ≤ u (Fin.last t) ∧ gateActive Y (p.gate line) (Fin.last t) = true) :=
          fun h => hL h.1
        rw [activeSharedCount_gate, activeSharedFanOutCount_gate, ite_eq_right hne,
          ite_eq_right hne, Nat.zero_add, Nat.zero_add]
        exact ⟨hact1, hact2⟩

namespace Internal

/-- Gate `g` is active on `Y` iff its syntactic input support intersects `Y`. -/
theorem gateActive_eq_true_iff (Y : Finset (Fin n)) (p : Program σ n t) (g : Fin t) :
    gateActive Y p g = true ↔ ∃ i ∈ Y, i ∈ p.wireSupport (Wire.gate g) := by
  induction p with
  | empty => exact Fin.elim0 g
  | @gate t p line ih =>
    have hw : ∀ w : Wire n t, wireActive Y p w = true ↔ ∃ i ∈ Y, i ∈ p.wireSupport w := by
      intro w
      cases w with
      | input i => simp [wireActive]
      | gate g => exact ih g
    refine Fin.lastCases ?_ (fun g => ?_) g
    · rw [gateActive_gate_last, decide_eq_true_iff, Program.wireSupport_gate_last]
      simp only [hw, Line.mem_inputSupport]
      exact ⟨fun ⟨a, i, hiY, hi⟩ => ⟨i, hiY, a, hi⟩, fun ⟨i, hiY, a, hi⟩ => ⟨a, i, hiY, hi⟩⟩
    · change gateActive Y (p.gate line) g.castSucc = true ↔
        ∃ i ∈ Y, i ∈ (p.gate line).wireSupport (Wire.gate g).castSucc
      rw [gateActive_gate_castSucc, Program.wireSupport_gate_castSucc, ih g]

/-- Over pairwise disjoint blocks `Y`, the number of blocks on which gate `g` is active is at most
the cardinality of its syntactic input support. -/
theorem gateBlockSpan_le_card_wireSupport {B : Nat} {Y : Fin B → Finset (Fin n)}
    (hdisj : Pairwise fun i j => Disjoint (Y i) (Y j)) (p : Program σ n t) (g : Fin t) :
    gateBlockSpan Y p g ≤ (p.wireSupport (Wire.gate g)).card := by
  set S := Finset.univ.filter fun b : Fin B => gateActive (Y b) p g = true
  set W := p.wireSupport (Wire.gate g)
  have h1 : ∀ b ∈ S, 1 ≤ (Y b ∩ W).card := by
    intro b hb
    obtain ⟨i, hiY, hiW⟩ := (gateActive_eq_true_iff (Y b) p g).mp (Finset.mem_filter.mp hb).2
    exact Finset.one_le_card.mpr ⟨i, Finset.mem_inter.mpr ⟨hiY, hiW⟩⟩
  have hbi : (S.biUnion fun b => Y b ∩ W).card = ∑ b ∈ S, (Y b ∩ W).card :=
    Finset.card_biUnion fun b₁ _ b₂ _ hne =>
      (hdisj hne).mono Finset.inter_subset_left Finset.inter_subset_left
  calc gateBlockSpan Y p g
      = ∑ _b ∈ S, 1 := Finset.card_eq_sum_ones S
    _ ≤ ∑ b ∈ S, (Y b ∩ W).card := Finset.sum_le_sum h1
    _ = (S.biUnion fun b => Y b ∩ W).card := hbi.symm
    _ ≤ W.card :=
        Finset.card_le_card (Finset.biUnion_subset.mpr fun _ _ => Finset.inter_subset_right)

/-- A wire equals at most one gate wire, so its indicator sum over the gates is at most `1`. -/
private theorem sum_ite_eq_gate_le_one (w : Wire n t) :
    (∑ x : Fin t, if w = Wire.gate x then 1 else 0) ≤ 1 := by
  cases w with
  | input _ => simp
  | gate g =>
    have hcongr : (∑ x : Fin t, if (Wire.gate g : Wire n t) = Wire.gate x then 1 else 0) =
        ∑ x : Fin t, if g = x then 1 else 0 :=
      Finset.sum_congr rfl fun x _ => by simp
    rw [hcongr, Finset.sum_ite_eq, ite_eq_left (Finset.mem_univ g)]

/-- Each binary gate has two input wires, so it contributes at most `2` to the sum of `KW.argUses`
across all earlier gates. -/
private theorem sum_argUses_le_two (line : Line Binary.signature n t) :
    ∑ g : Fin t, KW.argUses line g ≤ 2 := by
  obtain ⟨op, w⟩ := line
  simp only [KW.argUses, Finset.card_filter]
  rw [Finset.sum_comm]
  have huniv : (Finset.univ : Finset (Fin 2)) = {0, 1} := by decide
  have hne : (0 : Fin 2) ≠ 1 := by decide
  rw [huniv, Finset.sum_pair hne]
  have := sum_ite_eq_gate_le_one (w 0)
  have := sum_ite_eq_gate_le_one (w 1)
  omega

/-- Across a binary program of `t` gates, the total number of gate-argument uses is at most
`2 * t`. -/
private theorem sum_slotUses_le_two_mul :
    ∀ {t : Nat} (p : Program Binary.signature n t), ∑ g : Fin t, KW.slotUses p g ≤ 2 * t
  | 0, .empty => by simp
  | t + 1, .gate p line => by
    rw [Fin.sum_univ_castSucc]
    simp only [KW.slotUses_gate_castSucc, KW.slotUses_gate_last, add_zero, Finset.sum_add_distrib]
    have := sum_slotUses_le_two_mul p
    have := sum_argUses_le_two line
    omega

/-- In any single-output circuit over `Binary.signature`, the total fan-out of all shared gates is
at most `2 * c.size + 1`. -/
theorem sharedFanOut_le_two_mul_size_add_one (c : Circuit Binary.signature n 1) :
    sharedFanOut c ≤ 2 * c.size + 1 := by
  have hsub : sharedFanOut c ≤ ∑ g : Fin c.size, KW.gateFanOut c g :=
    Finset.sum_le_univ_sum_of_nonneg fun _ => Nat.zero_le _
  have hout : (∑ g : Fin c.size,
      (Finset.univ.filter fun o : Fin 1 => c.outputs o = Wire.gate g).card) ≤ 1 := by
    simp only [Finset.card_filter, Fintype.sum_unique]
    exact sum_ite_eq_gate_le_one (c.outputs 0)
  have hslot := sum_slotUses_le_two_mul c.program
  have htot : ∑ g : Fin c.size, KW.gateFanOut c g ≤ 2 * c.size + 1 := by
    simp only [KW.gateFanOut, Finset.sum_add_distrib]
    omega
  exact hsub.trans htot

end Internal

end BinaryCircuits

end Nechiporuk
end Algebraic
