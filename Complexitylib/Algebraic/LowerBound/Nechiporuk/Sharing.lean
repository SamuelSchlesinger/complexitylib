/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.KarchmerWigderson.Sharing.Circuit
public import Complexitylib.Algebraic.LowerBound.Nechiporuk.Subfunctions

/-!
# Programs with shared gates over the full binary basis

A `SharedProgram` over `Binary.Formula` on `n` inputs with `k` shared gates consists of `k`
intermediate formulas over the full binary basis together with one output formula, where each
formula may read the primary inputs and all previously computed shared values.

Fixing the coordinates outside a block `Y ⊆ Fin n` turns each of the `k + 1` formulas into a
subfunction of the coordinates in `Y` together with the shared variables. Since the output of the
program is determined by the `(k + 1)`-tuple of these restricted formulas, Nechiporuk's counting
lemma (`Nechiporuk.card_subfunctions_le`) applied to each formula yields
`|(subfunctions P.eval Y)| ≤ 2 ^ (k + 1) · 16 ^ (P.inputLeavesIn Y + P.sharedLeaves n)`
(`SharedProgram.card_subfunctions_le_inputLeavesIn`).

Every single-output circuit `c` over `Binary.signature` decomposes from its last gate down into a
`SharedProgram` with `k ≤ KW.sharedGateCount c` shared gates, at most `c.size` binary gates, and
at most `sharedFanOut c` shared-variable leaves (`exists_sharedProgram_of_circuit`).
-/

@[expose] public section

namespace Algebraic

namespace Binary
namespace Formula

variable {N : Nat}

/-- The number of binary gates in a formula. -/
def gates : Formula N → Nat
  | var _ => 0
  | const _ => 0
  | gate _ left right => left.gates + right.gates + 1

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

@[simp] theorem eval_mapIndex {M : Nat} (φ : Fin N → Fin M) :
    ∀ (F : Formula N) (x : Fin M → Bool), (F.mapIndex φ).eval x = F.eval (x ∘ φ)
  | var _, _ => rfl
  | const _, _ => rfl
  | gate op l r, x => by
    simp [mapIndex, eval_mapIndex φ l x, eval_mapIndex φ r x]

@[simp] theorem gates_mapIndex {M : Nat} (φ : Fin N → Fin M) :
    ∀ F : Formula N, (F.mapIndex φ).gates = F.gates
  | var _ => rfl
  | const _ => rfl
  | gate _ l r => by simp [mapIndex, gates, gates_mapIndex φ l, gates_mapIndex φ r]

/-- Substitute a formula for each variable. -/
def subst {M : Nat} (σ : Fin N → Formula M) : Formula N → Formula M
  | var i => σ i
  | const b => const b
  | gate op l r => gate op (l.subst σ) (r.subst σ)

theorem eval_subst {M : Nat} (σ : Fin N → Formula M) :
    ∀ (F : Formula N) (x : Fin M → Bool),
      (F.subst σ).eval x = F.eval fun i => (σ i).eval x
  | var _, _ => rfl
  | const _, _ => rfl
  | gate op l r, x => by
    simp [subst, eval_subst σ l x, eval_subst σ r x]

/-- The number of variable leaves with index `v`. -/
def occ (v : Nat) : Formula N → Nat
  | var i => if i.val = v then 1 else 0
  | const _ => 0
  | gate _ l r => l.occ v + r.occ v

@[simp] theorem occ_mapIndex_castLE {M : Nat} (v : Nat) (h : N ≤ M) :
    ∀ F : Formula N, (F.mapIndex (Fin.castLE h)).occ v = F.occ v
  | var _ => rfl
  | const _ => rfl
  | gate _ l r => by simp [mapIndex, occ, occ_mapIndex_castLE v h l, occ_mapIndex_castLE v h r]

/-- The number of variable leaves on the primary input variables `0, …, m - 1`. -/
def inputLeaves : Formula N → Nat → Nat
  | var i, m => if i.val < m then 1 else 0
  | const _, _ => 0
  | gate _ l r, m => l.inputLeaves m + r.inputLeaves m

/-- The number of variable leaves on the shared variables from `m` on. -/
def sharedLeaves : Formula N → Nat → Nat
  | var i, m => if m ≤ i.val then 1 else 0
  | const _, _ => 0
  | gate _ l r, m => l.sharedLeaves m + r.sharedLeaves m

/-- The number of variable leaves on variables below `n` that belong to `Y`. -/
def inputLeavesIn {n : Nat} (Y : Finset (Fin n)) : Formula N → Nat
  | var i => if h : i.val < n then if ⟨i.val, h⟩ ∈ Y then 1 else 0 else 0
  | const _ => 0
  | gate _ l r => l.inputLeavesIn Y + r.inputLeavesIn Y

theorem inputLeaves_le_leaves (m : Nat) : ∀ F : Formula N, F.inputLeaves m ≤ F.leaves
  | var _ => by
    simp only [inputLeaves, leaves]
    split <;> omega
  | const _ => Nat.zero_le _
  | gate _ l r => Nat.add_le_add (inputLeaves_le_leaves m l) (inputLeaves_le_leaves m r)

theorem inputLeaves_le_gates_add_one (m : Nat) (F : Formula N) :
    F.inputLeaves m ≤ F.gates + 1 :=
  (F.inputLeaves_le_leaves m).trans F.leaves_le_gates_add_one

theorem sharedLeaves_eq_zero_of_le {m : Nat} (hm : N ≤ m) :
    ∀ F : Formula N, F.sharedLeaves m = 0
  | var i => by
    have : ¬ m ≤ i.val := by omega
    simp [sharedLeaves, this]
  | const _ => rfl
  | gate _ l r => by
    simp [sharedLeaves, sharedLeaves_eq_zero_of_le hm l, sharedLeaves_eq_zero_of_le hm r]

@[simp] theorem sharedLeaves_mapIndex_castLE {M : Nat} (m : Nat) (h : N ≤ M) :
    ∀ F : Formula N, (F.mapIndex (Fin.castLE h)).sharedLeaves m = F.sharedLeaves m
  | var _ => rfl
  | const _ => rfl
  | gate _ l r => by
    simp [mapIndex, sharedLeaves, sharedLeaves_mapIndex_castLE m h l,
      sharedLeaves_mapIndex_castLE m h r]

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

theorem extendBlock_self {n : Nat} (Y : Finset (Fin n)) : extendBlock n Y = Y := by
  ext i
  simp [extendBlock]

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

/-- The substitution map replacing variable `N` by `φ`, keeping variables below `N`, and shifting
variables above `N` down by one. -/
def substVarMap (φ : Formula N) (d : Nat) (i : Fin (N + 1 + d)) : Formula (N + d) :=
  if h : i.val < N then var ⟨i.val, by omega⟩
  else if _ : i.val = N then φ.mapIndex (Fin.castLE (by omega))
  else var ⟨i.val - 1, by omega⟩

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

/-- A program on `n` inputs with `k` shared gates over the full binary basis: `k + 1` binary
formulas, where each formula reads the primary inputs and the values of the earlier shared
formulas. -/
inductive SharedProgram : Nat → Nat → Type
  /-- Return a binary formula of the current variables. -/
  | output {n : Nat} (F : Formula n) : SharedProgram n 0
  /-- Compute a shared binary formula and continue with its value as a new last variable. -/
  | share {n k : Nat} (G : Formula n) (P : SharedProgram (n + 1) k) : SharedProgram n (k + 1)

namespace SharedProgram

variable {n N k : Nat}

/-- Evaluate a binary program with shared gates. -/
def eval : {n k : Nat} → SharedProgram n k → (Fin n → Bool) → Bool
  | _, _, output F, x => F.eval x
  | _, _, share G P, x => P.eval (Fin.snoc x (G.eval x))

@[simp] theorem eval_output (F : Formula n) (x : Fin n → Bool) :
    (output F).eval x = F.eval x := rfl

@[simp] theorem eval_share (G : Formula n) (P : SharedProgram (n + 1) k) (x : Fin n → Bool) :
    (share G P).eval x = P.eval (Fin.snoc x (G.eval x)) := rfl

/-- A program computes `f` when it agrees with `f` on every input. -/
def Computes (P : SharedProgram n k) (f : Cslib.BooleanFunction n) : Prop :=
  ∀ x, P.eval x = f x

theorem Computes.eval_eq {P : SharedProgram n k} {f : Cslib.BooleanFunction n} (h : P.Computes f) :
    P.eval = f :=
  funext h

/-- The number of binary gates, summed over the formulas of the program. -/
def gates : {n k : Nat} → SharedProgram n k → Nat
  | _, _, output F => F.gates
  | _, _, share G P => G.gates + P.gates

@[simp] theorem gates_output (F : Formula n) : (output F).gates = F.gates := rfl

@[simp] theorem gates_share (G : Formula n) (P : SharedProgram (n + 1) k) :
    (share G P).gates = G.gates + P.gates := rfl

/-- The number of variable leaves on the variables `0, …, m - 1`, summed over the formulas. -/
def inputLeaves : {N k : Nat} → SharedProgram N k → Nat → Nat
  | _, _, output F, m => F.inputLeaves m
  | _, _, share G P, m => G.inputLeaves m + P.inputLeaves m

/-- The number of variable leaves on the variables from `m` on, summed over the formulas. -/
def sharedLeaves : {N k : Nat} → SharedProgram N k → Nat → Nat
  | _, _, output F, m => F.sharedLeaves m
  | _, _, share G P, m => G.sharedLeaves m + P.sharedLeaves m

/-- The number of variable leaves on variables below `n` that lie in `Y`, summed over the
formulas. -/
def inputLeavesIn {n : Nat} (Y : Finset (Fin n)) : {N k : Nat} → SharedProgram N k → Nat
  | _, _, output F => F.inputLeavesIn Y
  | _, _, share G P => G.inputLeavesIn Y + P.inputLeavesIn Y

/-- The input leaves of a program with `k` shared gates number at most `gates + k + 1`. -/
theorem inputLeaves_le_gates (m : Nat) : ∀ {N k : Nat} (P : SharedProgram N k),
    P.inputLeaves m ≤ P.gates + k + 1
  | _, _, output F => F.inputLeaves_le_gates_add_one m
  | _, _, share G P => by
    simp only [inputLeaves, gates]
    have := G.inputLeaves_le_gates_add_one m
    have := inputLeaves_le_gates m P
    omega

/-- Over pairwise disjoint blocks of `Fin n`, `inputLeavesIn` sums to at most `inputLeaves n`. -/
theorem sum_inputLeavesIn_le_inputLeaves {m n : Nat} (Y : Fin m → Finset (Fin n))
    (disjoint : Pairwise fun i j => Disjoint (Y i) (Y j)) :
    ∀ {N k : Nat} (P : SharedProgram N k), ∑ i, P.inputLeavesIn (Y i) ≤ P.inputLeaves n
  | _, _, output F => F.sum_inputLeavesIn_le_inputLeaves Y disjoint
  | _, _, share G P => by
    simp only [inputLeavesIn, inputLeaves, Finset.sum_add_distrib]
    exact Nat.add_le_add (G.sum_inputLeavesIn_le_inputLeaves Y disjoint)
      (sum_inputLeavesIn_le_inputLeaves Y disjoint P)

/-! ### Subfunctions of a program with shared gates -/

/-- Extend a block `Y ⊆ Fin N` to `Fin (N + 1)` by including the new shared variable `Fin.last N`.
-/
def snocBlock {N : Nat} (Y : Finset (Fin N)) : Finset (Fin (N + 1)) :=
  insert (Fin.last N) (Y.map Fin.castSuccEmb)

@[simp] theorem last_mem_snocBlock {N : Nat} (Y : Finset (Fin N)) :
    Fin.last N ∈ snocBlock Y :=
  Finset.mem_insert_self _ _

@[simp] theorem castSucc_mem_snocBlock {N : Nat} (Y : Finset (Fin N)) (i : Fin N) :
    i.castSucc ∈ snocBlock Y ↔ i ∈ Y := by
  have hne : i.castSucc ≠ Fin.last N := Fin.ne_of_lt i.isLt
  simp [snocBlock, hne]

theorem snocBlock_extendBlock {n N : Nat} (hn : n ≤ N) (Y : Finset (Fin n)) :
    snocBlock (Formula.extendBlock N Y) = Formula.extendBlock (N + 1) Y := by
  ext j
  refine Fin.lastCases ?_ (fun i => ?_) j
  · have hnot : ¬ N < n := by omega
    simp [Formula.extendBlock, hnot]
  · simp [castSucc_mem_snocBlock, Formula.extendBlock]

/-- The block leaf count of a program on `Y`: at each `share` step, the new shared variable is
included in the block for the continuation program. -/
def leavesIn : {N k : Nat} → SharedProgram N k → Finset (Fin N) → Nat
  | _, _, output F, Y => F.leavesIn Y
  | _, _, share G P, Y => G.leavesIn Y + P.leavesIn (snocBlock Y)

theorem leavesIn_extendBlock :
    ∀ {N k : Nat} (P : SharedProgram N k) {n : Nat} (_hn : n ≤ N) (Y : Finset (Fin n)),
      P.leavesIn (Formula.extendBlock N Y) = P.inputLeavesIn Y + P.sharedLeaves n
  | N, _, output F, _, _, Y => F.leavesIn_extendBlock N Y
  | N, _, share G P, _, hn, Y => by
    simp only [leavesIn, snocBlock_extendBlock hn Y, G.leavesIn_extendBlock N Y,
      leavesIn_extendBlock P (by omega) Y, inputLeavesIn, sharedLeaves]
    omega

theorem leavesIn_eq_inputLeavesIn_add_sharedLeaves (P : SharedProgram n k) (Y : Finset (Fin n)) :
    P.leavesIn Y = P.inputLeavesIn Y + P.sharedLeaves n := by
  have h := leavesIn_extendBlock P le_rfl Y
  rwa [Formula.extendBlock_self] at h

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

/-- **Nechiporuk's counting lemma for programs with shared gates.** A program with `k` shared
gates has at most `2 ^ (k + 1) · 16 ^ (P.leavesIn Y)` subfunctions on `Y`. -/
theorem card_subfunctions_le :
    ∀ {N k : Nat} (P : SharedProgram N k) (Y : Finset (Fin N)),
      (subfunctions P.eval Y).card ≤ 2 ^ (k + 1) * 16 ^ P.leavesIn Y
  | _, 0, output F, Y => by
    simpa [eval, leavesIn] using Nechiporuk.card_subfunctions_le Y F
  | N, k + 1, share G P, Y => by
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
      _ ≤ (2 * 16 ^ G.leavesIn Y) * (2 ^ (k + 1) * 16 ^ P.leavesIn (snocBlock Y)) :=
          Nat.mul_le_mul (Nechiporuk.card_subfunctions_le Y G)
            (card_subfunctions_le P (snocBlock Y))
      _ = 2 ^ (k + 1 + 1) * 16 ^ (share G P).leavesIn Y := by
          simp only [leavesIn, pow_add, pow_one]
          ring

/-- A program with `k` shared gates has at most
`2 ^ (k + 1) · 16 ^ (P.inputLeavesIn Y + P.sharedLeaves n)` subfunctions on `Y`. -/
theorem card_subfunctions_le_inputLeavesIn (P : SharedProgram n k) (Y : Finset (Fin n)) :
    (subfunctions P.eval Y).card ≤ 2 ^ (k + 1) * 16 ^ (P.inputLeavesIn Y + P.sharedLeaves n) := by
  rw [← leavesIn_eq_inputLeavesIn_add_sharedLeaves]
  exact P.card_subfunctions_le Y

/-! ### Occurrences and substitution of a variable in a `SharedProgram` -/

/-- The number of variable leaves with index `v`, summed over the formulas of the program. -/
def occ (v : Nat) : {N k : Nat} → SharedProgram N k → Nat
  | _, _, output F => F.occ v
  | _, _, share G P => G.occ v + P.occ v

@[simp] theorem occ_output (v : Nat) (F : Formula N) : (output F).occ v = F.occ v := rfl

@[simp] theorem occ_share (v : Nat) (G : Formula N) (P : SharedProgram (N + 1) k) :
    (share G P).occ v = G.occ v + P.occ v := rfl

theorem sharedLeaves_eq_occ_add_sharedLeaves_succ (m : Nat) :
    ∀ {N k : Nat} (P : SharedProgram N k),
      P.sharedLeaves m = P.occ m + P.sharedLeaves (m + 1)
  | _, _, output F => F.sharedLeaves_eq_occ_add_sharedLeaves_succ m
  | _, _, share G P => by
    simp only [sharedLeaves, occ, G.sharedLeaves_eq_occ_add_sharedLeaves_succ m,
      sharedLeaves_eq_occ_add_sharedLeaves_succ m P]
    omega

/-- Substitute the formula `φ` for variable `N` throughout a program on `N + 1 + d` variables. -/
def substVar (φ : Formula N) :
    {d k : Nat} → SharedProgram (N + 1 + d) k → SharedProgram (N + d) k
  | d, _, output F => output (F.subst (Formula.substVarMap φ d))
  | d, _, share G P => share (G.subst (Formula.substVarMap φ d)) (substVar φ (d := d + 1) P)

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

end SharedProgram

/-! ### Shared fan-out and translation from binary circuits to `SharedProgram` -/

section BinaryCircuits

variable {σ : Signature} {n m t : Nat}

/-- The total fan-out of the gates of `p` whose fan-out is at least two when gate `g` is read
`u g` more times. -/
def sharedFanOutCount (p : Program σ n t) (u : Fin t → Nat) : Nat :=
  ∑ g ∈ Finset.univ.filter (fun g => 2 ≤ KW.slotUses p g + u g), (KW.slotUses p g + u g)

/-- The total fan-out of all shared gates (gates of fan-out at least two) of a circuit. -/
def sharedFanOut (c : Circuit σ n m) : Nat :=
  ∑ g ∈ Finset.univ.filter (fun g => 2 ≤ KW.gateFanOut c g), KW.gateFanOut c g

theorem sharedFanOut_eq (c : Circuit σ n m) :
    sharedFanOut c = sharedFanOutCount c.program
      fun g => (Finset.univ.filter fun o => c.outputs o = Wire.gate g).card := rfl

theorem sharedGateCount_le_sharedFanOut (c : Circuit σ n m) :
    KW.sharedGateCount c ≤ sharedFanOut c := by
  rw [KW.sharedGateCount, sharedFanOut, Finset.card_eq_sum_ones]
  refine Finset.sum_le_sum fun g hg => ?_
  have := (Finset.mem_filter.mp hg).2
  omega

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

/-- The formula of one full-binary-basis gate over the earlier wires, numbered by `Wire.index`. -/
def lineFormula (line : Line Binary.signature n t) : Formula (n + t) :=
  .gate line.op (.var (line.wires 0).index) (.var (line.wires 1).index)

/-- The values of the inputs and gates of a binary program, numbered by `Wire.index`. -/
def wireValues (p : Program Binary.signature n t) (x : Fin n → Bool) : Fin (n + t) → Bool :=
  Fin.append x (p.eval Binary.interpretation x)

theorem eval_lineFormula (line : Line Binary.signature n t) (x : Fin n → Bool)
    (vals : Fin t → Bool) :
    (lineFormula line).eval (Fin.append x vals) = line.eval Binary.interpretation x vals := by
  simp [lineFormula, Line.eval, Binary.interpretation, KW.append_index]

theorem gates_lineFormula (line : Line Binary.signature n t) :
    (lineFormula line).gates = 1 := rfl

theorem sharedLeaves_lineFormula (line : Line Binary.signature n t) :
    (lineFormula line).sharedLeaves (n + t) = 0 :=
  Formula.sharedLeaves_eq_zero_of_le le_rfl _

theorem occ_lineFormula_le (line : Line Binary.signature n t) (g : Fin t) :
    (lineFormula line).occ (n + g.val) ≤ KW.argUses line g := by
  obtain ⟨op, w⟩ := line
  rw [KW.argUses, Finset.card_filter]
  have hne : (0 : Fin 2) ≠ 1 := by decide
  have huniv : (Finset.univ : Finset (Fin 2)) = {0, 1} := by decide
  rw [huniv, Finset.sum_pair hne]
  simp only [lineFormula, Formula.occ, KW.index_val_eq_iff]
  split_ifs <;> simp_all

theorem eval_gate (p : Program Binary.signature n t) (line : Line Binary.signature n t)
    (x : Fin n → Bool) :
    (p.gate line).eval Binary.interpretation x =
      Fin.snoc (p.eval Binary.interpretation x)
        (line.eval Binary.interpretation x (p.eval Binary.interpretation x)) := by
  funext g
  refine Fin.lastCases ?_ (fun g => ?_) g
  · rw [Program.eval_gate_last, Fin.snoc_last]
  · rw [Program.eval_gate_castSucc, Fin.snoc_castSucc]

theorem wireValues_gate (p : Program Binary.signature n t) (line : Line Binary.signature n t)
    (x : Fin n → Bool) :
    wireValues (p.gate line) x =
      Fin.snoc (wireValues p x) ((lineFormula line).eval (wireValues p x)) := by
  rw [wireValues, eval_gate, Fin.append_snoc, wireValues, eval_lineFormula]

theorem wireValues_empty (x : Fin n → Bool) :
    wireValues (.empty : Program Binary.signature n 0) x = x := by
  funext i
  change Fin.append x Fin.elim0 i = x i
  rw [Fin.append_elim0]
  rfl

/-- Build a `SharedProgram` from the last gate of a full-binary-basis program down. -/
theorem exists_sharedProgram_of_program {n : Nat} (f : Cslib.BooleanFunction n) :
    ∀ {t : Nat} (p : Program Binary.signature n t) (u : Fin t → Nat) {j : Nat}
      (Q : SharedProgram (n + t) j),
      (∀ x, Q.eval (wireValues p x) = f x) → (∀ g : Fin t, Q.occ (n + g.val) ≤ u g) →
      ∃ k, ∃ P : SharedProgram n k,
        k ≤ j + KW.sharedCount p u ∧ P.Computes f ∧
          P.gates ≤ Q.gates + t ∧
          P.sharedLeaves n ≤ Q.sharedLeaves (n + t) + sharedFanOutCount p u
  | _, .empty, u, j, Q, hQ, _ =>
    ⟨j, Q, by simp, fun x => by simpa [wireValues_empty] using hQ x, by simp,
      by simp [sharedFanOutCount]⟩
  | _, .gate (gateCount := t) p line, u, j, Q, hQ, hocc => by
    have hφocc := occ_lineFormula_le line
    have hφgates := gates_lineFormula line
    have hφshared := sharedLeaves_lineFormula line
    have hcount := KW.sharedCount_gate p line u
    have hfanout := sharedFanOutCount_gate p line u
    have hlast : Q.occ (n + t) ≤ u (Fin.last t) := hocc (Fin.last t)
    by_cases hL : 2 ≤ u (Fin.last t)
    · obtain ⟨k, P, hk, hP, hgates, hshared⟩ := exists_sharedProgram_of_program f p
        (fun g => u g.castSucc + KW.argUses line g) (SharedProgram.share (lineFormula line) Q)
        (fun x => by
          rw [SharedProgram.eval_share, ← wireValues_gate]
          exact hQ x)
        (fun g => by
          have h₁ : Q.occ (n + g.val) ≤ u g.castSucc := hocc g.castSucc
          have h₂ := hφocc g
          rw [SharedProgram.occ_share]
          omega)
      refine ⟨k, P, ?_, hP, ?_, ?_⟩
      · rw [hcount, ite_eq_left hL]
        omega
      · rw [SharedProgram.gates_share, hφgates] at hgates
        omega
      · have hQshared := Q.sharedLeaves_eq_occ_add_sharedLeaves_succ (n + t)
        simp only [SharedProgram.sharedLeaves, hφshared, zero_add] at hshared
        change P.sharedLeaves n ≤ Q.sharedLeaves (n + t + 1) + sharedFanOutCount (p.gate line) u
        rw [hfanout, ite_eq_left hL]
        omega
    · have hL₁ : Q.occ (n + t) ≤ 1 := by omega
      obtain ⟨k, P, hk, hP, hgates, hshared⟩ := exists_sharedProgram_of_program f p
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
      refine ⟨k, P, ?_, hP, ?_, ?_⟩
      · rw [hcount, ite_eq_right hL]
        omega
      · rw [SharedProgram.gates_substVar, hφgates] at hgates
        omega
      · rw [SharedProgram.sharedLeaves_substVar] at hshared
        change P.sharedLeaves n ≤ Q.sharedLeaves (n + t + 1) + sharedFanOutCount (p.gate line) u
        rw [hfanout, ite_eq_right hL]
        omega

/-- **Full-binary-basis circuits as programs with shared gates.** Every single-output circuit `c`
over `Binary.signature` computing `f` yields a `SharedProgram` computing `f` with at most
`KW.sharedGateCount c` shared gates, at most `c.size` binary gates, and at most `sharedFanOut c`
shared-variable leaves. -/
theorem exists_sharedProgram_of_circuit {n : Nat} (c : Circuit Binary.signature n 1)
    {f : Cslib.BooleanFunction n} (hc : c.ComputesWith Binary.interpretation fun x _ => f x) :
    ∃ k, ∃ P : SharedProgram n k,
      k ≤ KW.sharedGateCount c ∧ P.Computes f ∧
        P.gates ≤ c.size ∧ P.sharedLeaves n ≤ sharedFanOut c := by
  obtain ⟨k, P, hk, hP, hgates, hshared⟩ := exists_sharedProgram_of_program f c.program
    (fun g => (Finset.univ.filter fun o => c.outputs o = Wire.gate g).card) (j := 0)
    (SharedProgram.output (.var (c.outputs 0).index))
    (fun x => by
      have := congrFun (hc x) 0
      simp only [Circuit.eval, Function.comp_apply, Program.trace] at this
      simp [wireValues, KW.append_index, this])
    (fun g => by
      simp only [SharedProgram.occ, Formula.occ]
      split_ifs with h
      · exact Finset.card_pos.mpr ⟨0, by simpa using (KW.index_val_eq_iff _ g).mp h⟩
      · exact Nat.zero_le _)
  have hinit_shared :
      (SharedProgram.output (.var (c.outputs 0).index)).sharedLeaves (n + c.size) = 0 :=
    Formula.sharedLeaves_eq_zero_of_le le_rfl _
  refine ⟨k, P, by rw [KW.sharedGateCount_eq]; simpa using hk, hP, ?_, ?_⟩
  · simpa [Formula.gates] using hgates
  · rw [sharedFanOut_eq]
    simpa [hinit_shared] using hshared

end BinaryCircuits

end Nechiporuk
end Algebraic
