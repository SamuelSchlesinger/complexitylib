/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.KarchmerWigderson.Sharing
public import Complexitylib.Algebraic.Basis.DeMorgan
public import Complexitylib.Algebraic.Semantics
public import Complexitylib.Cslib.Circuit.Wire

/-!
# Khrapchenko's bound for circuits with shared gates and XOR/EQUIV gates

In `SharedProgram.sq_card_edges_le`, the Khrapchenko upper bound `(k + 1) · X · |A| · |B|` depends
on `X = P.inputLeaves n`, which counts only literal leaves on the original circuit inputs
`0, …, n - 1` and ignores literal leaves reading shared variables `z ≥ n`.

Consequently, any binary gadget built solely from shared variables `z₁, z₂ ≥ n`—such as the four-leaf
De Morgan expansion `Formula.xorGadget z₁ z₂` of `z₁ ⊕ z₂` or `Formula.equivGadget z₁ z₂` of
`z₁ ↔ z₂`—has `inputLeaves n = 0`. In a circuit over the extended basis containing De Morgan gates
 together with `r` binary XOR and EQUIV gates, allocating two shared steps for the two input wires
of each XOR/EQUIV gate and substituting `xorGadget` or `equivGadget` for the gate wire replaces
every XOR/EQUIV gate by a zero-input-leaf subformula while increasing the shared-variable count by
at most `2r` regardless of the XOR/EQUIV gate's fan-out.

Tracking `inputLeaves (n + t)` directly down the gate list of the circuit shows that a circuit with
`c_DM` binary De Morgan gates (`and`/`or`), `r` binary XOR/EQUIV gates, and `k` shared gates yields
a `SharedProgram n K` with `K ≤ k + 2r` and `P.inputLeaves n ≤ c_DM + k + 2r + 1`. Thus:
* `|edges A B|² ≤ (k + 2r + 1) · (c_DM + k + 2r + 1) · |A| · |B|` (`sq_card_edges_le_cost`),
* `n² ≤ (k + 2r + 1) · (c_DM + k + 2r + 1)` for parity (`parity_sq_le_cost`),
* `(n + 1 - t) · t ≤ (k + 2r + 1) · (c_DM + k + 2r + 1)` for `threshold t`
  (`threshold_mul_le_cost`),
* `(n - ⌊n/2⌋) · (⌊n/2⌋ + 1) ≤ (k + 2r + 1) · (c_DM + k + 2r + 1)` for majority
  (`majority_mul_le_cost`),
and both parity and majority require superlinear De Morgan gate count `c_DM = ω(n)` whenever both
`k(n) = o(n)` and `r(n) = o(n)` (`isLittleO_cost_of_parity`, `isLittleO_cost_of_majority`).
-/

@[expose] public section

namespace Algebraic
namespace KW

/-! ### XOR and EQUIV gadgets and input-leaf identities on formulas -/

namespace Formula

variable {N M : Nat}

/-- The De Morgan formula `(z₁ ∧ ¬z₂) ∨ (¬z₁ ∧ z₂)` computing `z₁ ⊕ z₂` on two variables. -/
def xorGadget (z₁ z₂ : Fin N) : Formula N :=
  .or (.and (.lit z₁ true) (.lit z₂ false)) (.and (.lit z₁ false) (.lit z₂ true))

/-- The De Morgan formula `(z₁ ∧ z₂) ∨ (¬z₁ ∧ ¬z₂)` computing `z₁ ↔ z₂` on two variables. -/
def equivGadget (z₁ z₂ : Fin N) : Formula N :=
  .or (.and (.lit z₁ true) (.lit z₂ true)) (.and (.lit z₁ false) (.lit z₂ false))

@[simp] theorem eval_xorGadget (z₁ z₂ : Fin N) (x : Fin N → Bool) :
    (xorGadget z₁ z₂).eval x = (x z₁ ^^ x z₂) := by
  simp only [xorGadget, eval]
  cases x z₁ <;> cases x z₂ <;> rfl

@[simp] theorem eval_equivGadget (z₁ z₂ : Fin N) (x : Fin N → Bool) :
    (equivGadget z₁ z₂).eval x = (x z₁ == x z₂) := by
  simp only [equivGadget, eval]
  cases x z₁ <;> cases x z₂ <;> rfl

/-- When both variables `z₁, z₂` are shared variables (`≥ m`), `xorGadget z₁ z₂` contributes zero
input leaves below `m`. -/
theorem inputLeaves_xorGadget_of_ge {m : Nat} {z₁ z₂ : Fin N} (h₁ : m ≤ z₁.val) (h₂ : m ≤ z₂.val) :
    (xorGadget z₁ z₂).inputLeaves m = 0 := by
  simp only [xorGadget, inputLeaves]
  split_ifs <;> omega

/-- When both variables `z₁, z₂` are shared variables (`≥ m`), `equivGadget z₁ z₂` contributes zero
input leaves below `m`. -/
theorem inputLeaves_equivGadget_of_ge {m : Nat} {z₁ z₂ : Fin N}
    (h₁ : m ≤ z₁.val) (h₂ : m ≤ z₂.val) :
    (equivGadget z₁ z₂).inputLeaves m = 0 := by
  simp only [equivGadget, inputLeaves]
  split_ifs <;> omega

end Formula

namespace KarchmerWigderson.Sharing

export Formula (xorGadget equivGadget eval_xorGadget eval_equivGadget
  inputLeaves_xorGadget_of_ge inputLeaves_equivGadget_of_ge)

/-! ### Variable occurrences, substitutions, and input-leaf tracking -/

section InsertVal

variable {N : Nat}

/-- Insert the value `b` at position `N` of `y`, moving the later entries up by one. -/
def insertVal {d : Nat} (y : Fin (N + d) → Bool) (b : Bool) : Fin (N + 1 + d) → Bool :=
  fun i => if h : i.val < N then y ⟨i.val, by omega⟩
    else if _ : i.val = N then b else y ⟨i.val - 1, by omega⟩

/-- Insert the two values `b₀, b₁` at positions `N, N + 1` of `y`, moving the later entries up by
two. -/
def insertVal2 {d : Nat} (y : Fin (N + d) → Bool) (b₀ b₁ : Bool) : Fin (N + 2 + d) → Bool :=
  fun i => if h : i.val < N then y ⟨i.val, by omega⟩
    else if _ : i.val = N then b₀
    else if _ : i.val = N + 1 then b₁
    else y ⟨i.val - 2, by omega⟩

private theorem snoc_apply {m : Nat} (y : Fin m → Bool) (g : Bool) (i : Fin (m + 1)) :
    Fin.snoc (α := fun _ => Bool) y g i = if h : i.val < m then y ⟨i.val, h⟩ else g := by
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp
  · simp

theorem insertVal_zero (y : Fin N → Bool) (b : Bool) :
    insertVal (d := 0) y b = Fin.snoc y b := by
  funext i
  rw [snoc_apply (m := N)]
  unfold insertVal
  split_ifs <;> first | rfl | omega

theorem insertVal_snoc {d : Nat} (y : Fin (N + d) → Bool) (g b : Bool) :
    insertVal (d := d + 1) (Fin.snoc y g) b = Fin.snoc (insertVal y b) g := by
  funext i
  simp only [insertVal, snoc_apply, Nat.add_eq]
  split_ifs <;> first | rfl | omega

theorem insertVal2_zero (y : Fin N → Bool) (b₀ b₁ : Bool) :
    insertVal2 (d := 0) y b₀ b₁ = Fin.snoc (Fin.snoc y b₀) b₁ := by
  funext i
  simp only [insertVal2, snoc_apply]
  split_ifs <;> first | rfl | omega

theorem insertVal2_snoc {d : Nat} (y : Fin (N + d) → Bool) (g b₀ b₁ : Bool) :
    insertVal2 (d := d + 1) (Fin.snoc y g) b₀ b₁ = Fin.snoc (insertVal2 y b₀ b₁) g := by
  funext i
  simp only [insertVal2, snoc_apply, Nat.add_eq]
  split_ifs <;> first | rfl | omega

end InsertVal

namespace Formula

variable {N M : Nat}

/-- The number of literal leaves on the variable with index `v`. -/
def occ (v : Nat) : Formula N → Nat
  | .lit i _ => if i.val = v then 1 else 0
  | .const _ => 0
  | .and l r => occ v l + occ v r
  | .or l r => occ v l + occ v r

@[simp] theorem occ_neg (v : Nat) : ∀ F : Formula N, occ v F.neg = occ v F
  | .lit _ _ => rfl
  | .const _ => rfl
  | .and l r => by simp [Formula.neg, occ, occ_neg v l, occ_neg v r]
  | .or l r => by simp [Formula.neg, occ, occ_neg v l, occ_neg v r]

@[simp] theorem occ_mapIndex_castLE (v : Nat) (h : N ≤ M) :
    ∀ F : Formula N, occ v (F.mapIndex (Fin.castLE h)) = occ v F
  | .lit _ _ => rfl
  | .const _ => rfl
  | .and l r => by simp [Formula.mapIndex, occ, occ_mapIndex_castLE v h l, occ_mapIndex_castLE v h r]
  | .or l r => by simp [Formula.mapIndex, occ, occ_mapIndex_castLE v h l, occ_mapIndex_castLE v h r]

@[simp] theorem inputLeaves_mapIndex_castLE (m : Nat) (h : N ≤ M) :
    ∀ F : Formula N, (F.mapIndex (Fin.castLE h)).inputLeaves m = F.inputLeaves m
  | .lit _ _ => rfl
  | .const _ => rfl
  | .and l r => by
    simp [Formula.mapIndex, Formula.inputLeaves, inputLeaves_mapIndex_castLE m h l,
      inputLeaves_mapIndex_castLE m h r]
  | .or l r => by
    simp [Formula.mapIndex, Formula.inputLeaves, inputLeaves_mapIndex_castLE m h l,
      inputLeaves_mapIndex_castLE m h r]

theorem inputLeaves_succ (m : Nat) :
    ∀ F : Formula N, F.inputLeaves (m + 1) = F.inputLeaves m + occ m F
  | .lit i _ => by
    simp only [Formula.inputLeaves, occ]
    split_ifs <;> omega
  | .const _ => rfl
  | .and l r => by
    simp only [Formula.inputLeaves, occ, inputLeaves_succ m l, inputLeaves_succ m r]
    omega
  | .or l r => by
    simp only [Formula.inputLeaves, occ, inputLeaves_succ m l, inputLeaves_succ m r]
    omega

theorem occ_eq_zero_of_inputLeaves_eq_zero {m v : Nat} (hv : v < m) :
    ∀ {F : Formula N}, F.inputLeaves m = 0 → occ v F = 0
  | .lit i _, h => by
    simp only [Formula.inputLeaves, occ] at h ⊢
    split_ifs at h ⊢ <;> omega
  | .const _, _ => rfl
  | .and l r, h => by
    simp only [Formula.inputLeaves, Nat.add_eq_zero_iff] at h
    simp [occ, occ_eq_zero_of_inputLeaves_eq_zero hv h.1, occ_eq_zero_of_inputLeaves_eq_zero hv h.2]
  | .or l r, h => by
    simp only [Formula.inputLeaves, Nat.add_eq_zero_iff] at h
    simp [occ, occ_eq_zero_of_inputLeaves_eq_zero hv h.1, occ_eq_zero_of_inputLeaves_eq_zero hv h.2]

/-- Substitute `φ : Formula N` for variable `N`, shifting variables above `N` down by one. -/
def substVarMap (φ : Formula N) (d : Nat) (i : Fin (N + 1 + d)) : Formula (N + d) :=
  if h : i.val < N then .lit ⟨i.val, by omega⟩ true
  else if _ : i.val = N then φ.mapIndex (Fin.castLE (by omega))
  else .lit ⟨i.val - 1, by omega⟩ true

theorem inputLeaves_subst_substVarMap (φ : Formula N) (d : Nat) :
    ∀ F : Formula (N + 1 + d),
      (F.subst (substVarMap φ d)).inputLeaves N = F.inputLeaves N + occ N F * φ.inputLeaves N
  | .lit i b => by
    have key : (substVarMap φ d i).inputLeaves N =
        (if i.val < N then 1 else 0) + (if i.val = N then 1 else 0) * φ.inputLeaves N := by
      unfold substVarMap
      split_ifs <;> simp [Formula.inputLeaves, inputLeaves_mapIndex_castLE] <;> omega
    cases b <;> simp [Formula.subst, Formula.inputLeaves, occ, key]
  | .const _ => by simp [Formula.subst, Formula.inputLeaves, occ]
  | .and l r => by
    simp only [Formula.subst, Formula.inputLeaves, occ,
      inputLeaves_subst_substVarMap φ d l, inputLeaves_subst_substVarMap φ d r]
    ring
  | .or l r => by
    simp only [Formula.subst, Formula.inputLeaves, occ,
      inputLeaves_subst_substVarMap φ d l, inputLeaves_subst_substVarMap φ d r]
    ring

theorem occ_subst_substVarMap (φ : Formula N) (d : Nat) {w : Nat} (hw : w < N) :
    ∀ F : Formula (N + 1 + d),
      occ w (F.subst (substVarMap φ d)) = occ w F + occ N F * occ w φ
  | .lit i b => by
    have key : occ w (substVarMap φ d i) =
        (if i.val = w then 1 else 0) + (if i.val = N then 1 else 0) * occ w φ := by
      unfold substVarMap
      split_ifs <;> simp [occ] <;> omega
    cases b <;> simp [Formula.subst, occ, key]
  | .const _ => by simp [Formula.subst, occ]
  | .and l r => by
    simp only [Formula.subst, occ, occ_subst_substVarMap φ d hw l, occ_subst_substVarMap φ d hw r]
    ring
  | .or l r => by
    simp only [Formula.subst, occ, occ_subst_substVarMap φ d hw l, occ_subst_substVarMap φ d hw r]
    ring

theorem eval_subst_substVarMap (φ : Formula N) (d : Nat) (F : Formula (N + 1 + d))
    (y : Fin (N + d) → Bool) :
    (F.subst (substVarMap φ d)).eval y =
      F.eval (insertVal y (φ.eval fun j => y (Fin.castLE (by omega) j))) := by
  rw [Formula.eval_subst]
  congr 1
  funext i
  unfold substVarMap insertVal
  split_ifs <;> simp [Function.comp_def]

/-- Substitute `ψ : Formula (N + 2)` for variable `N`, shifting variables above `N` up by one to
accommodate the two new shared variables at `N` and `N + 1`. -/
def liftSubstMap (ψ : Formula (N + 2)) (d : Nat) (i : Fin (N + 1 + d)) : Formula (N + 2 + d) :=
  if h : i.val < N then .lit ⟨i.val, by omega⟩ true
  else if _ : i.val = N then ψ.mapIndex (Fin.castLE (by omega))
  else .lit ⟨i.val + 1, by omega⟩ true

theorem inputLeaves_subst_liftSubstMap (ψ : Formula (N + 2)) (hψ : ψ.inputLeaves N = 0) (d : Nat) :
    ∀ F : Formula (N + 1 + d),
      (F.subst (liftSubstMap ψ d)).inputLeaves N = F.inputLeaves N
  | .lit i b => by
    have key : (liftSubstMap ψ d i).inputLeaves N = if i.val < N then 1 else 0 := by
      unfold liftSubstMap
      split_ifs <;> simp [Formula.inputLeaves, inputLeaves_mapIndex_castLE, hψ] <;> omega
    cases b <;> simp [Formula.subst, Formula.inputLeaves, key]
  | .const _ => by simp [Formula.subst, Formula.inputLeaves]
  | .and l r => by
    simp [Formula.subst, Formula.inputLeaves,
      inputLeaves_subst_liftSubstMap ψ hψ d l, inputLeaves_subst_liftSubstMap ψ hψ d r]
  | .or l r => by
    simp [Formula.subst, Formula.inputLeaves,
      inputLeaves_subst_liftSubstMap ψ hψ d l, inputLeaves_subst_liftSubstMap ψ hψ d r]

theorem occ_subst_liftSubstMap (ψ : Formula (N + 2)) (hψ : ψ.inputLeaves N = 0) (d : Nat)
    {w : Nat} (hw : w < N) :
    ∀ F : Formula (N + 1 + d),
      occ w (F.subst (liftSubstMap ψ d)) = occ w F
  | .lit i b => by
    have hψw : occ w ψ = 0 := occ_eq_zero_of_inputLeaves_eq_zero hw hψ
    have key : occ w (liftSubstMap ψ d i) = if i.val = w then 1 else 0 := by
      unfold liftSubstMap
      split_ifs <;> simp [occ, hψw] <;> omega
    cases b <;> simp [Formula.subst, occ, key]
  | .const _ => by simp [Formula.subst, occ]
  | .and l r => by
    simp [Formula.subst, occ,
      occ_subst_liftSubstMap ψ hψ d hw l, occ_subst_liftSubstMap ψ hψ d hw r]
  | .or l r => by
    simp [Formula.subst, occ,
      occ_subst_liftSubstMap ψ hψ d hw l, occ_subst_liftSubstMap ψ hψ d hw r]

theorem eval_subst_liftSubstMap (ψ : Formula (N + 2)) (d : Nat) (F : Formula (N + 1 + d))
    (y : Fin (N + d) → Bool) (b₀ b₁ : Bool) :
    (F.subst (liftSubstMap ψ d)).eval (insertVal2 y b₀ b₁) =
      F.eval (insertVal y
        (ψ.eval (insertVal2 (d := 0) (fun j => y (Fin.castLE (by omega) j)) b₀ b₁))) := by
  rw [Formula.eval_subst]
  congr 1
  funext i
  unfold liftSubstMap insertVal
  split_ifs with h₁ h₂
  · simp [insertVal2, h₁]
  · rw [Formula.eval_mapIndex]
    rfl
  · simp only [Formula.eval, insertVal2]
    split_ifs <;> first | rfl | omega

end Formula

namespace SharedProgram

variable {N : Nat}

/-- The number of literal leaves on the variable with index `v`, summed over the formulas. -/
def occ (v : Nat) : {N k : Nat} → SharedProgram N k → Nat
  | _, _, .output F => Formula.occ v F
  | _, _, .share G P => Formula.occ v G + occ v P

@[simp] theorem occ_output (v : Nat) (F : Formula N) : occ v (.output F) = Formula.occ v F := rfl

@[simp] theorem occ_share {k : Nat} (v : Nat) (G : Formula N) (P : SharedProgram (N + 1) k) :
    occ v (.share G P) = Formula.occ v G + occ v P := rfl

@[simp] theorem inputLeaves_output (m : Nat) (F : Formula N) :
    (SharedProgram.output F).inputLeaves m = F.inputLeaves m := rfl

@[simp] theorem inputLeaves_share {k : Nat} (m : Nat) (G : Formula N)
    (P : SharedProgram (N + 1) k) :
    (SharedProgram.share G P).inputLeaves m = G.inputLeaves m + P.inputLeaves m := rfl

theorem inputLeaves_succ (m : Nat) :
    ∀ {N k : Nat} (P : SharedProgram N k), P.inputLeaves (m + 1) = P.inputLeaves m + occ m P
  | _, _, .output F => Formula.inputLeaves_succ m F
  | _, _, .share G P => by
    simp only [inputLeaves_share, occ_share, Formula.inputLeaves_succ m G, inputLeaves_succ m P]
    omega

/-- Substitute the formula `φ` for the variable `N` of a program reading `N + 1 + d` variables. -/
def substVar (φ : Formula N) : {d k : Nat} → SharedProgram (N + 1 + d) k → SharedProgram (N + d) k
  | d, _, .output F => .output (F.subst (Formula.substVarMap φ d))
  | d, _, .share G P => .share (G.subst (Formula.substVarMap φ d)) (substVar φ (d := d + 1) P)

theorem eval_substVar (φ : Formula N) : ∀ {d k : Nat} (P : SharedProgram (N + 1 + d) k)
    (y : Fin (N + d) → Bool),
    (substVar φ P).eval y =
      P.eval (insertVal y (φ.eval fun j => y (Fin.castLE (by omega) j)))
  | d, _, .output F, y => by
    rw [substVar, SharedProgram.eval_output, Formula.eval_subst_substVarMap,
      SharedProgram.eval_output]
  | d, _, .share G P, y => by
    rw [substVar, SharedProgram.eval_share, SharedProgram.eval_share,
      eval_substVar φ (d := d + 1) P, Formula.eval_subst_substVarMap]
    congr 1
    have hφ : (φ.eval fun j => Fin.snoc (α := fun _ => Bool) y
        (G.eval (insertVal y (φ.eval fun j => y (Fin.castLE (by omega) j))))
          (Fin.castLE (by omega) j)) = φ.eval fun j => y (Fin.castLE (by omega) j) := by
      congr 1
      funext j
      rw [snoc_apply (m := N + d)]
      simp only [Fin.val_castLE]
      split_ifs with h
      · rfl
      · omega
    rw [hφ, insertVal_snoc]

theorem inputLeaves_substVar (φ : Formula N) :
    ∀ {d k : Nat} (P : SharedProgram (N + 1 + d) k),
      (substVar φ P).inputLeaves N = P.inputLeaves N + occ N P * φ.inputLeaves N
  | d, _, .output F => by
    rw [substVar]
    simp only [inputLeaves_output, occ_output, Formula.inputLeaves_subst_substVarMap]
  | d, _, .share G P => by
    rw [substVar]
    simp only [inputLeaves_share, occ_share, Formula.inputLeaves_subst_substVarMap,
      inputLeaves_substVar φ (d := d + 1) P]
    ring

theorem occ_substVar (φ : Formula N) {w : Nat} (hw : w < N) :
    ∀ {d k : Nat} (P : SharedProgram (N + 1 + d) k),
      occ w (substVar φ P) = occ w P + occ N P * Formula.occ w φ
  | d, _, .output F => by
    rw [substVar]
    simp only [occ_output, Formula.occ_subst_substVarMap φ d hw]
  | d, _, .share G P => by
    rw [substVar]
    simp only [occ_share, Formula.occ_subst_substVarMap φ d hw, occ_substVar φ hw (d := d + 1) P]
    ring

/-- Substitute `ψ : Formula (N + 2)` for variable `N` in a program reading `N + 1 + d` variables,
shifting variables above `N` up by one so the result reads `N + 2 + d` variables. -/
def liftSubst (ψ : Formula (N + 2)) :
    {d k : Nat} → SharedProgram (N + 1 + d) k → SharedProgram (N + 2 + d) k
  | d, _, .output F => .output (F.subst (Formula.liftSubstMap ψ d))
  | d, _, .share G P => .share (G.subst (Formula.liftSubstMap ψ d)) (liftSubst ψ (d := d + 1) P)

theorem eval_liftSubst (ψ : Formula (N + 2)) :
    ∀ {d k : Nat} (P : SharedProgram (N + 1 + d) k) (y : Fin (N + d) → Bool) (b₀ b₁ : Bool),
      (liftSubst ψ P).eval (insertVal2 y b₀ b₁) =
        P.eval (insertVal y
          (ψ.eval (insertVal2 (d := 0) (fun j => y (Fin.castLE (by omega) j)) b₀ b₁)))
  | d, _, .output F, y, b₀, b₁ => by
    rw [liftSubst, SharedProgram.eval_output, Formula.eval_subst_liftSubstMap,
      SharedProgram.eval_output]
  | d, _, .share G P, y, b₀, b₁ => by
    rw [liftSubst, SharedProgram.eval_share, SharedProgram.eval_share,
       ← insertVal2_snoc, eval_liftSubst ψ (d := d + 1) P, Formula.eval_subst_liftSubstMap]
    congr 1
    have hψ : (ψ.eval (insertVal2 (d := 0) (fun j => Fin.snoc (α := fun _ => Bool) y
        (G.eval (insertVal y
          (ψ.eval (insertVal2 (d := 0) (fun j => y (Fin.castLE (by omega) j)) b₀ b₁))))
        (Fin.castLE (by omega) j)) b₀ b₁)) =
        ψ.eval (insertVal2 (d := 0) (fun j => y (Fin.castLE (by omega) j)) b₀ b₁) := by
      congr 2
      funext j
      rw [snoc_apply (m := N + d)]
      simp only [Fin.val_castLE]
      split_ifs with h
      · rfl
      · omega
    rw [hψ, insertVal_snoc]

theorem inputLeaves_liftSubst (ψ : Formula (N + 2)) (hψ : ψ.inputLeaves N = 0) :
    ∀ {d k : Nat} (P : SharedProgram (N + 1 + d) k),
      (liftSubst ψ P).inputLeaves N = P.inputLeaves N
  | d, _, .output F => by
    rw [liftSubst, inputLeaves_output, Formula.inputLeaves_subst_liftSubstMap ψ hψ d,
      inputLeaves_output]
  | d, _, .share G P => by
    rw [liftSubst, inputLeaves_share, Formula.inputLeaves_subst_liftSubstMap ψ hψ d,
      inputLeaves_liftSubst ψ hψ (d := d + 1) P, inputLeaves_share]

theorem occ_liftSubst (ψ : Formula (N + 2)) (hψ : ψ.inputLeaves N = 0) {w : Nat} (hw : w < N) :
    ∀ {d k : Nat} (P : SharedProgram (N + 1 + d) k),
      occ w (liftSubst ψ P) = occ w P
  | d, _, .output F => by
    rw [liftSubst, occ_output, Formula.occ_subst_liftSubstMap ψ hψ d hw, occ_output]
  | d, _, .share G P => by
    rw [liftSubst, occ_share, Formula.occ_subst_liftSubstMap ψ hψ d hw,
      occ_liftSubst ψ hψ hw (d := d + 1) P, occ_share]

end SharedProgram

/-! ### Extended De Morgan + XOR/EQUIV basis -/

/-- Operation symbols of the extended De Morgan basis with binary `xor` and `equiv` gates. -/
inductive Op
  | false
  | true
  | id
  | not
  | and
  | or
  | xor
  | equiv
  deriving DecidableEq

instance : Fintype Op :=
  Fintype.ofList [.false, .true, .id, .not, .and, .or, .xor, .equiv] (by
    intro op
    cases op <;> simp)

/-- Arity of an operation in the extended basis. -/
def arity : Op → Nat
  | .false | .true => 0
  | .id | .not => 1
  | .and | .or | .xor | .equiv => 2

@[simp] theorem arity_false : arity .false = 0 := rfl
@[simp] theorem arity_true : arity .true = 0 := rfl
@[simp] theorem arity_id : arity .id = 1 := rfl
@[simp] theorem arity_not : arity .not = 1 := rfl
@[simp] theorem arity_and : arity .and = 2 := rfl
@[simp] theorem arity_or : arity .or = 2 := rfl
@[simp] theorem arity_xor : arity .xor = 2 := rfl
@[simp] theorem arity_equiv : arity .equiv = 2 := rfl

/-- Signature of the extended De Morgan + XOR/EQUIV basis. -/
abbrev signature : Signature where
  Op := Op
  Arity := arity

/-- Standard Boolean interpretation of the extended basis. -/
def interpretation : (op : Op) → (Fin (arity op) → Bool) → Bool
  | .false, _ => false
  | .true, _ => true
  | .id, input => input ⟨0, by decide⟩
  | .not, input => !(input ⟨0, by decide⟩)
  | .and, input => input ⟨0, by decide⟩ && input ⟨1, by decide⟩
  | .or, input => input ⟨0, by decide⟩ || input ⟨1, by decide⟩
  | .xor, input => (input ⟨0, by decide⟩ ^^ input ⟨1, by decide⟩)
  | .equiv, input => (input ⟨0, by decide⟩ == input ⟨1, by decide⟩)

/-- Cost model charging 1 for binary De Morgan gates (`and`, `or`) and 0 for all other gates. -/
def deMorganCost : OperationCost signature
  | .and | .or => 1
  | .false | .true | .id | .not | .xor | .equiv => 0

/-- Cost model charging 1 for binary XOR/EQUIV gates (`xor`, `equiv`) and 0 for all other gates. -/
def xorCost : OperationCost signature
  | .xor | .equiv => 1
  | .false | .true | .id | .not | .and | .or => 0

/-- Cost model charging 1 for all binary gates (`and`, `or`, `xor`, `equiv`). -/
def binaryCost : OperationCost signature
  | .and | .or | .xor | .equiv => 1
  | .false | .true | .id | .not => 0

/-- Whether an operation is in the De Morgan fragment (`false`, `true`, `id`, `not`, `and`, `or`). -/
def isDeMorgan : Op → Bool
  | .false | .true | .id | .not | .and | .or => true
  | .xor | .equiv => false

/-! ### Fan-out of circuit gates -/

section FanOut

variable {σ : Signature} {n m : Nat}

/-- The number of arguments of a gate that are equal to gate `g`. -/
def argUses {t : Nat} (line : Line σ n t) (g : Fin t) : Nat :=
  (Finset.univ.filter fun a => line.wires a = Wire.gate g).card

/-- The number of argument slots of the program's gates that read gate `g`. -/
def slotUses : {t : Nat} → Program σ n t → Fin t → Nat
  | _, .empty => Fin.elim0
  | _, .gate p line => Fin.lastCases 0 fun g => slotUses p g + argUses line g

/-- The fan-out of gate `g` of a circuit. -/
def gateFanOut (c : Circuit σ n m) (g : Fin c.size) : Nat :=
  slotUses c.program g + (Finset.univ.filter fun o => c.outputs o = Wire.gate g).card

/-- The number of gates of a circuit whose fan-out is at least two. -/
def sharedGateCount (c : Circuit σ n m) : Nat :=
  (Finset.univ.filter fun g => 2 ≤ gateFanOut c g).card

@[simp] theorem slotUses_gate_last {t : Nat} (p : Program σ n t) (line : Line σ n t) :
    slotUses (p.gate line) (Fin.last t) = 0 := by
  simp [slotUses]

@[simp] theorem slotUses_gate_castSucc {t : Nat} (p : Program σ n t) (line : Line σ n t)
    (g : Fin t) : slotUses (p.gate line) g.castSucc = slotUses p g + argUses line g := by
  simp [slotUses]

/-- The number of gates of `p` whose fan-out is at least two when gate `g` is read `u g` more
times. -/
def sharedCount {t : Nat} (p : Program σ n t) (u : Fin t → Nat) : Nat :=
  (Finset.univ.filter fun g => 2 ≤ slotUses p g + u g).card

theorem sharedGateCount_eq (c : Circuit σ n m) :
    sharedGateCount c = sharedCount c.program
      fun g => (Finset.univ.filter fun o => c.outputs o = Wire.gate g).card := rfl

theorem sharedCount_gate {t : Nat} (p : Program σ n t) (line : Line σ n t)
    (u : Fin (t + 1) → Nat) :
    sharedCount (p.gate line) u = (if 2 ≤ u (Fin.last t) then 1 else 0) +
      sharedCount p fun g => u g.castSucc + argUses line g := by
  rw [sharedCount, sharedCount, Finset.card_filter, Finset.card_filter, Fin.sum_univ_castSucc,
    add_comm]
  simp only [slotUses_gate_last, slotUses_gate_castSucc, zero_add]
  congr 1
  refine Finset.sum_congr rfl fun g _ => ?_
  split_ifs <;> omega

end FanOut

/-! ### Converting extended-basis circuits into `SharedProgram`s -/

section ExtendedGates

variable {n t : Nat}

/-- Formula for a De Morgan gate (or placeholder constant on `.xor`/`.equiv`, which are expanded via
`xorGadget`/`equivGadget`). -/
def lineFormula : Line signature n t → Formula (n + t)
  | ⟨.false, _⟩ => .const false
  | ⟨.true, _⟩ => .const true
  | ⟨.id, w⟩ => .lit (w ⟨0, by decide⟩).index true
  | ⟨.not, w⟩ => .lit (w ⟨0, by decide⟩).index false
  | ⟨.and, w⟩ => .and (.lit (w ⟨0, by decide⟩).index true) (.lit (w ⟨1, by decide⟩).index true)
  | ⟨.or, w⟩ => .or (.lit (w ⟨0, by decide⟩).index true) (.lit (w ⟨1, by decide⟩).index true)
  | ⟨.xor, _⟩ => .const false
  | ⟨.equiv, _⟩ => .const true

/-- The values of the inputs and gates of an extended-basis program, numbered by `Wire.index`. -/
def wireValues (p : Program signature n t) (x : Fin n → Bool) : Fin (n + t) → Bool :=
  Fin.append x (p.eval interpretation x)

theorem append_index (x : Fin n → Bool) (vals : Fin t → Bool) (w : Wire n t) :
    Fin.append x vals w.index = Wire.elim x vals w := by
  cases w <;> simp [Fin.append_left, Fin.append_right]

theorem eval_lineFormula_of_isDeMorgan (line : Line signature n t) (h : isDeMorgan line.op = true)
    (x : Fin n → Bool) (vals : Fin t → Bool) :
    (lineFormula line).eval (Fin.append x vals) = line.eval interpretation x vals := by
  obtain ⟨op, w⟩ := line
  cases op <;> simp [isDeMorgan, lineFormula, Line.eval, interpretation, append_index] at h ⊢ <;>
    rfl

theorem inputLeaves_lineFormula_le (line : Line signature n t) :
    (lineFormula line).inputLeaves (n + t) ≤ deMorganCost line.op + 1 := by
  obtain ⟨op, w⟩ := line
  cases op <;> simp only [lineFormula, Formula.inputLeaves, deMorganCost] <;> (try split_ifs) <;>
    omega

theorem index_val_eq_iff (w : Wire n t) (g : Fin t) :
    w.index.val = n + g.val ↔ w = Wire.gate g := by
  cases w with
  | input i => simp; omega
  | gate g' => simp [Fin.ext_iff]

theorem occ_lineFormula_le (line : Line signature n t) (g : Fin t) :
    Formula.occ (n + g.val) (lineFormula line) ≤ argUses line g := by
  obtain ⟨op, w⟩ := line
  rw [argUses, Finset.card_filter]
  cases op with
  | false | true | xor | equiv => simp [lineFormula, Formula.occ]
  | id =>
    refine le_trans ?_ (Finset.single_le_sum (fun _ _ => Nat.zero_le _)
      (Finset.mem_univ (⟨0, by decide⟩ : Fin (arity .id))))
    simp only [lineFormula, Formula.occ, index_val_eq_iff]
    split_ifs <;> simp_all
  | not =>
    refine le_trans ?_ (Finset.single_le_sum (fun _ _ => Nat.zero_le _)
      (Finset.mem_univ (⟨0, by decide⟩ : Fin (arity .not))))
    simp only [lineFormula, Formula.occ, index_val_eq_iff]
    split_ifs <;> simp_all
  | and =>
    have hne : (⟨0, by decide⟩ : Fin (arity .and)) ≠ ⟨1, by decide⟩ := by decide
    refine le_trans ?_ (Finset.sum_le_sum_of_subset (Finset.subset_univ {⟨0, by decide⟩,
      (⟨1, by decide⟩ : Fin (arity .and))}))
    rw [Finset.sum_pair hne]
    simp only [lineFormula, Formula.occ, index_val_eq_iff]
    split_ifs <;> simp_all
  | or =>
    have hne : (⟨0, by decide⟩ : Fin (arity .or)) ≠ ⟨1, by decide⟩ := by decide
    refine le_trans ?_ (Finset.sum_le_sum_of_subset (Finset.subset_univ {⟨0, by decide⟩,
      (⟨1, by decide⟩ : Fin (arity .or))}))
    rw [Finset.sum_pair hne]
    simp only [lineFormula, Formula.occ, index_val_eq_iff]
    split_ifs <;> simp_all

theorem occ_two_wires_le (op : Op) (ha : arity op = 2) (w : Fin (arity op) → Wire n t) (g : Fin t) :
    (if (w ⟨0, by omega⟩).index.val = n + g.val then 1 else 0) +
      (if (w ⟨1, by omega⟩).index.val = n + g.val then 1 else 0) ≤
      argUses (σ := signature) ⟨op, w⟩ g := by
  rw [argUses, Finset.card_filter]
  have hne : (⟨0, by omega⟩ : Fin (arity op)) ≠ ⟨1, by omega⟩ := by simp
  refine le_trans ?_ (Finset.sum_le_sum_of_subset (Finset.subset_univ {⟨0, by omega⟩,
    (⟨1, by omega⟩ : Fin (arity op))}))
  rw [Finset.sum_pair hne]
  simp only [index_val_eq_iff]
  split_ifs <;> simp_all

theorem eval_gate (p : Program signature n t) (line : Line signature n t)
    (x : Fin n → Bool) :
    (p.gate line).eval interpretation x =
      Fin.snoc (p.eval interpretation x)
        (line.eval interpretation x (p.eval interpretation x)) := by
  funext g
  refine Fin.lastCases ?_ (fun g => ?_) g
  · rw [Program.eval_gate_last, Fin.snoc_last]
  · rw [Program.eval_gate_castSucc, Fin.snoc_castSucc]

theorem wireValues_gate (p : Program signature n t) (line : Line signature n t)
    (x : Fin n → Bool) :
    wireValues (p.gate line) x =
      Fin.snoc (wireValues p x) (line.eval interpretation x (p.eval interpretation x)) := by
  rw [wireValues, eval_gate, Fin.append_snoc, wireValues]

theorem wireValues_empty (x : Fin n → Bool) : wireValues (.empty : Program _ n 0) x = x := by
  funext i
  change Fin.append x Fin.elim0 i = x i
  rw [Fin.append_elim0]
  rfl

/-- Expand one binary XOR or EQUIV gate at position `N = n + t` into two shared wire steps and
substitute `ψ` (`xorGadget` or `equivGadget`) for variable `N`. -/
def expandBinaryGadget {N j : Nat} (i₀ i₁ : Fin N) (ψ : Formula (N + 2))
    (Q : SharedProgram (N + 1) j) : SharedProgram N (j + 2) :=
  .share (.lit i₀ true) (.share (.lit i₁.castSucc true) (SharedProgram.liftSubst ψ (d := 0) Q))

theorem eval_expandBinaryGadget {N j : Nat} (i₀ i₁ : Fin N) (ψ : Formula (N + 2))
    (Q : SharedProgram (N + 1) j) (y : Fin N → Bool) :
    (expandBinaryGadget i₀ i₁ ψ Q).eval y =
      Q.eval (Fin.snoc y (ψ.eval (Fin.snoc (Fin.snoc y (y i₀)) (y i₁)))) := by
  unfold expandBinaryGadget
  rw [SharedProgram.eval_share, SharedProgram.eval_share]
  have h₀ : (Formula.lit i₀ true).eval y = y i₀ := by simp [Formula.eval]
  have h₁ : (Formula.lit i₁.castSucc true).eval (Fin.snoc y (y i₀)) = y i₁ := by
    simp [Formula.eval]
  rw [h₀, h₁, ← insertVal2_zero y, SharedProgram.eval_liftSubst ψ (d := 0) Q y (y i₀) (y i₁)]
  simp only [insertVal_zero, insertVal2_zero]
  rfl

theorem snoc_snoc_penult {N : Nat} (y : Fin N → Bool) (b₀ b₁ : Bool) :
    Fin.snoc (α := fun _ => Bool) (Fin.snoc (α := fun _ => Bool) y b₀) b₁
      ⟨N, by omega⟩ = b₀ := by
  change Fin.snoc (α := fun _ => Bool) (Fin.snoc (α := fun _ => Bool) y b₀) b₁
    (Fin.castSucc (Fin.last N)) = b₀
  rw [Fin.snoc_castSucc, Fin.snoc_last]

theorem snoc_snoc_ult {N : Nat} (y : Fin N → Bool) (b₀ b₁ : Bool) :
    Fin.snoc (α := fun _ => Bool) (Fin.snoc (α := fun _ => Bool) y b₀) b₁
      ⟨N + 1, by omega⟩ = b₁ := by
  change Fin.snoc (α := fun _ => Bool) (Fin.snoc (α := fun _ => Bool) y b₀) b₁
    (Fin.last (N + 1)) = b₁
  rw [Fin.snoc_last]

theorem inputLeaves_expandBinaryGadget {N j : Nat} (i₀ i₁ : Fin N) (ψ : Formula (N + 2))
    (hψ : ψ.inputLeaves N = 0) (Q : SharedProgram (N + 1) j) :
    (expandBinaryGadget i₀ i₁ ψ Q).inputLeaves N = 2 + Q.inputLeaves N := by
  unfold expandBinaryGadget
  rw [SharedProgram.inputLeaves_share, SharedProgram.inputLeaves_share,
    SharedProgram.inputLeaves_liftSubst ψ hψ (d := 0) Q]
  have h₀ : (Formula.lit i₀ true).inputLeaves N = 1 := by simp [Formula.inputLeaves, i₀.isLt]
  have h₁ : (Formula.lit i₁.castSucc true).inputLeaves N = 1 := by
    simp [Formula.inputLeaves, i₁.isLt]
  omega

theorem occ_expandBinaryGadget {N j : Nat} (i₀ i₁ : Fin N) (ψ : Formula (N + 2))
    (hψ : ψ.inputLeaves N = 0) (Q : SharedProgram (N + 1) j) {w : Nat} (hw : w < N) :
    SharedProgram.occ w (expandBinaryGadget i₀ i₁ ψ Q) =
      (if i₀.val = w then 1 else 0) + (if i₁.val = w then 1 else 0) + SharedProgram.occ w Q := by
  unfold expandBinaryGadget
  rw [SharedProgram.occ_share, SharedProgram.occ_share,
    SharedProgram.occ_liftSubst ψ hψ hw (d := 0) Q]
  simp only [Formula.occ, Fin.val_castSucc]
  omega

end ExtendedGates

/-- Build a `SharedProgram` from the last gate of an extended-basis program down, tracking the
number of shared steps and `inputLeaves (n + t)`. -/
theorem exists_sharedProgram_of_program {n : Nat} (f : Cslib.BooleanFunction n) :
    ∀ {t : Nat} (p : Program signature n t) (u : Fin t → Nat) {j : Nat}
      (Q : SharedProgram (n + t) j),
      (∀ x, Q.eval (wireValues p x) = f x) → (∀ g : Fin t, SharedProgram.occ (n + g.val) Q ≤ u g) →
      ∃ K, ∃ P : SharedProgram n K,
        K ≤ j + sharedCount p u + 2 * p.cost xorCost ∧
        P.Computes f ∧
        P.inputLeaves n ≤
          Q.inputLeaves (n + t) + p.cost deMorganCost + sharedCount p u + 2 * p.cost xorCost
  | _, .empty, _, j, Q, hQ, _ =>
    ⟨j, Q, by simp, fun x => by simpa [wireValues_empty] using hQ x, by simp⟩
  | _, .gate (gateCount := t) p line, u, j, Q, hQ, hocc => by
    have hcount := sharedCount_gate p line u
    have hcost_dm : (p.gate line).cost deMorganCost =
        p.cost deMorganCost + deMorganCost line.op := Program.cost_gate _ _ _
    have hcost_xor : (p.gate line).cost xorCost =
        p.cost xorCost + xorCost line.op := Program.cost_gate _ _ _
    have hQsucc : Q.inputLeaves (n + (t + 1)) =
        Q.inputLeaves (n + t) + SharedProgram.occ (n + t) Q := by
      simpa [Nat.add_assoc] using SharedProgram.inputLeaves_succ (n + t) Q
    by_cases hdm : isDeMorgan line.op = true
    · have hxor0 : xorCost line.op = 0 := by
        obtain ⟨op, _⟩ := line
        cases op <;> simp [isDeMorgan, xorCost] at hdm ⊢
      have hφocc := occ_lineFormula_le line
      have hφil := inputLeaves_lineFormula_le line
      have hlast : SharedProgram.occ (n + t) Q ≤ u (Fin.last t) := hocc (Fin.last t)
      by_cases hL : 2 ≤ u (Fin.last t)
      · obtain ⟨K, P, hK, hP, hil⟩ := exists_sharedProgram_of_program f p
          (fun g => u g.castSucc + argUses line g) (SharedProgram.share (lineFormula line) Q)
          (fun x => by
            rw [SharedProgram.eval_share, wireValues, eval_lineFormula_of_isDeMorgan line hdm,
              ← wireValues, ← wireValues_gate]
            exact hQ x)
          (fun g => by
            have h₁ : SharedProgram.occ (n + g.val) Q ≤ u g.castSucc := hocc g.castSucc
            have h₂ := hφocc g
            rw [SharedProgram.occ_share]
            omega)
        refine ⟨K, P, ?_, hP, ?_⟩
        · rw [hcount, ite_eq_left hL, hcost_xor, hxor0]
          omega
        · rw [SharedProgram.inputLeaves_share] at hil
          rw [hcount, ite_eq_left hL, hcost_dm, hcost_xor, hxor0, hQsucc]
          omega
      · have hL₁ : SharedProgram.occ (n + t) Q ≤ 1 := by omega
        obtain ⟨K, P, hK, hP, hil⟩ := exists_sharedProgram_of_program f p
          (fun g => u g.castSucc + argUses line g)
          (SharedProgram.substVar (lineFormula line) (d := 0) Q)
          (fun x => by
            rw [SharedProgram.eval_substVar, insertVal_zero]
            change Q.eval (Fin.snoc (wireValues p x)
              ((lineFormula line).eval (wireValues p x))) = _
            rw [wireValues, eval_lineFormula_of_isDeMorgan line hdm, ← wireValues,
              ← wireValues_gate]
            exact hQ x)
          (fun g => by
            rw [SharedProgram.occ_substVar _ (by omega)]
            have h₁ : SharedProgram.occ (n + g.val) Q ≤ u g.castSucc := hocc g.castSucc
            have h₂ := hφocc g
            have h₃ : SharedProgram.occ (n + t) Q *
                Formula.occ (n + g.val) (lineFormula line) ≤ argUses line g :=
              le_trans ((Nat.mul_le_mul_right _ hL₁).trans_eq (one_mul _)) h₂
            omega)
        refine ⟨K, P, ?_, hP, ?_⟩
        · rw [hcount, ite_eq_right hL, hcost_xor, hxor0]
          omega
        · rw [SharedProgram.inputLeaves_substVar] at hil
          have h₃ : SharedProgram.occ (n + t) Q * (lineFormula line).inputLeaves (n + t) ≤
              SharedProgram.occ (n + t) Q + deMorganCost line.op := by
            have := Nat.mul_le_mul_left (SharedProgram.occ (n + t) Q) hφil
            have := Nat.mul_le_mul_right (deMorganCost line.op) hL₁
            nlinarith
          rw [hcount, ite_eq_right hL, hcost_dm, hcost_xor, hxor0, hQsucc]
          omega
    · rcases line with ⟨op, w⟩
      cases op with
      | false | true | id | not | and | or => simp [isDeMorgan] at hdm
      | xor =>
        let z₁ : Fin (n + t + 2) := ⟨n + t, by omega⟩
        let z₂ : Fin (n + t + 2) := ⟨n + t + 1, by omega⟩
        let ψ : Formula (n + t + 2) := xorGadget z₁ z₂
        have hψ : ψ.inputLeaves (n + t) = 0 :=
          inputLeaves_xorGadget_of_ge (z₁ := z₁) (z₂ := z₂) le_rfl (Nat.le_succ (n + t))
        let w₀ := w ⟨0, by decide⟩
        let w₁ := w ⟨1, by decide⟩
        obtain ⟨K, P, hK, hP, hil⟩ := exists_sharedProgram_of_program f p
          (fun g => u g.castSucc + argUses (σ := signature) ⟨.xor, w⟩ g)
          (expandBinaryGadget w₀.index w₁.index ψ Q)
          (fun x => by
            rw [eval_expandBinaryGadget]
            have hψeval : ψ.eval (Fin.snoc (Fin.snoc (wireValues p x) (wireValues p x w₀.index))
                (wireValues p x w₁.index)) =
                (⟨.xor, w⟩ : Line signature n t).eval interpretation x
                  (p.eval interpretation x) := by
              change (xorGadget z₁ z₂).eval _ = _
              rw [eval_xorGadget, snoc_snoc_penult, snoc_snoc_ult]
              simp only [Line.eval, interpretation, wireValues, append_index, w₀, w₁]
              rfl
            rw [hψeval, ← wireValues_gate]
            exact hQ x)
          (fun g => by
            rw [occ_expandBinaryGadget _ _ ψ hψ Q (by omega)]
            have h₁ : SharedProgram.occ (n + g.val) Q ≤ u g.castSucc := hocc g.castSucc
            have h₂ := occ_two_wires_le .xor rfl w g
            dsimp only [w₀, w₁]
            omega)
        refine ⟨K, P, ?_, hP, ?_⟩
        · rw [hcount, hcost_xor]
          simp only [xorCost]
          split_ifs <;> omega
        · rw [inputLeaves_expandBinaryGadget _ _ ψ hψ Q] at hil
          rw [hcount, hcost_dm, hcost_xor, hQsucc]
          simp only [deMorganCost, xorCost]
          split_ifs <;> omega
      | equiv =>
        let z₁ : Fin (n + t + 2) := ⟨n + t, by omega⟩
        let z₂ : Fin (n + t + 2) := ⟨n + t + 1, by omega⟩
        let ψ : Formula (n + t + 2) := equivGadget z₁ z₂
        have hψ : ψ.inputLeaves (n + t) = 0 :=
          inputLeaves_equivGadget_of_ge (z₁ := z₁) (z₂ := z₂) le_rfl (Nat.le_succ (n + t))
        let w₀ := w ⟨0, by decide⟩
        let w₁ := w ⟨1, by decide⟩
        obtain ⟨K, P, hK, hP, hil⟩ := exists_sharedProgram_of_program f p
          (fun g => u g.castSucc + argUses (σ := signature) ⟨.equiv, w⟩ g)
          (expandBinaryGadget w₀.index w₁.index ψ Q)
          (fun x => by
            rw [eval_expandBinaryGadget]
            have hψeval : ψ.eval (Fin.snoc (Fin.snoc (wireValues p x) (wireValues p x w₀.index))
                (wireValues p x w₁.index)) =
                (⟨.equiv, w⟩ : Line signature n t).eval interpretation x
                  (p.eval interpretation x) := by
              change (equivGadget z₁ z₂).eval _ = _
              rw [eval_equivGadget, snoc_snoc_penult, snoc_snoc_ult]
              simp only [Line.eval, interpretation, wireValues, append_index, w₀, w₁]
              rfl
            rw [hψeval, ← wireValues_gate]
            exact hQ x)
          (fun g => by
            rw [occ_expandBinaryGadget _ _ ψ hψ Q (by omega)]
            have h₁ : SharedProgram.occ (n + g.val) Q ≤ u g.castSucc := hocc g.castSucc
            have h₂ := occ_two_wires_le .equiv rfl w g
            dsimp only [w₀, w₁]
            omega)
        refine ⟨K, P, ?_, hP, ?_⟩
        · rw [hcount, hcost_xor]
          simp only [xorCost]
          split_ifs <;> omega
        · rw [inputLeaves_expandBinaryGadget _ _ ψ hψ Q] at hil
          rw [hcount, hcost_dm, hcost_xor, hQsucc]
          simp only [deMorganCost, xorCost]
          split_ifs <;> omega

/-- **Extended-basis circuits as programs with shared gates.** Every single-output circuit over the
extended De Morgan + XOR/EQUIV basis computing `f` with `k` shared gates and `r` XOR/EQUIV gates
yields a `SharedProgram n K` computing `f` with `K ≤ k + 2r` and
`P.inputLeaves n ≤ c_DM + k + 2r + 1`. -/
theorem exists_sharedProgram_of_circuit {n : Nat} (c : Circuit signature n 1)
    {f : Cslib.BooleanFunction n} (hc : c.ComputesWith interpretation fun x _ => f x) :
    ∃ K, ∃ P : SharedProgram n K,
      K ≤ sharedGateCount c + 2 * c.cost xorCost ∧
      P.Computes f ∧
      P.inputLeaves n ≤
        c.cost deMorganCost + sharedGateCount c + 2 * c.cost xorCost + 1 := by
  obtain ⟨K, P, hK, hP, hil⟩ := exists_sharedProgram_of_program f c.program
    (fun g => (Finset.univ.filter fun o => c.outputs o = Wire.gate g).card) (j := 0)
    (SharedProgram.output (.lit (c.outputs 0).index true))
    (fun x => by
      have := congrFun (hc x) 0
      simp only [Circuit.eval, Function.comp_apply, Program.trace] at this
      simp [wireValues, append_index, this])
    (fun g => by
      simp only [SharedProgram.occ, Formula.occ]
      split_ifs with h
      · exact Finset.card_pos.mpr ⟨0, by simpa using (index_val_eq_iff _ g).mp h⟩
      · exact Nat.zero_le _)
  have hinit : (SharedProgram.output (.lit (c.outputs 0).index true)).inputLeaves (n + c.size) =
      1 := by
    simp [SharedProgram.inputLeaves, Formula.inputLeaves, (c.outputs 0).index.isLt]
  rw [hinit] at hil
  simp only [Circuit.cost, sharedGateCount_eq, zero_add] at hK hil ⊢
  exact ⟨K, P, hK, hP, by omega⟩

/-! ### Khrapchenko, parity, threshold, and majority lower bounds -/

variable {n : Nat}

/-- **Khrapchenko bound for circuits with `k` shared gates and `r` XOR/EQUIV gates.** -/
theorem khrapchenkoBound_of_circuit {k r : Nat} (c : Circuit signature n 1)
    {f : Cslib.BooleanFunction n} (hc : c.ComputesWith interpretation fun x _ => f x)
    (hk : sharedGateCount c ≤ k) (hr : c.cost xorCost ≤ r) :
    KhrapchenkoBound f ((k + 2 * r + 1) * (c.cost deMorganCost + k + 2 * r + 1)) := by
  obtain ⟨K, P, hK, hP, hil⟩ := exists_sharedProgram_of_circuit c hc
  intro A B hA hB
  refine (SharedProgram.khrapchenkoBound hP A B hA hB).trans ?_
  exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (Nat.mul_le_mul (by omega) (by omega)))

/-- **Rectangle edge bound for circuits with `k` shared gates and `r` XOR/EQUIV gates.** -/
theorem sq_card_edges_le_cost {k r : Nat} (c : Circuit signature n 1)
    {f : Cslib.BooleanFunction n} (hc : c.ComputesWith interpretation fun x _ => f x)
    (hk : sharedGateCount c ≤ k) (hr : c.cost xorCost ≤ r)
    (A B : Finset (Fin n → Bool)) (hA : ∀ x ∈ A, f x = true) (hB : ∀ y ∈ B, f y = false) :
    (edges A B).card ^ 2 ≤
      (k + 2 * r + 1) * (c.cost deMorganCost + k + 2 * r + 1) * A.card * B.card :=
  khrapchenkoBound_of_circuit c hc hk hr A B hA hB

/-- **Parity in circuits with `k` shared gates and `r` XOR/EQUIV gates.** -/
theorem parity_sq_le_cost [NeZero n] {k r : Nat} (c : Circuit signature n 1)
    (computes : c.ComputesWith interpretation (GateElimination.Xor.parityTarget n))
    (hk : sharedGateCount c ≤ k) (hr : c.cost xorCost ≤ r) :
    n ^ 2 ≤ (k + 2 * r + 1) * (c.cost deMorganCost + k + 2 * r + 1) :=
  (khrapchenkoBound_of_circuit c computes hk hr).parity_sq_le

/-- **Superlinear De Morgan cost for parity with few shared gates and few XOR/EQUIV gates.** -/
theorem mul_le_cost_of_parity {k r C : Nat} (hkrn : (k + 2 * r + 1) * (C + 1) ≤ n)
    (c : Circuit signature n 1)
    (computes : c.ComputesWith interpretation (GateElimination.Xor.parityTarget n))
    (hk : sharedGateCount c ≤ k) (hr : c.cost xorCost ≤ r) :
    C * n ≤ c.cost deMorganCost := by
  have hkr : k + 2 * r + 1 ≤ n := le_trans (Nat.le_mul_of_pos_right _ (Nat.succ_pos C)) hkrn
  have : NeZero n := ⟨by omega⟩
  have h : (k + 2 * r + 1) * (n * (C + 1)) ≤
      (k + 2 * r + 1) * (c.cost deMorganCost + k + 2 * r + 1) :=
    calc (k + 2 * r + 1) * (n * (C + 1)) = n * ((k + 2 * r + 1) * (C + 1)) := by ring
      _ ≤ n * n := Nat.mul_le_mul_left _ hkrn
      _ = n ^ 2 := (sq n).symm
      _ ≤ _ := parity_sq_le_cost c computes hk hr
  have h' := Nat.le_of_mul_le_mul_left h (Nat.succ_pos (k + 2 * r))
  nlinarith

alias mul_le_cost := mul_le_cost_of_parity

/-- Superlinearity when two parameters `k n = o(n)` and `r n = o(n)` control the linear factor. -/
theorem isLittleO_of_forall_mul_le_two {k r s : ℕ → ℕ} {a b d : ℕ}
    (hk : (fun n => (k n : ℝ)) =o[Filter.atTop] fun n : ℕ => (n : ℝ))
    (hr : (fun n => (r n : ℝ)) =o[Filter.atTop] fun n : ℕ => (n : ℝ))
    (h : ∀ n C, (a * k n + b * r n + d + 1) * (C + 1) ≤ n → C * n ≤ s n) :
    (fun n : ℕ => (n : ℝ)) =o[Filter.atTop] fun n => (s n : ℝ) := by
  rw [Asymptotics.isLittleO_iff]
  intro c hc
  obtain ⟨C, hC⟩ := exists_nat_ge (1 / c)
  have hεk : (0 : ℝ) < 1 / (4 * (a + 1) * (C + 1)) := by positivity
  have hεr : (0 : ℝ) < 1 / (4 * (b + 1) * (C + 1)) := by positivity
  filter_upwards [hk.bound hεk, hr.bound hεr,
    Filter.eventually_ge_atTop (4 * (d + 1) * (C + 1))] with n hkn hrn hn
  simp only [Real.norm_natCast] at hkn hrn ⊢
  have hkn' : 4 * (a + 1) * (C + 1) * k n ≤ n := by
    have h1 : ((4 * (a + 1) * (C + 1) * k n : ℕ) : ℝ) ≤ n :=
      calc ((4 * (a + 1) * (C + 1) * k n : ℕ) : ℝ) =
            4 * (a + 1) * (C + 1) * (k n : ℝ) := by push_cast; ring
        _ ≤ 4 * (a + 1) * (C + 1) * (1 / (4 * (a + 1) * (C + 1)) * n) := by gcongr
        _ = n := by field_simp
    exact_mod_cast h1
  have hrn' : 4 * (b + 1) * (C + 1) * r n ≤ n := by
    have h2 : ((4 * (b + 1) * (C + 1) * r n : ℕ) : ℝ) ≤ n :=
      calc ((4 * (b + 1) * (C + 1) * r n : ℕ) : ℝ) =
            4 * (b + 1) * (C + 1) * (r n : ℝ) := by push_cast; ring
        _ ≤ 4 * (b + 1) * (C + 1) * (1 / (4 * (b + 1) * (C + 1)) * n) := by gcongr
        _ = n := by field_simp
    exact_mod_cast h2
  have hs : (C * n : ℝ) ≤ s n := by
    exact_mod_cast h n C (by nlinarith)
  calc (n : ℝ) = c * (1 / c * n) := by field_simp
    _ ≤ c * (C * n) := by gcongr
    _ ≤ c * s n := by gcongr

/-- **Parity needs superlinear De Morgan gates when `k(n) = o(n)` and `r(n) = o(n)`.** -/
theorem isLittleO_cost_of_parity {k r : ℕ → ℕ}
    (hk : (fun n => (k n : ℝ)) =o[Filter.atTop] fun n : ℕ => (n : ℝ))
    (hr : (fun n => (r n : ℝ)) =o[Filter.atTop] fun n : ℕ => (n : ℝ))
    (c : (n : ℕ) → Circuit signature n 1)
    (computes : ∀ n, (c n).ComputesWith interpretation (GateElimination.Xor.parityTarget n))
    (hshared : ∀ n, sharedGateCount (c n) ≤ k n)
    (hxor : ∀ n, (c n).cost xorCost ≤ r n) :
    (fun n : ℕ => (n : ℝ)) =o[Filter.atTop] fun n => ((c n).cost deMorganCost : ℝ) :=
  isLittleO_of_forall_mul_le_two (a := 1) (b := 2) (d := 0) hk hr fun n _ hkrn =>
    mul_le_cost_of_parity (by nlinarith) (c n) (computes n) (hshared n) (hxor n)

alias isLittleO_cost_of_xorBool := isLittleO_cost_of_parity

/-- Single-output circuit target for the `t`-threshold function on `n` bits. -/
abbrev thresholdTarget (n t : Nat) : Target Bool n 1 := fun x _ => threshold t x

/-- Single-output circuit target for the strict majority function on `n` bits. -/
abbrev majorityTarget (n : Nat) : Target Bool n 1 := fun x _ => majority x

/-- **Threshold functions in circuits with `k` shared gates and `r` XOR/EQUIV gates.** -/
theorem threshold_mul_le_cost {t k r : Nat} (ht : 1 ≤ t) (htn : t ≤ n)
    (c : Circuit signature n 1)
    (computes : c.ComputesWith interpretation (thresholdTarget n t))
    (hk : sharedGateCount c ≤ k) (hr : c.cost xorCost ≤ r) :
    (n + 1 - t) * t ≤ (k + 2 * r + 1) * (c.cost deMorganCost + k + 2 * r + 1) :=
  (khrapchenkoBound_of_circuit c computes hk hr).threshold_mul_le ht htn

/-- **Majority in circuits with `k` shared gates and `r` XOR/EQUIV gates.** -/
theorem majority_mul_le_cost {k r : Nat} (hn : 1 ≤ n)
    (c : Circuit signature n 1)
    (computes : c.ComputesWith interpretation (majorityTarget n))
    (hk : sharedGateCount c ≤ k) (hr : c.cost xorCost ≤ r) :
    (n - n / 2) * (n / 2 + 1) ≤ (k + 2 * r + 1) * (c.cost deMorganCost + k + 2 * r + 1) :=
  (khrapchenkoBound_of_circuit c computes hk hr).majority_mul_le hn

/-- **Odd-input majority in circuits with `k` shared gates and `r` XOR/EQUIV gates.** -/
theorem majority_sq_le_cost_of_odd {k r : Nat} (hodd : Odd n)
    (c : Circuit signature n 1)
    (computes : c.ComputesWith interpretation (majorityTarget n))
    (hk : sharedGateCount c ≤ k) (hr : c.cost xorCost ≤ r) :
    (n / 2 + 1) ^ 2 ≤ (k + 2 * r + 1) * (c.cost deMorganCost + k + 2 * r + 1) := by
  obtain ⟨m, rfl⟩ := hodd
  have hdiv : (2 * m + 1) / 2 = m := by omega
  have hsub : (2 * m + 1 - (2 * m + 1) / 2) * ((2 * m + 1) / 2 + 1) =
      ((2 * m + 1) / 2 + 1) ^ 2 := by
    rw [hdiv, sq]
    congr 1
    omega
  rw [← hsub]
  exact majority_mul_le_cost (by omega) c computes hk hr

/-- **Superlinear De Morgan cost for odd-input majority with few shared and XOR/EQUIV gates.** -/
theorem mul_le_cost_of_majority_odd {m k r C : Nat} (hkrm : (k + 2 * r + 1) * (C + 1) ≤ m)
    (c : Circuit signature (2 * m + 1) 1)
    (computes : c.ComputesWith interpretation (majorityTarget (2 * m + 1)))
    (hk : sharedGateCount c ≤ k) (hr : c.cost xorCost ≤ r) :
    C * m ≤ c.cost deMorganCost := by
  have hodd : Odd (2 * m + 1) := ⟨m, rfl⟩
  have hsq := majority_sq_le_cost_of_odd hodd c computes hk hr
  have hdiv : (2 * m + 1) / 2 + 1 = m + 1 := by omega
  rw [hdiv] at hsq
  have h : (k + 2 * r + 1) * ((m + 1) * (C + 1)) ≤
      (k + 2 * r + 1) * (c.cost deMorganCost + k + 2 * r + 1) :=
    calc (k + 2 * r + 1) * ((m + 1) * (C + 1)) = (m + 1) * ((k + 2 * r + 1) * (C + 1)) := by ring
      _ ≤ (m + 1) * (m + 1) := Nat.mul_le_mul_left _ (by omega)
      _ = (m + 1) ^ 2 := (sq (m + 1)).symm
      _ ≤ _ := hsq
  have h' := Nat.le_of_mul_le_mul_left h (Nat.succ_pos (k + 2 * r))
  nlinarith

/-- **Superlinear De Morgan cost for majority with few shared and XOR/EQUIV gates.** -/
theorem mul_le_cost_of_majority {k r C : Nat} (hkrn : 4 * (k + 2 * r + 1) * (C + 1) ≤ n)
    (c : Circuit signature n 1)
    (computes : c.ComputesWith interpretation (majorityTarget n))
    (hk : sharedGateCount c ≤ k) (hr : c.cost xorCost ≤ r) :
    C * n ≤ c.cost deMorganCost := by
  rcases Nat.eq_zero_or_pos C with rfl | hC
  · simp
  have hn1 : 1 ≤ n := by nlinarith
  have hmaj := majority_mul_le_cost hn1 c computes hk hr
  set h := (n + 1) / 2
  have hh1 : h ≤ n - n / 2 := by omega
  have hh2 : h ≤ n / 2 + 1 := by omega
  have hnh : n ≤ 2 * h := by omega
  have hkh : (k + 2 * r + 1) * (2 * C + 1) ≤ h := by nlinarith
  have h : (k + 2 * r + 1) * (h * (2 * C + 1)) ≤
      (k + 2 * r + 1) * (c.cost deMorganCost + k + 2 * r + 1) :=
    calc (k + 2 * r + 1) * (h * (2 * C + 1)) = h * ((k + 2 * r + 1) * (2 * C + 1)) := by ring
      _ ≤ h * h := Nat.mul_le_mul_left _ hkh
      _ ≤ (n - n / 2) * (n / 2 + 1) := Nat.mul_le_mul hh1 hh2
      _ ≤ _ := hmaj
  have h' := Nat.le_of_mul_le_mul_left h (Nat.succ_pos (k + 2 * r))
  nlinarith

/-- **Majority needs superlinear De Morgan gates when `k(n) = o(n)` and `r(n) = o(n)`.** -/
theorem isLittleO_cost_of_majority {k r : ℕ → ℕ}
    (hk : (fun n => (k n : ℝ)) =o[Filter.atTop] fun n : ℕ => (n : ℝ))
    (hr : (fun n => (r n : ℝ)) =o[Filter.atTop] fun n : ℕ => (n : ℝ))
    (c : (n : ℕ) → Circuit signature n 1)
    (computes : ∀ n, (c n).ComputesWith interpretation (majorityTarget n))
    (hshared : ∀ n, sharedGateCount (c n) ≤ k n)
    (hxor : ∀ n, (c n).cost xorCost ≤ r n) :
    (fun n : ℕ => (n : ℝ)) =o[Filter.atTop] fun n => ((c n).cost deMorganCost : ℝ) :=
  isLittleO_of_forall_mul_le_two (a := 4) (b := 8) (d := 3) hk hr fun n _ hkrn =>
    mul_le_cost_of_majority (by nlinarith) (c n) (computes n) (hshared n) (hxor n)

end KarchmerWigderson.Sharing
end KW
end Algebraic
