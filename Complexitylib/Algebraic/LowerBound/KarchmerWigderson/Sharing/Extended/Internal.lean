/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.KarchmerWigderson.Sharing.Circuit
public import Complexitylib.Algebraic.LowerBound.KarchmerWigderson.Sharing.Extended.Defs

/-!
# Internals: extended-basis circuits as programs with shared gates

Proof internals for `Complexitylib.Algebraic.LowerBound.KarchmerWigderson.Sharing.Extended`.
The occurrence counts `Formula.occ`/`SharedProgram.occ`, the substitution
`SharedProgram.substVar`, and the fan-out counts `argUses`/`sharedCount` are reused from
`Complexitylib.Algebraic.LowerBound.KarchmerWigderson.Sharing.Circuit`. This file adds:

* how input leaves change under `substVar` (`SharedProgram.inputLeaves_substVar`) and under the
  lifting substitution `SharedProgram.liftSubst`, which replaces a variable by a formula over two
  fresh shared values;
* the expansion `Extended.expandBinaryGadget` of an XOR or EQUIV gate into two shared values
  and a zero-input-leaf gadget;
* the construction `Extended.exists_sharedProgram_of_program`, which tracks the number of shared
  values and the input leaves while processing an extended-basis program from the last gate down;
* the two-parameter superlinearity criterion `isLittleO_of_forall_mul_le_two`.
-/

@[expose] public section

namespace Algebraic
namespace KW

/-! ### Inserting two values -/

section InsertVal2

variable {N : Nat}

/-- `Fin.snoc` on Boolean vectors, entry by entry. -/
private theorem snoc_apply {m : Nat} (y : Fin m → Bool) (g : Bool) (i : Fin (m + 1)) :
    Fin.snoc (α := fun _ => Bool) y g i = if h : i.val < m then y ⟨i.val, h⟩ else g := by
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp
  · simp

/-- Insert the two values `b₀, b₁` at positions `N, N + 1` of `y`, moving the later entries up by
two. -/
def insertVal2 {d : Nat} (y : Fin (N + d) → Bool) (b₀ b₁ : Bool) : Fin (N + 2 + d) → Bool :=
  fun i => if h : i.val < N then y ⟨i.val, by omega⟩
    else if _ : i.val = N then b₀
    else if _ : i.val = N + 1 then b₁
    else y ⟨i.val - 2, by omega⟩

/-- With no later entries, `insertVal2` appends the two values. -/
theorem insertVal2_zero (y : Fin N → Bool) (b₀ b₁ : Bool) :
    insertVal2 (d := 0) y b₀ b₁ = Fin.snoc (Fin.snoc y b₀) b₁ := by
  funext i
  simp only [insertVal2, snoc_apply]
  split_ifs <;> first | rfl | omega

/-- `insertVal2` commutes with appending a later entry. -/
theorem insertVal2_snoc {d : Nat} (y : Fin (N + d) → Bool) (g b₀ b₁ : Bool) :
    insertVal2 (d := d + 1) (Fin.snoc y g) b₀ b₁ = Fin.snoc (insertVal2 y b₀ b₁) g := by
  funext i
  simp only [insertVal2, snoc_apply, Nat.add_eq]
  split_ifs <;> first | rfl | omega

end InsertVal2

/-! ### Input leaves of formulas under substitution -/

namespace Formula

variable {N M : Nat}

@[simp] theorem inputLeaves_mapIndex_castLE (m : Nat) (h : N ≤ M) :
    ∀ F : Formula N, (F.mapIndex (Fin.castLE h)).inputLeaves m = F.inputLeaves m
  | lit _ _ => rfl
  | const _ => rfl
  | and l r => by
    simp [mapIndex, inputLeaves, inputLeaves_mapIndex_castLE m h l,
      inputLeaves_mapIndex_castLE m h r]
  | or l r => by
    simp [mapIndex, inputLeaves, inputLeaves_mapIndex_castLE m h l,
      inputLeaves_mapIndex_castLE m h r]

/-- Raising the input threshold from `m` to `m + 1` adds the leaves on variable `m`. -/
theorem inputLeaves_succ (m : Nat) :
    ∀ F : Formula N, F.inputLeaves (m + 1) = F.inputLeaves m + F.occ m
  | lit i _ => by
    simp only [inputLeaves, occ]
    split_ifs <;> omega
  | const _ => rfl
  | and l r => by
    simp only [inputLeaves, occ, inputLeaves_succ m l, inputLeaves_succ m r]
    omega
  | or l r => by
    simp only [inputLeaves, occ, inputLeaves_succ m l, inputLeaves_succ m r]
    omega

/-- A formula with no input leaves below `m` has no leaves on any variable `v < m`. -/
theorem occ_eq_zero_of_inputLeaves_eq_zero {m v : Nat} (hv : v < m) :
    ∀ {F : Formula N}, F.inputLeaves m = 0 → F.occ v = 0
  | lit i _, h => by
    simp only [inputLeaves, occ] at h ⊢
    split_ifs at h ⊢ <;> omega
  | const _, _ => rfl
  | and l r, h => by
    simp only [inputLeaves, Nat.add_eq_zero_iff] at h
    simp [occ, occ_eq_zero_of_inputLeaves_eq_zero hv h.1, occ_eq_zero_of_inputLeaves_eq_zero hv h.2]
  | or l r, h => by
    simp only [inputLeaves, Nat.add_eq_zero_iff] at h
    simp [occ, occ_eq_zero_of_inputLeaves_eq_zero hv h.1, occ_eq_zero_of_inputLeaves_eq_zero hv h.2]

theorem inputLeaves_subst_substVarMap (φ : Formula N) (d : Nat) :
    ∀ F : Formula (N + 1 + d),
      (F.subst (substVarMap φ d)).inputLeaves N = F.inputLeaves N + F.occ N * φ.inputLeaves N
  | lit i b => by
    have key : (substVarMap φ d i).inputLeaves N =
        (if i.val < N then 1 else 0) + (if i.val = N then 1 else 0) * φ.inputLeaves N := by
      unfold substVarMap
      split_ifs <;> simp [inputLeaves, inputLeaves_mapIndex_castLE] <;> omega
    cases b <;> simp [subst, inputLeaves, occ, key]
  | const _ => by simp [subst, inputLeaves, occ]
  | and l r => by
    simp only [subst, inputLeaves, occ,
      inputLeaves_subst_substVarMap φ d l, inputLeaves_subst_substVarMap φ d r]
    ring
  | or l r => by
    simp only [subst, inputLeaves, occ,
      inputLeaves_subst_substVarMap φ d l, inputLeaves_subst_substVarMap φ d r]
    ring

/-- The substitution behind `SharedProgram.liftSubst`: the variable `N` becomes
`ψ : Formula (N + 2)`, the variables below `N` are kept, and those above `N` move up by one to make
room for the two new shared variables `N` and `N + 1`. -/
def liftSubstMap (ψ : Formula (N + 2)) (d : Nat) (i : Fin (N + 1 + d)) : Formula (N + 2 + d) :=
  if h : i.val < N then lit ⟨i.val, by omega⟩ true
  else if _ : i.val = N then ψ.mapIndex (Fin.castLE (by omega))
  else lit ⟨i.val + 1, by omega⟩ true

theorem inputLeaves_subst_liftSubstMap (ψ : Formula (N + 2)) (hψ : ψ.inputLeaves N = 0) (d : Nat) :
    ∀ F : Formula (N + 1 + d),
      (F.subst (liftSubstMap ψ d)).inputLeaves N = F.inputLeaves N
  | lit i b => by
    have key : (liftSubstMap ψ d i).inputLeaves N = if i.val < N then 1 else 0 := by
      unfold liftSubstMap
      split_ifs <;> simp [inputLeaves, inputLeaves_mapIndex_castLE, hψ] <;> omega
    cases b <;> simp [subst, inputLeaves, key]
  | const _ => by simp [subst, inputLeaves]
  | and l r => by
    simp [subst, inputLeaves,
      inputLeaves_subst_liftSubstMap ψ hψ d l, inputLeaves_subst_liftSubstMap ψ hψ d r]
  | or l r => by
    simp [subst, inputLeaves,
      inputLeaves_subst_liftSubstMap ψ hψ d l, inputLeaves_subst_liftSubstMap ψ hψ d r]

theorem occ_subst_liftSubstMap (ψ : Formula (N + 2)) (hψ : ψ.inputLeaves N = 0) (d : Nat)
    {w : Nat} (hw : w < N) :
    ∀ F : Formula (N + 1 + d), (F.subst (liftSubstMap ψ d)).occ w = F.occ w
  | lit i b => by
    have hψw : ψ.occ w = 0 := occ_eq_zero_of_inputLeaves_eq_zero hw hψ
    have key : (liftSubstMap ψ d i).occ w = if i.val = w then 1 else 0 := by
      unfold liftSubstMap
      split_ifs <;> simp [occ, hψw] <;> omega
    cases b <;> simp [subst, occ, key]
  | const _ => by simp [subst, occ]
  | and l r => by
    simp [subst, occ, occ_subst_liftSubstMap ψ hψ d hw l, occ_subst_liftSubstMap ψ hψ d hw r]
  | or l r => by
    simp [subst, occ, occ_subst_liftSubstMap ψ hψ d hw l, occ_subst_liftSubstMap ψ hψ d hw r]

theorem eval_subst_liftSubstMap (ψ : Formula (N + 2)) (d : Nat) (F : Formula (N + 1 + d))
    (y : Fin (N + d) → Bool) (b₀ b₁ : Bool) :
    (F.subst (liftSubstMap ψ d)).eval (insertVal2 y b₀ b₁) =
      F.eval (insertVal y
        (ψ.eval (insertVal2 (d := 0) (fun j => y (Fin.castLE (by omega) j)) b₀ b₁))) := by
  rw [eval_subst]
  congr 1
  funext i
  unfold liftSubstMap insertVal
  split_ifs with h₁ h₂
  · simp [insertVal2, h₁]
  · rw [eval_mapIndex]
    rfl
  · simp only [eval, insertVal2]
    split_ifs <;> first | rfl | omega

end Formula

/-! ### Input leaves of programs under substitution -/

namespace SharedProgram

variable {N : Nat}

@[simp] theorem inputLeaves_output (m : Nat) (F : Formula N) :
    (output F).inputLeaves m = F.inputLeaves m := rfl

@[simp] theorem inputLeaves_share {k : Nat} (m : Nat) (G : Formula N)
    (P : SharedProgram (N + 1) k) :
    (share G P).inputLeaves m = G.inputLeaves m + P.inputLeaves m := rfl

/-- Raising the input threshold from `m` to `m + 1` adds the leaves on variable `m`. -/
theorem inputLeaves_succ (m : Nat) :
    ∀ {N k : Nat} (P : SharedProgram N k), P.inputLeaves (m + 1) = P.inputLeaves m + P.occ m
  | _, _, output F => Formula.inputLeaves_succ m F
  | _, _, share G P => by
    simp only [inputLeaves_share, occ_share, Formula.inputLeaves_succ m G, inputLeaves_succ m P]
    omega

theorem inputLeaves_substVar (φ : Formula N) :
    ∀ {d k : Nat} (P : SharedProgram (N + 1 + d) k),
      (substVar φ P).inputLeaves N = P.inputLeaves N + P.occ N * φ.inputLeaves N
  | d, _, output F => by
    rw [substVar]
    simp only [inputLeaves_output, occ_output, Formula.inputLeaves_subst_substVarMap]
  | d, _, share G P => by
    rw [substVar]
    simp only [inputLeaves_share, occ_share, Formula.inputLeaves_subst_substVarMap,
      inputLeaves_substVar φ (d := d + 1) P]
    ring

/-- Substitute `ψ : Formula (N + 2)` for variable `N` in a program reading `N + 1 + d` variables,
shifting variables above `N` up by one so the result reads `N + 2 + d` variables. -/
def liftSubst (ψ : Formula (N + 2)) :
    {d k : Nat} → SharedProgram (N + 1 + d) k → SharedProgram (N + 2 + d) k
  | d, _, output F => output (F.subst (Formula.liftSubstMap ψ d))
  | d, _, share G P => share (G.subst (Formula.liftSubstMap ψ d)) (liftSubst ψ (d := d + 1) P)

theorem eval_liftSubst (ψ : Formula (N + 2)) :
    ∀ {d k : Nat} (P : SharedProgram (N + 1 + d) k) (y : Fin (N + d) → Bool) (b₀ b₁ : Bool),
      (liftSubst ψ P).eval (insertVal2 y b₀ b₁) =
        P.eval (insertVal y
          (ψ.eval (insertVal2 (d := 0) (fun j => y (Fin.castLE (by omega) j)) b₀ b₁)))
  | d, _, output F, y, b₀, b₁ => by
    rw [liftSubst, eval_output, Formula.eval_subst_liftSubstMap, eval_output]
  | d, _, share G P, y, b₀, b₁ => by
    rw [liftSubst, eval_share, eval_share, ← insertVal2_snoc, eval_liftSubst ψ (d := d + 1) P,
      Formula.eval_subst_liftSubstMap]
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
  | d, _, output F => by
    rw [liftSubst, inputLeaves_output, Formula.inputLeaves_subst_liftSubstMap ψ hψ d,
      inputLeaves_output]
  | d, _, share G P => by
    rw [liftSubst, inputLeaves_share, Formula.inputLeaves_subst_liftSubstMap ψ hψ d,
      inputLeaves_liftSubst ψ hψ (d := d + 1) P, inputLeaves_share]

theorem occ_liftSubst (ψ : Formula (N + 2)) (hψ : ψ.inputLeaves N = 0) {w : Nat} (hw : w < N) :
    ∀ {d k : Nat} (P : SharedProgram (N + 1 + d) k), (liftSubst ψ P).occ w = P.occ w
  | d, _, output F => by
    rw [liftSubst, occ_output, Formula.occ_subst_liftSubstMap ψ hψ d hw, occ_output]
  | d, _, share G P => by
    rw [liftSubst, occ_share, Formula.occ_subst_liftSubstMap ψ hψ d hw,
      occ_liftSubst ψ hψ hw (d := d + 1) P, occ_share]

end SharedProgram

/-! ### Extended-basis gates as formulas -/

namespace Extended

section ExtendedGates

variable {n t : Nat}

/-- The formula of one De Morgan gate over the earlier wires, numbered by `Wire.index`. On the
`xor` and `equiv` gates it is a placeholder constant: those gates are expanded by
`expandBinaryGadget` instead. -/
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

theorem occ_lineFormula_le (line : Line signature n t) (g : Fin t) :
    (lineFormula line).occ (n + g.val) ≤ argUses line g := by
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

/-- The two arguments of a binary gate read gate `g` at most `argUses` times in total. -/
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

private theorem snoc_snoc_penult {N : Nat} (y : Fin N → Bool) (b₀ b₁ : Bool) :
    Fin.snoc (α := fun _ => Bool) (Fin.snoc (α := fun _ => Bool) y b₀) b₁
      ⟨N, by omega⟩ = b₀ := by
  change Fin.snoc (α := fun _ => Bool) (Fin.snoc (α := fun _ => Bool) y b₀) b₁
    (Fin.castSucc (Fin.last N)) = b₀
  rw [Fin.snoc_castSucc, Fin.snoc_last]

private theorem snoc_snoc_ult {N : Nat} (y : Fin N → Bool) (b₀ b₁ : Bool) :
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
    (expandBinaryGadget i₀ i₁ ψ Q).occ w =
      (if i₀.val = w then 1 else 0) + (if i₁.val = w then 1 else 0) + Q.occ w := by
  unfold expandBinaryGadget
  rw [SharedProgram.occ_share, SharedProgram.occ_share,
    SharedProgram.occ_liftSubst ψ hψ hw (d := 0) Q]
  simp only [Formula.occ, Fin.val_castSucc]
  omega

end ExtendedGates

/-! ### From extended-basis programs to programs with shared gates -/

/-- Build a `SharedProgram` from the last gate of an extended-basis program down, tracking the
number of shared steps and `inputLeaves (n + t)`. `Q` reads all wires of `p`, gate `g` occurring
at most `u g` times. A De Morgan gate of total fan-out at least two becomes a shared gate and any
other De Morgan gate is substituted; an XOR or EQUIV gate becomes two shared values (its
arguments) and a zero-input-leaf gadget, whatever its fan-out. -/
theorem exists_sharedProgram_of_program {n : Nat} (f : Cslib.BooleanFunction n) :
    ∀ {t : Nat} (p : Program signature n t) (u : Fin t → Nat) {j : Nat}
      (Q : SharedProgram (n + t) j),
      (∀ x, Q.eval (wireValues p x) = f x) → (∀ g : Fin t, Q.occ (n + g.val) ≤ u g) →
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
    have hQsucc : Q.inputLeaves (n + (t + 1)) = Q.inputLeaves (n + t) + Q.occ (n + t) := by
      simpa [Nat.add_assoc] using SharedProgram.inputLeaves_succ (n + t) Q
    by_cases hdm : isDeMorgan line.op = true
    · have hxor0 : xorCost line.op = 0 := by
        obtain ⟨op, _⟩ := line
        cases op <;> simp [isDeMorgan, xorCost] at hdm ⊢
      have hφocc := occ_lineFormula_le line
      have hφil := inputLeaves_lineFormula_le line
      have hlast : Q.occ (n + t) ≤ u (Fin.last t) := hocc (Fin.last t)
      by_cases hL : 2 ≤ u (Fin.last t)
      · obtain ⟨K, P, hK, hP, hil⟩ := exists_sharedProgram_of_program f p
          (fun g => u g.castSucc + argUses line g) (SharedProgram.share (lineFormula line) Q)
          (fun x => by
            rw [SharedProgram.eval_share, wireValues, eval_lineFormula_of_isDeMorgan line hdm,
              ← wireValues, ← wireValues_gate]
            exact hQ x)
          (fun g => by
            have h₁ : Q.occ (n + g.val) ≤ u g.castSucc := hocc g.castSucc
            have h₂ := hφocc g
            rw [SharedProgram.occ_share]
            omega)
        refine ⟨K, P, ?_, hP, ?_⟩
        · rw [hcount, ite_eq_left hL, hcost_xor, hxor0]
          omega
        · rw [SharedProgram.inputLeaves_share] at hil
          rw [hcount, ite_eq_left hL, hcost_dm, hcost_xor, hxor0, hQsucc]
          omega
      · have hL₁ : Q.occ (n + t) ≤ 1 := by omega
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
            have h₁ : Q.occ (n + g.val) ≤ u g.castSucc := hocc g.castSucc
            have h₂ := hφocc g
            have h₃ : Q.occ (n + t) * (lineFormula line).occ (n + g.val) ≤ argUses line g :=
              le_trans ((Nat.mul_le_mul_right _ hL₁).trans_eq (one_mul _)) h₂
            omega)
        refine ⟨K, P, ?_, hP, ?_⟩
        · rw [hcount, ite_eq_right hL, hcost_xor, hxor0]
          omega
        · rw [SharedProgram.inputLeaves_substVar] at hil
          have h₃ : Q.occ (n + t) * (lineFormula line).inputLeaves (n + t) ≤
              Q.occ (n + t) + deMorganCost line.op := by
            have := Nat.mul_le_mul_left (Q.occ (n + t)) hφil
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
        let ψ : Formula (n + t + 2) := Formula.xorGadget z₁ z₂
        have hψ : ψ.inputLeaves (n + t) = 0 :=
          Formula.inputLeaves_xorGadget_of_ge (z₁ := z₁) (z₂ := z₂) le_rfl (Nat.le_succ (n + t))
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
              change (Formula.xorGadget z₁ z₂).eval _ = _
              rw [Formula.eval_xorGadget, snoc_snoc_penult, snoc_snoc_ult]
              simp only [Line.eval, interpretation, wireValues, append_index, w₀, w₁]
              rfl
            rw [hψeval, ← wireValues_gate]
            exact hQ x)
          (fun g => by
            rw [occ_expandBinaryGadget _ _ ψ hψ Q (by omega)]
            have h₁ : Q.occ (n + g.val) ≤ u g.castSucc := hocc g.castSucc
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
        let ψ : Formula (n + t + 2) := Formula.equivGadget z₁ z₂
        have hψ : ψ.inputLeaves (n + t) = 0 :=
          Formula.inputLeaves_equivGadget_of_ge (z₁ := z₁) (z₂ := z₂) le_rfl (Nat.le_succ (n + t))
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
              change (Formula.equivGadget z₁ z₂).eval _ = _
              rw [Formula.eval_equivGadget, snoc_snoc_penult, snoc_snoc_ult]
              simp only [Line.eval, interpretation, wireValues, append_index, w₀, w₁]
              rfl
            rw [hψeval, ← wireValues_gate]
            exact hQ x)
          (fun g => by
            rw [occ_expandBinaryGadget _ _ ψ hψ Q (by omega)]
            have h₁ : Q.occ (n + g.val) ≤ u g.castSucc := hocc g.castSucc
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

end Extended

/-! ### Superlinearity with two sublinear parameters -/

/-- Superlinearity when two parameters `k n = o(n)` and `r n = o(n)` control the linear factor:
if `(a · k n + b · r n + d + 1) · (C + 1) ≤ n` forces `C · n ≤ s n` for every `n` and `C`, then
`n = o(s n)`. The one-parameter version is `isLittleO_of_forall_mul_le`. -/
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

end KW
end Algebraic
