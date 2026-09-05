/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/
module
public import Complexitylib.Classes.P.Cobham.Internal.ChoiceSim
public import Complexitylib.Classes.P.Cobham.Internal.PolyLen
public import Complexitylib.Classes.P.Cobham.Internal.StringOps

/-!
# Looping over the blocks of a string inside the algebra

Amplified acceptance is a majority vote over the blocks of a random seed. Both
that vote and the outer disjunction over shift blocks are limited recursions
over a *ruler* whose length is the iteration count: at the step whose tail is
`y`, the block index is `|y|`, so the block itself is cut out of the source
string by a `drop` of `|y| · |τ|` bits — a length `smash` produces — followed
by a `take` of `|τ|`. No state has to be threaded through the recursion.

## Main definitions

- `Cobham.blockAtIdx` — the `j`-th block of a string at a given width
- `Cobham.acceptCountAux` — unary count of blocks on which the path accepts
- `Cobham.majorityFlag` — the amplified majority verdict as a flag

## Main results

- `Cobham.acceptCountAux_length` — the count is the number of accepting blocks
- `Cobham.acceptCountAux_mem`, `Cobham.majorityFlag_mem` — both are in the
  algebra
-/

@[expose] public section

namespace Complexity

namespace Cobham

variable {k : ℕ}

/-- The `j`-th block of `s` at width `w`. -/
def blockAtIdx (w : ℕ) (s : List Bool) (j : ℕ) : List Bool := (s.drop (j * w)).take w

/-- The block of `s` selected by the ruler `idx` at the width of `τ`. -/
def blockOf (τ s idx : List Bool) : List Bool :=
  (s.drop (Complexity.smash idx τ).length).take τ.length

@[simp] theorem blockOf_eq (τ s idx : List Bool) :
    blockOf τ s idx = blockAtIdx τ.length s idx.length := by
  rw [blockOf, blockAtIdx, smash_length]

theorem blockOf_mem {n : ℕ} {gτ gs gidx : (Fin n → List Bool) → List Bool}
    (hτ : Cobham gτ) (hs : Cobham gs) (hidx : Cobham gidx) :
    Cobham fun v : Fin n → List Bool => blockOf (gτ v) (gs v) (gidx v) :=
  (takeFn hτ (dropFn (comp₂ Cobham.smash hidx hτ) hs)).of_eq fun _ => rfl

/-! ## Counting accepting blocks -/

/-- Unary count of the blocks of `s` on which the path of `tm` accepts: one bit
per accepting block. The recursion runs once per bit of `ρ`, and the block
index at each step is the length of the remaining tail. -/
noncomputable def acceptCountAux (tm : NTM k) (u x τ s : List Bool) : List Bool → List Bool
  | [] => []
  | _ :: y =>
      caseBit₀ (acceptChoiceFn tm u x (blockOf τ s y))
        (false :: acceptCountAux tm u x τ s y) (acceptCountAux tm u x τ s y)

/-- The count is the number of accepting block indices below `|ρ|`. -/
theorem acceptCountAux_length (tm : NTM k) (u x τ s ρ : List Bool) :
    (acceptCountAux tm u x τ s ρ).length
      = ∑ j ∈ Finset.range ρ.length,
          (if acceptChoiceFn tm u x (blockAtIdx τ.length s j) = [true] then 1 else 0) := by
  induction ρ with
  | nil => simp [acceptCountAux]
  | cons β y ih =>
      have hflag := acceptChoiceFn_flag tm u x (blockOf τ s y)
      rw [acceptCountAux, List.length_cons, Finset.sum_range_succ, ← ih]
      rcases hflag with hf | hf
      · rw [hf]
        simp only [caseBit₀_cons, Bool.cond_true, List.length_cons]
        rw [ite_eq_left (by rw [← blockOf_eq]; exact hf)]
      · rw [hf]
        simp only [caseBit₀_cons, Bool.cond_false]
        rw [ite_eq_right (by rw [← blockOf_eq, hf]; simp)]
        omega

/-- The step of the counting recursion. -/
private noncomputable def countStep (tm : NTM k) (w : Fin 6 → List Bool) : List Bool :=
  caseBit₀ (acceptChoiceFn tm (w 2) (w 3) (blockOf (w 4) (w 5) (w 0)))
    (false :: w 1) (w 1)

private theorem countStep_mem (tm : NTM k) : Cobham (countStep tm) := by
  have hcons : Cobham fun w : Fin 6 → List Bool => false :: w 1 :=
    (Cobham.comp (Cobham.bit false) fun _ : Fin 1 => Cobham.proj 1).of_eq fun _ => rfl
  exact (iteFn
    (acceptChoiceFn_mem tm (Cobham.proj 2) (Cobham.proj 3)
      (blockOf_mem (Cobham.proj 4) (Cobham.proj 5) (Cobham.proj 0)))
    hcons (Cobham.proj 1)).of_eq fun _ => rfl

private theorem recNotation_count (tm : NTM k) (u x τ s ρ : List Bool) :
    recNotation (fun _ : Fin 4 → List Bool => ([] : List Bool)) (countStep tm)
        (countStep tm) ρ ![u, x, τ, s]
      = acceptCountAux tm u x τ s ρ := by
  induction ρ with
  | nil => rfl
  | cons β y ih =>
      rw [recNotation_cons, acceptCountAux]
      cases β <;>
        · simp only [Bool.cond_false, Bool.cond_true, countStep, Fin.cons_zero, Fin.cons_one]
          rw [show (Fin.cons y (Fin.cons (recNotation
              (fun _ : Fin 4 → List Bool => ([] : List Bool)) (countStep tm)
              (countStep tm) y ![u, x, τ, s]) ![u, x, τ, s]) : Fin 6 → List Bool) 2 = u from rfl,
            show (Fin.cons y (Fin.cons (recNotation
              (fun _ : Fin 4 → List Bool => ([] : List Bool)) (countStep tm)
              (countStep tm) y ![u, x, τ, s]) ![u, x, τ, s]) : Fin 6 → List Bool) 3 = x from rfl,
            show (Fin.cons y (Fin.cons (recNotation
              (fun _ : Fin 4 → List Bool => ([] : List Bool)) (countStep tm)
              (countStep tm) y ![u, x, τ, s]) ![u, x, τ, s]) : Fin 6 → List Bool) 4 = τ from rfl,
            show (Fin.cons y (Fin.cons (recNotation
              (fun _ : Fin 4 → List Bool => ([] : List Bool)) (countStep tm)
              (countStep tm) y ![u, x, τ, s]) ![u, x, τ, s]) : Fin 6 → List Bool) 5 = s from rfl,
            ih]

private theorem recNotation_count_length (tm : NTM k) (ρ : List Bool)
    (v : Fin 4 → List Bool) :
    (recNotation (fun _ : Fin 4 → List Bool => ([] : List Bool)) (countStep tm)
      (countStep tm) ρ v).length ≤ ρ.length := by
  induction ρ with
  | nil => simp
  | cons β y ih =>
      rw [recNotation_cons, List.length_cons]
      have hstep : ∀ (a b : List Bool) (w' : Fin 4 → List Bool),
          (countStep tm (Fin.cons a (Fin.cons b w'))).length ≤ b.length + 1 := by
        intro a b w'
        show (caseBit₀ (acceptChoiceFn tm _ _ _) (false :: b) b).length ≤ b.length + 1
        rcases hc : acceptChoiceFn tm ((Fin.cons a (Fin.cons b w') : Fin 6 → List Bool) 2)
            ((Fin.cons a (Fin.cons b w') : Fin 6 → List Bool) 3)
            (blockOf ((Fin.cons a (Fin.cons b w') : Fin 6 → List Bool) 4)
              ((Fin.cons a (Fin.cons b w') : Fin 6 → List Bool) 5)
              ((Fin.cons a (Fin.cons b w') : Fin 6 → List Bool) 0)) with _ | ⟨d, z⟩
        · simp
        · cases d <;> simp
      cases β <;>
        · simp only [Bool.cond_false, Bool.cond_true]
          have := hstep y (recNotation
            (fun _ : Fin 4 → List Bool => ([] : List Bool)) (countStep tm)
            (countStep tm) y v) v
          omega

/-- **The count is in the algebra.** -/
theorem acceptCountAux_mem {n : ℕ} (tm : NTM k)
    {gu gx gτ gs gρ : (Fin n → List Bool) → List Bool}
    (hu : Cobham gu) (hx : Cobham gx) (hτ : Cobham gτ) (hs : Cobham gs)
    (hρ : Cobham gρ) :
    Cobham fun v : Fin n → List Bool =>
      acceptCountAux tm (gu v) (gx v) (gτ v) (gs v) (gρ v) := by
  have hrec := Cobham.boundedRec (g := fun _ : Fin 4 → List Bool => ([] : List Bool))
    (h₀ := countStep tm) (h₁ := countStep tm)
    (j := fun w : Fin 5 → List Bool => w 0)
    Cobham.empty (countStep_mem tm) (countStep_mem tm) (Cobham.proj 0)
    (by
      intro ρ v
      simpa using recNotation_count_length tm ρ v)
  have hg : ∀ i : Fin 5, Cobham (![gρ, gu, gx, gτ, gs] i) := by
    intro i
    match i with
    | 0 => exact hρ
    | 1 => exact hu
    | 2 => exact hx
    | 3 => exact hτ
    | 4 => exact hs
  refine (Cobham.comp hrec hg).of_eq fun v => ?_
  have htail : (Fin.tail fun i => ![gρ, gu, gx, gτ, gs] i v)
      = ![gu v, gx v, gτ v, gs v] := by
    funext i
    match i with
    | 0 => rfl
    | 1 => rfl
    | 2 => rfl
    | 3 => rfl
  show recNotation _ _ _ (gρ v) (Fin.tail fun i => ![gρ, gu, gx, gτ, gs] i v) = _
  rw [htail, recNotation_count]

/-! ## The amplified verdict -/

/-- The amplified majority verdict as a flag: strictly more than half of the
`|ρ|` blocks of `s` accept. -/
noncomputable def majorityFlag (tm : NTM k) (u x τ s ρ : List Bool) : List Bool :=
  notBit (lenLeFlag ρ (acceptCountAux tm u x τ s ρ ++ acceptCountAux tm u x τ s ρ))

theorem majorityFlag_flag (tm : NTM k) (u x τ s ρ : List Bool) :
    majorityFlag tm u x τ s ρ = [true] ∨ majorityFlag tm u x τ s ρ = [false] := by
  rw [majorityFlag]
  rcases lenLeFlag_flag ρ (acceptCountAux tm u x τ s ρ ++ acceptCountAux tm u x τ s ρ)
    with h | h <;> rw [h] <;> simp [notBit]

theorem majorityFlag_eq_true_iff (tm : NTM k) (u x τ s ρ : List Bool) :
    majorityFlag tm u x τ s ρ = [true] ↔
      ρ.length < 2 * (acceptCountAux tm u x τ s ρ).length := by
  rw [majorityFlag, notBit_eq_true_iff (lenLeFlag_flag _ _)]
  constructor
  · intro h
    by_contra hcon
    rw [Nat.not_lt] at hcon
    have htrue : lenLeFlag ρ
        (acceptCountAux tm u x τ s ρ ++ acceptCountAux tm u x τ s ρ) = [true] := by
      rw [lenLeFlag_eq_true_iff, List.length_append]
      omega
    rw [htrue] at h
    exact absurd h (by simp)
  · intro h
    rcases lenLeFlag_flag ρ
      (acceptCountAux tm u x τ s ρ ++ acceptCountAux tm u x τ s ρ) with h' | h'
    · rw [lenLeFlag_eq_true_iff, List.length_append] at h'
      omega
    · exact h'

theorem majorityFlag_mem {n : ℕ} (tm : NTM k)
    {gu gx gτ gs gρ : (Fin n → List Bool) → List Bool}
    (hu : Cobham gu) (hx : Cobham gx) (hτ : Cobham gτ) (hs : Cobham gs)
    (hρ : Cobham gρ) :
    Cobham fun v : Fin n → List Bool =>
      majorityFlag tm (gu v) (gx v) (gτ v) (gs v) (gρ v) :=
  (notFn (lenLeFlag_mem hρ
    (appendFn (acceptCountAux_mem tm hu hx hτ hs hρ)
      (acceptCountAux_mem tm hu hx hτ hs hρ)))).of_eq fun _ => rfl

/-- The verdict sought at a shift: the amplified majority, or its negation. -/
noncomputable def verdictFlag (tm : NTM k) (b : Bool) (u x τ s ρ : List Bool) :
    List Bool :=
  bif b then majorityFlag tm u x τ s ρ else notBit (majorityFlag tm u x τ s ρ)

theorem verdictFlag_flag (tm : NTM k) (b : Bool) (u x τ s ρ : List Bool) :
    verdictFlag tm b u x τ s ρ = [true] ∨ verdictFlag tm b u x τ s ρ = [false] := by
  cases b
  · rw [verdictFlag]
    simp only [Bool.cond_false]
    rcases majorityFlag_flag tm u x τ s ρ with h | h <;> rw [h] <;> simp [notBit]
  · rw [verdictFlag]
    simp only [Bool.cond_true]
    exact majorityFlag_flag tm u x τ s ρ

theorem verdictFlag_mem {n : ℕ} (tm : NTM k) (b : Bool)
    {gu gx gτ gs gρ : (Fin n → List Bool) → List Bool}
    (hu : Cobham gu) (hx : Cobham gx) (hτ : Cobham gτ) (hs : Cobham gs)
    (hρ : Cobham gρ) :
    Cobham fun v : Fin n → List Bool =>
      verdictFlag tm b (gu v) (gx v) (gτ v) (gs v) (gρ v) := by
  cases b
  · exact (notFn (majorityFlag_mem tm hu hx hτ hs hρ)).of_eq fun _ => rfl
  · exact (majorityFlag_mem tm hu hx hτ hs hρ).of_eq fun _ => rfl

/-! ## Disjunction over shifts -/

/-- Disjunction of the verdict over the shift blocks of `wit`: the recursion
runs once per bit of the shift ruler, and at each step the shift block is cut
from `wit` at the index given by the remaining tail. -/
noncomputable def anyShiftAux (tm : NTM k) (b : Bool) (u x τ ρ σ r wit : List Bool) :
    List Bool → List Bool
  | [] => [false]
  | _ :: y =>
      orBit (verdictFlag tm b u x τ (xorSuffix r (padTo σ (blockOf σ wit y))) ρ)
        (anyShiftAux tm b u x τ ρ σ r wit y)

theorem anyShiftAux_flag (tm : NTM k) (b : Bool) (u x τ ρ σ r wit ι : List Bool) :
    anyShiftAux tm b u x τ ρ σ r wit ι = [true] ∨
      anyShiftAux tm b u x τ ρ σ r wit ι = [false] := by
  induction ι with
  | nil => exact Or.inr rfl
  | cons β y ih => exact orBit_flag (verdictFlag_flag _ _ _ _ _ _ _) ih

/-- **The disjunction is exactly an existential over shift indices.** -/
theorem anyShiftAux_eq_true_iff (tm : NTM k) (b : Bool)
    (u x τ ρ σ r wit ι : List Bool) :
    anyShiftAux tm b u x τ ρ σ r wit ι = [true] ↔
      ∃ i < ι.length,
        verdictFlag tm b u x τ
          (xorSuffix r (padTo σ (blockAtIdx σ.length wit i))) ρ = [true] := by
  induction ι with
  | nil => simp [anyShiftAux]
  | cons β y ih =>
      rw [anyShiftAux,
        orBit_eq_true_iff (verdictFlag_flag _ _ _ _ _ _ _) (anyShiftAux_flag _ _ _ _ _ _ _ _ _ _),
        ih, List.length_cons]
      rw [blockOf_eq]
      constructor
      · rintro (h | ⟨i, hi, hv⟩)
        · exact ⟨y.length, by omega, h⟩
        · exact ⟨i, by omega, hv⟩
      · rintro ⟨i, hi, hv⟩
        rcases Nat.lt_or_ge i y.length with hlt | hge
        · exact Or.inr ⟨i, hlt, hv⟩
        · have : i = y.length := by omega
          subst this
          exact Or.inl hv

/-- The step of the shift recursion. -/
private noncomputable def shiftStep (tm : NTM k) (b : Bool) (w : Fin 9 → List Bool) :
    List Bool :=
  orBit (verdictFlag tm b (w 2) (w 3) (w 4)
    (xorSuffix (w 7) (padTo (w 6) (blockOf (w 6) (w 8) (w 0)))) (w 5)) (w 1)

private theorem shiftStep_mem (tm : NTM k) (b : Bool) : Cobham (shiftStep tm b) :=
  (orFn (verdictFlag_mem tm b (Cobham.proj 2) (Cobham.proj 3) (Cobham.proj 4)
      (xorSuffix_mem (Cobham.proj 7)
        (padFn (Cobham.proj 6)
          (blockOf_mem (Cobham.proj 6) (Cobham.proj 8) (Cobham.proj 0))))
      (Cobham.proj 5))
    (Cobham.proj 1)).of_eq fun _ => rfl

private theorem recNotation_anyShift (tm : NTM k) (b : Bool)
    (u x τ ρ σ r wit ι : List Bool) :
    recNotation (fun _ : Fin 7 → List Bool => ([false] : List Bool)) (shiftStep tm b)
        (shiftStep tm b) ι ![u, x, τ, ρ, σ, r, wit]
      = anyShiftAux tm b u x τ ρ σ r wit ι := by
  induction ι with
  | nil => rfl
  | cons β y ih =>
      rw [recNotation_cons, anyShiftAux]
      cases β <;>
        · show shiftStep tm b (Fin.cons y (Fin.cons _ ![u, x, τ, ρ, σ, r, wit])) = _
          rw [shiftStep]
          show orBit (verdictFlag tm b u x τ (xorSuffix r (padTo σ (blockOf σ wit y))) ρ)
              (recNotation (fun _ : Fin 7 → List Bool => ([false] : List Bool))
                (shiftStep tm b) (shiftStep tm b) y ![u, x, τ, ρ, σ, r, wit]) = _
          rw [ih]

private theorem recNotation_anyShift_length (tm : NTM k) (b : Bool) (ι : List Bool)
    (v : Fin 7 → List Bool) :
    (recNotation (fun _ : Fin 7 → List Bool => ([false] : List Bool)) (shiftStep tm b)
      (shiftStep tm b) ι v).length ≤ 1 := by
  induction ι with
  | nil => simp
  | cons β y ih =>
      rw [recNotation_cons]
      have hstep : ∀ (a c : List Bool) (w' : Fin 7 → List Bool),
          (shiftStep tm b (Fin.cons a (Fin.cons c w'))).length ≤ 1 := by
        intro a c w'
        rw [shiftStep, orBit_length]
      cases β <;> simpa using hstep y _ v

/-- **The disjunction over shifts is in the algebra.** -/
theorem anyShiftAux_mem {n : ℕ} (tm : NTM k) (b : Bool)
    {gu gx gτ gρ gσ gr gwit gι : (Fin n → List Bool) → List Bool}
    (hu : Cobham gu) (hx : Cobham gx) (hτ : Cobham gτ) (hρ : Cobham gρ)
    (hσ : Cobham gσ) (hr : Cobham gr) (hwit : Cobham gwit) (hι : Cobham gι) :
    Cobham fun v : Fin n → List Bool =>
      anyShiftAux tm b (gu v) (gx v) (gτ v) (gρ v) (gσ v) (gr v) (gwit v) (gι v) := by
  have hrec := Cobham.boundedRec
    (g := fun _ : Fin 7 → List Bool => ([false] : List Bool))
    (h₀ := shiftStep tm b) (h₁ := shiftStep tm b)
    (j := fun _ : Fin 8 → List Bool => ([false] : List Bool))
    (Cobham.const _) (shiftStep_mem tm b) (shiftStep_mem tm b) (Cobham.const _)
    (by
      intro ι v
      simpa using recNotation_anyShift_length tm b ι v)
  have hg : ∀ i : Fin 8, Cobham (![gι, gu, gx, gτ, gρ, gσ, gr, gwit] i) := by
    intro i
    match i with
    | 0 => exact hι
    | 1 => exact hu
    | 2 => exact hx
    | 3 => exact hτ
    | 4 => exact hρ
    | 5 => exact hσ
    | 6 => exact hr
    | 7 => exact hwit
  refine (Cobham.comp hrec hg).of_eq fun v => ?_
  have htail : (Fin.tail fun i => ![gι, gu, gx, gτ, gρ, gσ, gr, gwit] i v)
      = ![gu v, gx v, gτ v, gρ v, gσ v, gr v, gwit v] := by
    funext i
    match i with
    | 0 => rfl
    | 1 => rfl
    | 2 => rfl
    | 3 => rfl
    | 4 => rfl
    | 5 => rfl
    | 6 => rfl
  show recNotation _ _ _ (gι v) (Fin.tail fun i => ![gι, gu, gx, gτ, gρ, gσ, gr, gwit] i v) = _
  rw [htail, recNotation_anyShift]

/-! ## Membership among blocks -/

/-- Flag: the block `c` occurs among the width-`|τ|` blocks of `s` indexed by the ruler. -/
def memBlockAux (τ s c : List Bool) : List Bool → List Bool
  | [] => [false]
  | _ :: y => orBit (eqFlag c (blockOf τ s y)) (memBlockAux τ s c y)

theorem memBlockAux_flag (τ s c ι : List Bool) :
    memBlockAux τ s c ι = [true] ∨ memBlockAux τ s c ι = [false] := by
  induction ι with
  | nil => exact Or.inr rfl
  | cons β y ih => exact orBit_flag (eqFlag_flag _ _) ih

/-- **The membership test is an existential over block indices.** -/
theorem memBlockAux_eq_true_iff (τ s c ι : List Bool) :
    memBlockAux τ s c ι = [true] ↔ ∃ i < ι.length, blockAtIdx τ.length s i = c := by
  induction ι with
  | nil => simp [memBlockAux]
  | cons β y ih =>
      rw [memBlockAux, orBit_eq_true_iff (eqFlag_flag _ _) (memBlockAux_flag _ _ _ _), ih,
        eqFlag_eq_true_iff, blockOf_eq, List.length_cons]
      constructor
      · rintro (h | ⟨i, hi, hv⟩)
        · exact ⟨y.length, by omega, h.symm⟩
        · exact ⟨i, by omega, hv⟩
      · rintro ⟨i, hi, hv⟩
        rcases Nat.lt_or_ge i y.length with hlt | hge
        · exact Or.inr ⟨i, hlt, hv⟩
        · have : i = y.length := by omega
          subst this
          exact Or.inl hv.symm

/-- The step of the membership recursion. -/
private def memStep (w : Fin 5 → List Bool) : List Bool :=
  orBit (eqFlag (w 4) (blockOf (w 2) (w 3) (w 0))) (w 1)

private theorem memStep_mem : Cobham memStep :=
  (orFn (eqFlag_mem (Cobham.proj 4)
      (blockOf_mem (Cobham.proj 2) (Cobham.proj 3) (Cobham.proj 0)))
    (Cobham.proj 1)).of_eq fun _ => rfl

private theorem recNotation_memBlock (τ s c ι : List Bool) :
    recNotation (fun _ : Fin 3 → List Bool => ([false] : List Bool)) memStep memStep ι
        ![τ, s, c] = memBlockAux τ s c ι := by
  induction ι with
  | nil => rfl
  | cons β y ih =>
      rw [recNotation_cons, memBlockAux]
      cases β <;>
        · show memStep (Fin.cons y (Fin.cons _ ![τ, s, c])) = _
          rw [memStep]
          show orBit (eqFlag c (blockOf τ s y))
              (recNotation (fun _ : Fin 3 → List Bool => ([false] : List Bool)) memStep memStep y
                ![τ, s, c]) = _
          rw [ih]

private theorem recNotation_memBlock_length (ι : List Bool) (v : Fin 3 → List Bool) :
    (recNotation (fun _ : Fin 3 → List Bool => ([false] : List Bool)) memStep memStep ι v).length
      ≤ 1 := by
  induction ι with
  | nil => simp
  | cons β y ih =>
      rw [recNotation_cons]
      have hstep : ∀ (a b : List Bool) (w' : Fin 3 → List Bool),
          (memStep (Fin.cons a (Fin.cons b w'))).length ≤ 1 := by
        intro a b w'
        rw [memStep, orBit_length]
      cases β <;> simpa using hstep y _ v

/-- **The membership test is in the algebra.** -/
theorem memBlockAux_mem {n : ℕ} {gτ gs gc gι : (Fin n → List Bool) → List Bool}
    (hτ : Cobham gτ) (hs : Cobham gs) (hc : Cobham gc) (hι : Cobham gι) :
    Cobham fun v : Fin n → List Bool => memBlockAux (gτ v) (gs v) (gc v) (gι v) := by
  have hrec := Cobham.boundedRec (g := fun _ : Fin 3 → List Bool => ([false] : List Bool))
    (h₀ := memStep) (h₁ := memStep)
    (j := fun _ : Fin 4 → List Bool => ([false] : List Bool))
    (Cobham.const _) memStep_mem memStep_mem (Cobham.const _)
    (by
      intro ι v
      simpa using recNotation_memBlock_length ι v)
  have hg : ∀ i : Fin 4, Cobham (![gι, gτ, gs, gc] i) := by
    intro i
    match i with
    | 0 => exact hι
    | 1 => exact hτ
    | 2 => exact hs
    | 3 => exact hc
  refine (Cobham.comp hrec hg).of_eq fun v => ?_
  have htail : (Fin.tail fun i => ![gι, gτ, gs, gc] i v) = ![gτ v, gs v, gc v] := by
    funext i
    match i with
    | 0 => rfl
    | 1 => rfl
    | 2 => rfl
  show recNotation _ _ _ (gι v) (Fin.tail fun i => ![gι, gτ, gs, gc] i v) = _
  rw [htail, recNotation_memBlock]

end Cobham

end Complexity
