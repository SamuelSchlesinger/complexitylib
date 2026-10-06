/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.Basis.AndOr
public import Complexitylib.Algebraic.Basis.DeMorgan
public import Complexitylib.Algebraic.Translation

/-!
# Internals of the monotone Boolean matrix product bound

This file proves that every De Morgan circuit without NOT gates (AND, OR,
constants and identity gates) computing a *partial* Boolean product
`z i j = ⋁ {x i k ∧ y k j | (i, k, j) ∈ T}` of an `I × K` matrix and a `K × J`
matrix has at least `|T|` AND gates (Pratt; Paterson; Mehlhorn--Galil; Wegener,
*The Complexity of Boolean Functions*, Theorem 6.8.1, whose argument never uses
the shape of `T`). Compiling the binary AND/OR basis into the De Morgan basis
(`ofAndOr`) gives the full product bound `I * J * K` for AND/OR circuits. The
surface statements are in `Complexitylib.Algebraic.LowerBound.Monotone.MatrixProduct`
and `Complexitylib.Algebraic.LowerBound.Monotone.MatrixProduct.Partial`.

## Proof

Call `x i k` and `y k j` the variables of *type* `k`. The argument runs in
stages `k = 0, 1, …, K - 1` and never edits the circuit: each stage is a new
evaluation of the same program, carried by a single interpretation whose
carrier holds the gate functions of every stage at once
(`stageInterpretation`). Stage `k` is `sem p (k + 1)`; `sem p 0` is the
ordinary Boolean evaluation.

* Stage `k` fixes the variables of type `< k` (`x` to one, `y` to zero), so the
  outputs become the product over the triples of `T` of type `≥ k`.
* A gate is *forced* to the constant one at stage `k` when it was constant one
  under this restriction at the previous stage, or when its function has two
  distinct variables of type `k` among its one-variable implicants (`Bad`).
  Wegener's Lemma 6.8.1 and replacement rule (Theorem 6.5.2) show that forcing
  such gates does not change the outputs. Here this is proved for all forced
  gates of a stage at once (`StepHyp.agree`): below a negative input of an
  output there is a negative input that sets at most one type-`k` variable to
  zero (`cover`), and on it every forced gate already evaluates to one.
* The *creator* of a triple `(i, k, j) ∈ T` is a gate whose stage-`k` function
  has `x i k ∧ y k j` as a prime implicant while none of its arguments has.
  Every output has that implicant, so a creator exists. Constants, identities
  and OR gates cannot create a prime implicant (`creator_shape`), so a creator
  is an AND gate one of whose arguments has the implicant `x i k` and the
  other `y k j`.
* Within a stage, two triples cannot share a creator, since an argument of it
  would have two type-`k` implicants of length one and would have been forced.
  Across stages, the argument with implicant `x i k` is constant one at every
  later stage (`x i k` is then fixed to one), so the gate is not a creator
  there.

The creators therefore form `|T|` distinct AND gates.
-/

@[expose] public section

namespace Algebraic
namespace Monotone
namespace MatrixProduct
namespace Internal

open Cslib.Circuits

/-- The Boolean core of `creator_shape` for an AND gate with arguments taking the
values `a`, `b`, `c` on the pair and the two singletons. -/
theorem and_shape : ∀ a₀ b₀ c₀ a₁ b₁ c₁ : Bool, (a₀ && a₁) = true → (b₀ && b₁) = false →
    (c₀ && c₁) = false → ¬ (a₀ = true ∧ b₀ = false ∧ c₀ = false) →
    ¬ (a₁ = true ∧ b₁ = false ∧ c₁ = false) →
    ((b₀ = true ∧ c₁ = true) ∨ (b₁ = true ∧ c₀ = true)) ∧
      ¬ (a₀ = true ∧ b₀ = true ∧ c₀ = true) ∧ ¬ (a₁ = true ∧ b₁ = true ∧ c₁ = true) := by
  intro a₀ b₀ c₀ a₁ b₁ c₁
  cases a₀ <;> cases b₀ <;> cases c₀ <;> cases a₁ <;> cases b₁ <;> cases c₁ <;> decide

noncomputable section

open scoped Classical

variable {N I J K g : Nat}

/-- The pointwise order on assignments. -/
def AssignmentLE (a b : Fin N → Bool) : Prop :=
  ∀ v, a v = true → b v = true

/-- A Boolean function is monotone. -/
def IsMonotone (f : (Fin N → Bool) → Bool) : Prop :=
  ∀ a b, AssignmentLE a b → f a = true → f b = true

/-- The assignment whose only true variable is `u`. -/
def single (u : Fin N) : Fin N → Bool :=
  fun v => decide (v = u)

/-- The assignment whose only true variables are `u` and `w`. -/
def pair (u w : Fin N) : Fin N → Bool :=
  fun v => decide (v = u ∨ v = w)

theorem assignmentLE_single {u : Fin N} {b : Fin N → Bool} (h : b u = true) :
    AssignmentLE (single u) b := by
  intro v hv
  simp only [single, decide_eq_true_eq] at hv
  exact hv ▸ h

theorem assignmentLE_false (b : Fin N → Bool) : AssignmentLE (fun _ => false) b := by
  intro v hv
  simp at hv

/-! ### The De Morgan basis without negation -/

/-- Every De Morgan operation other than negation is monotone. -/
theorem interpretation_mono {op : DeMorgan.Op} (hop : op ≠ .not)
    {a b : Fin (DeMorgan.arity op) → Bool} (hab : ∀ m, a m = true → b m = true) :
    DeMorgan.interpretation op a = true → DeMorgan.interpretation op b = true := by
  cases op with
  | false => exact id
  | true => exact id
  | id => exact hab _
  | not => exact absurd rfl hop
  | and =>
      simp only [DeMorgan.interpretation, Bool.and_eq_true]
      exact fun h => ⟨hab _ h.1, hab _ h.2⟩
  | or =>
      simp only [DeMorgan.interpretation, Bool.or_eq_true]
      exact fun h => h.imp (hab _) (hab _)

theorem isMonotone_interpretation {op : DeMorgan.Op} (hop : op ≠ .not)
    {f : Fin (DeMorgan.arity op) → (Fin N → Bool) → Bool} (hf : ∀ m, IsMonotone (f m)) :
    IsMonotone fun c => DeMorgan.interpretation op fun m => f m c :=
  fun a b hab => interpretation_mono hop fun m => hf m a b hab

/-- The local shape of a creator. A gate other than NOT whose function has the
prime implicant `u ∧ w` while none of its arguments has it is an AND gate, one
argument of which accepts `u` alone and the other `w` alone, and no argument of
which is constant one. -/
theorem creator_shape {op : DeMorgan.Op} (hop : op ≠ .not)
    (F : Fin (DeMorgan.arity op) → (Fin N → Bool) → Bool) {u w : Fin N}
    (hp : (DeMorgan.interpretation op fun m => F m (pair u w)) = true)
    (hu : (DeMorgan.interpretation op fun m => F m (single u)) = false)
    (hw : (DeMorgan.interpretation op fun m => F m (single w)) = false)
    (hF : ∀ m, ¬ (F m (pair u w) = true ∧ F m (single u) = false ∧ F m (single w) = false)) :
    op = .and ∧ (∃ a b, a ≠ b ∧ F a (single u) = true ∧ F b (single w) = true) ∧
      ∀ m, ¬ ∀ c, F m c = true := by
  cases op with
  | false => exact absurd hp (by simp [DeMorgan.interpretation])
  | true => exact absurd hu (by simp [DeMorgan.interpretation])
  | id => exact (hF ⟨0, by decide⟩ ⟨hp, hu, hw⟩).elim
  | not => exact absurd rfl hop
  | or =>
      exfalso
      simp only [DeMorgan.interpretation, Bool.or_eq_true, Bool.or_eq_false_iff] at hp hu hw
      rcases hp with hp | hp
      · exact hF _ ⟨hp, hu.1, hw.1⟩
      · exact hF _ ⟨hp, hu.2, hw.2⟩
  | and =>
      simp only [DeMorgan.interpretation] at hp hu hw
      have h0 := hF ⟨0, by decide⟩
      have h1 := hF ⟨1, by decide⟩
      obtain ⟨hshape, k0, k1⟩ := and_shape _ _ _ _ _ _ hp hu hw h0 h1
      refine ⟨rfl, ?_, ?_⟩
      · rcases hshape with ⟨hb, hc⟩ | ⟨hb, hc⟩
        · exact ⟨⟨0, by decide⟩, ⟨1, by decide⟩, by simp, hb, hc⟩
        · exact ⟨⟨1, by decide⟩, ⟨0, by decide⟩, by simp, hb, hc⟩
      · rintro ⟨m, hm⟩ hc
        change m < 2 at hm
        rcases m with _ | _ | m
        · exact k0 ⟨hc _, hc _, hc _⟩
        · exact k1 ⟨hc _, hc _, hc _⟩
        · omega

/-- The NOT-gate count of a program vanishes only when it has no NOT gate. -/
theorem lines_ne_not_of_cost_eq_zero (p : Program DeMorgan.signature N g)
    (h : p.cost DeMorgan.notCost = 0) (G : Fin g) : (p.lines G).op ≠ .not := by
  intro hG
  rw [Program.cost_eq_sum_lines, Finset.sum_eq_zero_iff] at h
  simpa [hG] using h G (Finset.mem_univ G)

/-- An injective layout of an `I × K` matrix `x` and a `K × J` matrix `y` among
`N` circuit inputs. -/
structure Layout (N I J K : Nat) where
  /-- The input carrying entry `(i, k)` of the left matrix. -/
  x : Fin I → Fin K → Fin N
  /-- The input carrying entry `(k, j)` of the right matrix. -/
  y : Fin K → Fin J → Fin N
  /-- Distinct left entries use distinct inputs. -/
  x_inj : ∀ {i k i' k'}, x i k = x i' k' → i = i' ∧ k = k'
  /-- Distinct right entries use distinct inputs. -/
  y_inj : ∀ {k j k' j'}, y k j = y k' j' → k = k' ∧ j = j'
  /-- Left and right entries use distinct inputs. -/
  x_ne_y : ∀ i k k' j, x i k ≠ y k' j

namespace Layout

/-- The layout of an injective placement of the entries of both matrices. -/
def ofInjective (x : Fin I → Fin K → Fin N) (y : Fin K → Fin J → Fin N)
    (distinct : Function.Injective (Sum.elim (Function.uncurry x) (Function.uncurry y))) :
    Layout N I J K where
  x := x
  y := y
  x_inj := fun h => by
    have := distinct (a₁ := Sum.inl (_, _)) (a₂ := Sum.inl (_, _)) h
    simpa using this
  y_inj := fun h => by
    have := distinct (a₁ := Sum.inr (_, _)) (a₂ := Sum.inr (_, _)) h
    simpa using this
  x_ne_y := fun i k k' j h => by
    have := distinct (a₁ := Sum.inl (i, k)) (a₂ := Sum.inr (k', j)) h
    simp at this

variable (L : Layout N I J K)

/-- Variable `v` is a left-matrix entry of type `< s`. -/
def FixedTrue (s : Nat) (v : Fin N) : Prop :=
  ∃ i k, (k : Fin K).val < s ∧ L.x i k = v

/-- Variable `v` is a right-matrix entry of type `< s`. -/
def FixedFalse (s : Nat) (v : Fin N) : Prop :=
  ∃ k j, (k : Fin K).val < s ∧ L.y k j = v

/-- The restriction of stage `s`: left entries of type `< s` read one, right
entries of type `< s` read zero. -/
def fix (s : Nat) (c : Fin N → Bool) : Fin N → Bool :=
  fun v => if L.FixedTrue s v then true else if L.FixedFalse s v then false else c v

/-- Variable `v` has type `s`. -/
def IsType (s : Nat) (v : Fin N) : Prop :=
  (∃ i k, (k : Fin K).val = s ∧ L.x i k = v) ∨ (∃ k j, (k : Fin K).val = s ∧ L.y k j = v)

/-- A function has two distinct type-`s` variables among its one-variable
implicants. -/
def Bad (s : Nat) (h : (Fin N → Bool) → Bool) : Prop :=
  ∃ u w, u ≠ w ∧ L.IsType s u ∧ L.IsType s w ∧ h (single u) = true ∧ h (single w) = true

/-- The entry `(i, j)` of the product over the triples of `T` of type `≥ s`. -/
def product (T : Finset (Fin I × Fin K × Fin J)) (s : Nat) (i : Fin I) (j : Fin J)
    (c : Fin N → Bool) : Bool :=
  decide (∃ k : Fin K, (i, k, j) ∈ T ∧ s ≤ k.val ∧ c (L.x i k) = true ∧ c (L.y k j) = true)

theorem isType_x (i : Fin I) (k : Fin K) : L.IsType k.val (L.x i k) :=
  Or.inl ⟨i, k, rfl, rfl⟩

theorem isType_y (k : Fin K) (j : Fin J) : L.IsType k.val (L.y k j) :=
  Or.inr ⟨k, j, rfl, rfl⟩

/-! ### The restriction -/

theorem fixedTrue_x {s : Nat} {i : Fin I} {k : Fin K} :
    L.FixedTrue s (L.x i k) ↔ k.val < s := by
  constructor
  · rintro ⟨i', k', hk', h⟩
    rw [(L.x_inj h).2] at hk'
    exact hk'
  · intro hk
    exact ⟨i, k, hk, rfl⟩

theorem not_fixedFalse_x {s : Nat} {i : Fin I} {k : Fin K} :
    ¬ L.FixedFalse s (L.x i k) := by
  rintro ⟨k', j, -, h⟩
  exact L.x_ne_y i k k' j h.symm

theorem not_fixedTrue_y {s : Nat} {k : Fin K} {j : Fin J} :
    ¬ L.FixedTrue s (L.y k j) := by
  rintro ⟨i, k', -, h⟩
  exact L.x_ne_y i k' k j h

theorem fixedFalse_y {s : Nat} {k : Fin K} {j : Fin J} :
    L.FixedFalse s (L.y k j) ↔ k.val < s := by
  constructor
  · rintro ⟨k', j', hk', h⟩
    rw [(L.y_inj h).1] at hk'
    exact hk'
  · intro hk
    exact ⟨k, j, hk, rfl⟩

theorem fix_of_fixedTrue {s : Nat} {v : Fin N} (h : L.FixedTrue s v) (c : Fin N → Bool) :
    L.fix s c v = true := by
  simp [fix, h]

theorem fix_of_fixedFalse {s : Nat} {v : Fin N} (h : L.FixedFalse s v) (c : Fin N → Bool) :
    L.fix s c v = false := by
  have hT : ¬ L.FixedTrue s v := by
    rintro ⟨i, k, -, rfl⟩
    exact L.not_fixedFalse_x h
  simp [fix, h, hT]

theorem fix_of_free {s : Nat} {v : Fin N} (hT : ¬ L.FixedTrue s v) (hF : ¬ L.FixedFalse s v)
    (c : Fin N → Bool) : L.fix s c v = c v := by
  simp [fix, hT, hF]

theorem fix_x_of_lt {s : Nat} {i : Fin I} {k : Fin K} (hk : k.val < s) (c : Fin N → Bool) :
    L.fix s c (L.x i k) = true :=
  L.fix_of_fixedTrue (L.fixedTrue_x.2 hk) c

theorem fix_x_of_le {s : Nat} {i : Fin I} {k : Fin K} (hk : s ≤ k.val) (c : Fin N → Bool) :
    L.fix s c (L.x i k) = c (L.x i k) :=
  L.fix_of_free (fun h => by have := L.fixedTrue_x.1 h; omega) L.not_fixedFalse_x c

theorem fix_y_of_lt {s : Nat} {k : Fin K} {j : Fin J} (hk : k.val < s) (c : Fin N → Bool) :
    L.fix s c (L.y k j) = false :=
  L.fix_of_fixedFalse (L.fixedFalse_y.2 hk) c

theorem fix_y_of_le {s : Nat} {k : Fin K} {j : Fin J} (hk : s ≤ k.val) (c : Fin N → Bool) :
    L.fix s c (L.y k j) = c (L.y k j) :=
  L.fix_of_free L.not_fixedTrue_y (fun h => by have := L.fixedFalse_y.1 h; omega) c

theorem fix_zero (c : Fin N → Bool) : L.fix 0 c = c := by
  funext v
  apply L.fix_of_free
  · rintro ⟨i, k, hk, -⟩
    exact Nat.not_lt_zero _ hk
  · rintro ⟨k, j, hk, -⟩
    exact Nat.not_lt_zero _ hk

theorem fix_fix {s' s : Nat} (hs : s' ≤ s) (c : Fin N → Bool) :
    L.fix s' (L.fix s c) = L.fix s c := by
  funext v
  by_cases hT : L.FixedTrue s' v
  · obtain ⟨i, k, hk, hv⟩ := hT
    rw [L.fix_of_fixedTrue ⟨i, k, hk, hv⟩, L.fix_of_fixedTrue ⟨i, k, by omega, hv⟩]
  by_cases hF : L.FixedFalse s' v
  · obtain ⟨k, j, hk, hv⟩ := hF
    rw [L.fix_of_fixedFalse ⟨k, j, hk, hv⟩, L.fix_of_fixedFalse ⟨k, j, by omega, hv⟩]
  · exact L.fix_of_free hT hF _

theorem fix_mono (s : Nat) {a b : Fin N → Bool} (hab : AssignmentLE a b) :
    AssignmentLE (L.fix s a) (L.fix s b) := by
  intro v hv
  unfold fix at hv ⊢
  split_ifs at hv ⊢ <;> first | rfl | exact hab v hv

theorem isMonotone_fix_apply (s : Nat) (v : Fin N) : IsMonotone fun c => L.fix s c v :=
  fun _ _ hab h => L.fix_mono s hab v h

theorem product_fix (T : Finset (Fin I × Fin K × Fin J)) {s' s : Nat} (hs : s' ≤ s)
    (i : Fin I) (j : Fin J) (c : Fin N → Bool) :
    L.product T s' i j (L.fix s c) = L.product T s i j c := by
  unfold product
  congr 1
  apply propext
  constructor
  · rintro ⟨k, hT, -, hx, hy⟩
    by_cases hk : k.val < s
    · rw [L.fix_y_of_lt hk] at hy
      exact absurd hy (by simp)
    · have hk' : s ≤ k.val := by omega
      exact ⟨k, hT, hk', by rwa [L.fix_x_of_le hk'] at hx, by rwa [L.fix_y_of_le hk'] at hy⟩
  · rintro ⟨k, hT, hk, hx, hy⟩
    exact ⟨k, hT, le_trans hs hk, by rwa [L.fix_x_of_le hk], by rwa [L.fix_y_of_le hk]⟩

end Layout

/-! ### Programs -/

section Programs

variable {σ : Signature}

/-- Induction over the wires of a program in topological order. -/
theorem wire_induction (p : Program σ N g) {P : Wire N g → Prop}
    (input : ∀ v, P (Wire.input v))
    (gate : ∀ G, (∀ m, P ((p.lines G).wires m)) → P (Wire.gate G)) (w : Wire N g) : P w := by
  induction hw : w.index.val using Nat.strong_induction_on generalizing w with
  | _ n ih =>
    cases w with
    | input v => exact input v
    | gate G =>
      subst hw
      exact gate G fun m => ih _ (p.lines_wires_lt G m) _ rfl

/-- A gate wire carries the gate operation applied to its argument wires. -/
theorem trace_gate {U : Type*} (p : Program σ N g) (interpretation : Interpretation σ U)
    (x : Fin N → U) (G : Fin g) :
    p.trace interpretation x (Wire.gate G) =
      interpretation (p.lines G).op (fun m => p.trace interpretation x ((p.lines G).wires m)) := by
  rw [Program.trace_gateWire, Program.gateFunction_apply, ← p.lines_eval]
  rfl

end Programs

namespace Layout

variable (L : Layout N I J K)

/-! ### The staged evaluation -/

/-- The functions of one gate at every index, from the functions of its
arguments. Index `0` is the ordinary evaluation. Index `s + 1` (stage `s`)
forces the gate to one when its function at index `s` is constant one under
the restriction `fix s`, or when the gate operation applied to the arguments
has two type-`s` implicants of length one (`Bad`). -/
def stageValue (op : DeMorgan.Op) (u : Fin (DeMorgan.arity op) → Nat → (Fin N → Bool) → Bool) :
    Nat → (Fin N → Bool) → Bool
  | 0 => fun c => DeMorgan.interpretation op fun m => u m 0 c
  | s + 1 =>
      if stageValue op u s (L.fix s fun _ => false) = true ∨
          L.Bad s (fun c => DeMorgan.interpretation op fun m => u m (s + 1) c) then
        fun _ => true
      else
        fun c => DeMorgan.interpretation op fun m => u m (s + 1) c

/-- The interpretation evaluating all stages at once. -/
def stageInterpretation : Interpretation DeMorgan.signature (Nat → (Fin N → Bool) → Bool) :=
  fun op args => L.stageValue op args

/-- Input `v` at every index: index `0` reads it, index `s + 1` reads it through
`fix s` (and `fix 0` changes nothing). -/
def inputValue (v : Fin N) : Nat → (Fin N → Bool) → Bool :=
  fun t c => L.fix (t - 1) c v

/-- The function carried by a wire at index `t`. -/
def sem (p : Program DeMorgan.signature N g) (t : Nat) (w : Wire N g) :
    (Fin N → Bool) → Bool :=
  p.trace L.stageInterpretation L.inputValue w t

theorem sem_input (p : Program DeMorgan.signature N g) (t : Nat) (v : Fin N) :
    L.sem p t (Wire.input v) = fun c => L.fix (t - 1) c v :=
  rfl

theorem sem_gate (p : Program DeMorgan.signature N g) (t : Nat) (G : Fin g) :
    L.sem p t (Wire.gate G) =
      L.stageValue (p.lines G).op (fun m t => L.sem p t ((p.lines G).wires m)) t := by
  unfold sem
  rw [trace_gate]
  rfl

theorem sem_zero_gate (p : Program DeMorgan.signature N g) (G : Fin g) (c : Fin N → Bool) :
    L.sem p 0 (Wire.gate G) c =
      DeMorgan.interpretation (p.lines G).op fun m => L.sem p 0 ((p.lines G).wires m) c := by
  rw [sem_gate]
  rfl

/-- The function of a gate at index `s + 1` before forcing. -/
def preValue (p : Program DeMorgan.signature N g) (s : Nat) (G : Fin g) :
    (Fin N → Bool) → Bool :=
  fun c => DeMorgan.interpretation (p.lines G).op fun m =>
    L.sem p (s + 1) ((p.lines G).wires m) c

theorem sem_succ_gate (p : Program DeMorgan.signature N g) (s : Nat) (G : Fin g) :
    L.sem p (s + 1) (Wire.gate G) =
      if L.sem p s (Wire.gate G) (L.fix s fun _ => false) = true ∨ L.Bad s (L.preValue p s G)
      then fun _ => true else L.preValue p s G := by
  rw [L.sem_gate p (s + 1) G, L.sem_gate p s G]
  rfl

/-! ### One stage -/

/-- Hypotheses relating the previous stage, restricted by `fix s` (`prev`), to
the next stage (`next`) of a program without NOT gates. -/
structure StepHyp (p : Program DeMorgan.signature N g) (s : Nat)
    (prev next : Wire N g → (Fin N → Bool) → Bool) : Prop where
  no_not : ∀ G, (p.lines G).op ≠ .not
  prev_input : ∀ v c, prev (Wire.input v) c = L.fix s c v
  next_input : ∀ v c, next (Wire.input v) c = L.fix s c v
  prev_gate : ∀ G, (∀ c, prev (Wire.gate G) c =
      DeMorgan.interpretation (p.lines G).op fun m => prev ((p.lines G).wires m) c) ∨
    ∀ c, prev (Wire.gate G) c = true
  next_gate : ∀ G, next (Wire.gate G) =
    if prev (Wire.gate G) (fun _ => false) = true ∨
        L.Bad s (fun c => DeMorgan.interpretation (p.lines G).op fun m =>
          next ((p.lines G).wires m) c) then
      fun _ => true
    else fun c => DeMorgan.interpretation (p.lines G).op fun m => next ((p.lines G).wires m) c
  prev_mono : ∀ w, IsMonotone (prev w)

/-- An assignment sets at most one type-`s` variable to zero. -/
def Covers (s : Nat) (b : Fin N → Bool) : Prop :=
  ∀ u w, u ≠ w → L.IsType s u → L.IsType s w → b u = true ∨ b w = true

namespace StepHyp

variable {L} {p : Program DeMorgan.signature N g} {s : Nat}
  {prev next : Wire N g → (Fin N → Bool) → Bool}

theorem mono (h : L.StepHyp p s prev next) (w : Wire N g) : IsMonotone (next w) := by
  refine wire_induction p (P := fun w => IsMonotone (next w)) ?_ ?_ w
  · intro v a b hab ha
    rw [h.next_input] at ha ⊢
    exact L.isMonotone_fix_apply s v a b hab ha
  · intro G ih
    rw [h.next_gate G]
    split_ifs
    · intro _ _ _ _
      rfl
    · exact isMonotone_interpretation (h.no_not G) ih

theorem le (h : L.StepHyp p s prev next) (w : Wire N g) (c : Fin N → Bool)
    (hc : prev w c = true) : next w c = true := by
  revert c
  refine wire_induction p (P := fun w => ∀ c, prev w c = true → next w c = true) ?_ ?_ w
  · intro v c hc
    rwa [h.next_input, ← h.prev_input]
  · intro G ih c hc
    rw [h.next_gate G]
    split_ifs with hcond
    · rfl
    · rcases h.prev_gate G with hop | hone
      · rw [hop] at hc
        exact interpretation_mono (h.no_not G) (fun m => ih m c) hc
      · exact absurd (Or.inl (hone _)) hcond

theorem agree (h : L.StepHyp p s prev next) {b : Fin N → Bool} (hb : L.Covers s b)
    (w : Wire N g) : next w b = prev w b := by
  refine wire_induction p (P := fun w => next w b = prev w b) ?_ ?_ w
  · intro v
    rw [h.next_input, h.prev_input]
  · intro G ih
    have hargs : (fun m => next ((p.lines G).wires m) b) =
        fun m => prev ((p.lines G).wires m) b :=
      funext ih
    rw [h.next_gate G]
    split_ifs with hcond
    · rcases hcond with h0 | ⟨u, w, hne, hu, hw, hHu, hHw⟩
      · exact (h.prev_mono _ _ _ (assignmentLE_false b) h0).symm
      · have hH : (DeMorgan.interpretation (p.lines G).op fun m =>
            next ((p.lines G).wires m) b) = true := by
          have hmono := isMonotone_interpretation (h.no_not G)
            fun m => h.mono ((p.lines G).wires m)
          rcases hb u w hne hu hw with hbu | hbw
          · exact hmono _ _ (assignmentLE_single hbu) hHu
          · exact hmono _ _ (assignmentLE_single hbw) hHw
        rw [hargs] at hH
        rcases h.prev_gate G with hop | hone
        · rw [hop]
          exact hH.symm
        · exact (hone b).symm
    · rcases h.prev_gate G with hop | hone
      · rw [hop]
        exact congrArg _ hargs
      · exact absurd (Or.inl (hone _)) hcond

end StepHyp

/-! ### Covering assignments -/

/-- Raise every variable that does not create a product `x i k ∧ y k j` with
the variables already true in `c`. -/
def cover (i : Fin I) (j : Fin J) (c : Fin N → Bool) : Fin N → Bool :=
  fun v => c v || decide (∀ k, L.y k j ≠ v ∧ (L.x i k = v → c (L.y k j) = false))

theorem le_cover (i : Fin I) (j : Fin J) (c : Fin N → Bool) :
    AssignmentLE c (L.cover i j c) := by
  intro v hv
  simp [cover, hv]

theorem cover_y (i : Fin I) (j : Fin J) (c : Fin N → Bool) (k : Fin K) :
    L.cover i j c (L.y k j) = c (L.y k j) := by
  have hall : ¬ ∀ k', L.y k' j ≠ L.y k j ∧ (L.x i k' = L.y k j → c (L.y k' j) = false) :=
    fun hall => (hall k).1 rfl
  simp [cover, hall]

theorem cover_x (i : Fin I) (j : Fin J) (c : Fin N → Bool) (k : Fin K) :
    L.cover i j c (L.x i k) = (c (L.x i k) || !c (L.y k j)) := by
  have hall : (∀ k', L.y k' j ≠ L.x i k ∧ (L.x i k' = L.x i k → c (L.y k' j) = false)) ↔
      c (L.y k j) = false := by
    constructor
    · intro hall
      exact (hall k).2 rfl
    · intro hk k'
      refine ⟨fun h => L.x_ne_y i k k' j h.symm, fun h => ?_⟩
      rw [(L.x_inj h).2]
      exact hk
  unfold cover
  congr 1
  rw [Bool.eq_iff_iff, decide_eq_true_iff, hall]
  simp

theorem product_cover (T : Finset (Fin I × Fin K × Fin J)) (s : Nat) (i : Fin I) (j : Fin J)
    (c : Fin N → Bool) : L.product T s i j (L.cover i j c) = L.product T s i j c := by
  unfold product
  congr 1
  apply propext
  refine exists_congr fun k => and_congr_right fun _ => and_congr_right fun _ => ?_
  rw [L.cover_x, L.cover_y]
  cases c (L.x i k) <;> cases c (L.y k j) <;> simp

theorem cover_eq_false {s : Nat} {i : Fin I} {j : Fin J} {c : Fin N → Bool} {v : Fin N}
    (hv : L.IsType s v) (hb : L.cover i j c v = false) :
    ∃ k : Fin K, k.val = s ∧
      ((v = L.y k j ∧ c (L.y k j) = false) ∨ (v = L.x i k ∧ c (L.y k j) = true)) := by
  simp only [cover, Bool.or_eq_false_iff, decide_eq_false_iff_not, not_forall] at hb
  obtain ⟨hcv, k', hk'⟩ := hb
  rw [not_and_or, not_not, Classical.not_imp] at hk'
  rcases hv with ⟨i₁, k₁, hk₁, rfl⟩ | ⟨k₁, j₁, hk₁, rfl⟩
  · rcases hk' with hyx | ⟨hxx, hy⟩
    · exact absurd hyx.symm (L.x_ne_y _ _ _ _)
    · obtain ⟨rfl, rfl⟩ := L.x_inj hxx
      exact ⟨k', hk₁, Or.inr ⟨rfl, by simpa using hy⟩⟩
  · rcases hk' with hyy | ⟨hxy, -⟩
    · obtain ⟨rfl, rfl⟩ := L.y_inj hyy
      exact ⟨k', hk₁, Or.inl ⟨rfl, hcv⟩⟩
    · exact absurd hxy (L.x_ne_y _ _ _ _)

theorem covers_cover (s : Nat) (i : Fin I) (j : Fin J) (c : Fin N → Bool) :
    L.Covers s (L.cover i j c) := by
  intro u w hne hu hw
  by_contra hcon
  rw [not_or, Bool.not_eq_true, Bool.not_eq_true] at hcon
  obtain ⟨k, hk, hku⟩ := L.cover_eq_false hu hcon.1
  obtain ⟨k', hk', hkw⟩ := L.cover_eq_false hw hcon.2
  obtain rfl : k = k' := Fin.ext (hk.trans hk'.symm)
  rcases hku with ⟨rfl, hu'⟩ | ⟨rfl, hu'⟩ <;> rcases hkw with ⟨rfl, hw'⟩ | ⟨rfl, hw'⟩
  · exact hne rfl
  · rw [hu'] at hw'
    exact absurd hw' (by simp)
  · rw [hu'] at hw'
    exact absurd hw' (by simp)
  · exact hne rfl

namespace StepHyp

variable {L} {p : Program DeMorgan.signature N g} {s : Nat}
  {prev next : Wire N g → (Fin N → Bool) → Bool}

/-- Forcing preserves every output that computes a restricted product entry. -/
theorem next_output (h : L.StepHyp p s prev next) (T : Finset (Fin I × Fin K × Fin J))
    (o : Wire N g) (i : Fin I) (j : Fin J) (ho : ∀ c, prev o c = L.product T s i j c)
    (c : Fin N → Bool) : next o c = L.product T s i j c := by
  cases hc : L.product T s i j c
  · by_contra hne
    rw [Bool.not_eq_false] at hne
    have hup := h.mono o _ _ (L.le_cover i j c) hne
    rw [h.agree (L.covers_cover s i j c), ho, L.product_cover, hc] at hup
    exact absurd hup (by simp)
  · exact h.le o c ((ho c).trans hc)

end StepHyp

/-! ### All stages -/

theorem stepHyp_of_mono (p : Program DeMorgan.signature N g)
    (hp : ∀ G, (p.lines G).op ≠ .not) (s : Nat) (hmono : ∀ w, IsMonotone (L.sem p s w)) :
    L.StepHyp p s (fun w c => L.sem p s w (L.fix s c)) (L.sem p (s + 1)) where
  no_not := hp
  prev_input v c := by
    simp only [sem_input]
    rw [L.fix_fix (Nat.sub_le s 1)]
  next_input v c := by
    simp [sem_input]
  prev_gate G := by
    cases s with
    | zero =>
        left
        intro c
        exact L.sem_zero_gate p G _
    | succ r =>
        show (∀ c, L.sem p (r + 1) (Wire.gate G) (L.fix (r + 1) c) = _) ∨
          ∀ c, L.sem p (r + 1) (Wire.gate G) (L.fix (r + 1) c) = true
        rw [L.sem_succ_gate p r G]
        split_ifs
        · right
          intro c
          rfl
        · left
          intro c
          rfl
  next_gate G := by
    rw [L.sem_succ_gate p s G]
    rfl
  prev_mono w := fun _ _ hab ha => hmono w _ _ (L.fix_mono s hab) ha

theorem sem_mono (p : Program DeMorgan.signature N g) (hp : ∀ G, (p.lines G).op ≠ .not) :
    ∀ t w, IsMonotone (L.sem p t w)
  | 0, w => by
      refine wire_induction p (P := fun w => IsMonotone (L.sem p 0 w)) ?_ ?_ w
      · intro v
        exact L.isMonotone_fix_apply (0 - 1) v
      · intro G ih
        have hG : L.sem p 0 (Wire.gate G) = fun c =>
            DeMorgan.interpretation (p.lines G).op fun m => L.sem p 0 ((p.lines G).wires m) c :=
          funext (L.sem_zero_gate p G)
        rw [hG]
        exact isMonotone_interpretation (hp G) ih
  | s + 1, w => (L.stepHyp_of_mono p hp s (sem_mono p hp s)).mono w

theorem stepHyp (p : Program DeMorgan.signature N g) (hp : ∀ G, (p.lines G).op ≠ .not)
    (s : Nat) : L.StepHyp p s (fun w c => L.sem p s w (L.fix s c)) (L.sem p (s + 1)) :=
  L.stepHyp_of_mono p hp s (L.sem_mono p hp s)

/-- Index `0` is the ordinary Boolean evaluation. -/
theorem sem_zero (p : Program DeMorgan.signature N g) (w : Wire N g) (c : Fin N → Bool) :
    L.sem p 0 w c = p.trace DeMorgan.interpretation c w := by
  refine wire_induction p
    (P := fun w => L.sem p 0 w c = p.trace DeMorgan.interpretation c w) ?_ ?_ w
  · intro v
    simp [sem_input, fix_zero]
  · intro G ih
    rw [L.sem_zero_gate, trace_gate]
    exact congrArg _ (funext ih)

/-- At index `t`, the outputs compute the product over the triples of type
`≥ t - 1`. -/
theorem sem_output {M : Nat} (T : Finset (Fin I × Fin K × Fin J)) (z : Fin I → Fin J → Fin M)
    (circuit : Circuit DeMorgan.signature N M) (hp : ∀ G, (circuit.program.lines G).op ≠ .not)
    (computes : ∀ a i j, circuit.eval DeMorgan.interpretation a (z i j) =
      decide (∃ k, (i, k, j) ∈ T ∧ a (L.x i k) = true ∧ a (L.y k j) = true)) :
    ∀ t i j c, L.sem circuit.program t (circuit.outputs (z i j)) c = L.product T (t - 1) i j c
  | 0, i, j, c => by
      rw [L.sem_zero]
      have := computes c i j
      simp only [Circuit.eval, Function.comp_apply] at this
      rw [this]
      simp [product]
  | s + 1, i, j, c => by
      rw [Nat.add_sub_cancel]
      refine (L.stepHyp circuit.program hp s).next_output T _ i j (fun c => ?_) c
      rw [sem_output T z circuit hp computes s i j, L.product_fix T (Nat.sub_le s 1)]

/-- A wire that is one at index `s + 1` on the restriction `fix s' c` is one at
the later index `s' + 1` on `c`. -/
theorem sem_of_lt (p : Program DeMorgan.signature N g) (hp : ∀ G, (p.lines G).op ≠ .not)
    {s s' : Nat} (hlt : s < s') (w : Wire N g) (c : Fin N → Bool)
    (h : L.sem p (s + 1) w (L.fix s' c) = true) : L.sem p (s' + 1) w c = true := by
  induction s', hlt using Nat.le_induction generalizing c with
  | base => exact (L.stepHyp p hp (s + 1)).le w c h
  | succ s' hs ih =>
      rw [← L.fix_fix (s' := s') (Nat.le_succ s') c] at h
      exact (L.stepHyp p hp (s' + 1)).le w c (ih _ h)

/-- At index `s + 1` every wire is constant one or has at most one type-`s`
implicant of length one. -/
theorem sem_good (p : Program DeMorgan.signature N g) (s : Nat) (w : Wire N g) :
    (∀ c, L.sem p (s + 1) w c = true) ∨ ¬ L.Bad s (L.sem p (s + 1) w) := by
  cases w with
  | input v =>
      by_cases hT : L.FixedTrue s v
      · left
        intro c
        simp [sem_input, L.fix_of_fixedTrue hT]
      · right
        rintro ⟨u, w, hne, -, -, hu, hw⟩
        simp only [sem_input, Nat.add_sub_cancel] at hu hw
        by_cases hF : L.FixedFalse s v
        · rw [L.fix_of_fixedFalse hF] at hu
          exact absurd hu (by simp)
        · rw [L.fix_of_free hT hF] at hu hw
          simp only [single, decide_eq_true_eq] at hu hw
          exact hne (hu.symm.trans hw)
  | gate G =>
      rw [L.sem_succ_gate p s G]
      split_ifs with hcond
      · left
        intro c
        rfl
      · right
        intro hbad
        exact hcond (Or.inr hbad)

/-! ### Creators -/

/-- `f` accepts `{x i k, y k j}` but neither `{x i k}` nor `{y k j}`; for a
monotone `f` this says that `x i k ∧ y k j` is a prime implicant. -/
def IsPrimePair (i : Fin I) (k : Fin K) (j : Fin J) (f : (Fin N → Bool) → Bool) : Prop :=
  f (pair (L.x i k) (L.y k j)) = true ∧ f (single (L.x i k)) = false ∧
    f (single (L.y k j)) = false

/-- A gate whose function at index `k + 1` has the prime implicant `x i k ∧ y k j`
while none of its arguments has it. -/
def Creator (p : Program DeMorgan.signature N g) (i : Fin I) (k : Fin K) (j : Fin J)
    (G : Fin g) : Prop :=
  L.IsPrimePair i k j (L.sem p (k.val + 1) (Wire.gate G)) ∧
    ∀ m, ¬ L.IsPrimePair i k j (L.sem p (k.val + 1) ((p.lines G).wires m))

theorem not_isPrimePair_input (p : Program DeMorgan.signature N g) (i : Fin I) (k : Fin K)
    (j : Fin J) (v : Fin N) : ¬ L.IsPrimePair i k j (L.sem p (k.val + 1) (Wire.input v)) := by
  rintro ⟨hp, hx, hy⟩
  simp only [sem_input, Nat.add_sub_cancel] at hp hx hy
  by_cases hT : L.FixedTrue k.val v
  · rw [L.fix_of_fixedTrue hT] at hx
    exact absurd hx (by simp)
  by_cases hF : L.FixedFalse k.val v
  · rw [L.fix_of_fixedFalse hF] at hp
    exact absurd hp (by simp)
  rw [L.fix_of_free hT hF] at hp hx hy
  simp only [pair, single, decide_eq_true_eq, decide_eq_false_iff_not] at hp hx hy
  rcases hp with hp | hp
  · exact hx hp
  · exact hy hp

theorem exists_creator (p : Program DeMorgan.signature N g) (i : Fin I) (k : Fin K) (j : Fin J)
    (w : Wire N g) (hw : L.IsPrimePair i k j (L.sem p (k.val + 1) w)) :
    ∃ G, L.Creator p i k j G := by
  revert hw
  refine wire_induction p
    (P := fun w => L.IsPrimePair i k j (L.sem p (k.val + 1) w) → ∃ G, L.Creator p i k j G)
    ?_ ?_ w
  · intro v hv
    exact absurd hv (L.not_isPrimePair_input p i k j v)
  · intro G ih hG
    by_cases hm : ∃ m, L.IsPrimePair i k j (L.sem p (k.val + 1) ((p.lines G).wires m))
    · obtain ⟨m, hm⟩ := hm
      exact ih m hm
    · exact ⟨G, hG, not_exists.mp hm⟩

theorem isPrimePair_product (T : Finset (Fin I × Fin K × Fin J)) {i : Fin I} {k : Fin K}
    {j : Fin J} (hT : (i, k, j) ∈ T) : L.IsPrimePair i k j (L.product T k.val i j) := by
  refine ⟨?_, ?_, ?_⟩
  · simp only [product, decide_eq_true_eq]
    exact ⟨k, hT, le_rfl, by simp [pair], by simp [pair]⟩
  · simp only [product, decide_eq_false_iff_not, not_exists, not_and]
    intro k' _ _ _
    simp [single, (L.x_ne_y i k k' j).symm]
  · simp only [product, decide_eq_false_iff_not, not_exists, not_and]
    intro k' _ _ hx
    simp [single, L.x_ne_y i k' k j] at hx

namespace Creator

variable {L} {p : Program DeMorgan.signature N g} {i i' : Fin I} {k k' : Fin K} {j j' : Fin J}
  {G : Fin g}

/-- A creator is an AND gate; one argument has the implicant `x i k`, another
`y k j`, and no argument is constant one. -/
theorem spec (hp : ∀ G, (p.lines G).op ≠ .not) (hc : L.Creator p i k j G) :
    (p.lines G).op = .and ∧
      (∃ a b, a ≠ b ∧
        L.sem p (k.val + 1) ((p.lines G).wires a) (single (L.x i k)) = true ∧
        L.sem p (k.val + 1) ((p.lines G).wires b) (single (L.y k j)) = true) ∧
      ∀ m, ¬ ∀ c, L.sem p (k.val + 1) ((p.lines G).wires m) c = true := by
  obtain ⟨⟨hpair, hx, hy⟩, hargs⟩ := hc
  have hG : L.sem p (k.val + 1) (Wire.gate G) = L.preValue p k.val G := by
    rw [L.sem_succ_gate p k.val G] at hx ⊢
    split_ifs at hx ⊢
    rfl
  rw [hG] at hpair hx hy
  exact creator_shape (hp G) (fun m => L.sem p (k.val + 1) ((p.lines G).wires m))
    hpair hx hy hargs

/-- Two triples of the same type have distinct creators. -/
theorem unique (hp : ∀ G, (p.lines G).op ≠ .not) (h₁ : L.Creator p i k j G)
    (h₂ : L.Creator p i' k j' G) : i = i' ∧ j = j' := by
  obtain ⟨hand, ⟨a₁, b₁, hab₁, ha₁, hb₁⟩, hnc⟩ := h₁.spec hp
  obtain ⟨-, ⟨a₂, b₂, hab₂, ha₂, hb₂⟩, -⟩ := h₂.spec hp
  have good : ∀ m, ¬ L.Bad k.val (L.sem p (k.val + 1) ((p.lines G).wires m)) :=
    fun m => (L.sem_good p k.val _).resolve_left (hnc m)
  have two : ∀ a b c : Fin (DeMorgan.arity (p.lines G).op), a ≠ b → c = a ∨ c = b := by
    have h2 : DeMorgan.arity (p.lines G).op = 2 := by rw [hand]; rfl
    intro a b c hab
    have := Fin.val_ne_of_ne hab
    have := a.isLt
    have := b.isLt
    have := c.isLt
    rw [Fin.ext_iff, Fin.ext_iff]
    omega
  have hx : ∀ {i i'}, i ≠ i' → L.x i k ≠ L.x i' k := fun hne h => hne (L.x_inj h).1
  have hy : ∀ {j j'}, j ≠ j' → L.y k j ≠ L.y k j' := fun hne h => hne (L.y_inj h).2
  rcases two a₁ b₁ a₂ hab₁ with ha | ha
  · subst ha
    have hb : b₂ = b₁ :=
      (two a₂ b₁ b₂ hab₁).resolve_left fun h => hab₂ h.symm
    subst hb
    constructor
    · by_contra hne
      exact good a₂ ⟨_, _, hx hne, L.isType_x i k, L.isType_x i' k, ha₁, ha₂⟩
    · by_contra hne
      exact good b₂ ⟨_, _, hy hne, L.isType_y k j, L.isType_y k j', hb₁, hb₂⟩
  · rw [ha] at ha₂
    exact absurd ⟨_, _, (L.x_ne_y i' k k j).symm, L.isType_y k j, L.isType_x i' k, hb₁, ha₂⟩
      (good b₁)

/-- A creator at one stage is not a creator at any later stage. -/
theorem not_creator_of_lt (hp : ∀ G, (p.lines G).op ≠ .not) (h₁ : L.Creator p i k j G)
    (hlt : k.val < k'.val) : ¬ L.Creator p i' k' j' G := by
  intro h₂
  obtain ⟨-, ⟨a, -, -, ha, -⟩, -⟩ := h₁.spec hp
  obtain ⟨-, -, hnc⟩ := h₂.spec hp
  exact hnc a fun c => L.sem_of_lt p hp hlt _ c
    (L.sem_mono p hp (k.val + 1) _ _ _ (assignmentLE_single (L.fix_x_of_lt hlt c)) ha)

end Creator

end Layout

/-- Distinct AND gates indexed by the triples of `T` bound the AND-gate count. -/
theorem card_le_cost (p : Program DeMorgan.signature N g) (T : Finset (Fin I × Fin K × Fin J))
    (creator : T → Fin g) (hand : ∀ t, (p.lines (creator t)).op = .and)
    (hinj : Function.Injective creator) : T.card ≤ p.cost DeMorgan.andCost := by
  rw [Program.cost_eq_sum_lines]
  have hsum : ∑ G, DeMorgan.andCost (p.lines G).op =
      (Finset.univ.filter fun G => (p.lines G).op = .and).card := by
    rw [Finset.card_filter]
    refine Finset.sum_congr rfl fun G _ => ?_
    cases (p.lines G).op <;> rfl
  rw [hsum, ← Fintype.card_coe T, ← Fintype.card_subtype]
  exact Fintype.card_le_of_injective (fun t => ⟨creator t, hand t⟩)
    fun t t' h => hinj (congrArg Subtype.val h)

/-- Every De Morgan circuit without NOT gates computing the partial Boolean
product over the triples of `T`, laid out injectively among its inputs, has at
least `|T|` AND gates. -/
theorem card_le_andCost (L : Layout N I J K) (T : Finset (Fin I × Fin K × Fin J)) {M : Nat}
    (z : Fin I → Fin J → Fin M) (circuit : Circuit DeMorgan.signature N M)
    (monotone : circuit.cost DeMorgan.notCost = 0)
    (computes : ∀ a i j, circuit.eval DeMorgan.interpretation a (z i j) =
      decide (∃ k, (i, k, j) ∈ T ∧ a (L.x i k) = true ∧ a (L.y k j) = true)) :
    T.card ≤ circuit.cost DeMorgan.andCost := by
  have hp := lines_ne_not_of_cost_eq_zero circuit.program monotone
  have hex : ∀ t : T, ∃ G, L.Creator circuit.program t.1.1 t.1.2.1 t.1.2.2 G := by
    rintro ⟨⟨i, k, j⟩, ht⟩
    refine L.exists_creator circuit.program i k j (circuit.outputs (z i j)) ?_
    have hout : L.sem circuit.program (k.val + 1) (circuit.outputs (z i j)) =
        L.product T k.val i j := by
      funext c
      rw [L.sem_output T z circuit hp computes, Nat.add_sub_cancel]
    rw [hout]
    exact L.isPrimePair_product T ht
  choose creator hcreator using hex
  refine card_le_cost circuit.program T creator (fun t => ((hcreator t).spec hp).1) ?_
  rintro ⟨⟨i, k, j⟩, ht⟩ ⟨⟨i', k', j'⟩, ht'⟩ heq
  have h₁ := hcreator ⟨(i, k, j), ht⟩
  have h₂ := hcreator ⟨(i', k', j'), ht'⟩
  rw [heq] at h₁
  rcases lt_trichotomy k.val k'.val with hlt | hk | hgt
  · exact absurd h₂ (h₁.not_creator_of_lt hp hlt)
  · obtain rfl : k = k' := Fin.ext hk
    obtain ⟨rfl, rfl⟩ := h₁.unique hp h₂
    rfl
  · exact absurd h₁ (h₂.not_creator_of_lt hp hgt)

/-! ### AND/OR circuits -/

/-- The binary AND/OR basis as the negation-free binary part of the De Morgan
basis: each operation becomes the single De Morgan gate of the same name. -/
def ofAndOr : Translation AndOr.signature DeMorgan.signature where
  operation
    | .and => ⟨Program.empty.gate ⟨.and, fun m => Wire.input m⟩, fun _ => Wire.gate 0⟩
    | .or => ⟨Program.empty.gate ⟨.or, fun m => Wire.input m⟩, fun _ => Wire.gate 0⟩

theorem ofAndOr_pull : ofAndOr.pull DeMorgan.interpretation = AndOr.boolInterpretation := by
  funext op input
  cases op <;> rfl

theorem ofAndOr_pullCost_andCost : ofAndOr.pullCost DeMorgan.andCost = AndOr.andCost := by
  funext op
  cases op <;> rfl

theorem ofAndOr_pullCost_notCost : ofAndOr.pullCost DeMorgan.notCost = fun _ => 0 := by
  funext op
  cases op <;> rfl

/-- Every AND/OR circuit computing the Boolean product of an `I × K` matrix and a
`K × J` matrix, laid out injectively among its inputs, has at least `I * J * K`
AND gates. -/
theorem mul_mul_le_andCost (L : Layout N I J K) {M : Nat} (z : Fin I → Fin J → Fin M)
    (circuit : Circuit AndOr.signature N M)
    (computes : ∀ a i j, circuit.eval AndOr.boolInterpretation a (z i j) =
      decide (∃ k, a (L.x i k) = true ∧ a (L.y k j) = true)) :
    I * J * K ≤ circuit.cost AndOr.andCost := by
  have hcard := card_le_andCost L Finset.univ z (ofAndOr.compile circuit) ?_ ?_
  · rw [Translation.compile_cost, ofAndOr_pullCost_andCost] at hcard
    have hIJK : I * J * K = I * (K * J) := by
      rw [Nat.mul_assoc, Nat.mul_comm J K]
    simpa [hIJK, Finset.card_univ, Fintype.card_prod] using hcard
  · rw [Translation.compile_cost, ofAndOr_pullCost_notCost, Circuit.cost,
      Program.cost_eq_sum_lines]
    simp
  · intro a i j
    rw [Translation.compile_eval, ofAndOr_pull, computes]
    simp

end

end Internal
end MatrixProduct
end Monotone
end Algebraic
