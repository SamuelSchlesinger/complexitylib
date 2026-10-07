/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module
public import Complexitylib.Circuits.ExactFourier.Internal.Words

/-!
# Exact Fourier circuits: shears

Adapted from OpenAI's formalization at revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
Source: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/FourierCircuit/Shears.lean

Imports, namespaces, module visibility, documentation, and formatting are adapted
for complexitylib. The source theorem statements and mathematical arguments are retained.
-/

@[expose] public section

namespace Complexity

section
namespace ExactFourier

/-- Each internal gate starts at an arbitrary dirty value, and its computed linear
combination is added to that value. The literal zero remains literal zero. -/
def Program.dirtyEval {n : ℕ} : {k : ℕ} → Program n k →
    (Fin n → ℂ) → (Fin k → ℂ) → (Fin (n + 1 + k) → ℂ)
  | 0, .nil, x, _ => Fin.snoc x 0
  | k + 1, .step p g, x, z =>
      let v := p.dirtyEval x (Fin.init z)
      Fin.snoc v (z (Fin.last k) + g.eval v)

theorem Gate.eval_add {w : ℕ} (g : Gate w) (v v' : Fin w → ℂ) :
    g.eval (v + v') = g.eval v + g.eval v' := by
  cases g <;> simp only [Gate.eval, Pi.add_apply] <;> ring

theorem snoc_add {n : ℕ} (v v' : Fin n → ℂ) (a a' : ℂ) :
    (Fin.snoc (v + v') (a + a') : Fin (n + 1) → ℂ) =
      (Fin.snoc v a : Fin (n + 1) → ℂ) + (Fin.snoc v' a' : Fin (n + 1) → ℂ) := by
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i <;> simp

theorem Program.dirtyEval_add {n k : ℕ} (p : Program n k)
    (x x' : Fin n → ℂ) (z z' : Fin k → ℂ) :
    p.dirtyEval (x + x') (z + z') = p.dirtyEval x z + p.dirtyEval x' z' := by
  induction p with
  | nil => simpa [Program.dirtyEval] using snoc_add x x' 0 0
  | @step k p g ih =>
      simp only [Program.dirtyEval]
      rw [show Fin.init (z + z') = Fin.init z + Fin.init z' from rfl,
        ih, Gate.eval_add]
      convert snoc_add (p.dirtyEval x (Fin.init z)) (p.dirtyEval x' (Fin.init z'))
        (z (Fin.last k) + g.eval (p.dirtyEval x (Fin.init z)))
        (z' (Fin.last k) + g.eval (p.dirtyEval x' (Fin.init z'))) using 1 ;
        (try simp only [Pi.add_apply]) ; congr 1 ; ring

theorem Program.dirtyEval_clean {n k : ℕ} (p : Program n k) (x : Fin n → ℂ) :
    p.dirtyEval x 0 = p.eval x := by
  induction p with
  | nil => rfl
  | @step k p g ih =>
      simp only [Program.dirtyEval, Program.eval]
      rw [show Fin.init (0 : Fin (k + 1) → ℂ) = 0 from rfl, ih]
      simp

/-- Exact identity behind the two replays (`fft:dirty-forward`, `fft:dirty-output`). -/
theorem Program.dirtyEval_split {n k : ℕ} (p : Program n k)
    (x : Fin n → ℂ) (z : Fin k → ℂ) :
    p.dirtyEval x z = p.eval x + p.dirtyEval 0 z := by
  simpa only [add_zero, zero_add, Program.dirtyEval_clean] using
    p.dirtyEval_add x 0 0 z

/-- A scalar circuit with independently specified input and output widths. -/
structure LinearDAG (n a : ℕ) where
  /-- The number of charged scalar gates. -/
  size : ℕ
  /-- The scalar straight-line program containing exactly `size` gates. -/
  program : Program n size
  /-- The available wire selected for each output coordinate. -/
  outputs : Fin a → Fin (n + 1 + size)

/-- Evaluate the program and read its designated output wires. -/
def LinearDAG.eval {n a : ℕ} (C : LinearDAG n a) (x : Fin n → ℂ) : Fin a → ℂ :=
  fun i => C.program.eval x (C.outputs i)

end ExactFourier

namespace ExactFourier

/-- An elementary operation adding a scalar multiple of one coordinate to another. -/
abbrev Shear (ι : Type*) := Matrix.TransvectionStruct ι ℂ

/-- Apply one elementary shear to a vector. -/
noncomputable def Shear.act {ι : Type*} (t : Shear ι) (v : ι → ℂ) : ι → ℂ := by
  classical
  exact fun i => if i = t.i then v i + t.c * v t.j else v i

/-- Execute elementary shears from left to right on the input vector. -/
noncomputable def runShears {ι : Type*} (W : List (Shear ι)) (v : ι → ℂ) : ι → ℂ :=
  W.foldl (fun v t => t.act v) v

@[simp] theorem runShears_nil {ι : Type*} (v : ι → ℂ) : runShears [] v = v := rfl
@[simp] theorem runShears_cons {ι : Type*} (s : Shear ι) (W : List (Shear ι))
    (v : ι → ℂ) : runShears (s :: W) v = runShears W (s.act v) := rfl
@[simp] theorem runShears_append {ι : Type*} (W V : List (Shear ι)) (v : ι → ℂ) :
    runShears (W ++ V) v = runShears V (runShears W v) := List.foldl_append

@[simp] theorem Shear.act_self {ι : Type*} (s : Shear ι) (v : ι → ℂ) :
    s.act v s.i = v s.i + s.c * v s.j := by simp [Shear.act]

theorem Shear.act_other {ι : Type*} (s : Shear ι) (v : ι → ℂ) {a : ι}
    (h : a ≠ s.i) : s.act v a = v a := by simp [Shear.act, h]

@[simp] theorem Shear.act_source {ι : Type*} (s : Shear ι) (v : ι → ℂ) :
    s.act v s.j = v s.j := s.act_other v s.hij.symm

@[simp] theorem Shear.inv_act_act {ι : Type*} (s : Shear ι) (v : ι → ℂ) :
    Shear.act s.inv (s.act v) = v := by
  classical
  funext a
  by_cases h : a = s.i
  · subst a
    simp [Shear.act, Matrix.TransvectionStruct.inv, s.hij.symm]
  · simp [Shear.act, Matrix.TransvectionStruct.inv, h]

/-- Reverse the execution order and invert every shear to undo a computation. -/
noncomputable def reverseShears {ι : Type*} (W : List (Shear ι)) : List (Shear ι) :=
  W.reverse.map Matrix.TransvectionStruct.inv

@[simp] theorem reverseShears_length {ι : Type*} (W : List (Shear ι)) :
    (reverseShears W).length = W.length := by simp [reverseShears]

@[simp] theorem runShears_reverse {ι : Type*} (W : List (Shear ι)) (v : ι → ℂ) :
    runShears (reverseShears W) (runShears W v) = v := by
  induction W generalizing v with
  | nil => rfl
  | cons s W ih =>
      simp only [reverseShears, List.reverse_cons, List.map_append, List.map_singleton,
        runShears_append, runShears_cons, runShears_nil]
      rw [show W.reverse.map Matrix.TransvectionStruct.inv = reverseShears W from rfl,
        ih, Shear.inv_act_act]

/-- `none` is the literal input zero, not a physical workspace coordinate. -/
def readCoord {ι : Type*} (r : Option ι) (v : ι → ℂ) : ℂ := r.elim 0 v

theorem readCoord_congr_except {ι : Type*} (d : ι) (r : Option ι)
    (h : ∀ i, r = some i → d ≠ i) (v v' : ι → ℂ)
    (hv : ∀ i, i ≠ d → v' i = v i) : readCoord r v' = readCoord r v := by
  cases r with
  | none => rfl
  | some i => exact hv i (h i rfl).symm

/-- Adding one permitted reference uses at most one elementary coordinate shear. -/
theorem add_reference {ι : Type*} (d : ι) (r : Option ι) (c : ℂ)
    (h : ∀ i, r = some i → d ≠ i) :
    ∃ W : List (Shear ι), W.length ≤ 1 ∧ ∀ v : ι → ℂ,
      runShears W v d = v d + c * readCoord r v ∧
      ∀ i, i ≠ d → runShears W v i = v i := by
  classical
  cases r with
  | none =>
      refine ⟨[], by simp, ?_⟩
      intro v
      simp [readCoord]
  | some j =>
      refine ⟨[⟨d, j, h j rfl, c⟩], by simp, ?_⟩
      intro v
      constructor
      · simp [readCoord, Shear.act]
      · intro i hi
        simp [Shear.act, hi]

/-- A gate's two (or one) distinct-from-destination reads, with repeated operands allowed. -/
theorem add_gate {ι : Type*} {w : ℕ} (d : ι) (refs : Fin w → Option ι)
    (h : ∀ a j, refs a = some j → d ≠ j) (g : Gate w) :
    ∃ W : List (Shear ι), W.length ≤ 2 ∧ ∀ v : ι → ℂ,
      runShears W v d = v d + g.eval (fun a => readCoord (refs a) v) ∧
      ∀ i, i ≠ d → runShears W v i = v i := by
  classical
  cases g with
  | scale c a =>
      obtain ⟨W, hw, he⟩ := add_reference d (refs a) c (h a)
      exact ⟨W, hw.trans (by omega), he⟩
  | add a b =>
      obtain ⟨W, hw, he⟩ := add_reference d (refs a) 1 (h a)
      obtain ⟨V, hv, hf⟩ := add_reference d (refs b) 1 (h b)
      refine ⟨W ++ V, by simp only [List.length_append]; omega, ?_⟩
      intro v
      rw [runShears_append]
      constructor
      · rw [(hf _).1, (he v).1,
          readCoord_congr_except d (refs b) (h b) v (runShears W v) (he v).2]
        simp only [Gate.eval, one_mul]
        ring
      · intro i hi
        rw [(hf _).2 i hi, (he v).2 i hi]
  | sub a b =>
      obtain ⟨W, hw, he⟩ := add_reference d (refs a) 1 (h a)
      obtain ⟨V, hv, hf⟩ := add_reference d (refs b) (-1) (h b)
      refine ⟨W ++ V, by simp only [List.length_append]; omega, ?_⟩
      intro v
      rw [runShears_append]
      constructor
      · rw [(hf _).1, (he v).1,
          readCoord_congr_except d (refs b) (h b) v (runShears W v) (he v).2]
        simp only [Gate.eval, one_mul, neg_mul]
        ring
      · intro i hi
        rw [(hf _).2 i hi, (he v).2 i hi]

end ExactFourier

namespace ExactFourier

/-- Combine the input vector, free zero, and scratch coordinates into one wire vector. -/
def available {n k : ℕ} (x : Fin n → ℂ) (z : Fin k → ℂ) : Fin (n + 1 + k) → ℂ :=
  Fin.addCases (Fin.snoc x 0) z

/-- The scratch-coordinate outputs of a program started with arbitrary scratch values. -/
def Program.dirtyScratch {n k : ℕ} (p : Program n k)
    (x : Fin n → ℂ) (z : Fin k → ℂ) : Fin k → ℂ :=
  fun i => p.dirtyEval x z (Fin.natAdd (n + 1) i)

theorem Program.dirtyEval_input {n k : ℕ} (p : Program n k)
    (x : Fin n → ℂ) (z : Fin k → ℂ) (i : Fin (n + 1)) :
    p.dirtyEval x z (Fin.castAdd k i) = (Fin.snoc x 0 : Fin (n + 1) → ℂ) i := by
  induction p with
  | nil => simp [Program.dirtyEval]
  | @step k p g ih =>
      change (Fin.snoc (p.dirtyEval x (Fin.init z)) _ : Fin (n + 1 + k + 1) → ℂ)
        (Fin.castSucc (Fin.castAdd k i)) = _
      rw [Fin.snoc_castSucc, ih]

theorem Program.dirtyEval_available {n k : ℕ} (p : Program n k)
    (x : Fin n → ℂ) (z : Fin k → ℂ) :
    p.dirtyEval x z = available x (p.dirtyScratch x z) := by
  funext i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · simp [available, Program.dirtyEval_input]
  · simp [available, Program.dirtyScratch]

@[simp] theorem Program.dirtyScratch_step_cast {n k : ℕ} (p : Program n k)
    (g : Gate (n + 1 + k)) (x : Fin n → ℂ) (z : Fin (k + 1) → ℂ) (i : Fin k) :
    (p.step g).dirtyScratch x z i.castSucc = p.dirtyScratch x (Fin.init z) i := by
  change (Fin.snoc (p.dirtyEval x (Fin.init z)) _ : Fin (n + 1 + k + 1) → ℂ)
    (Fin.castSucc (Fin.natAdd (n + 1) i)) = _
  rw [Fin.snoc_castSucc]
  rfl

@[simp] theorem Program.dirtyScratch_step_last {n k : ℕ} (p : Program n k)
    (g : Gate (n + 1 + k)) (x : Fin n → ℂ) (z : Fin (k + 1) → ℂ) :
    (p.step g).dirtyScratch x z (Fin.last k) =
      z (Fin.last k) + g.eval (p.dirtyEval x (Fin.init z)) := by
  change (Fin.snoc (p.dirtyEval x (Fin.init z)) _ : Fin (n + 1 + k + 1) → ℂ)
    (Fin.last (n + 1 + k)) = _
  rw [Fin.snoc_last]

/-- Read the selected input coordinates when enabled, using zeros otherwise. -/
def replayInputs {ι : Type*} {n : ℕ} (enabled : Bool) (xs : Fin n → ι)
    (v : ι → ℂ) : Fin n → ℂ := fun i => if enabled then v (xs i) else 0

/-- Map source inputs and scratch wires to ambient coordinates, respecting the enable flag. -/
def referenceMap {ι : Type*} {n k : ℕ} (enabled : Bool) (xs : Fin n → ι)
    (zs : Fin k → ι) : Fin (n + 1 + k) → Option ι :=
  Fin.addCases (Fin.snoc (fun i => if enabled then some (xs i) else none) none)
    (fun j => some (zs j))

theorem read_referenceMap {ι : Type*} {n k : ℕ} (enabled : Bool)
    (xs : Fin n → ι) (zs : Fin k → ι) (v : ι → ℂ) :
    (fun a => readCoord (referenceMap enabled xs zs a) v) =
      available (replayInputs enabled xs v) (v ∘ zs) := by
  funext a
  refine Fin.addCases (fun i => ?_) (fun j => ?_) a
  · refine Fin.lastCases ?_ (fun i => ?_) i
    · simp [referenceMap, available, readCoord]
    · cases enabled <;> simp [referenceMap, available, replayInputs, readCoord]
  · simp [referenceMap, available, readCoord]

theorem referenceMap_avoids {ι : Type*} {n k : ℕ} (enabled : Bool)
    (xs : Fin n → ι) (zs : Fin k → ι) (d : ι)
    (hx : ∀ i, d ≠ xs i) (hz : ∀ j, d ≠ zs j) :
    ∀ a j, referenceMap enabled xs zs a = some j → d ≠ j := by
  intro a
  refine Fin.addCases (fun i => ?_) (fun i => ?_) a
  · refine Fin.lastCases ?_ (fun i => ?_) i
    · simp [referenceMap]
    · cases enabled <;> simp [referenceMap, hx]
  · simpa [referenceMap] using hz i

/-- The full forward-sweep construction, with one coordinate per gate and NO zero
register. Its exact semantic statement is uniform in arbitrary dirty initial values. -/
theorem Program.dirtySweep_exists {ι : Type*} {n k : ℕ} (p : Program n k)
    (enabled : Bool) (xs : Fin n → ι) (zs : Fin k → ι)
    (hz : Function.Injective zs) (hxz : ∀ i j, xs i ≠ zs j) :
    ∃ W : List (Shear ι), W.length ≤ 2 * k ∧ ∀ v : ι → ℂ,
      (∀ j, runShears W v (zs j) =
        p.dirtyScratch (replayInputs enabled xs v) (v ∘ zs) j) ∧
      (∀ r, (∀ j, r ≠ zs j) → runShears W v r = v r) := by
  classical
  induction p with
  | nil =>
      refine ⟨[], by simp, ?_⟩
      intro v
      exact ⟨fun j => Fin.elim0 j, fun _ _ => rfl⟩
  | @step k p g ih =>
      let zs' : Fin k → ι := fun j => zs j.castSucc
      have hzi : Function.Injective zs' := hz.comp (Fin.castSucc_injective k)
      have hxzi : ∀ i j, xs i ≠ zs' j := fun i j => hxz i j.castSucc
      obtain ⟨W, hW, hWe⟩ := ih zs' hzi hxzi
      let d := zs (Fin.last k)
      have hdold : ∀ j, d ≠ zs' j := by
        intro j he
        have := hz he
        have hv := congrArg Fin.val this
        simp only [Fin.val_last, Fin.val_castSucc] at hv
        omega
      have hdx : ∀ i, d ≠ xs i := fun i => (hxz i (Fin.last k)).symm
      obtain ⟨V, hV, hVe⟩ := add_gate d (referenceMap enabled xs zs')
        (referenceMap_avoids enabled xs zs' d hdx hdold) g
      refine ⟨W ++ V, by simp only [List.length_append]; omega, ?_⟩
      intro v
      have hsrc : replayInputs enabled xs (runShears W v) = replayInputs enabled xs v := by
        funext i
        simp only [replayInputs]
        congr 1
        exact (hWe v).2 (xs i) (hxzi i)
      have hscratch : (runShears W v) ∘ zs' =
          p.dirtyScratch (replayInputs enabled xs v) (v ∘ zs') := by
        funext j
        exact (hWe v).1 j
      constructor
      · intro j
        refine Fin.lastCases ?_ (fun j => ?_) j
        · rw [runShears_append, (hVe _).1, (hWe v).2 d hdold,
            Program.dirtyScratch_step_last]
          rw [read_referenceMap, hsrc, hscratch, ← Program.dirtyEval_available]
          rfl
        · rw [runShears_append, (hVe _).2 (zs j.castSucc) (hdold j).symm,
            (hWe v).1 j, Program.dirtyScratch_step_cast]
          rfl
      · intro r hr
        rw [runShears_append, (hVe _).2 r (hr (Fin.last k))]
        exact (hWe v).2 r (fun j => hr j.castSucc)

end ExactFourier

end

end Complexity
