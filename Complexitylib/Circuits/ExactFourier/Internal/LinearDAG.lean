/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module
public import Complexitylib.Circuits.ExactFourier.Internal.PortMatrices

/-!
# Exact Fourier circuits: linear dag

Adapted from OpenAI's formalization at revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
Source: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/FourierCircuit/LinearDAG.lean

Imports, namespaces, module visibility, documentation, and formatting are adapted
for complexitylib. The source theorem statements and mathematical arguments are retained.
-/

@[expose] public section

namespace Complexity

section
namespace ExactFourier

/-- Relabel every input wire of a scalar gate. -/
def Gate.map {w w' : ℕ} (f : Fin w → Fin w') : Gate w → Gate w'
  | .add i j => .add (f i) (f j)
  | .sub i j => .sub (f i) (f j)
  | .scale c i => .scale c (f i)

theorem Gate.eval_map {w w' : ℕ} (f : Fin w → Fin w') (g : Gate w)
    (v : Fin w' → ℂ) : (g.map f).eval v = g.eval (v ∘ f) := by cases g <;> rfl

/-- Relocate a wire when appending a program to an existing computation. -/
def appendIndex {n m k l : ℕ} (f : Fin (m + 1) → Fin (n + 1 + k))
    (i : Fin (m + 1 + l)) : Fin (n + 1 + (k + l)) :=
  if h : i.val < m + 1 then ⟨(f ⟨i.val, h⟩).val, by have := (f ⟨i.val, h⟩).isLt; omega⟩
  else ⟨n + 1 + k + (i.val - (m + 1)), by have := i.isLt; omega⟩

/-- Retain an existing wire index after appending more gates. -/
def keepIndex {n k l : ℕ} (i : Fin (n + 1 + k)) : Fin (n + 1 + (k + l)) :=
  ⟨i.val, by have := i.isLt; omega⟩

@[simp] theorem appendIndex_last {n m k l : ℕ} (f : Fin (m + 1) → Fin (n + 1 + k)) :
    appendIndex (l := l + 1) f (Fin.last (m + 1 + l)) = Fin.last (n + 1 + (k + l)) := by
  unfold appendIndex
  split_ifs with h
  · have : m + 1 + l < m + 1 := h
    omega
  · apply Fin.ext
    simp only [Fin.val_last]
    omega

@[simp] theorem appendIndex_castSucc {n m k l : ℕ}
    (f : Fin (m + 1) → Fin (n + 1 + k)) (i : Fin (m + 1 + l)) :
    appendIndex (l := l + 1) f i.castSucc = (appendIndex f i).castSucc := by
  unfold appendIndex
  split_ifs <;> first | rfl | (exfalso; simp only [Fin.val_castSucc] at *; contradiction)

@[simp] theorem keepIndex_succ {n k l : ℕ} (i : Fin (n + 1 + k)) :
    keepIndex (l := l + 1) i = (keepIndex (l := l) i).castSucc := rfl

@[simp] theorem keepIndex_zero {n k : ℕ} (i : Fin (n + 1 + k)) :
    keepIndex (l := 0) i = i := rfl

@[simp] theorem appendIndex_zero {n m k : ℕ} (f : Fin (m + 1) → Fin (n + 1 + k))
    (i : Fin (m + 1)) : appendIndex (l := 0) f i = f i := by
  apply Fin.ext
  simp [appendIndex, i.isLt]

/-- Append a scalar program using the supplied references for its inputs and zero wire. -/
def Program.append {n m k : ℕ} (p : Program n k)
    (f : Fin (m + 1) → Fin (n + 1 + k)) : {l : ℕ} → Program m l → Program n (k + l)
  | 0, .nil => p
  | _ + 1, .step q g => .step (p.append f q) (g.map (appendIndex f))

/-- Literal semantics of DAG composition, including preservation of every existing value. -/
theorem Program.eval_append {n m k l : ℕ} (p : Program n k) (q : Program m l)
    (f : Fin (m + 1) → Fin (n + 1 + k)) (x : Fin n → ℂ) (y : Fin m → ℂ)
    (hf : ∀ (i : Fin (m + 1)), p.eval x (f i) = (Fin.snoc y 0 : Fin (m + 1) → ℂ) i) :
    (∀ j, (p.append f q).eval x (keepIndex j) = p.eval x j) ∧
    (∀ i, (p.append f q).eval x (appendIndex f i) = q.eval y i) := by
  induction q with
  | nil =>
      constructor
      · intro j; rfl
      · intro i; simpa [Program.append, Program.eval] using hf i
  | @step l q g ih =>
      constructor
      · intro j
        simp only [Program.append, Program.eval, keepIndex_succ, Fin.snoc_castSucc]
        exact ih.1 j
      · intro i
        refine Fin.lastCases ?_ (fun j => ?_) i
        · calc
            _ = (p.append f (q.step g)).eval x (Fin.last (n + 1 + (k + l))) :=
              congrArg ((p.append f (q.step g)).eval x) (appendIndex_last f)
            _ = _ := by
              simp only [Program.append, Program.eval, Nat.add_eq, Fin.snoc_last, Gate.eval_map]
              congr 1
              funext j
              exact ih.2 j
        · simp only [appendIndex_castSucc, Program.append, Program.eval, Fin.snoc_castSucc]
          exact ih.2 j

/-- Exact composition: all previous values can be reused without being consumed. -/
noncomputable def LinearDAG.comp {n a b : ℕ} (D : LinearDAG a b) (C : LinearDAG n a) :
    LinearDAG n b where
  size := C.size + D.size
  program := C.program.append (Fin.snoc C.outputs ⟨n, by omega⟩) D.program
  outputs := appendIndex (Fin.snoc C.outputs ⟨n, by omega⟩) ∘ D.outputs

theorem Program.eval_zero {n k : ℕ} (p : Program n k) (x : Fin n → ℂ) :
    p.eval x ⟨n, by omega⟩ = 0 := by
  induction p with
  | nil => exact Fin.snoc_last _ _
  | @step k p g ih =>
      change (Fin.snoc (p.eval x) (g.eval (p.eval x)) : Fin (n + 1 + k + 1) → ℂ)
        (Fin.castSucc (⟨n, by omega⟩ : Fin (n + 1 + k))) = 0
      rw [Fin.snoc_castSucc, ih]

theorem Program.eval_input {n k : ℕ} (p : Program n k) (x : Fin n → ℂ) (j : Fin n) :
    p.eval x ⟨j.val, by have := j.isLt; omega⟩ = x j := by
  induction p with
  | nil => exact Fin.snoc_castSucc _ _ j
  | @step k p g ih =>
      change (Fin.snoc (p.eval x) (g.eval (p.eval x)) : Fin (n + 1 + k + 1) → ℂ)
        (Fin.castSucc (⟨j.val, by have := j.isLt; omega⟩ : Fin (n + 1 + k))) = x j
      rw [Fin.snoc_castSucc, ih]

theorem LinearDAG.eval_comp {n a b : ℕ} (D : LinearDAG a b) (C : LinearDAG n a)
    (x : Fin n → ℂ) : (D.comp C).eval x = D.eval (C.eval x) := by
  have hf : ∀ (i : Fin (a + 1)), C.program.eval x
      ((Fin.snoc C.outputs (⟨n, by omega⟩ : Fin (n + 1 + C.size)) :
        Fin (a + 1) → Fin (n + 1 + C.size)) i) =
      (Fin.snoc (C.eval x) 0 : Fin (a + 1) → ℂ) i := by
    intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simpa using C.program.eval_zero x
    · simp [LinearDAG.eval]
  have he := C.program.eval_append D.program (Fin.snoc C.outputs ⟨n, by omega⟩) x (C.eval x) hf
  funext i
  exact he.2 (D.outputs i)

end ExactFourier

namespace ExactFourier

/-- Index of a newly emitted vector gate. -/
def gateIndex {n k a : ℕ} (i : Fin a) : Fin (n + 1 + (k + a)) :=
  ⟨n + 1 + k + i.val, by have := i.isLt; omega⟩

@[simp] theorem gateIndex_last {n k a : ℕ} :
    gateIndex (n := n) (k := k) (Fin.last a) = Fin.last (n + 1 + (k + a)) := by
  apply Fin.ext
  simp [gateIndex, Nat.add_assoc]

@[simp] theorem gateIndex_castSucc {n k a : ℕ} (i : Fin a) :
    gateIndex (n := n) (k := k) i.castSucc = (gateIndex (n := n) (k := k) i).castSucc := rfl

/-- Emit independent scalar operations, one cost unit per coordinate, with original
operands still available after the whole layer. -/
def Program.emit {n k : ℕ} (p : Program n k) :
    {a : ℕ} → (Fin a → Gate (n + 1 + k)) → Program n (k + a)
  | 0, _ => p
  | a + 1, g => .step (p.emit (g ∘ Fin.castSucc)) ((g (Fin.last a)).map keepIndex)

theorem Program.eval_emit {n k a : ℕ} (p : Program n k)
    (g : Fin a → Gate (n + 1 + k)) (x : Fin n → ℂ) :
    (∀ j, (p.emit g).eval x (keepIndex j) = p.eval x j) ∧
    (∀ i, (p.emit g).eval x (gateIndex i) = (g i).eval (p.eval x)) := by
  induction a with
  | zero =>
      constructor
      · intro j; rfl
      · intro i; exact Fin.elim0 i
  | succ a ih =>
      have ih := ih (g ∘ Fin.castSucc)
      constructor
      · intro j
        simp only [Program.emit, Program.eval, keepIndex_succ, Fin.snoc_castSucc]
        exact ih.1 j
      · intro i
        refine Fin.lastCases ?_ (fun j => ?_) i
        · calc
            _ = (p.emit g).eval x (Fin.last (n + 1 + (k + a))) :=
              congrArg ((p.emit g).eval x) gateIndex_last
            _ = _ := by
              simp only [Program.emit, Program.eval, Nat.add_eq, Fin.snoc_last, Gate.eval_map]
              congr 1
              funext j
              exact ih.1 j
        · simp only [gateIndex_castSucc, Program.emit, Program.eval, Fin.snoc_castSucc]
          exact ih.2 j

/-- Read-only input relabeling and arbitrary fanout are genuinely free. -/
def LinearDAG.wires {n a : ℕ} (f : Fin a → Fin (n + 1)) : LinearDAG n a where
  size := 0
  program := .nil
  outputs := f

@[simp] theorem LinearDAG.eval_wires {n a : ℕ} (f : Fin a → Fin (n + 1))
    (x : Fin n → ℂ) : (LinearDAG.wires f).eval x = fun i => (Fin.snoc x 0 : Fin (n + 1) → ℂ) (f
      i) := rfl

/-- A rectangular vector layer still charges every scalar gate separately. -/
def LinearDAG.layer {n a : ℕ} (g : Fin a → Gate (n + 1)) : LinearDAG n a where
  size := 0 + a
  program := Program.nil.emit g
  outputs := gateIndex

@[simp] theorem LinearDAG.size_layer {n a : ℕ} (g : Fin a → Gate (n + 1)) :
    (LinearDAG.layer g).size = a := Nat.zero_add _

theorem LinearDAG.eval_layer {n a : ℕ} (g : Fin a → Gate (n + 1))
    (x : Fin n → ℂ) : (LinearDAG.layer g).eval x = fun i => (g i).eval (Fin.snoc x 0) := by
  funext i
  exact (Program.nil.eval_emit g x).2 i

/-- Append a scaled original input into each existing output accumulator.
The two scalar operations per row are charged even for a zero scalar. -/
def LinearDAG.addColumn {n a : ℕ} (C : LinearDAG n a) (j : Fin n) (c : Fin a → ℂ) :
    LinearDAG n a where
  size := (C.size + a) + a
  program :=
    let p := C.program.emit (fun i => Gate.scale (c i) ⟨j.val, by have := j.isLt; omega⟩)
    p.emit (fun i => Gate.add (keepIndex (C.outputs i)) (gateIndex i))
  outputs := gateIndex

theorem LinearDAG.eval_addColumn {n a : ℕ} (C : LinearDAG n a) (j : Fin n)
    (c : Fin a → ℂ) (x : Fin n → ℂ) :
    (C.addColumn j c).eval x = fun i => C.eval x i + c i * x j := by
  let gs : Fin a → Gate (n + 1 + C.size) := fun i =>
    Gate.scale (c i) ⟨j.val, by have := j.isLt; omega⟩
  have hs := C.program.eval_emit gs x
  have ha := (C.program.emit gs).eval_emit
    (fun i : Fin a => Gate.add (keepIndex (C.outputs i)) (gateIndex i)) x
  funext i
  change (C.program.emit gs |>.emit _).eval x (gateIndex i) = _
  rw [ha.2, Gate.eval, hs.1, hs.2]
  change C.eval x i + c i * C.program.eval x ⟨j.val, by have := j.isLt; omega⟩ = _
  congr 2
  exact C.program.eval_input x j

/-- Direct multiplication: this construction will be used only for the fixed spatial
matrices in the coefficient-boundary comparison, not as a purported FFT saving. -/
def LinearDAG.matrix (n a : ℕ) (G : Matrix (Fin a) (Fin n) ℂ) : LinearDAG n a :=
  (List.finRange n).foldl (fun C j => C.addColumn j (fun i => G i j))
    (LinearDAG.wires (fun _ => Fin.last n))

end ExactFourier

namespace ExactFourier

private theorem foldColumns_size {n a : ℕ} (G : Matrix (Fin a) (Fin n) ℂ)
    (L : List (Fin n)) (C : LinearDAG n a) :
    (L.foldl (fun C j => C.addColumn j (fun i => G i j)) C).size =
      C.size + 2 * a * L.length := by
  induction L generalizing C with
  | nil => simp
  | cons j L ih =>
      rw [List.foldl_cons, ih]
      simp only [LinearDAG.addColumn, List.length_cons]
      ring

private theorem foldColumns_eval {n a : ℕ} (G : Matrix (Fin a) (Fin n) ℂ)
    (L : List (Fin n)) (C : LinearDAG n a) (x : Fin n → ℂ) (i : Fin a) :
    (L.foldl (fun C j => C.addColumn j (fun r => G r j)) C).eval x i =
      C.eval x i + (L.map (fun j => G i j * x j)).sum := by
  induction L generalizing C with
  | nil => simp
  | cons j L ih =>
      simp only [List.foldl_cons, ih, LinearDAG.eval_addColumn, List.map_cons, List.sum_cons]
      ring

@[simp] theorem LinearDAG.size_matrix {n a : ℕ} (G : Matrix (Fin a) (Fin n) ℂ) :
    (LinearDAG.matrix n a G).size = 2 * a * n := by
  simp [LinearDAG.matrix, foldColumns_size, LinearDAG.wires]

theorem LinearDAG.eval_matrix {n a : ℕ} (G : Matrix (Fin a) (Fin n) ℂ)
    (x : Fin n → ℂ) : (LinearDAG.matrix n a G).eval x = G.mulVec x := by
  funext i
  simp [LinearDAG.matrix, foldColumns_eval, LinearDAG.eval_wires, Matrix.mulVec,
    dotProduct, ← List.ofFn_id, List.map_ofFn, List.sum_ofFn]

end ExactFourier

namespace ExactFourier

/-- Quantitative version of the two-way pre-corner argument, with no hidden inverse
oracle: `D` is an actual charged DAG computing the inverse map. -/
theorem MatrixPrice.twoWay_DAG_bound (p : MatrixPrice) {n : ℕ}
    (G : Matrix (Fin n) (Fin n) ℂ) (hG : IsUnit G) (C D : LinearDAG n n)
    (hC : ∀ x, C.eval x = G.mulVec x) (hD : ∀ x, D.eval x = G⁻¹.mulVec x) :
    p.value G ≤ 8 * C.size + 4 * D.size + 3 * n := by
  have h := p.twoWay_bound G hG
  have h1 := p.rectangularShear_bound C G hC
  have h2 := p.rectangularShear_bound D G⁻¹ hD
  linarith

/-- Uniform finite upper bound needed in the compactness branch. It does not assert
that any price exists; it is a consequence of the standing price laws. -/
theorem MatrixPrice.quadratic_bound (p : MatrixPrice) {n : ℕ}
    (G : Matrix (Fin n) (Fin n) ℂ) (hG : IsUnit G) :
    p.value G ≤ 24 * (n : ℝ) ^ 2 + 3 * n := by
  have h := p.twoWay_DAG_bound G hG (LinearDAG.matrix n n G)
    (LinearDAG.matrix n n G⁻¹) (LinearDAG.eval_matrix G) (LinearDAG.eval_matrix G⁻¹)
  simp only [LinearDAG.size_matrix, Nat.cast_mul, Nat.cast_ofNat] at h
  nlinarith

end ExactFourier

end

end Complexity
