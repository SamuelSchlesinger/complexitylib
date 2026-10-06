/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.Basis.Binary
public import Complexitylib.Algebraic.Basis.DeMorgan.Residual
public import Complexitylib.Algebraic.BooleanCube
public import Complexitylib.Algebraic.Complexity.RelativeSupport
public import Complexitylib.Algebraic.LowerBound.FanIn.Size
public import Complexitylib.Algebraic.LowerBound.MCSP.Defs
public import Complexitylib.Algebraic.Parallel
public import Complexitylib.Algebraic.Support

/-!
# Input-XOR symmetry and essential coordinates of MCSP

Flipping a subset of input variables via `xorTranslate a` (`x ↦ fun i => x i ^^ a i`)
induces a permutation `tableTranslate a` of the `2 ^ n` truth-table coordinates that acts
transitively on `Fin (2 ^ n)`.

1. **Invariance of `DeMorgan.binaryCost` complexity**: Because NOT gates have zero `binaryCost`,
   precomposing a target with `xorTranslate a` preserves `Circuit.costComplexity
   DeMorgan.interpretation DeMorgan.binaryCost` for every `a : Fin n → Bool`. Consequently,
   `mcspCostScalar DeMorgan.interpretation DeMorgan.binaryCost n s` is invariant under
   `tableTranslate a` for every `s`.
2. **Invariance of `Binary` (`B₂`) gate complexity**: Absorbing input negations into the
   16 binary gate operations of `Binary.signature` preserves `Program.size` and `Circuit.size`
   whenever the output wire is a gate, and uses at most 1 gate when the output wire is an input.
   Consequently, `mcspScalar Binary.interpretation n s` is invariant under `tableTranslate a`
   for all `s ≥ 1`.
3. **All coordinates are essential**: Any non-constant function on `Fin N → Bool` that is
   invariant under a transitive family of coordinate permutations depends essentially on every
   coordinate `i : Fin N`. In particular, whenever `mcspCostScalar` or `mcspScalar` is
   non-constant (hypothesis `hne`), every truth-table bit is essential, forcing
   `c.inputSupport = Finset.univ`. The frontier bounds `Circuit.card_inputSupport_le_size` and
   `Circuit.card_inputSupport_le_cost` then give `2 ^ n ≤ c.size + 1` for fan-in-2 circuits and
   `2 ^ n ≤ c.cost DeMorgan.binaryCost + 1` for De Morgan circuits.

The non-constancy hypothesis is discharged for the De Morgan predicate in
`Complexitylib.Algebraic.LowerBound.MCSP.NonVacuity`, which shows that
`mcspCostScalar DeMorgan.interpretation DeMorgan.binaryCost (n + 1) s` is non-constant whenever
some truth table has exact `binaryCost` complexity `s ≥ 1`, and exhibits such a table for `s = 1`.
For the `Binary` predicate `mcspScalar Binary.interpretation n s`, non-constancy remains a
hypothesis.
-/

@[expose] public section

namespace Algebraic.MCSP

open scoped BigOperators

/-! ## Input XOR translation and truth-table coordinate permutations -/

/-- Translate an `n`-bit input vector by bitwise XOR with `a : Fin n → Bool`. -/
def xorTranslate {n : Nat} (a : Fin n → Bool) : (Fin n → Bool) ≃ (Fin n → Bool) where
  toFun := fun x i => xor (x i) (a i)
  invFun := fun x i => xor (x i) (a i)
  left_inv := fun x => by
    funext i
    dsimp only
    cases x i <;> cases a i <;> rfl
  right_inv := fun x => by
    funext i
    dsimp only
    cases x i <;> cases a i <;> rfl

/-- Coordinate `i` of `xorTranslate a x` is `xor (x i) (a i)`. -/
@[simp]
theorem xorTranslate_apply {n : Nat} (a x : Fin n → Bool) (i : Fin n) :
    xorTranslate a x i = xor (x i) (a i) :=
  rfl

/-- `xorTranslate a` is an involution. -/
@[simp]
theorem xorTranslate_symm {n : Nat} (a : Fin n → Bool) :
    (xorTranslate a).symm = xorTranslate a :=
  rfl

/-- Applying `xorTranslate a` twice is the identity. -/
@[simp]
theorem xorTranslate_self {n : Nat} (a x : Fin n → Bool) :
    xorTranslate a (xorTranslate a x) = x :=
  (xorTranslate a).left_inv x

/-- Permutation of the `2 ^ n` truth-table coordinates induced by `xorTranslate a`. -/
def tableTranslate {n : Nat} (a : Fin n → Bool) : Equiv.Perm (Fin (2 ^ n)) :=
  (inputEquiv n).symm.trans ((xorTranslate a).trans (inputEquiv n))

/-- `tableTranslate a` is an involution. -/
@[simp]
theorem tableTranslate_symm {n : Nat} (a : Fin n → Bool) :
    (tableTranslate a).symm = tableTranslate a :=
  rfl

/-- `tableTranslate a` maps the index of `x` to the index of `xorTranslate a x`. -/
@[simp]
theorem tableTranslate_inputEquiv {n : Nat} (a x : Fin n → Bool) :
    tableTranslate a (inputEquiv n x) = inputEquiv n (xorTranslate a x) := by
  simp [tableTranslate]

/-- Decoding a translated index translates the decoded input. -/
@[simp]
theorem inputEquiv_symm_tableTranslate {n : Nat} (a : Fin n → Bool) (i : Fin (2 ^ n)) :
    (inputEquiv n).symm (tableTranslate a i) = xorTranslate a ((inputEquiv n).symm i) := by
  simp [tableTranslate]

/-- Applying `tableTranslate a` twice is the identity. -/
@[simp]
theorem tableTranslate_self {n : Nat} (a : Fin n → Bool) (i : Fin (2 ^ n)) :
    tableTranslate a (tableTranslate a i) = i :=
  (tableTranslate a).left_inv i

/-- Precomposing a truth table with `tableTranslate a` corresponds to precomposing the
associated target with `xorTranslate a`. -/
@[simp]
theorem truthTableTargetEquiv_comp_tableTranslate {n : Nat} (a : Fin n → Bool)
    (tt : Fin (2 ^ n) → Bool) :
    truthTableTargetEquiv n (tt ∘ tableTranslate a) =
      fun x o => truthTableTargetEquiv n tt (xorTranslate a x) o := by
  funext x o
  simp

/-- The family of permutations `tableTranslate a` acts transitively on `Fin (2 ^ n)`. -/
theorem exists_tableTranslate_eq {n : Nat} (i j : Fin (2 ^ n)) :
    ∃ a : Fin n → Bool, tableTranslate a i = j := by
  refine ⟨fun k => xor ((inputEquiv n).symm i k) ((inputEquiv n).symm j k), ?_⟩
  simp only [tableTranslate, Equiv.trans_apply]
  have hxor :
      xorTranslate (fun k => xor ((inputEquiv n).symm i k) ((inputEquiv n).symm j k))
        ((inputEquiv n).symm i) = (inputEquiv n).symm j := by
    funext k
    simp only [xorTranslate_apply]
    cases (inputEquiv n).symm i k <;> cases (inputEquiv n).symm j k <;> rfl
  rw [hxor, Equiv.apply_symm_apply]

/-! ## De Morgan `binaryCost` invariance under `xorTranslate` -/

/-- A single-output De Morgan circuit computing `x ↦ xor (x i) neg` with zero `binaryCost`. -/
def deMorganLiteralCircuit {n : Nat} (i : Fin n) (neg : Bool) :
    Circuit DeMorgan.signature n 1 :=
  if neg then
    { program := Program.empty.gate (DeMorgan.notLine (Wire.input i))
      outputs := fun _ => Wire.gate 0 }
  else
    { program := Program.empty
      outputs := fun _ => Wire.input i }

/-- `deMorganLiteralCircuit i neg` computes `x ↦ xor (x i) neg`. -/
@[simp]
theorem eval_deMorganLiteralCircuit {n : Nat} (i : Fin n) (neg : Bool)
    (x : Fin n → Bool) (o : Fin 1) :
    (deMorganLiteralCircuit i neg).eval DeMorgan.interpretation x o = xor (x i) neg := by
  cases neg with
  | false =>
      simp [deMorganLiteralCircuit, Circuit.eval, Program.trace]
  | true =>
      rfl

/-- `deMorganLiteralCircuit i neg` has zero `binaryCost`. -/
@[simp]
theorem cost_deMorganLiteralCircuit {n : Nat} (i : Fin n) (neg : Bool) :
    (deMorganLiteralCircuit i neg).cost DeMorgan.binaryCost = 0 := by
  cases neg <;> rfl

/-- An `n`-output De Morgan circuit computing `xorTranslate a` with zero `binaryCost`. -/
def deMorganXorTranslateCircuit {n : Nat} (a : Fin n → Bool) :
    Circuit DeMorgan.signature n n :=
  Circuit.parallelFin n (fun i => deMorganLiteralCircuit i (a i))

/-- `deMorganXorTranslateCircuit a` computes `xorTranslate a`. -/
@[simp]
theorem eval_deMorganXorTranslateCircuit {n : Nat} (a x : Fin n → Bool) :
    (deMorganXorTranslateCircuit a).eval DeMorgan.interpretation x = xorTranslate a x := by
  funext i
  simp [deMorganXorTranslateCircuit]

/-- `deMorganXorTranslateCircuit a` has zero `binaryCost`. -/
@[simp]
theorem cost_deMorganXorTranslateCircuit {n : Nat} (a : Fin n → Bool) :
    (deMorganXorTranslateCircuit a).cost DeMorgan.binaryCost = 0 := by
  simp [deMorganXorTranslateCircuit]

/-- Precomposing a target with `xorTranslate a` preserves `DeMorgan.binaryCost` complexity. -/
theorem costComplexity_deMorgan_xorTranslate {n m : Nat} (a : Fin n → Bool)
    (target : Target Bool n m) :
    Circuit.costComplexity DeMorgan.interpretation DeMorgan.binaryCost
        (fun x => target (xorTranslate a x)) =
      Circuit.costComplexity DeMorgan.interpretation DeMorgan.binaryCost target := by
  have hle : ∀ (b : Fin n → Bool) (t : Target Bool n m),
      Circuit.costComplexity DeMorgan.interpretation DeMorgan.binaryCost
          (fun x => t (xorTranslate b x)) ≤
        Circuit.costComplexity DeMorgan.interpretation DeMorgan.binaryCost t := by
    intro b t
    apply Circuit.le_costComplexity
    intro c hc
    have hcomp : (c.comp (deMorganXorTranslateCircuit b)).ComputesWith
        DeMorgan.interpretation (fun x => t (xorTranslate b x)) := by
      intro x
      rw [Circuit.eval_comp, eval_deMorganXorTranslateCircuit, hc (xorTranslate b x)]
    have hcost := (c.comp (deMorganXorTranslateCircuit b)).costComplexity_le
      DeMorgan.binaryCost hcomp
    simpa using hcost
  apply le_antisymm (hle a target)
  simpa using hle a (fun x => target (xorTranslate a x))

/-- `mcspCostScalar` for `DeMorgan.binaryCost` is invariant under `tableTranslate a`. -/
@[simp]
theorem mcspCostScalar_deMorgan_comp_tableTranslate {n s : Nat} (a : Fin n → Bool)
    (tt : Fin (2 ^ n) → Bool) :
    mcspCostScalar DeMorgan.interpretation DeMorgan.binaryCost n s (tt ∘ tableTranslate a) =
      mcspCostScalar DeMorgan.interpretation DeMorgan.binaryCost n s tt := by
  classical
  simp only [mcspCostScalar, truthTableTargetEquiv_comp_tableTranslate]
  rw [costComplexity_deMorgan_xorTranslate (target := truthTableTargetEquiv n tt)]

/-! ## Full binary basis (`B₂`) gate-complexity invariance under `xorTranslate` -/

/-- Mask for a wire under input XOR translation: input `i` is masked by `a i`, while internal
gate wires are unmasked. -/
def wireXorMask {n g : Nat} (a : Fin n → Bool) : Wire n g → Bool :=
  Wire.elim a (fun _ => false)

/-- The mask of input wire `i` is `a i`. -/
@[simp]
theorem wireXorMask_input {n g : Nat} (a : Fin n → Bool) (i : Fin n) :
    wireXorMask (g := g) a (Wire.input i) = a i :=
  rfl

/-- Gate wires are unmasked. -/
@[simp]
theorem wireXorMask_gate {n g : Nat} (a : Fin n → Bool) (j : Fin g) :
    wireXorMask a (Wire.gate j) = false :=
  rfl

private theorem wire_elim_xor_mask {n g : Nat} (a x : Fin n → Bool)
    (vals : Fin g → Bool) (w : Wire n g) :
    xor (Wire.elim x vals w) (wireXorMask a w) = Wire.elim (xorTranslate a x) vals w := by
  cases w with
  | input i => rfl
  | gate j => simp

/-- Absorb input XOR masks into a single `Binary.signature` gate line. -/
def negateInputsBinaryLine {n g : Nat} (a : Fin n → Bool)
    (line : Line Binary.signature n g) : Line Binary.signature n g where
  op := fun b₀ b₁ =>
    line.op (xor b₀ (wireXorMask a (line.wires 0)))
      (xor b₁ (wireXorMask a (line.wires 1)))
  wires := line.wires

/-- Absorb input XOR masks into every gate of a `Binary.signature` program without changing
its gate count. -/
def negateInputsBinaryProgram {n : Nat} (a : Fin n → Bool) :
    {g : Nat} → Program Binary.signature n g → Program Binary.signature n g
  | _, .empty => .empty
  | _, .gate p line => .gate (negateInputsBinaryProgram a p) (negateInputsBinaryLine a line)

/-- `negateInputsBinaryProgram a p` evaluates `p` on the translated input `xorTranslate a x`. -/
theorem eval_negateInputsBinaryProgram {n g : Nat} (a : Fin n → Bool)
    (p : Program Binary.signature n g) (x : Fin n → Bool) :
    (negateInputsBinaryProgram a p).eval Binary.interpretation x =
      p.eval Binary.interpretation (xorTranslate a x) := by
  induction p with
  | empty =>
      funext k
      exact Fin.elim0 k
  | @gate g p line ih =>
      funext k
      refine Fin.lastCases ?_ (fun j => ?_) k
      · simp only [negateInputsBinaryProgram, Program.eval_gate_last, ih]
        unfold negateInputsBinaryLine Line.eval Binary.interpretation
        dsimp only [Function.comp_apply]
        rw [wire_elim_xor_mask, wire_elim_xor_mask]
      · simp only [negateInputsBinaryProgram, Program.eval_gate_castSucc]
        exact congrFun ih j

/-- For `1 ≤ s`, transforming a `Binary.signature` circuit of size `≤ s` produces a circuit of
size `≤ s` computing the `xorTranslate a`-shifted target. -/
theorem exists_binary_circuit_xorTranslate {n s : Nat} (hs : 1 ≤ s) (a : Fin n → Bool)
    {target : Target Bool n 1} {c : Circuit Binary.signature n 1}
    (hsize : c.size ≤ s) (hcomp : c.ComputesWith Binary.interpretation target) :
    ∃ c' : Circuit Binary.signature n 1,
      c'.size ≤ s ∧
        c'.ComputesWith Binary.interpretation (fun x => target (xorTranslate a x)) := by
  cases hout : c.outputs 0 with
  | gate j =>
      refine ⟨{ program := negateInputsBinaryProgram a c.program, outputs := c.outputs },
        hsize, ?_⟩
      intro x
      funext o
      rw [Subsingleton.elim o 0]
      have hcx := congrFun (hcomp (xorTranslate a x)) 0
      simpa [Circuit.eval, Program.trace, hout, eval_negateInputsBinaryProgram] using hcx
  | input i =>
      let line : Line Binary.signature n 0 :=
        { op := fun b _ => xor b (a i)
          wires := fun _ => Wire.input i }
      refine ⟨{ program := Program.empty.gate line, outputs := fun _ => Wire.gate 0 }, hs, ?_⟩
      intro x
      funext o
      rw [Subsingleton.elim o 0]
      have hcx := congrFun (hcomp (xorTranslate a x)) 0
      have htarget : target (xorTranslate a x) 0 = xor (x i) (a i) := by
        simpa [Circuit.eval, Program.trace, hout] using hcx.symm
      dsimp only
      rw [htarget]
      rfl

/-- For `1 ≤ s`, `mcspScalar Binary.interpretation n s` is invariant under `tableTranslate a`. -/
theorem mcspScalar_binary_comp_tableTranslate {n s : Nat} (hs : 1 ≤ s) (a : Fin n → Bool)
    (tt : Fin (2 ^ n) → Bool) :
    mcspScalar Binary.interpretation n s (tt ∘ tableTranslate a) =
      mcspScalar Binary.interpretation n s tt := by
  classical
  apply Bool.eq_iff_iff.mpr
  simp only [mcspScalar_eq_true_iff, truthTableTargetEquiv_comp_tableTranslate,
    gateComplexity_le_nat_iff]
  constructor
  · rintro ⟨c, hsize, hcomp⟩
    obtain ⟨c', hsize', hcomp'⟩ := exists_binary_circuit_xorTranslate hs a hsize hcomp
    have htarget_eq :
        (fun x => (fun x' o => truthTableTargetEquiv n tt (xorTranslate a x') o)
          (xorTranslate a x)) = truthTableTargetEquiv n tt := by
      funext x o
      simp
    rw [htarget_eq] at hcomp'
    exact ⟨c', hsize', hcomp'⟩
  · rintro ⟨c, hsize, hcomp⟩
    exact exists_binary_circuit_xorTranslate hs a hsize hcomp

/-! ## Essential coordinates of transitive non-constant Boolean functions -/

/-- Any non-constant function on the Boolean cube has at least one essential coordinate. -/
theorem exists_essentialAt_of_ne {N : Nat} {V : Type*} {F : (Fin N → Bool) → V}
    {x y : Fin N → Bool} (hne : F x ≠ F y) :
    ∃ i : Fin N, EssentialAt F i := by
  have hreach : F y = F x ∨ ∃ i : Fin N, EssentialAt F i := by
    apply BooleanCube.update_induction x y (fun z => F z = F x ∨ ∃ i : Fin N, EssentialAt F i)
    · exact Or.inl rfl
    · intro z i v hz
      rcases hz with hzx | hex
      · by_cases hupd : F (Function.update z i v) = F x
        · exact Or.inl hupd
        · refine Or.inr ⟨i, z, Function.update z i v, ?_, ?_⟩
          · intro k hk
            exact (Function.update_of_ne hk v z).symm
          · rw [hzx]
            exact Ne.symm hupd
      · exact Or.inr hex
  exact hreach.resolve_left (Ne.symm hne)

/-- If `F` is invariant under precomposition with `π : Equiv.Perm (Fin N)`, then `EssentialAt F i`
implies `EssentialAt F (π i)`. -/
theorem EssentialAt.perm {N : Nat} {V : Type*} {F : (Fin N → Bool) → V}
    {π : Equiv.Perm (Fin N)} (hinv : ∀ x, F (x ∘ π) = F x)
    {i : Fin N} (hess : EssentialAt F i) :
    EssentialAt F (π i) := by
  obtain ⟨left, right, hagree, hne⟩ := hess
  refine ⟨left ∘ π.symm, right ∘ π.symm, ?_, ?_⟩
  · intro k hk
    have hk' : π.symm k ≠ i := by
      intro heq
      apply hk
      rw [← heq, Equiv.apply_symm_apply]
    exact hagree (π.symm k) hk'
  · have hleft : (left ∘ π.symm) ∘ π = left := by
      funext k
      simp
    have hright : (right ∘ π.symm) ∘ π = right := by
      funext k
      simp
    rw [← hinv (left ∘ π.symm), ← hinv (right ∘ π.symm), hleft, hright]
    exact hne

/-- Any non-constant function on `Fin (2 ^ n) → Bool` that is invariant under `tableTranslate a`
for all `a : Fin n → Bool` has every coordinate `i : Fin (2 ^ n)` essential. -/
theorem essentialAt_all_of_tableTranslate_invariant {n : Nat} {V : Type*}
    {F : (Fin (2 ^ n) → Bool) → V}
    (hinv : ∀ (a : Fin n → Bool) (tt : Fin (2 ^ n) → Bool), F (tt ∘ tableTranslate a) = F tt)
    {tt₀ tt₁ : Fin (2 ^ n) → Bool} (hne : F tt₀ ≠ F tt₁) (i : Fin (2 ^ n)) :
    EssentialAt F i := by
  obtain ⟨i₀, hess₀⟩ := exists_essentialAt_of_ne hne
  obtain ⟨a, ha⟩ := exists_tableTranslate_eq i₀ i
  rw [← ha]
  exact EssentialAt.perm (hinv a) hess₀

/-- If every coordinate is essential for a scalar function `F`, then every circuit (in any basis)
computing a single-output target `T` with `T x 0 = F x` reads every input. -/
theorem inputSupport_eq_univ_of_forall_essentialAt {σ : Signature}
    {interpretation : Interpretation σ Bool} {N : Nat} {F : (Fin N → Bool) → Bool}
    {T : Target Bool N 1} (hT : ∀ x, T x 0 = F x)
    (hess : ∀ i, EssentialAt F i) {c : Circuit σ N 1}
    (hcomp : c.ComputesWith interpretation T) :
    c.inputSupport = Finset.univ := by
  ext i
  simp only [Finset.mem_univ, iff_true]
  obtain ⟨left, right, hagree, hdiff⟩ := hess i
  have hess_target : EssentialAt T i :=
    ⟨left, right, hagree, fun heq => hdiff (by rw [← hT, ← hT, heq])⟩
  exact hess_target.mem_support hcomp.dependsOnlyOn

/-! ## Input-support bounds for De Morgan circuits -/

/-- Every De Morgan operation has arity at most its `binaryCost` plus one, so the weighted
frontier bound `Circuit.card_inputSupport_le_cost` applies to `DeMorgan.binaryCost`. -/
theorem deMorgan_arity_le_binaryCost_add_one (op : DeMorgan.signature.Op) :
    DeMorgan.signature.Arity op ≤ DeMorgan.binaryCost op + 1 := by
  cases op <;> decide

/-- A De Morgan circuit with `m` outputs reads at most `m + c.cost DeMorgan.binaryCost` inputs. -/
theorem card_inputSupport_le_binaryCost {N m : Nat} (c : Circuit DeMorgan.signature N m) :
    c.inputSupport.card ≤ m + c.cost DeMorgan.binaryCost :=
  c.card_inputSupport_le_cost DeMorgan.binaryCost deMorgan_arity_le_binaryCost_add_one

/-! ## Essential coordinates and `2 ^ n - 1` circuit size / cost bounds for non-constant MCSP -/

/-- Whenever `mcspCostScalar DeMorgan.interpretation DeMorgan.binaryCost n s` is non-constant,
every truth-table coordinate `i : Fin (2 ^ n)` is essential. -/
theorem mcspCostScalar_deMorgan_essentialAt {n s : Nat}
    {tt₀ tt₁ : Fin (2 ^ n) → Bool}
    (hne : mcspCostScalar DeMorgan.interpretation DeMorgan.binaryCost n s tt₀ ≠
      mcspCostScalar DeMorgan.interpretation DeMorgan.binaryCost n s tt₁)
    (i : Fin (2 ^ n)) :
    EssentialAt (mcspCostScalar DeMorgan.interpretation DeMorgan.binaryCost n s) i :=
  essentialAt_all_of_tableTranslate_invariant
    (fun a tt => mcspCostScalar_deMorgan_comp_tableTranslate a tt) hne i

/-- Any circuit (in any basis) computing non-constant
`mcspCostTarget DeMorgan.interpretation DeMorgan.binaryCost n s` must include every truth-table
coordinate in its `inputSupport`. -/
theorem mcspCostTarget_deMorgan_inputSupport_eq_univ {σ : Signature}
    {interpretation : Interpretation σ Bool} {n s : Nat}
    {tt₀ tt₁ : Fin (2 ^ n) → Bool}
    (hne : mcspCostScalar DeMorgan.interpretation DeMorgan.binaryCost n s tt₀ ≠
      mcspCostScalar DeMorgan.interpretation DeMorgan.binaryCost n s tt₁)
    {c : Circuit σ (2 ^ n) 1}
    (hcomp : c.ComputesWith interpretation
      (mcspCostTarget DeMorgan.interpretation DeMorgan.binaryCost n s)) :
    c.inputSupport = Finset.univ :=
  inputSupport_eq_univ_of_forall_essentialAt (fun _ => rfl)
    (mcspCostScalar_deMorgan_essentialAt hne) hcomp

/-- `2 ^ n ≤ c.cost DeMorgan.binaryCost + 1` for any De Morgan circuit computing
`mcspCostTarget DeMorgan.interpretation DeMorgan.binaryCost n s`, provided this predicate is
non-constant (`hne`). -/
theorem mcspCostTarget_deMorgan_binaryCost_lower_bound {n s : Nat}
    {tt₀ tt₁ : Fin (2 ^ n) → Bool}
    (hne : mcspCostScalar DeMorgan.interpretation DeMorgan.binaryCost n s tt₀ ≠
      mcspCostScalar DeMorgan.interpretation DeMorgan.binaryCost n s tt₁)
    (c : Circuit DeMorgan.signature (2 ^ n) 1)
    (hcomp : c.ComputesWith DeMorgan.interpretation
      (mcspCostTarget DeMorgan.interpretation DeMorgan.binaryCost n s)) :
    2 ^ n ≤ c.cost DeMorgan.binaryCost + 1 := by
  have hcard : c.inputSupport.card = 2 ^ n := by
    rw [mcspCostTarget_deMorgan_inputSupport_eq_univ hne hcomp, Finset.card_univ,
      Fintype.card_fin]
  have hbound := card_inputSupport_le_binaryCost c
  omega

/-- `2 ^ n ≤ c.size + 1` for any fan-in-2 circuit (in any basis) computing
`mcspCostTarget DeMorgan.interpretation DeMorgan.binaryCost n s`, provided this predicate is
non-constant (`hne`). -/
theorem mcspCostTarget_deMorgan_size_lower_bound {σ : Signature}
    {interpretation : Interpretation σ Bool} {n s : Nat}
    {tt₀ tt₁ : Fin (2 ^ n) → Bool}
    (hne : mcspCostScalar DeMorgan.interpretation DeMorgan.binaryCost n s tt₀ ≠
      mcspCostScalar DeMorgan.interpretation DeMorgan.binaryCost n s tt₁)
    (c : Circuit σ (2 ^ n) 1) (hfan : c.FanInAtMost 2)
    (hcomp : c.ComputesWith interpretation
      (mcspCostTarget DeMorgan.interpretation DeMorgan.binaryCost n s)) :
    2 ^ n ≤ c.size + 1 := by
  have hcard : c.inputSupport.card = 2 ^ n := by
    rw [mcspCostTarget_deMorgan_inputSupport_eq_univ hne hcomp, Finset.card_univ,
      Fintype.card_fin]
  have hbound : c.inputSupport.card ≤ 1 + (2 - 1) * c.size := c.card_inputSupport_le_size hfan
  omega

/-- Whenever `1 ≤ s` and `mcspScalar Binary.interpretation n s` is non-constant,
every truth-table coordinate `i : Fin (2 ^ n)` is essential. -/
theorem mcspScalar_binary_essentialAt {n s : Nat} (hs : 1 ≤ s)
    {tt₀ tt₁ : Fin (2 ^ n) → Bool}
    (hne : mcspScalar Binary.interpretation n s tt₀ ≠
      mcspScalar Binary.interpretation n s tt₁)
    (i : Fin (2 ^ n)) :
    EssentialAt (mcspScalar Binary.interpretation n s) i :=
  essentialAt_all_of_tableTranslate_invariant
    (fun a tt => mcspScalar_binary_comp_tableTranslate hs a tt) hne i

/-- Any circuit (in any basis) computing `mcspTarget Binary.interpretation n s` (`1 ≤ s`),
provided this predicate is non-constant, must include every truth-table coordinate in its
`inputSupport`. -/
theorem mcspTarget_binary_inputSupport_eq_univ {σ : Signature}
    {interpretation : Interpretation σ Bool} {n s : Nat} (hs : 1 ≤ s)
    {tt₀ tt₁ : Fin (2 ^ n) → Bool}
    (hne : mcspScalar Binary.interpretation n s tt₀ ≠
      mcspScalar Binary.interpretation n s tt₁)
    {c : Circuit σ (2 ^ n) 1}
    (hcomp : c.ComputesWith interpretation (mcspTarget Binary.interpretation n s)) :
    c.inputSupport = Finset.univ :=
  inputSupport_eq_univ_of_forall_essentialAt (fun _ => rfl)
    (mcspScalar_binary_essentialAt hs hne) hcomp

/-- `2 ^ n ≤ c.size + 1` for any fan-in-2 circuit (in any basis) computing
`mcspTarget Binary.interpretation n s` (`1 ≤ s`), provided this predicate is non-constant
(`hne`). -/
theorem mcspTarget_binary_size_lower_bound {σ : Signature}
    {interpretation : Interpretation σ Bool} {n s : Nat} (hs : 1 ≤ s)
    {tt₀ tt₁ : Fin (2 ^ n) → Bool}
    (hne : mcspScalar Binary.interpretation n s tt₀ ≠
      mcspScalar Binary.interpretation n s tt₁)
    (c : Circuit σ (2 ^ n) 1) (hfan : c.FanInAtMost 2)
    (hcomp : c.ComputesWith interpretation (mcspTarget Binary.interpretation n s)) :
    2 ^ n ≤ c.size + 1 := by
  have hcard : c.inputSupport.card = 2 ^ n := by
    rw [mcspTarget_binary_inputSupport_eq_univ hs hne hcomp, Finset.card_univ,
      Fintype.card_fin]
  have hbound : c.inputSupport.card ≤ 1 + (2 - 1) * c.size := c.card_inputSupport_le_size hfan
  omega

end Algebraic.MCSP
