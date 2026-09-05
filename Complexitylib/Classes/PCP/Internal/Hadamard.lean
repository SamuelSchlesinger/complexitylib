/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/
module
public import Complexitylib.BooleanAnalysis.FourierExpansion
public import Complexitylib.Classes.PCP.Internal.CubeBlocks

/-!
# Decoding a Hadamard proof

Dinur's alphabet-reduction step composes a constraint system with an inner
verifier — an *assignment tester* — and the classical one is built from the
Hadamard code: an assignment `a ⊆ Fin n` is encoded as the parity function
`χ a`, and the verifier checks that the proof is (close to) such a function.

The two facts the analysis rests on are already in
`Complexitylib.BooleanAnalysis.FourierExpansion`: `blr_soundness`, which says a
proof passing the linearity test is close to *some* linear function, and
`local_correctability`, which recovers that function's value anywhere. What is
missing for a tester is the *witness*: soundness must hand back the coordinate
set `S`, since `S` is precisely the assignment being decoded.

This module extracts that witness, and records the two identities that make
`χ S` a usable decoding: its value on a basis vector is the membership bit of
`S`, so reading the corrected proof at basis vectors recovers the assignment.

## Main results

- `Complexity.exists_close_parity_of_blr` — soundness with the coordinate set
  named
- `Complexity.parityFun_basis` — the decoded assignment is read off at basis
  vectors
- `Complexity.hadamard`, `Complexity.signOf_hadamard` — the Hadamard code is a
  parity function, so the Fourier results apply to it
- `Complexity.tensor`, `Complexity.hadamard_tensor` — the consistency identity
  tying the quadratic table to the linear one
- `Complexity.parity_eq_signOf_hadamard`, `Complexity.exists_assignment_of_blr` —
  a proof passing the linearity test decodes to an assignment
- `Complexity.eq_tensorAssign_of_consistent` — the consistency check leaves the
  prover no freedom in the quadratic table
- `Complexity.QuadConstraint`, `Complexity.sat_of_checks` — the constraint check,
  and tester soundness in exact form
- `Complexity.checks_of_sat` — and its completeness
- `Complexity.hammingDist_comm`, `Complexity.hammingDist_triangle` — basic
  metric facts, absent from the Fourier layer
- `Complexity.eq_of_hammingDist_lt_half`, `Complexity.hadamard_inj_of_close` —
  the decoding is rigid, so a check passing often holds exactly
- `Complexity.prob_hadamard_ne_zero` — a nonzero linear form is balanced
- `Complexity.tensorRow`, `Complexity.hadamard_tensor_row` — the bilinear form,
  read as a linear form in one argument
- `Complexity.prob_mono`, `Complexity.prob_tensorRow_ne_zero` — a nonzero
  bilinear form has nonzero rows for at least half the second arguments
- `Complexity.prob₂_tensor_ne_zero` — hence it is nonzero on a quarter of all
  pairs
- `Complexity.eq_tensorAssign_of_prob_consistent` — so passing the consistency
  check often forces the quadratic table exactly
- `Complexity.prob_corrected_read_left`, `Complexity.prob_two_corrected_reads` —
  self-corrected reads over bundled randomness
- `Complexity.sat_of_prob_checks` — soundness when consistency is only tested
  on a random pair
- `Complexity.prob_consistency_of_honest` — and the matching completeness
- `Complexity.prob_all_reads` — every read of a tester is correct, for any
  bundling of its randomness
-/

@[expose] public section

namespace Complexity

open BooleanAnalysis

variable {n : ℕ}

/-- **BLR soundness, with the witness named.** A proof passing the linearity
test is close to `χ S` for an explicit coordinate set `S` — and `S` is the
assignment the tester decodes. -/
theorem exists_close_parity_of_blr (f : BooleanFunction n) (hf : IsBooleanValued f)
    (ε : ℝ) (h : blrAcceptProb f ≥ 1 - ε) :
    ∃ S : Finset (Fin n), hammingDist f (χ S) ≤ ε := by
  obtain ⟨g, ⟨S, hg⟩, hclose⟩ := blr_soundness f hf ε h
  refine ⟨S, ?_⟩
  have hgS : g = χ S := funext hg
  rw [← hgS]
  exact hclose

/-- The basis vector at coordinate `i`. -/
def basisVec (i : Fin n) : Cube n := fun j => if j = i then 1 else 0

/-- **Reading the assignment.** The decoded parity function, evaluated at the
`i`-th basis vector, is `-1` exactly when `i` belongs to the coordinate set: the
assignment is read off the proof one coordinate at a time. -/
theorem parityFun_basis (S : Finset (Fin n)) (i : Fin n) :
    (χ S) (basisVec i) = if i ∈ S then -1 else 1 := by
  classical
  rw [parityFun]
  by_cases hi : i ∈ S
  · rw [ite_eq_left hi]
    rw [Finset.prod_eq_single i]
    · show chi (if i = i then (1 : ZMod 2) else 0) = -1
      rw [ite_eq_left rfl]
      show chi 1 = -1
      simp
    · intro j _ hj
      show chi (if j = i then (1 : ZMod 2) else 0) = 1
      rw [ite_eq_right hj]
      show chi 0 = 1
      simp
    · intro hni
      exact absurd hi hni
  · rw [ite_eq_right hi]
    refine Finset.prod_eq_one fun j hj => ?_
    have hji : j ≠ i := fun h => hi (h ▸ hj)
    show chi (if j = i then (1 : ZMod 2) else 0) = 1
    rw [ite_eq_right hji]
    show chi 0 = 1
    simp

/-! ### The Hadamard code -/

/-- An `𝔽₂`-valued function on the cube. The tester's checks are stated over
`𝔽₂` — the consistency check multiplies two bits, which is not a `±1`
operation — while the linearity analysis lives in the `±1` world, so the two
views must be bridged. -/
abbrev BitFun (n : ℕ) : Type := Cube n → ZMod 2

/-- The `±1` encoding of an `𝔽₂`-valued function. -/
noncomputable def signOf (F : BitFun n) : BooleanFunction n := fun x => chi (F x)

theorem chi_sum {ι : Type*} (s : Finset ι) (f : ι → ZMod 2) :
    chi (∑ i ∈ s, f i) = ∏ i ∈ s, chi (f i) := by
  classical
  induction s using Finset.induction with
  | empty => simp [chi]
  | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.prod_insert ha, BooleanAnalysis.Internal.chi_add, ih]

/-- The Hadamard encoding of an assignment `a`: the linear function
`x ↦ ⟨a, x⟩`. -/
def hadamard (a : Cube n) : BitFun n := fun x => ∑ i, a i * x i

/-- **The Hadamard code is a parity function.** Its `±1` encoding is `χ` of the
support of the assignment — so the Fourier layer's linearity results apply to
Hadamard proofs verbatim, and the decoded coordinate set is the assignment's
support. -/
theorem signOf_hadamard (a : Cube n) :
    signOf (hadamard a) = χ (Finset.univ.filter fun i => a i = 1) := by
  classical
  funext x
  show chi (∑ i, a i * x i) = ∏ i ∈ Finset.univ.filter (fun i => a i = 1), chi (x i)
  rw [chi_sum]
  rw [← Finset.prod_filter_mul_prod_filter_not Finset.univ (fun i => a i = 1)
    (fun i => chi (a i * x i))]
  have hone : ∏ i ∈ Finset.univ.filter (fun i => ¬ a i = 1), chi (a i * x i) = 1 := by
    refine Finset.prod_eq_one fun i hi => ?_
    simp only [Finset.mem_filter] at hi
    have hzero : a i = 0 := by
      rcases (by decide : ∀ b : ZMod 2, b = 0 ∨ b = 1) (a i) with h | h
      · exact h
      · exact absurd h hi.2
    rw [hzero, zero_mul]
    simp
  rw [hone, mul_one]
  refine Finset.prod_congr rfl fun i hi => ?_
  simp only [Finset.mem_filter] at hi
  rw [hi.2, one_mul]

/-! ### The tensor part -/

/-- The outer product of two cube points, as a point of the squared cube. The
Fourier layer is indexed by `Fin n`, so the pair index is transported along
`finProdFinEquiv`. -/
def tensor (x y : Cube n) : Cube (n * n) :=
  fun k => x (finProdFinEquiv.symm k).1 * y (finProdFinEquiv.symm k).2

/-- The tensor square of an assignment — the second table a Hadamard proof
carries, so that the verifier can evaluate quadratic constraints. -/
def tensorAssign (a : Cube n) : Cube (n * n) := tensor a a

/-- **The consistency identity.** The tensor table, read at an outer product,
is the product of the two linear readings. This is the check that ties the
quadratic table to the linear one, and it is a statement about *bits*: over
`𝔽₂` the right-hand side is a product, which is why the tester's checks cannot
be phrased in the `±1` encoding. -/
theorem hadamard_tensor (a x y : Cube n) :
    hadamard (tensorAssign a) (tensor x y) = hadamard a x * hadamard a y := by
  classical
  have hre : ∀ f : Fin n × Fin n → ZMod 2,
      ∑ k : Fin (n * n), f (finProdFinEquiv.symm k) = ∑ p : Fin n × Fin n, f p := by
    intro f
    exact Fintype.sum_equiv finProdFinEquiv.symm (fun k => f (finProdFinEquiv.symm k)) f
      fun k => rfl
  show ∑ k : Fin (n * n), (tensorAssign a) k * (tensor x y) k
    = (∑ i, a i * x i) * (∑ j, a j * y j)
  have hstep : ∑ k : Fin (n * n), (tensorAssign a) k * (tensor x y) k
      = ∑ p : Fin n × Fin n, (a p.1 * a p.2) * (x p.1 * y p.2) :=
    hre fun p => (a p.1 * a p.2) * (x p.1 * y p.2)
  rw [hstep, Fintype.sum_prod_type, Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

/-! ### Decoding a proof into an assignment -/

/-- The assignment a coordinate set stands for. -/
def indicatorAssign (S : Finset (Fin n)) : Cube n := fun i => if i ∈ S then 1 else 0

/-- **Every parity function is a Hadamard codeword.** With `signOf_hadamard`
this makes the correspondence between assignments and parity functions a
bijection, so BLR's coordinate set can be handed back as an assignment. -/
theorem parity_eq_signOf_hadamard (S : Finset (Fin n)) :
    (χ S) = signOf (hadamard (indicatorAssign S)) := by
  classical
  rw [signOf_hadamard]
  congr 1
  ext i
  simp only [indicatorAssign]
  by_cases hi : i ∈ S
  · simp [hi]
  · simp [hi]

/-- **Decoding.** A proof passing the linearity test is close to the Hadamard
encoding of an explicit assignment — the assignment the tester extracts. -/
theorem exists_assignment_of_blr (f : BooleanFunction n) (hf : IsBooleanValued f)
    (ε : ℝ) (h : blrAcceptProb f ≥ 1 - ε) :
    ∃ a : Cube n, hammingDist f (signOf (hadamard a)) ≤ ε := by
  obtain ⟨S, hS⟩ := exists_close_parity_of_blr f hf ε h
  refine ⟨indicatorAssign S, ?_⟩
  rw [← parity_eq_signOf_hadamard S]
  exact hS

/-! ### Consistency forces the tensor -/

/-- Reading a Hadamard table at a basis vector returns that coordinate. -/
theorem hadamard_basisVec (a : Cube n) (i : Fin n) : hadamard a (basisVec i) = a i := by
  classical
  show ∑ j, a j * (basisVec i) j = a i
  rw [Finset.sum_eq_single i]
  · show a i * (if i = i then (1 : ZMod 2) else 0) = a i
    rw [ite_eq_left rfl, mul_one]
  · intro j _ hj
    show a j * (if j = i then (1 : ZMod 2) else 0) = 0
    rw [ite_eq_right hj, mul_zero]
  · intro hni
    exact absurd (Finset.mem_univ i) hni

/-- The outer product of two basis vectors is the basis vector at the
corresponding pair index. -/
theorem tensor_basisVec (i j : Fin n) :
    tensor (basisVec i) (basisVec j) = basisVec (finProdFinEquiv (i, j)) := by
  classical
  funext k
  show (basisVec i) (finProdFinEquiv.symm k).1 * (basisVec j) (finProdFinEquiv.symm k).2
    = if k = finProdFinEquiv (i, j) then (1 : ZMod 2) else 0
  by_cases hk : k = finProdFinEquiv (i, j)
  · subst hk
    rw [ite_eq_left rfl, Equiv.symm_apply_apply]
    show (if i = i then (1 : ZMod 2) else 0) * (if j = j then (1 : ZMod 2) else 0) = 1
    rw [ite_eq_left rfl, ite_eq_left rfl, mul_one]
  · rw [ite_eq_right hk]
    by_cases h1 : (finProdFinEquiv.symm k).1 = i
    · by_cases h2 : (finProdFinEquiv.symm k).2 = j
      · exfalso
        apply hk
        have hpair : finProdFinEquiv.symm k = (i, j) := Prod.ext h1 h2
        rw [← hpair, Equiv.apply_symm_apply]
      · show (if (finProdFinEquiv.symm k).1 = i then (1 : ZMod 2) else 0)
          * (if (finProdFinEquiv.symm k).2 = j then (1 : ZMod 2) else 0) = 0
        rw [ite_eq_right h2, mul_zero]
    · show (if (finProdFinEquiv.symm k).1 = i then (1 : ZMod 2) else 0)
        * (if (finProdFinEquiv.symm k).2 = j then (1 : ZMod 2) else 0) = 0
      rw [ite_eq_right h1, zero_mul]

/-- **Consistency forces the tensor.** A quadratic table that agrees with the
product of the linear readings on every outer product *is* the tensor square of
the assignment — testing at basis vectors pins down every entry. This is why the
consistency check suffices: it leaves the prover no freedom in the quadratic
table. -/
theorem eq_tensorAssign_of_consistent (a : Cube n) (b : Cube (n * n))
    (h : ∀ x y : Cube n, hadamard b (tensor x y) = hadamard a x * hadamard a y) :
    b = tensorAssign a := by
  classical
  funext k
  set i := (finProdFinEquiv.symm k).1 with hi
  set j := (finProdFinEquiv.symm k).2 with hj
  have hk : k = finProdFinEquiv (i, j) := by
    rw [hi, hj, Prod.mk.eta, Equiv.apply_symm_apply]
  have hb := h (basisVec i) (basisVec j)
  rw [tensor_basisVec, hadamard_basisVec, hadamard_basisVec, hadamard_basisVec] at hb
  show b k = a i * a j
  rw [hk]
  exact hb

/-! ### Checking a constraint -/

/-- A quadratic constraint over `𝔽₂`. Dinur's inner verifier tests exactly
this: the constraints of a system with a constant-size alphabet are quadratic
equations once the alphabet symbols are spelled out in bits. -/
structure QuadConstraint (n : ℕ) where
  /-- The quadratic coefficients, indexed like the tensor table. -/
  quad : Cube (n * n)
  /-- The linear coefficients. -/
  lin : Cube n
  /-- The constant term. -/
  const : ZMod 2

/-- The constraint evaluated at an assignment. -/
def QuadConstraint.eval (C : QuadConstraint n) (a : Cube n) : ZMod 2 :=
  hadamard (tensorAssign a) C.quad + hadamard a C.lin + C.const

/-- The assignment satisfies the constraint. -/
def QuadConstraint.Sat (C : QuadConstraint n) (a : Cube n) : Prop := C.eval a = 0

/-- What the verifier computes from the two tables: one query into each. -/
def checkValue (F : BitFun (n * n)) (f : BitFun n) (C : QuadConstraint n) : ZMod 2 :=
  F C.quad + f C.lin + C.const

/-- On honest tables the check *is* the constraint — this is completeness. -/
theorem checkValue_hadamard (a : Cube n) (C : QuadConstraint n) :
    checkValue (hadamard (tensorAssign a)) (hadamard a) C = C.eval a := rfl

/-- **Tester soundness, exact form.** If the two tables are Hadamard codewords,
the consistency check holds everywhere, and the constraint check passes, then
the decoded assignment satisfies the constraint. The prover's only freedom is
the assignment itself: consistency pins the quadratic table to the tensor of the
linear one, and then the check computes the constraint honestly. -/
theorem sat_of_checks (a : Cube n) (b : Cube (n * n)) (C : QuadConstraint n)
    (hcons : ∀ x y : Cube n, hadamard b (tensor x y) = hadamard a x * hadamard a y)
    (hcheck : checkValue (hadamard b) (hadamard a) C = 0) :
    C.Sat a := by
  rw [QuadConstraint.Sat, QuadConstraint.eval, ← eq_tensorAssign_of_consistent a b hcons]
  exact hcheck

/-- The Hadamard encoding of an assignment is linear, so it passes the
linearity test with certainty. -/
theorem isLinear_signOf_hadamard (a : Cube n) : IsLinear (signOf (hadamard a)) := by
  classical
  refine ⟨Finset.univ.filter fun i => a i = 1, fun x => ?_⟩
  rw [signOf_hadamard]

/-- **Tester completeness, exact form.** The honest tables of a satisfying
assignment pass the linearity test with certainty, satisfy the consistency check
everywhere, and pass the constraint check. -/
theorem checks_of_sat (a : Cube n) (C : QuadConstraint n) (h : C.Sat a) :
    blrAcceptProb (signOf (hadamard a)) = 1
      ∧ (∀ x y : Cube n,
          hadamard (tensorAssign a) (tensor x y) = hadamard a x * hadamard a y)
      ∧ checkValue (hadamard (tensorAssign a)) (hadamard a) C = 0 := by
  refine ⟨blr_completeness _ (isLinear_signOf_hadamard a), hadamard_tensor a, ?_⟩
  rw [checkValue_hadamard]
  exact h

/-! ### Rigidity of the decoding -/

/-- **Distinct parity functions are far apart.** Two different parity functions
disagree on exactly half the cube, so agreeing on more than half forces them to
be equal.

This is what makes the approximate tester work: the decoded tables are linear,
and a check that passes on a large enough fraction of the cube therefore holds
*everywhere* on the corrected tables — turning a probabilistic hypothesis into
the exact one `sat_of_checks` needs. -/
theorem eq_of_hammingDist_lt_half {S T : Finset (Fin n)}
    (h : hammingDist (χ S) (χ T) < 1 / 2) : S = T := by
  by_contra hne
  have h1 : ⟪χ S, χ T⟫ = 0 := by
    rw [parityFun_orthonormal]
    exact ite_eq_right hne
  have h2 : ⟪χ S, χ T⟫ = 1 - 2 * hammingDist (χ S) (χ T) :=
    inner_eq_one_sub_two_dist _ _ (isBooleanValued_parityFun S)
      (isBooleanValued_parityFun T)
  rw [h1] at h2
  linarith

theorem hammingDist_comm (f g : BooleanFunction n) :
    hammingDist f g = hammingDist g f := by
  have hpred : (fun x => f x ≠ g x) = (fun x => g x ≠ f x) := by
    funext x
    exact propext ⟨fun h => Ne.symm h, fun h => Ne.symm h⟩
  rw [hammingDist, hammingDist, hpred]

theorem hammingDist_triangle (f g h : BooleanFunction n) :
    hammingDist f h ≤ hammingDist f g + hammingDist g h := by
  have hbound := BooleanAnalysis.Internal.prob_union_bound
    (P := fun x => f x = h x) (Q := fun x => f x ≠ g x) (R := fun x => g x ≠ h x)
    (fun x hx => by
      by_contra hcon
      push Not at hcon
      exact hx (hcon.1.trans hcon.2))
  exact hbound

/-- The decoded assignment is unique: a proof cannot be close to the Hadamard
encodings of two different assignments. -/
theorem hadamard_inj_of_close {S T : Finset (Fin n)} {f : BooleanFunction n} {ε : ℝ}
    (hε : ε < 1 / 4) (hS : hammingDist f (χ S) ≤ ε) (hT : hammingDist f (χ T) ≤ ε) :
    S = T := by
  refine eq_of_hammingDist_lt_half ?_
  have htri : hammingDist (χ S) (χ T)
      ≤ hammingDist (χ S) f + hammingDist f (χ T) :=
    hammingDist_triangle _ _ _
  have hsymm : hammingDist (χ S) f = hammingDist f (χ S) := hammingDist_comm _ _
  rw [hsymm] at htri
  linarith

/-! ### A nonzero linear form is balanced -/

/-- The `±1` encoding turns a bit into `1 - 2·bit`. -/
theorem chi_eq_one_sub_two (v : ZMod 2) :
    chi v = 1 - 2 * (if v ≠ 0 then (1 : ℝ) else 0) := by
  by_cases h : v = 0
  · rw [h]
    norm_num [chi]
  · rw [ite_eq_left h]
    have hchi : chi v = -1 := by simp [chi, h]
    rw [hchi]
    norm_num

theorem card_cube (n : ℕ) : Fintype.card (Cube n) = 2 ^ n := by
  show Fintype.card (Fin n → ZMod 2) = 2 ^ n
  rw [Fintype.card_fun, ZMod.card, Fintype.card_fin]

/-- The expectation of a bit function's sign encoding. -/
theorem expect_signOf (F : BitFun n) :
    𝔼[signOf F] = 1 - 2 * Pr[fun x => F x ≠ 0] := by
  classical
  rw [expect_unfold, BooleanAnalysis.prob, expect_unfold]
  simp only [BooleanAnalysis.indicator]
  have hterm : ∀ x : Cube n, (signOf F) x = 1 - 2 * (if F x ≠ 0 then (1 : ℝ) else 0) :=
    fun x => chi_eq_one_sub_two (F x)
  rw [Finset.sum_congr rfl fun x _ => hterm x, Finset.sum_sub_distrib, ← Finset.mul_sum]
  have hcard : ∑ _x : Cube n, (1 : ℝ) = 2 ^ n := by
    rw [Finset.sum_const, Finset.card_univ, card_cube, nsmul_eq_mul, mul_one]
    norm_num
  rw [hcard]
  field_simp
  ring_nf

/-- **A nonzero linear form is balanced.** Over `𝔽₂` a nonzero linear form takes
each value on exactly half the cube — the counting fact behind every "the check
cannot pass too often unless it always passes" step. -/
theorem prob_hadamard_ne_zero (a : Cube n) (ha : a ≠ 0) :
    Pr[fun x => hadamard a x ≠ 0] = 1 / 2 := by
  classical
  have hne : (Finset.univ.filter fun i => a i = 1) ≠ ∅ := by
    intro hempty
    apply ha
    funext i
    have hi : i ∉ Finset.univ.filter fun j => a j = 1 := by
      rw [hempty]
      exact Finset.notMem_empty i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
    rcases (by decide : ∀ b : ZMod 2, b = 0 ∨ b = 1) (a i) with h | h
    · exact h
    · exact absurd h hi
  have hexp : 𝔼[signOf (hadamard a)] = 0 := by
    rw [signOf_hadamard, expect_parityFun, ite_eq_right hne]
  rw [expect_signOf] at hexp
  linarith

/-! ### The bilinear form -/

/-- The bilinear form of `c`, contracted against `y`: the linear form in `x`
obtained by fixing the second argument. -/
def tensorRow (c : Cube (n * n)) (y : Cube n) : Cube n :=
  fun i => ∑ j, c (finProdFinEquiv (i, j)) * y j

/-- **Row decomposition.** Reading the quadratic table at an outer product is a
*linear* reading in the first argument, with coefficients contracted against the
second. This is what lets the one-variable balance lemma be applied inside a
two-variable check. -/
theorem hadamard_tensor_row (c : Cube (n * n)) (x y : Cube n) :
    hadamard c (tensor x y) = hadamard (tensorRow c y) x := by
  classical
  have hre : ∀ f : Fin n × Fin n → ZMod 2,
      ∑ k : Fin (n * n), f (finProdFinEquiv.symm k) = ∑ p : Fin n × Fin n, f p := by
    intro f
    exact Fintype.sum_equiv finProdFinEquiv.symm (fun k => f (finProdFinEquiv.symm k)) f
      fun k => rfl
  have hlhs : hadamard c (tensor x y)
      = ∑ p : Fin n × Fin n, c (finProdFinEquiv p) * (x p.1 * y p.2) := by
    show ∑ k : Fin (n * n), c k * (tensor x y) k = _
    have hstep : ∑ k : Fin (n * n), c k * (tensor x y) k
        = ∑ p : Fin n × Fin n,
          c (finProdFinEquiv p) * (x p.1 * y p.2) := by
      refine Eq.trans ?_ (hre fun p => c (finProdFinEquiv p) * (x p.1 * y p.2))
      refine Finset.sum_congr rfl fun k _ => ?_
      show c k * ((x (finProdFinEquiv.symm k).1) * (y (finProdFinEquiv.symm k).2))
        = c (finProdFinEquiv (finProdFinEquiv.symm k))
          * (x (finProdFinEquiv.symm k).1 * y (finProdFinEquiv.symm k).2)
      rw [Equiv.apply_symm_apply]
    exact hstep
  rw [hlhs]
  show _ = ∑ i, (∑ j, c (finProdFinEquiv (i, j)) * y j) * x i
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

/-- Probability is monotone. The Fourier layer has the union bound and
complements but not this. -/
theorem prob_mono {P Q : Cube n → Prop} (h : ∀ x, P x → Q x) : Pr[P] ≤ Pr[Q] := by
  classical
  simp only [BooleanAnalysis.prob, expect_unfold, BooleanAnalysis.indicator]
  refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun x _ => ?_) (by positivity)
  by_cases hp : P x
  · rw [ite_eq_left hp, ite_eq_left (h x hp)]
  · rw [ite_eq_right hp]
    split_ifs <;> norm_num

/-- **The bilinear form is nonzero on many rows.** If the quadratic table's
error `c` is nonzero, then for at least half the `y` the contracted linear form
is nonzero — the first half of the `1/4` bound. -/
theorem prob_tensorRow_ne_zero (c : Cube (n * n)) (hc : c ≠ 0) :
    1 / 2 ≤ Pr[fun y => tensorRow c y ≠ 0] := by
  classical
  obtain ⟨k, hk⟩ : ∃ k, c k ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hc (funext hcon)
  set i := (finProdFinEquiv.symm k).1 with hi
  set j := (finProdFinEquiv.symm k).2 with hj
  have hkij : k = finProdFinEquiv (i, j) := by
    rw [hi, hj, Prod.mk.eta, Equiv.apply_symm_apply]
  set d : Cube n := fun j' => c (finProdFinEquiv (i, j')) with hd
  have hdne : d ≠ 0 := by
    intro h0
    apply hk
    rw [hkij]
    have := congrFun h0 j
    rw [hd] at this
    exact this
  have hrow : ∀ y : Cube n, (tensorRow c y) i = hadamard d y := fun y => rfl
  have hsub : ∀ y : Cube n, hadamard d y ≠ 0 → tensorRow c y ≠ 0 := by
    intro y hy hzero
    apply hy
    rw [← hrow y, hzero]
    rfl
  calc (1 : ℝ) / 2 = Pr[fun y => hadamard d y ≠ 0] := (prob_hadamard_ne_zero d hdne).symm
    _ ≤ Pr[fun y => tensorRow c y ≠ 0] := prob_mono hsub

theorem expect_mono {f g : BooleanFunction n} (h : ∀ x, f x ≤ g x) : 𝔼[f] ≤ 𝔼[g] := by
  rw [expect_unfold, expect_unfold]
  exact mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun x _ => h x) (by positivity)

theorem expect_const_mul (c : ℝ) (f : BooleanFunction n) :
    𝔼[fun x => c * f x] = c * 𝔼[f] := by
  rw [expect_unfold (f := fun x : Cube n => c * f x), expect_unfold (f := f),
    ← Finset.mul_sum (s := Finset.univ) (a := c) (f := fun x : Cube n => f x)]
  ring

/-- **A nonzero bilinear form is nonzero on a quarter of all pairs.** For at
least half the second arguments the contracted form is nonzero, and each such
form is nonzero on exactly half the first arguments.

This is the quantitative heart of the consistency check: a prover whose
quadratic table differs from the tensor square fails the check on at least a
quarter of the pairs, so passing it more often than that forces the tables to
agree exactly. -/
theorem prob₂_tensor_ne_zero (c : Cube (n * n)) (hc : c ≠ 0) :
    1 / 4 ≤ Pr₂[fun y x => hadamard c (tensor x y) ≠ 0] := by
  classical
  have hpoint : ∀ y : Cube n,
      (1 / 2 : ℝ) * (if tensorRow c y ≠ 0 then (1 : ℝ) else 0)
        ≤ 𝔼[BooleanAnalysis.indicator (fun x => hadamard c (tensor x y) ≠ 0)] := by
    intro y
    have hcond : (fun x => hadamard c (tensor x y) ≠ 0)
        = (fun x => hadamard (tensorRow c y) x ≠ 0) := by
      funext x
      rw [hadamard_tensor_row]
    by_cases hy : tensorRow c y ≠ 0
    · rw [ite_eq_left hy, mul_one, hcond]
      exact le_of_eq (prob_hadamard_ne_zero _ hy).symm
    · rw [ite_eq_right hy, mul_zero]
      exact BooleanAnalysis.Internal.prob_nonneg _
  have hhalf := prob_tensorRow_ne_zero c hc
  calc (1 : ℝ) / 4 = (1 / 2) * (1 / 2) := by norm_num
    _ ≤ (1 / 2) * Pr[fun y => tensorRow c y ≠ 0] := by linarith
    _ = 𝔼[fun y => (1 / 2 : ℝ) * (if tensorRow c y ≠ 0 then (1 : ℝ) else 0)] := by
        rw [expect_const_mul (n := n) (c := (1 / 2 : ℝ))
          (f := fun y : Cube n => if tensorRow c y ≠ 0 then (1 : ℝ) else 0)]
        congr 1
        rw [BooleanAnalysis.prob]
        congr 1
        funext y
        simp [BooleanAnalysis.indicator]
    _ ≤ Pr₂[fun y x => hadamard c (tensor x y) ≠ 0] := expect_mono hpoint

/-! ### Approximate consistency -/

theorem hadamard_add {m : ℕ} (b c z : Cube m) :
    hadamard (b + c) z = hadamard b z + hadamard c z := by
  show ∑ i, (b i + c i) * z i = (∑ i, b i * z i) + (∑ i, c i * z i)
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i _ => by ring

theorem expect_add (f g : BooleanFunction n) :
    𝔼[fun x => f x + g x] = 𝔼[f] + 𝔼[g] := by
  rw [expect_unfold (f := fun x : Cube n => f x + g x), expect_unfold (f := f),
    expect_unfold (f := g), ← mul_add,
    ← Finset.sum_add_distrib (f := fun x : Cube n => f x) (g := fun x : Cube n => g x)]

theorem expect_one : 𝔼[fun _ : Cube n => (1 : ℝ)] = 1 := by
  rw [expect_unfold (f := fun _ : Cube n => (1 : ℝ)), Finset.sum_const, Finset.card_univ,
    card_cube, nsmul_eq_mul, mul_one]
  push_cast
  field_simp

theorem prob₂_compl (P : Cube n → Cube n → Prop) :
    Pr₂[P] + Pr₂[fun x y => ¬ P x y] = 1 := by
  classical
  rw [BooleanAnalysis.prob₂, BooleanAnalysis.prob₂, ← expect_add (f := fun x : Cube n => 𝔼[𝟙(P x)])
      (g := fun x : Cube n => 𝔼[𝟙fun y => ¬P x y]), ← expect_one (n := n)]
  congr 1
  funext x
  exact BooleanAnalysis.Internal.prob_compl (P x)

/-- **Approximate consistency forces the tensor.** A quadratic table passing the
consistency check on more than three quarters of the pairs must be the tensor
square: otherwise their difference is a nonzero bilinear form, which
`prob₂_tensor_ne_zero` says fails on at least a quarter. -/
theorem eq_tensorAssign_of_prob_consistent (a : Cube n) (b : Cube (n * n))
    (h : 3 / 4 < Pr₂[fun y x =>
      hadamard b (tensor x y) = hadamard a x * hadamard a y]) :
    b = tensorAssign a := by
  classical
  by_contra hne
  have hcne : b + tensorAssign a ≠ 0 := by
    intro h0
    apply hne
    funext k
    have hk := congrFun h0 k
    show b k = (tensorAssign a) k
    rcases (by decide : ∀ u v : ZMod 2, u + v = 0 → u = v) (b k) ((tensorAssign a) k) hk with h'
    exact h'
  have hquarter := prob₂_tensor_ne_zero (b + tensorAssign a) hcne
  have hfail : (fun y x => hadamard (b + tensorAssign a) (tensor x y) ≠ 0)
      = fun y x => ¬ (hadamard b (tensor x y) = hadamard a x * hadamard a y) := by
    funext y x
    rw [hadamard_add, hadamard_tensor]
    have hiff : (hadamard b (tensor x y) + hadamard a x * hadamard a y = 0)
        ↔ (hadamard b (tensor x y) = hadamard a x * hadamard a y) := by
      rcases (by decide : ∀ u v : ZMod 2, (u + v = 0) ↔ (u = v)) (hadamard b (tensor x y))
        (hadamard a x * hadamard a y) with h'
      exact h'
    exact propext (not_congr hiff)
  rw [hfail] at hquarter
  have hcompl := prob₂_compl (fun y x =>
    hadamard b (tensor x y) = hadamard a x * hadamard a y)
  linarith

/-! ### Reads over bundled randomness -/

/-- **A corrected read is right.** Reading a close-to-linear table by
self-correction, with the randomness taken from the first block of a bundled
random string, returns the codeword's value except with probability `2ε`. -/
theorem prob_corrected_read_left (f : BooleanFunction n) (hf : IsBooleanValued f)
    (S : Finset (Fin n)) {ε : ℝ} (hclose : IsClose f (χ S) ε) (x : Cube n) :
    1 - 2 * ε ≤ Pr[fun z : Cube (n + n) =>
      f (leftBlock z) * f (x + leftBlock z) = (χ S) x] := by
  have h : Pr[fun z : Cube (n + n) => f (leftBlock z) * f (x + leftBlock z) = (χ S) x]
      = Pr[fun y : Cube n => f y * f (x + y) = (χ S) x] :=
    prob_leftBlock (fun y => f y * f (x + y) = (χ S) x)
  rw [h]
  exact local_correctability f hf S hclose x

/-- The same for the second block. -/
theorem prob_corrected_read_right (f : BooleanFunction n) (hf : IsBooleanValued f)
    (S : Finset (Fin n)) {ε : ℝ} (hclose : IsClose f (χ S) ε) (x : Cube n) :
    1 - 2 * ε ≤ Pr[fun z : Cube (n + n) =>
      f (rightBlock z) * f (x + rightBlock z) = (χ S) x] := by
  have h : Pr[fun z : Cube (n + n) => f (rightBlock z) * f (x + rightBlock z) = (χ S) x]
      = Pr[fun y : Cube n => f y * f (x + y) = (χ S) x] :=
    prob_rightBlock (fun y => f y * f (x + y) = (χ S) x)
  rw [h]
  exact local_correctability f hf S hclose x

/-- **Two corrected reads are both right.** The union bound over the two blocks:
bundling the randomness is what makes this an ordinary one-variable union bound
rather than a product-measure argument. -/
theorem prob_two_corrected_reads (f : BooleanFunction n) (hf : IsBooleanValued f)
    (S : Finset (Fin n)) {ε : ℝ} (hclose : IsClose f (χ S) ε) (x x' : Cube n) :
    1 - 4 * ε ≤ Pr[fun z : Cube (n + n) =>
      f (leftBlock z) * f (x + leftBlock z) = (χ S) x
        ∧ f (rightBlock z) * f (x' + rightBlock z) = (χ S) x'] := by
  classical
  have hleft := prob_corrected_read_left f hf S hclose x
  have hright := prob_corrected_read_right f hf S hclose x'
  have hcl : Pr[fun z : Cube (n + n) => ¬ (f (leftBlock z) * f (x + leftBlock z) = (χ S) x)]
      ≤ 2 * ε := by
    have := BooleanAnalysis.Internal.prob_compl
      (fun z : Cube (n + n) => f (leftBlock z) * f (x + leftBlock z) = (χ S) x)
    linarith
  have hcr : Pr[fun z : Cube (n + n) =>
      ¬ (f (rightBlock z) * f (x' + rightBlock z) = (χ S) x')] ≤ 2 * ε := by
    have := BooleanAnalysis.Internal.prob_compl
      (fun z : Cube (n + n) => f (rightBlock z) * f (x' + rightBlock z) = (χ S) x')
    linarith
  have hunion := BooleanAnalysis.Internal.prob_union_bound
    (P := fun z : Cube (n + n) => f (leftBlock z) * f (x + leftBlock z) = (χ S) x
      ∧ f (rightBlock z) * f (x' + rightBlock z) = (χ S) x')
    (Q := fun z : Cube (n + n) => ¬ (f (leftBlock z) * f (x + leftBlock z) = (χ S) x))
    (R := fun z : Cube (n + n) =>
      ¬ (f (rightBlock z) * f (x' + rightBlock z) = (χ S) x'))
    (fun z hz => by
      by_contra hcon
      push Not at hcon
      exact hz ⟨hcon.1, hcon.2⟩)
  have hcompl := BooleanAnalysis.Internal.prob_compl
    (fun z : Cube (n + n) => f (leftBlock z) * f (x + leftBlock z) = (χ S) x
      ∧ f (rightBlock z) * f (x' + rightBlock z) = (χ S) x')
  linarith

/-- **Tester soundness with a probabilistic consistency check.** The verifier
cannot test consistency everywhere — it tests one random pair. This says that is
enough: passing on more than three quarters of the pairs pins the quadratic table
down exactly, and then the constraint check computes the constraint honestly.

Together with `checks_of_sat` this is the assignment tester's guarantee at the
level of decoded tables: the prover's only freedom is which assignment to encode,
and if the checks pass, that assignment satisfies the constraint. -/
theorem sat_of_prob_checks (a : Cube n) (b : Cube (n * n)) (C : QuadConstraint n)
    (hcons : 3 / 4 < Pr₂[fun y x =>
      hadamard b (tensor x y) = hadamard a x * hadamard a y])
    (hcheck : checkValue (hadamard b) (hadamard a) C = 0) :
    C.Sat a := by
  refine sat_of_checks a b C (fun x y => ?_) hcheck
  rw [eq_tensorAssign_of_prob_consistent a b hcons]
  exact hadamard_tensor a x y

theorem prob₂_of_forall {P : Cube n → Cube n → Prop} (h : ∀ x y, P x y) : Pr₂[P] = 1 := by
  classical
  rw [BooleanAnalysis.prob₂]
  have hpt : ∀ x : Cube n, 𝔼[BooleanAnalysis.indicator (P x)] = 1 :=
    fun x => prob_of_forall (h x)
  calc 𝔼[fun x => 𝔼[BooleanAnalysis.indicator (P x)]] = 𝔼[fun _ : Cube n => (1 : ℝ)] := by
        congr 1
        funext x
        exact hpt x
    _ = 1 := expect_one

/-- **Completeness of the consistency check.** The honest tables pass it on every
pair, so the tester accepts a correct proof with certainty. -/
theorem prob_consistency_of_honest (a : Cube n) :
    Pr₂[fun y x =>
      hadamard (tensorAssign a) (tensor x y) = hadamard a x * hadamard a y] = 1 :=
  prob₂_of_forall fun y x => hadamard_tensor a x y

/-- **All of a tester's reads are correct.** Given a close-to-linear table and
any family of blocks of a bundled random string — each uniformly distributed,
which is what `hblk` asks and what `CubeBlocks` supplies — every self-corrected
read returns the codeword's value, except with probability `2kε`.

Parameterising by the block maps keeps this independent of how many reads the
tester makes and how the string is carved up. -/
theorem prob_all_reads {m k : ℕ} (f : BooleanFunction n) (hf : IsBooleanValued f)
    (S : Finset (Fin n)) {ε : ℝ} (hclose : IsClose f (χ S) ε)
    (blk : Fin k → Cube m → Cube n)
    (hblk : ∀ (i : Fin k) (P : Cube n → Prop),
      Pr[fun z : Cube m => P (blk i z)] = Pr[P])
    (pts : Fin k → Cube n) :
    1 - k * (2 * ε) ≤ Pr[fun z : Cube m =>
      ∀ i, f (blk i z) * f (pts i + blk i z) = (χ S) (pts i)] := by
  classical
  refine prob_forall_ge k
    (fun i z => f (blk i z) * f (pts i + blk i z) = (χ S) (pts i)) (2 * ε) fun i => ?_
  have hmarg : Pr[fun z : Cube m => f (blk i z) * f (pts i + blk i z) = (χ S) (pts i)]
      = Pr[fun y : Cube n => f y * f (pts i + y) = (χ S) (pts i)] :=
    hblk i (fun y => f y * f (pts i + y) = (χ S) (pts i))
  rw [hmarg]
  exact local_correctability f hf S hclose (pts i)

end Complexity
