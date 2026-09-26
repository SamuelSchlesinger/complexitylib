/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/
module
public import Complexitylib.Classes.PCP.Internal.Hadamard

/-!
# The Hadamard tester, as it actually runs

`Complexitylib.Classes.PCP.Internal.Hadamard` analyses the tester at the
*decoded* level: its statements are about the codewords `hadamard a` and
`hadamard b` that the two proof tables are supposed to be. A tester cannot read
those. It reads the tables it is given, which are only *close* to codewords, and
it recovers codeword values by self-correction — reading two nearby entries and
multiplying.

This module closes that gap. The tester's whole random string is one point of a
bundled cube (`CubeBlocks`): the first block picks the two query points, and the
remaining blocks supply one correction string per read. Every read is then
correct except with probability `2ε`, the failures are collected by a union
bound, and `prob_le_of_imp_of_good` transfers the observed acceptance
probability to the decoded check that `Hadamard` already knows how to use.

The one wrinkle is that the consistency check is *bilinear over `𝔽₂`*, not
multiplicative on signs: `⟨a ⊗ a, x ⊗ y⟩ = ⟨a, x⟩ · ⟨a, y⟩` is a product of
bits, and `chi` does not carry products of bits to products of signs. So the
reads' `±1` answers are converted back to bits by `signBit` before being
compared, which is exactly how the check is stated in the literature.

## Main definitions

- `Complexity.signBit` — the bit a `±1` answer stands for
- `Complexity.TesterAccepts` — the tester's check on the raw tables
- `Complexity.ReadsCorrect` — the event that every self-corrected read is right

## Main results

- `Complexity.prob_reads_correct` — every read is right except with
  probability `4ε + 2ε'`
- `Complexity.prob_testerAccepts_of_honest` — completeness: the honest proof
  is accepted always
- `Complexity.sat_of_prob_tester` — **soundness of the tester as it runs**: if
  the raw tables are close to codewords and the raw check passes often enough,
  the decoded assignment satisfies the constraint
- `Complexity.exists_sat_of_prob_tester` — the same with *nothing* assumed
  about the proof: BLR supplies the closeness
-/

@[expose] public section

namespace Complexity

open BooleanAnalysis

variable {n : ℕ}

/-! ### Reading a sign as a bit -/

/-- The bit a `±1` answer stands for. -/
noncomputable def signBit (r : ℝ) : ZMod 2 := if r = 1 then 0 else 1

/-- Signs and bits correspond: `signBit` inverts `chi`. -/
theorem signBit_chi (u : ZMod 2) : signBit (chi u) = u := by
  rcases (by decide : ∀ u : ZMod 2, u = 0 ∨ u = 1) u with h | h <;> subst h
  · norm_num [signBit, BooleanAnalysis.chi]
  · norm_num [signBit, BooleanAnalysis.chi]

/-- **A self-corrected read is right.** The decoded-level restatement of
`local_correctability`: the value returned is the codeword's bit, read as a
sign. -/
theorem prob_read_ge {m : ℕ} (f : BooleanFunction m) (_hf : IsBooleanValued f)
    (a : Cube m) {ε : ℝ} (hc : IsClose f (signOf (hadamard a)) ε) (x : Cube m) :
    1 - 2 * ε ≤ Pr[fun r : Cube m => f r * f (x + r) = chi (hadamard a x)] := by
  classical
  have hS : IsClose f (χ (Finset.univ.filter fun i => a i = 1)) ε := by
    rwa [← signOf_hadamard]
  have heq : (χ (Finset.univ.filter fun i => a i = 1)) x = chi (hadamard a x) := by
    rw [← signOf_hadamard]
    rfl
  have h := local_correctability f (Finset.univ.filter fun i => a i = 1) hS x
  rw [heq] at h
  exact h

/-! ### The tester -/

/-- The first query point: the second half of the query block. -/
def qX (z : Cube ((n + n) + (n + (n + n * n)))) : Cube n := rightBlock (leftBlock z)

/-- The second query point: the first half of the query block. -/
def qY (z : Cube ((n + n) + (n + (n + n * n)))) : Cube n := leftBlock (leftBlock z)

/-- The correction string for the first read of the linear table. -/
def cX (z : Cube ((n + n) + (n + (n + n * n)))) : Cube n := leftBlock (rightBlock z)

/-- The correction string for the second read of the linear table. -/
def cY (z : Cube ((n + n) + (n + (n + n * n)))) : Cube n :=
  leftBlock (rightBlock (rightBlock z))

/-- The correction string for the read of the quadratic table. -/
def cQ (z : Cube ((n + n) + (n + (n + n * n)))) : Cube (n * n) :=
  rightBlock (rightBlock (rightBlock z))

/-- **The tester's check**, made on the raw tables: the self-corrected value of
the quadratic table at `x ⊗ y` must be the product, as bits, of the
self-corrected values of the linear table at `x` and at `y`. -/
def TesterAccepts (f : BooleanFunction n) (g : BooleanFunction (n * n))
    (z : Cube ((n + n) + (n + (n + n * n)))) : Prop :=
  signBit (g (cQ z) * g (tensor (qX z) (qY z) + cQ z))
    = signBit (f (cX z) * f (qX z + cX z)) * signBit (f (cY z) * f (qY z + cY z))

/-- The event that all three self-corrected reads return the codeword's value. -/
def ReadsCorrect (a : Cube n) (b : Cube (n * n)) (f : BooleanFunction n)
    (g : BooleanFunction (n * n)) (z : Cube ((n + n) + (n + (n + n * n)))) : Prop :=
  f (cX z) * f (qX z + cX z) = chi (hadamard a (qX z))
    ∧ f (cY z) * f (qY z + cY z) = chi (hadamard a (qY z))
    ∧ g (cQ z) * g (tensor (qX z) (qY z) + cQ z)
        = chi (hadamard b (tensor (qX z) (qY z)))

/-- **Every read is right, at once.** The query points are chosen by the first
block and the corrections by the rest, so `prob_blocks_ge` fixes the points
before the corrections are drawn and the three failure probabilities simply
add. -/
theorem prob_reads_correct (a : Cube n) (b : Cube (n * n))
    (f : BooleanFunction n) (hf : IsBooleanValued f) {ε : ℝ}
    (hfc : IsClose f (signOf (hadamard a)) ε)
    (g : BooleanFunction (n * n)) (hg : IsBooleanValued g) {ε' : ℝ}
    (hgc : IsClose g (signOf (hadamard b)) ε') :
    1 - (4 * ε + 2 * ε') ≤ Pr[ReadsCorrect a b f g] := by
  classical
  have hsplit : (1 : ℝ) - (4 * ε + 2 * ε') = 1 - (2 * ε + (2 * ε + 2 * ε')) := by ring
  rw [hsplit]
  refine prob_blocks_ge (fun u w =>
    f (leftBlock w) * f (rightBlock u + leftBlock w) = chi (hadamard a (rightBlock u))
      ∧ f (leftBlock (rightBlock w)) * f (leftBlock u + leftBlock (rightBlock w))
          = chi (hadamard a (leftBlock u))
      ∧ g (rightBlock (rightBlock w))
          * g (tensor (rightBlock u) (leftBlock u) + rightBlock (rightBlock w))
          = chi (hadamard b (tensor (rightBlock u) (leftBlock u)))) _ fun u => ?_
  · refine prob_and_ge ?_ (prob_and_ge ?_ ?_)
    · have h : Pr[fun w : Cube (n + (n + n * n)) =>
          f (leftBlock w) * f (rightBlock u + leftBlock w)
            = chi (hadamard a (rightBlock u))]
          = Pr[fun r : Cube n =>
            f r * f (rightBlock u + r) = chi (hadamard a (rightBlock u))] :=
        prob_leftBlock (fun r : Cube n =>
          f r * f (rightBlock u + r) = chi (hadamard a (rightBlock u)))
      rw [h]
      exact prob_read_ge f hf a hfc (rightBlock u)
    · have h : Pr[fun w : Cube (n + (n + n * n)) =>
          f (leftBlock (rightBlock w)) * f (leftBlock u + leftBlock (rightBlock w))
            = chi (hadamard a (leftBlock u))]
          = Pr[fun r : Cube n =>
            f r * f (leftBlock u + r) = chi (hadamard a (leftBlock u))] :=
        prob_leftBlock_rightBlock (fun r : Cube n =>
          f r * f (leftBlock u + r) = chi (hadamard a (leftBlock u)))
      rw [h]
      exact prob_read_ge f hf a hfc (leftBlock u)
    · have h : Pr[fun w : Cube (n + (n + n * n)) =>
          g (rightBlock (rightBlock w))
            * g (tensor (rightBlock u) (leftBlock u) + rightBlock (rightBlock w))
            = chi (hadamard b (tensor (rightBlock u) (leftBlock u)))]
          = Pr[fun r : Cube (n * n) =>
            g r * g (tensor (rightBlock u) (leftBlock u) + r)
              = chi (hadamard b (tensor (rightBlock u) (leftBlock u)))] :=
        prob_rightBlock_rightBlock (fun r : Cube (n * n) =>
          g r * g (tensor (rightBlock u) (leftBlock u) + r)
            = chi (hadamard b (tensor (rightBlock u) (leftBlock u))))
      rw [h]
      exact prob_read_ge g hg b hgc (tensor (rightBlock u) (leftBlock u))

/-- **Consistency forces the tensor, on raw tables.** The consistency check
passing often enough on tables close to codewords forces the quadratic codeword
to be the tensor square of the linear one. -/
theorem eq_tensorAssign_of_prob_tester (a : Cube n) (b : Cube (n * n))
    (f : BooleanFunction n) (hf : IsBooleanValued f) {ε : ℝ}
    (hfc : IsClose f (signOf (hadamard a)) ε)
    (g : BooleanFunction (n * n)) (hg : IsBooleanValued g) {ε' : ℝ}
    (hgc : IsClose g (signOf (hadamard b)) ε')
    (haccept : 3 / 4 + (4 * ε + 2 * ε') < Pr[TesterAccepts f g]) :
    b = tensorAssign a := by
  classical
  have hgood := prob_reads_correct a b f hf hfc g hg hgc
  have htrans := prob_le_of_imp_of_good (E := TesterAccepts f g)
    (F := fun z : Cube ((n + n) + (n + (n + n * n))) =>
      hadamard b (tensor (rightBlock (leftBlock z)) (leftBlock (leftBlock z)))
        = hadamard a (rightBlock (leftBlock z)) * hadamard a (leftBlock (leftBlock z)))
    (A := ReadsCorrect a b f g) fun z hE hA => by
      have hE' : signBit (chi (hadamard b (tensor (qX z) (qY z))))
          = signBit (chi (hadamard a (qX z))) * signBit (chi (hadamard a (qY z))) := by
        rw [← hA.1, ← hA.2.1, ← hA.2.2]
        exact hE
      rw [signBit_chi, signBit_chi, signBit_chi] at hE'
      exact hE'
  have hpair : Pr[fun z : Cube ((n + n) + (n + (n + n * n))) =>
      hadamard b (tensor (rightBlock (leftBlock z)) (leftBlock (leftBlock z)))
        = hadamard a (rightBlock (leftBlock z)) * hadamard a (leftBlock (leftBlock z))]
      = Pr₂[fun y x => hadamard b (tensor x y) = hadamard a x * hadamard a y] :=
    prob_pair_block (fun y x => hadamard b (tensor x y) = hadamard a x * hadamard a y)
  rw [hpair] at htrans
  exact eq_tensorAssign_of_prob_consistent a b (by linarith)

/-- **Soundness of the tester as it runs.** Raw tables close to Hadamard
codewords, a raw check passing on more than three quarters of the randomness
(with room for the reads' failure probability), and a constraint satisfied by
the decoded tables together force the decoded assignment to satisfy the
constraint.

The gap `4ε + 2ε'` is the price of self-correction: three reads, each wrong
with probability at most twice the table's distance from its codeword. -/
theorem sat_of_prob_tester (a : Cube n) (b : Cube (n * n)) (C : QuadConstraint n)
    (f : BooleanFunction n) (hf : IsBooleanValued f) {ε : ℝ}
    (hfc : IsClose f (signOf (hadamard a)) ε)
    (g : BooleanFunction (n * n)) (hg : IsBooleanValued g) {ε' : ℝ}
    (hgc : IsClose g (signOf (hadamard b)) ε')
    (haccept : 3 / 4 + (4 * ε + 2 * ε') < Pr[TesterAccepts f g])
    (hcheck : checkValue (hadamard b) (hadamard a) C = 0) :
    C.Sat a := by
  have hb := eq_tensorAssign_of_prob_tester a b f hf hfc g hg hgc haccept
  rw [hb] at hcheck
  exact hcheck

/-! ### Completeness -/

/-- A Hadamard codeword is linear in the query point. -/
theorem hadamard_add_right {m : ℕ} (a x r : Cube m) :
    hadamard a (x + r) = hadamard a x + hadamard a r := by
  show ∑ i, a i * (x i + r i) = (∑ i, a i * x i) + (∑ i, a i * r i)
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i _ => by ring

/-- **Self-correction is exact on an honest table.** The two reads are
`chi ⟨a, r⟩` and `chi (⟨a, x⟩ + ⟨a, r⟩)`, and their product telescopes because
`chi` turns the `𝔽₂` sum into a product of signs and `2⟨a, r⟩ = 0`. -/
theorem corrected_read_honest {m : ℕ} (a x r : Cube m) :
    signOf (hadamard a) r * signOf (hadamard a) (x + r) = chi (hadamard a x) := by
  show chi (hadamard a r) * chi (hadamard a (x + r)) = chi (hadamard a x)
  rw [hadamard_add_right, ← BooleanAnalysis.Internal.chi_add]
  congr 1
  have h2 : hadamard a r + hadamard a r = 0 := by
    rcases (by decide : ∀ u : ZMod 2, u + u = 0) (hadamard a r) with h
    exact h
  calc hadamard a r + (hadamard a x + hadamard a r)
      = hadamard a x + (hadamard a r + hadamard a r) := by ring
    _ = hadamard a x := by rw [h2, add_zero]

/-- **The honest proof passes every read.** -/
theorem readsCorrect_of_honest (a : Cube n) (z : Cube ((n + n) + (n + (n + n * n)))) :
    ReadsCorrect a (tensorAssign a) (signOf (hadamard a))
      (signOf (hadamard (tensorAssign a))) z :=
  ⟨corrected_read_honest a (qX z) (cX z), corrected_read_honest a (qY z) (cY z),
    corrected_read_honest (tensorAssign a) (tensor (qX z) (qY z)) (cQ z)⟩

/-- **Completeness of the tester as it runs.** The honest proof — the Hadamard
encoding of an assignment together with the encoding of its tensor square — is
accepted on every random string, so with probability one. -/
theorem testerAccepts_of_honest (a : Cube n) (z : Cube ((n + n) + (n + (n + n * n)))) :
    TesterAccepts (signOf (hadamard a)) (signOf (hadamard (tensorAssign a))) z := by
  have hr := readsCorrect_of_honest a z
  show signBit (signOf (hadamard (tensorAssign a)) (cQ z)
      * signOf (hadamard (tensorAssign a)) (tensor (qX z) (qY z) + cQ z)) = _
  rw [hr.1, hr.2.1, hr.2.2, signBit_chi, signBit_chi, signBit_chi]
  exact hadamard_tensor a (qX z) (qY z)

/-- The honest proof is accepted with probability one. -/
theorem prob_testerAccepts_of_honest (a : Cube n) :
    Pr[TesterAccepts (signOf (hadamard a)) (signOf (hadamard (tensorAssign a)))] = 1 :=
  prob_of_forall (testerAccepts_of_honest a)

/-! ### The constraint check -/

/-- **The tester's constraint check**, made on the raw tables: the constraint's
quadratic part is read from `g`, its linear part from `f`, both by
self-correction, and the two bits plus the constant must cancel. -/
def ConstraintAccepts (f : BooleanFunction n) (g : BooleanFunction (n * n))
    (C : QuadConstraint n) (z : Cube (n + n * n)) : Prop :=
  signBit (g (rightBlock z) * g (C.quad + rightBlock z))
      + signBit (f (leftBlock z) * f (C.lin + leftBlock z)) + C.const = 0

/-- Both reads of the constraint check are right except with probability
`2ε + 2ε'`. -/
theorem prob_constraint_reads (a : Cube n) (b : Cube (n * n)) (C : QuadConstraint n)
    (f : BooleanFunction n) (hf : IsBooleanValued f) {ε : ℝ}
    (hfc : IsClose f (signOf (hadamard a)) ε)
    (g : BooleanFunction (n * n)) (hg : IsBooleanValued g) {ε' : ℝ}
    (hgc : IsClose g (signOf (hadamard b)) ε') :
    1 - (2 * ε + 2 * ε') ≤ Pr[fun z : Cube (n + n * n) =>
      f (leftBlock z) * f (C.lin + leftBlock z) = chi (hadamard a C.lin)
        ∧ g (rightBlock z) * g (C.quad + rightBlock z) = chi (hadamard b C.quad)] := by
  classical
  refine prob_and_ge ?_ ?_
  · have h : Pr[fun z : Cube (n + n * n) =>
        f (leftBlock z) * f (C.lin + leftBlock z) = chi (hadamard a C.lin)]
        = Pr[fun r : Cube n => f r * f (C.lin + r) = chi (hadamard a C.lin)] :=
      prob_leftBlock (fun r : Cube n => f r * f (C.lin + r) = chi (hadamard a C.lin))
    rw [h]
    exact prob_read_ge f hf a hfc C.lin
  · have h : Pr[fun z : Cube (n + n * n) =>
        g (rightBlock z) * g (C.quad + rightBlock z) = chi (hadamard b C.quad)]
        = Pr[fun r : Cube (n * n) => g r * g (C.quad + r) = chi (hadamard b C.quad)] :=
      prob_rightBlock (fun r : Cube (n * n) =>
        g r * g (C.quad + r) = chi (hadamard b C.quad))
    rw [h]
    exact prob_read_ge g hg b hgc C.quad

/-- **The constraint check is decisive.** Its conclusion — that the decoded
tables satisfy the constraint — does not depend on the randomness, so it is
enough that *some* random string both passes the check and has correct reads.
That happens as soon as the check passes more often than the reads fail. -/
theorem checkValue_eq_zero_of_prob (a : Cube n) (b : Cube (n * n)) (C : QuadConstraint n)
    (f : BooleanFunction n) (hf : IsBooleanValued f) {ε : ℝ}
    (hfc : IsClose f (signOf (hadamard a)) ε)
    (g : BooleanFunction (n * n)) (hg : IsBooleanValued g) {ε' : ℝ}
    (hgc : IsClose g (signOf (hadamard b)) ε')
    (hprob : 2 * ε + 2 * ε' < Pr[ConstraintAccepts f g C]) :
    checkValue (hadamard b) (hadamard a) C = 0 := by
  classical
  have hreads := prob_constraint_reads a b C f hf hfc g hg hgc
  have hboth : 0 < Pr[fun z : Cube (n + n * n) => ConstraintAccepts f g C z
      ∧ (f (leftBlock z) * f (C.lin + leftBlock z) = chi (hadamard a C.lin)
        ∧ g (rightBlock z) * g (C.quad + rightBlock z) = chi (hadamard b C.quad))] := by
    have := prob_and_ge (P := ConstraintAccepts f g C)
      (Q := fun z : Cube (n + n * n) =>
        f (leftBlock z) * f (C.lin + leftBlock z) = chi (hadamard a C.lin)
          ∧ g (rightBlock z) * g (C.quad + rightBlock z) = chi (hadamard b C.quad))
      (p := 1 - Pr[ConstraintAccepts f g C]) (q := 2 * ε + 2 * ε')
      (by linarith) hreads
    linarith
  obtain ⟨z, haccept, hleft, hright⟩ := exists_of_prob_pos hboth
  have h : signBit (chi (hadamard b C.quad)) + signBit (chi (hadamard a C.lin))
      + C.const = 0 := by
    rw [← hleft, ← hright]
    exact haccept
  rw [signBit_chi, signBit_chi] at h
  exact h

/-! ### Soundness with nothing assumed about the proof -/

/-- **The Hadamard assignment tester is sound.** Nothing is assumed about the
two tables: linearity is what the BLR test establishes, and the assignment is
what its soundness decodes. A proof passing all three tests often enough
certifies that the constraint is satisfiable.

This is the inner verifier Dinur's alphabet-reduction step composes with: its
proof length and query count do not depend on the outer system at all, only on
the constant-size constraint being checked. -/
theorem exists_sat_of_prob_tester (C : QuadConstraint n)
    (f : BooleanFunction n) (hf : IsBooleanValued f)
    (g : BooleanFunction (n * n)) (hg : IsBooleanValued g) {ε ε' : ℝ}
    (hblrf : blrAcceptProb f ≥ 1 - ε) (hblrg : blrAcceptProb g ≥ 1 - ε')
    (hcons : 3 / 4 + (4 * ε + 2 * ε') < Pr[TesterAccepts f g])
    (hchk : 2 * ε + 2 * ε' < Pr[ConstraintAccepts f g C]) :
    ∃ a : Cube n, C.Sat a := by
  classical
  obtain ⟨a, ha⟩ := exists_assignment_of_blr f hf ε hblrf
  obtain ⟨b, hb⟩ := exists_assignment_of_blr g hg ε' hblrg
  have hfc : IsClose f (signOf (hadamard a)) ε := ha
  have hgc : IsClose g (signOf (hadamard b)) ε' := hb
  exact ⟨a, sat_of_prob_tester a b C f hf hfc g hg hgc hcons
    (checkValue_eq_zero_of_prob a b C f hf hfc g hg hgc hchk)⟩

end Complexity
