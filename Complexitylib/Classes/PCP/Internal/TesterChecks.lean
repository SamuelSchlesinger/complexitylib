/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/
module
public import Complexitylib.Classes.PCP.Internal.HadamardTester
public import Complexitylib.Classes.PCP.Internal.Arithmetize

/-!
# The remaining checks of the assignment tester

`HadamardTester` proves the linearity and consistency checks. Two more are
needed for the tester to plug into Dinur's composition, and both are analysed
here on raw tables, over bundled randomness, in the same style.

* **The constraint check on a system.** The constraint is a *system* of
  quadratic equations (the one-hot arithmetization of `Arithmetize`), checked
  by one random linear combination. Passing on more than half of the
  coefficient vectors — after paying for the reads — forces every equation to
  hold on the decoded tables.

* **The input check, one coordinate at a time.** The tester is handed its
  input as a table it may read at a single random coordinate, and compares that
  bit with the corresponding coordinate of its decoded assignment, obtained by
  self-correction at a basis vector. Passing often means the input table is
  *close* to the decoded assignment's input part — not equal, which a single
  read could never certify, but close enough that, when the input is supposed
  to be a Hadamard codeword, it decodes uniquely.

The last point is what makes the composition work with constantly many
queries: the outer graph's labels are handed to the tester as Hadamard
codewords, and a wrong label is far from every right one.

## Main results

- `Complexity.forall_checkValue_of_prob_combined` — the random-combination
  constraint check
- `Complexity.prob_coord_eq_ge` — the single-coordinate input check
- `Complexity.decodeLabel_eq` — a table close to a codeword decodes to it
-/

@[expose] public section

namespace Complexity

open BooleanAnalysis

variable {n : ℕ}

/-! ### The constraint check on a system -/

/-- **The random-combination constraint check.** Reading the combined constraint
off the raw tables passes often enough only if every constraint of the system
holds on the decoded tables. The coefficient vector is the first block, the
correction strings the second. -/
theorem forall_checkValue_of_prob_combined {J : ℕ} (a : Cube n) (b : Cube (n * n))
    (C : Fin J → QuadConstraint n)
    (f : BooleanFunction n) (hf : IsBooleanValued f) {ε : ℝ}
    (hfc : IsClose f (signOf (hadamard a)) ε)
    (g : BooleanFunction (n * n)) (hg : IsBooleanValued g) {ε' : ℝ}
    (hgc : IsClose g (signOf (hadamard b)) ε')
    (haccept : 1 / 2 + (2 * ε + 2 * ε') < Pr[fun z : Cube (J + (n + n * n)) =>
      ConstraintAccepts f g (QuadConstraint.combine C (leftBlock z)) (rightBlock z)]) :
    ∀ j, checkValue (hadamard b) (hadamard a) (C j) = 0 := by
  classical
  have hgood : 1 - (2 * ε + 2 * ε') ≤ Pr[fun z : Cube (J + (n + n * n)) =>
      f (leftBlock (rightBlock z))
          * f ((QuadConstraint.combine C (leftBlock z)).lin + leftBlock (rightBlock z))
          = chi (hadamard a (QuadConstraint.combine C (leftBlock z)).lin)
        ∧ g (rightBlock (rightBlock z))
          * g ((QuadConstraint.combine C (leftBlock z)).quad + rightBlock (rightBlock z))
          = chi (hadamard b (QuadConstraint.combine C (leftBlock z)).quad)] :=
    prob_blocks_ge (fun c w =>
      f (leftBlock w) * f ((QuadConstraint.combine C c).lin + leftBlock w)
          = chi (hadamard a (QuadConstraint.combine C c).lin)
        ∧ g (rightBlock w) * g ((QuadConstraint.combine C c).quad + rightBlock w)
          = chi (hadamard b (QuadConstraint.combine C c).quad)) _
      fun c => prob_constraint_reads a b (QuadConstraint.combine C c) f hf hfc g hg hgc
  have htrans := prob_le_of_imp_of_good
    (E := fun z : Cube (J + (n + n * n)) =>
      ConstraintAccepts f g (QuadConstraint.combine C (leftBlock z)) (rightBlock z))
    (F := fun z : Cube (J + (n + n * n)) =>
      checkValue (hadamard b) (hadamard a) (QuadConstraint.combine C (leftBlock z)) = 0)
    (A := fun z : Cube (J + (n + n * n)) =>
      f (leftBlock (rightBlock z))
          * f ((QuadConstraint.combine C (leftBlock z)).lin + leftBlock (rightBlock z))
          = chi (hadamard a (QuadConstraint.combine C (leftBlock z)).lin)
        ∧ g (rightBlock (rightBlock z))
          * g ((QuadConstraint.combine C (leftBlock z)).quad + rightBlock (rightBlock z))
          = chi (hadamard b (QuadConstraint.combine C (leftBlock z)).quad))
    fun z hE hA => by
      have h : signBit (chi (hadamard b (QuadConstraint.combine C (leftBlock z)).quad))
          + signBit (chi (hadamard a (QuadConstraint.combine C (leftBlock z)).lin))
          + (QuadConstraint.combine C (leftBlock z)).const = 0 := by
        rw [← hA.1, ← hA.2]
        exact hE
      rw [signBit_chi, signBit_chi] at h
      exact h
  have hmarg : Pr[fun z : Cube (J + (n + n * n)) =>
      checkValue (hadamard b) (hadamard a) (QuadConstraint.combine C (leftBlock z)) = 0]
      = Pr[fun c : Cube J => checkValue (hadamard b) (hadamard a)
        (QuadConstraint.combine C c) = 0] :=
    prob_leftBlock (fun c : Cube J =>
      checkValue (hadamard b) (hadamard a) (QuadConstraint.combine C c) = 0)
  rw [hmarg] at htrans
  exact forall_checkValue_of_prob a b C (by linarith)

/-! ### The input check, one coordinate at a time -/

/-- **The single-coordinate input check**, on the raw table: a random
coordinate `r` (first block) of the input table `w` is compared with the
decoded assignment's bit at variable `idx r`, read by self-correction at the
basis vector (correction string: second block). -/
def CoordAccepts {m : ℕ} (f : BooleanFunction n) (w : Cube m → ZMod 2) (idx : Cube m → Fin n)
    (z : Cube (m + n)) : Prop :=
  signBit (f (rightBlock z) * f (basisVec (idx (leftBlock z)) + rightBlock z))
    = w (leftBlock z)

/-- **Passing the coordinate check means agreeing on most coordinates.** -/
theorem prob_coord_eq_ge {m : ℕ} (a : Cube n) (f : BooleanFunction n) (hf : IsBooleanValued f)
    {ε : ℝ} (hfc : IsClose f (signOf (hadamard a)) ε)
    (w : Cube m → ZMod 2) (idx : Cube m → Fin n) :
    Pr[CoordAccepts f w idx] - 2 * ε ≤ Pr[fun r : Cube m => a (idx r) = w r] := by
  classical
  have hgood : 1 - 2 * ε ≤ Pr[fun z : Cube (m + n) =>
      f (rightBlock z) * f (basisVec (idx (leftBlock z)) + rightBlock z)
        = chi (hadamard a (basisVec (idx (leftBlock z))))] :=
    prob_blocks_ge (fun r c =>
      f c * f (basisVec (idx r) + c) = chi (hadamard a (basisVec (idx r)))) _
      fun r => prob_read_ge f hf a hfc (basisVec (idx r))
  have htrans := prob_le_of_imp_of_good (E := CoordAccepts f w idx)
    (F := fun z : Cube (m + n) => a (idx (leftBlock z)) = w (leftBlock z))
    (A := fun z : Cube (m + n) =>
      f (rightBlock z) * f (basisVec (idx (leftBlock z)) + rightBlock z)
        = chi (hadamard a (basisVec (idx (leftBlock z)))))
    fun z hE hA => by
      have h : signBit (chi (hadamard a (basisVec (idx (leftBlock z))))) = w (leftBlock z) := by
        rw [← hA]
        exact hE
      rw [signBit_chi, hadamard_basisVec] at h
      exact h
  have hmarg : Pr[fun z : Cube (m + n) => a (idx (leftBlock z)) = w (leftBlock z)]
      = Pr[fun r : Cube m => a (idx r) = w r] :=
    prob_leftBlock (fun r : Cube m => a (idx r) = w r)
  rw [hmarg] at htrans
  linarith

/-- The honest table passes the coordinate check everywhere, when the input
table is the decoded assignment's input part. -/
theorem coordAccepts_of_honest {m : ℕ} (a : Cube n) (idx : Cube m → Fin n) (z : Cube (m + n)) :
    CoordAccepts (signOf (hadamard a)) (fun r => a (idx r)) idx z := by
  show signBit (signOf (hadamard a) (rightBlock z)
    * signOf (hadamard a) (basisVec (idx (leftBlock z)) + rightBlock z)) = _
  rw [corrected_read_honest, signBit_chi, hadamard_basisVec]

/-! ### Decoding a label from a table -/

/-- The distance between two bit tables: the fraction of coordinates where they
differ. -/
noncomputable def bitDist {m : ℕ} (s t : Cube m → ZMod 2) : ℝ := Pr[fun r => s r ≠ t r]

theorem bitDist_eq_hammingDist {m : ℕ} (s t : Cube m → ZMod 2) :
    bitDist s t = hammingDist (signOf s) (signOf t) := by
  unfold bitDist hammingDist
  congr 1
  funext r
  show (s r ≠ t r) = (chi (s r) ≠ chi (t r))
  have hinj : ∀ u v : ZMod 2, chi u = chi v ↔ u = v := by
    intro u v
    constructor
    · intro h
      by_contra hne
      have h' := signBit_chi u
      rw [h, signBit_chi] at h'
      exact hne h'.symm
    · intro h
      rw [h]
  rw [ne_eq, ne_eq, hinj]

theorem bitDist_comm {m : ℕ} (s t : Cube m → ZMod 2) : bitDist s t = bitDist t s := by
  rw [bitDist_eq_hammingDist, bitDist_eq_hammingDist, hammingDist_comm]

theorem bitDist_triangle {m : ℕ} (s t u : Cube m → ZMod 2) :
    bitDist s u ≤ bitDist s t + bitDist t u := by
  rw [bitDist_eq_hammingDist, bitDist_eq_hammingDist, bitDist_eq_hammingDist]
  exact hammingDist_triangle _ _ _

theorem bitDist_eq_one_sub {m : ℕ} (s t : Cube m → ZMod 2) :
    bitDist s t = 1 - Pr[fun r => s r = t r] := by
  have := BooleanAnalysis.Internal.prob_compl (fun r : Cube m => s r = t r)
  unfold bitDist
  linarith

/-- **Distinct codewords are far apart**: at distance exactly one half. -/
theorem bitDist_hadamard {m : ℕ} (u v : Cube m) (h : u ≠ v) :
    bitDist (hadamard u) (hadamard v) = 1 / 2 := by
  have hne : u + v ≠ 0 := by
    intro h0
    apply h
    funext i
    have hi := congrFun h0 i
    rcases (by decide : ∀ x y : ZMod 2, x + y = 0 → x = y) (u i) (v i) hi with h'
    exact h'
  have hhalf := prob_hadamard_ne_zero (u + v) hne
  unfold bitDist
  rw [← hhalf]
  congr 1
  funext r
  rw [hadamard_add]
  have hiff : ∀ x y : ZMod 2, (x ≠ y) ↔ (x + y ≠ 0) := by decide
  exact propext (hiff _ _)

/-- Decoding: the label whose codeword is within a quarter of the table, if
any; an arbitrary label otherwise. -/
noncomputable def decodeLabel {m : ℕ} {β : Type} [Nonempty β] (enc : β → Cube m)
    (t : Cube m → ZMod 2) : β :=
  open Classical in
  if h : ∃ σ : β, bitDist t (hadamard (enc σ)) < 1 / 4 then Classical.choose h
  else Classical.arbitrary β

/-- **A table close to a codeword decodes to its label.** -/
theorem decodeLabel_eq {m : ℕ} {β : Type} [Nonempty β] (enc : β → Cube m)
    (henc : Function.Injective enc) (t : Cube m → ZMod 2) (σ : β)
    (h : bitDist t (hadamard (enc σ)) < 1 / 4) : decodeLabel enc t = σ := by
  classical
  have hex : ∃ σ : β, bitDist t (hadamard (enc σ)) < 1 / 4 := ⟨σ, h⟩
  rw [decodeLabel, dite_eq_left hex]
  have hspec := Classical.choose_spec hex
  by_contra hne
  have hne' : enc (Classical.choose hex) ≠ enc σ := fun heq => hne (henc heq)
  have hfar := bitDist_hadamard _ _ hne'
  have htri := bitDist_triangle (hadamard (enc (Classical.choose hex))) t (hadamard (enc σ))
  rw [bitDist_comm _ t] at htri
  linarith

end Complexity
