/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Aggregate.Geometry.Affine.Lines
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Aggregate.Geometry.Multioutput.Rank.Internal
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Aggregate.Geometry.Multioutput.RestrictionRank.Defs
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.LinearAlgebra.Dimension.Finite
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# Restricting conjunctions before counting nonlinear generators

Process the conjunction gates in program order. While the current flat is larger
than the target, fix one live literal of each conjunction to its controlling value,
so the gate becomes constant and the codimension grows by at most one. Every gate
then stays affine on the flat. Once the target codimension is reached, the remaining
conjunctions become generators: every gate is affine on the flat modulo their span.
Output components that are independent modulo affine functions on the final flat
therefore need one remaining generator each.
-/

@[expose] public section

namespace Algebraic.Aggregate.Geometry

open scoped Classical

variable {n g : ℕ}

private theorem bitValue_xor (a b : Bool) :
    bitValue (a ^^ b) = bitValue a + bitValue b := by
  cases a <;> cases b <;> decide

private theorem bitValue_injective : Function.Injective bitValue := by
  intro a b h
  cases a <;> cases b <;> first | rfl | exact absurd h (by decide)

/-- A Boolean function is affine on a flat exactly when its prime-field values are. -/
theorem affineOn_iff_mem_flatAffineFunctions {S : AffineFlat n}
    {f : (Fin n → Bool) → Bool} :
    AffineOn S f ↔ (fun x => bitValue (f x)) ∈ flatAffineFunctions S := by
  constructor
  · intro h x hx y hy z hz
    change bitValue (f (xorThree x y z)) = bitValue (f x) + bitValue (f y) + bitValue (f z)
    rw [h x hx y hy z hz, bitValue_xor, bitValue_xor]
  · intro h x hx y hy z hz
    apply bitValue_injective
    rw [bitValue_xor, bitValue_xor]
    exact h x hx y hy z hz

/-- Functions affine on a flat remain affine on every smaller flat. -/
theorem flatAffineFunctions_anti {S T : AffineFlat n} (sub : T.carrier ⊆ S.carrier) :
    flatAffineFunctions S ≤ flatAffineFunctions T :=
  fun _ hf x hx y hy z hz => hf x (sub hx) y (sub hy) z (sub hz)

/-- Constant prime-field functions are affine on every flat. -/
theorem const_mem_flatAffineFunctions (S : AffineFlat n) (b : ZMod 2) :
    (fun _ : Fin n → Bool => b) ∈ flatAffineFunctions S := by
  intro _ _ _ _ _ _
  fin_cases b <;> rfl

/-- Primary input bits are affine on every flat. -/
theorem coordinate_mem_flatAffineFunctions (S : AffineFlat n) (i : Fin n) :
    (fun x : Fin n → Bool => bitValue (x i)) ∈ flatAffineFunctions S :=
  affineOn_iff_mem_flatAffineFunctions.mp (affineOn_coordinate i)

/-- Appending a line adds one to the conjunction count exactly for conjunctions. -/
theorem conjunctionCount_gate (p : Program signature n g) (line : Line signature n g) :
    conjunctionCount (p.gate line) =
      conjunctionCount p + if line.op.isConjunction = true then 1 else 0 := by
  simp only [conjunctionCount, Finset.card_filter, Fin.sum_univ_castSucc,
    Program.lines_gate_castSucc, Program.lines_gate_last, Line.mapWires_op]

/-- The restriction process for an actual program. The flat has codimension `d` at most
the target, and restrictions stop only at the target. Each processed conjunction raises
the codimension by at most one, and each later conjunction contributes at most one
dimension to `T`. Modulo `T`, every gate is affine on the flat. -/
theorem exists_restriction_generators (p : Program signature n g) (target : ℕ) :
    ∃ (S : AffineFlat n) (d : ℕ) (T : Submodule (ZMod 2) ((Fin n → Bool) → ZMod 2)),
      2 ^ d * S.carrier.card = 2 ^ n ∧ d ≤ target ∧ (d < target → T = ⊥) ∧
      d + Module.finrank (ZMod 2) T ≤ conjunctionCount p ∧
      ∀ i, (fun x => bitValue (p.gateFunction interpretation i x)) ∈
        flatAffineFunctions S ⊔ T := by
  induction p with
  | empty =>
      refine ⟨AffineFlat.full n, 0, ⊥, by simp, Nat.zero_le _, fun _ => rfl, ?_,
        fun i => Fin.elim0 i⟩
      simp [conjunctionCount]
  | @gate g p line ih =>
      obtain ⟨S, d, T, size, le, stop, count, mem⟩ := ih
      rw [conjunctionCount_gate]
      have old (W : Submodule (ZMod 2) ((Fin n → Bool) → ZMod 2))
          (hW : flatAffineFunctions S ⊔ T ≤ W) (j : Fin g) :
          (fun x => bitValue ((p.gate line).gateFunction interpretation j.castSucc x)) ∈ W := by
        simpa only [Program.gateFunction_gate_castSucc] using hW (mem j)
      rcases line with ⟨op, wires⟩
      cases op with
      | affine r bias coefficient =>
          refine ⟨S, d, T, size, le, stop, by simpa [Op.isConjunction] using count, ?_⟩
          apply gateValues_mem
          · exact fun b => Submodule.mem_sup_left (const_mem_flatAffineFunctions S b)
          · exact fun i => Submodule.mem_sup_left (coordinate_mem_flatAffineFunctions S i)
          · intro i hi
            refine Fin.lastCases ?_ (fun j _ => old _ le_rfl j) i hi
            intro last
            simp [Program.lines_gate_last, Line.mapWires, Op.isConjunction] at last
      | conjunction r polarity negated =>
          simp only [Op.isConjunction, ite_true]
          by_cases reached : d < target
          · obtain rfl := stop reached
            have affine (j : Fin g) : AffineOn S (p.gateFunction interpretation j) :=
              affineOn_iff_mem_flatAffineFunctions.mpr (by simpa using mem j)
            have extend (U : AffineFlat n) (sub : U.carrier ⊆ S.carrier)
                (current : ConstantOn U
                  (lineFunction p ⟨.conjunction r polarity negated, wires⟩)) :
                ∀ i, (fun x => bitValue (Program.gateFunction
                  (p.gate ⟨.conjunction r polarity negated, wires⟩) interpretation i x)) ∈
                  flatAffineFunctions U ⊔ ⊥ := by
              intro i
              refine Fin.lastCases ?_ (fun j => old _ ?_ j) i
              · rw [Program.gateFunction_gate_last]
                exact Submodule.mem_sup_left
                  (affineOn_iff_mem_flatAffineFunctions.mp current.affine)
              · simpa only [sup_bot_eq] using flatAffineFunctions_anti sub
            by_cases constant : ConstantOn S
                (lineFunction p ⟨.conjunction r polarity negated, wires⟩)
            · refine ⟨S, d, ⊥, size, le, fun _ => rfl, ?_, extend S subset_rfl constant⟩
              simp only [finrank_bot, add_zero] at count ⊢
              omega
            · have live : ∃ slot,
                  ¬ ConstantOn S (p.wireFunction interpretation (wires slot)) := by
                by_contra absent
                push Not at absent
                exact constant (constantOn_line_of_slots p _ absent)
              obtain ⟨slot, live⟩ := live
              obtain ⟨U, sub, fixed, half⟩ :=
                (affineOn_wire p affine (wires slot)).exists_half live (!(polarity slot))
              refine ⟨U, d + 1, ⊥, ?_, by omega, fun _ => rfl, ?_, ?_⟩
              · rw [Nat.pow_succ, Nat.mul_assoc, half, size]
              · simp only [finrank_bot, add_zero] at count ⊢
                omega
              · exact extend U sub (constantOn_conjunction p polarity negated wires slot fixed)
          · let new : (Fin n → Bool) → ZMod 2 := fun x => bitValue (Program.gateFunction
              (p.gate ⟨.conjunction r polarity negated, wires⟩) interpretation (Fin.last g) x)
            have dimension : Module.finrank (ZMod 2) ↥(T ⊔ Submodule.span (ZMod 2) {new}) ≤
                Module.finrank (ZMod 2) T + 1 := by
              refine (Submodule.finrank_add_le_finrank_add_finrank _ _).trans ?_
              have := finrank_span_le_card (R := ZMod 2) ({new} : Set ((Fin n → Bool) → ZMod 2))
              simp only [Set.toFinset_singleton, Finset.card_singleton] at this
              omega
            refine ⟨S, d, T ⊔ Submodule.span (ZMod 2) {new}, size, le,
              fun h => (reached h).elim, by omega, ?_⟩
            intro i
            refine Fin.lastCases ?_ (fun j => old _ (sup_le_sup_left le_sup_left _) j) i
            exact Submodule.mem_sup_right
              (Submodule.mem_sup_right (Submodule.subset_span (Set.mem_singleton new)))

/-- The restriction–rank inequality: output components independent modulo affine
functions on every flat of `2^D` points force `m + n - D` conjunction gates. -/
theorem output_add_input_le_of_nonaffineOnFlats {m D : ℕ} (c : Circuit signature n m)
    (rigid : NonaffineOnFlats (c.eval interpretation) D) (outputs : 0 < m)
    (dimension : D ≤ n) : m + n ≤ conjunctionCount c.program + D := by
  obtain ⟨S, d, T, size, le, stop, count, mem⟩ :=
    exists_restriction_generators c.program (n - D)
  have large : 2 ^ D ≤ S.carrier.card := by
    have split : 2 ^ n = 2 ^ d * 2 ^ (n - d) := by
      rw [← Nat.pow_add]
      congr 1
      omega
    have card : S.carrier.card = 2 ^ (n - d) :=
      Nat.eq_of_mul_eq_mul_left (Nat.two_pow_pos d) (size.trans split)
    rw [card]
    exact Nat.pow_le_pow_right (by decide) (by omega)
  have output (i : Fin m) :
      (fun x => bitValue (c.eval interpretation x i)) ∈ flatAffineFunctions S ⊔ T := by
    change (fun x => bitValue
      (c.program.wireFunction interpretation (c.outputs i) x)) ∈ flatAffineFunctions S ⊔ T
    cases c.outputs i with
    | input j => exact Submodule.mem_sup_left (coordinate_mem_flatAffineFunctions S j)
    | gate j => exact mem j
  let q := (flatAffineFunctions S).mkQ
  let f := q.comp (Fintype.linearCombination (ZMod 2)
    (fun i : Fin m => fun x => bitValue (c.eval interpretation x i)))
  have injective : Function.Injective f := by
    apply LinearMap.ker_eq_bot.mp
    apply LinearMap.ker_eq_bot'.mpr
    intro w hw
    apply rigid S large w
    change q (∑ i, w i • fun x => bitValue (c.eval interpretation x i)) = 0 at hw
    have member := (Submodule.Quotient.mk_eq_zero (flatAffineFunctions S)).mp hw
    convert member using 1
    ext x
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  have range : LinearMap.range f ≤ T.map q := by
    rintro _ ⟨w, rfl⟩
    have sum : (∑ i, w i • fun x => bitValue (c.eval interpretation x i)) ∈
        flatAffineFunctions S ⊔ T :=
      Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (output i)
    obtain ⟨a, ha, t, ht, eq⟩ := Submodule.mem_sup.mp sum
    refine ⟨t, ht, ?_⟩
    change q t = q (∑ i, w i • fun x => bitValue (c.eval interpretation x i))
    have killed : q a = 0 := (Submodule.Quotient.mk_eq_zero _).mpr ha
    rw [← eq, map_add, killed, zero_add]
  have rank : m ≤ Module.finrank (ZMod 2) T :=
    calc
      m = Module.finrank (ZMod 2) (LinearMap.range f) := by
        rw [LinearMap.finrank_range_of_inj injective]
        simp
      _ ≤ Module.finrank (ZMod 2) (T.map q) := Submodule.finrank_mono range
      _ ≤ Module.finrank (ZMod 2) T := Submodule.finrank_map_le q T
  have reached : d = n - D := by
    by_contra different
    rw [stop (by omega), finrank_bot] at rank
    omega
  omega

end Algebraic.Aggregate.Geometry
