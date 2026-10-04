/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Aggregate.Circuit.Internal
public import Complexitylib.Algebraic.LowerBound.Cutwidth.SingleCut.Defs

/-!
# Aggregate keys and mixing across component unions

The ordinary graph omits special gates and their incident edges. Equal special-output
guesses fix every omitted signal. A single vector of left-side partial aggregates
then suffices for exact mixing, using only the commutative-monoid laws.
-/

@[expose] public section

namespace Algebraic.Aggregate

variable {J : Type} {State : J → Type} {n g : ℕ}

/-- Whether a signal is the output of a special gate. Inputs are ordinary signals. -/
def specialWire (p : Program (signature State) n g) : Wire n g → Bool
  | .input _ => false
  | .gate gate => (p.lines gate).op.isSpecial

/-- A union of components of the graph of ordinary-to-ordinary slots.
Special-to-ordinary slots are known constants once the special outputs are guessed. -/
def ClosedSet (p : Program (signature State) n g) (S : Finset (Wire n g)) : Prop :=
  ∀ gate, (p.lines gate).op.isSpecial = false →
    ∀ slot, specialWire p ((p.lines gate).wires slot) = false →
      ((p.lines gate).wires slot ∈ S ↔ Wire.gate gate ∈ S)

/-- Erasure deletes exactly the slots whose target gate is special. -/
theorem reads_erase_iff (p : Program (signature State) n g) (a : Guess p)
    (gate : Fin g) (wire : Wire n g) :
    (erase p a).Reads gate wire ↔ (p.lines gate).op.isSpecial = false ∧ p.Reads gate wire := by
  unfold Cslib.Circuits.Program.Reads
  rw [erase, lines_eraseWith]
  generalize p.lines gate = line
  rcases line with ⟨op, wires⟩
  cases op <;> simp [eraseLine, Op.isSpecial]

/-- The erased graph is independent of the values of the guessed bits. -/
theorem reads_erase_iff_reads_erase (p : Program (signature State) n g) (a b : Guess p)
    (gate : Fin g) (wire : Wire n g) :
    (erase p a).Reads gate wire ↔ (erase p b).Reads gate wire := by
  rw [reads_erase_iff, reads_erase_iff]

/-- Closure for all slots of an erased program implies ordinary component closure. -/
theorem closedSet_of_erase_closed (p : Program (signature State) n g) (a : Guess p)
    (S : Finset (Wire n g))
    (closed : ∀ gate wire, (erase p a).Reads gate wire →
      (wire ∈ S ↔ Wire.gate gate ∈ S)) : ClosedSet p S := by
  intro gate hs slot _
  exact closed gate _ ((reads_erase_iff p a gate _).mpr ⟨hs, slot, rfl⟩)

/-- Multiply the contributions whose source signals lie in `S`, counting repeated slots. -/
def lineAggregate [∀ j, CommMonoid (State j)] (line : Line (signature State) n g)
    (S : Finset (Wire n g)) (values : Wire n g → Bool) : line.op.Register :=
  ∏ slot ∈ Finset.univ.filter (fun slot => line.wires slot ∈ S),
    line.op.slotContribution slot (values (line.wires slot))

/-- The partial aggregate vector associated to actual signal values on `S`. -/
def partialAggregate [∀ j, CommMonoid (State j)]
    (p : Program (signature State) n g) (S : Finset (Wire n g))
    (input : Fin n → Bool) : Registers p :=
  fun gate => lineAggregate (p.lines gate) S (p.trace interpretation input)

/-- The exact rectangle key: guessed special outputs and one partial aggregate vector. -/
def componentKey [∀ j, CommMonoid (State j)]
    (p : Program (signature State) n g) (S : Finset (Wire n g)) (input : Fin n → Bool) :
    Guess p × Registers p := (actualGuess p input, partialAggregate p S input)

theorem lineAggregate_partition [∀ j, CommMonoid (State j)]
    (line : Line (signature State) n g) (S : Finset (Wire n g))
    (values : Wire n g → Bool) :
    lineAggregate line S values * lineAggregate line Sᶜ values =
      lineAggregate line Finset.univ values := by
  simpa [lineAggregate] using Finset.prod_filter_mul_prod_filter_not Finset.univ
    (fun slot => line.wires slot ∈ S)
    (fun slot => line.op.slotContribution slot (values (line.wires slot)))

theorem lineAggregate_mix [∀ j, CommMonoid (State j)]
    (line : Line (signature State) n g) (S : Finset (Wire n g))
    (x y : Wire n g → Bool) :
    lineAggregate line Finset.univ (fun w => if w ∈ S then x w else y w) =
      lineAggregate line S x * lineAggregate line Sᶜ y := by
  rw [← lineAggregate_partition line S]
  congr 1
  · apply Finset.prod_congr rfl
    intro slot hslot
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hslot
    simp only [hslot, ite_true]
  · apply Finset.prod_congr rfl
    intro slot hslot
    simp only [Finset.mem_filter, Finset.mem_univ, Finset.mem_compl, true_and] at hslot
    simp only [hslot, ite_false]

theorem line_eval_eq_of_aggregate_eq [∀ j, CommMonoid (State j)]
    (line : Line (signature State) n g) (hs : line.op.isSpecial = true)
    (x y : Wire n g → Bool)
    (h : lineAggregate line Finset.univ x = lineAggregate line Finset.univ y) :
    interpretation line.op (x ∘ line.wires) = interpretation line.op (y ∘ line.wires) := by
  rcases line with ⟨op, wires⟩
  cases op with
  | binary => simp [Op.isSpecial] at hs
  | special kind arity contribution readout =>
      apply congrArg readout
      simpa [lineAggregate, Op.slotContribution] using h

/-- Equal component keys allow the two evaluations to be pasted along a closed set. -/
theorem trace_mix_of_componentKey_eq [∀ j, CommMonoid (State j)]
    (p : Program (signature State) n g) (S : Finset (Wire n g))
    (closed : ClosedSet p S) (x y : Fin n → Bool)
    (key : componentKey p S x = componentKey p S y) (wire : Wire n g) :
    p.trace interpretation (Cutwidth.SingleCut.mix S x y) wire =
      if wire ∈ S then p.trace interpretation x wire else p.trace interpretation y wire := by
  have guesses := congrArg Prod.fst key
  have aggregates := congrArg Prod.snd key
  have special (gate : Fin g) (hs : (p.lines gate).op.isSpecial = true) :
      p.trace interpretation x (.gate gate) = p.trace interpretation y (.gate gate) :=
    congrFun guesses ⟨gate, hs⟩
  let z := fun w => if w ∈ S then p.trace interpretation x w else p.trace interpretation y w
  have zspecial (w : Wire n g) (hs : specialWire p w = true) :
      p.trace interpretation x w = p.trace interpretation y w := by
    cases w with
    | input => simp [specialWire] at hs
    | gate gate => exact special gate hs
  have hz : Wire.elim (Cutwidth.SingleCut.mix S x y) (fun gate => z (.gate gate)) = z := by
    funext w
    cases w <;> rfl
  have equations : ∀ gate,
      (p.lines gate).eval interpretation (Cutwidth.SingleCut.mix S x y)
        (fun gate => z (.gate gate)) = z (.gate gate) := by
    intro gate
    unfold Line.eval
    rw [hz]
    by_cases hs : (p.lines gate).op.isSpecial = true
    · have ha : lineAggregate (p.lines gate) Finset.univ z =
          lineAggregate (p.lines gate) Finset.univ (p.trace interpretation y) := by
        rw [lineAggregate_mix, show lineAggregate (p.lines gate) S
            (p.trace interpretation x) = lineAggregate (p.lines gate) S
              (p.trace interpretation y) from congrFun aggregates ⟨gate, hs⟩,
          lineAggregate_partition]
      rw [line_eval_eq_of_aggregate_eq (p.lines gate) hs z (p.trace interpretation y) ha]
      change (p.lines gate).eval interpretation y (p.eval interpretation y) = _
      rw [Program.lines_eval]
      change p.trace interpretation y (.gate gate) = _
      simp only [z, special gate hs, ite_self]
    · have hs' : (p.lines gate).op.isSpecial = false := by
        cases h : (p.lines gate).op.isSpecial <;> simp_all
      have arg (slot) : z ((p.lines gate).wires slot) =
          if Wire.gate gate ∈ S then p.trace interpretation x ((p.lines gate).wires slot)
          else p.trace interpretation y ((p.lines gate).wires slot) := by
        by_cases hw : specialWire p ((p.lines gate).wires slot) = true
        · simp [z, zspecial _ hw]
        · have hw' : specialWire p ((p.lines gate).wires slot) = false := by
            cases h : specialWire p ((p.lines gate).wires slot) <;> simp_all
          simp only [z, closed gate hs' slot hw']
      by_cases hg : Wire.gate gate ∈ S
      · simp only [z, hg, ite_true]
        rw [Program.trace_gateWire, Program.gateFunction_apply,
          ← Program.lines_eval p interpretation x gate]
        unfold Line.eval
        congr 1
        funext slot
        simpa only [Function.comp_apply, hg, ite_true, z, Program.trace] using arg slot
      · simp only [z, hg, ite_false]
        rw [Program.trace_gateWire, Program.gateFunction_apply,
          ← Program.lines_eval p interpretation y gate]
        unfold Line.eval
        congr 1
        funext slot
        simpa only [Function.comp_apply, hg, ite_false, z, Program.trace] using arg slot
  have heval := Program.eq_eval_of_forall_lines_eval p interpretation
    (Cutwidth.SingleCut.mix S x y) (fun gate => z (.gate gate)) equations
  cases wire with
  | input => rfl
  | gate gate => exact (congrFun heval gate).symm

/-- Accepted inputs with the same component key mix to another accepted input. -/
theorem accepts_mix_of_componentKey_eq [∀ j, CommMonoid (State j)]
    (p : Program (signature State) n g) (S : Finset (Wire n g))
    (closed : ClosedSet p S) (out : Wire n g) (x y : Fin n → Bool)
    (hx : p.trace interpretation x out = true) (hy : p.trace interpretation y out = true)
    (key : componentKey p S x = componentKey p S y) :
    p.trace interpretation (Cutwidth.SingleCut.mix S x y) out = true := by
  rw [trace_mix_of_componentKey_eq p S closed x y key, hx, hy, ite_self]

end Algebraic.Aggregate
