/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Circuits.Encoding.Fragment.Defs
public import Complexitylib.Models.TuringMachine
public import Mathlib.Data.Fintype.Sum
public import Mathlib.Logic.Equiv.Fin.Basic
public import Mathlib.Tactic.DeriveFintype

/-!
# Circuit layouts for bounded Turing-machine traces

This file defines the wire layout used to unroll a bounded nondeterministic
Turing-machine trace. A configuration is represented by one-hot atoms for its
state, tape-head positions, and tape-cell symbols. Head positions range over
`Fin (T + 1)` and cells over `Fin (T + 2)`; the extra cell keeps output cell
one present even at the zero-step horizon.

The primary-input layout is independent of the configuration layout. This
lets later clients place random choices, data, and auxiliary inputs wherever
they choose. `prefixInputWires` supplies the canonical choices-first order.
-/


@[expose] public section

namespace Complexity

namespace CircuitUnrolling

/-- A named tape of a machine with `k` work tapes. -/
inductive TapeSlot (k : ℕ) where
  /-- The read-only input tape. -/
  | input
  /-- One of the machine's work tapes. -/
  | work (i : Fin k)
  /-- The output tape. -/
  | output
  deriving DecidableEq, Fintype

/-- A named tape on which a machine transition may write. -/
inductive WritableSlot (k : ℕ) where
  /-- One of the machine's work tapes. -/
  | work (i : Fin k)
  /-- The output tape. -/
  | output
  deriving DecidableEq, Fintype

namespace WritableSlot

/-- The zero-based position of a writable tape in work/output order. -/
def index : WritableSlot k → Fin (k + 1)
  | .work i => ⟨i.val, by omega⟩
  | .output => ⟨k, by omega⟩

/-- Regard a writable work/output slot as a general named tape slot. -/
def toTapeSlot : WritableSlot k → TapeSlot k
  | .work i => .work i
  | .output => .output

end WritableSlot

namespace TapeSlot

/-- The zero-based position of a named tape in input/work/output order. -/
def index : TapeSlot k → Fin (k + 2)
  | .input => ⟨0, by omega⟩
  | .work i => ⟨i.val + 1, by omega⟩
  | .output => ⟨k + 1, by omega⟩

/-- Select a named tape from a machine configuration. -/
def get (c : Cfg k Q) : TapeSlot k → Tape
  | .input => c.input
  | .work i => c.work i
  | .output => c.output

end TapeSlot

/-- The zero-based index of an alphabet symbol in zero/one/blank/start order. -/
def symbolIndex : Γ → Fin 4
  | .zero => ⟨0, by omega⟩
  | .one => ⟨1, by omega⟩
  | .blank => ⟨2, by omega⟩
  | .start => ⟨3, by omega⟩

/-- A one-hot proposition about a bounded machine configuration. -/
inductive ConfigAtom (tm : NTM k) (T : ℕ) where
  /-- The machine is in the indicated state. -/
  | state (q : tm.Q)
  /-- A named tape's head is at the indicated position. -/
  | head (tape : TapeSlot k) (position : Fin (T + 1))
  /-- A named tape's cell contains the indicated symbol. -/
  | cell (tape : TapeSlot k) (position : Fin (T + 2)) (symbol : Γ)
  deriving DecidableEq

/-- Number of Boolean wires in one bounded configuration block. -/
def configWidth (tm : NTM k) (T : ℕ) : ℕ :=
  Fintype.card tm.Q + (k + 2) * (T + 1) + 4 * (k + 2) * (T + 2)

/-- State/head/cell sum representation used to construct the explicit layout. -/
def configAtomSumEquiv (tm : NTM k) (T : ℕ) :
    ConfigAtom tm T ≃
      tm.Q ⊕ ((TapeSlot k × Fin (T + 1)) ⊕ ((TapeSlot k × Fin (T + 2)) × Γ)) where
  toFun
    | .state q => .inl q
    | .head tape position => .inr (.inl (tape, position))
    | .cell tape position symbol => .inr (.inr ((tape, position), symbol))
  invFun
    | .inl q => .state q
    | .inr (.inl (tape, position)) => .head tape position
    | .inr (.inr ((tape, position), symbol)) => .cell tape position symbol
  left_inv atom := by cases atom <;> rfl
  right_inv atom := by rcases atom with q | head | cell <;> rfl

private theorem TapeSlot.index_injective : Function.Injective (@TapeSlot.index k) := by
  intro first second h
  cases first with
  | input =>
      cases second <;> simp_all [TapeSlot.index]
  | work i =>
      cases second with
      | input => simp [TapeSlot.index] at h
      | work j =>
          congr 1
          apply Fin.ext
          simpa [TapeSlot.index] using congrArg Fin.val h
      | output =>
          have hi := i.isLt
          simp [TapeSlot.index] at h
          omega
  | output =>
      cases second with
      | input => simp [TapeSlot.index] at h
      | work j =>
          have hj := j.isLt
          simp [TapeSlot.index] at h
          omega
      | output => rfl

private theorem TapeSlot.index_surjective : Function.Surjective (@TapeSlot.index k) := by
  intro i
  by_cases hzero : i.val = 0
  · refine ⟨.input, Fin.ext ?_⟩
    simp [TapeSlot.index, hzero]
  by_cases hlast : i.val = k + 1
  · refine ⟨.output, Fin.ext ?_⟩
    simp [TapeSlot.index, hlast]
  · have hwork : i.val - 1 < k := by omega
    refine ⟨.work ⟨i.val - 1, hwork⟩, Fin.ext ?_⟩
    simp only [TapeSlot.index]
    omega

/-- Named tapes are explicitly equivalent to their input/work/output indices. -/
noncomputable def tapeSlotEquiv (k : ℕ) : TapeSlot k ≃ Fin (k + 2) :=
  Equiv.ofBijective TapeSlot.index
    ⟨by exact TapeSlot.index_injective, by exact TapeSlot.index_surjective⟩

private theorem symbolIndex_injective : Function.Injective symbolIndex := by
  intro first second h
  cases first <;> cases second <;> simp_all [symbolIndex]

private theorem symbolIndex_surjective : Function.Surjective symbolIndex := by
  decide

/-- Alphabet symbols are explicitly equivalent to their four layout indices. -/
noncomputable def symbolEquiv : Γ ≃ Fin 4 :=
  Equiv.ofBijective symbolIndex
    ⟨by exact symbolIndex_injective, by exact symbolIndex_surjective⟩

/-- Tape-head atoms are explicitly equivalent to their contiguous layout indices. -/
noncomputable def headAtomEquiv (k T : ℕ) :
    TapeSlot k × Fin (T + 1) ≃ Fin ((k + 2) * (T + 1)) :=
  (Equiv.prodCongr (tapeSlotEquiv k) (Equiv.refl _)).trans finProdFinEquiv

/-- Tape-cell atoms are explicitly equivalent to their contiguous layout indices. -/
noncomputable def cellAtomEquiv (k T : ℕ) :
    (TapeSlot k × Fin (T + 2)) × Γ ≃ Fin (4 * (k + 2) * (T + 2)) :=
  ((Equiv.prodCongr
      ((Equiv.prodCongr (tapeSlotEquiv k) (Equiv.refl _)).trans finProdFinEquiv)
      symbolEquiv).trans
        finProdFinEquiv).trans
    (finCongr (by ac_rfl))

/-- Explicit equivalence between configuration atoms and their block indices. -/
noncomputable def configAtomEquiv (tm : NTM k) (T : ℕ) :
    ConfigAtom tm T ≃ Fin (configWidth tm T) :=
  (configAtomSumEquiv tm T).trans <|
    (Equiv.sumCongr (Fintype.equivFin tm.Q)
      (Equiv.sumCongr (headAtomEquiv k T) (cellAtomEquiv k T))).trans <|
      (Equiv.sumCongr (Equiv.refl _) finSumFinEquiv).trans <|
        finSumFinEquiv.trans <|
          finCongr (by simp [configWidth, Nat.add_assoc])

/-- Finite enumeration of configuration atoms in explicit wire order. -/
noncomputable instance (tm : NTM k) (T : ℕ) : Fintype (ConfigAtom tm T) :=
  Fintype.ofEquiv (Fin (configWidth tm T)) (configAtomEquiv tm T).symm

/-- Zero-based index of a machine state in the fixed finite-state ordering. -/
noncomputable def stateIndex (tm : NTM k) (q : tm.Q) : ℕ :=
  (Fintype.equivFin tm.Q q).val

/-- Zero-based index of an atom within one configuration block. -/
noncomputable def configIndex (tm : NTM k) (T : ℕ) : ConfigAtom tm T → ℕ
  | .state q => stateIndex tm q
  | .head tape position =>
      Fintype.card tm.Q + tape.index.val * (T + 1) + position.val
  | .cell tape position symbol =>
      Fintype.card tm.Q + (k + 2) * (T + 1) +
        (tape.index.val * (T + 2) + position.val) * 4 + symbolIndex symbol

private theorem configIndex_eq_equivVal (tm : NTM k) (T : ℕ)
    (atom : ConfigAtom tm T) :
    configIndex tm T atom = (configAtomEquiv tm T atom).val := by
  cases atom with
  | state q => rfl
  | head tape position =>
      have htape : (tapeSlotEquiv k tape).val = tape.index.val := rfl
      simp [configIndex, configAtomEquiv, configAtomSumEquiv, headAtomEquiv,
        finProdFinEquiv, htape, Nat.mul_comm]
      omega
  | cell tape position symbol =>
      have htape : (tapeSlotEquiv k tape).val = tape.index.val := rfl
      have hsymbol : (symbolEquiv symbol).val = (symbolIndex symbol).val := rfl
      simp [configIndex, configAtomEquiv, configAtomSumEquiv, cellAtomEquiv,
        finProdFinEquiv, htape, hsymbol, Nat.mul_comm]
      omega

/-- The explicit arithmetic index agrees with the atom-layout equivalence. -/
theorem configAtomEquiv_apply_val (tm : NTM k) (T : ℕ)
    (atom : ConfigAtom tm T) :
    (configAtomEquiv tm T atom).val = configIndex tm T atom :=
  (configIndex_eq_equivVal tm T atom).symm

/-- Every explicit atom index lies inside its configuration block. -/
theorem configIndex_lt (tm : NTM k) (T : ℕ) (atom : ConfigAtom tm T) :
    configIndex tm T atom < configWidth tm T := by
  rw [configIndex_eq_equivVal]
  exact (configAtomEquiv tm T atom).isLt

/-- State atoms occupy the first portion of a configuration block. -/
@[simp] theorem configIndex_state (tm : NTM k) (T : ℕ) (q : tm.Q) :
    configIndex tm T (.state q) = stateIndex tm q := rfl

/-- Head atoms follow states, ordered first by tape and then position. -/
@[simp] theorem configIndex_head (tm : NTM k) (T : ℕ)
    (tape : TapeSlot k) (position : Fin (T + 1)) :
    configIndex tm T (.head tape position) =
      Fintype.card tm.Q + tape.index.val * (T + 1) + position.val := rfl

/-- Cell atoms follow heads, ordered by tape, position, and symbol. -/
@[simp] theorem configIndex_cell (tm : NTM k) (T : ℕ)
    (tape : TapeSlot k) (position : Fin (T + 2)) (symbol : Γ) :
    configIndex tm T (.cell tape position symbol) =
      Fintype.card tm.Q + (k + 2) * (T + 1) +
        (tape.index.val * (T + 2) + position.val) * 4 + symbolIndex symbol := rfl

/-- Absolute wire carrying a configuration atom after a given prefix. -/
noncomputable def configWire (tm : NTM k) (T base : ℕ)
    (atom : ConfigAtom tm T) : ℕ :=
  base + configIndex tm T atom

namespace ConfigAtom

/-- Boolean truth value of an atom in a concrete configuration. -/
def value {k : ℕ} {tm : NTM k} {T : ℕ} (c : Cfg k tm.Q)
    (atom : ConfigAtom tm T) : Bool :=
  match atom with
  | .state q => decide (c.state = q)
  | .head tape position => decide ((tape.get c).head = position.val)
  | .cell tape position symbol => decide ((tape.get c).cells position.val = symbol)

end ConfigAtom

/-- An array encodes a configuration at `base` when every atom wire has its
semantic one-hot value. -/
def EncodesConfig (tm : NTM k) (T base : ℕ) (wires : Array Bool)
    (c : Cfg k tm.Q) : Prop :=
  ∀ atom, wires[configWire tm T base atom]? = some (atom.value c)

/-- Locations of choice and input-data bits among an existing wire prefix. -/
structure InputWires (T n available : ℕ) where
  /-- Wire carrying each nondeterministic choice bit. -/
  choice : Fin T → Fin available
  /-- Wire carrying each input-data bit. -/
  data : Fin n → Fin available

/-- Canonical input order: all choice bits, followed by all input-data bits. -/
def prefixInputWires (T n : ℕ) : InputWires T n (T + n) where
  choice i := ⟨i.val, by omega⟩
  data i := ⟨T + i.val, by omega⟩

/-- In the canonical layout, choice `i` is primary input wire `i`. -/
@[simp] theorem prefixInputWires_choice (T n : ℕ) (i : Fin T) :
    ((prefixInputWires T n).choice i).val = i.val := rfl

/-- In the canonical layout, data bit `i` follows all `T` choice wires. -/
@[simp] theorem prefixInputWires_data (T n : ℕ) (i : Fin n) :
    ((prefixInputWires T n).data i).val = T + i.val := rfl

/-- A Boolean source used by the one-gate initialization fragment. -/
inductive InitSource (available : ℕ) where
  /-- A constant Boolean value. -/
  | constant (value : Bool)
  /-- An existing wire, optionally negated. -/
  | wire (input : Fin available) (negated : Bool)

namespace InitSource

/-- Semantic value of an initialization source under a prefix assignment. -/
def value (assignment : Fin available → Bool) : InitSource available → Bool
  | .constant value => value
  | .wire input negated => negated.xor (assignment input)

/-- Compile an initialization source to exactly one raw gate. -/
def gate : InitSource available → CircuitCode.RawGate
  | .constant value => CircuitCode.RawGate.constant 0 value
  | .wire input negated => CircuitCode.RawGate.copy input.val negated

end InitSource

/-- Source for the initial one-hot value of a bounded configuration atom. -/
def initSource (tm : NTM k) (T n available : ℕ)
    (layout : InputWires T n available) : ConfigAtom tm T → InitSource available
  | .state q => .constant (decide (tm.qstart = q))
  | .head _ position => .constant (decide (position.val = 0))
  | .cell tape position symbol =>
      if _hzero : position.val = 0 then
        .constant (decide (symbol = Γ.start))
      else
        match tape with
        | .input =>
            if hdata : position.val - 1 < n then
              match symbol with
              | .zero => .wire (layout.data ⟨position.val - 1, hdata⟩) true
              | .one => .wire (layout.data ⟨position.val - 1, hdata⟩) false
              | .blank => .constant false
              | .start => .constant false
            else
              .constant (decide (symbol = Γ.blank))
        | .work _ => .constant (decide (symbol = Γ.blank))
        | .output => .constant (decide (symbol = Γ.blank))

/-- Configuration atoms listed in exactly their explicit wire order. -/
noncomputable def configAtoms (tm : NTM k) (T : ℕ) : List (ConfigAtom tm T) :=
  List.ofFn (configAtomEquiv tm T).symm

/-- One-gate-per-atom fragment producing the initial configuration block. -/
noncomputable def initFragment (tm : NTM k) (T n available : ℕ)
    (layout : InputWires T n available) : CircuitCode.RawCircuit :=
  (configAtoms tm T).map fun atom => (initSource tm T n available layout atom).gate

end CircuitUnrolling

end Complexity
