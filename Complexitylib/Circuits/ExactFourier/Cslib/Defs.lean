/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Circuits.ExactFourier.Defs
public import Cslib.Computability.Circuit.Basic

/-!
# CSLib representation of exact scalar Fourier circuits

Addition, subtraction, and multiplication by an arbitrary complex scalar are
separate operations. All gates cost one in CSLib's gate-count model. The
source's free zero wire is implemented by one additional nullary zero gate.
-/

@[expose] public section

namespace Complexity.ExactFourier

/-- The charged scalar operations, together with a constant zero gate. -/
inductive ScalarOp where
  /-- Produce zero without arguments. -/
  | zero
  /-- Add two available values. -/
  | add
  /-- Subtract two available values. -/
  | sub
  /-- Multiply one available value by a fixed arbitrary complex scalar. -/
  | scale : ℂ → ScalarOp

/-- The literal scalar-operation signature, with fan-in at most two. -/
def scalarSignature : Cslib.Circuits.Signature where
  Op := ScalarOp
  Arity
    | .zero => 0
    | .add | .sub => 2
    | .scale _ => 1

/-- Exact complex arithmetic interprets the scalar-operation signature. -/
def scalarInterpretation : Cslib.Circuits.Interpretation scalarSignature ℂ
  | .zero, _ => 0
  | .add, x => x (0 : Fin 2) + x (1 : Fin 2)
  | .sub, x => x (0 : Fin 2) - x (1 : Fin 2)
  | .scale c, x => c * x (0 : Fin 1)

/-- Split the source's available values into original inputs and charged CSLib gates. -/
def sourceWire {n k : ℕ} (i : Fin (n + 1 + k)) : Cslib.Circuits.Wire n (k + 1) :=
  if h : i.val < n then .input ⟨i.val, h⟩ else .gate ⟨i.val - n, by have := i.isLt; lia⟩

/-- Translate one source operation, retaining its operands and scalar exactly. -/
def Gate.toCslib {n k : ℕ} : Gate (n + 1 + k) →
    Cslib.Circuits.Line scalarSignature n (k + 1)
  | .add i j => ⟨.add, ![sourceWire i, sourceWire j]⟩
  | .sub i j => ⟨.sub, ![sourceWire i, sourceWire j]⟩
  | .scale c i => ⟨.scale c, fun _ => sourceWire i⟩

/-- The zero gate followed by one CSLib gate for each source operation. -/
def Program.toCslib {n : ℕ} : {k : ℕ} → Program n k →
    Cslib.Circuits.Program scalarSignature n (k + 1)
  | 0, .nil => .gate .empty ⟨.zero, Fin.elim0⟩
  | _ + 1, .step p g => .gate p.toCslib g.toCslib

/-- Preserve designated outputs and sharing, adding only the source's free zero as a gate. -/
def Circuit.toCslib {n : ℕ} (C : Circuit n) :
    Cslib.Circuits.Circuit scalarSignature n n where
  program := C.program.toCslib
  outputs := sourceWire ∘ C.outputs

end Complexity.ExactFourier
