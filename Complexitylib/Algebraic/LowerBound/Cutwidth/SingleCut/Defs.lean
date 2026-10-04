/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.Program
public import Cslib.Computability.Circuit.Dependency

/-!
# Single cuts of a straight-line program

The vertices of a straight-line program are its wires: the inputs and the gates. A *cut* is a
set `S` of wires, with complement `Sᶜ`. A *signal* is the value carried by one wire, however
many gates read it.

* `inputsIn S` is the set of input coordinates whose wires lie in `S`;
* `forward p S` is the set of wires in `S` read by some gate outside `S`;
* `backward p S` is the set of wires outside `S` read by some gate in `S`;
* `boundaryKey p I S x` records the values of the forward and backward signals of `S`
  under the input `x`;
* `mix S x x'` takes the coordinates of `x` whose input wires lie in `S` and the other
  coordinates of `x'`;
* `leftPart S x` and `rightPart S x` restrict `x` to the coordinates whose input wires lie in
  `S` and outside `S`, respectively;
* `leftParts p I S Z κ` and `rightParts p I S Z κ` collect these restrictions over the members
  of `Z` with boundary key `κ`.

The definitions are generic in the signature and in the value type; the single-cut criterion
specializes the value type to `Bool`.
-/

@[expose] public section

namespace Algebraic.Cutwidth.SingleCut

variable {σ : Signature} {n s : Nat} {U : Type*}

/-- The input coordinates whose wires lie in `S`. -/
def inputsIn (S : Finset (Wire n s)) : Finset (Fin n) :=
  Finset.univ.filter fun j => Wire.input j ∈ S

/-- The forward signals of `S`: the wires in `S` read by some gate outside `S`. A wire read by
several gates outside `S` is one signal. -/
def forward (p : Program σ n s) (S : Finset (Wire n s)) : Finset (Wire n s) :=
  S.filter fun w => ∃ g : Fin s, Wire.gate g ∉ S ∧ p.Reads g w

/-- The backward signals of `S`: the wires outside `S` read by some gate in `S`. A wire read by
several gates in `S` is one signal. -/
def backward (p : Program σ n s) (S : Finset (Wire n s)) : Finset (Wire n s) :=
  Sᶜ.filter fun w => ∃ g : Fin s, Wire.gate g ∈ S ∧ p.Reads g w

/-- The values of the forward and of the backward signals of `S` under the input `x`. -/
def boundaryKey (p : Program σ n s) (I : Interpretation σ U) (S : Finset (Wire n s))
    (x : Fin n → U) : (↥(forward p S) → U) × (↥(backward p S) → U) :=
  (fun w => p.trace I x w, fun w => p.trace I x w)

/-- The input taking the coordinates of `x` whose wires lie in `S` and the other coordinates
of `x'`. -/
def mix (S : Finset (Wire n s)) (x x' : Fin n → U) : Fin n → U :=
  fun j => if Wire.input j ∈ S then x j else x' j

/-- The restriction of an input to the coordinates whose wires lie in `S`. -/
def leftPart (S : Finset (Wire n s)) (x : Fin n → U) : ↥(inputsIn S) → U :=
  fun j => x j

/-- The restriction of an input to the coordinates whose wires lie outside `S`. -/
def rightPart (S : Finset (Wire n s)) (x : Fin n → U) : ↥(inputsIn S)ᶜ → U :=
  fun j => x j

/-- The left parts of the members of `Z` whose boundary key is `κ`. -/
def leftParts [DecidableEq U] (p : Program σ n s) (I : Interpretation σ U)
    (S : Finset (Wire n s)) (Z : Finset (Fin n → U)) (κ : (↥(forward p S) → U) × (↥(backward p S) → U)) :
    Finset (↥(inputsIn S) → U) :=
  (Z.filter fun x => boundaryKey p I S x = κ).image (leftPart S)

/-- The right parts of the members of `Z` whose boundary key is `κ`. -/
def rightParts [DecidableEq U] (p : Program σ n s) (I : Interpretation σ U)
    (S : Finset (Wire n s)) (Z : Finset (Fin n → U)) (κ : (↥(forward p S) → U) × (↥(backward p S) → U)) :
    Finset (↥(inputsIn S)ᶜ → U) :=
  (Z.filter fun x => boundaryKey p I S x = κ).image (rightPart S)

theorem mem_inputsIn {S : Finset (Wire n s)} {j : Fin n} : j ∈ inputsIn S ↔ Wire.input j ∈ S := by
  simp [inputsIn]

theorem mem_forward {p : Program σ n s} {S : Finset (Wire n s)} {w : Wire n s} :
    w ∈ forward p S ↔ w ∈ S ∧ ∃ g : Fin s, Wire.gate g ∉ S ∧ p.Reads g w := by
  simp [forward]

theorem mem_backward {p : Program σ n s} {S : Finset (Wire n s)} {w : Wire n s} :
    w ∈ backward p S ↔ w ∉ S ∧ ∃ g : Fin s, Wire.gate g ∈ S ∧ p.Reads g w := by
  simp [backward]

/-- The inputs placed in the complement of `S` are the inputs not placed in `S`. -/
theorem inputsIn_compl (S : Finset (Wire n s)) : inputsIn Sᶜ = (inputsIn S)ᶜ := by
  ext j
  simp [mem_inputsIn]

/-- The forward signals of the complement are the backward signals. -/
theorem forward_compl (p : Program σ n s) (S : Finset (Wire n s)) :
    forward p Sᶜ = backward p S := by
  ext w
  simp [mem_forward, mem_backward]

/-- The backward signals of the complement are the forward signals. -/
theorem backward_compl (p : Program σ n s) (S : Finset (Wire n s)) :
    backward p Sᶜ = forward p S := by
  ext w
  simp [mem_forward, mem_backward]

end Algebraic.Cutwidth.SingleCut
