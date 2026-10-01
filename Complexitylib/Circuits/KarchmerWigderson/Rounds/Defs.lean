/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Mathlib.Data.Finset.Defs

/-!
# General protocols with bounded rounds and message alphabets

Each message is an element of `M`; `card M ≤ 2^m` expresses an `m`-bit
per-message cost bound. Both coordinate orientations are allowed at leaves.
The index bounds the number of messages on every path, with early termination.
-/

@[expose] public section

namespace Complexity.KarchmerWigderson

/-- A general deterministic KW protocol with message alphabet `M` and at
most `d` rounds. The speaker may depend on the preceding messages. An answer
is a coordinate determined by the transcript, with no further input dependence. -/
inductive RoundProtocol (ι M : Type*) : ℕ → Type _
  /-- Terminate with a coordinate, possibly before exhausting the round budget. -/
  | answer {d : ℕ} (index : ι) : RoundProtocol ι M d
  /-- Alice sends one message computed from her input. -/
  | alice {d : ℕ} (send : (ι → Bool) → M) (next : M → RoundProtocol ι M d) :
      RoundProtocol ι M (d + 1)
  /-- Bob sends one message computed from his input. -/
  | bob {d : ℕ} (send : (ι → Bool) → M) (next : M → RoundProtocol ι M d) :
      RoundProtocol ι M (d + 1)

namespace RoundProtocol

/-- The coordinate output by a protocol on the two inputs. -/
def run {ι M : Type*} {d : ℕ} : RoundProtocol ι M d → (ι → Bool) → (ι → Bool) → ι
  | .answer i, _, _ => i
  | .alice send next, x, y => (next (send x)).run x y
  | .bob send next, x, y => (next (send y)).run x y

/-- Every pair in the input rectangle differs at the protocol's output coordinate. -/
def Solves {ι M : Type*} {d : ℕ} (P : RoundProtocol ι M d)
    (X Y : Finset (ι → Bool)) : Prop := ∀ x ∈ X, ∀ y ∈ Y, x (P.run x y) ≠ y (P.run x y)

/-- Solve the general KW game of a Boolean function: Alice has a zero-input,
Bob a one-input, and the protocol must output a differing coordinate. -/
def SolvesKW {ι M : Type*} {d : ℕ} (P : RoundProtocol ι M d)
    (f : (ι → Bool) → Bool) : Prop :=
  ∀ x y, f x = false → f y = true → x (P.run x y) ≠ y (P.run x y)

/-- Swap the players throughout the protocol without changing its round or message bounds. -/
def swapPlayers {ι M : Type*} : {d : ℕ} → RoundProtocol ι M d → RoundProtocol ι M d
  | _, .answer i => .answer i
  | _, .alice send next => .bob send (fun a => (next a).swapPlayers)
  | _, .bob send next => .alice send (fun a => (next a).swapPlayers)


end RoundProtocol
end Complexity.KarchmerWigderson
