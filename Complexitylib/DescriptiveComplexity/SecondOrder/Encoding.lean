/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.DescriptiveComplexity.SecondOrder.Encoding.Defs
public import Complexitylib.DescriptiveComplexity.SecondOrder.Encoding.Internal

/-!
# Exact truth-table certificates for second-order witnesses

The encoder bijects Boolean relation environments with all bit strings of the
prescribed length. The decoder rejects exactly incorrect lengths. Nullary
relations take one bit, and an empty context takes no bits. The exact length is
a polynomial in the universe size, for a fixed relation context.
-/

public section

namespace Complexity.DescriptiveComplexity.DecREnv

/-- Every relation-table cell occurs in the certificate enumeration. -/
theorem mem_encodingSites (card : Nat) (rctx : List Nat) (site : EncodingSite card rctx) :
    site ∈ encodingSites card rctx := mem_encodingSites_internal card rctx site

/-- Each relation-table cell occurs exactly once. -/
theorem encodingSites_nodup (card : Nat) (rctx : List Nat) :
    (encodingSites card rctx).Nodup := encodingSites_nodup_internal card rctx

/-- The site list has the exact sum-of-powers length. -/
@[simp] theorem encodingSites_length (card : Nat) (rctx : List Nat) :
    (encodingSites card rctx).length = encodingLength card rctx :=
  encodingSites_length_internal card rctx

/-- The empty relation context needs no certificate bits. -/
@[simp] theorem encodingLength_nil (card : Nat) : encodingLength card [] = 0 := rfl

/-- Extending the context adds one truth table of length `card ^ k`. -/
@[simp] theorem encodingLength_cons (card k : Nat) (rctx : List Nat) :
    encodingLength card (k :: rctx) = card ^ k + encodingLength card rctx := rfl

/-- The certificate has exactly the sum of its relation-table sizes. -/
@[simp] theorem encode_length {card : Nat} {rctx : List Nat} (ρ : DecREnv card rctx) :
    (encode ρ).length = encodingLength card rctx := by
  simp only [encode, List.length_map, encodingSites_length]

/-- The certificate lists each relation's canonical truth table in context order. -/
theorem encode_eq_flatMap {card : Nat} {rctx : List Nat} (ρ : DecREnv card rctx) :
    encode ρ = (List.finRange rctx.length).flatMap fun r => encodeRelC (ρ r) := by
  simp [encode, encodingSites, List.map_flatMap, List.map_map, Function.comp_def, encodeRelC]

/-- Extending the environment prepends the new relation's truth table. -/
theorem encode_cons {card k : Nat} {rctx : List Nat}
    (S : (Fin k → Fin card) → Bool) (ρ : DecREnv card rctx) :
    encode (ρ.cons S) = encodeRelC S ++ encode ρ := by
  simp only [encode_eq_flatMap, List.length_cons, List.finRange_succ,
    List.flatMap_cons, List.flatMap_map]
  rfl

/-- A single unary relation is encoded in vertex order. -/
theorem encode_unary {card : Nat} (color : Fin card → Bool) :
    encode ((empty card).cons (fun args : Fin 1 → Fin card => color (args 0))) =
      List.ofFn color := by
  rw [encode_cons]
  simp [encode, encodingSites, encodeRelC, allTuples, List.ofFn_eq_map]

/-- Direct reads recover every encoded relation. -/
@[simp] theorem read_encode {card : Nat} {rctx : List Nat} (ρ : DecREnv card rctx) :
    read card rctx (encode ρ) = ρ := read_encode_internal ρ

/-- Every string of the specified length is the encoding of its decoded tables. -/
theorem encode_read (card : Nat) (rctx : List Nat) (bits : List Bool)
    (h : bits.length = encodingLength card rctx) :
    encode (read card rctx bits) = bits := encode_read_internal card rctx bits h

/-- The checked decoder recovers the supplied relation environment. -/
@[simp] theorem decode_encode {card : Nat} {rctx : List Nat} (ρ : DecREnv card rctx) :
    decode card rctx (encode ρ) = some ρ := by
  simp [decode]

/-- Distinct relation environments have distinct certificates. -/
theorem encode_injective (card : Nat) (rctx : List Nat) :
    Function.Injective (encode (card := card) (rctx := rctx)) := by
  intro ρ τ h
  simpa only [read_encode] using congrArg (read card rctx) h

/-- Decoding succeeds precisely on a relation environment's canonical encoding. -/
theorem decode_eq_some_iff {card : Nat} {rctx : List Nat} (bits : List Bool)
    (ρ : DecREnv card rctx) : decode card rctx bits = some ρ ↔ encode ρ = bits := by
  constructor
  · intro h
    unfold decode at h
    split at h
    next hlen =>
      cases Option.some.inj h
      exact encode_read card rctx bits hlen
    next => contradiction
  · rintro rfl
    exact decode_encode ρ

/-- Certificate rejection is exactly a length mismatch. -/
@[simp] theorem decode_eq_none_iff (card : Nat) (rctx : List Nat) (bits : List Bool) :
    decode card rctx bits = none ↔ bits.length ≠ encodingLength card rctx := by
  simp [decode]

/-- Exact witness length is a polynomial in universe cardinality. -/
@[simp] theorem encodingPolynomial_eval (card : Nat) (rctx : List Nat) :
    (encodingPolynomial rctx).eval card = encodingLength card rctx :=
  encodingPolynomial_eval_internal card rctx

/-- Increasing the universe size cannot shorten a relation certificate. -/
theorem encodingLength_mono (rctx : List Nat) :
    Monotone (fun card => encodingLength card rctx) := encodingLength_mono_internal rctx

end Complexity.DescriptiveComplexity.DecREnv
