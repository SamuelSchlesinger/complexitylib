import Complexitylib.Classes.Pairing

/-!
# Bit-string encoding typeclass

`BitEncodable α` provides a specification-level mapping between a type `α` and `List Bool`,
used to state that a Turing machine's bit-string I/O corresponds to a Lean function operating
on abstract types. The encoding carries **no computational obligation** — it is purely a
correspondence used in the *statements* of PPT predicates, not in any executed code.

## Main definitions

- `BitEncodable` — typeclass with `encode : α → List Bool`, `decode : List Bool → α`,
  and a roundtrip proof
- Instances for `Unit`, `List Bool`, `Prod`, `Option`
-/

/-- Specification-level encoding of a type as bit strings.
    Used to relate Turing machine I/O to Lean functions on abstract types.
    The `decode` function is total: it returns a default value for invalid inputs.
    Only the roundtrip property `decode (encode a) = a` is required. -/
class BitEncodable (α : Type) where
  /-- Encode a value as a bit string. -/
  encode : α → List Bool
  /-- Decode a bit string to a value. Returns a default for invalid inputs. -/
  decode : List Bool → α
  /-- Decoding an encoded value recovers the original. -/
  roundtrip : ∀ a, decode (encode a) = a

namespace BitEncodable

instance unit : BitEncodable Unit where
  encode _ := []
  decode _ := ()
  roundtrip _ := rfl

instance listBool : BitEncodable (List Bool) where
  encode := id
  decode := id
  roundtrip _ := rfl

/-- Encode `Option (List Bool)` as a bit string: `none ↦ [false]`,
    `some x ↦ true :: x`. -/
instance optionListBool : BitEncodable (Option (List Bool)) where
  encode
    | none => [false]
    | some x => true :: x
  decode
    | [] => none
    | false :: _ => none
    | true :: x => some x
  roundtrip a := by cases a <;> simp

instance prod [BitEncodable α] [BitEncodable β] : BitEncodable (α × β) where
  encode := fun (a, b) => pair (BitEncodable.encode a) (BitEncodable.encode b)
  decode := fun bits =>
    let (l, r) := unpair bits
    (BitEncodable.decode l, BitEncodable.decode r)
  roundtrip := fun (a, b) => by simp [unpair_pair, BitEncodable.roundtrip]

end BitEncodable
