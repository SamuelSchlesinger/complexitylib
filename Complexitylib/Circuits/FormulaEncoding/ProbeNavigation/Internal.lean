/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import Complexitylib.Circuits.FormulaEncoding.ProbeNavigation.Defs
import Complexitylib.Circuits.FormulaEncoding.BitNavigation.Internal

/-!
# Probe-oriented navigation in formula codes -- proof internals
-/

namespace Complexity

namespace FormulaCode

namespace BitOracle

private theorem ofList_append_boundary (before after : List Bool)
    (bit : Bool) :
    ofList (before ++ bit :: after) before.length = some bit := by
  rw [ofList, List.getElem?_append_right (Nat.le_refl _)]
  simp

private theorem ofList_append_getElem (before payload after : List Bool)
    (index : ℕ) (hindex : index < payload.length) :
    ofList (before ++ payload ++ after) (before.length + index) =
      some payload[index] := by
  rw [show before ++ payload ++ after = before ++ (payload ++ after) by
    simp [List.append_assoc]]
  rw [ofList, List.getElem?_append_right (by omega)]
  rw [show before.length + index - before.length = index by omega]
  rw [List.getElem?_append_left hindex]
  exact List.getElem?_eq_getElem hindex

theorem decodeNatAt?_ofList_append_encode_internal
    (before after : List Bool) (value extraFuel accumulator : ℕ) :
    decodeNatAt?
        (ofList
          (before ++ CircuitCode.NatCode.encode value ++ after))
        (value + 1 + extraFuel) before.length accumulator =
      some (accumulator + value, before.length + value + 1) := by
  induction value generalizing before accumulator with
  | zero =>
      simp only [CircuitCode.NatCode.encode, List.replicate_zero,
        List.nil_append, Nat.zero_add, Nat.one_add]
      rw [show before ++ [false] ++ after = before ++ false :: after by simp]
      simp only [decodeNatAt?]
      rw [ofList_append_boundary]
      rfl
  | succ value ih =>
      have hcode : CircuitCode.NatCode.encode (value + 1) =
          true :: CircuitCode.NatCode.encode value := by
        simp [CircuitCode.NatCode.encode, List.replicate_succ]
      rw [hcode]
      rw [show before ++ (true :: CircuitCode.NatCode.encode value) ++ after =
        before ++ true :: (CircuitCode.NatCode.encode value ++ after) by
          simp [List.append_assoc]]
      rw [show value + 1 + 1 + extraFuel =
        Nat.succ (value + 1 + extraFuel) by omega]
      simp only [decodeNatAt?]
      rw [ofList_append_boundary]
      simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
        ih (before ++ [true]) (accumulator + 1)

theorem decodeTokenAt?_ofList_append_encode_internal
    (before after : List Bool) (token : Token) (extraFuel : ℕ) :
    decodeTokenAt? (ofList (before ++ token.encode ++ after))
        (token.codeLength + extraFuel) before.length =
      some (token, before.length + token.codeLength) := by
  have h₀ := ofList_append_getElem before token.encode after 0
    (by cases token <;> simp [Token.encode])
  simp only [Nat.add_zero] at h₀
  have h₁ := ofList_append_getElem before token.encode after 1
    (by cases token <;> simp [Token.encode])
  have h₂ := ofList_append_getElem before token.encode after 2
    (by cases token <;> simp [Token.encode])
  rw [decodeTokenAt?, h₀, h₁, h₂]
  cases token with
  | var index =>
      have hnat :
          decodeNatAt?
              (ofList (before ++ Token.encode (.var index) ++ after))
              (Token.codeLength (.var index) + extraFuel)
              (before.length + 3) 0 =
            some (index,
              before.length + Token.codeLength (.var index)) := by
        simpa [Token.encode, Token.codeLength, List.append_assoc,
          Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
          decodeNatAt?_ofList_append_encode_internal
            (before ++ [false, false, false]) after index
            (3 + extraFuel) 0
      rw [hnat]
      simp [Token.encode]
  | tru => rfl
  | fls => rfl
  | neg => rfl
  | conj => rfl
  | disj => rfl

theorem decodeTokenAt?_ofList_append_encode_of_le_internal
    (before after : List Bool) (token : Token) (bitFuel : ℕ)
    (hfuel : token.codeLength ≤ bitFuel) :
    decodeTokenAt? (ofList (before ++ token.encode ++ after))
        bitFuel before.length =
      some (token, before.length + token.codeLength) := by
  simpa [Nat.add_sub_of_le hfuel] using
    decodeTokenAt?_ofList_append_encode_internal before after token
      (bitFuel - token.codeLength)

theorem tokenHeader?_ofList_encodeTokenStream_internal
    (stream : List Token) (extraFuel : ℕ) :
    tokenHeader? (ofList (encodeTokenStream stream))
        (stream.length + 1 + extraFuel) =
      some ⟨stream.length, stream.length + 1⟩ := by
  rw [tokenHeader?, encodeTokenStream]
  have hnat := decodeNatAt?_ofList_append_encode_internal []
    (stream.flatMap Token.encode) stream.length extraFuel 0
  simp only [List.nil_append, List.length_nil] at hnat
  rw [hnat]
  simp

theorem seekToken?_ofList_flatMap_encode_internal
    (beforeBits suffix : List Bool) (stream : List Token)
    (bitFuel index : ℕ) (hindex : index < stream.length)
    (hbound : ∀ token ∈ stream, token.codeLength ≤ bitFuel) :
    seekToken?
        (ofList (beforeBits ++ stream.flatMap Token.encode ++ suffix))
        bitFuel beforeBits.length index =
      some
        ⟨stream[index], beforeBits.length + tokenBitOffset stream index,
          beforeBits.length + tokenBitOffset stream index +
            stream[index].codeLength⟩ := by
  induction stream generalizing beforeBits index with
  | nil => simp at hindex
  | cons token stream ih =>
      have htoken : token.codeLength ≤ bitFuel := hbound token (by simp)
      have htail : ∀ item ∈ stream, item.codeLength ≤ bitFuel := by
        intro item hitem
        exact hbound item (by simp [hitem])
      cases index with
      | zero =>
          simp only [seekToken?, List.flatMap_cons, List.getElem_cons_zero,
            tokenBitOffset, List.take_zero, tokensCodeLength, List.map_nil,
            List.sum_nil, Nat.add_zero]
          rw [show beforeBits ++
              (token.encode ++ stream.flatMap Token.encode) ++ suffix =
                beforeBits ++ token.encode ++
                  (stream.flatMap Token.encode ++ suffix) by
            simp [List.append_assoc]]
          rw [decodeTokenAt?_ofList_append_encode_of_le_internal
            beforeBits (stream.flatMap Token.encode ++ suffix) token bitFuel
            htoken]
          rfl
      | succ index =>
          have htailIndex : index < stream.length := by
            simpa using hindex
          simp only [seekToken?, List.flatMap_cons]
          rw [show beforeBits ++
              (token.encode ++ stream.flatMap Token.encode) ++ suffix =
                beforeBits ++ token.encode ++
                  (stream.flatMap Token.encode ++ suffix) by
            simp [List.append_assoc]]
          rw [decodeTokenAt?_ofList_append_encode_of_le_internal
            beforeBits (stream.flatMap Token.encode ++ suffix) token bitFuel
            htoken]
          simpa [List.append_assoc, tokenBitOffset, tokensCodeLength,
            Nat.add_assoc] using
            ih (beforeBits ++ token.encode) index htailIndex htail

theorem tokenAt?_ofList_encodeTokenStream_internal
    (stream : List Token) (bitFuel index : ℕ)
    (hheader : stream.length + 1 ≤ bitFuel)
    (hindex : index < stream.length)
    (hbound : ∀ token ∈ stream, token.codeLength ≤ bitFuel) :
    tokenAt? (ofList (encodeTokenStream stream)) bitFuel index =
      some
        ⟨stream[index], stream.length + 1 + tokenBitOffset stream index,
          stream.length + 1 + tokenBitOffset stream index +
            stream[index].codeLength⟩ := by
  have hheaderExact :
      tokenHeader? (ofList (encodeTokenStream stream)) bitFuel =
        some ⟨stream.length, stream.length + 1⟩ := by
    simpa [Nat.add_sub_of_le hheader] using
      tokenHeader?_ofList_encodeTokenStream_internal stream
        (bitFuel - (stream.length + 1))
  rw [tokenAt?, hheaderExact]
  change (if index < stream.length then
      seekToken? (ofList (encodeTokenStream stream)) bitFuel
        (stream.length + 1) index
    else none) = _
  rw [if_pos hindex, encodeTokenStream]
  simpa [CircuitCode.NatCode.length_encode] using
    seekToken?_ofList_flatMap_encode_internal
      (CircuitCode.NatCode.encode stream.length) [] stream bitFuel index
        hindex hbound

theorem tokenValueAt?_ofList_encodeTokenStream_internal
    (stream : List Token) (bitFuel index : ℕ)
    (hheader : stream.length + 1 ≤ bitFuel)
    (hindex : index < stream.length)
    (hbound : ∀ token ∈ stream, token.codeLength ≤ bitFuel) :
    tokenValueAt? (ofList (encodeTokenStream stream)) bitFuel index =
      some stream[index] := by
  rw [tokenValueAt?, tokenAt?_ofList_encodeTokenStream_internal stream
    bitFuel index hheader hindex hbound]
  rfl

theorem encodedSubtreeWidth?_ofList_encodeTokenStream_internal
    (stream : List Token) (bitFuel root : ℕ)
    (hheader : stream.length + 1 ≤ bitFuel)
    (hroot : root < stream.length)
    (hbound : ∀ token ∈ stream, token.codeLength ≤ bitFuel) :
    encodedSubtreeWidth? (ofList (encodeTokenStream stream))
        bitFuel root = subtreeWidth? stream root := by
  rw [encodedSubtreeWidth?, subtreeWidth?]
  apply backwardScanQuery?_eq_backwardScan_internal stream
    (tokenValueAt? (ofList (encodeTokenStream stream)) bitFuel)
    root hroot
  intro index hindex
  have hvalid : index < stream.length := by omega
  rw [tokenValueAt?_ofList_encodeTokenStream_internal stream bitFuel
    index hheader hvalid hbound, List.getElem?_eq_getElem hvalid]

theorem encodedSubtreeWidth?_ofList_encodeTokenStream_context_internal
    (before after : List Token) (formula : BoolFormula) (bitFuel : ℕ)
    (hheader : (before ++ tokens formula ++ after).length + 1 ≤ bitFuel)
    (hbound : ∀ token ∈ before ++ tokens formula ++ after,
      token.codeLength ≤ bitFuel) :
    encodedSubtreeWidth?
        (ofList (encodeTokenStream (before ++ tokens formula ++ after)))
        bitFuel (before.length + formula.size - 1) =
      some formula.size := by
  have hpositive : 0 < formula.size := by
    cases formula <;> simp [BoolFormula.size]
  rw [encodedSubtreeWidth?_ofList_encodeTokenStream_internal]
  · exact subtreeWidth?_tokens_context_internal before after formula
  · exact hheader
  · simp
    omega
  · exact hbound

theorem encodedBinaryChildren?_ofList_encodeTokenStream_internal
    (before after : List Token) (left right : BoolFormula)
    (op : Token) (bitFuel : ℕ)
    (hheader :
      (before ++ tokens left ++ tokens right ++ [op] ++ after).length + 1 ≤
        bitFuel)
    (hbound : ∀ token ∈
      before ++ tokens left ++ tokens right ++ [op] ++ after,
        token.codeLength ≤ bitFuel) :
    encodedBinaryChildren?
        (ofList (encodeTokenStream
          (before ++ tokens left ++ tokens right ++ [op] ++ after)))
        bitFuel ⟨before.length, left.size + right.size + 1⟩ =
      some (⟨before.length, left.size⟩,
        ⟨before.length + left.size, right.size⟩) := by
  have hleftPositive : 0 < left.size := by
    cases left <;> simp [BoolFormula.size]
  have hrightPositive : 0 < right.size := by
    cases right <;> simp [BoolFormula.size]
  rw [encodedBinaryChildren?]
  simp only [TokenSegment.root?, TokenSegment.dropRoot?,
    Option.bind_eq_bind, Option.bind_some]
  rw [show before.length + (left.size + right.size) =
      (before.length + left.size + right.size - 1) + 1 by omega]
  simp only [previousToken?, Option.bind_some]
  change (do
    let rightWidth ← encodedSubtreeWidth?
      (ofList (encodeTokenStream
        (before ++ tokens left ++ tokens right ++ [op] ++ after)))
      bitFuel (before.length + left.size + right.size - 1)
    if 0 < rightWidth ∧ rightWidth < left.size + right.size then
      some (TokenSegment.mk before.length
          (left.size + right.size - rightWidth),
        TokenSegment.mk
          (before.length + (left.size + right.size - rightWidth))
          rightWidth)
    else none) = _
  rw [show before ++ tokens left ++ tokens right ++ [op] ++ after =
      (before ++ tokens left) ++ tokens right ++ ([op] ++ after) by
    simp [List.append_assoc]] at hheader hbound ⊢
  rw [show before.length + left.size + right.size - 1 =
      (before ++ tokens left).length + right.size - 1 by simp]
  rw [encodedSubtreeWidth?_ofList_encodeTokenStream_context_internal
    (before ++ tokens left) ([op] ++ after) right bitFuel hheader hbound]
  simp only [Option.bind_eq_bind, Option.bind_some]
  rw [if_pos (by omega)]
  congr <;> omega

end BitOracle

end FormulaCode

end Complexity
