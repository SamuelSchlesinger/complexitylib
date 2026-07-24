/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import Complexitylib.Circuits.FormulaEncoding
import Complexitylib.Circuits.FormulaEncoding.BitNavigation.Defs
import Complexitylib.Circuits.FormulaEncoding.Navigation.Internal

/-!
# Bit-level navigation in canonical formula codes -- proof internals
-/

namespace Complexity

namespace FormulaCode

namespace Token

theorem decodeAt?_append_encode_internal (beforeBits : List Bool)
    (token : Token) (suffix : List Bool) :
    decodeAt? (beforeBits ++ token.encode ++ suffix) beforeBits.length =
      some (token, beforeBits.length + token.codeLength) := by
  simp [decodeAt?, List.append_assoc]
  omega

end Token

theorem tokensCodeLength_append_internal (first second : List Token) :
    tokensCodeLength (first ++ second) =
      tokensCodeLength first + tokensCodeLength second := by
  simp [tokensCodeLength, List.sum_append]

theorem tokensCodeLength_take_succ_internal (stream : List Token)
    (index : ℕ) (hindex : index < stream.length) :
    tokensCodeLength (stream.take (index + 1)) =
      tokensCodeLength (stream.take index) + stream[index].codeLength := by
  rw [← List.take_concat_get' stream index hindex,
    tokensCodeLength_append_internal]
  simp [tokensCodeLength]

theorem tokensCodeLength_eq_flatMap_length_internal
    (stream : List Token) :
    tokensCodeLength stream = (stream.flatMap Token.encode).length := by
  simp [tokensCodeLength, List.length_flatMap]

theorem seekToken?_flatMap_encode_internal
    (beforeBits suffix : List Bool) (stream : List Token)
    (index : ℕ) (hindex : index < stream.length) :
    seekToken? (beforeBits ++ stream.flatMap Token.encode ++ suffix)
        beforeBits.length index =
      some
        ⟨stream[index], beforeBits.length + tokenBitOffset stream index,
          beforeBits.length + tokenBitOffset stream index +
            (stream[index]).codeLength⟩ := by
  induction stream generalizing beforeBits index with
  | nil => simp at hindex
  | cons token stream ih =>
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
          rw [Token.decodeAt?_append_encode_internal]
          rfl
      | succ index =>
          have htail : index < stream.length := by
            simpa using hindex
          simp only [seekToken?, List.flatMap_cons]
          rw [show beforeBits ++
              (token.encode ++ stream.flatMap Token.encode) ++ suffix =
                beforeBits ++ token.encode ++
                  (stream.flatMap Token.encode ++ suffix) by
            simp [List.append_assoc]]
          rw [Token.decodeAt?_append_encode_internal]
          simpa [List.append_assoc, tokenBitOffset, tokensCodeLength,
            Nat.add_assoc] using
            ih (beforeBits ++ token.encode) index htail

theorem tokenHeader?_encode_internal (formula : BoolFormula) :
    tokenHeader? (encode formula) =
      some ⟨formula.size, formula.size + 1⟩ := by
  rw [tokenHeader?, encode]
  simp only [CircuitCode.NatCode.decodePrefix?_encode_append,
    length_tokens_internal]
  simp [CircuitCode.NatCode.length_encode]

theorem tokenHeader?_encodeTokenStream_internal (stream : List Token) :
    tokenHeader? (encodeTokenStream stream) =
      some ⟨stream.length, stream.length + 1⟩ := by
  rw [tokenHeader?, encodeTokenStream]
  simp [CircuitCode.NatCode.length_encode]

theorem tokenAt?_encodeTokenStream_internal (stream : List Token)
    (index : ℕ) (hindex : index < stream.length) :
    tokenAt? (encodeTokenStream stream) index =
      some
        ⟨stream[index], stream.length + 1 + tokenBitOffset stream index,
          stream.length + 1 + tokenBitOffset stream index +
            stream[index].codeLength⟩ := by
  rw [tokenAt?, tokenHeader?_encodeTokenStream_internal]
  change (if index < stream.length then
      seekToken? (encodeTokenStream stream) (stream.length + 1) index
    else none) = _
  rw [if_pos hindex, encodeTokenStream]
  simpa [CircuitCode.NatCode.length_encode] using
    seekToken?_flatMap_encode_internal
      (CircuitCode.NatCode.encode stream.length) [] stream index hindex

theorem tokenAt?_encode_internal (formula : BoolFormula)
    (index : ℕ) (hindex : index < (tokens formula).length) :
    tokenAt? (encode formula) index =
      some
        ⟨(tokens formula)[index], formula.size + 1 +
            tokenBitOffset (tokens formula) index,
          formula.size + 1 + tokenBitOffset (tokens formula) index +
            ((tokens formula)[index]).codeLength⟩ := by
  rw [tokenAt?, tokenHeader?_encode_internal]
  have hsize : index < formula.size := by
    simpa only [length_tokens_internal] using hindex
  change (if index < formula.size then
      seekToken? (encode formula) (formula.size + 1) index else none) = _
  rw [if_pos hsize]
  rw [encode]
  simpa [CircuitCode.NatCode.length_encode, length_tokens_internal] using
    seekToken?_flatMap_encode_internal
      (CircuitCode.NatCode.encode (tokens formula).length) []
      (tokens formula) index hindex

theorem backwardScanQuery?_eq_backwardScan_internal
    (stream : List Token) (query : ℕ → Option Token)
    (root : ℕ) (hroot : root < stream.length)
    (hquery : ∀ index, index ≤ root → query index = stream[index]?)
    (owed : ℕ) :
    backwardScanQuery? query (root + 1) (some root) owed =
      backwardScan (stream.take (root + 1)).reverse owed := by
  induction root generalizing owed with
  | zero =>
      cases owed with
      | zero => simp [backwardScanQuery?, backwardScan]
      | succ owed =>
          rw [List.take_succ_eq_append_getElem hroot]
          simp only [List.take_zero, List.nil_append, List.reverse_singleton,
            backwardScanQuery?, previousToken?, backwardScan]
          rw [hquery 0 le_rfl, List.getElem?_eq_getElem hroot]
          cases hnext : owed + stream[0].arity <;>
            simp [hnext, backwardScanQuery?, backwardScan]
  | succ root ih =>
      cases owed with
      | zero => simp [backwardScanQuery?, backwardScan]
      | succ owed =>
          have hroot' : root < stream.length := by omega
          rw [List.take_succ_eq_append_getElem hroot]
          simp only [List.reverse_append, List.reverse_singleton,
            List.singleton_append, backwardScanQuery?, previousToken?,
            backwardScan]
          rw [hquery (root + 1) le_rfl,
            List.getElem?_eq_getElem hroot]
          simp only [Option.bind_eq_bind, Option.bind_some]
          change (backwardScanQuery? query (root + 1) (some root)
              (owed + stream[root + 1].arity)).bind (fun consumed =>
                some (consumed + 1)) = _
          rw [ih hroot' (fun index hindex =>
            hquery index (by omega))]
          cases backwardScan (stream.take (root + 1)).reverse
              (owed + stream[root + 1].arity) <;> rfl

theorem tokenValueAt?_encode_internal (formula : BoolFormula)
    (index : ℕ) (hindex : index < (tokens formula).length) :
    tokenValueAt? (encode formula) index = some (tokens formula)[index] := by
  rw [tokenValueAt?, tokenAt?_encode_internal formula index hindex]
  rfl

theorem tokenValueAt?_encodeTokenStream_internal (stream : List Token)
    (index : ℕ) (hindex : index < stream.length) :
    tokenValueAt? (encodeTokenStream stream) index = some stream[index] := by
  rw [tokenValueAt?,
    tokenAt?_encodeTokenStream_internal stream index hindex]
  rfl

theorem encodedSubtreeWidth?_encodeTokenStream_internal
    (stream : List Token) (root : ℕ) (hroot : root < stream.length) :
    encodedSubtreeWidth? (encodeTokenStream stream) root =
      subtreeWidth? stream root := by
  rw [encodedSubtreeWidth?, subtreeWidth?]
  apply backwardScanQuery?_eq_backwardScan_internal stream
    (tokenValueAt? (encodeTokenStream stream)) root hroot
  intro index hindex
  have hvalid : index < stream.length := by omega
  rw [tokenValueAt?_encodeTokenStream_internal stream index hvalid,
    List.getElem?_eq_getElem hvalid]

theorem subtreeWidth?_tokens_context_internal (before after : List Token)
    (formula : BoolFormula) :
    subtreeWidth? (before ++ tokens formula ++ after)
      (before.length + formula.size - 1) = some formula.size := by
  rw [subtreeWidth?]
  have hpositive : 0 < formula.size := by
    cases formula <;> simp [BoolFormula.size]
  rw [show before.length + formula.size - 1 + 1 =
    before.length + formula.size by omega]
  have hprefixLength : (before ++ tokens formula).length =
      before.length + formula.size := by
    simp
  have htake : (before ++ tokens formula ++ after).take
      (before.length + formula.size) = before ++ tokens formula := by
    rw [← hprefixLength]
    exact List.take_left
  rw [htake, List.reverse_append]
  have hscan := backwardScan_tokens_reverse_append_internal
    formula before.reverse 0
  simpa [backwardScan] using hscan

theorem encodedSubtreeWidth?_encodeTokenStream_context_internal
    (before after : List Token) (formula : BoolFormula) :
    encodedSubtreeWidth?
        (encodeTokenStream (before ++ tokens formula ++ after))
        (before.length + formula.size - 1) = some formula.size := by
  have hpositive : 0 < formula.size := by
    cases formula <;> simp [BoolFormula.size]
  rw [encodedSubtreeWidth?_encodeTokenStream_internal]
  · exact subtreeWidth?_tokens_context_internal before after formula
  · simp
    omega

theorem encodedBinaryChildren?_encodeTokenStream_internal
    (before after : List Token) (left right : BoolFormula)
    (op : Token) :
    encodedBinaryChildren?
        (encodeTokenStream
          (before ++ tokens left ++ tokens right ++ [op] ++ after))
        ⟨before.length, left.size + right.size + 1⟩ =
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
      (encodeTokenStream
        (before ++ tokens left ++ tokens right ++ [op] ++ after))
      (before.length + left.size + right.size - 1)
    if 0 < rightWidth ∧ rightWidth < left.size + right.size then
      some (TokenSegment.mk before.length
          (left.size + right.size - rightWidth),
        TokenSegment.mk
          (before.length + (left.size + right.size - rightWidth))
          rightWidth)
    else none) = _
  rw [show before ++ tokens left ++ tokens right ++ [op] ++ after =
      (before ++ tokens left) ++ tokens right ++ ([op] ++ after) by
    simp [List.append_assoc]]
  rw [show before.length + left.size + right.size - 1 =
      (before ++ tokens left).length + right.size - 1 by
    simp]
  rw [encodedSubtreeWidth?_encodeTokenStream_context_internal]
  simp only [Option.bind_eq_bind, Option.bind_some]
  rw [if_pos (by omega)]
  congr <;> omega

theorem encodedSubtreeWidth?_encode_internal (formula : BoolFormula)
    (root : ℕ) (hroot : root < (tokens formula).length) :
    encodedSubtreeWidth? (encode formula) root =
      subtreeWidth? (tokens formula) root := by
  rw [encodedSubtreeWidth?, subtreeWidth?]
  apply backwardScanQuery?_eq_backwardScan_internal
    (tokens formula) (tokenValueAt? (encode formula)) root hroot
  intro index hindex
  have hvalid : index < (tokens formula).length := by omega
  rw [tokenValueAt?_encode_internal formula index hvalid,
    List.getElem?_eq_getElem hvalid]

theorem encodedSubtreeStart?_encode_internal (formula : BoolFormula)
    (root : ℕ) (hroot : root < (tokens formula).length) :
    encodedSubtreeStart? (encode formula) root =
      subtreeStart? (tokens formula) root := by
  rw [encodedSubtreeStart?, subtreeStart?,
    encodedSubtreeWidth?_encode_internal formula root hroot]

theorem encodedSubtreeWidth?_encode_root_internal
    (formula : BoolFormula) :
    encodedSubtreeWidth? (encode formula) (formula.size - 1) =
      some formula.size := by
  have hpositive : 0 < formula.size := by
    cases formula <;> simp [BoolFormula.size]
  rw [encodedSubtreeWidth?_encode_internal]
  · exact subtreeWidth?_tokens_root_internal formula
  · simpa [length_tokens_internal] using hpositive

theorem encodedSubtreeWidth?_encode_conj_right_internal
    (left right : BoolFormula) :
    encodedSubtreeWidth? (encode (.conj left right))
      (left.size + right.size - 1) = some right.size := by
  have hroot : left.size + right.size - 1 <
      (tokens (.conj left right)).length := by
    have hrightPositive : 0 < right.size := by
      cases right <;> simp [BoolFormula.size]
    simp only [tokens, List.length_append, List.length_singleton,
      length_tokens_internal]
    omega
  rw [encodedSubtreeWidth?_encode_internal _ _ hroot]
  exact subtreeWidth?_tokens_binary_right_internal left right Token.conj

theorem encodedSubtreeWidth?_encode_disj_right_internal
    (left right : BoolFormula) :
    encodedSubtreeWidth? (encode (.disj left right))
      (left.size + right.size - 1) = some right.size := by
  have hroot : left.size + right.size - 1 <
      (tokens (.disj left right)).length := by
    have hrightPositive : 0 < right.size := by
      cases right <;> simp [BoolFormula.size]
    simp only [tokens, List.length_append, List.length_singleton,
      length_tokens_internal]
    omega
  rw [encodedSubtreeWidth?_encode_internal _ _ hroot]
  exact subtreeWidth?_tokens_binary_right_internal left right Token.disj

end FormulaCode

end Complexity
