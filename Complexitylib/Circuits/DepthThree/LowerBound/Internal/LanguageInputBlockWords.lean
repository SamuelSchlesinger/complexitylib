/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module
public import Complexitylib.Circuits.DepthThree.LowerBound.Internal.LanguageInputBlockLists
public import Complexitylib.Circuits.DepthThree.LowerBound.Internal.LanguageBitHashUpdates
public import Complexitylib.Circuits.DepthThree.LowerBound.Internal.LanguageBitHornerLoop

/-!
# Unrestricted depth-three lower bound: language input block words

Adapted from OpenAI's formalization at revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
Source: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/DepthThree/LanguageInputBlockWords.lean

Imports, namespaces, module visibility, documentation, and formatting are adapted
for complexitylib. The source theorem statements and mathematical proofs are retained.
-/

@[expose] public section

namespace Complexity

namespace DepthThreeLowerBound

private theorem list_eq_ofFn_of_getD {n : ℕ} (xs : List Bool) (f : Fin n → Bool)
    (hlen : xs.length = n) (hread : ∀ i, xs.getD i.val false = f i) :
    xs = List.ofFn f := by
  have heq : listWord n xs = f := by
    funext i
    exact hread i
  exact (wordList_listWord xs hlen).symm.trans (congrArg wordList heq)

theorem inputBlockData_data_length {w : List Bool} (hfit : InputFits w) :
    (inputBlockData w .data).length = (decodeInput w).dataSize :=
  inputBlockData_length hfit .data

theorem inputBlockData_hash_length {w : List Bool} (hfit : InputFits w) :
    (inputBlockData w .hash).length =
      (decodeInput w).dataSize + (decodeInput w).ringDegree - 1 :=
  inputBlockData_length hfit .hash

theorem inputBlockData_polynomial_length {w : List Bool} (hfit : InputFits w) :
    (inputBlockData w .polynomial).length = (decodeInput w).ringDegree :=
  inputBlockData_length hfit .polynomial

theorem inputBlockData_coefficients_length {w : List Bool} (hfit : InputFits w) :
    (inputBlockData w .coefficients).length =
      (decodeInput w).coefficientCount * (decodeInput w).ringDegree :=
  inputBlockData_length hfit .coefficients

theorem decoded_ringDegree_ne_zero {w : List Bool} (hfit : InputFits w) :
    (decodeInput w).ringDegree ≠ 0 :=
  Nat.ne_of_gt (decoded_ringDegree_pos hfit)

theorem inputBlockData_data_eq_ofFn {w : List Bool} (hfit : InputFits w) :
    inputBlockData w .data = List.ofFn (decodeInput w).data :=
  list_eq_ofFn_of_getD _ _ (inputBlockData_data_length hfit)
    (inputBlockData_data w)

theorem inputBlockData_hash_eq_ofFn {w : List Bool} (hfit : InputFits w) :
    inputBlockData w .hash = List.ofFn (decodeInput w).hashSeed :=
  list_eq_ofFn_of_getD _ _ (inputBlockData_hash_length hfit)
    (inputBlockData_hash w)

theorem inputBlockData_polynomial_eq_ofFn {w : List Bool} (hfit : InputFits w) :
    inputBlockData w .polynomial = List.ofFn (decodeInput w).polynomial :=
  list_eq_ofFn_of_getD _ _ (inputBlockData_polynomial_length hfit)
    (inputBlockData_polynomial w)

/-- The list of coefficient blocks extracted from the input. -/
def decodedCoefficientBlocks (w : List Bool) : List (List Bool) :=
  List.ofFn fun j => List.ofFn ((decodeInput w).coefficients j)

@[simp] theorem decodedCoefficientBlocks_length (w : List Bool) :
    (decodedCoefficientBlocks w).length = (decodeInput w).coefficientCount := by
  simp only [decodedCoefficientBlocks, List.length_ofFn]

theorem decodedCoefficientBlocks_row_length (w : List Bool) :
    ∀ b ∈ decodedCoefficientBlocks w, b.length = (decodeInput w).ringDegree := by
  intro b hb
  obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hb
  exact List.length_ofFn

theorem decodedCoefficientBlocks_flatten_length (w : List Bool) :
    (decodedCoefficientBlocks w).flatten.length =
      (decodeInput w).coefficientCount * (decodeInput w).ringDegree := by
  rw [block_flatten_length _ _ (decodedCoefficientBlocks_row_length w),
    decodedCoefficientBlocks_length]

theorem inputBlockData_coefficients_eq_flatten {w : List Bool} (hfit : InputFits w) :
    inputBlockData w .coefficients = (decodedCoefficientBlocks w).flatten := by
  have heq : inputBlockData w .coefficients = List.ofFn
      (fun i : Fin ((decodeInput w).coefficientCount * (decodeInput w).ringDegree) =>
        (inputBlockData w .coefficients).getD i.val false) :=
    list_eq_ofFn_of_getD _ _ (inputBlockData_coefficients_length hfit) (fun _ => rfl)
  rw [heq, List.ofFn_mul]
  apply congrArg List.flatten
  apply congrArg List.ofFn
  funext j
  apply congrArg List.ofFn
  funext i
  exact inputBlockData_coefficients w j i

theorem hornerBitLists_ofFn {r t : ℕ} (p h : BitWord r) (b : Fin t → BitWord r) :
    hornerBitLists r (List.ofFn p) (List.ofFn h) (List.ofFn fun j => List.ofFn (b j)) =
      List.ofFn (wordHorner p h t b) := by
  have hp : listWord r (List.ofFn p) = p := listWord_wordList p
  have hh : listWord r (List.ofFn h) = h := listWord_wordList h
  have hb : (fun j : Fin t => listWord r
      ((List.ofFn fun j => List.ofFn (b j)).getD j.val [])) = b := by
    funext j
    simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn, dite_eq_left j.isLt,
      Option.getD_some]
    exact listWord_wordList (b j)
  unfold hornerBitLists
  rw [List.length_ofFn]
  simp only [hp, hh, hb]
  rfl

theorem hashByUpdates_inputBlocks {w : List Bool} (hfit : InputFits w) :
    hashByUpdates (decodeInput w).ringDegree
        (inputBlockData w .hash) (inputBlockData w .data) =
      List.ofFn (wordHash (decodeInput w).hashSeed (decodeInput w).data) := by
  rw [inputBlockData_hash_eq_ofFn hfit, inputBlockData_data_eq_ofFn hfit]
  exact hashByUpdates_ofFn_eq _ _

theorem hornerBitLists_inputBlocks {w : List Bool} (hfit : InputFits w) :
    hornerBitLists (decodeInput w).ringDegree (inputBlockData w .polynomial)
        (hashByUpdates (decodeInput w).ringDegree
          (inputBlockData w .hash) (inputBlockData w .data))
        (decodedCoefficientBlocks w) =
      List.ofFn (decodeInput w).evaluationBits := by
  rw [inputBlockData_polynomial_eq_ofFn hfit, hashByUpdates_inputBlocks hfit]
  exact hornerBitLists_ofFn _ _ _

theorem hornerFrom_inputBlocks {w : List Bool} (hfit : InputFits w) :
    hornerFrom (decodeInput w).ringDegree (inputBlockData w .polynomial)
        (hashByUpdates (decodeInput w).ringDegree
          (inputBlockData w .hash) (inputBlockData w .data))
        (decodedCoefficientBlocks w)
        (List.replicate (decodeInput w).ringDegree false) =
      List.ofFn (decodeInput w).evaluationBits := by
  rw [hornerFrom_zero_eq_hornerBitLists _ _ _ _ (decodedCoefficientBlocks_row_length w)]
  exact hornerBitLists_inputBlocks hfit

theorem evaluateBits_eq_final_bit {w : List Bool} (hfit : InputFits w) :
    (decodeInput w).evaluateBits =
      !((hornerBitLists (decodeInput w).ringDegree (inputBlockData w .polynomial)
        (hashByUpdates (decodeInput w).ringDegree
          (inputBlockData w .hash) (inputBlockData w .data))
        (decodedCoefficientBlocks w)).getD 0 false) := by
  rw [hornerBitLists_inputBlocks hfit]
  change Bool.not (wordGet (decodeInput w).evaluationBits 0) =
    Bool.not ((wordList (decodeInput w).evaluationBits).getD 0 false)
  rw [wordList_getD]

theorem language_eq_final_bit {w : List Bool} (hfit : InputFits w) :
    language w =
      !((hornerBitLists (decodeInput w).ringDegree (inputBlockData w .polynomial)
        (hashByUpdates (decodeInput w).ringDegree
          (inputBlockData w .hash) (inputBlockData w .data))
        (decodedCoefficientBlocks w)).getD 0 false) := by
  simpa only [language, parseInput_of_fits hfit] using
    ((ParsedInput.evaluateBits_eq (decodeInput w)).symm.trans
      (evaluateBits_eq_final_bit hfit))

end DepthThreeLowerBound

end Complexity
