/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module
public import Complexitylib.Circuits.DepthThree.LowerBound.Internal.LanguageBitLoopInvariants

/-!
# Unrestricted depth-three lower bound: language bit horner loop

Adapted from OpenAI's formalization at revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
Source: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/DepthThree/LanguageBitHornerLoop.lean

Imports, namespaces, module visibility, documentation, and formatting are adapted
for complexitylib. The source theorem statements and mathematical proofs are retained.
-/

@[expose] public section

namespace Complexity

universe uDepth1

namespace DepthThreeLowerBound

/-- One multiply-and-add step of Horner evaluation. -/
def hornerStep (r : ℕ) (p h b a : List Bool) : List Bool :=
  List.zipWith Bool.xor b (multiplyBitLists r p h a)

theorem hornerStep_length (r : ℕ) (p h b a : List Bool) (hb : b.length = r) :
    (hornerStep r p h b a).length = r := by
  simp only [hornerStep, List.length_zipWith, multiplyBitLists_length, hb, min_self]

theorem hornerStep_eq_word (r : ℕ) (p h b a : List Bool) (hb : b.length = r) :
    hornerStep r p h b a =
      wordList (wordXor (listWord r b)
        (wordMulMod (listWord r p) (listWord r h) (listWord r a))) := by
  have hx (u v : BitWord r) :
      List.zipWith Bool.xor (wordList u) (wordList v) = wordList (wordXor u v) := by
    apply List.ext_getElem
    · simp only [wordList_length, List.length_zipWith, min_self]
    · intro i hi hj
      simp only [wordList, wordXor, List.getElem_zipWith, List.getElem_ofFn]
  have heq := hx (listWord r b)
    (wordMulMod (listWord r p) (listWord r h) (listWord r a))
  simpa only [wordList_listWord b hb, hornerStep, multiplyBitLists] using heq

/-- Continue Horner evaluation from an initial accumulator. -/
def hornerFrom (r : ℕ) (p h : List Bool) (bs : List (List Bool))
    (a : List Bool) : List Bool :=
  bs.foldr (hornerStep r p h) a

@[simp] theorem hornerFrom_nil (r : ℕ) (p h a : List Bool) :
    hornerFrom r p h [] a = a := rfl

theorem hornerFrom_cons (r : ℕ) (p h b : List Bool) (bs : List (List Bool))
    (a : List Bool) :
    hornerFrom r p h (b :: bs) a = hornerStep r p h b (hornerFrom r p h bs a) := rfl

theorem hornerFrom_append (r : ℕ) (p h : List Bool)
    (bs cs : List (List Bool)) (a : List Bool) :
    hornerFrom r p h (bs ++ cs) a =
      hornerFrom r p h bs (hornerFrom r p h cs a) := by
  simp only [hornerFrom, List.foldr_append]

theorem hornerFrom_append_singleton (r : ℕ) (p h : List Bool)
    (bs : List (List Bool)) (b a : List Bool) :
    hornerFrom r p h (bs ++ [b]) a =
      hornerFrom r p h bs (hornerStep r p h b a) := by
  rw [hornerFrom_append, hornerFrom_cons, hornerFrom_nil]

theorem hornerFrom_length (r : ℕ) (p h : List Bool)
    (bs : List (List Bool)) (a : List Bool) (ha : a.length = r)
    (hbs : ∀ b ∈ bs, b.length = r) :
    (hornerFrom r p h bs a).length = r := by
  cases bs with
  | nil => exact ha
  | cons b bs =>
      rw [hornerFrom_cons]
      exact hornerStep_length r p h b _ (hbs b (by simp))

theorem hornerFrom_zero_eq_hornerBitLists (r : ℕ) (p h : List Bool)
    (bs : List (List Bool)) (hbs : ∀ b ∈ bs, b.length = r) :
    hornerFrom r p h bs (List.replicate r false) = hornerBitLists r p h bs := by
  revert hbs
  induction bs with
  | nil =>
      intro hbs
      simp only [hornerFrom_nil, hornerBitLists_nil, wordList, List.ofFn_const]
  | cons b bs ih =>
      intro hbs
      have hb : b.length = r := hbs b (by simp)
      have htail : ∀ c ∈ bs, c.length = r :=
        fun c hc => hbs c (List.mem_cons_of_mem b hc)
      rw [hornerFrom_cons, ih htail, hornerStep_eq_word r p h b _ hb,
        hornerBitLists_cons]

theorem block_flatten_length {α : Type uDepth1} (r : ℕ) (bs : List (List α))
    (hbs : ∀ b ∈ bs, b.length = r) : bs.flatten.length = bs.length * r := by
  revert hbs
  induction bs with
  | nil => intro hbs; simp
  | cons b bs ih =>
      intro hbs
      have hb : b.length = r := hbs b (by simp)
      have htail : ∀ c ∈ bs, c.length = r :=
        fun c hc => hbs c (List.mem_cons_of_mem b hc)
      simp only [List.flatten_cons, List.length_append, List.length_cons, hb, ih htail]
      simp only [Nat.add_mul, Nat.one_mul, Nat.add_comm]

end DepthThreeLowerBound

end Complexity
