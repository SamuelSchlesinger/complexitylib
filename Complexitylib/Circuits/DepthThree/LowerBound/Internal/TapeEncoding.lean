/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module
public import Mathlib.Algebra.BigOperators.Group.List.Basic
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Data.Fintype.Sum
public import Mathlib.Data.List.FinRange
public import Mathlib.Tactic.DeriveFintype

/-!
# Unrestricted depth-three lower bound: tape encoding

Adapted from OpenAI's formalization at revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
Source: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/DepthThree/TapeEncoding.lean

Imports, namespaces, module visibility, documentation, and formatting are adapted
for complexitylib. The source theorem statements and mathematical proofs are retained.
-/

@[expose] public section

namespace Complexity

namespace DepthThreeLowerBound

/-- The 32 registers used by the explicit multitape evaluator. -/
abbrev TapeRegister := Fin 32

namespace TapeRegister

/-- Register 0, reserved for input. -/
abbrev input : TapeRegister := 0
/-- Register 1, reserved for length. -/
abbrev length : TapeRegister := 1
/-- Register 2, reserved for data length. -/
abbrev dataLength : TapeRegister := 2
/-- Register 3, reserved for ring degree. -/
abbrev ringDegree : TapeRegister := 3
/-- Register 4, reserved for coeff count. -/
abbrev coeffCount : TapeRegister := 4
/-- Register 5, reserved for candidate. -/
abbrev candidate : TapeRegister := 5
/-- Register 6, reserved for power target. -/
abbrev powerTarget : TapeRegister := 6
/-- Register 7, reserved for power scratch. -/
abbrev powerScratch : TapeRegister := 7
/-- Register 8, reserved for required length. -/
abbrev requiredLength : TapeRegister := 8
/-- Register 9, reserved for loop0. -/
abbrev loop0 : TapeRegister := 9
/-- Register 10, reserved for loop1. -/
abbrev loop1 : TapeRegister := 10
/-- Register 11, reserved for loop2. -/
abbrev loop2 : TapeRegister := 11
/-- Register 12, reserved for loop3. -/
abbrev loop3 : TapeRegister := 12
/-- Register 13, reserved for loop4. -/
abbrev loop4 : TapeRegister := 13
/-- Register 14, reserved for loop5. -/
abbrev loop5 : TapeRegister := 14
/-- Register 15, reserved for data bits. -/
abbrev dataBits : TapeRegister := 15
/-- Register 16, reserved for key bits. -/
abbrev keyBits : TapeRegister := 16
/-- Register 17, reserved for poly bits. -/
abbrev polyBits : TapeRegister := 17
/-- Register 18, reserved for coeff bits. -/
abbrev coeffBits : TapeRegister := 18
/-- Register 19, reserved for hash bits. -/
abbrev hashBits : TapeRegister := 19
/-- Register 20, reserved for accum bits. -/
abbrev accumBits : TapeRegister := 20
/-- Register 21, reserved for product bits. -/
abbrev productBits : TapeRegister := 21
/-- Register 22, reserved for index a. -/
abbrev indexA : TapeRegister := 22
/-- Register 23, reserved for index b. -/
abbrev indexB : TapeRegister := 23
/-- Register 24, reserved for index c. -/
abbrev indexC : TapeRegister := 24
/-- Register 25, reserved for scratch a. -/
abbrev scratchA : TapeRegister := 25
/-- Register 26, reserved for scratch b. -/
abbrev scratchB : TapeRegister := 26
/-- Register 27, reserved for scratch c. -/
abbrev scratchC : TapeRegister := 27
/-- Register 28, reserved for saved count. -/
abbrev savedCount : TapeRegister := 28
/-- Register 29, reserved for temp0. -/
abbrev temp0 : TapeRegister := 29
/-- Register 30, reserved for temp1. -/
abbrev temp1 : TapeRegister := 30
/-- Register 31, reserved for temp2. -/
abbrev temp2 : TapeRegister := 31

end TapeRegister

/-- Tape atoms for blank cells, boundaries, register delimiters, and bits. -/
inductive TapeAtom where
  | blank
  | home
  | delimiter (r : TapeRegister)
  | bit (b : Bool)
  | endMark
  deriving DecidableEq, Fintype, Inhabited

/-- The four marker positions carried by each tape symbol. -/
abbrev TapeMark := Fin 4

/-- A tape atom together with four Boolean marker flags. -/
abbrev TapeSymbol := TapeAtom × (TapeMark → Bool)

/-- A tape atom with all marker flags cleared. -/
def cleanAtom (a : TapeAtom) : TapeSymbol := (a, fun _ => false)

/-- The blank tape atom with no marker flags. -/
def blankSymbol : TapeSymbol := cleanAtom .blank

/-- Encode an input bit with no marker flags. -/
def rawInputSymbol (b : Bool) : TapeSymbol := cleanAtom (.bit b)

@[simp] theorem cleanAtom_atom (a : TapeAtom) : (cleanAtom a).1 = a := rfl

@[simp] theorem cleanAtom_mark (a : TapeAtom) (m : TapeMark) :
    (cleanAtom a).2 m = false := rfl

@[simp] theorem default_tapeSymbol : (default : TapeSymbol) = blankSymbol := rfl

theorem cleanAtom_injective : Function.Injective cleanAtom := by
  intro a b h
  exact congrArg Prod.fst h

theorem rawInputSymbol_injective : Function.Injective rawInputSymbol := by
  intro a b h
  have hab : TapeAtom.bit a = TapeAtom.bit b := congrArg Prod.fst h
  cases hab
  rfl

@[simp] theorem rawInputSymbol_ne_blank (b : Bool) : rawInputSymbol b ≠ blankSymbol := by
  intro h
  have hab : TapeAtom.bit b = TapeAtom.blank := congrArg Prod.fst h
  cases hab

/-- A bit-list value for each register. -/
abbrev TapeStore := TapeRegister → List Bool

/-- Enumerate all 32 tape registers. -/
def tapeRegisters : List TapeRegister := List.ofFn id

@[simp] theorem tapeRegisters_length : tapeRegisters.length = 32 := by
  simp [tapeRegisters]

@[simp] theorem mem_tapeRegisters (r : TapeRegister) : r ∈ tapeRegisters := by
  change r ∈ List.ofFn (fun i : TapeRegister => i)
  exact List.mem_ofFn.mpr ⟨r, rfl⟩

theorem tapeRegisters_nodup : tapeRegisters.Nodup := by
  exact List.nodup_ofFn_ofInjective (fun _ _ h => h)

/-- Encode input bits as unmarked tape symbols. -/
def encodeInput (bits : List Bool) : List TapeSymbol := bits.map rawInputSymbol

@[simp] theorem encodeInput_length (bits : List Bool) :
    (encodeInput bits).length = bits.length := by
  simp [encodeInput]

/-- Encode one register's bit-list block with its delimiter. -/
def encodeBlock (σ : TapeStore) (r : TapeRegister) : List TapeSymbol :=
  cleanAtom (.delimiter r) :: encodeInput (σ r)

/-- Concatenate the encoded blocks of the tape store. -/
def encodeStore (σ : TapeStore) : List TapeSymbol :=
  cleanAtom .home :: (tapeRegisters.flatMap (encodeBlock σ) ++ [cleanAtom .endMark])

@[simp] theorem encodeBlock_length (σ : TapeStore) (r : TapeRegister) :
    (encodeBlock σ r).length = (σ r).length + 1 := by
  simp [encodeBlock]

theorem encodeBlocks_length (σ : TapeStore) (rs : List TapeRegister) :
    (rs.flatMap (encodeBlock σ)).length =
      rs.length + (rs.map (fun r => (σ r).length)).sum := by
  induction rs with
  | nil => simp
  | cons r rs ih =>
      simp [ih, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

theorem encodeStore_length (σ : TapeStore) :
    (encodeStore σ).length =
      34 + (tapeRegisters.map (fun r => (σ r).length)).sum := by
  simp [encodeStore, Nat.add_comm]
  simp only [← Nat.add_assoc]

@[simp] theorem encodeStore_head? (σ : TapeStore) :
    (encodeStore σ).head? = some (cleanAtom .home) := rfl

@[simp] theorem encodeStore_ne_nil (σ : TapeStore) : encodeStore σ ≠ [] := by
  simp [encodeStore]

theorem encodeInput_symbols {bits : List Bool} {s : TapeSymbol}
    (hs : s ∈ encodeInput bits) :
    (∃ b : Bool, s.1 = .bit b) ∧ ∀ m, s.2 m = false := by
  rcases List.mem_map.mp hs with ⟨b, _, rfl⟩
  exact ⟨⟨b, rfl⟩, fun _ => rfl⟩

theorem encodeBlock_symbols {σ : TapeStore} {r : TapeRegister} {s : TapeSymbol}
    (hs : s ∈ encodeBlock σ r) :
    s.1 ≠ .blank ∧ s.1 ≠ .home ∧ s.1 ≠ .endMark ∧ ∀ m, s.2 m = false := by
  rcases List.mem_cons.mp hs with hs | hs
  · subst s
    simp [cleanAtom]
  · obtain ⟨⟨b, hb⟩, hm⟩ := encodeInput_symbols hs
    exact ⟨by simp [hb], by simp [hb], by simp [hb], hm⟩

theorem encodeBlocks_symbols {σ : TapeStore} {rs : List TapeRegister} {s : TapeSymbol}
    (hs : s ∈ rs.flatMap (encodeBlock σ)) :
    s.1 ≠ .blank ∧ s.1 ≠ .home ∧ s.1 ≠ .endMark ∧ ∀ m, s.2 m = false := by
  rcases List.mem_flatMap.mp hs with ⟨r, _, hr⟩
  exact encodeBlock_symbols hr

theorem encodeStore_no_blank {σ : TapeStore} {s : TapeSymbol}
    (hs : s ∈ encodeStore σ) : s.1 ≠ .blank := by
  rcases List.mem_cons.mp hs with hs | hs
  · subst s
    simp [cleanAtom]
  · rcases List.mem_append.mp hs with hs | hs
    · exact (encodeBlocks_symbols hs).1
    · have hs' : s = cleanAtom .endMark := List.mem_singleton.mp hs
      subst s
      simp [cleanAtom]

theorem encodeStore_clean {σ : TapeStore} {s : TapeSymbol}
    (hs : s ∈ encodeStore σ) (m : TapeMark) : s.2 m = false := by
  rcases List.mem_cons.mp hs with hs | hs
  · subst s
    rfl
  · rcases List.mem_append.mp hs with hs | hs
    · exact (encodeBlocks_symbols hs).2.2.2 m
    · have hs' : s = cleanAtom .endMark := List.mem_singleton.mp hs
      subst s
      rfl

theorem encodeStore_tail_no_home {σ : TapeStore} {s : TapeSymbol}
    (hs : s ∈ (encodeStore σ).tail) : s.1 ≠ .home := by
  change s ∈ tapeRegisters.flatMap (encodeBlock σ) ++ [cleanAtom .endMark] at hs
  rcases List.mem_append.mp hs with hs | hs
  · exact (encodeBlocks_symbols hs).2.1
  · have hs' : s = cleanAtom .endMark := List.mem_singleton.mp hs
    subst s
    simp [cleanAtom]

end DepthThreeLowerBound

end Complexity
