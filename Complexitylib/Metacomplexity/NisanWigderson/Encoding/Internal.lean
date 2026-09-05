/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Metacomplexity.NisanWigderson.Encoding.Defs

/-!
# Canonical encodings of Nisan--Wigderson designs -- proof internals
-/


public section

namespace Complexity

namespace NWDesign

theorem length_encode_internal
    {outputLength inputLength seedLength : ℕ}
    (design : NWDesign outputLength inputLength seedLength) :
    design.encode.length =
      outputLength * inputLength * Fin.bitWidth seedLength := by
  simp [encode]

theorem decodeCoordinate?_encode_internal
    {outputLength inputLength seedLength : ℕ}
    (design : NWDesign outputLength inputLength seedLength)
    (output : Fin outputLength) (input : Fin inputLength) :
    decodeCoordinate? outputLength inputLength seedLength design.encode
        output input =
      some (design.coordinates output input) := by
  simp [decodeCoordinate?, encode, coordinateBitTable]
  rw [← Fin.fromBits?_toBits (design.coordinates output input)]
  congr 1
  apply List.ext_get
  · simp
  · intro bit hfirst hsecond
    simp

theorem decodedCoordinates_encode_internal
    {outputLength inputLength seedLength : ℕ}
    (design : NWDesign outputLength inputLength seedLength)
    (hvalid : ∀ output input,
      (decodeCoordinate? outputLength inputLength seedLength design.encode
        output input).isSome)
    (output : Fin outputLength) (input : Fin inputLength) :
    decodedCoordinates outputLength inputLength seedLength design.encode
        hvalid output input =
      design.coordinates output input := by
  simp [decodedCoordinates, decodeCoordinate?_encode_internal]

theorem decode?_encode_internal
    {outputLength inputLength seedLength : ℕ}
    (design : NWDesign outputLength inputLength seedLength) :
    decode? outputLength inputLength seedLength design.encode = some design := by
  have hvalid : ∀ output input,
      (decodeCoordinate? outputLength inputLength seedLength design.encode
        output input).isSome := by
    intro output input
    simp [decodeCoordinate?_encode_internal]
  have hinjective : ∀ output, Function.Injective
      (decodedCoordinates outputLength inputLength seedLength design.encode
        hvalid output) := by
    intro output first second heq
    have hfirst :=
      decodedCoordinates_encode_internal design hvalid output first
    have hsecond :=
      decodedCoordinates_encode_internal design hvalid output second
    rw [hfirst, hsecond] at heq
    exact (design.coordinates output).injective heq
  unfold decode?
  rw [dite_eq_left (length_encode_internal design), dite_eq_left hvalid,
    dite_eq_left hinjective]
  congr 1
  cases design with
  | mk coordinates =>
      congr 1
      funext output
      apply Function.Embedding.ext
      intro input
      apply decodedCoordinates_encode_internal

theorem decode?_eq_none_of_length_ne_internal
    (outputLength inputLength seedLength : ℕ) (bits : List Bool)
    (hlength : bits.length ≠
      outputLength * inputLength * Fin.bitWidth seedLength) :
    decode? outputLength inputLength seedLength bits = none := by
  simp [decode?, hlength]

theorem encode_eq_of_decode?_eq_some_internal
    {outputLength inputLength seedLength : ℕ} (bits : List Bool)
    (design : NWDesign outputLength inputLength seedLength)
    (hdecode : decode? outputLength inputLength seedLength bits = some design) :
    design.encode = bits := by
  unfold decode? at hdecode
  split at hdecode
  · rename_i hlength
    split at hdecode
    · rename_i hvalid
      dsimp only at hdecode
      split at hdecode
      · rename_i hinjective
        cases hdecode
        apply List.ext_get
        · rw [length_encode_internal, hlength]
        · intro position hencoded hbits
          let flatPosition : Fin
              (outputLength * inputLength * Fin.bitWidth seedLength) :=
            ⟨position, by rw [← hlength]; exact hbits⟩
          let index :=
            (coordinateBitIndexEquiv outputLength inputLength seedLength).symm
              flatPosition
          have hcoordinate :
              decodeCoordinate? outputLength inputLength seedLength bits
                  index.1.1 index.1.2 =
                some ((decodeCoordinate? outputLength inputLength seedLength bits
                  index.1.1 index.1.2).get (hvalid index.1.1 index.1.2)) :=
            (Option.some_get (hvalid index.1.1 index.1.2)).symm
          simp only [decodeCoordinate?, dite_eq_left hlength] at hcoordinate
          have hcoordinateBits :=
            Fin.toBits_eq_of_fromBits?_eq_some hcoordinate
          simp [encode, coordinateBitTable, decodedCoordinates]
          simp only [decodeCoordinate?, dite_eq_left hlength]
          have hbit := congrArg (fun coordinateBits : List Bool =>
            coordinateBits[index.2.val]?) hcoordinateBits
          simp [index, flatPosition] at hbit
          exact hbit
      · simp at hdecode
    · simp at hdecode
  · simp at hdecode

theorem decode?_eq_some_iff_internal
    {outputLength inputLength seedLength : ℕ} (bits : List Bool)
    (design : NWDesign outputLength inputLength seedLength) :
    decode? outputLength inputLength seedLength bits = some design ↔
      bits = design.encode := by
  constructor
  · intro hdecode
    exact (encode_eq_of_decode?_eq_some_internal bits design hdecode).symm
  · rintro rfl
    exact decode?_encode_internal design

theorem encode_injective_internal
    {outputLength inputLength seedLength : ℕ} :
    Function.Injective
      (encode : NWDesign outputLength inputLength seedLength → List Bool) := by
  intro first second hencode
  have hdecode := congrArg
    (decode? outputLength inputLength seedLength) hencode
  simpa only [decode?_encode_internal, Option.some.injEq] using hdecode

theorem DecoderInstance.length_encode_internal (data : DecoderInstance) :
    data.encode.length =
      2 * (data.messageLength.size + data.inverseAccuracy.size +
        data.outputLength.size + data.inputLength.size + data.seedLength.size) +
        10 +
      data.outputLength * data.inputLength * Fin.bitWidth data.seedLength := by
  simp only [DecoderInstance.encode, pair_length,
    BinaryNatCode.length_encode]
  rw [NWDesign.length_encode_internal]
  omega

theorem DecoderInstance.decode?_encode_internal (data : DecoderInstance) :
    DecoderInstance.decode? data.encode = some data := by
  cases data
  simp [DecoderInstance.decode?, DecoderInstance.encode]
  rw [NWDesign.decode?_encode_internal]
  rfl

theorem DecoderInstance.decode?_eq_some_iff_internal
    (bits : List Bool) (data : DecoderInstance) :
    DecoderInstance.decode? bits = some data ↔ bits = data.encode := by
  cases data with
  | mk messageLength inverseAccuracy outputLength inputLength seedLength design =>
      simp [DecoderInstance.decode?, DecoderInstance.encode,
        Option.bind_eq_some_iff, unpair?_eq_some_iff,
        BinaryNatCode.decode?_eq_some_iff,
        NWDesign.decode?_eq_some_iff_internal]
      constructor
      · rintro ⟨decodedOutputLength, decodedInputLength, decodedSeedLength,
          decodedDesign, hbits, rfl, rfl, rfl, hdesign⟩
        cases hdesign
        exact hbits
      · intro hbits
        exact ⟨outputLength, inputLength, seedLength, design, hbits, rfl, rfl,
          rfl, HEq.rfl⟩

theorem DecoderInstance.encode_injective_internal :
    Function.Injective DecoderInstance.encode := by
  intro first second hencode
  have hdecode := congrArg DecoderInstance.decode? hencode
  simpa only [DecoderInstance.decode?_encode_internal, Option.some.injEq] using
    hdecode

end NWDesign

end Complexity
