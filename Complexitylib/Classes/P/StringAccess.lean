/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Classes.P.Unary
import Complexitylib.Classes.P.Bridge
import Complexitylib.Classes.P.Cobham.Internal
import Complexitylib.Classes.P.StringAccess.Internal

/-!
# Polynomial-time string access and slicing

An `FP` string can be read at a polynomial-time unary position, with false past
its end. Its leading run of true bits can also be measured in polynomial time,
even without a false terminator. Taking or dropping a prefix of polynomial-time
unary length preserves `FP`. These are machine-level consequences of the existing
Cobham constructions, useful for encoded structures and certificates.
-/

public section

namespace Complexity

/-- Taking a prefix of polynomial-time unary length preserves polynomial time. -/
theorem take_mem_FP {bits : List Bool → List Bool} {n : List Bool → Nat}
    (hbits : bits ∈ FP) (hn : UnaryFn n) :
    (fun z => (bits z).take (n z)) ∈ FP := by
  simpa only [List.length_replicate] using Cobham.takeLenFn_mem_FP hn.mem_FP hbits

/-- Dropping a prefix of polynomial-time unary length preserves polynomial time. -/
theorem drop_mem_FP {bits : List Bool → List Bool} {n : List Bool → Nat}
    (hbits : bits ∈ FP) (hn : UnaryFn n) :
    (fun z => (bits z).drop (n z)) ∈ FP := by
  simpa only [List.length_replicate] using dropLenFn_mem_FP hn.mem_FP hbits

/-- Reading one bit at a polynomial-time position is polynomial-time, with false past the end. -/
theorem getBit_mem_FP {bits : List Bool → List Bool} {i : List Bool → Nat}
    (hbits : bits ∈ FP) (hi : UnaryFn i) :
    (fun z => [(bits z)[i z]?.getD false]) ∈ FP := by
  refine mem_FP_of_eq (binFn_mem_FP Cobham.bitAtFn hi.mem_FP hbits) fun z => ?_
  rw [bitAt_eq, List.length_replicate, bitOf_eq_getElem?_internal]

/-- Testing a selected input bit is a polynomial-time predicate. -/
theorem FPPred.getBit {bits : List Bool → List Bool} {i : List Bool → Nat}
    (hbits : bits ∈ FP) (hi : UnaryFn i) :
    FPPred fun z => (bits z)[i z]?.getD false = true :=
  FPPred.of_flag (getBit_mem_FP hbits hi)

/-- The length of the leading true run of an `FP` string is a polynomial-time number. -/
theorem UnaryFn.leadingTrueLength {bits : List Bool → List Bool} (hbits : bits ∈ FP) :
    UnaryFn fun z => ((bits z).takeWhile id).length :=
  (UnaryFn.length (binFn_mem_FP (g := fun r bits => runTrue bits r.length)
    (Cobham.runTrueFn (Cobham.proj 0) (Cobham.proj 1)) hbits hbits)).of_eq
      fun z => runTrue_length_takeWhile_internal (bits z)

end Complexity
