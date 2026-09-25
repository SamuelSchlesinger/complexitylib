/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.MassProduction.SortingSemantics.Defs
public import Complexitylib.Algebraic.MassProduction.SortingSemantics.Internal

/-!
# Correctness of Batcher sorting networks

The ordered network sorts every finite input.  The keyed network moves whole
records, sorts their projected keys, and preserves the record multiset.
-/

@[expose] public section

namespace Algebraic
namespace MassProduction
namespace Sorting
namespace Semantics

/-- Batcher's ordered network sorts every input sequence. -/
theorem orderedBitonicSort_sorted [LinearOrder α]
    (depth : Nat) (ascending : Bool)
    (input : Fin (networkRecords depth) -> α) :
    SequenceSorted ascending
      (orderedBitonicSort depth ascending input) :=
  Internal.orderedBitonicSort_sorted depth ascending input

/-- The keyed network sorts records by their projected keys. -/
theorem keyedBitonicSort_sorted [LinearOrder κ]
    (key : α -> κ) (depth : Nat) (ascending : Bool)
    (input : Fin (networkRecords depth) -> α) :
    SequenceSorted ascending
      (fun output => key (keyedBitonicSort key depth ascending input output)) :=
  Internal.keyedBitonicSort_sorted key depth ascending input

/-- The keyed network preserves complete records up to permutation. -/
theorem keyedBitonicSort_permutes [LinearOrder κ]
    (key : α -> κ) (depth : Nat) (ascending : Bool)
    (input : Fin (networkRecords depth) -> α) :
    SequencePermutes (keyedBitonicSort key depth ascending input) input :=
  Internal.keyedBitonicSort_permutes key depth ascending input

end Semantics
end Sorting
end MassProduction
end Algebraic
