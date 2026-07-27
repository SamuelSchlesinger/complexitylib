/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Complexitylib.Models.TuringMachine.Subroutines.BinaryFor.Internal.Comparison
public import Complexitylib.Models.TuringMachine.Subroutines.BinaryFor.Internal.Loop

/-!
# Canonical binary count-up loops — internal proofs

Aggregation module for the comparison controller, certified loop induction,
all-prefix space bound, and transducer proof.
-/

@[expose] public section
