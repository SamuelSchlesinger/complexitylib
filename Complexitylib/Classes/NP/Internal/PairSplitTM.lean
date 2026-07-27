/-
Copyright (c) 2025 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Complexitylib.Models.TuringMachine.Subroutines.PairSplit

/-!
# Pair-split compatibility import

The pair codec and pair-splitting machine now live in neutral encoding and
Turing-machine subroutine modules. This file preserves the former import path
for downstream code; new code should import
`Complexitylib.Models.TuringMachine.Subroutines.PairSplit` directly.
-/

@[expose] public section
