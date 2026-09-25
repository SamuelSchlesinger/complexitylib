/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Counting.Basic
public import Complexitylib.Algebraic.LowerBound.Counting.Normalization
public import Complexitylib.Algebraic.LowerBound.Counting.Sharp
public import Complexitylib.Algebraic.LowerBound.Counting.Arity
public import Complexitylib.Algebraic.LowerBound.Counting.Coarse
public import Complexitylib.Algebraic.LowerBound.Counting.FinalTerm
public import Complexitylib.Algebraic.LowerBound.Counting.AlmostAll
public import Complexitylib.Algebraic.LowerBound.Counting.Shannon
public import Complexitylib.Algebraic.LowerBound.Counting.Depth

/-!
# Counting lower bounds

This umbrella exports the exact syntax census, normalization and factorial
relabeling, generic almost-all transfers, the closed-form Shannon theorem, and
the independent semantic-depth branch.
-/

@[expose] public section
