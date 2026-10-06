/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Complexitylib.Circuits.KCNF.Basic
import Complexitylib.Circuits.KCNF.Internal.Sparsification.Step

/-!
# The sparsification lemma

The sparsification lemma of Impagliazzo, Paturi and Zane ("Which problems have strongly
exponential complexity?", JCSS 63, 2001), with the proof of Calabro, Impagliazzo and Paturi
("A duality between clause width and clause density for SAT", CCC 2006).
-/
