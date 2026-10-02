/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module
public import Complexitylib.Encoding.Stack
public import Complexitylib.Classes.P.Pairing
public import Complexitylib.Classes.Containments.NPSPACESubsetPSPACE
public import Complexitylib.Classes.Containments.IPSubsetPSPACE

/-!
# Exact stack-encoding regression examples

Run with `lake build --wfail StackEncodingCheck`.
Only public modules are imported. The kernel checks the neutral API, empty
frames, ordering, unchanged total projections, and both consumers' transparent
constructor equations and quantitative state bounds. Return encodings stay
consumer-specific; this is an encoding check, not a recursive-traversal theorem.
-/

namespace Complexity
namespace StackEncodingCheck

example : StackEncoding.encode id ([] : List (List Bool)) = [] := rfl

example : StackEncoding.encode id [[]] = [false, true] := rfl

example : StackEncoding.encode id [[], [true]] =
    [false, true, true, true, false, true] := rfl

example : StackEncoding.encode id [[true], []] =
    [true, true, false, true, false, true] := rfl

example : StackEncoding.encode id [[]] ≠ [] := by decide

example (f : List Bool) (fs : List (List Bool)) :
    pairFst (StackEncoding.encode id (f :: fs)) = f :=
  StackEncoding.pairFst_encode_cons id f fs

example (f : List Bool) (fs : List (List Bool)) :
    pairSnd (StackEncoding.encode id (f :: fs)) = StackEncoding.encode id fs :=
  StackEncoding.pairSnd_encode_cons id f fs

example (fs : List (List Bool)) :
    (StackEncoding.encode id fs).length =
      fs.foldr (fun f n => 2 * f.length + 2 + n) 0 :=
  StackEncoding.length_encode id fs

example (fs : List (List Bool)) (h : ∀ f ∈ fs, f.length ≤ 0) :
    (StackEncoding.encode id fs).length ≤ fs.length * 2 :=
  StackEncoding.length_encode_le id fs 0 h

-- Existing FP operations apply directly to the raw push and projections.
example {f s : List Bool → List Bool} (hf : f ∈ FP) (hs : s ∈ FP) :
    (fun x => pair (f x) (s x)) ∈ FP := mem_FP_pair hf hs

example : pairFst ∈ FP := pairFst_mem_FP
example : pairSnd ∈ FP := pairSnd_mem_FP

-- Legacy names remain transparent, including their nil/cons equations.
example : encStack [] = [] := rfl
example (f : List Bool) (fs : List (List Bool)) :
    encStack (f :: fs) = pair f (encStack fs) := rfl
example (fs : List (List Bool)) : encStack fs = StackEncoding.encode id fs := rfl

example : IPM.encStk [] = [] := rfl
example (f : IPM.Frm) (fs : List IPM.Frm) :
    IPM.encStk (f :: fs) = pair (IPM.encFrm f) (IPM.encStk fs) := rfl
example (fs : List IPM.Frm) :
    IPM.encStk fs = StackEncoding.encode IPM.encFrm fs := rfl

example (fs : List (List Bool)) : encStack fs = [] ↔ fs = [] := encStack_eq_nil_iff fs
example (fs : List (List Bool)) :
    (encStack fs).length = fs.foldr (fun f n => 2 * f.length + 2 + n) 0 := by simp

-- Malformed-input behavior is still exactly that of the existing raw projections.
example (s : List Bool) : stkTop s = pairFst s := rfl
example (s : List Bool) : stkRest s = pairSnd s := rfl
example (s : List Bool) : IPM.sTop s = pairFst s := rfl
example (s : List Bool) : IPM.sRest s = pairSnd s := rfl

-- Empty data is allowed in stacks, but return absence retains its own conventions.
example : encOpt none = [] := rfl
example : encOpt (some false) = [false] := rfl
example : encOpt (some true) = [true] := rfl
example : IPM.encRet none = [] := rfl
example : IPM.encRet (some []) = IPM.encRet none := rfl
example : IPM.encRet (some [false]) ≠ [] := by decide

-- Preserve the exact quantitative interfaces used by the two containment proofs.
example {Lmax Wm : ℕ} (R : List Bool) (s : Sav.Sst) (h : Sav.StkSize Lmax Wm s.stk) :
    (encSst R s).length ≤
      2 * R.length + (Lmax + 1) * (2 * (2 * Lmax + 5 * Wm + 14) + 2) + 14 :=
  encSst_length_le R s h

example (P : IPM.Params) (D : ℕ) (s : IPM.Sst) (h : IPM.EncOk P D s)
    (hs : IPM.SizeOk P s.stk) : (IPM.encSst s).length ≤ IPM.stateBound P D :=
  IPM.encSst_length_le P D s h hs

end StackEncodingCheck
end Complexity
