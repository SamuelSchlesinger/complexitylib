/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Complexitylib.SAT.Tseitin.Machine.Defs
import Std.Tactic.BVDecide.Normalize.Prop

/-!
# Correctness of the pure Tseitin input validator

This proof-only module identifies the finite-state validity scan used by the
CNF-to-3CNF reduction machine with the existing executable CNF decoder. The
argument first characterizes accepted token prefixes as canonical `CNF.tokens`
streams, then transports that characterization across the concrete two-bit
tokenization.
-/

@[expose] public section

namespace Complexity

namespace SAT

namespace ThreeSAT

namespace Machine

/-- Acceptance for a completed token scan, before reintroducing the bit-pair
state carried by `ValidationState`. -/
private def ValidationMode.acceptsEnd : ValidationMode → Bool
  | .between false => true
  | _ => false

/-- A token prefix represents the partial CNF denoted by its validator mode.
The rejecting mode needs no representation invariant because it is absorbing. -/
private def Represents : List EncToken → ValidationMode → Prop
  | toks, .between false => ∃ φ : CNF, toks = φ.tokens
  | toks, .between true =>
      ∃ (φ : CNF) (c : Clause), c ≠ [] ∧ toks = φ.tokens ++ c.tokens
  | toks, .literal false =>
      ∃ (φ : CNF) (sign : Bool) (body : List Bool),
        (∀ b ∈ body, b = true) ∧
          toks = φ.tokens ++ (sign :: body).map EncToken.bit
  | toks, .literal true =>
      ∃ (φ : CNF) (c : Clause) (sign : Bool) (body : List Bool),
        c ≠ [] ∧ (∀ b ∈ body, b = true) ∧
          toks = φ.tokens ++ c.tokens ++ (sign :: body).map EncToken.bit
  | _, .reject => True

/-- A list consisting only of `true` is its canonical unary representation. -/
private theorem eq_replicate_true {body : List Bool}
    (hbody : ∀ b ∈ body, b = true) :
    body = List.replicate body.length true := by
  rw [List.eq_replicate_length]
  intro b hb
  exact hbody b hb

/-- Appending one token preserves the representation invariant for the mode
reached by that token. -/
private theorem represents_step {toks : List EncToken} {mode : ValidationMode}
    (hrep : Represents toks mode) (tok : EncToken) :
    Represents (toks ++ [tok]) (mode.step tok) := by
  cases mode with
  | between seen =>
      cases seen with
      | false =>
          rcases hrep with ⟨φ, rfl⟩
          cases tok with
          | bit b =>
              refine ⟨φ, b, [], by simp, ?_⟩
              simp
          | litSep => trivial
          | clauseSep =>
              refine ⟨φ ++ [[]], ?_⟩
              calc
                φ.tokens ++ [EncToken.clauseSep] =
                    φ.tokens ++ CNF.tokens [[]] := by rfl
                _ = CNF.tokens (φ ++ [[]]) := (CNF.tokens_append φ [[]]).symm
      | true =>
          rcases hrep with ⟨φ, c, hc, rfl⟩
          cases tok with
          | bit b =>
              refine ⟨φ, c, b, [], hc, by simp, ?_⟩
              simp [List.append_assoc]
          | litSep => trivial
          | clauseSep =>
              refine ⟨φ ++ [c], ?_⟩
              calc
                (φ.tokens ++ c.tokens) ++ [EncToken.clauseSep] =
                    φ.tokens ++ (c.tokens ++ [EncToken.clauseSep]) :=
                  List.append_assoc _ _ _
                _ = φ.tokens ++ CNF.tokens [c] := by
                  simp only [CNF.tokens, List.append_nil]
                _ = CNF.tokens (φ ++ [c]) := (CNF.tokens_append φ [c]).symm
  | literal seen =>
      cases seen with
      | false =>
          rcases hrep with ⟨φ, sign, body, hbody, rfl⟩
          cases tok with
          | bit b =>
              cases b with
              | false => trivial
              | true =>
                  refine ⟨φ, sign, body ++ [true], ?_, ?_⟩
                  · intro b hb
                    simp only [List.mem_append, List.mem_singleton] at hb
                    rcases hb with hb | rfl
                    · exact hbody b hb
                    · rfl
                  · simp [List.map_append, List.append_assoc]
          | litSep =>
              let ℓ : Lit := ⟨sign, body.length⟩
              have hbody' := eq_replicate_true hbody
              have hraw : (sign :: body).map EncToken.bit = ℓ.rawTokens := by
                simp only [Lit.rawTokens, Lit.encodeRaw, Unary.encode, ℓ]
                rw [hbody']
                simp only [List.length_replicate]
              refine ⟨φ, [ℓ], by simp, ?_⟩
              rw [hraw]
              simpa only [Clause.tokens, List.append_nil] using
                List.append_assoc φ.tokens ℓ.rawTokens [EncToken.litSep]
          | clauseSep => trivial
      | true =>
          rcases hrep with ⟨φ, c, sign, body, hc, hbody, rfl⟩
          cases tok with
          | bit b =>
              cases b with
              | false => trivial
              | true =>
                  refine ⟨φ, c, sign, body ++ [true], hc, ?_, ?_⟩
                  · intro b hb
                    simp only [List.mem_append, List.mem_singleton] at hb
                    rcases hb with hb | rfl
                    · exact hbody b hb
                    · rfl
                  · simp [List.map_append, List.append_assoc]
          | litSep =>
              let ℓ : Lit := ⟨sign, body.length⟩
              have hbody' := eq_replicate_true hbody
              have hraw : (sign :: body).map EncToken.bit = ℓ.rawTokens := by
                simp only [Lit.rawTokens, Lit.encodeRaw, Unary.encode, ℓ]
                rw [hbody']
                simp only [List.length_replicate]
              refine ⟨φ, c ++ [ℓ], by simp [hc], ?_⟩
              rw [hraw, Clause.tokens_append]
              simp only [Clause.tokens, List.append_nil, List.append_assoc]
          | clauseSep => trivial
  | reject => trivial

/-- Every token prefix has the representation prescribed by the mode reached
from the initial token state. -/
private theorem represents_foldl (toks : List EncToken) :
    Represents toks (toks.foldl ValidationMode.step (.between false)) := by
  induction toks using List.reverseRecOn with
  | nil => exact ⟨[], rfl⟩
  | append_singleton toks tok ih =>
      simpa [List.foldl_append] using represents_step ih tok

/-- An accepted token stream is the canonical token encoding of some CNF. -/
private theorem exists_cnf_of_tokens_accepts (toks : List EncToken)
    (haccept : ValidationMode.acceptsEnd
      (toks.foldl ValidationMode.step (.between false)) = true) :
    ∃ φ : CNF, toks = φ.tokens := by
  have hrep := represents_foldl toks
  generalize hmode : toks.foldl ValidationMode.step (.between false) = mode at haccept hrep
  cases mode with
  | between seen =>
      cases seen with
      | false => simpa [Represents] using hrep
      | true => simp [ValidationMode.acceptsEnd] at haccept
  | literal seen => simp [ValidationMode.acceptsEnd] at haccept
  | reject => simp [ValidationMode.acceptsEnd] at haccept

/-- Bit scanning agrees with token scanning; tokenization failure is precisely
the odd-length case, which cannot be accepted by `ValidationState`. -/
private theorem accepts_fold_eq_tokenize (z : List Bool) (mode : ValidationMode) :
    (z.foldl ValidationState.step (.first mode)).accepts =
      match tokenize? z with
      | none => false
      | some toks => ValidationMode.acceptsEnd
          (toks.foldl ValidationMode.step mode) := by
  induction z using List.twoStepInduction generalizing mode with
  | nil =>
      cases mode with
      | between seen => cases seen <;> rfl
      | literal seen => rfl
      | reject => rfl
  | singleton bit => cases bit <;> rfl
  | cons_cons first second rest ih _ =>
      have htokenize :
          tokenize? (first :: second :: rest) =
            Option.map (tokenOfPair first second :: ·) (tokenize? rest) := by
        cases first <;> cases second <;> rfl
      rw [htokenize]
      simp only [List.foldl_cons, ValidationState.step]
      cases htok : tokenize? rest <;>
        simpa [htok] using
          (ih (ValidationMode.step mode (tokenOfPair first second)))

/-- The finite-state validator accepts every canonical CNF encoding. -/
private theorem validEncoding_encode (φ : CNF) : validEncoding φ.encode = true := by
  rw [← CNF.encodeTokens_tokens φ]
  unfold validEncoding
  simp only [ValidationState.initial]
  rw [accepts_fold_eq_tokenize, tokenize?_encodeTokens]
  induction φ with
  | nil => rfl
  | cons c cs ih =>
      simp only [CNF.tokens, List.foldl_append, List.foldl_cons, List.foldl_nil]
      have hclause : ∀ seen, ∃ seen',
          c.tokens.foldl ValidationMode.step (.between seen) = .between seen' := by
        intro seen
        induction c generalizing seen with
        | nil => exact ⟨seen, rfl⟩
        | cons ℓ ls ihClause =>
            have hraw : ℓ.rawTokens.foldl ValidationMode.step (.between seen) =
                .literal seen := by
              rcases ℓ with ⟨sign, var⟩
              simp only [Lit.rawTokens, Lit.encodeRaw, Unary.encode, List.map_cons,
                List.map_replicate, List.foldl_cons, ValidationMode.step]
              induction var with
              | zero => rfl
              | succ var ihVar =>
                  rw [List.replicate_succ, List.foldl_cons, ValidationMode.step]
                  exact ihVar
            simp only [Clause.tokens, List.foldl_append, List.foldl_cons,
              List.foldl_nil, hraw, ValidationMode.step]
            exact ihClause true
      obtain ⟨seen, hc⟩ := hclause false
      rw [hc]
      simp only [ValidationMode.step]
      exact ih

/-- Acceptance by the finite-state validator produces a canonical CNF
encoding. -/
private theorem exists_cnf_of_validEncoding {z : List Bool}
    (hvalid : validEncoding z = true) :
    ∃ φ : CNF, z = φ.encode := by
  unfold validEncoding at hvalid
  simp only [ValidationState.initial] at hvalid
  rw [accepts_fold_eq_tokenize] at hvalid
  cases htok : tokenize? z with
  | none => simp [htok] at hvalid
  | some toks =>
      simp only [htok] at hvalid
      obtain ⟨φ, htoks⟩ := exists_cnf_of_tokens_accepts toks hvalid
      refine ⟨φ, ?_⟩
      calc
        z = encodeTokens toks := tokenize?_sound htok
        _ = encodeTokens φ.tokens := by rw [htoks]
        _ = φ.encode := CNF.encodeTokens_tokens φ

/-- The pure finite-state validator accepts exactly the inputs on which the
existing executable CNF decoder succeeds. -/
theorem validEncoding_eq_decode?_isSome_internal (z : List Bool) :
    validEncoding z = (CNF.decode? z).isSome := by
  cases hdecode : CNF.decode? z with
  | none =>
      cases hvalid : validEncoding z with
      | false => rfl
      | true =>
          obtain ⟨φ, hz⟩ := exists_cnf_of_validEncoding hvalid
          subst z
          simp at hdecode
  | some φ =>
      have hz : z = φ.encode := CNF.decode?_sound hdecode
      subst z
      simpa using validEncoding_encode φ

end Machine

end ThreeSAT

end SAT

end Complexity
