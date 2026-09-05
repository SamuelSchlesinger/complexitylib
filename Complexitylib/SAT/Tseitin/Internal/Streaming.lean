/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.SAT.Tseitin.Defs
public import Complexitylib.SAT.Verifier

/-!
# Streaming specification for the CNF-to-3CNF transformation

This file gives a token-level specification of a machine-friendly Tseitin
transducer. It reads the existing `EncToken` stream from left to right, keeps
at most three decoded literals, and emits completed exact-width-three clauses
as soon as a fourth source literal arrives. A literal body is represented only
by its sign and a unary counter, matching the data a concrete TM can retain in
finite control plus registers.

The formula-level entry point chooses the first fresh variable to be one more
than the source *bit length*. This is deliberately easier for a TM to obtain
than `CNF.maxVar`, and `CNF.maxVar_le_encode_length` ensures that the resulting
variables are fresh. On a valid `CNF.tokens` stream, the emitted tokens and
bits are exactly the encoding produced by `CNF.to3Aux` at that start value.
-/


@[expose] public section

namespace Complexity

namespace SAT

namespace ThreeSAT

namespace Streaming

/-- The source literals retained for the current clause. Three literals are
enough: seeing a fourth emits one chain clause and rolls the window forward. -/
inductive Pending where
  | zero
  | one (a : Lit)
  | two (a b : Lit)
  | three (a b c : Lit)
  deriving DecidableEq

/-- Recover the clause represented by the bounded pending-literal state. -/
def Pending.toClause : Pending → Clause
  | .zero => []
  | .one a => [a]
  | .two a b => [a, b]
  | .three a b c => [a, b, c]

/-- Token-parser state for a raw literal. The first data bit is its sign; every
later data bit must be `true` and increments the unary variable counter. -/
inductive Scan where
  | boundary
  | literal (sign : Bool) (var : ℕ)
  deriving DecidableEq

/-- State of the streaming transducer. `emitted` is an append-only token
accumulator, and `next` is the first unused auxiliary-variable index. -/
structure State where
  /-- First unused auxiliary-variable index. -/
  next : ℕ
  /-- At most three source literals waiting to be emitted. -/
  pending : Pending
  /-- Current raw-literal parser state. -/
  scan : Scan
  /-- Append-only output-token accumulator. -/
  emitted : List EncToken
  deriving DecidableEq

/-- State at the beginning of a formula, before any token has been read. -/
def initial (next : ℕ) : State :=
  { next, pending := .zero, scan := .boundary, emitted := [] }

/-- The token encoding of one completed output clause. -/
def clauseTokens (c : Clause) : List EncToken :=
  CNF.tokens [c]

/-- Incorporate a decoded source literal. The first three literals are kept;
each later literal emits the next link of the Tseitin chain. -/
def pushLiteral (st : State) (lit : Lit) : State :=
  match st.pending with
  | .zero => { st with pending := .one lit, scan := .boundary }
  | .one a => { st with pending := .two a lit, scan := .boundary }
  | .two a b => { st with pending := .three a b lit, scan := .boundary }
  | .three a b c =>
      { next := st.next + 1
        pending := .three (Lit.negVar st.next) c lit
        scan := .boundary
        emitted := st.emitted ++ clauseTokens [a, b, Lit.pos st.next] }

/-- Finish the current source clause. The bounded pending clause is handled by
the same short-clause cases as `Clause.to3CNF`; the empty case consumes one
fresh variable for its contradiction gadget. -/
def closeClause (st : State) : State :=
  let c := st.pending.toClause
  { next := st.next + c.tseitinFreshCount
    pending := .zero
    scan := .boundary
    emitted := st.emitted ++ (c.to3CNF st.next).tokens }

/-- One token transition. It rejects malformed raw literals and separators in
the middle of a literal. On valid `CNF.tokens` streams these cases are absent. -/
def step (st : State) : EncToken → Option State
  | .bit b =>
      match st.scan with
      | .boundary => some { st with scan := .literal b 0 }
      | .literal sign var =>
          if b then some { st with scan := .literal sign (var + 1) } else none
  | .litSep =>
      match st.scan with
      | .boundary => none
      | .literal sign var => some (pushLiteral st { sign, var })
  | .clauseSep =>
      match st.scan with
      | .boundary => some (closeClause st)
      | .literal .. => none

/-- Run the streaming transition over a token list. -/
def run : State → List EncToken → Option State
  | st, [] => some st
  | st, tok :: toks => step st tok >>= fun st' => run st' toks

/-- Accept a completed formula only at a clause boundary with no pending
literals. Valid `CNF.tokens` streams always have this shape. -/
def finish : State → Option (List EncToken × ℕ)
  | { next, pending := .zero, scan := .boundary, emitted } => some (emitted, next)
  | _ => none

/-- Transform a token stream using the supplied first fresh variable. -/
def transformFrom? (next : ℕ) (toks : List EncToken) :
    Option (List EncToken × ℕ) :=
  run (initial next) toks >>= finish

/-- Transform a token stream, choosing the first fresh variable as one more
than the concrete source bit length. -/
def transformTokens? (toks : List EncToken) : Option (List EncToken × ℕ) :=
  transformFrom? (encodeTokens toks).length.succ toks

/-- Bit-level output of `transformTokens?`, retaining the final fresh counter
for the machine-level invariant. -/
def transformBits? (toks : List EncToken) : Option (List Bool × ℕ) := do
  let (out, next) ← transformTokens? toks
  pure (encodeTokens out, next)

private theorem run_append_internal (st : State) (xs ys : List EncToken) :
    run st (xs ++ ys) = (run st xs >>= fun st' => run st' ys) := by
  induction xs generalizing st with
  | nil => rfl
  | cons tok toks ih =>
      simp only [List.cons_append, run]
      cases step st tok with
      | none => rfl
      | some st' => exact ih st'

private theorem run_true_body_internal (st : State) (sign : Bool) (start count : ℕ) :
    run { st with scan := .literal sign start }
        ((List.replicate count true).map EncToken.bit) =
      some { st with scan := .literal sign (start + count) } := by
  induction count generalizing start with
  | zero => rfl
  | succ count ih =>
      rw [List.replicate_succ, List.map_cons, run]
      change run { st with scan := .literal sign (start + 1) }
          ((List.replicate count true).map EncToken.bit) =
        some { st with scan := .literal sign (start + count.succ) }
      have hadd : (start + 1) + count = start + count.succ := by omega
      simpa only [hadd] using ih (start + 1)

private theorem run_raw_literal_internal (st : State) (hscan : st.scan = .boundary)
    (sign : Bool) (var : ℕ) :
    run st (({ sign, var } : Lit).rawTokens) =
      some { st with scan := .literal sign var } := by
  simp only [Lit.rawTokens, Lit.encodeRaw, Unary.encode, List.map_cons, run]
  rw [show step st (.bit sign) = some { st with scan := .literal sign 0 } by
    simp only [step, hscan]]
  have h := run_true_body_internal st sign 0 var
  rw [Nat.zero_add] at h
  exact h

private theorem run_literal_internal (st : State) (hscan : st.scan = .boundary)
    (lit : Lit) :
    run st (lit.rawTokens ++ [EncToken.litSep]) = some (pushLiteral st lit) := by
  rcases lit with ⟨sign, var⟩
  rw [run_append_internal, run_raw_literal_internal st hscan]
  simp only [run, step]
  cases st with
  | mk next pending scan emitted =>
      cases pending <;> rfl

private theorem run_literal_suffix_internal (st : State) (hscan : st.scan = .boundary)
    (lit : Lit) (suffix : List EncToken) :
    run st ((lit.rawTokens ++ [EncToken.litSep]) ++ suffix) =
      run (pushLiteral st lit) suffix := by
  rw [run_append_internal, run_literal_internal st hscan]
  rfl

private theorem run_clause_cons_internal (st : State) (hscan : st.scan = .boundary)
    (lit : Lit) (tail : Clause) :
    run st (Clause.tokens (lit :: tail) ++ [EncToken.clauseSep]) =
      run (pushLiteral st lit) (Clause.tokens tail ++ [EncToken.clauseSep]) := by
  simpa only [Clause.tokens, List.append_assoc] using
    run_literal_suffix_internal st hscan lit (Clause.tokens tail ++ [EncToken.clauseSep])

/-- Feed a typed clause through the same bounded literal window as the token
transducer, without closing the clause. -/
private def pushLiterals : State → Clause → State
  | st, [] => st
  | st, lit :: tail => pushLiterals (pushLiteral st lit) tail

private theorem pushLiteral_scan_internal (st : State) (lit : Lit) :
    (pushLiteral st lit).scan = .boundary := by
  cases st with
  | mk next pending scan emitted =>
      cases pending <;> rfl

private theorem run_clause_tokens_internal (st : State) (hscan : st.scan = .boundary)
    (c : Clause) :
    run st (c.tokens ++ [EncToken.clauseSep]) =
      run (pushLiterals st c) [EncToken.clauseSep] := by
  induction c generalizing st with
  | nil => rfl
  | cons lit tail ih =>
      calc
        run st (Clause.tokens (lit :: tail) ++ [EncToken.clauseSep]) =
            run (pushLiteral st lit) (Clause.tokens tail ++ [EncToken.clauseSep]) :=
          run_clause_cons_internal st hscan lit tail
        _ = run (pushLiterals (pushLiteral st lit) tail) [EncToken.clauseSep] :=
          ih (pushLiteral st lit) (pushLiteral_scan_internal st lit)

private theorem run_clause_internal (c : Clause) (next : ℕ) (emitted : List EncToken) :
    run { next, pending := .zero, scan := .boundary, emitted }
        (c.tokens ++ [EncToken.clauseSep]) =
      some
        { next := next + c.tseitinFreshCount
          pending := .zero
          scan := .boundary
          emitted := emitted ++ (c.to3CNF next).tokens } := by
  rw [run_clause_tokens_internal
    (st := { next, pending := .zero, scan := .boundary, emitted })
    (hscan := rfl) (c := c)]
  induction hlen : c.length using Nat.strong_induction_on generalizing c next emitted with
  | h n ih =>
      cases c with
      | nil =>
          rfl
      | cons a tail =>
          cases tail with
          | nil =>
              rfl
          | cons b tail =>
              cases tail with
              | nil =>
                  rfl
              | cons c tail =>
                  cases tail with
                  | nil =>
                      rfl
                  | cons d rest =>
                      let recClause : Clause := Lit.negVar next :: c :: d :: rest
                      have hrecLen : recClause.length < n := by
                        simp [recClause] at hlen ⊢
                        omega
                      have hrec := ih recClause.length hrecLen recClause (next + 1)
                        (emitted ++ clauseTokens [a, b, Lit.pos next])
                        rfl
                      have hrecCount :
                          Clause.tseitinFreshCount recClause = rest.length := by
                        simp only [recClause, Clause.tseitinFreshCount, reduceCtorEq,
                          ↓reduceIte, List.length_cons]
                        all_goals omega
                      have hsourceCount :
                          Clause.tseitinFreshCount (a :: b :: c :: d :: rest) =
                            rest.length + 1 := by
                        simp only [Clause.tseitinFreshCount, reduceCtorEq, ↓reduceIte,
                          List.length_cons]
                        all_goals omega
                      rw [hrecCount] at hrec
                      rw [hsourceCount]
                      simpa only [recClause, pushLiterals, pushLiteral, Clause.to3CNF,
                        clauseTokens, Nat.add_assoc, Nat.add_comm 1 rest.length, CNF.tokens,
                        List.append_nil, List.append_assoc] using hrec

private theorem run_cnf_internal (phi : CNF) (next : ℕ) (emitted : List EncToken) :
    run { next, pending := .zero, scan := .boundary, emitted } phi.tokens =
      some
        { next := (phi.to3Aux next).2
          pending := .zero
          scan := .boundary
          emitted := emitted ++ (phi.to3Aux next).1.tokens } := by
  induction phi generalizing next emitted with
  | nil => simp [CNF.tokens, CNF.to3Aux, run]
  | cons c cs ih =>
      rw [CNF.tokens, run_append_internal]
      rw [run_clause_internal]
      change run
        { next := next + c.tseitinFreshCount
          pending := .zero
          scan := .boundary
          emitted := emitted ++ (c.to3CNF next).tokens }
        (CNF.tokens cs) = _
      rw [ih]
      simp [CNF.to3Aux, CNF.tokens_append, List.append_assoc]

/-- On a valid encoded CNF token stream, the streaming transducer agrees
exactly with `CNF.to3Aux`, including its final fresh-variable counter. -/
theorem transformFrom?_tokens_internal (phi : CNF) (next : ℕ) :
    transformFrom? next phi.tokens =
      some ((phi.to3Aux next).1.tokens, (phi.to3Aux next).2) := by
  rw [transformFrom?, initial, run_cnf_internal]
  simp [finish]

/-- `transformTokens?` uses source bit length plus one as its fresh start and
emits exactly the corresponding typed Tseitin transformation. -/
theorem transformTokens?_tokens_internal (phi : CNF) :
    transformTokens? phi.tokens =
      some ((phi.to3Aux (phi.encode.length + 1)).1.tokens,
        (phi.to3Aux (phi.encode.length + 1)).2) := by
  rw [transformTokens?, transformFrom?_tokens_internal]
  simp

/-- Bit-level correctness of the streaming transducer on every valid CNF
token stream. -/
theorem transformBits?_tokens_internal (phi : CNF) :
    transformBits? phi.tokens =
      some ((phi.to3Aux (phi.encode.length + 1)).1.encode,
        (phi.to3Aux (phi.encode.length + 1)).2) := by
  rw [transformBits?, transformTokens?_tokens_internal]
  simp

/-- The bit-length-derived start is strictly above every source variable. -/
theorem maxVar_lt_streamStart_internal (phi : CNF) :
    phi.maxVar < phi.encode.length + 1 := by
  simpa using Nat.lt_succ_of_le phi.maxVar_le_encode_length

end Streaming

end ThreeSAT

end SAT

end Complexity
