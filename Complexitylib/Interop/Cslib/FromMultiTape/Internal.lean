/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Interop.Cslib.FromMultiTape.Defs

/-!
# Proof internals for simulating CSLib machines on Complexitylib machines

Folding lemmas for the simulator `Complexity.FromMultiTape.toTM`: the cell
layout of a folded two-way tape, and the head moves of the three phases of a
simulated step.
-/


public section

namespace Complexity

namespace FromMultiTape

/-- Our symbol storing a binary CSLib cell. -/
def enc (c : Option Bool) : Γ := (Γw.ofCell c).toΓ

/-- Our cell holding CSLib cell `z` of a folded tape: `2 z + 1` for `z ≥ 0`
and `-2 z` for `z < 0`. -/
def fold (z : ℤ) : ℕ := if 0 ≤ z then 2 * z.toNat + 1 else 2 * (-z).toNat

/-- Folded cells are never the left-end cell. -/
theorem one_le_fold (z : ℤ) : 1 ≤ fold z := by
  unfold fold; split <;> omega

/-- Folding is injective. -/
theorem fold_injective : Function.Injective fold := by
  intro a b h
  unfold fold at h
  split at h <;> split at h <;> omega

/-- Every cell past the left end is a folded cell. -/
theorem exists_fold_eq {n : ℕ} (hn : 1 ≤ n) : ∃ z, fold z = n := by
  rcases Nat.even_or_odd n with ⟨m, hm⟩ | ⟨m, hm⟩
  · exact ⟨-(m : ℤ), by unfold fold; split <;> omega⟩
  · exact ⟨(m : ℤ), by unfold fold; split <;> omega⟩

/-- Encoded cells are never `▷`. -/
@[simp] theorem enc_ne_start (c : Option Bool) : enc c ≠ Γ.start := by
  rcases c with _ | _ | _ <;> simp [enc, Γw.ofCell, Γw.toΓ]

/-- Decoding an encoded cell recovers it. -/
@[simp] theorem toCell_enc (c : Option Bool) : (enc c).toCell = c := by
  rcases c with _ | _ | _ <;> rfl

/-- Rewriting an encoded cell stores it again. -/
@[simp] theorem keep_enc (c : Option Bool) : (enc c).keep = Γw.ofCell c := by
  rcases c with _ | _ | _ <;> rfl

/-- Rewriting a symbol other than `▷` leaves it unchanged. -/
theorem keep_toΓ {r : Γ} (h : r ≠ Γ.start) : r.keep.toΓ = r := by
  cases r <;> simp_all [Γ.keep, Γw.toΓ]

/-- On a tape whose only `▷` is cell 0, rewriting the symbol under the head
changes nothing. -/
theorem write_keep {t : Tape} (hC : ∀ n, t.cells n = Γ.start ↔ n = 0) :
    t.write t.read.keep.toΓ = t := by
  unfold Tape.write
  split
  · rfl
  · next h =>
    have hr : t.read ≠ Γ.start := fun h' => h ((hC _).mp h')
    rw [keep_toΓ hr]
    ext <;> simp [Tape.read]

/-- A folded tape simulating the CSLib tape `f` with head at `z`; the sign flag
`s` records whether `z` is negative. -/
structure FoldRel (t : Tape) (f : ℤ → Option Bool) (z : ℤ) (s : Bool) : Prop where
  /-- The head is on the folded cell of `z`. -/
  head : t.head = fold z
  /-- The sign flag says whether `z` is negative. -/
  sign : s = decide (z < 0)
  /-- Cell 0 holds `▷`. -/
  start : t.cells 0 = Γ.start
  /-- Every folded cell stores its CSLib cell. -/
  cells : ∀ y, t.cells (fold y) = enc (f y)

/-- On a folded tape, `▷` sits exactly at cell 0. -/
theorem FoldRel.start_iff {t : Tape} {f : ℤ → Option Bool} {z : ℤ} {s : Bool}
    (h : FoldRel t f z s) (n : ℕ) : t.cells n = Γ.start ↔ n = 0 := by
  constructor
  · intro hn
    by_contra hne
    obtain ⟨y, rfl⟩ := exists_fold_eq (Nat.one_le_iff_ne_zero.mpr hne)
    exact enc_ne_start _ (h.cells y ▸ hn)
  · rintro rfl; exact h.start

/-- A folded tape reads the CSLib symbol under the CSLib head. -/
theorem FoldRel.read {t : Tape} {f : ℤ → Option Bool} {z : ℤ} {s : Bool}
    (h : FoldRel t f z s) : t.read = enc (f z) := by
  simp [Tape.read, h.head, h.cells]

/-- Writing the encoding of `c` on a folded tape simulates CSLib's write. -/
theorem FoldRel.write {t : Tape} {f : ℤ → Option Bool} {z : ℤ} {s : Bool}
    (h : FoldRel t f z s) (c : Option Bool) :
    FoldRel (t.write (Γw.ofCell c).toΓ) (Function.update f z c) z s := by
  have hz : t.head ≠ 0 := by rw [h.head]; exact Nat.one_le_iff_ne_zero.mp (one_le_fold z)
  have hw : t.write (Γw.ofCell c).toΓ =
      { t with cells := Function.update t.cells t.head (Γw.ofCell c).toΓ } := by
    unfold Tape.write; simp only [hz, ↓reduceIte]
  rw [hw]
  refine ⟨h.head, h.sign, ?_, fun y => ?_⟩
  · simp only [Function.update_of_ne hz.symm]; exact h.start
  · by_cases hy : y = z
    · subst hy; simp [h.head, enc]
    · have : fold y ≠ t.head := h.head ▸ fun e => hy (fold_injective e)
      simp only [Function.update_of_ne this, Function.update_of_ne hy]; exact h.cells y

/-- A left move decrements the head. -/
@[simp] theorem move_left_head (u : Tape) : (u.move .left).head = u.head - 1 := rfl

/-- A right move increments the head. -/
@[simp] theorem move_right_head (u : Tape) : (u.move .right).head = u.head + 1 := rfl

/-- Staying keeps the head. -/
@[simp] theorem move_stay (u : Tape) : u.move .stay = u := rfl

/-- The head moves of phases `0`, `1` and `2` on a folded tape whose only `▷`
is cell 0 carry the head from the folded cell of `z` to that of `z + m`, and
update the sign flag. -/
theorem fold_moves {t : Tape} (hC : ∀ n, t.cells n = Γ.start ↔ n = 0) {z : ℤ}
    (hh : t.head = fold z) (m : SignType) :
    let s := decide (z < 0)
    let t1 := t.move (Dir3.guard t.read (plan0 s m).2)
    let r1 := plan1 (plan0 s m).1 s t1.read
    let t2 := t1.move (Dir3.guard t1.read r1.2.2)
    let r2 := plan2 r1.1 r1.2.1 t2.read
    let t3 := t2.move (Dir3.guard t2.read r2.2)
    t3.head = fold (z + m) ∧ (r2.1 = true ↔ z + (m : ℤ) < 0) := by
  intro s t1 r1 t2 r2 t3
  have hf : ∀ y, (0 ≤ y ∧ (fold y : ℤ) = 2 * y + 1) ∨ (y < 0 ∧ (fold y : ℤ) = -2 * y) :=
    fun y => by unfold fold; split <;> omega
  have h1 := hf z
  have h2 := hf (z + 1)
  have h3 := hf (z + -1)
  cases m <;> rcases lt_or_ge z 0 with hz | hz <;>
    simp [t3, t2, r2, t1, r1, s, plan0, plan1, plan2, Dir3.guard, Tape.read, Tape.move_cells,
      hC, hh, hz] <;> (try split_ifs) <;>
    (try simp only [move_left_head, move_right_head, move_stay, hh, decide_eq_true_eq,
      false_iff, true_iff] at *) <;>
    omega

/-- The CSLib tape after the write `wr`. -/
def applyWr (f : ℤ → Option Bool) (z : ℤ) : Option (Option Bool) → ℤ → Option Bool
  | none => f
  | some c => Function.update f z c

/-- The phase-`0` write on a folded tape simulates CSLib's write. -/
theorem FoldRel.writePhase {t : Tape} {f : ℤ → Option Bool} {z : ℤ} {s : Bool}
    (h : FoldRel t f z s) (wr : Option (Option Bool)) :
    FoldRel (t.write (writeSym t.read wr).toΓ) (applyWr f z wr) z s := by
  cases wr with
  | none => simp only [writeSym, applyWr]; rw [write_keep h.start_iff]; exact h
  | some c => exact h.write c

/-- A moved tape keeps its cells. -/
theorem FoldRel.move_start_iff {t : Tape} {f : ℤ → Option Bool} {z : ℤ} {s : Bool}
    (h : FoldRel t f z s) (d : Dir3) (n : ℕ) : (t.move d).cells n = Γ.start ↔ n = 0 := by
  rw [Tape.move_cells]; exact h.start_iff n

/-- **One simulated step on a folded work tape.** Phases `0`, `1` and `2` carry a
folded tape simulating CSLib tape `f` with head `z` to one simulating the
CSLib tape after the write `wr` and the move `m`. -/
theorem FoldRel.phases {t : Tape} {f : ℤ → Option Bool} {z : ℤ} {s : Bool}
    (h : FoldRel t f z s) (wr : Option (Option Bool)) (m : SignType) :
    let t1 := t.writeAndMove (writeSym t.read wr).toΓ (Dir3.guard t.read (plan0 s m).2)
    let r1 := plan1 (plan0 s m).1 s t1.read
    let t2 := t1.writeAndMove t1.read.keep.toΓ (Dir3.guard t1.read r1.2.2)
    let r2 := plan2 r1.1 r1.2.1 t2.read
    let t3 := t2.writeAndMove t2.read.keep.toΓ (Dir3.guard t2.read r2.2)
    FoldRel t3 (applyWr f z wr) (z + m) r2.1 := by
  intro t1 r1 t2 r2 t3
  have hu := h.writePhase wr
  set u := t.write (writeSym t.read wr).toΓ with hu_def
  have hread : t.read ≠ Γ.start := by
    rw [h.read]; exact enc_ne_start _
  have hread' : u.read ≠ Γ.start := by
    rw [hu.read]; exact enc_ne_start _
  have hg : Dir3.guard t.read (plan0 s m).2 = Dir3.guard u.read (plan0 s m).2 := by
    simp [Dir3.guard, hread, hread']
  have hs : s = decide (z < 0) := h.sign
  have hC1 := hu.move_start_iff (Dir3.guard u.read (plan0 s m).2)
  have ht1 : t1 = u.move (Dir3.guard u.read (plan0 s m).2) := by
    simp only [t1, Tape.writeAndMove, ← hu_def, hg]
  have hC2 : ∀ n, t1.cells n = Γ.start ↔ n = 0 := by rw [ht1]; exact hC1
  have ht2 : t2 = t1.move (Dir3.guard t1.read r1.2.2) := by
    simp only [t2, Tape.writeAndMove, write_keep hC2]
  have hC3 : ∀ n, t2.cells n = Γ.start ↔ n = 0 := by
    rw [ht2, Tape.move_cells]; exact hC2
  have ht3 : t3 = t2.move (Dir3.guard t2.read r2.2) := by
    simp only [t3, Tape.writeAndMove, write_keep hC3]
  obtain ⟨hh3, hs3⟩ := fold_moves hu.start_iff hu.head m
  subst hs
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp only [ht3]; simp only [r2]; simp only [ht2]; simp only [r1]; simp only [ht1]
    exact hh3
  · simp only [r2]; simp only [ht2]; simp only [r1]; simp only [ht1]
    exact Bool.eq_iff_iff.mpr (by simpa using hs3)
  · rw [ht3, ht2, ht1]; simp only [Tape.move_cells]; exact hu.start
  · intro y; rw [ht3, ht2, ht1]; simp only [Tape.move_cells]; exact hu.cells y

/-- The position reached by a CSLib input-head move. -/
theorem moveInputPos_val {m : ℕ} (p : Fin (m + 2)) (s : SignType) :
    (Turing.moveInputPos p s : ℕ) = min ((p : ℤ) + (s : ℤ)).toNat (m + 1) := by
  unfold Turing.moveInputPos
  dsimp only
  split <;> simp <;> omega

/-- The input tape holds `▷` exactly at cell 0. -/
theorem input_start_iff (x : List Bool) (i : ℕ) :
    (Tape.init (x.map Γ.ofBool)).cells i = Γ.start ↔ i = 0 := by
  rcases i with _ | i
  · simp
  · rw [Tape.init_cells_succ]
    simp only [List.getElem?_map, Nat.add_one_ne_zero, iff_false]
    cases h : x[i]? with
    | none => simp
    | some b => cases b <;> simp [Γ.ofBool]

/-- Past `▷`, the input tape is blank exactly after the input. -/
theorem input_blank_iff (x : List Bool) (i : ℕ) :
    (Tape.init (x.map Γ.ofBool)).cells (i + 1) = Γ.blank ↔ x.length ≤ i := by
  rw [Tape.init_cells_succ]
  simp only [List.getElem?_map]
  cases h : x[i]? with
  | none =>
    simp only [Option.map_none, Option.getD_none, true_iff]
    exact List.getElem?_eq_none_iff.mp h
  | some b =>
    have : i < x.length := (List.getElem?_eq_some_iff.mp h).1
    cases b <;> simp [Γ.ofBool] <;> omega

/-- The symbol under our input head decodes to CSLib's input symbol. -/
theorem input_toCell {k : ℕ} {S : Type} {x : List Bool} (d : Turing.Cfg k Bool S x) :
    ((Tape.init (x.map Γ.ofBool)).cells d.inputPos.val).toCell = d.inputSymbol := by
  unfold Turing.Cfg.inputSymbol
  split_ifs with h1 h2
  · simp [h1, Γ.toCell]
  · rw [h2, Tape.init_cells_ge _ _ (by simp)]; rfl
  · have hp : d.inputPos.val ≠ 0 := fun h => h1 (Fin.ext h)
    obtain ⟨i, hi⟩ : ∃ i, d.inputPos.val = i + 1 := ⟨d.inputPos.val - 1, by omega⟩
    have hlt : i < x.length := by
      have := d.inputPos.isLt
      omega
    simp only [hi, Tape.init_cells_succ, List.getElem?_map, List.getElem?_eq_getElem hlt,
      Option.map_some, Option.getD_some, Nat.add_sub_cancel]
    cases x[i] <;> rfl

/-- **One simulated step on the input tape.** Phases `0`, `1` and `2` move our
input head from CSLib's input position `p` to the position reached by CSLib's
clamped move `m`. -/
theorem input_phases {x : List Bool} {t : Tape}
    (hc : t.cells = (Tape.init (x.map Γ.ofBool)).cells) (p : Fin (x.length + 2))
    (hp : t.head = p.val) (m : SignType) :
    let t1 := t.move (Dir3.guard t.read .stay)
    let t2 := t1.move (Dir3.guard t1.read .stay)
    let t3 := t2.move (Dir3.guard t2.read (inputPlan t.read m))
    t3.cells = t.cells ∧ t3.head = (Turing.moveInputPos p m).val := by
  intro t1 t2 t3
  have hpl := p.isLt
  have hmv := moveInputPos_val p m
  refine ⟨by simp only [t3, t2, t1, Tape.move_cells], ?_⟩
  have hb : ∀ i, 1 ≤ i →
      ((Tape.init (x.map Γ.ofBool)).cells i = Γ.blank ↔ x.length < i) := by
    intro i hi
    obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
    rw [input_blank_iff]; omega
  rw [hmv]
  rcases Nat.eq_zero_or_pos p.val with h0 | h0
  · have h1 : ¬ (Tape.init (x.map Γ.ofBool)).cells (0 + 1) = Γ.start := by
      rw [input_start_iff]; omega
    cases m <;>
      simp [t3, t2, t1, Dir3.guard, inputPlan, Tape.read, Tape.move_cells, hc, hp, h0,
        h1]
  · have hbp := hb _ h0
    have hsp : ¬ (Tape.init (x.map Γ.ofBool)).cells p.val = Γ.start := by
      rw [input_start_iff]; omega
    cases m <;>
      simp [t3, t2, t1, Dir3.guard, inputPlan, Tape.read, hc, hp, hbp, hsp] <;>
      (try split_ifs) <;> (try simp only [move_right_head, move_stay, hp]) <;> omega

/-- Our output tape holds the CSLib output `out` after `▷`, with the head just
past it. -/
structure OutRel (t : Tape) (out : List Bool) : Prop where
  /-- The head is just past the output. -/
  head : t.head = out.length + 1
  /-- `▷` sits exactly at cell 0. -/
  start_iff : ∀ n, t.cells n = Γ.start ↔ n = 0
  /-- Cells `1, …, |out|` hold the output. -/
  cells : ∀ i (h : i < out.length), t.cells (i + 1) = Γ.ofBool out[i]

/-- A tape whose only `▷` is cell 0, with its head off cell 0, stays put in the
idle phases. -/
theorem idle_phase {t : Tape} (hC : ∀ n, t.cells n = Γ.start ↔ n = 0) (hh : t.head ≠ 0) :
    t.writeAndMove t.read.keep.toΓ (Dir3.guard t.read .stay) = t := by
  have : t.read ≠ Γ.start := by simp only [Tape.read, ne_eq, hC]; exact hh
  simp only [Tape.writeAndMove, write_keep hC, Dir3.guard, this, ↓reduceIte, move_stay]

/-- **One simulated step on the output tape.** Phase `0` appends the emitted
bit `e`; phases `1` and `2` leave the tape alone. -/
theorem OutRel.phase0 {t : Tape} {out : List Bool} (h : OutRel t out) (e : Option Bool) :
    OutRel (t.writeAndMove (outSym t.read e).toΓ (Dir3.guard t.read (outDir e)))
      (out ++ e.toList) := by
  have hh : t.head ≠ 0 := by rw [h.head]; omega
  have hr : t.read ≠ Γ.start := by simp only [Tape.read, ne_eq, h.start_iff]; exact hh
  cases e with
  | none =>
    have := idle_phase h.start_iff hh
    simp only [outSym, outDir, Option.toList_none, List.append_nil]
    rw [this]; exact h
  | some b =>
    have hw : t.write (Γw.ofBool b).toΓ =
        { t with cells := Function.update t.cells t.head (Γw.ofBool b).toΓ } := by
      unfold Tape.write; simp only [hh, ↓reduceIte]
    simp only [outSym, outDir, Tape.writeAndMove, hw, Dir3.guard, hr, ↓reduceIte]
    refine ⟨by simp [h.head], fun n => ?_, fun i hi => ?_⟩
    · simp only [Tape.move_cells]
      by_cases hn : n = t.head
      · subst hn; simp only [Function.update_self]
        cases b <;> simp [Γw.ofBool, Γw.toΓ, hh]
      · rw [Function.update_of_ne hn]; exact h.start_iff n
    · simp only [Tape.move_cells, Option.toList_some, List.length_append,
        List.length_cons, List.length_nil] at hi ⊢
      by_cases hi' : i < out.length
      · rw [Function.update_of_ne (by rw [h.head]; omega), h.cells i hi',
          List.getElem_append_left hi']
      · have hio : i = out.length := by omega
        subst hio
        rw [← h.head, Function.update_self]
        simp only [List.getElem_append_right (Nat.le_refl _), Nat.sub_self,
          List.getElem_cons_zero]
        cases b <;> rfl

variable {k : ℕ} {S : Type}

/-- One step of the simulator from a configuration that has not halted. -/
theorem toTM_step [DecidableEq S] [Fintype S] (M : Turing.MultiTapeTM k Bool S)
    (c : Cfg k (St k S)) (h : c.state ≠ .halt) :
    (toTM M).step c = some
      { state := (δ M c.state c.input.read (fun i => (c.work i).read) c.output.read).1
        input := c.input.move
          (δ M c.state c.input.read (fun i => (c.work i).read) c.output.read).2.2.2.1
        work := fun i => (c.work i).writeAndMove
          ((δ M c.state c.input.read (fun i => (c.work i).read) c.output.read).2.1 i).toΓ
          ((δ M c.state c.input.read (fun i => (c.work i).read) c.output.read).2.2.2.2.1 i)
        output := c.output.writeAndMove
          (δ M c.state c.input.read (fun i => (c.work i).read) c.output.read).2.2.1.toΓ
          (δ M c.state c.input.read (fun i => (c.work i).read) c.output.read).2.2.2.2.2 } := by
  unfold TM.step
  split_ifs with h'
  · exact absurd h' h
  · rfl

/-- The simulation relation between our configuration `c` and a CSLib
configuration `d` on input `x`, at the start of a simulated step. -/
structure Sim (x : List Bool) (c : Cfg k (St k S)) (d : Turing.Cfg k Bool S x) : Prop where
  /-- The input head is on CSLib's input position. -/
  input_head : c.input.head = d.inputPos.val
  /-- The input tape is untouched. -/
  input_cells : c.input.cells = (Tape.init (x.map Γ.ofBool)).cells
  /-- Each work tape folds its CSLib work tape. -/
  work : ∀ j, FoldRel (c.work j) (d.workTapes j) (d.workTapePos j)
    (decide (d.workTapePos j < 0))
  /-- The output tape holds CSLib's output. -/
  output : OutRel c.output d.output

/-- Under the simulation relation, our input head reads CSLib's input symbol. -/
theorem Sim.input_read {x : List Bool} {c : Cfg k (St k S)} {d : Turing.Cfg k Bool S x}
    (h : Sim x c d) : c.input.read.toCell = d.inputSymbol := by
  rw [Tape.read, h.input_cells, h.input_head]; exact input_toCell d

/-- Under the simulation relation, our work heads read CSLib's work symbols. -/
theorem Sim.work_read {x : List Bool} {c : Cfg k (St k S)} {d : Turing.Cfg k Bool S x}
    (h : Sim x c d) : (fun j => (c.work j).read.toCell) = d.workTapeSymbols := by
  funext j; rw [(h.work j).read, toCell_enc]; rfl

/-- One CSLib step from a running configuration, field by field. -/
theorem cslib_step_eq (M : Turing.MultiTapeTM k Bool S) {x : List Bool}
    {d : Turing.Cfg k Bool S x} {q : S} (h : d.state = some q) :
    M.step d =
      { state := (M.tr q d.inputSymbol d.workTapeSymbols).state
        inputPos := Turing.moveInputPos d.inputPos
          (M.tr q d.inputSymbol d.workTapeSymbols).inputTape
        workTapes := fun i => applyWr (d.workTapes i) (d.workTapePos i)
          ((M.tr q d.inputSymbol d.workTapeSymbols).workTapes i).1
        workTapePos := fun i =>
          d.workTapePos i + ((M.tr q d.inputSymbol d.workTapeSymbols).workTapes i).2
        output := d.output ++ (M.tr q d.inputSymbol d.workTapeSymbols).output.toList } := by
  obtain ⟨state, inputPos, workTapes, workTapePos, output⟩ := d
  cases h
  simp only [Turing.MultiTapeTM.step, Turing.Action.apply]
  congr 1
  funext i
  cases ((M.tr q _ _).workTapes i).1 <;> rfl

/-- **One simulated step.** From the simulation relation at a CSLib step that
does not halt, three steps of the simulator restore the relation. -/
theorem Sim.step_run [DecidableEq S] [Fintype S] {M : Turing.MultiTapeTM k Bool S}
    {x : List Bool} {c : Cfg k (St k S)} {d : Turing.Cfg k Bool S x} (h : Sim x c d)
    {q q' : S} (hq : d.state = some q)
    (hc : c.state = .run q (fun j => decide (d.workTapePos j < 0)))
    (hq' : (M.tr q d.inputSymbol d.workTapeSymbols).state = some q') :
    ∃ c', (toTM M).reachesIn 3 c c' ∧ Sim x c' (M.step d) ∧
      c'.state = .run q' (fun j => decide ((M.step d).workTapePos j < 0)) := by
  refine ⟨_, .step (toTM_step M c ?_) (.step (toTM_step M _ ?_)
    (.step (toTM_step M _ ?_) .zero)), ?_, ?_⟩
  · rw [hc]; simp
  · simp only [hc, δ, h.input_read, h.work_read, hq']; simp
  · simp only [hc, δ, h.input_read, h.work_read, hq']; simp
  · simp only [hc, δ, h.input_read, h.work_read, hq', cslib_step_eq M hq]
    refine ⟨?_, ?_, fun j => ?_, ?_⟩ <;> dsimp only
    · exact (input_phases h.input_cells d.inputPos h.input_head _).2
    · exact (input_phases h.input_cells d.inputPos h.input_head _).1.trans h.input_cells
    · have hp := (h.work j).phases
        ((M.tr q d.inputSymbol d.workTapeSymbols).workTapes j).1
        ((M.tr q d.inputSymbol d.workTapeSymbols).workTapes j).2
      exact ⟨hp.head, rfl, hp.start, hp.cells⟩
    · have ho := h.output.phase0 (M.tr q d.inputSymbol d.workTapeSymbols).output
      have hh : ∀ n, n + 1 ≠ 0 := fun n => by omega
      rw [idle_phase ho.start_iff (ho.head ▸ hh _), idle_phase ho.start_iff (ho.head ▸ hh _)]
      exact ho
  · simp only [hc, δ, h.input_read, h.work_read, hq', cslib_step_eq M hq]
    congr 1; funext j; exact ((h.work j).phases _ _).sign

/-- **The halting step.** From the simulation relation at a CSLib step that
halts, one step of the simulator halts with CSLib's final output. -/
theorem Sim.step_halt [DecidableEq S] [Fintype S] {M : Turing.MultiTapeTM k Bool S}
    {x : List Bool} {c : Cfg k (St k S)} {d : Turing.Cfg k Bool S x} (h : Sim x c d)
    {q : S} (hq : d.state = some q)
    (hc : c.state = .run q (fun j => decide (d.workTapePos j < 0)))
    (hq' : (M.tr q d.inputSymbol d.workTapeSymbols).state = none) :
    ∃ c', (toTM M).reachesIn 1 c c' ∧ c'.state = .halt ∧
      OutRel c'.output (M.step d).output := by
  refine ⟨_, .step (toTM_step M c ?_) .zero, ?_, ?_⟩
  · rw [hc]; simp
  · simp only [hc, δ, h.input_read, h.work_read, hq']
    rfl
  · simp only [hc, δ, h.input_read, h.work_read, cslib_step_eq M hq]
    exact h.output.phase0 _

/-- The first move off `▷` on an initialized tape. -/
theorem init_move (l : List Γ) (d : Dir3) :
    (Tape.init l).move (Dir3.guard (Tape.init l).read d) =
      { head := 1, cells := (Tape.init l).cells } := by
  have : (Tape.init l).read = Γ.start := by simp [Tape.read]
  rw [this, Dir3.guard_start]; rfl

/-- The first step on an initialized tape: the write is dropped and the head
moves off `▷`. -/
theorem init_writeAndMove (l : List Γ) (s : Γ) (d : Dir3) :
    (Tape.init l).writeAndMove s (Dir3.guard (Tape.init l).read d) =
      { head := 1, cells := (Tape.init l).cells } := by
  have hw : (Tape.init l).write s = Tape.init l := by simp [Tape.write]
  rw [Tape.writeAndMove, hw, init_move]

/-- The blank tape holds `▷` exactly at cell 0. -/
theorem init_nil_start_iff (n : ℕ) : (Tape.init []).cells n = Γ.start ↔ n = 0 := by
  simpa using input_start_iff [] n

/-- The CSLib initial configuration on input `x`. -/
abbrev initD (M : Turing.MultiTapeTM k Bool S) (x : List Bool) : Turing.Cfg k Bool S x :=
  M.initCfg x

/-- **The first step.** One step of the simulator moves every head off `▷` and
establishes the simulation relation with CSLib's initial configuration. -/
theorem sim_init [DecidableEq S] [Fintype S] (M : Turing.MultiTapeTM k Bool S)
    (x : List Bool) :
    ∃ c, (toTM M).reachesIn 1 ((toTM M).initCfg x) c ∧ Sim x c (initD M x) ∧
      c.state = .run M.q₀ (fun j => decide ((initD M x).workTapePos j < 0)) := by
  refine ⟨_, .step (toTM_step M _ ?_) .zero, ?_, ?_⟩
  · simp [toTM]
  · simp only [toTM, δ]
    refine ⟨?_, ?_, fun j => ?_, ?_⟩ <;> dsimp only <;>
      simp only [init_move, init_writeAndMove]
    · rfl
    · refine ⟨by simp [fold], by simp, by simp, fun y => ?_⟩
      obtain ⟨m, hm⟩ : ∃ m, fold y = m + 1 :=
        ⟨fold y - 1, by have := one_le_fold y; omega⟩
      simp only [hm, Tape.init_nil_cells_succ]; rfl
    · exact ⟨rfl, init_nil_start_iff, fun i hi => absurd hi (by simp)⟩
  · simp [toTM, δ]

/-- **The run.** While CSLib has not halted after `n` steps, the simulator
reaches, after `3 n + 1` steps, a configuration related to CSLib's. -/
theorem sim_run [DecidableEq S] [Fintype S] (M : Turing.MultiTapeTM k Bool S)
    (x : List Bool) : ∀ n, (M.runFrom (initD M x) n).state ≠ none →
    ∃ c q, (toTM M).reachesIn (3 * n + 1) ((toTM M).initCfg x) c ∧
      Sim x c (M.runFrom (initD M x) n) ∧ (M.runFrom (initD M x) n).state = some q ∧
      c.state = .run q (fun j => decide ((M.runFrom (initD M x) n).workTapePos j < 0))
  | 0, _ => by
    obtain ⟨c, hr, hs, hc⟩ := sim_init M x
    exact ⟨c, M.q₀, hr, hs, rfl, hc⟩
  | n + 1, hn => by
    have hsucc : M.runFrom (initD M x) (n + 1) = M.step (M.runFrom (initD M x) n) :=
      Function.iterate_succ_apply' _ _ _
    have hn' : (M.runFrom (initD M x) n).state ≠ none := fun h0 =>
      hn (by rw [hsucc, Turing.MultiTapeTM.step_of_halt h0]; exact h0)
    obtain ⟨c, q, hr, hs, hq, hc⟩ := sim_run M x n hn'
    rw [hsucc] at hn ⊢
    cases ha : (M.tr q (M.runFrom (initD M x) n).inputSymbol
        (M.runFrom (initD M x) n).workTapeSymbols).state with
    | none => exact absurd (by rw [cslib_step_eq M hq]; exact ha) hn
    | some q' =>
      obtain ⟨c', hr', hs', hc'⟩ := hs.step_run hq hc ha
      refine ⟨c', q', ?_, hs', by rw [cslib_step_eq M hq]; exact ha, hc'⟩
      have := TM.reachesIn_trans _ hr hr'
      rwa [show 3 * n + 1 + 3 = 3 * (n + 1) + 1 by omega] at this

/-- **The simulator decides what CSLib decides.** If `M` computes the indicator
of `L` within time `t`, the simulator decides `L` within time `3 t`. -/
theorem toTM_decides [DecidableEq S] [Fintype S] (M : Turing.MultiTapeTM k Bool S)
    {L : Language} {t s : List Bool → ℕ}
    (hM : M.ComputesFunInTimeAndSpace (Function.Embedding.refl _)
      ⟨fun b => [b], by intro a b h; simpa using h⟩ (Turing.MultiTapeTM.indicator L) t s)
    (x : List Bool) :
    ∃ c' T, T ≤ 3 * t x ∧ (toTM M).reachesIn T ((toTM M).initCfg x) c' ∧
      (toTM M).halted c' ∧ (x ∈ L → c'.output.cells 1 = Γ.one) ∧
      (x ∉ L → c'.output.cells 1 = Γ.zero) := by
  obtain ⟨t', ht', s', -, hc⟩ := hM x
  obtain ⟨u, hu, hun, hmin⟩ := M.exists_minimal_halting_time (initD M x) t' hc.1
  obtain ⟨v, rfl⟩ : ∃ v, u = v + 1 := by
    rcases u with _ | v
    · exact absurd hun (by simp [Turing.MultiTapeTM.runFrom])
    · exact ⟨v, rfl⟩
  obtain ⟨c, q, hr, hs, hq, hcs⟩ := sim_run M x v (hmin v (by omega))
  have hsucc : M.runFrom (initD M x) (v + 1) = M.step (M.runFrom (initD M x) v) :=
    Function.iterate_succ_apply' _ _ _
  have ha : (M.tr q (M.runFrom (initD M x) v).inputSymbol
      (M.runFrom (initD M x) v).workTapeSymbols).state = none := by
    have := hun; rw [hsucc, cslib_step_eq M hq] at this; exact this
  obtain ⟨c', hr', hst, hout⟩ := hs.step_halt hq hcs ha
  have hfin : (M.step (M.runFrom (initD M x) v)).output = [Turing.MultiTapeTM.indicator L x] := by
    rw [← hsucc, ← M.runFrom_eq_of_halt _ hu hun]; exact hc.2.1
  rw [hfin] at hout
  have h1 := hout.cells 0 (by simp)
  simp only [List.getElem_cons_zero] at h1
  refine ⟨c', 3 * v + 1 + 1, by omega, TM.reachesIn_trans _ hr hr', hst, fun hx => ?_,
    fun hx => ?_⟩
  · rw [h1]; simp [Turing.MultiTapeTM.indicator, hx, Γ.ofBool]
  · rw [h1]; simp [Turing.MultiTapeTM.indicator, hx, Γ.ofBool]

end FromMultiTape

end Complexity
