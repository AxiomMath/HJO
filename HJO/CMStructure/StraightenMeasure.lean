/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Mathlib.Data.List.Count
public import Mathlib.Tactic.Ring
public meta import HJO.Attr

/-! # The straightening measure of a word in the Dyck path algebra

The straightening rule of `HJO.Dyck.Aq.Tg_mul_yMon_mem_span` moves a loop `T_i` rightwards through a
monomial in the corner elements at constant total degree. To know that the rewriting terminates one
needs a statistic on words that strictly falls at every application, and the statistic is

`μ(w) = ∑` over the occurrences of a `T`-letter in `w` of the number of corner-element letters
standing to the right of that occurrence.

This file gives the alphabet of formal letters the statistic is defined on and the statistic itself.
Nothing here is about `𝔸_q`: `μ` is a function of the *word*, not of the element it multiplies out
to, and that is the whole point — the element is unchanged by the rewriting while `μ` falls.

## Main definitions

* `HJO.Dyck.StraightenLetter`: a letter of the alphabet — a loop `T_i`, a corner element `y_i`, or
  one of the two arrows.
* `HJO.Dyck.straightenMeasure`: `μ`.

## Main results

* `HJO.Dyck.straightenMeasure_append`: `μ(vw) = μ(v) + μ(w) + t(v)·c(w)`, where `t(v)` is the
  number of `T`-letters of `v` and `c(w)` the number of corner letters of `w`.
* `HJO.Dyck.straightenMeasure_insert_loop`: inserting one `T`-letter raises `μ` by exactly the
  number of corner letters to its right. This is the defining description of `μ`, read as a
  theorem.
* `HJO.Dyck.straightenMeasure_insert_corner`: inserting one corner letter raises `μ` by exactly the
  number of `T`-letters to its left.

## Implementation notes

`μ` is defined by the obvious recursion from the left, which is a total function of the list, and
the two insertion lemmas are what certify that the recursion computes the sum over
occurrences. An indexed sum over the positions carrying a `T`-letter would say the same thing with
a `List.get` and a `Fin` in every rewrite; the insertion lemmas are the form the termination
argument uses, since a rewriting step *is* the replacement of one factor by another.

The arrow letters carry their vertex and the loop and corner letters their index, none of which `μ`
reads. They are kept because the words are words in all of those generators: an alphabet
with only two letters would be a statistic on a different set of words.
-/

@[expose] public section

namespace HJO.Dyck

/-- **A letter of a word in the Dyck path algebra**: a loop `T_i`, a corner element `y_i`, or one of
the two arrows `d₊`, `d₋` at a vertex. -/
inductive StraightenLetter where
  /-- The loop `T_i`. -/
  | loop (i : ℕ)
  /-- The corner element `y_i`. -/
  | corner (i : ℕ)
  /-- The raising arrow at the vertex `k`. -/
  | raise (k : ℕ)
  /-- The lowering arrow at the vertex `k`. -/
  | lower (k : ℕ)
  deriving DecidableEq

namespace StraightenLetter

/-- Whether a letter is a loop, that is, a `T`-letter. -/
def isLoop : StraightenLetter → Bool
  | loop _ => true
  | _ => false

/-- Whether a letter is a corner element. -/
def isCorner : StraightenLetter → Bool
  | corner _ => true
  | _ => false

@[simp] theorem isLoop_loop (i : ℕ) : (loop i).isLoop = true := rfl
@[simp] theorem isLoop_corner (i : ℕ) : (corner i).isLoop = false := rfl
@[simp] theorem isCorner_loop (i : ℕ) : (loop i).isCorner = false := rfl
@[simp] theorem isCorner_corner (i : ℕ) : (corner i).isCorner = true := rfl

end StraightenLetter

open StraightenLetter

/-- **The straightening measure** `μ(w)`: the sum, over the occurrences of a `T`-letter in `w`, of
the number of corner-element letters standing to the right of that occurrence. -/
@[hjo "def_cm_straighten_measure"]
def straightenMeasure : List StraightenLetter → ℕ
  | [] => 0
  | x :: t => (if x.isLoop then t.countP isCorner else 0) + straightenMeasure t

@[simp]
theorem straightenMeasure_nil : straightenMeasure [] = 0 := rfl

theorem straightenMeasure_cons (x : StraightenLetter) (t : List StraightenLetter) :
    straightenMeasure (x :: t) = (if x.isLoop then t.countP isCorner else 0)
      + straightenMeasure t := rfl

@[simp]
theorem straightenMeasure_cons_loop (i : ℕ) (t : List StraightenLetter) :
    straightenMeasure (StraightenLetter.loop i :: t) = t.countP isCorner
      + straightenMeasure t := by
  rw [straightenMeasure_cons]
  simp only [isLoop_loop, ite_true]

@[simp]
theorem straightenMeasure_cons_corner (i : ℕ) (t : List StraightenLetter) :
    straightenMeasure (StraightenLetter.corner i :: t) = straightenMeasure t := by
  rw [straightenMeasure_cons]
  simp only [isLoop_corner, Bool.false_eq_true, ite_false, zero_add]

/-- **The append law.** Concatenating two words adds their measures together with one cross term:
every `T`-letter of the left word acquires the corner letters of the right word. Together with the
single-letter values this pins `μ` down, and it is the arithmetic every step of the termination
argument uses. -/
@[hjo "def_cm_straighten_measure"]
theorem straightenMeasure_append (v w : List StraightenLetter) :
    straightenMeasure (v ++ w)
      = straightenMeasure v + straightenMeasure w + v.countP isLoop * w.countP isCorner := by
  induction v with
  | nil => simp
  | cons x t ih =>
    rw [List.cons_append, straightenMeasure_cons, ih, straightenMeasure_cons,
      List.countP_cons, List.countP_append]
    cases x <;> simp only [isLoop, Bool.false_eq_true, ite_true, ite_false, add_zero] <;> ring

/-- **The defining description of `μ`, as a theorem.** Inserting one `T`-letter into a word raises
`μ` by exactly the number of corner letters standing to the right of the insertion point — so the
contribution of an occurrence of a `T`-letter is that number, which is what
`HJO.Dyck.straightenMeasure` is meant to compute. -/
@[hjo "def_cm_straighten_measure"]
theorem straightenMeasure_insert_loop (v w : List StraightenLetter) (i : ℕ) :
    straightenMeasure (v ++ StraightenLetter.loop i :: w)
      = straightenMeasure (v ++ w) + w.countP isCorner := by
  rw [straightenMeasure_append, straightenMeasure_append, straightenMeasure_cons_loop,
    List.countP_cons]
  simp only [isCorner_loop, Bool.false_eq_true, ite_false, add_zero]
  ring

/-- Inserting one corner letter raises `μ` by exactly the number of `T`-letters standing to its
left: the same statistic read along the other axis. -/
@[hjo "def_cm_straighten_measure"]
theorem straightenMeasure_insert_corner (v w : List StraightenLetter) (i : ℕ) :
    straightenMeasure (v ++ StraightenLetter.corner i :: w)
      = straightenMeasure (v ++ w) + v.countP isLoop := by
  rw [straightenMeasure_append, straightenMeasure_append, straightenMeasure_cons_corner,
    List.countP_cons]
  simp only [isCorner_corner, ite_true]
  ring

end HJO.Dyck
