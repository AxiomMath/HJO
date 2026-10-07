/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.CMStructure.StraightenMeasure
public meta import HJO.Attr

/-! # Straightening terminates

The straightening rule of `HJO.Dyck.Aq.Tg_mul_yMon_mem_span` rewrites a factor
`T_iy_1^{a_1}⋯y_k^{a_k}` of a word into words `y_1^{b_1}⋯y_k^{b_k}T_i` and `y_1^{b_1}⋯y_k^{b_k}`
with `∑ b_r = ∑ a_r`. This file shows that the statistic `μ` of `HJO.Dyck.straightenMeasure`
strictly falls at every such replacement, and deduces that the rewriting cannot be applied
indefinitely.

Everything here is about *words*, which is the point of the statistic: `μ` is a function of the
list of letters, not of the element of `𝔸_q` it multiplies out to, and the replacement leaves that
element unchanged while `μ` falls. So the object that carries the argument is a one-step rewriting
relation `HJO.Dyck.StraightenStep` on `List HJO.Dyck.StraightenLetter`, whose two constructors are
the two kinds of word the rule produces.

## Main definitions

* `HJO.Dyck.StraightenStep`: one application of the straightening rule to a word, read as a
  relation on words. The `keep` constructor replaces `u (T_i y^a) v` by `u y^{b} T_i v` and the
  `drop` constructor replaces it by `u y^{b} v`, in both cases with `y^b` a monomial of the same
  total degree `∑ a_r ≥ 1` as `y^a`.

## Main results

* `HJO.Dyck.straightenMeasure_lt_of_step`: every word the rule produces has strictly smaller `μ`.
  This is the content of the lemma: `μ` falls by `∑ a_r ≥ 1` on a `keep` step and by
  `∑ a_r` plus the number of corner letters in the tail on a `drop` step.
* `HJO.Dyck.wellFounded_straightenStep`: the rewriting relation is well founded.
* `HJO.Dyck.not_forall_straightenStep`: no sequence of words steps forever — the statement
  "the rewriting cannot be applied indefinitely", in the most literal reading.

The clause "`μ` takes values in `ℕ`" is the type of `HJO.Dyck.straightenMeasure` and so
needs no lemma; it is what makes the strict decrease into termination.

## Implementation notes

**How the relation matches the algebraic straightening rule.** The rule is
`HJO.Dyck.Aq.Tg_mul_yMon_mem_span` in `HJO/CMStructure/HeckeStraighten.lean`, which says
`Tg K q k (i-1) * yMon K q k a ∈ Submodule.span K (straightenSet K q k i (yMonDeg k a))` with
`straightenSet K q k i n = {x | ∃ b, yMonDeg k b = n ∧ (x = yMon K q k b * Tg K q k (i-1) ∨
x = yMon K q k b)}`. So the words occurring in the expansion are *exactly* the two shapes
`y^bT_i` and `y^b` with `∑ b_r = ∑ a_r`, which are the `keep` and the `drop` constructor. The
conclusion is a membership in a span rather than an explicit finite sum, so it quantifies over the
same set of words the constructors do and over no others.

**A corner monomial is encoded as a list of indices.** The word `y_1^{a_1}⋯y_k^{a_k}` is
`cs.map HJO.Dyck.StraightenLetter.corner` for a list `cs : List ℕ` of vertex indices with
repetition, so `∑ a_r` is `cs.length` and the hypothesis `∑ a_r ≥ 1` is `1 ≤ cs.length`. Nothing in
the measure reads the indices, so the two monomials of a step are related only by
`cs'.length = cs.length`, which is the rule's "same total degree" and all of it that matters. The
alternative, a hypothesis `∀ x ∈ C, x.isCorner` on a list of letters, says the same thing at the
cost of proving the three counting facts of the block from the hypothesis at each use.

**Well-foundedness and the descending-chain corollary are both recorded.**
`HJO.Dyck.wellFounded_straightenStep` is the form a Lean termination argument consumes;
`HJO.Dyck.not_forall_straightenStep` is the literal statement, and it is proved
directly from the strict decrease by `μ(f n) + n ≤ μ(f 0)`, which avoids going through a relation
embedding.
-/

@[expose] public section

namespace HJO.Dyck

open StraightenLetter

/-! ### The three counting facts about a monomial in the corner letters -/

/-- A word of corner letters has no `T`-letter. -/
theorem countP_isLoop_map_corner (cs : List ℕ) :
    (cs.map StraightenLetter.corner).countP isLoop = 0 := by
  induction cs with
  | nil => simp
  | cons c t ih => simp [ih]

/-- A word of corner letters has as many corner letters as it has letters. -/
theorem countP_isCorner_map_corner (cs : List ℕ) :
    (cs.map StraightenLetter.corner).countP isCorner = cs.length := by
  induction cs with
  | nil => simp
  | cons c t ih => simp [List.countP_cons, ih]

/-- A word of corner letters has measure `0`: there is no `T`-letter to contribute. -/
@[simp]
theorem straightenMeasure_map_corner (cs : List ℕ) :
    straightenMeasure (cs.map StraightenLetter.corner) = 0 := by
  induction cs with
  | nil => simp
  | cons c t ih => simp [ih]

/-! ### The measure of the three words a step involves -/

/-- The measure of a word `u (T_iy^a) v` with the `T`-letter to the left of the monomial: the
`T`-letter contributes the `cs.length` corner letters of the monomial and the corner letters of
`v`, and every `T`-letter of `u` contributes both as well. -/
theorem straightenMeasure_loop_block (u v : List StraightenLetter) (cs : List ℕ) (i : ℕ) :
    straightenMeasure (u ++ (StraightenLetter.loop i :: cs.map StraightenLetter.corner) ++ v)
      = straightenMeasure u + straightenMeasure v + cs.length + v.countP isCorner
        + u.countP isLoop * (cs.length + v.countP isCorner) := by
  simp only [List.append_assoc, straightenMeasure_append, straightenMeasure_cons_loop,
    straightenMeasure_map_corner, List.countP_append, List.countP_cons, countP_isLoop_map_corner,
    countP_isCorner_map_corner, isLoop_loop, isCorner_loop, Bool.false_eq_true, ite_false,
    ite_true]
  ring

/-- The measure of a word `u y^b T_i v` with the `T`-letter to the right of the monomial: the
`T`-letter now contributes only the corner letters of `v`, while the `T`-letters of `u` still see
the whole monomial. -/
theorem straightenMeasure_block_loop (u v : List StraightenLetter) (cs : List ℕ) (i : ℕ) :
    straightenMeasure (u ++ cs.map StraightenLetter.corner
        ++ (StraightenLetter.loop i :: v))
      = straightenMeasure u + straightenMeasure v + v.countP isCorner
        + u.countP isLoop * (cs.length + v.countP isCorner) := by
  simp only [List.append_assoc, straightenMeasure_append, straightenMeasure_cons_loop,
    straightenMeasure_map_corner, List.countP_append, List.countP_cons, countP_isLoop_map_corner,
    countP_isCorner_map_corner, isCorner_loop, Bool.false_eq_true, ite_false]
  ring

/-- The measure of a word `u y^b v` from which the `T`-letter has vanished: only the `T`-letters of
`u` contribute, and they see the monomial and the corner letters of `v`. -/
theorem straightenMeasure_block (u v : List StraightenLetter) (cs : List ℕ) :
    straightenMeasure (u ++ cs.map StraightenLetter.corner ++ v)
      = straightenMeasure u + straightenMeasure v
        + u.countP isLoop * (cs.length + v.countP isCorner) := by
  simp only [List.append_assoc, straightenMeasure_append, straightenMeasure_map_corner,
    List.countP_append, countP_isLoop_map_corner, countP_isCorner_map_corner]
  ring

/-! ### The two arithmetic cores -/

/-- **Moving the `T`-letter to the right of the monomial lowers `μ` by the degree.** Replacing the
factor `T_iy^a` by `y^bT_i` with `∑ b_r = ∑ a_r` lowers the measure by exactly `∑ a_r`: the
`T`-letter loses the corner letters it has passed, and no other `T`-letter changes its
contribution, because the number of corner letters of the factor is unchanged. -/
theorem straightenMeasure_loop_block_eq_block_loop_add (u v : List StraightenLetter)
    (cs cs' : List ℕ) (i : ℕ) (hlen : cs'.length = cs.length) :
    straightenMeasure (u ++ (StraightenLetter.loop i :: cs.map StraightenLetter.corner) ++ v)
      = straightenMeasure (u ++ cs'.map StraightenLetter.corner
          ++ (StraightenLetter.loop i :: v)) + cs.length := by
  rw [straightenMeasure_loop_block, straightenMeasure_block_loop, hlen]
  ring

/-- **Deleting the `T`-letter lowers `μ` by the degree and by the corner letters further right.**
Replacing the factor `T_iy^a` by `y^b` with `∑ b_r = ∑ a_r` removes the whole contribution of that
occurrence of the `T`-letter. -/
theorem straightenMeasure_loop_block_eq_block_add (u v : List StraightenLetter)
    (cs cs' : List ℕ) (i : ℕ) (hlen : cs'.length = cs.length) :
    straightenMeasure (u ++ (StraightenLetter.loop i :: cs.map StraightenLetter.corner) ++ v)
      = straightenMeasure (u ++ cs'.map StraightenLetter.corner ++ v)
          + cs.length + v.countP isCorner := by
  rw [straightenMeasure_loop_block, straightenMeasure_block, hlen]
  ring

/-! ### The rewriting relation and its termination -/

/-- **One application of the straightening rule to a word.** The word `u (T_iy^a) v` steps to any
word the rule produces: either `u y^b T_i v`, the `T`-letter having moved to the right of the
monomial, or `u y^b v`, the `T`-letter having vanished. In both cases `y^b` has the same total
degree as `y^a`, which is at least `1`. -/
inductive StraightenStep : List StraightenLetter → List StraightenLetter → Prop
  /-- The `T`-letter survives to the right of the rewritten monomial. -/
  | keep (u v : List StraightenLetter) (cs cs' : List ℕ) (i : ℕ) (hlen : cs'.length = cs.length)
      (hpos : 1 ≤ cs.length) :
      StraightenStep (u ++ (StraightenLetter.loop i :: cs.map StraightenLetter.corner) ++ v)
        (u ++ cs'.map StraightenLetter.corner ++ (StraightenLetter.loop i :: v))
  /-- The `T`-letter is gone. -/
  | drop (u v : List StraightenLetter) (cs cs' : List ℕ) (i : ℕ) (hlen : cs'.length = cs.length)
      (hpos : 1 ≤ cs.length) :
      StraightenStep (u ++ (StraightenLetter.loop i :: cs.map StraightenLetter.corner) ++ v)
        (u ++ cs'.map StraightenLetter.corner ++ v)

/-- **Straightening strictly decreases the measure.** Every word occurring in the expansion given
by `HJO.Dyck.Aq.Tg_mul_yMon_mem_span` of a word containing a factor `T_iy_1^{a_1}⋯y_k^{a_k}` with
`a_1 + ⋯ + a_k ≥ 1` has strictly smaller `μ` than the word itself. -/
@[hjo "lem_cm_straighten_decreases"]
theorem straightenMeasure_lt_of_step {w w' : List StraightenLetter} (h : StraightenStep w w') :
    straightenMeasure w' < straightenMeasure w := by
  cases h with
  | keep u v cs cs' i hlen hpos =>
    rw [straightenMeasure_loop_block_eq_block_loop_add u v cs cs' i hlen]
    omega
  | drop u v cs cs' i hlen hpos =>
    rw [straightenMeasure_loop_block_eq_block_add u v cs cs' i hlen]
    omega

/-- The straightening rewriting is well founded: `μ` is an `ℕ`-valued statistic that falls at every
step, so the relation is a subrelation of the pullback of `<` on `ℕ` along `μ`. -/
theorem wellFounded_straightenStep :
    WellFounded (fun w' w : List StraightenLetter => StraightenStep w w') :=
  Subrelation.wf (fun h => straightenMeasure_lt_of_step h)
    (InvImage.wf straightenMeasure Nat.lt_wfRel.wf)

/-- **The rewriting cannot be applied indefinitely.** No sequence of words is an infinite chain of
straightening steps: `μ` falls by at least one at each step, so `μ (f n) + n ≤ μ (f 0)`, which
fails at `n = μ (f 0) + 1`. -/
@[hjo "lem_cm_straighten_decreases"]
theorem not_forall_straightenStep (f : ℕ → List StraightenLetter) :
    ¬ ∀ n, StraightenStep (f n) (f (n + 1)) := by
  intro h
  have key : ∀ n, straightenMeasure (f n) + n ≤ straightenMeasure (f 0) := by
    intro n
    induction n with
    | zero => omega
    | succ n ih =>
      have hlt := straightenMeasure_lt_of_step (h n)
      omega
  have := key (straightenMeasure (f 0) + 1)
  omega

end HJO.Dyck
