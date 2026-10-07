/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.CMStructure.StraightenMeasure
public meta import HJO.Attr

/-! # The straightening measure does not bound the second move of
`HJO.Sweep.exists_linearEquiv_e0Ideal`

**This file is a negative, and a permanent record.** The proof of
`HJO.Sweep.exists_linearEquiv_e0Ideal` reduces a word of `e_k𝔸_qe_0` to a normal form by four moves,
and justifies the termination of the reduction like this:

> Iterating the second and fourth moves drives every Hecke generator to an end, where the third
> removes it. [...] That the iteration terminates is Lemma `HJO.Dyck.straightenMeasure_lt_of_step`:
the
> measure of Definition `HJO.Dyck.straightenMeasure` --- for each `T`-letter, the number of corner
> letters to its right --- takes values in `ℕ` and falls by at least one at every application of the
> fourth move.

The second sentence is about the FOURTH move only, and that restriction is not an accident of the
writing: the SECOND move strictly RAISES `μ`. The second move is `HJO.Dyck.Aq.dPlus_mul_yElt`,

`d₊y_i^{(k)} = W_iy_i^{(k+1)}W_i^{-1}d₊` with `W_i = T_1T_2⋯T_i`,

which inserts the `i` loop letters of `W_i` immediately to the LEFT of a corner letter. By
`HJO.Dyck.straightenMeasure_insert_loop` each of them contributes at least that corner letter, so
`μ` rises by at least `i ≥ 1`. A statistic that strictly increases under one of the two moves being
iterated cannot witness the termination of the joint iteration, and `HJO.Dyck.StraightenStep`, the
Lean form of the rewriting, has exactly the two constructors of the fourth move and no others.

So the measure is sound where it is proved and does not reach the claim it is cited for. The gap
looks repairable by PHASE SEPARATION — run the first and second moves to completion first, under
their own measure (the number of arrow letters, then the number of letters standing to the right of
a `d₊` letter, neither of which the fourth move disturbs), and only then the third and fourth under
`μ`. That is not the argument usually given. Note also that `μ` is UNCHANGED when a loop
letter moves rightwards past a lowering arrow — the relation `T_id₋ = d₋T_i` of `HJO.Dyck.Aq`, which
is what brings a loop letter to the left end for the third move — so even inside the second phase
`μ` does not fall at every step, and the repaired measure has to be lexicographic.

One further remark, on the alphabet. `W_i^{-1}` is not a word in the letters of
`HJO.Dyck.straightenMeasure` at all — that alphabet is the loops, the corner elements and the
arrows, with no inverse loops — and rewriting it by `HJO.Dyck.Aq.Tg_mul_Tinv` in the form
`T_j^{-1} = q^{-1}(T_j + (q-1))` replaces each inverse letter by a loop letter or by nothing, so the
expansion of the right-hand side of the second move carries up to `2i` new loop letters and not
merely `i`. The lemmas below are stated for an arbitrary nonempty block of loop letters, so they
cover every term of that expansion at once.

## Main results

* `HJO.Dyck.straightenMeasure_le_of_prefix_loops`: prefixing any block of loop letters to a corner
  letter does not lower `μ`.
* `HJO.Dyck.straightenMeasure_lt_of_prefix_loops`: prefixing a NONEMPTY such block strictly raises
  it.
* `HJO.Dyck.straightenMeasure_lt_moveTwo`: the second move, read on words, strictly raises `μ`,
  whatever the surrounding word and whatever nonempty Hecke block the move inserts. Contrast
  `HJO.Dyck.straightenMeasure_lt_of_step`, the fourth move, which falls.
* `HJO.Dyck.straightenMeasure_moveTwo_witness`: the smallest instance with both values computed —
  `μ(d₊y_1) = 0` while `μ(T_1y_1T_1d₊) = 1` and `μ(T_1y_1d₊) = 1`.

## References

The proof of Lemma
`HJO.Sweep.exists_linearEquiv_e0Ideal`, the measure of Definition `HJO.Dyck.straightenMeasure`,
Lemma `HJO.Dyck.straightenMeasure_lt_of_step` and the second move `HJO.Dyck.Aq.dPlus_mul_yElt`.
-/

@[expose] public section

namespace HJO.Dyck

open StraightenLetter

@[simp] theorem isLoop_raise (k : ℕ) : (raise k).isLoop = false := rfl
@[simp] theorem isCorner_raise (k : ℕ) : (raise k).isCorner = false := rfl
@[simp] theorem isLoop_lower (k : ℕ) : (lower k).isLoop = false := rfl
@[simp] theorem isCorner_lower (k : ℕ) : (lower k).isCorner = false := rfl

/-- A word of loop letters is exactly that: each of its letters is `loop j` for some `j`. -/
theorem exists_eq_loop {x : StraightenLetter} (h : x.isLoop = true) : ∃ j, x = loop j := by
  cases x with
  | loop j => exact ⟨j, rfl⟩
  | corner _ => simp at h
  | raise _ => simp at h
  | lower _ => simp at h

/-- **Prefixing a block of loop letters to a corner letter does not lower `μ`.** Each inserted
letter stands to the left of the corner letter, so by `HJO.Dyck.straightenMeasure_insert_loop` it
contributes a nonnegative amount. -/
theorem straightenMeasure_le_of_prefix_loops (u v : List StraightenLetter) (i : ℕ) :
    ∀ ws : List StraightenLetter, (∀ x ∈ ws, x.isLoop = true) →
      straightenMeasure (u ++ corner i :: v)
        ≤ straightenMeasure (u ++ (ws ++ corner i :: v)) := by
  intro ws
  induction ws with
  | nil => intro _; simp
  | cons x ws ih =>
    intro hws
    obtain ⟨j, rfl⟩ := exists_eq_loop (hws x List.mem_cons_self)
    have ihv := ih fun y hy => hws y (List.mem_cons_of_mem _ hy)
    have hstep : straightenMeasure (u ++ loop j :: (ws ++ corner i :: v))
        = straightenMeasure (u ++ (ws ++ corner i :: v))
          + (ws ++ corner i :: v).countP isCorner :=
      straightenMeasure_insert_loop u (ws ++ corner i :: v) j
    rw [List.cons_append]
    omega

/-- **Prefixing a nonempty block of loop letters to a corner letter strictly raises `μ`.** This is
the arithmetic behind the failure this file records: the inserted letters all stand to the left of
the corner letter, and each of them therefore sees at least one corner letter. -/
theorem straightenMeasure_lt_of_prefix_loops (u v ws : List StraightenLetter)
    (hws : ∀ x ∈ ws, x.isLoop = true) (hne : ws ≠ []) (i : ℕ) :
    straightenMeasure (u ++ corner i :: v)
      < straightenMeasure (u ++ (ws ++ corner i :: v)) := by
  obtain ⟨x, ws', rfl⟩ : ∃ x ws', ws = x :: ws' := by
    cases ws with
    | nil => exact absurd rfl hne
    | cons x ws' => exact ⟨x, ws', rfl⟩
  obtain ⟨j, rfl⟩ := exists_eq_loop (hws x List.mem_cons_self)
  have hle := straightenMeasure_le_of_prefix_loops u v i ws'
    fun y hy => hws y (List.mem_cons_of_mem _ hy)
  have hstep : straightenMeasure (u ++ loop j :: (ws' ++ corner i :: v))
      = straightenMeasure (u ++ (ws' ++ corner i :: v))
        + (ws' ++ corner i :: v).countP isCorner :=
    straightenMeasure_insert_loop u (ws' ++ corner i :: v) j
  have hpos : 1 ≤ (ws' ++ corner i :: v).countP isCorner := by
    rw [List.countP_append, List.countP_cons]
    simp only [isCorner_corner, ite_true]
    omega
  rw [List.cons_append]
  omega

/-- **The second move of the proof of `HJO.Sweep.exists_linearEquiv_e0Ideal` strictly raises `μ`.**
On the left the word carries the factor `d₊y_i`; on the right the move has replaced it by a Hecke
block `ws`, the corner letter, and the raising arrow. `ws` is any nonempty block of loop letters —
the letters of `W_i`, together with those of the expansion of `W_i^{-1}` when they too are placed to
the left of the corner letter. Whatever the surrounding word `u`, `v`, the right-hand side has
strictly larger measure.

This is what the citation of `HJO.Dyck.straightenMeasure_lt_of_step` for the iteration of the
second and fourth moves jointly does not survive. -/
theorem straightenMeasure_lt_moveTwo (u v ws : List StraightenLetter)
    (hws : ∀ x ∈ ws, x.isLoop = true) (hne : ws ≠ []) (i k : ℕ) :
    straightenMeasure (u ++ raise k :: corner i :: v)
      < straightenMeasure (u ++ (ws ++ corner i :: raise k :: v)) := by
  have hL : straightenMeasure (u ++ raise k :: corner i :: v)
      = straightenMeasure (u ++ corner i :: raise k :: v) := by
    have h1 : straightenMeasure ((u ++ [raise k]) ++ corner i :: v)
        = straightenMeasure ((u ++ [raise k]) ++ v) + (u ++ [raise k]).countP isLoop :=
      straightenMeasure_insert_corner (u ++ [raise k]) v i
    have h2 : straightenMeasure (u ++ corner i :: raise k :: v)
        = straightenMeasure (u ++ raise k :: v) + u.countP isLoop :=
      straightenMeasure_insert_corner u (raise k :: v) i
    have h3 : (u ++ [raise k]).countP isLoop = u.countP isLoop := by
      rw [List.countP_append]; simp
    have h4 : ((u ++ [raise k]) ++ corner i :: v) = u ++ raise k :: corner i :: v := by simp
    have h5 : ((u ++ [raise k]) ++ v) = u ++ raise k :: v := by simp
    rw [← h4, h1, h3, h5, h2]
  rw [hL]
  exact straightenMeasure_lt_of_prefix_loops u (raise k :: v) ws hws hne i

/-- **The smallest witness, with all three values computed.** The word `d₊y_1` has measure `0`;
the two words `T_1y_1T_1d₊` and `T_1y_1d₊` — the shape of the two terms of the right-hand side of
`HJO.Dyck.Aq.dPlus_mul_yElt` at `i = 1`, once `T_1^{-1}` has been expanded by
`HJO.Dyck.Aq.Tg_mul_Tinv` — have measure `1`. So the move raises `μ` from `0` to `1` on every
term of its own expansion. -/
theorem straightenMeasure_moveTwo_witness :
    straightenMeasure [raise 0, corner 1] = 0 ∧
      straightenMeasure [loop 1, corner 1, loop 1, raise 0] = 1 ∧
      straightenMeasure [loop 1, corner 1, raise 0] = 1 :=
  ⟨rfl, rfl, rfl⟩

end HJO.Dyck

end
