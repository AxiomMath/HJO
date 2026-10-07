/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.Shuffle.BraidTypeBDictionary
public import HJO.Shuffle.MellitThm58Floor
public meta import HJO.Attr

/-! # Rule `BE` with the lower data eliminated: the residual names the two extra moves

`HJO.Mellit.braidValueColouring_sweepRecursionBEFloor_of_move` reduces the floored `BE` clause for
`HJO.Mellit.braidValueColouring` to one hypothesis `hmove` at every bracketed point — an identity
between `HJO.Mellit.braidValueOfData` at three data tuples, two of which are read off the *upper*
level and one off the *lower* one. The lower tuple is the obstacle: it is named by its own
colouring, so `hmove` says nothing about how the two sides are related and in particular nothing
about the two extra moves that `HJO.Mellit.Isolates.length_specialMoveList_of_eventType_B` counts.

`HJO/Shuffle/BraidTypeBDictionary.lean` removes that obstacle. Its
`HJO.Mellit.Isolates.braidData_of_eventType_B` writes the lower data *as a function of the upper
data*: with `j = HJO.Mellit.typeBIndex yB ηlo X`,

* the positions are the upper positions read along `j.succAbove`, rigidly rotated by
  `HJO.Mellit.levelDropShift` — one entry deleted and nothing else;
* the multiplicities are the upper multiplicities read along `j.succAbove`, with the entry at `j`
  overwritten by `α_hi j + α_hi (j+1) + 1` — the two upper components `j` and `j + 1` merged, and
  one crossing restored.

This file substitutes that into `hmove`. What comes out —
`HJO.Mellit.Isolates.braidValueColouring_eq_dminus_add_smul_of_merge` and the floored clause
`HJO.Mellit.braidValueColouring_sweepRecursionBEFloor_of_merge` — mentions the lower level only
through the rotation, and the two extra moves are *named*: they are the `+ 1` on the merged entry
and the merge itself, both sitting on the single index `i₀` of the lower data.

## What this is and what it is not

It is a **rewriting**, and it is worth exactly what the dictionary behind it is worth. `hmerge` is
equivalent to `hmove` instance by instance, the chain between them being a chain of equalities; no
braid combinatorics is done here and none is claimed. What changes is that the residual is now in
the shape a `d^♭_-` analogue of `HJO.Mellit.braidValueOfData_succAbove_eq_dplus` could be stated
against: at type `A` the corresponding description is an *insertion* of an entry of multiplicity
`1`, and that theorem turns it into a braid-value identity; here it is a *merge* of two entries, and
no such theorem exists in this library.

`hmerge` is proved nowhere, at no point and for no `(a, b, N)`. Neither is `hmove`.

## Genericity

Nothing new is excluded. `q ≠ 0`, `q ≠ 1`, `q + 1 ≠ 0`, `r * r = q` are `HJO.Sweep.braidRepMellit`'s
and are what `HJO.Mellit.braidValueColouring` already needs; `u ≠ 0` is not spent and no inverse in
`u` is evaluated. The dictionary itself is pure `ℕ`/`ℤ`/`ℚ` and carries no field hypothesis; the
field enters only through `HJO.Mellit.braidValueOfData`, which the clause being rewritten already
mentions.

`hmerge` is undischarged at every point, and
`HJO.Mellit.braidValueColouring_sweepRecursionsFloor` covers the whole level recursion.
`HJO.Mellit.SweepRecursionBEFloor` itself is proved by a different route:
`HJO.Mellit.braidValueColouring_sweepRecursionBEFloor` (`HJO/Shuffle/BraidBECut.lean`), which
does not go through this file.

## References

Transcribing A. Mellit, *Toric braids and
`(m, n)`-parking functions*, Sections 4 and 5.
-/

@[expose] public section

open Finset

namespace HJO.Mellit

open ParkingFunctions Paths Sweep Braid

variable {L : Type*} [Field L] [Algebra ℚ L] {a b N X Y : ℕ} {ηlo ηhi : ℚ}

namespace Isolates

/-- **Rule `BE` at one bracketed point, with the lower data replaced by its dictionary value.**
The hypothesis `hmove` of `HJO.Mellit.Isolates.braidValueColouring_eq_dminus_add_smul_of_move` is
traded for `hmerge`, in which the lower special-braid data no longer appears: its positions are the
upper ones read along `j.succAbove` and rotated by `HJO.Mellit.levelDropShift`, and its
multiplicities are the upper ones read along `j.succAbove` with the entry at `i₀` overwritten by
`α_hi j + α_hi (j+1) + 1`.

The two extra moves of `HJO.Mellit.Isolates.length_specialMoveList_of_eventType_B` are exactly what
that overwriting adds, and they sit on the one index `i₀`
(`HJO.Mellit.Isolates.count_specialMoveList_typeBIndex_of_eventType_B`).

This is a rewriting of `hmove` through
`HJO.Mellit.Isolates.braidData_of_eventType_B` and is equivalent to it; neither is proved. -/
theorem braidValueColouring_eq_dminus_add_smul_of_merge
    (q u : L) {r : L} (hq : q ≠ 0) (hq1 : q ≠ 1) (hqp : q + 1 ≠ 0) (hr : r * r = q) (ha : 0 < a)
    (hb : 0 < b) (hN : 0 < N) (hI : Isolates a b N X Y ηlo ηhi)
    (hηlo : ((a * N : ℕ) : ℚ) < ηlo) {yB yE : Heights a b N} (hyB : IsAboveDiagonal yB)
    (hyE : IsAboveDiagonal yE) (hevB : eventType yB (X, Y) = EventType.B)
    (hevE : eventType yE (X, Y) = EventType.E) (hcol : colouring yB ηlo = colouring yE ηlo)
    {k : ℕ} (hk : #(colouringEast yB ηlo) = k) (j j' : Fin (k + 1))
    (hj : (j : ℕ) = typeBIndex yB ηlo X) (hj' : (j' : ℕ) = typeBIndex yB ηlo X + 1) (i₀ : Fin k)
    (hi₀ : (i₀ : ℕ) = typeBIndex yB ηlo X)
    (hmerge : braidValueOfData q u hq hq1 hqp hr a b N
          (fun i => (braidDataOfColouring a b N yB ηhi (k + 1)).1 (j.succAbove i)
            + levelDropShift a b N ηlo ηhi)
          (Function.update
            (fun i => (braidDataOfColouring a b N yB ηhi (k + 1)).2 (j.succAbove i)) i₀
            ((braidDataOfColouring a b N yB ηhi (k + 1)).2 j
              + (braidDataOfColouring a b N yB ηhi (k + 1)).2 j' + 1))
        = dminus q (k + 1) (braidValueOfData q u hq hq1 hqp hr a b N
              (braidDataOfColouring a b N yB ηhi (k + 1)).1
              (braidDataOfColouring a b N yB ηhi (k + 1)).2)
          + u • braidValueOfData q u hq hq1 hqp hr a b N
              (braidDataOfColouring a b N yE ηhi k).1
              (braidDataOfColouring a b N yE ηhi k).2) :
    braidValueColouring q u hq hq1 hqp hr a b N ηlo (colouring yB ηlo)
      = dminus q (sweepWidth yB (X, Y))
          (braidValueColouring q u hq hq1 hqp hr a b N ηhi (colouring yB ηhi))
        + u • braidValueColouring q u hq hq1 hqp hr a b N ηhi (colouring yE ηhi) := by
  have hηhi : ((a * N : ℕ) : ℚ) < ηhi := hηlo.trans (hI.ltP.trans hI.Plt)
  have hX0 : 0 < X := hI.pos_fst_of_eventType_B_of_lt hηlo hyB hevB
  have hne : ((X, Y) : ℕ × ℕ) ≠ ((0 : ℕ), (0 : ℕ)) := by
    intro h
    rw [Prod.mk.injEq] at h
    omega
  refine hI.braidValueColouring_eq_dminus_add_smul_of_move q u hq hq1 hqp hr ha hb hN hηhi hyB
    hyE hevB hevE hcol hne hk ?_
  have hfst : (braidDataOfColouring a b N yB ηlo k).1
      = fun i => (braidDataOfColouring a b N yB ηhi (k + 1)).1 (j.succAbove i)
          + levelDropShift a b N ηlo ηhi :=
    funext fun i => hI.braidData_fst_succAbove ha hb hN hηlo hyB hevB hk j hj i
  have hsnd : (braidDataOfColouring a b N yB ηlo k).2
      = Function.update
          (fun i => (braidDataOfColouring a b N yB ηhi (k + 1)).2 (j.succAbove i)) i₀
          ((braidDataOfColouring a b N yB ηhi (k + 1)).2 j
            + (braidDataOfColouring a b N yB ηhi (k + 1)).2 j' + 1) := by
    funext i
    by_cases h : i = i₀
    · subst h
      rw [Function.update_self]
      exact (hI.braidData_snd_typeBIndex_add_succ ha hb hN hηlo hyB hevB hk j j' hj hj' i hi₀).symm
    · rw [Function.update_of_ne h]
      exact (hI.braidData_snd_succAbove_of_ne ha hb hN hηlo hyB hevB hk j hj i
        (fun hc => h (Fin.ext (hc.trans hi₀.symm)))).symm
  rw [hfst, hsnd]
  exact hmerge

end Isolates

/-! ### The floored clause, reduced to the merge identity -/

/-- **`HJO.Mellit.SweepRecursionBEFloor` for `HJO.Mellit.braidValueColouring`, given the merge
identity at every bracketed point.** This is
`HJO.Mellit.braidValueColouring_sweepRecursionBEFloor_of_move` with its hypothesis rewritten through
the type-`B` row: the lower special-braid data has been eliminated, and what the clause now asks for
is an identity between braid values of *upper* data only, one of them with the two components `j`
and `j + 1` merged into one and one crossing restored.

The indices are quantified rather than computed, because the `Fin` bounds they need —
`HJO.Mellit.Isolates.typeBIndex_succ_le` — are consequences of the hypotheses. Any consumer produces
them from that lemma.

`hmerge` is proved nowhere, at no point and for no `(a, b, N)`.
`HJO.Mellit.SweepRecursionBEFloor` itself is proved by a different route:
`HJO.Mellit.braidValueColouring_sweepRecursionBEFloor` (`HJO/Shuffle/BraidBECut.lean`), not
through this theorem. -/
theorem braidValueColouring_sweepRecursionBEFloor_of_merge
    (q u : L) {r : L} (hq : q ≠ 0) (hq1 : q ≠ 1) (hqp : q + 1 ≠ 0) (hr : r * r = q) (ha : 0 < a)
    (hb : 0 < b) (hN : 0 < N)
    (hmerge : ∀ (X Y : ℕ) (ηlo ηhi : ℚ), ((a * N : ℕ) : ℚ) < ηlo →
      Isolates a b N X Y ηlo ηhi → ∀ yB yE : Heights a b N, IsAboveDiagonal yB →
        IsAboveDiagonal yE → eventType yB (X, Y) = EventType.B →
          eventType yE (X, Y) = EventType.E → colouring yB ηlo = colouring yE ηlo →
            ∀ (j j' : Fin (#(colouringEast yB ηlo) + 1)) (i₀ : Fin #(colouringEast yB ηlo)),
              (j : ℕ) = typeBIndex yB ηlo X → (j' : ℕ) = typeBIndex yB ηlo X + 1 →
                (i₀ : ℕ) = typeBIndex yB ηlo X →
                  braidValueOfData q u hq hq1 hqp hr a b N
                      (fun i => (braidDataOfColouring a b N yB ηhi
                          (#(colouringEast yB ηlo) + 1)).1 (j.succAbove i)
                        + levelDropShift a b N ηlo ηhi)
                      (Function.update
                        (fun i => (braidDataOfColouring a b N yB ηhi
                          (#(colouringEast yB ηlo) + 1)).2 (j.succAbove i)) i₀
                        ((braidDataOfColouring a b N yB ηhi
                            (#(colouringEast yB ηlo) + 1)).2 j
                          + (braidDataOfColouring a b N yB ηhi
                            (#(colouringEast yB ηlo) + 1)).2 j' + 1))
                    = dminus q (#(colouringEast yB ηlo) + 1)
                        (braidValueOfData q u hq hq1 hqp hr a b N
                          (braidDataOfColouring a b N yB ηhi
                            (#(colouringEast yB ηlo) + 1)).1
                          (braidDataOfColouring a b N yB ηhi
                            (#(colouringEast yB ηlo) + 1)).2)
                      + u • braidValueOfData q u hq hq1 hqp hr a b N
                          (braidDataOfColouring a b N yE ηhi #(colouringEast yB ηlo)).1
                          (braidDataOfColouring a b N yE ηhi #(colouringEast yB ηlo)).2) :
    SweepRecursionBEFloor q u a b N (braidValueColouring q u hq hq1 hqp hr a b N) := by
  intro P ηlo ηhi hfloor hlo hhi hP1 hP2 hltP hPlt hiso yB yE hyB hyE _ hevB hevE hcol
  obtain ⟨X, Y⟩ := P
  have hI : Isolates a b N X Y ηlo ηhi := ⟨hlo, hhi, hltP, hPlt, hiso, hP1, hP2⟩
  have hle := hI.typeBIndex_succ_le ha hb hN hfloor hyB hevB (y := yB)
  exact hI.braidValueColouring_eq_dminus_add_smul_of_merge q u hq hq1 hqp hr ha hb hN hfloor hyB
    hyE hevB hevE hcol rfl ⟨typeBIndex yB ηlo X, by omega⟩ ⟨typeBIndex yB ηlo X + 1, by omega⟩
    rfl rfl ⟨typeBIndex yB ηlo X, by omega⟩ rfl
    (hmerge X Y ηlo ηhi hfloor hI yB yE hyB hyE hevB hevE hcol _ _ _ rfl rfl rfl)

end HJO.Mellit

end
