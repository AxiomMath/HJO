/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.Shuffle.BraidCDIndices
public import HJO.Shuffle.BraidTypeABelowTheta

/-! # The below-`θ` regime of the type-`A` clause is EMPTY

`HJO/Shuffle/BraidTypeABelowTheta.lean` shows that at a bottom insertion all of whose moving
stage positions are below the puncture `θ` the type-`A` clause of
`HJO.Mellit.braidValueColouring_sweepRecursionsFloor` is equivalent to an identity between
two *different* operators, `d_+` and `-y_1d^*_+`
(`HJO.Mellit.braidValueOfData_eq_dplus_iff_of_specialBraid_eq_phiPlusStar`,
`HJO.Mellit.dplus_ne_negYOneDPlusStar_auxVar_one_sq`). It closes by naming the one question that
would turn that into a refutation of the clause: **does a type-`A` event with a move, all of whose
special-braid moves lie below `θ`, exist?**

**It does not, and the reason has nothing to do with type `A`: no colouring of any above-diagonal
path at any admissible level has one.** The below-`θ` regime is therefore vacuous, the clause
survives it, and what remains of the type-`A` clause is entirely the above-`θ` case.

## The mechanism, in one line

Every component of a colouring **ends** below `θ`, and a move made from below `θ` lands above
`1 - θ`. So the last move of a component is never made from below `θ`.

In detail. A component is a maximal run of crossings of the level line, and
`HJO.Mellit.componentLeft` — the abscissa at which the line enters the region through the crossed
north step — is the *column* of that north step, hence an integer. The bottom crossing of the
component is the first crossing at or after that integer, and consecutive crossings are `θ` apart,
so its abscissa lies in `[x, x + θ)` and its torus coordinate in `[0, θ)`:
`HJO.Mellit.fract_crossingAbscissa_componentBotIndex_lt_sweepTheta`. Since the `α_i` crossings of
the component are listed downwards from `v_i` by the iterates of `HJO.Braid.nextCrossing`
(`HJO.Mellit.iterate_nextCrossing_fract_crossingAbscissa`), the position the component reaches after
all `α_i - 1` of its moves is that bottom crossing, hence below `θ`:
`HJO.Mellit.iterate_nextCrossing_braidDataOfColouring_lt_sweepTheta`.

But `nx_θ` on an argument below `θ` is `x \mapsto x + 1 - θ`, which for `x \ge 0` and `θ < 1/2`
exceeds `θ` (`HJO.Braid.sweepTheta_lt_nextCrossing`; `θ < 1/2` is
`HJO.Mellit.sweepTheta_lt_half`, which needs `a < b` and so holds throughout the range the shuffle
route quantifies over). So the position *before* the last move cannot have been below `θ`:
`HJO.Mellit.sweepTheta_lt_iterate_nextCrossing_braidDataOfColouring`.

## The verdict

* `HJO.Mellit.not_forall_iterate_nextCrossing_lt_sweepTheta` — at a component of multiplicity at
  least `2`, not all of its moves are below `θ`.
* `HJO.Mellit.specialMoveList_braidDataOfColouring_eq_nil_of_forall_lt`,
  `HJO.Mellit.specialBraid_braidDataOfColouring_eq_one_of_forall_lt` and — in the
  `Fin.succAbove`-shifted shape that lemma actually asks it —
  `HJO.Mellit.specialMoveList_comp_succAbove_eq_nil_of_forall_lt`: the `hlt` hypothesis of
  `HJO.Braid.specialBraid_eq_phiPlusStar_of_lt`, read at a colouring's own data, forces the move
  sequence to be **empty** and the special braid to be the identity of `HJO.Braid.BraidMonoid`. So
  in the regime that lemma covers there is no letter at all, the `φ^*_+` identity it supplies is
  `1 = φ^*_+(1)`, and `HJO.Mellit.braidValueOfData_eq_negYOneDPlusStar` reduces to
  `HJO.Sweep.dplus_dplusIter`, where `d_+` and `-y_1d^*_+` agree by that very lemma. Nothing is
  refuted and nothing is owed.
* `HJO.Mellit.not_exists_eventType_A_forall_move_lt_sweepTheta` — the question as asked, answered:
  there is no type-`A` event at coprime `1 < a < b` with a moving component all of whose moves are
  below `θ`.

## Why the answer is not vacuous for want of instances

The type-`A` hypotheses of that last statement are **not** what makes it false; they are carried
because they are the question. Every one of them is satisfiable together with `2 \le \alpha_i`, and
that is a theorem here and not a remark:
`HJO.Mellit.exists_eventType_A_and_two_le_braidDataOfColouring_snd` exhibits the whole conjunction
minus its last clause at the witness of `HJO/Shuffle/BraidTypeAWitness.lean` — `a = 2`,
`b = 5`, `N = 1`, `HJO.Mellit.gapPath`, `P = (1, 5)`, `\eta_\pm = 31/2, 33/2` — whose component `0`
has multiplicity `2` (`HJO.Mellit.braidData_gap_snd_zero`). So the `¬∃` refutes the below-`θ` clause
and not the configuration.

`HJO.Mellit.sweepTheta_lt_braidData_gap_fst_zero` is the general theorem firing at that same
witness, and it returns the number the witness file computed by hand: `θ = 3/10 < 17/40 = v_0`
(`HJO.Mellit.sweepTheta_gap`, `HJO.Mellit.braidData_gap_fst_zero`).

## Genericity

No scalar field and no operator appears here: every statement is about `ℚ`-valued positions and the
combinatorics of the crossing lattice, so no letter can degenerate and no inverse is evaluated.
The parameter hypotheses are `0 < a`, `0 < b`, `0 < N` and — only where `θ < 1/2` is needed —
`a < b`, all of them inside the range of `HJO.Mellit.braidValueColouring_sweepRecursionsFloor`. The
`¬∃` additionally carries `1 < a` and `Nat.Coprime a b`, which the proof does not consume; it is
therefore the statement about the smaller, coprime, `1 < a < b` range, and true a fortiori on it.

## References

A. Mellit, *Toric braids and `(m, n)`-parking functions*, section 5.
-/

@[expose] public section

open Finset

namespace HJO.Braid

/-! ### A move made from below the puncture lands above `1 - θ` -/

/-- **`nx_θ` carries the window `[0, θ]` above `1 - θ`.** Off the branch `θ < x`, the next-crossing
map of `HJO.Braid.nextCrossing` is `x \mapsto x + 1 - θ`, so at `θ < 1/2` its value exceeds `θ`.
This is the whole obstruction: a component whose trajectory ends below `θ` cannot have made its last
move from below `θ`. -/
theorem sweepTheta_lt_nextCrossing {θ x : ℚ} (hθ : θ < 1 / 2) (hx : 0 ≤ x) (h : ¬ θ < x) :
    θ < nextCrossing θ x := by
  rw [nextCrossing, ite_eq_right_of_eq_false _ _ (eq_false h)]
  linarith

end HJO.Braid

namespace HJO.Mellit

open ParkingFunctions Paths Sweep Braid

variable {a b N : ℕ}

/-! ### The bottom crossing of a component is below the puncture -/

/-- **THE GEOMETRIC INPUT: a component ends below `θ`.** `HJO.Mellit.componentLeft` is the column
of the crossed north step through which the level line enters the region, hence a natural number;
`HJO.Mellit.componentBotIndex` is the ceiling that names the first crossing at or after it; and
consecutive crossings are `θ` apart (`HJO.Mellit.crossingAbscissa_succ`). So the bottom crossing has
abscissa in `[x, x + θ)` for that integer `x`, and its torus coordinate — the fractional part — is
in `[0, θ)`.

Nothing about the path, the level or the event type enters: this holds at every component of every
colouring. -/
theorem fract_crossingAbscissa_componentBotIndex_lt_sweepTheta (ha : 0 < a) (hb : 0 < b)
    (hN : 0 < N) (y : Heights a b N) (η : ℚ) (i : ℕ) :
    Int.fract (crossingAbscissa a b N η (componentBotIndex a b N y η i)) < sweepTheta a b N := by
  have hs := one_add_sweepSlope_pos (a := a) (b := b) (N := N) ha hb hN
  have hθmul := sweepTheta_mul (a := a) (b := b) (N := N) hs.ne'
  obtain ⟨hθ0, hθ1⟩ := sweepTheta_mem_Ioo (a := a) (b := b) (N := N) ha hb hN
  set x : ℕ := ((sortByColumn (colouringNorth y η)).getD i (0, 0)).1 with hxdef
  have hL : componentLeft y η i = ((x : ℕ) : ℚ) := rfl
  have hle : ((x : ℕ) : ℚ) ≤ crossingAbscissa a b N η (componentBotIndex a b N y η i) := by
    rw [← hL]
    exact componentLeft_le_crossingAbscissa hs y η i le_rfl
  have hup : crossingAbscissa a b N η (componentBotIndex a b N y η i)
      < ((x : ℕ) : ℚ) + sweepTheta a b N := by
    have hceil : ((componentBotIndex a b N y η i : ℤ) : ℚ)
        < (1 + sweepSlope a b N) * ((x : ℕ) : ℚ) + levelIntercept a N η + 1 := by
      rw [componentBotIndex, ← hL]
      exact Int.ceil_lt_add_one _
    have hexp : (((x : ℕ) : ℚ) + sweepTheta a b N) * (1 + sweepSlope a b N)
        = (1 + sweepSlope a b N) * ((x : ℕ) : ℚ) + 1 := by linear_combination hθmul
    rw [crossingAbscissa, div_lt_iff₀ hs, hexp]
    linarith
  rw [show crossingAbscissa a b N η (componentBotIndex a b N y η i)
      = ((x : ℕ) : ℚ)
        + (crossingAbscissa a b N η (componentBotIndex a b N y η i) - ((x : ℕ) : ℚ)) from by ring,
    Int.fract_natCast_add, Int.fract_eq_self.2 ⟨by linarith, by linarith⟩]
  linarith

/-! ### The position a component reaches after all its moves -/

/-- **The trajectory of a component ends below `θ`.** Its `α_i` crossings are the iterates
`nx_θ^j(v_i)` for `j < α_i` (`HJO.Mellit.iterate_nextCrossing_fract_crossingAbscissa`), and the last
of them is the crossing of the bottom index, which
`HJO.Mellit.fract_crossingAbscissa_componentBotIndex_lt_sweepTheta` puts below `θ`. -/
theorem iterate_nextCrossing_braidDataOfColouring_lt_sweepTheta (ha : 0 < a) (hb : 0 < b)
    (hN : 0 < N) {η : ℚ} (hη : IsAdmissibleLevel η) (hηpos : 0 < η) (y : Heights a b N) {k : ℕ}
    (i : Fin k) (hα : 1 ≤ (braidDataOfColouring a b N y η k).2 i) :
    (nextCrossing (sweepTheta a b N))^[(braidDataOfColouring a b N y η k).2 i - 1]
        ((braidDataOfColouring a b N y η k).1 i) < sweepTheta a b N := by
  have hcard := braidDataOfColouring_snd_eq_toNat a b N y η _ i
  have hidx : componentTopIndex a b N y η (i : ℕ)
      - (((braidDataOfColouring a b N y η k).2 i - 1 : ℕ) : ℤ)
      = componentBotIndex a b N y η (i : ℕ) := by rw [hcard] at hα ⊢; omega
  rw [braidDataOfColouring_fst,
    iterate_nextCrossing_fract_crossingAbscissa ha hb hN hη hηpos y (i : ℕ)
      (le_of_eq hidx.symm), hidx]
  exact fract_crossingAbscissa_componentBotIndex_lt_sweepTheta ha hb hN y η (i : ℕ)

/-! ### Hence the LAST move of a component is above the puncture -/

/-- **THE VERDICT AT ONE COMPONENT: the last move is made from above `θ`.** The move sequence of
`HJO.Braid.specialBraid` advances the `i`-th entry `α_i - 1` times, the last of them from the
position `nx_θ^{α_i - 2}(v_i)`; and that position is above `θ`.

For if it were below, `HJO.Braid.sweepTheta_lt_nextCrossing` would put the position after it above
`θ`, while `HJO.Mellit.iterate_nextCrossing_braidDataOfColouring_lt_sweepTheta` puts it below.
`a < b` enters only through `HJO.Mellit.sweepTheta_lt_half`. -/
theorem sweepTheta_lt_iterate_nextCrossing_braidDataOfColouring (ha : 0 < a) (hb : 0 < b)
    (hN : 0 < N) (hab : a < b) {η : ℚ} (hη : IsAdmissibleLevel η) (hηpos : 0 < η)
    (y : Heights a b N) {k : ℕ} (i : Fin k)
    (hα : 2 ≤ (braidDataOfColouring a b N y η k).2 i) :
    sweepTheta a b N
      < (nextCrossing (sweepTheta a b N))^[(braidDataOfColouring a b N y η k).2 i - 2]
          ((braidDataOfColouring a b N y η k).1 i) := by
  have hcard := braidDataOfColouring_snd_eq_toNat a b N y η _ i
  have hfin := iterate_nextCrossing_braidDataOfColouring_lt_sweepTheta ha hb hN hη hηpos y i
    (by omega)
  rw [show (braidDataOfColouring a b N y η k).2 i - 1
      = ((braidDataOfColouring a b N y η k).2 i - 2) + 1 from by omega,
    Function.iterate_succ_apply'] at hfin
  have hidx : componentBotIndex a b N y η (i : ℕ)
      ≤ componentTopIndex a b N y η (i : ℕ)
        - (((braidDataOfColouring a b N y η k).2 i - 2 : ℕ) : ℤ) := by
    rw [hcard] at hα ⊢; omega
  have hnn : 0 ≤ (nextCrossing (sweepTheta a b N))^[(braidDataOfColouring a b N y η k).2 i - 2]
      ((braidDataOfColouring a b N y η k).1 i) := by
    rw [braidDataOfColouring_fst,
      iterate_nextCrossing_fract_crossingAbscissa ha hb hN hη hηpos y (i : ℕ) hidx]
    exact Int.fract_nonneg _
  by_contra hcon
  exact absurd hfin (not_lt.2 (sweepTheta_lt_nextCrossing
    (sweepTheta_lt_half (a := a) (b := b) (N := N) ha hb hN hab) hnn hcon).le)

/-- **Not all the moves of a component are below `θ`.** The negation of the below-`θ` condition,
read as a statement about the iterates. -/
theorem not_forall_iterate_nextCrossing_lt_sweepTheta (ha : 0 < a) (hb : 0 < b) (hN : 0 < N)
    (hab : a < b) {η : ℚ} (hη : IsAdmissibleLevel η) (hηpos : 0 < η) (y : Heights a b N) {k : ℕ}
    (i : Fin k) (hα : 2 ≤ (braidDataOfColouring a b N y η k).2 i) :
    ¬ ∀ j < (braidDataOfColouring a b N y η k).2 i - 1,
        (nextCrossing (sweepTheta a b N))^[j] ((braidDataOfColouring a b N y η k).1 i)
          < sweepTheta a b N := fun h =>
  absurd (h _ (by omega))
    (not_lt.2 (sweepTheta_lt_iterate_nextCrossing_braidDataOfColouring ha hb hN hab hη hηpos y i
      hα).le)

/-! ### The below-`θ` hypothesis forces the empty word -/

/-- **The below-`θ` hypothesis of `HJO.Braid.specialBraid_eq_phiPlusStar_of_lt`, read at a
colouring's own data, forces the move sequence to be empty.**

The hypothesis quantifies over the suffixes `t_0 :: l'` of the move sequence, the moves of `l'`
having already been made. Only one suffix is needed: the sequence itself. Its head `t_0` occurs
`α_{t_0} - 1` times in the sequence and `α_{t_0} - 2` times in the tail
(`HJO.Braid.count_specialMoveList`), so the hypothesis read there is exactly that the **last** move
of `t_0` is made from below `θ` — which
`HJO.Mellit.sweepTheta_lt_iterate_nextCrossing_braidDataOfColouring` refutes. So the sequence has no
head, that is, no move. -/
theorem specialMoveList_braidDataOfColouring_eq_nil_of_forall_lt (ha : 0 < a) (hb : 0 < b)
    (hN : 0 < N) (hab : a < b) {η : ℚ} (hη : IsAdmissibleLevel η) (hηpos : 0 < η)
    (y : Heights a b N) {k : ℕ}
    (hlt : ∀ (t₀ : Fin k) (l' : List (Fin k)),
      t₀ :: l' <:+ specialMoveList (braidDataOfColouring a b N y η k).2 →
        moveTuple (sweepTheta a b N) (braidDataOfColouring a b N y η k).1 l' t₀
          < sweepTheta a b N) :
    specialMoveList (braidDataOfColouring a b N y η k).2 = [] := by
  by_contra hcon
  obtain ⟨t₀, l', hl⟩ := List.exists_cons_of_ne_nil hcon
  have hcount := count_specialMoveList (braidDataOfColouring a b N y η k).2 t₀
  rw [hl, List.count_cons_self] at hcount
  have hmove := hlt t₀ l' (by rw [hl])
  rw [moveTuple_apply_eq_iterate, show l'.count t₀
      = (braidDataOfColouring a b N y η k).2 t₀ - 2 from by omega] at hmove
  exact absurd hmove (not_lt.2 (sweepTheta_lt_iterate_nextCrossing_braidDataOfColouring ha hb hN
    hab hη hηpos y t₀ (by omega)).le)

/-- **Below `θ` the special braid of a colouring is the identity.** With no move there is no letter,
so `HJO.Braid.specialBraid` is the empty word.

This is what makes the below-`θ` case of the type-`A` clause empty rather than dangerous. The
`φ^*_+` identity `HJO.Braid.specialBraid_eq_phiPlusStar_of_lt` supplies in that regime reads
`1 = φ^*_+(1)`, and the operator identity
`HJO.Mellit.braidValueOfData_eq_negYOneDPlusStar` it feeds is then applied to the vacuum tower,
where `HJO.Sweep.dplus_dplusIter` says `d_+` and `-y_1d^*_+` agree. The disagreement
`HJO.Mellit.dplus_ne_negYOneDPlusStar_auxVar_one_sq` exhibits on `V_1` is therefore never reached
along this route. -/
theorem specialBraid_braidDataOfColouring_eq_one_of_forall_lt (ha : 0 < a) (hb : 0 < b) (hN : 0 < N)
    (hab : a < b) {η : ℚ} (hη : IsAdmissibleLevel η) (hηpos : 0 < η) (y : Heights a b N) {k : ℕ}
    (hlt : ∀ (t₀ : Fin k) (l' : List (Fin k)),
      t₀ :: l' <:+ specialMoveList (braidDataOfColouring a b N y η k).2 →
        moveTuple (sweepTheta a b N) (braidDataOfColouring a b N y η k).1 l' t₀
          < sweepTheta a b N) :
    specialBraid (sweepTheta a b N) (braidDataOfColouring a b N y η k).1
        (braidDataOfColouring a b N y η k).2 = 1 := by
  rw [specialBraid, specialMoveList_braidDataOfColouring_eq_nil_of_forall_lt ha hb hN hab hη hηpos
    y hlt, braidWord_nil]

/-- **The same, in the shape `HJO.Braid.specialBraid_eq_phiPlusStar_of_lt` asks it.** That lemma
reads the below-`θ` condition on the tuple of the lower level through `Fin.succAbove`, the inserted
entry being skipped: `hlt` there quantifies over the suffixes of
`specialMoveList (β ∘ j.succAbove)` and evaluates the lower tuple `w` at `j.succAbove t_0`. Read at
a colouring's own data it forces that sequence to be empty, so the lemma's conclusion in the
below-`θ` regime is `B_- = φ^*_+(1) = 1` and carries no letter.

`Fin.succAbove` being injective, the count of `j.succAbove t_0` in `l'.map j.succAbove` is the count
of `t_0` in `l'`, which at the sequence's own head is `α_{j.succAbove t_0} - 2`: the last move of
that entry, again. -/
theorem specialMoveList_comp_succAbove_eq_nil_of_forall_lt (ha : 0 < a) (hb : 0 < b) (hN : 0 < N)
    (hab : a < b) {η : ℚ} (hη : IsAdmissibleLevel η) (hηpos : 0 < η) (y : Heights a b N) {k : ℕ}
    (j : Fin (k + 1))
    (hlt : ∀ (t₀ : Fin k) (l' : List (Fin k)),
      t₀ :: l' <:+ specialMoveList ((braidDataOfColouring a b N y η (k + 1)).2 ∘ j.succAbove) →
        moveTuple (sweepTheta a b N) (braidDataOfColouring a b N y η (k + 1)).1
            (l'.map j.succAbove) (j.succAbove t₀) < sweepTheta a b N) :
    specialMoveList ((braidDataOfColouring a b N y η (k + 1)).2 ∘ j.succAbove) = [] := by
  by_contra hcon
  obtain ⟨t₀, l', hl⟩ := List.exists_cons_of_ne_nil hcon
  have hcount := count_specialMoveList
    ((braidDataOfColouring a b N y η (k + 1)).2 ∘ j.succAbove) t₀
  rw [hl, List.count_cons_self, Function.comp_apply] at hcount
  have hmove := hlt t₀ l' (by rw [hl])
  rw [moveTuple_apply_eq_iterate,
    List.count_map_of_injective _ _ (Fin.succAbove_right_injective (p := j)),
    show l'.count t₀ = (braidDataOfColouring a b N y η (k + 1)).2 (j.succAbove t₀) - 2 from by
      omega] at hmove
  exact absurd hmove (not_lt.2 (sweepTheta_lt_iterate_nextCrossing_braidDataOfColouring ha hb hN
    hab hη hηpos y (j.succAbove t₀) (by omega)).le)

/-! ### The question, answered -/

/-- **THERE IS NO TYPE-`A` EVENT WITH A MOVE ALL OF WHOSE MOVES LIE BELOW `θ`.** At coprime
`1 < a < b` with the level above `aN` — everything the shuffle route's induction supplies — no
above-diagonal path, isolating bracketing pair, type-`A` point and component of multiplicity at
least `2` has all `α_i - 1` of that component's moves made from below the puncture.

So the below-`θ` regime of `HJO/Shuffle/BraidTypeABelowTheta.lean` is **empty at a type-`A`
event with a move**, the type-`A` clause of `HJO.Mellit.braidValueColouring_sweepRecursionsFloor` is
not refuted there, and what remains of that clause is the above-`θ` case — the case the decided
instance `HJO.Mellit.braidValueColouring_gap_typeA` lies in and satisfies.

The type-`A` hypotheses are carried because they are the question; the proof consumes only
`HJO.Mellit.not_forall_iterate_nextCrossing_lt_sweepTheta`, which holds at every colouring of every
above-diagonal path at every admissible level. That the remaining hypotheses are jointly
satisfiable — so that this is not a `¬∃` over an empty index — is
`HJO.Mellit.sweepTheta_lt_braidData_gap_fst_zero`. -/
theorem not_exists_eventType_A_forall_move_lt_sweepTheta :
    ¬ ∃ (a b N X Y k : ℕ) (ηlo ηhi : ℚ) (y : Heights a b N) (i : Fin k),
        1 < a ∧ a < b ∧ 0 < N ∧ Nat.Coprime a b ∧ ((a * N : ℕ) : ℚ) < ηlo ∧
        Isolates a b N X Y ηlo ηhi ∧ IsAboveDiagonal y ∧
        ((X, Y) : ℕ × ℕ) ∈ sweptRegion y ∧ eventType y (X, Y) = EventType.A ∧
        2 ≤ (braidDataOfColouring a b N y ηlo k).2 i ∧
        ∀ j < (braidDataOfColouring a b N y ηlo k).2 i - 1,
          (nextCrossing (sweepTheta a b N))^[j] ((braidDataOfColouring a b N y ηlo k).1 i)
            < sweepTheta a b N := by
  rintro ⟨a, b, N, X, Y, k, ηlo, ηhi, y, i, ha, hab, hN, -, hηa, hI, -, -, -, hα, hmoves⟩
  exact not_forall_iterate_nextCrossing_lt_sweepTheta (by omega) (by omega) hN hab hI.lo
    (lt_of_le_of_lt (Nat.cast_nonneg _) hηa) y i hα hmoves

/-- **Everything but the last clause of `¬∃` is satisfiable.** At `a = 2`, `b = 5`, `N = 1`,
`HJO.Mellit.gapPath`, `P = (1, 5)` and the isolating pair `\eta_\pm = 31/2, 33/2` every hypothesis
of `HJO.Mellit.not_exists_eventType_A_forall_move_lt_sweepTheta` holds — a coprime `1 < a < b`, a
level above `aN`, a genuine type-`A` event in the swept region, and a component of multiplicity `2`,
hence with a move. So that `¬∃` is a statement about a nonempty family of configurations: what it
refutes is the below-`θ` clause alone, and not the existence of the configuration. -/
theorem exists_eventType_A_and_two_le_braidDataOfColouring_snd :
    ∃ (a b N X Y k : ℕ) (ηlo ηhi : ℚ) (y : Heights a b N) (i : Fin k),
      1 < a ∧ a < b ∧ 0 < N ∧ Nat.Coprime a b ∧ ((a * N : ℕ) : ℚ) < ηlo ∧
      Isolates a b N X Y ηlo ηhi ∧ IsAboveDiagonal y ∧
      ((X, Y) : ℕ × ℕ) ∈ sweptRegion y ∧ eventType y (X, Y) = EventType.A ∧
      2 ≤ (braidDataOfColouring a b N y ηlo k).2 i :=
  ⟨2, 5, 1, 1, 5, 2, gapLo, gapHi, gapPath, 0, by norm_num, by norm_num, by norm_num, by norm_num,
    by norm_num [gapLo], isolates_gapPath, isAboveDiagonal_gapPath, mem_sweptRegion_gapPath,
    eventType_gapPath, by rw [braidData_gap_snd_zero]⟩

/-! ### The general theorem at the type-`A` witness -/

/-- **The general theorem, fired at the one decided type-`A` instance.** At `a = 2`, `b = 5`,
`N = 1`, `HJO.Mellit.gapPath` and `\eta_- = 31/2` the component `0` has multiplicity `2`
(`HJO.Mellit.braidData_gap_snd_zero`), so its single move is its last, and
`HJO.Mellit.sweepTheta_lt_iterate_nextCrossing_braidDataOfColouring` says that move is made from
above `θ`.

Two things are checked at once. The type-`A` hypotheses of
`HJO.Mellit.not_exists_eventType_A_forall_move_lt_sweepTheta` really are satisfiable together with
`2 \le \alpha_i`, so that statement is not empty for want of instances; and the general theorem
returns the number `HJO/Shuffle/BraidTypeAGapRefuted.lean` computed by hand,
`θ = 3/10 < 17/40 = v_0` (`HJO.Mellit.sweepTheta_gap`, `HJO.Mellit.braidData_gap_fst_zero`). -/
theorem sweepTheta_lt_braidData_gap_fst_zero :
    sweepTheta 2 5 1 < (braidDataOfColouring 2 5 1 gapPath gapLo 2).1 0 := by
  have h := sweepTheta_lt_iterate_nextCrossing_braidDataOfColouring (a := 2) (b := 5) (N := 1)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) isAdmissibleLevel_gapLo gapLo_pos
    gapPath (0 : Fin 2) (by rw [braidData_gap_snd_zero])
  rwa [braidData_gap_snd_zero, show (2 : ℕ) - 2 = 0 from rfl, Function.iterate_zero_apply] at h

end HJO.Mellit

end
