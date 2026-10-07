/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.Shuffle.BraidCDLetterWitness
public import HJO.Shuffle.BraidTypeAGapRefuted
public meta import HJO.Attr

/-! # The type-`C` letter, evaluated: `T_{1↘k} ỹ_k` at every rank

`HJO/Shuffle/BraidCDLetterResidual.lean` reduces the type-`C` clause of
`HJO.Mellit.braidValueColouring_sweepRecursionsFloor` to one letter of `HJO.Braid.braidStep`, read
at the index `j` of the moving component and at the final position tuple of `HJO.Braid.positionPair`
for the **lower positions with the upper multiplicities**. It says of that letter only that it
is *some* `HJO.Braid.braidStep`, and its docstring names the missing input:
`entryRank (positionPair θ v_- α_+).2 j = k`, together with the train being the full `T_{1↘k}`.
Without those two the letter is `ỹ_a` at an unknown interior index and cannot match
`HJO.Sweep.corner`, whose closed form `HJO.Sweep.corner_eq_neg_cmAscWord_auxVar_mul` reads
`Δ^{(k)}F = -T_{1↑k}(y_kF)`.

**Both are proved here, at every rank, and the letter comes out in closed form:**

```
braidStep θ (positionPair θ v_- α_+).2 j = braidTrainDown k 1 k * braidYtilde k k.
```

`HJO.Mellit.Isolates.braidStep_positionPair_snd_of_eventType_C` is that identity and
`HJO.Mellit.Isolates.braidValueColouring_eq_sweepOperator_of_eventType_C_of_train` is the clause
restated with the letter written out.

## The mechanism: one comparison of RANKS, no comparison of positions

Everything runs on `HJO.Mellit.positionPair_snd_braidDataOfColouring_eq_div`: the final position
tuple of a colouring's data reads the **bottom** crossing of each component, and that crossing is
the lattice point one row above the crossed north step `u_i`, at the normalised height
`(rk̂(u_i) + ω - η)/D`. So a comparison of two such entries is a comparison of two integer ranks,
and the two facts fall out of the rank bookkeeping of a type-`C` drop:

* the lower colouring lists `(X, Y - 1)` at the index `j`, so **the `j`-th entry of the mixed tuple
  is one crossing short of the bottom** — the upper multiplicity being one less than the lower —
  namely `(X, Y + 1)`, of rank `rk̂(P) + ω` with `rk̂(P) > η_-`; while every other entry reads a
  point above a crossed north step of the *lower* colouring, of rank below `η_- + ω`. Hence the
  `j`-th entry is the maximum and the rank is `k`
  (`HJO.Mellit.Isolates.entryRank_positionPair_snd_of_eventType_C`);
* the move takes that entry to `(X, Y)`, of rank `rk̂(P)`, which by
  `HJO.Mellit.Isolates.pointRank_le` is the **least** rank of the rectangle above `η_-`. Hence it
  becomes the minimum, its rank is `1`, and the train is the full `T_{1↘k}`
  (`HJO.Mellit.Isolates.entryRank_moveOne_positionPair_snd_of_eventType_C`). The strictness — `≤`
  from isolation, `<` needed — is the injectivity of the *lower* data's own final tuple, which
  `HJO.Braid.positionPair_snd_update_succ` identifies the moved tuple with.

The branch is the `ỹ` one for the same reason the rank is `k`: `(rk̂(P) + ω - η_-)/D > ω/D = θ`. So
the `ỹ` predicted by the `z`-count bookkeeping of
`HJO.Mellit.Isolates.zCount_sub_eq_zero_of_eventType_C` is now read off the letter itself.

## The one hypothesis beyond the clause's own

`hwin`: `rk̂(P) < η_- + (b(aN+1)N - 1)`. It is what puts the crossing of index `X + Y + 1` in the
column of `X` rather than the next one — equivalently what stops the fractional part from wrapping
— and it is not decoration: in the wrapped case the `j`-th entry reads
`(rk̂(X + 1, Y) − η_-)/D` instead, and `rk̂(X + 1, Y)` is **below** `rk̂(P)`, so the rank comes out
`1` rather than `k` and the letter is not `T_{1↘k} ỹ_k`. *That* reading of the wrapped case is an
unproved remark here — nothing below states or uses it; what is proved is the unwrapped case, under
`hwin`.

It is discharged two ways, neither of which is an extra assumption in practice:

* `HJO.Mellit.Isolates.pointRank_lt_add_of_eventType_C_of_lt` from `a < b`, the range
  `HJO.Mellit.shuffle_of_lhs_and_induction` quantifies over;
* `HJO.Mellit.Isolates.pointRank_lt_add_of_eventType_C_of_succ` from `η_+ = η_- + 1`, the hypothesis
  `HJO.Mellit.Isolates.zCount_sub_eq_zero_of_eventType_C` already carries — and this one uses no
  relation between `a` and `b` at all.

## What is NOT done here

The match of `T_{1↘k} ỹ_k` against `Δ^{(k)}`. That is
`HJO.Mellit.Isolates.braidValueColouring_eq_sweepOperator_of_eventType_C_of_train`'s `htrain`, and
it is the whole remaining content of the type-`C` clause; it carries no geometry. Nothing here
proves `HJO.Mellit.braidValueColouring_sweepRecursionsFloor`: three of its four clauses and all six
recursions are untouched.

## Genericity

The geometry is `ℕ`, `ℤ` and `ℚ` throughout and needs no field: `0 < a`, `0 < b`, `0 < N`, plus the
`hwin` above. The only statement mentioning a field is the restated clause, which carries
`HJO.Sweep.braidRep`'s own exclusions `q ≠ 0`, `q ≠ 1`, `q + 1 ≠ 0`, `r * r = q` and nothing else,
and no letter here is a zero map that the unreduced clause was not.

## References

A. Mellit, *Toric braids and `(m, n)`-parking functions*,
section 5.
-/

@[expose] public section

open Finset

namespace HJO.Braid

variable {θ : ℚ} {k : ℕ}

/-! ### Two readings of `HJO.Braid.entryRank` -/

/-- **An entry weakly above every entry has rank `k`.** `HJO.Braid.entryRank` counts the entries
weakly below the given one, so a maximum is counted against all `k` of them. -/
theorem entryRank_eq_card_of_forall_le {α : Type*} [LinearOrder α] (w : Fin k → α) (i : Fin k)
    (h : ∀ t, w t ≤ w i) : entryRank w i = k := by
  rw [entryRank, Finset.filter_true_of_mem fun t _ => h t, Finset.card_univ, Fintype.card_fin]

/-- **An entry strictly below every other entry has rank `1`.** Only the entry itself is counted. -/
theorem entryRank_eq_one_of_forall_ne_lt {α : Type*} [LinearOrder α] (w : Fin k → α) (i : Fin k)
    (h : ∀ t, t ≠ i → w i < w t) : entryRank w i = 1 := by
  rw [entryRank]
  refine Finset.card_eq_one.2 ⟨i, Finset.eq_singleton_iff_unique_mem.2
    ⟨Finset.mem_filter.2 ⟨Finset.mem_univ _, le_rfl⟩, fun t ht => ?_⟩⟩
  by_contra hne
  exact absurd (Finset.mem_filter.1 ht).2 (not_le.2 (h t hne))

/-! ### The final position tuple of a raised multiplicity -/

/-- **Raising `α_j` by one advances the final position tuple of `HJO.Braid.positionPair` at `j` and
nowhere else.** The `j`-th entry gains one iterate of `HJO.Braid.nextCrossing` and the others are
untouched, which is exactly `HJO.Braid.moveOne`. `1 ≤ α_j` is needed: at `α_j = 0` the truncated
subtraction makes both exponents `0`.

This is the identity that turns the *raised* data's final tuple — which is where the remaining
letters of the lower special braid are read — into one move of the *mixed* tuple that
`HJO.Braid.specialBraid_update_succ_left` puts the extra letter at. -/
theorem positionPair_snd_update_succ (v : Fin k → ℚ) (α : Fin k → ℕ) (j : Fin k) (hα : 1 ≤ α j) :
    (positionPair θ v (Function.update α j (α j + 1))).2
      = moveOne θ (positionPair θ v α).2 j := by
  funext i
  by_cases h : i = j
  · subst h
    rw [positionPair_snd, Function.update_self, moveOne_self, positionPair_snd,
      show α i + 1 - 1 = (α i - 1) + 1 from by omega, Function.iterate_succ_apply']
  · rw [positionPair_snd, Function.update_of_ne h, moveOne_of_ne _ _ h, positionPair_snd]

/-! ### The letter of a full descent from the top -/

/-- **The letter of a move that carries the top entry to the bottom is `T_{1↘k} ỹ_k`.** The three
hypotheses are the three things `HJO.Braid.braidStep` reads: the moving entry is above the puncture,
so the letter is a `ỹ`; its rank before the move is `k`, so the `ỹ` sits at the top index; and its
rank after the move is `1`, so the descending train is the full `T_{1↘k}`.

This is the shape `HJO.Sweep.corner_eq_neg_cmAscWord_auxVar_mul` needs of a letter that is to match
`Δ^{(k)}F = -T_{1↑k}(y_kF)`: the `ỹ` at the top index `k` and the train the full one. -/
theorem braidStep_eq_trainDown_one_braidYtilde {w : Fin k → ℚ} {i : Fin k} (hgt : θ < w i)
    (hrk : entryRank w i = k) (hrk' : entryRank (moveOne θ w i) i = 1) :
    braidStep θ w i = braidTrainDown k 1 k * braidYtilde k k := by
  rw [braidStep_of_gt hgt, hrk, hrk']

end HJO.Braid

namespace HJO.Mellit

open Braid Finset ParkingFunctions Paths Sweep

variable {a b N : ℕ}

/-! ### `θ` over the common denominator -/

/-- **`θ` is the attack window over the crossing denominator.** `HJO.Mellit.crossDen` is
`a(aN+1)N(1 + s)` and `θ(1 + s) = 1`, so `θ D = ω`. Every position below is a quotient by `D`, and
this is what compares one with `θ`. -/
theorem sweepTheta_mul_crossDen (ha : 0 < a) (hb : 0 < b) (hN : 0 < N) :
    sweepTheta a b N * crossDen a b N = ((attackWindow a N : ℕ) : ℚ) := by
  have hs := one_add_sweepSlope_pos (a := a) (b := b) (N := N) ha hb hN
  rw [crossDen_eq_mul (b := b) ha hN, sweepTheta, cast_attackWindow]
  field_simp

/-- `θ = ω / D`, the division form. -/
theorem sweepTheta_eq_div_crossDen (ha : 0 < a) (hb : 0 < b) (hN : 0 < N) :
    sweepTheta a b N = ((attackWindow a N : ℕ) : ℚ) / crossDen a b N := by
  rw [eq_div_iff (crossDen_pos ha hb hN).ne']
  exact sweepTheta_mul_crossDen ha hb hN

/-- `D - ω = b(aN+1)N - 1`: the crossing denominator less the attack window is the amount by which
one step east lowers the rank. -/
theorem crossDen_sub_cast_attackWindow (a b N : ℕ) :
    crossDen a b N - ((attackWindow a N : ℕ) : ℚ) = (b : ℚ) * ((a : ℚ) * N + 1) * N - 1 := by
  rw [crossDen, cast_attackWindow]
  push_cast
  ring

/-- **`ω ≤ b(aN+1)N - 1` whenever `a < b`.** The attack window is `a(aN+1)N`, so the inequality is
`a(aN+1)N + 1 ≤ b(aN+1)N`, which one extra factor of `(aN+1)N ≥ 1` supplies. This is the one place
`a < b` enters the type-`C` evaluation, and
`HJO.Mellit.Isolates.pointRank_lt_add_of_eventType_C_of_succ` records the alternative route through
the level gap. -/
theorem cast_attackWindow_le_bMN_sub_one (ha : 0 < a) (hN : 0 < N) (hab : a < b) :
    ((attackWindow a N : ℕ) : ℚ) ≤ (b : ℚ) * ((a : ℚ) * N + 1) * N - 1 := by
  have h1 : 1 ≤ (a * N + 1) * N := Nat.one_le_iff_ne_zero.2 (by positivity)
  have h2 : a * (a * N + 1) * N + 1 ≤ b * (a * N + 1) * N := by
    calc a * (a * N + 1) * N + 1 ≤ a * ((a * N + 1) * N) + (a * N + 1) * N := by
          rw [Nat.mul_assoc]; omega
      _ = (a + 1) * ((a * N + 1) * N) := by ring
      _ ≤ b * ((a * N + 1) * N) := Nat.mul_le_mul_right _ (by omega)
      _ = b * (a * N + 1) * N := by ring
  have h2' : ((a * (a * N + 1) * N + 1 : ℕ) : ℚ) ≤ ((b * (a * N + 1) * N : ℕ) : ℚ) := by
    exact_mod_cast h2
  rw [cast_attackWindow]
  push_cast at h2' ⊢
  linarith

/-! ### The final position tuple of a colouring, over the common denominator -/

/-- **The final position of the `i`-th component is the normalised rank of the lattice point just
above its crossed north step.** `HJO.Mellit.positionPair_snd_braidDataOfColouring` says the tuple
reads the crossing of the *bottom* index, and
`HJO.Mellit.fract_crossingAbscissa_componentBotIndex` evaluates that crossing as
`(rk̂(u_i) + ω - η)/D`. Stated at an arbitrary rank `k`, which is the shape every consumer of
`HJO.Braid.positionPair` reads it in.

Since `rk̂(u_i) < η` — the first clause of `HJO.Mellit.colouring` for a crossed north step — this
number is below `ω/D = θ`; and since `η < rk̂(u_i) + ω` it is positive. So the final tuple of a
colouring lies in `(0, θ)`, entrywise. -/
theorem positionPair_snd_braidDataOfColouring_eq_div (ha : 0 < a) (hb : 0 < b) (hN : 0 < N)
    {η : ℚ} (hη : IsAdmissibleLevel η) (hηN : ((a * N : ℕ) : ℚ) < η) {y : Heights a b N}
    (hy : IsAboveDiagonal y) {k : ℕ} (i : Fin k) (hi : (i : ℕ) < #(colouringNorth y η)) :
    (positionPair (sweepTheta a b N) (braidDataOfColouring a b N y η k).1
        (braidDataOfColouring a b N y η k).2).2 i
      = (((pointRank a b N (colStep (colouringNorth y η) (i : ℕ)) : ℤ) : ℚ)
          + ((attackWindow a N : ℕ) : ℚ) - η) / crossDen a b N := by
  have hηpos : 0 < η := lt_of_le_of_lt (Nat.cast_nonneg _) hηN
  have hBT := componentBotIndex_le_componentTopIndex ha hb hN hη hηN hy hi
  have hcard := braidDataOfColouring_snd_eq_toNat a b N y η k i
  have hidx : componentTopIndex a b N y η (i : ℕ)
      - (((braidDataOfColouring a b N y η k).2 i - 1 : ℕ) : ℤ)
      = componentBotIndex a b N y η (i : ℕ) := by rw [hcard]; omega
  rw [positionPair_snd, braidDataOfColouring_fst,
    iterate_nextCrossing_fract_crossingAbscissa ha hb hN hη hηpos y (i : ℕ) (le_of_eq hidx.symm),
    hidx, fract_crossingAbscissa_componentBotIndex ha hb hN hη hηpos hi]

namespace Isolates

variable {X Y : ℕ} {ηlo ηhi : ℚ}

/-! ### The mixed final tuple at a type-`C` drop -/

/-- **Away from the moving index the mixed final tuple is the lower colouring's own final tuple.**
At a type-`C` drop the multiplicity at `i ≠ j` is the same at the two levels
(`HJO.Mellit.Isolates.braidData_snd_of_eventType_C_of_ne`), so reading the lower positions with the
upper multiplicities changes nothing there: the entry is the normalised rank of the lattice point
just above the `i`-th crossed north step of the **lower** colouring, which is below `ηlo + ω`. -/
theorem positionPair_snd_of_eventType_C_of_ne (ha : 0 < a) (hb : 0 < b) (hN : 0 < N)
    (hI : Isolates a b N X Y ηlo ηhi) (hηlo : ((a * N : ℕ) : ℚ) < ηlo) {y : Heights a b N}
    (hy : IsAboveDiagonal y) (hev : eventType y (X, Y) = EventType.C) {k : ℕ}
    (hk : #(colouringEast y ηhi) = k) (j : Fin k)
    (hj : colStep (colouringNorth y ηhi) (j : ℕ) = (X, Y)) (i : Fin k) (hne : i ≠ j) :
    (positionPair (sweepTheta a b N) (braidDataOfColouring a b N y ηlo k).1
        (braidDataOfColouring a b N y ηhi k).2).2 i
      = (((pointRank a b N (colStep (colouringNorth y ηlo) (i : ℕ)) : ℤ) : ℚ)
          + ((attackWindow a N : ℕ) : ℚ) - ηlo) / crossDen a b N := by
  have hηhi : ((a * N : ℕ) : ℚ) < ηhi := hηlo.trans (hI.ltP.trans hI.Plt)
  have hkN : #(colouringNorth y ηhi) = k := by
    rw [card_colouringNorth_eq_card_colouringEast hb hN hI.hi hηhi hy]; exact hk
  have hkNlo : #(colouringNorth y ηlo) = k := by
    rw [hI.card_colouringNorth_of_eventType_C ha hN hev]; exact hkN
  have hjlt : (j : ℕ) < #(colouringNorth y ηhi) := by rw [hkN]; exact j.isLt
  have hmult : (braidDataOfColouring a b N y ηhi k).2 i
      = (braidDataOfColouring a b N y ηlo k).2 i :=
    (hI.braidData_snd_of_eventType_C_of_ne ha hb hN hηlo hy hev hjlt hj i
      (by rw [hkN]; exact i.isLt) (fun hc => hne (Fin.ext hc))).symm
  have hswap : (positionPair (sweepTheta a b N) (braidDataOfColouring a b N y ηlo k).1
        (braidDataOfColouring a b N y ηhi k).2).2 i
      = (positionPair (sweepTheta a b N) (braidDataOfColouring a b N y ηlo k).1
        (braidDataOfColouring a b N y ηlo k).2).2 i := by
    rw [positionPair_snd, positionPair_snd, hmult]
  rw [hswap, positionPair_snd_braidDataOfColouring_eq_div ha hb hN hI.lo hηlo hy i
    (by rw [hkNlo]; exact i.isLt)]

/-- **At the moving index the mixed final tuple is the normalised rank of `(X, Y + 1)`.** The lower
colouring's `j`-th crossed north step is `(X, Y - 1)`, so its component's bottom crossing is the one
of index `X + Y` — the point `(X, Y)`, whose rank is `rk̂(P)` — and the upper multiplicity is one
less than the lower one, so the mixed tuple stops **one crossing short of the bottom**, at the index
`X + Y + 1`. That crossing is the point `(X, Y + 1)`, of rank `rk̂(P) + ω`.

`hwin` is what puts that crossing in the column of `X` rather than the next one: the rank must stay
inside the window of width `D` above `ηlo`, and `rk̂(P) + ω < ηlo + D` is exactly
`rk̂(P) < ηlo + (b(aN+1)N - 1)`. It is the ONLY hypothesis here beyond the clause's own, and
`HJO.Mellit.Isolates.pointRank_lt_add_of_eventType_C_of_lt` and
`HJO.Mellit.Isolates.pointRank_lt_add_of_eventType_C_of_succ` discharge it. -/
theorem positionPair_snd_of_eventType_C_self (ha : 0 < a) (hb : 0 < b) (hN : 0 < N)
    (hI : Isolates a b N X Y ηlo ηhi) (hηlo : ((a * N : ℕ) : ℚ) < ηlo) {y : Heights a b N}
    (hy : IsAboveDiagonal y) (hev : eventType y (X, Y) = EventType.C) {k : ℕ}
    (hk : #(colouringEast y ηhi) = k) (j : Fin k)
    (hj : colStep (colouringNorth y ηhi) (j : ℕ) = (X, Y))
    (hwin : ((pointRank a b N (X, Y) : ℤ) : ℚ)
      < ηlo + ((b : ℚ) * ((a : ℚ) * N + 1) * N - 1)) :
    (positionPair (sweepTheta a b N) (braidDataOfColouring a b N y ηlo k).1
        (braidDataOfColouring a b N y ηhi k).2).2 j
      = (((pointRank a b N (X, Y) : ℤ) : ℚ)
          + ((attackWindow a N : ℕ) : ℚ) - ηlo) / crossDen a b N := by
  have hηhi : ((a * N : ℕ) : ℚ) < ηhi := hηlo.trans (hI.ltP.trans hI.Plt)
  have hlopos : (0 : ℚ) < ηlo := lt_of_le_of_lt (Nat.cast_nonneg _) hηlo
  have hkN : #(colouringNorth y ηhi) = k := by
    rw [card_colouringNorth_eq_card_colouringEast hb hN hI.hi hηhi hy]; exact hk
  have hkNlo : #(colouringNorth y ηlo) = k := by
    rw [hI.card_colouringNorth_of_eventType_C ha hN hev]; exact hkN
  have hjlt : (j : ℕ) < #(colouringNorth y ηhi) := by rw [hkN]; exact j.isLt
  have hjltlo : (j : ℕ) < #(colouringNorth y ηlo) := by rw [hkNlo]; exact j.isLt
  obtain ⟨hht, hXlt, hht'⟩ := ht_lt_of_eventType_C hev
  have hY : 0 < Y := by omega
  -- the lower colouring lists `(X, Y - 1)` at the index `j`
  have hcolN : colStep (colouringNorth y ηlo) (j : ℕ) = ((X, Y - 1) : ℕ × ℕ) := by
    rw [hI.colStep_colouringNorth_of_eventType_C ha hN hev hjlt hj hjlt, Function.update_self]
  -- one row up from `(X, Y)` the rank is `rk̂(P) + ω`
  have hPr : ((pointRank a b N (X, Y) : ℤ) : ℚ) = ((abovePointRank a b N X Y : ℤ) : ℚ) := by
    simp only [pointRank]
  have hstep1 : ((abovePointRank a b N X (Y + 1) : ℤ) : ℚ)
      = ((abovePointRank a b N X Y : ℤ) : ℚ) + ((attackWindow a N : ℕ) : ℚ) := by
    rw [abovePointRank_succ a b N X Y]
    push_cast
    ring
  -- the bottom crossing index of the lower `j`-th component is `X + Y`
  have hbot : componentBotIndex a b N y ηlo (j : ℕ) = (X : ℤ) + (Y : ℤ) := by
    rw [componentBotIndex_eq_add_snd ha hb hN hI.lo hlopos y hjltlo, hcolN]
    simp only
    omega
  -- the multiplicities, and the index the mixed tuple stops at
  have hone : 1 ≤ (braidDataOfColouring a b N y ηhi k).2 j :=
    (isSpecialBraidData_braidDataOfColouring_of_card ha hb hN hI.hi hηhi hy hkN).one_le_mult j
  have hraise : (braidDataOfColouring a b N y ηlo k).2 j
      = (braidDataOfColouring a b N y ηhi k).2 j + 1 :=
    hI.braidData_snd_succ_of_eventType_C ha hb hN hηlo hy hev hjlt hj j rfl
  have hcardlo := braidDataOfColouring_snd_eq_toNat a b N y ηlo k j
  have hBT := componentBotIndex_le_componentTopIndex ha hb hN hI.lo hηlo hy hjltlo
  have hidx : componentTopIndex a b N y ηlo (j : ℕ)
      - (((braidDataOfColouring a b N y ηhi k).2 j - 1 : ℕ) : ℤ)
      = (X : ℤ) + ((Y + 1 : ℕ) : ℤ) := by
    rw [hraise, hbot] at hcardlo
    rw [hbot] at hBT
    push_cast
    omega
  -- the two window bounds that put that crossing in the column of `X`
  have hD := crossDen_sub_cast_attackWindow (a := a) (b := b) N
  have hω : (0 : ℚ) ≤ ((attackWindow a N : ℕ) : ℚ) := Nat.cast_nonneg _
  have hltP : ηlo < ((abovePointRank a b N X Y : ℤ) : ℚ) := by rw [← hPr]; exact hI.ltP
  have hwin' : ((abovePointRank a b N X Y : ℤ) : ℚ)
      < ηlo + ((b : ℚ) * ((a : ℚ) * N + 1) * N - 1) := by rw [← hPr]; exact hwin
  have hlow : ηlo < ((abovePointRank a b N X (Y + 1) : ℤ) : ℚ) := by rw [hstep1]; linarith
  have hhigh : ((abovePointRank a b N X (Y + 1) : ℤ) : ℚ) < ηlo + crossDen a b N := by
    rw [hstep1]; linarith
  rw [positionPair_snd, braidDataOfColouring_fst,
    iterate_nextCrossing_fract_crossingAbscissa ha hb hN hI.lo hlopos y (j : ℕ)
      (by rw [hidx, hbot]; push_cast; omega),
    hidx, fract_crossingAbscissa_natCast_add ha hb hN hlow hhigh, hstep1, hPr]

/-! ### The window hypothesis, discharged two ways -/

/-- **The window hypothesis from `a < b`.** The point one row below `P` is the lower colouring's
crossed north step in the column of `X`, so `rk̂(P) = rk̂(X, Y - 1) + ω < ηlo + ω`; and `a < b`
makes `ω ≤ b(aN+1)N - 1`.

This is the only place the type-`C` evaluation needs anything of the parameters beyond
nondegeneracy, and `a < b` is inside the range `HJO.Mellit.shuffle_of_lhs_and_induction`
quantifies over. -/
theorem pointRank_lt_add_of_eventType_C_of_lt (ha : 0 < a) (hN : 0 < N) (hab : a < b)
    (hI : Isolates a b N X Y ηlo ηhi) {y : Heights a b N}
    (hev : eventType y (X, Y) = EventType.C) :
    ((pointRank a b N (X, Y) : ℤ) : ℚ) < ηlo + ((b : ℚ) * ((a : ℚ) * N + 1) * N - 1) := by
  obtain ⟨hht, hXlt, hht'⟩ := ht_lt_of_eventType_C hev
  have hY : 0 < Y := by omega
  have hmem : ((X, Y - 1) : ℕ × ℕ) ∈ colouringNorth y ηlo := by
    rw [hI.colouringNorth_eq_of_eventType_C ha hN hev]
    exact Finset.mem_insert_self _ _
  have hlt : ((pointRank a b N (X, Y - 1) : ℤ) : ℚ) < ηlo := (Finset.mem_filter.1 hmem).2.1
  have hstep := cast_pointRank_pred_add_attackWindow a b N X (Y := Y) hY
  have hω := cast_attackWindow_le_bMN_sub_one (a := a) (b := b) (N := N) ha hN hab
  linarith

/-- **The window hypothesis from consecutive levels.** The isolating pair of the sweep is a pair of
*consecutive* admissible levels, and then `rk̂(P) < ηhi = ηlo + 1 ≤ ηlo + (b(aN+1)N - 1)` because
`b(aN+1)N ≥ 2`. No relation between `a` and `b` is used.

`hstep` is the hypothesis `HJO.Mellit.Isolates.zCount_sub_eq_zero_of_eventType_C` already carries,
so this is the route that leaves the type-`C` evaluation with no parameter restriction at all. -/
theorem pointRank_lt_add_of_eventType_C_of_succ (ha : 0 < a) (hb : 0 < b) (hN : 0 < N)
    (hI : Isolates a b N X Y ηlo ηhi) (hstep : ηhi = ηlo + 1) :
    ((pointRank a b N (X, Y) : ℤ) : ℚ) < ηlo + ((b : ℚ) * ((a : ℚ) * N + 1) * N - 1) := by
  have haN : 1 ≤ a * N := Nat.one_le_iff_ne_zero.2 (by positivity)
  have h2 : 2 ≤ b * (a * N + 1) * N := by
    calc 2 = 1 * 2 * 1 := by norm_num
      _ ≤ b * (a * N + 1) * N := Nat.mul_le_mul (Nat.mul_le_mul hb (by omega)) hN
  have h2' : (2 : ℚ) ≤ ((b * (a * N + 1) * N : ℕ) : ℚ) := by exact_mod_cast h2
  push_cast at h2'
  have := hI.Plt
  rw [hstep] at this
  linarith

/-! ### The two ranks of the type-`C` letter -/

/-- **THE ENTRY RANK: at a type-`C` drop the moving entry of the mixed final tuple is the TOP one.**
The rank of `(positionPair θ v_- α_+).2` at the moving index `j` is `k`.

The reason is one comparison of ranks, and no inequality between positions is needed for it. Every
other entry of that tuple is the normalised rank of the point above a crossed north step of the
**lower** colouring, hence of rank *below* `ηlo`; the `j`-th entry is the normalised rank of
`(X, Y + 1)`, of rank `rk̂(P) + ω` with `rk̂(P)` *above* `ηlo`. So the `j`-th entry exceeds every
other by the width of a whole attack window, and the `ỹ` the letter carries sits at the index `k`
— which is what `HJO.Sweep.corner_eq_neg_cmAscWord_auxVar_mul` needs of it. -/
theorem entryRank_positionPair_snd_of_eventType_C (ha : 0 < a) (hb : 0 < b) (hN : 0 < N)
    (hI : Isolates a b N X Y ηlo ηhi) (hηlo : ((a * N : ℕ) : ℚ) < ηlo) {y : Heights a b N}
    (hy : IsAboveDiagonal y) (hev : eventType y (X, Y) = EventType.C) {k : ℕ}
    (hk : #(colouringEast y ηhi) = k) (j : Fin k)
    (hj : colStep (colouringNorth y ηhi) (j : ℕ) = (X, Y))
    (hwin : ((pointRank a b N (X, Y) : ℤ) : ℚ)
      < ηlo + ((b : ℚ) * ((a : ℚ) * N + 1) * N - 1)) :
    entryRank (positionPair (sweepTheta a b N) (braidDataOfColouring a b N y ηlo k).1
        (braidDataOfColouring a b N y ηhi k).2).2 j = k := by
  have hηhi : ((a * N : ℕ) : ℚ) < ηhi := hηlo.trans (hI.ltP.trans hI.Plt)
  have hD := crossDen_pos (a := a) (b := b) (N := N) ha hb hN
  have hkN : #(colouringNorth y ηhi) = k := by
    rw [card_colouringNorth_eq_card_colouringEast hb hN hI.hi hηhi hy]; exact hk
  have hkNlo : #(colouringNorth y ηlo) = k := by
    rw [hI.card_colouringNorth_of_eventType_C ha hN hev]; exact hkN
  refine entryRank_eq_card_of_forall_le _ _ fun i => ?_
  by_cases h : i = j
  · rw [h]
  rw [hI.positionPair_snd_of_eventType_C_of_ne ha hb hN hηlo hy hev hk j hj i h,
    hI.positionPair_snd_of_eventType_C_self ha hb hN hηlo hy hev hk j hj hwin,
    div_le_div_iff_of_pos_right hD]
  have hmem := colStep_mem (S := colouringNorth y ηlo) (show (i : ℕ) < #(colouringNorth y ηlo) by
    rw [hkNlo]; exact i.isLt)
  have hlt : ((pointRank a b N (colStep (colouringNorth y ηlo) (i : ℕ)) : ℤ) : ℚ) < ηlo :=
    (Finset.mem_filter.1 hmem).2.1
  have := hI.ltP
  linarith

/-- **THE TRAIN: the move carries the moving entry to the BOTTOM.** The rank of the once-moved tuple
at `j` is `1`, so the descending train of `HJO.Braid.braidStep` is the full `T_{1↘k}`.

The move takes the `j`-th entry from the crossing of index `X + Y + 1` to the crossing of index
`X + Y`, whose normalised rank is `rk̂(P) - ηlo` — and `rk̂(P)` is the **least** rank of the
rectangle above `ηlo` (`HJO.Mellit.Isolates.pointRank_le`), while every other entry reads the point
above a crossed north step of the lower colouring, a rectangle point above `ηlo` too. The
inequality is therefore weak from the isolation clause alone; the strictness is the injectivity of
the lower data's own final position tuple, which
`HJO.Braid.injective_positionPair_snd_of_isSpecialBraidData` supplies from
`HJO.Mellit.isSpecialBraidData_braidDataOfColouring`. -/
theorem entryRank_moveOne_positionPair_snd_of_eventType_C (ha : 0 < a) (hb : 0 < b) (hN : 0 < N)
    (hI : Isolates a b N X Y ηlo ηhi) (hηlo : ((a * N : ℕ) : ℚ) < ηlo) {y : Heights a b N}
    (hy : IsAboveDiagonal y) (hev : eventType y (X, Y) = EventType.C) {k : ℕ}
    (hk : #(colouringEast y ηhi) = k) (j : Fin k)
    (hj : colStep (colouringNorth y ηhi) (j : ℕ) = (X, Y)) :
    entryRank (moveOne (sweepTheta a b N)
        (positionPair (sweepTheta a b N) (braidDataOfColouring a b N y ηlo k).1
          (braidDataOfColouring a b N y ηhi k).2).2 j) j = 1 := by
  have hηhi : ((a * N : ℕ) : ℚ) < ηhi := hηlo.trans (hI.ltP.trans hI.Plt)
  have hD := crossDen_pos (a := a) (b := b) (N := N) ha hb hN
  have hkN : #(colouringNorth y ηhi) = k := by
    rw [card_colouringNorth_eq_card_colouringEast hb hN hI.hi hηhi hy]; exact hk
  have hkNlo : #(colouringNorth y ηlo) = k := by
    rw [hI.card_colouringNorth_of_eventType_C ha hN hev]; exact hkN
  have hjlt : (j : ℕ) < #(colouringNorth y ηhi) := by rw [hkN]; exact j.isLt
  have hdatahi := isSpecialBraidData_braidDataOfColouring_of_card ha hb hN hI.hi hηhi hy hkN
  have hdatalo := isSpecialBraidData_braidDataOfColouring_of_card ha hb hN hI.lo hηlo hy hkNlo
  -- the moved tuple IS the lower data's own final position tuple
  have hsnd : (braidDataOfColouring a b N y ηlo k).2
      = Function.update (braidDataOfColouring a b N y ηhi k).2 j
          ((braidDataOfColouring a b N y ηhi k).2 j + 1) := by
    funext i
    by_cases h : i = j
    · subst h
      rw [Function.update_self]
      exact hI.braidData_snd_succ_of_eventType_C ha hb hN hηlo hy hev hjlt hj i rfl
    · rw [Function.update_of_ne h]
      exact hI.braidData_snd_of_eventType_C_of_ne ha hb hN hηlo hy hev hjlt hj i
        (by rw [hkN]; exact i.isLt) (fun hc => h (Fin.ext hc))
  have hmove : moveOne (sweepTheta a b N)
      (positionPair (sweepTheta a b N) (braidDataOfColouring a b N y ηlo k).1
        (braidDataOfColouring a b N y ηhi k).2).2 j
      = (positionPair (sweepTheta a b N) (braidDataOfColouring a b N y ηlo k).1
          (braidDataOfColouring a b N y ηlo k).2).2 := by
    rw [hsnd, positionPair_snd_update_succ _ _ j (hdatahi.one_le_mult j)]
  rw [hmove]
  refine entryRank_eq_one_of_forall_ne_lt _ _ fun i hne => ?_
  have hij : (positionPair (sweepTheta a b N) (braidDataOfColouring a b N y ηlo k).1
      (braidDataOfColouring a b N y ηlo k).2).2 j
      ≠ (positionPair (sweepTheta a b N) (braidDataOfColouring a b N y ηlo k).1
        (braidDataOfColouring a b N y ηlo k).2).2 i := fun hc =>
    hne (injective_positionPair_snd_of_isSpecialBraidData hdatalo hc.symm)
  -- both entries are normalised ranks of rectangle points above `ηlo`
  have hcolN : colStep (colouringNorth y ηlo) (j : ℕ) = ((X, Y - 1) : ℕ × ℕ) := by
    rw [hI.colStep_colouringNorth_of_eventType_C ha hN hev hjlt hj hjlt, Function.update_self]
  obtain ⟨hht, hXlt, hht'⟩ := ht_lt_of_eventType_C hev
  have hY : 0 < Y := by omega
  have hmemi := colStep_mem (S := colouringNorth y ηlo) (show (i : ℕ) < #(colouringNorth y ηlo) by
    rw [hkNlo]; exact i.isLt)
  obtain ⟨hxi, -, -, -⟩ := mem_colouringNorth_spec ha hN hI.lo y hmemi
  obtain ⟨-, -, hupi⟩ := Finset.mem_filter.1 hmemi
  have hQy : (colStep (colouringNorth y ηlo) (i : ℕ)).2 + 1 ≤ b * N := by
    have h4 := ht_le_mul (a := a) (b := b) (N := N) y
      ((colStep (colouringNorth y ηlo) (i : ℕ)).1 + 1)
    obtain ⟨-, -, h5, h6⟩ := mem_colouringNorth_spec ha hN hI.lo y hmemi
    omega
  have hQrank : ((pointRank a b N ((colStep (colouringNorth y ηlo) (i : ℕ)).1,
        (colStep (colouringNorth y ηlo) (i : ℕ)).2 + 1) : ℤ) : ℚ)
      = ((pointRank a b N (colStep (colouringNorth y ηlo) (i : ℕ)) : ℤ) : ℚ)
        + ((attackWindow a N : ℕ) : ℚ) := by
    have h := cast_pointRank_pred_add_attackWindow a b N
      (colStep (colouringNorth y ηlo) (i : ℕ)).1
      (Y := (colStep (colouringNorth y ηlo) (i : ℕ)).2 + 1) (by omega)
    rw [show (colStep (colouringNorth y ηlo) (i : ℕ)).2 + 1 - 1
        = (colStep (colouringNorth y ηlo) (i : ℕ)).2 from by omega] at h
    rw [← h]
  have hle : ((pointRank a b N (X, Y) : ℤ) : ℚ)
      ≤ ((pointRank a b N (colStep (colouringNorth y ηlo) (i : ℕ)) : ℤ) : ℚ)
        + ((attackWindow a N : ℕ) : ℚ) := by
    rw [← hQrank]
    exact hI.pointRank_le (Q := ((colStep (colouringNorth y ηlo) (i : ℕ)).1,
        (colStep (colouringNorth y ηlo) (i : ℕ)).2 + 1)) (by omega) hQy (by rw [hQrank]; exact hupi)
  rw [positionPair_snd_braidDataOfColouring_eq_div ha hb hN hI.lo hηlo hy j
      (by rw [hkNlo]; exact j.isLt),
    positionPair_snd_braidDataOfColouring_eq_div ha hb hN hI.lo hηlo hy i
      (by rw [hkNlo]; exact i.isLt), hcolN] at hij ⊢
  rw [div_lt_div_iff_of_pos_right hD]
  have hstep := cast_pointRank_pred_add_attackWindow a b N X (Y := Y) hY
  exact lt_of_le_of_ne (by linarith) fun hc => hij (by rw [hc])

/-! ### The letter, in closed form -/

/-- **THE TYPE-`C` LETTER, EVALUATED: `T_{1↘k} ỹ_k`, at every rank.** The residual letter of
`HJO.Mellit.Isolates.braidValueColouring_eq_sweepOperator_of_eventType_C_of_letter` is the full
descending train times the `ỹ` of the **top** index — the exact shape
`HJO.Sweep.corner_eq_neg_cmAscWord_auxVar_mul` reads `Δ^{(k)}F = -T_{1↑k}(y_kF)` in.

The three readings of `HJO.Braid.braidStep` are all supplied:
`HJO.Mellit.Isolates.entryRank_positionPair_snd_of_eventType_C` gives the index `k`,
`HJO.Mellit.Isolates.entryRank_moveOne_positionPair_snd_of_eventType_C` the train `T_{1↘k}`, and
the branch is the `ỹ` one because the entry sits above `θ`: its normalised rank is
`(rk̂(P) + ω - ηlo)/D` with `rk̂(P) > ηlo`, and `θ = ω/D`
(`HJO.Mellit.sweepTheta_eq_div_crossDen`). This last is also the braid-side `ỹ` that
`HJO.Mellit.Isolates.zCount_sub_eq_zero_of_eventType_C` predicted, now read off the letter itself
rather than off the `z`-count. -/
theorem braidStep_positionPair_snd_of_eventType_C (ha : 0 < a) (hb : 0 < b) (hN : 0 < N)
    (hI : Isolates a b N X Y ηlo ηhi) (hηlo : ((a * N : ℕ) : ℚ) < ηlo) {y : Heights a b N}
    (hy : IsAboveDiagonal y) (hev : eventType y (X, Y) = EventType.C) {k : ℕ}
    (hk : #(colouringEast y ηhi) = k) (j : Fin k)
    (hj : colStep (colouringNorth y ηhi) (j : ℕ) = (X, Y))
    (hwin : ((pointRank a b N (X, Y) : ℤ) : ℚ)
      < ηlo + ((b : ℚ) * ((a : ℚ) * N + 1) * N - 1)) :
    braidStep (sweepTheta a b N)
        (positionPair (sweepTheta a b N) (braidDataOfColouring a b N y ηlo k).1
          (braidDataOfColouring a b N y ηhi k).2).2 j
      = braidTrainDown k 1 k * braidYtilde k k := by
  have hD := crossDen_pos (a := a) (b := b) (N := N) ha hb hN
  refine braidStep_eq_trainDown_one_braidYtilde ?_
    (hI.entryRank_positionPair_snd_of_eventType_C ha hb hN hηlo hy hev hk j hj hwin)
    (hI.entryRank_moveOne_positionPair_snd_of_eventType_C ha hb hN hηlo hy hev hk j hj)
  rw [hI.positionPair_snd_of_eventType_C_self ha hb hN hηlo hy hev hk j hj hwin,
    sweepTheta_eq_div_crossDen ha hb hN, div_lt_div_iff_of_pos_right hD]
  have := hI.ltP
  linarith

/-! ### The type-`C` clause with the letter replaced by its closed form -/

section Residual

variable {L : Type*} [Field L] [Algebra ℚ L]

/-- **The type-`C` clause of `HJO.Mellit.braidValueColouring_sweepRecursionsFloor` with the residual
letter evaluated.**
`HJO.Mellit.Isolates.braidValueColouring_eq_sweepOperator_of_eventType_C_of_letter` left the clause
hanging on an identity about `HJO.Braid.braidStep` at an index and a tuple neither of which was
known. `HJO.Mellit.Isolates.braidStep_positionPair_snd_of_eventType_C` evaluates that letter as
`T_{1↘k} ỹ_k`, and `htrain` is the same residual with the letter written out.

**What is left, with the quantifier named.** For every `k`, every above-diagonal path, every
isolating pair and every index `j`: that `π_k` of `T_{1↘k} ỹ_k`, applied to the braid value of the
lower positions with the upper multiplicities and scaled by the `r`-power the two
`HJO.Braid.invFin` counts differ by, is `q^{-(k-1-j)}Δ^{(k)}` of the upper braid value. No
geometry is left in it — no colouring, no `HJO.Mellit.colStep`, no crossing index and no event type
— and the braid word is now the one `HJO.Sweep.corner_eq_neg_cmAscWord_auxVar_mul` states `Δ^{(k)}`
with: `Δ^{(k)}F = -T_{1↑k}(y_kF)` against `T_{1↘k} ỹ_k` here. Matching the two is the remaining
step, and it is **not** taken here. -/
theorem braidValueColouring_eq_sweepOperator_of_eventType_C_of_train (q u : L) {r : L}
    (hq : q ≠ 0) (hq1 : q ≠ 1) (hqp : q + 1 ≠ 0) (hr : r * r = q) (ha : 0 < a) (hb : 0 < b)
    (hN : 0 < N) (hI : Isolates a b N X Y ηlo ηhi) (hηlo : ((a * N : ℕ) : ℚ) < ηlo)
    {y : Heights a b N} (hy : IsAboveDiagonal y) (hev : eventType y (X, Y) = EventType.C)
    {k : ℕ} (hk : #(colouringEast y ηhi) = k) (j : Fin k)
    (hj : colStep (colouringNorth y ηhi) (j : ℕ) = (X, Y))
    (hwin : ((pointRank a b N (X, Y) : ℤ) : ℚ)
      < ηlo + ((b : ℚ) * ((a : ℚ) * N + 1) * N - 1))
    (htrain : r ^ ((invFin (sweepTheta a b N) (braidDataOfColouring a b N y ηlo k).1
            (Function.update (braidDataOfColouring a b N y ηhi k).2 j
              ((braidDataOfColouring a b N y ηhi k).2 j + 1)) : ℤ)
          - (invFin (sweepTheta a b N) (braidDataOfColouring a b N y ηlo k).1
              (braidDataOfColouring a b N y ηhi k).2 : ℤ)) •
        ((braidRepMellit q u hq hq1 hqp hr k (braidTrainDown k 1 k * braidYtilde k k)
            ⟨braidValueOfData q u hq hq1 hqp hr a b N (braidDataOfColouring a b N y ηlo k).1
                (braidDataOfColouring a b N y ηhi k).2,
              braidValueOfData_mem_pieceSub q u hq hq1 hqp hr a b N _ _⟩ : pieceSub L k)
          : Total L)
      = q ^ (-((k - 1 - (j : ℕ) : ℕ) : ℤ)) • corner q k
          (braidValueOfData q u hq hq1 hqp hr a b N (braidDataOfColouring a b N y ηhi k).1
            (braidDataOfColouring a b N y ηhi k).2)) :
    braidValueColouring q u hq hq1 hqp hr a b N ηlo (colouring y ηlo)
      = sweepOperator q u y (X, Y)
          (braidValueColouring q u hq hq1 hqp hr a b N ηhi (colouring y ηhi)) := by
  refine hI.braidValueColouring_eq_sweepOperator_of_eventType_C_of_letter q u hq hq1 hqp hr ha hb
    hN hηlo hy hev hk j hj ?_
  rw [hI.braidStep_positionPair_snd_of_eventType_C ha hb hN hηlo hy hev hk j hj hwin]
  exact htrain

end Residual

end Isolates

/-! ### The consistency check: the decided witness through the general theorem

`HJO.Mellit.braidStep_cdPathC_lo` computed the type-`C` letter at the decided `a = 2`, `b = 3`,
`N = 1` witness by hand — the rank of the moving entry, the rank after the move and the branch, all
three read off the two numbers `13/28` and `1/28`. Here the same letter comes out of
`HJO.Mellit.Isolates.braidStep_positionPair_snd_of_eventType_C`, with the ad-hoc computation
unused, and the two statements are identified by `rfl`.

At this witness every upper multiplicity is `1`, so the mixed final position tuple of
`HJO.Braid.positionPair` is the lower initial tuple itself
(`HJO.Braid.positionPair_snd_of_mult_eq_one`), which is the tuple the hand computation read. -/

/-- **The type-`C` letter at the decided witness, through the general evaluation.** Verbatim
`HJO.Mellit.braidStep_cdPathC_lo`, now with the entry rank `2 = k` and the full train `T_{1↘2}`
supplied by the general theorem rather than computed. -/
theorem braidStep_cdPathC_lo_via_general :
    braidStep (sweepTheta 2 3 1) (braidDataOfColouring 2 3 1 cdPathC cdLoC 2).1 0
      = braidTrainDown 2 1 2 * braidYtilde 2 2 := by
  have hfin : (positionPair (sweepTheta 2 3 1) (braidDataOfColouring 2 3 1 cdPathC cdLoC 2).1
      (braidDataOfColouring 2 3 1 cdPathC cdHiC 2).2).2
      = (braidDataOfColouring 2 3 1 cdPathC cdLoC 2).1 :=
    funext fun t => positionPair_snd_of_mult_eq_one (braidData_cdPathC_hi_snd_eq_one t)
  rw [← hfin]
  exact isolates_cdPathC.braidStep_positionPair_snd_of_eventType_C (by norm_num) (by norm_num)
    (by norm_num) lt_cdLoC isAboveDiagonal_cdPathC eventType_cdPathC
    card_colouringEast_cdPathC_hi 0 colStep_colouringNorth_cdPathC_hi_zero
    (isolates_cdPathC.pointRank_lt_add_of_eventType_C_of_lt (by norm_num) (by norm_num)
      (by norm_num) eventType_cdPathC)

/-- The two readings are the same statement, so the general evaluation lands on the decided
letter — `ỹ` at the top index `2 = k`, after the full train `T_{1↘2}`. -/
example : braidStep_cdPathC_lo = braidStep_cdPathC_lo_via_general := rfl

/-- The same letter through the *other* discharge of the window hypothesis: the witness's two levels
are consecutive (`HJO.Mellit.cdLoC_lt_cdHiC`), so
`HJO.Mellit.Isolates.pointRank_lt_add_of_eventType_C_of_succ` applies and no relation between `a`
and `b` is used. -/
theorem braidStep_cdPathC_lo_via_general_succ :
    braidStep (sweepTheta 2 3 1) (braidDataOfColouring 2 3 1 cdPathC cdLoC 2).1 0
      = braidTrainDown 2 1 2 * braidYtilde 2 2 := by
  have hfin : (positionPair (sweepTheta 2 3 1) (braidDataOfColouring 2 3 1 cdPathC cdLoC 2).1
      (braidDataOfColouring 2 3 1 cdPathC cdHiC 2).2).2
      = (braidDataOfColouring 2 3 1 cdPathC cdLoC 2).1 :=
    funext fun t => positionPair_snd_of_mult_eq_one (braidData_cdPathC_hi_snd_eq_one t)
  rw [← hfin]
  exact isolates_cdPathC.braidStep_positionPair_snd_of_eventType_C (by norm_num) (by norm_num)
    (by norm_num) lt_cdLoC isAboveDiagonal_cdPathC eventType_cdPathC
    card_colouringEast_cdPathC_hi 0 colStep_colouringNorth_cdPathC_hi_zero
    (isolates_cdPathC.pointRank_lt_add_of_eventType_C_of_succ (by norm_num) (by norm_num)
      (by norm_num) cdLoC_lt_cdHiC)

/-- The two discharges give the same statement. -/
example : braidStep_cdPathC_lo_via_general = braidStep_cdPathC_lo_via_general_succ := rfl

/-! ### A second witness, at a multiplicity of `2`

Every upper multiplicity of the type-`C` witness is `1`, so the iterate count in
`HJO.Mellit.positionPair_snd_braidDataOfColouring_eq_div` is `0` there and the identification of the
final tuple with the *bottom* crossing is not exercised. The type-`A` witness of
`HJO/Shuffle/BraidTypeAGapRefuted.lean` — `a = 2`, `b = 5`, `N = 1`,
`HJO.Mellit.gapPath`, `\eta_- = 31/2` — has `\alpha_0 = 2`
(`HJO.Mellit.braidData_gap_snd_zero`), so there the count is `1` and one genuine
`HJO.Braid.nextCrossing` step is taken. Both routes are checked at a different `(a, b, N)` from the
type-`C` witness. -/

/-- The final position of the `0`-th component of the type-`A` witness, computed from the data:
`\alpha_0 = 2`, so it is one `HJO.Braid.nextCrossing` step down from `v_0 = 17/40`, and
`17/40 > \theta = 3/10` puts that step on the subtracting branch: `17/40 - 12/40 = 1/8`. -/
theorem positionPair_snd_gap_zero_decided :
    (positionPair (sweepTheta 2 5 1) (braidDataOfColouring 2 5 1 gapPath gapLo 2).1
        (braidDataOfColouring 2 5 1 gapPath gapLo 2).2).2 0 = 1 / 8 := by
  rw [positionPair_snd, braidData_gap_snd_zero, braidData_gap_fst_zero,
    show (2 : ℕ) - 1 = 1 from rfl, Function.iterate_one, nextCrossing, sweepTheta_gap]
  norm_num

/-- The same through `HJO.Mellit.positionPair_snd_braidDataOfColouring_eq_div`, at a nonzero iterate
count: the `0`-th crossed north step is `u_0 = (0, 2)` of rank `12`, the point above it has rank
`12 + 6 = 18`, and `(18 - 31/2)/20 = 1/8`. -/
theorem positionPair_snd_gap_zero_via_general :
    (positionPair (sweepTheta 2 5 1) (braidDataOfColouring 2 5 1 gapPath gapLo 2).1
        (braidDataOfColouring 2 5 1 gapPath gapLo 2).2).2 0 = 1 / 8 := by
  rw [positionPair_snd_braidDataOfColouring_eq_div (a := 2) (b := 5) (N := 1) (by norm_num)
      (by norm_num) (by norm_num) isAdmissibleLevel_gapLo (by norm_num [gapLo])
      isAboveDiagonal_gapPath (0 : Fin 2) (by rw [card_colouringNorth_gapPath]; norm_num),
    show ((0 : Fin 2) : ℕ) = 0 from rfl, colStep_colouringNorth_gapPath.1, pointRank_gap, crossDen,
    attackWindow, gapLo]
  norm_num

/-- The two readings are the same statement, hence the same value: the general formula for the final
position tuple is right at a multiplicity above `1` too. -/
example : positionPair_snd_gap_zero_decided = positionPair_snd_gap_zero_via_general := rfl

end HJO.Mellit

end
