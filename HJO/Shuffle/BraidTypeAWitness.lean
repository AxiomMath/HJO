/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.Shuffle.BraidTypeAGapRefuted
public import HJO.Shuffle.BraidValueUnswept
public import HJO.Shuffle.MellitDplusVacuum
public meta import HJO.Attr

/-! # The type-`A` clause holds at the witness where its only route was refuted

`HJO/Shuffle/BraidTypeAGapRefuted.lean` refutes the rank squeeze — the hypothesis of
`HJO.Braid.braidWord_map_succAbove_mul_trainDown_one_of_le`, the only stated route to the type-`A`
clause of `HJO.Mellit.braidValueColouring_sweepRecursionsFloor` — at the configuration `a = 2`,
`b = 5`, `N = 1`, path `HJO.Mellit.gapPath`, levels `\eta_- = 31/2` and `\eta_+ = 33/2`, isolated
point `P = (1, 5)`. That file says in as many words that what it refutes is the route and not the
clause, and that deciding the clause itself at that configuration "would be a computation in
`HJO.Braid.BraidMonoid`".

**This file performs that computation. The clause HOLDS at the witness.**

`HJO.Mellit.braidValueColouring_gap_typeA` is the verdict: at exactly the data the refutation uses,
the braid value of `HJO.Mellit.braidValueColouring` satisfies the conclusion of
`HJO.Mellit.SweepRecursionACD`,

`R \eta_- (c_-) = \Phi_{\widehat P}(P) (R \eta_+ (c_+))`,

and every hypothesis of that clause is discharged at this instance by the refutation file's own
lemmas (`HJO.Mellit.isolates_gapPath`, `HJO.Mellit.isAboveDiagonal_gapPath`,
`HJO.Mellit.mem_sweptRegion_gapPath`) together with
`HJO.Mellit.ht_lt_or_ht_succ_eq_gapPath` below. So the refutation does not propagate to the clause,
and the type-`A` clause needs a different route rather than being false.

## What the computation is

The two ranks are `k_- = 2` and `k_+ = 1` (`HJO.Mellit.card_colouringEast_gapPath`,
`HJO.Mellit.card_colouringEast_gapPath_hi`), and `k_{\widehat P}(P) = 1`
(`HJO.Mellit.sweepWidth_gap`), so the event operator is `d_+ : V_1 \to V_2`
(`HJO.Mellit.sweepOperator_gap`). The two special-braid data are

* at `\eta_-`: `v = (17/40, 1/40)`, `\alpha = (2, 1)`, from the refutation file;
* at `\eta_+`: `v = (3/8)`, `\alpha = (2)` (`HJO.Mellit.braidData_gap_hi_fst`,
  `HJO.Mellit.braidData_gap_hi_snd`).

Both move sequences are a single move of the entry of largest position, and both positions are
**above** `\theta = 3/10`, so each move contributes a `\tilde y` letter and no train:
`HJO.Mellit.specialBraid_gap_lo` gives `B_- = \tilde y_2` and `HJO.Mellit.specialBraid_gap_hi` gives
`B_+ = \tilde y_1`. The two inversion counts agree on both sides
(`HJO.Mellit.invFin_eq_invIni_gap_lo`, `HJO.Mellit.invFin_eq_invIni_gap_hi`), so `\delta = 0`
and the half-integral prefactor is `1` — the clause is tested with no `q`-power that could
absorb a discrepancy.

Then `\tilde y_2 = T_1 y_1 \bar T_1` in `𝔹_2^+(𝕋_0)` (`HJO.Mellit.braidYtilde_two_two`), the two
`q^{\mp 1/2}` normalisations cancel, `\bar T_1` fixes `d_+^2(1)`
(`HJO.Sweep.braidInvEnd_dplusIter`), and `d_+^k(1) = (-1)^k y_1\cdots y_k`
(`HJO.Sweep.dplusIter_eq_smul_auxVarProd`). Both sides come out as `-T_1(y_1^2y_2)`:

* `HJO.Mellit.braidValueOfPath_gap_lo` — the lower value is `-T_1(y_1y_1y_2)`;
* `HJO.Mellit.braidValueOfPath_gap_hi` — the upper value is `y_1^2`, and `d_+` of it is the same
  thing, since `\tau_{2,2}` fixes `y_1` and `T_{1↗2} = T_1`.

## Genericity, and that nothing degenerated

The exclusions carried are exactly `HJO.Sweep.braidRepMellit`'s — `q \ne 0`, `q \ne 1`,
`q + 1 \ne 0`, `r * r = q` — plus `r \ne 0`, which follows from the first and the last. **`u` does
not enter and no inverse is evaluated**: both braids consist of `T`, `\bar T` and `y` letters only,
so neither the `(q-1)^{-1}` of `HJO.Sweep.corner` nor the `(qu)^{-1}` of `HJO.Sweep.zop` occurs, and
`q \ne 0` is spent only on `T_1\bar T_1 = 1` and on `r^{-1}r = 1`. The identity is therefore not the
degenerate `0 = 0` of a letter that became the zero map:
`HJO.Mellit.braidValueOfPath_gap_hi_ne_zero` shows the upper value is nonzero over every field,
and `HJO.Mellit.braidEnd_gap_value` gives the common value in closed form,
`y_1y_2^2 - (q-1)y_1^2y_2` up to sign, whose leading monomial has coefficient `-1`.

## What this does and does not settle

It settles **one instance** of the type-`A` clause, the one instance at which the clause's only
stated route is known to fail. It is therefore evidence that the clause is true and that the squeeze
was merely sufficient; it is not the clause, which quantifies over all `a`, `b`, `N`, paths, points
and bracketing levels. The general statement `HJO.Mellit.braidValueColouring_sweepRecursionsFloor`
is proved in `HJO/Shuffle/MellitThm58Closed.lean`, and the general argument this witness suggests —
that the type-`A` event inserts a fixed point of least rank whose component contributes the identity
braid, so that the only letter is the one the retained components already carried — is not carried
out.

## References

Declarations involved: `HJO.Mellit.braidValueColouring_sweepRecursionsFloor`,
`HJO.Mellit.not_forall_pointRank_le_add_rankDen`, `HJO.Mellit.Isolates.pointRank_le`,
`HJO.Mellit.braidValueColouring_eq_dsc_floor`, `HJO.Mellit.dsc_lo_eq_dplus_dsc_hi`,
`HJO.Mellit.braidDataOfColouring`, `HJO.Braid.specialBraid`, `HJO.Sweep.braidRep`,
`HJO.Braid.braidYtilde`, `HJO.Mellit.sweepOperator`, `HJO.Sweep.dplus`, `HJO.Sweep.braid_dplusIter`,
`HJO.Sweep.dplus_dplusIter`. Transcribing A. Mellit, *Toric braids and `(m, n)`-parking functions*,
section 5.
-/

@[expose] public section

open Finset

namespace HJO.Mellit

open ParkingFunctions Paths Sweep Braid

/-! ### The upper level of the witness bracket -/

/-- The upper level is positive, which the position closed forms read. -/
theorem gapHi_pos : (0 : ℚ) < gapHi := by norm_num [gapHi]

/-- **Only one east step is crossed at `\eta_+`.** At `33/2` the step `(0, 4)` is still crossed,
`rk̂(1,4) = 10 < 33/2 < 24`, but `(1, 5) = P` is not: its rank is `16 < 33/2`. So the level drop
past `P` is exactly the insertion of a new component, which is what a type-`A` event does. -/
theorem colouringEast_gapPath_hi : colouringEast gapPath gapHi = {((0 : ℕ), (4 : ℕ))} := by
  ext P
  rw [colouringEast, Finset.mem_filter, eastSteps_gapPath]
  constructor
  · rintro ⟨hP, h⟩
    revert h
    fin_cases hP <;> norm_num [gapHi, pointRank_gap]
  · intro hP
    rw [Finset.mem_singleton] at hP
    subst hP
    exact ⟨by decide, by norm_num [gapHi, pointRank_gap]⟩

/-- **Only one north step is crossed at `\eta_+`**: `(0, 2)`, with `12 < 33/2 < 18`. The step
`(1, 4)` that the type-`A` event creates has `10 < 33/2` but `33/2 > 16 = 10 + \omega`, so it is
below the window. -/
theorem colouringNorth_gapPath_hi : colouringNorth gapPath gapHi = {((0 : ℕ), (2 : ℕ))} := by
  ext P
  rw [colouringNorth, Finset.mem_filter, northSteps_gapPath]
  constructor
  · rintro ⟨hP, h⟩
    revert h
    fin_cases hP <;> norm_num [gapHi, pointRank_gap, attackWindow_gap]
  · intro hP
    rw [Finset.mem_singleton] at hP
    subst hP
    exact ⟨by decide, by norm_num [gapHi, pointRank_gap, attackWindow_gap]⟩

/-- The rank above the drop is `k_+ = 1`, one less than `k_- = 2`. -/
theorem card_colouringEast_gapPath_hi : #(colouringEast gapPath gapHi) = 1 := by
  rw [colouringEast_gapPath_hi]; decide

/-- The two halves have the same cardinality at `\eta_+` as well. -/
theorem card_colouringNorth_gapPath_hi : #(colouringNorth gapPath gapHi) = 1 := by
  rw [colouringNorth_gapPath_hi]; decide

/-- The single crossed east step at `\eta_+`, read through the column listing. -/
theorem colStep_colouringEast_gapPath_hi :
    colStep (colouringEast gapPath gapHi) 0 = (0, 4) := by
  have h0 : colStep (colouringEast gapPath gapHi) 0 ∈ ({((0 : ℕ), (4 : ℕ))} : Finset (ℕ × ℕ)) := by
    rw [← colouringEast_gapPath_hi]
    exact colStep_mem (by rw [card_colouringEast_gapPath_hi]; omega)
  exact Finset.mem_singleton.1 h0

/-- The single crossed north step at `\eta_+`, read through the column listing. -/
theorem colStep_colouringNorth_gapPath_hi :
    colStep (colouringNorth gapPath gapHi) 0 = (0, 2) := by
  have h0 : colStep (colouringNorth gapPath gapHi) 0 ∈ ({((0 : ℕ), (2 : ℕ))} : Finset (ℕ × ℕ)) := by
    rw [← colouringNorth_gapPath_hi]
    exact colStep_mem (by rw [card_colouringNorth_gapPath_hi]; omega)
  exact Finset.mem_singleton.1 h0

/-- `HJO.Mellit.levelPosition` at the upper level: a rank `r` sits at `(3/10)(r - 33/2)/6`. -/
theorem levelPosition_gap_hi (r : ℚ) :
    levelPosition 2 5 1 gapHi r = 3 / 10 * ((r - 33 / 2) / 6) := by
  rw [levelPosition, sweepTheta_gap, gapHi]; norm_num

/-- The level index of the column `0` is still `2` at `\eta_+`: `12 < 33/2 < 18`. -/
theorem levelIndex_gap_hi_zero : levelIndex 2 5 1 gapHi 0 = 2 := by
  rw [levelIndex, gapHi]; norm_num [Int.floor_eq_iff]

/-- **The position of the one component above the drop is `3/8`**, the normalised rank of its
crossed east step `(0, 4)`: `(3/10)(24 - 33/2)/6 = 15/40`. -/
theorem braidData_gap_hi_fst_zero :
    (braidDataOfColouring 2 5 1 gapPath gapHi 1).1 0 = 3 / 8 := by
  have hi : ((0 : Fin 1) : ℕ) < #(colouringEast gapPath gapHi) := by
    rw [card_colouringEast_gapPath_hi]; norm_num
  rw [braidDataOfColouring_fst_eq_levelPosition (a := 2) (b := 5) (N := 1) (by norm_num)
      (by norm_num) (by norm_num) isAdmissibleLevel_gapHi gapHi_pos (0 : Fin 1) hi,
    show ((0 : Fin 1) : ℕ) = 0 from rfl, colStep_colouringEast_gapPath_hi, pointRank_gap,
    levelPosition_gap_hi]
  norm_num

/-- **The multiplicity above the drop is `2`**, unchanged: the top index `4` and the bottom index
`0 + 2 + 1 = 3` are the same as at `\eta_-`, so the retained component keeps its move. -/
theorem braidData_gap_hi_snd_zero :
    (braidDataOfColouring 2 5 1 gapPath gapHi 1).2 0 = 2 := by
  have hi : (0 : ℕ) < #(colouringEast gapPath gapHi) := by
    rw [card_colouringEast_gapPath_hi]; norm_num
  rw [braidDataOfColouring_snd, show ((0 : Fin 1) : ℕ) = 0 from rfl,
    componentCrossingIndices_eq_Icc, Int.card_Icc,
    componentBotIndex_eq (a := 2) (b := 5) (N := 1) (by norm_num) (by norm_num) (by norm_num)
      isAdmissibleLevel_gapHi gapHi_pos gapPath 0,
    componentTopIndex_eq (a := 2) (b := 5) (N := 1) (by norm_num) (by norm_num) (by norm_num)
      isAdmissibleLevel_gapHi gapHi_pos hi,
    colStep_colouringEast_gapPath_hi, colStep_colouringNorth_gapPath_hi]
  norm_num [levelIndex_gap_hi_zero]
  rfl

/-! ### Ranks and inversions of a short tuple -/

/-- The only entry of a one-entry tuple has rank `1`. -/
private theorem entryRank_one (w : Fin 1 → ℚ) (i : Fin 1) : entryRank w i = 1 := by
  rw [entryRank, Finset.filter_true_of_mem (fun j _ => by fin_cases j; fin_cases i; exact le_rfl)]
  rfl

/-- The larger entry of a two-entry tuple has rank `2`. -/
private theorem entryRank_pair_zero {w : Fin 2 → ℚ} (h : w 1 ≤ w 0) : entryRank w 0 = 2 := by
  rw [entryRank, Finset.filter_true_of_mem (fun j _ => by fin_cases j; · exact le_rfl
                                                          · exact h)]
  rfl

/-- A one-entry tuple has no inversion, there being no pair of indices. -/
private theorem tupleInversions_one (w : Fin 1 → ℚ) : tupleInversions w = 0 := by
  rw [tupleInversions, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  rintro ⟨i, j⟩ -
  fin_cases i
  fin_cases j
  simp

/-- A decreasing two-entry tuple has exactly one inversion, the pair `(0, 1)`. -/
private theorem tupleInversions_pair {w : Fin 2 → ℚ} (h : w 1 < w 0) : tupleInversions w = 1 := by
  rw [tupleInversions_eq_card_lt,
    show {p ∈ (univ : Finset (Fin 2 × Fin 2)) | p.1 < p.2 ∧ w p.2 < w p.1}
        = {((0 : Fin 2), (1 : Fin 2))} from ?_]
  · rfl
  ext p
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
  obtain ⟨i, j⟩ := p
  fin_cases i <;> fin_cases j <;> simp_all

/-! ### The braid data of the two levels as explicit tuples -/

/-- The positions below the drop, as a tuple: `(17/40, 1/40)`. -/
theorem braidData_gap_lo_fst :
    (braidDataOfColouring 2 5 1 gapPath gapLo 2).1 = ![17 / 40, 1 / 40] := by
  funext i
  fin_cases i
  · simpa using braidData_gap_fst_zero
  · simpa using braidData_gap_fst_one

/-- The multiplicities below the drop, as a tuple: `(2, 1)`. -/
theorem braidData_gap_lo_snd :
    (braidDataOfColouring 2 5 1 gapPath gapLo 2).2 = ![2, 1] := by
  funext i
  fin_cases i
  · simpa using braidData_gap_snd_zero
  · simpa using braidData_gap_snd_one

/-- The position above the drop, as a tuple: `(3/8)`. -/
theorem braidData_gap_hi_fst :
    (braidDataOfColouring 2 5 1 gapPath gapHi 1).1 = ![3 / 8] := by
  funext i
  fin_cases i
  simpa using braidData_gap_hi_fst_zero

/-- The multiplicity above the drop, as a tuple: `(2)`. -/
theorem braidData_gap_hi_snd :
    (braidDataOfColouring 2 5 1 gapPath gapHi 1).2 = ![2] := by
  funext i
  fin_cases i
  simpa using braidData_gap_hi_snd_zero

/-! ### The two special braids -/

/-- Below the drop the move sequence is the single move of the entry `0`, the inserted entry `1`
having multiplicity `1`. -/
theorem specialMoveList_gap_lo : specialMoveList ![2, 1] = [(0 : Fin 2)] := by decide

/-- Above the drop the move sequence is the single move of the one entry. -/
theorem specialMoveList_gap_hi : specialMoveList ![2] = [(0 : Fin 1)] := by decide

/-- **`B_- = \tilde y_2`.** The one move is of the entry at `17/40`, which is above
`\theta = 3/10`, so the letter is a `\tilde y` and not a `z`; and the move does not change that
entry's rank — `17/40 \mapsto 5/40` stays above `1/40` — so the descending train is empty. -/
theorem specialBraid_gap_lo :
    specialBraid (sweepTheta 2 5 1) ![(17 : ℚ) / 40, 1 / 40] ![2, 1] = braidYtilde 2 2 := by
  have hgt : sweepTheta 2 5 1 < ![(17 : ℚ) / 40, 1 / 40] 0 := by
    rw [sweepTheta_gap]; norm_num
  have hr0 : entryRank ![(17 : ℚ) / 40, 1 / 40] 0 = 2 := entryRank_pair_zero (by norm_num)
  have hr1 : entryRank (moveOne (sweepTheta 2 5 1) ![(17 : ℚ) / 40, 1 / 40] 0) 0 = 2 := by
    refine entryRank_pair_zero ?_
    rw [moveOne_of_ne _ _ (by decide), moveOne_self, nextCrossing, sweepTheta_gap]
    norm_num
  rw [specialBraid, specialMoveList_gap_lo, braidWord_singleton, braidStep_of_gt hgt, hr0, hr1,
    braidTrainDown_self, one_mul]

/-- **`B_+ = \tilde y_1`.** At rank `1` every train is empty and every entry has rank `1`; the
position `3/8` is above `\theta`, so again a `\tilde y` letter. -/
theorem specialBraid_gap_hi :
    specialBraid (sweepTheta 2 5 1) ![(3 : ℚ) / 8] ![2] = braidYtilde 1 1 := by
  have hgt : sweepTheta 2 5 1 < ![(3 : ℚ) / 8] 0 := by rw [sweepTheta_gap]; norm_num
  rw [specialBraid, specialMoveList_gap_hi, braidWord_singleton, braidStep_of_gt hgt,
    entryRank_one, entryRank_one, braidTrainDown_self, one_mul]

/-! ### Both exponents vanish -/

/-- **`inv_fin = inv_ini` below the drop**, both counts being `1`: the move `17/40 \mapsto 5/40`
does not carry the entry past `1/40`. So the clause is tested at `\delta = 0`. -/
theorem invFin_eq_invIni_gap_lo :
    invFin (sweepTheta 2 5 1) ![(17 : ℚ) / 40, 1 / 40] ![2, 1]
      = invIni (sweepTheta 2 5 1) ![(17 : ℚ) / 40, 1 / 40] ![2, 1] := by
  rw [invFin_eq_tupleInversions, invIni_eq_tupleInversions,
    tupleInversions_pair (w := ![(17 : ℚ) / 40, 1 / 40]) (by norm_num)]
  refine tupleInversions_pair ?_
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  norm_num [nextCrossing, sweepTheta_gap]

/-- **`inv_fin = inv_ini` above the drop**, both counts being `0` at rank `1`. -/
theorem invFin_eq_invIni_gap_hi :
    invFin (sweepTheta 2 5 1) ![(3 : ℚ) / 8] ![2]
      = invIni (sweepTheta 2 5 1) ![(3 : ℚ) / 8] ![2] := by
  rw [invFin_eq_tupleInversions, invIni_eq_tupleInversions, tupleInversions_one,
    tupleInversions_one]

/-! ### The width at the witness, and the event hypothesis -/

/-- The level line through `P = (1, 5)` crosses exactly one north step of the path, `(0, 2)`: the
step `(1, 4)` has `rk̂ + \omega = 16 = rk̂(P)`, so `P` is its head and not inside it. -/
theorem liveSteps_gap : liveSteps gapPath ((1 : ℕ), (5 : ℕ)) = {((0 : ℕ), (2 : ℕ))} := by decide

/-- `k_{\widehat P}(P) = 1`, so the event operator raises `V_1` to `V_2` — matching
`k_+ = 1` and `k_- = 2`. -/
theorem sweepWidth_gap : sweepWidth gapPath ((1 : ℕ), (5 : ℕ)) = 1 := by
  rw [sweepWidth, liveSteps_gap]; decide

/-- The event hypothesis of `HJO.Mellit.SweepRecursionACD` at the witness, `ŷ_1 = 4 < 5`. With
`HJO.Mellit.isolates_gapPath`, `HJO.Mellit.isAboveDiagonal_gapPath` and
`HJO.Mellit.mem_sweptRegion_gapPath` this is every hypothesis of that clause at this instance. -/
theorem ht_lt_or_ht_succ_eq_gapPath : ht gapPath 1 < 5 ∨ ht gapPath (1 + 1) = 5 := by decide

/-! ### The two braids, written in the generators -/

/-- **`\tilde y_2 = T_1 y_1 \bar T_1` in `𝔹_2^+(𝕋_0)`.** By `HJO.Braid.braidYtilde_self` the
commuting lift is `T_{2↘1}T_{1↗2}y_2`, both trains are the single letter `T_1`, and
`y_2 = \bar T_1 y_1 \bar T_1`; one `T_1\bar T_1` cancels. -/
theorem braidYtilde_two_two :
    braidYtilde 2 2 = braidGenT 2 1 * braidGenY 2 1 * braidGenTinv 2 1 := by
  have hT : braidTrainDown 2 2 1 = braidGenT 2 1 := by
    simp [Braid.trainDown, Braid.descendingWord]
  have hU : braidTrainUp 2 1 2 = braidGenT 2 1 := by
    simp [Braid.trainUp, Braid.ascendingWord]
  have hY : braidGenY 2 2 = braidGenTinv 2 1 * braidGenY 2 1 * braidGenTinv 2 1 :=
    braidGenY_succ 2 0
  have hinv : braidGenT 2 1 * braidGenTinv 2 1 = 1 :=
    braidGenT_mul_inv (by omega) (by omega)
  rw [braidYtilde_self, hT, hU, hY]
  calc braidGenT 2 1 * braidGenT 2 1 * (braidGenTinv 2 1 * braidGenY 2 1 * braidGenTinv 2 1)
      = braidGenT 2 1 * (braidGenT 2 1 * braidGenTinv 2 1) *
          (braidGenY 2 1 * braidGenTinv 2 1) := by simp only [mul_assoc]
    _ = braidGenT 2 1 * braidGenY 2 1 * braidGenTinv 2 1 := by
        rw [hinv, mul_one, mul_assoc]

section Operators

variable {L : Type*} [Field L] [Algebra ℚ L]

/-! ### The vacuum tower at ranks one and two -/

omit [Algebra ℚ L] in
/-- `d_+(1) = -y_1`. -/
theorem dplusIter_one_eq (q : L) : dplusIter q 1 = -(auxVar 1 : Total L) := by
  rw [dplusIter_eq_smul_auxVarProd, auxVarProd_succ, auxVarProd_zero, one_mul, pow_one,
    neg_one_smul]

omit [Algebra ℚ L] in
/-- `d_+^2(1) = y_1y_2`. -/
theorem dplusIter_two_eq (q : L) :
    dplusIter q 2 = (auxVar 1 : Total L) * (auxVar 2 : Total L) := by
  rw [dplusIter_eq_smul_auxVarProd, auxVarProd_succ, auxVarProd_succ, auxVarProd_zero, one_mul]
  norm_num

omit [Algebra ℚ L] in
/-- The ascending train from `1` to `2` is the single operator `T_1`. -/
theorem trainUpEnd_one_two (q : L) : trainUpEnd q 1 2 = braidEnd q 1 := by
  simp [trainUpEnd, Braid.trainUp, Braid.ascendingWord]

/-! ### `π_k` on the three generators the witness uses -/

/-- `π_k(T_i) = q^{-1/2}T_i` on `V_k`, read on the total space. -/
theorem coe_braidRepMellit_T (q u : L) {r : L} (hq : q ≠ 0) (hq1 : q ≠ 1) (hqp : q + 1 ≠ 0)
    (hr : r * r = q) {k i : ℕ} (hi : 1 ≤ i) (hik : i + 1 ≤ k) (x : pieceSub L k) :
    ((braidRepMellit q u hq hq1 hqp hr k (braidGenT k i) x : pieceSub L k) : Total L)
      = r⁻¹ • braidEnd q i (x : Total L) :=
  coe_braidRep_T q u r (braidRepRespects_mellit q u hq hq1 hqp hr k) hi hik x

/-- `π_k(\bar T_i) = q^{1/2}T_i^{-1}` on `V_k`, read on the total space. -/
theorem coe_braidRepMellit_Tbar (q u : L) {r : L} (hq : q ≠ 0) (hq1 : q ≠ 1) (hqp : q + 1 ≠ 0)
    (hr : r * r = q) {k i : ℕ} (hi : 1 ≤ i) (hik : i + 1 ≤ k) (x : pieceSub L k) :
    ((braidRepMellit q u hq hq1 hqp hr k (braidGenTinv k i) x : pieceSub L k) : Total L)
      = r • braidInvEnd q i (x : Total L) :=
  coe_braidRep_Tbar q u r (braidRepRespects_mellit q u hq hq1 hqp hr k) hi hik x

/-- `π_k(y_1)` is multiplication by `-y_1`. This is the only loop letter the witness evaluates; in
particular the `z` assignment of `HJO.Sweep.braidRep`, with its `(qu)^{-1}`, is never read. -/
theorem coe_braidRepMellit_y (q u : L) {r : L} (hq : q ≠ 0) (hq1 : q ≠ 1) (hqp : q + 1 ≠ 0)
    (hr : r * r = q) {k : ℕ} (hk : 1 ≤ k) (x : pieceSub L k) :
    ((braidRepMellit q u hq hq1 hqp hr k (braidGenY k 1) x : pieceSub L k) : Total L)
      = -((auxVar 1 : Total L) * (x : Total L)) := by
  rw [braidRepMellit, braidRep_y, coe_yRep, yRepTotal_one q u r hk]
  simp

/-! ### The two braid values -/

/-- **The braid value above the drop is `y_1^2`.** The braid is `\tilde y_1 = y_1`, the prefactor is
`1`, and `d_+(1) = -y_1`. -/
theorem braidValueOfData_gap_hi (q u : L) {r : L} (hq : q ≠ 0) (hq1 : q ≠ 1) (hqp : q + 1 ≠ 0)
    (hr : r * r = q) :
    braidValueOfData q u hq hq1 hqp hr 2 5 1 ![(3 : ℚ) / 8] ![2]
      = (auxVar 1 : Total L) * (auxVar 1 : Total L) := by
  rw [braidValueOfData, specialBraid_gap_hi, invFin_eq_invIni_gap_hi, sub_self, zpow_zero,
    one_smul, braidYtilde_one_one, coe_braidRepMellit_y q u hq hq1 hqp hr (le_refl 1),
    coe_dplusIterPiece, dplusIter_one_eq]
  ring

/-- **The braid value below the drop is `-T_1(y_1^2y_2)`.** The braid is
`\tilde y_2 = T_1y_1\bar T_1`, whose two normalising scalars `r^{-1}` and `r` cancel; `\bar T_1`
fixes `d_+^2(1) = y_1y_2`, multiplication by `-y_1` gives `-y_1^2y_2`, and `T_1` is applied
last. -/
theorem braidValueOfData_gap_lo (q u : L) {r : L} (hq : q ≠ 0) (hq1 : q ≠ 1) (hqp : q + 1 ≠ 0)
    (hr : r * r = q) :
    braidValueOfData q u hq hq1 hqp hr 2 5 1 ![(17 : ℚ) / 40, 1 / 40] ![2, 1]
      = -braidEnd q 1 ((auxVar 1 : Total L) * (auxVar 1) * (auxVar 2)) := by
  have hrne : r ≠ 0 := fun h => hq (by rw [← hr, h, mul_zero])
  rw [braidValueOfData, specialBraid_gap_lo, invFin_eq_invIni_gap_lo, sub_self, zpow_zero,
    one_smul, braidYtilde_two_two, map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply,
    coe_braidRepMellit_T q u hq hq1 hqp hr (le_refl 1) (by omega),
    coe_braidRepMellit_y q u hq hq1 hqp hr (by omega),
    coe_braidRepMellit_Tbar q u hq hq1 hqp hr (le_refl 1) (by omega),
    coe_dplusIterPiece, braidInvEnd_dplusIter q hq (le_refl 1) (by omega), dplusIter_two_eq,
    mul_smul_comm, map_neg, map_smul, smul_neg, smul_smul, inv_mul_cancel₀ hrne, one_smul]
  congr 2
  ring

/-! ### The event operator at the witness -/

/-- **The event operator is `d_+` at index `1`**, the event being of type `A` and the width `1`. -/
theorem sweepOperator_gap (q u : L) :
    sweepOperator q u gapPath ((1 : ℕ), (5 : ℕ)) = dplus q 1 := by
  rw [sweepOperator, eventType_gapPath, sweepWidth_gap]

/-! ### The two braid values of the path -/

/-- The braid value of the path at `\eta_-`. -/
theorem braidValueOfPath_gap_lo (q u : L) {r : L} (hq : q ≠ 0) (hq1 : q ≠ 1) (hqp : q + 1 ≠ 0)
    (hr : r * r = q) :
    braidValueOfPath q u hq hq1 hqp hr gapPath gapLo
      = -braidEnd q 1 ((auxVar 1 : Total L) * (auxVar 1) * (auxVar 2)) := by
  rw [braidValueOfPath, card_colouringEast_gapPath, braidData_gap_lo_fst, braidData_gap_lo_snd,
    braidValueOfData_gap_lo]

/-- The braid value of the path at `\eta_+`. -/
theorem braidValueOfPath_gap_hi (q u : L) {r : L} (hq : q ≠ 0) (hq1 : q ≠ 1) (hqp : q + 1 ≠ 0)
    (hr : r * r = q) :
    braidValueOfPath q u hq hq1 hqp hr gapPath gapHi
      = (auxVar 1 : Total L) * (auxVar 1 : Total L) := by
  rw [braidValueOfPath, card_colouringEast_gapPath_hi, braidData_gap_hi_fst,
    braidData_gap_hi_snd, braidValueOfData_gap_hi]

/-! ### The verdict -/

/-- **THE TYPE-`A` IDENTITY HOLDS AT THE WITNESS.** At `a = 2`, `b = 5`, `N = 1`, the path
`HJO.Mellit.gapPath`, the isolated type-`A` point `P = (1, 5)` and the bracketing levels
`\eta_- = 31/2`, `\eta_+ = 33/2` — the exact configuration at which
`HJO.Mellit.not_forall_braidDataOfColouring_fst_lt_add_sweepTheta` refutes the rank squeeze, hence
the only stated route to this clause — the braid value satisfies the clause:
`R_- = d_+ R_+`, with `\delta = 0`.

Both sides are `-T_1(y_1^2y_2)`, and `HJO.Mellit.braidEnd_gap_value` writes that out. So the
refutation does not carry over to the clause, and the hypotheses of
`HJO.Braid.braidWord_map_succAbove_mul_trainDown_one_of_le` really are sufficient and not
necessary. -/
theorem braidValueOfPath_gap_typeA (q u : L) {r : L} (hq : q ≠ 0) (hq1 : q ≠ 1) (hqp : q + 1 ≠ 0)
    (hr : r * r = q) :
    braidValueOfPath q u hq hq1 hqp hr gapPath gapLo
      = sweepOperator q u gapPath (1, 5) (braidValueOfPath q u hq hq1 hqp hr gapPath gapHi) := by
  have hax : (auxVar 1 : Total L) = MvPolynomial.X 0 := rfl
  have htop : (auxVar (1 + 1) : Total L) = auxVar 2 := rfl
  have hqs : qshift q (1 + 1) ((auxVar 1 : Total L) * (auxVar 1 : Total L))
      = (auxVar 1 : Total L) * (auxVar 1 : Total L) := by
    rw [hax, map_mul, qshift_auxVar]
  rw [braidValueOfPath_gap_lo, braidValueOfPath_gap_hi, sweepOperator_gap, dplus_apply,
    trainUpEnd_one_two, hqs]
  congr 2
  rw [htop]
  ring

/-! ### The common value, and that it is not zero -/

omit [Algebra ℚ L] in
/-- **The common value of the two sides, written out**: `T_1(y_1^2y_2) = y_1y_2^2 - (q-1)y_1^2y_2`,
by `HJO.Sweep.braid_apply` with `s_1(y_1^2y_2) = y_1y_2^2` and `\partial_1(y_1^2y_2) = -y_1y_2`. The
monomial `y_1y_2^2` has coefficient `1` whatever `q` is, so the identity of
`HJO.Mellit.braidValueOfPath_gap_typeA` is not an identity between two zero maps. -/
theorem braidEnd_gap_value (q : L) :
    braidEnd q 1 ((auxVar 1 : Total L) * (auxVar 1) * (auxVar 2))
      = (MvPolynomial.X 0 : Total L) * MvPolynomial.X 1 * MvPolynomial.X 1
        - scal (q - 1) *
          ((MvPolynomial.X 0 : Total L) * MvPolynomial.X 0 * MvPolynomial.X 1) := by
  have hax1 : (auxVar 1 : Total L) = MvPolynomial.X 0 := rfl
  have hax2 : (auxVar 2 : Total L) = MvPolynomial.X 1 := rfl
  have hs0 : swapAux L 1 (MvPolynomial.X 0 : Total L) = MvPolynomial.X 1 := by
    rw [swapAux_X]; simp
  have hs1 : swapAux L 1 (MvPolynomial.X 1 : Total L) = MvPolynomial.X 0 := by
    rw [swapAux_X]; simp
  have hd : dividedDiff 1 ((MvPolynomial.X 0 : Total L) * MvPolynomial.X 0 * MvPolynomial.X 1)
      = -((MvPolynomial.X 0 : Total L) * MvPolynomial.X 1) := by
    refine (dividedDiff_unique (by omega) ?_).symm
    rw [map_mul, map_mul, hs0, hs1]
    norm_num
    ring
  rw [braidEnd, LinearMap.restrictScalars_apply, braid_apply, hax1, hax2, hd, map_mul, map_mul,
    hs0, hs1]
  ring

/-- **The value above the drop is nonzero over every field**, so the identity at the witness is not
the degenerate `0 = 0` that a letter carrying an inverse would produce at `q \in \{0, 1\}` or
`u = 0`. No inverse is evaluated anywhere in this file: see the module docstring. -/
theorem braidValueOfPath_gap_hi_ne_zero (q u : L) {r : L} (hq : q ≠ 0) (hq1 : q ≠ 1)
    (hqp : q + 1 ≠ 0) (hr : r * r = q) :
    braidValueOfPath q u hq hq1 hqp hr gapPath gapHi ≠ (0 : Total L) := by
  rw [braidValueOfPath_gap_hi, show (auxVar 1 : Total L) = MvPolynomial.X 0 from rfl]
  exact mul_ne_zero (MvPolynomial.X_ne_zero 0) (MvPolynomial.X_ne_zero 0)

/-- **The clause of `HJO.Mellit.SweepRecursionACD`, at the witness.** The same verdict as
`HJO.Mellit.braidValueOfPath_gap_typeA`, stated for the candidate
`HJO.Mellit.braidValueColouring` on the colourings rather than for the path — which is the shape the
clause is asked in, and legitimate because `HJO.Mellit.braidValueColouring_colouring` says the
representative does not matter. Every hypothesis of the clause holds at this instance:
`HJO.Mellit.isolates_gapPath`, `HJO.Mellit.isAboveDiagonal_gapPath`,
`HJO.Mellit.mem_sweptRegion_gapPath` and `HJO.Mellit.ht_lt_or_ht_succ_eq_gapPath`. -/
theorem braidValueColouring_gap_typeA (q u : L) {r : L} (hq : q ≠ 0) (hq1 : q ≠ 1)
    (hqp : q + 1 ≠ 0) (hr : r * r = q) :
    braidValueColouring q u hq hq1 hqp hr 2 5 1 gapLo (colouring gapPath gapLo)
      = sweepOperator q u gapPath (1, 5)
          (braidValueColouring q u hq hq1 hqp hr 2 5 1 gapHi (colouring gapPath gapHi)) := by
  rw [braidValueColouring_colouring q u hq hq1 hqp hr isAboveDiagonal_gapPath,
    braidValueColouring_colouring q u hq hq1 hqp hr isAboveDiagonal_gapPath]
  exact braidValueOfPath_gap_typeA q u hq hq1 hqp hr

end Operators

end HJO.Mellit

end
