/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.CarlssonMellit.PDeltaGraded
public import HJO.CarlssonMellit.ZSubring
public meta import HJO.Attr

/-! # The swapping operator on the merged alphabet

The `Δ_m` on `Z^{(k)}` is defined by a division that cannot be performed: it names the
element `H` with

`(z^{(k)}_{m+1} - z^{(k)}_m)H = (q-1)z^{(k)}_{m+1}F + (z^{(k)}_{m+1} - qz^{(k)}_m)ŝ_m(F)`,

"if there is one", the divisor having no constant term and so not being invertible. This file states
that definition as the equation it is, and the uniqueness that stands in for a quotient: the
difference of two distinct letters of the merged alphabet is nonzero and `P°_{k+1}` is a domain, so
there is at most one such `H` and the notation `Δ_m(F)` is unambiguous.

## Main definitions

* `HJO.Sym.zLetterSeries`: the letter `z^{(k+1)}_{k+1+r}` of the merged alphabet as an element of
  `P°_{k+1}`: the constant series `y_{k+1}` at `r = 0` and the letter `x_r` at `r ≥ 1`.
* `HJO.Sym.zdeltaNum`: the numerator `(q-1)z_{m+1}F + (z_{m+1} - qz_m)ŝ_m(F)`.
* `HJO.Sym.IsZDelta`: the defining equation, `H` being `Δ_m(F)`.

## Main results

* `HJO.Sym.zLetterSeries_succ_sub_ne_zero`: the divisor is nonzero. This is what the definition
  rests on.
* `HJO.Sym.eq_of_isZDelta`, there is at most one `Δ_m(F)`.
* `HJO.Sym.isZDelta_one`: `Δ_m(1) = q`, so the equation is satisfiable at a nonzero argument and the
  definition is not vacuous.

## Implementation notes

*`Δ_m` is a relation and not a function, deliberately.* The definition is conditional —
"if there is one" — so a total function would have to invent a value where none exists, and every
statement about it would then carry the existence hypothesis anyway. `HJO.Sym.IsZDelta q r F H` is
the equation, `HJO.Sym.eq_of_isZDelta` is the uniqueness that makes it a partial function, and
`HJO.Sym.zDeltaOn`, in `HJO.CarlssonMellit.ZDeltaDefined`, is where existence on a graded piece is
established.

*The offset, not the absolute index.* As in `HJO.CarlssonMellit.ZSubring`, the operator
`Δ_m` for `m ≥ k` at its level `k` is indexed here by the offset `r = m - (k + 1)` at the level
`k + 1`, so `HJO.Sym.zdeltaNum q r` is the numerator at `m = k + 1 + r`, and the two
letters it involves are `HJO.Sym.zLetterSeries K k r` and `HJO.Sym.zLetterSeries K k (r + 1)`. No
`ℕ`-subtraction appears anywhere.

*Uniqueness needs neither `Z^{(k+1)}`-membership nor a grading.* The natural statement of
`HJO.Sym.eq_of_isZDelta` is for `F, H ∈ Z^{(k)}`, and its proof spends only that `P°_k` is a domain
and that the divisor is nonzero — both facts about the ambient ring. So the membership hypotheses
are dead and are dropped, and the result is stated for arbitrary elements of `P°_{k+1}`.
What the graded structure is needed for is *existence*, which is proved in
`HJO.CarlssonMellit.ZDeltaDefined` through the explicit solution `HJO.Sym.zDeltaOn`.

*The divisor at `r = 0` is not a difference of two power-series variables.* For `r ≥ 1` the two
letters are `x_r` and `x_{r+1}` and the nonvanishing is `HJO.Sym.X_sub_X_ne_zero`; at `r = 0` the
lower letter is the *coefficient* `y_{k+1}`, and what separates the two is that `x_1` has a
coefficient at the monomial `x_1` while a constant series has none. That asymmetry is the whole
reason `Δ_k` is not induced by a substitution and needs the merged alphabet in the first place.

*What is not here.* For `m > k` this `Δ_m` is the
`Δ_{x_{m-k},x_{m-k+1}}` of `HJO.Sym.existsUnique_mem_pGraded_xdeltaNum_eq` — `HJO.Sym.xdelta` of
`HJO.CarlssonMellit.PDeltaGraded`. Identifying the two needs `HJO.Sym.zPerm` at a permutation
of the letters alone to agree with `MvPowerSeries.rename` along that permutation, which holds on
`Z^{(k+1)}` and is not proved here.

## References

E. Carlsson and A. Mellit, *A proof of the shuffle conjecture*, J. Amer. Math. Soc. **31** (2018)
661--697, Section 4, where the divided difference is written as a fraction.
-/

@[expose] public section

namespace HJO.Sym

variable {K : Type*} [CommRing K] [IsDomain K] {k : ℕ}

/-! ### The letters of the merged alphabet as series -/

/-- The letter of the merged alphabet at offset `r` from the level, as an element of `P°_{k+1}`:
the `z^{(k+1)}_{k+1+r}`, which is the constant series `y_{k+1}` at `r = 0` and the
letter `x_r` at `r ≥ 1`. -/
noncomputable def zLetterSeries (K : Type*) [CommRing K] [IsDomain K] (k r : ℕ) :
    AuxAlphabetSeriesFrac K (k + 1) :=
  zMonomial K k (Finsupp.single (zLetter r) 1) 1

/-- The letter at offset `0` is the distinguished letter `y_{k+1}`, a *constant* series: this is the
one that no substitution in `P°_{k+1}` moves. -/
@[simp]
theorem zLetterSeries_zero (K : Type*) [CommRing K] [IsDomain K] (k : ℕ) :
    zLetterSeries K k 0 = MvPowerSeries.C (yFrac K (Fin.last k)) :=
  zMonomial_single_none K k

/-- The letter at offset `r + 1` is the letter `x_{r+1}` of the alphabet. -/
@[simp]
theorem zLetterSeries_succ (K : Type*) [CommRing K] [IsDomain K] (k r : ℕ) :
    zLetterSeries K k (r + 1) = MvPowerSeries.X r :=
  zMonomial_single_some K k r

/-- **The divisor of the swapping operator is nonzero.** Two adjacent letters of the merged alphabet
are distinct in `P°_{k+1}`: at a positive offset they are two power-series variables, and at offset
`0` the upper letter `x_1` has a coefficient at the monomial `x_1` while the lower one, the constant
series `y_{k+1}`, has none. This is the fact `HJO.Sym.IsZDelta` rests on. -/
theorem zLetterSeries_succ_sub_ne_zero (K : Type*) [CommRing K] [IsDomain K] (k r : ℕ) :
    zLetterSeries K k (r + 1) - zLetterSeries K k r ≠ 0 := by
  classical
  cases r with
  | zero =>
    rw [zLetterSeries_succ, zLetterSeries_zero]
    intro h
    have hc := congrArg (MvPowerSeries.coeff (Finsupp.single 0 1)) h
    rw [map_sub, MvPowerSeries.coeff_X, MvPowerSeries.coeff_C, MvPowerSeries.coeff_zero,
      ite_eq_left rfl, ite_eq_right ?_, sub_zero] at hc
    · exact one_ne_zero hc
    · intro h0
      have h1 := congrArg (fun f : ℕ →₀ ℕ => f 0) h0
      simp at h1
  | succ r =>
    rw [zLetterSeries_succ, zLetterSeries_succ]
    exact X_sub_X_ne_zero (Nat.ne_of_lt (Nat.lt_succ_self r))

/-! ### The swapping operator on the merged alphabet -/

/-- The numerator of the swapping operator on the merged alphabet:
`(q-1)z_{m+1}F + (z_{m+1} - qz_m)ŝ_m(F)` at `m = k + 1 + r`, the formula of `HJO.Sym.pdelta` with
the two merged letters in place of the two auxiliary variables. -/
noncomputable def zdeltaNum (q : K) (r : ℕ) (F : AuxAlphabetSeriesFrac K (k + 1)) :
    AuxAlphabetSeriesFrac K (k + 1) :=
  (MvPowerSeries.C (scalarFrac K q) - 1) * zLetterSeries K k (r + 1) * F
    + (zLetterSeries K k (r + 1) - MvPowerSeries.C (scalarFrac K q) * zLetterSeries K k r)
      * zSwap K k r F

theorem zdeltaNum_apply (q : K) (r : ℕ) (F : AuxAlphabetSeriesFrac K (k + 1)) :
    zdeltaNum q r F = (MvPowerSeries.C (scalarFrac K q) - 1) * zLetterSeries K k (r + 1) * F
      + (zLetterSeries K k (r + 1) - MvPowerSeries.C (scalarFrac K q) * zLetterSeries K k r)
        * zSwap K k r F :=
  rfl

/-- **The swapping operator on the merged alphabet**: `H` is `Δ_m(F)` when

`(z^{(k+1)}_{m+1} - z^{(k+1)}_m)H = (q-1)z^{(k+1)}_{m+1}F + (z^{(k+1)}_{m+1} - qz^{(k+1)}_m)ŝ_m(F)`,

at `m = k + 1 + r`. The definition is exactly this equation together with the phrase "if
there is one", so it is a relation and not a function: the divisor has no constant term, hence is
not invertible, and there is nothing to name unless the equation is solvable.
`HJO.Sym.eq_of_isZDelta` is the uniqueness that makes `Δ_m(F)` a well-formed notation, and
`HJO.Sym.zDeltaOn` is where solvability on a graded piece is established. -/
@[hjo "def_cm_zdelta"]
def IsZDelta (q : K) (r : ℕ) (F H : AuxAlphabetSeriesFrac K (k + 1)) : Prop :=
  (zLetterSeries K k (r + 1) - zLetterSeries K k r) * H = zdeltaNum q r F

/-- The defining equation, unfolded. -/
@[hjo "def_cm_zdelta"]
theorem isZDelta_iff (q : K) (r : ℕ) (F H : AuxAlphabetSeriesFrac K (k + 1)) :
    IsZDelta q r F H ↔ (zLetterSeries K k (r + 1) - zLetterSeries K k r) * H
      = (MvPowerSeries.C (scalarFrac K q) - 1) * zLetterSeries K k (r + 1) * F
        + (zLetterSeries K k (r + 1) - MvPowerSeries.C (scalarFrac K q) * zLetterSeries K k r)
          * zSwap K k r F :=
  Iff.rfl

/-- **The swapping operator on the merged alphabet is unique**: at most one `H` satisfies the
equation of `HJO.Sym.IsZDelta`. The two letters are distinct so their difference is nonzero, and
`P°_{k+1}` is a domain, so the factor cancels.

The hypotheses `F, H ∈ Z^{(k)}` of the natural statement are not needed — the proof spends only the
two facts about the ambient ring — so they are dropped. -/
@[hjo "lem_cm_zdelta_unique"]
theorem eq_of_isZDelta {q : K} {r : ℕ} {F H H' : AuxAlphabetSeriesFrac K (k + 1)}
    (h : IsZDelta q r F H) (h' : IsZDelta q r F H') : H = H' :=
  mul_left_cancel₀ (zLetterSeries_succ_sub_ne_zero K k r) (h.trans h'.symm)

/-- `ŝ_m` fixes `1`, the empty merged monomial. -/
@[simp]
theorem zSwap_one (r : ℕ) : zSwap K k r (1 : AuxAlphabetSeriesFrac K (k + 1)) = 1 := by
  have h : (1 : AuxAlphabetSeriesFrac K (k + 1)) = MvPowerSeries.C (auxFracCastSucc K k 1) := by
    rw [map_one, map_one]
  rw [zSwap, h, zPerm_C]

/-- **The equation is satisfiable at a nonzero argument**: `Δ_m(1) = q`. So the definition is not
vacuous, and the operator is not the zero map on the one element every `ŝ_m` fixes. -/
theorem isZDelta_one (q : K) (r : ℕ) :
    IsZDelta q r (1 : AuxAlphabetSeriesFrac K (k + 1)) (MvPowerSeries.C (scalarFrac K q)) := by
  rw [IsZDelta, zdeltaNum_apply, zSwap_one]
  ring

end HJO.Sym
