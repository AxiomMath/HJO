/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.CarlssonMellit.PDelta
public meta import HJO.Attr

/-! # The starred swapping operator of the Carlsson--Mellit layer

Beside the operator `Δ_i` of `HJO.CarlssonMellit.PDelta` Carlsson and Mellit use a second
Demazure-type operator on `P°_k = 𝕂(y_1, …, y_k)⟦x_1, x_2, …⟧`,

`Δ*_i(F) = ((q-1) y_i F + (y_{i+1} - q y_i) ŝ_i(F)) / (y_{i+1} - y_i)`,

differing from `Δ_i` only in the auxiliary variable multiplying `F` in the numerator. It is the one
the Demazure--Lusztig operator `T_i` (`HJO.Sweep.braid`) realises, and Carlsson and Mellit's
assertion that `Δ* = qΔ^{-1}` is proved here: `Δ*_i(Δ_i(F)) = qF`.

## Main definitions

* `HJO.Sym.pdeltaStarCoeff`: the operator on the coefficient field, as an additive map.
* `HJO.Sym.pdeltaStar`: the operator `Δ*_i` on `P°_k`.

## Main results

* `HJO.Sym.coeff_pdeltaStar`: `Δ*_i` acts coefficientwise, through `pdeltaStarCoeff`.
* `HJO.Sym.pdeltaStar_pdelta`: `Δ*_i(Δ_i(F)) = qF`, the two operators inverse up to `q`.
* `HJO.Sym.pdeltaStar_mul_of_pswap_eq`: `Δ*_i(gF) = g Δ*_i(F)` for `ŝ_i(g) = g`, which at a
  constant of the base is the `𝕂`-linearity the raising recursion uses.
* `HJO.Sym.pdeltaStar_summableSum`: `Δ*_i` commutes with the sum of a summable family.

## Implementation notes

*The shape is `HJO.Sym.pdelta`'s, verbatim.* Both auxiliary indices are arguments and the base is
`[CommRing K] [IsDomain K]`, so Carlsson and Mellit's `Δ*_{y_i y_{i+1}}` for `1 ≤ i ≤ k-1` is
`pdeltaStar q i j` at `j` the successor of `i`; the `k ≥ 2` and `1 ≤ i ≤ k-1` are the structural
content of having two distinct indices of `Fin k` and are not hypotheses. Every lemma that divides
carries `i ≠ j`. This is forced by the consumer: `HJO.Dyck.isSigmaCharacter_cmDPlus` composes `Δ*_i`
with the `Δ_i` produced by `HJO.Dyck.auxToFrac_partialCharSeries_transposeTuple`, so the two
operators must be indexed alike, and `HJO.Sym.pdelta` fixes the shape.

*The inverse identity is proved on the coefficients.* `Δ*_i` and `Δ_i` both act coefficientwise
(`coeff_pdeltaStar`, `HJO.Sym.coeff_pdelta`), so the whole content of `pdeltaStar_pdelta` is the
field identity `pdeltaStarCoeff_pdeltaCoeff` in `𝕂(y_1, …, y_k)`, where the computation
— `s` fixing `q`, exchanging `u = y_i` with `v = y_{i+1}`, negating `D = v - u`, and being an
involution — reduces to a rational-function identity whose numerator is
`(q-1)^2uv - (v-qu)(u-qv) = q(u-v)^2`. The terms in `ŝ_i` of the coefficient cancel there rather
than in `P°_k`.

*`pswap_C` is stated here.* The general "`ŝ_i` of a constant series is the constant series of the
moved coefficient" is what the composite needs, `HJO.Sym.pswap_C_yFrac_left` and
`HJO.Sym.pswap_C_scalarFrac` being its two instances already recorded upstream.

## References

Definition `HJO.Sym.pdeltaStar` and Lemma `HJO.Sym.pdeltaStar_pdelta`; and E. Carlsson and
A. Mellit, *A proof of the shuffle conjecture*, J. Amer. Math. Soc. **31** (2018) 661--697,
Section 4.
-/

@[expose] public section

namespace HJO.Sym

variable {K : Type*} [CommRing K] {k : ℕ} {i j : Fin k}

/-- `ŝ_i` carries the constant series of a coefficient to the constant series of the moved
coefficient: the alphabet is fixed and all the motion is in the coefficients. -/
@[simp]
theorem pswap_C (c : AuxFrac K k) :
    pswap K i j (MvPowerSeries.C c : AuxAlphabetSeriesFrac K k)
      = MvPowerSeries.C (fracSwapAux K i j c) :=
  MvPowerSeries.ext fun e => by
    rw [coeff_pswap]
    simp only [MvPowerSeries.coeff_C]
    split
    · rfl
    · exact map_zero _

/-! ### The operator on the coefficients -/

/-- The coefficientwise starred swap, as an additive map of the coefficient field: the map
`c ↦ ((q-1) y_i c + (y_j - q y_i) s_i(c)) / (y_j - y_i)`. Additivity holds for the same reason as
for `HJO.Sym.pdeltaCoeff`: `fracSwapAux` is a ring automorphism, and multiplication by and division
by a fixed element are additive. -/
noncomputable def pdeltaStarCoeff [IsDomain K] (q : K) {k : ℕ} (i j : Fin k) :
    AuxFrac K k →+ AuxFrac K k where
  toFun c := (yFrac K j - yFrac K i)⁻¹ *
    ((scalarFrac K q - 1) * yFrac K i * c + (yFrac K j - scalarFrac K q * yFrac K i) *
      fracSwapAux K i j c)
  map_zero' := by simp
  map_add' c c' := by
    simp only [map_add]
    ring

@[simp]
theorem pdeltaStarCoeff_apply [IsDomain K] (q : K) (i j : Fin k) (c : AuxFrac K k) :
    pdeltaStarCoeff q i j c = (yFrac K j - yFrac K i)⁻¹ *
      ((scalarFrac K q - 1) * yFrac K i * c + (yFrac K j - scalarFrac K q * yFrac K i) *
        fracSwapAux K i j c) :=
  rfl

/-! ### The operator on the series -/

/-- **The starred swapping operator `Δ*_i`** on `P°_k`:

`Δ*_i(F) = ((q-1) y_i F + (y_{i+1} - q y_i) ŝ_i(F)) / (y_{i+1} - y_i)`,

Carlsson and Mellit's `Δ*_{y_i y_{i+1}}` made to act on power series in the letters with
coefficients rational in the auxiliary variables. It differs from `HJO.Sym.pdelta` only in the
variable multiplying `F`: `y_i` in place of `y_{i+1}`. Auxiliary variables are indexed from `0` and
both indices are arguments, so their `Δ*_{y_i y_{i+1}}` for `1 ≤ i ≤ k-1` is this at `j` the
successor of `i`. -/
@[hjo "def_cm_pdelta_star"]
noncomputable def pdeltaStar [IsDomain K] (q : K) {k : ℕ} (i j : Fin k)
    (F : AuxAlphabetSeriesFrac K k) : AuxAlphabetSeriesFrac K k :=
  MvPowerSeries.C (yFrac K j - yFrac K i)⁻¹ *
    (MvPowerSeries.C ((scalarFrac K q - 1) * yFrac K i) * F
      + MvPowerSeries.C (yFrac K j - scalarFrac K q * yFrac K i) * pswap K i j F)

variable [IsDomain K] {q : K}

/-- **The starred swapping operator acts coefficientwise**, through `pdeltaStarCoeff`: every factor
of the definition is a constant series, so no factor mixes two monomials in the letters, and `ŝ_i`
moves each coefficient through `fracSwapAux`. -/
theorem coeff_pdeltaStar (F : AuxAlphabetSeriesFrac K k) (e : ℕ →₀ ℕ) :
    MvPowerSeries.coeff e (pdeltaStar q i j F)
      = pdeltaStarCoeff q i j (MvPowerSeries.coeff e F) := by
  rw [pdeltaStar, MvPowerSeries.coeff_C_mul, map_add, MvPowerSeries.coeff_C_mul,
    MvPowerSeries.coeff_C_mul, coeff_pswap, pdeltaStarCoeff_apply]

/-- `Δ*_i` is additive, acting coefficientwise through an additive map. -/
theorem pdeltaStar_add (F G : AuxAlphabetSeriesFrac K k) :
    pdeltaStar q i j (F + G) = pdeltaStar q i j F + pdeltaStar q i j G :=
  MvPowerSeries.ext fun e => by
    simp only [map_add, coeff_pdeltaStar]

@[simp]
theorem pdeltaStar_zero : pdeltaStar q i j (0 : AuxAlphabetSeriesFrac K k) = 0 :=
  MvPowerSeries.ext fun e => by rw [coeff_pdeltaStar, map_zero, map_zero]

/-- The starred swapping operator is linear over invariant coefficients: `Δ*_i(gF) = g Δ*_i(F)`
whenever `ŝ_i(g) = g`. At `g` a constant of the base, which `ŝ_i` fixes, this is the `𝕂`-linearity
of `Δ*_i` that the raising recursion uses. -/
theorem pdeltaStar_mul_of_pswap_eq {g F : AuxAlphabetSeriesFrac K k} (hg : pswap K i j g = g) :
    pdeltaStar q i j (g * F) = g * pdeltaStar q i j F := by
  rw [pdeltaStar, pdeltaStar, show pswap K i j (g * F) = g * pswap K i j F by rw [map_mul, hg]]
  ring

/-! ### The two operators are inverse up to `q` -/

/-- The composite of the two coefficientwise swaps is multiplication by `q`. Writing `u = y_i`,
`v = y_j`, `D = v - u` and `s = fracSwapAux`, so that `s u = v`, `s v = u`, `s D = -D`, `s` fixes
`q` and `s² = id`, the coefficient `((q-1)vc + (v-qu)sc)/D` is carried to
`((q-1)u((q-1)vc + (v-qu)sc) - (v-qu)((q-1)u sc + (u-qv)c))/D²`; the two terms in `sc` cancel and
the bracket multiplying `c` is `(q-1)²uv - (v-qu)(u-qv) = q(u-v)² = qD²`. -/
theorem pdeltaStarCoeff_pdeltaCoeff (hij : i ≠ j) (c : AuxFrac K k) :
    pdeltaStarCoeff q i j (pdeltaCoeff q i j c) = scalarFrac K q * c := by
  have hne : yFrac K j - yFrac K i ≠ (0 : AuxFrac K k) := sub_yFrac_ne_zero hij
  -- With a genuine atom `t` in place of `(y_j - y_i)⁻¹` the identity is a polynomial one: the two
  -- terms in `fracSwapAux c` cancel, and the bracket left multiplying `c` is `q (y_j - y_i)²`.
  have main : ∀ t : AuxFrac K k, t * (yFrac K j - yFrac K i) = 1 →
      t * ((scalarFrac K q - 1) * yFrac K i *
            (t * ((scalarFrac K q - 1) * yFrac K j * c
              + (yFrac K j - scalarFrac K q * yFrac K i) * fracSwapAux K i j c))
          + (yFrac K j - scalarFrac K q * yFrac K i) *
            (-t * ((scalarFrac K q - 1) * yFrac K i * fracSwapAux K i j c
              + (yFrac K i - scalarFrac K q * yFrac K j) * c)))
        = scalarFrac K q * c := fun t ht =>
    calc _ = t * (yFrac K j - yFrac K i) *
          (t * (yFrac K j - yFrac K i) * (scalarFrac K q * c)) := by ring
      _ = scalarFrac K q * c := by rw [ht, one_mul, one_mul]
  simp only [pdeltaStarCoeff_apply, pdeltaCoeff_apply, map_add, map_mul, map_sub, map_one,
    map_inv₀, fracSwapAux_scalarFrac, fracSwapAux_yFrac_left, fracSwapAux_yFrac_right,
    fracSwapAux_fracSwapAux]
  rw [show yFrac K i - yFrac K j = -(yFrac K j - yFrac K i) by ring, inv_neg]
  exact main _ (inv_mul_cancel₀ hne)

/-- **The two swapping operators are inverse up to `q`**: `Δ*_i(Δ_i(F)) = qF`, Carlsson and Mellit's
`Δ* = qΔ^{-1}`. Both operators act coefficientwise, so the identity is the field computation
`pdeltaStarCoeff_pdeltaCoeff` applied to each coefficient of `F`. -/
@[hjo "lem_cm_pdelta_star_inverse"]
theorem pdeltaStar_pdelta (hij : i ≠ j) (F : AuxAlphabetSeriesFrac K k) :
    pdeltaStar q i j (pdelta q i j F) = MvPowerSeries.C (scalarFrac K q) * F :=
  MvPowerSeries.ext fun e => by
    rw [coeff_pdeltaStar, coeff_pdelta, pdeltaStarCoeff_pdeltaCoeff hij,
      MvPowerSeries.coeff_C_mul]

/-! ### Monomialwise sums -/

/-- The image of a summable family under `Δ*_i` is summable: the operator acts coefficientwise
through a map killing `0`. -/
theorem isSummableFamily_pdeltaStar {I : Type*} {F : I → AuxAlphabetSeriesFrac K k}
    (hF : IsSummableFamily F) : IsSummableFamily fun l => pdeltaStar q i j (F l) :=
  hF.map (pdeltaStarCoeff q i j) fun G e => coeff_pdeltaStar G e

/-- The starred swapping operator respects monomialwise sums:
`Δ*_i(∑_l F_l) = ∑_l Δ*_i(F_l)`, both sums being monomialwise finite. -/
theorem pdeltaStar_summableSum {I : Type*} {F : I → AuxAlphabetSeriesFrac K k}
    (hF : IsSummableFamily F) :
    pdeltaStar q i j (summableSum F) = summableSum fun l => pdeltaStar q i j (F l) :=
  map_summableSum hF (pdeltaStarCoeff q i j) fun G e => coeff_pdeltaStar G e

end HJO.Sym
