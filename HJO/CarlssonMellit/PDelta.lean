/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.CarlssonMellit.PSwap
public import HJO.PointwiseSum
public meta import HJO.Attr

/-! # The swapping operator of the Carlsson--Mellit layer

Built from the interchange `ŝ_i` of two auxiliary variables, the Demazure-type operator

`Δ_i(F) = ((q-1) y_{i+1} F + (y_{i+1} - q y_i) ŝ_i(F)) / (y_{i+1} - y_i)`

acts on `P°_k = 𝕂(y_1, …, y_k)⟦x_1, x_2, …⟧`, and it is the operator Carlsson and Mellit's
Proposition 4.8 applies to the characteristic series of a partial Dyck path. This file defines it
and proves the four identities that proposition's proof uses: it acts coefficientwise, it is linear
over `ŝ_i`-invariant series, it multiplies an `ŝ_i`-invariant series by `q`, it carries `y_i` to
`y_{i+1}`, and it respects monomialwise sums.

## Main definitions

* `HJO.Sym.pdeltaCoeff`: the operator on the coefficient field, as an additive map.
* `HJO.Sym.pdelta`: the operator `Δ_i` on `P°_k`.

## Main results

* `HJO.Sym.coeff_pdelta`: `Δ_i` acts coefficientwise, through `pdeltaCoeff`.
* `HJO.Sym.pdelta_mul_of_pswap_eq`: `Δ_i(gF) = g Δ_i(F)` for `ŝ_i(g) = g`.
* `HJO.Sym.pdelta_of_pswap_eq`: `Δ_i(F) = qF` for `ŝ_i(F) = F`.
* `HJO.Sym.pdelta_C_yFrac`: `Δ_i(y_i) = y_{i+1}`.
* `HJO.Sym.pdelta_summableSum`: `Δ_i` commutes with the sum of a summable family.

## Implementation notes

*The base is a commutative domain, not an arbitrary commutative ring.* `Δ_i` divides by
`y_{i+1} - y_i`, so the coefficient ring must be a field: over `[CommRing K] [IsDomain K]` the
polynomials `MvPolynomial (Fin k) K` form a domain and `AuxFrac K k` is its fraction *field*, which
is what `HJO.Sym.AuxAlphabetSeriesFrac` was enlarged for. The `𝕂 = ℚ(q, u)` is such a
base. The hypothesis is on this file and not on `HJO.Sym.PowerRing`, exactly as that file's note
says.

*Both indices are taken as arguments*, as for `HJO.Sym.pswap`: Carlsson and Mellit's
`Δ_{y_i y_{i+1}}` for `1 ≤ i ≤ k-1` is `pdelta q i j` at `j` the successor of `i`. Every lemma below
that divides carries `i ≠ j`, which is what makes `y_j - y_i` invertible and is automatic at the
indices `i`, `i + 1`; at `i = j` the difference is `0`, its inverse is the junk value `0`, and `Δ_i`
is identically `0`.

*`q` enters as a scalar of the base, through `HJO.Sym.scalarFrac`.* It is therefore fixed by `ŝ_i`
(`fracSwapAux_scalarFrac`), which Carlsson and Mellit use without comment and which the three
identities below all use.

*`Δ_i` is defined by the ring formula, and its coefficientwise action is a theorem.* `pdeltaCoeff`
is stated first, so that `HJO.Sym.coeff_pdelta` can name it; but `pdelta` does not mention it, being
the product and sum of series of the defining formula.

*`pdelta_summableSum` is stated in `P°_k`, where `Δ_i` lives.* One might state
`HJO.Sym.pdelta_summableSum` for a family in `P_k`, which `Δ_i` does not act on: `P_k` reaches
`P°_k` only through `HJO.Sym.auxToFrac`, so the statement there is this one composed with that
inclusion. The version below is the general one.

## References

The definition `HJO.Sym.pdelta` and the lemmas `HJO.Sym.coeff_pdelta`, `HJO.Sym.pdeltaCoeff`,
`HJO.Sym.pdelta_mul_of_pswap_eq`, `HJO.Sym.pdelta_of_pswap_eq`, `HJO.Sym.pdelta_C_yFrac` and
`HJO.Sym.pdelta_summableSum`; and E. Carlsson and A. Mellit, *A proof of the shuffle conjecture*, J.
Amer. Math. Soc. **31** (2018) 661--697, Section 4.
-/

@[expose] public section

namespace HJO.Sym

variable {K : Type*} [CommRing K]

/-- A scalar of the base, read inside the coefficient ring `𝕂(y_1, …, y_k)`: this is how the
parameter `q` enters the swapping operator. Being a constant it is fixed by every
`fracSwapAux`. -/
noncomputable def scalarFrac (K : Type*) [CommRing K] {k : ℕ} (a : K) : AuxFrac K k :=
  algebraMap (MvPolynomial (Fin k) K) _ (MvPolynomial.C a)

variable {k : ℕ} {i j : Fin k}

@[simp]
theorem fracSwapAux_scalarFrac (a : K) : fracSwapAux K i j (scalarFrac K a) = scalarFrac K a :=
  fracSwapAux_C a

@[simp]
theorem pswap_C_scalarFrac (a : K) :
    pswap K i j (MvPowerSeries.C (scalarFrac K a) : AuxAlphabetSeriesFrac K k)
      = MvPowerSeries.C (scalarFrac K a) :=
  MvPowerSeries.ext fun e => by
    rw [coeff_pswap]
    simp only [MvPowerSeries.coeff_C]
    split
    · exact fracSwapAux_scalarFrac a
    · exact map_zero _

/-- `ŝ_i` carries the constant series `y_j` to the constant series `y_i`, the other half of the
prescription defining `ŝ_i`. -/
@[simp]
theorem pswap_C_yFrac_right :
    pswap K i j (MvPowerSeries.C (yFrac K j) : AuxAlphabetSeriesFrac K k)
      = MvPowerSeries.C (yFrac K i) :=
  MvPowerSeries.ext fun e => by
    rw [coeff_pswap]
    simp only [MvPowerSeries.coeff_C]
    split
    · exact fracSwapAux_yFrac_right
    · exact map_zero _

/-- The two auxiliary variables of an interchange are distinct elements of the coefficient field as
soon as their indices are: the polynomial variables are distinct and the localization map is
injective. This is what makes the division in `Δ_i` meaningful. -/
theorem sub_yFrac_ne_zero [IsDomain K] (hij : i ≠ j) :
    yFrac K j - yFrac K i ≠ (0 : AuxFrac K k) := by
  rw [sub_ne_zero]
  intro h
  exact hij (MvPolynomial.X_injective
    (IsFractionRing.injective (MvPolynomial (Fin k) K) (AuxFrac K k) h)).symm

/-! ### The operator on the coefficients -/

/-- **The coefficientwise swap is additive and kills zero**: the map
`c ↦ ((q-1) y_j c + (y_j - q y_i) s_i(c)) / (y_j - y_i)` of the coefficient field
`𝕂(y_1, …, y_k)`, packaged as an additive map. Additivity is the content: `fracSwapAux`
is a ring automorphism hence additive, multiplication by a fixed element and division by a fixed
element are additive, and a sum of additive maps is additive; each sends `0` to `0`. -/
@[hjo "lem_cm_pdelta_coeff_additive"]
noncomputable def pdeltaCoeff [IsDomain K] (q : K) {k : ℕ} (i j : Fin k) :
    AuxFrac K k →+ AuxFrac K k where
  toFun c := (yFrac K j - yFrac K i)⁻¹ *
    ((scalarFrac K q - 1) * yFrac K j * c + (yFrac K j - scalarFrac K q * yFrac K i) *
      fracSwapAux K i j c)
  map_zero' := by simp
  map_add' c c' := by
    simp only [map_add]
    ring

@[simp]
theorem pdeltaCoeff_apply [IsDomain K] (q : K) (i j : Fin k) (c : AuxFrac K k) :
    pdeltaCoeff q i j c = (yFrac K j - yFrac K i)⁻¹ *
      ((scalarFrac K q - 1) * yFrac K j * c + (yFrac K j - scalarFrac K q * yFrac K i) *
        fracSwapAux K i j c) :=
  rfl

/-! ### The operator on the series -/

/-- **The swapping operator `Δ_i`** on `P°_k`:

`Δ_i(F) = ((q-1) y_{i+1} F + (y_{i+1} - q y_i) ŝ_i(F)) / (y_{i+1} - y_i)`,

Carlsson and Mellit's `Δ_{y_i y_{i+1}}` made to act on power series in the letters with coefficients
rational in the auxiliary variables. Auxiliary variables are indexed from `0` and both indices are
arguments, so their `Δ_{y_i y_{i+1}}` for `1 ≤ i ≤ k-1` is this at `j` the successor of `i`. -/
@[hjo "def_cm_pdelta"]
noncomputable def pdelta [IsDomain K] (q : K) {k : ℕ} (i j : Fin k)
    (F : AuxAlphabetSeriesFrac K k) : AuxAlphabetSeriesFrac K k :=
  MvPowerSeries.C (yFrac K j - yFrac K i)⁻¹ *
    (MvPowerSeries.C ((scalarFrac K q - 1) * yFrac K j) * F
      + MvPowerSeries.C (yFrac K j - scalarFrac K q * yFrac K i) * pswap K i j F)

variable [IsDomain K] {q : K}

/-- **The swapping operator acts coefficientwise**: the coefficient of a monomial in the letters in
`Δ_i(F)` is `pdeltaCoeff` applied to the coefficient of that monomial in `F`. Every factor of the
definition is a constant series, so no factor mixes two monomials in the letters, and `ŝ_i` moves
each coefficient through `fracSwapAux`. -/
@[hjo "lem_cm_pdelta_coeffwise"]
theorem coeff_pdelta (F : AuxAlphabetSeriesFrac K k) (e : ℕ →₀ ℕ) :
    MvPowerSeries.coeff e (pdelta q i j F) = pdeltaCoeff q i j (MvPowerSeries.coeff e F) := by
  rw [pdelta, MvPowerSeries.coeff_C_mul, map_add, MvPowerSeries.coeff_C_mul,
    MvPowerSeries.coeff_C_mul, coeff_pswap, pdeltaCoeff_apply]

/-- `Δ_i` is additive, acting coefficientwise through an additive map. -/
theorem pdelta_add (F G : AuxAlphabetSeriesFrac K k) :
    pdelta q i j (F + G) = pdelta q i j F + pdelta q i j G :=
  MvPowerSeries.ext fun e => by
    simp only [map_add, coeff_pdelta]

@[simp]
theorem pdelta_zero : pdelta q i j (0 : AuxAlphabetSeriesFrac K k) = 0 :=
  MvPowerSeries.ext fun e => by rw [coeff_pdelta, map_zero, map_zero]

/-- **The swapping operator is linear over invariant coefficients**: `Δ_i(gF) = g Δ_i(F)` whenever
`ŝ_i(g) = g`. The interchange is a ring homomorphism, so `ŝ_i(gF) = g ŝ_i(F)`, and `g` factors out
of the numerator. -/
@[hjo "lem_cm_pdelta_symmetric"]
theorem pdelta_mul_of_pswap_eq {g F : AuxAlphabetSeriesFrac K k} (hg : pswap K i j g = g) :
    pdelta q i j (g * F) = g * pdelta q i j F := by
  rw [pdelta, pdelta, show pswap K i j (g * F) = g * pswap K i j F by rw [map_mul, hg]]
  ring

/-- **The swapping operator on an invariant series**: `Δ_i(F) = qF` whenever `ŝ_i(F) = F`. The
numerator becomes `((q-1) y_j + y_j - q y_i) F = q (y_j - y_i) F`, and the division by
`y_j - y_i ≠ 0` leaves `qF`. -/
@[hjo "lem_cm_pdelta_fix"]
theorem pdelta_of_pswap_eq (hij : i ≠ j) {F : AuxAlphabetSeriesFrac K k}
    (hF : pswap K i j F = F) :
    pdelta q i j F = MvPowerSeries.C (scalarFrac K q) * F := by
  have hne : yFrac K j - yFrac K i ≠ (0 : AuxFrac K k) := sub_yFrac_ne_zero hij
  have key : (yFrac K j - yFrac K i)⁻¹ *
      ((scalarFrac K q - 1) * yFrac K j + (yFrac K j - scalarFrac K q * yFrac K i))
      = scalarFrac K q := by
    rw [show (scalarFrac K q - 1) * yFrac K j + (yFrac K j - scalarFrac K q * yFrac K i)
        = (yFrac K j - yFrac K i) * scalarFrac K q by ring,
      ← mul_assoc, inv_mul_cancel₀ hne, one_mul]
  rw [pdelta, hF, ← add_mul, ← map_add, ← mul_assoc, ← map_mul, key]

/-- **The swapping operator moves the variable**: `Δ_i(y_i) = y_{i+1}`. The interchange sends `y_i`
to `y_j`, so the numerator is `(q-1) y_j y_i + (y_j - q y_i) y_j = y_j (y_j - y_i)`. -/
@[hjo "lem_cm_pdelta_ym"]
theorem pdelta_C_yFrac (hij : i ≠ j) (q : K) :
    pdelta q i j (MvPowerSeries.C (yFrac K i) : AuxAlphabetSeriesFrac K k)
      = MvPowerSeries.C (yFrac K j) := by
  have hne : yFrac K j - yFrac K i ≠ (0 : AuxFrac K k) := sub_yFrac_ne_zero hij
  rw [pdelta, pswap_C_yFrac_left, ← map_mul, ← map_mul, ← map_add, ← map_mul]
  congr 1
  rw [show (scalarFrac K q - 1) * yFrac K j * yFrac K i
        + (yFrac K j - scalarFrac K q * yFrac K i) * yFrac K j
      = (yFrac K j - yFrac K i) * yFrac K j by ring,
    ← mul_assoc, inv_mul_cancel₀ hne, one_mul]

/-! ### Monomialwise sums -/

/-- The image of a summable family under `Δ_i` is summable: the operator acts coefficientwise
through a map killing `0`, so the members reaching a monomial afterwards are among those reaching it
before. -/
theorem isSummableFamily_pdelta {I : Type*} {F : I → AuxAlphabetSeriesFrac K k}
    (hF : IsSummableFamily F) : IsSummableFamily fun l => pdelta q i j (F l) :=
  hF.map (pdeltaCoeff q i j) fun G e => coeff_pdelta G e

/-- **The swapping operator respects monomialwise sums**: for a family in `P°_k` only finitely many
of whose members have a nonzero coefficient at any given monomial in the letters,
`Δ_i(∑_l F_l) = ∑_l Δ_i(F_l)`, both sums being monomialwise finite. -/
@[hjo "lem_cm_pdelta_sums"]
theorem pdelta_summableSum {I : Type*} {F : I → AuxAlphabetSeriesFrac K k}
    (hF : IsSummableFamily F) :
    pdelta q i j (summableSum F) = summableSum fun l => pdelta q i j (F l) :=
  map_summableSum hF (pdeltaCoeff q i j) fun G e => coeff_pdelta G e

end HJO.Sym
