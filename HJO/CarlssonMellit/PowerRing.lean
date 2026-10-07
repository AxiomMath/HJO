/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Mathlib.Algebra.BigOperators.Finprod
public import Mathlib.Algebra.MvPolynomial.Equiv
public import Mathlib.RingTheory.Localization.FractionRing
public import HJO.Symmetric.SymmetricFunctions
public meta import HJO.Attr

/-! # The ambient rings of the Carlsson--Mellit recursions

The characteristic functions of partial Dyck paths live in the ring
`P_k = 𝕂[y₁, …, y_k]⟦x₁, x₂, …⟧`: formal power series in the alphabet whose coefficients are
polynomial in `k` auxiliary variables. This file fixes that ring for the whole layer together
with the three things built directly on it: the enlargement `P°_k = 𝕂(y₁, …, y_k)⟦x₁, x₂, …⟧` of
its coefficients to their fraction field, on which the Demazure-type operators of the layer act;
the merged variables `z^{(k)}_j`, the single family that reads `y_j` below the level and `x_{j-k}`
above it, out of which every labelling monomial of the layer is a product; and the insertion
`Φ_k : P_k → P_{k+1}`, which turns the first letter into the new auxiliary variable.

## Main definitions

* `HJO.Sym.AuxAlphabetSeries`: the ring `P_k`.
* `HJO.Sym.AuxAlphabetSeriesFrac`: the ring `P°_k`.
* `HJO.Sym.auxToFrac`: the coefficientwise inclusion `P_k → P°_k`.
* `HJO.Sym.zvar`: the merged variable `z^{(k)}_j`.
* `HJO.Sym.insertFront`: the insertion `Φ_k : P_k → P_{k+1}`.

## Implementation notes

The alphabet is indexed by `ℕ` from `0`, so Carlsson and Mellit's letter `x_j` for `j ≥ 1` is
`MvPowerSeries.X (j - 1)`, and the auxiliary variables are indexed by `Fin k` from `0`, so the
paper's `y_i` for `1 ≤ i ≤ k` is the image of `MvPolynomial.X (i - 1)`. Labels are indexed from
`0` as everywhere in this layer — the paper's label `j` is `j - 1` here — so `zvar K k j` is the
paper's `z^{(k)}_{j+1}`, which is `y_{j+1}` exactly for `j < k`.

`AuxAlphabetSeries` and `AuxAlphabetSeriesFrac` are `abbrev`s over the library's own
`HJO.Sym.AlphabetSeries` rather than second copies of `MvPowerSeries`: nothing is true of either
beyond what holds of `MvPowerSeries ℕ A` for a commutative `A`, and reducibility is what makes
both a `CommRing`, a `K`-algebra and an algebra over their coefficient rings, with
`MvPowerSeries.coeff`, `MvPowerSeries.X` and `MvPowerSeries.map` available unchanged.

The containment `P_k ⊆ P°_k` is the *coefficientwise* map `auxToFrac`, not the algebra map
`algebraMap (MvPolynomial (Fin k) K) (AuxAlphabetSeriesFrac K k)`, which lands in the constants; it
is injective over any commutative base.

`insertFront` substitutes `y_{k+1}` for `x₁`, so it turns an unbounded `x₁`-degree into an
unbounded `y_{k+1}`-degree, which the polynomial coefficients of `P_{k+1}` cannot carry. The value
is therefore the substitution exactly where, for each letter-monomial, only finitely many powers of
`x₁` occur, and is `0` where that sum is infinite. That covers every series of bounded total
degree, hence every `ν_σ(π)` and every `ι_k(G)`, which are the only arguments the layer feeds it.

The base is a commutative ring and not a field. `FractionRing` is the total ring of fractions of
any commutative ring, and when `K` is a domain — in particular for the field `𝕂 = ℚ(q, u)`,
the only case the layer instantiates — `MvPolynomial (Fin k) K` is a domain and its fraction ring
is a field, which is what makes the differences `y_{i+1} - y_i` invertible. That hypothesis
belongs on the lemmas that divide, not on the ring.

## References

The definitions `HJO.Sym.AuxAlphabetSeries`, `HJO.Sym.AuxAlphabetSeriesFrac`, `HJO.Sym.zvar` and
`HJO.Sym.insertFront`; E. Carlsson and A. Mellit, *A proof of the shuffle conjecture*, J. Amer.
Math. Soc. **31** (2018) 661--697, Section 4.
-/

@[expose] public section

namespace HJO.Sym

/-! ### The two coefficient rings -/

/-- The formal power series `𝕂[y₁, …, y_k]⟦x₁, x₂, …⟧` in the alphabet with coefficients
polynomial in the `k` auxiliary variables `y₁, …, y_k`: the ring `P_k` in which the characteristic
functions of partial Dyck paths are realised. The paper's letter `x_j`, `j ≥ 1`, is
`MvPowerSeries.X (j - 1)` and its auxiliary variable `y_i`, `1 ≤ i ≤ k`, is the image of
`MvPolynomial.X (i - 1)` under `algebraMap`. At `k = 0` this is the ring `AlphabetSeries K` of
power series in the alphabet, up to the canonical isomorphism induced by
`MvPolynomial.isEmptyAlgEquiv K (Fin 0)` on coefficients. -/
@[hjo "def_cm_pring"]
abbrev AuxAlphabetSeries (K : Type*) [CommRing K] (k : ℕ) : Type _ :=
  AlphabetSeries (MvPolynomial (Fin k) K)

/-- The formal power series `𝕂(y₁, …, y_k)⟦x₁, x₂, …⟧` in the alphabet with coefficients rational
in the `k` auxiliary variables `y₁, …, y_k`: the ring `P°_k` on which the operators `ŝᵢ` and `Δᵢ`
act, obtained from `AuxAlphabetSeries` by enlarging the coefficients to their fraction ring so
that the differences `y_{i+1} - y_i` become invertible. It contains `AuxAlphabetSeries K k`
through the coefficientwise inclusion `HJO.Sym.auxToFrac`, which is injective. -/
@[hjo "def_cm_pring_frac"]
abbrev AuxAlphabetSeriesFrac (K : Type*) [CommRing K] (k : ℕ) : Type _ :=
  AlphabetSeries (FractionRing (MvPolynomial (Fin k) K))

variable {K : Type*} [CommRing K]

/-- The containment `P_k ⊆ P°_k`: the coefficientwise inclusion, acting on each coefficient by the
localization map of the coefficient ring. It is *not* the algebra map of the `MvPowerSeries`
algebra instance, which lands in the constants. -/
noncomputable def auxToFrac (K : Type*) [CommRing K] (k : ℕ) :
    AuxAlphabetSeries K k →ₐ[MvPolynomial (Fin k) K] AuxAlphabetSeriesFrac K k :=
  MvPowerSeries.mapAlgHom (Algebra.ofId _ _)

@[simp]
theorem coeff_auxToFrac (k : ℕ) (F : AuxAlphabetSeries K k) (e : ℕ →₀ ℕ) :
    MvPowerSeries.coeff e (auxToFrac K k F) =
      algebraMap (MvPolynomial (Fin k) K) _ (MvPowerSeries.coeff e F) :=
  rfl

/-- The coefficientwise inclusion of `P_k` in `P°_k` is injective: a series is determined by its
coefficients, and the localization map of a commutative ring at its non-zerodivisors is
injective. -/
theorem auxToFrac_injective (k : ℕ) : Function.Injective (auxToFrac K k) := fun F G h =>
  MvPowerSeries.ext fun e =>
    IsFractionRing.injective (MvPolynomial (Fin k) K)
      (FractionRing (MvPolynomial (Fin k) K)) (by rw [← coeff_auxToFrac, ← coeff_auxToFrac, h])

/-! ### The merged variables -/

/-- The merged variable `z^{(k)}_{j+1}` of the level `k`: the auxiliary variable `y_{j+1}` when the
label `j` lies below the level, and the letter `x_{j+1-k}` when it lies at or above it. This is the
paper's `z^{(k)}_j = y_j` for `j ≤ k` and `x_{j-k}` for `j > k`, with labels indexed from `0`, so
that the paper's label `j` is `j - 1` here and the paper's dividing line `j ≤ k` is `j < k`. -/
@[hjo "def_cm_zvar"]
noncomputable def zvar (K : Type*) [CommRing K] (k j : ℕ) : AuxAlphabetSeries K k :=
  if h : j < k then MvPowerSeries.C (MvPolynomial.X ⟨j, h⟩) else MvPowerSeries.X (j - k)

/-- Below the level the merged variable is an auxiliary variable: the paper's `z^{(k)}_j = y_j`
for `j ≤ k`. -/
@[hjo "def_cm_zvar"]
theorem zvar_of_lt {k j : ℕ} (h : j < k) :
    zvar K k j = MvPowerSeries.C (MvPolynomial.X ⟨j, h⟩) := by
  simp only [zvar, h, ↓reduceDIte]

/-- At or above the level the merged variable is a letter of the alphabet: the paper's
`z^{(k)}_j = x_{j-k}` for `j > k`. -/
@[hjo "def_cm_zvar"]
theorem zvar_of_le {k j : ℕ} (h : k ≤ j) : zvar K k j = MvPowerSeries.X (j - k) := by
  simp only [zvar, Nat.not_lt.2 h, ↓reduceDIte]

/-- At the level `0` every merged variable is a letter, with no shift: the ring `P_0 = P` has
no auxiliary variables, and its `z^{(0)}_j` is `x_j`. -/
@[simp]
theorem zvar_zero (j : ℕ) : zvar K 0 j = MvPowerSeries.X j := by
  rw [zvar_of_le (Nat.zero_le j), Nat.sub_zero]

/-- The first merged variable at a positive level is the first auxiliary variable: the paper's
`z^{(k)}_1 = y_1` for `k ≥ 1`. -/
theorem zvar_zero_left {k : ℕ} (h : 0 < k) :
    zvar K k 0 = MvPowerSeries.C (MvPolynomial.X ⟨0, h⟩) :=
  zvar_of_lt h

/-- The merged variable at the level itself is the first letter: the paper's
`z^{(k)}_{k+1} = x_1`. This is the letter that `HJO.Sym.insertFront` turns into the new auxiliary
variable. -/
theorem zvar_self (K : Type*) [CommRing K] (k : ℕ) : zvar K k k = MvPowerSeries.X 0 := by
  rw [zvar_of_le le_rfl, Nat.sub_self]

/-- A value check of the shift above the level, at the paper's own indices: at the level `k = 2`
the paper's `z^{(2)}_4` is `x_2`, which is the letter `MvPowerSeries.X 1` of the `0`-based
alphabet. An off-by-one in either direction changes this value. -/
theorem zvar_two_three : zvar K 2 3 = MvPowerSeries.X 1 := by
  rw [zvar_of_le (by omega)]

/-- A value check below the level, at the paper's own indices: at the level `k = 2` the paper's
`z^{(2)}_2` is `y_2`, the second auxiliary variable, which is `MvPolynomial.X 1`. -/
theorem zvar_two_one : zvar K 2 1 = MvPowerSeries.C (MvPolynomial.X 1) := by
  rw [zvar_of_lt (by omega)]
  rfl

/-! ### Inserting a variable at the front -/

/-- **Inserting a variable at the front**: the map `Φ_k` from `P_k` to `P_{k+1}` that substitutes
the new auxiliary variable `y_{k+1}` for the first letter `x₁` and `x_{r-1}` for `x_r`, `r ≥ 2`,
leaving `y₁, …, y_k` fixed; on monomials, `y^b x₁^{a₁} x₂^{a₂} ⋯ ↦ y^b y_{k+1}^{a₁} x₁^{a₂} ⋯`. The
coefficient of the image at the letter-monomial `e` is `∑_a y_{k+1}^a` times the coefficient of `F`
at `x₁^a` times `e` pushed up one letter. Substituting `y_{k+1}` for `x₁` turns an `x₁`-degree into
a `y_{k+1}`-degree, so the substitution is defined only where those degrees are bounded: the value
is the substitution for every `F` such that, for each letter-monomial `e`, only finitely many powers
of `x₁` occur, and the coefficient is `0` where that sum is infinite. That covers every `F` of
bounded total degree, hence every `ν_σ(π)` and every `ι_k(G)`. -/
@[hjo "def_cm_insert"]
noncomputable def insertFront (K : Type*) [CommRing K] (k : ℕ) :
    AuxAlphabetSeries K k → AuxAlphabetSeries K (k + 1) := fun F e =>
  ∑ᶠ a : ℕ, MvPolynomial.X (Fin.last k) ^ a *
    MvPolynomial.rename Fin.castSucc
      (MvPowerSeries.coeff (Finsupp.single 0 a + e.mapDomain Nat.succ) F)

/-- The coefficients of `Φ_k F`, by definition: at the letter-monomial `e` the coefficient is the
sum over `a` of `y_{k+1}^a` against the coefficient of `F` at `x₁^a` times `e` pushed up one
letter, with the old auxiliary variables renamed into the first `k` of the new ones. -/
theorem coeff_insertFront (k : ℕ) (F : AuxAlphabetSeries K k) (e : ℕ →₀ ℕ) :
    MvPowerSeries.coeff e (insertFront K k F) =
      ∑ᶠ a : ℕ, MvPolynomial.X (Fin.last k) ^ a *
        MvPolynomial.rename Fin.castSucc
          (MvPowerSeries.coeff (Finsupp.single 0 a + e.mapDomain Nat.succ) F) :=
  rfl

/-- `Φ_k` sends `0` to `0`: every coefficient of the image is an empty sum. -/
@[simp]
theorem insertFront_zero (k : ℕ) : insertFront K k 0 = 0 := by
  refine MvPowerSeries.ext fun e => ?_
  rw [coeff_insertFront]
  simp

end HJO.Sym
