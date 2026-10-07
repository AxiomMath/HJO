/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Mathlib.RingTheory.Localization.FractionRing
public import HJO.CarlssonMellit.PowerRing
public meta import HJO.Attr

/-! # The swapping operator on the ring of the merged alphabet

The Demazure-type operators of the Carlsson--Mellit layer act on `P°_k`, and the one they are built
from is `ŝ_i`: it interchanges the auxiliary variables `y_i` and `y_{i+1}` in the *coefficients* of
a power series in the alphabet, leaving the alphabet alone. This file defines it.

## Main definitions

* `HJO.Sym.fracSwapAux`: the automorphism of `𝕂(y_1, …, y_k)` interchanging `y_i` and `y_j`.
* `HJO.Sym.pswap`: the automorphism `ŝ_i` of `P°_k`.

## Implementation notes

`ŝ_i` is *not* a renaming of the series variables: it acts coefficientwise on the power series in
`x_1, x_2, …` through the automorphism of `𝕂(y_1, …, y_k)` that interchanges `y_i` and `y_{i+1}`, so
the alphabet is fixed pointwise and all the motion is inside the coefficient field. Accordingly
`pswap` is `MvPowerSeries.map` of the coefficient automorphism, packaged as a `RingEquiv` exactly as
`HJO.Sym.paramInvSeries` is, and `coeff_pswap` is the coefficientwise action that is its whole
content. It fixes every letter (`pswap_X`) and carries the constant series `y_i` to `y_j`
(`pswap_C_yFrac_left`).

The coefficient automorphism is obtained by pushing the renaming `MvPolynomial.renameEquiv` of
`𝕂[y_1, …, y_k]` through the fraction ring, which is `IsFractionRing.ringEquivOfRingEquiv`: the
transposition carries non-zerodivisors to non-zerodivisors, being an automorphism, so no domain
hypothesis is needed and `fracSwapAux` exists over any commutative base.

Auxiliary variables are indexed by `Fin k` from `0`, as in `HJO.Sym.AuxAlphabetSeriesFrac`, so the
variable `y_i` for `1 ≤ i ≤ k` is the image of `MvPolynomial.X (i - 1)`, and `ŝ_i` for `1 ≤ i ≤ k-1`
is `pswap K k i' i'.succ` at `i' = i - 1`. Both indices are taken as arguments rather than one, so
that the degenerate member `i = j` is available and the involutivity and far-commutation lemmas the
`Δ_i` identities need are statements about one family.

The base is a commutative ring, not a field: `FractionRing` is the total ring of fractions of any
commutative ring and nothing here needs more. When `K` is a domain — in particular at `𝕂 = ℚ(q, u)`
— the coefficient ring is a field and the differences `y_{i+1} - y_i` the Demazure operators divide
by become units, which is a hypothesis for those operators and not for this one.

## References

E. Carlsson and
A. Mellit, *A proof of the shuffle conjecture*, J. Amer. Math. Soc. **31** (2018) 661--697,
Section 4.
-/

@[expose] public section

namespace HJO.Sym

variable {K : Type*} [CommRing K]

/-! ### The transposition of two auxiliary variables in the coefficient field -/

/-- The coefficient ring `𝕂(y_1, …, y_k)` of `P°_k`: the total ring of fractions of the polynomials
in the `k` auxiliary variables. Naming it is what keeps the statements below free of metavariables
in the target of `algebraMap`. -/
abbrev AuxFrac (K : Type*) [CommRing K] (k : ℕ) : Type _ :=
  FractionRing (MvPolynomial (Fin k) K)

/-- The auxiliary variable `y_{l+1}` as an element of the coefficient ring. -/
noncomputable def yFrac (K : Type*) [CommRing K] {k : ℕ} (l : Fin k) : AuxFrac K k :=
  algebraMap (MvPolynomial (Fin k) K) _ (MvPolynomial.X l)

/-- The automorphism of `𝕂(y_1, …, y_k)` interchanging `y_i` and `y_j` and fixing every other
auxiliary variable: the renaming automorphism of `𝕂[y_1, …, y_k]` pushed through the fraction ring.
No domain hypothesis is needed — a ring automorphism carries non-zerodivisors to
non-zerodivisors. -/
noncomputable def fracSwapAux (K : Type*) [CommRing K] {k : ℕ} (i j : Fin k) :
    AuxFrac K k ≃+* AuxFrac K k :=
  IsFractionRing.ringEquivOfRingEquiv (MvPolynomial.renameEquiv K (Equiv.swap i j)).toRingEquiv

variable {k : ℕ} {i j : Fin k}

/-- The coefficient automorphism on an honest polynomial in the auxiliary variables: it renames
along the transposition. -/
@[simp]
theorem fracSwapAux_algebraMap (g : MvPolynomial (Fin k) K) :
    fracSwapAux K i j (algebraMap (MvPolynomial (Fin k) K) (AuxFrac K k) g)
      = algebraMap _ _ (MvPolynomial.rename (Equiv.swap i j) g) :=
  IsFractionRing.ringEquivOfRingEquiv_algebraMap _ g

/-- The coefficient automorphism sends `y_i` to `y_j`. -/
@[simp]
theorem fracSwapAux_yFrac_left : fracSwapAux K i j (yFrac K i) = yFrac K j := by
  simp only [yFrac, fracSwapAux_algebraMap, MvPolynomial.rename_X, Equiv.swap_apply_left]

/-- The coefficient automorphism sends `y_j` to `y_i`. -/
@[simp]
theorem fracSwapAux_yFrac_right : fracSwapAux K i j (yFrac K j) = yFrac K i := by
  simp only [yFrac, fracSwapAux_algebraMap, MvPolynomial.rename_X, Equiv.swap_apply_right]

/-- The coefficient automorphism fixes every auxiliary variable outside the transposed pair: `y_l`
is fixed for `l ∉ \{i, i+1\}`. -/
theorem fracSwapAux_yFrac_of_ne {l : Fin k} (hi : l ≠ i) (hj : l ≠ j) :
    fracSwapAux K i j (yFrac K l) = yFrac K l := by
  simp only [yFrac, fracSwapAux_algebraMap, MvPolynomial.rename_X,
    Equiv.swap_apply_of_ne_of_ne hi hj]

/-- The coefficient automorphism fixes the base: the transposition moves no scalar of `𝕂`. -/
@[simp]
theorem fracSwapAux_C (a : K) :
    fracSwapAux K i j (algebraMap (MvPolynomial (Fin k) K) (AuxFrac K k) (MvPolynomial.C a))
      = algebraMap (MvPolynomial (Fin k) K) (AuxFrac K k) (MvPolynomial.C a) := by
  rw [fracSwapAux_algebraMap, MvPolynomial.rename_C]

/-- The coefficient automorphism is an involution: the transposition is. Proved through the
universal property of the fraction ring, two ring homomorphisms out of it agreeing as soon as they
agree on the image of the polynomials. -/
theorem fracSwapAux_comp_self :
    (fracSwapAux K i j).toRingHom.comp (fracSwapAux K i j).toRingHom
      = RingHom.id (AuxFrac K k) := by
  refine IsLocalization.ringHom_ext (nonZeroDivisors (MvPolynomial (Fin k) K)) ?_
  refine MvPolynomial.ringHom_ext (fun a => ?_) (fun l => ?_) <;>
    simp [Equiv.swap_apply_self]

theorem fracSwapAux_fracSwapAux (x : AuxFrac K k) :
    fracSwapAux K i j (fracSwapAux K i j x) = x :=
  congrFun (congrArg (fun f : AuxFrac K k →+* AuxFrac K k => f.toFun) fracSwapAux_comp_self) x

/-! ### The swapping operator on `P°_k` -/

/-- **The swapping operator `ŝ_i`** on `P°_k`: the automorphism acting coefficientwise on the power
series in the alphabet through the automorphism of `𝕂(y_1, …, y_k)` that interchanges `y_i` and
`y_j`. The alphabet is fixed pointwise; all the motion is in the coefficients. The operator `ŝ_i`
for `1 ≤ i ≤ k-1` is this at `j = i.succ`, with auxiliary variables indexed from `0`. -/
@[hjo "def_cm_pswap"]
noncomputable def pswap (K : Type*) [CommRing K] {k : ℕ} (i j : Fin k) :
    AuxAlphabetSeriesFrac K k ≃+* AuxAlphabetSeriesFrac K k :=
  RingEquiv.ofRingHom (MvPowerSeries.map (fracSwapAux K i j : _ →+* _))
    (MvPowerSeries.map ((fracSwapAux K i j).symm : _ →+* _))
    (by ext F e; simp) (by ext F e; simp)

/-- **`ŝ_i` acts coefficientwise**: the coefficient of a monomial in the alphabet moves by the
coefficient automorphism, and the monomial itself does not move. This is the whole content of the
definition. -/
@[hjo "def_cm_pswap", simp]
theorem coeff_pswap (F : AuxAlphabetSeriesFrac K k) (e : ℕ →₀ ℕ) :
    MvPowerSeries.coeff e (pswap K i j F) = fracSwapAux K i j (MvPowerSeries.coeff e F) :=
  rfl

/-- `ŝ_i` fixes every letter of the alphabet: the operator moves the auxiliary variables and nothing
else. This is what separates it from a renaming of the series variables. -/
@[hjo "def_cm_pswap", simp]
theorem pswap_X (l : ℕ) :
    pswap K i j (MvPowerSeries.X l : AuxAlphabetSeriesFrac K k) = MvPowerSeries.X l := by
  refine MvPowerSeries.ext fun e => ?_
  rw [coeff_pswap]
  simp only [MvPowerSeries.coeff_X]
  split <;> simp

/-- `ŝ_i` carries the constant series `y_i` to the constant series `y_j`: the defining
prescription, read inside `P°_k`. -/
@[hjo "def_cm_pswap"]
theorem pswap_C_yFrac_left :
    pswap K i j (MvPowerSeries.C (yFrac K i) : AuxAlphabetSeriesFrac K k)
      = MvPowerSeries.C (yFrac K j) := by
  refine MvPowerSeries.ext fun e => ?_
  rw [coeff_pswap]
  simp only [MvPowerSeries.coeff_C]
  split
  · exact fracSwapAux_yFrac_left
  · exact map_zero _

/-- `ŝ_i` fixes the constant series `y_l` for every `l` outside the transposed pair. -/
@[hjo "def_cm_pswap"]
theorem pswap_C_yFrac_of_ne {l : Fin k} (hi : l ≠ i) (hj : l ≠ j) :
    pswap K i j (MvPowerSeries.C (yFrac K l) : AuxAlphabetSeriesFrac K k)
      = MvPowerSeries.C (yFrac K l) := by
  refine MvPowerSeries.ext fun e => ?_
  rw [coeff_pswap]
  simp only [MvPowerSeries.coeff_C]
  split
  · exact fracSwapAux_yFrac_of_ne hi hj
  · exact map_zero _

/-- `ŝ_i` is an involution, the coefficient automorphism being one. -/
theorem pswap_pswap (F : AuxAlphabetSeriesFrac K k) : pswap K i j (pswap K i j F) = F :=
  MvPowerSeries.ext fun e => by rw [coeff_pswap, coeff_pswap, fracSwapAux_fracSwapAux]

end HJO.Sym
