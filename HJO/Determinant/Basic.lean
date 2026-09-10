/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Mathlib.RingTheory.LaurentSeries
public import HJO.Series.Gaps
public import HJO.Paths.Basic
public meta import HJO.Attr

/-! # The three generating series in `z` and the common equation

The generating functions of the two sides of the finite identity are assembled here: the HJO
generating series, the area generating series, the predicate of satisfying the common
`q`-difference equation, and the determinant series of the weighted path graph.

The three series live in the ring `ℚ((q))⟦z⟧` of formal power series in `z` whose coefficients are
Laurent series in `q` over `ℚ`. The coefficient field is taken to be `ℚ((q))` rather than
`ℤ⟦q⟧` so that the division by `(q)_N` in the HJO generating series is an honest division in a
field, and so that the substitution `z ↦ qz` has an inverse. The integral `q`-series of the
finite HJO polynomial and of the area polynomial are carried into it along `qOfInt`.
-/

@[expose] public section

open Finset PowerSeries
open scoped QTheory PowerSeries.WithPiTopology

namespace HJO.Determinant

/-- The ring `ℚ((q))⟦z⟧`: formal power series in `z` over the field of `q`-Laurent series. -/
abbrev ZSeries : Type := PowerSeries (LaurentSeries ℚ)

/-- The inclusion of integral `q`-power series into the field `ℚ((q))` of `q`-Laurent series. -/
noncomputable def qOfInt : ℤ⟦X⟧ →+* LaurentSeries ℚ :=
  (HahnSeries.ofPowerSeries ℤ ℚ).comp (PowerSeries.map (Int.castRingHom ℚ))

/-- The variable `q`, as an element of the field `ℚ((q))`. -/
noncomputable def qVar : LaurentSeries ℚ := qOfInt X

/-! ### The three series -/

/-- `ℋ(z;q) = ∑_{N ≥ 0} q^{γ_N} F_N(q) z^N / (q)_N`, the generating series of the finite HJO
polynomials, rescaled by the rank shift and divided by the `q`-Pochhammer symbol. -/
@[hjo "def_gen_h"]
noncomputable def genH (a b : ℕ) : ZSeries :=
  mk fun N => qOfInt (X ^ Paths.gammaShift a b N * Gaps.finiteSeries a b N) / qOfInt (X; X)_N

/-- `𝒜(z;q) = ∑_{N ≥ 0} A_N(q) z^N`, the generating series of the area polynomials of the
below-diagonal `(aN, bN)`-paths. -/
@[hjo "def_gen_a"]
noncomputable def genA (a b : ℕ) : ZSeries :=
  mk fun N => qOfInt (Paths.areaPoly a b N)

/-- `G` satisfies the common equation: `G(qz;q) = 𝒜(-z;q) G(z;q)` and `G(0;q) = 1`. -/
@[hjo "def_common_equation"]
def IsCommonSolution (a b : ℕ) (G : ZSeries) : Prop :=
  rescale qVar G = rescale (-1) (genA a b) * G ∧ constantCoeff G = 1

/-! ### The determinant series -/

/-- `L_H(s,q)`, the weighted adjacency matrix on the vertices `0, …, H` of the graph whose edges
are `r → r + b` of weight `s q^{⌊r/a⌋}` and `r → r - a` of weight `s`. -/
noncomputable def weightedAdjacency (a b H : ℕ) :
    Matrix (Fin (H + 1)) (Fin (H + 1)) (Polynomial (LaurentSeries ℚ)) :=
  .of fun r c =>
    if (c : ℕ) = (r : ℕ) + b then Polynomial.C (qVar ^ ((r : ℕ) / a)) * Polynomial.X
    else if (r : ℕ) = (c : ℕ) + a then Polynomial.X else 0

/-- `𝒟_H(z;q) = det(I - L_H(s,q))` written in the variable `z = s^d`: its coefficient of `z^N`
is the coefficient of `s^{dN}` of the determinant. -/
noncomputable def detTrunc (a b H : ℕ) : ZSeries :=
  mk fun N => (1 - weightedAdjacency a b H).det.coeff ((a + b) * N)

/-- `𝒟(z;q)`, the coefficientwise limit of `𝒟_H(z;q)` as `H → ∞`: the limit is taken in the
topology on `ℚ((q))⟦z⟧` in which a sequence converges exactly when each of its `z`-coefficients
converges in `ℚ((q))`. -/
@[hjo "def_det_series"]
noncomputable def detSeries (a b : ℕ) : ZSeries :=
  Filter.limUnder Filter.atTop (detTrunc a b)

end HJO.Determinant
