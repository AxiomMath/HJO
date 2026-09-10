/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.Determinant.DetEquation
public import HJO.Determinant.DetLimit
public meta import HJO.Attr

/-! # The determinant series solves the common equation

The `q`-difference equation for the determinant series is proved in `HJO.DetEquation`
conditionally on the truncated determinants converging, and that convergence is proved in
`HJO.DetLimit`. This module puts the two together.
-/

@[expose] public section

open Finset

namespace HJO.DetSolves

/-- The determinant series, read at `-z`, satisfies the common equation. -/
@[hjo "prop_det_equation"]
theorem isCommonSolution_rescale_neg_one_detSeries (a b : ℕ) (hab : Nat.Coprime a b)
    (ha : 0 < a) (hb : 0 < b) :
    Determinant.IsCommonSolution a b
      (PowerSeries.rescale (-1) (Determinant.detSeries a b)) :=
  DetEquation.isCommonSolution_rescale_neg_one_detSeries a b hab ha hb
    (DetLimit.tendsto_detTrunc a b ha hb)

end HJO.DetSolves
