/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.CylindricProduct.Borodin
public import HJO.CylindricProduct.Product
public import HJO.Series.Limits
public import HJO.Defs
public meta import HJO.Attr

/-! # The cylindric product is not an assumption

`HJO.Literature.CylindricProduct` states the Foda--Welsh product for the unbounded cylindric
series in its explicit shape, as a ratio of self-Pochhammer symbols with the shift sums
`J_{v,s}` in the exponents. It is proved here.

The route is as follows. Borodin's single-product form,
`HJO.CylindricProduct.borodin_form`, gives `C_c(q) (q^d; q^d)_∞` as
`∏_{m ≥ 1} (1 - q^m)^{-w_{a,b}(m)}`, whose exponent is the cylindric weight; multiplying by
`(q; q)_∞` and applying `HJO.CylindricProduct.qPochhammerInf_mul_tprod_cylWeight` turns the right
side into `P_{a,b}(q) (q^d; q^d)_∞`. The factor `(q^d; q^d)_∞` has constant coefficient `1`, so it
is a unit by `HJO.CylindricProduct.isUnit_selfQPochhammerInf` and cancels, leaving
`(q; q)_∞ C_c(q) = P_{a,b}(q)`. Finally `HJO.Limits.fodaWelsh_eq_charge` identifies the explicit
Foda--Welsh product with `P_{a,b}(q)`, its exponents being those of the HJO product by
`HJO.ProductExponents.total_exponent_eq`.
-/

@[expose] public section

open Finset PowerSeries
open scoped QTheory Topology PowerSeries.DiscreteTopology

namespace HJO.CylindricProductDischarged

/-- `(q)_∞ C_c(q) = P_{a,b}(q)`: the cylindric series, normalised by the `q`-Pochhammer symbol,
is the HJO product. This is Borodin's form with its exponent renormalised, the factor
`(q^d; q^d)_∞` cancelled from both sides as a unit. -/
theorem qPochhammerInf_mul_unboundedGF_eq_charge {a b : ℕ} (hco : Nat.Coprime a b) (ha : 1 < a)
    (hab : a < b) :
    ((X; X)_∞ : ℤ⟦X⟧) * HJO.Cylindric.unboundedGF a b = HJO.charge a b := by
  have hd : 0 < a + b := by omega
  have hmul : (((X; X)_∞ : ℤ⟦X⟧) * HJO.Cylindric.unboundedGF a b) *
      ((X ^ (a + b); X ^ (a + b))_∞ : ℤ⟦X⟧)
      = HJO.charge a b * ((X ^ (a + b); X ^ (a + b))_∞ : ℤ⟦X⟧) := by
    calc (((X; X)_∞ : ℤ⟦X⟧) * HJO.Cylindric.unboundedGF a b) *
          ((X ^ (a + b); X ^ (a + b))_∞ : ℤ⟦X⟧)
        = ((X; X)_∞ : ℤ⟦X⟧) * (HJO.Cylindric.unboundedGF a b *
            ((X ^ (a + b); X ^ (a + b))_∞ : ℤ⟦X⟧)) := by ring
      _ = ((X; X)_∞ : ℤ⟦X⟧) *
            ∏' m, Limits.zpowOneSub m (-(HJO.Defs.cylWeight a b (m + 1) : ℤ)) := by
          rw [CylindricProduct.borodin_form hco (by omega) hab]
      _ = HJO.charge a b * ((X ^ (a + b); X ^ (a + b))_∞ : ℤ⟦X⟧) :=
          CylindricProduct.qPochhammerInf_mul_tprod_cylWeight hco hd
  exact (CylindricProduct.isUnit_selfQPochhammerInf hd).mul_right_cancel hmul

/-- **`CylindricProduct` is not an assumption.** The explicit Foda--Welsh product for the
unbounded cylindric series holds at every coprime pair with `1 < a < b`. -/
theorem cylindricProduct : HJO.Literature.CylindricProduct := by
  intro a b hco ha hab
  rw [qPochhammerInf_mul_unboundedGF_eq_charge hco ha hab,
    ← Limits.fodaWelsh_eq_charge hco ha hab]

end HJO.CylindricProductDischarged
