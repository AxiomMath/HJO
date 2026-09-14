/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.Series.GapForms
public import HJO.CylindricProduct.Exponents
public import HJO.CylindricProduct.SameCommute
public import HJO.CylindricProduct.TransferTrace
public meta import HJO.Attr

/-! # The cylindric weight against the product exponent

Borodin's form of the cylindric series carries the exponent `w_{a,b}(m) = min {a, b, dist(am, dℤ)}`
of `HJO.Defs.cylWeight`, while the HJO product `P_{a,b}` carries the product exponent
`ρ_{a,b}(m) = HJO.negR a b m`. The two differ by one off the multiples of `d`, and this file
records that shift and the normalisation it implies:

`(q; q)_∞ ∏_{m ≥ 1} (1 - q^m)^{-w_{a,b}(m)} = P_{a,b}(q) (q^d; q^d)_∞`.

Both sides are convergent products of integer powers of the `1 - q^m`, so it is enough to compare
exponents at each `m`; the machinery for that is `HJO.Limits.zpowOneSub` and the sequence
`m ↦ 1 - w_{a,b}(m+1)` against `m ↦ -ρ_{a,b}(m+1) + 1_{d | m+1}`.
-/

@[expose] public section

open Finset PowerSeries
open scoped QTheory Topology PowerSeries.DiscreteTopology

namespace HJO.CylindricProduct

/-- **The cylindric weight shifts the product exponent**: `w_{a,b}(m) = ρ_{a,b}(m) + 1 - 1_{d|m}`.
Both exponents are the same minimum `min {a, b, dist(am, dℤ)}`, read once as it stands and once
lowered by one away from the multiples of `d`. Stated in `ℤ`, where the correction is a genuine
subtraction, and for every `m`: no restriction to `m ≥ 1` is needed. -/
@[hjo "lem_cyl_weight_rho"]
theorem cylWeight_eq_negR (a b m : ℕ) (hab : a.Coprime b) :
    (HJO.Defs.cylWeight a b m : ℤ)
      = (HJO.negR a b m : ℤ) + 1 - (if a + b ∣ m then 1 else 0) := by
  rw [HJO.Defs.cylWeight_eq, HJO.Gaps.negR_eq a b m hab]
  ring

/-- The membership condition cut out by `(q^d; q^d)_∞` at the exponent `m + 1` is divisibility
by `d`. -/
theorem selfQPochhammerInf_cond (d m : ℕ) :
    (d ≤ m + 1 ∧ d ∣ (m + 1) - d) ↔ d ∣ m + 1 := by
  refine ⟨fun ⟨hle, hdvd⟩ => ?_, fun hdvd => ⟨Nat.le_of_dvd (by omega) hdvd, ?_⟩⟩
  · obtain ⟨c, hc⟩ := hdvd
    refine ⟨c + 1, ?_⟩
    rw [Nat.mul_add, Nat.mul_one]
    omega
  · obtain ⟨c, hc⟩ := hdvd
    refine ⟨c - 1, ?_⟩
    have hc1 : 1 ≤ c := by
      rcases Nat.eq_zero_or_pos c with rfl | hpos
      · omega
      · exact hpos
    rw [Nat.mul_sub, Nat.mul_one, ← hc]

/-- `(q^d; q^d)_∞` as a product of integer powers of the `1 - q^m`: the exponent at `m` is `1`
exactly at the multiples of `d`. -/
theorem selfQPochhammerInf_eq_tprod {d : ℕ} (hd : 0 < d) :
    ((X ^ d; X ^ d)_∞ : ℤ⟦X⟧)
      = ∏' m, Limits.zpowOneSub m (if d ∣ m + 1 then 1 else 0) := by
  rw [Limits.qPochhammerInf_eq_tprod_zpowOneSub hd hd]
  refine tprod_congr fun m => ?_
  congr 1
  exact if_congr (selfQPochhammerInf_cond d m) rfl rfl

/-- **Normalising the cylindric weight product**:
`(q; q)_∞ ∏_{m ≥ 1} (1 - q^m)^{-w_{a,b}(m)} = P_{a,b}(q) (q^d; q^d)_∞`.

The exponent of `1 - q^m` is `1 - w_{a,b}(m)` on the left and `-ρ_{a,b}(m) + 1_{d|m}` on the
right, and those agree by `cylWeight_eq_negR`. -/
@[hjo "lem_cyl_weight_product"]
theorem qPochhammerInf_mul_tprod_cylWeight {a b : ℕ} (hab : a.Coprime b) (hd : 0 < a + b) :
    ((X; X)_∞ : ℤ⟦X⟧) * ∏' m, Limits.zpowOneSub m (-(HJO.Defs.cylWeight a b (m + 1) : ℤ))
      = HJO.charge a b * ((X ^ (a + b); X ^ (a + b))_∞ : ℤ⟦X⟧) := by
  rw [Limits.qPochhammerInf_self_eq_tprod, Limits.tprod_zpowOneSub_mul,
    Limits.charge_eq_tprod_zpowOneSub, selfQPochhammerInf_eq_tprod hd,
    Limits.tprod_zpowOneSub_mul]
  refine tprod_congr fun m => ?_
  congr 1
  rw [cylWeight_eq_negR a b (m + 1) hab]
  ring

end HJO.CylindricProduct
