/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Mathlib.Topology.UniformSpace.Uniformizable
public import HJO.Determinant.Basic
public meta import HJO.Attr

/-! # Convergence of the truncated determinants

The truncated determinants `det(I - L_H(s,q))`, read in the variable `z = s^{a+b}`, converge as
`H → ∞`. The convergence is coefficientwise in `z` and, in each `z`-degree, `X`-adic in the
coefficient field `ℚ((q))`: it is *not* eventual constancy of the `z`-coefficients, which are
polynomials in `q` of degree growing with `H`.

The mechanism is a bound on how far a term of the determinant can reach up the path. Expanding
`det(I - L_{H+1})` along its last row leaves the diagonal term, which is `det(I - L_H)`, together
with terms that all use an entry of the last column; the only edge into the vertex `H + 1` comes
from `H + 1 - b` and carries the weight `q ^ ⌊(H+1-b)/a⌋`. So the two determinants agree modulo
that power of `q`, and since the exponent grows without bound the sequence stabilises in every
fixed `q`-degree.

To make "modulo a power of `q`" meaningful the determinant is computed in an integral model, over
`ℚ⟦q⟧[s]` rather than over the field `ℚ((q))[s]`, and pushed forward along the inclusion
`ℚ⟦q⟧ → ℚ((q))` afterwards.
-/

@[expose] public section

open Finset

namespace HJO.DetLimit

open Determinant
open scoped PowerSeries.WithPiTopology

/-! ### The integral model of the weighted adjacency matrix -/

/-- The inclusion of `q`-power series over `ℚ` into the field `ℚ((q))` of `q`-Laurent series. -/
noncomputable def qOfRat : PowerSeries ℚ →+* LaurentSeries ℚ := HahnSeries.ofPowerSeries ℤ ℚ

/-- `qOfRat` is the standard coercion of power series into Laurent series. -/
theorem qOfRat_apply (f : PowerSeries ℚ) : qOfRat f = (f : LaurentSeries ℚ) := rfl

/-- `qOfRat` carries the power series variable to the Laurent series variable `q`. -/
theorem qOfRat_X : qOfRat PowerSeries.X = qVar := by
  simp only [qVar, qOfInt, qOfRat, RingHom.coe_comp, Function.comp_apply, PowerSeries.map_X]

/-- The integral model of `L_H(s,q)`: the same weighted adjacency matrix, with its `q`-weights read
in the power series ring `ℚ⟦q⟧` instead of in the field `ℚ((q))`. -/
noncomputable def intAdjacency (a b H : ℕ) :
    Matrix (Fin (H + 1)) (Fin (H + 1)) (Polynomial (PowerSeries ℚ)) :=
  .of fun r c =>
    if (c : ℕ) = (r : ℕ) + b then
      Polynomial.C (PowerSeries.X ^ ((r : ℕ) / a)) * Polynomial.X
    else if (r : ℕ) = (c : ℕ) + a then Polynomial.X else 0

/-- `det(I - L_H(s,q))` computed in the integral model `ℚ⟦q⟧[s]`. -/
noncomputable def intDet (a b H : ℕ) : Polynomial (PowerSeries ℚ) :=
  (1 - intAdjacency a b H).det

/-- The integral model of `I - L_H` maps onto `I - L_H` over `ℚ((q))[s]`. -/
theorem mapMatrix_one_sub_intAdjacency (a b H : ℕ) :
    (Polynomial.mapRingHom qOfRat).mapMatrix (1 - intAdjacency a b H)
      = 1 - weightedAdjacency a b H := by
  rw [map_sub, map_one, sub_right_inj]
  ext r c
  simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Polynomial.coe_mapRingHom, intAdjacency,
    weightedAdjacency, Matrix.of_apply]
  split_ifs
  · rw [Polynomial.map_mul, Polynomial.map_C, Polynomial.map_X, map_pow, qOfRat_X]
  · rw [Polynomial.map_X]
  · rw [Polynomial.map_zero]

/-- `det(I - L_H)` over `ℚ((q))[s]` is the image of its integral model. -/
theorem det_one_sub_weightedAdjacency (a b H : ℕ) :
    (1 - weightedAdjacency a b H).det = Polynomial.map qOfRat (intDet a b H) := by
  have h := RingHom.map_det (Polynomial.mapRingHom qOfRat) (1 - intAdjacency a b H)
  rw [mapMatrix_one_sub_intAdjacency] at h
  rw [← h, intDet, Polynomial.coe_mapRingHom]

/-- The `z^N`-coefficient of the truncated determinant is the image of the `s^{(a+b)N}`-coefficient
of the integral model. -/
theorem coeff_detTrunc (a b H N : ℕ) :
    PowerSeries.coeff N (detTrunc a b H) = qOfRat ((intDet a b H).coeff ((a + b) * N)) := by
  rw [detTrunc, PowerSeries.coeff_mk, det_one_sub_weightedAdjacency, Polynomial.coeff_map]

/-! ### The vertex bound -/

/-- The `q`-order that the vertex `H + 1` forces on any term of the determinant using it: the only
edge into that vertex starts at `H + 1 - b` and carries the weight `q ^ ⌊(H+1-b)/a⌋`. -/
def vertexOrder (a b H : ℕ) : ℕ := (H + 1 - b) / a

/-- `vertexOrder` is monotone in the height bound. -/
theorem vertexOrder_le (a b : ℕ) {H H' : ℕ} (h : H ≤ H') :
    vertexOrder a b H ≤ vertexOrder a b H' :=
  Nat.div_le_div_right (by omega)

/-- Every entry of `I - L_{H+1}` in the last column, other than the diagonal one, is divisible by
`q ^ vertexOrder a b H`: the vertex `H + 1` is reached only from `H + 1 - b`. -/
theorem C_pow_dvd_apply_last (a b H : ℕ) (r : Fin (H + 1)) :
    Polynomial.C (PowerSeries.X ^ vertexOrder a b H) ∣
      (1 - intAdjacency a b (H + 1)) r.castSucc (Fin.last (H + 1)) := by
  have hr : (r : ℕ) < H + 1 := r.isLt
  have hne : r.castSucc ≠ Fin.last (H + 1) := (Fin.castSucc_lt_last r).ne
  rw [Matrix.sub_apply, Matrix.one_apply_ne hne, zero_sub, dvd_neg]
  simp only [intAdjacency, Matrix.of_apply, Fin.val_castSucc, Fin.val_last]
  split_ifs with h1 h2
  · have hrb : (r : ℕ) = H + 1 - b := by omega
    rw [vertexOrder, ← hrb]
    exact dvd_mul_right _ _
  · exact absurd h2 (by omega)
  · exact dvd_zero _

/-- Deleting the last row of `I - L_{H+1}` together with any column other than the last leaves a
matrix whose determinant is divisible by `q ^ vertexOrder a b H`: every term of the Leibniz
expansion must use an entry of the last column. -/
theorem C_pow_dvd_det_submatrix (a b H : ℕ) {j : Fin (H + 2)} (hj : j ≠ Fin.last (H + 1)) :
    Polynomial.C (PowerSeries.X ^ vertexOrder a b H) ∣
      ((1 - intAdjacency a b (H + 1)).submatrix Fin.castSucc j.succAbove).det := by
  obtain ⟨i₀, hi₀⟩ := Fin.exists_succAbove_eq hj.symm
  rw [Matrix.det_apply']
  refine Finset.dvd_sum fun σ _ => Dvd.dvd.mul_left ?_ _
  have hfac : Polynomial.C (PowerSeries.X ^ vertexOrder a b H) ∣
      ((1 - intAdjacency a b (H + 1)).submatrix Fin.castSucc j.succAbove) (σ i₀) i₀ := by
    rw [Matrix.submatrix_apply, hi₀]
    exact C_pow_dvd_apply_last a b H (σ i₀)
  rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ i₀)]
  exact hfac.mul_left _

/-- Restricting `I - L_{H+1}` to the vertices `0, …, H` gives back `I - L_H`. -/
theorem submatrix_castSucc_one_sub_intAdjacency (a b H : ℕ) :
    (1 - intAdjacency a b (H + 1)).submatrix Fin.castSucc Fin.castSucc
      = 1 - intAdjacency a b H := by
  ext r c
  have h1 : (1 : Matrix (Fin (H + 2)) (Fin (H + 2)) (Polynomial (PowerSeries ℚ)))
        r.castSucc c.castSucc
      = (1 : Matrix (Fin (H + 1)) (Fin (H + 1)) (Polynomial (PowerSeries ℚ))) r c := by
    simp only [Matrix.one_apply, Fin.castSucc_inj]
  simp only [Matrix.submatrix_apply, Matrix.sub_apply, h1, intAdjacency, Matrix.of_apply,
    Fin.val_castSucc]

/-- The last diagonal entry of `I - L_{H+1}` is `1`: the graph carries no loop. -/
theorem apply_last_last (a b H : ℕ) (ha : 0 < a) (hb : 0 < b) :
    (1 - intAdjacency a b (H + 1)) (Fin.last (H + 1)) (Fin.last (H + 1)) = 1 := by
  simp [Matrix.sub_apply, intAdjacency, ha.ne', hb.ne']

/-- Raising the height bound from `H` to `H + 1` changes `det(I - L_H)` only by a multiple of
`q ^ vertexOrder a b H`. -/
theorem C_pow_dvd_intDet_succ_sub (a b H : ℕ) (ha : 0 < a) (hb : 0 < b) :
    Polynomial.C (PowerSeries.X ^ vertexOrder a b H) ∣ intDet a b (H + 1) - intDet a b H := by
  have heven : Even ((Fin.last (H + 1) : ℕ) + (Fin.last (H + 1) : ℕ)) := ⟨_, rfl⟩
  have hterm : (-1 : Polynomial (PowerSeries ℚ)) ^
        ((Fin.last (H + 1) : ℕ) + (Fin.last (H + 1) : ℕ)) *
        (1 - intAdjacency a b (H + 1)) (Fin.last (H + 1)) (Fin.last (H + 1)) *
        ((1 - intAdjacency a b (H + 1)).submatrix (Fin.last (H + 1)).succAbove
          (Fin.last (H + 1)).succAbove).det = intDet a b H := by
    rw [apply_last_last a b H ha hb, mul_one, Fin.succAbove_last,
      submatrix_castSucc_one_sub_intAdjacency,
      heven.neg_one_pow, one_mul, intDet]
  have hsum := Matrix.det_succ_row (1 - intAdjacency a b (H + 1)) (Fin.last (H + 1))
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (Fin.last (H + 1))), hterm] at hsum
  rw [intDet, hsum, add_sub_cancel_left]
  refine Finset.dvd_sum fun j hj => ?_
  have hj' : j ≠ Fin.last (H + 1) := (Finset.mem_erase.1 hj).1
  rw [Fin.succAbove_last]
  exact (C_pow_dvd_det_submatrix a b H hj').mul_left _

/-- The coefficientwise form of the one-step comparison. -/
theorem X_pow_dvd_coeff_intDet_succ_sub (a b H : ℕ) (ha : 0 < a) (hb : 0 < b) (n : ℕ) :
    PowerSeries.X ^ vertexOrder a b H ∣
      (intDet a b (H + 1)).coeff n - (intDet a b H).coeff n := by
  obtain ⟨Q, hQ⟩ := C_pow_dvd_intDet_succ_sub a b H ha hb
  refine ⟨Q.coeff n, ?_⟩
  rw [← Polynomial.coeff_sub, hQ, Polynomial.coeff_C_mul]

/-- Raising the height bound past `H` changes the `s`-coefficients of the determinant only by
multiples of `q ^ vertexOrder a b H`. -/
theorem X_pow_dvd_coeff_intDet_sub (a b : ℕ) (ha : 0 < a) (hb : 0 < b) (n : ℕ) {H H' : ℕ}
    (h : H ≤ H') :
    PowerSeries.X ^ vertexOrder a b H ∣
      (intDet a b H').coeff n - (intDet a b H).coeff n := by
  induction H', h using Nat.le_induction with
  | base => simp
  | succ K hK ih =>
    have hstep : PowerSeries.X ^ vertexOrder a b H ∣
        (intDet a b (K + 1)).coeff n - (intDet a b K).coeff n :=
      (pow_dvd_pow _ (vertexOrder_le a b hK)).trans
        (X_pow_dvd_coeff_intDet_succ_sub a b K ha hb n)
    have hrw : (intDet a b (K + 1)).coeff n - (intDet a b H).coeff n
        = ((intDet a b (K + 1)).coeff n - (intDet a b K).coeff n)
          + ((intDet a b K).coeff n - (intDet a b H).coeff n) := by ring
    rw [hrw]
    exact dvd_add hstep ih

/-! ### The limit -/

/-- The stabilised `q`-series: its `q^m`-coefficient is the common value, over all large height
bounds, of the `q^m`-coefficient of the `s^n`-coefficient of `det(I - L_H)`. -/
noncomputable def limCoeff (a b n : ℕ) : PowerSeries ℚ :=
  PowerSeries.mk fun m => PowerSeries.coeff m ((intDet a b (a * (m + 1) + b)).coeff n)

/-- Each `q`-coefficient of the `s^n`-coefficient of `det(I - L_H)` is independent of the height
bound once `H ≥ a(m+1) + b`. -/
theorem coeff_limCoeff (a b n m : ℕ) (ha : 0 < a) (hb : 0 < b) {H : ℕ}
    (hH : a * (m + 1) + b ≤ H) :
    PowerSeries.coeff m (limCoeff a b n) = PowerSeries.coeff m ((intDet a b H).coeff n) := by
  have hlt : m < vertexOrder a b (a * (m + 1) + b) := by
    have he : a * (m + 1) + b + 1 - b = a * (m + 1) + 1 := by omega
    rw [vertexOrder, he]
    calc m < m + 1 := Nat.lt_succ_self m
      _ = a * (m + 1) / a := (Nat.mul_div_cancel_left _ ha).symm
      _ ≤ (a * (m + 1) + 1) / a := Nat.div_le_div_right (Nat.le_succ _)
  have h0 := PowerSeries.X_pow_dvd_iff.1 (X_pow_dvd_coeff_intDet_sub a b ha hb n hH) m hlt
  rw [map_sub, sub_eq_zero] at h0
  rw [limCoeff, PowerSeries.coeff_mk]
  exact h0.symm

/-- The `s^n`-coefficient of `det(I - L_H)` agrees with its limit to order `D` in `q`, once the
height bound satisfies `H ≥ a(D+1) + b`. -/
theorem X_pow_dvd_coeff_intDet_sub_limCoeff (a b n D : ℕ) (ha : 0 < a) (hb : 0 < b) {H : ℕ}
    (hH : a * (D + 1) + b ≤ H) :
    PowerSeries.X ^ D ∣ (intDet a b H).coeff n - limCoeff a b n := by
  rw [PowerSeries.X_pow_dvd_iff]
  intro m hm
  have hm' : a * (m + 1) + b ≤ H := by
    have hmul : a * (m + 1) ≤ a * (D + 1) := Nat.mul_le_mul_left a (by omega)
    omega
  rw [map_sub, coeff_limCoeff a b n m ha hb hm', sub_self]

/-- Any nonzero element of `ℤᵐ⁰` dominates `exp (-D)` for some natural number `D`. -/
theorem exists_exp_neg_lt {g : WithZero (Multiplicative ℤ)} (hg : g ≠ 0) :
    ∃ D : ℕ, WithZero.exp (-(D : ℤ)) < g := by
  obtain ⟨c, rfl⟩ : ∃ c : ℤ, g = WithZero.exp c := ⟨WithZero.log g, (WithZero.exp_log hg).symm⟩
  refine ⟨(1 - c).toNat, ?_⟩
  rw [WithZero.exp_lt_exp]
  omega

/-- A sequence of `q`-Laurent series converges as soon as, for every `D`, the valuation of its
difference from the candidate limit is eventually at most `exp (-D)`. -/
theorem tendsto_of_valuation_sub_le {f : ℕ → LaurentSeries ℚ} {L : LaurentSeries ℚ}
    (h : ∀ D : ℕ, ∀ᶠ H in Filter.atTop, Valued.v (f H - L) ≤ WithZero.exp (-(D : ℤ))) :
    Filter.Tendsto f Filter.atTop (nhds L) := by
  rw [Filter.tendsto_def]
  intro s hs
  obtain ⟨γ, hγ⟩ := Valued.mem_nhds.1 hs
  have hne : MonoidWithZeroHom.ValueGroup₀.embedding γ.1 ≠ 0 := by simp
  obtain ⟨D, hD⟩ := exists_exp_neg_lt hne
  filter_upwards [h D] with H hH
  refine hγ ?_
  change Valued.v.restrict (f H - L) < γ.1
  rw [Valuation.restrict_lt_iff_lt_embedding]
  exact lt_of_le_of_lt hH hD

/-- The `z^N`-coefficient of the truncated determinant is within `q^D` of its limit once the height
bound satisfies `H ≥ a(D+1) + b`. -/
theorem valuation_coeff_detTrunc_sub_le (a b N D : ℕ) (ha : 0 < a) (hb : 0 < b) {H : ℕ}
    (hH : a * (D + 1) + b ≤ H) :
    Valued.v (PowerSeries.coeff N (detTrunc a b H) - qOfRat (limCoeff a b ((a + b) * N)))
      ≤ WithZero.exp (-(D : ℤ)) := by
  rw [coeff_detTrunc, qOfRat_apply, qOfRat_apply, ← PowerSeries.coe_sub,
    LaurentSeries.intValuation_le_iff_coeff_lt_eq_zero ℚ]
  exact fun m hm =>
    PowerSeries.X_pow_dvd_iff.1
      (X_pow_dvd_coeff_intDet_sub_limCoeff a b ((a + b) * N) D ha hb hH) m hm

/-- Each `z`-coefficient of the truncated determinant converges `X`-adically in `ℚ((q))`. -/
theorem tendsto_coeff_detTrunc (a b : ℕ) (ha : 0 < a) (hb : 0 < b) (N : ℕ) :
    Filter.Tendsto (fun H => PowerSeries.coeff N (detTrunc a b H)) Filter.atTop
      (nhds (qOfRat (limCoeff a b ((a + b) * N)))) := by
  refine tendsto_of_valuation_sub_le fun D => ?_
  filter_upwards [Filter.eventually_ge_atTop (a * (D + 1) + b)] with H hH
  exact valuation_coeff_detTrunc_sub_le a b N D ha hb hH

/-- The coefficientwise limit of the truncated determinants, assembled from the stabilised
`q`-series in each `z`-degree. -/
noncomputable def detLimit (a b : ℕ) : ZSeries :=
  PowerSeries.mk fun N => qOfRat (limCoeff a b ((a + b) * N))

/-- The truncated determinants converge to `detLimit a b` in `ℚ((q))⟦z⟧`. -/
theorem tendsto_detTrunc_detLimit (a b : ℕ) (ha : 0 < a) (hb : 0 < b) :
    Filter.Tendsto (detTrunc a b) Filter.atTop (nhds (detLimit a b)) := by
  rw [PowerSeries.WithPiTopology.tendsto_iff_coeff_tendsto]
  intro N
  rw [detLimit, PowerSeries.coeff_mk]
  exact tendsto_coeff_detTrunc a b ha hb N

/-- The truncated determinants `det(I - L_H)`, read in `z = s^{a+b}`, converge as `H → ∞`: the
limit is taken coefficientwise in `z` and `X`-adically in the coefficient field `ℚ((q))`, and it is
the series `𝒟(z;q)`. -/
@[hjo "lem_det_limit"]
theorem tendsto_detTrunc (a b : ℕ) (ha : 0 < a) (hb : 0 < b) :
    Filter.Tendsto (detTrunc a b) Filter.atTop (nhds (detSeries a b)) := by
  have h := tendsto_detTrunc_detLimit a b ha hb
  rw [detSeries, h.limUnder_eq]
  exact h

end HJO.DetLimit
