/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.Determinant.Basic
public import HJO.RankGraph
public meta import HJO.Attr

/-! # The transfer matrix of the rank graph and its truncated determinant

Fix `a`, `b`, a height `H` and two marked scalars `s` and `q`. The *transfer matrix* `L_H(s, q)`
is the weighted adjacency matrix of the rank graph `G_H` (`HJO.Determinant.rankGraph`): it is
indexed by the vertices `0, …, H`, and its `(r, r')` entry is the weight `edgeWeight a b s q r r'`
of the edge `r → r'` when `G_H` has one, and `0` otherwise. The *truncated determinant* is
`𝒟_H(s;q) := det(I - L_H(s,q))`. Its Leibniz expansion enumerates the collections of pairwise
vertex-disjoint directed cycles of `G_H`
(`HJO.Determinant.det_one_sub_edgeWeight_eq_sum_collectionWeight`), and its `H → ∞` limit, written
in the variable `z = s^{a+b}`, is the determinant series `𝒟(z;q)`.

## Main definitions

* `HJO.Determinant.transferMatrix a b H s q`: the matrix `L_H(s, q)`.
* `HJO.Determinant.detTruncPoly a b H s q`: the truncated determinant `det(I - L_H(s, q))`.

## Main results

* `HJO.Determinant.transferMatrix_apply_eq_edgeWeight`: on the index type `Fin (H + 1)` the
  adjacency guard of the definition is vacuous, and the entry is `edgeWeight a b s q r r'`.
* `HJO.Determinant.weightedAdjacency_eq_transferMatrix`: the matrix `weightedAdjacency` that
  `detTrunc` and `detSeries` are built from is this one, at `s = X` and `q = C qVar`.
* `HJO.Determinant.detTrunc_eq_coeff_detTruncPoly`: `detTrunc` reads off the coefficients of
  `s^{(a+b)N}` of the truncated determinant at that instance.

## Implementation notes

The entry is written with the case distinction of the paper cited below (the weight of the edge, or
zero if no such edge exists), `if (rankGraph a b H).Adj r r' then edgeWeight a b s q r r' else 0`,
even though `edgeWeight` is already `0` off the two edge families: the guard is what the paper says,
and `transferMatrix_apply_eq_edgeWeight` discharges it once and for all. It is vacuous only because
the index type is `Fin (H + 1)`, which supplies the bounds `r ≤ H` and `r' ≤ H` of `rankGraph`'s
adjacency.

The scalars of the matrix live in any `MonoidWithZero`, as for `edgeWeight`, and those of the
determinant in any `CommRing`. The polynomial ring `ℚ[s, q]` is one instance, and
`Polynomial (LaurentSeries ℚ)`, with `s` the polynomial variable and `q` entering as
`Polynomial.C qVar`, is another; that instance is `weightedAdjacency`, the matrix the determinant
series is built from.

## References

Definitions `HJO.Determinant.transferMatrix` and `HJO.Determinant.detTruncPoly`, using
`HJO.Determinant.edgeWeight`; *Rogers-Ramanujan identities from the geometry of `X^a = Y^b`*,
first paragraph of §7 "Finite determinants, cofactors, and the second equation".
-/

@[expose] public section

namespace HJO.Determinant

section TransferMatrix

variable {R : Type*} [MonoidWithZero R]

/-- The transfer matrix `L_H(s, q)`: the weighted adjacency matrix of the rank graph
`rankGraph a b H`, indexed by its vertices `0, …, H`. Its `(r, r')` entry is
`edgeWeight a b s q r r'`, the weight of the edge `r → r'`, when there is such an edge, and
`0` otherwise. -/
@[hjo "def_transfer_matrix"]
def transferMatrix (a b H : ℕ) (s q : R) : Matrix (Fin (H + 1)) (Fin (H + 1)) R :=
  Matrix.of fun r r' => if (rankGraph a b H).Adj r r' then edgeWeight a b s q r r' else 0

lemma transferMatrix_apply (a b H : ℕ) (s q : R) (r r' : Fin (H + 1)) :
    transferMatrix a b H s q r r' =
      if (rankGraph a b H).Adj r r' then edgeWeight a b s q r r' else 0 :=
  rfl

/-- On the index type `Fin (H + 1)` the guard in the definition of `transferMatrix` is
vacuous: the bounds `r ≤ H` and `r' ≤ H` hold automatically, and `edgeWeight` already
vanishes off the two edge families. -/
@[simp]
lemma transferMatrix_apply_eq_edgeWeight (a b H : ℕ) (s q : R) (r r' : Fin (H + 1)) :
    transferMatrix a b H s q r r' = edgeWeight a b s q r r' := by
  have hr : (r : ℕ) ≤ H := Nat.lt_succ_iff.mp r.isLt
  have hr' : (r' : ℕ) ≤ H := Nat.lt_succ_iff.mp r'.isLt
  rw [transferMatrix_apply]
  split_ifs with h
  · rfl
  · rw [rankGraph_adj] at h
    exact (edgeWeight_eq_zero (fun hup => h ⟨Or.inl hup, hr, hr'⟩)
      (fun hdown => h ⟨Or.inr hdown, hr, hr'⟩)).symm

/-- The entry of `transferMatrix` on an up edge `r → r + b`. -/
lemma transferMatrix_apply_of_up {a b H : ℕ} (s q : R) {r r' : Fin (H + 1)}
    (h : (r' : ℕ) = (r : ℕ) + b) :
    transferMatrix a b H s q r r' = s * q ^ ((r : ℕ) / a) := by
  rw [transferMatrix_apply_eq_edgeWeight, h, edgeWeight_up]

/-- The entry of `transferMatrix` on a down edge `r → r - a`. -/
lemma transferMatrix_apply_of_down {a b H : ℕ} (s q : R) {r r' : Fin (H + 1)}
    (h : (r : ℕ) = (r' : ℕ) + a) :
    transferMatrix a b H s q r r' = s := by
  rw [transferMatrix_apply_eq_edgeWeight, h, edgeWeight_down]

/-- The entry of `transferMatrix` off both edge families. -/
lemma transferMatrix_apply_eq_zero {a b H : ℕ} {s q : R} {r r' : Fin (H + 1)}
    (hup : (r' : ℕ) ≠ (r : ℕ) + b) (hdown : (r : ℕ) ≠ (r' : ℕ) + a) :
    transferMatrix a b H s q r r' = 0 := by
  rw [transferMatrix_apply_eq_edgeWeight]
  exact edgeWeight_eq_zero hup hdown

/-- The matrix that `detTrunc` and `detSeries` are built from is the transfer
matrix, at `s` the polynomial variable and `q` the Laurent variable. -/
lemma weightedAdjacency_eq_transferMatrix (a b H : ℕ) :
    weightedAdjacency a b H =
      transferMatrix a b H (Polynomial.X : Polynomial (LaurentSeries ℚ)) (Polynomial.C qVar) := by
  refine Matrix.ext fun r c => ?_
  rw [transferMatrix_apply_eq_edgeWeight]
  simp only [weightedAdjacency, Matrix.of_apply, edgeWeight, Polynomial.C_pow]
  split_ifs <;> first | rfl | exact mul_comm _ _

end TransferMatrix

/-! ### The truncated determinant -/

section DetTrunc

variable {R : Type*} [CommRing R]

/-- The truncated determinant `𝒟_H(s;q) = det(I - L_H(s,q))`: the determinant of one minus the
transfer matrix of the rank graph `rankGraph a b H`, a polynomial in the two marked scalars
`s` and `q`. -/
@[hjo "def_det_trunc"]
def detTruncPoly (a b H : ℕ) (s q : R) : R :=
  (1 - transferMatrix a b H s q).det

lemma detTruncPoly_eq_det (a b H : ℕ) (s q : R) :
    detTruncPoly a b H s q = (1 - transferMatrix a b H s q).det :=
  rfl

/-- `𝒟_H(0;q) = 1`: every edge weight is divisible by `s`, so at `s = 0` the transfer matrix
vanishes and the determinant is that of the identity. -/
@[simp]
lemma detTruncPoly_zero_left (a b H : ℕ) (q : R) : detTruncPoly a b H 0 q = 1 := by
  have h : transferMatrix a b H (0 : R) q = 0 := by
    refine Matrix.ext fun r r' => ?_
    rw [transferMatrix_apply_eq_edgeWeight, edgeWeight, Matrix.zero_apply]
    split_ifs <;> simp
  rw [detTruncPoly_eq_det, h, sub_zero, Matrix.det_one]

/-- A ring homomorphism carries the truncated determinant over the two marked scalars. -/
lemma map_detTruncPoly {S : Type*} [CommRing S] (f : R →+* S) (a b H : ℕ) (s q : R) :
    f (detTruncPoly a b H s q) = detTruncPoly a b H (f s) (f q) := by
  have h : f.mapMatrix (transferMatrix a b H s q) = transferMatrix a b H (f s) (f q) := by
    refine Matrix.ext fun r r' => ?_
    rw [RingHom.mapMatrix_apply, Matrix.map_apply, transferMatrix_apply_eq_edgeWeight,
      transferMatrix_apply_eq_edgeWeight, edgeWeight, edgeWeight]
    split_ifs <;> simp
  rw [detTruncPoly_eq_det, detTruncPoly_eq_det, RingHom.map_det, map_sub, map_one, h]

/-- A witness: at `a = b = 1` and `H = 2` the rank graph has exactly the two 2-cycles
`0 ↔ 1`, of weight `s^2`, and `1 ↔ 2`, of weight `s^2 q`, and
`𝒟_2(s;q) = 1 - s^2 - s^2 q`. -/
lemma detTruncPoly_one_one_two (s q : R) : detTruncPoly 1 1 2 s q = 1 - s ^ 2 - s ^ 2 * q := by
  rw [detTruncPoly_eq_det, Matrix.det_fin_three]
  simp only [Matrix.sub_apply, Matrix.one_apply, transferMatrix_apply_eq_edgeWeight, edgeWeight,
    Fin.ext_iff]
  norm_num
  ring

/-- The truncation `detTrunc`, whose limit is the determinant series `𝒟(z;q)`, reads off the
coefficients of `s^{(a+b)N}` in the truncated determinant at `s` the polynomial variable and
`q` the Laurent variable. -/
lemma detTrunc_eq_coeff_detTruncPoly (a b H : ℕ) :
    detTrunc a b H = PowerSeries.mk fun N =>
      (detTruncPoly a b H (Polynomial.X : Polynomial (LaurentSeries ℚ))
        (Polynomial.C qVar)).coeff ((a + b) * N) := by
  rw [detTrunc, detTruncPoly_eq_det, ← weightedAdjacency_eq_transferMatrix]

end DetTrunc

end HJO.Determinant
