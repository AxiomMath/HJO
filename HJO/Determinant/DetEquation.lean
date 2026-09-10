/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Mathlib.Topology.UniformSpace.Uniformizable
public import HJO.Determinant.DetCoeff
public import HJO.Main.Uniqueness

/-! # The resolvent of the weighted path graph and the `q`-difference equation

The weighted adjacency matrix `L_H` of the path graph on the vertices `0, …, H` has every entry
divisible by the edge variable `s`, so `1 - L_H` is invertible over the formal power series in
`s`. This file records that divisibility, the invertibility of `1 - L_H` over `ℚ((q))⟦s⟧`, the
agreement of its inverse with the partial geometric sum `∑_{k < m} L_H^k` to order `m` in `s`, the
expansion of a matrix power as a weighted sum over walks, and Cramer's rule at the corner of a
matrix. Together these identify `det(1 - L_H)` times the `(0,0)` entry of that partial geometric
sum, to order `m` in `s`, with the principal minor deleting the vertex `0`. The constant term of
the determinant is computed as well, both before and after the limit in `H`.

Three further ingredients turn that into a `q`-difference equation for the determinant.

* *The vertex shift.* Reading the up-edge weights one vertex further up the path multiplies the
  coefficient of `s^{dN}` of the determinant by `q^N`, where `d = a + b`. Each term of the Leibniz
  expansion is a monomial whose `s`-degree is the number of vertices its permutation moves, and
  those vertices carry a collection of vertex-disjoint cycles occupying `d` of them per cycle, `N`
  of them in each residue class modulo `d`; the shift raises the weight by one for each vertex
  just below a multiple of `d`. Since the restriction of `1 - L_{H+1}` to the vertices
  `1, …, H + 1` is exactly this shift of `1 - L_H`, the coefficient of `s^{dN}` of the principal
  minor deleting the vertex `0` is `q^N` times that of `det(1 - L_H)`.
* *Walks and paths.* The closed walks of length `dN` at the vertex `0` are in bijection with the
  below-diagonal `(aN, bN)`-paths as soon as `H ≥ abN`: a path is recovered from a walk by
  counting its up-edges, a walk from a path by tracking the vertex `bx - ay`, and the weight of a
  walk is `q` to the area of its path. At smaller `H` the walks are only a proper part of the
  paths of height at most `H`, so the identification is available only from that bound on.
* *The equation.* Combining these with Cramer's rule gives `𝒟_{H+1}(z;q) 𝒲_{H+1}(z;q)
  = 𝒟_H(qz;q)`, where `𝒲_H` generates the closed walks; the determinant is supported in
  `s`-degrees divisible by `d`, which is what makes the product of the two series in `z` the
  right regrouping. Letting `H → ∞` and using that each `z`-coefficient of `𝒲_H` is eventually
  the area polynomial yields `𝒟(qz;q) = 𝒜(z;q) 𝒟(z;q)`, hence that `𝒟(-z;q)` solves the common
  equation.
-/

@[expose] public section

open Finset

namespace HJO.DetEquation

open Determinant
open scoped QTheory PowerSeries.WithPiTopology

/-! ### Divisibility by the edge variable -/

/-- If every entry of a square matrix is divisible by `x`, then every entry of its `m`-th power
is divisible by `x ^ m`. -/
theorem pow_apply_dvd {ι : Type*} [Fintype ι] [DecidableEq ι] {S : Type*} [CommRing S] {x : S}
    {M : Matrix ι ι S} (hM : ∀ i j, x ∣ M i j) (m : ℕ) : ∀ i j : ι, x ^ m ∣ (M ^ m) i j := by
  induction m with
  | zero => intro i j; simp only [pow_zero]; exact one_dvd _
  | succ m ih =>
    intro i j
    rw [pow_succ x, pow_succ M, Matrix.mul_apply]
    exact Finset.dvd_sum fun k _ => mul_dvd_mul (ih i k) (hM k j)

/-- Every entry of the weighted adjacency matrix is divisible by the edge variable: each edge of
the graph contributes one factor of it. -/
theorem X_dvd_weightedAdjacency (a b H : ℕ) (r c : Fin (H + 1)) :
    Polynomial.X ∣ weightedAdjacency a b H r c := by
  simp only [weightedAdjacency, Matrix.of_apply]
  split_ifs
  · exact dvd_mul_left _ _
  · exact dvd_rfl
  · exact dvd_zero _

/-! ### Invertibility over the formal series in the edge variable -/

/-- Setting the edge variable to zero collapses `1 - L_H` to the identity matrix. -/
theorem mapMatrix_evalRingHom_zero (a b H : ℕ) :
    (Polynomial.evalRingHom (0 : LaurentSeries ℚ)).mapMatrix (1 - weightedAdjacency a b H) = 1 := by
  have h0 : ∀ r c, Polynomial.evalRingHom (0 : LaurentSeries ℚ) (weightedAdjacency a b H r c)
      = 0 := by
    intro r c
    obtain ⟨p, hp⟩ := X_dvd_weightedAdjacency a b H r c
    rw [hp]
    simp
  ext r c
  simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.sub_apply, map_sub, h0, sub_zero,
    Matrix.one_apply]
  split <;> simp

/-- The determinant of `1 - L_H` has constant term `1` in the edge variable, because only the
empty collection of edges contributes to it. -/
theorem coeff_zero_det_one_sub (a b H : ℕ) :
    (1 - weightedAdjacency a b H).det.coeff 0 = 1 := by
  rw [Polynomial.coeff_zero_eq_eval_zero]
  have h : Polynomial.eval (0 : LaurentSeries ℚ) (1 - weightedAdjacency a b H).det
      = Polynomial.evalRingHom (0 : LaurentSeries ℚ) (1 - weightedAdjacency a b H).det := rfl
  rw [h, RingHom.map_det, mapMatrix_evalRingHom_zero, Matrix.det_one]

/-- The weighted adjacency matrix with its entries read as formal power series in the edge
variable, that is, as elements of `ℚ((q))⟦s⟧`. -/
noncomputable def psAdjacency (a b H : ℕ) :
    Matrix (Fin (H + 1)) (Fin (H + 1)) (PowerSeries (LaurentSeries ℚ)) :=
  (Polynomial.coeToPowerSeries.ringHom (R := LaurentSeries ℚ)).mapMatrix
    (weightedAdjacency a b H)

/-- Reading the entries of `1 - L_H` as formal power series gives `1 - psAdjacency`. -/
theorem mapMatrix_one_sub (a b H : ℕ) :
    (Polynomial.coeToPowerSeries.ringHom (R := LaurentSeries ℚ)).mapMatrix
        (1 - weightedAdjacency a b H) = 1 - psAdjacency a b H := by
  rw [map_sub, map_one, psAdjacency]

/-- Every entry of the adjacency matrix over `ℚ((q))⟦s⟧` is divisible by the edge variable. -/
theorem X_dvd_psAdjacency (a b H : ℕ) (r c : Fin (H + 1)) :
    PowerSeries.X ∣ psAdjacency a b H r c := by
  obtain ⟨p, hp⟩ := X_dvd_weightedAdjacency a b H r c
  refine ⟨Polynomial.coeToPowerSeries.ringHom p, ?_⟩
  rw [psAdjacency, RingHom.mapMatrix_apply, Matrix.map_apply, hp, map_mul,
    Polynomial.coeToPowerSeries.ringHom_apply, Polynomial.coe_X]

/-- Every entry of the `m`-th power of the adjacency matrix over `ℚ((q))⟦s⟧` is divisible by the
`m`-th power of the edge variable. -/
theorem X_pow_dvd_pow_psAdjacency (a b H m : ℕ) (r c : Fin (H + 1)) :
    PowerSeries.X ^ m ∣ (psAdjacency a b H ^ m) r c :=
  pow_apply_dvd (X_dvd_psAdjacency a b H) m r c

/-- The determinant over `ℚ((q))⟦s⟧` is the determinant over `ℚ((q))[s]`, read as a series. -/
theorem det_one_sub_psAdjacency (a b H : ℕ) :
    (1 - psAdjacency a b H).det
      = Polynomial.coeToPowerSeries.ringHom (1 - weightedAdjacency a b H).det := by
  rw [← mapMatrix_one_sub]
  exact (RingHom.map_det _ _).symm

/-- The determinant of `1 - L_H` has constant term `1` as a formal power series in the edge
variable. -/
theorem constantCoeff_det_one_sub_psAdjacency (a b H : ℕ) :
    PowerSeries.constantCoeff (1 - psAdjacency a b H).det = 1 := by
  rw [det_one_sub_psAdjacency, Polynomial.coeToPowerSeries.ringHom_apply,
    ← PowerSeries.coeff_zero_eq_constantCoeff_apply, Polynomial.coeff_coe,
    coeff_zero_det_one_sub]

/-- Over the ring `ℚ((q))⟦s⟧` of formal power series in the edge variable the matrix `1 - L_H`
is invertible, since its determinant has invertible constant term. -/
theorem isUnit_one_sub_psAdjacency (a b H : ℕ) : IsUnit (1 - psAdjacency a b H) := by
  rw [Matrix.isUnit_iff_isUnit_det, PowerSeries.isUnit_iff_constantCoeff,
    constantCoeff_det_one_sub_psAdjacency]
  exact isUnit_one

/-- The inverse of `1 - L_H` over `ℚ((q))⟦s⟧` agrees with the partial geometric sum
`∑_{k < m} L_H^k` to order `m` in the edge variable, so the geometric series is the inverse. -/
theorem X_pow_dvd_inv_sub_geomSum (a b H m : ℕ) (r c : Fin (H + 1)) :
    PowerSeries.X ^ m ∣
      ((1 - psAdjacency a b H)⁻¹ - ∑ k ∈ range m, psAdjacency a b H ^ k) r c := by
  have hdet := (Matrix.isUnit_iff_isUnit_det _).1 (isUnit_one_sub_psAdjacency a b H)
  set A := psAdjacency a b H with hA
  have hinv : (1 - A)⁻¹ * (1 - A) = 1 := Matrix.nonsing_inv_mul _ hdet
  have key : (1 - A)⁻¹ - ∑ k ∈ range m, A ^ k = (1 - A)⁻¹ * A ^ m :=
    calc (1 - A)⁻¹ - ∑ k ∈ range m, A ^ k
        = (1 - A)⁻¹ - (1 - A)⁻¹ * ((1 - A) * ∑ k ∈ range m, A ^ k) := by
          rw [← mul_assoc, hinv, one_mul]
      _ = (1 - A)⁻¹ - (1 - A)⁻¹ * (1 - A ^ m) := by rw [mul_neg_geom_sum]
      _ = (1 - A)⁻¹ * A ^ m := by rw [mul_sub, mul_one, sub_sub_cancel]
  rw [key, Matrix.mul_apply]
  exact Finset.dvd_sum fun j _ =>
    Dvd.dvd.mul_left (hA ▸ X_pow_dvd_pow_psAdjacency a b H m j c) _

/-! ### Matrix powers as weighted sums over walks -/

/-- The weight of the walk `w` of length `n` in the graph whose edge weights are the entries of
`M`: the product of the weights of its steps. -/
def walkWeight {ι : Type*} {S : Type*} [CommRing S] (M : Matrix ι ι S) {n : ℕ}
    (w : Fin (n + 1) → ι) : S :=
  ∏ i : Fin n, M (w i.castSucc) (w i.succ)

/-- Prefixing a walk with one more starting vertex multiplies its weight by the weight of the new
first step. -/
theorem walkWeight_cons {ι : Type*} {S : Type*} [CommRing S] (M : Matrix ι ι S) {n : ℕ} (r : ι)
    (w : Fin (n + 1) → ι) :
    walkWeight M (Fin.cons r w : Fin (n + 2) → ι) = M r (w 0) * walkWeight M w := by
  have h0 : (Fin.cons r w : Fin (n + 2) → ι) (0 : Fin (n + 1)).castSucc = r := by
    rw [Fin.castSucc_zero]
    exact Fin.cons_zero _ _
  have h1 : (Fin.cons r w : Fin (n + 2) → ι) (0 : Fin (n + 1)).succ = w 0 :=
    Fin.cons_succ _ _ _
  rw [walkWeight, Fin.prod_univ_succ, h0, h1, walkWeight]
  congr 1

/-- The `(r, c)` entry of `M ^ n` is the total weight of the length-`n` walks from `r` to `c`. -/
theorem pow_apply_eq_sum_walkWeight {ι : Type*} [Fintype ι] [DecidableEq ι] {S : Type*}
    [CommRing S] (M : Matrix ι ι S) (n : ℕ) : ∀ r c : ι,
    (M ^ n) r c = ∑ w ∈ Finset.univ.filter
      (fun w : Fin (n + 1) → ι => w 0 = r ∧ w (Fin.last n) = c), walkWeight M w := by
  induction n with
  | zero =>
    intro r c
    rw [pow_zero]
    rcases eq_or_ne r c with rfl | h
    · have hset : Finset.univ.filter (fun w : Fin 1 → ι => w 0 = r ∧ w (Fin.last 0) = r)
          = {fun _ => r} := by
        ext w
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton,
          Fin.last_zero, and_self]
        exact ⟨fun hw => funext fun i => by rw [Subsingleton.elim i 0]; exact hw,
          fun hw => by rw [hw]⟩
      rw [hset, Finset.sum_singleton, Matrix.one_apply_eq]
      simp [walkWeight]
    · have hset : Finset.univ.filter (fun w : Fin 1 → ι => w 0 = r ∧ w (Fin.last 0) = c)
          = ∅ := by
        ext w
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false,
          Fin.last_zero, not_and]
        exact fun h1 h2 => h (h1.symm.trans h2)
      rw [hset, Finset.sum_empty, Matrix.one_apply_ne h]
  | succ n ih =>
    intro r c
    have hcons : Finset.univ.filter
          (fun w : Fin (n + 2) → ι => w 0 = r ∧ w (Fin.last (n + 1)) = c)
        = (Finset.univ.filter (fun w : Fin (n + 1) → ι => w (Fin.last n) = c)).image
            (Fin.cons r) := by
      ext w
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
      constructor
      · rintro ⟨h0, hl⟩
        refine ⟨Fin.tail w, ?_, ?_⟩
        · change w (Fin.last n).succ = c
          rw [Fin.succ_last]
          exact hl
        · rw [← h0]
          exact Fin.cons_self_tail w
      · rintro ⟨v, hv, rfl⟩
        refine ⟨Fin.cons_zero _ _, ?_⟩
        rw [← Fin.succ_last, Fin.cons_succ]
        exact hv
    rw [hcons, Finset.sum_image fun x _ y _ hxy => by
      simpa only [Fin.tail_cons] using congrArg Fin.tail hxy]
    simp only [walkWeight_cons]
    rw [pow_succ' M, Matrix.mul_apply]
    rw [← Finset.sum_fiberwise (Finset.univ.filter
      (fun w : Fin (n + 1) → ι => w (Fin.last n) = c)) (fun w => w 0)
      (fun w => M r (w 0) * walkWeight M w)]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [ih j c, Finset.mul_sum, Finset.filter_filter]
    refine Finset.sum_congr (Finset.filter_congr fun w _ => and_comm) fun w hw => ?_
    rw [Finset.mem_filter] at hw
    rw [hw.2.2]

/-! ### Cramer's rule at the corner -/

/-- Cramer's rule at the corner: the `(0,0)` entry of the inverse of an invertible matrix,
cleared of its denominator, is the principal minor deleting the first row and column. -/
theorem det_mul_inv_apply_zero_zero {n : ℕ} {S : Type*} [CommRing S]
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) S) (hA : IsUnit A.det) :
    A.det * A⁻¹ 0 0 = (A.submatrix Fin.succ Fin.succ).det := by
  rw [Matrix.inv_def, Matrix.smul_apply, smul_eq_mul, ← mul_assoc,
    Ring.mul_inverse_cancel _ hA, one_mul, Matrix.adjugate_fin_succ_eq_det_submatrix]
  simp

/-- Cramer's rule for the resolvent of the weighted path graph: the `(0,0)` entry of
`(1 - L_H)⁻¹`, multiplied by `det(1 - L_H)`, is the principal minor that deletes the vertex `0`.
Both sides live in `ℚ((q))⟦s⟧`, where `1 - L_H` is invertible. -/
theorem det_mul_inv_apply_zero_zero_one_sub (a b H : ℕ) :
    (1 - psAdjacency a b H).det * (1 - psAdjacency a b H)⁻¹ 0 0
      = ((1 - psAdjacency a b H).submatrix Fin.succ Fin.succ).det :=
  det_mul_inv_apply_zero_zero _
    ((Matrix.isUnit_iff_isUnit_det _).1 (isUnit_one_sub_psAdjacency a b H))

/-- The total weight of the closed walks at the vertex `0` of length less than `m`, multiplied by
`det(1 - L_H)`, agrees to order `m` in the edge variable with the principal minor of `1 - L_H`
that deletes the vertex `0`. -/
theorem X_pow_dvd_det_mul_geomSum_sub_minor (a b H m : ℕ) :
    PowerSeries.X ^ m ∣
      (1 - psAdjacency a b H).det * (∑ k ∈ range m, psAdjacency a b H ^ k) 0 0
        - ((1 - psAdjacency a b H).submatrix Fin.succ Fin.succ).det := by
  rw [← det_mul_inv_apply_zero_zero_one_sub, ← mul_sub]
  refine Dvd.dvd.mul_left ?_ _
  rw [← neg_sub, dvd_neg, ← Matrix.sub_apply]
  exact X_pow_dvd_inv_sub_geomSum a b H m 0 0

/-! ### The constant term of the determinant series -/

/-- The `z`-coefficient of order `0` of `𝒟_H(z;q)` is `1`. -/
theorem coeff_zero_detTrunc (a b H : ℕ) : PowerSeries.coeff 0 (detTrunc a b H) = 1 := by
  rw [detTrunc, PowerSeries.coeff_mk, mul_zero, coeff_zero_det_one_sub]

/-- Rescaling the variable `z` does not change the constant term. -/
theorem constantCoeff_rescale (u : LaurentSeries ℚ) (F : ZSeries) :
    PowerSeries.constantCoeff (PowerSeries.rescale u F) = PowerSeries.constantCoeff F := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_rescale, pow_zero,
    one_mul, PowerSeries.coeff_zero_eq_constantCoeff_apply]

/-- `𝒟(0;q) = 1`, given that the coefficientwise limit defining `𝒟` exists. -/
theorem constantCoeff_detSeries (a b : ℕ) {D : ZSeries}
    (hD : Filter.Tendsto (detTrunc a b) Filter.atTop (nhds D)) :
    PowerSeries.constantCoeff (detSeries a b) = 1 := by
  have hD' := hD
  rw [PowerSeries.WithPiTopology.tendsto_iff_coeff_tendsto] at hD'
  have h0 := hD' 0
  simp only [coeff_zero_detTrunc] at h0
  rw [detSeries, hD.limUnder_eq, ← PowerSeries.coeff_zero_eq_constantCoeff_apply]
  exact (tendsto_const_nhds_iff.1 h0).symm

/-- The normalisation requirement of the common equation holds for `𝒟(-z;q)`, given that the
coefficientwise limit defining `𝒟` exists. -/
theorem constantCoeff_rescale_neg_one_detSeries (a b : ℕ) {D : ZSeries}
    (hD : Filter.Tendsto (detTrunc a b) Filter.atTop (nhds D)) :
    PowerSeries.constantCoeff (PowerSeries.rescale (-1) (detSeries a b)) = 1 := by
  rw [constantCoeff_rescale, constantCoeff_detSeries a b hD]

/-! ### The vertex shift -/

/-- `L_H` with every up-edge weight read `k` vertices further up the path: the entry from `r` to
`r + b` carries `q^{⌊(r+k)/a⌋}` instead of `q^{⌊r/a⌋}`. -/
noncomputable def shiftedAdjacency (a b H k : ℕ) :
    Matrix (Fin (H + 1)) (Fin (H + 1)) (Polynomial (LaurentSeries ℚ)) :=
  .of fun r c =>
    if (c : ℕ) = (r : ℕ) + b then Polynomial.C (qVar ^ (((r : ℕ) + k) / a)) * Polynomial.X
    else if (r : ℕ) = (c : ℕ) + a then Polynomial.X else 0

/-- The matrix `1 - L_H` with the up-edge weights read `k` vertices further up the path. -/
noncomputable def shiftedOneSub (a b H k : ℕ) :
    Matrix (Fin (H + 1)) (Fin (H + 1)) (Polynomial (LaurentSeries ℚ)) :=
  1 - shiftedAdjacency a b H k

/-- Without a shift the matrix is `1 - L_H`. -/
theorem shiftedOneSub_zero (a b H : ℕ) : shiftedOneSub a b H 0 = 1 - weightedAdjacency a b H := by
  rw [shiftedOneSub, sub_right_inj]
  ext r c
  simp only [shiftedAdjacency, weightedAdjacency, Matrix.of_apply, add_zero]

/-- Shifting by one vertex describes the restriction of `L_{H+1}` to the vertices
`1, …, H + 1`. -/
theorem shiftedAdjacency_one (a b H : ℕ) :
    shiftedAdjacency a b H 1 = (weightedAdjacency a b (H + 1)).submatrix Fin.succ Fin.succ := by
  ext r c
  have h1 : ((c : ℕ) + 1 = (r : ℕ) + 1 + b) ↔ ((c : ℕ) = (r : ℕ) + b) := by omega
  have h2 : ((r : ℕ) + 1 = (c : ℕ) + 1 + a) ↔ ((r : ℕ) = (c : ℕ) + a) := by omega
  simp only [shiftedAdjacency, weightedAdjacency, Matrix.submatrix_apply, Matrix.of_apply,
    Fin.val_succ, h1, h2]

/-- Shifting by one vertex describes the restriction of `1 - L_{H+1}` to the vertices
`1, …, H + 1`. -/
theorem shiftedOneSub_one (a b H : ℕ) :
    shiftedOneSub a b H 1 = (1 - weightedAdjacency a b (H + 1)).submatrix Fin.succ Fin.succ := by
  rw [shiftedOneSub, shiftedAdjacency_one]
  ext r c
  simp only [Matrix.sub_apply, Matrix.submatrix_apply, Matrix.one_apply, Fin.succ_inj]

/-- The graph carries no loop, so every diagonal entry of the shifted matrix is `1`. -/
theorem shiftedOneSub_apply_self (a b H k : ℕ) (ha : 0 < a) (hb : 0 < b) (r : Fin (H + 1)) :
    shiftedOneSub a b H k r r = 1 := by
  have h1 : ¬ ((r : ℕ) = (r : ℕ) + b) := by omega
  have h2 : ¬ ((r : ℕ) = (r : ℕ) + a) := by omega
  rw [shiftedOneSub, Matrix.sub_apply, Matrix.one_apply_eq, shiftedAdjacency, Matrix.of_apply,
    ite_eq_right h1, ite_eq_right h2, sub_zero]

/-- Off the diagonal the shifted matrix carries the negated edge weight. -/
theorem shiftedOneSub_apply_of_ne (a b H k : ℕ) {r c : Fin (H + 1)} (h : r ≠ c) :
    shiftedOneSub a b H k r c
      = -(if (c : ℕ) = (r : ℕ) + b then Polynomial.C (qVar ^ (((r : ℕ) + k) / a)) * Polynomial.X
          else if (r : ℕ) = (c : ℕ) + a then Polynomial.X else 0) := by
  rw [shiftedOneSub, Matrix.sub_apply, Matrix.one_apply_ne h, shiftedAdjacency, Matrix.of_apply,
    zero_sub]

/-- The permutation `σ` moves every vertex along an edge of the graph: to `v + b` or to
`v - a`. -/
def IsEdgePerm (a b H : ℕ) (σ : Equiv.Perm (Fin (H + 1))) : Prop :=
  ∀ i ∈ σ.support, ((σ i : ℕ) = (i : ℕ) + b) ∨ ((i : ℕ) = (σ i : ℕ) + a)

/-- The `q`-exponent of the Leibniz term of `σ`, with the up-edge weights read `k` vertices
further up the path. -/
def edgeExp (a b H k : ℕ) (σ : Equiv.Perm (Fin (H + 1))) : ℕ :=
  ∑ i ∈ σ.support, if (σ i : ℕ) = (i : ℕ) + b then ((i : ℕ) + k) / a else 0

/-- The Leibniz term of an edge permutation is a monomial: its `s`-degree is the number of
vertices moved and its `q`-exponent is `edgeExp`. -/
theorem prod_shiftedOneSub (a b H k : ℕ) (ha : 0 < a) (hb : 0 < b)
    {σ : Equiv.Perm (Fin (H + 1))} (hσ : IsEdgePerm a b H σ) :
    ∏ i, shiftedOneSub a b H k i (σ i)
      = Polynomial.C ((-1) ^ σ.support.card * qVar ^ edgeExp a b H k σ) *
          Polynomial.X ^ σ.support.card := by
  have hsub : ∏ i ∈ σ.support, shiftedOneSub a b H k i (σ i)
      = ∏ i, shiftedOneSub a b H k i (σ i) := by
    refine Finset.prod_subset (Finset.subset_univ _) fun i _ hi => ?_
    rw [not_not.1 (Equiv.Perm.mem_support.not.1 hi)]
    exact shiftedOneSub_apply_self a b H k ha hb i
  have hterm : ∀ i ∈ σ.support, shiftedOneSub a b H k i (σ i)
      = -(Polynomial.C (qVar ^ (if (σ i : ℕ) = (i : ℕ) + b then ((i : ℕ) + k) / a else 0)) *
          Polynomial.X) := by
    intro i hi
    rw [shiftedOneSub_apply_of_ne a b H k (Equiv.Perm.mem_support.1 hi).symm]
    rcases hσ i hi with hup | hdown
    · rw [ite_eq_left hup, ite_eq_left hup]
    · have hnot : ¬ ((σ i : ℕ) = (i : ℕ) + b) := by omega
      rw [ite_eq_right hnot, ite_eq_right hnot, ite_eq_left hdown, pow_zero, map_one,
        one_mul]
  have hC : (∏ i ∈ σ.support,
        Polynomial.C (qVar ^ (if (σ i : ℕ) = (i : ℕ) + b then ((i : ℕ) + k) / a else 0)))
      = Polynomial.C (qVar ^ edgeExp a b H k σ) := by
    rw [edgeExp, ← Finset.prod_pow_eq_pow_sum, map_prod]
  have hneg : ∀ (n : ℕ) (u : LaurentSeries ℚ),
      Polynomial.C ((-1 : LaurentSeries ℚ) ^ n * u) = (-1) ^ n * Polynomial.C u := by
    intro n u
    rw [map_mul, map_pow, map_neg, map_one]
  rw [← hsub, Finset.prod_congr rfl hterm, Finset.prod_neg, Finset.prod_mul_distrib,
    Finset.prod_const, hC, hneg]
  ring

/-- A permutation moving some vertex along a non-edge contributes nothing. -/
theorem prod_shiftedOneSub_eq_zero (a b H k : ℕ) {σ : Equiv.Perm (Fin (H + 1))}
    (hσ : ¬ IsEdgePerm a b H σ) : ∏ i, shiftedOneSub a b H k i (σ i) = 0 := by
  rw [IsEdgePerm] at hσ
  push Not at hσ
  obtain ⟨i, hi, hup, hdown⟩ := hσ
  refine Finset.prod_eq_zero (Finset.mem_univ i) ?_
  rw [shiftedOneSub_apply_of_ne a b H k (Equiv.Perm.mem_support.1 hi).symm, ite_eq_right hup,
    ite_eq_right hdown, neg_zero]

/-- The successor map on `ℕ` induced by a permutation of the vertices `0, …, H`. -/
def permSucc (H : ℕ) (σ : Equiv.Perm (Fin (H + 1))) (v : ℕ) : ℕ :=
  if h : v < H + 1 then ((σ ⟨v, h⟩ : Fin (H + 1)) : ℕ) else v

/-- On a vertex of the path the induced successor map is `σ`. -/
theorem permSucc_val (H : ℕ) (σ : Equiv.Perm (Fin (H + 1))) (i : Fin (H + 1)) :
    permSucc H σ (i : ℕ) = (σ i : ℕ) := by
  rw [permSucc, dite_eq_left i.isLt, Fin.eta]

/-- The collection of vertex-disjoint cycles traced out by an edge permutation: the occupied
vertices are the ones it moves, and the successor map along the cycles is `σ` itself. -/
def cycleSystemOfPerm (a b H : ℕ) (σ : Equiv.Perm (Fin (H + 1))) (hσ : IsEdgePerm a b H σ) :
    DetCoeff.CycleSystem a b where
  occupied := σ.support.image Fin.val
  succ := permSucc H σ
  step := by
    intro v hv
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 hv
    rw [permSucc_val]
    rcases hσ i hi with h | h
    · exact Or.inl h
    · exact Or.inr ⟨by omega, by omega⟩
  succ_mem := by
    intro v hv
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 hv
    rw [permSucc_val]
    exact Finset.mem_image.2 ⟨σ i, Equiv.Perm.apply_mem_support.2 hi, rfl⟩
  succ_inj := by
    intro v hv w hw h
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 hv
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.1 hw
    rw [permSucc_val, permSucc_val] at h
    exact congrArg Fin.val (σ.injective (Fin.val_injective h))

/-- Translating a collection of vertex-disjoint cycles one vertex up the path. -/
def shiftUp {a b : ℕ} (X : DetCoeff.CycleSystem a b) : DetCoeff.CycleSystem a b where
  occupied := X.occupied.image (· + 1)
  succ := fun v => X.succ (v - 1) + 1
  step := by
    intro v hv
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.1 hv
    rcases X.step u hu with h | ⟨hau, h⟩
    · exact Or.inl (by simp only [Nat.add_sub_cancel, h]; omega)
    · exact Or.inr ⟨by omega, by simp only [Nat.add_sub_cancel, h]; omega⟩
  succ_mem := by
    intro v hv
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.1 hv
    simp only [Nat.add_sub_cancel]
    exact Finset.mem_image.2 ⟨X.succ u, X.succ_mem u hu, rfl⟩
  succ_inj := by
    intro v hv w hw h
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.1 hv
    obtain ⟨u', hu', rfl⟩ := Finset.mem_image.1 hw
    simp only [Nat.add_sub_cancel, Nat.add_right_cancel_iff] at h
    rw [X.succ_inj u hu u' hu' h]

/-- Translating the collection up the path raises its weight by the number of occupied vertices
just below a multiple of `d = a + b`: the potential telescopes on both sides. -/
theorem weightExp_shiftUp {a b : ℕ} (ha : 0 < a) (hb : 0 < b) (X : DetCoeff.CycleSystem a b) :
    (shiftUp X).weightExp = X.weightExp + #{v ∈ X.occupied | (a + b) ∣ v + 1} := by
  rw [(shiftUp X).weightExp_eq_sum_div ha hb, X.weightExp_eq_sum_div ha hb]
  have hocc : (shiftUp X).occupied = X.occupied.image (· + 1) := rfl
  rw [hocc, Finset.sum_image fun x _ y _ h => by omega]
  have hstep : ∀ u ∈ X.occupied, (u + 1) / (a + b)
      = u / (a + b) + if (a + b) ∣ u + 1 then 1 else 0 := fun u _ => Nat.succ_div
  rw [Finset.sum_congr rfl hstep, Finset.sum_add_distrib, Finset.sum_boole, Nat.cast_id]

/-- Of the `dN` occupied vertices of a collection of `N` cycles, exactly `N` sit just below a
multiple of `d = a + b`: each residue class carries the same number of them. -/
theorem card_filter_dvd_succ {a b : ℕ} (X : DetCoeff.CycleSystem a b) (hab : Nat.Coprime a b)
    (hb : 0 < b) {N : ℕ} (hcard : X.occupied.card = (a + b) * N) :
    #{v ∈ X.occupied | (a + b) ∣ v + 1} = N := by
  have hd : 0 < a + b := by omega
  have : NeZero (a + b) := ⟨by omega⟩
  have hfe : {v ∈ X.occupied | (a + b) ∣ v + 1} = X.classOf (-1) := by
    rw [DetCoeff.CycleSystem.classOf]
    refine Finset.filter_congr fun v _ => ?_
    constructor
    · intro h
      have h0 : ((v + 1 : ℕ) : ZMod (a + b)) = 0 := (ZMod.natCast_eq_zero_iff _ _).2 h
      push_cast at h0
      linear_combination h0
    · intro h
      refine (ZMod.natCast_eq_zero_iff _ _).1 ?_
      push_cast [h]
      ring
  have hzero : (X.classOf 0).card = N := by
    have h := X.card_occupied hab hb
    rw [hcard] at h
    exact (Nat.eq_of_mul_eq_mul_left hd h).symm
  rw [hfe, X.card_classOf_eq_card_zero hab hb, hzero]

/-- Reading the up-edge weights one vertex further up the path raises the `q`-exponent of the
Leibniz term of an edge permutation moving `dN` vertices by exactly `N`. -/
theorem edgeExp_one_eq (a b H N : ℕ) (hab : Nat.Coprime a b) (ha : 0 < a) (hb : 0 < b)
    {σ : Equiv.Perm (Fin (H + 1))} (hσ : IsEdgePerm a b H σ)
    (hcard : σ.support.card = (a + b) * N) :
    edgeExp a b H 1 σ = edgeExp a b H 0 σ + N := by
  set X := cycleSystemOfPerm a b H σ hσ with hX
  have hocc : X.occupied = σ.support.image Fin.val := rfl
  have hcard' : X.occupied.card = (a + b) * N := by
    rw [hocc, Finset.card_image_of_injective _ Fin.val_injective, hcard]
  have hinj : ∀ x ∈ σ.support, ∀ y ∈ σ.support, (x : ℕ) = (y : ℕ) → x = y :=
    fun x _ y _ h => Fin.val_injective h
  have hinj1 : ∀ x ∈ σ.support, ∀ y ∈ σ.support,
      ((fun v => v + 1) ∘ Fin.val) x = ((fun v => v + 1) ∘ Fin.val) y → x = y := by
    intro x hx y hy h
    simp only [Function.comp_apply] at h
    exact hinj x hx y hy (by omega)
  have hsucc : ∀ v : ℕ, X.succ v = permSucc H σ v := fun _ => rfl
  have hsucc1 : ∀ v : ℕ, (shiftUp X).succ v = permSucc H σ (v - 1) + 1 := fun _ => rfl
  have h0 : X.weightExp = edgeExp a b H 0 σ := by
    rw [DetCoeff.CycleSystem.weightExp, hocc, Finset.sum_image hinj, edgeExp]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hsucc, permSucc_val, add_zero]
  have h1 : (shiftUp X).weightExp = edgeExp a b H 1 σ := by
    have hocc1 : (shiftUp X).occupied = X.occupied.image (· + 1) := rfl
    rw [DetCoeff.CycleSystem.weightExp, hocc1, hocc, Finset.image_image,
      Finset.sum_image hinj1, edgeExp]
    refine Finset.sum_congr rfl fun i _ => ?_
    have hs : (shiftUp X).succ ((i : ℕ) + 1) = (σ i : ℕ) + 1 := by
      rw [hsucc1, Nat.add_sub_cancel, permSucc_val]
    have hcond : ((shiftUp X).succ ((i : ℕ) + 1) = (i : ℕ) + 1 + b)
        ↔ ((σ i : ℕ) = (i : ℕ) + b) := by
      rw [hs]; omega
    simp only [Function.comp_apply, hcond]
  rw [← h0, ← h1, weightExp_shiftUp ha hb X, card_filter_dvd_succ X hab hb hcard']

/-- Reading the up-edge weights one vertex further up the path multiplies the `s^{dN}`
coefficient of a Leibniz term by `q^N`. -/
theorem coeff_prod_shiftedOneSub (a b H N : ℕ) (hab : Nat.Coprime a b) (ha : 0 < a) (hb : 0 < b)
    (σ : Equiv.Perm (Fin (H + 1))) :
    (∏ i, shiftedOneSub a b H 1 i (σ i)).coeff ((a + b) * N)
      = qVar ^ N * (∏ i, shiftedOneSub a b H 0 i (σ i)).coeff ((a + b) * N) := by
  by_cases hσ : IsEdgePerm a b H σ
  · rw [prod_shiftedOneSub a b H 1 ha hb hσ, prod_shiftedOneSub a b H 0 ha hb hσ,
      Polynomial.coeff_C_mul, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow]
    by_cases hc : (a + b) * N = σ.support.card
    · rw [ite_eq_left hc, edgeExp_one_eq a b H N hab ha hb hσ hc.symm, pow_add]
      ring
    · rw [ite_eq_right hc, mul_zero, mul_zero, mul_zero]
  · rw [prod_shiftedOneSub_eq_zero a b H 1 hσ, prod_shiftedOneSub_eq_zero a b H 0 hσ,
      Polynomial.coeff_zero, mul_zero]

/-- The Leibniz expansion of a determinant, with the permutation acting on the columns. -/
theorem det_eq_sum_perm {n : ℕ} (M : Matrix (Fin n) (Fin n) (Polynomial (LaurentSeries ℚ))) :
    M.det = ∑ σ : Equiv.Perm (Fin n),
      Polynomial.C ((Equiv.Perm.sign σ : ℤ) : LaurentSeries ℚ) * ∏ i, M i (σ i) := by
  rw [← Matrix.det_transpose M, Matrix.det_apply']
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [Polynomial.C_eq_intCast]
  simp only [Matrix.transpose_apply]

/-- Reading the up-edge weights one vertex further up the path multiplies the `s^{dN}`
coefficient of the determinant by `q^N`. -/
theorem coeff_det_shiftedOneSub (a b H N : ℕ) (hab : Nat.Coprime a b) (ha : 0 < a) (hb : 0 < b) :
    (shiftedOneSub a b H 1).det.coeff ((a + b) * N)
      = qVar ^ N * (shiftedOneSub a b H 0).det.coeff ((a + b) * N) := by
  rw [det_eq_sum_perm, det_eq_sum_perm, Polynomial.finsetSum_coeff, Polynomial.finsetSum_coeff,
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [Polynomial.coeff_C_mul, Polynomial.coeff_C_mul,
    coeff_prod_shiftedOneSub a b H N hab ha hb σ]
  ring

/-- `𝒟_H(qz;q)`, read off the principal minor of `1 - L_{H+1}` that deletes the vertex `0`: the
minor's coefficient of `s^{dN}` is `q^N` times that of `det(1 - L_H)`, because translating the
cycles one vertex up the path multiplies the weight of each of the `N` cycles by `q`. -/
theorem coeff_det_submatrix_succ (a b H N : ℕ) (hab : Nat.Coprime a b) (ha : 0 < a) (hb : 0 < b) :
    ((1 - weightedAdjacency a b (H + 1)).submatrix Fin.succ Fin.succ).det.coeff ((a + b) * N)
      = qVar ^ N * (1 - weightedAdjacency a b H).det.coeff ((a + b) * N) := by
  rw [← shiftedOneSub_one, ← shiftedOneSub_zero, coeff_det_shiftedOneSub a b H N hab ha hb]

/-! ### The generating series of the closed walks -/

/-- The `q`-weights of the edges of the path graph on `0, …, H`, with the edge variable dropped:
the entry from `r` to `r + b` is `q^{⌊r/a⌋}` and the entry from `r` to `r - a` is `1`. -/
noncomputable def constAdjacency (a b H : ℕ) :
    Matrix (Fin (H + 1)) (Fin (H + 1)) (LaurentSeries ℚ) :=
  .of fun r c =>
    if (c : ℕ) = (r : ℕ) + b then qVar ^ ((r : ℕ) / a)
    else if (r : ℕ) = (c : ℕ) + a then 1 else 0

/-- `L_H` is the edge variable times the matrix of `q`-weights: every edge carries exactly one
factor of `s`. -/
theorem weightedAdjacency_eq_smul (a b H : ℕ) :
    weightedAdjacency a b H = (Polynomial.X : Polynomial (LaurentSeries ℚ)) •
      (constAdjacency a b H).map (Polynomial.C (R := LaurentSeries ℚ)) := by
  ext r c
  simp only [weightedAdjacency, constAdjacency, Matrix.of_apply, Matrix.smul_apply,
    Matrix.map_apply, smul_eq_mul]
  split_ifs
  · rw [map_pow, mul_comm]
  · rw [map_one, mul_one]
  · rw [map_zero, mul_zero]

/-- Every entry of `L_H ^ k` is `s^k` times a weight in `q`. -/
theorem pow_weightedAdjacency_eq_smul (a b H k : ℕ) :
    weightedAdjacency a b H ^ k
      = (Polynomial.X : Polynomial (LaurentSeries ℚ)) ^ k •
        ((constAdjacency a b H ^ k).map (Polynomial.C (R := LaurentSeries ℚ))) := by
  rw [weightedAdjacency_eq_smul, smul_pow, Matrix.map_pow]

/-- The `(0,0)` entry of `L_H ^ k` is the monomial `s^k` times the weighted count of the closed
walks of length `k` at the vertex `0`. -/
theorem coeff_pow_weightedAdjacency_apply (a b H k i : ℕ) :
    ((weightedAdjacency a b H ^ k) 0 0).coeff i
      = if i = k then (constAdjacency a b H ^ k) 0 0 else 0 := by
  rw [pow_weightedAdjacency_eq_smul, Matrix.smul_apply, Matrix.map_apply, smul_eq_mul, mul_comm,
    Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, mul_ite, mul_one, mul_zero]

/-- The `s^i` coefficient of the `(0,0)` entry of a partial geometric sum in `L_H` is the weighted
count of the closed walks of length `i` at the vertex `0`. -/
theorem coeff_geomSum_apply_zero_zero (a b H m i : ℕ) (hi : i < m) :
    ((∑ k ∈ range m, weightedAdjacency a b H ^ k) 0 0).coeff i
      = (constAdjacency a b H ^ i) 0 0 := by
  rw [Matrix.sum_apply, Polynomial.finsetSum_coeff]
  refine (Finset.sum_eq_single_of_mem i (Finset.mem_range.2 hi) ?_).trans ?_
  · intro k _ hk
    rw [coeff_pow_weightedAdjacency_apply, ite_eq_right (Ne.symm hk)]
  · rw [coeff_pow_weightedAdjacency_apply, ite_eq_left rfl]

/-- `𝒲_H(z;q)`, the generating series of the closed walks at the vertex `0` in the graph on
`0, …, H`: the coefficient of `z^N` is the total `q`-weight of those of length `dN`. -/
noncomputable def walkTrunc (a b H : ℕ) : ZSeries :=
  PowerSeries.mk fun N => (constAdjacency a b H ^ ((a + b) * N)) 0 0

/-! ### The determinant is graded by the number of cycles -/

/-- An edge permutation moves a multiple of `d = a + b` vertices: each of its cycles occupies `d`
of them. -/
theorem dvd_card_support_of_isEdgePerm (a b H : ℕ) (hab : Nat.Coprime a b) (hb : 0 < b)
    {σ : Equiv.Perm (Fin (H + 1))} (hσ : IsEdgePerm a b H σ) : (a + b) ∣ σ.support.card := by
  have hX := (cycleSystemOfPerm a b H σ hσ).card_occupied hab hb
  have hocc : (cycleSystemOfPerm a b H σ hσ).occupied = σ.support.image Fin.val := rfl
  rw [hocc, Finset.card_image_of_injective _ Fin.val_injective] at hX
  exact Dvd.intro _ hX.symm

/-- The determinant of `1 - L_H` is supported in `s`-degrees divisible by `d = a + b`. -/
theorem coeff_det_one_sub_eq_zero (a b H j : ℕ) (hab : Nat.Coprime a b) (ha : 0 < a) (hb : 0 < b)
    (hj : ¬ (a + b) ∣ j) : (1 - weightedAdjacency a b H).det.coeff j = 0 := by
  rw [← shiftedOneSub_zero, det_eq_sum_perm, Polynomial.finsetSum_coeff]
  refine Finset.sum_eq_zero fun σ _ => ?_
  rw [Polynomial.coeff_C_mul]
  by_cases hσ : IsEdgePerm a b H σ
  · have hne : ¬ (j = σ.support.card) := fun h =>
      hj (h ▸ dvd_card_support_of_isEdgePerm a b H hab hb hσ)
    rw [prod_shiftedOneSub a b H 0 ha hb hσ, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
      ite_eq_right hne, mul_zero, mul_zero]
  · rw [prod_shiftedOneSub_eq_zero a b H 0 hσ, Polynomial.coeff_zero, mul_zero]

/-- The multiples of `d = a + b` below `dN` are exactly the `dM` with `M ≤ N`. -/
theorem filter_dvd_range (d N : ℕ) (hd : 0 < d) :
    {k ∈ range (d * N + 1) | d ∣ k} = (range (N + 1)).image (fun M => d * M) := by
  ext k
  simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_image]
  constructor
  · rintro ⟨hk, M, rfl⟩
    refine ⟨M, ?_, rfl⟩
    have : d * M ≤ d * N := by omega
    exact Nat.lt_succ_of_le (Nat.le_of_mul_le_mul_left this hd)
  · rintro ⟨M, hM, rfl⟩
    refine ⟨?_, Dvd.intro M rfl⟩
    have : d * M ≤ d * N := Nat.mul_le_mul_left d (by omega)
    omega

/-- Multiplying `det(1 - L_H)` by any polynomial convolves their coefficients in degrees divisible
by `d = a + b`, because the determinant vanishes in the other degrees. -/
theorem coeff_det_one_sub_mul (a b H N : ℕ) (hab : Nat.Coprime a b) (ha : 0 < a) (hb : 0 < b)
    (Q : Polynomial (LaurentSeries ℚ)) :
    ((1 - weightedAdjacency a b H).det * Q).coeff ((a + b) * N)
      = ∑ M ∈ range (N + 1), (1 - weightedAdjacency a b H).det.coeff ((a + b) * M) *
          Q.coeff ((a + b) * (N - M)) := by
  have hd : 0 < a + b := by omega
  have hvanish : ∀ k ∈ range ((a + b) * N + 1),
      (1 - weightedAdjacency a b H).det.coeff k * Q.coeff ((a + b) * N - k) ≠ 0 → (a + b) ∣ k := by
    intro k _ hk
    by_contra hdvd
    rw [coeff_det_one_sub_eq_zero a b H k hab ha hb hdvd, zero_mul] at hk
    exact hk rfl
  rw [Polynomial.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,
    ← Finset.sum_filter_of_ne hvanish, filter_dvd_range (a + b) N hd,
    Finset.sum_image fun x _ y _ h => Nat.eq_of_mul_eq_mul_left hd h]
  exact Finset.sum_congr rfl fun M _ => by rw [Nat.mul_sub]

/-! ### The finite form of the equation -/

/-- Two polynomials whose difference is divisible by `s^m` as a formal power series agree in every
degree below `m`. -/
theorem coeff_eq_of_X_pow_dvd_sub {P Q : Polynomial (LaurentSeries ℚ)} {m : ℕ}
    (h : PowerSeries.X ^ m ∣
      (P : PowerSeries (LaurentSeries ℚ)) - (Q : PowerSeries (LaurentSeries ℚ)))
    {i : ℕ} (hi : i < m) : P.coeff i = Q.coeff i := by
  have h0 := PowerSeries.X_pow_dvd_iff.1 h i hi
  rw [map_sub, Polynomial.coeff_coe, Polynomial.coeff_coe, sub_eq_zero] at h0
  exact h0

/-- The `(0,0)` entry of a partial geometric sum over `ℚ((q))⟦s⟧` is the one over `ℚ((q))[s]`,
read as a series. -/
theorem psGeomSum_apply_zero_zero_eq_coe (a b H m : ℕ) :
    (∑ k ∈ range m, psAdjacency a b H ^ k) 0 0
      = (((∑ k ∈ range m, weightedAdjacency a b H ^ k) 0 0 :
          Polynomial (LaurentSeries ℚ)) : PowerSeries (LaurentSeries ℚ)) := by
  have hmap : ∑ k ∈ range m, psAdjacency a b H ^ k
      = (Polynomial.coeToPowerSeries.ringHom (R := LaurentSeries ℚ)).mapMatrix
          (∑ k ∈ range m, weightedAdjacency a b H ^ k) := by
    rw [map_sum]
    exact Finset.sum_congr rfl fun k _ => by rw [psAdjacency, map_pow]
  rw [hmap, RingHom.mapMatrix_apply, Matrix.map_apply,
    Polynomial.coeToPowerSeries.ringHom_apply]

/-- The principal minor deleting the vertex `0` over `ℚ((q))⟦s⟧` is the one over `ℚ((q))[s]`, read
as a series. -/
theorem det_submatrix_psAdjacency_eq_coe (a b H : ℕ) :
    ((1 - psAdjacency a b H).submatrix Fin.succ Fin.succ).det
      = ((((1 - weightedAdjacency a b H).submatrix Fin.succ Fin.succ).det :
          Polynomial (LaurentSeries ℚ)) : PowerSeries (LaurentSeries ℚ)) := by
  rw [← mapMatrix_one_sub, RingHom.mapMatrix_apply, Matrix.submatrix_map,
    ← RingHom.mapMatrix_apply, ← RingHom.map_det, Polynomial.coeToPowerSeries.ringHom_apply]

/-- Over `ℚ((q))[s]`: the partial geometric sum inverts `1 - L_H` at the corner to order `m`, so
`det(1 - L_H)` times its `(0,0)` entry agrees with the principal minor deleting the vertex `0` in
every `s`-degree below `m`. -/
theorem coeff_det_mul_geomSum_eq (a b H m i : ℕ) (hi : i < m) :
    ((1 - weightedAdjacency a b H).det *
        (∑ k ∈ range m, weightedAdjacency a b H ^ k) 0 0).coeff i
      = ((1 - weightedAdjacency a b H).submatrix Fin.succ Fin.succ).det.coeff i := by
  refine coeff_eq_of_X_pow_dvd_sub ?_ hi
  have h := X_pow_dvd_det_mul_geomSum_sub_minor a b H m
  rw [det_one_sub_psAdjacency, psGeomSum_apply_zero_zero_eq_coe,
    det_submatrix_psAdjacency_eq_coe, Polynomial.coeToPowerSeries.ringHom_apply,
    ← Polynomial.coe_mul] at h
  exact h

/-- The finite form of the equation: `𝒟_{H+1}(z;q)` times the generating series of the closed
walks at the vertex `0` in the graph on `0, …, H+1` is `𝒟_H(qz;q)`. -/
theorem detTrunc_mul_walkTrunc (a b H : ℕ) (hab : Nat.Coprime a b) (ha : 0 < a) (hb : 0 < b) :
    detTrunc a b (H + 1) * walkTrunc a b (H + 1)
      = PowerSeries.rescale qVar (detTrunc a b H) := by
  refine PowerSeries.ext fun N => ?_
  have hd : 0 < a + b := by omega
  have hlt : ∀ M ∈ range (N + 1), (a + b) * (N - M) < (a + b) * N + 1 := by
    intro M _
    have : (a + b) * (N - M) ≤ (a + b) * N := Nat.mul_le_mul_left _ (Nat.sub_le _ _)
    omega
  have hRHS : PowerSeries.coeff N (PowerSeries.rescale qVar (detTrunc a b H))
      = ((1 - weightedAdjacency a b (H + 1)).det *
          (∑ k ∈ range ((a + b) * N + 1), weightedAdjacency a b (H + 1) ^ k) 0 0).coeff
            ((a + b) * N) := by
    rw [PowerSeries.coeff_rescale, detTrunc, PowerSeries.coeff_mk,
      ← coeff_det_submatrix_succ a b H N hab ha hb,
      coeff_det_mul_geomSum_eq a b (H + 1) ((a + b) * N + 1) ((a + b) * N) (Nat.lt_succ_self _)]
  rw [hRHS, coeff_det_one_sub_mul a b (H + 1) N hab ha hb, PowerSeries.coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  refine Finset.sum_congr rfl fun M hM => ?_
  rw [detTrunc, PowerSeries.coeff_mk, walkTrunc, PowerSeries.coeff_mk,
    coeff_geomSum_apply_zero_zero a b (H + 1) ((a + b) * N + 1) ((a + b) * (N - M)) (hlt M hM)]

/-! ### The walk traced out by a below-diagonal path -/

/-- The height of a below-diagonal path is monotone up to its last coordinate. -/
theorem ht_mono {a b N : ℕ} {y : Paths.Heights a b N} (hy : Paths.IsBelowDiagonal y) {r r' : ℕ}
    (h : r ≤ r') (hr' : r' ≤ a * N) : Paths.ht y r ≤ Paths.ht y r' := by
  induction r', h using Nat.le_induction with
  | base => exact le_rfl
  | succ K hK ih => exact (ih (by omega)).trans (hy.2.2.1 K (by omega))

/-- The time at which the path `y` takes the horizontal step out of the column `r`: the `r`
horizontal steps and the `y_r` vertical steps before it. -/
def stepTime {a b N : ℕ} (y : Paths.Heights a b N) (r : ℕ) : ℕ := r + Paths.ht y r

/-- The horizontal steps of a below-diagonal path happen at strictly increasing times. -/
theorem stepTime_lt_stepTime {a b N : ℕ} {y : Paths.Heights a b N}
    (hy : Paths.IsBelowDiagonal y) {r r' : ℕ} (h : r < r') (hr' : r' ≤ a * N) :
    stepTime y r < stepTime y r' := by
  have := ht_mono hy (Nat.le_of_lt h) hr'
  rw [stepTime, stepTime]
  omega

/-- The number of horizontal steps of the path `y` taken strictly before the time `t`. -/
def eCount {a b N : ℕ} (y : Paths.Heights a b N) (t : ℕ) : ℕ :=
  #{r ∈ range (a * N) | stepTime y r < t}

/-- No horizontal step is taken before time `0`. -/
theorem eCount_zero {a b N : ℕ} (y : Paths.Heights a b N) : eCount y 0 = 0 := by
  rw [eCount, Finset.card_eq_zero]
  exact Finset.filter_false_of_mem fun r _ => by omega

/-- There are at most `aN` horizontal steps. -/
theorem eCount_le {a b N : ℕ} (y : Paths.Heights a b N) (t : ℕ) : eCount y t ≤ a * N :=
  le_trans (Finset.card_filter_le _ _) (le_of_eq (Finset.card_range _))

/-- At most one horizontal step is taken per unit of time. -/
theorem eCount_le_self {a b N : ℕ} (y : Paths.Heights a b N) (t : ℕ) : eCount y t ≤ t := by
  have hsub : {r ∈ range (a * N) | stepTime y r < t} ⊆ range t := by
    intro r hr
    rw [Finset.mem_filter] at hr
    have : r ≤ stepTime y r := by rw [stepTime]; omega
    exact Finset.mem_range.2 (by omega)
  calc eCount y t ≤ #(range t) := Finset.card_le_card hsub
    _ = t := Finset.card_range t

/-- The counting adjunction: at most `r` horizontal steps have been taken by the time `t`
exactly when `t` does not exceed the time of the horizontal step out of the column `r`. -/
theorem eCount_le_iff {a b N : ℕ} {y : Paths.Heights a b N} (hy : Paths.IsBelowDiagonal y)
    {r t : ℕ} (hr : r < a * N) : eCount y t ≤ r ↔ t ≤ stepTime y r := by
  constructor
  · intro hc
    by_contra hlt
    have hsub : range (r + 1) ⊆ {r' ∈ range (a * N) | stepTime y r' < t} := by
      intro r' hr'
      rw [Finset.mem_range] at hr'
      refine Finset.mem_filter.2 ⟨Finset.mem_range.2 (by omega), ?_⟩
      rcases Nat.lt_or_ge r' r with h | h
      · exact lt_of_lt_of_le (stepTime_lt_stepTime hy h (by omega)) (by omega)
      · have heq : r' = r := by omega
        subst heq
        omega
    have hcard := Finset.card_le_card hsub
    rw [Finset.card_range] at hcard
    rw [eCount] at hc
    omega
  · intro ht
    have hsub : {r' ∈ range (a * N) | stepTime y r' < t} ⊆ range r := by
      intro r' hr'
      rw [Finset.mem_filter, Finset.mem_range] at hr'
      refine Finset.mem_range.2 ?_
      by_contra hge
      rcases Nat.lt_or_ge r r' with h | h
      · have := stepTime_lt_stepTime hy h (by omega)
        omega
      · have heq : r' = r := by omega
        subst heq
        omega
    calc eCount y t ≤ #(range r) := Finset.card_le_card hsub
      _ = r := Finset.card_range r

/-- The vertex `b x - a y` of the graph that the path `y` occupies at the time `t`. -/
def walkVertex {a b N : ℕ} (y : Paths.Heights a b N) (t : ℕ) : ℕ :=
  (a + b) * eCount y t - a * t

/-- The time `t` never runs ahead of the vertex count: the walk of a below-diagonal path stays at
a nonnegative vertex. -/
theorem mul_le_mul_eCount {a b N : ℕ} {y : Paths.Heights a b N} (hy : Paths.IsBelowDiagonal y)
    {t : ℕ} (ht : t ≤ (a + b) * N) : a * t ≤ (a + b) * eCount y t := by
  rcases Nat.lt_or_ge (eCount y t) (a * N) with hlt | hge
  · have h1 : t ≤ stepTime y (eCount y t) := (eCount_le_iff hy hlt).1 le_rfl
    have h2 : a * Paths.ht y (eCount y t) ≤ b * eCount y t :=
      hy.2.2.2 _ (le_of_lt hlt)
    rw [stepTime] at h1
    calc a * t ≤ a * (eCount y t + Paths.ht y (eCount y t)) := Nat.mul_le_mul_left a h1
      _ = a * eCount y t + a * Paths.ht y (eCount y t) := by ring
      _ ≤ a * eCount y t + b * eCount y t := by omega
      _ = (a + b) * eCount y t := by ring
  · calc a * t ≤ a * ((a + b) * N) := Nat.mul_le_mul_left a ht
      _ = (a + b) * (a * N) := by ring
      _ ≤ (a + b) * eCount y t := Nat.mul_le_mul_left _ hge

/-- The vertex at the time `t`, written without truncated subtraction. -/
theorem add_walkVertex {a b N : ℕ} {y : Paths.Heights a b N} (hy : Paths.IsBelowDiagonal y)
    {t : ℕ} (ht : t ≤ (a + b) * N) : a * t + walkVertex y t = (a + b) * eCount y t := by
  rw [walkVertex]
  have := mul_le_mul_eCount hy ht
  omega

/-- The walk of a below-diagonal path never rises above `abN`. -/
theorem walkVertex_le {a b N : ℕ} {y : Paths.Heights a b N} (hy : Paths.IsBelowDiagonal y)
    {t : ℕ} (ht : t ≤ (a + b) * N) : walkVertex y t ≤ a * b * N := by
  have h1 := add_walkVertex hy ht
  have h2 : a * eCount y t ≤ a * t := Nat.mul_le_mul_left a (eCount_le_self y t)
  have h3 : b * eCount y t ≤ b * (a * N) := Nat.mul_le_mul_left b (eCount_le y t)
  have h4 : (a + b) * eCount y t = a * eCount y t + b * eCount y t := by ring
  have h5 : b * (a * N) = a * b * N := by ring
  omega

/-- The walk starts at the vertex `0`. -/
theorem walkVertex_zero {a b N : ℕ} (y : Paths.Heights a b N) : walkVertex y 0 = 0 := by
  rw [walkVertex, eCount_zero, mul_zero, mul_zero, Nat.sub_zero]

/-- Every horizontal step is taken before the end of the walk. -/
theorem stepTime_lt {a b N : ℕ} {y : Paths.Heights a b N} (hy : Paths.IsBelowDiagonal y) {r : ℕ}
    (hr : r < a * N) : stepTime y r < (a + b) * N := by
  have h := ht_mono hy (le_of_lt hr) (le_refl (a * N))
  rw [hy.2.1] at h
  have : (a + b) * N = a * N + b * N := by ring
  rw [stepTime]
  omega

/-- All `aN` horizontal steps have been taken by the end of the walk. -/
theorem eCount_length {a b N : ℕ} {y : Paths.Heights a b N} (hy : Paths.IsBelowDiagonal y) :
    eCount y ((a + b) * N) = a * N := by
  refine le_antisymm (eCount_le y _) ?_
  have hsub : range (a * N) ⊆ {r ∈ range (a * N) | stepTime y r < (a + b) * N} := by
    intro r hr
    rw [Finset.mem_range] at hr
    exact Finset.mem_filter.2 ⟨Finset.mem_range.2 hr, stepTime_lt hy hr⟩
  calc a * N = #(range (a * N)) := (Finset.card_range _).symm
    _ ≤ eCount y ((a + b) * N) := Finset.card_le_card hsub

/-- The walk returns to the vertex `0`. -/
theorem walkVertex_length {a b N : ℕ} {y : Paths.Heights a b N} (hy : Paths.IsBelowDiagonal y) :
    walkVertex y ((a + b) * N) = 0 := by
  have h := add_walkVertex hy (le_refl ((a + b) * N))
  rw [eCount_length hy] at h
  have : (a + b) * (a * N) = a * ((a + b) * N) := by ring
  omega

/-- The time `t` is the time of a horizontal step of the path `y`. -/
def IsEStep {a b N : ℕ} (y : Paths.Heights a b N) (t : ℕ) : Prop :=
  ∃ r < a * N, stepTime y r = t

/-- Whether the time `t` is the time of a horizontal step of `y` is decidable: the column it
would leave is bounded by `aN`. -/
instance instDecidableIsEStep {a b N : ℕ} (y : Paths.Heights a b N) (t : ℕ) :
    Decidable (IsEStep y t) := by
  unfold IsEStep; infer_instance

/-- At the time of the horizontal step out of the column `r`, exactly `r` horizontal steps have
been taken. -/
theorem eCount_stepTime {a b N : ℕ} {y : Paths.Heights a b N} (hy : Paths.IsBelowDiagonal y)
    {r : ℕ} (hr : r < a * N) : eCount y (stepTime y r) = r := by
  refine le_antisymm ((eCount_le_iff hy hr).2 le_rfl) ?_
  by_contra hlt
  have hle : eCount y (stepTime y r) ≤ r - 1 := by omega
  have hr1 : r - 1 < a * N := by omega
  have h := (eCount_le_iff hy hr1).1 hle
  have := stepTime_lt_stepTime hy (show r - 1 < r by omega) (le_of_lt hr)
  omega

/-- A horizontal step raises the vertex by `b`. -/
theorem walkVertex_succ_of_isEStep {a b N : ℕ} {y : Paths.Heights a b N}
    (hy : Paths.IsBelowDiagonal y) {t : ℕ} (ht : t < (a + b) * N) (hE : IsEStep y t) :
    walkVertex y (t + 1) = walkVertex y t + b := by
  obtain ⟨r, hr, hrt⟩ := hE
  have h1 : eCount y t = r := by rw [← hrt]; exact eCount_stepTime hy hr
  have h2 : eCount y (t + 1) = r + 1 := by
    refine le_antisymm ?_ ?_
    · rcases Nat.lt_or_ge (r + 1) (a * N) with hlt | hge
      · refine (eCount_le_iff hy hlt).2 ?_
        have := stepTime_lt_stepTime hy (show r < r + 1 by omega) (le_of_lt hlt)
        omega
      · have := eCount_le y (t + 1)
        omega
    · by_contra hlt
      have hle : eCount y (t + 1) ≤ r := by omega
      have := (eCount_le_iff hy hr).1 hle
      omega
  have e1 := add_walkVertex hy (le_of_lt ht)
  have e2 := add_walkVertex hy (show t + 1 ≤ (a + b) * N by omega)
  rw [h1] at e1
  rw [h2] at e2
  have h3 : (a + b) * (r + 1) = (a + b) * r + (a + b) := by ring
  have h4 : a * (t + 1) = a * t + a := by ring
  omega

/-- Every other step lowers the vertex by `a`. -/
theorem walkVertex_succ_of_not_isEStep {a b N : ℕ} {y : Paths.Heights a b N}
    (hy : Paths.IsBelowDiagonal y) {t : ℕ} (ht : t < (a + b) * N) (hE : ¬ IsEStep y t) :
    walkVertex y t = walkVertex y (t + 1) + a := by
  have h2 : eCount y (t + 1) = eCount y t := by
    refine le_antisymm ?_ ?_
    · rcases Nat.lt_or_ge (eCount y t) (a * N) with hlt | hge
      · refine (eCount_le_iff hy hlt).2 ?_
        have hge' : t ≤ stepTime y (eCount y t) := (eCount_le_iff hy hlt).1 le_rfl
        rcases Nat.lt_or_ge t (stepTime y (eCount y t)) with h | h
        · omega
        · exact absurd ⟨eCount y t, hlt, by omega⟩ hE
      · have := eCount_le y (t + 1)
        omega
    · rw [eCount, eCount]
      refine Finset.card_le_card fun r hr => ?_
      rw [Finset.mem_filter] at hr ⊢
      exact ⟨hr.1, by omega⟩
  have e1 := add_walkVertex hy (le_of_lt ht)
  have e2 := add_walkVertex hy (show t + 1 ≤ (a + b) * N by omega)
  rw [h2] at e2
  have h3 : a * (t + 1) = a * t + a := by ring
  omega

/-- The walk in the graph on the vertices `0, …, H` traced out by the path `y`, clamped to those
vertices so as to be defined on every height vector. -/
def pathWalk (a b N H : ℕ) (y : Paths.Heights a b N) : Fin ((a + b) * N + 1) → Fin (H + 1) :=
  fun t => ⟨min (walkVertex y (t : ℕ)) H, Nat.lt_succ_of_le (min_le_right _ _)⟩

/-- For a below-diagonal path and a height bound at least `abN` the clamp is inactive. -/
theorem pathWalk_val (a b N H : ℕ) {y : Paths.Heights a b N} (hy : Paths.IsBelowDiagonal y)
    (hH : a * b * N ≤ H) (t : Fin ((a + b) * N + 1)) :
    ((pathWalk a b N H y t : Fin (H + 1)) : ℕ) = walkVertex y (t : ℕ) :=
  min_eq_left (le_trans (walkVertex_le hy (Nat.lt_succ_iff.1 t.isLt)) hH)

/-- The walk of a path starts at the vertex `0`. -/
theorem pathWalk_zero (a b N H : ℕ) {y : Paths.Heights a b N} (hy : Paths.IsBelowDiagonal y)
    (hH : a * b * N ≤ H) : pathWalk a b N H y 0 = 0 := by
  refine Fin.ext ?_
  rw [pathWalk_val a b N H hy hH, Fin.val_zero, walkVertex_zero, Fin.val_zero]

/-- The walk of a below-diagonal path returns to the vertex `0`. -/
theorem pathWalk_last (a b N H : ℕ) {y : Paths.Heights a b N} (hy : Paths.IsBelowDiagonal y)
    (hH : a * b * N ≤ H) : pathWalk a b N H y (Fin.last ((a + b) * N)) = 0 := by
  refine Fin.ext ?_
  rw [pathWalk_val a b N H hy hH, Fin.val_last, walkVertex_length hy, Fin.val_zero]

/-- Each step of the walk of a below-diagonal path carries the weight of its edge: `q^{⌊v/a⌋}` at
a horizontal step of the path and `1` at a vertical one. -/
theorem constAdjacency_pathWalk (a b N H : ℕ) {y : Paths.Heights a b N}
    (hy : Paths.IsBelowDiagonal y) (ha : 0 < a) (hb : 0 < b) (hH : a * b * N ≤ H)
    (i : Fin ((a + b) * N)) :
    constAdjacency a b H (pathWalk a b N H y i.castSucc) (pathWalk a b N H y i.succ)
      = if IsEStep y (i : ℕ) then qVar ^ (walkVertex y (i : ℕ) / a) else 1 := by
  have hi : (i : ℕ) < (a + b) * N := i.isLt
  have hcast : ((pathWalk a b N H y i.castSucc : Fin (H + 1)) : ℕ) = walkVertex y (i : ℕ) := by
    rw [pathWalk_val a b N H hy hH, Fin.val_castSucc]
  have hsucc : ((pathWalk a b N H y i.succ : Fin (H + 1)) : ℕ) = walkVertex y ((i : ℕ) + 1) := by
    rw [pathWalk_val a b N H hy hH, Fin.val_succ]
  rw [constAdjacency, Matrix.of_apply, hcast, hsucc]
  by_cases hE : IsEStep y (i : ℕ)
  · rw [ite_eq_left hE, ite_eq_left (walkVertex_succ_of_isEStep hy hi hE)]
  · have hdown := walkVertex_succ_of_not_isEStep hy hi hE
    have hne : ¬ (walkVertex y ((i : ℕ) + 1) = walkVertex y (i : ℕ) + b) := by omega
    rw [ite_eq_right hE, ite_eq_right hne, ite_eq_left hdown]

/-- The times of the horizontal steps of a below-diagonal path are exactly the `stepTime y r`. -/
theorem filter_isEStep (a b N : ℕ) {y : Paths.Heights a b N} (hy : Paths.IsBelowDiagonal y) :
    {t ∈ range ((a + b) * N) | IsEStep y t} = (range (a * N)).image (stepTime y) := by
  refine Finset.Subset.antisymm (fun t ht => ?_) (fun t ht => ?_)
  · obtain ⟨-, r, hr, hrt⟩ := Finset.mem_filter.1 ht
    exact Finset.mem_image.2 ⟨r, Finset.mem_range.2 hr, hrt⟩
  · obtain ⟨r, hr, hrt⟩ := Finset.mem_image.1 ht
    rw [Finset.mem_range] at hr
    exact Finset.mem_filter.2 ⟨Finset.mem_range.2 (hrt ▸ stepTime_lt hy hr), r, hr, hrt⟩

/-- At the horizontal step out of the column `r` the walk sits at the vertex `br - a y_r`. -/
theorem add_walkVertex_stepTime (a b N : ℕ) {y : Paths.Heights a b N}
    (hy : Paths.IsBelowDiagonal y) {r : ℕ} (hr : r < a * N) :
    a * Paths.ht y r + walkVertex y (stepTime y r) = b * r := by
  have hle : stepTime y r ≤ (a + b) * N := le_of_lt (stepTime_lt hy hr)
  have h := add_walkVertex hy hle
  rw [eCount_stepTime hy hr] at h
  have h1 : a * stepTime y r = a * r + a * Paths.ht y r := by rw [stepTime]; ring
  have h2 : (a + b) * r = a * r + b * r := by ring
  omega

/-- The same, with the vertex written as a truncated difference. -/
theorem walkVertex_stepTime (a b N : ℕ) {y : Paths.Heights a b N} (hy : Paths.IsBelowDiagonal y)
    {r : ℕ} (hr : r < a * N) :
    walkVertex y (stepTime y r) = b * r - a * Paths.ht y r := by
  have h := add_walkVertex_stepTime a b N hy hr
  omega

/-- The weight of the walk of a below-diagonal path is `q` to its area. -/
theorem walkWeight_pathWalk (a b N H : ℕ) {y : Paths.Heights a b N}
    (hy : Paths.IsBelowDiagonal y) (ha : 0 < a) (hb : 0 < b) (hH : a * b * N ≤ H) :
    walkWeight (constAdjacency a b H) (pathWalk a b N H y) = qVar ^ Paths.area y := by
  have hinj : Set.InjOn (stepTime y) (range (a * N) : Finset ℕ) := by
    intro r hr r' hr' h
    simp only [Finset.coe_range, Set.mem_Iio] at hr hr'
    rcases Nat.lt_trichotomy r r' with hlt | heq | hgt
    · exact absurd h (stepTime_lt_stepTime hy hlt (by omega)).ne
    · exact heq
    · exact absurd h.symm (stepTime_lt_stepTime hy hgt (by omega)).ne
  have hterm : ∀ r ∈ range (a * N),
      walkVertex y (stepTime y r) / a = b * r / a - Paths.ht y r := by
    intro r hr
    rw [Finset.mem_range] at hr
    rw [walkVertex_stepTime a b N hy hr, Nat.sub_mul_div]
  rw [walkWeight,
    Finset.prod_congr rfl fun i _ => constAdjacency_pathWalk a b N H hy ha hb hH i,
    Fin.prod_univ_eq_prod_range
      (fun t => if IsEStep y t then qVar ^ (walkVertex y t / a) else 1) ((a + b) * N),
    ← Finset.prod_filter, filter_isEStep a b N hy, Finset.prod_image hinj,
    Finset.prod_congr rfl fun r hr => congrArg (fun e => qVar ^ e) (hterm r hr),
    Finset.prod_pow_eq_pow_sum, Paths.area]
  rcases Nat.eq_zero_or_pos (a * N) with h0 | h0
  · rw [h0]
    rfl
  · rw [Finset.range_eq_Ico, Finset.sum_eq_sum_Ico_succ_bot h0]
    simp only [Nat.mul_zero, Nat.zero_div, hy.1, Nat.sub_zero, zero_add]

/-! ### The path traced out by a walk -/

/-- The vertex of the walk `w` at the time `t`, read as a natural number. -/
def walkVal {n H : ℕ} (w : Fin (n + 1) → Fin (H + 1)) (t : ℕ) : ℕ :=
  if h : t < n + 1 then ((w ⟨t, h⟩ : Fin (H + 1)) : ℕ) else 0

/-- The vertex at the start of the `i`-th step. -/
theorem walkVal_val_castSucc {n H : ℕ} (w : Fin (n + 1) → Fin (H + 1)) (i : Fin n) :
    ((w i.castSucc : Fin (H + 1)) : ℕ) = walkVal w (i : ℕ) := by
  have h : (⟨(i : ℕ), Nat.lt_succ_of_lt i.isLt⟩ : Fin (n + 1)) = i.castSucc :=
    Fin.ext (by rw [Fin.val_castSucc])
  rw [walkVal, dite_eq_left (Nat.lt_succ_of_lt i.isLt), h]

/-- The vertex at the end of the `i`-th step. -/
theorem walkVal_val_succ {n H : ℕ} (w : Fin (n + 1) → Fin (H + 1)) (i : Fin n) :
    ((w i.succ : Fin (H + 1)) : ℕ) = walkVal w ((i : ℕ) + 1) := by
  have hlt : (i : ℕ) + 1 < n + 1 := by omega
  have h : (⟨(i : ℕ) + 1, hlt⟩ : Fin (n + 1)) = i.succ := Fin.ext (by rw [Fin.val_succ])
  rw [walkVal, dite_eq_left hlt, h]

/-- Every step of the walk `w` is an edge of the graph. -/
def IsWalk (a b : ℕ) {n H : ℕ} (w : Fin (n + 1) → Fin (H + 1)) : Prop :=
  ∀ i : Fin n, ((w i.succ : Fin (H + 1)) : ℕ) = ((w i.castSucc : Fin (H + 1)) : ℕ) + b
    ∨ ((w i.castSucc : Fin (H + 1)) : ℕ) = ((w i.succ : Fin (H + 1)) : ℕ) + a

/-- Whether every step of `w` is an edge of the graph is decidable: there are finitely many
steps, each an equality of natural numbers. -/
instance instDecidableIsWalk (a b : ℕ) {n H : ℕ} (w : Fin (n + 1) → Fin (H + 1)) :
    Decidable (IsWalk a b w) := by
  unfold IsWalk; infer_instance

/-- The step relation of a walk, read at the level of times. -/
theorem isWalk_val {a b n H : ℕ} {w : Fin (n + 1) → Fin (H + 1)} (hw : IsWalk a b w) {t : ℕ}
    (ht : t < n) : walkVal w (t + 1) = walkVal w t + b ∨ walkVal w t = walkVal w (t + 1) + a := by
  have h := hw ⟨t, ht⟩
  rw [walkVal_val_castSucc, walkVal_val_succ] at h
  exact h

/-- A walk with a step that is not an edge of the graph has weight zero. -/
theorem walkWeight_eq_zero_of_not_isWalk (a b H : ℕ) {n : ℕ} {w : Fin (n + 1) → Fin (H + 1)}
    (hw : ¬ IsWalk a b w) : walkWeight (constAdjacency a b H) w = 0 := by
  rw [IsWalk] at hw
  push Not at hw
  obtain ⟨i, h1, h2⟩ := hw
  refine Finset.prod_eq_zero (Finset.mem_univ i) ?_
  rw [constAdjacency, Matrix.of_apply, ite_eq_right h1, ite_eq_right h2]

/-- The number of up-edges taken by the walk `w` before the time `t`. -/
def upCount (a b : ℕ) {n H : ℕ} (w : Fin (n + 1) → Fin (H + 1)) (t : ℕ) : ℕ :=
  (walkVal w t + a * t) / (a + b)

/-- The vertex reached and the time elapsed determine the number of up-edges taken. -/
theorem mul_upCount {a b n H : ℕ} {w : Fin (n + 1) → Fin (H + 1)} (hw : IsWalk a b w)
    (h0 : walkVal w 0 = 0) (hd : 0 < a + b) :
    ∀ t ≤ n, (a + b) * upCount a b w t = walkVal w t + a * t := by
  intro t
  induction t with
  | zero =>
    intro _
    rw [upCount, h0]
    simp
  | succ t ih =>
    intro ht
    have iht := ih (by omega)
    have hexp : a * (t + 1) = a * t + a := by ring
    rcases isWalk_val hw (show t < n by omega) with hup | hdown
    · have key : walkVal w (t + 1) + a * (t + 1) = (a + b) * (upCount a b w t + 1) := by
        have hr : (a + b) * (upCount a b w t + 1) = (a + b) * upCount a b w t + (a + b) := by ring
        omega
      have h2 : upCount a b w (t + 1) = upCount a b w t + 1 := by
        rw [upCount, key, Nat.mul_div_cancel_left _ hd]
      rw [h2]
      exact key.symm
    · have key : walkVal w (t + 1) + a * (t + 1) = (a + b) * upCount a b w t := by omega
      have h2 : upCount a b w (t + 1) = upCount a b w t := by
        rw [upCount, key, Nat.mul_div_cancel_left _ hd]
      rw [h2]
      exact key.symm

/-- Each step of a walk raises the number of up-edges taken by `1` or leaves it alone. -/
theorem upCount_succ {a b n H : ℕ} {w : Fin (n + 1) → Fin (H + 1)} (hw : IsWalk a b w)
    (h0 : walkVal w 0 = 0) (hd : 0 < a + b) {t : ℕ} (ht : t < n) :
    upCount a b w (t + 1) = upCount a b w t + 1 ∨ upCount a b w (t + 1) = upCount a b w t := by
  have e1 := mul_upCount hw h0 hd t (by omega)
  have e2 := mul_upCount hw h0 hd (t + 1) (by omega)
  have hexp : a * (t + 1) = a * t + a := by ring
  have hr : (a + b) * (upCount a b w t + 1) = (a + b) * upCount a b w t + (a + b) := by ring
  rcases isWalk_val hw ht with hup | hdown
  · refine Or.inl (Nat.eq_of_mul_eq_mul_left hd ?_)
    omega
  · refine Or.inr (Nat.eq_of_mul_eq_mul_left hd ?_)
    omega

/-- The number of up-edges taken is monotone in the time. -/
theorem upCount_mono {a b n H : ℕ} {w : Fin (n + 1) → Fin (H + 1)} (hw : IsWalk a b w)
    (h0 : walkVal w 0 = 0) (hd : 0 < a + b) {t t' : ℕ} (h : t ≤ t') (ht' : t' ≤ n) :
    upCount a b w t ≤ upCount a b w t' := by
  induction t', h using Nat.le_induction with
  | base => exact le_rfl
  | succ K hK ih =>
    have hstep := upCount_succ hw h0 hd (show K < n by omega)
    have := ih (by omega)
    omega

/-- No up-edge has been taken at time zero. -/
theorem upCount_zero {a b n H : ℕ} {w : Fin (n + 1) → Fin (H + 1)} (h0 : walkVal w 0 = 0) :
    upCount a b w 0 = 0 := by
  rw [upCount, h0]
  simp

/-- At most one up-edge is taken per unit of time. -/
theorem upCount_le_self {a b n H : ℕ} {w : Fin (n + 1) → Fin (H + 1)} (hw : IsWalk a b w)
    (h0 : walkVal w 0 = 0) (hd : 0 < a + b) : ∀ t ≤ n, upCount a b w t ≤ t := by
  intro t
  induction t with
  | zero =>
    intro _
    exact le_of_eq (upCount_zero h0)
  | succ t ih =>
    intro ht
    have := ih (by omega)
    have hstep := upCount_succ hw h0 hd (show t < n by omega)
    omega

/-- A walk of length `dN` closed at the vertex `0` takes exactly `aN` up-edges. -/
theorem upCount_length {a b N H : ℕ} {w : Fin ((a + b) * N + 1) → Fin (H + 1)}
    (hw : IsWalk a b w) (h0 : walkVal w 0 = 0) (hlast : walkVal w ((a + b) * N) = 0)
    (hd : 0 < a + b) : upCount a b w ((a + b) * N) = a * N := by
  have h := mul_upCount hw h0 hd ((a + b) * N) le_rfl
  rw [hlast] at h
  refine Nat.eq_of_mul_eq_mul_left hd ?_
  rw [h, Nat.zero_add]
  ring

/-- The number of times by which at most `r` up-edges of the walk `w` have been taken. -/
def pcount (a b N : ℕ) {H : ℕ} (w : Fin ((a + b) * N + 1) → Fin (H + 1)) (r : ℕ) : ℕ :=
  #{t ∈ range ((a + b) * N + 1) | upCount a b w t ≤ r}

/-- The times by which at most `r` up-edges have been taken form an initial segment. -/
theorem le_iff_lt_pcount (a b N : ℕ) {H : ℕ} {w : Fin ((a + b) * N + 1) → Fin (H + 1)}
    (hw : IsWalk a b w) (h0 : walkVal w 0 = 0) (hd : 0 < a + b) {r t : ℕ}
    (ht : t ≤ (a + b) * N) : upCount a b w t ≤ r ↔ t < pcount a b N w r := by
  constructor
  · intro hc
    have hsub : range (t + 1) ⊆ {t' ∈ range ((a + b) * N + 1) | upCount a b w t' ≤ r} := by
      intro t' ht'
      rw [Finset.mem_range] at ht'
      refine Finset.mem_filter.2 ⟨Finset.mem_range.2 (by omega), ?_⟩
      exact le_trans (upCount_mono hw h0 hd (show t' ≤ t by omega) ht) hc
    have hcard := Finset.card_le_card hsub
    rw [Finset.card_range] at hcard
    rw [pcount]
    omega
  · intro hlt
    by_contra hc
    have hsub : {t' ∈ range ((a + b) * N + 1) | upCount a b w t' ≤ r} ⊆ range t := by
      intro t' ht'
      obtain ⟨ht'r, ht'c⟩ := Finset.mem_filter.1 ht'
      rw [Finset.mem_range] at ht'r
      refine Finset.mem_range.2 ?_
      by_contra hge
      have := upCount_mono hw h0 hd (show t ≤ t' by omega) (by omega)
      omega
    have hcard := Finset.card_le_card hsub
    rw [Finset.card_range] at hcard
    rw [pcount] at hlt
    omega

/-- The count is at least `r + 1`, since no up-edge is taken at a time before `r`. -/
theorem pcount_ge (a b N : ℕ) {H : ℕ} {w : Fin ((a + b) * N + 1) → Fin (H + 1)}
    (hw : IsWalk a b w) (h0 : walkVal w 0 = 0) (hd : 0 < a + b) {r : ℕ}
    (hr : r ≤ (a + b) * N) : r + 1 ≤ pcount a b N w r := by
  have hsub : range (r + 1) ⊆ {t ∈ range ((a + b) * N + 1) | upCount a b w t ≤ r} := by
    intro t ht
    rw [Finset.mem_range] at ht
    refine Finset.mem_filter.2 ⟨Finset.mem_range.2 (by omega), ?_⟩
    exact le_trans (upCount_le_self hw h0 hd t (by omega)) (by omega)
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_range] at hcard
  rw [pcount]
  omega

/-- The count never exceeds the number of times. -/
theorem pcount_le (a b N : ℕ) {H : ℕ} (w : Fin ((a + b) * N + 1) → Fin (H + 1)) (r : ℕ) :
    pcount a b N w r ≤ (a + b) * N + 1 :=
  le_trans (Finset.card_filter_le _ _) (le_of_eq (Finset.card_range _))

/-- The height at the column `r` of the path traced out by the walk `w`. -/
def walkHeight (a b N : ℕ) {H : ℕ} (w : Fin ((a + b) * N + 1) → Fin (H + 1)) (r : ℕ) : ℕ :=
  pcount a b N w r - (r + 1)

/-- The horizontal step out of the column `r` happens at the time `r + y_r`. -/
theorem pcount_eq (a b N : ℕ) {H : ℕ} {w : Fin ((a + b) * N + 1) → Fin (H + 1)}
    (hw : IsWalk a b w) (h0 : walkVal w 0 = 0) (hd : 0 < a + b) {r : ℕ}
    (hr : r ≤ (a + b) * N) : pcount a b N w r = r + walkHeight a b N w r + 1 := by
  have h := pcount_ge a b N hw h0 hd hr
  rw [walkHeight]
  omega

/-- That time does not exceed the length of the walk. -/
theorem add_walkHeight_le (a b N : ℕ) {H : ℕ} (w : Fin ((a + b) * N + 1) → Fin (H + 1)) {r : ℕ}
    (hr : r ≤ (a + b) * N) : r + walkHeight a b N w r ≤ (a + b) * N := by
  have h := pcount_le a b N w r
  rw [walkHeight]
  omega

/-- The counting adjunction for a walk: at most `r` up-edges have been taken by the time `t`
exactly when `t` does not exceed the time of the horizontal step out of the column `r`. -/
theorem upCount_le_iff (a b N : ℕ) {H : ℕ} {w : Fin ((a + b) * N + 1) → Fin (H + 1)}
    (hw : IsWalk a b w) (h0 : walkVal w 0 = 0) (hd : 0 < a + b) {r t : ℕ}
    (hr : r ≤ (a + b) * N) (ht : t ≤ (a + b) * N) :
    upCount a b w t ≤ r ↔ t ≤ r + walkHeight a b N w r := by
  rw [le_iff_lt_pcount a b N hw h0 hd ht, pcount_eq a b N hw h0 hd hr]
  omega

/-- Every time is one by which at most `aN` up-edges have been taken. -/
theorem pcount_length (a b N : ℕ) {H : ℕ} {w : Fin ((a + b) * N + 1) → Fin (H + 1)}
    (hw : IsWalk a b w) (h0 : walkVal w 0 = 0) (hlast : walkVal w ((a + b) * N) = 0)
    (hd : 0 < a + b) : pcount a b N w (a * N) = (a + b) * N + 1 := by
  refine le_antisymm (pcount_le a b N w _) ?_
  have hsub : range ((a + b) * N + 1)
      ⊆ {t ∈ range ((a + b) * N + 1) | upCount a b w t ≤ a * N} := by
    intro t ht
    rw [Finset.mem_range] at ht
    refine Finset.mem_filter.2 ⟨Finset.mem_range.2 (by omega), ?_⟩
    have h := upCount_mono hw h0 hd (show t ≤ (a + b) * N by omega) le_rfl
    rw [upCount_length hw h0 hlast hd] at h
    exact h
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_range] at hcard
  rw [pcount]
  omega

/-- The path traced out by a closed walk ends at the height `bN`. -/
theorem walkHeight_length (a b N : ℕ) {H : ℕ} {w : Fin ((a + b) * N + 1) → Fin (H + 1)}
    (hw : IsWalk a b w) (h0 : walkVal w 0 = 0) (hlast : walkVal w ((a + b) * N) = 0)
    (hd : 0 < a + b) : walkHeight a b N w (a * N) = b * N := by
  have h := pcount_length a b N hw h0 hlast hd
  have hexp : (a + b) * N = a * N + b * N := by ring
  rw [walkHeight, h]
  omega

/-- Before the end of the walk there is always another up-edge to take. -/
theorem add_walkHeight_lt (a b N : ℕ) {H : ℕ} {w : Fin ((a + b) * N + 1) → Fin (H + 1)}
    (hw : IsWalk a b w) (h0 : walkVal w 0 = 0) (hlast : walkVal w ((a + b) * N) = 0)
    (hd : 0 < a + b) {r : ℕ} (hr : r < a * N) :
    r + walkHeight a b N w r < (a + b) * N := by
  have hrn : r ≤ (a + b) * N := by
    have : a * N ≤ (a + b) * N := Nat.mul_le_mul_right N (by omega)
    omega
  have hle := add_walkHeight_le a b N w hrn
  by_contra hge
  have heq : r + walkHeight a b N w r = (a + b) * N := by omega
  have h := (upCount_le_iff a b N hw h0 hd hrn (le_refl ((a + b) * N))).2 (by omega)
  rw [upCount_length hw h0 hlast hd] at h
  omega

/-- The up-edge taken at the time of the horizontal step out of the column `r`. -/
theorem upCount_succ_add_walkHeight (a b N : ℕ) {H : ℕ} {w : Fin ((a + b) * N + 1) → Fin (H + 1)}
    (hw : IsWalk a b w) (h0 : walkVal w 0 = 0) (hlast : walkVal w ((a + b) * N) = 0)
    (hd : 0 < a + b) {r : ℕ} (hr : r < a * N) :
    upCount a b w (r + walkHeight a b N w r + 1) = r + 1 := by
  have hrn : r ≤ (a + b) * N := by
    have : a * N ≤ (a + b) * N := Nat.mul_le_mul_right N (by omega)
    omega
  have hlt := add_walkHeight_lt a b N hw h0 hlast hd hr
  have h1 : upCount a b w (r + walkHeight a b N w r) ≤ r :=
    (upCount_le_iff a b N hw h0 hd hrn (le_of_lt hlt)).2 le_rfl
  have h2 : ¬ (upCount a b w (r + walkHeight a b N w r + 1) ≤ r) := by
    intro hc
    have := (upCount_le_iff a b N hw h0 hd hrn (by omega)).1 hc
    omega
  have h3 := upCount_succ hw h0 hd hlt
  omega

/-- At the time of the horizontal step out of the column `r`, exactly `r` up-edges have been
taken. -/
theorem upCount_add_walkHeight (a b N : ℕ) {H : ℕ} {w : Fin ((a + b) * N + 1) → Fin (H + 1)}
    (hw : IsWalk a b w) (h0 : walkVal w 0 = 0) (hlast : walkVal w ((a + b) * N) = 0)
    (hd : 0 < a + b) {r : ℕ} (hr : r ≤ a * N) :
    upCount a b w (r + walkHeight a b N w r) = r := by
  have hrn : r ≤ (a + b) * N := by
    have : a * N ≤ (a + b) * N := Nat.mul_le_mul_right N (by omega)
    omega
  rcases Nat.lt_or_ge r (a * N) with hlt | hge
  · have hltn := add_walkHeight_lt a b N hw h0 hlast hd hlt
    have h1 : upCount a b w (r + walkHeight a b N w r) ≤ r :=
      (upCount_le_iff a b N hw h0 hd hrn (le_of_lt hltn)).2 le_rfl
    have h2 := upCount_succ_add_walkHeight a b N hw h0 hlast hd hlt
    have h3 := upCount_succ hw h0 hd hltn
    omega
  · have heq : r = a * N := by omega
    subst heq
    have h := walkHeight_length a b N hw h0 hlast hd
    have hexp : (a + b) * N = a * N + b * N := by ring
    rw [h, ← hexp]
    exact upCount_length hw h0 hlast hd

/-- The path traced out by a walk starts at the height `0`. -/
theorem walkHeight_zero (a b N : ℕ) {H : ℕ} {w : Fin ((a + b) * N + 1) → Fin (H + 1)}
    (hw : IsWalk a b w) (h0 : walkVal w 0 = 0) (hlast : walkVal w ((a + b) * N) = 0)
    (ha : 0 < a) (hb : 0 < b) : walkHeight a b N w 0 = 0 := by
  have hd : 0 < a + b := by omega
  have hle := add_walkHeight_le a b N w (r := 0) (Nat.zero_le _)
  have hu := upCount_add_walkHeight a b N hw h0 hlast hd (Nat.zero_le (a * N))
  have h := mul_upCount hw h0 hd (0 + walkHeight a b N w 0) (by omega)
  rw [hu, Nat.mul_zero] at h
  have hap : a * (0 + walkHeight a b N w 0) = 0 := by omega
  rcases Nat.mul_eq_zero.1 hap with hz | hz
  · omega
  · omega

/-- The path traced out by a walk is monotone. -/
theorem walkHeight_mono (a b N : ℕ) {H : ℕ} {w : Fin ((a + b) * N + 1) → Fin (H + 1)}
    (hw : IsWalk a b w) (h0 : walkVal w 0 = 0) (hlast : walkVal w ((a + b) * N) = 0)
    (hd : 0 < a + b) {r : ℕ} (hr : r < a * N) :
    walkHeight a b N w r ≤ walkHeight a b N w (r + 1) := by
  have hrn : r + 1 ≤ (a + b) * N := by
    have : a * N ≤ (a + b) * N := Nat.mul_le_mul_right N (by omega)
    omega
  have h2 := upCount_succ_add_walkHeight a b N hw h0 hlast hd hr
  have h3 := (upCount_le_iff a b N hw h0 hd hrn
    (show r + walkHeight a b N w r + 1 ≤ (a + b) * N from
      add_walkHeight_lt a b N hw h0 hlast hd hr)).1 (le_of_eq h2)
  omega

/-- The path traced out by a walk stays below the diagonal. -/
theorem mul_walkHeight_le (a b N : ℕ) {H : ℕ} {w : Fin ((a + b) * N + 1) → Fin (H + 1)}
    (hw : IsWalk a b w) (h0 : walkVal w 0 = 0) (hlast : walkVal w ((a + b) * N) = 0)
    (hd : 0 < a + b) {r : ℕ} (hr : r ≤ a * N) :
    a * walkHeight a b N w r ≤ b * r := by
  have hrn : r ≤ (a + b) * N := by
    have : a * N ≤ (a + b) * N := Nat.mul_le_mul_right N (by omega)
    omega
  have hle := add_walkHeight_le a b N w hrn
  have hu := upCount_add_walkHeight a b N hw h0 hlast hd hr
  have h := mul_upCount hw h0 hd (r + walkHeight a b N w r) hle
  rw [hu] at h
  have h1 : a * (r + walkHeight a b N w r) = a * r + a * walkHeight a b N w r := by ring
  have h2 : (a + b) * r = a * r + b * r := by ring
  omega

/-- The path traced out by a walk stays below the height `bN`. -/
theorem walkHeight_le (a b N : ℕ) {H : ℕ} {w : Fin ((a + b) * N + 1) → Fin (H + 1)}
    (hw : IsWalk a b w) (h0 : walkVal w 0 = 0) (hlast : walkVal w ((a + b) * N) = 0)
    (ha : 0 < a) (hb : 0 < b) {r : ℕ} (hr : r ≤ a * N) : walkHeight a b N w r ≤ b * N := by
  have hd : 0 < a + b := by omega
  have h := mul_walkHeight_le a b N hw h0 hlast hd hr
  have h2 : b * r ≤ b * (a * N) := Nat.mul_le_mul_left b hr
  have h3 : b * (a * N) = a * (b * N) := by ring
  exact Nat.le_of_mul_le_mul_left (by omega) ha

/-- The vertex of a walk at a time of the walk. -/
theorem walkVal_val {n H : ℕ} (w : Fin (n + 1) → Fin (H + 1)) (t : Fin (n + 1)) :
    walkVal w (t : ℕ) = ((w t : Fin (H + 1)) : ℕ) := by
  rw [walkVal, dite_eq_left t.isLt, Fin.eta]

/-- The vertex of a walk at time zero. -/
theorem walkVal_zero {n H : ℕ} (w : Fin (n + 1) → Fin (H + 1)) :
    walkVal w 0 = ((w 0 : Fin (H + 1)) : ℕ) := by
  have h := walkVal_val w 0
  rw [Fin.val_zero] at h
  exact h

/-- The vertex of a walk at its last time. -/
theorem walkVal_last {n H : ℕ} (w : Fin (n + 1) → Fin (H + 1)) :
    walkVal w n = ((w (Fin.last n) : Fin (H + 1)) : ℕ) := by
  have h := walkVal_val w (Fin.last n)
  rw [Fin.val_last] at h
  exact h

/-- The height of a path at a coordinate of the path. -/
theorem ht_val {a b N : ℕ} (y : Paths.Heights a b N) (r : Fin (a * N + 1)) :
    Paths.ht y (r : ℕ) = ((y r : Fin (b * N + 1)) : ℕ) := by
  rw [Paths.ht, dite_eq_left r.isLt, Fin.eta]

/-- The path traced out by the walk `w`, clamped to the height `bN` so as to be defined on every
walk. -/
def walkPath (a b N : ℕ) {H : ℕ} (w : Fin ((a + b) * N + 1) → Fin (H + 1)) :
    Paths.Heights a b N :=
  fun r => ⟨min (walkHeight a b N w (r : ℕ)) (b * N), Nat.lt_succ_of_le (min_le_right _ _)⟩

/-- For a walk closed at the vertex `0` the clamp is inactive. -/
theorem ht_walkPath (a b N : ℕ) {H : ℕ} {w : Fin ((a + b) * N + 1) → Fin (H + 1)}
    (hw : IsWalk a b w) (h0 : walkVal w 0 = 0) (hlast : walkVal w ((a + b) * N) = 0)
    (ha : 0 < a) (hb : 0 < b) {r : ℕ} (hr : r ≤ a * N) :
    Paths.ht (walkPath a b N w) r = walkHeight a b N w r := by
  rw [Paths.ht, dite_eq_left (show r < a * N + 1 by omega), walkPath]
  exact min_eq_left (walkHeight_le a b N hw h0 hlast ha hb hr)

/-- The path traced out by a closed walk is a below-diagonal path. -/
theorem isBelowDiagonal_walkPath (a b N : ℕ) {H : ℕ} {w : Fin ((a + b) * N + 1) → Fin (H + 1)}
    (hw : IsWalk a b w) (h0 : walkVal w 0 = 0) (hlast : walkVal w ((a + b) * N) = 0)
    (ha : 0 < a) (hb : 0 < b) : Paths.IsBelowDiagonal (walkPath a b N w) := by
  have hd : 0 < a + b := by omega
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [ht_walkPath a b N hw h0 hlast ha hb (Nat.zero_le _)]
    exact walkHeight_zero a b N hw h0 hlast ha hb
  · rw [ht_walkPath a b N hw h0 hlast ha hb (le_refl (a * N))]
    exact walkHeight_length a b N hw h0 hlast hd
  · intro r hr
    rw [ht_walkPath a b N hw h0 hlast ha hb (le_of_lt hr),
      ht_walkPath a b N hw h0 hlast ha hb (show r + 1 ≤ a * N by omega)]
    exact walkHeight_mono a b N hw h0 hlast hd hr
  · intro r hr
    rw [ht_walkPath a b N hw h0 hlast ha hb hr]
    exact mul_walkHeight_le a b N hw h0 hlast hd hr

/-- The horizontal steps of the path traced out by a walk are its up-edges. -/
theorem eCount_walkPath (a b N : ℕ) {H : ℕ} {w : Fin ((a + b) * N + 1) → Fin (H + 1)}
    (hw : IsWalk a b w) (h0 : walkVal w 0 = 0) (hlast : walkVal w ((a + b) * N) = 0)
    (ha : 0 < a) (hb : 0 < b) {t : ℕ} (ht : t ≤ (a + b) * N) :
    eCount (walkPath a b N w) t = upCount a b w t := by
  have hd : 0 < a + b := by omega
  have hut : upCount a b w t ≤ a * N := by
    have h := upCount_mono hw h0 hd ht (le_refl ((a + b) * N))
    rw [upCount_length hw h0 hlast hd] at h
    exact h
  have hstep : ∀ r ≤ a * N, stepTime (walkPath a b N w) r = r + walkHeight a b N w r := by
    intro r hr
    rw [stepTime, ht_walkPath a b N hw h0 hlast ha hb hr]
  have hfe : {r ∈ range (a * N) | stepTime (walkPath a b N w) r < t}
      = range (upCount a b w t) := by
    refine Finset.Subset.antisymm (fun r hr => ?_) (fun r hr => ?_)
    · obtain ⟨hrr, hrt⟩ := Finset.mem_filter.1 hr
      rw [Finset.mem_range] at hrr
      rw [hstep r (le_of_lt hrr)] at hrt
      refine Finset.mem_range.2 ?_
      by_contra hge
      have hrn : r ≤ (a + b) * N := by
        have : a * N ≤ (a + b) * N := Nat.mul_le_mul_right N (by omega)
        omega
      have := (upCount_le_iff a b N hw h0 hd hrn ht).1 (by omega)
      omega
    · rw [Finset.mem_range] at hr
      have hrr : r < a * N := by omega
      have hrn : r ≤ (a + b) * N := by
        have : a * N ≤ (a + b) * N := Nat.mul_le_mul_right N (by omega)
        omega
      refine Finset.mem_filter.2 ⟨Finset.mem_range.2 hrr, ?_⟩
      rw [hstep r (le_of_lt hrr)]
      by_contra hge
      have := (upCount_le_iff a b N hw h0 hd hrn ht).2 (by omega)
      omega
  rw [eCount, hfe, Finset.card_range]

/-- The walk traced out by the path traced out by a walk is the walk itself. -/
theorem walkVertex_walkPath (a b N : ℕ) {H : ℕ} {w : Fin ((a + b) * N + 1) → Fin (H + 1)}
    (hw : IsWalk a b w) (h0 : walkVal w 0 = 0) (hlast : walkVal w ((a + b) * N) = 0)
    (ha : 0 < a) (hb : 0 < b) {t : ℕ} (ht : t ≤ (a + b) * N) :
    walkVertex (walkPath a b N w) t = walkVal w t := by
  have hd : 0 < a + b := by omega
  have h1 := add_walkVertex (isBelowDiagonal_walkPath a b N hw h0 hlast ha hb) ht
  have h2 := mul_upCount hw h0 hd t ht
  rw [eCount_walkPath a b N hw h0 hlast ha hb ht] at h1
  omega

/-- The vertex of the walk of a below-diagonal path. -/
theorem walkVal_pathWalk (a b N H : ℕ) {y : Paths.Heights a b N} (hy : Paths.IsBelowDiagonal y)
    (hH : a * b * N ≤ H) {t : ℕ} (ht : t ≤ (a + b) * N) :
    walkVal (pathWalk a b N H y) t = walkVertex y t := by
  have hlt : t < (a + b) * N + 1 := by omega
  rw [walkVal, dite_eq_left hlt, pathWalk_val a b N H hy hH ⟨t, hlt⟩]

/-- The walk of a below-diagonal path steps along the edges of the graph. -/
theorem isWalk_pathWalk (a b N H : ℕ) {y : Paths.Heights a b N} (hy : Paths.IsBelowDiagonal y)
    (hH : a * b * N ≤ H) : IsWalk a b (pathWalk a b N H y) := by
  intro i
  rw [walkVal_val_castSucc, walkVal_val_succ,
    walkVal_pathWalk a b N H hy hH (show (i : ℕ) ≤ (a + b) * N from le_of_lt i.isLt),
    walkVal_pathWalk a b N H hy hH (show (i : ℕ) + 1 ≤ (a + b) * N from i.isLt)]
  by_cases hE : IsEStep y (i : ℕ)
  · exact Or.inl (walkVertex_succ_of_isEStep hy i.isLt hE)
  · exact Or.inr (walkVertex_succ_of_not_isEStep hy i.isLt hE)

/-- The times before a given one form an initial segment. -/
theorem filter_le_eq_range {n s : ℕ} (hs : s ≤ n) :
    {t ∈ range (n + 1) | t ≤ s} = range (s + 1) := by
  refine Finset.Subset.antisymm (fun t ht => ?_) (fun t ht => ?_)
  · obtain ⟨-, hts⟩ := Finset.mem_filter.1 ht
    exact Finset.mem_range.2 (by omega)
  · rw [Finset.mem_range] at ht
    exact Finset.mem_filter.2 ⟨Finset.mem_range.2 (by omega), by omega⟩

/-- The path traced out by the walk of a below-diagonal path is the path itself. -/
theorem walkHeight_pathWalk (a b N H : ℕ) {y : Paths.Heights a b N}
    (hy : Paths.IsBelowDiagonal y) (ha : 0 < a) (hb : 0 < b) (hH : a * b * N ≤ H) {r : ℕ}
    (hr : r ≤ a * N) :
    walkHeight a b N (pathWalk a b N H y) r = Paths.ht y r := by
  have hd : 0 < a + b := by omega
  have h0 : walkVal (pathWalk a b N H y) 0 = 0 := by
    rw [walkVal_pathWalk a b N H hy hH (Nat.zero_le _), walkVertex_zero]
  have hlast : walkVal (pathWalk a b N H y) ((a + b) * N) = 0 := by
    rw [walkVal_pathWalk a b N H hy hH (le_refl _), walkVertex_length hy]
  have hup : ∀ t ≤ (a + b) * N, upCount a b (pathWalk a b N H y) t = eCount y t := by
    intro t ht
    have h1 := mul_upCount (isWalk_pathWalk a b N H hy hH) h0 hd t ht
    have h2 := add_walkVertex hy ht
    rw [walkVal_pathWalk a b N H hy hH ht] at h1
    exact Nat.eq_of_mul_eq_mul_left hd (by omega)
  rcases Nat.lt_or_ge r (a * N) with hlt | hge
  · have hpc : pcount a b N (pathWalk a b N H y) r = stepTime y r + 1 := by
      rw [pcount]
      have hfe : {t ∈ range ((a + b) * N + 1) | upCount a b (pathWalk a b N H y) t ≤ r}
          = {t ∈ range ((a + b) * N + 1) | t ≤ stepTime y r} := by
        refine Finset.filter_congr fun t ht => ?_
        rw [Finset.mem_range] at ht
        rw [hup t (by omega)]
        exact eCount_le_iff hy hlt
      rw [hfe, filter_le_eq_range (le_of_lt (stepTime_lt hy hlt)), Finset.card_range]
    rw [walkHeight, hpc, stepTime]
    omega
  · have heq : r = a * N := by omega
    subst heq
    rw [walkHeight_length a b N (isWalk_pathWalk a b N H hy hH) h0 hlast hd, hy.2.1]

/-- The two constructions are mutually inverse, on paths. -/
theorem walkPath_pathWalk (a b N H : ℕ) {y : Paths.Heights a b N} (hy : Paths.IsBelowDiagonal y)
    (ha : 0 < a) (hb : 0 < b) (hH : a * b * N ≤ H) : walkPath a b N (pathWalk a b N H y) = y := by
  funext r
  refine Fin.ext ?_
  have hr : (r : ℕ) ≤ a * N := Nat.lt_succ_iff.1 r.isLt
  have hval : walkHeight a b N (pathWalk a b N H y) (r : ℕ) = ((y r : Fin (b * N + 1)) : ℕ) := by
    rw [walkHeight_pathWalk a b N H hy ha hb hH hr, ht_val]
  have hmin : min (walkHeight a b N (pathWalk a b N H y) (r : ℕ)) (b * N)
      = ((y r : Fin (b * N + 1)) : ℕ) := by
    rw [hval]
    exact min_eq_left (Nat.lt_succ_iff.1 (y r).isLt)
  exact hmin

/-- The two constructions are mutually inverse, on walks. -/
theorem pathWalk_walkPath (a b N H : ℕ) {w : Fin ((a + b) * N + 1) → Fin (H + 1)}
    (hw : IsWalk a b w) (h0 : walkVal w 0 = 0) (hlast : walkVal w ((a + b) * N) = 0)
    (ha : 0 < a) (hb : 0 < b) (hH : a * b * N ≤ H) :
    pathWalk a b N H (walkPath a b N w) = w := by
  funext t
  refine Fin.ext ?_
  rw [pathWalk_val a b N H (isBelowDiagonal_walkPath a b N hw h0 hlast ha hb) hH t,
    walkVertex_walkPath a b N hw h0 hlast ha hb (Nat.lt_succ_iff.1 t.isLt), walkVal_val]

/-- The weighted count of the closed walks of length `dN` at the vertex `0` of the graph on
`0, …, H` is the area generating polynomial of the below-diagonal `(aN, bN)`-paths, as soon as the
height bound `H` is at least `abN`: the walk of a path is closed and carries the weight `q` to its
area, and every closed walk arises this way. -/
theorem pow_constAdjacency_apply_zero_zero (a b N H : ℕ) (ha : 0 < a) (hb : 0 < b)
    (hH : a * b * N ≤ H) :
    (constAdjacency a b H ^ ((a + b) * N)) 0 0 = qOfInt (Paths.areaPoly a b N) := by
  have hd : 0 < a + b := by omega
  have hzero : ∀ w ∈ Finset.univ.filter
      (fun w : Fin ((a + b) * N + 1) → Fin (H + 1) => w 0 = 0 ∧ w (Fin.last _) = 0),
      walkWeight (constAdjacency a b H) w ≠ 0 → IsWalk a b w := by
    intro w _ hne
    by_contra hw
    exact hne (walkWeight_eq_zero_of_not_isWalk a b H hw)
  have hmem : ∀ w ∈ (Finset.univ.filter
      (fun w : Fin ((a + b) * N + 1) → Fin (H + 1) => w 0 = 0 ∧ w (Fin.last _) = 0)).filter
        (IsWalk a b),
      IsWalk a b w ∧ walkVal w 0 = 0 ∧ walkVal w ((a + b) * N) = 0 := by
    intro w hw
    obtain ⟨hw1, hw2⟩ := Finset.mem_filter.1 hw
    obtain ⟨-, he0, hel⟩ := Finset.mem_filter.1 hw1
    refine ⟨hw2, ?_, ?_⟩
    · rw [walkVal_zero, he0, Fin.val_zero]
    · rw [walkVal_last, hel, Fin.val_zero]
  rw [pow_apply_eq_sum_walkWeight, ← Finset.sum_filter_of_ne hzero, Paths.areaPoly, map_sum]
  refine Finset.sum_nbij' (i := fun w => walkPath a b N w) (j := fun y => pathWalk a b N H y)
    (fun w hw => ?_) (fun y hy => ?_) (fun w hw => ?_) (fun y hy => ?_) (fun w hw => ?_)
  · obtain ⟨hw1, hw2, hw3⟩ := hmem w hw
    exact Finset.mem_filter.2 ⟨Finset.mem_univ _,
      isBelowDiagonal_walkPath a b N hw1 hw2 hw3 ha hb⟩
  · obtain ⟨-, hy'⟩ := Finset.mem_filter.1 hy
    refine Finset.mem_filter.2 ⟨Finset.mem_filter.2 ⟨Finset.mem_univ _, ?_, ?_⟩,
      isWalk_pathWalk a b N H hy' hH⟩
    · exact pathWalk_zero a b N H hy' hH
    · exact pathWalk_last a b N H hy' hH
  · obtain ⟨hw1, hw2, hw3⟩ := hmem w hw
    exact pathWalk_walkPath a b N H hw1 hw2 hw3 ha hb hH
  · obtain ⟨-, hy'⟩ := Finset.mem_filter.1 hy
    exact walkPath_pathWalk a b N H hy' ha hb hH
  · obtain ⟨hw1, hw2, hw3⟩ := hmem w hw
    have hbd := isBelowDiagonal_walkPath a b N hw1 hw2 hw3 ha hb
    have hrt := pathWalk_walkPath a b N H hw1 hw2 hw3 ha hb hH
    calc walkWeight (constAdjacency a b H) w
        = walkWeight (constAdjacency a b H) (pathWalk a b N H (walkPath a b N w)) := by rw [hrt]
      _ = qVar ^ Paths.area (walkPath a b N w) := walkWeight_pathWalk a b N H hbd ha hb hH
      _ = qOfInt (PowerSeries.X ^ Paths.area (walkPath a b N w)) := by rw [map_pow, qVar]

/-! ### The equation for the determinant series -/

/-- The `z^N` coefficient of the walk generating series is the `N`-th area polynomial as soon as
the height bound is at least `abN`. -/
theorem coeff_walkTrunc (a b N H : ℕ) (ha : 0 < a) (hb : 0 < b) (hH : a * b * N ≤ H) :
    PowerSeries.coeff N (walkTrunc a b H) = PowerSeries.coeff N (genA a b) := by
  rw [walkTrunc, PowerSeries.coeff_mk, genA, PowerSeries.coeff_mk,
    pow_constAdjacency_apply_zero_zero a b N H ha hb hH]

/-- Each `z`-coefficient of the walk generating series is eventually that of `𝒜(z;q)`. -/
theorem tendsto_coeff_walkTrunc (a b N : ℕ) (ha : 0 < a) (hb : 0 < b) :
    Filter.Tendsto (fun H => PowerSeries.coeff N (walkTrunc a b H)) Filter.atTop
      (nhds (PowerSeries.coeff N (genA a b))) := by
  refine Filter.Tendsto.congr' ?_ tendsto_const_nhds
  filter_upwards [Filter.eventually_ge_atTop (a * b * N)] with H hH
  exact (coeff_walkTrunc a b N H ha hb hH).symm

/-- The `q`-difference equation for the determinant series: `𝒟(qz;q) = 𝒜(z;q) 𝒟(z;q)`, given that
the coefficientwise limit defining `𝒟` exists. -/
theorem rescale_detSeries (a b : ℕ) (hab : Nat.Coprime a b) (ha : 0 < a) (hb : 0 < b)
    {D : ZSeries} (hD : Filter.Tendsto (detTrunc a b) Filter.atTop (nhds D)) :
    PowerSeries.rescale qVar (detSeries a b) = genA a b * detSeries a b := by
  have hlim : detSeries a b = D := by rw [detSeries, hD.limUnder_eq]
  have hcoeff := (PowerSeries.WithPiTopology.tendsto_iff_coeff_tendsto _ _ _ _).1 hD
  rw [hlim]
  refine PowerSeries.ext fun N => ?_
  have hid : ∀ H : ℕ, (∑ M ∈ range (N + 1), PowerSeries.coeff M (detTrunc a b (H + 1)) *
      PowerSeries.coeff (N - M) (walkTrunc a b (H + 1)))
        = qVar ^ N * PowerSeries.coeff N (detTrunc a b H) := by
    intro H
    have h := congrArg (PowerSeries.coeff N) (detTrunc_mul_walkTrunc a b H hab ha hb)
    rw [PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,
      PowerSeries.coeff_rescale] at h
    exact h
  have hL : Filter.Tendsto (fun H => ∑ M ∈ range (N + 1),
      PowerSeries.coeff M (detTrunc a b (H + 1)) *
        PowerSeries.coeff (N - M) (walkTrunc a b (H + 1))) Filter.atTop
      (nhds (∑ M ∈ range (N + 1),
        PowerSeries.coeff M D * PowerSeries.coeff (N - M) (genA a b))) := by
    refine tendsto_finsetSum _ fun M _ => Filter.Tendsto.mul ?_ ?_
    · exact (hcoeff M).comp (Filter.tendsto_add_atTop_nat 1)
    · exact (tendsto_coeff_walkTrunc a b (N - M) ha hb).comp (Filter.tendsto_add_atTop_nat 1)
  have hR : Filter.Tendsto (fun H => qVar ^ N * PowerSeries.coeff N (detTrunc a b H))
      Filter.atTop (nhds (qVar ^ N * PowerSeries.coeff N D)) :=
    Filter.Tendsto.const_mul _ (hcoeff N)
  have heq := tendsto_nhds_unique (hL.congr hid) hR
  rw [PowerSeries.coeff_rescale, mul_comm (genA a b) D, PowerSeries.coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  exact heq.symm

/-- `𝒟(-z;q)` satisfies the common equation, given that the coefficientwise limit defining `𝒟`
exists: the equation `𝒟(qz;q) = 𝒜(z;q)𝒟(z;q)` becomes `G(qz;q) = 𝒜(-z;q)G(z;q)` after the
substitution `z ↦ -z`, and the constant term is `1`. -/
theorem isCommonSolution_rescale_neg_one_detSeries (a b : ℕ) (hab : Nat.Coprime a b) (ha : 0 < a)
    (hb : 0 < b) {D : ZSeries} (hD : Filter.Tendsto (detTrunc a b) Filter.atTop (nhds D)) :
    IsCommonSolution a b (PowerSeries.rescale (-1) (detSeries a b)) := by
  refine ⟨?_, constantCoeff_rescale_neg_one_detSeries a b hD⟩
  rw [← map_mul, ← rescale_detSeries a b hab ha hb hD, PowerSeries.rescale_rescale,
    PowerSeries.rescale_rescale, mul_comm (-1 : LaurentSeries ℚ) qVar]

end HJO.DetEquation
