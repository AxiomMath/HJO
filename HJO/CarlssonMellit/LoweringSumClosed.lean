/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.CarlssonMellit.ChiPrimeExpansionExists
public import HJO.CarlssonMellit.ChiPrimeNu
public import HJO.CarlssonMellit.InsertRealisation
public import HJO.CarlssonMellit.LoweringSum
public import HJO.CarlssonMellit.NegateHsymm
public import HJO.CarlssonMellit.ZFirTelescope
public import HJO.Shuffle.SweepComputesLowering
public meta import HJO.Attr

/-! # The lowering sum, with the expansion discharged

`HJO/CarlssonMellit/LoweringSum.lean` carries Carlsson and Mellit's derivation of the lowering sum
`HJO.Dyck.IsLoweringSum` down to two gaps, every one of its results carrying the expansion
`χ'_{Id_k}(π) = ∑_{j ≥ 1}y_k^jg_j(π)[X + y_k]` as a hypothesis. That expansion is
`HJO.Dyck.existsUnique_eq_sum_pow_mul_realiseAddLetter`, proved in
`HJO/CarlssonMellit/ChiPrimeExpansionExists.lean`, so the hypothesis can be discharged and those
results restated unconditionally. This file does that, carries out Carlsson and Mellit's own
comparison of their equations (4.15) and (4.16), and so proves `HJO.Dyck.isLoweringSum`.

## Main results

* `HJO.Dyck.exists_expansion_unnormalisedCharSeries_identityTuple`: the expansion in the shape
  `LoweringSum.lean` reads it — a `Finset` of indices missing `0`, a family of members of `V_{k-1}`
  and the identity.
* `HJO.Dyck.exists_sum_auxToFrac_unnormalisedCharSeries_lowerTuple`: Carlsson and Mellit's formula
  `χ'_{k,r}(π) = ∑_{i}f_{i,r}g_i(π)[X + y_k]` with the expansion discharged.
* `HJO.Dyck.exists_ringHom_sum_one_sub_C_scalarFrac_mul_auxToFrac_insertFront`: the last display of
  Carlsson and Mellit's "Lowering operator" before their equation (4.15), with the expansion
  discharged and with every alphabet produced rather than carried.
* `HJO.Dyck.lowerAuxProd_mul_theta_qshiftNeg`: Carlsson and Mellit's equation (4.16), on `V_k`.
* `HJO.Dyck.one_sub_mul_lowerAuxProd_mul_theta_dminusCM`: Carlsson and Mellit's comparison of (4.15)
  with (4.16), on `V_{k-1}`.
* `HJO.Dyck.isLoweringSum`: the lowering-sum identity `HJO.Dyck.IsLoweringSum`, for every `q`.
* `HJO.Dyck.isSigmaCharacter_dminusCM'`, `HJO.Dyck.mem_piece_and_isSigmaCharacter_partialWordOp'`,
  `HJO.Dyck.realisation_constantCoeff_markedWordOp'`,
  `HJO.Mellit.map_constantCoeff_markedWordOp'` and `HJO.Mellit.sweepComputes`: the five statements
  downstream of the lowering sum that were stated with `HJO.Dyck.IsLoweringSum` as a hypothesis,
  now with that hypothesis discharged.

## References

E. Carlsson and A. Mellit, *A proof of the shuffle conjecture*, arXiv:1508.06239v3, Section 4,
subsection "Lowering operator".
-/

@[expose] public section

namespace HJO.Dyck

open HJO.Sweep

/-! ### The expansion, in the shape the telescoping reads -/

section Expansion

variable {K : Type*} [CommRing K] [IsDomain K] [Algebra ℚ K] {m N : ℕ} {x : Fin N → ℕ}
  {ι : Sweep.Total K →ₐ[K] Sym.AuxAlphabetSeries K (m + 1)}

/-- **`HJO.Dyck.existsUnique_eq_sum_pow_mul_realiseAddLetter` in the shape
`HJO/CarlssonMellit/LoweringSum.lean` reads it.** The lemma produces a family indexed by all of `ℕ`,
vanishing at `0` and past a bound; the telescoping reads a `Finset` of indices not containing `0`.
Deleting `0` from the range of the bound converts one into the other, the deleted term vanishing
because `g_0 = 0`. -/
theorem exists_expansion_unnormalisedCharSeries_identityTuple (q : K)
    (hx : IsPartialDyck (m + 1) N x) (hι : IsAuxRealisation (m + 1) ι) :
    ∃ (u : Finset ℕ) (g : ℕ → Sweep.Total K), (∀ i ∈ u, g i ∈ Sweep.piece K m) ∧ (0 : ℕ) ∉ u ∧
      Sym.auxToFrac K (m + 1)
          (unnormalisedCharSeries q (m + 1) x (identityTuple (m + 1)))
        = ∑ i ∈ u, MvPowerSeries.C (Sym.yFrac K (Fin.last m)) ^ i *
            realiseAddLetter K m ι (g i) := by
  obtain ⟨g, ⟨hgmem, hg0, M, -, hgsum⟩, -⟩ :=
    existsUnique_eq_sum_pow_mul_realiseAddLetter hι q hx hx.le_length
  refine ⟨(Finset.range (M + 1)).erase 0, g, fun i _ => hgmem i, Finset.notMem_erase 0 _, ?_⟩
  rw [hgsum, Finset.sum_erase _ (by rw [hg0, map_zero, mul_zero])]

end Expansion

/-! ### The freed characteristic series in terms of the expansion, unconditionally -/

section Step

variable {K : Type*} [CommRing K] [IsDomain K] [Algebra ℚ K] {m N : ℕ} {x : Fin N → ℕ}
  {ι : Sweep.Total K →ₐ[K] Sym.AuxAlphabetSeries K (m + 1)}

/-- **The freed characteristic series in terms of the expansion, with the expansion discharged**:
for a partial Dyck path `π ∈ 𝔻_{k,N}` of level `k = m + 1` there are `g_i(π) ∈ V_{k-1}`, `i ≥ 1`,
with

`χ'_{k,r}(π) = ∑_{i}f_{i,r}g_i(π)[X + y_k]`

for *every* `r ≥ 0` at once. This is
`HJO.Dyck.auxToFrac_unnormalisedCharSeries_lowerTuple_eq_sum` with its hypothesis `hexp` supplied by
`HJO.Dyck.existsUnique_eq_sum_pow_mul_realiseAddLetter`. -/
theorem exists_sum_auxToFrac_unnormalisedCharSeries_lowerTuple (q : K)
    (hx : IsPartialDyck (m + 1) N x) (hι : IsAuxRealisation (m + 1) ι) :
    ∃ (u : Finset ℕ) (g : ℕ → Sweep.Total K), (∀ i ∈ u, g i ∈ Sweep.piece K m) ∧ (0 : ℕ) ∉ u ∧
      ∀ r : ℕ, Sym.auxToFrac K (m + 1) (unnormalisedCharSeries q (m + 1) x (lowerTuple m r))
        = ∑ i ∈ u, Sym.zSwapCoeff K m q i r * realiseAddLetter K m ι (g i) := by
  obtain ⟨u, g, hg, hu, hexp⟩ :=
    exists_expansion_unnormalisedCharSeries_identityTuple q hx hι
  exact ⟨u, g, hg, hu, auxToFrac_unnormalisedCharSeries_lowerTuple_eq_sum q hx hι hg hexp⟩

/-- **The display of Carlsson and Mellit before their equation (4.15), unconditionally**: for a
partial Dyck path `π ∈ 𝔻_{k,N}` of level `k = m + 1` there are `g_i(π) ∈ V_{k-1}`, `i ≥ 1`, and an
alphabet `(1-q)(X + y_k)` with

`(1-q)·y_1 ⋯ y_{k-1}·Φ_{k-1}(ν_{Id_{k-1}}(π)) = ∑_{i}h_i[(1-q)(X+y_k)]·g_i(π)[X+y_k]`.

This is `HJO.Dyck.exists_ringHom_one_sub_C_scalarFrac_mul_auxToFrac_insertFront_partialCharSeries`
with its hypothesis `hexp` supplied by `HJO.Dyck.existsUnique_eq_sum_pow_mul_realiseAddLetter`, so
Carlsson and Mellit's argument is carried to that display with no hypothesis left. -/
theorem exists_ringHom_sum_one_sub_C_scalarFrac_mul_auxToFrac_insertFront
    {A : Type*} [CommRing A] [Algebra ℚ A] (q : K) (base : A →+* Sym.AuxFrac K m)
    (hx : IsPartialDyck (m + 1) N x) (hι : IsAuxRealisation (m + 1) ι) :
    ∃ (u : Finset ℕ) (g : ℕ → Sweep.Total K) (Λ : Sym.Lambda A →+* Sym.AuxAlphabetSeriesFrac K
        (m + 1)),
      (∀ i ∈ u, g i ∈ Sweep.piece K m) ∧ (0 : ℕ) ∉ u ∧
        (∀ a : A, Λ (MvPolynomial.C a) = MvPowerSeries.C (Sym.auxFracCastSucc K m (base a))) ∧
          (∀ j : ℕ, 0 < j → Λ (Sym.powerSum A j)
            = (1 - MvPowerSeries.C (Sym.scalarFrac K q) ^ j)
                * Sym.summableSum fun b => Sym.zLetterSeries K m b ^ j) ∧
            (1 - MvPowerSeries.C (Sym.scalarFrac K q))
                * (MvPowerSeries.C (Sym.auxFracCastSucc K m (lowerAuxScalar K m))
                  * Sym.auxToFrac K (m + 1)
                      (Sym.insertFront K m (partialCharSeries q m x (identityTuple m))))
              = ∑ i ∈ u, Λ (Sym.completeHomog A i) * realiseAddLetter K m ι (g i) := by
  obtain ⟨u, g, hg, hu, hexp⟩ :=
    exists_expansion_unnormalisedCharSeries_identityTuple q hx hι
  obtain ⟨Λ, hΛC, hΛp, hsum⟩ :=
    exists_ringHom_one_sub_C_scalarFrac_mul_auxToFrac_insertFront_partialCharSeries (A := A) q base
      hx hι hg hu hexp
  exact ⟨u, g, Λ, hg, hu, hΛC, hΛp, hsum⟩

end Step

/-! ### The expansion of `V_k` in powers of its last auxiliary variable -/

section LowerPart

variable {K : Type*} [CommRing K]

/-- **The coefficient of `y_{j+1}^i` in an element of `V_*`.** On the `Λ`-basis of `y`-monomials it
keeps the monomials whose exponent of `y_{j+1}` is `i`, with that exponent deleted, and kills the
others. This is the reading of an element of `V_k` as a polynomial in `y_k` over `V_{k-1}` that
`HJO.Sweep.dminusCM` performs before pairing the coefficients against the elementary functions:
`HJO.Sweep.lowerCoeffShift` is `∑_i(-1)^ie_{i+1}` against these coefficients. -/
noncomputable def lowerPart (K : Type*) [CommRing K] (j i : ℕ) :
    Sweep.Total K →ₗ[Sym.Lambda K] Sweep.Total K :=
  (MvPolynomial.basisMonomials ℕ (Sym.Lambda K)).constr (Sym.Lambda K) fun d =>
    if d j = i then MvPolynomial.monomial (Finsupp.erase j d) 1 else 0

/-- `lowerPart` on a basis monomial, read off. -/
theorem lowerPart_monomial_one (j i : ℕ) (d : ℕ →₀ ℕ) :
    lowerPart K j i (MvPolynomial.monomial d (1 : Sym.Lambda K))
      = if d j = i then MvPolynomial.monomial (Finsupp.erase j d) 1 else 0 := by
  have hb : (MvPolynomial.basisMonomials ℕ (Sym.Lambda K)) d
      = MvPolynomial.monomial d 1 := congrFun (MvPolynomial.coe_basisMonomials ℕ _) d
  rw [lowerPart, ← hb]
  exact Module.Basis.constr_basis _ _ _ _

/-- `lowerPart` on an arbitrary monomial: the coefficient rides along. -/
theorem lowerPart_monomial (j i : ℕ) (d : ℕ →₀ ℕ) (c : Sym.Lambda K) :
    lowerPart K j i (MvPolynomial.monomial d c)
      = if d j = i then MvPolynomial.monomial (Finsupp.erase j d) c else 0 := by
  rw [show MvPolynomial.monomial d c = c • MvPolynomial.monomial d (1 : Sym.Lambda K) from by
      rw [MvPolynomial.smul_monomial, smul_eq_mul, mul_one], map_smul, lowerPart_monomial_one]
  rcases eq_or_ne (d j) i with h | h
  · rw [ite_eq_left h, ite_eq_left h, MvPolynomial.smul_monomial, smul_eq_mul, mul_one]
  · rw [ite_eq_right h, ite_eq_right h, smul_zero]

/-- Deleting the exponent of `y_{j+1}` and restoring it returns the monomial. -/
private theorem erase_add_single (j : ℕ) (d : ℕ →₀ ℕ) :
    Finsupp.erase j d + Finsupp.single j (d j) = d := by
  refine Finsupp.ext fun a => ?_
  rcases eq_or_ne a j with rfl | ha
  · rw [Finsupp.add_apply, Finsupp.erase_same, Finsupp.single_eq_same, zero_add]
  · rw [Finsupp.add_apply, Finsupp.erase_ne ha, Finsupp.single_eq_of_ne ha, add_zero]

/-- Above the exponents occurring on the support there is no coefficient. -/
theorem lowerPart_eq_zero_of_lt {j i : ℕ} {W : Sweep.Total K}
    (h : ∀ d ∈ W.support, d j < i) : lowerPart K j i W = 0 := by
  classical
  have hWs : lowerPart K j i W = ∑ d ∈ W.support,
      lowerPart K j i (MvPolynomial.monomial d (MvPolynomial.coeff d W)) := by
    conv_lhs => rw [W.as_sum]
    rw [map_sum]
  rw [hWs]
  exact Finset.sum_eq_zero fun d hd => by
    rw [lowerPart_monomial, ite_eq_right (Nat.ne_of_lt (h d hd))]

/-- **The expansion of an element of `V_*` in powers of `y_{j+1}`**: once the exponent of `y_{j+1}`
is bounded by `D` on the support, the element is `∑_{i ≤ D}(lowerPart_i F)y_{j+1}^i`. -/
theorem eq_sum_lowerPart_mul_pow (j : ℕ) (W : Sweep.Total K) {D : ℕ}
    (hD : ∀ d ∈ W.support, d j ≤ D) :
    W = ∑ i ∈ Finset.range (D + 1),
      lowerPart K j i W * (MvPolynomial.X j : Sweep.Total K) ^ i := by
  classical
  have hterm : ∀ d ∈ W.support, MvPolynomial.monomial d (MvPolynomial.coeff d W)
      = ∑ i ∈ Finset.range (D + 1),
        lowerPart K j i (MvPolynomial.monomial d (MvPolynomial.coeff d W))
          * (MvPolynomial.X j : Sweep.Total K) ^ i := by
    intro d hd
    rw [Finset.sum_eq_single_of_mem (d j) (Finset.mem_range.2 (Nat.lt_succ_of_le (hD d hd)))
      fun i _ hi => by rw [lowerPart_monomial, ite_eq_right (Ne.symm hi), zero_mul],
      lowerPart_monomial, ite_eq_left rfl, MvPolynomial.X_pow_eq_monomial,
      MvPolynomial.monomial_mul, mul_one, erase_add_single]
  calc W = ∑ d ∈ W.support, MvPolynomial.monomial d (MvPolynomial.coeff d W) := W.as_sum
    _ = ∑ d ∈ W.support, ∑ i ∈ Finset.range (D + 1),
          lowerPart K j i (MvPolynomial.monomial d (MvPolynomial.coeff d W))
            * (MvPolynomial.X j : Sweep.Total K) ^ i := Finset.sum_congr rfl hterm
    _ = ∑ i ∈ Finset.range (D + 1), ∑ d ∈ W.support,
          lowerPart K j i (MvPolynomial.monomial d (MvPolynomial.coeff d W))
            * (MvPolynomial.X j : Sweep.Total K) ^ i := Finset.sum_comm
    _ = ∑ i ∈ Finset.range (D + 1),
          lowerPart K j i W * (MvPolynomial.X j : Sweep.Total K) ^ i :=
        Finset.sum_congr rfl fun i _ => by
          rw [← Finset.sum_mul, ← map_sum, ← W.as_sum]

/-- Every element of `V_*` has its exponent of `y_{j+1}` bounded on its support, so the expansion
above is available for it. -/
theorem exists_eq_sum_lowerPart_mul_pow (j : ℕ) (W : Sweep.Total K) :
    ∃ D : ℕ, W = ∑ i ∈ Finset.range (D + 1),
      lowerPart K j i W * (MvPolynomial.X j : Sweep.Total K) ^ i :=
  ⟨W.support.sup fun d => d j,
    eq_sum_lowerPart_mul_pow j W fun _ hd => Finset.le_sup (f := fun d : ℕ →₀ ℕ => d j) hd⟩

/-- **The coefficients of the expansion of a member of `V_{k}` lie in `V_{k-1}`**: deleting the
exponent of `y_k` from a monomial of `V_k` leaves a monomial of `V_{k-1}`. -/
theorem lowerPart_mem_piece {j i : ℕ} {W : Sweep.Total K} (hW : W ∈ Sweep.piece K (j + 1)) :
    lowerPart K j i W ∈ Sweep.piece K j := by
  classical
  have hvars : ∀ a : ℕ, ∀ d ∈ W.support, a ∈ d.support → a < j + 1 := by
    intro a d hd ha
    rw [Sweep.piece, MvPolynomial.mem_supported] at hW
    exact Set.mem_Iio.1 (hW ((MvPolynomial.mem_vars_iff_mem_support a).2 ⟨d, hd, ha⟩))
  have hWs : lowerPart K j i W = ∑ d ∈ W.support,
      lowerPart K j i (MvPolynomial.monomial d (MvPolynomial.coeff d W)) := by
    conv_lhs => rw [W.as_sum]
    rw [map_sum]
  rw [hWs]
  refine sum_mem fun d hd => ?_
  rw [lowerPart_monomial]
  rcases eq_or_ne (d j) i with h | h
  · rw [ite_eq_left h, Sweep.piece, MvPolynomial.mem_supported,
      MvPolynomial.vars_monomial (MvPolynomial.mem_support_iff.1 hd)]
    intro a ha
    rw [Finset.mem_coe] at ha
    have hane : a ≠ j := by
      intro hj
      rw [hj] at ha
      exact absurd (Finsupp.erase_same (a := j) (f := d)) (Finsupp.mem_support_iff.1 ha)
    have had : a ∈ d.support := by
      have h' := Finsupp.mem_support_iff.1 ha
      rw [Finsupp.erase_ne hane] at h'
      exact Finsupp.mem_support_iff.2 h'
    exact Set.mem_Iio.2 (by have := hvars a d hd had; omega)
  · rw [ite_eq_right h]
    exact zero_mem _

/-- **The expansion coefficient of a single term**: for `F ∈ V_{k-1}`, free of `y_k`, the
coefficient of `y_k^i` in `Fy_k^{i'}` is `F` when `i' = i` and `0` otherwise. -/
theorem lowerPart_mul_pow_of_mem_piece {j : ℕ} {F : Sweep.Total K} (hF : F ∈ Sweep.piece K j)
    (i i' : ℕ) :
    lowerPart K j i (F * (MvPolynomial.X j : Sweep.Total K) ^ i')
      = if i' = i then F else 0 := by
  classical
  have hzero : ∀ d ∈ F.support, d j = 0 := by
    intro d hd
    by_contra h
    rw [Sweep.piece, MvPolynomial.mem_supported] at hF
    exact absurd (hF ((MvPolynomial.mem_vars_iff_mem_support j).2
      ⟨d, MvPolynomial.mem_support_iff.2 (MvPolynomial.mem_support_iff.1 hd),
        Finsupp.mem_support_iff.2 h⟩)) (by simp)
  have hexp : ∀ d ∈ F.support,
      lowerPart K j i (MvPolynomial.monomial d (MvPolynomial.coeff d F)
          * (MvPolynomial.X j : Sweep.Total K) ^ i')
        = if i' = i then MvPolynomial.monomial d (MvPolynomial.coeff d F) else 0 := by
    intro d hd
    have hval : (d + Finsupp.single j i') j = i' := by
      rw [Finsupp.add_apply, hzero d hd, Finsupp.single_eq_same, zero_add]
    have herase : Finsupp.erase j (d + Finsupp.single j i') = d := by
      refine Finsupp.ext fun a => ?_
      rcases eq_or_ne a j with rfl | ha
      · rw [Finsupp.erase_same, hzero d hd]
      · rw [Finsupp.erase_ne ha, Finsupp.add_apply, Finsupp.single_eq_of_ne ha, add_zero]
    rw [MvPolynomial.X_pow_eq_monomial, MvPolynomial.monomial_mul, mul_one, lowerPart_monomial,
      hval, herase]
  by_cases hii : i' = i
  · conv_lhs => rw [F.as_sum]
    rw [Finset.sum_mul, map_sum, ite_eq_left hii]
    refine Eq.trans (Finset.sum_congr rfl fun d hd => ?_) F.as_sum.symm
    rw [hexp d hd, ite_eq_left hii]
  · conv_lhs => rw [F.as_sum]
    rw [Finset.sum_mul, map_sum, ite_eq_right hii]
    exact Finset.sum_eq_zero fun d hd => by rw [hexp d hd, ite_eq_right hii]

/-- **The coefficients of an expansion over `V_{k-1}` are the `lowerPart` coefficients**, so the
expansion in powers of `y_k` over `V_{k-1}` is unique. -/
theorem lowerPart_sum_mul_pow {j i : ℕ} {t : Finset ℕ} {F : ℕ → Sweep.Total K}
    (hF : ∀ i' ∈ t, F i' ∈ Sweep.piece K j) :
    lowerPart K j i (∑ i' ∈ t, F i' * (MvPolynomial.X j : Sweep.Total K) ^ i')
      = if i ∈ t then F i else 0 := by
  classical
  rw [map_sum, Finset.sum_congr rfl fun i' hi' => lowerPart_mul_pow_of_mem_piece (hF i' hi') i i',
    Finset.sum_ite_eq' t i F]

end LowerPart

/-! ### Comparing two maps out of the total space -/

section Ext

variable {K : Type*} [CommRing K]

/-- Two ring homomorphisms out of the total space agree as soon as they agree on the scalars of
`𝕜`, on the power sums and on the auxiliary variables: those three families generate
`V_* = 𝕜[y][Λ]` as a ring. -/
theorem total_ringHom_ext {B : Type*} [CommRing B] {f g : Sweep.Total K →+* B}
    (hC : ∀ a : K, f (MvPolynomial.C (MvPolynomial.C a : Sym.Lambda K))
      = g (MvPolynomial.C (MvPolynomial.C a : Sym.Lambda K)))
    (hp : ∀ r : ℕ, f (MvPolynomial.C (Sym.powerSum K (r + 1)))
      = g (MvPolynomial.C (Sym.powerSum K (r + 1))))
    (hX : ∀ j : ℕ, f (MvPolynomial.X j : Sweep.Total K) = g (MvPolynomial.X j)) : f = g := by
  have hp' : ∀ r : ℕ, f (MvPolynomial.C (MvPolynomial.X r : Sym.Lambda K))
      = g (MvPolynomial.C (MvPolynomial.X r : Sym.Lambda K)) := fun r => by
    have h := hp r
    rwa [Sym.powerSum, Nat.add_sub_cancel] at h
  refine MvPolynomial.ringHom_ext (fun c => RingHom.congr_fun (MvPolynomial.ringHom_ext
    (f := f.comp (MvPolynomial.C : Sym.Lambda K →+* Sweep.Total K))
    (g := g.comp (MvPolynomial.C : Sym.Lambda K →+* Sweep.Total K)) hC hp') c) hX

end Ext

/-! ### Subtracting the letter `y_k` -/

section AddLetterNeg

variable {K : Type*} [CommRing K]

/-- **Subtracting the letter `y_i`**, the inverse of `HJO.Sweep.addLetter`: the `𝕜[y]`-algebra
endomorphism with `p_r ↦ p_r - y_i^r`, the plethystic substitution `F ↦ F[X - y_i]`.

The letter is genuine, not the virtual `(q-1)y_i` of `HJO.Sweep.qshiftNeg`; the two differ already
on `p_1`. This is the substitution that turns Carlsson and Mellit's display before their equation
(4.16) back into the expansion the equation reads, and the composite
`HJO.Dyck.addLetterNeg_addLetter` is what makes it the inverse. -/
noncomputable def addLetterNeg (K : Type*) [CommRing K] (i : ℕ) :
    Sweep.Total K →ₐ[K] Sweep.Total K :=
  MvPolynomial.aevalTower
    (MvPolynomial.aeval fun j : ℕ =>
      (MvPolynomial.C (MvPolynomial.X j) - Sweep.auxVar i ^ (j + 1) : Sweep.Total K))
    MvPolynomial.X

/-- The defining value on the alphabet: `p_{r+1} ↦ p_{r+1} - y_i^{r+1}`. -/
theorem addLetterNeg_powerSum (i r : ℕ) :
    addLetterNeg K i (MvPolynomial.C (Sym.powerSum K (r + 1)))
      = MvPolynomial.C (Sym.powerSum K (r + 1)) - Sweep.auxVar i ^ (r + 1) := by
  simp [addLetterNeg, Sym.powerSum]

/-- Subtracting a letter fixes every auxiliary variable. -/
@[simp]
theorem addLetterNeg_auxVar (i j : ℕ) :
    addLetterNeg K i (MvPolynomial.X j : Sweep.Total K) = MvPolynomial.X j := by
  simp [addLetterNeg]

/-- **Subtracting the letter undoes adding it.** Both composites are ring homomorphisms out of the
total space and they agree on the three generating families. -/
theorem addLetterNeg_addLetter (i : ℕ) (F : Sweep.Total K) :
    addLetterNeg K i (Sweep.addLetter K i F) = F := by
  have h : ((addLetterNeg K i).toRingHom.comp (Sweep.addLetter K i).toRingHom)
      = RingHom.id (Sweep.Total K) := by
    refine total_ringHom_ext (fun a => ?_) (fun r => ?_) fun j => ?_
    · simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, RingHom.id_apply,
        show (MvPolynomial.C (MvPolynomial.C a : Sym.Lambda K) : Sweep.Total K)
          = algebraMap K (Sweep.Total K) a from rfl, AlgHom.commutes, AlgHom.commutes]
    · simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, RingHom.id_apply]
      rw [Sweep.addLetter_powerSum, map_add, addLetterNeg_powerSum, map_pow, Sweep.auxVar,
        addLetterNeg_auxVar, ← Sweep.auxVar, sub_add_cancel]
    · simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, RingHom.id_apply]
      rw [Sweep.addLetter_auxVar, addLetterNeg_auxVar]
  exact RingHom.congr_fun h F

end AddLetterNeg

/-! ### The two substitutions of Carlsson and Mellit's (4.16) -/

section ThetaShift

variable {K : Type*} [Field K]

/-- **`θ_k` turns the virtual subtraction into the genuine one**: `θ_k(τ^-_{k,i}(F))` is
`θ_k(F)[X - y_i]`.

Both composites send `p_{r+1}` to `(q^{r+1}-1)(p_{r+1} - y_i^{r+1})` — on the left because
`τ^-_{k,i}` subtracts `(q^{r+1}-1)y_i^{r+1}` and `θ_k` then scales the whole thing, on the right
because `θ_k` scales `p_{r+1}` and the genuine subtraction removes `y_i^{r+1}` from the scaled
letter. This is Carlsson and Mellit's substitution of `X/(q-1) - y_k` for `X`, performed on `V_*`
where it needs no inverse of `θ_k`: the identity it is applied to already has `θ_k` on it. -/
theorem addLetterNeg_theta (q : K) (i : ℕ) (F : Sweep.Total K) :
    addLetterNeg K i (Sweep.theta q F) = Sweep.theta q (Sweep.qshiftNeg q i F) := by
  have h : ((addLetterNeg K i).toRingHom.comp (Sweep.theta q).toRingHom)
      = (Sweep.theta q).toRingHom.comp (Sweep.qshiftNeg q i).toRingHom := by
    refine total_ringHom_ext (fun a => ?_) (fun r => ?_) fun j => ?_
    · simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
        show (MvPolynomial.C (MvPolynomial.C a : Sym.Lambda K) : Sweep.Total K)
          = algebraMap K (Sweep.Total K) a from rfl, AlgHom.commutes]
    · have hscal : (Sweep.scal (q ^ (r + 1) - 1) : Sweep.Total K)
          = algebraMap K (Sweep.Total K) (q ^ (r + 1) - 1) := rfl
      have hav : Sweep.theta q (Sweep.auxVar i : Sweep.Total K) = Sweep.auxVar i := by
        rw [Sweep.auxVar, Sweep.theta_auxVar]
      have hL : addLetterNeg K i (Sweep.theta q (MvPolynomial.C (Sym.powerSum K (r + 1))))
          = algebraMap K (Sweep.Total K) (q ^ (r + 1) - 1)
            * (MvPolynomial.C (Sym.powerSum K (r + 1)) - Sweep.auxVar i ^ (r + 1)) := by
        rw [Sweep.theta_powerSum, map_mul, AlgHom.commutes, addLetterNeg_powerSum]
      have hR : Sweep.theta q (Sweep.qshiftNeg q i (MvPolynomial.C (Sym.powerSum K (r + 1))))
          = algebraMap K (Sweep.Total K) (q ^ (r + 1) - 1)
              * MvPolynomial.C (Sym.powerSum K (r + 1))
            - algebraMap K (Sweep.Total K) (q ^ (r + 1) - 1) * Sweep.auxVar i ^ (r + 1) := by
        rw [Sweep.qshiftNeg_powerSum, map_sub, Sweep.theta_powerSum, map_mul, hscal,
          AlgHom.commutes, map_pow, hav]
      simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
      rw [hL, hR, mul_sub]
    · simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
      rw [Sweep.theta_auxVar, addLetterNeg_auxVar, Sweep.qshiftNeg_auxVar, Sweep.theta_auxVar]
  exact RingHom.congr_fun h F

end ThetaShift

/-! ### The realisation is injective on `V_k` at its own level -/

section Injective

variable {K : Type*} [CommRing K] {k : ℕ}
  {ι : Sweep.Total K →ₐ[K] Sym.AuxAlphabetSeries K k}

/-- **The realisation of a scalar of the polynomial ring at its own level is that scalar as a
constant series.** This is `HJO.Dyck.realise_auxToTotal` with the level of the realisation equal to
the number of auxiliary variables, so that no renaming appears. -/
theorem realise_auxToTotal_self (hι : IsAuxRealisation k ι) (r : MvPolynomial (Fin k) K) :
    ι (Sweep.auxToTotal K k r) = MvPowerSeries.C r := by
  have h : (ι.toRingHom.comp (Sweep.auxToTotal K k).toRingHom)
      = (MvPowerSeries.C : MvPolynomial (Fin k) K →+* Sym.AuxAlphabetSeries K k) := by
    refine MvPolynomial.ringHom_ext (fun a => ?_) fun i => ?_
    · have h2 : (algebraMap K (Sym.AuxAlphabetSeries K k) a)
          = MvPowerSeries.C (MvPolynomial.C a) := by
        rw [MvPowerSeries.algebraMap_apply, MvPolynomial.algebraMap_eq]
      simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
      rw [Sweep.auxToTotal_C, AlgHom.commutes, h2]
    · have haux : (MvPolynomial.X (i : ℕ) : Sweep.Total K) = Sweep.auxVar ((i : ℕ) + 1) := by
        rw [Sweep.auxVar, Nat.add_sub_cancel]
      simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
      rw [Sweep.auxToTotal_X, haux, hι.map_auxVar i]
  exact RingHom.congr_fun h r

/-- **The realisation restricted to `V_k` at its own level is the classical realisation over
`𝕜[y_1, …, y_k]`.** This is `HJO.Dyck.auxToFrac_realise_pieceLift` one level down, where the
coefficient ring already holds every auxiliary variable of `V_k`, so no inclusion of coefficient
rings is needed. -/
theorem realise_pieceLift_self (hι : IsAuxRealisation k ι)
    (f : Sym.Lambda (MvPolynomial (Fin k) K)) :
    ι (Sweep.pieceLift K k f) = PhiMul.realise (MvPolynomial (Fin k) K) f := by
  have h : (ι.toRingHom.comp (Sweep.pieceLift K k).toRingHom)
      = (PhiMul.realise (MvPolynomial (Fin k) K)).toRingHom := by
    refine MvPolynomial.ringHom_ext (fun r => ?_) fun n => ?_
    · have hR : PhiMul.realise (MvPolynomial (Fin k) K) (MvPolynomial.C r)
          = MvPowerSeries.C r := by
        rw [show (MvPolynomial.C r : Sym.Lambda (MvPolynomial (Fin k) K))
            = algebraMap (MvPolynomial (Fin k) K) _ r from rfl, AlgHom.commutes,
          MvPowerSeries.algebraMap_apply]
        simp
      simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Sweep.pieceLift_C,
        realise_auxToTotal_self hι, hR]
    · have hR : PhiMul.realise (MvPolynomial (Fin k) K) (MvPolynomial.X n)
          = PhiMul.alphabetPowerSum (MvPolynomial (Fin k) K) (n + 1) :=
        MvPolynomial.aeval_X _ n
      simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Sweep.pieceLift_X,
        hR]
      refine MvPowerSeries.ext fun α => ?_
      by_cases hα : ∃ i : ℕ, α = Finsupp.single i (n + 1)
      · obtain ⟨i, rfl⟩ := hα
        rw [hι.coeff_pow n i, PhiMul.coeff_alphabetPowerSum_single]
      · simp only [not_exists] at hα
        rw [hι.coeff_of_ne n α hα, PhiMul.coeff_alphabetPowerSum_of_ne _ _ _ hα]
  exact RingHom.congr_fun h f

/-- **The realisation with auxiliary variables is injective on `V_k`**, at the level `k` of `V_k`
itself and not only on `V_{k-1}`: this is `HJO.Dyck.realise_injective_on_piece` with the level of
the realisation matched to the piece, which is the form Carlsson and Mellit's (4.16) needs — the
identity it compares lives in `V_k`, not in `V_{k-1}`. -/
theorem realise_injective_on_piece_self [IsDomain K] [Algebra ℚ K] (hι : IsAuxRealisation k ι)
    {F : Sweep.Total K} (hF : F ∈ Sweep.piece K k) (h0 : ι F = 0) : F = 0 := by
  have : CharZero K := charZero_of_inj_zero fun m hm =>
    Nat.cast_eq_zero.1 ((algebraMap ℚ K).injective (by rw [map_natCast, hm, map_zero]))
  obtain ⟨f, rfl⟩ := Sweep.exists_pieceLift_eq hF
  have hf0 : f = 0 :=
    Sym.realisation_injective (PhiMul.isRealisation_realise (MvPolynomial (Fin k) K))
      (by rw [← realise_pieceLift_self hι, h0, map_zero])
  rw [hf0, map_zero]

end Injective

/-! ### The merged alphabet, realised -/

section MergedAlphabet

variable {K : Type*} [CommRing K] [IsDomain K] {m : ℕ}
  {ι : Sweep.Total K →ₐ[K] Sym.AuxAlphabetSeries K (m + 1)}

/-- **A scalar realised on the enlarged alphabet is a constant of the coefficient field.** -/
theorem realiseAddLetter_algebraMap (c : K) :
    realiseAddLetter K m ι (algebraMap K (Sweep.Total K) c)
      = MvPowerSeries.C (Sym.scalarFrac K c) := by
  rw [realiseAddLetter_apply, AlgHom.commutes, AlgHom.commutes,
    show (algebraMap K (Sym.AuxAlphabetSeries K (m + 1)) c)
      = MvPowerSeries.C (MvPolynomial.C c) from by
        rw [MvPowerSeries.algebraMap_apply, MvPolynomial.algebraMap_eq], auxToFrac_C]
  rfl

/-- **The power sum realised on the enlarged alphabet is the power sum of the merged alphabet**:
`ρ_{k+1}(p_{r+1})` realised is `∑_{b}z^{(k+1)}_{k+1+b}{}^{r+1}`, the monomialwise sum over all the
letters of the merged alphabet `y_{k+1}, x_1, x_2, …`.

This is `HJO.Dyck.realiseAddLetter_powerSum_mem` with the value in place of the membership: the
coefficients of `ρ_{k+1}(p_{r+1})` realised are `1` at each `x_i^{r+1}`, `y_{k+1}^{r+1}` at the
empty letter-monomial and `0` elsewhere, and those are the coefficients of the monomialwise sum. It
is the
alphabet that `HJO.Sym.one_sub_C_scalarFrac_mul_summableSum_zSwapCoeff` names `(1-q)(X + y_k)`
before the twist. -/
theorem realiseAddLetter_C_powerSum (hι : IsAuxRealisation (m + 1) ι) (r : ℕ) :
    realiseAddLetter K m ι (MvPolynomial.C (Sym.powerSum K (r + 1)))
      = Sym.summableSum fun b => Sym.zLetterSeries K m b ^ (r + 1) := by
  classical
  have hy : ι (Sweep.auxVar (m + 1) : Sweep.Total K)
      = MvPowerSeries.C (MvPolynomial.X (Fin.last m)) := by
    have h := hι.map_auxVar (Fin.last m)
    rwa [Fin.val_last] at h
  have hyF : Sym.auxToFrac K (m + 1) (MvPowerSeries.C (MvPolynomial.X (Fin.last m)))
      = MvPowerSeries.C (Sym.yFrac K (Fin.last m)) := auxToFrac_C _ _
  have hsplit : realiseAddLetter K m ι (MvPolynomial.C (Sym.powerSum K (r + 1)))
      = Sym.auxToFrac K (m + 1) (ι (MvPolynomial.C (Sym.powerSum K (r + 1))))
        + MvPowerSeries.C (Sym.yFrac K (Fin.last m) ^ (r + 1)) := by
    rw [realiseAddLetter_apply, Sweep.addLetter_powerSum, map_add, map_add, map_pow, map_pow, hy,
      hyF, map_pow]
  have hc0 : Sym.zLetterSeries K m 0 ^ (r + 1)
      = MvPowerSeries.C (Sym.yFrac K (Fin.last m) ^ (r + 1)) := by
    rw [Sym.zLetterSeries_zero, ← map_pow]
  have hcs : ∀ b : ℕ, Sym.zLetterSeries K m (b + 1) ^ (r + 1)
      = (MvPowerSeries.X b : Sym.AuxAlphabetSeriesFrac K (m + 1)) ^ (r + 1) := fun b => by
    rw [Sym.zLetterSeries_succ]
  refine MvPowerSeries.ext fun α => ?_
  rw [hsplit, map_add, Sym.coeff_auxToFrac, MvPowerSeries.coeff_C]
  by_cases hα : ∃ i, α = Finsupp.single i (r + 1)
  · obtain ⟨i, rfl⟩ := hα
    have hne : (Finsupp.single i (r + 1) : ℕ →₀ ℕ) ≠ 0 :=
      Finsupp.single_ne_zero.2 (Nat.succ_ne_zero r)
    have hcov : ∀ b : ℕ, MvPowerSeries.coeff (Finsupp.single i (r + 1))
        (Sym.zLetterSeries K m b ^ (r + 1)) ≠ 0 → b ∈ ({0, i + 1} : Finset ℕ) := by
      intro b hb
      cases b with
      | zero => exact Finset.mem_insert_self _ _
      | succ b =>
        rw [hcs b, MvPowerSeries.coeff_X_pow] at hb
        refine Finset.mem_insert_of_mem (Finset.mem_singleton.2 ?_)
        by_cases hbi : (Finsupp.single i (r + 1) : ℕ →₀ ℕ) = Finsupp.single b (r + 1)
        · rw [Finsupp.single_left_injective (Nat.succ_ne_zero r) hbi]
        · exact absurd (ite_eq_right hbi) hb
    rw [hι.coeff_pow r i, map_one, ite_eq_right hne, add_zero,
      Sym.coeff_summableSum_eq_sum hcov, Finset.sum_pair (Nat.succ_ne_zero i).symm,
      hc0, hcs i, MvPowerSeries.coeff_C, ite_eq_right hne, MvPowerSeries.coeff_X_pow,
      ite_eq_left rfl, zero_add]
  · simp only [not_exists] at hα
    have hcov : ∀ b : ℕ,
        MvPowerSeries.coeff α (Sym.zLetterSeries K m b ^ (r + 1)) ≠ 0 →
          b ∈ ({0} : Finset ℕ) := by
      intro b hb
      cases b with
      | zero => exact Finset.mem_singleton_self _
      | succ b =>
        rw [hcs b, MvPowerSeries.coeff_X_pow, ite_eq_right (hα b)] at hb
        exact absurd rfl hb
    rw [hι.coeff_of_ne r α hα, map_zero, zero_add, Sym.coeff_summableSum_eq_sum hcov,
      Finset.sum_singleton, hc0, MvPowerSeries.coeff_C]

end MergedAlphabet

/-! ### The alphabet `(q-1)(X + y_k)`, and `HJO.Sym.plethNegate_completeHomog` on it -/

section Pleth

variable {K : Type*} [CommRing K] [IsDomain K] {m : ℕ}
  {ι : Sweep.Total K →ₐ[K] Sym.AuxAlphabetSeries K (m + 1)}

/-- **The alphabet `(q-1)(X + y_k)`, realised in `P°_{k+1}`**: `f ↦ f[(q-1)(X + y_k)]`, which is
`HJO.Sweep.theta` followed by `HJO.Sweep.addLetter` and the realisation. It is the negative of the
alphabet `(1-q)(X + y_k)` of `HJO.Sym.one_sub_C_scalarFrac_mul_summableSum_zSwapCoeff`, which is
what `HJO.Sym.plethNegate_completeHomog` turns into the sign and the exchange of the two
families. -/
noncomputable def realiseTheta (q : K) (m : ℕ)
    (ι : Sweep.Total K →ₐ[K] Sym.AuxAlphabetSeries K (m + 1)) :
    Sym.Lambda K →+* Sym.AuxAlphabetSeriesFrac K (m + 1) :=
  (realiseAddLetter K m ι).comp
    ((Sweep.theta q).toRingHom.comp (MvPolynomial.C : Sym.Lambda K →+* Sweep.Total K))

theorem realiseTheta_apply (q : K) (f : Sym.Lambda K) :
    realiseTheta q m ι f = realiseAddLetter K m ι (Sweep.theta q (MvPolynomial.C f)) :=
  rfl

omit [IsDomain K] in
/-- The scalar `q^n - 1` of `HJO.Sweep.theta`, read in the coefficient field. -/
private theorem C_scalarFrac_pow_sub_one {k : ℕ} (a : K) (n : ℕ) :
    (MvPowerSeries.C (Sym.scalarFrac K (a ^ n - 1)) : Sym.AuxAlphabetSeriesFrac K k)
      = MvPowerSeries.C (Sym.scalarFrac K a) ^ n - 1 := by
  simp only [Sym.scalarFrac, map_sub, map_one, map_pow]

/-- **The power sum on the alphabet `(q-1)(X + y_k)`**: `p_{r+1} ↦ (q^{r+1}-1)∑_bz_b^{r+1}`, the
scalar being the one `HJO.Sweep.theta` prescribes and the sum the power sum of the merged
alphabet. -/
theorem realiseTheta_powerSum (hι : IsAuxRealisation (m + 1) ι) (q : K) (r : ℕ) :
    realiseTheta q m ι (Sym.powerSum K (r + 1))
      = (MvPowerSeries.C (Sym.scalarFrac K q) ^ (r + 1) - 1)
        * Sym.summableSum fun b => Sym.zLetterSeries K m b ^ (r + 1) := by
  rw [realiseTheta_apply, Sweep.theta_powerSum, map_mul, realiseAddLetter_algebraMap,
    realiseAddLetter_C_powerSum hι, C_scalarFrac_pow_sub_one]

/-- **`HJO.Sym.plethNegate_completeHomog` on the two alphabets of Carlsson and Mellit's
comparison**: a homomorphism sending `p_j` to `(1-q^j)∑_bz_b^j` sends `h_i` to `(-1)^i` times the
value of `e_i` on the alphabet `(q-1)(X + y_k)`.

This is `HJO.Sym.completeHomog_neg_scale_alphabet` at the scale `1`, the two alphabets
`(1-q)(X+y_k)` and `(q-1)(X+y_k)` differing exactly by a sign on every power sum. It is the
plethystic half of the comparison of Carlsson and Mellit's (4.15) with their (4.16). -/
theorem completeHomog_eq_realiseTheta_elemSymm [Algebra ℚ K] (hι : IsAuxRealisation (m + 1) ι)
    (q : K) {Λ : Sym.Lambda K →+* Sym.AuxAlphabetSeriesFrac K (m + 1)}
    (hΛp : ∀ j : ℕ, 0 < j → Λ (Sym.powerSum K j)
      = (1 - MvPowerSeries.C (Sym.scalarFrac K q) ^ j)
          * Sym.summableSum fun b => Sym.zLetterSeries K m b ^ j) (i : ℕ) :
    Λ (Sym.completeHomog K i) = (-1) ^ i * realiseTheta q m ι (Sym.elemSymm K i) := by
  have hneg : ∀ j : ℕ, 0 < j → Λ (Sym.powerSum K j)
      = -((1 : Sym.AuxAlphabetSeriesFrac K (m + 1)) ^ j
        * realiseTheta q m ι (Sym.powerSum K j)) := by
    intro j hj
    obtain ⟨r, rfl⟩ : ∃ r, j = r + 1 := ⟨j - 1, by omega⟩
    rw [hΛp _ hj, realiseTheta_powerSum hι, one_pow, one_mul, ← neg_mul, neg_sub]
  have h := Sym.completeHomog_neg_scale_alphabet (realiseTheta q m ι) Λ 1 hneg i
  rwa [one_pow, mul_one] at h

end Pleth

/-! ### The prescribed product of auxiliary variables, on the total space -/

section AuxProd

variable {K : Type*} [CommRing K]

/-- **The product `y_1 ⋯ y_k` inside `V_k`**: the factor
`HJO.Dyck.unnormalisedCharSeries_eq_C_prod_X_mul` puts in front of `ν_{Id_k}(π)`, read on the total
space rather than in the coefficient field. -/
noncomputable def lowerAuxProd (K : Type*) [CommRing K] (k : ℕ) : Sweep.Total K :=
  ∏ l : Fin k, (MvPolynomial.X (l : ℕ) : Sweep.Total K)

theorem lowerAuxProd_eq_auxToTotal (K : Type*) [CommRing K] (k : ℕ) :
    lowerAuxProd K k = Sweep.auxToTotal K k (∏ l : Fin k, MvPolynomial.X l) := by
  rw [lowerAuxProd, map_prod]
  exact Finset.prod_congr rfl fun l _ => (Sweep.auxToTotal_X l).symm

theorem lowerAuxProd_mem_piece (K : Type*) [CommRing K] (k : ℕ) :
    lowerAuxProd K k ∈ Sweep.piece K k := by
  rw [lowerAuxProd_eq_auxToTotal]
  exact Sweep.auxToTotal_mem_piece _

/-- Splitting off the last auxiliary variable: `y_1 ⋯ y_{k+1} = (y_1 ⋯ y_k)y_{k+1}`. -/
theorem lowerAuxProd_succ (K : Type*) [CommRing K] (k : ℕ) :
    lowerAuxProd K (k + 1) = lowerAuxProd K k * (MvPolynomial.X k : Sweep.Total K) := by
  rw [lowerAuxProd, lowerAuxProd, Fin.prod_univ_castSucc, Fin.val_last]
  exact congrArg (· * (MvPolynomial.X k : Sweep.Total K))
    (Finset.prod_congr rfl fun l _ => by rw [Fin.val_castSucc])

/-- Neither adding nor subtracting the letter moves the prescribed product: both fix every
auxiliary variable. -/
theorem addLetterNeg_lowerAuxProd (i k : ℕ) :
    addLetterNeg K i (lowerAuxProd K k) = lowerAuxProd K k := by
  rw [lowerAuxProd, map_prod]
  exact Finset.prod_congr rfl fun l _ => addLetterNeg_auxVar i (l : ℕ)

end AuxProd

/-! ### Carlsson and Mellit's equation (4.16), on the total space -/

section ChiStepTwo

variable {K : Type*} [Field K] [Algebra ℚ K] {m N : ℕ} {x : Fin N → ℕ}
  {ι : Sweep.Total K →ₐ[K] Sym.AuxAlphabetSeries K (m + 1)}

omit [Algebra ℚ K] in
/-- The realised prescribed product is the constant `y_1 ⋯ y_{k-1}` of
`HJO.Dyck.unnormalisedCharSeries_lowerTuple`. -/
theorem realiseAddLetter_lowerAuxProd (hι : IsAuxRealisation (m + 1) ι) :
    realiseAddLetter K m ι (lowerAuxProd K m)
      = MvPowerSeries.C (Sym.auxFracCastSucc K m (lowerAuxScalar K m)) := by
  rw [lowerAuxProd_eq_auxToTotal, realiseAddLetter_apply, Sweep.addLetter_auxToTotal,
    auxToFrac_realise_auxToTotal hι, Sym.auxFracPoly_apply, lowerAuxScalar]

omit [Algebra ℚ K] in
/-- The realised last auxiliary variable is the distinguished letter of the merged alphabet. -/
theorem realiseAddLetter_X_last (hι : IsAuxRealisation (m + 1) ι) :
    realiseAddLetter K m ι (MvPolynomial.X m : Sweep.Total K)
      = MvPowerSeries.C (Sym.yFrac K (Fin.last m)) := by
  have hy := hι.map_auxVar (Fin.last m)
  rw [Fin.val_last] at hy
  rw [realiseAddLetter_apply, Sweep.addLetter_auxVar,
    show (MvPolynomial.X m : Sweep.Total K) = Sweep.auxVar (m + 1) from by
      rw [Sweep.auxVar, Nat.add_sub_cancel], hy]
  exact auxToFrac_C _ _

omit [Algebra ℚ K] in
/-- `ι_k` of the prescribed product at its own level. -/
private theorem realise_lowerAuxProd_succ (hι : IsAuxRealisation (m + 1) ι) :
    ι (lowerAuxProd K (m + 1)) = MvPowerSeries.C (∏ l : Fin (m + 1), MvPolynomial.X l) := by
  rw [lowerAuxProd_eq_auxToTotal, realise_auxToTotal_self hι]

/-- **Carlsson and Mellit's display before their equation (4.16), on the total space**: for
`π ∈ 𝔻_{k,N}` of level `k = m + 1` and `G` an `Id_k`-character of `π` whose freed characteristic
series expands as `∑_{i ≥ 1}y_k^ig_i(π)[X + y_k]`,

`y_1 ⋯ y_k·θ_k(G) = (q-1)^{|π|}∑_{i}y_k^i·g_i(π)[X + y_k]`.

This is Carlsson and Mellit's `χ_k(π)[(q-1)X] = (q-1)^{n-k}/(y_1⋯y_k)∑_iy_k^ig_i(π)[X+y_k]` with the
division written as a product and read on `V_k` rather than on its realisation: both sides lie in
`V_k`, and `HJO.Dyck.realise_injective_on_piece_self` transports the realised identity back. The
realised identity is `HJO.Dyck.unnormalisedCharSeries_eq_C_prod_X_mul` — which turns `ν_{Id_k}(π)`
into `χ'_{Id_k}(π)` — against `HJO.Dyck.IsSigmaCharacter` and the expansion. -/
theorem lowerAuxProd_mul_theta (q : K) (hx : IsPartialDyck (m + 1) N x)
    (hι : IsAuxRealisation (m + 1) ι) {G : Sweep.Total K} (hG : G ∈ Sweep.piece K (m + 1))
    (hchar : IsSigmaCharacter q (m + 1) ι x (identityTuple (m + 1)) G)
    {u : Finset ℕ} {g : ℕ → Sweep.Total K} (hg : ∀ i ∈ u, g i ∈ Sweep.piece K m)
    (hexp : Sym.auxToFrac K (m + 1)
        (unnormalisedCharSeries q (m + 1) x (identityTuple (m + 1)))
      = ∑ i ∈ u, MvPowerSeries.C (Sym.yFrac K (Fin.last m)) ^ i * realiseAddLetter K m ι (g i)) :
    lowerAuxProd K (m + 1) * Sweep.theta q G
      = ∑ i ∈ u, (algebraMap K (Sweep.Total K) ((q - 1) ^ (N - (m + 1)))
        * Sweep.addLetter K (m + 1) (g i)) * (MvPolynomial.X m : Sweep.Total K) ^ i := by
  have hXm : (MvPolynomial.X m : Sweep.Total K) ∈ Sweep.piece K (m + 1) :=
    Sweep.X_mem_piece (Nat.lt_succ_self m)
  have hscalmem : ∀ c : K, algebraMap K (Sweep.Total K) c ∈ Sweep.piece K (m + 1) := fun c =>
    (Sweep.piece K (m + 1)).algebraMap_mem (MvPolynomial.C c)
  have hiotaX : Sym.auxToFrac K (m + 1) (ι (MvPolynomial.X m : Sweep.Total K))
      = MvPowerSeries.C (Sym.yFrac K (Fin.last m)) := by
    rw [← Sweep.addLetter_auxVar (L := K) (m + 1) m, ← realiseAddLetter_apply,
      realiseAddLetter_X_last hι]
  have hiotaC : ∀ c : K, Sym.auxToFrac K (m + 1) (ι (algebraMap K (Sweep.Total K) c))
      = MvPowerSeries.C (Sym.scalarFrac K c) := fun c => by
    rw [← (Sweep.addLetter K (m + 1)).commutes c, ← realiseAddLetter_apply,
      realiseAddLetter_algebraMap]
  have hmemL : lowerAuxProd K (m + 1) * Sweep.theta q G ∈ Sweep.piece K (m + 1) :=
    mul_mem (lowerAuxProd_mem_piece K (m + 1)) (Sweep.theta_mem_piece q le_rfl hG)
  have hmemR : (∑ i ∈ u, (algebraMap K (Sweep.Total K) ((q - 1) ^ (N - (m + 1)))
      * Sweep.addLetter K (m + 1) (g i))
        * (MvPolynomial.X m : Sweep.Total K) ^ i) ∈ Sweep.piece K (m + 1) :=
    sum_mem fun i hi => mul_mem (mul_mem (hscalmem _)
      (Sweep.addLetter_mem_piece (by omega) (Nat.le_succ m) (hg i hi))) (pow_mem hXm i)
  refine sub_eq_zero.1 (realise_injective_on_piece_self hι (sub_mem hmemL hmemR) ?_)
  rw [map_sub, sub_eq_zero]
  refine Sym.auxToFrac_injective (m + 1) ?_
  have hnu := unnormalisedCharSeries_eq_C_prod_X_mul (q := q) (x := x)
    (σ := identityTuple (m + 1)) hx.le_length (identityTuple_lt (m + 1))
    (identityTuple_injective (m + 1))
  have hL : Sym.auxToFrac K (m + 1) (ι (lowerAuxProd K (m + 1) * Sweep.theta q G))
      = MvPowerSeries.C (Sym.scalarFrac K ((q - 1) ^ (N - (m + 1))))
        * ∑ i ∈ u, MvPowerSeries.C (Sym.yFrac K (Fin.last m)) ^ i
            * realiseAddLetter K m ι (g i) := by
    rw [map_mul, map_mul, realise_lowerAuxProd_succ hι, hchar, auxToFrac_smul, mul_left_comm,
      ← map_mul, ← hnu, hexp]
  have hR : Sym.auxToFrac K (m + 1) (ι (∑ i ∈ u,
        (algebraMap K (Sweep.Total K) ((q - 1) ^ (N - (m + 1)))
          * Sweep.addLetter K (m + 1) (g i))
          * (MvPolynomial.X m : Sweep.Total K) ^ i))
      = MvPowerSeries.C (Sym.scalarFrac K ((q - 1) ^ (N - (m + 1))))
        * ∑ i ∈ u, MvPowerSeries.C (Sym.yFrac K (Fin.last m)) ^ i
            * realiseAddLetter K m ι (g i) := by
    rw [map_sum, map_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [map_mul]
    rw [hiotaC, map_pow, map_pow, hiotaX, ← realiseAddLetter_apply]
    ring
  rw [hL, hR]

/-- **Carlsson and Mellit's equation (4.16), on the total space**: with the notation above,

`y_1 ⋯ y_k·θ_k(τ^-_{k,k}(G)) = (q-1)^{|π|}∑_{i}y_k^i·g_i(π)`.

This is `HJO.Dyck.lowerAuxProd_mul_theta` after the substitution `X ↦ X - y_k` of
`HJO.Dyck.addLetterNeg`, which is Carlsson and Mellit's substitution of `X/(q-1) - y_k` for `X`
performed where it needs no inverse: it turns `θ_k(G)` into `θ_k(τ^-_{k,k}(G))` by
`HJO.Dyck.addLetterNeg_theta` and strips the added letter off each `g_i(π)[X + y_k]` by
`HJO.Dyck.addLetterNeg_addLetter`, leaving an honest expansion of `θ_k(τ^-_{k,k}(G))` in powers of
`y_k` with coefficients in `V_{k-1}`. That is the expansion `HJO.Sweep.dminusCM` reads. -/
theorem lowerAuxProd_mul_theta_qshiftNeg (q : K) (hx : IsPartialDyck (m + 1) N x)
    (hι : IsAuxRealisation (m + 1) ι) {G : Sweep.Total K} (hG : G ∈ Sweep.piece K (m + 1))
    (hchar : IsSigmaCharacter q (m + 1) ι x (identityTuple (m + 1)) G)
    {u : Finset ℕ} {g : ℕ → Sweep.Total K} (hg : ∀ i ∈ u, g i ∈ Sweep.piece K m)
    (hexp : Sym.auxToFrac K (m + 1)
        (unnormalisedCharSeries q (m + 1) x (identityTuple (m + 1)))
      = ∑ i ∈ u, MvPowerSeries.C (Sym.yFrac K (Fin.last m)) ^ i * realiseAddLetter K m ι (g i)) :
    lowerAuxProd K (m + 1) * Sweep.theta q (Sweep.qshiftNeg q (m + 1) G)
      = ∑ i ∈ u, (algebraMap K (Sweep.Total K) ((q - 1) ^ (N - (m + 1))) * g i)
        * (MvPolynomial.X m : Sweep.Total K) ^ i := by
  have h := congrArg (addLetterNeg K (m + 1))
    (lowerAuxProd_mul_theta q hx hι hG hchar hg hexp)
  rw [map_mul, addLetterNeg_lowerAuxProd, addLetterNeg_theta, map_sum] at h
  refine h.trans (Finset.sum_congr rfl fun i _ => ?_)
  rw [map_mul, map_mul, AlgHom.commutes, addLetterNeg_addLetter]
  simp only [map_pow, addLetterNeg_auxVar]

/-- **The coefficients of Carlsson and Mellit's (4.16)**: the coefficient of `y_k^i` on the left is
`(q-1)^{|π|}g_i(π)`, read off by the uniqueness of the expansion in powers of `y_k` over
`V_{k-1}`. -/
theorem lowerPart_lowerAuxProd_mul_theta_qshiftNeg (q : K) (hx : IsPartialDyck (m + 1) N x)
    (hι : IsAuxRealisation (m + 1) ι) {G : Sweep.Total K} (hG : G ∈ Sweep.piece K (m + 1))
    (hchar : IsSigmaCharacter q (m + 1) ι x (identityTuple (m + 1)) G)
    {u : Finset ℕ} {g : ℕ → Sweep.Total K} (hg : ∀ i ∈ u, g i ∈ Sweep.piece K m)
    (hexp : Sym.auxToFrac K (m + 1)
        (unnormalisedCharSeries q (m + 1) x (identityTuple (m + 1)))
      = ∑ i ∈ u, MvPowerSeries.C (Sym.yFrac K (Fin.last m)) ^ i * realiseAddLetter K m ι (g i))
    (i : ℕ) :
    lowerPart K m i (lowerAuxProd K (m + 1) * Sweep.theta q (Sweep.qshiftNeg q (m + 1) G))
      = algebraMap K (Sweep.Total K) ((q - 1) ^ (N - (m + 1)))
        * (if i ∈ u then g i else 0) := by
  classical
  have hmem : ∀ i' ∈ u, algebraMap K (Sweep.Total K) ((q - 1) ^ (N - (m + 1))) * g i'
      ∈ Sweep.piece K m := fun i' hi' =>
    mul_mem ((Sweep.piece K m).algebraMap_mem (MvPolynomial.C _)) (hg i' hi')
  rw [lowerAuxProd_mul_theta_qshiftNeg q hx hι hG hchar hg hexp, lowerPart_sum_mul_pow hmem]
  by_cases hiu : i ∈ u
  · rw [ite_eq_left hiu, ite_eq_left hiu]
  · rw [ite_eq_right hiu, ite_eq_right hiu, mul_zero]

omit [Algebra ℚ K] in
/-- **The coefficient of `y_k^{i+1}` in `y_1 ⋯ y_k·θ_k(W)` is `y_1 ⋯ y_{k-1}·θ_k` of the coefficient
of `y_k^i` in `W`.** The factor `y_k` shifts the expansion by one, `θ_k` fixes every auxiliary
variable so it acts coefficientwise, and `y_1 ⋯ y_{k-1}` is free of `y_k`. -/
theorem lowerPart_succ_lowerAuxProd_succ_mul_theta (q : K) {W : Sweep.Total K}
    (hW : W ∈ Sweep.piece K (m + 1)) (j : ℕ) :
    lowerPart K m (j + 1) (lowerAuxProd K (m + 1) * Sweep.theta q W)
      = lowerAuxProd K m * Sweep.theta q (lowerPart K m j W) := by
  classical
  have hbound : ∀ d ∈ W.support, d m ≤ W.support.sup fun d => d m := fun _ hd =>
    Finset.le_sup (f := fun d : ℕ →₀ ℕ => d m) hd
  have hmemF : ∀ i : ℕ, lowerPart K m i W ∈ Sweep.piece K m := fun _ => lowerPart_mem_piece hW
  have hcoef : ∀ i : ℕ, lowerAuxProd K m * Sweep.theta q (lowerPart K m i W)
      ∈ Sweep.piece K m := fun i =>
    mul_mem (lowerAuxProd_mem_piece K m) (Sweep.theta_mem_piece q le_rfl (hmemF i))
  have hexpand : lowerAuxProd K (m + 1) * Sweep.theta q W
      = ∑ i ∈ Finset.range ((W.support.sup fun d => d m) + 1),
        (lowerAuxProd K m * Sweep.theta q (lowerPart K m i W))
          * (MvPolynomial.X m : Sweep.Total K) ^ (i + 1) := by
    conv_lhs => rw [eq_sum_lowerPart_mul_pow m W hbound]
    rw [map_sum, lowerAuxProd_succ, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_mul, map_pow, Sweep.theta_auxVar]
    ring
  have hterm : ∀ i : ℕ, lowerPart K m (j + 1)
      ((lowerAuxProd K m * Sweep.theta q (lowerPart K m i W))
        * (MvPolynomial.X m : Sweep.Total K) ^ (i + 1))
      = if i = j then lowerAuxProd K m * Sweep.theta q (lowerPart K m i W) else 0 := by
    intro i
    rw [lowerPart_mul_pow_of_mem_piece (hcoef i) (j + 1) (i + 1)]
    by_cases hij : i = j
    · rw [ite_eq_left (by omega : i + 1 = j + 1), ite_eq_left hij]
    · rw [ite_eq_right (by omega : ¬ i + 1 = j + 1), ite_eq_right hij]
  rw [hexpand, map_sum, Finset.sum_congr rfl fun i _ => hterm i,
    Finset.sum_ite_eq' (Finset.range ((W.support.sup fun d => d m) + 1)) j
      fun i => lowerAuxProd K m * Sweep.theta q (lowerPart K m i W)]
  by_cases hjD : j ∈ Finset.range ((W.support.sup fun d => d m) + 1)
  · rw [ite_eq_left hjD]
  · have hjD' : (W.support.sup fun d => d m) < j := by
      rw [Finset.mem_range] at hjD
      omega
    rw [ite_eq_right hjD, lowerPart_eq_zero_of_lt fun d hd => by
      have := hbound d hd
      omega, map_zero, mul_zero]

end ChiStepTwo

/-! ### The comparison of Carlsson and Mellit's (4.15) with their (4.16) -/

section Compare

variable {K : Type*} [Field K] [Algebra ℚ K] {m N : ℕ} {x : Fin N → ℕ}
  {ι : Sweep.Total K →ₐ[K] Sym.AuxAlphabetSeries K (m + 1)}

/-- **Carlsson and Mellit's comparison of (4.15) with (4.16), on the total space**: for
`π ∈ 𝔻_{k,N}` of level `k = m + 1` and `G` an `Id_k`-character of `π` whose freed characteristic
series expands as `∑_{i ≥ 1}y_k^ig_i(π)[X + y_k]`,

`(1-q)·y_1 ⋯ y_{k-1}·θ_{k-1}(d_-G) = (q-1)^{|π|+1}∑_i(-1)^ie_i[(q-1)X]·g_i(π)`.

The right-hand side is Carlsson and Mellit's `∑_{i ≥ 0}-h_{i+1}[-X](χ_k(π)[X-(q-1)y_k]|_{y_k^i})`
after `HJO.Sym.plethNegate_completeHomog` has replaced `h_{i+1}[-X]` by `(-1)^{i+1}e_{i+1}` and
after the normalisation of `HJO.Dyck.partialCharSeries`; the left-hand side is `HJO.Sweep.dminusCM`
read on the expansion of `HJO.Dyck.lowerAuxProd_mul_theta_qshiftNeg`. The index shift by one between
the two sums is the one between `d_-`'s pairing with `e_{j+1}` and Carlsson and Mellit's expansion
starting at `i = 1`, and it is what the hypothesis `0 ∉ u` pays for. -/
theorem one_sub_mul_lowerAuxProd_mul_theta_dminusCM (q : K) (hx : IsPartialDyck (m + 1) N x)
    (hι : IsAuxRealisation (m + 1) ι) {G : Sweep.Total K} (hG : G ∈ Sweep.piece K (m + 1))
    (hchar : IsSigmaCharacter q (m + 1) ι x (identityTuple (m + 1)) G)
    {u : Finset ℕ} {g : ℕ → Sweep.Total K} (hg : ∀ i ∈ u, g i ∈ Sweep.piece K m)
    (hu : (0 : ℕ) ∉ u)
    (hexp : Sym.auxToFrac K (m + 1)
        (unnormalisedCharSeries q (m + 1) x (identityTuple (m + 1)))
      = ∑ i ∈ u, MvPowerSeries.C (Sym.yFrac K (Fin.last m)) ^ i * realiseAddLetter K m ι (g i)) :
    algebraMap K (Sweep.Total K) (1 - q)
        * (lowerAuxProd K m * Sweep.theta q (Sweep.dminusCM q (m + 1) G))
      = algebraMap K (Sweep.Total K) ((q - 1) ^ (N - m))
        * ∑ i ∈ u, (-1 : Sweep.Total K) ^ i
            * Sweep.theta q (MvPolynomial.C (Sym.elemSymm K i)) * g i := by
  classical
  have hNm : N - m = N - (m + 1) + 1 := by have := hx.le_length; omega
  have hWmem : Sweep.qshiftNeg q (m + 1) G ∈ Sweep.piece K (m + 1) :=
    Sweep.qshiftNeg_mem_piece q (by omega) le_rfl hG
  set E := max ((Sweep.qshiftNeg q (m + 1) G).support.sup fun d => d m) (u.sup id) with hE
  have hEb : ∀ d ∈ (Sweep.qshiftNeg q (m + 1) G).support, d m ≤ E := fun d hd =>
    le_trans (Finset.le_sup (f := fun d : ℕ →₀ ℕ => d m) hd) (le_max_left _ _)
  have hdm : Sweep.dminusCM q (m + 1) G = ∑ j ∈ Finset.range (E + 1),
      (-1 : Sweep.Total K) ^ j * MvPolynomial.C (Sym.elemSymm K (j + 1))
        * lowerPart K m j (Sweep.qshiftNeg q (m + 1) G) :=
    dminusCM_eq_sum_of_qshiftNeg_eq q (fun _ _ => lowerPart_mem_piece hWmem)
      (eq_sum_lowerPart_mul_pow m _ hEb)
  have hC2 : ∀ j : ℕ, lowerAuxProd K m
      * Sweep.theta q (lowerPart K m j (Sweep.qshiftNeg q (m + 1) G))
      = algebraMap K (Sweep.Total K) ((q - 1) ^ (N - (m + 1)))
        * (if j + 1 ∈ u then g (j + 1) else 0) := fun j => by
    rw [← lowerPart_succ_lowerAuxProd_succ_mul_theta q hWmem j,
      lowerPart_lowerAuxProd_mul_theta_qshiftNeg q hx hι hG hchar hg hexp (j + 1)]
  obtain ⟨GG, hGG⟩ : ∃ GG : ℕ → Sweep.Total K, ∀ i, GG i = (-1 : Sweep.Total K) ^ i
      * Sweep.theta q (MvPolynomial.C (Sym.elemSymm K i)) * (if i ∈ u then g i else 0) :=
    ⟨_, fun _ => rfl⟩
  have hinj : ∀ a ∈ Finset.range (E + 1), ∀ b ∈ Finset.range (E + 1), a + 1 = b + 1 → a = b :=
    fun a _ b _ h => by omega
  have hsub : u ⊆ (Finset.range (E + 1)).image (· + 1) := by
    intro i hi
    have hi0 : i ≠ 0 := fun h => hu (h ▸ hi)
    have hiE : i ≤ E := le_trans (Finset.le_sup (f := id) hi) (le_max_right _ _)
    exact Finset.mem_image.2 ⟨i - 1, Finset.mem_range.2 (by omega), by omega⟩
  have hRHS : ∑ i ∈ u, (-1 : Sweep.Total K) ^ i
        * Sweep.theta q (MvPolynomial.C (Sym.elemSymm K i)) * g i
      = ∑ j ∈ Finset.range (E + 1), GG (j + 1) :=
    calc ∑ i ∈ u, (-1 : Sweep.Total K) ^ i
          * Sweep.theta q (MvPolynomial.C (Sym.elemSymm K i)) * g i
        = ∑ i ∈ u, GG i :=
          Finset.sum_congr rfl fun i hi => by rw [hGG, ite_eq_left hi]
      _ = ∑ i ∈ (Finset.range (E + 1)).image (· + 1), GG i :=
          Finset.sum_subset hsub fun i _ hiu => by rw [hGG, ite_eq_right hiu, mul_zero]
      _ = ∑ j ∈ Finset.range (E + 1), GG (j + 1) := Finset.sum_image hinj
  have hL : lowerAuxProd K m * Sweep.theta q (Sweep.dminusCM q (m + 1) G)
      = ∑ j ∈ Finset.range (E + 1), (-1 : Sweep.Total K) ^ j
          * Sweep.theta q (MvPolynomial.C (Sym.elemSymm K (j + 1)))
          * (algebraMap K (Sweep.Total K) ((q - 1) ^ (N - (m + 1)))
            * (if j + 1 ∈ u then g (j + 1) else 0)) := by
    rw [hdm, map_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_mul, map_mul, map_pow, map_neg, map_one, ← hC2 j]
    ring
  have hscal : algebraMap K (Sweep.Total K) (1 - q)
      * algebraMap K (Sweep.Total K) ((q - 1) ^ (N - (m + 1)))
      = -algebraMap K (Sweep.Total K) ((q - 1) ^ (N - m)) := by
    rw [← map_mul, hNm, pow_succ, ← map_neg]
    exact congrArg (algebraMap K (Sweep.Total K)) (by ring)
  rw [hL, hRHS, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [hGG (j + 1), pow_succ]
  linear_combination ((-1 : Sweep.Total K) ^ j
    * Sweep.theta q (MvPolynomial.C (Sym.elemSymm K (j + 1)))
    * (if j + 1 ∈ u then g (j + 1) else 0)) * hscal

end Compare

/-! ### `HJO.Dyck.isLoweringSum` -/

section Main

variable {K : Type*} [Field K] [Algebra ℚ K]

/-- **`θ_k` kills every elementary symmetric function at `q = 1`.** The virtual alphabet `(q-1)X`
is empty at `q = 1`, so `θ_k(p_r) = 0` for every `r ≥ 1`, and Newton's identity — which is the
*definition* of `HJO.Sym.elemSymm` — writes `e_{n+1}` as a combination of products each carrying a
power sum. -/
theorem theta_one_C_elemSymm (n : ℕ) :
    Sweep.theta (1 : K) (MvPolynomial.C (Sym.elemSymm K (n + 1))) = 0 := by
  have hzero : ∀ k : ℕ, Sweep.theta (1 : K) (MvPolynomial.C
      ((-1 : Sym.Lambda K) ^ k * Sym.powerSum K (k + 1) * Sym.elemSymm K (n - k))) = 0 :=
    fun k => by
      simp only [map_mul]
      rw [Sweep.theta_one_powerSum]
      ring
  conv_lhs => rw [Sym.elemSymm]
  rw [map_mul, map_mul, map_sum, map_sum, Finset.sum_eq_zero fun k _ => hzero k, mul_zero]

/-- **`HJO.Dyck.isLoweringSum` at `q = 1`.** There `θ_{k-1}(d_-G) = 0`, since `HJO.Sweep.dminusCM`
pairs the expansion coefficients against the elementary symmetric functions and
`HJO.Dyck.theta_one_C_elemSymm` kills each of them; and the scalar `(q-1)^{|π|}` on the right is
`0^{|π|}` with `|π| = N - k + 1 ≥ 1`, the length bound of `HJO.Dyck.IsPartialDyck`. So both sides
vanish, and Carlsson and Mellit's argument — which divides by `1-q` — is not needed at this one
value. -/
theorem isLoweringSum_one : IsLoweringSum (1 : K) := by
  intro m N x hx ι _ _ _ G hG _
  have hNm : N - m ≠ 0 := by have := hx.le_length; omega
  have hW : Sweep.qshiftNeg (1 : K) (m + 1) G ∈ Sweep.piece K (m + 1) :=
    Sweep.qshiftNeg_mem_piece 1 (by omega) le_rfl hG
  obtain ⟨D, hD⟩ := exists_eq_sum_lowerPart_mul_pow m (Sweep.qshiftNeg (1 : K) (m + 1) G)
  have hdm : Sweep.theta (1 : K) (Sweep.dminusCM (1 : K) (m + 1) G) = 0 := by
    rw [dminusCM_eq_sum_of_qshiftNeg_eq (1 : K) (fun _ _ => lowerPart_mem_piece hW) hD, map_sum]
    exact Finset.sum_eq_zero fun j _ => by
      rw [map_mul, map_mul, theta_one_C_elemSymm, mul_zero, zero_mul]
  rw [hdm, map_zero, Sym.insertFront_zero, sub_self, zero_pow hNm, zero_smul]

/-- **`HJO.Dyck.isLoweringSum` away from `q = 1`**: Carlsson and Mellit's own argument, whose
division by `1-q` is the cancellation performed here.

The two sides are compared after `Φ_{k-1}` and the inclusion `P_{k-1} ⊆ P°_k`, and then multiplied
by the unit `(1-q)y_1 ⋯ y_{k-1}` of `P°_k`. On the right that product is
`HJO.Dyck.exists_ringHom_one_sub_C_scalarFrac_mul_auxToFrac_insertFront_partialCharSeries`, Carlsson
and Mellit's display before (4.15); on the left `HJO.Dyck.insertFront_realisation` turns
`Φ_{k-1}(ι_{k-1}(-))` into `ι_k(ρ_k(-))`, so both sides are realisations of elements of `V_{k-1}`,
and the identity between those elements is `HJO.Dyck.one_sub_mul_lowerAuxProd_mul_theta_dminusCM` —
the comparison of (4.15) with (4.16) — after
`HJO.Dyck.completeHomog_eq_realiseTheta_elemSymm` has replaced `h_i[(1-q)(X+y_k)]` by
`(-1)^ie_i[(q-1)(X+y_k)]`. -/
theorem isLoweringSum_of_ne_one {q : K} (hq : q ≠ 1) : IsLoweringSum q := by
  intro m N x hx ι hι ι' hι' G hG hchar
  obtain ⟨u, g, hg, hu, hexp⟩ := exists_expansion_unnormalisedCharSeries_identityTuple q hx hι'
  obtain ⟨Λ, -, hΛp, hchistep⟩ :=
    exists_ringHom_one_sub_C_scalarFrac_mul_auxToFrac_insertFront_partialCharSeries
      (A := K) q (algebraMap K (Sym.AuxFrac K m)) hx hι' hg hu hexp
  -- the two factors that are cancelled are units of `P°_k`
  have hscalsub : (Sym.scalarFrac K (1 - q) : Sym.AuxFrac K (m + 1))
      = 1 - Sym.scalarFrac K q := by
    simp only [Sym.scalarFrac, map_sub, map_one]
  have hUne : (1 : Sym.AuxFrac K (m + 1)) - Sym.scalarFrac K q ≠ 0 := by
    rw [← hscalsub]
    exact scalarFrac_ne_zero (sub_ne_zero.2 fun h => hq h.symm)
  have hVne : Sym.auxFracCastSucc K m (lowerAuxScalar K m) ≠ 0 := fun h =>
    lowerAuxScalar_ne_zero K m (Sym.auxFracCastSucc_injective K m (h.trans (map_zero _).symm))
  have hUunit : IsUnit ((1 : Sym.AuxAlphabetSeriesFrac K (m + 1))
      - MvPowerSeries.C (Sym.scalarFrac K q)) := by
    have h := (isUnit_iff_ne_zero.2 hUne).map
      (MvPowerSeries.C : Sym.AuxFrac K (m + 1) →+* Sym.AuxAlphabetSeriesFrac K (m + 1))
    rwa [map_sub, map_one] at h
  have hVunit : IsUnit (MvPowerSeries.C (Sym.auxFracCastSucc K m (lowerAuxScalar K m))
      : Sym.AuxAlphabetSeriesFrac K (m + 1)) :=
    (isUnit_iff_ne_zero.2 hVne).map _
  -- the two sides as realisations of elements of `V_{k-1}`
  have hU : (1 : Sym.AuxAlphabetSeriesFrac K (m + 1)) - MvPowerSeries.C (Sym.scalarFrac K q)
      = realiseAddLetter K m ι' (algebraMap K (Sweep.Total K) (1 - q)) := by
    rw [realiseAddLetter_algebraMap, hscalsub, map_sub, map_one]
  have hV : (MvPowerSeries.C (Sym.auxFracCastSucc K m (lowerAuxScalar K m))
      : Sym.AuxAlphabetSeriesFrac K (m + 1)) = realiseAddLetter K m ι' (lowerAuxProd K m) :=
    (realiseAddLetter_lowerAuxProd hι').symm
  have hΛh : ∀ i : ℕ, Λ (Sym.completeHomog K i)
      = realiseAddLetter K m ι' ((-1 : Sweep.Total K) ^ i
        * Sweep.theta q (MvPolynomial.C (Sym.elemSymm K i))) := fun i => by
    rw [map_mul, map_pow, map_neg, map_one, ← realiseTheta_apply]
    exact completeHomog_eq_realiseTheta_elemSymm hι' q hΛp i
  have hmemθ : Sweep.theta q (Sweep.dminusCM q (m + 1) G) ∈ Sweep.piece K m :=
    Sweep.theta_mem_piece q le_rfl (Sweep.dminusCM_mem_piece q m hG)
  have hLHS : (1 - MvPowerSeries.C (Sym.scalarFrac K q))
        * MvPowerSeries.C (Sym.auxFracCastSucc K m (lowerAuxScalar K m))
        * realiseAddLetter K m ι' (Sweep.theta q (Sweep.dminusCM q (m + 1) G))
      = realiseAddLetter K m ι' (algebraMap K (Sweep.Total K) (1 - q)
          * (lowerAuxProd K m * Sweep.theta q (Sweep.dminusCM q (m + 1) G))) := by
    rw [map_mul, map_mul, hU, hV]
    ring
  have hRHS : realiseAddLetter K m ι' (algebraMap K (Sweep.Total K) ((q - 1) ^ (N - m))
        * ∑ i ∈ u, (-1 : Sweep.Total K) ^ i
            * Sweep.theta q (MvPolynomial.C (Sym.elemSymm K i)) * g i)
      = MvPowerSeries.C (Sym.scalarFrac K ((q - 1) ^ (N - m)))
        * ((1 - MvPowerSeries.C (Sym.scalarFrac K q))
          * (MvPowerSeries.C (Sym.auxFracCastSucc K m (lowerAuxScalar K m))
            * Sym.auxToFrac K (m + 1)
                (Sym.insertFront K m (partialCharSeries q m x (identityTuple m))))) := by
    rw [map_mul, realiseAddLetter_algebraMap, map_sum, hchistep]
    exact congrArg _ (Finset.sum_congr rfl fun i _ => by rw [map_mul, hΛh i])
  rw [← insertFront_partialCharSeries_identityTuple q hx]
  refine Sym.auxToFrac_injective (m + 1) ?_
  rw [insertFront_realisation hι hι' hmemθ, ← realiseAddLetter_apply, auxToFrac_smul]
  refine (hUunit.mul hVunit).mul_right_injective ?_
  dsimp only
  rw [hLHS, one_sub_mul_lowerAuxProd_mul_theta_dminusCM q hx hι' hG hchar hg hu hexp, hRHS]
  ring

/-- **The lowering-sum identity of Carlsson and Mellit's Section 4**: for `k = m + 1 ≥ 1`, a partial
Dyck path `π ∈ 𝔻_{k,N}`, realisations `ι_{k-1}` and `ι_k` with auxiliary variables and `G ∈ V_k` an
`Id_k`-character of `π`,

`Φ_{k-1}(ι_{k-1}(θ_{k-1}(d_-G))) = (q-1)^{|π|}∑_{r ≥ 0}z^{(k)}_{k+r}μ_r(π)`.

Carlsson and Mellit's argument is carried out away from `q = 1`
(`HJO.Dyck.isLoweringSum_of_ne_one`); at `q = 1` both sides vanish (`HJO.Dyck.isLoweringSum_one`),
which is what makes the statement true as stated, with no hypothesis on `q` — Carlsson and Mellit's
division by `1-q` is a cancellation of a unit here, and the one value it excludes is the one where
the identity is `0 = 0`. -/
@[hjo "lem_cm_lowering_sum"]
theorem isLoweringSum (q : K) : IsLoweringSum q := by
  rcases eq_or_ne q 1 with rfl | hq
  · exact isLoweringSum_one
  · exact isLoweringSum_of_ne_one hq

end Main

end HJO.Dyck

/-! ### The statements downstream of the lowering sum

`HJO/CarlssonMellit/CharWordPartial.lean` and
`HJO/Shuffle/SweepComputesLowering.lean` state `HJO.Dyck.isSigmaCharacter_dminusCM'`,
`HJO.Dyck.mem_piece_and_isSigmaCharacter_partialWordOp'`,
`HJO.Dyck.realisation_constantCoeff_markedWordOp'`, `HJO.Mellit.map_constantCoeff_markedWordOp'` and
`HJO.Mellit.sweepComputes` with `HJO.Dyck.IsLoweringSum` as an explicit hypothesis. That hypothesis
is now the theorem `HJO.Dyck.isLoweringSum`, so each of them is stated here with it discharged. -/

namespace HJO.Dyck

section Downstream

variable {K : Type*} [Field K] [Algebra ℚ K]

/-- **The lowering recursion.** For `k = m + 1 ≥ 1`, a partial Dyck path
`π ∈ 𝔻_{k,N}` and `G ∈ V_k` an `Id_k`-character of `π`, the element `d_-G` is an
`Id_{k-1}`-character of `π` read in `𝔻_{k-1,N}`.

This is `HJO.Dyck.isSigmaCharacter_dminusCM` with its hypothesis `hsum` discharged by
`HJO.Dyck.isLoweringSum`. -/
@[hjo "lem_cm_lowering"]
theorem isSigmaCharacter_dminusCM' (q : K) {m N : ℕ} {x : Fin N → ℕ}
    (hx : IsPartialDyck (m + 1) N x)
    {ι : Sweep.Total K →ₐ[K] Sym.AuxAlphabetSeries K m} (hι : IsAuxRealisation m ι)
    {ι' : Sweep.Total K →ₐ[K] Sym.AuxAlphabetSeries K (m + 1)}
    (hι' : IsAuxRealisation (m + 1) ι') {G : Sweep.Total K} (hG : G ∈ Sweep.piece K (m + 1))
    (hchar : IsSigmaCharacter q (m + 1) ι' x (identityTuple (m + 1)) G) :
    IsSigmaCharacter q m ι x (identityTuple m) (Sweep.dminusCM q (m + 1) G) :=
  isSigmaCharacter_dminusCM q hx hι hG (isLoweringSum q m N x hx ι hι ι' hι' G hG hchar)

/-- **`HJO.Dyck.mem_piece_and_isSigmaCharacter_partialWordOp'`.** For `π ∈ 𝔻_{k,N}` with step word
`w_k(π) = ε₁ ⋯ ε_M` the composite `d_{ε₁}(⋯ d_{ε_M}(1)⋯)` lies in `V_k` and is an `Id_k`-character
of `π`.

This is `HJO.Dyck.mem_piece_and_isSigmaCharacter_partialWordOp` with its hypothesis `hsum`
discharged. The hypothesis `q ≠ 0` is `HJO.Dyck.isSigmaCharacter_cmDPlus`'s. -/
@[hjo "lem_cm_char_word_partial"]
theorem mem_piece_and_isSigmaCharacter_partialWordOp' {q : K} (hq : q ≠ 0)
    (ι : ∀ l : ℕ, Sweep.Total K →ₐ[K] Sym.AuxAlphabetSeries K l)
    (hι : ∀ l : ℕ, IsAuxRealisation l (ι l)) {k N : ℕ} {x : Fin N → ℕ}
    (hx : IsPartialDyck k N x) :
    Sweep.partialWordOp q k (partialStepWord k x) 1 ∈ Sweep.piece K k ∧
      IsSigmaCharacter q k (ι k) x (identityTuple k)
        (Sweep.partialWordOp q k (partialStepWord k x) 1) :=
  mem_piece_and_isSigmaCharacter_partialWordOp hq (isLoweringSum q) ι hι hx

/-- **`HJO.Dyck.realisation_constantCoeff_markedWordOp'`**: `ι(Ξ_{π,∅}(1)) = χ(π)` for every square
Dyck path.

This is `HJO.Dyck.realisation_constantCoeff_markedWordOp` with its hypothesis `hsum` discharged.
The hypotheses `q ≠ 0` and `∀ r, IsUnit (q^{r+1}-1)` come from `HJO.Dyck.isSigmaCharacter_cmDPlus`
and `HJO.Dyck.auxZeroMap_eq_pathCharSeries_of_isSigmaCharacter`; both hold over the coefficient
field. -/
@[hjo "lem_cm_thm44"]
theorem realisation_constantCoeff_markedWordOp' [CharZero K] (q : K) (hq0 : q ≠ 0)
    (hq : ∀ r : ℕ, IsUnit (q ^ (r + 1) - 1)) {n : ℕ} {x : Fin n → ℕ} (hx : IsSquareDyck n x)
    {ι : Sym.Lambda K →ₐ[K] Sym.AlphabetSeries K} (hι : Sym.IsRealisation ι) :
    ι (MvPolynomial.constantCoeff (Sweep.markedWordOp q x ∅ 1)) = pathMarkedCharSeries q x ∅ :=
  realisation_constantCoeff_markedWordOp q hq0 hq hx hι (isLoweringSum q)

end Downstream

end HJO.Dyck

namespace HJO.Mellit

open ParkingFunctions Paths Sweep

variable {L : Type*} [Field L] [Algebra ℚ L] [CharZero L] {a b : ℕ}

/-- **`HJO.Mellit.map_constantCoeff_markedWordOp'`**: the marked word computes the marked
characteristic series, `ι(Ξ_{π,T}(1)) = χ(π, T)`.

This is `HJO.Mellit.map_constantCoeff_markedWordOp_of_isLoweringSum` with its hypothesis `hsum`
discharged by `HJO.Dyck.isLoweringSum`. The hypothesis `q ≠ 1` is **not** visible in the displayed
identity and cannot be dropped — at `q = 1` the left-hand side vanishes at every nonempty marking
while the right-hand side does not — and `q ≠ 0`, `∀ r, IsUnit (q^{r+1}-1)` are
`HJO.Dyck.isSigmaCharacter_cmDPlus`'s and
`HJO.Dyck.auxZeroMap_eq_pathCharSeries_of_isSigmaCharacter`'s; all three hold over the coefficient
field. -/
@[hjo "lem_cm_cor46"]
theorem map_constantCoeff_markedWordOp' (q : L) (hq0 : q ≠ 0) (hq1 : q ≠ 1)
    (hqu : ∀ r : ℕ, IsUnit (q ^ (r + 1) - 1))
    {ι : Sym.Lambda L →ₐ[L] Sym.AlphabetSeries L} (hι : Sym.IsRealisation ι) {n : ℕ}
    (x : Fin n → ℕ) (T : Finset (ℕ × ℕ)) (hx : Dyck.IsSquareDyck n x)
    (hT : T ⊆ Dyck.corner x) :
    ι (MvPolynomial.constantCoeff (markedWordOp q x T (1 : Total L)))
      = Dyck.pathMarkedCharSeries q x T :=
  map_constantCoeff_markedWordOp_of_isLoweringSum q hq0 hq1 hqu (Dyck.isLoweringSum q) hι x T hx hT

/-- **`HJO.Mellit.sweepComputes`**, the sweep leg of `HJO.Mellit.shuffle_of_three`, outright: the
sweep word of a path above the diagonal computes its sweep character.

This is `HJO.Mellit.sweepComputes_of_isLoweringSum` with its hypothesis `hsum` discharged by
`HJO.Dyck.isLoweringSum`. The three conditions on `q` are the ones that file records: `q ≠ 0` from
collecting the scalars of `HJO.Mellit.sweepOperator`, `q ≠ 1` from
`HJO.Mellit.map_constantCoeff_markedWordOp'` at a nonempty marking, and `∀ r, IsUnit (q^{r+1}-1)`
from `HJO.Dyck.auxZeroMap_eq_pathCharSeries_of_isSigmaCharacter`. All three hold over the ambient
coefficient field `ℚ(q,u)`, and `HJO.Mellit.shuffle_of_three`'s algebraic independence supplies
them. -/
@[hjo "lem_sweep_computes"]
theorem sweepComputes (q u : L) (hq0 : q ≠ 0) (hq1 : q ≠ 1)
    (hqu : ∀ r : ℕ, IsUnit (q ^ (r + 1) - 1)) :
    SweepComputes q u a b :=
  sweepComputes_of_isLoweringSum q u hq0 hq1 hqu (Dyck.isLoweringSum q)

end HJO.Mellit
