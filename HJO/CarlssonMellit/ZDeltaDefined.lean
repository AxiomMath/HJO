/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.CarlssonMellit.DiffDivides
public import HJO.CarlssonMellit.RunWeight
public import HJO.CarlssonMellit.ZDelta
public meta import HJO.Attr

/-! # The swapping operator on the merged alphabet is defined

`HJO.CarlssonMellit.ZDelta` defines `Δ_m` as the equation `HJO.Sym.IsZDelta` together with the
uniqueness of its solution, and leaves *existence* open: the divisor `z_{m+1} - z_m` has no constant
term, so nothing in the ambient ring performs the division. This file supplies existence on a graded
piece, through the explicit solution `HJO.Sym.zDeltaOn`, and with it the consequences that depend on
it: linearity over invariant coefficients, compatibility with sums, and the effect of the operator
on the two weights of a free run.

The route is a transport rather than the block decomposition. A member of `Z^{(k+1)}_d`
is a formal `𝕂(y₁, …, y_k)`-combination of the monomials of merged degree `d`, so its merged
coefficients are exactly the data of a power series in the merged alphabet over the *lower*
coefficient field: `HJO.Sym.zSeries` reads that power series off, `HJO.Sym.zOfSeries` builds the
member back from it, and `HJO.Sym.zSeriesHom` says the passage is a ring homomorphism. Under it the
equation of `HJO.Sym.IsZDelta` becomes a division by a difference of two honest power-series
variables in `MvPowerSeries (Option ℕ) (AuxFrac K k)`, and that division is
`HJO.Sym.isHomogeneous_and_eq_X_sub_X_mul_diffQuot` of `HJO.CarlssonMellit.DiffDivides` — the
same theorem that licenses `Δ_{x_r,x_{r+1}}`, now read at the letter type `Option ℕ`.

## Main definitions

* `HJO.Sym.zSeries`, `HJO.Sym.zOfSeries`: the merged coefficients of a series as a power series in
  the merged alphabet, and the member of `Z^{(k+1)}_d` with prescribed merged coefficients.
* `HJO.Sym.zSeriesHom`: the first of these as a ring homomorphism out of `Z^{(k+1)}`.

## Main results

* `HJO.Sym.exists_isZDelta_of_mem_zGraded`: existence on a graded piece. For `G ∈ Z^{(k+1)}_d` there
  is an `H ∈ Z^{(k+1)}_d` with `IsZDelta q r G H`; by `HJO.Sym.eq_of_isZDelta` it is the only one,
  so `Δ_m(G)` is defined on every graded piece.
* `HJO.Sym.zDelta`, `HJO.Sym.isZDelta_zDelta`: the value, chosen from that existence, and the
  equation it satisfies — so that the operator can be written as a function where the graded
  hypothesis is available.
* `HJO.Sym.isZDelta_mul_of_zSwap_eq`, `HJO.Sym.zDelta_mul_of_zSwap_eq`: linearity over coefficients
  invariant under `ŝ_m`, as a statement about the relation and as one about the value.
* `HJO.Sym.isZDelta_add`, `HJO.Sym.isZDelta_sum`: additivity, and the finite-sum case of
  `HJO.Sym.isZDelta_summableSum` — see the note below.
* `HJO.Sym.isZDelta_runWeight`.
* `HJO.Sym.zSwap_runWeight_add_runWeight`.

## Implementation notes

*The blockwise conjunct is not stated separately, and nothing is lost.* Existence may be stated
"in the situation of" the block decomposition
`MvPowerSeries.IsHomogeneous.existsUnique_eq_monomialwiseFinsum_monomial_mul`, adjoining to the
conclusion that the *blocks* of `Δ_m(G)` along the two moved letters satisfy the same equation in
the two-variable polynomial ring. That conjunct quantifies over the block family
that decomposition produces, and the reason to carry it is to hand the blocks to
`HJO.Sym.isZDelta_summableSum`. Here the identity is proved at the level of merged
coefficients, where it is blockwise already — the coefficient identity at `ρ z_m^i z_{m+1}^j`
involves only monomials with that same `ρ`, which is `HJO.Sym.zCoeff_zDelta_sub_zCoeff_zDelta` below
— and `HJO.Sym.isZDelta_summableSum` is proved from the additivity of the construction instead. So
the statements here are existence, membership and the equation, with the blockwise refinement
recorded as the coefficient identity it is.

*`HJO.Sym.isZDelta_summableSum` is not proved here, and `HJO.Sym.isZDelta_sum` is weaker than it.*
The lemma is stated for an arbitrary index set together with a monomialwise finiteness
hypothesis, so that a coefficient of the sum is a finite sum of coefficients. That notion of sum is
`MvPowerSeries.monomialwiseFinsum`, which this library has only inside
`HJO.CarlssonMellit.HomogeneousSplit` and not as a summation the graded pieces are stated with;
what is proved below is the `Finset`-indexed case, which is genuinely weaker. The general statement
is proved in `HJO.CarlssonMellit.ZDeltaSums`.

*`HJO.Sym.zDelta` is a function and `HJO.Sym.IsZDelta` remains the definition.* The
operator is partial, and `HJO.CarlssonMellit.ZDelta` records that faithfully as a relation.
What this file adds is that the relation is total on each `Z^{(k+1)}_d`, so a function may be
*derived* there by `Classical.choose`; `HJO.Sym.zDelta` is that derived function, and every
statement about it carries the graded hypothesis that justifies it. The definition keeps its
relational form.

*The letters are the offsets, as everywhere in this part of the library.* `HJO.Sym.zLetter r` is the
letter of the merged alphabet at offset `r` from the level `k + 1`, so the two letters `Δ_m` moves
at `m = k + 1 + r` are `HJO.Sym.zLetter r` and `HJO.Sym.zLetter (r + 1)`, distinct by
`HJO.Sym.zLetter_injective`, and no `ℕ`-subtraction appears.

*The hypothesis of the division is checked by a permutation identity.* What
`HJO.CarlssonMellit.DiffDivides` needs is that the numerator vanishes on substituting the upper
letter for the lower one. The numerator is
`(q-1)z_{m+1}G + (z_{m+1} - qz_m)ŝ_m(G)`; the substitution carries `ŝ_m(G)` and `G` to the same
series, because composing the collapse with the interchange is the collapse
(`HJO.Sym.collapseVar_comp_zSwapEquiv`), and the two scalar factors `(q-1)` and `(1-q)` then cancel.
This is the standard computation, done with `MvPowerSeries.rename` in place of an evaluation.

## References

E. Carlsson and A. Mellit, *A proof of the shuffle conjecture*,
J. Amer. Math. Soc. **31** (2018) 661--697, Section 4, where the divided difference is a fraction
and its existence is not discussed.
-/

@[expose] public section

namespace HJO.Sym

variable {K : Type*} [CommRing K] [IsDomain K] {k d : ℕ}
  {G H : AuxAlphabetSeriesFrac K (k + 1)}

/-! ### Renaming along a permutation of the letters -/

/-- Two renamings along equal maps of letters agree. The maps carry their own finite-fibre
hypotheses, which are propositions, so the two instances are interchangeable. -/
theorem rename_congr_fun {σ τ R : Type*} [CommSemiring R] {f g : σ → τ}
    [Filter.TendstoCofinite f] [Filter.TendstoCofinite g] (h : f = g) (p : MvPowerSeries σ R) :
    MvPowerSeries.rename f p = MvPowerSeries.rename g p := by
  subst h
  rfl

/-- **Renaming along a permutation reads a coefficient at the inverse image.** The fibres of a
permutation are singletons, so the sum defining a coefficient of the renamed series has one term. -/
theorem coeff_rename_perm {σ R : Type*} [CommSemiring R] (e : Equiv.Perm σ)
    (p : MvPowerSeries σ R) (ν : σ →₀ ℕ) :
    MvPowerSeries.coeff ν (MvPowerSeries.rename (e : σ → σ) p)
      = MvPowerSeries.coeff (Finsupp.equivMapDomain e.symm ν) p := by
  classical
  rw [MvPowerSeries.coeff_rename]
  refine Finset.sum_eq_single_of_mem (Finsupp.equivMapDomain e.symm ν) ?_ fun μ hμ hne => ?_
  · rw [Set.Finite.mem_toFinset]
    change Finsupp.mapDomain (e : σ → σ) (Finsupp.equivMapDomain e.symm ν) = ν
    rw [← Finsupp.equivMapDomain_eq_mapDomain, equivMapDomain_equivMapDomain_symm]
  · rw [Set.Finite.mem_toFinset] at hμ
    refine absurd ?_ hne
    change Finsupp.mapDomain (e : σ → σ) μ = ν at hμ
    rw [← Finsupp.equivMapDomain_eq_mapDomain] at hμ
    rw [← hμ, equivMapDomain_symm_equivMapDomain]

/-! ### The merged coefficients as a power series -/

/-- **The merged coefficients of a series, assembled into a power series in the merged alphabet**
`y_{k+1}, x₁, x₂, …` over the *lower* coefficient field `𝕂(y₁, …, y_k)`. On `Z^{(k+1)}` this loses
nothing — `HJO.Sym.eq_of_zCoeff_eq` — and it turns the distinguished letter `y_{k+1}`, which lives
in the coefficient field of `P°_{k+1}` and which no substitution there moves, into an honest
power-series variable that every substitution moves. -/
noncomputable def zSeries (K : Type*) [CommRing K] [IsDomain K] (k : ℕ)
    (G : AuxAlphabetSeriesFrac K (k + 1)) : MvPowerSeries (Option ℕ) (AuxFrac K k) :=
  fun ν => zCoeff K k G ν

@[simp]
theorem coeff_zSeries (G : AuxAlphabetSeriesFrac K (k + 1)) (ν : Option ℕ →₀ ℕ) :
    MvPowerSeries.coeff ν (zSeries K k G) = zCoeff K k G ν :=
  rfl

/-- A member of `Z^{(k+1)}` is determined by the power series of its merged coefficients. -/
theorem eq_of_zSeries_eq (hG : G ∈ zRing K k) (hH : H ∈ zRing K k)
    (h : zSeries K k G = zSeries K k H) : G = H :=
  eq_of_zCoeff_eq (coeff_mem_range_yFracEval_of_mem_zRing hG)
    (coeff_mem_range_yFracEval_of_mem_zRing hH) fun ν => by
      rw [← coeff_zSeries G ν, ← coeff_zSeries H ν, h]

/-- The merged coefficients of a merged monomial: the monomial with the same exponent vector. -/
@[simp]
theorem zSeries_zMonomial (ν : Option ℕ →₀ ℕ) (c : AuxFrac K k) :
    zSeries K k (zMonomial K k ν c) = MvPowerSeries.monomial ν c := by
  classical
  refine MvPowerSeries.ext fun μ => ?_
  rw [coeff_zSeries, zCoeff_zMonomial, MvPowerSeries.coeff_monomial]

/-- The merged coefficients of a constant of the lower coefficient field: the constant itself. -/
@[simp]
theorem zSeries_C_auxFracCastSucc (c : AuxFrac K k) :
    zSeries K k (MvPowerSeries.C (auxFracCastSucc K k c)) = MvPowerSeries.C c := by
  have h : (MvPowerSeries.C (auxFracCastSucc K k c) : AuxAlphabetSeriesFrac K (k + 1))
      = zMonomial K k 0 c := by
    rw [zMonomial, Finsupp.some_zero, Finsupp.coe_zero, Pi.zero_apply, pow_zero, mul_one,
      MvPowerSeries.monomial_zero_eq_C_apply]
  rw [h, zSeries_zMonomial, MvPowerSeries.monomial_zero_eq_C_apply]

/-- The merged coefficients of a letter of the merged alphabet: that letter as a power-series
variable. -/
@[simp]
theorem zSeries_zLetterSeries (r : ℕ) :
    zSeries K k (zLetterSeries K k r) = MvPowerSeries.X (zLetter r) := by
  rw [zLetterSeries, zSeries_zMonomial, MvPowerSeries.X]

/-! ### The merged coefficients are a ring homomorphism -/

/-- **The merged coefficients as a ring homomorphism out of `Z^{(k+1)}`.** Additivity is
`HJO.Sym.zCoeff_add` and multiplicativity is `HJO.Sym.zCoeff_mul`, the merged coefficients of a
product being the convolution of the merged coefficients; both hold only on `Z^{(k+1)}`, which is
why the domain is the subring rather than `P°_{k+1}`. -/
noncomputable def zSeriesHom (K : Type*) [CommRing K] [IsDomain K] (k : ℕ) :
    zSubring K k →+* MvPowerSeries (Option ℕ) (AuxFrac K k) where
  toFun G := zSeries K k (G : AuxAlphabetSeriesFrac K (k + 1))
  map_one' := by
    have h : ((1 : zSubring K k) : AuxAlphabetSeriesFrac K (k + 1))
        = MvPowerSeries.C (auxFracCastSucc K k 1) := by rw [Subring.coe_one, map_one, map_one]
    rw [h, zSeries_C_auxFracCastSucc, map_one]
  map_mul' G H := by
    classical
    refine MvPowerSeries.ext fun ν => ?_
    rw [Subring.coe_mul, coeff_zSeries, zCoeff_mul (mem_zSubring.1 G.2) (mem_zSubring.1 H.2),
      MvPowerSeries.coeff_mul]
    exact Finset.sum_congr rfl fun p _ => by rw [coeff_zSeries, coeff_zSeries]
  map_zero' := by
    refine MvPowerSeries.ext fun ν => ?_
    rw [Subring.coe_zero, coeff_zSeries, zCoeff, MvPowerSeries.coeff_zero, yFracCoeff_zero,
      MvPowerSeries.coeff_zero]
  map_add' G H := by
    refine MvPowerSeries.ext fun ν => ?_
    rw [Subring.coe_add, coeff_zSeries,
      zCoeff_add (coeff_mem_range_yFracEval_of_mem_zRing (mem_zSubring.1 G.2))
        (coeff_mem_range_yFracEval_of_mem_zRing (mem_zSubring.1 H.2)),
      map_add (MvPowerSeries.coeff (R := AuxFrac K k) ν), coeff_zSeries, coeff_zSeries]

@[simp]
theorem zSeriesHom_apply (G : zSubring K k) :
    zSeriesHom K k G = zSeries K k (G : AuxAlphabetSeriesFrac K (k + 1)) :=
  rfl

/-- The merged coefficients of a sum, on `Z^{(k+1)}`. -/
theorem zSeries_add (hG : G ∈ zRing K k) (hH : H ∈ zRing K k) :
    zSeries K k (G + H) = zSeries K k G + zSeries K k H :=
  map_add (zSeriesHom K k) ⟨G, hG⟩ ⟨H, hH⟩

/-- The merged coefficients of a difference, on `Z^{(k+1)}`. -/
theorem zSeries_sub (hG : G ∈ zRing K k) (hH : H ∈ zRing K k) :
    zSeries K k (G - H) = zSeries K k G - zSeries K k H :=
  map_sub (zSeriesHom K k) ⟨G, hG⟩ ⟨H, hH⟩

/-- The merged coefficients of a product, on `Z^{(k+1)}`. -/
theorem zSeries_mul (hG : G ∈ zRing K k) (hH : H ∈ zRing K k) :
    zSeries K k (G * H) = zSeries K k G * zSeries K k H :=
  map_mul (zSeriesHom K k) ⟨G, hG⟩ ⟨H, hH⟩

/-- The merged coefficients of the unit series. -/
@[simp]
theorem zSeries_one : zSeries K k (1 : AuxAlphabetSeriesFrac K (k + 1)) = 1 :=
  map_one (zSeriesHom K k)

/-- **The merged coefficients of a relabelled series are the relabelled merged coefficients**:
`ŝ_ρ` becomes `MvPowerSeries.rename ρ` on the merged alphabet. This is the identity that makes the
distinguished letter movable. -/
theorem zSeries_zPerm (ρ : Equiv.Perm (Option ℕ)) (hG : G ∈ zRing K k) :
    zSeries K k (zPerm K k ρ G) = MvPowerSeries.rename (ρ : Option ℕ → Option ℕ) (zSeries K k G) :=
  MvPowerSeries.ext fun ν => by
    rw [coeff_zSeries, zCoeff_zPerm ρ hG, coeff_rename_perm, coeff_zSeries]

/-- The merged coefficients of `ŝ_m G`: the merged coefficients of `G` renamed along the
interchange. -/
theorem zSeries_zSwap (r : ℕ) (hG : G ∈ zRing K k) :
    zSeries K k (zSwap K k r G)
      = MvPowerSeries.rename (zSwapEquiv r : Option ℕ → Option ℕ) (zSeries K k G) :=
  zSeries_zPerm _ hG

/-- A member of a graded piece has merged coefficients supported in merged degree `d`: its power
series of merged coefficients is homogeneous of degree `d`. -/
theorem isHomogeneous_zSeries (hG : G ∈ zGraded K k d) : (zSeries K k G).IsHomogeneous d :=
  isHomogeneous_of_coeff_eq_zero fun _ hν => zCoeff_eq_zero_of_mem_zGraded hG hν

/-! ### A graded series with prescribed merged coefficients -/

/-- **The member of `Z^{(k+1)}_d` with prescribed merged coefficients**: the coefficient at the
letter-monomial `x^α` is the prescribed coefficient at `y_{k+1}^b x^α` times `y_{k+1}^b`, for the
`b` with `b + |α| = d`, and `0` when there is none. Inverse to `HJO.Sym.zSeries` on the homogeneous
series, by `HJO.Sym.zSeries_zOfSeries`. -/
noncomputable def zOfSeries (K : Type*) [CommRing K] [IsDomain K] (k d : ℕ)
    (Q : MvPowerSeries (Option ℕ) (AuxFrac K k)) : AuxAlphabetSeriesFrac K (k + 1) := fun α =>
  if Finsupp.degree α ≤ d then
    auxFracCastSucc K k (MvPowerSeries.coeff (α.optionElim (d - Finsupp.degree α)) Q)
      * yFrac K (Fin.last k) ^ (d - Finsupp.degree α)
  else 0

theorem coeff_zOfSeries (Q : MvPowerSeries (Option ℕ) (AuxFrac K k)) (α : ℕ →₀ ℕ) :
    MvPowerSeries.coeff α (zOfSeries K k d Q)
      = if Finsupp.degree α ≤ d then
          auxFracCastSucc K k (MvPowerSeries.coeff (α.optionElim (d - Finsupp.degree α)) Q)
            * yFrac K (Fin.last k) ^ (d - Finsupp.degree α)
        else 0 :=
  rfl

/-- The prescribed series does land in the graded piece: below the degree its coefficient is a
scalar multiple of the single power of `y_{k+1}` that `HJO.Sym.zGraded` asks for, and above it the
coefficient is `0`. -/
theorem zOfSeries_mem_zGraded (Q : MvPowerSeries (Option ℕ) (AuxFrac K k)) :
    zOfSeries K k d Q ∈ zGraded K k d := by
  refine ⟨fun α b hb => ⟨MvPowerSeries.coeff (α.optionElim b) Q, ?_⟩, fun α hα => ?_⟩
  · rw [coeff_zOfSeries, ite_eq_left (by omega), show d - Finsupp.degree α = b from by omega]
  · rw [coeff_zOfSeries, ite_eq_right (by omega)]

/-- **The two constructions are inverse on the homogeneous series**: the merged coefficients of
`HJO.Sym.zOfSeries` are the prescribed ones. Homogeneity is needed and is not a convenience: outside
merged degree `d` the built series has no coefficient to carry the prescription. -/
theorem zSeries_zOfSeries {Q : MvPowerSeries (Option ℕ) (AuxFrac K k)} (hQ : Q.IsHomogeneous d) :
    zSeries K k (zOfSeries K k d Q) = Q := by
  refine MvPowerSeries.ext fun ν => ?_
  rw [coeff_zSeries, zCoeff, coeff_zOfSeries]
  have hdeg : Finsupp.degree ν = ν none + Finsupp.degree ν.some := degree_eq_add_degree_some ν
  by_cases hα : Finsupp.degree ν.some ≤ d
  · rw [ite_eq_left hα, yFracCoeff_mul_yFrac_pow]
    by_cases hb : ν none = d - Finsupp.degree ν.some
    · rw [ite_eq_left hb, ← hb, Finsupp.optionElim_some]
    · rw [ite_eq_right hb]
      exact (hQ.coeff_eq_zero (by omega)).symm
  · rw [ite_eq_right hα, yFracCoeff_zero]
    exact (hQ.coeff_eq_zero (by omega)).symm

/-! ### Memberships of the pieces of the numerator -/

/-- A merged monomial of merged degree `d` lies in `Z^{(k+1)}_d`. -/
theorem zMonomial_mem_zGraded {ν : Option ℕ →₀ ℕ} (hν : Finsupp.degree ν = d) (c : AuxFrac K k) :
    zMonomial K k ν c ∈ zGraded K k d :=
  monomial_mem_zGraded ((degree_eq_add_degree_some ν).symm.trans hν) c

/-- A letter of the merged alphabet lies in `Z^{(k+1)}_1`. -/
theorem zLetterSeries_mem_zGraded (r : ℕ) : zLetterSeries K k r ∈ zGraded K k 1 :=
  zMonomial_mem_zGraded (by rw [Finsupp.degree_single]) 1

/-- A letter of the merged alphabet lies in `Z^{(k+1)}`. -/
theorem zLetterSeries_mem_zRing (r : ℕ) : zLetterSeries K k r ∈ zRing K k :=
  zGraded_subset_zRing K k 1 (zLetterSeries_mem_zGraded r)

/-- The inclusion of coefficient fields fixes a scalar of the base. -/
@[simp]
theorem auxFracCastSucc_scalarFrac (q : K) :
    auxFracCastSucc K k (scalarFrac K q) = scalarFrac K q := by
  rw [scalarFrac, auxFracCastSucc_algebraMap, MvPolynomial.rename_C, scalarFrac]

/-- The constant series of the parameter `q` lies in `Z^{(k+1)}_0`. -/
theorem C_scalarFrac_mem_zGraded (q : K) :
    (MvPowerSeries.C (scalarFrac K q) : AuxAlphabetSeriesFrac K (k + 1)) ∈ zGraded K k 0 := by
  have h : (MvPowerSeries.C (scalarFrac K q) : AuxAlphabetSeriesFrac K (k + 1))
      = zMonomial K k 0 (scalarFrac K q) := by
    rw [zMonomial, Finsupp.some_zero, Finsupp.coe_zero, Pi.zero_apply, pow_zero, mul_one,
      MvPowerSeries.monomial_zero_eq_C_apply, auxFracCastSucc_scalarFrac]
  rw [h]
  exact zMonomial_mem_zGraded (map_zero Finsupp.degree) _

/-- The merged coefficients of the constant series of the parameter `q`. -/
@[simp]
theorem zSeries_C_scalarFrac (q : K) :
    zSeries K k (MvPowerSeries.C (scalarFrac K q) : AuxAlphabetSeriesFrac K (k + 1))
      = MvPowerSeries.C (scalarFrac K q) := by
  rw [← auxFracCastSucc_scalarFrac (K := K) (k := k) q, zSeries_C_auxFracCastSucc]

/-- **The numerator stays in the graded pieces, one degree up.** The two scalar factors have merged
degree `0`, the letters merged degree `1`, and `ŝ_m` preserves each piece, so both summands have
merged degree `d + 1`. -/
theorem zdeltaNum_mem_zGraded (q : K) (r : ℕ) (hG : G ∈ zGraded K k d) :
    zdeltaNum q r G ∈ zGraded K k (d + 1) := by
  have hq : (MvPowerSeries.C (scalarFrac K q) : AuxAlphabetSeriesFrac K (k + 1)) ∈ zGraded K k 0 :=
    C_scalarFrac_mem_zGraded q
  have hone : (1 : AuxAlphabetSeriesFrac K (k + 1)) ∈ zGraded K k 0 := one_mem_zGraded
  have hu : zLetterSeries K k r ∈ zGraded K k 1 := zLetterSeries_mem_zGraded r
  have hv : zLetterSeries K k (r + 1) ∈ zGraded K k 1 := zLetterSeries_mem_zGraded (r + 1)
  have h1 : (MvPowerSeries.C (scalarFrac K q) - 1 : AuxAlphabetSeriesFrac K (k + 1))
      * zLetterSeries K k (r + 1) * G ∈ zGraded K k (0 + 1 + d) :=
    mul_mem_zGraded (mul_mem_zGraded (sub_mem_zGraded hq hone) hv) hG
  have h2 : (zLetterSeries K k (r + 1)
      - MvPowerSeries.C (scalarFrac K q) * zLetterSeries K k r) * zSwap K k r G
      ∈ zGraded K k (1 + d) :=
    mul_mem_zGraded (sub_mem_zGraded hv (by
      have := mul_mem_zGraded (d := 0) (e := 1) hq hu
      rwa [Nat.zero_add] at this)) (zSwap_mem_zGraded r hG)
  rw [zdeltaNum, show d + 1 = 1 + d from Nat.add_comm d 1]
  exact add_mem_zGraded (by rwa [Nat.zero_add] at h1) h2

/-- The numerator lies in `Z^{(k+1)}`. -/
theorem zdeltaNum_mem_zRing (q : K) (r : ℕ) (hG : G ∈ zGraded K k d) :
    zdeltaNum q r G ∈ zRing K k :=
  zGraded_subset_zRing K k (d + 1) (zdeltaNum_mem_zGraded q r hG)

/-! ### The numerator vanishes on collapsing the two letters -/

/-- **Collapsing the two letters swallows the interchange**: substituting the upper letter for the
lower one is unchanged by first interchanging them. This is what makes the two scalar factors `q-1`
and `1-q` of the numerator cancel. -/
theorem collapseVar_comp_zSwapEquiv (r : ℕ) :
    collapseVar (zLetter r) (zLetter (r + 1)) ∘ (zSwapEquiv r : Option ℕ → Option ℕ)
      = collapseVar (zLetter r) (zLetter (r + 1)) := by
  have hne : zLetter r ≠ zLetter (r + 1) :=
    fun h => absurd (zLetter_injective h) (Nat.ne_of_lt (Nat.lt_succ_self r))
  funext l
  rcases eq_or_ne l (zLetter r) with rfl | h1
  · rw [Function.comp_apply, zSwapEquiv, Equiv.swap_apply_left, collapseVar_right,
      collapseVar_self]
  rcases eq_or_ne l (zLetter (r + 1)) with rfl | h2
  · rw [Function.comp_apply, zSwapEquiv, Equiv.swap_apply_right, collapseVar_self,
      collapseVar_right]
  · rw [Function.comp_apply, zSwapEquiv, Equiv.swap_apply_of_ne_of_ne h1 h2]

/-- **The merged coefficients of the numerator**, as a power series in the merged alphabet: the
formula of `HJO.Sym.IsZDelta` with the two letters read as power-series variables and `ŝ_m` read as
a renaming. -/
theorem zSeries_zdeltaNum (q : K) (r : ℕ) (hG : G ∈ zRing K k) :
    zSeries K k (zdeltaNum q r G)
      = (MvPowerSeries.C (scalarFrac K q) - 1) * MvPowerSeries.X (zLetter (r + 1))
            * zSeries K k G
          + (MvPowerSeries.X (zLetter (r + 1))
              - MvPowerSeries.C (scalarFrac K q) * MvPowerSeries.X (zLetter r))
            * MvPowerSeries.rename (zSwapEquiv r : Option ℕ → Option ℕ) (zSeries K k G) := by
  have hq : (MvPowerSeries.C (scalarFrac K q) : AuxAlphabetSeriesFrac K (k + 1)) ∈ zRing K k :=
    zGraded_subset_zRing K k 0 (C_scalarFrac_mem_zGraded q)
  have hqone : (MvPowerSeries.C (scalarFrac K q) - 1 : AuxAlphabetSeriesFrac K (k + 1))
      ∈ zRing K k := Subring.sub_mem (zSubring K k) hq one_mem_zRing
  have hu : zLetterSeries K k r ∈ zRing K k := zLetterSeries_mem_zRing r
  have hv : zLetterSeries K k (r + 1) ∈ zRing K k := zLetterSeries_mem_zRing (r + 1)
  have hqu : (MvPowerSeries.C (scalarFrac K q) : AuxAlphabetSeriesFrac K (k + 1))
      * zLetterSeries K k r ∈ zRing K k := mul_mem_zRing hq hu
  rw [zdeltaNum, zSeries_add (mul_mem_zRing (mul_mem_zRing hqone hv) hG)
      (mul_mem_zRing (Subring.sub_mem (zSubring K k) hv hqu) (zSwap_mem_zRing r hG)),
    zSeries_mul (mul_mem_zRing hqone hv) hG, zSeries_mul hqone hv,
    zSeries_mul (Subring.sub_mem (zSubring K k) hv hqu) (zSwap_mem_zRing r hG),
    zSeries_sub hv hqu, zSeries_mul hq hu, zSeries_sub hq one_mem_zRing, zSeries_one,
    zSeries_C_scalarFrac, zSeries_zLetterSeries, zSeries_zLetterSeries, zSeries_zSwap r hG]

/-- **The numerator vanishes on collapsing the two letters.** Substituting the upper letter for the
lower one carries `G` and `ŝ_m(G)` to the same series, by
`HJO.Sym.collapseVar_comp_zSwapEquiv`, and the surviving scalar factors are `q-1` and `1-q`. This
is the hypothesis under which `HJO.CarlssonMellit.DiffDivides` performs the division. -/
theorem rename_collapseVar_zSeries_zdeltaNum (q : K) (r : ℕ) (hG : G ∈ zRing K k) :
    MvPowerSeries.rename (collapseVar (zLetter r) (zLetter (r + 1)))
      (zSeries K k (zdeltaNum q r G)) = 0 := by
  have hswap : MvPowerSeries.rename (collapseVar (zLetter r) (zLetter (r + 1)))
        (MvPowerSeries.rename (zSwapEquiv r : Option ℕ → Option ℕ) (zSeries K k G))
      = MvPowerSeries.rename (collapseVar (zLetter r) (zLetter (r + 1))) (zSeries K k G) := by
    rw [MvPowerSeries.rename_rename, rename_congr_fun (collapseVar_comp_zSwapEquiv r)]
  rw [zSeries_zdeltaNum q r hG]
  simp only [map_add, map_mul, map_sub, map_one, MvPowerSeries.rename_C, MvPowerSeries.rename_X]
  rw [hswap, collapseVar_self, collapseVar_right]
  ring

/-! ### The swapping operator exists on each graded piece -/

/-- **The swapping operator on the merged alphabet, written down.** For `G` in `Z^{(k+1)}_d` this is
the `H` in `Z^{(k+1)}_d` satisfying the equation of `HJO.Sym.IsZDelta`, so `Δ_m(G)` exists; by
`HJO.Sym.eq_of_isZDelta` it is the only one, and therefore `Δ_m(G)` names an element of the same
graded piece. It is written as a total map of `P°_{k+1}` because the construction is total; only
`HJO.Sym.isZDelta_zDeltaOn` needs the graded hypothesis, and off `Z^{(k+1)}_d` the value is junk.

Read at merged coefficients the equation is a division, in
`MvPowerSeries (Option ℕ) 𝕂(y₁, …, y_k)`, of a series homogeneous of degree `d + 1` by the
difference of two of its variables; the numerator vanishes on substituting one for the other, which
is `HJO.Sym.rename_collapseVar_zSeries_zdeltaNum`, and the division is then
`HJO.Sym.isHomogeneous_and_eq_X_sub_X_mul_diffQuot`. Another route divides
the two-variable blocks
of `MvPowerSeries.IsHomogeneous.existsUnique_eq_monomialwiseFinsum_monomial_mul` instead; the two
routes give the same element, uniqueness of the quotient being `HJO.Sym.eq_of_isZDelta`. -/
@[hjo "lem_cm_zdelta_defined"]
noncomputable def zDeltaOn (K : Type*) [CommRing K] [IsDomain K] (k : ℕ) (q : K) (d r : ℕ)
    (G : AuxAlphabetSeriesFrac K (k + 1)) : AuxAlphabetSeriesFrac K (k + 1) :=
  zOfSeries K k d (diffQuot (zLetter r) (zLetter (r + 1)) (zSeries K k (zdeltaNum q r G)))

/-- **The value lies in the same graded piece**, and unconditionally so: `HJO.Sym.zOfSeries` lands
in `Z^{(k+1)}_d` whatever it is given. -/
@[hjo "lem_cm_zdelta_defined"]
theorem zDeltaOn_mem_zGraded (q : K) (d r : ℕ) (G : AuxAlphabetSeriesFrac K (k + 1)) :
    zDeltaOn K k q d r G ∈ zGraded K k d :=
  zOfSeries_mem_zGraded _

/-- **The value satisfies the equation of `HJO.Sym.IsZDelta`** when the argument lies in the graded
piece. This is where the graded hypothesis is spent. -/
@[hjo "lem_cm_zdelta_defined"]
theorem isZDelta_zDeltaOn (q : K) (r : ℕ) (hG : G ∈ zGraded K k d) :
    IsZDelta q r G (zDeltaOn K k q d r G) := by
  have hGring : G ∈ zRing K k := zGraded_subset_zRing K k d hG
  have hne : zLetter r ≠ zLetter (r + 1) :=
    fun h => absurd (zLetter_injective h) (Nat.ne_of_lt (Nat.lt_succ_self r))
  obtain ⟨hhom, heq⟩ := isHomogeneous_and_eq_X_sub_X_mul_diffQuot hne
    (isHomogeneous_zSeries (zdeltaNum_mem_zGraded q r hG))
    (rename_collapseVar_zSeries_zdeltaNum q r hGring)
  refine eq_of_zSeries_eq (mul_mem_zRing (Subring.sub_mem (zSubring K k)
      (zLetterSeries_mem_zRing (r + 1)) (zLetterSeries_mem_zRing r))
      (zGraded_subset_zRing K k d (zDeltaOn_mem_zGraded q d r G)))
    (zdeltaNum_mem_zRing q r hG) ?_
  rw [zSeries_mul (Subring.sub_mem (zSubring K k) (zLetterSeries_mem_zRing (r + 1))
      (zLetterSeries_mem_zRing r)) (zGraded_subset_zRing K k d (zDeltaOn_mem_zGraded q d r G)),
    zSeries_sub (zLetterSeries_mem_zRing (r + 1)) (zLetterSeries_mem_zRing r),
    zSeries_zLetterSeries, zSeries_zLetterSeries, zDeltaOn, zSeries_zOfSeries hhom]
  exact heq.symm

/-- **The swapping operator on the merged alphabet is defined**, as an existence
statement: for `G` in `Z^{(k+1)}_d` some `H` in `Z^{(k+1)}_d` satisfies the equation. -/
@[hjo "lem_cm_zdelta_defined"]
theorem exists_isZDelta_of_mem_zGraded (q : K) (r : ℕ) (hG : G ∈ zGraded K k d) :
    ∃ H : AuxAlphabetSeriesFrac K (k + 1), H ∈ zGraded K k d ∧ IsZDelta q r G H :=
  ⟨zDeltaOn K k q d r G, zDeltaOn_mem_zGraded q d r G, isZDelta_zDeltaOn q r hG⟩

/-- **The value of the swapping operator on a graded piece**, with the membership carried in the
notation: `Δ_m(G)` for `G ∈ Z^{(k+1)}_d`. It is `HJO.Sym.zDeltaOn` at the degree the hypothesis
names, so it does not depend on the proof. -/
noncomputable def zDelta (q : K) (r : ℕ) (_hG : G ∈ zGraded K k d) :
    AuxAlphabetSeriesFrac K (k + 1) :=
  zDeltaOn K k q d r G

theorem zDelta_mem_zGraded (q : K) (r : ℕ) (hG : G ∈ zGraded K k d) :
    zDelta q r hG ∈ zGraded K k d :=
  zDeltaOn_mem_zGraded q d r G

/-- The value satisfies the equation of `HJO.Sym.IsZDelta`. -/
theorem isZDelta_zDelta (q : K) (r : ℕ) (hG : G ∈ zGraded K k d) :
    IsZDelta q r G (zDelta q r hG) :=
  isZDelta_zDeltaOn q r hG

/-- The value is the only solution, so `HJO.Sym.zDelta` does not depend on the membership proof and
any solution is it. -/
theorem eq_zDelta (q : K) (r : ℕ) (hG : G ∈ zGraded K k d) (h : IsZDelta q r G H) :
    H = zDelta q r hG :=
  eq_of_isZDelta h (isZDelta_zDelta q r hG)

/-- **The defining equation, read at merged coefficients, is blockwise.** Every monomial occurring
in the identity at `ρ z_m^{i+1} z_{m+1}^{j+1}` carries the same `ρ`: the coefficients of `Δ_m(G)` at
`ρ z_m^{i+1} z_{m+1}^{j}` and at `ρ z_m^{i} z_{m+1}^{j+1}` differ by the coefficient of the
numerator at `ρ z_m^{i+1} z_{m+1}^{j+1}`.

This is the conjunct adjoined to `HJO.Sym.zDeltaOn` as an equation between the
two-variable blocks of
`MvPowerSeries.IsHomogeneous.existsUnique_eq_monomialwiseFinsum_monomial_mul`. Here no block family
is named: the merged-coefficient form of the series identity is already block-diagonal, one `ρ` at a
time, and it needs no hypothesis on `ρ` at all. -/
theorem zCoeff_zDelta_sub_zCoeff_zDelta (q : K) (r : ℕ) (hG : G ∈ zGraded K k d)
    (ρ : Option ℕ →₀ ℕ) (i j : ℕ) :
    zCoeff K k (zDelta q r hG) (ρ + Finsupp.single (zLetter r) (i + 1)
          + Finsupp.single (zLetter (r + 1)) j)
        - zCoeff K k (zDelta q r hG) (ρ + Finsupp.single (zLetter r) i
          + Finsupp.single (zLetter (r + 1)) (j + 1))
      = zCoeff K k (zdeltaNum q r G) (ρ + Finsupp.single (zLetter r) (i + 1)
          + Finsupp.single (zLetter (r + 1)) (j + 1)) := by
  set Q := zSeries K k (zDelta q r hG) with hQ
  have hHring : zDelta q r hG ∈ zRing K k :=
    zGraded_subset_zRing K k d (zDelta_mem_zGraded q r hG)
  have key : (MvPowerSeries.X (zLetter (r + 1)) - MvPowerSeries.X (zLetter r)) * Q
      = zSeries K k (zdeltaNum q r G) := by
    rw [hQ, ← zSeries_zLetterSeries (K := K) (k := k) r,
      ← zSeries_zLetterSeries (K := K) (k := k) (r + 1),
      ← zSeries_sub (zLetterSeries_mem_zRing (r + 1)) (zLetterSeries_mem_zRing r),
      ← zSeries_mul (Subring.sub_mem (zSubring K k) (zLetterSeries_mem_zRing (r + 1))
        (zLetterSeries_mem_zRing r)) hHring]
    exact congrArg (zSeries K k) (isZDelta_zDelta q r hG)
  have h := congrArg (MvPowerSeries.coeff (ρ + Finsupp.single (zLetter r) (i + 1)
    + Finsupp.single (zLetter (r + 1)) (j + 1))) key
  have h1 : MvPowerSeries.coeff (ρ + Finsupp.single (zLetter r) (i + 1)
        + Finsupp.single (zLetter (r + 1)) (j + 1)) (MvPowerSeries.X (zLetter (r + 1)) * Q)
      = MvPowerSeries.coeff (ρ + Finsupp.single (zLetter r) (i + 1)
        + Finsupp.single (zLetter (r + 1)) j) Q := by
    rw [add_single_add_single_succ_right, coeff_X_mul_add]
  have h2 : MvPowerSeries.coeff (ρ + Finsupp.single (zLetter r) (i + 1)
        + Finsupp.single (zLetter (r + 1)) (j + 1)) (MvPowerSeries.X (zLetter r) * Q)
      = MvPowerSeries.coeff (ρ + Finsupp.single (zLetter r) i
        + Finsupp.single (zLetter (r + 1)) (j + 1)) Q := by
    rw [add_single_succ_add_single_left, coeff_X_mul_add]
  rw [sub_mul, map_sub, h1, h2, hQ, coeff_zSeries, coeff_zSeries, coeff_zSeries] at h
  exact h

/-! ### Linearity over the invariant coefficients -/

/-- **The swapping operator is linear over the coefficients the interchange fixes**: if `g` lies in
`Z^{(k+1)}` and `ŝ_m(g) = g`, then `Δ_m(gF) = gΔ_m(F)`. Multiplying the equation of
`HJO.Sym.IsZDelta` for `F` by `g` exhibits `gΔ_m(F)` as a solution of the equation for `gF`, because
`ŝ_m` is a ring homomorphism on `Z^{(k+1)}` (`HJO.Sym.zPermEquiv`) and so carries `gF` to `gŝ_m(F)`;
and by `HJO.Sym.eq_of_isZDelta` there is no other solution.

Stated for the relation, so that no grading hypothesis is needed: the statement
`Δ_m(gF) = gΔ_m(F)` for `F ∈ Z^{(k)}` is this together with the uniqueness of the solution. -/
@[hjo "lem_cm_zdelta_symmetric"]
theorem isZDelta_mul_of_zSwap_eq {q : K} {r : ℕ} {F g : AuxAlphabetSeriesFrac K (k + 1)}
    (hF : F ∈ zRing K k) (hg : g ∈ zRing K k) (hgs : zSwap K k r g = g)
    (h : IsZDelta q r F H) : IsZDelta q r (g * F) (g * H) := by
  have hnum : zdeltaNum q r (g * F) = g * zdeltaNum q r F := by
    rw [zdeltaNum_apply, zdeltaNum_apply, zSwap_apply,
      zPerm_mul_of_mem_zRing (zSwapEquiv r) hg hF, ← zSwap_apply, ← zSwap_apply, hgs]
    ring
  rw [IsZDelta, hnum, ← h]
  ring

/-- The same as an identity of values, where the grading makes `Δ_m` a function: `Δ_m(gF)` is
`gΔ_m(F)`. -/
@[hjo "lem_cm_zdelta_symmetric"]
theorem zDelta_mul_of_zSwap_eq {q : K} {r e : ℕ} {F g : AuxAlphabetSeriesFrac K (k + 1)}
    (hF : F ∈ zGraded K k d) (hg : g ∈ zGraded K k e) (hgs : zSwap K k r g = g) :
    zDelta q r (mul_mem_zGraded hg hF) = g * zDelta q r hF :=
  (eq_zDelta q r (mul_mem_zGraded hg hF)
    (isZDelta_mul_of_zSwap_eq (zGraded_subset_zRing K k d hF) (zGraded_subset_zRing K k e hg) hgs
      (isZDelta_zDelta q r hF))).symm

/-! ### Additivity -/

/-- **The swapping operator is additive**: the equation of `HJO.Sym.IsZDelta` is additive in its
argument and in its solution. -/
theorem isZDelta_add {q : K} {r : ℕ} {F F' H H' : AuxAlphabetSeriesFrac K (k + 1)}
    (hF : F ∈ zRing K k) (hF' : F' ∈ zRing K k) (h : IsZDelta q r F H) (h' : IsZDelta q r F' H') :
    IsZDelta q r (F + F') (H + H') := by
  have hnum : zdeltaNum q r (F + F') = zdeltaNum q r F + zdeltaNum q r F' := by
    rw [zdeltaNum_apply, zdeltaNum_apply, zdeltaNum_apply, zSwap_apply,
      zPerm_add_of_mem_zRing (zSwapEquiv r) hF hF', ← zSwap_apply, ← zSwap_apply]
    ring
  rw [IsZDelta, hnum, ← h, ← h']
  ring

/-- **The swapping operator respects finite sums**: `Δ_m(∑_{l ∈ t}F_l) = ∑_{l ∈ t}Δ_m(F_l)` for a
finite family in `Z^{(k+1)}`. This is
`HJO.Sym.isZDelta_summableSum` for a finite index set; the general lemma is stated for an
arbitrary index set with a monomialwise finiteness hypothesis, which is *not* covered here — see
the note in the module docstring. -/
theorem isZDelta_sum {q : K} {r : ℕ} {ι : Type*} {t : Finset ι}
    {F H' : ι → AuxAlphabetSeriesFrac K (k + 1)} (hF : ∀ l ∈ t, F l ∈ zRing K k)
    (h : ∀ l ∈ t, IsZDelta q r (F l) (H' l)) :
    IsZDelta q r (∑ l ∈ t, F l) (∑ l ∈ t, H' l) := by
  classical
  induction t using Finset.cons_induction with
  | empty =>
    rw [Finset.sum_empty, Finset.sum_empty, IsZDelta, zdeltaNum_apply, mul_zero, zSwap_apply,
      zPerm_zero]
    ring
  | cons a s ha ih =>
    rw [Finset.sum_cons, Finset.sum_cons]
    exact isZDelta_add (hF a (Finset.mem_cons_self ..))
      (sum_mem_zRing fun l hl => hF l (Finset.mem_cons_of_mem hl))
      (h a (Finset.mem_cons_self ..))
      (ih (fun l hl => hF l (Finset.mem_cons_of_mem hl))
        fun l hl => h l (Finset.mem_cons_of_mem hl))

/-! ### The two letters and the parameter under the interchange -/

/-- `ŝ_m` carries the lower of the two letters to the upper one. -/
@[simp]
theorem zSwap_zLetterSeries (r : ℕ) :
    zSwap K k r (zLetterSeries K k r) = zLetterSeries K k (r + 1) := by
  rw [zLetterSeries, zLetterSeries, zSwap_zMonomial, Finsupp.equivMapDomain_single, zSwapEquiv,
    Equiv.swap_apply_left]

/-- `ŝ_m` carries the upper of the two letters to the lower one. -/
@[simp]
theorem zSwap_zLetterSeries_succ (r : ℕ) :
    zSwap K k r (zLetterSeries K k (r + 1)) = zLetterSeries K k r := by
  rw [zLetterSeries, zLetterSeries, zSwap_zMonomial, Finsupp.equivMapDomain_single, zSwapEquiv,
    Equiv.swap_apply_right]

/-- `ŝ_m` fixes the parameter `q`, a constant of the base. -/
@[simp]
theorem zSwap_C_scalarFrac (q : K) (r : ℕ) :
    zSwap K k r (MvPowerSeries.C (scalarFrac K q) : AuxAlphabetSeriesFrac K (k + 1))
      = MvPowerSeries.C (scalarFrac K q) := by
  rw [← auxFracCastSucc_scalarFrac (K := K) (k := k) q, zSwap_apply, zPerm_C]

/-! ### The weights of a free run -/

/-- A ring homomorphism carries the weight of a run to the weight computed from the images of the
three elements: the weight is a product of powers. -/
theorem map_runWeight {A B F : Type*} [CommRing A] [CommRing B] [FunLike F A B]
    [RingHomClass F A B] (f : F) (q u v : A) (l : ℕ) (ε : Bool) :
    f (runWeight q u v l ε) = runWeight (f q) (f u) (f v) l ε := by
  cases ε <;> simp [runWeight]

/-- The weight of a run computed in the subring is the weight computed in `P°_{k+1}`: the subring
inclusion is a ring homomorphism. -/
theorem coe_runWeight (a b c : zSubring K k) (l : ℕ) (ε : Bool) :
    ((runWeight a b c l ε : zSubring K k) : AuxAlphabetSeriesFrac K (k + 1))
      = runWeight (a : AuxAlphabetSeriesFrac K (k + 1)) (b : AuxAlphabetSeriesFrac K (k + 1))
        (c : AuxAlphabetSeriesFrac K (k + 1)) l ε := by
  cases ε <;> push_cast [runWeight] <;> ring

/-- `ŝ_m` read on the subring, so that the ring automorphism `HJO.Sym.zPermEquiv` of
`HJO.Sym.zPermEquiv` can be pushed through a product. -/
theorem zSwap_coe (r : ℕ) (X : zSubring K k) :
    zSwap K k r (X : AuxAlphabetSeriesFrac K (k + 1))
      = ((zPermEquiv K k (zSwapEquiv r) X : zSubring K k) : AuxAlphabetSeriesFrac K (k + 1)) :=
  rfl

/-- **`ŝ_m` acts on the weight of a run by interchanging the two letters**: the weight is a product
of powers and `ŝ_m` is a ring automorphism of `Z^{(k+1)}`. -/
theorem zSwap_runWeight {a b c : AuxAlphabetSeriesFrac K (k + 1)} (r l : ℕ) (ε : Bool)
    (ha : a ∈ zRing K k) (hb : b ∈ zRing K k) (hc : c ∈ zRing K k) :
    zSwap K k r (runWeight a b c l ε)
      = runWeight (zSwap K k r a) (zSwap K k r b) (zSwap K k r c) l ε := by
  rw [← coe_runWeight (⟨a, ha⟩ : zSubring K k) ⟨b, hb⟩ ⟨c, hc⟩ l ε, zSwap_coe,
    map_runWeight (zPermEquiv K k (zSwapEquiv r)), coe_runWeight]
  rfl

/-- **The two weights of a free run sum to an invariant**: `ŝ_m(a_m(l,0) + a_m(l,1))` is
`a_m(l,0) + a_m(l,1)`. For an even length each weight is separately symmetric in the two letters;
for an odd one the interchange swaps the two weights. The symmetry is
`HJO.Sym.runWeight_add_comm`, and what this adds is that `ŝ_m` — which is not induced by any
substitution in `P°_{k+1}` when the lower letter is the distinguished one — does interchange the two
letters and fix `q`. -/
@[hjo "lem_cm_zrunweight_sum_symmetric"]
theorem zSwap_runWeight_add_runWeight (q : K) (r l : ℕ) :
    zSwap K k r (runWeight (MvPowerSeries.C (scalarFrac K q)) (zLetterSeries K k r)
          (zLetterSeries K k (r + 1)) l false
        + runWeight (MvPowerSeries.C (scalarFrac K q)) (zLetterSeries K k r)
          (zLetterSeries K k (r + 1)) l true)
      = runWeight (MvPowerSeries.C (scalarFrac K q)) (zLetterSeries K k r)
          (zLetterSeries K k (r + 1)) l false
        + runWeight (MvPowerSeries.C (scalarFrac K q)) (zLetterSeries K k r)
          (zLetterSeries K k (r + 1)) l true := by
  have hq : (MvPowerSeries.C (scalarFrac K q) : AuxAlphabetSeriesFrac K (k + 1)) ∈ zRing K k :=
    zGraded_subset_zRing K k 0 (C_scalarFrac_mem_zGraded q)
  have hu : zLetterSeries K k r ∈ zRing K k := zLetterSeries_mem_zRing r
  have hv : zLetterSeries K k (r + 1) ∈ zRing K k := zLetterSeries_mem_zRing (r + 1)
  have hw : ∀ ε : Bool, runWeight (MvPowerSeries.C (scalarFrac K q)
      : AuxAlphabetSeriesFrac K (k + 1)) (zLetterSeries K k r) (zLetterSeries K k (r + 1)) l ε
        ∈ zRing K k := by
    intro ε
    rw [← coe_runWeight (⟨_, hq⟩ : zSubring K k) ⟨_, hu⟩ ⟨_, hv⟩ l ε]
    exact (runWeight (⟨_, hq⟩ : zSubring K k) ⟨_, hu⟩ ⟨_, hv⟩ l ε).2
  rw [zSwap_apply, zPerm_add_of_mem_zRing _ (hw false) (hw true), ← zSwap_apply, ← zSwap_apply,
    zSwap_runWeight r l false hq hu hv, zSwap_runWeight r l true hq hu hv, zSwap_C_scalarFrac,
    zSwap_zLetterSeries, zSwap_zLetterSeries_succ, runWeight_add_comm]

/-- **The swapping operator flips the weight of a free run**: `Δ_m(a_m(l,0)) = a_m(l,1)` for
`l ≥ 1`. For an even length the weight is `ŝ_m`-invariant and the operator multiplies it by `q`; for
an odd one the symmetric factor comes out and what is left is `Δ_m(z_m) = z_{m+1}`.

Stated for the relation, so that the identity is a product and not a quotient; with
`HJO.Sym.eq_of_isZDelta` it is the equation of values. -/
@[hjo "lem_cm_zrunweight_delta"]
theorem isZDelta_runWeight (q : K) (r : ℕ) {l : ℕ} (hl : 1 ≤ l) :
    IsZDelta q r (runWeight (MvPowerSeries.C (scalarFrac K q)) (zLetterSeries K k r)
        (zLetterSeries K k (r + 1)) l false)
      (runWeight (MvPowerSeries.C (scalarFrac K q)) (zLetterSeries K k r)
        (zLetterSeries K k (r + 1)) l true) := by
  have hq : (MvPowerSeries.C (scalarFrac K q) : AuxAlphabetSeriesFrac K (k + 1)) ∈ zRing K k :=
    zGraded_subset_zRing K k 0 (C_scalarFrac_mem_zGraded q)
  have hu : zLetterSeries K k r ∈ zRing K k := zLetterSeries_mem_zRing r
  have hv : zLetterSeries K k (r + 1) ∈ zRing K k := zLetterSeries_mem_zRing (r + 1)
  rw [IsZDelta, zdeltaNum_apply, zSwap_runWeight r l false hq hu hv, zSwap_C_scalarFrac,
    zSwap_zLetterSeries, zSwap_zLetterSeries_succ]
  rcases Nat.even_or_odd l with ⟨l', rfl⟩ | ⟨l', rfl⟩
  · obtain ⟨l'', rfl⟩ : ∃ l'', l' = l'' + 1 := ⟨l' - 1, by omega⟩
    rw [show l'' + 1 + (l'' + 1) = 2 * (l'' + 1) from by ring]
    obtain ⟨e0, e1⟩ := runWeight_two_mul (MvPowerSeries.C (scalarFrac K q)
      : AuxAlphabetSeriesFrac K (k + 1)) (zLetterSeries K k r) (zLetterSeries K k (r + 1))
      (l' := l'' + 1) (by omega)
    obtain ⟨f0, -⟩ := runWeight_two_mul (MvPowerSeries.C (scalarFrac K q)
      : AuxAlphabetSeriesFrac K (k + 1)) (zLetterSeries K k (r + 1)) (zLetterSeries K k r)
      (l' := l'' + 1) (by omega)
    rw [e0, e1, f0, show l'' + 1 - 1 = l'' from by omega]
    ring
  · obtain ⟨e0, e1⟩ := runWeight_two_mul_add_one (MvPowerSeries.C (scalarFrac K q)
      : AuxAlphabetSeriesFrac K (k + 1)) (zLetterSeries K k r) (zLetterSeries K k (r + 1)) l'
    obtain ⟨f0, -⟩ := runWeight_two_mul_add_one (MvPowerSeries.C (scalarFrac K q)
      : AuxAlphabetSeriesFrac K (k + 1)) (zLetterSeries K k (r + 1)) (zLetterSeries K k r) l'
    rw [e0, e1, f0]
    ring

end HJO.Sym
