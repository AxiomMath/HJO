/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.CarlssonMellit.ChiPrimeExpansion
public import HJO.Classical.RealisationInjective
public import HJO.Symmetric.SwapInvariant
public meta import HJO.Attr

/-! # The unique expansion of the invariant in the last variable

`HJO.Dyck.existsUnique_eq_sum_pow_mul_realiseAddLetter`: for `N ≥ k` and `π ∈ 𝔻_{k,N}` there are
unique `g_j(π) ∈ V_{k-1}`, `j ≥ 1`, with `χ'_{Id_k}(π) = ∑_{j ≥ 1}y_k^{j}g_j(π)[X + y_k]`.

`HJO/CarlssonMellit/ChiPrimeExpansion.lean` proves everything the proof asks for except two steps,
both asserted in the proof as usually written without justification. This file supplies those two
and assembles the lemma.

**The first missing step** is the sentence of the proof as usually written:

> A symmetric series of bounded degree in the free variables with coefficients in
> `𝕜[y_1, …, y_{k-1}]` is a finite combination of monomial symmetric functions, hence the
> realisation under `HJO.Dyck.IsAuxRealisation` of an element of `V_{k-1}`.

That is the surjectivity of the realisation onto the symmetric part in bounded degree, over the base
`𝕜[y_1, …, y_{k-1}]` — which is not a field. **The second** is the injectivity of the realisation on
`V_{k-1}`, which the uniqueness half needs and which `HJO.Sym.realisation_injective` states only at
the level `0`, about `Λ`. Both are steps of the proof as usually written with no statement of their
own, and both are stated separately here.

## Main results

* `HJO.Dyck.existsUnique_eq_sum_pow_mul_realiseAddLetter`: the lemma.
* `HJO.Dyck.exists_eq_sum_pow_mul_realiseAddLetter`: its existence half.
* `HJO.Sym.exists_iota_eq_of_letterPerm_swap`: over any `ℚ`-algebra, a series of the alphabet fixed
  by every adjacent interchange of letters and with no monomial of total degree above `N` is `ι(f)`
  for an `f ∈ Λ`, homogeneous piece by homogeneous piece. This is the classical half of the first
  missing step, obtained by splitting into homogeneous components and applying
  `HJO.Sym.map_lambdaComp_eq_msymmSpan` to each.
* `HJO.Dyck.exists_mem_piece_of_zPartPoly`,
  `HJO.Dyck.exists_mem_piece_auxToFrac_realise_eq_zPart`: the first missing step at the level
  `k + 1` — a symmetric expansion coefficient of bounded degree is `ι_{k+1}(h)` for an
  `h ∈ V_{k-1}`, and `h[X + y_{k+1}]` inherits a bound on its merged degree.
* `HJO.Dyck.realise_injective_on_piece`: the second missing step.
* `HJO.Dyck.exists_solve`: the triangular recursion, and the one place the merged-degree bookkeeping
  is spent.

## Main definitions

* `HJO.Sweep.auxToTotal`, `HJO.Sweep.pieceLift`: the presentation of `V_{k-1}` as the ring of
  symmetric functions over the lower polynomial ring, `Λ(𝕜[y_1, …, y_{k-1}]) → V_*`, landing on
  `V_{k-1}` (`HJO.Sweep.pieceLift_mem_piece`, `HJO.Sweep.exists_pieceLift_eq`).
* `HJO.Sym.auxFracPoly`: the inclusion `𝕜[y_1, …, y_{k-1}] → 𝕜(y_1, …, y_k)` of the lower
  polynomial ring into the coefficient field of `P°_{k+1}`.
* `HJO.Sym.zPartPoly`: the coefficient `c_j` read in `𝕜[y_1, …, y_{k-1}]⟦x_1, x_2, …⟧` rather than
  in `P°_{k+1}` — the series the classical statement is applied to.
* `HJO.Sym.MergedLE`: a bound on the merged degree of a member of `P_{k+1}`, stated in the
  polynomial ring so that it is additive under multiplication.

## Implementation notes

*The base of the symmetric-function statement is the polynomial ring and not the fraction field.*
`HJO.Sym.zBase` says that the coefficients of `c_j` lie in `𝕂(y_1, …, y_k)`, which for `K` a domain
is a field; but what the recursion needs is an element of `V_{k-1} = Λ ⊗ 𝕜[y_1, …, y_{k-1}]`, whose
scalars are *polynomials*. The coefficients of `c_j` are polynomial as soon as the series it comes
from is (`HJO.Sym.zCoeff_auxToFrac`), and the whole argument is therefore run over
`R = 𝕜[y_1, …, y_{k-1}]`, with `HJO.Sym.auxFracPoly` as the coefficientwise comparison map. That is
why `HJO.Sym.map_lambdaComp_eq_msymmSpan` had to be generalised from a field of characteristic zero
to a `ℚ`-algebra: see the implementation notes of `HJO/Classical/IotaMsymm.lean`.

*The aux series ring is an `abbrev`.* `HJO.Sym.AuxAlphabetSeries K k` is by definition
`HJO.Sym.AlphabetSeries (MvPolynomial (Fin k) K)`, so the classical statements about
`AlphabetSeries R` instantiate verbatim at `R = MvPolynomial (Fin k) K`, and `HJO.Sym.zPartPoly` is
literally an element of `AuxAlphabetSeries K k`. No new ring is introduced.

*The realisation the classical statement is applied to is `HJO.PhiMul.realise`, not `ι`.* The
hypothesis `HJO.Dyck.IsAuxRealisation (k+1) ι` pins `ι` on `V_k` only, and `ι` has the wrong source
and target for the classical statement; what is proved instead is that the two agree,
`HJO.Dyck.auxToFrac_realise_pieceLift`, after which the `f ∈ Λ(R)` the classical statement produces
is transported to `HJO.Sweep.pieceLift K k f ∈ V_{k-1}`. The same identification is what makes the
level-`0` injectivity apply on `V_{k-1}`.

*Why the merged degree is carried in `P_{k+1}` and not as membership in `Z^{(k+1)}_d`.* The
recursion determines `g_n` from `c_n` and the `g_j` with `j < n`, and it would not terminate without
a reason for the family to be finitely supported. That reason is the *merged* degree: the term
`y_k^{j}g_j[X + y_k]` has merged degree `j` plus the weight of `g_j`, and the weight of `g_j` is
bounded by the degree of the coefficient it was produced from, so subtracting the term leaves the
merged bound where it was and the index `j` cannot exceed it. The bound therefore has to be
*additive under multiplication*, and `HJO.Sym.MergedLE`, stated through the ring homomorphism
`HJO.Sym.auxSplitLast` inside `P_{k+1}`, is. It and the bound on the merged coefficients that
`HJO.Sym.zGraded` records are interchangeable at the level of statements:
`HJO.Sym.mergedLE_of_zCoeff_eq_zero` and `HJO.Sym.zCoeff_eq_zero_of_mergedLE`. *The `g_j` are a
function on `ℕ` with `g_0 = 0`.* They are usually indexed by `j ≥ 1`; a total
function vanishing at `0` is the same data and keeps every index free of a truncated subtraction, as
`HJO/CarlssonMellit/ChiPrimeExpansion.lean` already does for the uniqueness half. "All but
finitely many are zero" is a bound `M` past which the family vanishes, so the infinite
sum is the finite `∑_{j ≤ M}`.

*The base is a domain and a `ℚ`-algebra.* The coefficient field `𝕜 = ℚ(q,u)` is a field of
characteristic zero; `[IsDomain K]` is what the merged alphabet needs (`HJO.Sym.auxFracCastSucc`)
and `[Algebra ℚ K]` is what the triangular basis of `HJO.Sym.map_lambdaComp_eq_msymmSpan` needs.
Nothing in the proof divides by anything else, so the field hypothesis is dropped; this only
generalises the statement.

## References

E. Carlsson and A. Mellit, *A proof of the
shuffle conjecture*, J. Amer. Math. Soc. **31** (2018) 661--697, Section 4, "Lowering operator",
where both missing steps are used without comment.
-/

@[expose] public section

namespace HJO.Sym

/-! ### A symmetric series of bounded degree is realised -/

variable {R : Type*} [CommRing R] [Algebra ℚ R] {ιR : Lambda R →ₐ[R] AlphabetSeries R}

/-- **A symmetric series of bounded degree in the alphabet is the realisation of a symmetric
function.** This is the statement "a symmetric series of bounded degree in the free variables with
coefficients in `𝕜[y_1, …, y_{k-1}]` is a finite combination of monomial symmetric functions, hence
the realisation of an element of `V_{k-1}`", stated over an arbitrary `ℚ`-algebra.

The passage from *bounded* to *homogeneous* degree is the decomposition into the homogeneous
components `MvPowerSeries.homogeneousComponent d`, of which only those with `d ≤ N` are nonzero.
Each is still fixed by the adjacent interchanges, since a relabelling preserves total degree; so
`HJO.Sym.mem_msymmSpan_of_letterPerm_swap` puts it in `W_d`, and
`HJO.Sym.map_lambdaComp_eq_msymmSpan` identifies `W_d` with `ι(Λ_d)`. -/
theorem exists_iota_eq_of_letterPerm_swap (hι : IsRealisation ιR) {H : AlphabetSeries R} {N : ℕ}
    (hbd : ∀ α : ℕ →₀ ℕ, N < Finsupp.degree α → MvPowerSeries.coeff α H = 0)
    (hsym : ∀ m : ℕ, letterPerm R (Equiv.swap m (m + 1)) H = H) :
    ∃ f : ℕ → Lambda R, (∀ d, f d ∈ LambdaComp R d) ∧
      ιR (∑ d ∈ Finset.range (N + 1), f d) = H := by
  classical
  have hcomp : ∀ d : ℕ, ∃ f ∈ LambdaComp R d, ιR f = MvPowerSeries.homogeneousComponent d H := by
    intro d
    have hhom : ∀ α : ℕ →₀ ℕ, (α.sum fun _ e => e) ≠ d →
        MvPowerSeries.coeff α (MvPowerSeries.homogeneousComponent d H) = 0 := fun α hα => by
      rw [MvPowerSeries.coeff_homogeneousComponent]
      exact ite_eq_right hα
    have hsym' : ∀ m : ℕ, letterPerm R (Equiv.swap m (m + 1))
        (MvPowerSeries.homogeneousComponent d H) = MvPowerSeries.homogeneousComponent d H := by
      intro m
      refine MvPowerSeries.ext fun α => ?_
      have h1 : MvPowerSeries.coeff (Finsupp.equivMapDomain (Equiv.swap m (m + 1)).symm α) H
          = MvPowerSeries.coeff α H := by rw [← coeff_letterPerm, hsym m]
      rw [coeff_letterPerm, MvPowerSeries.coeff_homogeneousComponent,
        MvPowerSeries.coeff_homogeneousComponent, degree_equivMapDomain, h1]
    have hmem := mem_msymmSpan_of_letterPerm_swap hhom hsym'
    rw [← map_lambdaComp_eq_msymmSpan hι d] at hmem
    obtain ⟨f, hfmem, hf⟩ := Submodule.mem_map.1 hmem
    exact ⟨f, hfmem, hf⟩
  choose f hfmem hf using hcomp
  refine ⟨f, hfmem, ?_⟩
  rw [map_sum, Finset.sum_congr rfl fun d _ => hf d]
  refine MvPowerSeries.ext fun α => ?_
  rw [map_sum]
  simp only [MvPowerSeries.coeff_homogeneousComponent]
  by_cases hα : Finsupp.degree α ≤ N
  · rw [Finset.sum_eq_single (Finsupp.degree α) (fun d _ hd => ite_eq_right (Ne.symm hd))
      (fun h => absurd (Finset.mem_range.2 (by omega)) h), ite_eq_left rfl]
  · rw [Finset.sum_eq_zero fun d hd => ite_eq_right (by rw [Finset.mem_range] at hd; omega),
      hbd α (by omega)]

/-! ### The lower polynomial ring inside the coefficient field -/

variable {K : Type*} [CommRing K] {k : ℕ}

/-- The inclusion `𝕜[y_1, …, y_k] → 𝕜(y_1, …, y_{k+1})` of the lower polynomial ring into the
coefficient field of `P°_{k+1}`: the localization map followed by `HJO.Sym.auxFracCastSucc`. This is
the map along which a series over the lower polynomial ring is compared with a member of
`HJO.Sym.zBase`. -/
noncomputable def auxFracPoly (K : Type*) [CommRing K] [IsDomain K] (k : ℕ) :
    MvPolynomial (Fin k) K →+* AuxFrac K (k + 1) :=
  (auxFracCastSucc K k).comp (algebraMap (MvPolynomial (Fin k) K) (AuxFrac K k))

theorem auxFracPoly_apply [IsDomain K] (p : MvPolynomial (Fin k) K) :
    auxFracPoly K k p
      = auxFracCastSucc K k (algebraMap (MvPolynomial (Fin k) K) (AuxFrac K k) p) :=
  rfl

/-- The inclusion of the lower polynomial ring is injective: the localization map of a domain at its
non-zerodivisors is, and so is `HJO.Sym.auxFracCastSucc`. -/
theorem auxFracPoly_injective (K : Type*) [CommRing K] [IsDomain K] (k : ℕ) :
    Function.Injective (auxFracPoly K k) :=
  (auxFracCastSucc_injective K k).comp
    (IsFractionRing.injective (MvPolynomial (Fin k) K) (AuxFrac K k))

/-- The inclusion of the lower polynomial ring carries the auxiliary variable `y_{l+1}` to the
auxiliary variable of the same index one level up. -/
theorem auxFracPoly_X [IsDomain K] (l : Fin k) :
    auxFracPoly K k (MvPolynomial.X l) = yFrac K l.castSucc := by
  rw [auxFracPoly_apply, show algebraMap (MvPolynomial (Fin k) K) (AuxFrac K k)
    (MvPolynomial.X l) = yFrac K l from rfl, auxFracCastSucc_yFrac]

/-! ### The expansion coefficient over the lower polynomial ring -/

/-- **The coefficient `c_j` of `y_{k+1}^j` read over the lower polynomial ring**: the series in the
free variables whose coefficient at `x^α` is the coefficient of `Y^j` in the polynomial that
`HJO.Sym.auxSplitLast` makes of the coefficient of `F` at `x^α`. For `F` in `P_{k+1}` this is the
`c_j` of the expansion, with its coefficients where they belong — in `𝕜[y_1, …, y_{k-1}]` and
not merely in `𝕜(y_1, …, y_{k-1})` — and `HJO.Sym.map_zPartPoly` identifies it with
`HJO.Sym.zPart` of the image of `F` in `P°_{k+1}`. -/
noncomputable def zPartPoly (K : Type*) [CommRing K] (k : ℕ) (F : AuxAlphabetSeries K (k + 1))
    (j : ℕ) : AuxAlphabetSeries K k :=
  fun α => (auxSplitLast K k (MvPowerSeries.coeff α F)).coeff j

theorem coeff_zPartPoly (F : AuxAlphabetSeries K (k + 1)) (j : ℕ) (α : ℕ →₀ ℕ) :
    MvPowerSeries.coeff α (zPartPoly K k F j)
      = (auxSplitLast K k (MvPowerSeries.coeff α F)).coeff j :=
  rfl

/-- **The expansion coefficient over the lower polynomial ring is `HJO.Sym.zPart`** once its
coefficients are pushed into the coefficient field of `P°_{k+1}`. This is
`HJO.Sym.zCoeff_auxToFrac`, read as an identity between series and not between coefficients. -/
theorem map_zPartPoly [IsDomain K] (F : AuxAlphabetSeries K (k + 1)) (j : ℕ) :
    MvPowerSeries.map (auxFracPoly K k) (zPartPoly K k F j)
      = zPart K k (auxToFrac K (k + 1) F) j :=
  MvPowerSeries.ext fun α => by
    rw [MvPowerSeries.coeff_map, coeff_zPartPoly, coeff_zPart, zCoeff_auxToFrac, auxFracPoly_apply]

/-- **The bound on the merged degree bounds the degree of each expansion coefficient**: if the
merged coefficients of `F` vanish in merged degree above `N`, then `c_j` has no monomial of degree
above `N` in the free variables — the "bounded degree in the free variables" of the expansion
argument. -/
theorem coeff_zPartPoly_eq_zero_of_lt [IsDomain K] {F : AuxAlphabetSeries K (k + 1)} {N : ℕ}
    (hN : ∀ μ : Option ℕ →₀ ℕ, N < Finsupp.degree μ → zCoeff K k (auxToFrac K (k + 1) F) μ = 0)
    (j : ℕ) {α : ℕ →₀ ℕ} (hα : N < j + Finsupp.degree α) :
    MvPowerSeries.coeff α (zPartPoly K k F j) = 0 := by
  refine auxFracPoly_injective K k ?_
  rw [map_zero, ← MvPowerSeries.coeff_map, map_zPartPoly, coeff_zPart,
    hN _ (by rw [degree_optionElim]; omega), map_zero]

/-! ### Relabelling the letters of the merged alphabet -/

/-- The permutation of the merged alphabet induced by a permutation of the letters fixes the
distinguished letter. -/
theorem optionCongr_none (σ : Equiv.Perm ℕ) : σ.optionCongr none = none := rfl

theorem optionCongr_some (σ : Equiv.Perm ℕ) (i : ℕ) : σ.optionCongr (some i) = some (σ i) := rfl

/-- **Relabelling the letters commutes with prescribing the exponent of the distinguished letter**:
the induced permutation of the merged alphabet leaves that exponent where it is and relabels the
letter part. -/
private theorem equivMapDomain_optionCongr_optionElim (σ : Equiv.Perm ℕ) (α : ℕ →₀ ℕ) (b : ℕ) :
    Finsupp.equivMapDomain σ.optionCongr.symm (α.optionElim b)
      = (Finsupp.equivMapDomain σ.symm α).optionElim b := by
  refine Finsupp.ext fun a => ?_
  rw [Finsupp.equivMapDomain_apply, Equiv.symm_symm]
  cases a with
  | none => rw [optionCongr_none, Finsupp.optionElim_apply_none, Finsupp.optionElim_apply_none]
  | some i =>
    rw [optionCongr_some, Finsupp.optionElim_apply_some, Finsupp.optionElim_apply_some,
      Finsupp.equivMapDomain_apply, Equiv.symm_symm]

/-- **An adjacent interchange of letters moves at most two letters of the merged alphabet**, so the
finitarity hypothesis of `HJO.Sym.zPerm_eq_self_of_forall_zSwap_eq_self` is met by the induced
permutation. -/
theorem finite_compl_fixedBy_optionCongr_swap (m : ℕ) :
    (MulAction.fixedBy (Option ℕ) (Equiv.swap m (m + 1)).optionCongr)ᶜ.Finite := by
  refine Set.Finite.subset ((Set.finite_singleton (some (m + 1))).insert (some m)) fun a ha => ?_
  have ha' : (Equiv.swap m (m + 1)).optionCongr a ≠ a := ha
  cases a with
  | none => exact absurd (optionCongr_none _) ha'
  | some i =>
    have hi : Equiv.swap m (m + 1) i ≠ i := fun h =>
      ha' (by rw [optionCongr_some, h])
    rcases eq_or_ne i m with rfl | him
    · exact Set.mem_insert _ _
    rcases eq_or_ne i (m + 1) with rfl | him'
    · exact Set.mem_insert_of_mem _ rfl
    · exact absurd (Equiv.swap_apply_of_ne_of_ne him him') hi

/-- **A relabelling of the letters acts on a series free of `y_{k+1}` by relabelling its
coefficients.** The induced permutation fixes the distinguished letter, so the only surviving term
of `HJO.Sym.zPerm` is the one in `y_{k+1}`-degree `0`, and that term is the coefficient of the
series at the relabelled letter-monomial. -/
theorem coeff_zPerm_optionCongr_of_mem_zBase [IsDomain K]
    {A : AuxAlphabetSeriesFrac K (k + 1)} (hA : A ∈ zBase K k) (σ : Equiv.Perm ℕ) (α : ℕ →₀ ℕ) :
    MvPowerSeries.coeff α (zPerm K k σ.optionCongr A)
      = MvPowerSeries.coeff (Finsupp.equivMapDomain σ.symm α) A := by
  classical
  rw [coeff_zPerm]
  have hterm : ∀ b : ℕ, auxFracCastSucc K k
        (zCoeff K k A (Finsupp.equivMapDomain σ.optionCongr.symm (α.optionElim b)))
        * yFrac K (Fin.last k) ^ b
      = if b = 0 then MvPowerSeries.coeff (Finsupp.equivMapDomain σ.symm α) A else 0 := by
    intro b
    rw [equivMapDomain_optionCongr_optionElim]
    rcases eq_or_ne b 0 with rfl | hb
    · rw [ite_eq_left rfl, pow_zero, mul_one, auxFracCastSucc_zCoeff_of_mem_zBase hA]
    · rw [ite_eq_right hb, zCoeff_eq_zero_of_mem_zBase hA
        (by rw [Finsupp.optionElim_apply_none]; exact hb), map_zero, zero_mul]
  rw [finsum_congr hterm, finsum_eq_single _ 0 fun b hb => ite_eq_right hb, ite_eq_left rfl]

/-- **The expansion coefficient over the lower polynomial ring inherits the symmetry in the
letters.** The invariance of `c_j` under the relabellings of the merged alphabet fixing `y_{k+1}`,
which for `χ'_{Id_k}(π)` is
`HJO.Dyck.zPerm_zPart_auxToFrac_unnormalisedCharSeries_identityTuple`, says exactly that the
coefficients of `HJO.Sym.zPartPoly` are permuted along `σ`, the comparison map being injective. -/
theorem letterPerm_zPartPoly [IsDomain K] (F : AuxAlphabetSeries K (k + 1)) (j : ℕ)
    (σ : Equiv.Perm ℕ)
    (hfix : zPerm K k σ.optionCongr (zPart K k (auxToFrac K (k + 1) F) j)
      = zPart K k (auxToFrac K (k + 1) F) j) :
    letterPerm (MvPolynomial (Fin k) K) σ (zPartPoly K k F j) = zPartPoly K k F j := by
  refine MvPowerSeries.ext fun α => auxFracPoly_injective K k ?_
  have hL : ∀ β : ℕ →₀ ℕ, auxFracPoly K k (MvPowerSeries.coeff β (zPartPoly K k F j))
      = MvPowerSeries.coeff β (zPart K k (auxToFrac K (k + 1) F) j) := fun β => by
    rw [← map_zPartPoly, MvPowerSeries.coeff_map]
  rw [coeff_letterPerm, hL, hL, ← coeff_zPerm_optionCongr_of_mem_zBase (zPart_mem_zBase _ j) σ α,
    hfix]

/-! ### A bound on the merged degree, in the polynomial ring -/

/-- **`F` has merged degree at most `D`**: writing each coefficient of `F` as a polynomial in
`y_{k+1}` over `𝕜[y_1, …, y_k]`, the coefficient of `y_{k+1}^b x^α` vanishes as soon as
`b + |α| > D`. This is the degree bound of `HJO.Sym.zGraded` stated inside `P_{k+1}`, where
`HJO.Sym.auxSplitLast` is a ring homomorphism and the bound is therefore *additive under
multiplication* — which is what the triangular recursion of
`HJO.Dyck.existsUnique_eq_sum_pow_mul_realiseAddLetter` needs of it, and why it is used here in
place of the `Set`-shaped `HJO.Sym.zGraded`. It is equivalent to the bound on the merged
coefficients: `HJO.Sym.mergedLE_of_zCoeff_eq_zero` and `HJO.Sym.zCoeff_eq_zero_of_mergedLE`. -/
def MergedLE (K : Type*) [CommRing K] (k D : ℕ) (F : AuxAlphabetSeries K (k + 1)) : Prop :=
  ∀ (α : ℕ →₀ ℕ) (b : ℕ), D < b + Finsupp.degree α →
    (auxSplitLast K k (MvPowerSeries.coeff α F)).coeff b = 0

variable {D E : ℕ} {F G : AuxAlphabetSeries K (k + 1)}

theorem mergedLE_mono (h : D ≤ E) (hF : MergedLE K k D F) : MergedLE K k E F :=
  fun α b hb => hF α b (by omega)

theorem mergedLE_zero (K : Type*) [CommRing K] (k D : ℕ) :
    MergedLE K k D (0 : AuxAlphabetSeries K (k + 1)) := fun _ _ _ => by
  rw [MvPowerSeries.coeff_zero, map_zero, Polynomial.coeff_zero]

theorem mergedLE_add (hF : MergedLE K k D F) (hG : MergedLE K k D G) : MergedLE K k D (F + G) :=
  fun α b hb => by rw [map_add, map_add, Polynomial.coeff_add, hF α b hb, hG α b hb, add_zero]

theorem mergedLE_neg (hF : MergedLE K k D F) : MergedLE K k D (-F) := fun α b hb => by
  rw [map_neg, map_neg, Polynomial.coeff_neg, hF α b hb, neg_zero]

theorem mergedLE_sub (hF : MergedLE K k D F) (hG : MergedLE K k D G) : MergedLE K k D (F - G) := by
  rw [sub_eq_add_neg]
  exact mergedLE_add hF (mergedLE_neg hG)

theorem mergedLE_sum {S : Type*} {t : Finset S} {H : S → AuxAlphabetSeries K (k + 1)}
    (hH : ∀ i ∈ t, MergedLE K k D (H i)) : MergedLE K k D (∑ i ∈ t, H i) := by
  classical
  induction t using Finset.induction with
  | empty => rw [Finset.sum_empty]; exact mergedLE_zero K k D
  | insert a t ha ih =>
    rw [Finset.sum_insert ha]
    exact mergedLE_add (hH a (Finset.mem_insert_self a t))
      (ih fun i hi => hH i (Finset.mem_insert_of_mem hi))

/-- **The merged degree is additive under multiplication.** A coefficient of a product is a sum over
the factorisations of the letter-monomial and of the power of `y_{k+1}`, and in each summand the two
merged degrees add up to more than `D + E`, so one of the two factors already vanishes. -/
theorem mergedLE_mul (hF : MergedLE K k D F) (hG : MergedLE K k E G) :
    MergedLE K k (D + E) (F * G) := by
  classical
  intro α b hb
  rw [MvPowerSeries.coeff_mul, map_sum, Polynomial.finsetSum_coeff]
  refine Finset.sum_eq_zero fun p hp => ?_
  rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp
  rw [map_mul, Polynomial.coeff_mul]
  refine Finset.sum_eq_zero fun c hc => ?_
  rw [Finset.HasAntidiagonal.mem_antidiagonal] at hc
  have hdeg : Finsupp.degree p.1 + Finsupp.degree p.2 = Finsupp.degree α := by
    rw [← AddMonoidHom.map_add Finsupp.degree, hp]
  rcases le_or_gt (c.1 + Finsupp.degree p.1) D with h1 | h1
  · rw [hG p.2 c.2 (by omega), mul_zero]
  · rw [hF p.1 c.1 h1, zero_mul]

theorem mergedLE_one (K : Type*) [CommRing K] (k : ℕ) :
    MergedLE K k 0 (1 : AuxAlphabetSeries K (k + 1)) := by
  classical
  intro α b hb
  rw [MvPowerSeries.coeff_one]
  split_ifs with h
  · subst h
    rw [map_zero Finsupp.degree] at hb
    rw [map_one, Polynomial.coeff_one]
    exact ite_eq_right (by omega)
  · rw [map_zero, Polynomial.coeff_zero]

theorem mergedLE_pow (hF : MergedLE K k D F) (n : ℕ) : MergedLE K k (n * D) (F ^ n) := by
  induction n with
  | zero => rw [Nat.zero_mul, pow_zero]; exact mergedLE_one K k
  | succ n ih =>
    rw [pow_succ, show (n + 1) * D = n * D + D from by ring]
    exact mergedLE_mul ih hF

theorem mergedLE_prod {S : Type*} {t : Finset S} {D : S → ℕ}
    {H : S → AuxAlphabetSeries K (k + 1)} (hH : ∀ i ∈ t, MergedLE K k (D i) (H i)) :
    MergedLE K k (∑ i ∈ t, D i) (∏ i ∈ t, H i) := by
  classical
  induction t using Finset.induction with
  | empty => rw [Finset.sum_empty, Finset.prod_empty]; exact mergedLE_one K k
  | insert a t ha ih =>
    rw [Finset.sum_insert ha, Finset.prod_insert ha]
    exact mergedLE_mul (hH a (Finset.mem_insert_self a t))
      (ih fun i hi => hH i (Finset.mem_insert_of_mem hi))

/-- A constant of the lower polynomial ring has merged degree `0`: it involves neither `y_{k+1}` nor
a letter. -/
theorem mergedLE_C_rename (p : MvPolynomial (Fin k) K) :
    MergedLE K k 0 ((MvPowerSeries.C (MvPolynomial.rename Fin.castSucc p)) :
      AuxAlphabetSeries K (k + 1)) := by
  classical
  intro α b hb
  rw [MvPowerSeries.coeff_C]
  split_ifs with h
  · subst h
    rw [map_zero Finsupp.degree] at hb
    rw [auxSplitLast_rename_castSucc, Polynomial.coeff_C]
    exact ite_eq_right (by omega)
  · rw [map_zero, Polynomial.coeff_zero]

/-- The `n`-th power of the distinguished auxiliary variable has merged degree `n`. -/
theorem mergedLE_C_X_last_pow (K : Type*) [CommRing K] (k n : ℕ) :
    MergedLE K k n (((MvPowerSeries.C (MvPolynomial.X (Fin.last k))) :
      AuxAlphabetSeries K (k + 1)) ^ n) := by
  classical
  intro α b hb
  rw [← map_pow, MvPowerSeries.coeff_C]
  split_ifs with h
  · subst h
    rw [map_zero Finsupp.degree] at hb
    rw [map_pow, auxSplitLast_X_last, Polynomial.coeff_X_pow]
    exact ite_eq_right (by omega)
  · rw [map_zero, Polynomial.coeff_zero]

/-- **The merged bound in `P_{k+1}` is the merged bound in `P°_{k+1}`**, read forwards: the merged
coefficients of the image of `F` vanish above the merged degree `D`. -/
theorem zCoeff_eq_zero_of_mergedLE [IsDomain K] (hF : MergedLE K k D F) {μ : Option ℕ →₀ ℕ}
    (hμ : D < Finsupp.degree μ) : zCoeff K k (auxToFrac K (k + 1) F) μ = 0 := by
  have hd : Finsupp.degree μ = μ none + Finsupp.degree μ.some := degree_eq_add_degree_some μ
  rw [← Finsupp.optionElim_some μ, zCoeff_auxToFrac, hF μ.some (μ none) (by omega), map_zero]

/-- **The merged bound in `P_{k+1}` is the merged bound in `P°_{k+1}`**, read backwards: the
comparison map is injective, so the vanishing of the merged coefficients of the image is the
vanishing of the polynomial coefficients. -/
theorem mergedLE_of_zCoeff_eq_zero [IsDomain K] {N : ℕ}
    (hN : ∀ μ : Option ℕ →₀ ℕ, N < Finsupp.degree μ → zCoeff K k (auxToFrac K (k + 1) F) μ = 0) :
    MergedLE K k N F := fun α b hb =>
  IsFractionRing.injective (MvPolynomial (Fin k) K) (AuxFrac K k) (by
    rw [map_zero, ← zCoeff_auxToFrac, hN _ (by rw [degree_optionElim]; omega)])

/-! ### The distinguished letter as a factor -/

/-- The `n`-th power of the distinguished letter, as a merged monomial. -/
theorem zMonomial_single_none_pow [IsDomain K] (n : ℕ) :
    zMonomial K k (Finsupp.single none n) 1
      = ((MvPowerSeries.C (yFrac K (Fin.last k))) : AuxAlphabetSeriesFrac K (k + 1)) ^ n := by
  rw [zMonomial, Finsupp.some_single_none, Finsupp.single_eq_same, map_one, one_mul,
    MvPowerSeries.monomial_zero_eq_C_apply, map_pow]

/-- The `n`-th power of the distinguished letter lies in `Z^{(k+1)}_n`, hence in `Z^{(k+1)}`. -/
theorem C_yFrac_pow_mem_zRing [IsDomain K] (n : ℕ) :
    (((MvPowerSeries.C (yFrac K (Fin.last k))) : AuxAlphabetSeriesFrac K (k + 1)) ^ n)
      ∈ zRing K k := by
  refine zGraded_subset_zRing K k n ?_
  have h := monomial_mem_zGraded (K := K) (k := k) (d := n) (b := n) (α := 0)
    (by rw [map_zero Finsupp.degree, Nat.add_zero]) 1
  rwa [map_one, one_mul, MvPowerSeries.monomial_zero_eq_C_apply, map_pow] at h

/-- A relabelling fixing the distinguished letter fixes each of its powers. -/
theorem zPerm_C_yFrac_pow [IsDomain K] {ρ : Equiv.Perm (Option ℕ)} (hρ : ρ none = none) (n : ℕ) :
    zPerm K k ρ (((MvPowerSeries.C (yFrac K (Fin.last k))) : AuxAlphabetSeriesFrac K (k + 1)) ^ n)
      = MvPowerSeries.C (yFrac K (Fin.last k)) ^ n := by
  rw [← zMonomial_single_none_pow, zPerm_zMonomial, Finsupp.equivMapDomain_single, hρ]

/-- A relabelling fixing the distinguished letter passes a power of it through a product. -/
theorem zPerm_C_yFrac_pow_mul [IsDomain K] {ρ : Equiv.Perm (Option ℕ)} (hρ : ρ none = none)
    (n : ℕ) {B : AuxAlphabetSeriesFrac K (k + 1)} (hB : B ∈ zRing K k) :
    zPerm K k ρ (MvPowerSeries.C (yFrac K (Fin.last k)) ^ n * B)
      = MvPowerSeries.C (yFrac K (Fin.last k)) ^ n * zPerm K k ρ B := by
  rw [zPerm_mul_of_mem_zRing ρ (C_yFrac_pow_mem_zRing n) hB, zPerm_C_yFrac_pow hρ]

/-! ### The expansion is additive -/

variable [IsDomain K] {G' H' : AuxAlphabetSeriesFrac K (k + 1)}

/-- The expansion coefficient is additive on the series whose coefficients are polynomial in
`y_{k+1}`: `HJO.Sym.zPart_sum` at two summands, in the form the triangular recursion subtracts
with. -/
theorem zPart_add' (hG : ∀ α : ℕ →₀ ℕ, MvPowerSeries.coeff α G' ∈ (yFracEval K k).range)
    (hH : ∀ α : ℕ →₀ ℕ, MvPowerSeries.coeff α H' ∈ (yFracEval K k).range) (j : ℕ) :
    zPart K k (G' + H') j = zPart K k G' j + zPart K k H' j :=
  MvPowerSeries.ext fun α => by
    rw [map_add, coeff_zPart, coeff_zPart, coeff_zPart, zCoeff, zCoeff, zCoeff, map_add,
      yFracCoeff_add_of_mem_range (hG _) (hH _), map_add]

theorem zPart_sub' (hG : ∀ α : ℕ →₀ ℕ, MvPowerSeries.coeff α G' ∈ (yFracEval K k).range)
    (hH : ∀ α : ℕ →₀ ℕ, MvPowerSeries.coeff α H' ∈ (yFracEval K k).range) (j : ℕ) :
    zPart K k (G' - H') j = zPart K k G' j - zPart K k H' j := by
  have hGH : ∀ α : ℕ →₀ ℕ, MvPowerSeries.coeff α (G' - H') ∈ (yFracEval K k).range := fun α => by
    rw [map_sub]
    exact sub_mem (hG α) (hH α)
  have h := zPart_add' hGH hH j
  rw [sub_add_cancel] at h
  exact eq_sub_of_add_eq h.symm

end HJO.Sym

namespace HJO.Sweep

/-! ### `V_{k-1}` as the symmetric functions over the lower polynomial ring -/

variable {K : Type*} [CommRing K] {k : ℕ}

/-- The lower polynomial ring inside the total space of the sweep: `𝕜[y_1, …, y_k] → V_*` sending
`y_{i+1}` to the auxiliary variable of the same index. Its image is inside `V_k`. -/
noncomputable def auxToTotal (K : Type*) [CommRing K] (k : ℕ) :
    MvPolynomial (Fin k) K →ₐ[K] Total K :=
  MvPolynomial.aeval fun i : Fin k => (MvPolynomial.X (i : ℕ) : Total K)

@[simp]
theorem auxToTotal_C (a : K) : auxToTotal K k (MvPolynomial.C a) = algebraMap K (Total K) a :=
  MvPolynomial.aeval_C _ a

@[simp]
theorem auxToTotal_X (i : Fin k) :
    auxToTotal K k (MvPolynomial.X i) = (MvPolynomial.X (i : ℕ) : Total K) :=
  MvPolynomial.aeval_X _ i

theorem auxToTotal_mem_piece (r : MvPolynomial (Fin k) K) : auxToTotal K k r ∈ piece K k := by
  induction r using MvPolynomial.induction_on with
  | C a =>
    rw [auxToTotal_C, show algebraMap K (Total K) a
      = algebraMap (Sym.Lambda K) (Total K) (MvPolynomial.C a) from rfl]
    exact (piece K k).algebraMap_mem _
  | add p q hp hq => rw [map_add]; exact add_mem hp hq
  | mul_X p i hp => rw [map_mul, auxToTotal_X]; exact mul_mem hp (X_mem_piece i.isLt)

/-- Adding a letter fixes a polynomial in the auxiliary variables: `ρ_i` fixes each `y_j`. -/
theorem addLetter_auxToTotal (i : ℕ) (r : MvPolynomial (Fin k) K) :
    addLetter K i (auxToTotal K k r) = auxToTotal K k r := by
  induction r using MvPolynomial.induction_on with
  | C a => rw [auxToTotal_C, AlgHom.commutes]
  | add p q hp hq => rw [map_add, map_add, hp, hq]
  | mul_X p j hp => rw [map_mul, map_mul, hp, auxToTotal_X, addLetter_auxVar]

/-- **`V_{k-1}` presented as the symmetric functions over the lower polynomial ring**: the
`𝕜`-algebra map `Λ(𝕜[y_1, …, y_k]) → V_*` sending the generator `p_{r+1}` to `p_{r+1}` and the
scalar `y_{i+1}` to the auxiliary variable `y_{i+1}`. It lands in `V_k`
(`HJO.Sweep.pieceLift_mem_piece`) and is onto it (`HJO.Sweep.exists_pieceLift_eq`), which is the
tensor decomposition `HJO.Sweep.pieceTensorAlgEquiv` in the form the realisation reads. -/
noncomputable def pieceLift (K : Type*) [CommRing K] (k : ℕ) :
    Sym.Lambda (MvPolynomial (Fin k) K) →ₐ[K] Total K :=
  MvPolynomial.aevalTower (auxToTotal K k) fun r : ℕ => MvPolynomial.C (Sym.powerSum K (r + 1))

@[simp]
theorem pieceLift_C (r : MvPolynomial (Fin k) K) :
    pieceLift K k (MvPolynomial.C r) = auxToTotal K k r :=
  MvPolynomial.aevalTower_C _ _ _

@[simp]
theorem pieceLift_X (n : ℕ) :
    pieceLift K k (MvPolynomial.X n) = MvPolynomial.C (Sym.powerSum K (n + 1)) :=
  MvPolynomial.aevalTower_X _ _ _

theorem pieceLift_mem_piece (f : Sym.Lambda (MvPolynomial (Fin k) K)) :
    pieceLift K k f ∈ piece K k := by
  induction f using MvPolynomial.induction_on with
  | C r => rw [pieceLift_C]; exact auxToTotal_mem_piece r
  | add p q hp hq => rw [map_add]; exact add_mem hp hq
  | mul_X p n hp =>
    rw [map_mul, pieceLift_X]
    exact mul_mem hp ((piece K k).algebraMap_mem _)

/-- Every symmetric function, read inside the total space as a constant, is a value of
`HJO.Sweep.pieceLift`: the generator `p_{n+1}` is the value at the generator `X n` and a scalar is
the value at a scalar. -/
private theorem exists_pieceLift_eq_C (c : Sym.Lambda K) :
    ∃ f : Sym.Lambda (MvPolynomial (Fin k) K), pieceLift K k f = MvPolynomial.C c := by
  induction c using MvPolynomial.induction_on with
  | C a =>
    refine ⟨MvPolynomial.C (MvPolynomial.C a), ?_⟩
    rw [pieceLift_C, auxToTotal_C]
    rfl
  | add p q hp hq =>
    obtain ⟨f, hf⟩ := hp
    obtain ⟨g, hg⟩ := hq
    exact ⟨f + g, by rw [map_add, hf, hg, map_add]⟩
  | mul_X p n hp =>
    obtain ⟨f, hf⟩ := hp
    refine ⟨f * MvPolynomial.X n, ?_⟩
    rw [map_mul, hf, pieceLift_X, map_mul, Sym.powerSum, Nat.add_sub_cancel]

/-- **`HJO.Sweep.pieceLift` is onto `V_k`.** Its image is a subalgebra containing every constant of
`Λ` and every auxiliary variable below the level, which is what generates `V_k`. Together with
`HJO.Sweep.pieceLift_mem_piece` this says `V_k` *is* the ring of symmetric functions over
`𝕜[y_1, …, y_k]`, which is `HJO.Sweep.pieceTensorAlgEquiv` in the form the realisation reads. -/
theorem exists_pieceLift_eq {F : Total K} (hF : F ∈ piece K k) :
    ∃ f : Sym.Lambda (MvPolynomial (Fin k) K), pieceLift K k f = F := by
  rw [piece, MvPolynomial.supported_eq_adjoin_X] at hF
  induction hF using Algebra.adjoin_induction with
  | mem y hy =>
    obtain ⟨j, hj, rfl⟩ := hy
    have hjk : j < k := hj
    exact ⟨MvPolynomial.C (MvPolynomial.X ⟨j, hjk⟩), by rw [pieceLift_C, auxToTotal_X]⟩
  | algebraMap c =>
    obtain ⟨f, hf⟩ := exists_pieceLift_eq_C (k := k) c
    exact ⟨f, hf⟩
  | add u v _ _ hu hv =>
    obtain ⟨f, hf⟩ := hu
    obtain ⟨g, hg⟩ := hv
    exact ⟨f + g, by rw [map_add, hf, hg]⟩
  | mul u v _ _ hu hv =>
    obtain ⟨f, hf⟩ := hu
    obtain ⟨g, hg⟩ := hv
    exact ⟨f * g, by rw [map_mul, hf, hg]⟩

end HJO.Sweep

namespace HJO.Dyck

open HJO.Sweep

variable {K : Type*} [CommRing K] [IsDomain K] {k : ℕ}
  {ι : Sweep.Total K →ₐ[K] Sym.AuxAlphabetSeries K (k + 1)}

/-! ### The realisation on `V_{k-1}` is the classical realisation over the lower ring -/

omit [IsDomain K] in
/-- **The realisation of a scalar of the lower polynomial ring is that scalar as a constant
series.** Both sides are ring homomorphisms out of `𝕜[y_1, …, y_k]`, and they agree on the scalars
of `𝕜` and on each auxiliary variable, the latter by
`HJO.Dyck.IsAuxRealisation.map_auxVar`. -/
theorem realise_auxToTotal (hι : IsAuxRealisation (k + 1) ι) (r : MvPolynomial (Fin k) K) :
    ι (auxToTotal K k r) = MvPowerSeries.C (MvPolynomial.rename Fin.castSucc r) := by
  have h : (ι.toRingHom.comp (auxToTotal K k).toRingHom)
      = (MvPowerSeries.C :
          MvPolynomial (Fin (k + 1)) K →+* Sym.AuxAlphabetSeries K (k + 1)).comp
        (MvPolynomial.rename Fin.castSucc).toRingHom := by
    refine MvPolynomial.ringHom_ext (fun a => ?_) fun i => ?_
    · have h2 : (algebraMap K (Sym.AuxAlphabetSeries K (k + 1)) a)
          = MvPowerSeries.C (MvPolynomial.C a) := by
        rw [MvPowerSeries.algebraMap_apply, MvPolynomial.algebraMap_eq]
      simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
      rw [auxToTotal_C, AlgHom.commutes, h2, MvPolynomial.rename_C]
    · have hj : (i : ℕ) < k + 1 := by omega
      have haux : (MvPolynomial.X (i : ℕ) : Sweep.Total K)
          = auxVar (((⟨(i : ℕ), hj⟩ : Fin (k + 1)) : ℕ) + 1) := by
        rw [auxVar, Nat.add_sub_cancel]
      have hcast : (⟨(i : ℕ), hj⟩ : Fin (k + 1)) = Fin.castSucc i := rfl
      simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
      rw [auxToTotal_X, haux, hι.map_auxVar ⟨(i : ℕ), hj⟩, hcast, MvPolynomial.rename_X]
  exact RingHom.congr_fun h r

/-- The realisation of a scalar of the lower polynomial ring, read in `P°_{k+1}`: the constant
series that scalar becomes in the coefficient field. -/
theorem auxToFrac_realise_auxToTotal (hι : IsAuxRealisation (k + 1) ι)
    (r : MvPolynomial (Fin k) K) :
    Sym.auxToFrac K (k + 1) (ι (auxToTotal K k r))
      = MvPowerSeries.C (Sym.auxFracPoly K k r) := by
  rw [realise_auxToTotal hι, auxToFrac_C, Sym.auxFracPoly_apply, Sym.auxFracCastSucc_algebraMap]

/-- **The realisation with auxiliary variables restricted to `V_{k-1}` is the classical realisation
over the lower polynomial ring.** Both sides are ring homomorphisms out of `Λ(𝕜[y_1, …, y_k])`, and
they agree on the two families of generators: on a scalar by
`HJO.Dyck.auxToFrac_realise_auxToTotal`, and on the generator `p_{r+1}` because both realise it as
the `(r+1)`-st power sum of the alphabet, whose coefficients are `1` and `0`. -/
theorem auxToFrac_realise_pieceLift (hι : IsAuxRealisation (k + 1) ι)
    (f : Sym.Lambda (MvPolynomial (Fin k) K)) :
    Sym.auxToFrac K (k + 1) (ι (pieceLift K k f))
      = MvPowerSeries.map (Sym.auxFracPoly K k) (PhiMul.realise (MvPolynomial (Fin k) K) f) := by
  classical
  have h : (((Sym.auxToFrac K (k + 1)).toRingHom.comp ι.toRingHom).comp
        (pieceLift K k).toRingHom)
      = (MvPowerSeries.map (Sym.auxFracPoly K k)).comp
        (PhiMul.realise (MvPolynomial (Fin k) K)).toRingHom := by
    refine MvPolynomial.ringHom_ext (fun r => ?_) fun n => ?_
    · have hR : PhiMul.realise (MvPolynomial (Fin k) K) (MvPolynomial.C r)
          = MvPowerSeries.C r := by
        rw [show (MvPolynomial.C r : Sym.Lambda (MvPolynomial (Fin k) K))
            = algebraMap (MvPolynomial (Fin k) K) _ r from rfl, AlgHom.commutes,
          MvPowerSeries.algebraMap_apply]
        simp
      simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, pieceLift_C,
        auxToFrac_realise_auxToTotal hι, hR, MvPowerSeries.map_C]
    · have hR : PhiMul.realise (MvPolynomial (Fin k) K) (MvPolynomial.X n)
          = PhiMul.alphabetPowerSum (MvPolynomial (Fin k) K) (n + 1) :=
        MvPolynomial.aeval_X _ n
      simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, pieceLift_X, hR]
      refine MvPowerSeries.ext fun α => ?_
      rw [Sym.coeff_auxToFrac, MvPowerSeries.coeff_map]
      by_cases hα : ∃ i : ℕ, α = Finsupp.single i (n + 1)
      · obtain ⟨i, rfl⟩ := hα
        rw [hι.coeff_pow n i, PhiMul.coeff_alphabetPowerSum_single, map_one, map_one]
      · simp only [not_exists] at hα
        rw [hι.coeff_of_ne n α hα, PhiMul.coeff_alphabetPowerSum_of_ne _ _ _ hα, map_zero,
          map_zero]
  exact RingHom.congr_fun h f

/-! ### The merged degree of the realisation of an element of `V_{k-1}` -/

omit [IsDomain K] in
/-- A scalar of the lower polynomial ring has merged degree `0`, and adding the letter does not
change it: `ρ_{k+1}` fixes every auxiliary variable. -/
theorem mergedLE_realise_addLetter_auxToTotal (hι : IsAuxRealisation (k + 1) ι)
    (r : MvPolynomial (Fin k) K) :
    Sym.MergedLE K k 0 (ι (addLetter K (k + 1) (auxToTotal K k r))) := by
  rw [addLetter_auxToTotal, realise_auxToTotal hι]
  exact Sym.mergedLE_C_rename r

omit [IsDomain K] in
/-- The realisation of the power sum `p_{r+1}` has merged degree `r + 1`: its coefficients are `1`
at the letter-monomials `x_i^{r+1}`, of degree `r + 1`, and `0` elsewhere. -/
theorem mergedLE_realise_powerSum (hι : IsAuxRealisation (k + 1) ι) (r : ℕ) :
    Sym.MergedLE K k (r + 1) (ι (MvPolynomial.C (Sym.powerSum K (r + 1)))) := by
  classical
  intro α b hb
  by_cases hα : ∃ i : ℕ, α = Finsupp.single i (r + 1)
  · obtain ⟨i, rfl⟩ := hα
    rw [Finsupp.degree_single] at hb
    rw [hι.coeff_pow r i, map_one, Polynomial.coeff_one]
    exact ite_eq_right (by omega)
  · simp only [not_exists] at hα
    rw [hι.coeff_of_ne r α hα, map_zero, Polynomial.coeff_zero]

omit [IsDomain K] in
/-- **The generator with the letter added has merged degree its weight**: `ρ_{k+1}(p_{n+1})` is
`p_{n+1} + y_{k+1}^{n+1}`, and both the power sum of the alphabet and the power of the distinguished
letter have merged degree `n + 1`. -/
theorem mergedLE_realise_addLetter_pieceLift_X (hι : IsAuxRealisation (k + 1) ι) (n : ℕ) :
    Sym.MergedLE K k (n + 1) (ι (addLetter K (k + 1) (pieceLift K k (MvPolynomial.X n)))) := by
  have hy : ι (auxVar (k + 1) : Sweep.Total K)
      = MvPowerSeries.C (MvPolynomial.X (Fin.last k)) := by
    have h := hι.map_auxVar (Fin.last k)
    rwa [Fin.val_last] at h
  rw [pieceLift_X, addLetter_powerSum, map_add, map_pow, hy]
  exact Sym.mergedLE_add (mergedLE_realise_powerSum hι n) (Sym.mergedLE_C_X_last_pow K k (n + 1))

omit [IsDomain K] in
/-- **`g[X + y_{k+1}]` realised has merged degree the weight of `g`.** For `g` of weight `d` in the
power sums, the realisation of `ρ_{k+1}(g)` is a combination of products of `d` merged letters, so
no monomial `y_{k+1}^b x^α` with `b + |α| > d` occurs in it.

This is the bookkeeping the triangular recursion of
`HJO.Dyck.existsUnique_eq_sum_pow_mul_realiseAddLetter` needs in order to terminate: it bounds the
merged degree of the term `y_k^{j}g_j[X + y_k]` by `j` plus the weight of `g_j`, and the weight of
`g_j` is bounded by the degree of the coefficient `c_j` it was produced from. The merged degree is
multiplicative in the polynomial ring `P_{k+1}` — `HJO.Sym.mergedLE_mul` — which is why the bound is
carried there and not as membership in `HJO.Sym.zGraded`. -/
theorem mergedLE_realise_addLetter_pieceLift (hι : IsAuxRealisation (k + 1) ι) {d : ℕ}
    {f : Sym.Lambda (MvPolynomial (Fin k) K)}
    (hf : f ∈ Sym.LambdaComp (MvPolynomial (Fin k) K) d) :
    Sym.MergedLE K k d (ι (addLetter K (k + 1) (pieceLift K k f))) := by
  classical
  set Ψ : Sym.Lambda (MvPolynomial (Fin k) K) →+* Sym.AuxAlphabetSeries K (k + 1) :=
    (ι.toRingHom.comp (addLetter K (k + 1)).toRingHom).comp (pieceLift K k).toRingHom with hΨdef
  have hΨ : ∀ g, Ψ g = ι (addLetter K (k + 1) (pieceLift K k g)) := fun _ => rfl
  rw [← hΨ, MvPolynomial.as_sum f, map_sum]
  refine Sym.mergedLE_sum fun e he => ?_
  have hw : Finsupp.weight (fun i : ℕ => i + 1) e = d :=
    Sym.mem_lambdaComp.1 hf (MvPolynomial.mem_support_iff.1 he)
  have hexp : Ψ (MvPolynomial.monomial e (MvPolynomial.coeff e f))
      = Ψ (MvPolynomial.C (MvPolynomial.coeff e f))
        * ∏ i ∈ e.support, Ψ (MvPolynomial.X i) ^ e i := by
    rw [MvPolynomial.monomial_eq, map_mul, Finsupp.prod, map_prod]
    exact congrArg _ (Finset.prod_congr rfl fun i _ => map_pow _ _ _)
  have hsum : ∑ i ∈ e.support, e i * (i + 1) = d := by
    rw [← hw]
    simp only [Finsupp.weight_apply, Finsupp.sum, smul_eq_mul]
  have hbase : Sym.MergedLE K k 0 (Ψ (MvPolynomial.C (MvPolynomial.coeff e f))) := by
    rw [hΨ, pieceLift_C]
    exact mergedLE_realise_addLetter_auxToTotal hι _
  have hgen : ∀ i ∈ e.support, Sym.MergedLE K k (e i * (i + 1)) (Ψ (MvPolynomial.X i) ^ e i) :=
    fun i _ => Sym.mergedLE_pow
      (by rw [hΨ]; exact mergedLE_realise_addLetter_pieceLift_X hι i) (e i)
  have hmul := Sym.mergedLE_mul hbase (Sym.mergedLE_prod hgen)
  rw [hexp]
  rwa [zero_add, hsum] at hmul

/-! ### The realisation is injective on `V_{k-1}` -/

/-- **The realisation with auxiliary variables is injective on `V_{k-1}`.**

This is the second step that the proof of `HJO.Dyck.existsUnique_eq_sum_pow_mul_realiseAddLetter`,
as usually written, uses without justification: `HJO.Sym.realisation_injective` is the statement at
the level `0`, about `Λ`, and the uniqueness half of the lemma needs it about `ι_{k+1}` on
`V_{k-1}`.

The reduction is `HJO.Sweep.exists_pieceLift_eq` — every element of `V_{k-1}` is
`HJO.Sweep.pieceLift K k f` for an `f` in the symmetric functions over `𝕜[y_1, …, y_{k-1}]` —
together with `HJO.Dyck.auxToFrac_realise_pieceLift`, which identifies `ι_{k+1}(pieceLift f)` with
the classical realisation of `f` over that ring, coefficientwise along the injective
`HJO.Sym.auxFracPoly`. So the level-`0` statement applies verbatim, at the base
`𝕜[y_1, …, y_{k-1}]` rather than at `𝕜`. -/
theorem realise_injective_on_piece [Algebra ℚ K] (hι : IsAuxRealisation (k + 1) ι)
    {F : Sweep.Total K} (hF : F ∈ Sweep.piece K k) (h0 : ι F = 0) : F = 0 := by
  have : CharZero K := charZero_of_inj_zero fun m hm =>
    Nat.cast_eq_zero.1 ((algebraMap ℚ K).injective (by rw [map_natCast, hm, map_zero]))
  obtain ⟨f, rfl⟩ := exists_pieceLift_eq hF
  have hmap : MvPowerSeries.map (Sym.auxFracPoly K k)
      (PhiMul.realise (MvPolynomial (Fin k) K) f) = 0 := by
    rw [← auxToFrac_realise_pieceLift hι, h0, map_zero]
  have hzero : PhiMul.realise (MvPolynomial (Fin k) K) f = 0 := by
    refine MvPowerSeries.ext fun α => Sym.auxFracPoly_injective K k ?_
    rw [← MvPowerSeries.coeff_map, hmap, MvPowerSeries.coeff_zero]
    exact (map_zero (Sym.auxFracPoly K k)).symm
  have hf0 : f = 0 :=
    Sym.realisation_injective (PhiMul.isRealisation_realise (MvPolynomial (Fin k) K))
      (by rw [hzero, map_zero])
  rw [hf0, map_zero]

/-! ### A step used without comment in the literature -/

/-- **A symmetric expansion coefficient is the realisation of an element of `V_{k-1}`.** Let
`F ∈ P_{k+1}` be such that the `j`-th coefficient `c_j` of the expansion of its image in powers of
`y_{k+1}` has no monomial of total degree above `M` in the free variables and is fixed by every
finitary relabelling of the merged alphabet leaving `y_{k+1}` alone. Then `c_j = ι_{k+1}(h)` for an
`h ∈ V_{k-1}`, and `h[X + y_{k+1}]` realised has merged degree at most `M`.

This is the sentence of the proof of `HJO.Dyck.existsUnique_eq_sum_pow_mul_realiseAddLetter`, as
usually written, given without justification: "a symmetric series of bounded degree in the free
variables with coefficients in `𝕜[y_1, …, y_{k-1}]` is a finite combination of monomial symmetric
functions, hence the realisation under `HJO.Dyck.IsAuxRealisation` of an element of `V_{k-1}`". Its
two ingredients are `HJO.Sym.letterPerm_zPartPoly`, which reads the symmetry as invariance under the
adjacent interchanges of letters, and `HJO.Sym.exists_iota_eq_of_letterPerm_swap`, the classical
statement over the lower polynomial ring; the realisation is transported back along
`HJO.Dyck.auxToFrac_realise_pieceLift`.

The bound on the merged degree of `h[X + y_{k+1}]` comes for free and is not decoration: the `h`
produced is `HJO.Sweep.pieceLift` of a sum of weight-homogeneous pieces of weights at most `M`, and
`HJO.Dyck.mergedLE_realise_addLetter_pieceLift` turns each weight into a merged degree. It is what
makes the triangular recursion of `HJO.Dyck.existsUnique_eq_sum_pow_mul_realiseAddLetter`
terminate.

The step is used without comment in the literature and deserves a statement of its own. -/
theorem exists_mem_piece_of_zPartPoly [Algebra ℚ K] (hι : IsAuxRealisation (k + 1) ι)
    {F : Sym.AuxAlphabetSeries K (k + 1)} (j M : ℕ)
    (hbd : ∀ α : ℕ →₀ ℕ, M < Finsupp.degree α →
      MvPowerSeries.coeff α (Sym.zPartPoly K k F j) = 0)
    (hsym : ∀ ρ : Equiv.Perm (Option ℕ), ρ none = none →
        (MulAction.fixedBy (Option ℕ) ρ)ᶜ.Finite →
      Sym.zPerm K k ρ (Sym.zPart K k (Sym.auxToFrac K (k + 1) F) j)
        = Sym.zPart K k (Sym.auxToFrac K (k + 1) F) j) :
    ∃ h ∈ Sweep.piece K k,
      Sym.auxToFrac K (k + 1) (ι h) = Sym.zPart K k (Sym.auxToFrac K (k + 1) F) j ∧
        Sym.MergedLE K k M (ι (addLetter K (k + 1) h)) := by
  obtain ⟨f, hfd, hf⟩ := Sym.exists_iota_eq_of_letterPerm_swap
    (PhiMul.isRealisation_realise (MvPolynomial (Fin k) K)) (N := M) hbd
    fun m => Sym.letterPerm_zPartPoly F j (Equiv.swap m (m + 1))
      (hsym _ (Sym.optionCongr_none _) (Sym.finite_compl_fixedBy_optionCongr_swap m))
  refine ⟨pieceLift K k (∑ d ∈ Finset.range (M + 1), f d), pieceLift_mem_piece _, ?_, ?_⟩
  · rw [auxToFrac_realise_pieceLift hι, hf, Sym.map_zPartPoly]
  · rw [map_sum, map_sum, map_sum]
    refine Sym.mergedLE_sum fun d hd => Sym.mergedLE_mono ?_
      (mergedLE_realise_addLetter_pieceLift hι (hfd d))
    rw [Finset.mem_range] at hd
    omega

/-- **A symmetric expansion coefficient of a member of `Z^{(k+1)}` is the realisation of an element
of `V_{k-1}`**, the degree bound being the one membership in `Z^{(k+1)}` supplies. -/
theorem exists_mem_piece_auxToFrac_realise_eq_zPart [Algebra ℚ K]
    (hι : IsAuxRealisation (k + 1) ι) {F : Sym.AuxAlphabetSeries K (k + 1)}
    (hmem : Sym.auxToFrac K (k + 1) F ∈ Sym.zRing K k) (j : ℕ)
    (hsym : ∀ ρ : Equiv.Perm (Option ℕ), ρ none = none →
        (MulAction.fixedBy (Option ℕ) ρ)ᶜ.Finite →
      Sym.zPerm K k ρ (Sym.zPart K k (Sym.auxToFrac K (k + 1) F) j)
        = Sym.zPart K k (Sym.auxToFrac K (k + 1) F) j) :
    ∃ h ∈ Sweep.piece K k,
      Sym.auxToFrac K (k + 1) (ι h) = Sym.zPart K k (Sym.auxToFrac K (k + 1) F) j := by
  obtain ⟨N, hN⟩ := Sym.exists_zCoeff_eq_zero_of_mem_zRing hmem
  obtain ⟨h, hmemh, heq, -⟩ := exists_mem_piece_of_zPartPoly hι j N
    (fun α hα => Sym.coeff_zPartPoly_eq_zero_of_lt hN j (by omega)) hsym
  exact ⟨h, hmemh, heq⟩

/-- **Each coefficient of the expansion of `χ'_{Id_k}(π)` in powers of `y_k` is the realisation of
an element of `V_{k-1}`**, which the recursion of
`HJO.Dyck.existsUnique_eq_sum_pow_mul_realiseAddLetter` needs of it. The membership in `Z^{(k+1)}`
is `HJO.Dyck.auxToFrac_unnormalisedCharPart_mem_zGraded` and the symmetry is
`HJO.Dyck.zPerm_zPart_auxToFrac_unnormalisedCharSeries_identityTuple`, itself the route through
`HJO.Dyck.zSwap_auxToFrac_unnormalisedCharSeries` and
`HJO.Sym.zPerm_eq_self_of_forall_zSwap_eq_self`. -/
theorem exists_mem_piece_auxToFrac_realise_eq_zPart_identityTuple [Algebra ℚ K]
    (hι : IsAuxRealisation (k + 1) ι) (q : K) {N : ℕ} {x : Fin N → ℕ}
    (hx : IsPartialDyck (k + 1) N x) (j : ℕ) :
    ∃ h ∈ Sweep.piece K k, Sym.auxToFrac K (k + 1) (ι h)
      = Sym.zPart K k (Sym.auxToFrac K (k + 1)
          (unnormalisedCharSeries q (k + 1) x (identityTuple (k + 1)))) j :=
  exists_mem_piece_auxToFrac_realise_eq_zPart hι
    (auxToFrac_unnormalisedCharSeries_mem_zRing q k x (identityTuple (k + 1))) j
    fun _ hρ hsupport =>
      zPerm_zPart_auxToFrac_unnormalisedCharSeries_identityTuple q hx hρ hsupport j

/-! ### The triangular recursion -/

/-- The degenerate step of the recursion: once every expansion coefficient below `n` vanishes and
the merged degree is below `n` too, the series itself is `0`. -/
private theorem exists_solve_zero [Algebra ℚ K] {n N : ℕ} {F : Sym.AuxAlphabetSeries K (k + 1)}
    (hnN : N < n) (hring : Sym.auxToFrac K (k + 1) F ∈ Sym.zRing K k)
    (hML : Sym.MergedLE K k N F)
    (hlow : ∀ j < n, Sym.zPart K k (Sym.auxToFrac K (k + 1) F) j = 0) :
    ∃ g : ℕ → Sweep.Total K, (∀ j, g j ∈ Sweep.piece K k) ∧
      (∀ j, j < n → g j = 0) ∧ (∀ j, N < j → g j = 0) ∧
      Sym.auxToFrac K (k + 1) F
        = ∑ j ∈ Finset.range (N + 1), MvPowerSeries.C (Sym.yFrac K (Fin.last k)) ^ j *
            realiseAddLetter K k ι (g j) := by
  have hzero : Sym.auxToFrac K (k + 1) F = 0 := by
    rw [Sym.eq_sum_pow_mul_zPart hring (N := N) fun μ hμ => Sym.zCoeff_eq_zero_of_mergedLE hML hμ]
    refine Finset.sum_eq_zero fun j hj => ?_
    rw [Finset.mem_range] at hj
    rw [hlow j (by omega), mul_zero]
  refine ⟨0, fun j => by rw [Pi.zero_apply]; exact zero_mem _, fun _ _ => rfl, fun _ _ => rfl, ?_⟩
  rw [hzero]
  refine (Finset.sum_eq_zero fun j _ => ?_).symm
  rw [Pi.zero_apply, map_zero, mul_zero]

/-- **The triangular recursion of `HJO.Dyck.existsUnique_eq_sum_pow_mul_realiseAddLetter`.** Read
from the bottom up: if the expansion coefficients `c_j` of a member of `Z^{(k+1)}` vanish for
`j < n` and its merged degree is at most `N`, then it is `∑_{j ≤ N}y_{k+1}^{j}g_j[X + y_{k+1}]` for
elements `g_j` of `V_{k-1}` vanishing for `j < n` and for `j > N`.

At each step `c_n` is the realisation of some `g_n ∈ V_{k-1}`
(`HJO.Dyck.exists_mem_piece_of_zPartPoly`), and subtracting `y_{k+1}^{n}g_n[X + y_{k+1}]` kills
`c_n` without disturbing the coefficients below it, since `g_n[X + y_{k+1}]` is `g_n[X]` plus terms
of positive degree in `y_{k+1}` (`HJO.Dyck.zPart_realiseAddLetter_zero`,
`HJO.Sym.zPart_C_pow_mul_of_lt`). **The recursion terminates because the merged degree does not
grow**: the `g_n` produced has weight at most `N - n`, so `y_{k+1}^{n}g_n[X + y_{k+1}]` has merged
degree at most `N` again (`HJO.Dyck.mergedLE_realise_addLetter_pieceLift`), and the induction runs
on `N + 1 - n`, presented as an upper bound `D` with `N < n + D`. -/
private theorem exists_solve [Algebra ℚ K] (hι : IsAuxRealisation (k + 1) ι) :
    ∀ (D n N : ℕ) (F : Sym.AuxAlphabetSeries K (k + 1)), N < n + D →
      Sym.auxToFrac K (k + 1) F ∈ Sym.zRing K k → Sym.MergedLE K k N F →
      (∀ ρ : Equiv.Perm (Option ℕ), ρ none = none → (MulAction.fixedBy (Option ℕ) ρ)ᶜ.Finite →
        Sym.zPerm K k ρ (Sym.auxToFrac K (k + 1) F) = Sym.auxToFrac K (k + 1) F) →
      (∀ j < n, Sym.zPart K k (Sym.auxToFrac K (k + 1) F) j = 0) →
      ∃ g : ℕ → Sweep.Total K, (∀ j, g j ∈ Sweep.piece K k) ∧
        (∀ j, j < n → g j = 0) ∧ (∀ j, N < j → g j = 0) ∧
        Sym.auxToFrac K (k + 1) F
          = ∑ j ∈ Finset.range (N + 1), MvPowerSeries.C (Sym.yFrac K (Fin.last k)) ^ j *
              realiseAddLetter K k ι (g j) := by
  classical
  intro D
  induction D with
  | zero => exact fun n N F hND hring hML _ hlow => exists_solve_zero (by omega) hring hML hlow
  | succ D ihD =>
    intro n N F hND hring hML hsym hlow
    rcases lt_or_ge N n with hnN | hnN
    · exact exists_solve_zero hnN hring hML hlow
    obtain ⟨M, hM⟩ : ∃ M : ℕ, N = M + n := ⟨N - n, by omega⟩
    have hNcoeff : ∀ μ : Option ℕ →₀ ℕ, N < Finsupp.degree μ →
        Sym.zCoeff K k (Sym.auxToFrac K (k + 1) F) μ = 0 :=
      fun μ hμ => Sym.zCoeff_eq_zero_of_mergedLE hML hμ
    obtain ⟨h, hmemh, heqh, hMLh⟩ := exists_mem_piece_of_zPartPoly hι n M
      (fun α hα => Sym.coeff_zPartPoly_eq_zero_of_lt hNcoeff n (by omega))
      fun ρ hρ hsup => Sym.zPerm_zPart_eq_self hring hρ (hsym ρ hρ hsup) n
    have hringh : realiseAddLetter K k ι h ∈ Sym.zRing K k := realiseAddLetter_mem_zRing hι hmemh
    have hAFh : Sym.auxToFrac K (k + 1)
          (MvPowerSeries.C (MvPolynomial.X (Fin.last k)) ^ n * ι (addLetter K (k + 1) h))
        = MvPowerSeries.C (Sym.yFrac K (Fin.last k)) ^ n * realiseAddLetter K k ι h := by
      rw [map_mul, map_pow, auxToFrac_C, realiseAddLetter_apply]
      rfl
    have hAF' : Sym.auxToFrac K (k + 1)
          (F - MvPowerSeries.C (MvPolynomial.X (Fin.last k)) ^ n * ι (addLetter K (k + 1) h))
        = Sym.auxToFrac K (k + 1) F
          - MvPowerSeries.C (Sym.yFrac K (Fin.last k)) ^ n * realiseAddLetter K k ι h := by
      rw [map_sub, hAFh]
    have hprodring : MvPowerSeries.C (Sym.yFrac K (Fin.last k)) ^ n * realiseAddLetter K k ι h
        ∈ Sym.zRing K k := Sym.mul_mem_zRing (Sym.C_yFrac_pow_mem_zRing n) hringh
    have hring' : Sym.auxToFrac K (k + 1)
        (F - MvPowerSeries.C (MvPolynomial.X (Fin.last k)) ^ n * ι (addLetter K (k + 1) h))
          ∈ Sym.zRing K k := by
      rw [hAF', sub_eq_add_neg]
      exact Sym.add_mem_zRing hring (Sym.neg_mem_zRing hprodring)
    have hML' : Sym.MergedLE K k N
        (F - MvPowerSeries.C (MvPolynomial.X (Fin.last k)) ^ n * ι (addLetter K (k + 1) h)) :=
      Sym.mergedLE_sub hML (Sym.mergedLE_mono (by omega)
        (Sym.mergedLE_mul (Sym.mergedLE_C_X_last_pow K k n) hMLh))
    have hsym' : ∀ ρ : Equiv.Perm (Option ℕ), ρ none = none →
        (MulAction.fixedBy (Option ℕ) ρ)ᶜ.Finite →
        Sym.zPerm K k ρ (Sym.auxToFrac K (k + 1)
            (F - MvPowerSeries.C (MvPolynomial.X (Fin.last k)) ^ n * ι (addLetter K (k + 1) h)))
          = Sym.auxToFrac K (k + 1) (F - MvPowerSeries.C (MvPolynomial.X (Fin.last k)) ^ n
            * ι (addLetter K (k + 1) h)) := by
      intro ρ hρ hsup
      rw [hAF', sub_eq_add_neg, Sym.zPerm_add_of_mem_zRing ρ hring (Sym.neg_mem_zRing hprodring),
        Sym.zPerm_neg_of_mem_zRing ρ hprodring, hsym ρ hρ hsup,
        Sym.zPerm_C_yFrac_pow_mul hρ n hringh, zPerm_realiseAddLetter hι hmemh ρ]
    have hrangeF : ∀ α : ℕ →₀ ℕ,
        MvPowerSeries.coeff α (Sym.auxToFrac K (k + 1) F) ∈ (Sym.yFracEval K k).range :=
      fun α => Sym.coeff_auxToFrac_mem_range_yFracEval F α
    have hrangeh : ∀ α : ℕ →₀ ℕ,
        MvPowerSeries.coeff α (realiseAddLetter K k ι h) ∈ (Sym.yFracEval K k).range :=
      fun α => Sym.coeff_mem_range_yFracEval_of_mem_zRing hringh α
    have hlow' : ∀ j < n + 1, Sym.zPart K k (Sym.auxToFrac K (k + 1)
        (F - MvPowerSeries.C (MvPolynomial.X (Fin.last k)) ^ n
          * ι (addLetter K (k + 1) h))) j = 0 := by
      intro j hj
      rw [hAF', Sym.zPart_sub' hrangeF (Sym.coeff_C_pow_mul_mem_range_yFracEval hrangeh n)]
      rcases eq_or_lt_of_le (Nat.lt_succ_iff.1 hj) with rfl | hjn
      · have hshift := Sym.zPart_C_pow_mul hrangeh j 0
        rw [zero_add] at hshift
        rw [hshift, zPart_realiseAddLetter_zero hι hmemh, heqh, sub_self]
      · rw [hlow j hjn, Sym.zPart_C_pow_mul_of_lt hrangeh hjn, sub_self]
    obtain ⟨g, hgmem, hglow, hghigh, hgsum⟩ :=
      ihD (n + 1) N (F - MvPowerSeries.C (MvPolynomial.X (Fin.last k)) ^ n
        * ι (addLetter K (k + 1) h)) (by omega) hring' hML' hsym' hlow'
    have hmemn : n ∈ Finset.range (N + 1) := Finset.mem_range.2 (by omega)
    have hgn : g n = 0 := hglow n (Nat.lt_succ_self n)
    refine ⟨Function.update g n h, fun j => ?_, fun j hjlt => ?_, fun j hjgt => ?_, ?_⟩
    · rcases eq_or_ne j n with rfl | hjn
      · rw [Function.update_self]
        exact hmemh
      · rw [Function.update_of_ne hjn]
        exact hgmem j
    · rw [Function.update_of_ne (by omega : j ≠ n)]
      exact hglow j (by omega)
    · rw [Function.update_of_ne (by omega : j ≠ n)]
      exact hghigh j hjgt
    · have h1 : ∑ j ∈ Finset.range (N + 1), MvPowerSeries.C (Sym.yFrac K (Fin.last k)) ^ j *
            realiseAddLetter K k ι (g j)
          = ∑ j ∈ (Finset.range (N + 1)).erase n,
              MvPowerSeries.C (Sym.yFrac K (Fin.last k)) ^ j * realiseAddLetter K k ι (g j) := by
        rw [← Finset.add_sum_erase _ _ hmemn, hgn, map_zero, mul_zero, zero_add]
      have h2 : ∑ j ∈ Finset.range (N + 1), MvPowerSeries.C (Sym.yFrac K (Fin.last k)) ^ j *
            realiseAddLetter K k ι (Function.update g n h j)
          = MvPowerSeries.C (Sym.yFrac K (Fin.last k)) ^ n * realiseAddLetter K k ι h
            + ∑ j ∈ (Finset.range (N + 1)).erase n,
              MvPowerSeries.C (Sym.yFrac K (Fin.last k)) ^ j * realiseAddLetter K k ι (g j) := by
        rw [← Finset.add_sum_erase _ _ hmemn, Function.update_self]
        exact congrArg _ (Finset.sum_congr rfl fun j hj => by
          rw [Function.update_of_ne (Finset.mem_erase.1 hj).1])
      rw [h2, ← h1, ← hgsum, hAF']
      ring

/-! ### The unique expansion -/

/-- **`χ'_{Id_k}(π)` is symmetric in the letters.** Every finitary relabelling of the merged
alphabet fixing the distinguished letter `y_{k+1}` fixes it:
`HJO.Dyck.zSwap_auxToFrac_unnormalisedCharSeries` gives the invariance under each `ŝ_m` with
`m ≥ k + 1`, and `HJO.Sym.zPerm_eq_self_of_forall_zSwap_eq_self` at the threshold `1` turns that
into invariance under every such relabelling. This is the intermediate step of
`HJO.Dyck.zPerm_zPart_auxToFrac_unnormalisedCharSeries_identityTuple`, stated of the series itself
rather than of its expansion coefficients. -/
theorem zPerm_auxToFrac_unnormalisedCharSeries_identityTuple (q : K) {N : ℕ} {x : Fin N → ℕ}
    (hx : IsPartialDyck (k + 1) N x) {ρ : Equiv.Perm (Option ℕ)} (hρ : ρ none = none)
    (hsupport : (MulAction.fixedBy (Option ℕ) ρ)ᶜ.Finite) :
    Sym.zPerm K k ρ (Sym.auxToFrac K (k + 1)
        (unnormalisedCharSeries q (k + 1) x (identityTuple (k + 1))))
      = Sym.auxToFrac K (k + 1)
        (unnormalisedCharSeries q (k + 1) x (identityTuple (k + 1))) := by
  refine Sym.zPerm_eq_self_of_forall_zSwap_eq_self
    (auxToFrac_unnormalisedCharSeries_mem_zRing q k x (identityTuple (k + 1))) (t₀ := 1)
    (fun t ht => ?_) (fun t ht => ?_) hsupport
  · refine zSwap_auxToFrac_unnormalisedCharSeries q hx fun i => ⟨?_, ?_⟩
    · have := i.isLt
      change (i : ℕ) ≠ k + t
      omega
    · have := i.isLt
      change (i : ℕ) ≠ k + t + 1
      omega
  · rw [show t = 0 from by omega, Sym.zLetter_zero]
    exact hρ

/-- **The existence half of `HJO.Dyck.existsUnique_eq_sum_pow_mul_realiseAddLetter`**: for a partial
Dyck path `π` with `N ≥ k+1` positions there are `g_j ∈ V_{k-1}`, all but finitely many zero and
with `g_0 = 0`, with `χ'_{Id_k}(π) = ∑_{j ≥ 1}y_k^{j}g_j[X + y_k]`.

The proof as usually written, assembled: `HJO.Dyck.auxToFrac_unnormalisedCharPart_mem_zGraded`
bounds the merged degree, `HJO.Dyck.unnormalisedCharSeries_eq_C_prod_X_mul` gives `c_0 = 0`,
`HJO.Dyck.zSwap_auxToFrac_unnormalisedCharSeries` and
`HJO.Sym.zPerm_eq_self_of_forall_zSwap_eq_self` give the symmetry, and `HJO.Dyck.exists_solve` runs
the triangular recursion. -/
theorem exists_eq_sum_pow_mul_realiseAddLetter [Algebra ℚ K] (hι : IsAuxRealisation (k + 1) ι)
    (q : K) {N : ℕ} {x : Fin N → ℕ} (hx : IsPartialDyck (k + 1) N x) (hk : k + 1 ≤ N) :
    ∃ (M : ℕ) (g : ℕ → Sweep.Total K), (∀ j, g j ∈ Sweep.piece K k) ∧ g 0 = 0 ∧
      (∀ j, M < j → g j = 0) ∧
      Sym.auxToFrac K (k + 1) (unnormalisedCharSeries q (k + 1) x (identityTuple (k + 1)))
        = ∑ j ∈ Finset.range (M + 1), MvPowerSeries.C (Sym.yFrac K (Fin.last k)) ^ j *
            realiseAddLetter K k ι (g j) := by
  have hring := auxToFrac_unnormalisedCharSeries_mem_zRing q k x (identityTuple (k + 1))
  obtain ⟨M, hM⟩ := Sym.exists_zCoeff_eq_zero_of_mem_zRing hring
  obtain ⟨g, hgmem, hglow, hghigh, hgsum⟩ := exists_solve hι (M + 1) 1 M _ (by omega) hring
    (Sym.mergedLE_of_zCoeff_eq_zero hM)
    (fun ρ hρ hsup => zPerm_auxToFrac_unnormalisedCharSeries_identityTuple q hx hρ hsup)
    fun j hj => by
      rw [show j = 0 from by omega]
      exact zPart_auxToFrac_unnormalisedCharSeries_identityTuple_zero q hk
  exact ⟨M, g, hgmem, hglow 0 Nat.one_pos, hghigh, hgsum⟩

/-- **The unique expansion of the invariant in the last variable.** For
`N ≥ k + 1` and a partial Dyck path `π` with `N` positions there are *unique* `g_j(π) ∈ V_{k-1}`,
`j ≥ 1`, all but finitely many zero, with
`χ'_{Id_k}(π) = ∑_{j ≥ 1}y_k^{j}g_j(π)[X + y_k]`.

The level is written `k + 1`, as `HJO.Sym.zGraded` and its siblings are: the `V_{k-1}` is
`HJO.Sweep.piece K k`, its `y_k` is the distinguished letter `HJO.Sym.yFrac K (Fin.last k)` of the
merged alphabet, and its `g[X + y_k]` realised in `P°_{k+1}` is `HJO.Dyck.realiseAddLetter`. The
family `g_j`, `j ≥ 1`, is a function on `ℕ` with `g_0 = 0`, and "all but finitely many zero" is the
bound `M` past which the family vanishes; no index is a truncated subtraction.

Existence is `HJO.Dyck.exists_eq_sum_pow_mul_realiseAddLetter` and uniqueness is
`HJO.Dyck.eq_of_sum_pow_mul_realiseAddLetter_eq`, whose hypothesis that the realisation be injective
on `V_{k-1}` is `HJO.Dyck.realise_injective_on_piece`. The base is a domain and a `ℚ`-algebra, which
is weaker than the field of characteristic zero and all the proof reads. -/
@[hjo "lem_cm_chiprime_expansion"]
theorem existsUnique_eq_sum_pow_mul_realiseAddLetter [Algebra ℚ K]
    (hι : IsAuxRealisation (k + 1) ι) (q : K) {N : ℕ} {x : Fin N → ℕ}
    (hx : IsPartialDyck (k + 1) N x) (hk : k + 1 ≤ N) :
    ∃! g : ℕ → Sweep.Total K, (∀ j, g j ∈ Sweep.piece K k) ∧ g 0 = 0 ∧
      ∃ M : ℕ, (∀ j, M < j → g j = 0) ∧
        Sym.auxToFrac K (k + 1) (unnormalisedCharSeries q (k + 1) x (identityTuple (k + 1)))
          = ∑ j ∈ Finset.range (M + 1), MvPowerSeries.C (Sym.yFrac K (Fin.last k)) ^ j *
              realiseAddLetter K k ι (g j) := by
  obtain ⟨M, g, hgmem, hg0, hghigh, hgsum⟩ :=
    exists_eq_sum_pow_mul_realiseAddLetter hι q hx hk
  refine ⟨g, ⟨hgmem, hg0, M, hghigh, hgsum⟩, ?_⟩
  rintro g' ⟨hg'mem, -, M', hg'high, hg'sum⟩
  -- compare the two families on a common range
  set s : Finset ℕ := Finset.range (max M M' + 1) with hs
  have hext : ∀ (L : ℕ) (u : ℕ → Sweep.Total K), (∀ j, L < j → u j = 0) → L ≤ max M M' →
      ∑ j ∈ Finset.range (L + 1), MvPowerSeries.C (Sym.yFrac K (Fin.last k)) ^ j *
          realiseAddLetter K k ι (u j)
        = ∑ j ∈ s, MvPowerSeries.C (Sym.yFrac K (Fin.last k)) ^ j *
          realiseAddLetter K k ι (u j) := by
    intro L u hu hL
    refine Finset.sum_subset (fun j hj => ?_) fun j _ hj => ?_
    · rw [Finset.mem_range] at hj
      rw [hs, Finset.mem_range]
      omega
    · rw [Finset.mem_range] at hj
      rw [hu j (by omega), map_zero, mul_zero]
  have heq : ∑ j ∈ s, MvPowerSeries.C (Sym.yFrac K (Fin.last k)) ^ j *
        realiseAddLetter K k ι (g' j)
      = ∑ j ∈ s, MvPowerSeries.C (Sym.yFrac K (Fin.last k)) ^ j *
        realiseAddLetter K k ι (g j) := by
    rw [← hext M' g' hg'high (le_max_right M M'), ← hext M g hghigh (le_max_left M M'),
      ← hg'sum, ← hgsum]
  exact funext fun j => eq_of_sum_pow_mul_realiseAddLetter_eq hι
    (fun F hF h0 => realise_injective_on_piece hι hF h0) hg'mem hgmem
    (fun i hi => hg'high i (by rw [hs, Finset.mem_range] at hi; omega))
    (fun i hi => hghigh i (by rw [hs, Finset.mem_range] at hi; omega)) heq j

end HJO.Dyck
