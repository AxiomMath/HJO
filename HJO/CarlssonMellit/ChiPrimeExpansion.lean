/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.CarlssonMellit.ChiPrimeCoeffSymmetric
public import HJO.CarlssonMellit.ChiPrimeNu
public import HJO.CarlssonMellit.ChiPrimeSwapFixed
public import HJO.CarlssonMellit.ChiPrimeZGraded
public import HJO.CarlssonMellit.ZFixedSymmetric
public meta import HJO.Attr

/-! # The expansion of the characteristic series in the last auxiliary variable

The lowering step of the Carlsson--Mellit analysis reads `χ'_{Id_k}(π)` as
`∑_{j ≥ 1}y_k^{j}g_j(π)[X + y_k]` with `g_j(π) ∈ V_{k-1}`, which is
`HJO.Dyck.existsUnique_eq_sum_pow_mul_realiseAddLetter`. That lemma is **not** proved here; what is
proved is everything its proof asks for except one step (see below).

The level is written `k + 1`, as `HJO.Sym.zGraded` and its siblings are: the level
`k ≥ 1` is `k + 1` here, its `V_{k-1}` is `HJO.Sweep.piece K k`, its `y_k` is the distinguished
letter `HJO.Sym.yFrac K (Fin.last k)` of the merged alphabet, its `𝕜(y_1, …, y_{k-1})` is
`HJO.Sym.AuxFrac K k` entering by `HJO.Sym.auxFracCastSucc`, and its `g[X + y_k]` realised in
`P°_{k+1}` is `HJO.Dyck.realiseAddLetter`. No index is ever a truncated subtraction.

## The expansion in powers of `y_{k+1}`

The first half of the proof is the expansion `χ'_{Id_k}(π) = ∑_{j ≥ 0}y_k^{j}c_j` of a
member of `Z^{(k+1)}` in powers of the distinguished letter, with `c_j` a series in the free
variables over the lower coefficient field, together with `c_0 = 0`. That half is complete:

* `HJO.Sym.zBase`: the members of `P°_{k+1}` free of `y_{k+1}` — the "series in the free
  variables with coefficients in `𝕜[y_1, …, y_{k-1}]`", a subring.
* `HJO.Sym.zPart`: the coefficient `c_j` of `y_{k+1}^{j}`, read off through `HJO.Sym.zCoeff`.
* `HJO.Sym.eq_sum_pow_mul_zPart`, `HJO.Sym.exists_eq_sum_pow_mul_zPart`: the expansion exists and is
  finite.
* `HJO.Sym.eq_zero_of_sum_pow_mul_eq_zero`, `HJO.Sym.eq_of_sum_pow_mul_eq`: its coefficients are
  unique. This is what "read off degree by degree and therefore unique" means, and the
  mathematics in it is the transcendence of `y_{k+1}` over `𝕂(y_1, …, y_k)`.
* `HJO.Dyck.zPart_auxToFrac_unnormalisedCharSeries_identityTuple_zero`: `c_0 = 0`, from
  `HJO.Dyck.unnormalisedCharSeries_eq_C_prod_X_mul`.
* `HJO.Sym.zPerm_zPart`, `HJO.Dyck.zPerm_zPart_auxToFrac_unnormalisedCharSeries_identityTuple`: each
  `c_j` is symmetric in the letters. The route is the usual one —
  `HJO.Dyck.zSwap_auxToFrac_unnormalisedCharSeries`, then
  `HJO.Sym.zPerm_eq_self_of_forall_zSwap_eq_self` at the threshold `1`, then the observation that a
  relabelling fixing `y_{k+1}` acts on the expansion coefficient by coefficient.

## The triangularity of `X ↦ X + y_k`, and the uniqueness of the `g_j`

* `HJO.Dyck.addLetter_sub_mem_span`: `ρ_{k+1}` is the identity modulo `y_{k+1}`. It fixes every
  auxiliary variable and adds `y_{k+1}^{r}` to `p_r`, so it and the identity induce the same
  homomorphism to the quotient by `(y_{k+1})`; no hypothesis on the argument is needed.
* `HJO.Dyck.auxToFrac_realise_mem_zBase`: the realisation of an element of `V_{k-1}` is free of
  `y_{k+1}`.
* `HJO.Dyck.zPart_realiseAddLetter_zero`: hence the triangularity, `g[X + y_k]` is
  `g[X]` plus terms of positive degree in `y_k`, in the form "the coefficient of `y_{k+1}^0` in
  `g[X + y_{k+1}]` is `g[X]`".
* `HJO.Dyck.eq_zero_of_sum_pow_mul_realiseAddLetter_eq_zero`,
  `HJO.Dyck.eq_of_sum_pow_mul_realiseAddLetter_eq`: the uniqueness half of
  `HJO.Dyck.existsUnique_eq_sum_pow_mul_realiseAddLetter` — the expansion
  `∑_j y_k^{j}g_j[X + y_k]` determines the `g_j`, by the recursion on `n`.

## Implementation notes

*The coefficients of anything coming from `P_{k+1}` are polynomials in `y_{k+1}`, with no grading
hypothesis.* `HJO.Sym.yFracEval_auxSplitLastFrac` factors the inclusion
`𝕂[y_1, …, y_{k+1}] → 𝕂(y_1, …, y_{k+1})` through `𝕂(y_1, …, y_k)[Y]` using the splitting
`HJO.Sym.auxSplitLast` of `HJO.Sym.zGraded`'s toolkit, so `HJO.Sym.zCoeff_auxToFrac` computes every
merged coefficient of `auxToFrac K (k+1) F` as a polynomial coefficient. That is what makes
`c_0 = 0` a one-line consequence of `HJO.Dyck.unnormalisedCharSeries_eq_C_prod_X_mul`: the
distinguished variable divides every coefficient of `χ'_{Id_k}(π)`, so the constant term of each of
those polynomials vanishes.

*The injectivity of the realisation on `V_{k-1}` is carried, not invented.* The uniqueness
statements take `∀ F ∈ piece K k, ι F = 0 → F = 0` as a hypothesis, so they hold over an arbitrary
base. `HJO.Sym.realisation_injective` is the statement at the level `0`, about `Λ` and over a field
of characteristic zero; the statement on `V_{k-1}` is proved over a `ℚ`-algebra base as
`HJO.Dyck.realise_injective_on_piece` in `HJO.CarlssonMellit.ChiPrimeExpansionExists`.

*Why the lemma itself is not proved here.* The proof as usually written needs each `c_j` to be the
realisation of an element of `V_{k-1}`, and asserts this in one sentence: "A symmetric series of
bounded degree in the free variables with coefficients in `𝕜[y_1, …, y_{k-1}]` is a finite
combination of monomial symmetric functions, hence the realisation under `HJO.Dyck.IsAuxRealisation`
of an element of `V_{k-1}`". That is the surjectivity of the realisation onto the symmetric part in
bounded degree, a step in its own right. The two ingredients exist separately —
`HJO.Sym.mem_msymmSpan_of_letterPerm_swap` (symmetric and homogeneous implies a combination of
monomial symmetric functions, over an arbitrary commutative base) and
`HJO.Sym.map_lambdaComp_eq_msymmSpan` (that combination is in the image of `ι`) — and what remains
is the composite at the base `𝕂[y_1, …, y_k]`, which is not a field, together with the passage from
bounded to homogeneous degree. That is supplied in `HJO.CarlssonMellit.ChiPrimeExpansionExists`,
which generalises `HJO.Sym.map_lambdaComp_eq_msymmSpan` to a `ℚ`-algebra base, carries the degree
bookkeeping, and proves the lemma. The results below are the halves of the lemma that do not read
the surjectivity: the expansion, its uniqueness, `c_0 = 0`, the symmetry of the coefficients and the
triangularity.

## References

E. Carlsson and A. Mellit, *A proof of
the shuffle conjecture*, J. Amer. Math. Soc. **31** (2018) 661--697, Section 4, "Lowering operator".
-/

@[expose] public section

namespace HJO.Sym

variable {K : Type*} [CommRing K] [IsDomain K] {k : ℕ}

/-! ### Every coefficient coming from `P_{k+1}` is a polynomial in `y_{k+1}` -/

/-- The last auxiliary variable split off, with the remaining coefficients enlarged to the lower
coefficient field: `𝕂[y_1, …, y_{k+1}] → 𝕂(y_1, …, y_k)[Y]`. -/
noncomputable def auxSplitLastFrac (K : Type*) [CommRing K] [IsDomain K] (k : ℕ) :
    MvPolynomial (Fin (k + 1)) K →+* Polynomial (AuxFrac K k) :=
  (Polynomial.mapRingHom (algebraMap (MvPolynomial (Fin k) K) (AuxFrac K k))).comp
    (auxSplitLast K k).toRingHom

theorem coeff_auxSplitLastFrac (p : MvPolynomial (Fin (k + 1)) K) (b : ℕ) :
    (auxSplitLastFrac K k p).coeff b
      = algebraMap (MvPolynomial (Fin k) K) (AuxFrac K k) ((auxSplitLast K k p).coeff b) :=
  Polynomial.coeff_map _ _

/-- **Splitting off `y_{k+1}` inverts the evaluation at `y_{k+1}`**: every element of
`𝕂(y_1, …, y_{k+1})` coming from a polynomial is a polynomial in `y_{k+1}` over the lower
coefficient field, namely the one `HJO.Sym.auxSplitLastFrac` produces. -/
theorem yFracEval_auxSplitLastFrac (p : MvPolynomial (Fin (k + 1)) K) :
    yFracEval K k (auxSplitLastFrac K k p)
      = algebraMap (MvPolynomial (Fin (k + 1)) K) (AuxFrac K (k + 1)) p := by
  have h : (yFracEval K k).comp (auxSplitLastFrac K k)
      = (algebraMap (MvPolynomial (Fin (k + 1)) K) (AuxFrac K (k + 1)) : _ →+* _) := by
    refine MvPolynomial.ringHom_ext (fun a => ?_) fun l => ?_
    · have hsplit : auxSplitLastFrac K k (MvPolynomial.C a) = Polynomial.C
          (algebraMap (MvPolynomial (Fin k) K) (AuxFrac K k) (MvPolynomial.C a)) := by
        rw [auxSplitLastFrac]
        simp [auxSplitLast]
      rw [RingHom.comp_apply, hsplit, yFracEval_C, auxFracCastSucc_algebraMap,
        MvPolynomial.rename_C]
    · refine Fin.lastCases ?_ (fun l => ?_) l
      · have hsplit : auxSplitLastFrac K k (MvPolynomial.X (Fin.last k)) = Polynomial.X := by
          rw [auxSplitLastFrac, RingHom.comp_apply]
          change Polynomial.map _ (auxSplitLast K k (MvPolynomial.X (Fin.last k))) = _
          rw [auxSplitLast_X_last, Polynomial.map_X]
        rw [RingHom.comp_apply, hsplit, yFracEval, Polynomial.coe_eval₂RingHom,
          Polynomial.eval₂_X, yFrac]
      · have hX : (MvPolynomial.X (Fin.castSucc l) : MvPolynomial (Fin (k + 1)) K)
            = MvPolynomial.rename Fin.castSucc (MvPolynomial.X l) := by
          rw [MvPolynomial.rename_X]
        have hsplit : auxSplitLastFrac K k (MvPolynomial.X (Fin.castSucc l))
            = Polynomial.C (algebraMap (MvPolynomial (Fin k) K) (AuxFrac K k)
                (MvPolynomial.X l)) := by
          rw [auxSplitLastFrac, RingHom.comp_apply]
          change Polynomial.map _ (auxSplitLast K k (MvPolynomial.X (Fin.castSucc l))) = _
          rw [hX, auxSplitLast_rename_castSucc, Polynomial.map_C]
        rw [RingHom.comp_apply, hsplit, yFracEval_C, auxFracCastSucc_algebraMap, ← hX]
  exact RingHom.congr_fun h p

/-- Every coefficient of a series of `P_{k+1}`, read in `P°_{k+1}`, is a polynomial in `y_{k+1}`
over the lower coefficient field: no membership in `Z^{(k+1)}` is needed, only that the coefficient
is an honest polynomial in `y_1, …, y_{k+1}`. -/
theorem coeff_auxToFrac_mem_range_yFracEval (F : AuxAlphabetSeries K (k + 1)) (α : ℕ →₀ ℕ) :
    MvPowerSeries.coeff α (auxToFrac K (k + 1) F) ∈ (yFracEval K k).range := by
  rw [coeff_auxToFrac]
  exact ⟨_, yFracEval_auxSplitLastFrac _⟩

/-- **The merged coefficients of a series of `P_{k+1}`**: the coefficient of `y_{k+1}^b x^α` is the
`b`-th coefficient of the polynomial in `y_{k+1}` that the coefficient of `x^α` is. -/
theorem zCoeff_auxToFrac (F : AuxAlphabetSeries K (k + 1)) (α : ℕ →₀ ℕ) (b : ℕ) :
    zCoeff K k (auxToFrac K (k + 1) F) (α.optionElim b)
      = algebraMap (MvPolynomial (Fin k) K) (AuxFrac K k)
          ((auxSplitLast K k (MvPowerSeries.coeff α F)).coeff b) := by
  rw [zCoeff, Finsupp.some_optionElim, Finsupp.optionElim_apply_none, coeff_auxToFrac,
    ← yFracEval_auxSplitLastFrac, yFracCoeff_yFracEval, coeff_auxSplitLastFrac]

/-! ### The series free of the last auxiliary variable -/

/-- **The members of `P°_{k+1}` free of the distinguished letter `y_{k+1}`**: those whose
coefficients already lie in the lower coefficient field `𝕂(y_1, …, y_k)`. These are the `c_j` of the
expansion `∑_j y_k^j c_j`, "a series in the free variables with coefficients in
`𝕜[y_1, …, y_{k-1}]`"; they form a subring because a coefficient of a sum or of a product is a sum
of products of coefficients. -/
noncomputable def zBase (K : Type*) [CommRing K] [IsDomain K] (k : ℕ) :
    Subring (AuxAlphabetSeriesFrac K (k + 1)) where
  carrier := {G | ∀ α : ℕ →₀ ℕ, MvPowerSeries.coeff α G ∈ (auxFracCastSucc K k).range}
  one_mem' α := by
    rw [MvPowerSeries.coeff_one]
    split_ifs
    · exact one_mem _
    · exact zero_mem _
  mul_mem' hG hH α := by
    rw [MvPowerSeries.coeff_mul]
    exact sum_mem fun p _ => mul_mem (hG _) (hH _)
  zero_mem' α := by rw [MvPowerSeries.coeff_zero]; exact zero_mem _
  add_mem' hG hH α := by rw [map_add]; exact add_mem (hG α) (hH α)
  neg_mem' hG α := by rw [map_neg]; exact neg_mem (hG α)

variable {G H : AuxAlphabetSeriesFrac K (k + 1)}

theorem mem_zBase :
    G ∈ zBase K k ↔ ∀ α : ℕ →₀ ℕ, MvPowerSeries.coeff α G ∈ (auxFracCastSucc K k).range :=
  Iff.rfl

/-- A series free of `y_{k+1}` has all its coefficients polynomial in `y_{k+1}`: they are the
constant polynomials. -/
theorem coeff_mem_range_yFracEval_of_mem_zBase (hG : G ∈ zBase K k) (α : ℕ →₀ ℕ) :
    MvPowerSeries.coeff α G ∈ (yFracEval K k).range := by
  obtain ⟨c, hc⟩ := hG α
  exact ⟨Polynomial.C c, by rw [yFracEval_C, hc]⟩

/-- The merged coefficients of a series free of `y_{k+1}` in positive `y_{k+1}`-degree vanish. -/
theorem zCoeff_eq_zero_of_mem_zBase (hG : G ∈ zBase K k) {ν : Option ℕ →₀ ℕ} (hν : ν none ≠ 0) :
    zCoeff K k G ν = 0 := by
  obtain ⟨c, hc⟩ := hG ν.some
  rw [zCoeff, ← hc, ← yFracEval_C c, yFracCoeff_yFracEval, Polynomial.coeff_C,
    ite_eq_right hν]

/-- The merged coefficients of a series free of `y_{k+1}` in `y_{k+1}`-degree `0` are its own
coefficients. -/
theorem auxFracCastSucc_zCoeff_of_mem_zBase (hG : G ∈ zBase K k) (α : ℕ →₀ ℕ) :
    auxFracCastSucc K k (zCoeff K k G (α.optionElim 0)) = MvPowerSeries.coeff α G := by
  obtain ⟨c, hc⟩ := hG α
  have hcoeff : zCoeff K k G (α.optionElim 0) = c := by
    rw [zCoeff, Finsupp.some_optionElim, Finsupp.optionElim_apply_none, ← hc, ← yFracEval_C c,
      yFracCoeff_yFracEval, Polynomial.coeff_C, ite_eq_left rfl]
  rw [hcoeff, hc]

/-! ### The expansion in powers of the last auxiliary variable -/

/-- **The coefficient `c_j` of `y_{k+1}^j`** in a member of `Z^{(k+1)}`: the series in the free
variables whose coefficient at `x^α` is the merged coefficient of `y_{k+1}^j x^α`. This is the
`c_j` of `χ'_{Id_k}(π) = ∑_{j ≥ 0}y_k^j c_j`, read off "degree by degree" through
`HJO.Sym.zCoeff` and therefore unique by construction. -/
noncomputable def zPart (K : Type*) [CommRing K] [IsDomain K] (k : ℕ)
    (G : AuxAlphabetSeriesFrac K (k + 1)) (j : ℕ) : AuxAlphabetSeriesFrac K (k + 1) :=
  fun α => auxFracCastSucc K k (zCoeff K k G (α.optionElim j))

theorem coeff_zPart (G : AuxAlphabetSeriesFrac K (k + 1)) (j : ℕ) (α : ℕ →₀ ℕ) :
    MvPowerSeries.coeff α (zPart K k G j)
      = auxFracCastSucc K k (zCoeff K k G (α.optionElim j)) :=
  rfl

/-- Each coefficient of the expansion is free of `y_{k+1}`, as is required of the `c_j`. -/
theorem zPart_mem_zBase (G : AuxAlphabetSeriesFrac K (k + 1)) (j : ℕ) :
    zPart K k G j ∈ zBase K k := fun _ => ⟨_, rfl⟩

/-- A series already free of `y_{k+1}` is its own coefficient of `y_{k+1}^0`. -/
theorem zPart_zero_of_mem_zBase (hG : G ∈ zBase K k) : zPart K k G 0 = G :=
  MvPowerSeries.ext fun α => by
    rw [coeff_zPart, auxFracCastSucc_zCoeff_of_mem_zBase hG]

/-- A series already free of `y_{k+1}` has no coefficient in positive `y_{k+1}`-degree. -/
theorem zPart_of_mem_zBase_of_ne (hG : G ∈ zBase K k) {j : ℕ} (hj : j ≠ 0) :
    zPart K k G j = 0 :=
  MvPowerSeries.ext fun α => by
    rw [coeff_zPart, zCoeff_eq_zero_of_mem_zBase hG
      (by rw [Finsupp.optionElim_apply_none]; exact hj), map_zero, MvPowerSeries.coeff_zero]

/-- **The powers of `y_{k+1}` are independent over the series free of `y_{k+1}`**: this is
what "read off degree by degree and therefore unique" means. The transcendence of `y_{k+1}` over
`𝕂(y_1, …, y_k)` is what makes it true, in the form
`HJO.Sym.eq_zero_of_sum_auxFracCastSucc_mul_yFrac_pow_eq_zero`. -/
theorem eq_zero_of_sum_pow_mul_eq_zero {s : Finset ℕ} {F : ℕ → AuxAlphabetSeriesFrac K (k + 1)}
    (hF : ∀ j ∈ s, F j ∈ zBase K k)
    (h : ∑ j ∈ s, MvPowerSeries.C (yFrac K (Fin.last k)) ^ j * F j = 0) :
    ∀ j ∈ s, F j = 0 := by
  classical
  intro j hj
  refine MvPowerSeries.ext fun α => ?_
  choose! c hc using fun i (hi : i ∈ s) => hF i hi α
  have hsum : ∑ i ∈ s, auxFracCastSucc K k (c i) * yFrac K (Fin.last k) ^ i = 0 := by
    have hh := congrArg (MvPowerSeries.coeff α) h
    rw [map_sum, MvPowerSeries.coeff_zero] at hh
    refine Eq.trans (Finset.sum_congr rfl fun i hi => ?_) hh
    rw [hc i hi, ← map_pow, MvPowerSeries.coeff_C_mul, mul_comm]
  rw [← hc j hj, eq_zero_of_sum_auxFracCastSucc_mul_yFrac_pow_eq_zero hsum hj, map_zero,
    MvPowerSeries.coeff_zero]

/-- **The expansion in powers of `y_{k+1}`**: a member of `Z^{(k+1)}` whose merged coefficients
vanish in merged degree above `N` is the finite sum `∑_{j ≤ N}y_{k+1}^j c_j` of its coefficients of
`HJO.Sym.zPart`. This is the existence half of
`χ'_{Id_k}(π) = ∑_{j ≥ 0}y_k^j c_j`. -/
theorem eq_sum_pow_mul_zPart (hG : G ∈ zRing K k) {N : ℕ}
    (hN : ∀ μ : Option ℕ →₀ ℕ, N < Finsupp.degree μ → zCoeff K k G μ = 0) :
    G = ∑ j ∈ Finset.range (N + 1),
      MvPowerSeries.C (yFrac K (Fin.last k)) ^ j * zPart K k G j := by
  classical
  refine MvPowerSeries.ext fun α => ?_
  have hrange := coeff_mem_range_yFracEval_of_mem_zRing hG α
  have hsub : (zPoly K k G α).support ⊆ Finset.range (N + 1) := by
    intro b hb
    rw [Finset.mem_range]
    by_contra hbN
    refine Polynomial.mem_support_iff.1 hb ?_
    rw [coeff_zPoly]
    exact hN _ (by rw [degree_optionElim]; omega)
  rw [map_sum]
  calc MvPowerSeries.coeff α G
      = ∑ b ∈ (zPoly K k G α).support,
          auxFracCastSucc K k ((zPoly K k G α).coeff b) * yFrac K (Fin.last k) ^ b := by
        rw [← yFracEval_apply, yFracEval_zPoly hrange]
    _ = ∑ b ∈ Finset.range (N + 1),
          auxFracCastSucc K k ((zPoly K k G α).coeff b) * yFrac K (Fin.last k) ^ b :=
        Finset.sum_subset hsub fun b _ hb => by
          rw [Polynomial.notMem_support_iff.1 hb, map_zero, zero_mul]
    _ = ∑ j ∈ Finset.range (N + 1),
          MvPowerSeries.coeff α (MvPowerSeries.C (yFrac K (Fin.last k)) ^ j * zPart K k G j) :=
        Finset.sum_congr rfl fun j _ => by
          rw [← map_pow, MvPowerSeries.coeff_C_mul, coeff_zPart, coeff_zPoly, mul_comm]

/-- The expansion in powers of `y_{k+1}` of an arbitrary member of `Z^{(k+1)}`: the bound is the one
`HJO.Sym.exists_zCoeff_eq_zero_of_mem_zRing` supplies. -/
theorem exists_eq_sum_pow_mul_zPart (hG : G ∈ zRing K k) :
    ∃ N : ℕ, G = ∑ j ∈ Finset.range (N + 1),
      MvPowerSeries.C (yFrac K (Fin.last k)) ^ j * zPart K k G j := by
  obtain ⟨N, hN⟩ := exists_zCoeff_eq_zero_of_mem_zRing hG
  exact ⟨N, eq_sum_pow_mul_zPart hG hN⟩

/-- **The coefficients of the expansion are unique.** Two finitely supported families of series free
of `y_{k+1}` with the same expansion in powers of `y_{k+1}` agree termwise. -/
theorem eq_of_sum_pow_mul_eq {s : Finset ℕ} {F F' : ℕ → AuxAlphabetSeriesFrac K (k + 1)}
    (hF : ∀ j ∈ s, F j ∈ zBase K k) (hF' : ∀ j ∈ s, F' j ∈ zBase K k)
    (h : ∑ j ∈ s, MvPowerSeries.C (yFrac K (Fin.last k)) ^ j * F j
      = ∑ j ∈ s, MvPowerSeries.C (yFrac K (Fin.last k)) ^ j * F' j) :
    ∀ j ∈ s, F j = F' j := by
  intro j hj
  have hzero : ∀ i ∈ s, (F - F') i = 0 := by
    refine eq_zero_of_sum_pow_mul_eq_zero (fun i hi => sub_mem (hF i hi) (hF' i hi)) ?_
    rw [show ∑ i ∈ s, MvPowerSeries.C (yFrac K (Fin.last k)) ^ i * (F - F') i
        = (∑ i ∈ s, MvPowerSeries.C (yFrac K (Fin.last k)) ^ i * F i)
          - ∑ i ∈ s, MvPowerSeries.C (yFrac K (Fin.last k)) ^ i * F' i from by
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun i _ => by rw [Pi.sub_apply, mul_sub], h, sub_self]
  exact sub_eq_zero.1 (hzero j hj)

/-! ### The expansion is additive and reads off a shift by a power of `y_{k+1}` -/

/-- The expansion coefficients of the zero series vanish. -/
@[simp]
theorem zPart_zero (j : ℕ) : zPart K k (0 : AuxAlphabetSeriesFrac K (k + 1)) j = 0 :=
  MvPowerSeries.ext fun α => by
    rw [coeff_zPart, zCoeff, MvPowerSeries.coeff_zero, yFracCoeff_zero, map_zero,
      MvPowerSeries.coeff_zero]

/-- **The expansion is additive** on the series whose coefficients are polynomial in `y_{k+1}`, in
particular on `Z^{(k+1)}`. -/
theorem zPart_sum {S : Type*} {t : Finset S} {F : S → AuxAlphabetSeriesFrac K (k + 1)}
    (hF : ∀ i ∈ t, ∀ α : ℕ →₀ ℕ, MvPowerSeries.coeff α (F i) ∈ (yFracEval K k).range) (j : ℕ) :
    zPart K k (∑ i ∈ t, F i) j = ∑ i ∈ t, zPart K k (F i) j := by
  refine MvPowerSeries.ext fun α => ?_
  have hL : ∀ A : AuxAlphabetSeriesFrac K (k + 1), MvPowerSeries.coeff α (zPart K k A j)
      = auxFracCastSucc K k (yFracCoeff K k (MvPowerSeries.coeff α A) j) := fun A => by
    rw [coeff_zPart, zCoeff, Finsupp.some_optionElim, Finsupp.optionElim_apply_none]
  rw [hL, map_sum, yFracCoeff_sum_of_mem_range (fun i hi => hF i hi α), map_sum, map_sum]
  exact Finset.sum_congr rfl fun i _ => (hL (F i)).symm

/-- The evaluation at `y_{k+1}` of the polynomial variable. -/
@[simp]
theorem yFracEval_X : yFracEval K k Polynomial.X = yFrac K (Fin.last k) := by
  rw [yFracEval, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_X]

/-- Multiplying by `y_{k+1}^i` multiplies the polynomial in `y_{k+1}` that a coefficient is by
`Y^i`. -/
theorem coeff_C_pow_mul_eq (i : ℕ) {α : ℕ →₀ ℕ} {p : Polynomial (AuxFrac K k)}
    (hp : yFracEval K k p = MvPowerSeries.coeff α G) :
    MvPowerSeries.coeff α (MvPowerSeries.C (yFrac K (Fin.last k)) ^ i * G)
      = yFracEval K k (Polynomial.X ^ i * p) := by
  rw [← map_pow, MvPowerSeries.coeff_C_mul, ← hp, map_mul, map_pow, yFracEval_X]

theorem coeff_C_pow_mul_mem_range_yFracEval
    (hG : ∀ α : ℕ →₀ ℕ, MvPowerSeries.coeff α G ∈ (yFracEval K k).range) (i : ℕ) (α : ℕ →₀ ℕ) :
    MvPowerSeries.coeff α (MvPowerSeries.C (yFrac K (Fin.last k)) ^ i * G)
      ∈ (yFracEval K k).range := by
  obtain ⟨p, hp⟩ := hG α
  exact ⟨Polynomial.X ^ i * p, (coeff_C_pow_mul_eq i hp).symm⟩

/-- **Multiplying by `y_{k+1}^i` shifts the expansion by `i`**: the coefficient of
`y_{k+1}^{m+i}` in `y_{k+1}^i G` is the coefficient of `y_{k+1}^m` in `G`. No `ℕ`-subtraction: the
shift is written as an addition on the index. -/
theorem zPart_C_pow_mul
    (hG : ∀ α : ℕ →₀ ℕ, MvPowerSeries.coeff α G ∈ (yFracEval K k).range) (i m : ℕ) :
    zPart K k (MvPowerSeries.C (yFrac K (Fin.last k)) ^ i * G) (m + i) = zPart K k G m := by
  refine MvPowerSeries.ext fun α => ?_
  obtain ⟨p, hp⟩ := hG α
  rw [coeff_zPart, coeff_zPart, zCoeff, zCoeff, Finsupp.some_optionElim,
    Finsupp.optionElim_apply_none, Finsupp.some_optionElim, Finsupp.optionElim_apply_none,
    coeff_C_pow_mul_eq i hp, ← hp, yFracCoeff_yFracEval, yFracCoeff_yFracEval,
    Polynomial.coeff_X_pow_mul]

/-- **Multiplying by `y_{k+1}^i` kills the expansion below `i`**. -/
theorem zPart_C_pow_mul_of_lt
    (hG : ∀ α : ℕ →₀ ℕ, MvPowerSeries.coeff α G ∈ (yFracEval K k).range) {i n : ℕ} (hn : n < i) :
    zPart K k (MvPowerSeries.C (yFrac K (Fin.last k)) ^ i * G) n = 0 := by
  refine MvPowerSeries.ext fun α => ?_
  obtain ⟨p, hp⟩ := hG α
  rw [coeff_zPart, zCoeff, Finsupp.some_optionElim, Finsupp.optionElim_apply_none,
    coeff_C_pow_mul_eq i hp, yFracCoeff_yFracEval, Polynomial.coeff_X_pow_mul',
    ite_eq_right (by omega : ¬ i ≤ n), map_zero, MvPowerSeries.coeff_zero]

/-! ### The expansion coefficients inherit the symmetry in the letters -/

/-- The merged coefficients of the `j`-th expansion coefficient: `c_j` has the merged coefficient of
`G` at `y_{k+1}^j x^α` at the merged monomial `x^α`, and nothing in positive `y_{k+1}`-degree. -/
theorem zCoeff_zPart (G : AuxAlphabetSeriesFrac K (k + 1)) (j : ℕ) (ν : Option ℕ →₀ ℕ) :
    zCoeff K k (zPart K k G j) ν
      = if ν none = 0 then zCoeff K k G (ν.some.optionElim j) else 0 := by
  classical
  rcases eq_or_ne (ν none) 0 with hν | hν
  · rw [ite_eq_left hν]
    refine auxFracCastSucc_injective K k ?_
    calc auxFracCastSucc K k (zCoeff K k (zPart K k G j) ν)
        = auxFracCastSucc K k (zCoeff K k (zPart K k G j) (ν.some.optionElim 0)) := by
          rw [← hν, Finsupp.optionElim_some]
      _ = MvPowerSeries.coeff ν.some (zPart K k G j) :=
          auxFracCastSucc_zCoeff_of_mem_zBase (zPart_mem_zBase G j) _
      _ = auxFracCastSucc K k (zCoeff K k G (ν.some.optionElim j)) := coeff_zPart _ _ _
  · rw [ite_eq_right hν, zCoeff_eq_zero_of_mem_zBase (zPart_mem_zBase G j) hν]

section Perm

variable {ρ : Equiv.Perm (Option ℕ)}

/-- A relabelling fixing the distinguished letter leaves the exponent of that letter alone. -/
private theorem equivMapDomain_apply_none (hρ : ρ none = none) (ν : Option ℕ →₀ ℕ) :
    Finsupp.equivMapDomain ρ.symm ν none = ν none := by
  rw [Finsupp.equivMapDomain_apply, Equiv.symm_symm, hρ]

/-- A relabelling fixing the distinguished letter commutes with replacing the exponent of that
letter: it permutes the letters and leaves the distinguished exponent where it is. -/
private theorem equivMapDomain_some_optionElim (hρ : ρ none = none) (α : ℕ →₀ ℕ) (b j : ℕ) :
    (Finsupp.equivMapDomain ρ.symm (α.optionElim b)).some.optionElim j
      = Finsupp.equivMapDomain ρ.symm (α.optionElim j) := by
  refine Finsupp.ext fun a => ?_
  cases a with
  | none =>
    rw [Finsupp.optionElim_apply_none, equivMapDomain_apply_none hρ,
      Finsupp.optionElim_apply_none]
  | some i =>
    have h : ρ (some i) ≠ none := fun hh =>
      Option.some_ne_none i (ρ.injective (hh.trans hρ.symm))
    obtain ⟨i', hi'⟩ := Option.ne_none_iff_exists'.1 h
    rw [Finsupp.optionElim_apply_some, Finsupp.some_apply, Finsupp.equivMapDomain_apply,
      Finsupp.equivMapDomain_apply, Equiv.symm_symm, hi', Finsupp.optionElim_apply_some,
      Finsupp.optionElim_apply_some]

/-- **A relabelling fixing `y_{k+1}` acts on the expansion coefficient by coefficient**, which is
the step "such a `ρ` fixes `y_k` and permutes the free variables, so it acts on the expansion
above coefficient by coefficient" of the proof as usually written. -/
theorem zPerm_zPart (hG : G ∈ zRing K k) (hρ : ρ none = none) (j : ℕ) :
    zPerm K k ρ (zPart K k G j) = zPart K k (zPerm K k ρ G) j := by
  classical
  refine MvPowerSeries.ext fun α => ?_
  have hterm : ∀ b : ℕ,
      auxFracCastSucc K k (zCoeff K k (zPart K k G j)
            (Finsupp.equivMapDomain ρ.symm (α.optionElim b))) * yFrac K (Fin.last k) ^ b
        = if b = 0 then
            auxFracCastSucc K k (zCoeff K k G (Finsupp.equivMapDomain ρ.symm (α.optionElim j)))
          else 0 := by
    intro b
    rw [zCoeff_zPart, equivMapDomain_apply_none hρ, Finsupp.optionElim_apply_none]
    rcases eq_or_ne b 0 with rfl | hb
    · rw [ite_eq_left rfl, ite_eq_left rfl, equivMapDomain_some_optionElim hρ, pow_zero, mul_one]
    · rw [ite_eq_right hb, ite_eq_right hb, map_zero, zero_mul]
  rw [coeff_zPerm, finsum_congr hterm, finsum_eq_single _ 0 fun b hb => ite_eq_right hb,
    ite_eq_left rfl, coeff_zPart, zCoeff_zPerm ρ hG]

/-- **Each expansion coefficient of a series symmetric in the letters is symmetric in the
letters.** -/
theorem zPerm_zPart_eq_self (hG : G ∈ zRing K k) (hρ : ρ none = none)
    (hfix : zPerm K k ρ G = G) (j : ℕ) : zPerm K k ρ (zPart K k G j) = zPart K k G j := by
  rw [zPerm_zPart hG hρ, hfix]

end Perm

end HJO.Sym


namespace HJO.Dyck

open HJO.Sweep MulAction

variable {K : Type*} [CommRing K] [IsDomain K] {N k : ℕ} {x : Fin N → ℕ} {σ : Fin (k + 1) → ℕ}
  {ι : Sweep.Total K →ₐ[K] Sym.AuxAlphabetSeries K (k + 1)}

/-! ### The expansion of the characteristic series in the last auxiliary variable -/

/-- **The coefficient of `y_{k+1}^0` in `χ'_σ(π)` vanishes**, for a prescription listing the labels
below the level once each: this is `HJO.Dyck.unnormalisedCharSeries_eq_C_prod_X_mul`, which exhibits
`y_1 ⋯ y_{k+1}` as a factor, read through the splitting `HJO.Sym.auxSplitLast` — the distinguished
variable divides every coefficient, so no coefficient survives in `y_{k+1}`-degree `0`. This is the
`c_0 = 0`.
-/
theorem zCoeff_auxToFrac_unnormalisedCharSeries_optionElim_zero (q : K) (hk : k + 1 ≤ N)
    (hlt : ∀ j, σ j < k + 1) (hinj : Function.Injective σ) (α : ℕ →₀ ℕ) :
    Sym.zCoeff K k (Sym.auxToFrac K (k + 1) (unnormalisedCharSeries q (k + 1) x σ))
        (α.optionElim 0) = 0 := by
  obtain ⟨c, hc⟩ := Finset.dvd_prod_of_mem
    (fun l : Fin (k + 1) => (MvPolynomial.X l : MvPolynomial (Fin (k + 1)) K))
    (Finset.mem_univ (Fin.last k))
  have hsplit : Sym.auxSplitLast K k
        (MvPowerSeries.coeff α (unnormalisedCharSeries q (k + 1) x σ))
      = Polynomial.X * (Sym.auxSplitLast K k c * Sym.auxSplitLast K k
          (MvPowerSeries.coeff α (partialCharSeries q (k + 1) x σ))) := by
    rw [unnormalisedCharSeries_eq_C_prod_X_mul hk hlt hinj, MvPowerSeries.coeff_C_mul, hc, map_mul,
      map_mul, Sym.auxSplitLast_X_last, mul_assoc]
  rw [Sym.zCoeff_auxToFrac, hsplit, Polynomial.mul_coeff_zero, Polynomial.coeff_X_zero, zero_mul,
    map_zero]

/-- **`c_0 = 0`**: the step "`c_0 = 0`, because `y_1y_2 ⋯ y_k` divides `χ'_{Id_k}(π)` by
`HJO.Dyck.unnormalisedCharSeries_eq_C_prod_X_mul`", so that the expansion runs over `j ≥ 1`. -/
theorem zPart_auxToFrac_unnormalisedCharSeries_zero (q : K) (hk : k + 1 ≤ N)
    (hlt : ∀ j, σ j < k + 1) (hinj : Function.Injective σ) :
    Sym.zPart K k (Sym.auxToFrac K (k + 1) (unnormalisedCharSeries q (k + 1) x σ)) 0 = 0 :=
  MvPowerSeries.ext fun α => by
    rw [Sym.coeff_zPart, zCoeff_auxToFrac_unnormalisedCharSeries_optionElim_zero q hk hlt hinj,
      map_zero, MvPowerSeries.coeff_zero]

/-- **`c_0 = 0` at the identity tuple**, whose entries are `0, …, k`: the labels below the level,
each once. -/
theorem zPart_auxToFrac_unnormalisedCharSeries_identityTuple_zero (q : K) (hk : k + 1 ≤ N) :
    Sym.zPart K k (Sym.auxToFrac K (k + 1)
      (unnormalisedCharSeries q (k + 1) x (identityTuple (k + 1)))) 0 = 0 :=
  zPart_auxToFrac_unnormalisedCharSeries_zero q hk (identityTuple_lt (k + 1))
    (identityTuple_injective (k + 1))

/-- **The expansion of `χ'_σ(π)` in powers of `y_{k+1}`**: a finite sum `∑_{j ≤ M}y_{k+1}^j c_j`
whose coefficients `c_j` are free of `y_{k+1}`. Together with
`HJO.Sym.eq_of_sum_pow_mul_eq` — the coefficients of such an expansion are unique — and
`HJO.Dyck.zPart_auxToFrac_unnormalisedCharSeries_identityTuple_zero` — the coefficient at `j = 0`
vanishes at the identity tuple — this is the first half of the proof of
`HJO.Dyck.existsUnique_eq_sum_pow_mul_realiseAddLetter`. -/
theorem exists_eq_sum_pow_mul_zPart_unnormalisedCharSeries (q : K) (x : Fin N → ℕ)
    (σ : Fin (k + 1) → ℕ) :
    ∃ M : ℕ, Sym.auxToFrac K (k + 1) (unnormalisedCharSeries q (k + 1) x σ)
      = ∑ j ∈ Finset.range (M + 1), MvPowerSeries.C (Sym.yFrac K (Fin.last k)) ^ j *
          Sym.zPart K k (Sym.auxToFrac K (k + 1) (unnormalisedCharSeries q (k + 1) x σ)) j :=
  Sym.exists_eq_sum_pow_mul_zPart (auxToFrac_unnormalisedCharSeries_mem_zRing q k x σ)

/-- **The expansion coefficients of `χ'_{Id_k}(π)` are symmetric in the letters.** Every finitary
relabelling of the merged alphabet fixing the distinguished letter `y_{k+1}` fixes each `c_j`:
`HJO.Dyck.zSwap_auxToFrac_unnormalisedCharSeries` gives the invariance of `χ'_{Id_k}(π)` under each
`ŝ_m` with `m ≥ k + 1`, `HJO.Sym.zPerm_eq_self_of_forall_zSwap_eq_self` turns that into invariance
under every such relabelling, and `HJO.Sym.zPerm_zPart` says that a relabelling fixing `y_{k+1}`
acts on the expansion coefficient by coefficient. -/
theorem zPerm_zPart_auxToFrac_unnormalisedCharSeries_identityTuple (q : K)
    (hx : IsPartialDyck (k + 1) N x) {ρ : Equiv.Perm (Option ℕ)} (hρ : ρ none = none)
    (hsupport : (fixedBy (Option ℕ) ρ)ᶜ.Finite) (j : ℕ) :
    Sym.zPerm K k ρ (Sym.zPart K k (Sym.auxToFrac K (k + 1)
          (unnormalisedCharSeries q (k + 1) x (identityTuple (k + 1)))) j)
      = Sym.zPart K k (Sym.auxToFrac K (k + 1)
          (unnormalisedCharSeries q (k + 1) x (identityTuple (k + 1)))) j := by
  have hmem := auxToFrac_unnormalisedCharSeries_mem_zRing q k x (identityTuple (k + 1))
  refine Sym.zPerm_zPart_eq_self hmem hρ ?_ j
  refine Sym.zPerm_eq_self_of_forall_zSwap_eq_self hmem (t₀ := 1) (fun t ht => ?_)
    (fun t ht => ?_) hsupport
  · refine zSwap_auxToFrac_unnormalisedCharSeries q hx fun i => ⟨?_, ?_⟩
    · have := i.isLt
      change (i : ℕ) ≠ k + t
      omega
    · have := i.isLt
      change (i : ℕ) ≠ k + t + 1
      omega
  · rw [show t = 0 from by omega, Sym.zLetter_zero]
    exact hρ

/-! ### The realisation of a coefficient is free of the last auxiliary variable -/

/-- The image of a power sum under a realisation is free of `y_{k+1}`: its coefficients are `0` and
`1`. -/
theorem auxToFrac_realise_powerSum_mem_zBase (hι : IsAuxRealisation (k + 1) ι) (r : ℕ) :
    Sym.auxToFrac K (k + 1) (ι (MvPolynomial.C (Sym.powerSum K (r + 1)))) ∈ Sym.zBase K k := by
  classical
  intro α
  rw [Sym.coeff_auxToFrac]
  by_cases h : ∃ i : ℕ, α = Finsupp.single i (r + 1)
  · obtain ⟨i, rfl⟩ := h
    rw [hι.coeff_pow r i, map_one]
    exact one_mem _
  · simp only [not_exists] at h
    rw [hι.coeff_of_ne r α h, map_zero]
    exact zero_mem _

/-- A constant of the lower coefficient field is free of `y_{k+1}`. -/
theorem C_auxFracCastSucc_mem_zBase (c : Sym.AuxFrac K k) :
    (MvPowerSeries.C (Sym.auxFracCastSucc K k c) : Sym.AuxAlphabetSeriesFrac K (k + 1))
      ∈ Sym.zBase K k := by
  classical
  intro α
  rw [MvPowerSeries.coeff_C]
  split_ifs
  · exact ⟨c, rfl⟩
  · exact zero_mem _

/-- The image of an element of `Λ` under a realisation is free of `y_{k+1}`: the power sums generate
`Λ` and their images have coefficients `0` and `1`, while the scalars go to constants of the
base. -/
theorem auxToFrac_realise_C_mem_zBase (hι : IsAuxRealisation (k + 1) ι) (c : Sym.Lambda K) :
    Sym.auxToFrac K (k + 1) (ι (MvPolynomial.C c)) ∈ Sym.zBase K k := by
  induction c using MvPolynomial.induction_on with
  | C a =>
    have h1 : (MvPolynomial.C (MvPolynomial.C a : Sym.Lambda K) : Sweep.Total K)
        = algebraMap K (Sweep.Total K) a := rfl
    have h2 : (algebraMap K (Sym.AuxAlphabetSeries K (k + 1)) a)
        = MvPowerSeries.C (MvPolynomial.C a) := by
      rw [MvPowerSeries.algebraMap_apply, MvPolynomial.algebraMap_eq]
    rw [h1, AlgHom.commutes, h2, auxToFrac_C,
      show algebraMap (MvPolynomial (Fin (k + 1)) K) (Sym.AuxFrac K (k + 1)) (MvPolynomial.C a)
        = Sym.scalarFrac K a from rfl, ← Sym.auxFracCastSucc_scalarFrac (K := K) (k := k) a]
    exact C_auxFracCastSucc_mem_zBase _
  | add p q hp hq =>
    rw [map_add, map_add, map_add]
    exact add_mem hp hq
  | mul_X p n hp =>
    rw [map_mul, map_mul, map_mul,
      show (MvPolynomial.X n : Sym.Lambda K) = Sym.powerSum K (n + 1) from by
        rw [Sym.powerSum, Nat.add_sub_cancel]]
    exact mul_mem hp (auxToFrac_realise_powerSum_mem_zBase hι n)

/-- **The realisation of an element of `V_{k-1}` is free of `y_{k+1}`.** That ring is generated as a
`𝕂`-algebra by the auxiliary variables `y_1, …, y_{k-1}` and the power sums; the realisation carries
the first family to constants of the lower coefficient field and the second to series with
coefficients `0` and `1`, and the series free of `y_{k+1}` form a subring. This is what makes the
substitution `g ↦ g[X + y_k]` triangular. -/
theorem auxToFrac_realise_mem_zBase (hι : IsAuxRealisation (k + 1) ι) {G : Sweep.Total K}
    (hG : G ∈ piece K k) : Sym.auxToFrac K (k + 1) (ι G) ∈ Sym.zBase K k := by
  rw [piece, MvPolynomial.supported_eq_adjoin_X] at hG
  induction hG using Algebra.adjoin_induction with
  | mem y hy =>
    obtain ⟨j, hj, rfl⟩ := hy
    have hlt : j < k := hj
    have hj' : j < k + 1 := by omega
    have haux : (MvPolynomial.X j : Sweep.Total K)
        = auxVar (((⟨j, hj'⟩ : Fin (k + 1)) : ℕ) + 1) := by
      rw [auxVar, Nat.add_sub_cancel]
    have hcast : (⟨j, hj'⟩ : Fin (k + 1)) = Fin.castSucc ⟨j, hlt⟩ := rfl
    rw [haux, hι.map_auxVar ⟨j, hj'⟩, auxToFrac_C,
      show algebraMap (MvPolynomial (Fin (k + 1)) K) (Sym.AuxFrac K (k + 1))
          (MvPolynomial.X (⟨j, hj'⟩ : Fin (k + 1))) = Sym.yFrac K (⟨j, hj'⟩ : Fin (k + 1)) from rfl,
      hcast, ← Sym.auxFracCastSucc_yFrac]
    exact C_auxFracCastSucc_mem_zBase _
  | algebraMap c =>
    rw [show algebraMap (Sym.Lambda K) (Sweep.Total K) c = MvPolynomial.C c from rfl]
    exact auxToFrac_realise_C_mem_zBase hι c
  | add u v _ _ hu hv =>
    rw [map_add, map_add]
    exact add_mem hu hv
  | mul u v _ _ hu hv =>
    rw [map_mul, map_mul]
    exact mul_mem hu hv

/-! ### The substitution `X ↦ X + y_{k+1}` is triangular -/

omit [IsDomain K] in
/-- **`ρ_{k+1}` is the identity modulo `y_{k+1}`.** It fixes every auxiliary variable and adds
`y_{k+1}^r` to the power sum `p_r`, so the two ring homomorphisms `Λ[y] → Λ[y]/(y_{k+1})` it and the
identity induce agree on both families of generators. -/
theorem addLetter_sub_mem_span (k : ℕ) (G : Sweep.Total K) :
    addLetter K (k + 1) G - G ∈ Ideal.span {(MvPolynomial.X k : Sweep.Total K)} := by
  have hgen : (MvPolynomial.X k : Sweep.Total K)
      ∈ Ideal.span {(MvPolynomial.X k : Sweep.Total K)} := Ideal.mem_span_singleton_self _
  have h : (Ideal.Quotient.mk (Ideal.span {(MvPolynomial.X k : Sweep.Total K)})).comp
        (addLetter K (k + 1)).toRingHom
      = Ideal.Quotient.mk (Ideal.span {(MvPolynomial.X k : Sweep.Total K)}) := by
    refine MvPolynomial.ringHom_ext (fun c => ?_) fun j => ?_
    · have hc : ((Ideal.Quotient.mk (Ideal.span {(MvPolynomial.X k : Sweep.Total K)})).comp
            (addLetter K (k + 1)).toRingHom).comp
              (MvPolynomial.C : Sym.Lambda K →+* Sweep.Total K)
          = (Ideal.Quotient.mk (Ideal.span {(MvPolynomial.X k : Sweep.Total K)})).comp
              (MvPolynomial.C : Sym.Lambda K →+* Sweep.Total K) := by
        refine MvPolynomial.ringHom_ext (fun a => ?_) fun r => ?_
        · have h1 : addLetter K (k + 1) (MvPolynomial.C (MvPolynomial.C a : Sym.Lambda K))
              = MvPolynomial.C (MvPolynomial.C a : Sym.Lambda K) := by
            rw [show (MvPolynomial.C (MvPolynomial.C a : Sym.Lambda K) : Sweep.Total K)
              = algebraMap K (Sweep.Total K) a from rfl, AlgHom.commutes]
          simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, h1]
        · have hps : (MvPolynomial.X r : Sym.Lambda K) = Sym.powerSum K (r + 1) := by
            rw [Sym.powerSum, Nat.add_sub_cancel]
          have h1 : addLetter K (k + 1) (MvPolynomial.C (MvPolynomial.X r : Sym.Lambda K))
              = MvPolynomial.C (MvPolynomial.X r : Sym.Lambda K)
                + (MvPolynomial.X k : Sweep.Total K) ^ (r + 1) := by
            rw [hps, addLetter_powerSum, auxVar, Nat.add_sub_cancel]
          simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, h1, map_add,
            map_pow, Ideal.Quotient.eq_zero_iff_mem.2 hgen, zero_pow (Nat.succ_ne_zero r), add_zero]
      exact RingHom.congr_fun hc c
    · simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, addLetter_auxVar]
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, sub_eq_zero]
  exact RingHom.congr_fun h G

/-- **The triangularity of `g ↦ g[X + y_k]`**: the coefficient of `y_{k+1}^0` in the realisation of
`g[X + y_{k+1}]` is the realisation of `g` itself. This is the statement "`g_j(π)[X+y_k]` is
`g_j(π)[X]` together with terms of positive degree in `y_k`". -/
theorem zPart_realiseAddLetter_zero (hι : IsAuxRealisation (k + 1) ι) {G : Sweep.Total K}
    (hG : G ∈ piece K k) :
    Sym.zPart K k (realiseAddLetter K k ι G) 0 = Sym.auxToFrac K (k + 1) (ι G) := by
  obtain ⟨R, hR⟩ := Ideal.mem_span_singleton.1 (addLetter_sub_mem_span k G)
  have hadd : addLetter K (k + 1) G = G + MvPolynomial.X k * R := by
    rw [← hR, add_sub_cancel]
  have hiXk : ι (MvPolynomial.X k : Sweep.Total K)
      = MvPowerSeries.C (MvPolynomial.X (Fin.last k)) := by
    have h := hι.map_auxVar (Fin.last k)
    rwa [Fin.val_last, auxVar, Nat.add_sub_cancel] at h
  refine MvPowerSeries.ext fun α => ?_
  rw [Sym.coeff_zPart, ← Sym.auxFracCastSucc_zCoeff_of_mem_zBase
    (auxToFrac_realise_mem_zBase hι hG) α]
  congr 1
  rw [realiseAddLetter_apply, Sym.zCoeff_auxToFrac, Sym.zCoeff_auxToFrac]
  congr 1
  rw [hadd, map_add, map_mul, hiXk, map_add, MvPowerSeries.coeff_C_mul, map_add,
    map_mul, Sym.auxSplitLast_X_last, Polynomial.coeff_add, Polynomial.mul_coeff_zero,
    Polynomial.coeff_X_zero, zero_mul, add_zero]

/-- `g[X + y_{k+1}]`, realised in `P°_{k+1}`, lies in `Z^{(k+1)}`: this is the half of
`HJO.Dyck.realiseAddLetter_mem_zSymmSubring` that the expansion needs, the symmetry being the
other. -/
theorem realiseAddLetter_mem_zRing (hι : IsAuxRealisation (k + 1) ι) {G : Sweep.Total K}
    (hG : G ∈ piece K k) : realiseAddLetter K k ι G ∈ Sym.zRing K k :=
  (realiseAddLetter_mem_zSymmSubring hι hG).1

/-- **The triangular substitution determines the coefficients `g_j` recursively.** If
`∑_j y_{k+1}^j g_j[X + y_{k+1}]` vanishes, with every `g_j` in `V_{k-1}` and all but finitely many
of them zero, then every `g_j` vanishes.

This is the uniqueness half of `HJO.Dyck.existsUnique_eq_sum_pow_mul_realiseAddLetter`, and it is
exactly the triangularity argument: the coefficient of `y_{k+1}^n` in the sum is
`g_n[X]` plus contributions of `g_j` with `j < n` only (`HJO.Sym.zPart_C_pow_mul_of_lt` kills
`j > n`, and `HJO.Dyck.zPart_realiseAddLetter_zero` identifies the term at `j = n`), so an induction
on `n` reads off `ι(g_n) = 0` one index at a time.

The injectivity of `ι` on `V_{k-1}` is a hypothesis, so that the statement holds over an arbitrary
base; `HJO.Sym.realisation_injective` is the statement at the level `0`, about `Λ`, and
`HJO.Dyck.realise_injective_on_piece` supplies the hypothesis over a `ℚ`-algebra base. -/
theorem eq_zero_of_sum_pow_mul_realiseAddLetter_eq_zero (hι : IsAuxRealisation (k + 1) ι)
    (hinj : ∀ F ∈ piece K k, ι F = 0 → F = 0) {s : Finset ℕ} {g : ℕ → Sweep.Total K}
    (hg : ∀ j, g j ∈ piece K k) (hg0 : ∀ j ∉ s, g j = 0)
    (hsum : ∑ j ∈ s, MvPowerSeries.C (Sym.yFrac K (Fin.last k)) ^ j *
      realiseAddLetter K k ι (g j) = 0) :
    ∀ j, g j = 0 := by
  classical
  have hrange : ∀ j : ℕ, ∀ α : ℕ →₀ ℕ,
      MvPowerSeries.coeff α (realiseAddLetter K k ι (g j)) ∈ (Sym.yFracEval K k).range :=
    fun j α => Sym.coeff_mem_range_yFracEval_of_mem_zRing (realiseAddLetter_mem_zRing hι (hg j)) α
  have step : ∀ n : ℕ, (∀ i < n, g i = 0) → g n = 0 := by
    intro n hbelow
    by_cases hn : n ∈ s
    · have hzp := Sym.zPart_sum (t := s)
        (F := fun j => MvPowerSeries.C (Sym.yFrac K (Fin.last k)) ^ j *
          realiseAddLetter K k ι (g j))
        (fun j _ α => Sym.coeff_C_pow_mul_mem_range_yFracEval (hrange j) j α) n
      rw [hsum, Sym.zPart_zero] at hzp
      have hterm : Sym.zPart K k (MvPowerSeries.C (Sym.yFrac K (Fin.last k)) ^ n *
          realiseAddLetter K k ι (g n)) n = Sym.auxToFrac K (k + 1) (ι (g n)) := by
        have h := Sym.zPart_C_pow_mul (hrange n) n 0
        rw [zero_add] at h
        rw [h, zPart_realiseAddLetter_zero hι (hg n)]
      have hsingle := Finset.sum_eq_single_of_mem n hn
        (f := fun j => Sym.zPart K k (MvPowerSeries.C (Sym.yFrac K (Fin.last k)) ^ j *
          realiseAddLetter K k ι (g j)) n)
        fun j _ hjn => by
          rcases lt_or_gt_of_ne hjn with hlt | hgt
          · rw [hbelow j hlt, map_zero, mul_zero, Sym.zPart_zero]
          · exact Sym.zPart_C_pow_mul_of_lt (hrange j) hgt
      have h0 : Sym.auxToFrac K (k + 1) (ι (g n)) = 0 := by
        rw [← hterm, ← hsingle, ← hzp]
      exact hinj (g n) (hg n)
        (Sym.auxToFrac_injective (k + 1) (by rw [h0, map_zero]))
    · exact hg0 n hn
  have key : ∀ n : ℕ, ∀ i < n, g i = 0 := by
    intro n
    induction n with
    | zero => exact fun i hi => absurd hi (Nat.not_lt_zero i)
    | succ n ihn =>
      intro i hi
      rcases eq_or_lt_of_le (Nat.lt_succ_iff.1 hi) with heq | hlt
      · subst heq
        exact step i ihn
      · exact ihn i hlt
  exact fun n => step n (key n)

/-- **The expansion `∑_{j ≥ 1}y_k^j g_j[X + y_k]` determines the `g_j`**: the uniqueness half of
`HJO.Dyck.existsUnique_eq_sum_pow_mul_realiseAddLetter`, stated for two finitely supported families
of elements of `V_{k-1}` with the same expansion. -/
theorem eq_of_sum_pow_mul_realiseAddLetter_eq (hι : IsAuxRealisation (k + 1) ι)
    (hinj : ∀ F ∈ piece K k, ι F = 0 → F = 0) {s : Finset ℕ} {g g' : ℕ → Sweep.Total K}
    (hg : ∀ j, g j ∈ piece K k) (hg' : ∀ j, g' j ∈ piece K k)
    (hg0 : ∀ j ∉ s, g j = 0) (hg0' : ∀ j ∉ s, g' j = 0)
    (heq : ∑ j ∈ s, MvPowerSeries.C (Sym.yFrac K (Fin.last k)) ^ j *
        realiseAddLetter K k ι (g j)
      = ∑ j ∈ s, MvPowerSeries.C (Sym.yFrac K (Fin.last k)) ^ j *
        realiseAddLetter K k ι (g' j)) :
    ∀ j, g j = g' j := by
  have hzero := eq_zero_of_sum_pow_mul_realiseAddLetter_eq_zero hι hinj
    (g := fun j => g j - g' j) (s := s) (fun j => sub_mem (hg j) (hg' j))
    (fun j hj => by rw [hg0 j hj, hg0' j hj, sub_self]) ?_
  · exact fun j => sub_eq_zero.1 (hzero j)
  · rw [show ∑ j ∈ s, MvPowerSeries.C (Sym.yFrac K (Fin.last k)) ^ j *
        realiseAddLetter K k ι (g j - g' j)
      = (∑ j ∈ s, MvPowerSeries.C (Sym.yFrac K (Fin.last k)) ^ j *
          realiseAddLetter K k ι (g j))
        - ∑ j ∈ s, MvPowerSeries.C (Sym.yFrac K (Fin.last k)) ^ j *
          realiseAddLetter K k ι (g' j) from by
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun j _ => by rw [map_sub, mul_sub], heq, sub_self]

end HJO.Dyck
