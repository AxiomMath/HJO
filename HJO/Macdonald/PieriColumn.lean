/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.Macdonald.PieriPpoly
public meta import HJO.Attr

/-! # Adding a full first column multiplies by the product of the variables

`HJO.Mac.macPpoly_eq_prod_X_mul`: if `κ_i = λ_i + 1` for every letter of the alphabet then
`res_n(e_n) P_λ[X_n] = P_κ[X_n]`. This is Stanley's Proposition 5.1 in Macdonald's normalisation,
and it is what proves the case of the Pieri support in which the right-hand index is no longer than
the left-hand one.

## The proof

`HJO.Mac.eq_macPpoly` asks for the two conditions of `HJO.Mac.macPpoly` on
`g := x_1 ⋯ x_n P_λ[X_n]`, and both are computations.

* The eigenvalue. `T_{q,x_i}` scales `x_1 ⋯ x_n` by `q` (`HJO.Mac.qShift_algebraMap_prod_X`), so
  `D^{(n)}_1(x_1 ⋯ x_n f) = q\,x_1 ⋯ x_n D^{(n)}_1 f` (`HJO.Mac.macOp_prod_X_mul`) --- the whole
  content of the eigenfunction paragraph, with no sum over `i` left to do. And
  `E_n(κ) = q E_n(λ)` (`HJO.Mac.macdonaldEigenvalue_partDiagram_add_onesExp`), adding one to every
  part multiplying each term of the eigenvalue by `q`.
* The shape. The coefficient of `x^{\bar\nu}` in `g` is the coefficient of `x^{\bar\nu - (1,…,1)}`
  in `P_λ[X_n]` when `(1,…,1) ≤ \bar\nu` and `0` otherwise, so it is `1` at `\bar\kappa` and
  vanishes above it, the lexicographic order being translation invariant
  (`Finsupp.add_lex_add_iff_right`). `HJO.Mac.sub_msymm_mem_span_lowerMsymmSet` turns that into
  membership in the span: an element of `𝒮_{n,D}` whose coefficients at the exponents `\bar\nu` are
  those of `m_κ[X_n]` outside the lower set *is* `m_κ[X_n]` modulo the lower set, the coordinates in
  the monomial symmetric basis being those coefficients.

`sub_msymm_mem_span_lowerMsymmSet` is the reading of the monomial symmetric basis that
`HJO.Mac.macOpComp_msymm_sub_smul_mem_span_of_ne_zero` carries out inline; it is stated here
because this is the second consumer, and its own file cannot be edited from this seat.

## Main results

* `HJO.Mac.exists_partExp_eq`, `HJO.Mac.exists_partExp_eq_onesExp_add`: an index is readable off
  any weakly decreasing exponent vector, so the `κ` of the statement below exists for every `λ`.
* `HJO.Mac.macOp_prod_X_mul`: `D^{(n)}_1(x_1 ⋯ x_n f) = q\,x_1 ⋯ x_n D^{(n)}_1 f`.
* `HJO.Mac.sub_msymm_mem_span_lowerMsymmSet`: coefficients at the exponents `\bar\nu` decide
  membership in `m_μ[X_n] +` the span of the lower monomial symmetric polynomials.
* `HJO.Mac.macPpoly_eq_prod_X_mul`.

## References

Lemma `HJO.Mac.macPpoly_eq_prod_X_mul`, on
Definitions `HJO.Sym.elemSymm`, `HJO.Sym.rowLenSeq`, `HJO.Sym.cells`,
`MvPolynomial.symmetricSubalgebra`, `MvPolynomial.symmetricHomogeneousSubmodule`,
`HJO.Mac.msymmMem`, `Finsupp.lex_lt_iff_isLeast`, `MonomialOrder.lex_degree_isGreatest`,
`HJO.Sym.restrictAlphabet`, `HJO.Mac.qShift`, `HJO.Mac.macOp`, `HJO.Sym.macdonaldEigenvalue` and
`HJO.Mac.macPpoly`.
-/

@[expose] public section

open Finset MvPolynomial MonomialOrder

namespace HJO.Mac

/-! ### The exponent vector of the product of all the variables -/

section Ones

variable {σ : Type*} [Fintype σ]

/-- The product of all the variables has degree `n`: every one of the `n` entries of its exponent
vector is `1`. -/
theorem degree_onesExp (σ : Type*) [Fintype σ] : (onesExp σ).degree = Fintype.card σ := by
  classical
  have hs : (onesExp σ).support = Finset.univ := by
    ext j
    simp [Finsupp.mem_support_iff]
  rw [Finsupp.degree_apply, hs]
  simp

/-- The product of all the variables is homogeneous of degree `n`. -/
theorem isHomogeneous_prod_X (σ : Type*) [Fintype σ] (R : Type*) [CommSemiring R] :
    (∏ j : σ, (X j : MvPolynomial σ R)).IsHomogeneous (Fintype.card σ) := by
  rw [prod_X_eq_monomial_onesExp]
  exact isHomogeneous_monomial _ (degree_onesExp σ)

/-- The product of all the variables is symmetric: renaming the letters permutes the factors. -/
theorem isSymmetric_prod_X (σ : Type*) [Fintype σ] (R : Type*) [CommSemiring R] :
    (∏ j : σ, (X j : MvPolynomial σ R)).IsSymmetric := by
  intro e
  rw [map_prod]
  exact Fintype.prod_equiv e _ _ fun j => rename_X e j

end Ones

/-! ### Reading an index off its exponent vector -/

section Exists

variable {σ : Type*} [Fintype σ] [LinearOrder σ]

/-- **Every weakly decreasing exponent vector is the exponent vector of an index.** The converse of
`HJO.Mac.eq_partExp`: `α` is the multiplicity vector of a multiset of `|α|` letters
(`MvPolynomial.degree_eq_iff_exists_sym`), whose multiplicity partition has at most `n` parts. The
size is an argument so that the index lands in the type the consumer wants. -/
theorem exists_partExp_eq {α : σ →₀ ℕ} (hα : Antitone α) {D : ℕ} (hD : α.degree = D) :
    ∃ μ : PartIdx σ D, partExp σ μ = α := by
  classical
  subst hD
  obtain ⟨a, ha⟩ := degree_eq_iff_exists_sym.mp (rfl : α.degree = α.degree)
  refine ⟨⟨Nat.Partition.ofSym a, Nat.Partition.parts_card_le a⟩, ?_⟩
  rw [← eq_partExp rfl (by rw [ha]; exact hα)]
  exact ha

/-- Adding one to every entry of a weakly decreasing exponent vector leaves it weakly
decreasing. -/
theorem antitone_onesExp_add {α : σ →₀ ℕ} (hα : Antitone α) : Antitone (onesExp σ + α) := by
  intro i j hij
  simp only [Finsupp.add_apply, onesExp_apply]
  exact Nat.add_le_add_left (hα hij) 1

/-- **The index with a full first column added exists**: this is the `κ` of
`HJO.Mac.macPpoly_eq_prod_X_mul`, produced for a given `λ`. Its size is `|λ| + n`, one new cell in
each of the `n` rows. -/
theorem exists_partExp_eq_onesExp_add {d : ℕ} (lam : PartIdx σ d) :
    ∃ κ : PartIdx σ (Fintype.card σ + d), partExp σ κ = onesExp σ + partExp σ lam :=
  exists_partExp_eq (antitone_onesExp_add (antitone_partExp lam))
    (by rw [map_add Finsupp.degree, degree_onesExp, degree_partExp])

end Exists

/-! ### The product of all the variables carries an eigenfunction to an eigenfunction -/

section Shift

variable {σ : Type*} [LinearOrder σ] [Fintype σ] {K : Type*} [Field K] {q : Kˣ} {u : K}

/-- **The parameter shift `T_{q,x_i}` scales the product of all the variables by `q`**: it scales
`x_i` and fixes the other `n - 1` factors. -/
theorem rescaleEquiv_mulSingle_prod_X (q : Kˣ) (i : σ) :
    rescaleEquiv (Pi.mulSingle i q) (∏ j : σ, (X j : MvPolynomial σ K))
      = (q : K) • ∏ j : σ, (X j : MvPolynomial σ K) := by
  classical
  rw [prod_X_eq_monomial_onesExp, rescaleEquiv_monomial, prod_mulSingle_pow, onesExp_apply,
    pow_one, one_mul, smul_monomial, smul_eq_mul, mul_one]

/-- The parameter shift scales the product of all the variables by `q`, in the rational function
field where Macdonald's operator lives. -/
theorem qShift_algebraMap_prod_X (q : Kˣ) (i : σ) :
    qShift q i (algebraMap (MvPolynomial σ K) (FractionRing (MvPolynomial σ K))
        (∏ j : σ, X j))
      = (q : K) • algebraMap (MvPolynomial σ K) (FractionRing (MvPolynomial σ K))
        (∏ j : σ, (X j : MvPolynomial σ K)) := by
  rw [qShift_algebraMap, rescaleEquiv_mulSingle_prod_X, algebraMap_smul]

/-- **Macdonald's operator against the product of all the variables**:
`D^{(n)}_1(x_1 ⋯ x_n f) = q\,x_1 ⋯ x_n D^{(n)}_1 f`. This is the eigenfunction
computation: each `T_{q,x_i}` pulls one factor `q` out of the product and leaves the sum over `i`
untouched. -/
theorem macOp_prod_X_mul (q : Kˣ) (u : K) (f : FractionRing (MvPolynomial σ K)) :
    macOp q u (algebraMap (MvPolynomial σ K) (FractionRing (MvPolynomial σ K))
          (∏ j : σ, X j) * f)
      = (q : K) • (algebraMap (MvPolynomial σ K) (FractionRing (MvPolynomial σ K))
          (∏ j : σ, (X j : MvPolynomial σ K)) * macOp q u f) := by
  rw [macOp_apply, macOp_apply, Finset.mul_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_mul, qShift_algebraMap_prod_X, smul_mul_assoc, mul_smul_comm]
  exact congrArg _ (mul_left_comm _ _ _)

end Shift

/-! ### The eigenvalue of an index with a full first column added -/

section Eigenvalue

variable {σ : Type*} [LinearOrder σ] [Fintype σ] {K : Type*} [CommSemiring K] {d e : ℕ}

/-- **Adding one to every part multiplies the eigenvalue by `q`**: `E_n(κ) = q E_n(λ)`, each term
`q^{λ_i}u^{\#\{j : i < j\}}` of `HJO.Mac.macdonaldEigenvalue_partDiagram` gaining one factor `q`. -/
theorem macdonaldEigenvalue_partDiagram_add_onesExp (q u : K) {lam : PartIdx σ d}
    {κ : PartIdx σ e} (hκ : partExp σ κ = onesExp σ + partExp σ lam) :
    HJO.Sym.macdonaldEigenvalue q u (Fintype.card σ) (partDiagram σ κ)
      = q * HJO.Sym.macdonaldEigenvalue q u (Fintype.card σ) (partDiagram σ lam) := by
  classical
  rw [macdonaldEigenvalue_partDiagram, macdonaldEigenvalue_partDiagram, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [hκ, Finsupp.add_apply, onesExp_apply, pow_add, pow_one, mul_assoc]

end Eigenvalue

/-! ### Coefficients decide membership in the lower span -/

section Coordinates

variable {σ : Type*} [LinearOrder σ] [Fintype σ] {K : Type*} [Field K] {D : ℕ}

/-- **An element of `𝒮_{n,D}` is `m_μ[X_n]` modulo the lower monomial symmetric polynomials as soon
as its coefficients say so.** The coordinates of an element of `𝒮_{n,D}` in the monomial symmetric
basis are its coefficients at the exponents `\bar\nu`
(`MvPolynomial.exists_basis_symmetricHomogeneousSubmodule_msymm` and `HJO.Mac.coeff_partExp_msymm`),
so prescribing those outside the lower set prescribes the element modulo it.

This is the step `HJO.Mac.macOpComp_msymm_sub_smul_mem_span_of_ne_zero` performs inline for
Macdonald's operator; `HJO.Mac.macPpoly_eq_prod_X_mul` is the second consumer. -/
theorem sub_msymm_mem_span_lowerMsymmSet {μ : PartIdx σ D} {f : MvPolynomial σ K}
    (hf : f ∈ symmetricHomogeneousSubmodule σ K D)
    (hcoeff : ∀ ν : PartIdx σ D, ¬ toLex (partExp σ ν) < toLex (partExp σ μ) →
      coeff (partExp σ ν) f = if ν = μ then 1 else 0) :
    f - msymm σ K μ.1 ∈ Submodule.span K (lowerMsymmSet σ K μ) := by
  classical
  obtain ⟨B, hB⟩ := exists_basis_symmetricHomogeneousSubmodule_msymm σ K D
  set x : symmetricHomogeneousSubmodule σ K D := ⟨f, hf⟩ - msymmMem σ K μ with hxdef
  have hxcoe : (x : MvPolynomial σ K) = f - msymm σ K μ.1 := rfl
  -- the coordinates of an element of `𝒮_{n,D}` are its coefficients at the exponents `\bar\nu`
  have hrepr : ∀ (ν : PartIdx σ D) (y : symmetricHomogeneousSubmodule σ K D),
      B.repr y ν = coeff (partExp σ ν) (y : MvPolynomial σ K) := by
    intro ν
    have hext : (Finsupp.lapply ν).comp (B.repr : symmetricHomogeneousSubmodule σ K D →ₗ[K] _)
        = (lcoeff K (partExp σ ν)).comp (symmetricHomogeneousSubmodule σ K D).subtype :=
      B.ext fun ρ => by
        rw [LinearMap.comp_apply, LinearMap.comp_apply, Finsupp.lapply_apply, LinearEquiv.coe_coe,
          Module.Basis.repr_self, Submodule.subtype_apply, lcoeff_apply, hB, coeff_partExp_msymm,
          Finsupp.single_apply]
        exact if_congr eq_comm rfl rfl
    exact fun y => LinearMap.congr_fun hext y
  have hzero : ∀ ν : PartIdx σ D, ¬ toLex (partExp σ ν) < toLex (partExp σ μ) →
      B.repr x ν = 0 := by
    intro ν hν
    rw [hrepr, hxcoe, coeff_sub, coeff_partExp_msymm, hcoeff ν hν]
    split_ifs with h
    · rw [sub_self]
    · rw [sub_zero]
  have hsum : (x : MvPolynomial σ K) = ∑ ν : PartIdx σ D, B.repr x ν • msymm σ K ν.1 := by
    have h1 : ((∑ ν : PartIdx σ D, B.repr x ν • B ν :
        symmetricHomogeneousSubmodule σ K D) : MvPolynomial σ K)
        = ∑ ν : PartIdx σ D, B.repr x ν • msymm σ K ν.1 := by
      rw [AddSubmonoidClass.coe_finsetSum]
      exact Finset.sum_congr rfl fun ν _ => by rw [SetLike.val_smul, hB]
    rw [← h1, B.sum_repr x]
  rw [← hxcoe, hsum]
  refine Submodule.sum_mem _ fun ν _ => ?_
  by_cases hlow : toLex (partExp σ ν) < toLex (partExp σ μ)
  · exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨ν, hlow, rfl⟩)
  · rw [hzero ν hlow, zero_smul]
    exact Submodule.zero_mem _

end Coordinates

/-! ### Adding a full first column -/

section Column

variable {σ : Type*} [LinearOrder σ] [Fintype σ] {K : Type*} [Field K] [Algebra ℚ K] {q : Kˣ}
  {u : K} {d e : ℕ}

/-- **Adding a full first column multiplies Macdonald's polynomial by the
product of the variables.** If `\bar\kappa = (1,…,1) + \bar\lambda`, that is `κ_i = λ_i + 1` for
every one of the `n` letters, then `P_κ[X_n] = x_1 ⋯ x_n P_λ[X_n]`.

The restriction `res_n(e_n)` is `x_1 ⋯ x_n` by `HJO.Sym.restrictAlphabet_elemSymm` and
`HJO.Mac.esymm_fintypeCard`; its hypotheses `λ_{n+1} = κ_{n+1} = 0` are carried by the index type
`PartIdx`, and its `|κ| = |λ| + n` is forced by the exponent vectors, so it is derived here rather
than assumed. -/
@[hjo "lem_pie_ppoly_column"]
theorem macPpoly_eq_prod_X_mul (hqu : AlgebraicIndependent ℤ ![(q : K), u]) {lam : PartIdx σ d}
    {κ : PartIdx σ e} (hκ : partExp σ κ = onesExp σ + partExp σ lam) :
    (macPpoly hqu κ : MvPolynomial σ K)
      = (∏ j : σ, X j) * (macPpoly hqu lam : MvPolynomial σ K) := by
  classical
  -- the size of `κ` is forced
  have he : Fintype.card σ + d = e := by
    have h1 := degree_partExp κ
    rw [hκ, map_add Finsupp.degree, degree_onesExp, degree_partExp] at h1
    exact h1
  subst he
  -- `g` lies in `𝒮_{n,|κ|}`
  have hg : ((∏ j : σ, X j) * (macPpoly hqu lam : MvPolynomial σ K))
      ∈ symmetricHomogeneousSubmodule σ K (Fintype.card σ + d) := by
    obtain ⟨hsym, hhom⟩ := mem_symmetricHomogeneousSubmodule.mp (macPpoly hqu lam).2
    exact mem_symmetricHomogeneousSubmodule.mpr
      ⟨(isSymmetric_prod_X σ K).mul hsym, (isHomogeneous_prod_X σ K).mul hhom⟩
  refine (congrArg (Subtype.val (p := fun p => p ∈ symmetricHomogeneousSubmodule σ K _))
    (eq_macPpoly hqu (f := ⟨_, hg⟩) ⟨?_, ?_⟩)).symm
  · -- the eigenvalue condition
    refine eq_macOpComp q u _ ?_
    rw [SetLike.val_smul, algebraMap_smul, macdonaldEigenvalue_partDiagram_add_onesExp _ _ hκ,
      map_mul, macOp_prod_X_mul, ← algebraMap_macOpComp, macOpComp_macPpoly, SetLike.val_smul,
      algebraMap_smul, mul_smul_comm, smul_smul]
  · -- the shape condition
    refine sub_msymm_mem_span_lowerMsymmSet hg fun ν hν => ?_
    have hcoeff : coeff (partExp σ ν) ((∏ j : σ, X j) * (macPpoly hqu lam : MvPolynomial σ K))
        = if onesExp σ ≤ partExp σ ν then
            coeff (partExp σ ν - onesExp σ) (macPpoly hqu lam : MvPolynomial σ K) else 0 := by
      rw [prod_X_eq_monomial_onesExp, coeff_monomial_mul']
      split_ifs with h
      · rw [one_mul]
      · rfl
    rw [hcoeff]
    by_cases hνκ : ν = κ
    · subst hνκ
      rw [hκ, add_tsub_cancel_left, coeff_partExp_macPpoly]
      simp
    · rw [ite_eq_right fun h => absurd h hνκ]
      split_ifs with hle
      · -- above `\bar\kappa`, so the shifted exponent is above `\bar\lambda`
        have hlt : toLex (partExp σ κ) < toLex (partExp σ ν) :=
          lt_of_le_of_ne (le_of_not_gt hν) fun heq =>
            hνκ (partExp_injective (toLex.injective heq)).symm
        rw [hκ] at hlt
        have hsplit : partExp σ ν = onesExp σ + (partExp σ ν - onesExp σ) :=
          (add_tsub_cancel_of_le hle).symm
        rw [hsplit] at hlt
        have hlt2 : toLex (partExp σ lam) < toLex (partExp σ ν - onesExp σ) := by
          rwa [toLex_add, toLex_add, add_lt_add_iff_left] at hlt
        by_contra hne
        exact absurd (lt_of_lt_of_le hlt2
          (toLex_le_of_mem_support_macPpoly hqu lam (mem_support_iff.mpr hne))) (lt_irrefl _)
      · rfl

end Column

end HJO.Mac
