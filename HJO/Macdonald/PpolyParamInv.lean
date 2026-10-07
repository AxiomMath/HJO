/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.Macdonald.HtildeSpan
public meta import HJO.Attr

/-! # The invariance of `P_μ` under inverting both parameters, reduced to one eigenvalue relation

`HJO.Sym.coeffSubst_macPfun` --- `ς(P_μ) = P_μ`, the hypothesis `hPι` of
`HJO.Standing.hasUnnormalisedMacdonaldEigenbasis_macHtilde_param` --- reduced to
`HJO.Mac.macOpCompInv_macPpoly`, the statement that the conjugated operator
`\widehat D^{(n)}_1 = \widehat\iota_n ∘ D^{(n)}_1 ∘ \widehat\iota_n` scales `P_μ[X_n]` by
`ι(E_n(μ))`.

**Four of the eight steps of the argument are covered here, in the form the argument uses**, and
they are the four that are not about Macdonald's operator itself: the inversion acting on a graded
piece (`HJO.Mac.exists_mem_eq_paramInvFrac_algebraMap`), the triangularity of the conjugated
operator (`HJO.Mac.exists_eq_paramInvFrac_macOp_msymm`), the appeal to the uniqueness of the monic
eigenfunction (`HJO.Mac.paramInvComp_macPpoly` from `HJO.Mac.macOpCompInv_macPpoly`) and the passage
from the finite alphabet to `Λ` (`HJO.Sym.coeffSubst_macPfun` from `HJO.Mac.paramInvComp_macPpoly`).

## Main definitions

* `HJO.Mac.paramInvComp`: `\widehat\iota_n` on the graded piece `𝒮_{n,d}`, the `ι`-semilinear
  involution applying `ι` to each coefficient.
* `HJO.Mac.macOpCompInv`: the conjugated operator
  `\widehat D^{(n)}_1 = \widehat\iota_n ∘ D^{(n)}_1 ∘ \widehat\iota_n` on `𝒮_{n,d}`.

## Main results

* `HJO.Mac.map_mem_symmetricHomogeneousSubmodule`: the graded-piece form of
  `HJO.Mac.exists_mem_eq_paramInvFrac_algebraMap`.
* `HJO.Mac.macOpCompInv_msymm_sub_smul_mem_span`: the graded-piece form of
  `HJO.Mac.exists_eq_paramInvFrac_macOp_msymm`.
* `HJO.Sym.restrictAlphabet_coeffSubst`: **restriction intertwines the two inversions**,
  `res_n ∘ ς = \widehat\iota_n ∘ res_n`. This is the first paragraph of the proof of
  `HJO.Sym.coeffSubst_macPfun`.
* `HJO.Mac.paramInvComp_macPpoly_of_eigen`: `HJO.Mac.paramInvComp_macPpoly` from
  `HJO.Mac.macOpCompInv_macPpoly`.
* `HJO.Sym.coeffSubst_macPfun_of_finite`: `hPι` at one `μ` from `HJO.Mac.paramInvComp_macPpoly`.
* `HJO.Sym.coeffSubst_macPfun_of_eigen`: `hPι` at one `μ` from `HJO.Mac.macOpCompInv_macPpoly`
  alone.
* `HJO.Standing.hasUnnormalisedMacdonaldEigenbasis_of_dop_and_eigen_param`: the first residual
  hypothesis of the collinear goal from `HJO.Standing.dop_zero_smul_macHtilde_param` and
  `HJO.Mac.macOpCompInv_macPpoly`, and nothing else.

## What is not here, and what it needs

`HJO.Mac.macOpCompInv_macPpoly` --- `\widehat D^{(n)}_1P_μ[X_n] = ι(E_n(μ))P_μ[X_n]` --- is the
hypothesis `hinv` of `coeffSubst_macPfun_of_eigen` and of
`HJO.Standing.hasUnnormalisedMacdonaldEigenbasis_of_dop_and_eigen_param`. Of the inputs its
proof spends, `HJO.Mac.exists_basis_macPpoly`, `HJO.Sym.eq_of_macdonaldEigenvalue_eq` and
`HJO.Mac.exists_eq_paramInvFrac_macOp_msymm` are proved elsewhere; what is left, and is proved in
`HJO/Macdonald/DopCommute.lean`, is

* **`HJO.Mac.macOp_comm`**, the identity
  `D^{(n)}_1\widehat D^{(n)}_1 = \widehat D^{(n)}_1D^{(n)}_1`, which on the rational function field
  is `HJO.Mac.macCoeff_cross` --- an identity between two products of linear forms in `x_i`, `x_j`,
  `q` and `u` --- summed over the pairs, with the diagonal term killed by `D(1) ∈ 𝕜`. This is the
  whole remaining cost of `hPι`, and it is the one thing this file does not touch: it needs the
  operator on the fraction field (`HJO.Mac.macOp`, `HJO.Mac.macCoeff`, `HJO.Mac.qShift`), not on the
  graded piece, and the inversion there as well;
* the two linear-algebra steps of that proof: reading `\widehat D^{(n)}_1P_μ[X_n]` in the basis
  `HJO.Mac.exists_basis_macPpoly` to see it is a multiple of `P_μ[X_n]`, and reading the coefficient
  of `m_μ[X_n]` against `HJO.Mac.exists_eq_paramInvFrac_macOp_msymm` to identify the multiple as
  `ι(E_n(μ))`.

## Why the graded-piece forms suffice

The `\widehat\iota_n` (`HJO.Mac.paramInvFrac`) and `\widehat D^{(n)}_1` (`HJO.Mac.macOpInv`) are
maps of the rational function field `𝕜(x_1,…,x_n)`, and `HJO.Mac.paramInvFrac_macCoeff`,
`HJO.Mac.macCoeff_cross` and `HJO.Mac.macOp_comm` are statements there. `HJO.Mac.paramInvComp` and
`HJO.Mac.macOpCompInv` are their restrictions to the graded piece `𝒮_{n,d}`, which is all the
uniqueness argument consumes and is strictly less than the fraction-field statements:
`HJO.Mac.exists_mem_eq_paramInvFrac_algebraMap` and `HJO.Mac.exists_eq_paramInvFrac_macOp_msymm` are
proved in their graded-piece form, and the fraction-field forms would need the fraction-field
inversion for `HJO.Mac.macOp_comm`.

## The route taken here, and one citation it does not need

`HJO.Sym.coeffSubst_macPfun` is proved here rather than quoted from Macdonald's Chapter VI (5.13)
(iv). **So nothing here depends on that citation**: the two conditions of
`HJO.Mac.macPpoly` are what `HJO.Mac.eq_macPpoly` delivers, and the route below uses only those.
Macdonald's own proof, through the scalar product of his Section 1, is not this one; there is no
scalar product in this library and this route does not want one.

`HJO.Mac.restrictAlphabet_macPfun_partDiagram` is cited by the proof of `HJO.Sym.coeffSubst_macPfun`
and is **not needed**: that proof takes `n` to be the larger of `|μ|` and `1`, which is exactly the
alphabet `HJO.Mac.baseAlphabet μ` in which `HJO.Sym.macPfun` is defined, so
`HJO.Sym.restrictAlphabet_macPfun` --- a defining property of `HJO.Sym.macPfun` --- says what
`HJO.Mac.restrictAlphabet_macPfun_partDiagram` would be invoked for. The same observation removes
`HJO.Mac.restrictAlphabet_macPfun_partDiagram` from `HJO.Sym.exists_basis_macPfun`; see
`HJO/Macdonald/HtildeSpan.lean`.

## Genericity and the degenerate corners

Nothing here spends a nonvanishing. `hqu` is carried because `macPpoly` and `macPfun` are functions
of it, and the only hypothesis on `ι` is that it is an involution (`hιι`), which
`HJO.Ascent.paramQUInvHom_involutive` supplies at the standing field. That is as it should be: the
statement `ς(P_μ) = P_μ` is an identity between two elements of `Λ_{|μ|}` that holds wherever `P_μ`
is defined, and `P_μ` is defined exactly where `HJO.Mac.existsUnique_isMonicEigen` holds --- so the
corners `q = u = -1` and `qu = 1` recorded for that lemma are the only ones, and they are already
inside `hqu`. Instantiating at `u = 1` or at a root of unity changes nothing here, which is the
check: unlike `hspan`, this clause does not degenerate.

## References

Macdonald's polynomials: the definitions `HJO.Mac.macPpoly`, `HJO.Sym.macPfun`,
`HJO.Sym.coeffSubst`, `HJO.Mac.paramInvFrac` and `HJO.Mac.macOpInv`, and the lemmas
`HJO.Mac.existsUnique_isMonicEigen`, `HJO.Sym.restrictAlphabetComp_bijective`,
`HJO.Mac.exists_mem_eq_paramInvFrac_algebraMap`, `HJO.Mac.exists_eq_paramInvFrac_macOp_msymm`,
`HJO.Mac.macOp_comm`, `HJO.Mac.macOpCompInv_macPpoly`, `HJO.Mac.paramInvComp_macPpoly` and
`HJO.Sym.coeffSubst_macPfun`.
-/

@[expose] public section

open MvPolynomial

namespace HJO.Mac

/-! ### The parameter inversion of a finite alphabet -/

variable {σ : Type*} {K : Type*} [Field K] {d : ℕ}

/-- **The parameter inversion acts on a graded piece**
(`HJO.Mac.exists_mem_eq_paramInvFrac_algebraMap`): applying `ι` to each coefficient preserves both
symmetry and homogeneity. Symmetry because renaming the variables and substituting the coefficients
commute, homogeneity because no monomial is created. -/
theorem map_mem_symmetricHomogeneousSubmodule (ι : K →+* K) {f : MvPolynomial σ K}
    (hf : f ∈ symmetricHomogeneousSubmodule σ K d) :
    MvPolynomial.map ι f ∈ symmetricHomogeneousSubmodule σ K d := by
  obtain ⟨hsym, hhom⟩ := mem_symmetricHomogeneousSubmodule.1 hf
  refine mem_symmetricHomogeneousSubmodule.2 ⟨fun e => ?_, fun e he => ?_⟩
  · rw [← MvPolynomial.map_rename, hsym e]
  · refine hhom fun hc => he ?_
    rw [MvPolynomial.coeff_map, hc, map_zero]

/-- **`\widehat\iota_n` on the graded piece `𝒮_{n,d}`** (`HJO.Mac.paramInvFrac`): the map applying
`ι` to each coefficient. It is `ι`-semilinear rather than `𝕜`-linear
(`paramInvComp_smul`), which is why it is a bare function here and not a `LinearMap`. -/
noncomputable def paramInvComp (ι : K →+* K) (d : ℕ)
    (f : symmetricHomogeneousSubmodule σ K d) : symmetricHomogeneousSubmodule σ K d :=
  ⟨MvPolynomial.map ι (f : MvPolynomial σ K),
    map_mem_symmetricHomogeneousSubmodule ι f.2⟩

@[simp]
theorem coe_paramInvComp (ι : K →+* K) (f : symmetricHomogeneousSubmodule σ K d) :
    (paramInvComp ι d f : MvPolynomial σ K) = MvPolynomial.map ι (f : MvPolynomial σ K) := rfl

/-- `\widehat\iota_n` twists the scalars by `ι` instead of fixing them. -/
theorem paramInvComp_smul (ι : K →+* K) (c : K) (f : symmetricHomogeneousSubmodule σ K d) :
    paramInvComp ι d (c • f) = ι c • paramInvComp ι d f :=
  Subtype.ext (by
    rw [coe_paramInvComp, SetLike.val_smul, SetLike.val_smul, coe_paramInvComp,
      MvPolynomial.smul_eq_C_mul, MvPolynomial.smul_eq_C_mul, map_mul, MvPolynomial.map_C])

/-- **`\widehat\iota_n` is an involution** when `ι` is: applying `ι` twice to each coefficient. -/
theorem paramInvComp_involutive {ι : K →+* K} (hιι : ∀ c : K, ι (ι c) = c)
    (f : symmetricHomogeneousSubmodule σ K d) :
    paramInvComp ι d (paramInvComp ι d f) = f :=
  Subtype.ext (by
    rw [coe_paramInvComp, coe_paramInvComp, MvPolynomial.map_map,
      show ι.comp ι = RingHom.id K from RingHom.ext hιι, MvPolynomial.map_id])

/-- **`\widehat\iota_n` preserves a span of polynomials it fixes pointwise.** It is additive and
`ι`-semilinear, and `ι` maps the scalars into themselves, so a combination of members of `S` goes
to a combination of members of `S`. -/
theorem map_mem_span_of_forall_map_eq (ι : K →+* K) {S : Set (MvPolynomial σ K)}
    (hS : ∀ s ∈ S, MvPolynomial.map ι s = s) {x : MvPolynomial σ K}
    (hx : x ∈ Submodule.span K S) : MvPolynomial.map ι x ∈ Submodule.span K S := by
  induction hx using Submodule.span_induction with
  | mem y hy => rw [hS y hy]; exact Submodule.subset_span hy
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add y z _ _ hy hz => rw [map_add]; exact Submodule.add_mem _ hy hz
  | smul c y _ hy =>
      rw [MvPolynomial.smul_eq_C_mul, map_mul, MvPolynomial.map_C, ← MvPolynomial.smul_eq_C_mul]
      exact Submodule.smul_mem _ _ hy

/-! ### The finite-alphabet statement from the eigenvalue relation

`DecidableEq σ` is taken from `LinearOrder σ` rather than assumed separately, as in
`HJO/Macdonald/FiniteAlphabet.lean` and `HJO/Macdonald/Ppoly.lean`: with both in scope the
monomial symmetric polynomials and the span of `HJO.Mac.macOpComp_msymm_sub_smul_mem_span` pick up
different instances and nothing matches.
-/

section Eigen

variable {σ : Type*} [LinearOrder σ] [Fintype σ] {K : Type*} [Field K] [Algebra ℚ K] {d : ℕ}
  {q : Kˣ} {u : K}

omit [Algebra ℚ K] in
/-- **`\widehat\iota_n` fixes a monomial symmetric polynomial**: every coefficient of `m_ν[X_n]` is
`1` (`MvPolynomial.msymm_eq_sum_monomial`). -/
theorem map_msymm (ι : K →+* K) (ν : Nat.Partition d) :
    MvPolynomial.map ι (msymm σ K ν) = msymm σ K ν := by
  rw [msymm_eq_sum_monomial, map_sum]
  exact Finset.sum_congr rfl fun a _ => by rw [MvPolynomial.map_monomial, map_one]

/-- **The conjugated Macdonald operator on a graded piece** (`HJO.Mac.macOpInv`):
`\widehat D^{(n)}_1 = \widehat\iota_n ∘ D^{(n)}_1 ∘ \widehat\iota_n`, read on `𝒮_{n,d}` rather than
on the rational function field. It is `𝕜`-linear although `\widehat\iota_n` is not, the two
applications contributing `ι(c)` and then `ι(ι(c)) = c`; and `\widehat\iota_n` being an involution,
`\widehat\iota_n ∘ \widehat D^{(n)}_1 = D^{(n)}_1 ∘ \widehat\iota_n`, which is the form the
uniqueness argument uses. -/
noncomputable def macOpCompInv (ι : K →+* K) (q : Kˣ) (u : K) (d : ℕ)
    (f : symmetricHomogeneousSubmodule σ K d) : symmetricHomogeneousSubmodule σ K d :=
  paramInvComp ι d (macOpComp q u d (paramInvComp ι d f))

omit [Algebra ℚ K] in
/-- `\widehat\iota_n` fixes each member of the monomial symmetric basis. -/
theorem paramInvComp_msymmMem (ι : K →+* K) (μ : PartIdx σ d) :
    paramInvComp ι d (msymmMem σ K μ) = msymmMem σ K μ :=
  Subtype.ext (by rw [coe_paramInvComp, coe_msymmMem, map_msymm])

/-- **The conjugated operator is triangular on the monomial symmetric polynomials**
(`HJO.Mac.exists_eq_paramInvFrac_macOp_msymm`): `\widehat D^{(n)}_1 m_μ - ι(E_n(μ)) m_μ` is a
combination of the `m_ν` with `\bar\nu <_lex \bar\mu`.

It is `HJO.Mac.macOpComp_msymm_sub_smul_mem_span` with `ι` applied to it, and nothing more:
`\widehat\iota_n` fixes every `m_ν` (`paramInvComp_msymmMem`), so `\widehat D^{(n)}_1 m_μ` is
`\widehat\iota_n` of `D^{(n)}_1 m_μ`, whose triangular expansion the substitution carries to a
triangular expansion with `ι` applied to each scalar (`map_mem_span_of_forall_map_eq`). The
hypothesis `u ≠ 0` is the one `HJO.Mac.macOpComp_msymm_sub_smul_mem_span` carries. -/
theorem macOpCompInv_msymm_sub_smul_mem_span (hu : u ≠ 0) (ι : K →+* K) (μ : PartIdx σ d) :
    (macOpCompInv ι q u d (msymmMem σ K μ) : MvPolynomial σ K)
        - ι (HJO.Sym.macdonaldEigenvalue (q : K) u (Fintype.card σ) (partDiagram σ μ)) •
          msymm σ K μ.1
      ∈ Submodule.span K {p : MvPolynomial σ K | ∃ ν : PartIdx σ d,
          toLex (partExp σ ν) < toLex (partExp σ μ) ∧ p = msymm σ K ν.1} := by
  have h2 := map_mem_span_of_forall_map_eq ι
    (S := {p : MvPolynomial σ K | ∃ ν : PartIdx σ d,
      toLex (partExp σ ν) < toLex (partExp σ μ) ∧ p = msymm σ K ν.1})
    (fun s hs => by obtain ⟨ν, -, rfl⟩ := hs; exact map_msymm ι ν.1)
    (macOpComp_msymm_sub_smul_mem_span_of_ne_zero (q := q) hu μ)
  rw [map_sub, MvPolynomial.smul_eq_C_mul, map_mul, MvPolynomial.map_C, map_msymm,
    ← MvPolynomial.smul_eq_C_mul] at h2
  rwa [macOpCompInv, paramInvComp_msymmMem, coe_paramInvComp]

/-- **`HJO.Mac.paramInvComp_macPpoly` from `HJO.Mac.macOpCompInv_macPpoly`.** If the conjugated
operator `\widehat D^{(n)}_1 = \widehat\iota_n ∘ D^{(n)}_1 ∘ \widehat\iota_n` scales `P_ν[X_n]` by
`ι(E_n(ν))`, then `\widehat\iota_n` fixes `P_ν[X_n]`.

This is the proof of `HJO.Mac.paramInvComp_macPpoly` verbatim: the two conditions of
`HJO.Mac.macPpoly` are checked for `\widehat\iota_n(P_ν[X_n])` and
`HJO.Mac.existsUnique_isMonicEigen` --- here `HJO.Mac.eq_macPpoly` --- concludes. The eigenvalue
condition comes from the hypothesis by applying `\widehat\iota_n` to it, which turns
`\widehat D^{(n)}_1` into `D^{(n)}_1 ∘ \widehat\iota_n` and `ι(E_n(ν))` back into `E_n(ν)`; the
triangularity comes from `map_msymm` and `map_mem_span_of_forall_map_eq`. Nothing about Macdonald's
operator is used beyond the hypothesis: in particular `HJO.Mac.macOp_comm`, which the proof of the
hypothesis spends, is not spent again here. -/
theorem paramInvComp_macPpoly_of_eigen (hqu : AlgebraicIndependent ℤ ![(q : K), u])
    {ι : K →+* K} (hιι : ∀ c : K, ι (ι c) = c) {ν : PartIdx σ d}
    (hinv : macOpCompInv ι q u d (macPpoly hqu ν)
      = ι (HJO.Sym.macdonaldEigenvalue (q : K) u (Fintype.card σ) (partDiagram σ ν))
          • macPpoly hqu ν) :
    paramInvComp ι d (macPpoly hqu ν) = macPpoly hqu ν := by
  refine eq_macPpoly hqu ⟨?_, ?_⟩
  · -- the eigenvalue condition, from the hypothesis by applying `\widehat\iota_n` to it
    have h := congrArg (paramInvComp ι d) hinv
    rw [macOpCompInv, paramInvComp_involutive hιι, paramInvComp_smul, hιι] at h
    exact h
  · -- the triangularity condition, `\widehat\iota_n` fixing every `m_ρ[X_n]`
    have h := macPpoly_sub_msymm_mem_span hqu ν
    have h2 := map_mem_span_of_forall_map_eq ι
      (S := {p : MvPolynomial σ K | ∃ ρ : PartIdx σ d,
        toLex (partExp σ ρ) < toLex (partExp σ ν) ∧ p = msymm σ K ρ.1})
      (fun s hs => by obtain ⟨ρ, -, rfl⟩ := hs; exact map_msymm ι ρ.1) h
    rw [map_sub, map_msymm] at h2
    rw [coe_paramInvComp]
    exact h2

end Eigen

end HJO.Mac

/-! ### `hPι`, from the finite alphabet -/

namespace HJO.Sym

open HJO.Mac

variable {σ : Type*} [Fintype σ] {K : Type*} [Field K] [Algebra ℚ K] {q : Kˣ} {u : K}

omit [Algebra ℚ K] in
/-- **Restriction intertwines the two inversions**: `res_n(ς F) = \widehat\iota_n(res_n F)`.

This is the first paragraph of the proof of `HJO.Sym.coeffSubst_macPfun`. Both sides are
ring homomorphisms `Λ → 𝕜[x_1,…,x_n]` restricting to `ι` on the coefficients --- `res_n` being
`𝕜`-linear and `ς` acting on the coefficients by `ι` --- and both send `p_k` to
`x_1^k + ⋯ + x_n^k`: the first because `ς` fixes `p_k`, the second because `\widehat\iota_n` fixes
each `x_i` and the power sum has integer coefficients. `Λ` is a polynomial ring over the
coefficients on the `p_k`, so they agree. -/
theorem restrictAlphabet_coeffSubst (ι : K →+* K) (f : Lambda K) :
    restrictAlphabet σ K (coeffSubst ι f)
      = MvPolynomial.map ι (restrictAlphabet σ K f) := by
  have hpsum : ∀ k : ℕ, MvPolynomial.map ι (psum σ K k) = psum σ K k := by
    intro k
    rw [psum, map_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [map_pow, MvPolynomial.map_X]
  have h : ((restrictAlphabet σ K : Lambda K →ₐ[K] MvPolynomial σ K).toRingHom).comp
        (coeffSubst ι)
      = (MvPolynomial.map (σ := σ) ι).comp
        (restrictAlphabet σ K : Lambda K →ₐ[K] MvPolynomial σ K).toRingHom := by
    have hC : ∀ c : K, restrictAlphabet σ K (MvPolynomial.C c) = MvPolynomial.C c := fun c => by
      rw [← MvPolynomial.algebraMap_eq, AlgHom.commutes, MvPolynomial.algebraMap_eq]
    refine MvPolynomial.ringHom_ext (fun c => ?_) (fun i => ?_)
    · simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, coeffSubst_C, hC,
        MvPolynomial.map_C]
    · simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, coeffSubst_X,
        restrictAlphabet_powerSum', hpsum]
  exact RingHom.congr_fun h f

/-- **`hPι` at one `μ`, from `HJO.Mac.paramInvComp_macPpoly`.** If `\widehat\iota_{n_μ}` fixes
`P_μ[X_{n_μ}]` then `ς` fixes `P_μ`.

`ς(P_μ)` lies in `Λ_{|μ|}` because `ς` respects the grading
(`HJO.Sym.coeffSubst_mem_lambdaComp`), and it restricts to `P_μ[X_{n_μ}]` by
`restrictAlphabet_coeffSubst`, `HJO.Sym.restrictAlphabet_macPfun` and the hypothesis. Those two
facts pin it as `P_μ` by `HJO.Sym.eq_macPfun`, which is `HJO.Sym.restrictAlphabetComp_bijective` at
work: `res_{n_μ}` is injective on `Λ_{|μ|}`.

**The alphabet is the one `HJO.Sym.macPfun` names**, `n_μ = max(|μ|, 1)`, so
`HJO.Mac.restrictAlphabet_macPfun_partDiagram` --- the extension of `res_n(P_μ) = P_μ[X_n]` to every
`n ≥ |μ|`, which the proof cites --- is not needed. -/
theorem coeffSubst_macPfun_of_finite (hqu : AlgebraicIndependent ℤ ![(q : K), u])
    (ι : K →+* K) {μ : YoungDiagram}
    (hfin : MvPolynomial.map ι (macPpoly hqu (baseIdx μ) : MvPolynomial (baseAlphabet μ) K)
      = (macPpoly hqu (baseIdx μ) : MvPolynomial (baseAlphabet μ) K)) :
    coeffSubst ι (macPfun hqu μ) = macPfun hqu μ :=
  eq_macPfun hqu (coeffSubst_mem_lambdaComp ι (macPfun_mem hqu μ))
    (by rw [restrictAlphabet_coeffSubst, restrictAlphabet_macPfun, hfin])

/-- **`hPι` at one `μ`, from `HJO.Mac.macOpCompInv_macPpoly` alone**: if the conjugated operator
`\widehat D^{(n_μ)}_1` scales `P_μ[X_{n_μ}]` by `ι(E_{n_μ}(μ))`, then `ς(P_μ) = P_μ`.

This is the whole of `HJO.Mac.paramInvComp_macPpoly` and
`HJO.Sym.coeffSubst_macPfun` in one statement, the two steps that come after the mathematics. What
the hypothesis costs is `HJO.Mac.macOp_comm` --- the commutation of Macdonald's operator with
its inversion, from the cross-term identity `HJO.Mac.macCoeff_cross` --- together with the cheap
`HJO.Mac.exists_eq_paramInvFrac_macOp_msymm`; the eigenvalue and the basis facts the proof of the
hypothesis also uses, `HJO.Sym.eq_of_macdonaldEigenvalue_eq` and `HJO.Mac.exists_basis_macPpoly`,
are proved. -/
theorem coeffSubst_macPfun_of_eigen (hqu : AlgebraicIndependent ℤ ![(q : K), u])
    {ι : K →+* K} (hιι : ∀ c : K, ι (ι c) = c) {μ : YoungDiagram}
    (hinv : macOpCompInv ι q u μ.card (macPpoly hqu (baseIdx μ))
      = ι (macdonaldEigenvalue (q : K) u (Fintype.card (baseAlphabet μ))
            (partDiagram (baseAlphabet μ) (baseIdx μ))) • macPpoly hqu (baseIdx μ)) :
    coeffSubst ι (macPfun hqu μ) = macPfun hqu μ :=
  coeffSubst_macPfun_of_finite hqu ι
    (congrArg Subtype.val (paramInvComp_macPpoly_of_eigen hqu hιι hinv))

end HJO.Sym

/-! ### Where the collinear side stands, at the standing field -/

namespace HJO.Standing

open HJO.Ascent HJO.Sym HJO.Mac

variable (K : Type*) [Field K] [Algebra ParamRing K] [IsFractionRing ParamRing K] [Algebra ℚ K]

/-- **`hPι` at the standing field, from `HJO.Mac.macOpCompInv_macPpoly`**, in exactly the shape
`HJO.Standing.hasUnnormalisedMacdonaldEigenbasis_macHtilde_param` asks for. The involutivity of
`ς`'s coefficient map is `HJO.Ascent.paramQUInvHom_involutive`. -/
theorem coeffSubst_macPfun_param_of_eigen
    (hinv : ∀ μ : YoungDiagram,
      macOpCompInv (paramQUInvHom K) (paramQUnit K) (paramU K) μ.card
          (macPpoly (algebraicIndependent_paramQUnit K) (baseIdx μ))
        = paramQUInvHom K (macdonaldEigenvalue (paramQ K) (paramU K)
              (Fintype.card (baseAlphabet μ)) (partDiagram (baseAlphabet μ) (baseIdx μ)))
            • macPpoly (algebraicIndependent_paramQUnit K) (baseIdx μ))
    (μ : YoungDiagram) :
    coeffSubst (paramQUInvHom K) (macPfun (algebraicIndependent_paramQUnit K) μ)
      = macPfun (algebraicIndependent_paramQUnit K) μ :=
  coeffSubst_macPfun_of_eigen (algebraicIndependent_paramQUnit K) (paramQUInvHom_involutive K)
    (hinv μ)

/-- **The first residual hypothesis of the collinear goal, from two statements about operators.**
An unnormalised Macdonald eigenbasis exists at the standing field given

* `hdop`, `HJO.Standing.dop_zero_smul_macHtilde_param`: `D_0 H̃_μ = -(M B_μ - 1) H̃_μ`,
  Garsia--Haiman--Tesler's Theorem 1.2 (1.11) a; and
* `hinv`, `HJO.Mac.macOpCompInv_macPpoly`: the conjugated Macdonald operator scales `P_μ[X_{n_μ}]`
  by `ι(E_{n_μ}(μ))`.

Against `HJO.Standing.hasUnnormalisedMacdonaldEigenbasis_macHtilde_param` this has `hspan`
discharged (`HJO.Standing.span_range_macHtilde_param_eq_top`) and `hPι` replaced by the
finite-alphabet eigenvalue relation it follows from. Together with
`HJO.Sym.HasPieriEigenfamily` --- `HJO.Standing.elemSymm_one_mul_macHtilde_mem_span_param` --- those
two are what this reduction of the collinear side asks for. -/
theorem hasUnnormalisedMacdonaldEigenbasis_of_dop_and_eigen_param
    (hdop : ∀ μ : YoungDiagram,
      Dop (paramQ K) (paramU K) 0
          (macHtilde (paramUInvHom K) (algebraicIndependent_paramQUnit K) μ)
        = -(HJO.Sym.paramProduct (paramQ K) (paramU K) * cellSum (paramQ K) (paramU K) μ - 1) •
            macHtilde (paramUInvHom K) (algebraicIndependent_paramQUnit K) μ)
    (hinv : ∀ μ : YoungDiagram,
      macOpCompInv (paramQUInvHom K) (paramQUnit K) (paramU K) μ.card
          (macPpoly (algebraicIndependent_paramQUnit K) (baseIdx μ))
        = paramQUInvHom K (macdonaldEigenvalue (paramQ K) (paramU K)
              (Fintype.card (baseAlphabet μ)) (partDiagram (baseAlphabet μ) (baseIdx μ)))
            • macPpoly (algebraicIndependent_paramQUnit K) (baseIdx μ)) :
    HasUnnormalisedMacdonaldEigenbasis (paramQUInvHom K) (paramQ K) (paramU K) :=
  hasUnnormalisedMacdonaldEigenbasis_macHtilde_dop_param K hdop
    (coeffSubst_macPfun_param_of_eigen K hinv)

end HJO.Standing
