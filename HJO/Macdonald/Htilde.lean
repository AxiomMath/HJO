/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.Collinear.HAlphabet
public import HJO.Macdonald.EigenbasisNormalisation
public import HJO.Macdonald.PpolyBasis
public import HJO.Macdonald.RestrictBasis
public import HJO.Macdonald.StandingFacts
public meta import HJO.Attr

/-! # Macdonald's symmetric function, its integral form and the modified Macdonald family

The construction chain `HJO.Sym.macPfun → HJO.Sym.macJfun → HJO.Sym.macHtilde`, and what it delivers
towards the two residual hypotheses of the collinear goal.

`HJO/Macdonald/Ppoly.lean` builds Macdonald's polynomial `P_μ[X_n]` inside the symmetric
polynomials in a finite alphabet, and `HJO/Macdonald/RestrictBasis.lean` proves that the
restriction `res_n` carries the graded piece `Λ_d` **bijectively** onto `𝒮_{n,d}` once `d ≤ n`. That
bijection is what makes `P_μ ∈ Λ_{|μ|}` a definition rather than an assumption: `P_μ[X_{n_μ}]` lies
in the target, so it has exactly one preimage. This file takes that step and the two that follow it.

## Main definitions

* `HJO.Mac.baseAlphabet`: the alphabet `X_{n_μ}` of `n_μ = max(|μ|, 1)` letters, as
  `Fin (max μ.card 1)`.
* `HJO.Mac.baseIdx`: the partition `μ` read as an index of the monomial symmetric basis of that
  alphabet, which is what `exists_partDiagram_eq` supplies.
* `HJO.Sym.macPfun`: Macdonald's symmetric function `P_μ ∈ Λ_{|μ|}`.
* `HJO.Sym.macJfun`: Macdonald's integral form `J_μ = γ_μ P_μ`.
* `HJO.Sym.coeffSubst` (`HJO.Sym.coeffSubst`): the ring endomorphism of `Λ` applying
  a ring endomorphism of the coefficients to each coefficient and fixing every `p_k`. The
  substitution `ς` is this at `ι` and `ȷ` is this at `υ`; the two are one construction.
* `HJO.Sym.plethDivide`: the plethystic division `𝒴`,
  `p_k ↦ (1-u^{-k})^{-1} p_k`.
* `HJO.Sym.rowOffsetSum`: `n(μ) = ∑_i (i-1) μ_i`.
* `HJO.Sym.macHtilde`: `H̃_μ = u^{n(μ)} 𝒴(ȷ(J_μ))`.

## Main results

* `HJO.Sym.inversion_plethDivide_coeffSubst`: **the whole of
  `HJO.Standing.inversion_macHtilde_param` except its last paragraph.** For `F ∈ Λ_d` fixed by `ς`,
  `↓ 𝒴(ȷ F) = (-u^{-1})^d 𝒴(ȷ F)` --- an honest equation, with the scalar named, and uniform in the
  power-sum index.
* `HJO.Sym.exists_inversion_smul_macHtilde`: clause `(c)` of `IsUnnormalisedMacdonaldEigenbasis` for
  `H̃`, from `HJO.Sym.coeffSubst_macPfun` alone.
* `HJO.Sym.macHtilde_ne_zero`: clause `(a)`'s first half for `H̃`.
* `HJO.Sym.hasUnnormalisedMacdonaldEigenbasis_macHtilde`, and its standing-field form
  `HJO.Standing.hasUnnormalisedMacdonaldEigenbasis_macHtilde_param`: the first residual hypothesis
  of the collinear goal reduced to **two** statements about `H̃` --- that it spans `Λ`
  (`HJO.Standing.exists_basis_macHtilde`) and that `D_0` scales it by `-(M B_μ - 1)`
  (`HJO.Standing.dop_zero_smul_macHtilde_param`) --- together with `HJO.Sym.coeffSubst_macPfun`.

## Stopping a paragraph early, and what that saves

`HJO.Standing.inversion_macHtilde_param` asserts `↓H̃_μ = T_μ^{-1} H̃_μ`, and its proof spends
`HJO.Sym.cellProd_eq_pow_sum_cellArm_mul_pow_sum_cellLeg`, `HJO.Sym.sum_cellLeg` and
`HJO.Sym.sum_cellArm` --- hence also `HJO.Sym.cellArm` and `HJO.Sym.cellLeg` --- in its final
"remaining identity" paragraph and nowhere else. Everything before that paragraph establishes
`∃ c, ↓H̃_μ = c H̃_μ`, and `HJO.Sym.IsUnnormalisedMacdonaldEigenbasis` asks only for that.
`exists_inversion_smul_macHtilde` is that statement, so the five arm-and-leg lemmas are not on this
route.

The saving is larger than the standard proof suggests, because the paragraphs that *are* needed
collapse. One route expands `P_μ` in the power-sum basis, applies `↓` monomial by monomial and
compares coefficients; here the same fact is a composition of five ring homomorphisms of `Λ`, and
the comparison of coefficients never happens:

* `↓` **is** `ς` after the sign substitution: `inversion ι = coeffSubst ι ∘ diagScale ((-1)^i)`
  (`inversion_eq_coeffSubst_diagScale`), both sides being ring endomorphisms with the same values on
  the coefficients and on the `p_k`.
* `coeffSubst` and `diagScale` commute up to relabelling the scalars
  (`coeffSubst_diagScale`), and two diagonal substitutions compose into one
  (`diagScale_diagScale`). So the composite `↓ ∘ 𝒴 ∘ ȷ` is a single diagonal substitution applied
  to `ȷ F`, with scalars `ι((-1)^i (1-u^{-i-1})^{-1})`.
* Those scalars are `(-u^{-1})^{i+1}` times the scalars of `𝒴`
  (`paramInv_plethDivide_scalar`), the one-line computation `1 - u^k = -u^k(1 - u^{-k})`.
* A diagonal substitution rescaled by `t^{i+1}` acts on `Λ_d` as the single scalar `t^d`
  (`HJO.Sym.diagScale_pow_smul_of_mem_lambdaComp`, already proved). This is the
  observation that `(-1)^{d-ℓ(λ)} ι(Y_λ) = (-1)^d u^{-d} Y_λ` **uniformly in `λ`**, and it is where
  the uniformity actually comes from: the exponent `ℓ(λ)` cancels because each part contributes one
  factor `-u^{-λ_j}` and the `λ_j` sum to `d`.

So the paragraph "the coefficients are fixed by `ι`" of that proof is the hypothesis
`coeffSubst ι F = F` (`HJO.Sym.coeffSubst_macPfun`), and the three paragraphs after it are the four
bullets above. Nothing is expanded in a basis.

## Where genericity is spent, and the two degenerate corners that bite

`AlgebraicIndependent ℤ ![(q : K), u]` is carried throughout because `macPpoly` is a function of it:
`HJO.Mac.existsUnique_isMonicEigen` is **false** at `q = u = -1` and has no solution on `qu = 1`. It
is spent again, through `HJO.Sym.normalisingProduct_ne_zero` and `HJO.Standing.u_pow_succ_ne_one`,
in `macHtilde_ne_zero`.

Two corners deserve attention, and both bite:

* **`u = 0`.** `inversion_plethDivide_coeffSubst` is *false* there, and the failure is in its core
  identity `(1-u^k)^{-1} = -u^{-k}(1-u^{-k})^{-1}`: at `u = 0` and `k ≥ 1` the left side is `1` and
  the right side is `0`. So `hu0 : u ≠ 0` is a hypothesis of that lemma and is not decoration. It is
  *not* needed for `u^k = 1`: there both sides are `0`, and the lemma holds at every root of unity.
* **`u` a root of unity.** `plethDivide` is then not injective --- its scalar at `p_k` is
  `(1-u^{-k})^{-1} = 0` --- so `H̃_μ` can vanish and clause `(a)` fails while the inversion clause
  still holds. `macHtilde_ne_zero` therefore carries `hu1 : ∀ k, u ^ (k+1) ≠ 1`, which at the
  standing field is `HJO.Standing.paramU_pow_succ_ne_one`. This is the same failure that
  `HJO.Standing.elemSymm_one_mul_macHtilde_mem_span_param` has at `u = 1`, one step earlier in the
  chain: at `u = 1` already `γ_{(1)} = 1 - u = 0`.

Nothing here needs `q ≠ 0`, `M ≠ 0`, or `qu ≠ 1` beyond what `hqu` gives.

## What is not here

`HJO.Standing.dop_zero_smul_macHtilde_param` (clause `(b)`) and
`HJO.Standing.exists_basis_macHtilde` (clause `(a)`'s second half) are **not proved here** (they
are proved later, in `HJO/Macdonald/EopJfun.lean` and `HJO/Macdonald/HtildeBasis.lean`), and they
are the two hypotheses of `hasUnnormalisedMacdonaldEigenbasis_macHtilde`. Clause `(b)` needs the
whole of Garsia--Haiman--Tesler's Section 4 --- `HJO.Sym.dop_zero_macSubst`,
`HJO.Sym.isEopEigenJfun`, `HJO.Sym.paramUInv_dopZeroEigenvalue`,
`HJO.Sym.one_sub_mul_sum_pow_mul_pow_rowLen` --- none of which is available at this point (they
are proved in `HJO/Macdonald/DopZeroHtilde.lean` and `HJO/Macdonald/EopJfun.lean`). Clause `(a)`
needs `HJO.Sym.exists_basis_macPfun`, and that needs `HJO.Mac.restrictAlphabet_macPfun_partDiagram`
(`res_n(P_μ) = P_μ[X_n]` for *every* `n ≥ |μ|`, not only `n_μ`), whose proof runs through
`HJO.Sym.killCompl_restrictAlphabet`, `HJO.Mac.killComplComp_macPpoly` and
`MvPolynomial.killComplComp_bijective`. Stating them as hypotheses here is what makes the reduction
checkable: the theorem below is the statement that nothing else is missing.

`HJO.Standing.elemSymm_one_mul_macHtilde_mem_span_param`, the second residual hypothesis, is
not addressed here; it is false at `u = 1`.

## References

I. G. Macdonald, *Symmetric functions and Hall polynomials*, Chapter VI, equations
(4.15), (8.1) and (8.3), and A. M. Garsia, M. Haiman and G. Tesler, *Explicit plethystic formulas
for Macdonald (q,t)-Kostka coefficients*, Sém. Lothar. Combin. **42** (1999), B42m, equation (I.7).
The sources'
`t` is written `u` here.
-/

@[expose] public section

open Finset MvPolynomial

/-! ### Every partition of `d` is an index of the monomial symmetric basis

`HJO.Mac.partDiagram` reads an index `ν` of the monomial symmetric basis of `𝒮_{n,d}` as a Young
diagram, and `HJO.Mac.partDiagram_injective` says it does so faithfully. The construction of `P_μ`
needs the other direction: a diagram with `d` cells that the alphabet does not truncate is
`partDiagram σ ν` for some `ν`. That is proved here, by reading the row lengths of the diagram off
the increasing listing of the alphabet.
-/

namespace HJO.Mac

/-- **A diagram with `d` cells has no row at index `d` or beyond.** If the `k`-th row were nonempty
then so would every earlier row be, the row lengths being weakly decreasing, so the `k+1` cells
`(0,0), …, (k,0)` would all belong to the diagram. -/
theorem rowLen_eq_zero_of_card_le {D : YoungDiagram} {k : ℕ} (h : D.card ≤ k) : D.rowLen k = 0 := by
  classical
  by_contra hne
  have hpos : 0 < D.rowLen k := Nat.pos_of_ne_zero hne
  have hsub : (Finset.range (k + 1)).image (fun i => (i, 0)) ⊆ D.cells := by
    intro c hc
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hc
    exact (YoungDiagram.mem_cells _).mpr (YoungDiagram.mem_iff_lt_rowLen.mpr
      (hpos.trans_le (D.rowLen_anti i k (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)))))
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_image_of_injective _ fun _ _ hab => ((Prod.mk_inj).mp hab).1,
    Finset.card_range] at hcard
  have hDcard : D.card = D.cells.card := rfl
  omega

/-- **The number of cells is the sum of the row lengths below the alphabet.** Sorting the cells by
their row index splits the diagram into its rows, each contributing its length; the hypothesis says
no row at index `n` or beyond contributes. -/
theorem card_eq_sum_rowLen (D : YoungDiagram) {n : ℕ} (hn : D.rowLen n = 0) :
    D.card = ∑ k ∈ Finset.range n, D.rowLen k := by
  classical
  have hsupp : ∀ c ∈ D.cells, c.1 ∈ Finset.range n := by
    intro c hc
    refine Finset.mem_range.mpr (lt_of_not_ge fun hle => ?_)
    have h1 := YoungDiagram.mem_iff_lt_rowLen.mp ((YoungDiagram.mem_cells _).mp hc)
    have h2 : D.rowLen c.1 ≤ D.rowLen n := D.rowLen_anti n c.1 hle
    omega
  rw [YoungDiagram.card, Finset.card_eq_sum_card_fiberwise hsupp]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [YoungDiagram.rowLen_eq_card]
  rfl

variable {σ : Type*} [Fintype σ] [LinearOrder σ]

/-- **Every diagram the alphabet does not truncate is the diagram of an index.** For a diagram `D`
with `D.rowLen #σ = 0` there is an index `ν` of the monomial symmetric basis of `𝒮_{#σ, |D|}` with
`partDiagram σ ν = D`.

The exponent vector is read off the increasing listing of the alphabet: the letter in position `k`
carries the exponent `D.rowLen k`. It is weakly decreasing because `HJO.Mac.letterEquiv` is an order
isomorphism and the row lengths are weakly decreasing, and its total degree is `|D|` by
`card_eq_sum_rowLen`, so it is the multiplicity vector of a multiset of `|D|` letters
(`MvPolynomial.degree_eq_iff_exists_sym`); `HJO.Mac.eq_partExp` then identifies it with `\bar ν` for
the multiplicity partition `ν` of that multiset.

**This is what makes `HJO.Sym.macPfun` well defined**, together with
`HJO.Sym.restrictAlphabetComp_bijective`: without it `P_μ[X_n]` is not available at an index given
as a Young diagram, which is how the modified Macdonald family is indexed. -/
theorem exists_partDiagram_eq {D : YoungDiagram} (hD : D.rowLen (Fintype.card σ) = 0) :
    ∃ ν : PartIdx σ D.card, partDiagram σ ν = D := by
  classical
  set α : σ →₀ ℕ := Finsupp.equivFunOnFinite.symm
    (fun i => D.rowLen ((letterEquiv σ).symm i : ℕ)) with hαdef
  have hα : ∀ i : σ, α i = D.rowLen ((letterEquiv σ).symm i : ℕ) := by
    intro i; rw [hαdef]; rfl
  have hanti : Antitone α := by
    intro i j hij
    rw [hα, hα]
    exact D.rowLen_anti _ _ (Fin.le_def.mp ((letterEquiv σ).symm.monotone hij))
  have hdeg : α.degree = D.card := by
    have hsum : α.degree = ∑ i : σ, α i := by
      rw [Finsupp.degree_apply]
      exact Finset.sum_subset (Finset.subset_univ _)
        fun i _ hi => Finsupp.notMem_support_iff.mp hi
    rw [hsum, card_eq_sum_rowLen D hD, ← Fin.sum_univ_eq_sum_range]
    exact Fintype.sum_equiv (letterEquiv σ).symm.toEquiv _ _ fun i => hα i
  obtain ⟨a, ha⟩ := MvPolynomial.degree_eq_iff_exists_sym.mp hdeg
  refine ⟨⟨Nat.Partition.ofSym a, Nat.Partition.parts_card_le a⟩, ?_⟩
  have hpe : α = partExp σ ⟨Nat.Partition.ofSym a, Nat.Partition.parts_card_le a⟩ := by
    rw [← ha]
    exact eq_partExp rfl (by rw [ha]; exact hanti)
  have hrow : ∀ k : ℕ,
      (partDiagram σ ⟨Nat.Partition.ofSym a, Nat.Partition.parts_card_le a⟩).rowLen k
        = D.rowLen k := by
    intro k
    rw [rowLen_partDiagram, ← hpe]
    rcases Nat.lt_or_ge k (Fintype.card σ) with hk | hk
    · rw [rowLenSeqOf_of_lt hk, hα]
      simp
    · rw [rowLenSeqOf_of_le hk]
      exact le_antisymm (hD ▸ D.rowLen_anti _ _ hk) (Nat.zero_le _) |>.symm
  refine YoungDiagram.ext (Finset.ext fun c => ?_)
  rw [YoungDiagram.mem_cells c, YoungDiagram.mem_cells c, YoungDiagram.mem_iff_lt_rowLen,
    YoungDiagram.mem_iff_lt_rowLen, hrow]

/-! ### The base alphabet of a partition -/

/-- **The alphabet `X_{n_μ}`**, with `n_μ` the larger of `|μ|` and `1`: the finite
alphabet in which `P_μ` is first constructed, before being transported to `Λ`. -/
abbrev baseAlphabet (μ : YoungDiagram) : Type := Fin (max μ.card 1)

/-- The base alphabet has at least `|μ|` letters, which is the hypothesis
`HJO.Sym.restrictAlphabetComp_bijective` and `HJO.Mac.exists_partDiagram_eq` need. -/
theorem card_le_card_baseAlphabet (μ : YoungDiagram) :
    μ.card ≤ Fintype.card (baseAlphabet μ) := by
  rw [Fintype.card_fin]
  exact le_max_left _ _

/-- **`μ` read as an index of the monomial symmetric basis of the base alphabet.** The base alphabet
has at least `|μ|` letters, so `μ` has no row it truncates, and `exists_partDiagram_eq` supplies the
index. -/
noncomputable def baseIdx (μ : YoungDiagram) : PartIdx (baseAlphabet μ) μ.card :=
  (exists_partDiagram_eq (σ := baseAlphabet μ)
    (rowLen_eq_zero_of_card_le (card_le_card_baseAlphabet μ))).choose

/-- `baseIdx μ` is an index for `μ` itself. -/
theorem partDiagram_baseIdx (μ : YoungDiagram) :
    partDiagram (baseAlphabet μ) (baseIdx μ) = μ :=
  (exists_partDiagram_eq (σ := baseAlphabet μ)
    (rowLen_eq_zero_of_card_le (card_le_card_baseAlphabet μ))).choose_spec

/-! ### Macdonald's polynomial in a finite alphabet is nonzero -/

variable {K : Type*} [Field K] [Algebra ℚ K] {q : Kˣ} {u : K} {d : ℕ}

/-- **`P_μ[X_n]` is not zero**: it is a member of a basis of `𝒮_{n,d}`
(`HJO.Mac.exists_basis_macPpoly`). -/
theorem macPpoly_ne_zero (hqu : AlgebraicIndependent ℤ ![(q : K), u]) (ν : PartIdx σ d) :
    macPpoly hqu ν ≠ 0 := by
  obtain ⟨B, hB⟩ := exists_basis_macPpoly (σ := σ) (K := K) (q := q) (u := u) hqu
  have h := B.ne_zero ν
  rwa [hB] at h

end HJO.Mac

/-! ### Macdonald's symmetric function and its integral form -/

namespace HJO.Sym

open HJO.Mac

variable {K : Type*} [Field K] [Algebra ℚ K] {q : Kˣ} {u : K}

/-- **Macdonald's symmetric function `P_μ`**, the element of `Λ_{|μ|}` with
`res_{n_μ}(P_μ) = P_μ[X_{n_μ}]`.

It exists and is unique because `res_{n_μ}` is a bijection from `Λ_{|μ|}` onto `𝒮_{n_μ,|μ|}`
(`HJO.Sym.restrictAlphabetComp_bijective`) and
`P_μ[X_{n_μ}]` lies in the latter. The side condition `μ_{n_μ+1} = 0` is
`HJO.Mac.rowLen_eq_zero_of_card_le`: a partition with `|μ|` cells has at most `|μ|` nonzero entries.

The two theorems below state its defining property and the pinning that property gives: the
preimage under an equivalence says nothing by itself. -/
@[hjo "def_mac_pfun"]
noncomputable def macPfun (hqu : AlgebraicIndependent ℤ ![(q : K), u]) (μ : YoungDiagram) :
    Lambda K :=
  ((restrictAlphabetEquiv (baseAlphabet μ) K (card_le_card_baseAlphabet μ)).symm
    (macPpoly hqu (baseIdx μ)) : LambdaComp K μ.card)

/-- **`P_μ` lies in the graded piece `Λ_{|μ|}`**, being by construction the value of a map into it.
This is the containment `HJO.Sym.macPfun` asserts. -/
theorem macPfun_mem (hqu : AlgebraicIndependent ℤ ![(q : K), u]) (μ : YoungDiagram) :
    macPfun hqu μ ∈ LambdaComp K μ.card :=
  Submodule.coe_mem _

/-- **`P_μ` restricts to `P_μ[X_{n_μ}]`**: the defining property of `HJO.Sym.macPfun`. -/
@[hjo "def_mac_pfun"]
theorem restrictAlphabet_macPfun (hqu : AlgebraicIndependent ℤ ![(q : K), u])
    (μ : YoungDiagram) :
    restrictAlphabet (baseAlphabet μ) K (macPfun hqu μ)
      = (macPpoly hqu (baseIdx μ) : MvPolynomial (baseAlphabet μ) K) := by
  rw [macPfun, ← coe_restrictAlphabetEquiv (card_le_card_baseAlphabet μ),
    LinearEquiv.apply_symm_apply]

/-- **The defining property pins `P_μ`**: an element of `Λ_{|μ|}` restricting to `P_μ[X_{n_μ}]` is
`P_μ`. This is the uniqueness half of `HJO.Sym.macPfun`, and it is how a consumer identifies an
element it has built with Macdonald's. -/
@[hjo "def_mac_pfun"]
theorem eq_macPfun (hqu : AlgebraicIndependent ℤ ![(q : K), u]) {μ : YoungDiagram}
    {f : Lambda K} (hf : f ∈ LambdaComp K μ.card)
    (hres : restrictAlphabet (baseAlphabet μ) K f
      = (macPpoly hqu (baseIdx μ) : MvPolynomial (baseAlphabet μ) K)) :
    f = macPfun hqu μ := by
  have h : restrictAlphabetEquiv (baseAlphabet μ) K (card_le_card_baseAlphabet μ) ⟨f, hf⟩
      = macPpoly hqu (baseIdx μ) :=
    Subtype.ext (by rw [coe_restrictAlphabetEquiv]; exact hres)
  rw [macPfun, ← h, LinearEquiv.symm_apply_apply]

/-- **`P_μ` is not zero**: its restriction `P_μ[X_{n_μ}]` is not
(`HJO.Mac.macPpoly_ne_zero`). -/
theorem macPfun_ne_zero (hqu : AlgebraicIndependent ℤ ![(q : K), u]) (μ : YoungDiagram) :
    macPfun hqu μ ≠ 0 := by
  intro h
  refine macPpoly_ne_zero hqu (baseIdx μ) (Subtype.ext ?_)
  rw [← restrictAlphabet_macPfun hqu μ, h, map_zero]
  rfl

/-- **Macdonald's integral form `J_μ = γ_μ P_μ`**, Macdonald's Chapter VI, equation (8.3). This is a
definition and not a quotation: `γ_μ` is the explicit product `HJO.Sym.normalisingProduct` and `P_μ`
is `HJO.Sym.macPfun`, both constructed. -/
@[hjo "def_mac_jfun"]
noncomputable def macJfun (hqu : AlgebraicIndependent ℤ ![(q : K), u]) (μ : YoungDiagram) :
    Lambda K :=
  normalisingProduct (q : K) u μ • macPfun hqu μ

/-- **`J_μ` lies in the graded piece `Λ_{|μ|}`**, being a scalar multiple of `P_μ`. -/
theorem macJfun_mem (hqu : AlgebraicIndependent ℤ ![(q : K), u]) (μ : YoungDiagram) :
    macJfun hqu μ ∈ LambdaComp K μ.card :=
  Submodule.smul_mem _ _ (macPfun_mem hqu μ)

/-- **`J_μ` is not zero**: `γ_μ ≠ 0` at generic parameters
(`HJO.Sym.normalisingProduct_ne_zero`) and `P_μ ≠ 0`. This is
the load-bearing nonvanishing of the chain: at `u = 1` every factor of `γ_μ` vanishes for a nonempty
`μ`, and then `J_μ = 0`. -/
theorem macJfun_ne_zero (hqu : AlgebraicIndependent ℤ ![(q : K), u]) (μ : YoungDiagram) :
    macJfun hqu μ ≠ 0 :=
  smul_ne_zero (normalisingProduct_ne_zero hqu μ) (macPfun_ne_zero hqu μ)

/-! ### The two substitutions of the modified Macdonald family -/

/-- **The substitution of the coefficients**: the ring endomorphism of `Λ` whose restriction to the
coefficients is `φ` and which fixes `p_k` for every `k ≥ 1`. It is `MvPolynomial.map`, `Λ` being a
polynomial ring over the coefficients on the `p_k`, so prescribing the values there determines
exactly one such endomorphism.

This construction appears twice: `ς` (`HJO.Sym.coeffSubst`, written `F[X;1/q,1/u]`) is
it at the inversion `ι` of both parameters and `ȷ` (`HJO.Sym.coeffSubst`, written `F[X;q,1/u]`) is
it at the inversion `υ` of the second alone. They are one definition at two arguments, so they are
one declaration here; nothing distinguishes them but the endomorphism supplied.

It is not `𝕜`-linear: `coeffSubst φ (c • F) = φ(c) • coeffSubst φ F`, which is
`coeffSubst_smul`. -/
@[hjo "def_mac_param_sub", hjo "def_mac_uinv"]
noncomputable def coeffSubst {K : Type*} [CommRing K] (φ : K →+* K) : Lambda K →+* Lambda K :=
  MvPolynomial.map φ

section CoeffSubst

variable {L : Type*} [CommRing L]

@[simp]
theorem coeffSubst_C (φ : L →+* L) (c : L) :
    coeffSubst φ (MvPolynomial.C c) = MvPolynomial.C (φ c) :=
  MvPolynomial.map_C φ c

@[simp]
theorem coeffSubst_X (φ : L →+* L) (i : ℕ) : coeffSubst φ (MvPolynomial.X i) = MvPolynomial.X i :=
  MvPolynomial.map_X φ i

/-- `ς` fixes every power sum: the second defining clause. -/
@[simp]
theorem coeffSubst_powerSum (φ : L →+* L) (k : ℕ) :
    coeffSubst φ (powerSum L k) = powerSum L k :=
  MvPolynomial.map_X φ _

/-- The substitution of the coefficients twists the scalars rather than fixing them. -/
theorem coeffSubst_smul (φ : L →+* L) (c : L) (f : Lambda L) :
    coeffSubst φ (c • f) = φ c • coeffSubst φ f := by
  rw [MvPolynomial.smul_eq_C_mul, MvPolynomial.smul_eq_C_mul, map_mul, coeffSubst_C]

/-- **The substitution of the coefficients respects the grading**: applying `φ` to each coefficient
cannot create a monomial, so the support does not grow. -/
theorem coeffSubst_mem_lambdaComp (φ : L →+* L) {d : ℕ} {f : Lambda L}
    (hf : f ∈ LambdaComp L d) : coeffSubst φ f ∈ LambdaComp L d := by
  rw [mem_lambdaComp] at hf ⊢
  intro e he
  exact hf fun hc => he (by rw [coeffSubst, MvPolynomial.coeff_map, hc, map_zero])

/-- **The composite of two substitutions of the coefficients** is the substitution at the composite
endomorphism. -/
theorem coeffSubst_coeffSubst (φ ψ : L →+* L) (f : Lambda L) :
    coeffSubst φ (coeffSubst ψ f) = coeffSubst (φ.comp ψ) f :=
  MvPolynomial.map_map ψ φ f

end CoeffSubst

/-- **The plethystic division by the second parameter**, `𝒴`, written
`F[X/(1-1/u)]`: the `𝕜`-algebra endomorphism of `Λ` sending `p_k` to `(1 - u^{-k})^{-1} p_k`.

At a root of unity some scalar vanishes and `𝒴` is not injective; that is the corner at which the
nonvanishing clause of a Macdonald eigenbasis fails, and it is why `macHtilde_ne_zero` carries
`∀ k, u^{k+1} ≠ 1`. -/
@[hjo "def_mac_pleth_div"]
noncomputable def plethDivide (u : K) : Lambda K →ₐ[K] Lambda K :=
  diagScale fun i => (1 - u⁻¹ ^ (i + 1))⁻¹

omit [Algebra ℚ K] in
/-- The plethystic division on a generator: the defining clause, read through the
index shift `p_k = X_{k-1}`. The hypothesis `k ≥ 1` is part of the definition, and it is not
removable: `HJO.Sym.powerSum` reads the index through `k - 1`, so `p_0` is the generator `p_1` and
the scalar at it is the one for `k = 1`, not for `k = 0`. -/
theorem plethDivide_powerSum (u : K) {k : ℕ} (hk : 1 ≤ k) :
    plethDivide u (powerSum K k) = MvPolynomial.C ((1 - u⁻¹ ^ k)⁻¹) * powerSum K k := by
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
  rw [plethDivide, diagScale_powerSum, Nat.add_sub_cancel]

/-- **The row offset sum `n(μ) = ∑_i (i-1) μ_i`**, a finite sum: the row lengths vanish from index
`|μ|` on (`HJO.Mac.rowLen_eq_zero_of_card_le`), so the sum over the first `|μ|` rows is the whole of
it. Rows are numbered from `0` here, so the `(i-1)` of the formula is the row index. -/
@[hjo "def_mac_nmu"]
def rowOffsetSum (μ : YoungDiagram) : ℕ := ∑ i ∈ Finset.range μ.card, i * μ.rowLen i

/-- **The modified Macdonald polynomial `H̃_μ = u^{n(μ)} J_μ[X/(1-1/u); q, 1/u]`**,
Garsia--Haiman--Tesler's equation (I.7), read from the inside out: `ȷ = coeffSubst υ` performs the
substitution `u ↦ 1/u` on the coefficients and `𝒴 = plethDivide u` the plethystic substitution of
the alphabet `X/(1-1/u)`, in that order. The order matters, the scalars of `𝒴` involving `u`.

The inversion `υ` of the second parameter is a parameter here rather than the specific automorphism
of `ℚ(q,u)`, exactly as the coefficient inversion `ι` is in
`HJO/Macdonald/EigenbasisFamily.lean`; `HJO.Sym.paramUInv` instantiates it. -/
@[hjo "def_mac_htilde"]
noncomputable def macHtilde (υ : K →+* K) (hqu : AlgebraicIndependent ℤ ![(q : K), u])
    (μ : YoungDiagram) : Lambda K :=
  u ^ rowOffsetSum μ • plethDivide u (coeffSubst υ (macJfun hqu μ))

/-- **`H̃_μ` is `P_μ` scaled by one coefficient.** Both `ȷ` and `𝒴` carry a scalar multiple to a
scalar multiple --- the first twisting the scalar by `υ`, the second fixing it, being `𝕜`-linear ---
so `H̃_μ` is `u^{n(μ)} υ(γ_μ)` times `𝒴(ȷ(P_μ))`. This is the shape the inversion clause is read in:
everything that depends on `μ` beyond `|μ|` sits in that one scalar. -/
theorem macHtilde_eq_smul (υ : K →+* K) (hqu : AlgebraicIndependent ℤ ![(q : K), u])
    (μ : YoungDiagram) :
    macHtilde υ hqu μ
      = (u ^ rowOffsetSum μ * υ (normalisingProduct (q : K) u μ))
          • plethDivide u (coeffSubst υ (macPfun hqu μ)) := by
  rw [macHtilde, macJfun, coeffSubst_smul, map_smul, smul_smul]

/-! ### The inversion clause, one paragraph early -/

section Inversion

variable {L : Type*} [CommRing L]

/-- **`↓` is the substitution of the coefficients after the sign substitution.** Both sides are ring
endomorphisms of `Λ` sending a coefficient `c` to `ι(c)` and the generator `p_{i+1}` to
`(-1)^i p_{i+1}`, and `Λ` is a polynomial ring over the coefficients on the generators. -/
theorem inversion_eq_coeffSubst_diagScale (ι : L →+* L) (f : Lambda L) :
    inversion ι f = coeffSubst ι (diagScale (fun i => (-1 : L) ^ i) f) := by
  have h : (inversion ι : Lambda L →+* Lambda L)
      = (coeffSubst ι).comp (diagScale (fun i => (-1 : L) ^ i)).toRingHom := by
    refine MvPolynomial.ringHom_ext (fun c => ?_) (fun i => ?_)
    · rw [inversion_C, RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
        diagScale_C, coeffSubst_C]
    · have hC : (MvPolynomial.C ((-1 : L) ^ i) : Lambda L) = (-1 : Lambda L) ^ i := by
        rw [map_pow, map_neg, map_one]
      rw [inversion_X, RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
        diagScale_X, map_mul, coeffSubst_C, coeffSubst_X, map_pow, map_neg, map_one, hC]
  exact RingHom.congr_fun h f

/-- **The substitution of the coefficients commutes with a diagonal substitution**, up to applying
it to the scalars. Both sides are ring endomorphisms; on a coefficient `c` both give `φ(c)` and on
`p_{i+1}` both give `φ(c_i) p_{i+1}`. -/
theorem coeffSubst_diagScale (φ : L →+* L) (c : ℕ → L) (f : Lambda L) :
    coeffSubst φ (diagScale c f) = diagScale (fun i => φ (c i)) (coeffSubst φ f) := by
  have h : (coeffSubst φ).comp (diagScale c).toRingHom
      = (diagScale (fun i => φ (c i))).toRingHom.comp (coeffSubst φ) := by
    refine MvPolynomial.ringHom_ext (fun a => ?_) (fun i => ?_)
    · simp
    · simp [diagScale_X]
  exact RingHom.congr_fun h f

/-- **Two diagonal substitutions compose into one**, with the scalars multiplied. -/
theorem diagScale_diagScale (c c' : ℕ → L) (f : Lambda L) :
    diagScale c (diagScale c' f) = diagScale (fun i => c i * c' i) f := by
  have h : (diagScale c).comp (diagScale c') = diagScale (fun i => c i * c' i) := by
    refine MvPolynomial.algHom_ext fun i => ?_
    rw [AlgHom.comp_apply, diagScale_X, map_mul, diagScale_C, diagScale_X, diagScale_X,
      ← mul_assoc, ← MvPolynomial.C_mul, mul_comm (c' i) (c i)]
  exact AlgHom.congr_fun h f

end Inversion

omit [Algebra ℚ K] in
/-- **The core identity of `HJO.Standing.inversion_macHtilde_param`**: `1 - u^k = -u^k(1 - u^{-k})`,
read as an identity between the two inverses. It holds at every root of unity, where both sides are
`0`, and it is **false at `u = 0`**, where the left side is `1` and the right side is `0` for
`k ≥ 1`; this is the one place `u ≠ 0` is spent in the inversion clause. -/
theorem inv_one_sub_pow_eq (hu0 : u ≠ 0) (k : ℕ) :
    (1 - u ^ k)⁻¹ = -u⁻¹ ^ k * (1 - u⁻¹ ^ k)⁻¹ := by
  have hk : u⁻¹ ^ k = (u ^ k)⁻¹ := inv_pow u k
  have hx : u ^ k ≠ 0 := pow_ne_zero k hu0
  by_cases h : u ^ k = 1
  · rw [hk, h, inv_one]
    simp
  · have h2 : (1 : K) - (u ^ k)⁻¹ ≠ 0 :=
      sub_ne_zero.mpr fun hc => h (by rw [← inv_inv (u ^ k), ← hc, inv_one])
    rw [hk]
    refine inv_eq_of_mul_eq_one_right ?_
    have hstep : (1 - u ^ k) * -(u ^ k)⁻¹ = 1 - (u ^ k)⁻¹ := by
      field_simp
      ring
    rw [← mul_assoc, hstep, mul_inv_cancel₀ h2]

omit [Algebra ℚ K] in
/-- **The scalars of `↓ ∘ 𝒴` against those of `𝒴`.** The scalar `ι((-1)^i (1-u^{-i-1})^{-1})` that
`↓ ∘ 𝒴` attaches to `p_{i+1}` is `(-u^{-1})^{i+1}` times the scalar `(1-u^{-i-1})^{-1}` of `𝒴`.

The whole of the fourth paragraph of the standard proof of
`HJO.Standing.inversion_macHtilde_param` is here, and this is where the uniformity in the
power-sum index comes from: the rescaling factor is a power of a *single* scalar, one factor per
unit of weight, so `HJO.Sym.diagScale_pow_smul_of_mem_lambdaComp` turns it into `(-u^{-1})^{|μ|}` on
the whole graded piece. -/
theorem paramInv_plethDivide_scalar {ι : K →+* K} (hu0 : u ≠ 0) (hιu : ι u⁻¹ = u) (i : ℕ) :
    ι ((-1 : K) ^ i * (1 - u⁻¹ ^ (i + 1))⁻¹)
      = (-u⁻¹) ^ (i + 1) * (1 - u⁻¹ ^ (i + 1))⁻¹ := by
  have h1 : ι ((1 - u⁻¹ ^ (i + 1))⁻¹) = (1 - u ^ (i + 1))⁻¹ := by
    rw [map_inv₀, map_sub, map_one, map_pow, hιu]
  have h2 : ((-u⁻¹ : K)) ^ (i + 1) = (-1 : K) ^ i * -u⁻¹ ^ (i + 1) := by
    rw [neg_pow, neg_pow, pow_succ]
    ring
  rw [map_mul, map_pow, map_neg, map_one, h1, inv_one_sub_pow_eq hu0 (i + 1), h2, mul_assoc]

omit [Algebra ℚ K] in
/-- **The inversion clause, with the scalar named and no arm-and-leg identity.** For `F` in the
graded piece `Λ_d` whose coefficients are fixed by `ι` --- which for `F = P_μ` is
`HJO.Sym.coeffSubst_macPfun` --- the inversion `↓` scales `𝒴(ȷ(F))` by `(-u^{-1})^d`.

This is `HJO.Standing.inversion_macHtilde_param` stopped one paragraph early, and it is *stronger*
than the `∃ c` that `HJO.Sym.IsUnnormalisedMacdonaldEigenbasis` asks for: the scalar is named, and
it depends on nothing but `d`. Four steps, each a ring-homomorphism identity:
`inversion_eq_coeffSubst_diagScale`, then `diagScale_diagScale` and `coeffSubst_diagScale` to make
the composite a single diagonal substitution, then `paramInv_plethDivide_scalar` to identify its
scalars, then `HJO.Sym.diagScale_pow_smul_of_mem_lambdaComp` to read them off the grading. The
hypothesis `hcomm` is the condition "the composites `ι ∘ υ` and `υ ∘ ι` agree", and it is what
lets `coeffSubst ι` be pushed past `coeffSubst υ` onto `F`, where it is the identity. -/
theorem inversion_plethDivide_coeffSubst {ι υ : K →+* K} (hu0 : u ≠ 0) (hιu : ι u⁻¹ = u)
    (hcomm : ∀ c : K, ι (υ c) = υ (ι c)) {d : ℕ} {F : Lambda K} (hF : F ∈ LambdaComp K d)
    (hFι : coeffSubst ι F = F) :
    inversion ι (plethDivide u (coeffSubst υ F))
      = (-u⁻¹) ^ d • plethDivide u (coeffSubst υ F) := by
  have hfix : coeffSubst ι (coeffSubst υ F) = coeffSubst υ F := by
    rw [coeffSubst_coeffSubst, show ι.comp υ = υ.comp ι from RingHom.ext hcomm,
      ← coeffSubst_coeffSubst, hFι]
  have hmem : coeffSubst υ F ∈ LambdaComp K d := coeffSubst_mem_lambdaComp υ hF
  have hscal : (fun i => ι ((-1 : K) ^ i * (1 - u⁻¹ ^ (i + 1))⁻¹))
      = fun i => (-u⁻¹ : K) ^ (i + 1) * (1 - u⁻¹ ^ (i + 1))⁻¹ :=
    funext fun i => paramInv_plethDivide_scalar hu0 hιu i
  rw [inversion_eq_coeffSubst_diagScale, plethDivide, diagScale_diagScale, coeffSubst_diagScale,
    hfix, hscal, diagScale_pow_smul_of_mem_lambdaComp (-u⁻¹) _ hmem, MvPolynomial.smul_eq_C_mul]

/-! ### The first residual hypothesis of the collinear goal, for `H̃` -/

/-- **Clause `(c)` of `IsUnnormalisedMacdonaldEigenbasis` for `H̃`**: each `H̃_μ` is an eigenvector
of `↓`. The only input is `HJO.Sym.coeffSubst_macPfun`, `ς(P_μ) = P_μ`.

`H̃_μ` is one scalar `A` times `𝒴(ȷ(P_μ))` (`macHtilde_eq_smul`), and `↓` scales the latter by
`(-u^{-1})^{|μ|}` (`inversion_plethDivide_coeffSubst`), so the eigenvalue is
`ι(A)(-u^{-1})^{|μ|}A^{-1}`; with `A = u^{n(μ)}υ(γ_μ)` that is
`(-1)^{|μ|}u^{-|μ|-2n(μ)}ιυ(γ_μ)υ(γ_μ)^{-1}`. **No nonvanishing of `A` is needed**: at `A = 0` both
`H̃_μ` and `↓H̃_μ` are zero and `c = 0` serves, so the genericity that
`HJO.Sym.normalisingProduct_ne_zero` supplies is spent in `macHtilde_ne_zero` and not here. -/
theorem exists_inversion_smul_macHtilde {ι υ : K →+* K} (hu0 : u ≠ 0) (hιu : ι u⁻¹ = u)
    (hcomm : ∀ c : K, ι (υ c) = υ (ι c)) (hqu : AlgebraicIndependent ℤ ![(q : K), u])
    {μ : YoungDiagram} (hPι : coeffSubst ι (macPfun hqu μ) = macPfun hqu μ) :
    ∃ c : K, inversion ι (macHtilde υ hqu μ) = c • macHtilde υ hqu μ := by
  set A : K := u ^ rowOffsetSum μ * υ (normalisingProduct (q : K) u μ) with hAdef
  set G : Lambda K := plethDivide u (coeffSubst υ (macPfun hqu μ)) with hGdef
  have hH : macHtilde υ hqu μ = A • G := macHtilde_eq_smul υ hqu μ
  have hG : inversion ι G = (-u⁻¹) ^ μ.card • G :=
    inversion_plethDivide_coeffSubst hu0 hιu hcomm (macPfun_mem hqu μ) hPι
  by_cases hA : A = 0
  · exact ⟨0, by rw [hH, hA, zero_smul, map_zero, smul_zero]⟩
  · refine ⟨ι A * (-u⁻¹) ^ μ.card * A⁻¹, ?_⟩
    rw [hH, inversion_smul, hG, smul_smul, smul_smul]
    congr 1
    field_simp

omit [Algebra ℚ K] in
/-- **A diagonal substitution with no vanishing scalar does not kill anything.** The coefficient of
a monomial in the image is the matching product of the scalars times its coefficient in the argument
(`HJO.UkRegular.coeff_diagScale`), and that product is a unit. -/
theorem diagScale_ne_zero {c : ℕ → K} (hc : ∀ i, c i ≠ 0) {f : Lambda K} (hf : f ≠ 0) :
    diagScale c f ≠ 0 := by
  classical
  intro h
  obtain ⟨e, he⟩ : ∃ e, MvPolynomial.coeff e f ≠ 0 := by
    by_contra hcon
    exact hf (MvPolynomial.ext f 0 fun e => by
      rw [MvPolynomial.coeff_zero]
      simpa using not_exists.mp hcon e)
  have hco := HJO.UkRegular.coeff_diagScale c e f
  rw [h, MvPolynomial.coeff_zero] at hco
  rcases mul_eq_zero.mp hco.symm with h1 | h2
  · exact absurd h1 (Finset.prod_ne_zero_iff.mpr fun i _ => pow_ne_zero _ (hc i))
  · exact he h2

/-- **Clause `(a)`'s first half for `H̃`**: no `H̃_μ` is zero.

Three nonvanishings meet: `γ_μ ≠ 0` (`HJO.Sym.normalisingProduct_ne_zero`), which fails at `u = 1`;
`u^{n(μ)} ≠ 0`; and the injectivity of `𝒴`, which needs `1 - u^{-k} ≠ 0` for every `k ≥ 1`, that is
`hu1`, and fails at every root of unity. `υ` and `ȷ` are injective for free, a ring endomorphism of
a field being injective. -/
theorem macHtilde_ne_zero {υ : K →+* K} (hu0 : u ≠ 0) (hu1 : ∀ k : ℕ, u ^ (k + 1) ≠ 1)
    (hqu : AlgebraicIndependent ℤ ![(q : K), u]) (μ : YoungDiagram) : macHtilde υ hqu μ ≠ 0 := by
  have hY : ∀ i : ℕ, (1 - u⁻¹ ^ (i + 1))⁻¹ ≠ 0 := by
    intro i
    refine inv_ne_zero (sub_ne_zero.mpr fun hc => hu1 i ?_)
    rw [inv_pow, eq_comm, inv_eq_one] at hc
    exact hc
  have hP : coeffSubst υ (macPfun hqu μ) ≠ 0 := fun h =>
    macPfun_ne_zero hqu μ (MvPolynomial.map_injective υ υ.injective (by rw [← coeffSubst, h,
      map_zero]))
  have hA : u ^ rowOffsetSum μ * υ (normalisingProduct (q : K) u μ) ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ hu0)
      fun h => normalisingProduct_ne_zero hqu μ (υ.injective (by rw [h, map_zero]))
  rw [macHtilde_eq_smul]
  exact smul_ne_zero hA (diagScale_ne_zero hY hP)

/-- **The first residual hypothesis of the collinear goal, reduced to three statements about the
constructed family `H̃`.**

`HJO.Sym.HasUnnormalisedMacdonaldEigenbasis` is what
`HJO.Standing.exists_isMacdonaldConjugator_of_hasPieriEigenfamily_param` needs, alongside
`HJO.Sym.HasPieriEigenfamily`. Of its four clauses, two are discharged here for `H̃`: the
nonvanishing is `macHtilde_ne_zero` and the inversion clause is
`exists_inversion_smul_macHtilde`. What remains is exactly

* `hspan`, the spanning half of `HJO.Standing.exists_basis_macHtilde`;
* `hdop`, `HJO.Standing.dop_zero_smul_macHtilde_param`, Garsia--Haiman--Tesler's Theorem 1.2 (1.11)
  a);
* `hPι`, `HJO.Sym.coeffSubst_macPfun`, Macdonald's (5.13) (iv).

Each is a statement from the literature with no hypothesis beyond genericity, and none is weakened.
This is the reduction: **the collinear side of this library rests on those three, together with
`HJO.Standing.elemSymm_one_mul_macHtilde_mem_span_param`.** -/
theorem hasUnnormalisedMacdonaldEigenbasis_macHtilde {ι υ : K →+* K} (hu0 : u ≠ 0)
    (hu1 : ∀ k : ℕ, u ^ (k + 1) ≠ 1) (hιu : ι u⁻¹ = u) (hcomm : ∀ c : K, ι (υ c) = υ (ι c))
    (hqu : AlgebraicIndependent ℤ ![(q : K), u])
    (hspan : Submodule.span K (Set.range (macHtilde υ hqu)) = ⊤)
    (hdop : ∀ μ : YoungDiagram, Dop (q : K) u 0 (macHtilde υ hqu μ)
      = -(paramProduct (q : K) u * cellSum (q : K) u μ - 1) • macHtilde υ hqu μ)
    (hPι : ∀ μ : YoungDiagram, coeffSubst ι (macPfun hqu μ) = macPfun hqu μ) :
    HasUnnormalisedMacdonaldEigenbasis ι (q : K) u :=
  ⟨macHtilde υ hqu,
    { ne_zero := fun μ => macHtilde_ne_zero hu0 hu1 hqu μ
      span_eq_top := hspan
      dop_zero := hdop
      exists_inversion_smul := fun μ =>
        exists_inversion_smul_macHtilde hu0 hιu hcomm hqu (hPι μ) }⟩

end HJO.Sym

/-! ### The same reduction at the standing field

At the standing field `𝕜 = ℚ(q, u)` every hypothesis of
`HJO.Sym.hasUnnormalisedMacdonaldEigenbasis_macHtilde` that is about the parameters or about the two
inversions is a theorem: the nonvanishing facts come from
`HJO/Macdonald/StandingFacts.lean` and the two inversions are constructed in
`HJO/Macdonald/ParamInversion.lean`, where `ι` and `υ` commute because both are read off the
same presentation of `𝕜`.
-/

namespace HJO.Standing

open HJO.Ascent HJO.Sym

variable (K : Type*) [Field K] [Algebra ParamRing K] [IsFractionRing ParamRing K] [Algebra ℚ K]

/-- The dinv parameter of the standing field as a unit, which is the form `HJO.Mac.macPpoly` and
hence `HJO.Sym.macPfun` take it in. -/
noncomputable def paramQUnit : Kˣ := Units.mk0 (paramQ K) (paramQ_ne_zero K)

omit [Algebra ℚ K] in
@[simp]
theorem paramQUnit_val : (paramQUnit K : K) = paramQ K := rfl

omit [Algebra ℚ K] in
/-- The genericity of the standing parameters, in the shape `HJO.Sym.macPfun` asks for. -/
theorem algebraicIndependent_paramQUnit :
    AlgebraicIndependent ℤ ![((paramQUnit K : K)), paramU K] :=
  algebraicIndependent_param K

/-- **The two parameter inversions commute at the standing field**: both composites are ring
endomorphisms of `𝕜` sending `q` to `q^{-1}` and `u` to `u`, and `𝕜` is rigid over those two values.
This is the condition "the composites `ι ∘ υ` and `υ ∘ ι` agree", which
`HJO.Standing.inversion_macHtilde_param` uses to move `ι` past `υ` onto the coefficients of
`P_μ`. -/
theorem paramQUInvHom_paramUInvHom_comm (c : K) :
    paramQUInvHom K (paramUInvHom K c) = paramUInvHom K (paramQUInvHom K c) := by
  have h : (paramQUInvHom K).comp (paramUInvHom K) = (paramUInvHom K).comp (paramQUInvHom K) := by
    refine ringHom_ext_param ?_ ?_ <;> simp [RingHom.comp_apply, map_inv₀]
  exact RingHom.congr_fun h c

/-- **The first residual hypothesis of the collinear goal at the standing field, reduced to
three statements.**

Feeding the conclusion to
`HJO.Standing.exists_isMacdonaldConjugator_of_hasPieriEigenfamily_param` leaves
`HJO.Sym.HasPieriEigenfamily` --- `HJO.Standing.elemSymm_one_mul_macHtilde_mem_span_param` --- as
the only other hypothesis of the whole collinear side. Everything about the parameters and about the
two inversions is discharged here. -/
theorem hasUnnormalisedMacdonaldEigenbasis_macHtilde_param
    (hspan : Submodule.span K
      (Set.range (macHtilde (paramUInvHom K) (algebraicIndependent_paramQUnit K))) = ⊤)
    (hdop : ∀ μ : YoungDiagram,
      Dop (paramQ K) (paramU K) 0
          (macHtilde (paramUInvHom K) (algebraicIndependent_paramQUnit K) μ)
        = -(HJO.Sym.paramProduct (paramQ K) (paramU K) * cellSum (paramQ K) (paramU K) μ - 1) •
            macHtilde (paramUInvHom K) (algebraicIndependent_paramQUnit K) μ)
    (hPι : ∀ μ : YoungDiagram,
      coeffSubst (paramQUInvHom K) (macPfun (algebraicIndependent_paramQUnit K) μ)
        = macPfun (algebraicIndependent_paramQUnit K) μ) :
    HasUnnormalisedMacdonaldEigenbasis (paramQUInvHom K) (paramQ K) (paramU K) :=
  hasUnnormalisedMacdonaldEigenbasis_macHtilde (paramU_ne_zero K) (paramU_pow_succ_ne_one K)
    (by rw [← paramQUInvHom_paramU K, paramQUInvHom_involutive])
    (fun c => paramQUInvHom_paramUInvHom_comm K c) (algebraicIndependent_paramQUnit K) hspan hdop
    hPι

end HJO.Standing
