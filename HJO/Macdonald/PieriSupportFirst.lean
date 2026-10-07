/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.Macdonald.PfunBasis
public import HJO.Macdonald.PpolyBasis
public import HJO.Macdonald.PpolyCut
public import HJO.Macdonald.PpolyDegree
public import HJO.Macdonald.PpolyTopMain
public meta import HJO.Attr

/-! # The first row of the one-cell Pieri expansion

The two lemmas that bound and then pin the first row of an index occurring in `e₁P_ρ`:

* `HJO.Mac.rowLen_zero_le_of_coeff_ne_zero`: if `e₁P_ρ = ∑_κ c_κ P_κ` with every index of size
  `|ρ| + 1`, then a nonzero `c_λ` forces `λ_1 ≤ ρ_1 + 1`;
* `HJO.Mac.rowLen_succ_eq_of_coeff_ne_zero`: and at the extreme `λ_1 = ρ_1 + 1` the rest of `λ` is
  forced too, `λ_i = ρ_i` for every `i ≥ 2`.

They are in one file because they are one setup. Both restrict the expansion to the single alphabet
`Fin (|ρ| + 2)` — long enough for `ρ` and for every index of size `|ρ| + 1` — and read the result
off the leading-exponent calculus there; `HJO.Mac.restrictAlphabet_elemSymm_one_mul_macPfun` is that
common step, and the second lemma takes the first as an input.

## The route of `HJO.Mac.rowLen_zero_le_of_coeff_ne_zero`

Restrict everything to one alphabet long enough for every index that occurs. Take `n := |ρ| + 2`;
`HJO.Mac.restrictAlphabet_macPfun_partDiagram_of_pos` turns each `P_μ` into `P_μ[X_n]`, and
`HJO.Sym.restrictAlphabet_elemSymm` turns `e₁` into `x_1 + ⋯ + x_n`. The identity becomes one of
polynomials, and the leading-exponent calculus applies:

* `x_1 + ⋯ + x_n` has leading exponent `δ_1`, the indicator of the least letter, with
  coefficient `1` (`HJO.Mac.lex_degree_esymm_one`);
* each `P_μ[X_n]` has leading exponent `\bar\mu` with coefficient `1`
  (`HJO.Mac.coeff_partExp_macPpoly`);
* so the left-hand side is nonzero with leading exponent `\bar\rho + δ_1`
  (`MonomialOrder.mul_ne_zero_and_degree_mul`) and no exponent above it
  (`MonomialOrder.le_degree_add_degree_of_mem_support_mul`).

The right-hand side is then read at its own largest exponent. Among the `μ` with `c_μ ≠ 0` pick one
whose `\bar\mu` is lexicographically largest; every other index contributes nothing at that
exponent, so the coefficient there is that `c_μ ≠ 0`, and the exponent therefore occurs on the left.
That bounds `\bar\lambda ≤_lex \bar\rho + δ_1`, and at the least letter a lexicographic `≤` is an
entrywise `≤` (`Finsupp.apply_le_of_toLex_le`, from `HJO/Macdonald/PpolyDegree.lean`) — which
is the conclusion, `\bar\mu` at the least letter being `μ_1`.

## The route of `HJO.Mac.rowLen_succ_eq_of_coeff_ne_zero`

The same restriction, then read both sides as polynomials in the *greatest* letter `t` and take the
coefficient of `x_t^{r+1}`, `r := ρ_1`. On the left `x_1 + ⋯ + x_n` splits as
`Polynomial.X + Polynomial.C (x_1 + ⋯ + x_{n-1})` (`HJO.Mac.splitAt_esymm_one`), and `P_ρ[X_n]` has
degree at most `r` in `x_t` (`HJO.Mac.apply_le_partExp_of_mem_support_macPpoly`), so only the `X`
factor contributes and what is left is the coefficient of `x_t^r` in `P_ρ[X_n]`, which
`HJO.Mac.coeff_partExp_splitAt_macPpoly_eq` identifies with `P_{shiftRows ρ}[X_{n-1}]`. On the
right, `HJO.Mac.rowLen_zero_le_of_coeff_ne_zero` bounds each `μ_1` by `r+1`; the indices with
`μ_1 ≤ r` contribute `0` for the same degree reason, and those with `μ_1 = r+1` contribute
`c_μ P_{shiftRows μ}[X_{n-1}]`.

So `P_{shiftRows ρ}[X_{n-1}]` is a combination of the `P_{shiftRows μ}[X_{n-1}]`, and the
`P_ϖ[X_{n-1}]` of one degree are a **basis** (`HJO.Mac.exists_basis_macPpoly`). One could compare
coefficients in it; what is actually applied here is the single coordinate functional at the index
of `shiftRows λ`. It reads `c_λ` on the right — every other index of the sum has a different
`shiftRows`, `μ` being recovered from `shiftRows μ` and `μ_1 = r+1` — and on the left it reads `0`
unless `shiftRows ρ = shiftRows λ`. Since `c_λ ≠ 0`, the two shifts agree, which is the conclusion.

The one piece of bookkeeping that is not free is the *degree* of the index:
`HJO.Mac.coeff_partExp_splitAt_macPpoly_eq` delivers its `κ` at `|μ| - μ_1`, which is `|ρ| - r` for
every `μ` that contributes but is not syntactically that. `HJO.Mac.exists_coeff_splitAt_macPpoly_eq`
restates it with the degree as an argument and an equation, so a single `subst` absorbs the
arithmetic once.

## Shape of the statement

The family is indexed by *all* partitions of `|ρ| + 1`; here the index set is a
`Finset` of diagrams with the zero coefficients discarded, exactly as in
`HJO.Sym.HasPfunPieriCoeff` (`HJO/Macdonald/PfunBasis.lean`), which is the shape this lemma and
its three neighbours are stated in. The two are the same statement and this one needs no finiteness
of the set of partitions (`HJO.Sym.finite_setOf_card_eq` is thereby unused).
`HJO.Mac.rowLen_succ_eq_of_coeff_ne_zero` is stated in the same shape, and its conclusion
`λ_i = ρ_i for i ≥ 2` is `λ.rowLen (k+1) = ρ.rowLen (k+1)` for every `k`, the row lengths being
indexed from `0`.

Nothing asks the coefficients to be *the* coefficients of an expansion in a basis: any identity of
the displayed shape will do, which is what a consumer holding one has.

## Genericity

None is spent. `AlgebraicIndependent ℤ ![(q : K), u]` is carried only because `macPfun` and
`macPpoly` are functions of it, exactly as in `HJO.Sym.HasPfunPieriCoeff`; no nonvanishing in `q` or
`u` is consumed, and the degenerate corners are unreachable because that hypothesis already excludes
them (see `HJO/Macdonald/PfunBasis.lean`, "Where genericity is spent"). The statement is not
vacuous: `HJO.Sym.elemSymm_one_mul_macPfun_bot_mem_span` exhibits an expansion of the displayed
shape at `ρ = ∅`.

## Main definitions

* `HJO.Mac.idxOfDiagram`: a diagram of size at most `n` read as an index of the monomial symmetric
  basis in the alphabet `Fin n`.

## Main results

* `HJO.Mac.partExp_of_isBot`: the exponent vector of an index at the least letter is the first row
  length of its diagram — the identity `\bar\mu_1 = μ_1`.
* `HJO.Mac.lex_degree_esymm_one`, `HJO.Mac.coeff_single_esymm_one`: `x_1 + ⋯ + x_n` has leading
  exponent `δ_1` with coefficient `1`.
* `HJO.Mac.splitAt_esymm_one`: and read in one letter it is `X + C(x_1 + ⋯ + x_{n-1})`.
* `HJO.Mac.restrictAlphabet_elemSymm_one_mul_macPfun`: the expansion restricted to `Fin n`, the step
  both lemmas begin with.
* `HJO.Mac.exists_coeff_splitAt_macPpoly_eq`: `HJO.Mac.coeff_partExp_splitAt_macPpoly_eq` with the
  degree of its index as an argument.
* `HJO.Mac.rowLen_zero_le_of_coeff_ne_zero`.
* `HJO.Mac.rowLen_succ_eq_of_coeff_ne_zero`.

## References

This file proves `HJO.Mac.rowLen_zero_le_of_coeff_ne_zero` and
`HJO.Mac.rowLen_succ_eq_of_coeff_ne_zero`, from the definitions `HJO.Sym.Lambda`,
`HJO.Sym.elemSymm`, `HJO.Sym.rowLenSeq`, `HJO.Sym.cells`,
`MvPolynomial.symmetricHomogeneousSubmodule`, `HJO.Sym.restrictAlphabet`, `HJO.Mac.macPpoly` and
`HJO.Sym.macPfun` and the lemmas `Finsupp.isStrictTotalOrder_lex`,
`MonomialOrder.le_degree_add_degree_of_mem_support_mul`, `MonomialOrder.mul_ne_zero_and_degree_mul`,
`HJO.Mac.exists_basis_macPpoly`, `HJO.Sym.restrictAlphabet_elemSymm`,
`HJO.Mac.restrictAlphabet_macPfun_partDiagram`, `HJO.Mac.apply_le_partExp_of_mem_support_macPpoly`,
`HJO.Mac.coeff_partExp_splitAt_macPpoly_eq`, `HJO.Mac.coeff_partExp_macPpoly` and
`HJO.Sym.finite_setOf_card_eq`. The consumer of both is
`HJO.Ascent.elemSymm_one_mul_macPfun_mem_span_covers_or_short`.
-/

@[expose] public section

open Finset MvPolynomial MonomialOrder

namespace HJO.Sym

/-- **Two Young diagrams with the same row lengths are equal**, the injectivity half of
`HJO.Sym.equivRowLenSeq`. -/
theorem eq_of_rowLen_eq {μ ν : YoungDiagram} (h : ∀ k, μ.rowLen k = ν.rowLen k) : μ = ν :=
  equivRowLenSeq.injective (Subtype.ext (funext h))

end HJO.Sym

namespace HJO.Mac

/-! ### Reading a diagram as an index in a long enough alphabet -/

section Idx

variable {σ : Type*} [Fintype σ] [LinearOrder σ] [DecidableEq σ] {d : ℕ}

/-- **The exponent vector at the least letter is the first row length of the diagram.** This is the
identification of `\bar\mu_1` with `μ_1`: `\bar\mu` lists the row lengths along the
order of the alphabet, so its value at the least letter is the length of row `0`. -/
theorem partExp_of_isBot (ν : PartIdx σ d) {i : σ} (hi : IsBot i) :
    partExp σ ν i = (partDiagram σ ν).rowLen 0 := by
  have hpos : 0 < Fintype.card σ := Fintype.card_pos_iff.mpr ⟨i⟩
  rw [rowLen_partDiagram, rowLenSeqOf_of_lt hpos]
  congr 1
  refine le_antisymm (hi _) ?_
  obtain ⟨k, hk⟩ := (letterEquiv σ).surjective i
  rw [← hk]
  exact (letterEquiv σ).monotone (Fin.le_def.mpr (Nat.zero_le _))

/-- A diagram whose rows all fit in the alphabet `Fin n` is the diagram of an index. -/
theorem exists_partDiagram_eq_fin {n : ℕ} (μ : YoungDiagram) (h : μ.card ≤ n) :
    ∃ ν : PartIdx (Fin n) μ.card, partDiagram (Fin n) ν = μ :=
  exists_partDiagram_eq (rowLen_eq_zero_of_card_le (by rw [Fintype.card_fin]; exact h))

/-- **A diagram of size at most `n`, read as an index of the monomial symmetric basis of
`𝒮_{n,|μ|}`.** This is the passage made silently when one writes `P_κ[X_n]` for a
partition `κ`: `HJO.Mac.macPpoly` is indexed by `PartIdx`, and the index is recovered from the
diagram by `HJO.Mac.exists_partDiagram_eq`. -/
noncomputable def idxOfDiagram {n : ℕ} (μ : YoungDiagram) (h : μ.card ≤ n) :
    PartIdx (Fin n) μ.card :=
  (exists_partDiagram_eq_fin μ h).choose

@[simp]
theorem partDiagram_idxOfDiagram {n : ℕ} (μ : YoungDiagram) (h : μ.card ≤ n) :
    partDiagram (Fin n) (idxOfDiagram μ h) = μ :=
  (exists_partDiagram_eq_fin μ h).choose_spec

/-- The exponent vector of `idxOfDiagram μ h` at the least letter is `μ_1`. -/
theorem partExp_idxOfDiagram_of_isBot {n : ℕ} (μ : YoungDiagram) (h : μ.card ≤ n) {i : Fin n}
    (hi : IsBot i) : partExp (Fin n) (idxOfDiagram μ h) i = μ.rowLen 0 := by
  rw [partExp_of_isBot _ hi, partDiagram_idxOfDiagram]

/-- **Distinct diagrams have distinct exponent vectors** in an alphabet long enough for both: the
row lengths of the diagram are read off the exponent vector. -/
theorem eq_of_partExp_idxOfDiagram_eq {n : ℕ} {μ ν : YoungDiagram} (hμ : μ.card ≤ n)
    (hν : ν.card ≤ n)
    (h : partExp (Fin n) (idxOfDiagram μ hμ) = partExp (Fin n) (idxOfDiagram ν hν)) : μ = ν := by
  refine HJO.Sym.eq_of_rowLen_eq fun k => ?_
  rw [← partDiagram_idxOfDiagram μ hμ, ← partDiagram_idxOfDiagram ν hν, rowLen_partDiagram,
    rowLen_partDiagram, h]

end Idx

/-! ### The leading exponent of the first power sum in a finite alphabet -/

section Esymm

variable {σ : Type*} [Fintype σ] [LinearOrder σ] {K : Type*} [Field K]

/-- The coefficient of `x_i` in `x_1 + ⋯ + x_n` is `1`. -/
theorem coeff_single_esymm_one (i : σ) :
    coeff (Finsupp.single i 1) (esymm σ K 1) = 1 := by
  classical
  rw [esymm_one, coeff_sum, Finset.sum_eq_single_of_mem i (mem_univ i)
    (fun j _ hj => by
      rw [coeff_X]
      exact ite_eq_right fun h => hj (Finsupp.single_left_injective one_ne_zero h)),
    coeff_X, ite_eq_left rfl]

omit [LinearOrder σ] in
/-- Every exponent of `x_1 + ⋯ + x_n` is the indicator of a letter. -/
theorem exists_eq_single_of_mem_support_esymm_one {c : σ →₀ ℕ}
    (hc : c ∈ (esymm σ K 1).support) : ∃ j : σ, c = Finsupp.single j 1 := by
  classical
  rw [mem_support_iff, esymm_one, coeff_sum] at hc
  obtain ⟨j, -, hj⟩ := Finset.exists_ne_zero_of_sum_ne_zero hc
  exact ⟨j, Finset.mem_singleton.mp (support_X (R := K) (n := j) ▸ mem_support_iff.mpr hj)⟩

omit [LinearOrder σ] in
/-- **`x_1 + ⋯ + x_n` read as a polynomial in one letter is `X + C(x_1 + ⋯ + x_{n-1})`.** The letter
`t` contributes the variable and the others the constant term, which is again a first elementary
symmetric polynomial — this is what makes the coefficient of `x_t^{r+1}` in
`(x_1 + ⋯ + x_n)P_ρ[X_n]` the coefficient of `x_t^r` in `P_ρ[X_n]`, once the latter is known to have
degree at most `r` in `x_t`. -/
theorem splitAt_esymm_one [DecidableEq σ] (t : σ) :
    splitAt (R := K) t (esymm σ K 1)
      = Polynomial.X + Polynomial.C (esymm {b : σ // b ≠ t} K 1) := by
  rw [esymm_one, map_sum, Fintype.sum_eq_add_sum_subtype_ne _ t, splitAt_X_self, esymm_one,
    map_sum]
  exact congrArg (Polynomial.X + ·)
    (Finset.sum_congr rfl fun b _ => splitAt_X_of_ne (R := K) b.2)

variable [WellFoundedGT σ]

/-- **The leading exponent of `x_1 + ⋯ + x_n` is the indicator of the least letter**, with
coefficient `1` there (`HJO.Mac.coeff_single_esymm_one`). This is the vector `δ_1`, "the
indicator vector of `{1}` exceeding that of `{k}` for `k > 1`". -/
theorem lex_degree_esymm_one {i : σ} (hi : IsBot i) :
    lex.degree (esymm σ K 1) = Finsupp.single i 1 :=
  degree_eq_of_coeff_ne_zero (by rw [coeff_single_esymm_one]; exact one_ne_zero) fun c hc => by
    obtain ⟨j, rfl⟩ := exists_eq_single_of_mem_support_esymm_one hc
    refine lex_le_iff.mpr ?_
    rcases eq_or_lt_of_le (hi j) with rfl | hlt
    · exact le_rfl
    · exact (toLex_single_lt_single hlt).le

omit [WellFoundedGT σ] in
/-- `x_1 + ⋯ + x_n` is nonzero: its coefficient at the indicator of any letter is `1`. -/
theorem esymm_one_ne_zero [Nonempty σ] : esymm σ K 1 ≠ 0 := fun h => by
  have h1 := coeff_single_esymm_one (K := K) (Classical.arbitrary σ)
  rw [h, coeff_zero] at h1
  exact one_ne_zero h1.symm

end Esymm

/-! ### The first row of the one-cell Pieri expansion -/

section Support

variable {K : Type*} [Field K] [Algebra ℚ K] {q : Kˣ} {u : K}

/-- **The one-cell Pieri expansion, restricted to one alphabet long enough for every index that
occurs.** `HJO.Sym.restrictAlphabet_elemSymm` turns `e₁` into `x_1 + ⋯ + x_n` and
`HJO.Mac.restrictAlphabet_macPfun_partDiagram_of_pos` turns each `P_μ` into `P_μ[X_n]`; the sum is
reindexed over `S.attach` so that each summand carries the membership proof its index needs.

This is the step `HJO.Mac.rowLen_zero_le_of_coeff_ne_zero` and
`HJO.Mac.rowLen_succ_eq_of_coeff_ne_zero` share. The hypothesis is `μ.card ≤ n` for each `μ ∈ S`,
which at `n = |ρ| + 2` holds for every index of size `|ρ| + 1`. -/
theorem restrictAlphabet_elemSymm_one_mul_macPfun (hqu : AlgebraicIndependent ℤ ![(q : K), u])
    {n : ℕ} (hn : 1 ≤ n) {ρ : YoungDiagram} (hρn : ρ.card ≤ n) {S : Finset YoungDiagram}
    {c : YoungDiagram → K} (hSn : ∀ μ ∈ S, μ.card ≤ n)
    (hexp : HJO.Sym.elemSymm K 1 * HJO.Sym.macPfun hqu ρ
      = ∑ μ ∈ S, c μ • HJO.Sym.macPfun hqu μ) :
    esymm (Fin n) K 1 * (macPpoly hqu (idxOfDiagram ρ hρn) : MvPolynomial (Fin n) K)
      = ∑ x ∈ S.attach, c (x : YoungDiagram)
          • (macPpoly hqu (idxOfDiagram (x : YoungDiagram) (hSn x x.2)) :
              MvPolynomial (Fin n) K) := by
  have hres : ∀ (μ : YoungDiagram) (h : μ.card ≤ n),
      HJO.Sym.restrictAlphabet (Fin n) K (HJO.Sym.macPfun hqu μ)
        = (macPpoly hqu (idxOfDiagram μ h) : MvPolynomial (Fin n) K) := fun μ h => by
    have hr := restrictAlphabet_macPfun_partDiagram_of_pos hqu hn (idxOfDiagram μ h)
    rwa [partDiagram_idxOfDiagram μ h] at hr
  have h := congrArg (HJO.Sym.restrictAlphabet (Fin n) K) hexp
  rw [map_mul, map_sum, HJO.Sym.restrictAlphabet_elemSymm, hres ρ hρn] at h
  refine h.trans (((Finset.sum_attach S fun μ =>
    HJO.Sym.restrictAlphabet (Fin n) K (c μ • HJO.Sym.macPfun hqu μ)).symm).trans
    (Finset.sum_congr rfl fun x _ => ?_))
  rw [map_smul, hres (x : YoungDiagram) (hSn x x.2)]

/-- **`HJO.Mac.coeff_partExp_splitAt_macPpoly_eq` with the degree of its index as an argument.**
`HJO.Mac.coeff_partExp_splitAt_macPpoly_eq` delivers the coefficient of `x_t^{λ_1}` in `P_λ[X_n]` as
`P_κ[X_{n-1}]` for a `κ` of size `|λ| - λ_1`. A consumer comparing several such coefficients needs
them all at one size, and `|λ| - λ_1` is only *propositionally* that size; taking the size as an
argument with an equation absorbs the arithmetic in a single `subst`. -/
theorem exists_coeff_splitAt_macPpoly_eq {σ : Type*} [LinearOrder σ] [Fintype σ] {t : σ}
    (ht : IsTop t) (hqu : AlgebraicIndependent ℤ ![(q : K), u]) {d : ℕ} (μ : PartIdx σ d)
    {i₀ : σ} (hi₀ : IsBot i₀) {e : ℕ} (he : d - partExp σ μ i₀ = e) :
    ∃ κ : PartIdx {b : σ // b ≠ t} e,
      partDiagram {b : σ // b ≠ t} κ = HJO.Sym.shiftRows (partDiagram σ μ) ∧
      Polynomial.coeff (splitAt t (macPpoly hqu μ : MvPolynomial σ K)) (partExp σ μ i₀)
        = (macPpoly hqu κ : MvPolynomial {b : σ // b ≠ t} K) := by
  subst he
  obtain ⟨κ, hκ⟩ := exists_partDiagram_eq_shiftRows μ hi₀ t
  exact ⟨κ, hκ, coeff_partExp_splitAt_macPpoly_eq ht hqu μ hi₀ κ hκ⟩

/-- **The one-cell Pieri expansion does not lengthen the first row.** In
any identity `e₁P_ρ = ∑_{μ ∈ S} c_μ P_μ` whose indices all have `|μ| = |ρ| + 1`, an index with a
nonzero coefficient has `λ_1 ≤ ρ_1 + 1`.

Restrict to the alphabet `Fin (|ρ| + 2)`, which truncates no index that occurs: the left-hand side
becomes `(x_1 + ⋯ + x_n)P_ρ[X_n]`, of leading exponent `\bar\rho + δ_1`, and the right-hand side a
combination of the `P_μ[X_n]`, of leading exponents `\bar\mu`. At the lexicographically largest
`\bar\mu` with `c_μ ≠ 0` the right-hand side has coefficient `c_μ ≠ 0`, so that exponent is at most
`\bar\rho + δ_1`; and `\bar\lambda` is at most it. Reading the comparison at the least letter, where
a lexicographic `≤` is an entrywise `≤`, gives `λ_1 ≤ ρ_1 + 1`. -/
@[hjo "lem_dua_support_first"]
theorem rowLen_zero_le_of_coeff_ne_zero (hqu : AlgebraicIndependent ℤ ![(q : K), u])
    (ρ : YoungDiagram) (S : Finset YoungDiagram) (c : YoungDiagram → K)
    (hcard : ∀ μ ∈ S, μ.card = ρ.card + 1)
    (hexp : HJO.Sym.elemSymm K 1 * HJO.Sym.macPfun hqu ρ
      = ∑ μ ∈ S, c μ • HJO.Sym.macPfun hqu μ)
    {lam : YoungDiagram} (hlam : lam ∈ S) (hc : c lam ≠ 0) :
    lam.rowLen 0 ≤ ρ.rowLen 0 + 1 := by
  classical
  set n := ρ.card + 2 with hndef
  have hn1 : 1 ≤ n := by omega
  have hρn : ρ.card ≤ n := by omega
  have hSn : ∀ μ ∈ S, μ.card ≤ n := fun μ hμ => by rw [hcard μ hμ]; omega
  set i₀ : Fin n := ⟨0, by omega⟩ with hi₀def
  have hbot : IsBot i₀ := fun j => Fin.le_def.mpr (Nat.zero_le _)
  -- the exponent vector of an index of `S`, carried with its membership proof
  set E : {x // x ∈ S} → (Fin n →₀ ℕ) :=
    fun x => partExp (Fin n) (idxOfDiagram (x : YoungDiagram) (hSn x x.2)) with hEdef
  -- the restricted identity
  have hr := restrictAlphabet_elemSymm_one_mul_macPfun hqu hn1 hρn hSn hexp
  -- the leading exponent of the left-hand side
  have hPne : (macPpoly hqu (idxOfDiagram ρ hρn) : MvPolynomial (Fin n) K) ≠ 0 := fun h0 => by
    have h1 := coeff_partExp_macPpoly hqu (idxOfDiagram ρ hρn)
    rw [h0, coeff_zero] at h1
    exact one_ne_zero h1.symm
  obtain ⟨hne, hdeg⟩ := lex.mul_ne_zero_and_degree_mul (esymm_one_ne_zero (K := K)) hPne
  rw [lex_degree_esymm_one hbot, lex_degree_macPpoly] at hdeg
  -- the largest exponent among the indices with a nonzero coefficient
  set T : Finset {x // x ∈ S} := S.attach.filter fun x => c (x : YoungDiagram) ≠ 0 with hTdef
  have hlamT : (⟨lam, hlam⟩ : {x // x ∈ S}) ∈ T :=
    Finset.mem_filter.mpr ⟨Finset.mem_attach _ _, hc⟩
  obtain ⟨y, hyT, hymax⟩ := T.exists_max_image (fun x => toLex (E x)) ⟨_, hlamT⟩
  have hyc : c (y : YoungDiagram) ≠ 0 := (Finset.mem_filter.mp hyT).2
  -- the coefficient of the right-hand side at that exponent is `c y`
  have hcoeff : coeff (E y)
      (esymm (Fin n) K 1 * (macPpoly hqu (idxOfDiagram ρ hρn) : MvPolynomial (Fin n) K))
      = c (y : YoungDiagram) := by
    rw [hr, coeff_sum, Finset.sum_eq_single_of_mem y (Finset.mem_attach _ _) ?_, coeff_smul,
      smul_eq_mul, hEdef, coeff_partExp_macPpoly, mul_one]
    intro x _ hxy
    rw [coeff_smul, smul_eq_mul]
    rcases eq_or_ne (c (x : YoungDiagram)) 0 with h0 | h0
    · rw [h0, zero_mul]
    refine mul_eq_zero_of_right _ ?_
    have hxT : x ∈ T := Finset.mem_filter.mpr ⟨Finset.mem_attach _ _, h0⟩
    have hlt : toLex (E x) < toLex (E y) := lt_of_le_of_ne (hymax x hxT) fun heq =>
      hxy (Subtype.ext (eq_of_partExp_idxOfDiagram_eq _ _ (toLex.injective heq)))
    by_contra hne0
    exact absurd (lt_of_lt_of_le hlt
      (toLex_le_of_mem_support_macPpoly hqu _ (mem_support_iff.mpr hne0))) (lt_irrefl _)
  -- so that exponent occurs on the left, hence is at most `\bar\rho + δ_1`
  have hle : toLex (E y) ≤ toLex (Finsupp.single i₀ 1 + partExp (Fin n) (idxOfDiagram ρ hρn)) := by
    rw [← hdeg]
    exact lex_le_iff.mp (lex.le_degree (mem_support_iff.mpr (by rw [hcoeff]; exact hyc)))
  have hfinal := Finsupp.apply_le_of_toLex_le hbot
    ((hymax _ hlamT).trans hle : toLex (E ⟨lam, hlam⟩) ≤ _)
  rw [Finsupp.add_apply, Finsupp.single_eq_same, hEdef] at hfinal
  rw [partExp_idxOfDiagram_of_isBot lam (hSn lam hlam) hbot,
    partExp_idxOfDiagram_of_isBot ρ hρn hbot] at hfinal
  omega

/-- **At the longest first row the one-cell Pieri expansion is determined.**
In an identity `e₁P_ρ = ∑_{μ ∈ S} c_μ P_μ` whose indices all have `|μ| = |ρ| + 1`, an index `λ` with
`c_λ ≠ 0` and `λ_1 = ρ_1 + 1` agrees with `ρ` from the second row on.

Restrict to `Fin (|ρ| + 2)` (`restrictAlphabet_elemSymm_one_mul_macPfun`) and take the coefficient
of `x_t^{ρ_1+1}` in the greatest letter `t`. On the left only the `X` half of
`x_1 + ⋯ + x_n = X + C(x_1 + ⋯ + x_{n-1})` survives, `P_ρ[X_n]` having degree at most `ρ_1` in `x_t`
(`HJO.Mac.apply_le_partExp_of_mem_support_macPpoly`), and what is left is `P_{shiftRows ρ}[X_{n-1}]`
by `HJO.Mac.coeff_partExp_splitAt_macPpoly_eq`. On the right
`HJO.Mac.rowLen_zero_le_of_coeff_ne_zero` bounds each `μ_1` by `ρ_1+1`; the indices below that
contribute nothing and the rest contribute `c_μ P_{shiftRows μ}[X_{n-1}]`.

The `P_ϖ[X_{n-1}]` of one degree are a basis (`HJO.Mac.exists_basis_macPpoly`), and the coordinate
functional at the index of `shiftRows λ` reads `c_λ` on the right — distinct indices of the sum have
distinct shifts, `μ` being determined by `shiftRows μ` together with `μ_1 = ρ_1+1` — and `0` on the
left unless `shiftRows ρ = shiftRows λ`. Since `c_λ ≠ 0` the shifts agree, which is the
conclusion. -/
@[hjo "lem_dua_support_top"]
theorem rowLen_succ_eq_of_coeff_ne_zero (hqu : AlgebraicIndependent ℤ ![(q : K), u])
    (ρ : YoungDiagram) (S : Finset YoungDiagram) (c : YoungDiagram → K)
    (hcard : ∀ μ ∈ S, μ.card = ρ.card + 1)
    (hexp : HJO.Sym.elemSymm K 1 * HJO.Sym.macPfun hqu ρ
      = ∑ μ ∈ S, c μ • HJO.Sym.macPfun hqu μ)
    {lam : YoungDiagram} (hlam : lam ∈ S) (hc : c lam ≠ 0)
    (hone : lam.rowLen 0 = ρ.rowLen 0 + 1) (k : ℕ) :
    lam.rowLen (k + 1) = ρ.rowLen (k + 1) := by
  set n := ρ.card + 2 with hndef
  have hn1 : 1 ≤ n := by omega
  have hρn : ρ.card ≤ n := by omega
  have hSn : ∀ μ ∈ S, μ.card ≤ n := fun μ hμ => by rw [hcard μ hμ]; omega
  set i₀ : Fin n := ⟨0, by omega⟩ with hi₀def
  have hbot : IsBot i₀ := fun j => Fin.le_def.mpr (Nat.zero_le _)
  set t : Fin n := ⟨n - 1, by omega⟩ with htdef
  have htop : IsTop t := by
    intro j
    have hj := j.isLt
    exact Fin.le_def.mpr (show (j : ℕ) ≤ n - 1 by omega)
  -- `r` is `ρ_1` and `e` is `|ρ| - r`, the degree every extracted coefficient has
  obtain ⟨r, hr0⟩ : ∃ r, ρ.rowLen 0 = r := ⟨_, rfl⟩
  rw [hr0] at hone
  have hpμ : ∀ (μ : YoungDiagram) (h : μ.card ≤ n),
      partExp (Fin n) (idxOfDiagram μ h) i₀ = μ.rowLen 0 :=
    fun μ h => partExp_idxOfDiagram_of_isBot μ h hbot
  have hpρ : partExp (Fin n) (idxOfDiagram ρ hρn) i₀ = r := by rw [hpμ ρ hρn, hr0]
  have hrc : r ≤ ρ.card := hpρ ▸ partExp_le (idxOfDiagram ρ hρn) i₀
  obtain ⟨e, he0⟩ : ∃ e, r + e = ρ.card := ⟨ρ.card - r, by omega⟩
  -- the index of `shiftRows ρ`, and the identification of the coefficient of `x_t^r`
  obtain ⟨κρ, hκρ1, hκρ2⟩ := exists_coeff_splitAt_macPpoly_eq htop hqu (idxOfDiagram ρ hρn) hbot
    (e := e) (by rw [hpρ]; omega)
  rw [partDiagram_idxOfDiagram ρ hρn] at hκρ1
  rw [hpρ] at hκρ2
  -- the same for `λ`, whose first row is `r + 1`
  obtain ⟨κlam, hκlam1, hκlam2⟩ := exists_coeff_splitAt_macPpoly_eq htop hqu
    (idxOfDiagram lam (hSn lam hlam)) hbot (e := e)
    (by rw [hpμ lam (hSn lam hlam), hone, hcard lam hlam]; omega)
  rw [partDiagram_idxOfDiagram lam (hSn lam hlam)] at hκlam1
  rw [hpμ lam (hSn lam hlam), hone] at hκlam2
  -- the coefficient identity in the smaller alphabet
  have hr := restrictAlphabet_elemSymm_one_mul_macPfun hqu hn1 hρn hSn hexp
  have hkey : Polynomial.coeff
      (splitAt t (macPpoly hqu (idxOfDiagram ρ hρn) : MvPolynomial (Fin n) K)) r
      = ∑ x ∈ S.attach, c (x : YoungDiagram) • Polynomial.coeff
          (splitAt t (macPpoly hqu (idxOfDiagram (x : YoungDiagram) (hSn x x.2)) :
            MvPolynomial (Fin n) K)) (r + 1) := by
    have h : Polynomial.coeff (splitAt t (esymm (Fin n) K 1
          * (macPpoly hqu (idxOfDiagram ρ hρn) : MvPolynomial (Fin n) K))) (r + 1)
        = Polynomial.coeff (splitAt t (∑ x ∈ S.attach, c (x : YoungDiagram)
            • (macPpoly hqu (idxOfDiagram (x : YoungDiagram) (hSn x x.2)) :
                MvPolynomial (Fin n) K))) (r + 1) := by rw [hr]
    rw [map_mul, splitAt_esymm_one, add_mul, Polynomial.coeff_add, Polynomial.coeff_X_mul,
      Polynomial.coeff_C_mul,
      coeff_splitAt_macPpoly_eq_zero hqu (idxOfDiagram ρ hρn) hbot t (k := r + 1)
        (by rw [hpρ]; omega),
      mul_zero, add_zero, map_sum, Polynomial.finsetSum_coeff] at h
    refine h.trans (Finset.sum_congr rfl fun x _ => ?_)
    rw [map_smul, Polynomial.coeff_smul]
  -- both sides live in `𝒮_{n-1,e}`
  have memρ : Polynomial.coeff
      (splitAt t (macPpoly hqu (idxOfDiagram ρ hρn) : MvPolynomial (Fin n) K)) r
      ∈ symmetricHomogeneousSubmodule {b : Fin n // b ≠ t} K e :=
    coeff_splitAt_macPpoly_mem hqu (idxOfDiagram ρ hρn) t he0
  have hmem : ∀ x : {x // x ∈ S}, Polynomial.coeff
      (splitAt t (macPpoly hqu (idxOfDiagram (x : YoungDiagram) (hSn x x.2)) :
        MvPolynomial (Fin n) K)) (r + 1)
      ∈ symmetricHomogeneousSubmodule {b : Fin n // b ≠ t} K e := fun x =>
    coeff_splitAt_macPpoly_mem hqu _ t (by rw [hcard x x.2]; omega)
  have hEq : (⟨_, memρ⟩ : symmetricHomogeneousSubmodule {b : Fin n // b ≠ t} K e)
      = ∑ x ∈ S.attach, c (x : YoungDiagram)
          • (⟨_, hmem x⟩ : symmetricHomogeneousSubmodule {b : Fin n // b ≠ t} K e) := by
    refine Subtype.ext ?_
    rw [AddSubmonoidClass.coe_finsetSum]
    exact hkey.trans (Finset.sum_congr rfl fun x _ => rfl)
  -- the coordinate functional of the basis at the index of `shiftRows λ`
  obtain ⟨B, hB⟩ := exists_basis_macPpoly (σ := {b : Fin n // b ≠ t}) (K := K) (q := q) (u := u)
    (d := e) hqu
  set L : symmetricHomogeneousSubmodule {b : Fin n // b ≠ t} K e →ₗ[K] K :=
    (Finsupp.lapply κlam).comp (B.repr : _ →ₗ[K] _) with hLdef
  have hL : ∀ ν : PartIdx {b : Fin n // b ≠ t} e,
      L (macPpoly hqu ν) = (Finsupp.single ν (1 : K)) κlam := fun ν => by
    rw [hLdef, LinearMap.comp_apply, Finsupp.lapply_apply, LinearEquiv.coe_coe, ← hB,
      Module.Basis.repr_self]
  -- reading the identity through it
  have hLeq := congrArg L hEq
  rw [map_sum, Finset.sum_eq_single_of_mem (⟨lam, hlam⟩ : {x // x ∈ S})
    (Finset.mem_attach _ _) ?_] at hLeq
  · rw [show (⟨_, memρ⟩ : symmetricHomogeneousSubmodule {b : Fin n // b ≠ t} K e)
        = macPpoly hqu κρ from Subtype.ext hκρ2, hL, map_smul,
      show (⟨_, hmem (⟨lam, hlam⟩ : {x // x ∈ S})⟩ :
          symmetricHomogeneousSubmodule {b : Fin n // b ≠ t} K e)
        = macPpoly hqu κlam from Subtype.ext hκlam2,
      hL, Finsupp.single_eq_same, smul_eq_mul, mul_one] at hLeq
    have hκeq : κρ = κlam := by
      by_contra hne
      rw [Finsupp.single_eq_of_ne (Ne.symm hne)] at hLeq
      exact hc hLeq.symm
    rw [← HJO.Sym.rowLen_shiftRows lam k, ← HJO.Sym.rowLen_shiftRows ρ k, ← hκlam1, ← hκρ1, hκeq]
  · intro x _ hxne
    rcases eq_or_ne (c (x : YoungDiagram)) 0 with h0 | h0
    · rw [h0, zero_smul, map_zero]
    rw [map_smul]
    have hb := rowLen_zero_le_of_coeff_ne_zero hqu ρ S c hcard hexp x.2 h0
    rw [hr0] at hb
    rcases lt_or_eq_of_le hb with hlt | heq
    · rw [show (⟨_, hmem x⟩ : symmetricHomogeneousSubmodule {b : Fin n // b ≠ t} K e) = 0 from
        Subtype.ext (coeff_splitAt_macPpoly_eq_zero hqu _ hbot t (k := r + 1)
          (by rw [hpμ (x : YoungDiagram) (hSn x x.2)]; exact hlt)), map_zero, smul_zero]
    obtain ⟨κx, hκx1, hκx2⟩ := exists_coeff_splitAt_macPpoly_eq htop hqu
      (idxOfDiagram (x : YoungDiagram) (hSn x x.2)) hbot (e := e)
      (by rw [hpμ (x : YoungDiagram) (hSn x x.2), heq, hcard x x.2]; omega)
    rw [partDiagram_idxOfDiagram (x : YoungDiagram) (hSn x x.2)] at hκx1
    rw [hpμ (x : YoungDiagram) (hSn x x.2), heq] at hκx2
    have hne : κx ≠ κlam := by
      intro hh
      refine hxne (Subtype.ext (HJO.Sym.eq_of_rowLen_eq fun j => ?_))
      cases j with
      | zero => rw [heq, hone]
      | succ m =>
          rw [← HJO.Sym.rowLen_shiftRows (x : YoungDiagram) m,
            ← HJO.Sym.rowLen_shiftRows lam m, ← hκx1, hh, hκlam1]
    rw [show (⟨_, hmem x⟩ : symmetricHomogeneousSubmodule {b : Fin n // b ≠ t} K e)
        = macPpoly hqu κx from Subtype.ext hκx2, hL,
      Finsupp.single_eq_of_ne (Ne.symm hne), smul_zero]

end Support

end HJO.Mac
