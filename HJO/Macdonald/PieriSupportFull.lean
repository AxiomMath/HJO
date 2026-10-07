/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.Macdonald.PieriColumn
public import HJO.Macdonald.PieriSupportLong
public import HJO.Macdonald.PpolyBasis
public import HJO.Macdonald.ResPpolyZero
public meta import HJO.Attr

/-! # The one-cell Pieri support of Macdonald's `P`

`HJO.Standing.hasPfunPieriSupport_param`: `e₁P_ν` lies in the `𝕜`-span of the `P_μ` with `μ`
covering `ν`. This is the last input of the collinear cone: `HJO.Sym.HasPfunPieriSupport` is the one
`Prop` `HJO.CollinearNarrowed.collinearCommutation_of_pfunPieriSupport` costs.

## The route

The induction on `|ν|`. `HJO.Ascent.elemSymm_one_mul_macPfun_mem_span_covers_or_short` disposes of
every index except the short ones, so what is left is: `c_λ ≠ 0` and `λ_{l+1} = 0` force `λ ⋗ ν`,
where `l = ν.colLen 0` is the number of nonempty rows of `ν`.

* `l = 0` is impossible, not a base case: then `λ_1 = 0`, so `λ` has no cell
  (`HJO.Mac.card_eq_sum_rowLen` at `n = 0`), while `|λ| = |ν|+1 ≥ 1`.
* Restrict to `Fin l`. `HJO.Sym.restrictAlphabet_elemSymm` turns `e₁` into `x_1 + ⋯ + x_l` and
  `HJO.Mac.restrictAlphabet_macPfun_eq_zero` kills every `P_κ` with `κ_{l+1} ≥ 1`.
* Remove the first column. `HJO.Mac.macPpoly_eq_prod_X_mul` gives
  `res_l(P_κ) = x_1⋯x_l · res_l(P_{κ⁻})` whenever all `l` rows of `κ` are nonempty, and `ν` is such
  a `κ`. The indices with `κ_l = 0` are not, and `HJO.Mac.eq_zero_of_sum_smul_macPpoly_eq_esymm_mul`
  makes their coefficients vanish, after which `x_1⋯x_l` cancels in the domain `𝕜[x_1,…,x_l]`.
* Compare with the induction hypothesis at `ν⁻`, whose expansion restricts the same way. The
  `res_l(P_ρ)` with `|ρ| = |ν⁻|+1` and `ρ_{l+1} = 0` are independent
  (`HJO.Mac.exists_basis_macPpoly`), so `c_λ = b_{λ⁻}`, so `λ⁻ ⋗ ν⁻`; adding the column back is
  entrywise and gives `λ ⋗ ν`.

## Where the indices live, and where they do not

`HJO.Mac.macPpoly` is indexed by `HJO.Mac.PartIdx (Fin l) d`, a type that depends on the degree, and
the degrees here are `|ν|+1` and `|ν|+1-l`; carrying that dependency through the induction is what
makes this lemma awkward rather than long. So every index is confined to four wrappers, each stated
in terms of `res_l(P_ρ)` for a *diagram* `ρ` and nothing else:

* `HJO.Mac.restrict_expansion`: restricting an expansion to `Fin l` keeps the short indices.
* `HJO.Mac.restrictAlphabet_macPfun_eq_prod_X_mul`: the column removal
  (`HJO.Mac.macPpoly_eq_prod_X_mul`).
* `HJO.Mac.eq_zero_of_sum_smul_restrictAlphabet_macPfun_eq_prod_X_mul`: the column independence
  (`HJO.Mac.eq_zero_of_sum_smul_macPpoly_eq_esymm_mul`).
* `HJO.Mac.eq_of_sum_smul_restrictAlphabet_macPfun_eq`: the comparison
  (`HJO.Mac.exists_basis_macPpoly`).

The induction itself then never mentions `PartIdx`, and `HJO.Sym.dropFirstColumn` is a diagram.

## The reindexing, without an inverse

The usual argument compares a sum indexed by the `κ` with a sum indexed by the `κ⁻`, as this proof
does, and inverts `κ ↦ κ⁻`. Here the left-hand coefficient is instead read as
`f ρ = ∑_{κ ∈ S₁} [κ⁻ = ρ] c_κ`, which is total in `ρ` and needs no inverse; injectivity of
`κ ↦ κ⁻` on `S₁` (`HJO.Sym.dropFirstColumn_injOn`) is spent once, at the end, to evaluate
`f λ⁻ = c_λ`. Adding a full first column back to a diagram is therefore never constructed.

## Genericity

At the standing field, because `HJO.Ascent.elemSymm_one_mul_macPfun_mem_span_covers_or_short` is,
because `HJO.Ascent.coeff_transpose_ne_zero_of_coeff_ne_zero` is: it runs on `Ω`, which needs the
parameter automorphism `ι∘τ` of the coefficient field. Nothing in the present file spends any
nonvanishing beyond the genericity `macPfun` already carries -- the four wrappers are all at an
arbitrary pair with `AlgebraicIndependent ℤ ![q, u]`.

## Main results

* `HJO.Sym.dropFirstColumn`, `HJO.Sym.rowLen_dropFirstColumn`, `HJO.Sym.card_dropFirstColumn`,
  `HJO.Sym.dropFirstColumn_injOn`: the diagram `ν⁻`.
* the four wrappers listed above.
* `HJO.Standing.hasPfunPieriCoeff_param`, `HJO.Standing.hasPfunPieriSupport_param`.

## References

This file proves `HJO.Standing.hasPfunPieriSupport_param`, the support of the Pieri expansion, on
Definitions `HJO.Sym.Lambda`, `HJO.Sym.LambdaComp`, `HJO.Sym.elemSymm`, `HJO.Sym.rowLenSeq`,
`HJO.Sym.cells`, `HJO.Sym.Covers`, `HJO.Sym.macPfun` and `HJO.Sym.restrictAlphabet` and Lemmas
`HJO.Sym.exists_basis_lambdaComp_macPfun`, `HJO.Sym.restrictAlphabet_elemSymm`,
`HJO.Mac.exists_basis_macPpoly`, `HJO.Mac.restrictAlphabet_macPfun_partDiagram_of_pos`,
`HJO.Mac.restrictAlphabet_macPfun_eq_zero`, `HJO.Mac.macPpoly_eq_prod_X_mul`,
`HJO.Mac.eq_zero_of_sum_smul_macPpoly_eq_esymm_mul` and
`HJO.Ascent.elemSymm_one_mul_macPfun_mem_span_covers_or_short`.
-/

@[expose] public section

open Finset MvPolynomial

namespace HJO.Sym

/-! ### Removing the first column of a diagram -/

/-- **The diagram with its first column removed**, `ν⁻`: row `k` loses one cell, so
`ν⁻_k = ν_k - 1`. The truncated subtraction is harmless and is what makes the sequence total: a row
that was already empty stays empty, and the sequence is still weakly decreasing and eventually
zero. -/
noncomputable def dropFirstColumn (Y : YoungDiagram) : YoungDiagram :=
  ofRowLenSeq (fun k => Y.rowLen k - 1)
    (fun a b hab => Nat.sub_le_sub_right (Y.rowLen_anti a b hab) 1)
    ((rowLenSeq_finite_support Y).subset fun i hi => by
      simp only [Set.mem_ofPred_eq, rowLenSeq_apply] at hi ⊢
      omega)

@[simp]
theorem rowLen_dropFirstColumn (Y : YoungDiagram) (k : ℕ) :
    (dropFirstColumn Y).rowLen k = Y.rowLen k - 1 :=
  rowLen_ofRowLenSeq k

/-- **Removing the first column of a diagram with `l` nonempty rows removes `l` cells**, that is,
`|ν⁻| = |ν| - l`. Both sizes are the sum of the first `l` row lengths
(`HJO.Mac.card_eq_sum_rowLen`), and each summand drops by exactly one, no row being empty. -/
theorem card_dropFirstColumn {l : ℕ} {Y : YoungDiagram} (hshort : Y.rowLen l = 0)
    (hfull : ∀ k, k < l → Y.rowLen k ≠ 0) : (dropFirstColumn Y).card + l = Y.card := by
  have h1 : Y.card = ∑ k ∈ Finset.range l, Y.rowLen k := HJO.Mac.card_eq_sum_rowLen Y hshort
  have h2 : (dropFirstColumn Y).card = ∑ k ∈ Finset.range l, (Y.rowLen k - 1) := by
    rw [HJO.Mac.card_eq_sum_rowLen (dropFirstColumn Y) (by rw [rowLen_dropFirstColumn, hshort])]
    exact Finset.sum_congr rfl fun k _ => rowLen_dropFirstColumn Y k
  have h3 : ∑ k ∈ Finset.range l, Y.rowLen k
      = ∑ k ∈ Finset.range l, (Y.rowLen k - 1 + 1) :=
    Finset.sum_congr rfl fun k hk => by
      have := hfull k (Finset.mem_range.mp hk)
      omega
  rw [h1, h3, Finset.sum_add_distrib, h2]
  simp

/-- **A diagram whose first row is empty has no cells**, `HJO.Mac.card_eq_sum_rowLen` at `n = 0`.
This is what makes the `l = 0` case vacuous rather than a base case of the
induction. -/
theorem card_eq_zero_of_rowLen_zero_eq_zero {Y : YoungDiagram} (h : Y.rowLen 0 = 0) :
    Y.card = 0 := by
  rw [HJO.Mac.card_eq_sum_rowLen Y h, Finset.range_zero, Finset.sum_empty]

/-- **Removing the first column is injective on the diagrams with `l` nonempty rows and no row at
`l`.** The row lengths are recovered by adding one back below `l`, and are zero from `l` on. -/
theorem dropFirstColumn_injOn {l : ℕ} {Y Z : YoungDiagram}
    (hYs : Y.rowLen l = 0) (hYf : ∀ k, k < l → Y.rowLen k ≠ 0)
    (hZs : Z.rowLen l = 0) (hZf : ∀ k, k < l → Z.rowLen k ≠ 0)
    (h : dropFirstColumn Y = dropFirstColumn Z) : Y = Z := by
  refine eq_of_rowLen_eq fun k => ?_
  have hk := congrArg (fun W : YoungDiagram => W.rowLen k) h
  simp only [rowLen_dropFirstColumn] at hk
  rcases lt_or_ge k l with hlt | hge
  · have h1 := hYf k hlt
    have h2 := hZf k hlt
    omega
  · have h1 : Y.rowLen k = 0 := Nat.le_zero.mp (hYs ▸ Y.rowLen_anti l k hge)
    have h2 : Z.rowLen k = 0 := Nat.le_zero.mp (hZs ▸ Z.rowLen_anti l k hge)
    rw [h1, h2]

end HJO.Sym

namespace HJO.Mac

/-! ### Reading an index off a diagram -/

section Index

variable {σ : Type*} [Fintype σ] [LinearOrder σ] [DecidableEq σ] {d : ℕ}

/-- **The row lengths of the diagram of an index are the entries of its exponent vector**, read
along the order of the alphabet. This is `HJO.Mac.rowLen_partDiagram` with the `dite` of
`HJO.Mac.rowLenSeqOf` discharged. -/
theorem rowLen_partDiagram_letterEquiv (μ : PartIdx σ d) (i : Fin (Fintype.card σ)) :
    (partDiagram σ μ).rowLen (i : ℕ) = partExp σ μ (letterEquiv σ i) := by
  rw [rowLen_partDiagram, rowLenSeqOf_of_lt i.isLt]

/-- **A diagram with no row at `l` and `D` cells is the diagram of an index of
`PartIdx (Fin l) D`.** `HJO.Mac.exists_partDiagram_eq` with the size named, so that all the indices
occurring in one comparison have one type. -/
theorem exists_partDiagram_eq_of_card {l D : ℕ} {Y : YoungDiagram} (hD : Y.card = D)
    (hY : Y.rowLen l = 0) : ∃ I : PartIdx (Fin l) D, partDiagram (Fin l) I = Y := by
  subst hD
  exact exists_partDiagram_eq (σ := Fin l) (by simpa using hY)

/-- **The index with the first column removed exists**, and its exponent vector is that of `I` with
one subtracted everywhere -- which is the hypothesis of `HJO.Mac.macPpoly_eq_prod_X_mul`.

The degree bookkeeping is the identity `|κ⁻| = |κ| - l`: every entry of the exponent vector is at
least `1`, no row of the diagram being empty, so subtracting one from each drops the degree by
exactly the size `l` of the alphabet. -/
theorem exists_partExp_eq_onesExp_add_of_full {l E : ℕ} {Y : YoungDiagram}
    {I : PartIdx (Fin l) (l + E)} (hI : partDiagram (Fin l) I = Y)
    (hfull : ∀ k, k < l → Y.rowLen k ≠ 0) :
    ∃ J : PartIdx (Fin l) E, partDiagram (Fin l) J = HJO.Sym.dropFirstColumn Y ∧
      partExp (Fin l) I = onesExp (Fin l) + partExp (Fin l) J := by
  classical
  have hcardl : Fintype.card (Fin l) = l := Fintype.card_fin l
  have hdegsum : ∀ α : Fin l →₀ ℕ, α.degree = ∑ i : Fin l, α i := fun α => by
    rw [Finsupp.degree_apply]
    exact Finset.sum_subset (Finset.subset_univ _) fun i _ hi =>
      Finsupp.notMem_support_iff.mp hi
  -- the entries of `\bar I` are the row lengths of `Y`, hence all at least `1`
  have hval : ∀ i : Fin l, partExp (Fin l) I i
      = Y.rowLen (((letterEquiv (Fin l)).symm i : Fin (Fintype.card (Fin l))) : ℕ) := by
    intro i
    have h := rowLen_partDiagram_letterEquiv I ((letterEquiv (Fin l)).symm i)
    rw [OrderIso.apply_symm_apply, hI] at h
    exact h.symm
  have hpos : ∀ i : Fin l, 1 ≤ partExp (Fin l) I i := by
    intro i
    rw [hval i]
    refine Nat.one_le_iff_ne_zero.mpr (hfull _ ?_)
    have := ((letterEquiv (Fin l)).symm i).isLt
    omega
  -- the exponent vector with one subtracted everywhere
  set β : Fin l →₀ ℕ :=
    Finsupp.equivFunOnFinite.symm (fun i => partExp (Fin l) I i - 1) with hβdef
  have hβ : ∀ i, β i = partExp (Fin l) I i - 1 := fun i => by rw [hβdef]; rfl
  have hanti : Antitone β := fun a b hab => by
    rw [hβ, hβ]
    exact Nat.sub_le_sub_right (antitone_partExp I hab) 1
  have hdeg : β.degree = E := by
    have h1 : ∑ i : Fin l, partExp (Fin l) I i = ∑ i : Fin l, (β i + 1) :=
      Finset.sum_congr rfl fun i _ => by
        have := hpos i
        rw [hβ]
        omega
    have hone : ∑ _i : Fin l, 1 = l := by simp
    have h2 : (partExp (Fin l) I).degree = l + E := by rw [degree_partExp]
    rw [hdegsum] at h2 ⊢
    rw [h1, Finset.sum_add_distrib, hone] at h2
    omega
  obtain ⟨J, hJ⟩ := exists_partExp_eq hanti hdeg
  refine ⟨J, HJO.Sym.eq_of_rowLen_eq fun k => ?_, Finsupp.ext fun i => ?_⟩
  · rw [rowLen_partDiagram, hJ, HJO.Sym.rowLen_dropFirstColumn]
    rcases lt_or_ge k (Fintype.card (Fin l)) with hlt | hge
    · rw [rowLenSeqOf_of_lt hlt, hβ, hval]
      congr 2
      exact congrArg _ ((letterEquiv (Fin l)).symm_apply_apply _)
    · rw [rowLenSeqOf_of_le hge]
      have hY : Y.rowLen k = 0 := by rw [← hI, rowLen_partDiagram, rowLenSeqOf_of_le hge]
      rw [hY]
  · have := hpos i
    rw [Finsupp.add_apply, onesExp_apply, hJ, hβ]
    omega

end Index

/-! ### The four wrappers: everything about indices, stated about diagrams -/

section Wrappers

variable {K : Type*} [Field K] [Algebra ℚ K] {q : Kˣ} {u : K}

/-- **Restricting an expansion of `e₁P_Y` to `Fin l` keeps exactly the short indices.**
`HJO.Sym.restrictAlphabet_elemSymm` turns `e₁` into `x_1 + ⋯ + x_l` and
`HJO.Mac.restrictAlphabet_macPfun_eq_zero` kills every `P_ρ` with `ρ_{l+1} ≥ 1`.

`res_l(P_ρ)` is left unevaluated on both sides:
`HJO.Mac.restrictAlphabet_macPfun_partDiagram_of_pos` identifies it with `P_ρ[X_l]`, but no consumer
needs that here -- the other three wrappers do it internally. -/
theorem restrict_expansion {l : ℕ} (hqu : AlgebraicIndependent ℤ ![(q : K), u])
    (Y : YoungDiagram) (T T₀ : Finset YoungDiagram) (b : YoungDiagram → K)
    (hexp : HJO.Sym.elemSymm K 1 * HJO.Sym.macPfun hqu Y
      = ∑ ρ ∈ T, b ρ • HJO.Sym.macPfun hqu ρ)
    (hT₀ : ∀ ρ, ρ ∈ T₀ ↔ ρ ∈ T ∧ ρ.rowLen l = 0) :
    esymm (Fin l) K 1 * HJO.Sym.restrictAlphabet (Fin l) K (HJO.Sym.macPfun hqu Y)
      = ∑ ρ ∈ T₀, b ρ • HJO.Sym.restrictAlphabet (Fin l) K (HJO.Sym.macPfun hqu ρ) := by
  classical
  have h := congrArg (HJO.Sym.restrictAlphabet (Fin l) K) hexp
  rw [map_mul, HJO.Sym.restrictAlphabet_elemSymm, map_sum] at h
  have hsub : T₀ ⊆ T := fun ρ hρ => ((hT₀ ρ).mp hρ).1
  have hzero : ∀ ρ ∈ T, ρ ∉ T₀ →
      HJO.Sym.restrictAlphabet (Fin l) K (b ρ • HJO.Sym.macPfun hqu ρ) = 0 := by
    intro ρ hρT hρ0
    rw [map_smul, restrictAlphabet_macPfun_eq_zero hqu
      (fun hz => hρ0 ((hT₀ ρ).mpr ⟨hρT, hz⟩)), smul_zero]
  rw [h, ← Finset.sum_subset hsub hzero]
  exact Finset.sum_congr rfl fun ρ _ => by rw [map_smul]

/-- **`HJO.Mac.macPpoly_eq_prod_X_mul`, about diagrams**: if all `l` rows of `Y` are nonempty and
there is no row at `l`, then `res_l(P_Y) = x_1 ⋯ x_l · res_l(P_{Y⁻})`.

`HJO.Mac.exists_partDiagram_eq_of_card` names the index of `Y`,
`HJO.Mac.exists_partExp_eq_onesExp_add_of_full` the index of `Y⁻` together with the exponent
identity `HJO.Mac.macPpoly_eq_prod_X_mul` asks for, and
`HJO.Mac.restrictAlphabet_macPfun_partDiagram_of_pos` identifies both restrictions. -/
theorem restrictAlphabet_macPfun_eq_prod_X_mul {l : ℕ} (hl : 1 ≤ l)
    (hqu : AlgebraicIndependent ℤ ![(q : K), u]) {Y : YoungDiagram} (hshort : Y.rowLen l = 0)
    (hfull : ∀ k, k < l → Y.rowLen k ≠ 0) :
    HJO.Sym.restrictAlphabet (Fin l) K (HJO.Sym.macPfun hqu Y)
      = (∏ j : Fin l, X j) *
          HJO.Sym.restrictAlphabet (Fin l) K
            (HJO.Sym.macPfun hqu (HJO.Sym.dropFirstColumn Y)) := by
  obtain ⟨E, hE⟩ : ∃ E, Y.card = l + E :=
    ⟨Y.card - l, by have := HJO.Sym.card_dropFirstColumn hshort hfull; omega⟩
  obtain ⟨I, hI⟩ := exists_partDiagram_eq_of_card (l := l) hE hshort
  obtain ⟨J, hJ, hIJ⟩ := exists_partExp_eq_onesExp_add_of_full hI hfull
  rw [← hJ, restrictAlphabet_macPfun_partDiagram_of_pos hqu hl J, ← hI,
    restrictAlphabet_macPfun_partDiagram_of_pos hqu hl I]
  exact macPpoly_eq_prod_X_mul hqu hIJ

/-- **`HJO.Mac.eq_zero_of_sum_smul_macPpoly_eq_esymm_mul`, about diagrams**: a combination of the
`res_l(P_ρ)` over diagrams of one size whose row at `l-1` is empty cannot be a multiple of
`x_1 ⋯ x_l` unless every coefficient vanishes.

The exponent vector of such a `ρ` has a zero entry at the greatest letter
(`HJO.Mac.rowLen_partDiagram_letterEquiv`), which is what
`HJO.Mac.eq_zero_of_sum_smul_macPpoly_eq_esymm_mul` asks for; the coefficient is transported to
`HJO.Mac.SizedIdx` by reading the diagram of the index, so no inverse is needed. -/
theorem eq_zero_of_sum_smul_restrictAlphabet_macPfun_eq_prod_X_mul {l D : ℕ} (hl : 1 ≤ l)
    (hqu : AlgebraicIndependent ℤ ![(q : K), u]) (T : Finset YoungDiagram) (c : YoungDiagram → K)
    (hcard : ∀ ρ ∈ T, ρ.card = D) (hshort : ∀ ρ ∈ T, ρ.rowLen l = 0)
    (hnotfull : ∀ ρ ∈ T, ρ.rowLen (l - 1) = 0) {g : MvPolynomial (Fin l) K}
    (hsum : ∑ ρ ∈ T, c ρ • HJO.Sym.restrictAlphabet (Fin l) K (HJO.Sym.macPfun hqu ρ)
      = (∏ j : Fin l, X j) * g) :
    ∀ ρ ∈ T, c ρ = 0 := by
  classical
  choose I hI using fun x : {ρ // ρ ∈ T} =>
    exists_partDiagram_eq_of_card (l := l) (D := D) (hcard _ x.2) (hshort _ x.2)
  have hres : ∀ x : {ρ // ρ ∈ T},
      HJO.Sym.restrictAlphabet (Fin l) K (HJO.Sym.macPfun hqu (x : YoungDiagram))
        = (macPpoly hqu (I x) : MvPolynomial (Fin l) K) := by
    intro x
    rw [← hI x]
    exact restrictAlphabet_macPfun_partDiagram_of_pos hqu hl (I x)
  -- the greatest letter, at which the exponent vector of every index of `T` vanishes
  have hlt : l - 1 < Fintype.card (Fin l) := by rw [Fintype.card_fin]; omega
  have hzero : ∀ x : {ρ // ρ ∈ T},
      partExp (Fin l) (I x) (letterEquiv (Fin l) ⟨l - 1, hlt⟩) = 0 := by
    intro x
    rw [← rowLen_partDiagram_letterEquiv (I x) ⟨l - 1, hlt⟩, hI x]
    exact hnotfull _ x.2
  set V : Finset (SizedIdx (Fin l)) :=
    T.attach.image (fun x => (⟨D, I x⟩ : SizedIdx (Fin l))) with hVdef
  set cc : SizedIdx (Fin l) → K := fun s => c (partDiagram (Fin l) s.2) with hccdef
  have hccval : ∀ x : {ρ // ρ ∈ T}, cc (⟨D, I x⟩ : SizedIdx (Fin l)) = c (x : YoungDiagram) := by
    intro x
    simp only [hccdef]
    exact congrArg c (hI x)
  have hinj : Set.InjOn (fun x : {ρ // ρ ∈ T} => (⟨D, I x⟩ : SizedIdx (Fin l))) T.attach := by
    intro x _ y _ hxy
    have h1 := congrArg (fun s : SizedIdx (Fin l) => partDiagram (Fin l) s.2) hxy
    simp only at h1
    rw [hI x, hI y] at h1
    exact Subtype.ext h1
  have hVmem : ∀ x : {ρ // ρ ∈ T}, (⟨D, I x⟩ : SizedIdx (Fin l)) ∈ V := fun x => by
    rw [hVdef]
    exact Finset.mem_image_of_mem _ (Finset.mem_attach _ _)
  have hVexists : ∀ s ∈ V, ∃ x : {ρ // ρ ∈ T}, (⟨D, I x⟩ : SizedIdx (Fin l)) = s := by
    intro s hs
    rw [hVdef] at hs
    obtain ⟨x, -, hx⟩ := Finset.mem_image.mp hs
    exact ⟨x, hx⟩
  have hVsum : ∑ s ∈ V, cc s • (macPpoly hqu s.2 : MvPolynomial (Fin l) K)
      = esymm (Fin l) K (Fintype.card (Fin l)) * g := by
    rw [esymm_fintypeCard, hVdef, Finset.sum_image hinj, ← hsum, ← Finset.sum_attach T
      (fun ρ => c ρ • HJO.Sym.restrictAlphabet (Fin l) K (HJO.Sym.macPfun hqu ρ))]
    exact Finset.sum_congr rfl fun x _ => by rw [hccval x, hres x]
  have hkey := eq_zero_of_sum_smul_macPpoly_eq_esymm_mul hqu (S := V) (c := cc)
    (fun s hs => by
      obtain ⟨x, rfl⟩ := hVexists s hs
      exact ⟨letterEquiv (Fin l) ⟨l - 1, hlt⟩, hzero x⟩)
    hVsum
  intro ρ hρ
  have h := hkey _ (hVmem ⟨ρ, hρ⟩)
  rwa [hccval ⟨ρ, hρ⟩] at h

/-- **`HJO.Mac.exists_basis_macPpoly`, about diagrams**: the `res_l(P_ρ)` over the diagrams of one
size with no row at `l` are independent, so two combinations of them agree coefficientwise.

`HJO.Mac.restrictAlphabet_macPfun_partDiagram_of_pos` identifies each with `P_ρ[X_l]`, distinct
diagrams give distinct indices (`HJO.Mac.partDiagram_injective`), and each coefficient is read back
through the diagram of the index, which is what makes both coefficient functions total. -/
theorem eq_of_sum_smul_restrictAlphabet_macPfun_eq {l D : ℕ} (hl : 1 ≤ l)
    (hqu : AlgebraicIndependent ℤ ![(q : K), u]) (U : Finset YoungDiagram)
    (hcard : ∀ ρ ∈ U, ρ.card = D) (hshort : ∀ ρ ∈ U, ρ.rowLen l = 0) (f g : YoungDiagram → K)
    (h : ∑ ρ ∈ U, f ρ • HJO.Sym.restrictAlphabet (Fin l) K (HJO.Sym.macPfun hqu ρ)
      = ∑ ρ ∈ U, g ρ • HJO.Sym.restrictAlphabet (Fin l) K (HJO.Sym.macPfun hqu ρ)) :
    ∀ ρ ∈ U, f ρ = g ρ := by
  classical
  choose I hI using fun x : {ρ // ρ ∈ U} =>
    exists_partDiagram_eq_of_card (l := l) (D := D) (hcard _ x.2) (hshort _ x.2)
  have hres : ∀ x : {ρ // ρ ∈ U},
      HJO.Sym.restrictAlphabet (Fin l) K (HJO.Sym.macPfun hqu (x : YoungDiagram))
        = (macPpoly hqu (I x) : MvPolynomial (Fin l) K) := by
    intro x
    rw [← hI x]
    exact restrictAlphabet_macPfun_partDiagram_of_pos hqu hl (I x)
  obtain ⟨B, hB⟩ := exists_basis_macPpoly (σ := Fin l) (d := D) (K := K) (q := q) (u := u) hqu
  have hind : LinearIndependent K
      (fun s : PartIdx (Fin l) D => (macPpoly hqu s : MvPolynomial (Fin l) K)) := by
    have h0 : LinearIndependent K (macPpoly hqu :
        PartIdx (Fin l) D → symmetricHomogeneousSubmodule (Fin l) K D) := by
      rw [← hB]; exact B.linearIndependent
    exact h0.map' (Submodule.subtype _) (Submodule.ker_subtype _)
  set V : Finset (PartIdx (Fin l) D) := U.attach.image I with hVdef
  have hinj : Set.InjOn I U.attach := fun x _ y _ hxy =>
    Subtype.ext (by rw [← hI x, ← hI y, hxy])
  have hsum : ∀ F : YoungDiagram → K,
      ∑ s ∈ V, F (partDiagram (Fin l) s) • (macPpoly hqu s : MvPolynomial (Fin l) K)
        = ∑ ρ ∈ U, F ρ • HJO.Sym.restrictAlphabet (Fin l) K (HJO.Sym.macPfun hqu ρ) := by
    intro F
    rw [hVdef, Finset.sum_image hinj, ← Finset.sum_attach U
      (fun ρ => F ρ • HJO.Sym.restrictAlphabet (Fin l) K (HJO.Sym.macPfun hqu ρ))]
    exact Finset.sum_congr rfl fun x _ => by rw [hI x, hres x]
  have hVzero : ∑ s ∈ V, (f (partDiagram (Fin l) s) - g (partDiagram (Fin l) s)) •
      (macPpoly hqu s : MvPolynomial (Fin l) K) = 0 := by
    rw [Finset.sum_congr rfl fun s _ => sub_smul (f (partDiagram (Fin l) s))
      (g (partDiagram (Fin l) s)) _, Finset.sum_sub_distrib, hsum f, hsum g, h, sub_self]
  have heq := linearIndependent_iff'.mp hind V
    (fun s => f (partDiagram (Fin l) s) - g (partDiagram (Fin l) s)) hVzero
  intro ρ hρ
  have hmem : I ⟨ρ, hρ⟩ ∈ V := by
    rw [hVdef]
    exact Finset.mem_image_of_mem _ (Finset.mem_attach _ _)
  have h1 := heq _ hmem
  rw [hI ⟨ρ, hρ⟩] at h1
  exact sub_eq_zero.mp h1

end Wrappers

end HJO.Mac

/-! ### The Pieri support at the standing field -/

namespace HJO.Standing

open HJO.Sym HJO.Mac HJO.Ascent

variable (K : Type*) [Field K] [Algebra ℚ K] [Algebra ParamRing K] [IsFractionRing ParamRing K]

/-- **`HJO.Standing.hasPfunPieriSupport_param` in coordinates**: in an expansion
`e₁P_ν = ∑_{μ ∈ S} c_μ P_μ` with `|μ| = |ν|+1` on `S`, an index with a nonzero coefficient covers
`ν`.

The induction on `|ν|`. `HJO.Ascent.elemSymm_one_mul_macPfun_mem_span_covers_or_short` leaves only
the indices `λ` with `λ_{l+1} = 0`, where `l = ν.colLen 0`; `l = 0` is impossible; and for `l ≥ 1`
the expansion is restricted to `Fin l`, the first column is removed from both sides, the indices
whose first column was not full are killed by `HJO.Mac.eq_zero_of_sum_smul_macPpoly_eq_esymm_mul`,
`x_1 ⋯ x_l` is cancelled in the domain, and what remains is compared with the induction hypothesis
at `ν⁻` in the basis `HJO.Mac.exists_basis_macPpoly`. -/
theorem hasPfunPieriCoeff_param :
    HasPfunPieriCoeff (q := paramQUnit K) (u := paramU K)
      (algebraicIndependent_paramQUnit K) := by
  classical
  suffices H : ∀ (n : ℕ) (ν : YoungDiagram), ν.card = n →
      ∀ (S : Finset YoungDiagram) (c : YoungDiagram → K), (∀ μ ∈ S, μ.card = ν.card + 1) →
      elemSymm K 1 * macPfun (algebraicIndependent_paramQUnit K) ν
        = ∑ μ ∈ S, c μ • macPfun (algebraicIndependent_paramQUnit K) μ →
      ∀ μ ∈ S, c μ ≠ 0 → Covers μ ν by
    intro ν S c hcard hexp μ hμ h0
    exact H ν.card ν rfl S c hcard hexp μ hμ h0
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro ν hn S c hcard hexp lam hlam hc
  rcases covers_or_rowLen_colLen_zero_eq_zero_of_coeff_ne_zero K ν S c hcard hexp hlam hc with
    hcov | hz
  · exact hcov
  set hqu := algebraicIndependent_paramQUnit K with hqudef
  set l := ν.colLen 0 with hldef
  have hcardlam : lam.card = ν.card + 1 := hcard lam hlam
  -- `l = 0` is impossible: it would make `λ` empty
  have hl1 : 1 ≤ l := by
    rcases Nat.eq_zero_or_pos l with h0 | h
    · rw [h0] at hz
      have := card_eq_zero_of_rowLen_zero_eq_zero hz
      omega
    · exact h
  have hνshort : ν.rowLen l = 0 := rowLen_colLen_zero ν
  have hνfull : ∀ k, k < l → ν.rowLen k ≠ 0 := fun k hk =>
    lt_colLen_zero_iff_rowLen_ne_zero.mp hk
  have hνmcard : (dropFirstColumn ν).card + l = ν.card := card_dropFirstColumn hνshort hνfull
  -- the short indices of `S`, split on whether the first column is full
  set S₀ : Finset YoungDiagram := S.filter (fun μ => μ.rowLen l = 0) with hS₀def
  have hS₀ : ∀ ρ, ρ ∈ S₀ ↔ ρ ∈ S ∧ ρ.rowLen l = 0 := fun ρ => by
    rw [hS₀def]; exact Finset.mem_filter
  set S₂ : Finset YoungDiagram := S₀.filter (fun μ => μ.rowLen (l - 1) = 0) with hS₂def
  set S₁ : Finset YoungDiagram := S₀.filter (fun μ => ¬ μ.rowLen (l - 1) = 0) with hS₁def
  have hS₂ : ∀ ρ, ρ ∈ S₂ ↔ ρ ∈ S₀ ∧ ρ.rowLen (l - 1) = 0 := fun ρ => by
    rw [hS₂def]; exact Finset.mem_filter
  have hS₁ : ∀ ρ, ρ ∈ S₁ ↔ ρ ∈ S₀ ∧ ¬ ρ.rowLen (l - 1) = 0 := fun ρ => by
    rw [hS₁def]; exact Finset.mem_filter
  have hsplit : ∀ F : YoungDiagram → MvPolynomial (Fin l) K,
      ∑ ρ ∈ S₀, F ρ = (∑ ρ ∈ S₂, F ρ) + ∑ ρ ∈ S₁, F ρ := fun F => by
    rw [hS₁def, hS₂def]
    exact (Finset.sum_filter_add_sum_filter_not S₀ _ F).symm
  have hfull₁ : ∀ ρ ∈ S₁, ∀ k, k < l → ρ.rowLen k ≠ 0 := by
    intro ρ hρ k hk h0
    exact ((hS₁ ρ).mp hρ).2 (Nat.le_zero.mp (h0 ▸ ρ.rowLen_anti k (l - 1) (by omega)))
  -- the restricted expansion, and the column removal on it
  have hrestr := restrict_expansion (l := l) hqu ν S S₀ c hexp hS₀
  have hcolν := restrictAlphabet_macPfun_eq_prod_X_mul hl1 hqu hνshort hνfull
  have hcol₁ : ∑ ρ ∈ S₁, c ρ • restrictAlphabet (Fin l) K (macPfun hqu ρ)
      = (∏ j : Fin l, X j) *
          ∑ ρ ∈ S₁, c ρ • restrictAlphabet (Fin l) K (macPfun hqu (dropFirstColumn ρ)) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun ρ hρ => ?_
    rw [restrictAlphabet_macPfun_eq_prod_X_mul hl1 hqu ((hS₀ ρ).mp ((hS₁ ρ).mp hρ).1).2
      (hfull₁ ρ hρ)]
    exact (mul_smul_comm (c ρ) _ _).symm
  -- the members whose first column is not full have zero coefficient
  have hA : ∀ ρ ∈ S₂, c ρ = 0 := by
    have hrhs : (∏ j : Fin l, (X j : MvPolynomial (Fin l) K)) *
        (esymm (Fin l) K 1 * restrictAlphabet (Fin l) K (macPfun hqu (dropFirstColumn ν))
          - ∑ ρ ∈ S₁, c ρ • restrictAlphabet (Fin l) K (macPfun hqu (dropFirstColumn ρ)))
        = esymm (Fin l) K 1 * restrictAlphabet (Fin l) K (macPfun hqu ν)
          - ∑ ρ ∈ S₁, c ρ • restrictAlphabet (Fin l) K (macPfun hqu ρ) := by
      rw [mul_sub, ← hcol₁, hcolν]
      ring
    refine eq_zero_of_sum_smul_restrictAlphabet_macPfun_eq_prod_X_mul hl1 hqu S₂ c
      (fun ρ hρ => hcard ρ ((hS₀ ρ).mp ((hS₂ ρ).mp hρ).1).1)
      (fun ρ hρ => ((hS₀ ρ).mp ((hS₂ ρ).mp hρ).1).2) (fun ρ hρ => ((hS₂ ρ).mp hρ).2)
      (g := esymm (Fin l) K 1 * restrictAlphabet (Fin l) K (macPfun hqu (dropFirstColumn ν))
        - ∑ ρ ∈ S₁, c ρ • restrictAlphabet (Fin l) K (macPfun hqu (dropFirstColumn ρ))) ?_
    rw [hrhs, hrestr, hsplit (fun ρ => c ρ • restrictAlphabet (Fin l) K (macPfun hqu ρ))]
    ring
  -- so `x_1 ⋯ x_l` cancels, leaving the divided expansion
  have hB : esymm (Fin l) K 1 * restrictAlphabet (Fin l) K (macPfun hqu (dropFirstColumn ν))
      = ∑ ρ ∈ S₁, c ρ • restrictAlphabet (Fin l) K (macPfun hqu (dropFirstColumn ρ)) := by
    have hprod : (∏ j : Fin l, (X j : MvPolynomial (Fin l) K)) ≠ 0 :=
      Finset.prod_ne_zero_iff.mpr fun j _ => X_ne_zero j
    have hlhs : (∏ j : Fin l, (X j : MvPolynomial (Fin l) K)) *
        (esymm (Fin l) K 1 * restrictAlphabet (Fin l) K (macPfun hqu (dropFirstColumn ν)))
        = esymm (Fin l) K 1 * restrictAlphabet (Fin l) K (macPfun hqu ν) := by
      rw [hcolν]; ring
    have h2 : ∑ ρ ∈ S₂, c ρ • restrictAlphabet (Fin l) K (macPfun hqu ρ) = 0 :=
      Finset.sum_eq_zero fun ρ hρ => by rw [hA ρ hρ, zero_smul]
    refine mul_left_cancel₀ hprod ?_
    rw [hlhs, ← hcol₁, hrestr,
      hsplit (fun ρ => c ρ • restrictAlphabet (Fin l) K (macPfun hqu ρ)), h2, zero_add]
  -- the induction hypothesis at `ν⁻`, restricted the same way
  obtain ⟨T, b, hTcard, hTexp⟩ :=
    exists_expansion_elemSymm_one_mul_macPfun hqu (dropFirstColumn ν)
  have hIH : ∀ ρ ∈ T, b ρ ≠ 0 → Covers ρ (dropFirstColumn ν) :=
    ih (dropFirstColumn ν).card (by omega) (dropFirstColumn ν) rfl T b hTcard hTexp
  set T₀ : Finset YoungDiagram := T.filter (fun ρ => ρ.rowLen l = 0) with hT₀def
  have hT₀ : ∀ ρ, ρ ∈ T₀ ↔ ρ ∈ T ∧ ρ.rowLen l = 0 := fun ρ => by
    rw [hT₀def]; exact Finset.mem_filter
  have hrestr' := restrict_expansion (l := l) hqu (dropFirstColumn ν) T T₀ b hTexp hT₀
  -- one index set for the comparison, both coefficients total in the diagram
  set U : Finset YoungDiagram := S₁.image dropFirstColumn ∪ T₀ with hUdef
  set f : YoungDiagram → K :=
    fun ρ => ∑ μ ∈ S₁, if dropFirstColumn μ = ρ then c μ else 0 with hfdef
  set g : YoungDiagram → K := fun ρ => if ρ ∈ T₀ then b ρ else 0 with hgdef
  have hmemU₁ : ∀ ρ ∈ S₁, dropFirstColumn ρ ∈ U := by
    intro ρ hρ
    rw [hUdef]
    exact Finset.mem_union_left _ (Finset.mem_image_of_mem _ hρ)
  have hT₀U : T₀ ⊆ U := by rw [hUdef]; exact Finset.subset_union_right
  have hUmem : ∀ ρ ∈ U, (∃ μ ∈ S₁, dropFirstColumn μ = ρ) ∨ ρ ∈ T₀ := by
    intro ρ hρ
    rw [hUdef] at hρ
    rcases Finset.mem_union.mp hρ with h | h
    · exact Or.inl (Finset.mem_image.mp h)
    · exact Or.inr h
  have hUcard : ∀ ρ ∈ U, ρ.card = (dropFirstColumn ν).card + 1 := by
    intro ρ hρ
    rcases hUmem ρ hρ with ⟨μ, hμ, rfl⟩ | h
    · have h1 := card_dropFirstColumn ((hS₀ μ).mp ((hS₁ μ).mp hμ).1).2 (hfull₁ μ hμ)
      have h2 := hcard μ ((hS₀ μ).mp ((hS₁ μ).mp hμ).1).1
      omega
    · exact hTcard ρ ((hT₀ ρ).mp h).1
  have hUshort : ∀ ρ ∈ U, ρ.rowLen l = 0 := by
    intro ρ hρ
    rcases hUmem ρ hρ with ⟨μ, hμ, rfl⟩ | h
    · rw [rowLen_dropFirstColumn, ((hS₀ μ).mp ((hS₁ μ).mp hμ).1).2]
    · exact ((hT₀ ρ).mp h).2
  have hfsum : ∑ ρ ∈ U, f ρ • restrictAlphabet (Fin l) K (macPfun hqu ρ)
      = ∑ ρ ∈ S₁, c ρ • restrictAlphabet (Fin l) K (macPfun hqu (dropFirstColumn ρ)) := by
    simp only [hfdef, Finset.sum_smul, ite_smul, zero_smul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun μ hμ => ?_
    rw [Finset.sum_ite_eq U (dropFirstColumn μ)
      (fun ρ => c μ • restrictAlphabet (Fin l) K (macPfun hqu ρ))]
    simp [hmemU₁ μ hμ]
  have hgsum : ∑ ρ ∈ U, g ρ • restrictAlphabet (Fin l) K (macPfun hqu ρ)
      = ∑ ρ ∈ T₀, b ρ • restrictAlphabet (Fin l) K (macPfun hqu ρ) := by
    rw [← Finset.sum_subset hT₀U fun ρ _ hρ => by simp only [hgdef]; simp [hρ]]
    exact Finset.sum_congr rfl fun ρ hρ => by simp only [hgdef]; simp [hρ]
  have hcompare := eq_of_sum_smul_restrictAlphabet_macPfun_eq hl1 hqu U hUcard hUshort f g
    (by rw [hfsum, hgsum, ← hB, hrestr'])
  -- read the comparison at `λ⁻`
  have hlamS₁ : lam ∈ S₁ := by
    refine (hS₁ lam).mpr ⟨(hS₀ lam).mpr ⟨hlam, hz⟩, fun h0 => hc ?_⟩
    exact hA lam ((hS₂ lam).mpr ⟨(hS₀ lam).mpr ⟨hlam, hz⟩, h0⟩)
  have hflam : f (dropFirstColumn lam) = c lam := by
    have hsingle : ∀ μ ∈ S₁, μ ≠ lam →
        (if dropFirstColumn μ = dropFirstColumn lam then c μ else 0) = 0 := by
      intro μ hμ hne
      have hne' : ¬ dropFirstColumn μ = dropFirstColumn lam := fun heq =>
        hne (dropFirstColumn_injOn ((hS₀ μ).mp ((hS₁ μ).mp hμ).1).2 (hfull₁ μ hμ) hz
          (hfull₁ lam hlamS₁) heq)
      simp [hne']
    simp only [hfdef]
    rw [Finset.sum_eq_single_of_mem lam hlamS₁ hsingle]
    simp
  have hglam := hcompare (dropFirstColumn lam) (hmemU₁ lam hlamS₁)
  rw [hflam] at hglam
  simp only [hgdef] at hglam
  have hmemT₀ : dropFirstColumn lam ∈ T₀ := by
    by_contra h0
    simp only [h0, ite_false] at hglam
    exact hc hglam
  simp only [hmemT₀, ite_true] at hglam
  -- `λ⁻ ⋗ ν⁻`, and adding the column back is entrywise
  obtain ⟨hcov, -⟩ := hIH (dropFirstColumn lam) ((hT₀ _).mp hmemT₀).1 (hglam ▸ hc)
  refine ⟨le_iff_rowLen_le.mpr fun i => ?_, hcardlam⟩
  have hi := le_iff_rowLen_le.mp hcov i
  rw [rowLen_dropFirstColumn, rowLen_dropFirstColumn] at hi
  rcases lt_or_ge i l with hlt | hge
  · have h1 := hνfull i hlt
    have h2 := hfull₁ lam hlamS₁ i hlt
    omega
  · have h3 : ν.rowLen i = 0 := Nat.le_zero.mp (hνshort ▸ ν.rowLen_anti l i hge)
    omega

/-- **The one-cell Pieri expansion of Macdonald's `P` is supported on the
covers.** `e₁P_ν` lies in the `𝕜`-span of the `P_μ` with `μ ⋗ ν`, for every partition `ν`.

`HJO.Standing.hasPfunPieriCoeff_param` read through
`HJO.Sym.hasPfunPieriSupport_of_hasPfunPieriCoeff`: expansions in the basis
`HJO.Sym.exists_basis_lambdaComp_macPfun` being unique, the two forms are the same statement.

**This discharges `HJO.Sym.HasPfunPieriSupport`**, the one `Prop`
`HJO.CollinearNarrowed.collinearCommutation_of_pfunPieriSupport` costs. -/
@[hjo "lem_pie_pfun_support"]
theorem hasPfunPieriSupport_param :
    HasPfunPieriSupport (q := paramQUnit K) (u := paramU K)
      (algebraicIndependent_paramQUnit K) :=
  hasPfunPieriSupport_of_hasPfunPieriCoeff _ (hasPfunPieriCoeff_param K)

/-- **The one-cell Pieri expansion of the modified Macdonald family is
supported on the covers.** `e₁H̃_ν` lies in the `𝕜`-span of the `H̃_μ` with `μ ⋗ ν`, for every
partition `ν`.

The proof is one substitution: `HJO.Sym.elemSymm_one_mul_macHtilde_mem_span`
(`HJO/Macdonald/PieriSupport.lean`) carries out the three steps -- `H̃` is `Φ ∘ P` rescaled by one
nonzero scalar per index, `Φ(e₁)` is `e₁` rescaled, and `Φ` respects spans -- given the hypothesis
`hP`, and `HJO.Standing.hasPfunPieriSupport_param` above is that hypothesis.

Every parameter condition is discharged at the standing field: `u ≠ 0` is
`HJO.Standing.paramU_ne_zero` and `u ≠ 1` is `paramU_pow_succ_ne_one` at `k = 0`. Both genuinely
fail at a degenerate corner -- at a root of unity a scalar of the plethystic substitution vanishes
and `H̃_μ` is zero -- which is why the general-field reading of this statement is false and the
library fixes `q, u` as indeterminates instead of quantifying over fields. -/
@[hjo "lem_pie_htilde_support"]
theorem elemSymm_one_mul_macHtilde_mem_span_param (ν : YoungDiagram) :
    elemSymm K 1 * macHtilde (paramUInvHom K) (algebraicIndependent_paramQUnit K) ν
      ∈ Submodule.span K (macHtilde (paramUInvHom K) (algebraicIndependent_paramQUnit K) ''
          {μ : YoungDiagram | Covers μ ν}) :=
  elemSymm_one_mul_macHtilde_mem_span (paramU_ne_zero K)
    (by simpa using paramU_pow_succ_ne_one K 0)
    (algebraicIndependent_paramQUnit K) (hasPfunPieriSupport_param K) ν

end HJO.Standing
