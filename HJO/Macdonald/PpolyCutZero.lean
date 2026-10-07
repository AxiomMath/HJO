/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.Macdonald.CutAlphabet
public import HJO.Macdonald.PieriColumn
public meta import HJO.Attr

/-! # Erasing a variable kills a Macdonald polynomial of full length

`HJO.Mac.killCompl_macPpoly_eq_zero`: for a partition `μ` with `μ_{n+1} ≥ 1` and `μ_{n+2} = 0`,
`cut_n(P_μ[X_{n+1}]) = 0`.

## The route, and where the index conditions live

The argument in one line: `μ` has a full first column, so
`P_μ[X_{n+1}] = x_1 ⋯ x_{n+1} P_λ[X_{n+1}]` by `HJO.Mac.macPpoly_eq_prod_X_mul`, and `cut_n` kills
the factor `x_{n+1}`.

The two index conditions are read off the index *type*. `PartIdx τ D` is the partitions of `D` with
at most `#τ` parts, so the condition `μ_{n+2} = 0` is carried by the type and never appears as a
hypothesis; and the condition `μ_{n+1} ≥ 1` — that `μ` has `n+1 = #τ` nonzero parts — is
`Fintype.card τ ≤ μ.1.parts.card`, the reverse of the inequality the type already provides.

Producing the `λ` of the statement is the only work. Full length says exactly that every entry of
`\bar\mu` is positive (`HJO.Mac.one_le_partExp_of_card_le`: the multiset `partSym τ μ` then meets
every letter), so `\bar\mu - (1,…,1)` is still weakly decreasing, and
`HJO.Mac.exists_partExp_eq` reads an index off it. Its size is `D - #τ`, which is not written down:
the existential carries whatever size the vector's degree is, and `HJO.Mac.macPpoly_eq_prod_X_mul`
derives `|κ| = |λ| + n` itself.

## Generality

The erasure is `MvPolynomial.killCompl hf` for an arbitrary injection `f : σ → τ` together with
*one* letter `t` off its range, as in `HJO/Macdonald/CutAlphabet.lean`; the map `cut_n` is
`σ = Fin n`, `τ = Fin (n + 1)`, `f = Fin.castSucc`, `t = Fin.last n`. Nothing asks the two alphabets
to differ by one letter, nor `σ` to be nonempty, so a hypothesis `n ≥ 1` is absent. Note that some
such `t` is *needed*: for a bijective `f` the map `killCompl hf` is an isomorphism and `P_μ[X_τ]` is
nonzero.

The field and the genericity hypothesis are exactly those needed to name `P_μ[X_τ]`
(`HJO.Mac.macPpoly`); no further arithmetic in `q` and `u` is spent here,
`HJO.Mac.macPpoly_eq_prod_X_mul` being applied as it stands.

## Main results

* `HJO.Mac.one_le_partExp_of_card_le`: an index of full length has every entry of its exponent
  vector positive.
* `HJO.Mac.exists_partExp_eq_onesExp_add_of_card_le`: an index of full length is a full first
  column plus an index, the converse of `HJO.Mac.exists_partExp_eq_onesExp_add`.
* `HJO.Mac.killCompl_macPpoly_eq_zero`.

## References

The file proves `HJO.Mac.killCompl_macPpoly_eq_zero`, on `HJO.Sym.rowLenSeq` and
`HJO.Mac.macPpoly`, from `MvPolynomial.eq_killCompl_castSucc_iff`,
`HJO.Sym.restrictAlphabet_elemSymm` and `HJO.Mac.macPpoly_eq_prod_X_mul`. The consumer is
`HJO.Mac.restrictAlphabet_macPfun_eq_zero`.
-/

@[expose] public section

open Finset MvPolynomial

namespace HJO.Mac

variable {σ τ : Type*} [LinearOrder τ] [Fintype τ] {K : Type*} [Field K] [Algebra ℚ K] {q : Kˣ}
  {u : K} {D : ℕ}

/-- **An index of full length has every entry of its exponent vector positive.** If `μ` has `#τ`
parts then the multiset `partSym τ μ` representing it has `#τ` distinct elements, hence meets every
letter, and `\bar\mu i` is the multiplicity of `i` in it. This is the argument "`μ` is weakly
decreasing with `μ_l ≥ 1`, so `μ_i ≥ 1` for every `i ≤ l`", read without the weak decrease: full
length is the same information. -/
theorem one_le_partExp_of_card_le (μ : PartIdx τ D) (hμ : Fintype.card τ ≤ μ.1.parts.card)
    (i : τ) : 1 ≤ partExp τ μ i := by
  classical
  have hpc : μ.1.parts.card = (partSym τ μ).1.toFinset.card := by
    rw [← ofSym_partSym μ, Nat.Partition.parts_ofSym, Multiset.card_map, Multiset.card_toFinset]
  have hcard : (partSym τ μ).1.toFinset.card = Fintype.card τ :=
    le_antisymm ((Finset.card_le_univ _).trans_eq Finset.card_univ) (hpc ▸ hμ)
  have hmem : i ∈ (partSym τ μ).1 :=
    Multiset.mem_toFinset.mp (Finset.eq_univ_of_card _ hcard ▸ Finset.mem_univ i)
  rw [partExp, Multiset.toFinsupp_apply]
  exact Multiset.one_le_count_iff_mem.mpr hmem

/-- **An index of full length is a full first column plus an index.** The converse of
`HJO.Mac.exists_partExp_eq_onesExp_add`: subtracting one from every entry of `\bar\mu` leaves a
weakly decreasing vector, because every entry was positive, and
`HJO.Mac.exists_partExp_eq` turns that vector back into an index. The size is whatever the
vector's degree is, namely `D - #τ`. -/
theorem exists_partExp_eq_onesExp_add_of_card_le (μ : PartIdx τ D)
    (hμ : Fintype.card τ ≤ μ.1.parts.card) :
    ∃ (e : ℕ) (lam : PartIdx τ e), partExp τ μ = onesExp τ + partExp τ lam := by
  have hsub : ∀ i : τ, (partExp τ μ - onesExp τ) i = partExp τ μ i - 1 := fun i => by
    rw [Finsupp.tsub_apply, onesExp_apply]
  have hanti : Antitone (partExp τ μ - onesExp τ : τ →₀ ℕ) := fun i j hij => by
    rw [hsub, hsub]
    exact Nat.sub_le_sub_right (antitone_partExp μ hij) 1
  obtain ⟨lam, hlam⟩ := exists_partExp_eq hanti (D := (partExp τ μ - onesExp τ).degree) rfl
  refine ⟨_, lam, Finsupp.ext fun i => ?_⟩
  have h1 := one_le_partExp_of_card_le μ hμ i
  rw [Finsupp.add_apply, onesExp_apply, hlam, hsub]
  omega

/-- **Erasing a variable kills a Macdonald polynomial of full length.**
If `μ` has as many nonzero parts as the alphabet `τ` has letters — the condition `μ_{n+1} ≥ 1` —
then `killCompl hf` carries `P_μ[X_τ]` to `0`, for any injection `f : σ → τ` missing a letter `t`.

By `HJO.Mac.exists_partExp_eq_onesExp_add_of_card_le` the index is a full first column over some
`λ`, so `HJO.Mac.macPpoly_eq_prod_X_mul` writes `P_μ[X_τ] = (∏_{j ∈ τ} x_j) P_λ[X_τ]`; the factor
`x_t` of that product is erased. -/
@[hjo "lem_pie_ppoly_cut_zero"]
theorem killCompl_macPpoly_eq_zero (hqu : AlgebraicIndependent ℤ ![(q : K), u])
    {μ : PartIdx τ D} (hμ : Fintype.card τ ≤ μ.1.parts.card) {f : σ → τ}
    (hf : Function.Injective f) {t : τ} (ht : t ∉ Set.range f) :
    killCompl (R := K) hf (macPpoly hqu μ : MvPolynomial τ K) = 0 := by
  obtain ⟨e, lam, hlam⟩ := exists_partExp_eq_onesExp_add_of_card_le μ hμ
  rw [macPpoly_eq_prod_X_mul hqu hlam, map_mul, map_prod,
    Finset.prod_eq_zero (Finset.mem_univ t) (killCompl_X_eq_zero hf ht), zero_mul]

end HJO.Mac
