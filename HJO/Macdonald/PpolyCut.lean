/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.Macdonald.DopCut
public import HJO.Macdonald.HtildeSpan
public import HJO.Macdonald.PieriColumn
public meta import HJO.Attr

/-! # Macdonald's polynomials are stable under erasing a variable

The last three steps of the alphabet descent: `HJO.Mac.killComplComp_macPpoly`, and the two
restriction statements it unlocks, `HJO.Mac.restrictAlphabet_macPfun_partDiagram` and
`HJO.Mac.restrictAlphabet_macPfun_partDiagram_of_pos`.

`HJO.Mac.killComplComp_macPpoly` is `cut_n(P_μ[X_{n+1}]) = P_μ[X_n]` for a partition `μ` with
`μ_{n+1} = 0`, and the route is `HJO.Mac.eq_macPpoly`: exhibit the two conditions of
`HJO.Mac.macPpoly` on `g := cut_n(P_μ[X_{n+1}])` and appeal to uniqueness rather than compute. The
eigenvalue condition is `HJO.Mac.killComplComp_macOpComp` plus `E_{n+1}(μ) = u E_n(μ) + 1`; the
shape condition is the transport of the exponent vectors and of the lexicographic order across the
alphabets.

`HJO.Mac.restrictAlphabet_macPfun_partDiagram` and
`HJO.Mac.restrictAlphabet_macPfun_partDiagram_of_pos` then say `res_n(P_μ) = P_μ[X_n]`, the first
for `n ≥ max(|μ|, 1)` and the second whenever `μ_{n+1} = 0` and `n ≥ 1`. Both are the same descent:
upward from the base alphabet `X_{n_μ}` of `HJO.Sym.macPfun` through
`MvPolynomial.killComplComp_bijective`, downward from it through `HJO.Mac.killComplComp_macPpoly`
alone.

## `MvPolynomial.killCompl_msymm` is routed around, not needed

One proof of the shape condition transports the monomial symmetric basis: `cut_n` sends
`m_ν[X_{n+1}]` to `m_ν[X_n]` when `ν_{n+1} = 0` and to `0` otherwise
(`MvPolynomial.killCompl_msymm`). That fact is **not** proved here and is not used. Instead the
shape condition is read as *coefficient data*: `HJO.Mac.sub_msymm_mem_span_lowerMsymmSet` says that
prescribing the coefficients at the exponents `\bar\nu` outside the lower set prescribes an element
of `𝒮_{n,d}` modulo that set, and `coeff_partExp_macPpoly_of_not_lt` below is its converse at
`P_μ[X_n]`. Coefficients transport along `cut_n` for free (`MvPolynomial.coeff_killCompl`), so the
two directions compose and no monomial symmetric polynomial is ever pushed across the alphabets.

This is a deliberate choice: `MvPolynomial.killCompl_msymm` is the natural route to
`HJO.Mac.killComplComp_macPpoly`, but it is *avoidable*. It has no consumer in the Lean
library at all -- `MvPolynomial.killComplComp_bijective`
(`HJO/Macdonald/CutRestrict.lean`) also routes around it, through
`HJO.Sym.killCompl_restrictAlphabet` and `HJO.Sym.restrictAlphabetComp_bijective` -- so the descent
costs three steps rather than four.

## Genericity: `u ≠ 0`, once, and it costs the statements nothing

`HJO.Mac.killComplComp_macOpComp` spends no genericity (see `HJO/Macdonald/DopCut.lean`). The
`u ≠ 0` of this descent is spent **here**, in exactly one step: `HJO.Mac.killComplComp_macOpComp`
delivers `u D^{(n)}_1 g + g = E_{n+1}(μ) g = u E_n(μ) g + g`, and cancelling `u` from
`u D^{(n)}_1 g = u E_n(μ) g` is the whole of it. This matches the standard proof, which
spends it in the same place.

It costs the statements nothing. `HJO.Mac.macPpoly` takes `AlgebraicIndependent ℤ ![q, u]` as an
argument -- without it there is no `P_μ[X_n]` to speak of, uniqueness failing at `q = u = -1` and
existence on `qu = 1` (see `HJO/Macdonald/Ppoly.lean`) -- so `u ≠ 0` is available from
`HJO.Standing.u_ne_zero` and no statement here carries a hypothesis beyond the ones needed to name
`P_μ`. In particular the cancellation is *not* removable: at `u = 0` the identity of
`HJO.Mac.killComplComp_macOpComp` degenerates to `cut_n(D^{(n+1)}_1 f) = cut_n f`, which says
nothing about `D^{(n)}_1 g`, and `HJO.Mac.existsUnique_isMonicEigen` has already failed there.

The other degenerate corners, at which the general-field readings of several statements of this
library fail, do no harm: `q = 0` and `u = 1` are harmless here (nothing divides by `q` or by
`1 - u`), and `qu = 1` and the roots of unity enter only through `macPpoly`'s own hypothesis.

## Generality: one new largest letter, as in `HJO.Mac.killComplComp_macOpComp`

Everything runs on `HJO.Mac.IsTopExtension`, the datum of `HJO/Macdonald/DopCut.lean`: `e`
embeds the small alphabet in the large one in an order-preserving way and `t` is the one new letter,
above every old one. The instance is `HJO.Mac.isTopExtension_castSucc`. No
`n ≥ 1` is needed in `HJO.Mac.killComplComp_macPpoly`: `σ` may be empty. It is present in the two
restriction statements, where `res_0` is not a bijection onto anything.

## Main definitions

* `HJO.Mac.upIdx`: an index of the monomial symmetric basis read in a larger alphabet -- the
  passage from `μ_{n+1} = 0` to `μ_{n+2} = 0`.
* `HJO.Mac.finIdx`: a partition of `d` read as an index in the alphabet `X_n`.

## Main results

* `HJO.Mac.partExp_upIdx`, `HJO.Mac.toLex_mapDomain_lt_iff`: the two transports -- the exponent
  vector `\bar\mu` is the same in both alphabets, and lexicographic comparisons are preserved *and
  reflected* by the alphabet extension.
* `HJO.Mac.partDiagram_upIdx`, `HJO.Mac.partDiagram_finIdx`: the Young diagram of an index does not
  change with the alphabet, which is what makes `P_μ` -- indexed by a diagram -- a well-posed target
  for the descent, and what makes the eigenvalue relation Horner's rule.
* `HJO.Mac.macdonaldEigenvalue_upIdx`: `E_{n+1}(μ) = u E_n(μ) + 1`.
* `HJO.Mac.coeff_partExp_macPpoly_of_not_lt`: the converse of
  `HJO.Mac.sub_msymm_mem_span_lowerMsymmSet` at `P_μ[X_n]`.
* `HJO.Mac.killComplComp_macPpoly`, `HJO.Mac.killComplComp_macPpoly_castSucc`:
  **`HJO.Mac.killComplComp_macPpoly`**, in general and at the alphabets `X_n`.
* `HJO.Mac.restrictAlphabet_macPfun_partDiagram`
  (**`HJO.Mac.restrictAlphabet_macPfun_partDiagram`**),
  `HJO.Mac.restrictAlphabet_macPfun_partDiagram_of_pos`
  (**`HJO.Mac.restrictAlphabet_macPfun_partDiagram_of_pos`**).

## Remarks on the statements

* `HJO.Mac.killComplComp_macPpoly` depends on `HJO.Mac.exists_eq_macOp_algebraMap`, which the
  *statement* of `HJO.Mac.killComplComp_macOpComp` needs and hence so does this one. No `n ≥ 1` is
  needed.
* `HJO.Mac.restrictAlphabet_macPfun_partDiagram` and
  `HJO.Mac.restrictAlphabet_macPfun_partDiagram_of_pos` have the *same conclusion*, and the
  hypotheses of the first (`n ≥ |μ|`, `n ≥ 1`) imply those of the second (`μ_{n+1} = 0`, `n ≥ 1`) --
  a partition of `d` having at most `d` parts. So `HJO.Mac.restrictAlphabet_macPfun_partDiagram` is
  a special case of `HJO.Mac.restrictAlphabet_macPfun_partDiagram_of_pos`, while
  `HJO.Mac.restrictAlphabet_macPfun_partDiagram_of_pos`'s own proof takes
  `HJO.Mac.restrictAlphabet_macPfun_partDiagram` as the base of a descent. The two lemmas are one
  theorem stated twice; both are proved here, the weaker one first because it is what the induction
  actually needs.
* The proof of `HJO.Mac.restrictAlphabet_macPfun_partDiagram` also uses
  `HJO.Sym.restrictAlphabetComp_bijective`, which `HJO.Sym.macPfun` needs to be a definition at all.

## References

This file formalises the stability of Macdonald's polynomials `HJO.Mac.macPpoly` and
`HJO.Sym.macPfun` under erasing a variable: `HJO.Mac.killComplComp_macPpoly`,
`HJO.Mac.restrictAlphabet_macPfun_partDiagram` and
`HJO.Mac.restrictAlphabet_macPfun_partDiagram_of_pos`.
-/

@[expose] public section

open Finset MvPolynomial

namespace HJO.Mac

/-! ### Lifting an index along an alphabet extension -/

section Idx

variable {σ τ : Type*} [Fintype σ] [Fintype τ] {d : ℕ}

/-- An index of the monomial symmetric basis read in a larger alphabet: the passage from
a partition `μ` with `μ_{n+1} = 0` to the same partition read with `μ_{n+2} = 0`, which is the one
step the statement of `HJO.Mac.killComplComp_macPpoly` needs. Only the bound on the number of parts
changes. -/
def upIdx (hle : Fintype.card σ ≤ Fintype.card τ) (ν : PartIdx σ d) : PartIdx τ d :=
  ⟨ν.1, ν.2.trans hle⟩

@[simp]
theorem upIdx_val (hle : Fintype.card σ ≤ Fintype.card τ) (ν : PartIdx σ d) :
    (upIdx hle ν).1 = ν.1 := rfl

/-- Reading an index in a larger alphabet loses nothing: the underlying partition is unchanged. -/
theorem upIdx_inj (hle : Fintype.card σ ≤ Fintype.card τ) {ν ρ : PartIdx σ d} :
    upIdx hle ν = upIdx hle ρ ↔ ν = ρ := by
  rw [Subtype.ext_iff, Subtype.ext_iff, upIdx_val, upIdx_val]

end Idx

/-! ### What one new largest letter does to the order-theoretic data

`HJO.Mac.IsTopExtension` is the datum of `HJO/Macdonald/DopCut.lean`: `e` embeds the small
alphabet in the large one in an order-preserving way and `t` is the one new letter, above every old
one. Two things it does not record are wanted here: that the large alphabet has one letter more, and
that pushing an exponent vector forward keeps it weakly decreasing, which needs the new letter to be
the *top* and to carry the exponent `0`.
-/

namespace IsTopExtension

variable {σ τ : Type*} [LinearOrder σ] [LinearOrder τ] {e : σ → τ} {t : τ}
  (hd : IsTopExtension e t)

include hd

/-- **Pushing a weakly decreasing exponent vector into the large alphabet leaves it weakly
decreasing**: the new letter is the largest and carries the exponent `0`. This is the
condition `μ_{n+2} = 0`. -/
theorem antitone_mapDomain {α : σ →₀ ℕ} (hα : Antitone α) : Antitone (Finsupp.mapDomain e α) := by
  intro b c hbc
  rcases eq_or_ne c t with rfl | hct
  · rw [Finsupp.mapDomain_of_notMem_range _ _ hd.notMem_range]
    exact Nat.zero_le _
  · obtain ⟨a₂, rfl⟩ := hd.exists_eq hct
    obtain ⟨a₁, rfl⟩ := hd.exists_eq fun h => absurd (h ▸ hbc) (not_le.2 (hd.lt_top a₂))
    rw [Finsupp.mapDomain_apply hd.injective, Finsupp.mapDomain_apply hd.injective]
    exact hα (hd.strictMono.le_iff_le.1 hbc)

variable [Fintype σ] [Fintype τ]

/-- The large alphabet has one letter more than the small one. -/
theorem card_eq : Fintype.card τ = Fintype.card σ + 1 := by
  classical
  rw [← Finset.card_univ, hd.univ_eq, Finset.card_insert_of_notMem (hd.notMem_image _),
    Finset.card_image_of_injective _ hd.injective, Finset.card_univ]

/-- The small alphabet is no larger than the big one, which is what lets an index be read in
either. -/
theorem card_le : Fintype.card σ ≤ Fintype.card τ :=
  Fintype.card_le_of_injective e hd.injective

end IsTopExtension

/-! ### The exponent vector of an index in the large alphabet -/

section PartExp

variable {σ τ : Type*} [Fintype σ] [Fintype τ] [DecidableEq σ] [DecidableEq τ] {d : ℕ}

omit [Fintype σ] [Fintype τ] in
/-- **An injection of alphabets does not change a multiplicity partition**: it matches the letters
occurring in a multiset one for one, so the multiset of multiplicities is the same.
`Nat.Partition.ofSym_map` is this for a bijection, and its proof uses only injectivity. -/
theorem ofSym_map_of_injective {f : σ → τ} (hf : Function.Injective f) (a : Sym σ d) :
    Nat.Partition.ofSym (a.map f) = Nat.Partition.ofSym a := by
  refine Nat.Partition.ext ?_
  change (a.1.map f).dedup.map (a.1.map f).count = a.1.dedup.map a.1.count
  rw [Multiset.dedup_map_of_injective hf, Multiset.map_map]
  exact Multiset.map_congr rfl fun i _ => Multiset.count_map_eq_count' f _ hf i

variable {e : σ → τ} {t : τ} [LinearOrder σ] [LinearOrder τ]

/-- **The exponent vector of an index is unchanged by the alphabet extension**: `\bar\mu` read in
`x_1, …, x_{n+1}` is `\bar\mu` read in `x_1, …, x_n` with a final `0`.

`HJO.Mac.eq_partExp` says the weakly decreasing representative of the orbit is unique, so the choice
made in the definition of `HJO.Mac.partExp` is not a choice and the two alphabets cannot disagree.
This is the first of the two transports that carry the shape condition of `HJO.Mac.macPpoly` across
the alphabets. -/
theorem partExp_upIdx (hd : IsTopExtension e t) (ν : PartIdx σ d) :
    partExp τ (upIdx hd.card_le ν) = Finsupp.mapDomain e (partExp σ ν) := by
  refine (eq_partExp (a := (partSym σ ν).map e) ?_ ?_).symm.trans ?_
  · rw [ofSym_map_of_injective hd.injective, ofSym_partSym, upIdx_val]
  · change Antitone ((Multiset.toFinsupp ((partSym σ ν).1.map e) : τ →₀ ℕ) : τ → ℕ)
    rw [Multiset.toFinsupp_map]
    exact hd.antitone_mapDomain (antitone_partExp ν)
  · change (Multiset.toFinsupp ((partSym σ ν).1.map e) : τ →₀ ℕ) = _
    rw [Multiset.toFinsupp_map]
    rfl

end PartExp

/-! ### The lexicographic order is transported by the alphabet extension -/

section Lex

variable {σ τ : Type*} [LinearOrder σ] [LinearOrder τ] {e : σ → τ}

/-- Pushing exponent vectors forward along an order embedding preserves lexicographic
comparisons. -/
theorem toLex_mapDomain_lt (he : StrictMono e) {α β : σ →₀ ℕ} (h : toLex α < toLex β) :
    toLex (Finsupp.mapDomain e α) < toLex (Finsupp.mapDomain e β) := by
  obtain ⟨a, hagree, hlt⟩ := Finsupp.Lex.lt_iff.mp h
  refine Finsupp.Lex.lt_iff.mpr ⟨e a, fun b hb => ?_, ?_⟩
  · by_cases hbr : b ∈ Set.range e
    · obtain ⟨c, rfl⟩ := hbr
      simp only [ofLex_toLex, Finsupp.mapDomain_apply he.injective]
      simpa using hagree c (he.lt_iff_lt.mp hb)
    · simp only [ofLex_toLex, Finsupp.mapDomain_of_notMem_range _ _ hbr]
  · simp only [ofLex_toLex, Finsupp.mapDomain_apply he.injective]
    simpa using hlt

/-- **Lexicographic comparisons are reflected by the alphabet extension.** Two exponent vectors of
the small alphabet compare in the large alphabet exactly as they do in the small one: off the image
of `e` both pushforwards vanish, so the least index at which they differ is in the image, and `e`
matches the indices below it with the indices below its preimage.

This is the second of the two transports, and it is what turns the observation "the least index at
which `\bar\nu` and `\bar\mu` differ is at most `n`, both having last entry `0`" into a statement
about the order rather than about entries. -/
theorem toLex_mapDomain_lt_iff (he : StrictMono e) {α β : σ →₀ ℕ} :
    toLex (Finsupp.mapDomain e α) < toLex (Finsupp.mapDomain e β) ↔ toLex α < toLex β := by
  refine ⟨fun h => ?_, toLex_mapDomain_lt he⟩
  obtain ⟨b, hagree, hlt⟩ := Finsupp.Lex.lt_iff.mp h
  obtain ⟨a, rfl⟩ : b ∈ Set.range e := by
    by_contra hnr
    simp only [ofLex_toLex, Finsupp.mapDomain_of_notMem_range _ _ hnr] at hlt
    exact absurd hlt (lt_irrefl _)
  refine Finsupp.Lex.lt_iff.mpr ⟨a, fun c hc => ?_, ?_⟩
  · have hce := hagree (e c) (he hc)
    simp only [ofLex_toLex, Finsupp.mapDomain_apply he.injective] at hce
    simpa using hce
  · simp only [ofLex_toLex, Finsupp.mapDomain_apply he.injective] at hlt
    simpa using hlt

end Lex

/-! ### The diagram of an index does not change with the alphabet

The diagram of `μ` is read off the increasing listing of the alphabet (`HJO.Mac.rowLenSeqOf`), so
comparing the diagrams in the two alphabets means comparing the two listings. The position of a
letter in the listing is the number of letters below it, and
`HJO.Mac.IsTopExtension.card_filter_lt` says that count is the same in both alphabets; the new
letter, having every old one below it, is listed last.

This is what makes the eigenvalue relation Horner's rule, and it is what makes `P_μ`
-- indexed by a Young diagram, not by an index in an alphabet -- a well-posed target for the
descent.
-/

section Letters

variable {σ τ : Type*} [Fintype σ] [LinearOrder σ] [Fintype τ] [LinearOrder τ] {e : σ → τ} {t : τ}
  {d : ℕ}

/-- **The position of a letter in the increasing listing of the alphabet is the number of letters
below it.** The companion of `HJO.Mac.card_filter_lt`, which counts the letters above. -/
theorem coe_symm_letterEquiv (i : σ) :
    ((letterEquiv σ).symm i : ℕ) = #{j ∈ (univ : Finset σ) | j < i} := by
  rw [← Fin.card_Iio ((letterEquiv σ).symm i)]
  refine (Finset.card_equiv (letterEquiv σ).symm.toEquiv fun j => ?_).symm
  simp [Finset.mem_Iio, OrderIso.lt_iff_lt]

/-- **The new letter sits last in the increasing listing of the large alphabet**: every old letter
is below it. -/
theorem IsTopExtension.letterEquiv_card (hd : IsTopExtension e t)
    (h : Fintype.card σ < Fintype.card τ) : letterEquiv τ ⟨Fintype.card σ, h⟩ = t := by
  have h1 : (letterEquiv τ).symm t = ⟨Fintype.card σ, h⟩ :=
    Fin.ext (by rw [coe_symm_letterEquiv, hd.card_filter_lt_top])
  rw [← h1, OrderIso.apply_symm_apply]

/-- **An old letter sits in the same position in both increasing listings**: the new letter is above
it, so it does not change the count of the letters below. -/
theorem IsTopExtension.letterEquiv_of_lt (hd : IsTopExtension e t) {k : ℕ}
    (hk : k < Fintype.card σ) (hk' : k < Fintype.card τ) :
    letterEquiv τ ⟨k, hk'⟩ = e (letterEquiv σ ⟨k, hk⟩) := by
  have h1 : (letterEquiv τ).symm (e (letterEquiv σ ⟨k, hk⟩)) = ⟨k, hk'⟩ := by
    refine Fin.ext ?_
    rw [coe_symm_letterEquiv, hd.card_filter_lt, ← coe_symm_letterEquiv,
      OrderIso.symm_apply_apply]
  rw [← h1, OrderIso.apply_symm_apply]

/-- **The row-length sequence of an index does not change with the alphabet**: the old letters keep
their positions and the new one, carrying the exponent `0`, contributes an empty row. -/
theorem rowLenSeqOf_partExp_upIdx (hd : IsTopExtension e t) (ν : PartIdx σ d) (k : ℕ) :
    rowLenSeqOf τ (partExp τ (upIdx hd.card_le ν)) k = rowLenSeqOf σ (partExp σ ν) k := by
  rw [partExp_upIdx hd]
  rcases Nat.lt_or_ge k (Fintype.card σ) with hk | hk
  · rw [rowLenSeqOf_of_lt (lt_of_lt_of_le hk hd.card_le), rowLenSeqOf_of_lt hk,
      hd.letterEquiv_of_lt hk, Finsupp.mapDomain_apply hd.injective]
  · rw [rowLenSeqOf_of_le hk]
    rcases Nat.lt_or_ge k (Fintype.card τ) with hk2 | hk2
    · have hkeq : k = Fintype.card σ := by
        have := hd.card_eq
        omega
      subst hkeq
      rw [rowLenSeqOf_of_lt hk2, hd.letterEquiv_card hk2,
        Finsupp.mapDomain_of_notMem_range _ _ hd.notMem_range]
    · rw [rowLenSeqOf_of_le hk2]

/-- **The diagram of an index does not change with the alphabet.** This is what makes
`P_μ`, indexed by a Young diagram, a well-posed target for the descent: the diagram
named at `x_1, …, x_{n+1}` is the one named at `x_1, …, x_n`. -/
theorem partDiagram_upIdx (hd : IsTopExtension e t) (ν : PartIdx σ d) :
    partDiagram τ (upIdx hd.card_le ν) = partDiagram σ ν :=
  YoungDiagram.ext (Finset.ext fun c => by
    rw [YoungDiagram.mem_cells c, YoungDiagram.mem_cells c, YoungDiagram.mem_iff_lt_rowLen,
      YoungDiagram.mem_iff_lt_rowLen, rowLen_partDiagram, rowLen_partDiagram,
      rowLenSeqOf_partExp_upIdx hd])

end Letters

/-! ### The eigenvalue in the large alphabet -/

section Eigenvalue

variable {σ τ : Type*} [LinearOrder σ] [Fintype σ] [LinearOrder τ] [Fintype τ] {e : σ → τ}
  {t : τ} {d : ℕ}

/-- **`E_{n+1}(μ) = u E_n(μ) + 1`.** The diagram of `μ` is the same in both alphabets
(`partDiagram_upIdx`) and the large alphabet has one letter more (`IsTopExtension.card_eq`), so this
is Horner's rule in the size of the alphabet (`HJO.Sym.macdonaldEigenvalue_succ`) together with the
hypothesis `μ_{n+1} = 0`, which the index type carries
(`HJO.Mac.rowLen_partDiagram_card`) and which makes the new letter's term `q^0 = 1`. -/
theorem macdonaldEigenvalue_upIdx (hd : IsTopExtension e t) {K : Type*} [CommSemiring K] (q u : K)
    (ν : PartIdx σ d) :
    HJO.Sym.macdonaldEigenvalue q u (Fintype.card τ) (partDiagram τ (upIdx hd.card_le ν))
      = u * HJO.Sym.macdonaldEigenvalue q u (Fintype.card σ) (partDiagram σ ν) + 1 := by
  rw [hd.card_eq, partDiagram_upIdx hd, HJO.Sym.macdonaldEigenvalue_succ,
    rowLen_partDiagram_card, pow_zero, mul_comm]

end Eigenvalue

/-! ### `HJO.Mac.killComplComp_macPpoly` -/

section Main

variable {σ τ : Type*} [LinearOrder σ] [Fintype σ] [LinearOrder τ] [Fintype τ]
  {K : Type*} [Field K] [Algebra ℚ K] {q : Kˣ} {u : K} {d : ℕ} {e : σ → τ} {t : τ}

/-- **The coefficients of `P_μ[X_n]` at the exponents `\bar\nu` outside the lower set**: `1` at
`\bar\mu` and `0` above it.

This is the converse of `HJO.Mac.sub_msymm_mem_span_lowerMsymmSet`, read at `P_μ[X_n]`: the shape
condition of `HJO.Mac.macPpoly` is *equivalent* to this coefficient data, so it can be transported
across an alphabet extension coefficient by coefficient. It is what lets
`HJO.Mac.killComplComp_macPpoly` avoid `MvPolynomial.killCompl_msymm`: the monomial symmetric basis
is never transported, only read. -/
theorem coeff_partExp_macPpoly_of_not_lt (hqu : AlgebraicIndependent ℤ ![(q : K), u])
    {μ ν : PartIdx σ d} (hν : ¬ toLex (partExp σ ν) < toLex (partExp σ μ)) :
    coeff (partExp σ ν) (macPpoly hqu μ : MvPolynomial σ K) = if ν = μ then 1 else 0 := by
  rcases eq_or_ne ν μ with rfl | hne
  · rw [ite_eq_left rfl, coeff_partExp_macPpoly]
  · rw [ite_eq_right hne]
    have hlt : toLex (partExp σ μ) < toLex (partExp σ ν) :=
      lt_of_le_of_ne (not_lt.mp hν) fun h => hne (partExp_injective (toLex.injective h)).symm
    by_contra hc
    exact absurd (lt_of_lt_of_le hlt (toLex_le_of_mem_support_macPpoly hqu μ
      (mem_support_iff.mpr hc))) (lt_irrefl _)

/-- **Erasing the new variable carries `P_μ[X_{n+1}]` to `P_μ[X_n]`.** For an
index `μ` of the monomial symmetric basis of `𝒮_{n,d}` -- the partition of `d` with
`μ_{n+1} = 0`, read in the larger alphabet by `HJO.Mac.upIdx` -- `cut_n(P_μ[X_{n+1}]) = P_μ[X_n]`.

`HJO.Mac.eq_macPpoly` asks for the two conditions of `HJO.Mac.macPpoly` on
`g := cut_n(P_μ[X_{n+1}])`.

* The eigenvalue. `HJO.Mac.killComplComp_macOpComp` gives
  `u D^{(n)}_1 g + g = cut_n(D^{(n+1)}_1P_μ[X_{n+1}])`, which is `E_{n+1}(μ) g = (u E_n(μ) + 1) g`
  by `macdonaldEigenvalue_upIdx`; cancelling `g` off the `+ g` and then `u` leaves
  `D^{(n)}_1 g = E_n(μ) g`. **This cancellation is the one place any genericity is spent in this
  proof**, and what it spends is `u ≠ 0` (`HJO.Standing.u_ne_zero`) -- the `u ≠ 0` that
  `HJO.Mac.killComplComp_macOpComp` does *not* spend. It costs the statement nothing: `hqu` is
  already an argument of `HJO.Mac.macPpoly`, so the statement carries no hypothesis beyond the ones
  needed to name `P_μ` at all.
* The shape. The coefficient of `x^{\bar\nu}` in `cut_n f` is the coefficient of
  `x^{\bar\nu + 0}` in `f` (`MvPolynomial.coeff_killCompl`), the exponent vectors transport
  (`partExp_upIdx`) and so do the lexicographic comparisons (`toLex_mapDomain_lt_iff`), so
  `coeff_partExp_macPpoly_of_not_lt` in the large alphabet gives the coefficient data in the small
  one, and `HJO.Mac.sub_msymm_mem_span_lowerMsymmSet` turns that back into the span condition.
  `MvPolynomial.killCompl_msymm` is thereby avoided: nothing here computes `cut_n(m_μ[X_{n+1}])`. -/
@[hjo "lem_mac_ppoly_cut"]
theorem killComplComp_macPpoly (hd : IsTopExtension e t)
    (hqu : AlgebraicIndependent ℤ ![(q : K), u]) (ν : PartIdx σ d) :
    killComplComp hd.injective K d (macPpoly hqu (upIdx hd.card_le ν)) = macPpoly hqu ν := by
  classical
  set P := macPpoly hqu (upIdx hd.card_le ν) with hP
  set g := killComplComp hd.injective K d P with hg
  refine eq_macPpoly hqu ⟨?_, ?_⟩
  · have h1 : killComplComp hd.injective K d (macOpComp q u d P)
        = u • macOpComp q u d g + g := killComplComp_macOpComp hd q u d P
    rw [macOpComp_macPpoly, map_smul, macdonaldEigenvalue_upIdx hd, add_smul, one_smul,
      add_left_inj, ← smul_smul] at h1
    exact (smul_right_injective _ (HJO.Standing.u_ne_zero hqu) h1).symm
  · refine sub_msymm_mem_span_lowerMsymmSet g.2 fun ρ hρ => ?_
    have hup : ¬ toLex (partExp τ (upIdx hd.card_le ρ))
        < toLex (partExp τ (upIdx hd.card_le ν)) := by
      rw [partExp_upIdx hd, partExp_upIdx hd, toLex_mapDomain_lt_iff hd.strictMono]
      exact hρ
    rw [hg, coe_killComplComp, coeff_killCompl, ← partExp_upIdx hd, hP,
      coeff_partExp_macPpoly_of_not_lt hqu hup]
    exact if_congr (upIdx_inj hd.card_le) rfl rfl

/-- **`HJO.Mac.killComplComp_macPpoly` at the alphabets `X_n`**: with `cut_n` the erasure of
`x_{n+1}` from `𝕜[x_1, …, x_{n+1}]`, `cut_n(P_μ[X_{n+1}]) = P_μ[X_n]` for every index `μ` of the
monomial symmetric basis of `𝒮_{n,d}`. -/
theorem killComplComp_macPpoly_castSucc {n : ℕ}
    (hqu : AlgebraicIndependent ℤ ![(q : K), u]) (ν : PartIdx (Fin n) d) :
    killComplComp (Fin.castSucc_injective n) K d
        (macPpoly hqu (upIdx (isTopExtension_castSucc n).card_le ν))
      = macPpoly hqu ν :=
  killComplComp_macPpoly (isTopExtension_castSucc n) hqu ν

end Main

/-! ### The alphabets `X_n`, and the index of a partition in them -/

section Fin

variable {d : ℕ}

/-- A partition of `d` has at most `d` parts, its parts being positive and summing to `d`. This is
the observation that `μ_{m+1} = 0` for every `m ≥ |μ|`. -/
theorem parts_card_le_size (p : Nat.Partition d) : p.parts.card ≤ d := by
  have h := Multiset.card_nsmul_le_sum (s := p.parts) (a := 1) fun x hx => p.parts_pos hx
  rwa [p.parts_sum, smul_eq_mul, mul_one] at h

/-- The partition `p` read as an index of the monomial symmetric basis of `𝒮_{n,d}`: a partition
`μ` with `μ_{n+1} = 0`, which is exactly the bound on the number of parts. -/
def finIdx (p : Nat.Partition d) {n : ℕ} (hn : p.parts.card ≤ n) : PartIdx (Fin n) d :=
  ⟨p, by rwa [Fintype.card_fin]⟩

/-- Reading `p` in `x_1, …, x_{n+1}` is reading it in `x_1, …, x_n` and then extending the
alphabet: both are the partition `p` with a bound on its number of parts. -/
theorem upIdx_finIdx (p : Nat.Partition d) {n : ℕ} (hn : p.parts.card ≤ n) :
    upIdx (isTopExtension_castSucc n).card_le (finIdx p hn)
      = finIdx p (hn.trans (Nat.le_succ n)) := rfl

/-- **The diagram of a partition is the same in every alphabet that does not truncate it.** -/
theorem partDiagram_finIdx (p : Nat.Partition d) {n m : ℕ} (hn : p.parts.card ≤ n) (hnm : n ≤ m) :
    partDiagram (Fin m) (finIdx p (hn.trans hnm)) = partDiagram (Fin n) (finIdx p hn) := by
  induction m, hnm using Nat.le_induction with
  | base => rfl
  | succ m hm ih =>
      rw [← ih, ← upIdx_finIdx p (hn.trans hm),
        partDiagram_upIdx (isTopExtension_castSucc m) (finIdx p (hn.trans hm))]

end Fin

/-! ### `HJO.Mac.restrictAlphabet_macPfun_partDiagram` -/

section Pfun

variable {K : Type*} [Field K] [Algebra ℚ K] {q : Kˣ} {u : K} {d : ℕ}

/-- **One step of the descent through the alphabets.** If `P_D` restricts to `P_p[X_{n+1}]` then it
restricts to `P_p[X_n]`: erase the last variable, which turns `res_{n+1}` into `res_n`
(`HJO.Sym.killCompl_restrictAlphabet`) and `P_p[X_{n+1}]` into `P_p[X_n]`
(`HJO.Mac.killComplComp_macPpoly`). No injectivity is needed in this direction, so it holds for
every `n` that does not truncate `p`. -/
theorem restrictAlphabet_macPfun_of_succ (hqu : AlgebraicIndependent ℤ ![(q : K), u])
    {p : Nat.Partition d} {n : ℕ} (hn : p.parts.card ≤ n) {D : YoungDiagram}
    (h : HJO.Sym.restrictAlphabet (Fin (n + 1)) K (HJO.Sym.macPfun hqu D)
      = (macPpoly hqu (finIdx p (hn.trans (Nat.le_succ n))) : MvPolynomial (Fin (n + 1)) K)) :
    HJO.Sym.restrictAlphabet (Fin n) K (HJO.Sym.macPfun hqu D)
      = (macPpoly hqu (finIdx p hn) : MvPolynomial (Fin n) K) := by
  have hcut := congrArg (Subtype.val (p := fun r => r ∈ symmetricHomogeneousSubmodule (Fin n) K d))
    (killComplComp_macPpoly (isTopExtension_castSucc n) hqu (finIdx p hn))
  rw [coe_killComplComp, upIdx_finIdx] at hcut
  rw [← HJO.Sym.killCompl_restrictAlphabet (Fin.castSucc_injective n)
    (HJO.Sym.macPfun hqu D), h, hcut]

/-- **Macdonald's symmetric function restricts to Macdonald's polynomial.**
For a partition `p` of `d` and `n ≥ max(d, 1)`, `res_n(P_p) = P_p[X_n]`.

The partition `μ` is the Young diagram `partDiagram (Fin n) ν` of the index `ν`, which is the same
diagram in every alphabet (`partDiagram_finIdx`), and its `|μ| = d` is `HJO.Mac.card_partDiagram`.

Induct upward from `n_μ = max(d, 1)`, where the claim is `HJO.Sym.macPfun` read at an index
(`HJO.Sym.macPfun_partDiagram`). The step is `restrictAlphabet_macPfun_of_succ` run backwards:
`res_{n+1}(P_p)` and `P_p[X_{n+1}]` have the same image under `cut_n`, both lie in `𝒮_{n+1,d}`, and
`cut_n` is injective there because `d ≤ n` (`MvPolynomial.killComplComp_bijective`). -/
@[hjo "lem_mac_pfun_res"]
theorem restrictAlphabet_macPfun_partDiagram (hqu : AlgebraicIndependent ℤ ![(q : K), u])
    {n : ℕ} (hn : max d 1 ≤ n) (ν : PartIdx (Fin n) d) :
    HJO.Sym.restrictAlphabet (Fin n) K (HJO.Sym.macPfun hqu (partDiagram (Fin n) ν))
      = (macPpoly hqu ν : MvPolynomial (Fin n) K) := by
  suffices H : ∀ m : ℕ, max d 1 ≤ m → ∀ (p : Nat.Partition d) (hp : p.parts.card ≤ m),
      HJO.Sym.restrictAlphabet (Fin m) K (HJO.Sym.macPfun hqu (partDiagram (Fin m) (finIdx p hp)))
        = (macPpoly hqu (finIdx p hp) : MvPolynomial (Fin m) K) from
    H n hn ν.1 (by simpa using ν.2)
  clear hn ν n
  intro m hm
  induction m, hm using Nat.le_induction with
  | base =>
      intro p hp
      rw [HJO.Sym.macPfun_partDiagram hqu (by rw [Fintype.card_fin]; exact le_max_left d 1),
        ← HJO.Sym.coe_restrictAlphabetEquiv (by rw [Fintype.card_fin]; exact le_max_left d 1),
        LinearEquiv.apply_symm_apply]
  | succ m hm ih =>
      intro p hp
      have hdm : d ≤ m := le_trans (le_max_left d 1) hm
      have hpm : p.parts.card ≤ m := (parts_card_le_size p).trans hdm
      have hD : partDiagram (Fin (m + 1)) (finIdx p hp) = partDiagram (Fin m) (finIdx p hpm) := by
        rw [← partDiagram_finIdx p hpm (Nat.le_succ m)]
      rw [hD]
      -- both sides lie in `𝒮_{m+1,d}` and have the same image under `cut_m`
      have hmem : HJO.Sym.macPfun hqu (partDiagram (Fin m) (finIdx p hpm))
          ∈ HJO.Sym.LambdaComp K d := by
        have := HJO.Sym.macPfun_mem hqu (partDiagram (Fin m) (finIdx p hpm))
        rwa [card_partDiagram] at this
      refine MvPolynomial.eq_of_killCompl_eq (Fin.castSucc_injective m)
        (by rwa [Fintype.card_fin]) (HJO.Sym.restrictAlphabet_mem_symmetricHomogeneousSubmodule
          hmem) (macPpoly hqu (finIdx p hp)).2 ?_
      have hcut := congrArg
        (Subtype.val (p := fun r => r ∈ symmetricHomogeneousSubmodule (Fin m) K d))
        (killComplComp_macPpoly (isTopExtension_castSucc m) hqu (finIdx p hpm))
      rw [coe_killComplComp, upIdx_finIdx] at hcut
      rw [HJO.Sym.killCompl_restrictAlphabet (Fin.castSucc_injective m), ih p hpm, hcut]

/-- **`HJO.Mac.restrictAlphabet_macPfun_partDiagram_of_pos`: `res_n(P_μ) = P_μ[X_n]` for every
alphabet that does not truncate `μ`.** The same statement as
`HJO.Mac.restrictAlphabet_macPfun_partDiagram` with its hypothesis `n ≥ |μ|` dropped: all that is
needed is `μ_{n+1} = 0`, which the index type carries, and `n ≥ 1`.

Above `max(d, 1)` this is `HJO.Mac.restrictAlphabet_macPfun_partDiagram`; below it, the descent runs
downward from `max(d, 1)` by `restrictAlphabet_macPfun_of_succ`, which needs no injectivity and
therefore no bound on `d`. -/
@[hjo "lem_pie_res_ppoly"]
theorem restrictAlphabet_macPfun_partDiagram_of_pos (hqu : AlgebraicIndependent ℤ ![(q : K), u])
    {n : ℕ} (hn : 1 ≤ n) (ν : PartIdx (Fin n) d) :
    HJO.Sym.restrictAlphabet (Fin n) K (HJO.Sym.macPfun hqu (partDiagram (Fin n) ν))
      = (macPpoly hqu ν : MvPolynomial (Fin n) K) := by
  rcases le_or_gt (max d 1) n with hle | hlt
  · exact restrictAlphabet_macPfun_partDiagram hqu hle ν
  -- below `max(d, 1)`: descend from there, one variable at a time
  suffices H : ∀ k m : ℕ, m + k = max d 1 → 1 ≤ m → ∀ (p : Nat.Partition d)
      (hp : p.parts.card ≤ m),
      HJO.Sym.restrictAlphabet (Fin m) K (HJO.Sym.macPfun hqu (partDiagram (Fin m) (finIdx p hp)))
        = (macPpoly hqu (finIdx p hp) : MvPolynomial (Fin m) K) from
    H (max d 1 - n) n (by omega) hn ν.1 (by simpa using ν.2)
  clear hlt hn ν n
  intro k
  induction k with
  | zero =>
      intro m hmk hm p hp
      subst hmk
      exact restrictAlphabet_macPfun_partDiagram hqu (by omega) (finIdx p hp)
  | succ k ih =>
      intro m hmk hm p hp
      have hp' : p.parts.card ≤ m + 1 := hp.trans (Nat.le_succ m)
      have hstep := ih (m + 1) (by omega) (by omega) p hp'
      rw [partDiagram_finIdx p hp (Nat.le_succ m)] at hstep
      exact restrictAlphabet_macPfun_of_succ hqu hp hstep

end Pfun

end HJO.Mac
