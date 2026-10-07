/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.Macdonald.LeadingExponent
public import HJO.Macdonald.RestrictBasis
public meta import HJO.Attr

/-! # The leading exponent of a restricted elementary monomial

Fix a finite alphabet `σ` with a linear order and a degree `d ≤ #σ`, and let `λ` be a partition of
`d`. The restricted elementary monomial `res_n(e_λ)` is nonzero, its leading exponent for the
lexicographic monomial order is the **conjugate** of `λ` read along the order of the alphabet -- the
entry at a letter sitting in position `k` of the increasing listing is the number of parts `λ_j`
with `λ_j ≥ k + 1` -- and the coefficient there is `1`.

The proof is direct. `res_n(e_r)` is the elementary symmetric *polynomial*
(`HJO.Sym.restrictAlphabet_elemSymm`), which is the sum of the squarefree monomials `x^{1_T}` over
the `r`-element subsets `T` of the alphabet, each with coefficient `1`. Among those indicator
vectors the lexicographically largest is the one of the `r` smallest letters, so
`ld(res_n(e_r)) = 1_{L_r}` and the coefficient there is `1`. The elementary monomial is the product
of the `e_{λ_j}` and `res_n` is multiplicative, so `MonomialOrder.mul_ne_zero_and_degree_mul` and
`MonomialOrder.coeff_mul_of_degree_add`, applied along the multiset of parts, give nonvanishing, the
sum of the indicator vectors as leading exponent, and `1` as the coefficient. Reading the sum
`∑_j 1_{L_{λ_j}}` at a letter counts the parts exceeding that letter's position, which is the
conjugate.

## Main definitions

* `HJO.Mac.lowerLetters σ r`: the `r` smallest letters of the alphabet, the set
  `{1, …, r}`.
* `HJO.Mac.conjExp σ m`: the conjugate exponent vector of a multiset of parts, whose entry at a
  letter is the number of parts exceeding that letter's position.

## Main results

* `HJO.Mac.restrictAlphabet_elemSymmMonomial_ne_zero`,
  `HJO.Mac.lex_degree_restrictAlphabet_elemSymmMonomial`,
  `HJO.Mac.lex_leadingCoeff_restrictAlphabet_elemSymmMonomial`: the three clauses of the
  leading-term statement for `res_n(e_λ)` -- nonvanishing, leading exponent, leading coefficient.
* `HJO.Mac.lex_degree_esymm`, `HJO.Mac.lex_leadingCoeff_esymm`: the leading exponent of an
  elementary symmetric polynomial is the indicator of the smallest letters, and the coefficient
  there is `1`. Mathlib has `MvPolynomial.monic_esymm` and `MvPolynomial.supDegree_esymm` only for
  the alphabet `Fin m` and only in the `accumulate` coordinates its fundamental theorem uses, so
  neither transfers to an arbitrary ordered alphabet.

## Implementation notes

**The alphabet is an arbitrary linearly ordered `Fintype σ`**, as everywhere in
`HJO/Macdonald/`, and the index `i ∈ {1, …, n}` is the position
`(letterEquiv σ).symm i` of a letter in the increasing listing of the alphabet. At `σ = Fin n` that
position is the letter itself.

**The base must have no zero divisors, and this is the first step of the restriction chain that
needs it.** The leading exponent of a product is the sum of the leading exponents only over a domain
(`MonomialOrder.mul_ne_zero_and_degree_mul`), and it is the only extra hypothesis:
`[CommRing K] [IsDomain K] [Algebra ℚ K]`, which the standing field `𝕜 = ℚ(q, u)` satisfies. No
genericity enters: the parameters `q` and `u` do not occur.

**The conjugate partition is not built.** The proof of
`HJO.Sym.exists_basis_symmetricHomogeneousSubmodule_restrictAlphabet` wants the involution `ν ↦ ν'`
on the partitions of `d`; nothing here needs it, because the leading exponent is produced as
the *exponent vector* `HJO.Mac.conjExp`, a sum of indicator vectors over the letters rather than a
partition, and `HJO.Sym.exists_basis_symmetricHomogeneousSubmodule_restrictAlphabet` is proved in
`HJO/Macdonald/RestrictBasis.lean` by a route that never reindexes. The conjugate is treated
separately, in `HJO.Sym.rowLen_transpose_eq_natCard`, which identifies it with Mathlib's
`YoungDiagram.transpose`, and `HJO.DetCoeff.conjPart` is a third presentation of it for a partition
given as a function `ℕ → ℕ`.

The rearrangement step -- that all the indicator vectors of a fixed cardinality are permutations of
one another, so the weakly decreasing one among them is the lexicographically largest -- is
`HJO.Mac.toLex_le_of_antitone` of `HJO/Macdonald/LeadingExponent.lean`, reached through
`Nat.Partition.ofSym`: two subsets of the same cardinality have the same multiplicity partition,
namely that many copies of `1`.

## References

The file proves `HJO.Mac.restrictAlphabet_elemSymmMonomial_ne_zero`, on
`HJO.Sym.partitionEquivList`, `HJO.Sym.elemSymmMonomial` and `HJO.Sym.restrictAlphabet`, from
`HJO.Sym.restrictAlphabet_elemSymm`, `Finsupp.lex_lt_iff_isLeast`,
`MonomialOrder.lex_degree_isGreatest`, `MonomialOrder.coeff_mul_of_degree_add` and
`MonomialOrder.mul_ne_zero_and_degree_mul`.
-/

@[expose] public section

open Finset MvPolynomial

namespace HJO.Mac

/-! ### The indicator vector of a subset of the alphabet -/

section Indicator

variable {σ : Type*} [DecidableEq σ]

/-- The exponent vector of the squarefree monomial `∏_{i ∈ t} x_i`: the indicator of `t`. -/
theorem toFinsupp_val_apply (t : Finset σ) (j : σ) :
    Multiset.toFinsupp t.val j = if j ∈ t then 1 else 0 := by
  rw [Multiset.toFinsupp_apply]
  by_cases hj : j ∈ t
  · rw [ite_eq_left hj, Multiset.count_eq_one_of_mem t.nodup (Finset.mem_val.mpr hj)]
  · rw [ite_eq_right hj, Multiset.count_eq_zero_of_notMem fun h => hj (Finset.mem_val.mp h)]

/-- The indicator of a subset is the sum of the unit vectors at its members, which is the exponent
vector `MvPolynomial.esymm_eq_sum_monomial` writes. -/
theorem toFinsupp_val_eq_sum_single (t : Finset σ) :
    Multiset.toFinsupp t.val = ∑ i ∈ t, Finsupp.single i (1 : ℕ) := by
  refine Finsupp.ext fun j => ?_
  rw [toFinsupp_val_apply, Finset.sum_apply']
  simp only [Finsupp.single_apply]
  rw [Finset.sum_ite_eq' t j fun _ => (1 : ℕ)]

/-- A subset of the alphabet is determined by its indicator vector. -/
private theorem toFinsupp_val_inj {t t' : Finset σ}
    (h : Multiset.toFinsupp t.val = Multiset.toFinsupp t'.val) : t = t' := by
  refine Finset.ext fun j => ?_
  have hj := congrArg (fun f => f j) h
  rw [toFinsupp_val_apply, toFinsupp_val_apply] at hj
  by_cases h1 : j ∈ t <;> by_cases h2 : j ∈ t' <;> simp_all

/-- A multiset of `d` letters with no repetition has `d` copies of `1` as its multiplicity
partition: every letter that occurs occurs once. -/
private theorem parts_ofSym_of_nodup {d : ℕ} (a : Sym σ d) (ha : a.1.Nodup) :
    (Nat.Partition.ofSym a).parts = Multiset.replicate d 1 := by
  rw [Nat.Partition.parts_ofSym, ha.dedup]
  calc Multiset.map (fun x => Multiset.count x a.1) a.1
      = Multiset.map (Function.const σ 1) a.1 :=
        Multiset.map_congr rfl fun x hx => Multiset.count_eq_one_of_mem ha hx
    _ = Multiset.replicate d 1 := by rw [Multiset.map_const, a.2]

/-- Two subsets of the alphabet of the same cardinality have the same multiplicity partition. -/
private theorem ofSym_finset_eq {d : ℕ} {t t' : Finset σ} (ht : t.val.card = d)
    (ht' : t'.val.card = d) :
    Nat.Partition.ofSym (⟨t.val, ht⟩ : Sym σ d) = Nat.Partition.ofSym ⟨t'.val, ht'⟩ :=
  Nat.Partition.ext ((parts_ofSym_of_nodup ⟨t.val, ht⟩ t.nodup).trans
    (parts_ofSym_of_nodup ⟨t'.val, ht'⟩ t'.nodup).symm)

/-- **The indicators of two subsets of the same cardinality are rearrangements of one another**:
read over the whole alphabet they have the same multiset of entries, `#t` ones and the rest
zeros. -/
theorem map_toFinsupp_univ_val_eq [Fintype σ] {t t' : Finset σ} (h : #t = #t') :
    Multiset.map (Multiset.toFinsupp t.val) Finset.univ.val
      = Multiset.map (Multiset.toFinsupp t'.val) Finset.univ.val :=
  map_toFinsupp_univ_val_eq_of_ofSym_eq (ofSym_finset_eq (t := t') (t' := t) rfl h)

end Indicator

/-! ### The smallest letters of the alphabet -/

section LowerLetters

variable {σ : Type*} [Fintype σ] [LinearOrder σ]

/-- **The `r` smallest letters of the alphabet**: those whose position in the increasing listing of
`σ` is below `r`. This is the set `{1, …, r}`, and at `σ = Fin n` it is
`Finset.range r`. -/
noncomputable def lowerLetters (σ : Type*) [Fintype σ] [LinearOrder σ] (r : ℕ) : Finset σ :=
  Finset.filter (fun i => ((letterEquiv σ).symm i : ℕ) < r) Finset.univ

@[simp]
theorem mem_lowerLetters {r : ℕ} {i : σ} :
    i ∈ lowerLetters σ r ↔ ((letterEquiv σ).symm i : ℕ) < r := by
  rw [lowerLetters, Finset.mem_filter]
  exact and_iff_right (Finset.mem_univ i)

/-- There are `r` of them, as long as the alphabet has that many letters. -/
theorem card_lowerLetters {r : ℕ} (hr : r ≤ Fintype.card σ) : #(lowerLetters σ r) = r := by
  have h : #(lowerLetters σ r)
      = #(Finset.filter (fun k : Fin (Fintype.card σ) => (k : ℕ) < r) Finset.univ) :=
    Finset.card_equiv (letterEquiv σ).symm.toEquiv fun i => by simp
  rw [h, ← Finset.card_range r]
  refine Finset.card_nbij (fun k => (k : ℕ)) (fun k hk => ?_) (fun a _ b _ hab => ?_)
    fun a ha => ?_
  · simpa using (Finset.mem_filter.mp hk).2
  · exact Fin.val_injective hab
  · refine ⟨⟨a, lt_of_lt_of_le (Finset.mem_range.mp ha) hr⟩, ?_, rfl⟩
    simpa using Finset.mem_range.mp ha

/-- The indicator of the smallest letters is weakly decreasing, the set being downward closed. This
is what makes it the lexicographically largest of the indicators of its cardinality. -/
theorem antitone_toFinsupp_lowerLetters [DecidableEq σ] (r : ℕ) :
    Antitone (Multiset.toFinsupp (lowerLetters σ r).val) := by
  intro i j hij
  rw [toFinsupp_val_apply, toFinsupp_val_apply]
  by_cases hj : j ∈ lowerLetters σ r
  · rw [ite_eq_left hj, ite_eq_left (mem_lowerLetters.mpr (lt_of_le_of_lt
      (Fin.le_def.mp ((letterEquiv σ).symm.monotone hij)) (mem_lowerLetters.mp hj)))]
  · rw [ite_eq_right hj]
    exact Nat.zero_le _

end LowerLetters

/-! ### The monomials of an elementary symmetric polynomial -/

section EsymmCoeff

variable {σ : Type*} [Fintype σ] [DecidableEq σ] (R : Type*) [CommSemiring R]

/-- Each squarefree monomial of the right cardinality occurs in `e_r` with coefficient `1`. -/
theorem coeff_toFinsupp_esymm {r : ℕ} {t : Finset σ} (ht : #t = r) :
    coeff (Multiset.toFinsupp t.val) (esymm σ R r) = 1 := by
  rw [esymm_eq_sum_monomial, coeff_sum,
    Finset.sum_eq_single_of_mem t (Finset.mem_powersetCard_univ.mpr ht)]
  · rw [coeff_monomial, ← toFinsupp_val_eq_sum_single, ite_eq_left rfl]
  · intro t' _ hne
    rw [coeff_monomial, ← toFinsupp_val_eq_sum_single]
    exact ite_eq_right fun h => hne (toFinsupp_val_inj h)

/-- No other monomial occurs in `e_r`: every monomial of `e_r` is squarefree on exactly `r`
letters. -/
theorem coeff_esymm_eq_zero {r : ℕ} {c : σ →₀ ℕ}
    (hc : ∀ t : Finset σ, #t = r → Multiset.toFinsupp t.val ≠ c) :
    coeff c (esymm σ R r) = 0 := by
  rw [esymm_eq_sum_monomial, coeff_sum, Finset.sum_eq_zero]
  intro t ht
  rw [coeff_monomial, ← toFinsupp_val_eq_sum_single]
  exact ite_eq_right (hc t (Finset.mem_powersetCard_univ.mp ht))

end EsymmCoeff

/-! ### The leading exponent of an elementary symmetric polynomial -/

section EsymmLead

variable {σ : Type*} [Fintype σ] [LinearOrder σ] (R : Type*) [CommSemiring R] [Nontrivial R]

/-- **The leading exponent of `e_r` is the indicator of the `r` smallest letters.** Every monomial
of `e_r` is the indicator of an `r`-element subset, all such indicators are rearrangements of one
another, and the weakly decreasing one among them -- the indicator of the smallest letters -- is the
largest for the lexicographic order. -/
theorem lex_degree_esymm [DecidableEq σ] {r : ℕ} (hr : r ≤ Fintype.card σ) :
    MonomialOrder.lex.degree (esymm σ R r) = Multiset.toFinsupp (lowerLetters σ r).val := by
  refine MonomialOrder.degree_eq_of_coeff_ne_zero ?_ fun c hc => ?_
  · rw [coeff_toFinsupp_esymm R (card_lowerLetters hr)]
    exact one_ne_zero
  · obtain ⟨t, ht, rfl⟩ : ∃ t : Finset σ, #t = r ∧ Multiset.toFinsupp t.val = c := by
      by_contra hno
      exact mem_support_iff.mp hc (coeff_esymm_eq_zero R fun t htc h => hno ⟨t, htc, h⟩)
    exact MonomialOrder.lex_le_iff.mpr (toLex_le_of_antitone
      (antitone_toFinsupp_lowerLetters r)
      (map_toFinsupp_univ_val_eq (by rw [ht, card_lowerLetters hr])))

/-- **The elementary symmetric polynomials are monic** for the lexicographic order. -/
theorem lex_leadingCoeff_esymm {r : ℕ} (hr : r ≤ Fintype.card σ) :
    MonomialOrder.lex.leadingCoeff (esymm σ R r) = 1 := by
  classical
  rw [MonomialOrder.leadingCoeff, lex_degree_esymm R hr,
    coeff_toFinsupp_esymm R (card_lowerLetters hr)]

/-- `e_r` is not the zero polynomial: the monomial of the `r` smallest letters occurs in it. -/
theorem esymm_ne_zero {r : ℕ} (hr : r ≤ Fintype.card σ) : esymm σ R r ≠ 0 := fun h => by
  classical
  simpa [h] using (coeff_toFinsupp_esymm (σ := σ) R (card_lowerLetters hr)).symm

end EsymmLead

/-! ### The conjugate exponent vector of a multiset of parts -/

section ConjExp

variable {σ : Type*} [Fintype σ] [LinearOrder σ] [DecidableEq σ]

/-- **The conjugate exponent vector of a multiset of parts**: the sum, over the parts `a`, of the
indicators of the `a` smallest letters. Its entry at a letter `i` is the number of parts exceeding
the position of `i` (`HJO.Mac.conjExp_apply`), so for a partition `λ` it lists the parts of the
conjugate partition `λ'` along the order of the alphabet. -/
noncomputable def conjExp (σ : Type*) [Fintype σ] [LinearOrder σ] [DecidableEq σ]
    (m : Multiset ℕ) : σ →₀ ℕ :=
  (m.map fun a => Multiset.toFinsupp (lowerLetters σ a).val).sum

/-- **The conjugate exponent vector, entry by entry**: at the letter `i`, sitting in position `k` of
the increasing listing of the alphabet, it is the number of parts `a` with `a ≥ k + 1`. This is
`α_i = #{j : λ_j ≥ i}`. -/
theorem conjExp_apply (m : Multiset ℕ) (i : σ) :
    conjExp σ m i = (m.filter fun a => ((letterEquiv σ).symm i : ℕ) < a).card := by
  induction m using Multiset.induction with
  | empty => simp [conjExp]
  | cons a m ih =>
      rw [conjExp] at ih ⊢
      rw [Multiset.map_cons, Multiset.sum_cons, Finsupp.add_apply, toFinsupp_val_apply, ih]
      by_cases ha : ((letterEquiv σ).symm i : ℕ) < a
      · rw [ite_eq_left (mem_lowerLetters.mpr ha)]
        simp [Multiset.filter_cons_of_pos _ ha, Nat.add_comm]
      · rw [ite_eq_right fun h => ha (mem_lowerLetters.mp h), zero_add]
        simp [Multiset.filter_cons_of_neg _ ha]

end ConjExp

/-! ### The leading exponent of a product -/

section Prod

variable {σ : Type*} [Finite σ] [LinearOrder σ] {K : Type*} [CommRing K] [IsDomain K]

/-- A product of nonzero polynomials over a domain is nonzero and its leading exponent is the sum
of theirs: `MonomialOrder.mul_ne_zero_and_degree_mul` along a multiset. -/
private theorem prod_ne_zero_and_lex_degree_prod (s : Multiset (MvPolynomial σ K))
    (hs : ∀ f ∈ s, f ≠ 0) :
    s.prod ≠ 0 ∧ MonomialOrder.lex.degree s.prod = (s.map MonomialOrder.lex.degree).sum := by
  induction s using Multiset.induction with
  | empty => exact ⟨by simp, by simp [MonomialOrder.degree_one]⟩
  | cons a s ih =>
      obtain ⟨hprod, hdeg⟩ := ih fun f hf => hs f (Multiset.mem_cons_of_mem hf)
      obtain ⟨hne, hmul⟩ := MonomialOrder.mul_ne_zero_and_degree_mul MonomialOrder.lex
        (hs a (Multiset.mem_cons_self a s)) hprod
      rw [Multiset.prod_cons]
      exact ⟨hne, by rw [hmul, hdeg, Multiset.map_cons, Multiset.sum_cons]⟩

/-- The leading coefficient of a product is the product of the leading coefficients:
`MonomialOrder.coeff_mul_of_degree_add` along a multiset. -/
private theorem lex_leadingCoeff_multiset_prod (s : Multiset (MvPolynomial σ K)) :
    MonomialOrder.lex.leadingCoeff s.prod = (s.map MonomialOrder.lex.leadingCoeff).prod := by
  induction s using Multiset.induction with
  | empty => simp
  | cons a s ih =>
      rw [Multiset.prod_cons, MonomialOrder.leadingCoeff_mul, ih, Multiset.map_cons,
        Multiset.prod_cons]

end Prod

/-! ### The leading exponent of a restricted elementary monomial -/

section EmonomialLead

open HJO.Sym

/-- The restriction of an elementary monomial is the product of the elementary symmetric
polynomials over the parts, the restriction being multiplicative. -/
theorem restrictAlphabet_elemSymmMonomial (σ : Type*) [Fintype σ] (K : Type*) [CommRing K]
    [Algebra ℚ K] (m : Multiset ℕ) :
    restrictAlphabet σ K (elemSymmMonomial K m) = (m.map fun a => esymm σ K a).prod := by
  rw [elemSymmMonomial, map_multiset_prod, Multiset.map_map]
  exact congrArg Multiset.prod (Multiset.map_congr rfl fun a _ => restrictAlphabet_elemSymm σ K a)

/-- Every part of a partition of `d` is at most `d`, hence at most the size of the alphabet. -/
private theorem le_card_of_mem_parts {σ : Type*} [Fintype σ] {d : ℕ} (hd : d ≤ Fintype.card σ)
    (μ : Nat.Partition d) {a : ℕ} (ha : a ∈ μ.parts) : a ≤ Fintype.card σ :=
  le_trans (μ.parts_sum ▸ Multiset.single_le_sum (fun _ _ => Nat.zero_le _) a ha) hd

variable {σ : Type*} [Fintype σ] [LinearOrder σ] (K : Type*) [CommRing K] [IsDomain K]
  [Algebra ℚ K]

omit [Algebra ℚ K] in
/-- Each factor `res_n(e_{λ_j})` of a restricted elementary monomial is nonzero, its index being at
most `d` and hence at most the size of the alphabet. -/
private theorem esymm_ne_zero_of_mem_map {d : ℕ} (hd : d ≤ Fintype.card σ)
    (μ : Nat.Partition d) : ∀ f ∈ μ.parts.map fun a => esymm σ K a, f ≠ 0 := by
  intro f hf
  obtain ⟨a, ha, rfl⟩ := Multiset.mem_map.mp hf
  exact esymm_ne_zero K (le_card_of_mem_parts hd μ ha)

/-- **A restricted elementary monomial is nonzero.** Over a domain a product of nonzero polynomials
is nonzero, and each `res_n(e_{λ_j}) = e_{λ_j}[X_n]` is nonzero because `λ_j ≤ d ≤ n`. -/
@[hjo "lem_mac_res_emonomial_lead"]
theorem restrictAlphabet_elemSymmMonomial_ne_zero {d : ℕ} (hd : d ≤ Fintype.card σ)
    (μ : Nat.Partition d) : restrictAlphabet σ K (elemSymmMonomial K μ.parts) ≠ 0 := by
  rw [restrictAlphabet_elemSymmMonomial σ K μ.parts]
  exact (prod_ne_zero_and_lex_degree_prod _ (esymm_ne_zero_of_mem_map K hd μ)).1

/-- **The leading exponent of a restricted elementary monomial is the conjugate of the partition.**
At the letter `i`, sitting in position `k` of the increasing listing of the alphabet, the leading
exponent of `res_n(e_λ)` is the number of parts `λ_j` with `λ_j ≥ k + 1`: the restriction is
multiplicative, the leading exponent of `res_n(e_{λ_j})` is the indicator of the `λ_j` smallest
letters, and by `MonomialOrder.mul_ne_zero_and_degree_mul` the leading exponent of the product is
the sum of those indicators, whose entry at `i` counts the parts exceeding `k`. -/
@[hjo "lem_mac_res_emonomial_lead"]
theorem lex_degree_restrictAlphabet_elemSymmMonomial {d : ℕ} (hd : d ≤ Fintype.card σ)
    (μ : Nat.Partition d) (i : σ) :
    MonomialOrder.lex.degree (restrictAlphabet σ K (elemSymmMonomial K μ.parts)) i
      = (μ.parts.filter fun a => ((letterEquiv σ).symm i : ℕ) < a).card := by
  classical
  rw [restrictAlphabet_elemSymmMonomial σ K μ.parts,
    (prod_ne_zero_and_lex_degree_prod _ (esymm_ne_zero_of_mem_map K hd μ)).2, Multiset.map_map,
    ← conjExp_apply μ.parts i, conjExp]
  exact congrFun (congrArg _ (congrArg Multiset.sum (Multiset.map_congr rfl fun a ha =>
    lex_degree_esymm K (le_card_of_mem_parts hd μ ha)))) i

/-- **A restricted elementary monomial is monic.** By `MonomialOrder.coeff_mul_of_degree_add` the
leading coefficient of a product is the product of the leading coefficients, and each
`res_n(e_{λ_j})` is monic. -/
@[hjo "lem_mac_res_emonomial_lead"]
theorem lex_leadingCoeff_restrictAlphabet_elemSymmMonomial {d : ℕ} (hd : d ≤ Fintype.card σ)
    (μ : Nat.Partition d) :
    MonomialOrder.lex.leadingCoeff (restrictAlphabet σ K (elemSymmMonomial K μ.parts)) = 1 := by
  rw [restrictAlphabet_elemSymmMonomial σ K μ.parts, lex_leadingCoeff_multiset_prod,
    Multiset.map_map]
  refine Multiset.prod_eq_one fun x hx => ?_
  obtain ⟨a, ha, rfl⟩ := Multiset.mem_map.mp hx
  exact lex_leadingCoeff_esymm K (le_card_of_mem_parts hd μ ha)

/-- The leading exponent of a restricted elementary monomial, as one vector rather than entry by
entry: it is the conjugate exponent vector of the parts. -/
theorem lex_degree_restrictAlphabet_elemSymmMonomial_eq_conjExp [DecidableEq σ] {d : ℕ}
    (hd : d ≤ Fintype.card σ) (μ : Nat.Partition d) :
    MonomialOrder.lex.degree (restrictAlphabet σ K (elemSymmMonomial K μ.parts))
      = conjExp σ μ.parts :=
  Finsupp.ext fun i => (lex_degree_restrictAlphabet_elemSymmMonomial K hd μ i).trans
    (conjExp_apply μ.parts i).symm

end EmonomialLead

end HJO.Mac
