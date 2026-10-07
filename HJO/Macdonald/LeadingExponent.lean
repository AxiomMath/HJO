/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Mathlib.Data.Fin.Tuple.Sort
public import Mathlib.Data.Finsupp.Lex
public import Mathlib.Data.Fintype.Sort
public import HJO.Macdonald.MonomialBasis
public meta import HJO.Attr

/-! # The leading exponent of a monomial symmetric polynomial

Macdonald's operator is triangular on the `m_μ` for the lexicographic order on exponent vectors, so
the statement of the triangularity needs, for each index `μ` of the basis of `𝒮_{n,d}`, the exponent
vector `\bar\mu = (μ_1, …, μ_n)` it compares. This file produces it and identifies it
three ways: as the *weakly decreasing* exponent vector in the orbit `μ` (`HJO.Mac.partExp`), as the
**leading exponent** of `m_μ` for the lexicographic monomial order
(`HJO.Mac.lex_degree_msymm`), and -- through the Young diagram whose row lengths it lists --  as the
partition whose eigenvalue `E_n(μ)` is (`HJO.Mac.macdonaldEigenvalue_partDiagram`).

The alphabet is an arbitrary linearly ordered `Fintype σ` rather than `Fin n`, as everywhere in
`HJO/Macdonald/`. Reading a partition as an exponent vector needs the letters listed in
increasing order, which is `HJO.Mac.letterEquiv`, an order isomorphism `Fin #σ ≃o σ`; at
`σ = Fin n` it is the identity.

## Main definitions

* `HJO.Mac.PartIdx σ d`: the index set of the monomial symmetric basis of `𝒮_{n,d}` -- the
  partitions of `d` with at most `#σ` parts, which is the `|μ| = d`, `μ_{n+1} = 0`.
* `HJO.Mac.letterEquiv`: the letters of `σ` listed in increasing order.
* `HJO.Mac.partExp`: the exponent vector `\bar\mu` of a partition, weakly decreasing along the
  order of the alphabet.
* `HJO.Mac.partDiagram`: the Young diagram whose row lengths are the entries of `partExp`.

## Three folded cards

`MonomialOrder.le_degree_add_degree_of_mem_support_mul`,
`MonomialOrder.mul_ne_zero_and_degree_mul` and `Finsupp.add_lex_add_iff_right` are each a line or
two over Mathlib's `MonomialOrder` interface, and are proved below. The rest of the
leading-exponent calculus is Mathlib's outright:
`Finsupp.lex_lt_iff_isLeast` is `MonomialOrder.lex`,
`MonomialOrder.lex_degree_isGreatest` is `MonomialOrder.degree`,
`MonomialOrder.coeff_mul_of_degree_add` is `MonomialOrder.coeff_mul_of_degree_add`, and
`Finsupp.isStrictTotalOrder_lex` is the linear order on the type synonym `Lex (σ →₀ ℕ)`.

## Main results

* `MonomialOrder.le_degree_add_degree_of_mem_support_mul`,
  `MonomialOrder.mul_ne_zero_and_degree_mul`, `Finsupp.add_lex_add_iff_right`: the three folded
  cards.
* `HJO.Mac.toLex_le_of_antitone`: among the rearrangements of one exponent vector the weakly
  decreasing one is the largest for the lexicographic order. This is the Step 3 of
  `HJO.Mac.macOpComp_msymm_sub_smul_mem_span`, and it is where the weak decrease of a partition is
  used.
* `HJO.Mac.eq_partExp`: `partExp σ μ` is the *only* weakly decreasing exponent vector in the orbit
  `μ`, so the choice made in its definition is not a choice.
* `HJO.Mac.coeff_partExp_msymm`: the coefficient of `x^{\bar\nu}` in `m_μ` is `1` if `μ = ν` and
  `0` otherwise -- the functionals dual to the basis.
* `HJO.Mac.lex_degree_msymm`, `HJO.Mac.lex_leadingCoeff_msymm`: `ld(m_μ) = \bar\mu` and the
  coefficient there is `1`.
* `HJO.Mac.card_partDiagram`, `HJO.Mac.macdonaldEigenvalue_partDiagram`: the diagram of `μ` has `d`
  cells, and its eigenvalue is `∑_i q^{\bar\mu_i} u^{#\{j : i < j\}}`.

## Implementation notes

`partExp` is defined by choosing a weakly decreasing member of the orbit and `eq_partExp` shows
there is only one, rather than by sorting the parts of `μ` into a list and reading the list off.
Sorting is what `Tuple.sort` already does, and `exists_perm_antitone_comp` is the whole of the
construction; the alternative would re-derive `List.Sorted` bookkeeping that `Tuple.sort` has.

The Step 1 of `HJO.Mac.macOpComp_msymm_sub_smul_mem_span` states that the `k`th entry of
`ld(\mathcal{V}_S)` is `#\{l ∈ S : l > k\}` **for every `S ⊆ N`**, which is false at a `k ∉ S`: the
Vandermonde product of `S` does not mention `x_k` at all, so its leading exponent is `0` there,
and Step 2 uses the correct value (`0` at `k = i`, for `S = N ∖ \{i\}`). The formula is only used
at `S = N`, where it is right. Nothing here or in `HJO/Macdonald/Triangular.lean` depends on
the false reading: the leading exponent of `\mathcal{V}_{N∖\{i\}}` is never computed entrywise, only
compared with that of `\mathcal{V}_N` through the repo's `vandermondeProd_univ_eq_erase`.

## References

The file formalises Definitions `HJO.Sym.rowLenSeq`, `HJO.Mac.msymmMem`,
`Finsupp.lex_lt_iff_isLeast`, `MonomialOrder.lex_degree_isGreatest`, `HJO.Sym.macdonaldEigenvalue`
and Lemma `MvPolynomial.exists_basis_symmetricHomogeneousSubmodule_msymm`; Steps 1 and 3 of the
proof of `HJO.Mac.macOpComp_msymm_sub_smul_mem_span`.
-/

@[expose] public section

open Finset MvPolynomial

/-! ### The leading-exponent calculus

Three facts of the calculus are each a line or two over Mathlib's `MonomialOrder` interface, and
are proved here. The remaining facts of the calculus are Mathlib's outright:
`Finsupp.lex_lt_iff_isLeast` is `MonomialOrder.lex`, `MonomialOrder.lex_degree_isGreatest` is
`MonomialOrder.degree`, `MonomialOrder.coeff_mul_of_degree_add` is
`MonomialOrder.coeff_mul_of_degree_add`.
-/

namespace MonomialOrder

variable {σ R : Type*} [CommSemiring R]

/-- **The exponents of a product are bounded.** Every exponent `α` whose monomial has a nonzero
coefficient in `f * g` satisfies `α ≼[m] m.degree f + m.degree g`, that is, `α` is equal to the sum
of the two leading exponents or strictly below it in the monomial order. -/
@[hjo "lem_mac_lead_bound"]
theorem le_degree_add_degree_of_mem_support_mul (m : MonomialOrder σ)
    {f g : MvPolynomial σ R} {α : σ →₀ ℕ} (hα : α ∈ (f * g).support) :
    α ≼[m] m.degree f + m.degree g :=
  le_trans (m.le_degree hα) m.degree_mul_le

end MonomialOrder

/-- The leading exponent of a product: if `f` and `g` are nonzero polynomials over a commutative
semiring without zero divisors, then `f * g` is nonzero and its largest exponent for a monomial
order `m` is the sum of the largest exponents of `f` and of `g`. -/
@[hjo "lem_mac_lead_product"]
theorem MonomialOrder.mul_ne_zero_and_degree_mul {σ : Type*} (m : MonomialOrder σ) {R : Type*}
    [CommSemiring R] [NoZeroDivisors R] {f g : MvPolynomial σ R} (hf : f ≠ 0) (hg : g ≠ 0) :
    f * g ≠ 0 ∧ m.degree (f * g) = m.degree f + m.degree g :=
  ⟨mul_ne_zero hf hg, m.degree_mul hf hg⟩

/-- Lexicographic comparison of exponent vectors is invariant under translation: for exponent
vectors `a`, `b` and `c`, the comparison `a + c <_lex b + c` holds if and only if `a <_lex b` does,
where `<_lex` is `Finsupp.Lex r (· < ·)`, the relation that holds when the entry of the first vector
is the smaller at an index below which the two agree. -/
@[hjo "lem_mac_lex_translate"]
theorem Finsupp.add_lex_add_iff_right {σ N : Type*} {r : σ → σ → Prop} [AddZeroClass N] [LT N]
    [IsRightCancelAdd N] [AddRightStrictMono N] [AddRightReflectLT N] {a b : σ →₀ N}
    (c : σ →₀ N) :
    Finsupp.Lex r (· < ·) (a + c) (b + c) ↔ Finsupp.Lex r (· < ·) a b := by
  constructor
  · rintro ⟨i, hj, hi⟩
    refine ⟨i, fun j hjr => add_right_cancel (b := c j) (by simpa using hj j hjr), ?_⟩
    exact (add_lt_add_iff_right (c i)).mp (by simpa using hi)
  · rintro ⟨i, hj, hi⟩
    refine ⟨i, fun j hjr => by simp [hj j hjr], ?_⟩
    change (a + c) i < (b + c) i
    simp only [Finsupp.add_apply]
    exact (add_lt_add_iff_right (c i)).mpr hi

namespace HJO.Mac

/-! ### Rearranging an exponent vector into weakly decreasing order -/

section Antitone

variable {σ : Type*} [Fintype σ] [LinearOrder σ]

omit [LinearOrder σ] in
/-- A permutation of a finite type permutes the multiset of all its elements. -/
theorem map_univ_val_equiv (e : Equiv.Perm σ) :
    Multiset.map e Finset.univ.val = Finset.univ.val := by
  conv_rhs => rw [← Finset.map_univ_equiv e]
  rfl

omit [Fintype σ] in
/-- **Every exponent vector is a rearrangement of a weakly decreasing one**: sort the entries
decreasingly, which is `Tuple.sort` read through the increasing listing of the alphabet. -/
theorem exists_perm_antitone_comp [Finite σ] (α : σ → ℕ) :
    ∃ w : Equiv.Perm σ, Antitone (α ∘ w) := by
  have : Fintype σ := Fintype.ofFinite σ
  set e := monoEquivOfFin σ (rfl : Fintype.card σ = Fintype.card σ) with he
  set f : Fin (Fintype.card σ) → ℕᵒᵈ := fun k => OrderDual.toDual (α (e k)) with hf
  refine ⟨Equiv.permCongr e.toEquiv (Tuple.sort f), fun x y hxy => ?_⟩
  have h := Tuple.monotone_sort f (show e.symm x ≤ e.symm y from e.symm.monotone hxy)
  simp only [Function.comp_apply, hf, OrderDual.toDual_le_toDual] at h
  simpa [Equiv.permCongr_apply] using h

/-- **Among the rearrangements of one exponent vector the weakly decreasing one is the largest for
the lexicographic order.** At the least index at which they differ the two vectors have the same
multiset of remaining entries, and the weakly decreasing one attains the largest of them there.

This is the Step 3 of `HJO.Mac.macOpComp_msymm_sub_smul_mem_span`, and the only place the weak
decrease of a partition enters the triangularity. -/
theorem toLex_le_of_antitone {α β : σ →₀ ℕ} (hα : Antitone α)
    (h : Multiset.map β Finset.univ.val = Multiset.map α Finset.univ.val) :
    toLex β ≤ toLex α := by
  classical
  rcases eq_or_ne β α with rfl | hne
  · exact le_rfl
  have hne' : {i ∈ (Finset.univ : Finset σ) | β i ≠ α i}.Nonempty := by
    obtain ⟨i, hi⟩ := Finsupp.ne_iff.mp hne
    exact ⟨i, by simp [hi]⟩
  set i₀ := {i ∈ (Finset.univ : Finset σ) | β i ≠ α i}.min' hne' with hi₀def
  have hi₀ : β i₀ ≠ α i₀ := by
    have := Finset.min'_mem _ hne'
    simpa [hi₀def] using this
  have hagree : ∀ j, j < i₀ → β j = α j := fun j hj => by
    by_contra hc
    exact absurd (Finset.min'_le _ j (by simp [hc])) (not_le.mpr hj)
  have hlow : Multiset.map β (Multiset.filter (fun i => i < i₀) Finset.univ.val)
      = Multiset.map α (Multiset.filter (fun i => i < i₀) Finset.univ.val) :=
    Multiset.map_congr rfl fun j hj => hagree j (by simpa using hj)
  have hsplit : Multiset.map β (Multiset.filter (fun i => ¬ i < i₀) Finset.univ.val)
      = Multiset.map α (Multiset.filter (fun i => ¬ i < i₀) Finset.univ.val) := by
    have h2 := h
    rw [← Multiset.filter_add_not (fun i => i < i₀) Finset.univ.val, Multiset.map_add,
      Multiset.map_add, hlow] at h2
    exact add_left_cancel h2
  have hmem : β i₀ ∈ Multiset.map α (Multiset.filter (fun i => ¬ i < i₀) Finset.univ.val) := by
    rw [← hsplit]
    exact Multiset.mem_map_of_mem _
      (Multiset.mem_filter.mpr ⟨Finset.mem_val.mpr (Finset.mem_univ _), not_lt.mpr le_rfl⟩)
  obtain ⟨k, hk, hkv⟩ := Multiset.mem_map.mp hmem
  have hik : i₀ ≤ k := not_lt.mp (by simpa using Multiset.of_mem_filter hk)
  refine le_of_lt (Finsupp.Lex.lt_iff.mpr ⟨i₀, fun m hm => ?_, ?_⟩)
  · simpa using hagree m hm
  · simp only [ofLex_toLex]
    exact lt_of_le_of_ne (hkv ▸ hα hik) hi₀

/-- There is only one weakly decreasing rearrangement of an exponent vector. -/
theorem eq_of_antitone {α β : σ →₀ ℕ} (hα : Antitone α) (hβ : Antitone β)
    (h : Multiset.map β Finset.univ.val = Multiset.map α Finset.univ.val) : β = α :=
  toLex.injective (le_antisymm (toLex_le_of_antitone hα h) (toLex_le_of_antitone hβ h.symm))

variable [DecidableEq σ] {d : ℕ}

omit [LinearOrder σ] in
/-- Two multisets of letters with the same multiplicity partition have the same multiset of
multiplicities over the whole alphabet: they differ by a permutation of the alphabet. -/
theorem map_toFinsupp_univ_val_eq_of_ofSym_eq {a b : Sym σ d}
    (h : Nat.Partition.ofSym a = Nat.Partition.ofSym b) :
    Multiset.map (Multiset.toFinsupp b.1) Finset.univ.val
      = Multiset.map (Multiset.toFinsupp a.1) Finset.univ.val := by
  obtain ⟨w, rfl⟩ := Nat.Partition.ofSym_eq_iff_exists_perm.mp h
  change Multiset.map (Multiset.toFinsupp (a.1.map w)) Finset.univ.val = _
  rw [Multiset.toFinsupp_map, show ((Finsupp.mapDomain w (Multiset.toFinsupp a.1) : σ →₀ ℕ) :
      σ → ℕ) = (Multiset.toFinsupp a.1) ∘ (w.symm : σ → σ) from
    funext fun x => Finsupp.mapDomain_equiv_apply (f := w) _ x,
    ← Multiset.map_map, map_univ_val_equiv]

end Antitone

/-! ### The exponent vector of a partition -/

section PartExp

/-- The index set of the monomial symmetric basis of `𝒮_{n,d}`: the partitions of `d` with at most
`#σ` parts. This is the set of `μ` with `|μ| = d` and `μ_{n+1} = 0`, the second
condition saying that at most `n` of the entries are nonzero. -/
abbrev PartIdx (σ : Type*) [Fintype σ] (d : ℕ) : Type :=
  {μ : Nat.Partition d // μ.parts.card ≤ Fintype.card σ}

variable (σ : Type*) [Fintype σ] [LinearOrder σ] {d : ℕ}

/-- The letters of the alphabet listed in increasing order: the order isomorphism
`Fin #σ ≃o σ`, the identity at `σ = Fin n`. -/
noncomputable def letterEquiv : Fin (Fintype.card σ) ≃o σ :=
  monoEquivOfFin σ rfl

variable {σ}

/-- The number of letters above `i` is `n - 1 - k`, where `k` is the position of `i` in the
increasing listing of the alphabet. -/
theorem card_filter_lt (i : σ) :
    #{j ∈ (Finset.univ : Finset σ) | i < j}
      = Fintype.card σ - 1 - ((letterEquiv σ).symm i : ℕ) := by
  rw [← Fin.card_Ioi ((letterEquiv σ).symm i)]
  refine Finset.card_equiv (letterEquiv σ).symm.toEquiv fun j => ?_
  simp [Finset.mem_Ioi, OrderIso.lt_iff_lt]

variable (σ) [DecidableEq σ]

/-- A weakly decreasing multiset of `d` letters representing the partition `μ`: the orbit `μ` is
nonempty (`Nat.Partition.exists_sym_ofSym_eq`) and any member of it can be sorted
(`exists_perm_antitone_comp`). -/
theorem exists_antitone_sym (μ : PartIdx σ d) :
    ∃ a : Sym σ d, Nat.Partition.ofSym a = μ.1 ∧ Antitone (Multiset.toFinsupp a.1) := by
  obtain ⟨a₀, ha₀⟩ := Nat.Partition.exists_sym_ofSym_eq μ.2
  obtain ⟨w, hw⟩ := exists_perm_antitone_comp (Multiset.toFinsupp a₀.1 : σ → ℕ)
  refine ⟨a₀.map (w⁻¹ : Equiv.Perm σ), by rw [Nat.Partition.ofSym_map, ha₀], ?_⟩
  have : ((Multiset.toFinsupp ((a₀.map (w⁻¹ : Equiv.Perm σ)).1) : σ →₀ ℕ) : σ → ℕ)
      = (Multiset.toFinsupp a₀.1 : σ → ℕ) ∘ w := by
    change ((Multiset.toFinsupp (a₀.1.map (w⁻¹ : Equiv.Perm σ)) : σ →₀ ℕ) : σ → ℕ) = _
    rw [Multiset.toFinsupp_map]
    exact funext fun x => Finsupp.mapDomain_equiv_apply (f := (w⁻¹ : Equiv.Perm σ)) _ x
  rw [this]
  exact hw

/-- A weakly decreasing multiset of `d` letters representing the partition `μ`. -/
noncomputable def partSym (μ : PartIdx σ d) : Sym σ d := (exists_antitone_sym σ μ).choose

/-- **The exponent vector `\bar\mu` of a partition** in the alphabet `σ`: the weakly decreasing
vector whose nonzero entries are the parts of `μ`, read along the order of `σ`. It is the
vector `(μ_1, …, μ_n)`, and `eq_partExp` says the choice in the definition is not one. -/
noncomputable def partExp (μ : PartIdx σ d) : σ →₀ ℕ := Multiset.toFinsupp (partSym σ μ).1

variable {σ}

/-- `partSym` represents the partition it was chosen for. -/
theorem ofSym_partSym (μ : PartIdx σ d) : Nat.Partition.ofSym (partSym σ μ) = μ.1 :=
  (exists_antitone_sym σ μ).choose_spec.1

/-- `\bar\mu` is weakly decreasing, a partition being weakly decreasing. -/
theorem antitone_partExp (μ : PartIdx σ d) : Antitone (partExp σ μ) :=
  (exists_antitone_sym σ μ).choose_spec.2

/-- `\bar\mu` has total degree `d`, that is `|μ| = d`. -/
theorem degree_partExp (μ : PartIdx σ d) : (partExp σ μ).degree = d :=
  degree_eq_iff_exists_sym.mpr ⟨partSym σ μ, rfl⟩

/-- **`\bar\mu` is the only weakly decreasing exponent vector in the orbit `μ`.** -/
theorem eq_partExp {μ : PartIdx σ d} {a : Sym σ d} (ha : Nat.Partition.ofSym a = μ.1)
    (hanti : Antitone (Multiset.toFinsupp a.1)) : Multiset.toFinsupp a.1 = partExp σ μ :=
  eq_of_antitone (antitone_partExp μ) hanti
    (map_toFinsupp_univ_val_eq_of_ofSym_eq ((ofSym_partSym μ).trans ha.symm))

variable {R : Type*} [CommSemiring R]

/-- **The functionals dual to the monomial symmetric basis**: the coefficient of `x^{\bar\mu}` in
`m_ν` is `1` when `μ = ν` and `0` otherwise. -/
theorem coeff_partExp_msymm (μ ν : PartIdx σ d) :
    coeff (partExp σ μ) (msymm σ R ν.1) = if μ = ν then 1 else 0 := by
  rw [partExp, coeff_msymm, ofSym_partSym]
  exact if_congr (by rw [Subtype.ext_iff]) rfl rfl

/-- Every exponent of `m_μ` is at most `\bar\mu` for the lexicographic order. -/
theorem toLex_le_of_mem_support_msymm {μ : PartIdx σ d} {c : σ →₀ ℕ}
    (hc : c ∈ (msymm σ R μ.1).support) : toLex c ≤ toLex (partExp σ μ) := by
  have hdeg : c.degree = d := by
    rw [Finsupp.degree_eq_weight_one]
    exact (msymm_isHomogeneous μ.1) (mem_support_iff.mp hc)
  obtain ⟨a, rfl⟩ := degree_eq_iff_exists_sym.mp hdeg
  have ha : Nat.Partition.ofSym a = μ.1 := by
    by_contra hne
    exact mem_support_iff.mp hc
      (by rw [coeff_msymm]; exact ite_eq_right fun h => absurd h hne)
  exact toLex_le_of_antitone (antitone_partExp μ)
    (map_toFinsupp_univ_val_eq_of_ofSym_eq ((ofSym_partSym μ).trans ha.symm))

/-- `m_μ` is not the zero polynomial: the monomial `x^{\bar\mu}` occurs in it. -/
theorem msymm_ne_zero [Nontrivial R] (μ : PartIdx σ d) : msymm σ R μ.1 ≠ 0 := fun h => by
  simpa [h] using (coeff_partExp_msymm (R := R) μ μ).symm

/-- **The leading exponent of `m_μ` is `\bar\mu`**: the monomial `x^{\bar\mu}` occurs, and no
larger one does. -/
theorem lex_degree_msymm [Nontrivial R] (μ : PartIdx σ d) :
    MonomialOrder.lex.degree (msymm σ R μ.1) = partExp σ μ :=
  MonomialOrder.degree_eq_of_coeff_ne_zero
    (by rw [coeff_partExp_msymm]; simp)
    fun c hc => MonomialOrder.lex_le_iff.mpr (toLex_le_of_mem_support_msymm hc)

/-- **The leading coefficient of `m_μ` is `1`**: the monomial symmetric polynomials are monic. -/
theorem lex_leadingCoeff_msymm [Nontrivial R] (μ : PartIdx σ d) :
    MonomialOrder.lex.leadingCoeff (msymm σ R μ.1) = 1 := by
  rw [MonomialOrder.leadingCoeff, lex_degree_msymm, coeff_partExp_msymm]
  simp

/-- **Distinct partitions have distinct exponent vectors**, so `partExp` indexes the monomial
symmetric basis faithfully: the coefficient of `x^{\bar\mu}` separates `m_μ` from the other
members of the family. -/
theorem partExp_injective : Function.Injective (partExp σ : PartIdx σ d → (σ →₀ ℕ)) := by
  intro μ ν h
  by_contra hne
  have h1 := coeff_partExp_msymm (R := ℕ) μ ν
  rw [ite_eq_right fun hc => absurd hc hne, h, coeff_partExp_msymm, ite_eq_left rfl] at h1
  exact one_ne_zero h1

end PartExp

/-! ### The monomial symmetric polynomials as elements of the graded piece -/

section Mem

variable {σ : Type*} [Fintype σ] [DecidableEq σ] {R : Type*} [CommSemiring R] {d : ℕ}

/-- `m_μ`, read as an element of `𝒮_{n,d}`: it is symmetric (`MvPolynomial.msymm_isSymmetric`) and
homogeneous of degree `d` (`MvPolynomial.msymm_isHomogeneous`). -/
@[hjo "def_mac_msymm"]
noncomputable def msymmMem (σ : Type*) [Fintype σ] [DecidableEq σ] (R : Type*) [CommSemiring R]
    {d : ℕ} (μ : PartIdx σ d) : symmetricHomogeneousSubmodule σ R d :=
  ⟨msymm σ R μ.1, mem_symmetricHomogeneousSubmodule.mpr
    ⟨msymm_isSymmetric σ R _, msymm_isHomogeneous _⟩⟩

@[simp]
theorem coe_msymmMem (μ : PartIdx σ d) :
    (msymmMem σ R μ : MvPolynomial σ R) = msymm σ R μ.1 := rfl

end Mem

/-! ### The Young diagram of a partition, and its eigenvalue -/

section Diagram

variable {σ : Type*} [Fintype σ] [LinearOrder σ] {d : ℕ}

/-- The row-length sequence of the exponent vector `α`: the `k`-th entry is the value of `α` at the
`k`-th smallest letter, and `0` beyond the alphabet. -/
noncomputable def rowLenSeqOf (σ : Type*) [Fintype σ] [LinearOrder σ] (α : σ →₀ ℕ) : ℕ → ℕ :=
  fun k => if h : k < Fintype.card σ then α (letterEquiv σ ⟨k, h⟩) else 0

theorem rowLenSeqOf_of_lt {α : σ →₀ ℕ} {k : ℕ} (h : k < Fintype.card σ) :
    rowLenSeqOf σ α k = α (letterEquiv σ ⟨k, h⟩) := dite_eq_left h

theorem rowLenSeqOf_of_le {α : σ →₀ ℕ} {k : ℕ} (h : Fintype.card σ ≤ k) :
    rowLenSeqOf σ α k = 0 := dite_eq_right (Nat.not_lt.mpr h)

/-- A weakly decreasing exponent vector gives a weakly decreasing row-length sequence. -/
theorem antitone_rowLenSeqOf {α : σ →₀ ℕ} (hα : Antitone α) : Antitone (rowLenSeqOf σ α) := by
  intro k l hkl
  rcases Nat.lt_or_ge l (Fintype.card σ) with hl | hl
  · rw [rowLenSeqOf_of_lt (lt_of_le_of_lt hkl hl), rowLenSeqOf_of_lt hl]
    exact hα ((letterEquiv σ).monotone (Fin.mk_le_mk.mpr hkl))
  · rw [rowLenSeqOf_of_le hl]
    exact Nat.zero_le _

/-- A row-length sequence vanishes beyond the alphabet, so it has finite support. -/
theorem finite_support_rowLenSeqOf (α : σ →₀ ℕ) : {k | rowLenSeqOf σ α k ≠ 0}.Finite :=
  Set.Finite.subset (Set.finite_Iio (Fintype.card σ)) fun _ hk =>
    lt_of_not_ge fun hle => hk (rowLenSeqOf_of_le hle)

/-- **The Young diagram of the partition `μ` in the alphabet `σ`**: the diagram whose `k`-th row
has `\bar\mu_k` cells. Its cells are the cells of `μ` and its size is `d`
(`card_partDiagram`). -/
noncomputable def partDiagram (σ : Type*) [Fintype σ] [LinearOrder σ] [DecidableEq σ] {d : ℕ}
    (μ : PartIdx σ d) : YoungDiagram :=
  HJO.Sym.ofRowLenSeq (rowLenSeqOf σ (partExp σ μ)) (antitone_rowLenSeqOf (antitone_partExp μ))
    (finite_support_rowLenSeqOf _)

variable [DecidableEq σ]

@[simp]
theorem rowLen_partDiagram (μ : PartIdx σ d) (k : ℕ) :
    (partDiagram σ μ).rowLen k = rowLenSeqOf σ (partExp σ μ) k :=
  HJO.Sym.rowLen_ofRowLenSeq k

/-- **The diagram of `μ` has `d` cells**: its rows have the entries of `\bar\mu` as lengths, and
`\bar\mu` has total degree `d`. -/
theorem card_partDiagram (μ : PartIdx σ d) : (partDiagram σ μ).card = d := by
  classical
  have hrow : ∀ k, (partDiagram σ μ).row k
      = {c ∈ (partDiagram σ μ).cells | c.1 = k} := fun k => rfl
  have hsupp : ∀ c ∈ (partDiagram σ μ).cells, c.1 ∈ Finset.range (Fintype.card σ) := by
    intro c hc
    refine Finset.mem_range.mpr (lt_of_not_ge fun hle => ?_)
    have := YoungDiagram.mem_iff_lt_rowLen.mp (show (c.1, c.2) ∈ partDiagram σ μ from hc)
    rw [rowLen_partDiagram, rowLenSeqOf_of_le hle] at this
    exact Nat.not_lt_zero _ this
  rw [YoungDiagram.card, Finset.card_eq_sum_card_fiberwise hsupp]
  calc ∑ k ∈ Finset.range (Fintype.card σ), #{c ∈ (partDiagram σ μ).cells | c.1 = k}
      = ∑ k ∈ Finset.range (Fintype.card σ), rowLenSeqOf σ (partExp σ μ) k :=
        Finset.sum_congr rfl fun k _ => by
          rw [← hrow k, ← YoungDiagram.rowLen_eq_card, rowLen_partDiagram]
    _ = ∑ k : Fin (Fintype.card σ), rowLenSeqOf σ (partExp σ μ) k :=
        (Fin.sum_univ_eq_sum_range _ _).symm
    _ = ∑ i : σ, partExp σ μ i :=
        Fintype.sum_equiv (letterEquiv σ).toEquiv _ _ fun k => by
          rw [rowLenSeqOf_of_lt k.2]; rfl
    _ = d := by
        have hsum : (partExp σ μ).degree = ∑ i : σ, partExp σ μ i := by
          rw [Finsupp.degree_apply]
          exact Finset.sum_subset (Finset.subset_univ _)
            fun i _ hi => Finsupp.notMem_support_iff.mp hi
        rw [← hsum, degree_partExp]

/-- **The eigenvalue of `μ` in the alphabet `σ`**: `E_n(μ) = ∑_i q^{\bar\mu_i} u^{\#\{j : i < j\}}`,
the exponent of `u` at the letter `i` being the number of letters above `i`. This is the form the
triangularity produces, `HJO.Sym.macdonaldEigenvalue`'s `u^{n-i}` being that count. -/
theorem macdonaldEigenvalue_partDiagram {K : Type*} [CommSemiring K] (q u : K)
    (μ : PartIdx σ d) :
    HJO.Sym.macdonaldEigenvalue q u (Fintype.card σ) (partDiagram σ μ)
      = ∑ i : σ, q ^ partExp σ μ i * u ^ #{j ∈ (Finset.univ : Finset σ) | i < j} := by
  classical
  rw [HJO.Sym.macdonaldEigenvalue, ← Fin.sum_univ_eq_sum_range
    (fun k => q ^ (partDiagram σ μ).rowLen k * u ^ (Fintype.card σ - 1 - k))]
  refine Fintype.sum_equiv (letterEquiv σ).toEquiv _ _ fun k => ?_
  rw [rowLen_partDiagram, rowLenSeqOf_of_lt k.2, card_filter_lt]
  simp

end Diagram

end HJO.Mac
