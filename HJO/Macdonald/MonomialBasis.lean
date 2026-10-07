/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Mathlib.Combinatorics.Enumerative.Partition.Basic
public import Mathlib.Data.Finsupp.Multiset
public import Mathlib.LinearAlgebra.Basis.Basic
public import Mathlib.RingTheory.MvPolynomial.MonomialOrder
public import HJO.Macdonald.FiniteAlphabet
public meta import HJO.Attr

/-! # The monomial symmetric polynomials are a basis of a graded piece

Fix a finite alphabet `σ` and a degree `d`. The monomial symmetric polynomials `m_μ`, indexed by
the partitions `μ` of `d` with at most `#σ` parts, are a basis of `𝒮_{n,d}`. This is
`MvPolynomial.exists_basis_symmetricHomogeneousSubmodule_msymm`, and it is the coordinate system in
which Macdonald's operator is triangular.

## Organisation

The helper lemmas sit in the namespaces they belong to (`Multiset`, `Nat.Partition`,
`MvPolynomial`), and the five that the leading-exponent calculus downstream needs are public:
`Nat.Partition.ofSym_eq_iff_exists_perm`, `Nat.Partition.exists_sym_ofSym_eq`,
`Nat.Partition.parts_card_le`, `MvPolynomial.coeff_msymm` and `MvPolynomial.msymm_eq_sum_monomial`.

## Main results

* `MvPolynomial.exists_basis_symmetricHomogeneousSubmodule_msymm`: the family `m_μ`, indexed by the
  partitions `μ` of `d` with at most `#σ` parts, is an `R`-basis of the symmetric polynomials in
  `σ` that are homogeneous of degree `d` -- and the basis produced is that very family.
* `MvPolynomial.coeff_msymm`: the coefficients of `m_μ` are the indicator function of the orbit `μ`.
* `Nat.Partition.ofSym_eq_iff_exists_perm`: the fibres of `Nat.Partition.ofSym` are the orbits of
  `Equiv.Perm σ` on `Sym σ d`.
* `MonomialOrder.degree_eq_of_coeff_ne_zero`, `MonomialOrder.leadingCoeff_prod`: two gaps in
  Mathlib's `MonomialOrder` interface, used here and downstream.

## Implementation notes

`R` is only a commutative semiring, so there is no subtraction: the spanning half cannot be a
"strip off one monomial and induct on the support" argument, and linear independence cannot be
phrased as "a vanishing combination has zero coefficients". Both are therefore done in the form
that survives a semiring -- the spanning by regrouping the finite sum `∑_{a : Sym σ d} coeff · x^a`
over the fibres of `Nat.Partition.ofSym` (`Fintype.sum_fiberwise`), and the independence as
injectivity of `Finsupp.linearCombination` (which is its definition), obtained from a family of
functionals that is dual to the family `m_μ`.

Four facts used here are missing from Mathlib. Three concern `msymm` and `Nat.Partition.ofSym`,
where Mathlib defines `msymm`, proves it symmetric and stops: that the fibres of
`Nat.Partition.ofSym` are the `Equiv.Perm σ`-orbits of `Sym σ d`
(`Nat.Partition.ofSym_eq_iff_exists_perm`) and are nonempty exactly for the partitions with at most
`#σ` parts (`Nat.Partition.exists_sym_ofSym_eq`), that `msymm` is homogeneous of degree `d`
(`MvPolynomial.msymm_isHomogeneous`), and that `Multiset.toFinsupp` carries `Multiset.map` to
`Finsupp.mapDomain` (`Multiset.toFinsupp_map`). The fourth is linear algebra over a semiring: a
family admitting a dual family of functionals is linearly independent, which is Mathlib's
`LinearIndependent.of_pairwise_dual_eq_zero_one` with its `Ring` weakened to a `Semiring`, the
`linearIndependent_iff'` route of the latter being unavailable here.

The basis is produced as `Module.Basis.span` of the family, transported along `LinearEquiv.ofEq`,
so that the values are the `m_μ` on the nose rather than up to an unfolding.

## References

This file proves `MvPolynomial.exists_basis_symmetricHomogeneousSubmodule_msymm`, on the definitions
`HJO.Sym.rowLenSeq`, `HJO.Sym.cells`, `MvPolynomial.symmetricSubalgebra`,
`MvPolynomial.symmetricHomogeneousSubmodule` and `HJO.Mac.msymmMem`.
-/

@[expose] public section

open Finset MvPolynomial

/-! ### Two gaps in Mathlib's monomial-order interface -/

namespace MonomialOrder

variable {σ : Type*} {m : MonomialOrder σ} {R : Type*} [CommSemiring R]

/-- The leading exponent, read off a witness: an exponent whose coefficient is nonzero and which
no exponent of the support exceeds is *the* leading exponent. -/
theorem degree_eq_of_coeff_ne_zero {f : MvPolynomial σ R} {d : σ →₀ ℕ} (hd : coeff d f ≠ 0)
    (hle : ∀ c ∈ f.support, m.toSyn c ≤ m.toSyn d) : m.degree f = d :=
  m.toSyn.injective
    (le_antisymm (m.degree_le_iff.mpr hle) (m.le_degree (mem_support_iff.mpr hd)))

/-- The leading coefficient of a finite product is the product of the leading coefficients.
Mathlib has the two-factor `MonomialOrder.leadingCoeff_mul` and stops there. -/
theorem leadingCoeff_prod [NoZeroDivisors R] {ι : Type*} (s : Finset ι)
    (P : ι → MvPolynomial σ R) :
    m.leadingCoeff (∏ i ∈ s, P i) = ∏ i ∈ s, m.leadingCoeff (P i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [Finset.prod_empty, m.leadingCoeff_one]
  | insert a s ha ih =>
      rw [Finset.prod_insert ha, Finset.prod_insert ha, m.leadingCoeff_mul, ih]

end MonomialOrder

/-! ### A family with a dual family of functionals is independent -/

section Dual

variable {R : Type*} [Semiring R]

/-- A family of vectors admitting a dual family of functionals is linearly independent: a functional
reads off its own coefficient from a finite combination, so `Finsupp.linearCombination` is
injective. This is Mathlib's `LinearIndependent.of_pairwise_dual_eq_zero_one` over a semiring,
where linear independence is not "a vanishing combination has zero coefficients". -/
private theorem linearIndependent_of_pairwise_dual_eq_zero_one {ι M : Type*} [AddCommMonoid M]
    [Module R M] (v : ι → M) (f : ι → M →ₗ[R] R) (h1 : Pairwise fun i j => f i (v j) = 0)
    (h2 : ∀ i, f i (v i) = 1) : LinearIndependent R v := by
  have key (i : ι) (l : ι →₀ R) : f i (Finsupp.linearCombination R v l) = l i := by
    rw [Finsupp.linearCombination_apply, Finsupp.sum, map_sum, Finset.sum_eq_single i]
    · rw [map_smul, h2, smul_eq_mul, mul_one]
    · exact fun j _ hj => by rw [map_smul, h1 (Ne.symm hj), smul_zero]
    · exact fun hi => by rw [Finsupp.notMem_support_iff.mp hi, zero_smul, map_zero]
  exact fun l₁ l₂ hl => Finsupp.ext fun i => by rw [← key i l₁, ← key i l₂, hl]

end Dual

/-! ### Multisets of letters and exponent vectors -/

namespace Multiset

variable {σ τ : Type*} [DecidableEq σ] [DecidableEq τ]

/-- Recording multiplicities turns a map of the alphabet into a map of exponent vectors; this is
`Finsupp.toMultiset_map` read through the inverse bijection. -/
theorem toFinsupp_map (f : σ → τ) (m : Multiset σ) :
    Multiset.toFinsupp (m.map f) = Finsupp.mapDomain f (Multiset.toFinsupp m) := by
  rw [Multiset.toFinsupp_eq_iff, ← Finsupp.toMultiset_map, Multiset.toFinsupp_toMultiset]

end Multiset

namespace MvPolynomial

section Dictionary

variable {σ : Type*} [DecidableEq σ] {R : Type*} [CommSemiring R] {d : ℕ}

/-- The product of the variables indexed by a multiset of letters is the monomial whose exponent
vector records the multiplicities of that multiset. -/
theorem prod_map_X_eq_monomial (m : Multiset σ) :
    (m.map (X : σ → MvPolynomial σ R)).prod = monomial (Multiset.toFinsupp m) 1 := by
  rw [Finset.prod_multiset_map_count, ← prod_X_pow_eq_monomial, Multiset.toFinsupp_support]
  exact Finset.prod_congr rfl fun x _ => by rw [Multiset.toFinsupp_apply]

/-- The exponent vectors of total degree `d` are exactly the multiplicity vectors of the multisets
of `d` letters: the monomials of degree `d` are indexed by `Sym σ d`. -/
theorem degree_eq_iff_exists_sym {α : σ →₀ ℕ} :
    α.degree = d ↔ ∃ a : Sym σ d, Multiset.toFinsupp a.1 = α := by
  refine ⟨fun hα => ⟨⟨Finsupp.toMultiset α, ?_⟩, Finsupp.toMultiset_toFinsupp α⟩, ?_⟩
  · simpa [Finsupp.card_toMultiset, Finsupp.sum, Finsupp.degree_apply] using hα
  · rintro ⟨a, rfl⟩
    simp [Finsupp.degree_apply]

/-- Distinct multisets of `d` letters have distinct multiplicity vectors, so they index distinct
monomials. -/
theorem toFinsupp_val_injective :
    Function.Injective fun a : Sym σ d => Multiset.toFinsupp a.1 :=
  fun _ _ h => Sym.coe_injective (Multiset.toFinsupp.injective h)

end Dictionary

end MvPolynomial

namespace Nat.Partition

variable {σ : Type*} [DecidableEq σ] {d : ℕ}

/-- The parts of `Nat.Partition.ofSym a`, unfolded. -/
theorem parts_ofSym (a : Sym σ d) :
    (Nat.Partition.ofSym a).parts = Multiset.map (fun x => Multiset.count x a.1) a.1.dedup :=
  rfl

omit [DecidableEq σ] in
/-- Two functions on a finite type taking the same multiset of values differ by a permutation of
the source: the fibres over each value are equinumerous, so they can be matched up. -/
private theorem exists_perm_comp_eq [Fintype σ] {β : Type*} {f g : σ → β}
    (h : Multiset.map f Finset.univ.val = Multiset.map g Finset.univ.val) :
    ∃ w : Equiv.Perm σ, ∀ x, g (w x) = f x := by
  classical
  have hcount : ∀ (u : σ → β) (b : β), Multiset.count b (Multiset.map u Finset.univ.val)
      = Fintype.card {x : σ // u x = b} := fun u b => by
    simp [Multiset.count_map, Fintype.card_subtype, Finset.card_def, Finset.filter_val, eq_comm]
  exact ⟨Equiv.ofFiberEquiv fun b => Fintype.equivOfCardEq (by rw [← hcount f b, ← hcount g b, h]),
    fun x => Equiv.ofFiberEquiv_map _ x⟩

/-- The multiplicities of `m` read over the whole alphabet are its positive multiplicities padded
with zeros, one for each letter that does not occur; compare `Equiv.Perm.parts_partition`. -/
private theorem map_count_univ_val [Fintype σ] (m : Multiset σ) :
    Multiset.map (fun x => Multiset.count x m) Finset.univ.val
      = Multiset.map (fun x => Multiset.count x m) m.dedup
        + Multiset.replicate (Fintype.card σ - m.dedup.card) 0 := by
  have hmem : Multiset.filter (fun x => x ∈ m) Finset.univ.val = m.dedup :=
    (Multiset.Nodup.ext (Finset.univ.nodup.filter _) m.nodup_dedup).mpr (by simp)
  have hcard := congrArg Multiset.card (Multiset.filter_add_not (fun x => x ∈ m) Finset.univ.val)
  rw [Multiset.card_add, hmem, show Finset.univ.val.card = Fintype.card σ from Finset.card_univ]
    at hcard
  conv_lhs => rw [← Multiset.filter_add_not (fun x => x ∈ m) Finset.univ.val]
  rw [Multiset.map_add, hmem]
  refine congrArg _ (Multiset.eq_replicate.mpr ⟨?_, by simp +contextual⟩)
  simp only [Multiset.card_map]
  omega

/-- Two multisets of `d` letters have the same multiplicity partition exactly when a permutation of
the alphabet carries one to the other: the fibres of `Nat.Partition.ofSym` are the orbits of
`Equiv.Perm σ` acting on `Sym σ d`. The `←` direction is `Nat.Partition.ofSym_map`. -/
theorem ofSym_eq_iff_exists_perm [Finite σ] {a b : Sym σ d} :
    Nat.Partition.ofSym a = Nat.Partition.ofSym b ↔ ∃ w : Equiv.Perm σ, a.map w = b := by
  refine ⟨fun h => ?_, fun ⟨w, hw⟩ => hw ▸ (Nat.Partition.ofSym_map w a).symm⟩
  let := Fintype.ofFinite σ
  have hparts : Multiset.map (fun x => Multiset.count x a.1) a.1.dedup
      = Multiset.map (fun x => Multiset.count x b.1) b.1.dedup := by
    rw [← parts_ofSym, ← parts_ofSym, h]
  have hdedup : a.1.dedup.card = b.1.dedup.card := by
    simpa using congrArg Multiset.card hparts
  obtain ⟨w, hw⟩ := exists_perm_comp_eq (f := fun x => Multiset.count x a.1)
    (g := fun x => Multiset.count x b.1)
    (by rw [map_count_univ_val, map_count_univ_val, hparts, hdedup])
  refine ⟨w, Sym.coe_injective (Multiset.ext.mpr (w.surjective.forall.mpr fun x => ?_))⟩
  rw [Sym.coe_map, Multiset.count_map_eq_count' _ _ w.injective]
  exact (hw x).symm

/-- A multiset of positive naturals of size at most `#t` is the multiset of positive multiplicities
of a multiset of letters drawn from `t`. -/
private theorem exists_multiset_map_count_dedup_eq (p : Multiset ℕ) (hp : ∀ k ∈ p, 0 < k)
    (t : Finset σ) (ht : p.card ≤ t.card) :
    ∃ m : Multiset σ, m.card = p.sum ∧ m.toFinset ⊆ t ∧
      Multiset.map (fun x => Multiset.count x m) m.dedup = p := by
  induction p using Multiset.induction generalizing t with
  | empty => exact ⟨0, by simp, by simp, by simp⟩
  | cons k q ih =>
      have hk : 0 < k := hp k (Multiset.mem_cons_self _ _)
      obtain ⟨x, hx⟩ : t.Nonempty :=
        Finset.card_pos.mp (by simp only [Multiset.card_cons] at ht; omega)
      obtain ⟨m, hmcard, hmsub, hmcount⟩ :=
        ih (fun j hj => hp j (Multiset.mem_cons_of_mem hj)) (t.erase x)
          (by rw [Finset.card_erase_of_mem hx]; simp only [Multiset.card_cons] at ht; omega)
      have hxm : x ∉ m := fun h =>
        (Finset.mem_erase.mp (hmsub (Multiset.mem_toFinset.mpr h))).1 rfl
      refine ⟨Multiset.replicate k x + m, by simp [hmcard], ?_, ?_⟩
      · simp only [Multiset.toFinset_add, Finset.union_subset_iff, Multiset.toFinset_replicate,
          hk.ne', ite_false]
        exact ⟨by simpa using hx, hmsub.trans (Finset.erase_subset _ _)⟩
      · have hdedup : (Multiset.replicate k x + m).dedup = x ::ₘ m.dedup :=
          (Multiset.Nodup.ext (Multiset.nodup_dedup _)
            (Multiset.nodup_cons.mpr ⟨fun h => hxm (Multiset.mem_dedup.mp h),
              m.nodup_dedup⟩)).mpr fun y => by simp [Multiset.mem_replicate, hk.ne']
        rw [hdedup, Multiset.map_cons]
        congr 1
        · simp [hxm]
        · refine (Multiset.map_congr rfl fun y hy => ?_).trans hmcount
          have hyx : y ≠ x := fun h => hxm (h ▸ Multiset.mem_dedup.mp hy)
          simp [Multiset.count_replicate, Ne.symm hyx]

/-- A multiplicity partition has at most `#σ` parts, one for each letter that occurs. -/
theorem parts_card_le [Fintype σ] (a : Sym σ d) :
    (Nat.Partition.ofSym a).parts.card ≤ Fintype.card σ := by
  rw [parts_ofSym, Multiset.card_map]
  exact (Finset.card_le_univ a.1.toFinset).trans_eq Finset.card_univ

/-- Every partition of `d` with at most `#σ` parts is the multiplicity partition of a multiset of
`d` letters: the orbit it names is not empty. -/
theorem exists_sym_ofSym_eq [Fintype σ] {μ : Nat.Partition d}
    (hμ : μ.parts.card ≤ Fintype.card σ) : ∃ a : Sym σ d, Nat.Partition.ofSym a = μ := by
  obtain ⟨m, hcard, -, hcount⟩ := exists_multiset_map_count_dedup_eq μ.parts
    (fun k hk => μ.parts_pos hk) (Finset.univ : Finset σ) (by rwa [Finset.card_univ])
  exact ⟨⟨m, by rw [hcard, μ.parts_sum]⟩, Nat.Partition.ext hcount⟩

end Nat.Partition

namespace MvPolynomial

/-! ### The monomial symmetric polynomials, monomial by monomial -/

section Msymm

variable {σ : Type*} [Fintype σ] [DecidableEq σ] {R : Type*} [CommSemiring R] {d : ℕ}

/-- `m_μ` is the sum of the monomials of the orbit `μ`, each with coefficient `1`. -/
theorem msymm_eq_sum_monomial (μ : Nat.Partition d) :
    msymm σ R μ = ∑ a : {a : Sym σ d // Nat.Partition.ofSym a = μ},
      monomial (Multiset.toFinsupp (a.1).1) (1 : R) :=
  Finset.sum_congr rfl fun _ _ => prod_map_X_eq_monomial _

/-- Every monomial of `m_μ` has total degree `d`; Mathlib has `msymm_isSymmetric` but not this. -/
theorem msymm_isHomogeneous (μ : Nat.Partition d) : (msymm σ R μ).IsHomogeneous d := by
  rw [msymm_eq_sum_monomial]
  exact IsHomogeneous.sum _ _ _ fun a _ =>
    isHomogeneous_monomial _ (degree_eq_iff_exists_sym.mpr ⟨a.1, rfl⟩)

/-- The coefficients of `m_μ` are the indicator function of the orbit `μ`. -/
theorem coeff_msymm (μ : Nat.Partition d) (b : Sym σ d) :
    coeff (Multiset.toFinsupp b.1) (msymm σ R μ) = if Nat.Partition.ofSym b = μ then 1 else 0 := by
  rw [msymm_eq_sum_monomial, coeff_sum]
  simp only [coeff_monomial, toFinsupp_val_injective.eq_iff]
  split_ifs with h
  · rw [Finset.sum_eq_single_of_mem ⟨b, h⟩ (mem_univ _)
      fun a _ ha => ite_eq_right fun hc => ha (Subtype.ext hc), ite_eq_left rfl]
  · exact Finset.sum_eq_zero fun a _ => ite_eq_right fun hc => h (by rw [← hc]; exact a.2)

omit [Fintype σ] in
/-- A symmetric polynomial has a single coefficient on each orbit of monomials. -/
theorem coeff_eq_of_ofSym_eq [Finite σ] {f : MvPolynomial σ R} (hf : f.IsSymmetric)
    {a b : Sym σ d} (h : Nat.Partition.ofSym a = Nat.Partition.ofSym b) :
    coeff (Multiset.toFinsupp a.1) f = coeff (Multiset.toFinsupp b.1) f := by
  obtain ⟨w, rfl⟩ := Nat.Partition.ofSym_eq_iff_exists_perm.mp h
  change coeff (Multiset.toFinsupp a.1) f = coeff (Multiset.toFinsupp (a.1.map w)) f
  rw [Multiset.toFinsupp_map, ← coeff_rename_mapDomain (⇑w) w.injective f (Multiset.toFinsupp a.1),
    hf w]

end Msymm

/-! ### The basis -/

section Basis

variable {σ : Type*} [Fintype σ] [DecidableEq σ] {R : Type*} [CommSemiring R] {d : ℕ}

/-- A polynomial homogeneous of degree `d` in a finite alphabet is the sum of its monomials, which
are indexed by the multisets of `d` letters. -/
private theorem eq_sum_monomial_of_isHomogeneous {f : MvPolynomial σ R} (hf : f.IsHomogeneous d) :
    f = ∑ a : Sym σ d, monomial (Multiset.toFinsupp a.1) (coeff (Multiset.toFinsupp a.1) f) := by
  have hsupp : f.support ⊆ univ.image fun a : Sym σ d => Multiset.toFinsupp a.1 := fun α hα => by
    obtain ⟨a, rfl⟩ := degree_eq_iff_exists_sym.mp
      (not_ne_iff.mp fun hc => mem_support_iff.mp hα (hf.coeff_eq_zero hc))
    exact mem_image_of_mem _ (mem_univ a)
  calc f = ∑ α ∈ f.support, monomial α (coeff α f) := (support_sum_monomial_coeff f).symm
    _ = ∑ α ∈ univ.image fun a : Sym σ d => Multiset.toFinsupp a.1, monomial α (coeff α f) :=
        Finset.sum_subset hsupp fun α _ hα => by rw [notMem_support_iff.mp hα, monomial_zero]
    _ = _ := Finset.sum_image fun _ _ _ _ hab => toFinsupp_val_injective hab

/-- The part of a symmetric `f` carried by one orbit of monomials is a multiple of `m_μ`: on that
orbit `f` has a single coefficient, and the orbit's monomials sum to `m_μ`. -/
private theorem sum_orbit_monomial_eq_smul_msymm {f : MvPolynomial σ R} (hf : f.IsSymmetric)
    {μ : Nat.Partition d} (a₀ : {a : Sym σ d // Nat.Partition.ofSym a = μ}) :
    ∑ a : {a : Sym σ d // Nat.Partition.ofSym a = μ},
        monomial (Multiset.toFinsupp (a.1).1) (coeff (Multiset.toFinsupp (a.1).1) f)
      = coeff (Multiset.toFinsupp (a₀.1).1) f • msymm σ R μ := by
  rw [msymm_eq_sum_monomial, Finset.smul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [smul_monomial, smul_eq_mul, mul_one]
  exact congrArg _ (coeff_eq_of_ofSym_eq hf (a.2.trans a₀.2.symm))

/-- The `m_μ` with at most `#σ` parts span the symmetric polynomials homogeneous of degree `d`:
grouping the monomials of a symmetric `f` into orbits writes `f` as a combination of them. -/
theorem span_range_msymm (σ : Type*) [Fintype σ] [DecidableEq σ] (R : Type*)
    [CommSemiring R] (d : ℕ) :
    Submodule.span R (Set.range fun μ : {μ : Nat.Partition d // μ.parts.card ≤ Fintype.card σ} =>
        msymm σ R μ.1) = symmetricHomogeneousSubmodule σ R d := by
  refine le_antisymm (Submodule.span_le.mpr ?_) fun f hf => ?_
  · rintro p ⟨μ, rfl⟩
    exact mem_symmetricHomogeneousSubmodule.mpr ⟨msymm_isSymmetric σ R _, msymm_isHomogeneous _⟩
  · obtain ⟨hsym, hhom⟩ := mem_symmetricHomogeneousSubmodule.mp hf
    rw [eq_sum_monomial_of_isHomogeneous hhom, ← Fintype.sum_fiberwise
      (fun a : Sym σ d => Nat.Partition.ofSym a) fun a : Sym σ d =>
        monomial (Multiset.toFinsupp a.1) (coeff (Multiset.toFinsupp a.1) f)]
    refine Submodule.sum_mem _ fun μ _ => ?_
    rcases isEmpty_or_nonempty {a : Sym σ d // Nat.Partition.ofSym a = μ} with _ | hne
    · simp
    · obtain ⟨a₀⟩ := hne
      rw [sum_orbit_monomial_eq_smul_msymm hsym a₀]
      exact Submodule.smul_mem _ _
        (Submodule.subset_span ⟨⟨μ, a₀.2 ▸ Nat.Partition.parts_card_le a₀.1⟩, rfl⟩)

/-- The `m_μ` with at most `#σ` parts are linearly independent: each orbit is nonempty, and the
coefficient at a monomial of the orbit `μ` is a functional dual to the family. -/
theorem linearIndependent_msymm (σ : Type*) [Fintype σ] [DecidableEq σ] (R : Type*)
    [CommSemiring R] (d : ℕ) : LinearIndependent R
      fun μ : {μ : Nat.Partition d // μ.parts.card ≤ Fintype.card σ} => msymm σ R μ.1 := by
  choose rep hrep using fun μ : {μ : Nat.Partition d // μ.parts.card ≤ Fintype.card σ} =>
    Nat.Partition.exists_sym_ofSym_eq μ.2
  have key : ∀ μ ν : {μ : Nat.Partition d // μ.parts.card ≤ Fintype.card σ},
      lcoeff R (Multiset.toFinsupp (rep μ).1) (msymm σ R ν.1)
        = if (μ : Nat.Partition d) = ν then 1 else 0 := fun μ ν => by
    rw [lcoeff_apply, coeff_msymm, hrep]
  exact linearIndependent_of_pairwise_dual_eq_zero_one _
    (fun μ => lcoeff R (Multiset.toFinsupp (rep μ).1))
    (fun μ ν hμν => (key μ ν).trans (ite_eq_right fun h => hμν (Subtype.ext h)))
    fun μ => (key μ μ).trans (ite_eq_left rfl)

/-- The monomial symmetric polynomials `m_μ`, indexed by the partitions `μ` of `d` having at most
`#σ` parts, are an `R`-basis of the symmetric polynomials in the finite alphabet `σ` that are
homogeneous of degree `d`. The index condition is `μ_{n+1} = 0`; without it the
family would contain `0`. -/
@[hjo "lem_mac_msymm_basis"]
theorem exists_basis_symmetricHomogeneousSubmodule_msymm (σ : Type*) [Fintype σ] [DecidableEq σ]
    (R : Type*) [CommSemiring R] (d : ℕ) :
    ∃ B : Module.Basis {μ : Nat.Partition d // μ.parts.card ≤ Fintype.card σ} R
        (symmetricHomogeneousSubmodule σ R d),
      ∀ μ, (B μ : MvPolynomial σ R) = msymm σ R (μ : Nat.Partition d) := by
  refine ⟨(Module.Basis.span (linearIndependent_msymm σ R d)).map
    (LinearEquiv.ofEq _ _ (span_range_msymm σ R d)), fun μ => ?_⟩
  rw [Module.Basis.map_apply, LinearEquiv.coe_ofEq_apply, Module.Basis.span_apply]

end Basis

end MvPolynomial
