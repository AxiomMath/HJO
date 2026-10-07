/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.Collinear.ScalarFamily
public import HJO.Collinear.SymbolSym
public meta import HJO.Attr

/-! # Two properties of the symmetrised symbol: symmetry, and a bound on its support

The necessity half of the BGLX vanishing criterion isolates one coefficient of the symmetrised
symbol `Ξ_c` at a time, and to do that it needs two facts about `Ξ_c` that are visible from its
definition alone and need no criterion:

* `Ξ_c` is **symmetric** — relabelling the variables fixes it, because the definition already
  averages over the `k!` relabellings, and left multiplication by a permutation is a bijection of
  the group onto itself;
* the support of `Ξ_c` is **bounded below in total degree** — if `c` is supported on the words
  `a` with `a₁ + ⋯ + a_k ≤ A` then `(Ξ_c)_α = 0` whenever `α₁ + ⋯ + α_k < -A`, because the symbol
  `Π_c` is supported on the exponents `-a` and the kernel expansion `Ω̂_k` is supported on the
  exponents of coordinate sum `0`.

## Main statements

* `HJO.Bglx.relabel_symbolSym`.
* `HJO.Bglx.symbolSym_eq_zero_of_coordSum_lt`.
* `HJO.Bglx.symbolSym_apply_eq_symbolSym_apply_of_relabel`: the form the coefficient extraction
  uses — a coefficient of `Ξ_c` depends only on the multiset of coordinates of its exponent.

## Implementation notes

**The support bound is a statement about a product in a cone ring, and it is proved from the
convolution.** For a fixed `α` of coordinate sum `< -A` and any splitting `α = α' + (α - α')`,
either `α'` has coordinate sum `< -A` — and then `Π_c` vanishes there — or it does not, and then
`α - α'` has *nonzero* coordinate sum, where the kernel expansion vanishes by
`HJO.Bglx.isBalancedScalar_kernelExpansion`. So every term of the convolution vanishes. No
finiteness argument is needed beyond the one `HJO.Bglx.ConeRing.coeff_mul` already packages.

**Relabelling preserves the coordinate sum**, which is `HJO.Bglx.coordSum_relabelExp_symm`: it
permutes the coordinates of the exponent. That is what carries the bound from each summand of the
average to the average itself.

## References

The reference is F. Bergeron, A. M. Garsia, E. Leven and G. Xin, *Some remarkable new plethystic
operators in the theory of Macdonald polynomials*, arXiv:1405.0316v1, J. Comb. **7** (2016)
671--714, whose proof of Theorem 2.1 uses the symmetry of their `G_m` to pass from their equation
(2.14) to the vanishing of every coefficient.
-/

@[expose] public section

namespace HJO.Bglx

open HJO.Sym

variable {L : Type*} [Field L] [Algebra ℚ L] {k : ℕ}

/-! ### Relabelling preserves the coordinate sum -/

/-- **Relabelling the variables permutes the coordinates of an exponent**, so it leaves their sum
alone. -/
lemma coordSum_relabelExp_symm (σ : Equiv.Perm (Fin k)) (α : Fin k →₀ ℤ) :
    coordSum ((relabelExp σ).symm α) = coordSum α := by
  rw [coordSum, coordSum]
  refine Fintype.sum_equiv σ _ _ fun i => ?_
  rw [relabelExp_symm_apply]

/-! ### The symmetrised symbol is symmetric -/

omit [Algebra ℚ L] in
/-- Relabelling is additive over a finite sum of families, pointwise by definition. -/
lemma relabel_finsetSum {ι : Type*} (σ : Equiv.Perm (Fin k)) (s : Finset ι)
    (f : ι → Family k (Lambda L)) :
    relabel σ (∑ i ∈ s, f i) = ∑ i ∈ s, relabel σ (f i) := by
  funext α
  rw [relabel_apply, Finset.sum_apply, Finset.sum_apply]
  exact Finset.sum_congr rfl fun i _ => rfl

/-- **The symmetrised symbol is symmetric**: relabelling the variables fixes `Ξ_c`. The definition
already averages over the `k!` relabellings, and `τ ↦ ρτ` is a bijection of the permutation group
onto itself, so the average is a reindexing of itself. -/
@[hjo "lem_bglx_symbol_sym_invariant"]
theorem relabel_symbolSym (q u : L) (k : ℕ) (c : (Fin k → ℕ) →₀ L) (ρ : Equiv.Perm (Fin k)) :
    relabel ρ (symbolSym q u k c) = symbolSym q u k c := by
  set g := (symbolElem (1 : Equiv.Perm (Fin k)) c * kernelExpansion q u k).coeff with hg
  have hsmul : relabel ρ ((Nat.factorial k : L)⁻¹ • ∑ σ : Equiv.Perm (Fin k), relabel σ g)
      = (Nat.factorial k : L)⁻¹ • relabel ρ (∑ σ : Equiv.Perm (Fin k), relabel σ g) := rfl
  rw [symbolSym, ← hg, hsmul, relabel_finsetSum]
  congr 1
  refine Fintype.sum_bijective (fun σ => ρ * σ) (Group.mulLeft_bijective ρ)
    (fun σ => relabel ρ (relabel σ g)) (fun σ => relabel σ g) fun σ => ?_
  rw [relabel_relabel]

/-- **A coefficient of the symmetrised symbol depends only on the multiset of coordinates of its
exponent.** This is the form `HJO.Bglx.relabel_symbolSym` is used in: two exponents that differ
by a relabelling carry the same coefficient. -/
theorem symbolSym_relabelExp (q u : L) (k : ℕ) (c : (Fin k → ℕ) →₀ L) (ρ : Equiv.Perm (Fin k))
    (α : Fin k →₀ ℤ) : symbolSym q u k c (relabelExp ρ α) = symbolSym q u k c α := by
  have h := congrFun (relabel_symbolSym q u k c ρ) (relabelExp ρ α)
  rw [relabel_apply, AddEquiv.symm_apply_apply] at h
  exact h.symm

/-! ### The support of the symmetrised symbol is bounded below in total degree -/

omit [Algebra ℚ L] in
/-- **The symbol is supported on the exponents `-a` with `c a ≠ 0`**, so a bound on the total degree
of the words in the support of `c` bounds the coordinate sum of the support of `Π_c` below. -/
theorem symbolFamily_eq_zero_of_coordSum_lt (c : (Fin k → ℕ) →₀ L) (A : ℤ)
    (hc : ∀ a : Fin k → ℕ, A < ∑ i : Fin k, (a i : ℤ) → c a = 0) {β : Fin k →₀ ℤ}
    (hβ : coordSum β < -A) : symbolFamily c β = 0 := by
  classical
  rw [symbolFamily, dopWordSymbol, Finsupp.linearCombination_apply, Finsupp.sum,
    AddMonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply, map_sum]
  refine Finset.sum_eq_zero fun a ha => ?_
  rw [AddMonoidAlgebra.coeff_smul, Finsupp.smul_apply, AddMonoidAlgebra.coeff_single,
    Finsupp.single_apply, smul_eq_mul]
  refine (congrArg (algebraMap L (Lambda L)) ?_).trans (map_zero _)
  by_cases hβa : (Finsupp.equivFunOnFinite.symm fun i => -(a i : ℤ)) = β
  · refine absurd (hc a ?_) (Finsupp.mem_support_iff.1 ha)
    have hcoord : coordSum β = -∑ i : Fin k, (a i : ℤ) := by
      rw [← hβa, coordSum, ← Finset.sum_neg_distrib]
      exact Finset.sum_congr rfl fun i _ => by simp
    omega
  · rw [ite_eq_right hβa, mul_zero]

/-- **The product of the symbol with the kernel expansion is bounded below in coordinate sum.**
Every splitting of an exponent of coordinate sum `< -A` puts one factor where it vanishes. -/
theorem coeff_symbolElem_mul_kernelExpansion_eq_zero (q u : L) (k : ℕ) (c : (Fin k → ℕ) →₀ L)
    (A : ℤ) (hc : ∀ a : Fin k → ℕ, A < ∑ i : Fin k, (a i : ℤ) → c a = 0) {α : Fin k →₀ ℤ}
    (hα : coordSum α < -A) :
    (symbolElem 1 c * kernelExpansion q u k).coeff α = 0 := by
  rw [ConeRing.coeff_mul]
  refine (finsum_congr fun α' => ?_).trans finsum_zero
  by_cases h' : coordSum α' < -A
  · rw [coeff_symbolElem, symbolFamily_eq_zero_of_coordSum_lt c A hc h', zero_mul]
  · refine mul_eq_zero_of_right _ ?_
    by_contra hne
    have hbal := (isBalancedScalar_kernelExpansion q u k).balanced (α - α') hne
    rw [coordSum_sub] at hbal
    omega

/-- **The symmetrised symbol is bounded below in total degree.** If `c` vanishes on every word whose
indices sum to more than `A`, then `(Ξ_c)_α = 0` for every exponent `α` whose coordinates sum to
less than `-A`: the bound holds for the product `Π_c Ω̂_k` and relabelling preserves the coordinate
sum, so it holds for each of the `k!` summands of the average and hence for the average. -/
@[hjo "lem_bglx_symbol_sym_support"]
theorem symbolSym_eq_zero_of_coordSum_lt (q u : L) (k : ℕ) (c : (Fin k → ℕ) →₀ L) (A : ℤ)
    (hc : ∀ a : Fin k → ℕ, A < ∑ i : Fin k, (a i : ℤ) → c a = 0) {α : Fin k →₀ ℤ}
    (hα : coordSum α < -A) : symbolSym q u k c α = 0 := by
  rw [symbolSym, Pi.smul_apply, Finset.sum_apply,
    Finset.sum_eq_zero fun σ _ => ?_, smul_zero]
  rw [relabel_apply]
  exact coeff_symbolElem_mul_kernelExpansion_eq_zero q u k c A hc
    (by rw [coordSum_relabelExp_symm]; exact hα)

/-- The total-degree bound a finitely supported coefficient family always has: the supremum of the
sums of the indices over its support. -/
noncomputable def wordDegreeBound (c : (Fin k → ℕ) →₀ L) : ℕ :=
  c.support.sup fun a => ∑ i : Fin k, a i

omit [Algebra ℚ L] in
/-- **The bound is one**: outside it the family vanishes. -/
theorem eq_zero_of_wordDegreeBound_lt (c : (Fin k → ℕ) →₀ L) (a : Fin k → ℕ)
    (ha : (wordDegreeBound c : ℤ) < ∑ i : Fin k, (a i : ℤ)) : c a = 0 := by
  classical
  by_contra hne
  have hle : (∑ i : Fin k, a i) ≤ wordDegreeBound c :=
    Finset.le_sup (f := fun a => ∑ i : Fin k, a i) (Finsupp.mem_support_iff.2 hne)
  have hcast : (∑ i : Fin k, (a i : ℤ)) = ((∑ i : Fin k, a i : ℕ) : ℤ) := by push_cast; rfl
  rw [hcast] at ha
  omega

/-- **Every symmetrised symbol is bounded below in total degree**, with the bound read off the
support of `c`. This is the form the coefficient extraction uses, where the bound is not given in
advance. -/
theorem symbolSym_eq_zero_of_coordSum_lt_neg_bound (q u : L) (k : ℕ) (c : (Fin k → ℕ) →₀ L)
    {α : Fin k →₀ ℤ} (hα : coordSum α < -(wordDegreeBound c : ℤ)) : symbolSym q u k c α = 0 :=
  symbolSym_eq_zero_of_coordSum_lt q u k c _ (eq_zero_of_wordDegreeBound_lt c) hα

/-! ### The coefficients of the symmetrised symbol are scalars -/

omit [Algebra ℚ L] in
/-- Scalar coefficients survive a product in a cone ring: this is the `scalar` half of
`HJO.Bglx.IsBalancedScalar.mul`, isolated because the symbol `Π_c` has scalar coefficients but is
not balanced — it is supported on the exponents `-a`, of coordinate sum `-(a₁+⋯+a_k)`. -/
theorem scalar_coeff_mul {τ : Equiv.Perm (Fin k)} {x y : ConeRing k τ (Lambda L)}
    (hx : ∀ α, ∃ a : L, x.coeff α = MvPolynomial.C a)
    (hy : ∀ α, ∃ a : L, y.coeff α = MvPolynomial.C a) (α : Fin k →₀ ℤ) :
    ∃ a : L, (x * y).coeff α = MvPolynomial.C a := by
  classical
  rw [ConeRing.coeff_mul_of_subset x y α (ConeRing.finite_convSupport x y α).toFinset
    (by rw [Set.Finite.coe_toFinset])]
  refine ⟨∑ α' ∈ (ConeRing.finite_convSupport x y α).toFinset,
    (hx α').choose * (hy (α - α')).choose, ?_⟩
  rw [map_sum]
  refine Finset.sum_congr rfl fun α' _ => ?_
  rw [map_mul, ← (hx α').choose_spec, ← (hy (α - α')).choose_spec]

omit [Algebra ℚ L] in
/-- The symbol has scalar coefficients: they are the coefficients of a Laurent polynomial over the
base field, pushed into `Λ`. -/
theorem scalar_symbolFamily (c : (Fin k → ℕ) →₀ L) (α : Fin k →₀ ℤ) :
    ∃ a : L, symbolFamily c α = MvPolynomial.C a :=
  ⟨(dopWordSymbol L k c).coeff α, by rw [symbolFamily, MvPolynomial.algebraMap_eq]⟩

/-- **The coefficients of the symmetrised symbol are scalars.** Both factors of `Π_c Ω̂_k` have
coefficients in the image of `𝕜 → Λ` — the symbol by construction, the kernel expansion by
`HJO.Bglx.isBalancedScalar_kernelExpansion` — relabelling permutes exponents and leaves the
coefficients alone, and the average multiplies them by `(k!)⁻¹`.

This is what makes the coefficient extraction of Step 5 of the necessity argument a statement about
a `𝕜`-linear combination of the elementary monomials. The argument as usually written
calls that relation a `𝕜`-linear combination without recording why the coefficients are scalars,
`Ξ_c` being a member of `M_k` with coefficients in `Λ`; this lemma is the missing justification, and
without it the appeal to `HJO.Sym.linearIndependent_elemSymmMonomial` there would be an appeal to
independence over `Λ`, which is false — `e_2 · e_1 - e_1 · e_2 = 0` is a nontrivial `Λ`-relation. -/
theorem scalar_symbolSym (q u : L) (k : ℕ) (c : (Fin k → ℕ) →₀ L) (α : Fin k →₀ ℤ) :
    ∃ a : L, symbolSym q u k c α = MvPolynomial.C a := by
  classical
  have hg : ∀ β : Fin k →₀ ℤ, ∃ a : L,
      (symbolElem (1 : Equiv.Perm (Fin k)) c * kernelExpansion q u k).coeff β
        = MvPolynomial.C a :=
    scalar_coeff_mul (fun β => by rw [coeff_symbolElem]; exact scalar_symbolFamily c β)
      (isBalancedScalar_kernelExpansion q u k).scalar
  have hpt : ∀ σ : Equiv.Perm (Fin k),
      relabel σ (symbolElem (1 : Equiv.Perm (Fin k)) c * kernelExpansion q u k).coeff α
        = MvPolynomial.C (hg ((relabelExp σ).symm α)).choose := fun σ => by
    rw [relabel_apply]
    exact (hg ((relabelExp σ).symm α)).choose_spec
  refine ⟨(Nat.factorial k : L)⁻¹ * ∑ σ : Equiv.Perm (Fin k),
    (hg ((relabelExp σ).symm α)).choose, ?_⟩
  rw [symbolSym, Pi.smul_apply, Finset.sum_apply, Finset.sum_congr rfl fun σ _ => hpt σ,
    ← map_sum, Algebra.smul_def, map_mul, MvPolynomial.algebraMap_eq]

end HJO.Bglx
