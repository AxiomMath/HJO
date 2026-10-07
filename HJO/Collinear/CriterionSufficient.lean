/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.Collinear.CompositeCT
public import HJO.Collinear.SymbolSym
public import HJO.Collinear.WordGrading
public meta import HJO.Attr

/-! # The operator of a coefficient family as a constant term, and the easy half of the criterion

With BGLX's composite formula available (`HJO.Bglx.dopComp_eq_ct`), the operator of a whole
coefficient family is a single constant term,

`V_c F = CT_k(δ^{(k)}(F) E_k Π_c Ω̂_k)`,

and the Stanton--Stembridge pairing turns that into a pairing against the *symmetrised* symbol,

`V_c F = ∑_α (δ^{(k)}(F) E_k)_α (Ξ_c)_{-α}`,

a sum with finitely many nonzero terms. The sufficiency half of the vanishing criterion is then
immediate: if `Ξ_c` vanishes then every term of that sum does.

## Main statements

* `HJO.Bglx.dopWordOperator_eq_ct`.
* `HJO.Bglx.dopWordOperator_eq_pairing`.
* `HJO.Bglx.sum_dopWordOperator_eq_zero`: `HJO.Bglx.dopWordOperator_eq_zero_of_symbolSym`.
* `HJO.Bglx.raiseStableKernel_of_criterionNecessary`: with the necessity half, the kernel of `π` is
  `σ`-stable — so `HJO.Bglx.exists_isIndexShift_param` waits on exactly one statement.

## Implementation notes

**The symbol is a finite combination of monomials**, and that is how the composite formula is summed
over the words: `symbolElem_eq_sum` writes `Π_c` as `∑_a c_a z^{-a}` inside the cone ring, so
`dopWordOperator_eq_ct` is the composite formula plus linearity of the constant term.

**The pairing needs the interchange of a finite sum over the `k!` orderings with the (finitely
supported) sum over the exponents.** That is `finsum_sum_comm`, whose hypothesis is exactly that
each pairing has finite support — which it does, being the constant term of a product formed in a
cone ring (`ConeRing.finite_convSupport`).

No hypothesis on `q` or `u` appears anywhere here: sufficiency is a formal identity, and the only
division is by `k!`, which `Algebra ℚ L` supplies. The necessity half is a different matter and is
recorded as a predicate in `HJO/Collinear/SymbolSym.lean`.

## References

Lemmas `HJO.Bglx.dopWordOperator_eq_ct`,
`HJO.Bglx.dopWordOperator_eq_pairing` and `HJO.Bglx.dopWordOperator_eq_zero_of_symbolSym`. The
source is F. Bergeron, A. M. Garsia, E. Leven and G. Xin, *Some remarkable new plethystic operators
in the theory of Macdonald polynomials*, arXiv:1405.0316v1, J. Comb. **7** (2016) 671--714,
Theorem 2.1.
-/

@[expose] public section

namespace HJO.Bglx

open HJO.Sym

variable {L : Type*} [Field L] [Algebra ℚ L] {k : ℕ}

omit [Algebra ℚ L] in
/-- **The symbol is the finite combination of monomials its definition displays.** -/
theorem symbolElem_eq_sum (c : (Fin k → ℕ) →₀ L) :
    symbolElem 1 c
      = ∑ a ∈ c.support, algebraMap L (Lambda L) (c a) • monoElem 1 (negExp a) := by
  refine ConeRing.ext (funext fun α => ?_)
  have hsum : (∑ a ∈ c.support, algebraMap L (Lambda L) (c a) •
      (monoElem 1 (negExp a) : ConeRing k 1 (Lambda L))).coeff α
      = ∑ a ∈ c.support, algebraMap L (Lambda L) (c a) * (monoElem 1 (negExp a)).coeff α := by
    rw [show (∑ a ∈ c.support, algebraMap L (Lambda L) (c a) •
        (monoElem 1 (negExp a) : ConeRing k 1 (Lambda L))).coeff
        = ConeRing.coeffLinear k 1 (Lambda L) (∑ a ∈ c.support,
          algebraMap L (Lambda L) (c a) • monoElem 1 (negExp a)) from rfl, map_sum]
    simp only [map_smul, Finset.sum_apply]
    rfl
  rw [hsum, coeff_symbolElem, symbolFamily, dopWordSymbol, Finsupp.linearCombination_apply,
    Finsupp.sum, AddMonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply, map_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [coeff_monoElem, AddMonoidAlgebra.coeff_smul, Finsupp.smul_apply,
    AddMonoidAlgebra.coeff_single, Finsupp.single_apply, smul_eq_mul, map_mul,
    show (Finsupp.equivFunOnFinite.symm fun i => -(a i : ℤ)) = negExp a from rfl]
  rcases eq_or_ne α (negExp a) with h | h
  · rw [ite_eq_left h, ite_eq_left (show negExp a = α from h.symm), map_one]
  · rw [ite_eq_right h, ite_eq_right (show ¬(negExp a = α) from fun hc => h hc.symm), map_zero]

omit [Algebra ℚ L] in
/-- The constant term is additive over a finite sum of cone ring elements. -/
lemma ct_sum {ι : Type*} {τ : Equiv.Perm (Fin k)} (s : Finset ι)
    (x : ι → ConeRing k τ (Lambda L)) :
    ct k (Lambda L) (∑ i ∈ s, x i).coeff = ∑ i ∈ s, ct k (Lambda L) (x i).coeff :=
  map_sum ((ct k (Lambda L)).comp (ConeRing.coeffLinear k τ (Lambda L))) x s

/-- **The operator of a coefficient family is a constant term.** -/
@[hjo "lem_bglx_word_operator_ct"]
theorem dopWordOperator_eq_ct (q u : L) (k : ℕ) (c : (Fin k → ℕ) →₀ L) (F : Lambda L) :
    dopWordOperator q u k c F
      = ct k (Lambda L)
        (shiftExpElem q u k 1 F * (symbolElem 1 c * kernelExpansion q u k)).coeff := by
  rw [dopWordOperator, Finsupp.linearCombination_apply, Finsupp.sum, symbolElem_eq_sum,
    Finset.sum_mul, Finset.mul_sum, ct_sum, LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [LinearMap.smul_apply, dopComp_eq_ct q u k a F, compositeElem,
    show shiftExpElem q u k 1 F * (algebraMap L (Lambda L) (c a) • monoElem 1 (negExp a)
        * kernelExpansion q u k)
      = algebraMap L (Lambda L) (c a) •
        (shiftExpElem q u k 1 F * (monoElem 1 (negExp a) * kernelExpansion q u k)) from by
      rw [smul_mul_assoc, mul_smul_comm],
    ct_apply, ct_apply, ConeRing.coeff_smul, Algebra.smul_def]

omit [Algebra ℚ L] in
/-- The constant term of a product is the pairing of the two coefficient families. -/
theorem ct_mul_eq_finsum {τ : Equiv.Perm (Fin k)} (x y : ConeRing k τ (Lambda L)) :
    ct k (Lambda L) (x * y).coeff = ∑ᶠ α : Fin k →₀ ℤ, x.coeff α * y.coeff (-α) := by
  rw [ct_apply, ConeRing.coeff_mul]
  exact finsum_congr fun α => by rw [zero_sub]

omit [Algebra ℚ L] in
/-- The pairing of the displaced exponential factor against a relabelling of the symbol has finite
support, being the constant term of a product formed in a cone ring. -/
theorem finite_support_pairing {τ : Equiv.Perm (Fin k)} (x y : ConeRing k τ (Lambda L)) :
    (Function.support fun α : Fin k →₀ ℤ => x.coeff α * y.coeff (-α)).Finite := by
  refine Set.Finite.subset (ConeRing.finite_convSupport x y 0) fun α hα => ?_
  rw [Function.mem_support] at hα
  rw [ConeRing.convSupport, Set.mem_ofPred_eq, zero_sub]
  exact ⟨fun h => hα (by rw [h, zero_mul]), fun h => hα (by rw [h, mul_zero])⟩

/-- **The operator paired against the symmetrised symbol.** For every ordering the operator is the
pairing of `δ^{(k)}(F) E_k` against that ordering's relabelling of `Π_c Ω̂_k`, by the
Stanton--Stembridge step; averaging over the `k!` orderings replaces the relabelling by `Ξ_c`. -/
@[hjo "lem_bglx_word_operator_pairing"]
theorem dopWordOperator_eq_pairing (q u : L) (k : ℕ) (c : (Fin k → ℕ) →₀ L) (F : Lambda L) :
    dopWordOperator q u k c F
      = ∑ᶠ α : Fin k →₀ ℤ, (shiftExpElem q u k 1 F).coeff α * symbolSym q u k c (-α) := by
  classical
  set H := shiftExpElem q u k 1 F with hH
  set g := symbolElem (1 : Equiv.Perm (Fin k)) c * kernelExpansion q u k with hg
  have hfac : (Nat.factorial k : L) ≠ 0 := by
    rw [← map_natCast (algebraMap ℚ L) (Nat.factorial k)]
    intro hc
    have h0 := (map_eq_zero_iff (algebraMap ℚ L) (algebraMap ℚ L).injective).1 hc
    exact absurd (Nat.cast_eq_zero.1 h0) (Nat.factorial_ne_zero k)
  have hτ : ∀ τ : Equiv.Perm (Fin k),
      dopWordOperator q u k c F
        = ∑ᶠ α : Fin k →₀ ℤ, H.coeff α * relabel τ g.coeff (-α) := by
    intro τ
    have h2 := ct_mul_eq_ct_mul_relabel q u F τ g (ConeRing.relabelAlgEquiv τ 1 g)
      (funext fun α => ConeRing.coeff_relabelAlgEquiv τ 1 g α)
    rw [dopWordOperator_eq_ct q u k c F, ← hg, h2,
      ct_mul_eq_finsum (shiftExpElem q u k τ F) (ConeRing.relabelAlgEquiv τ 1 g)]
    refine finsum_congr fun α => ?_
    rw [ConeRing.coeff_relabelAlgEquiv, hH]
    exact congrArg (fun x => x * relabel τ g.coeff (-α))
      (congrFun (coeff_shiftExpElem_congr q u k τ 1 F) α)
  have hcard : ∑ _τ : Equiv.Perm (Fin k), dopWordOperator q u k c F
      = (Nat.factorial k : L) • dopWordOperator q u k c F := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin,
      ← Nat.cast_smul_eq_nsmul L]
  have hswap : ∑ τ : Equiv.Perm (Fin k), (∑ᶠ α : Fin k →₀ ℤ, H.coeff α * relabel τ g.coeff (-α))
      = ∑ᶠ α : Fin k →₀ ℤ, ∑ τ : Equiv.Perm (Fin k), H.coeff α * relabel τ g.coeff (-α) := by
    refine (finsum_sum_comm Finset.univ
      (fun (α : Fin k →₀ ℤ) (τ : Equiv.Perm (Fin k)) =>
        H.coeff α * relabel τ g.coeff (-α)) fun τ _ => ?_).symm
    refine (finite_support_pairing (shiftExpElem q u k τ F)
      (ConeRing.relabelAlgEquiv τ 1 g)).subset fun α hα => ?_
    rw [Function.mem_support] at hα ⊢
    rw [ConeRing.coeff_relabelAlgEquiv,
      congrFun (coeff_shiftExpElem_congr q u k τ 1 F) α]
    exact hα
  have hinner : ∀ α : Fin k →₀ ℤ,
      ∑ τ : Equiv.Perm (Fin k), H.coeff α * relabel τ g.coeff (-α)
        = (Nat.factorial k : L) • (H.coeff α * symbolSym q u k c (-α)) := by
    intro α
    rw [symbolSym, ← hg, Pi.smul_apply, Finset.sum_apply, mul_smul_comm, smul_smul,
      mul_inv_cancel₀ hfac, one_smul, Finset.mul_sum]
  refine smul_right_injective (Lambda L) hfac ?_
  calc (Nat.factorial k : L) • dopWordOperator q u k c F
      = ∑ _τ : Equiv.Perm (Fin k), dopWordOperator q u k c F := hcard.symm
    _ = ∑ τ : Equiv.Perm (Fin k), (∑ᶠ α : Fin k →₀ ℤ, H.coeff α * relabel τ g.coeff (-α)) :=
        Finset.sum_congr rfl fun τ _ => hτ τ
    _ = ∑ᶠ α : Fin k →₀ ℤ, ∑ τ : Equiv.Perm (Fin k), H.coeff α * relabel τ g.coeff (-α) := hswap
    _ = ∑ᶠ α : Fin k →₀ ℤ, (Nat.factorial k : L) • (H.coeff α * symbolSym q u k c (-α)) :=
        finsum_congr hinner
    _ = (Nat.factorial k : L) • ∑ᶠ α : Fin k →₀ ℤ, H.coeff α * symbolSym q u k c (-α) :=
        (smul_finsum _ _).symm

/-- **The symmetrised symbol vanishing forces the operator to vanish**, one length at a time. -/
@[hjo "lem_bglx_criterion_sufficient"]
theorem dopWordOperator_eq_zero_of_symbolSym (q u : L) (k : ℕ) (c : (Fin k → ℕ) →₀ L)
    (h : symbolSym q u k c = 0) : dopWordOperator q u k c = 0 := by
  refine LinearMap.ext fun F => ?_
  rw [dopWordOperator_eq_pairing, LinearMap.zero_apply]
  refine (finsum_congr fun α => ?_).trans finsum_zero
  rw [h]
  exact mul_zero _

/-- **The symmetrised symbols vanishing force the sum of the operators to vanish.** This is the
statement of the sufficiency half. -/
@[hjo "lem_bglx_criterion_sufficient"]
theorem sum_dopWordOperator_eq_zero (q u : L) (m : ℕ) (c : ∀ k : ℕ, (Fin k → ℕ) →₀ L)
    (h : ∀ k ≤ m, symbolSym q u k (c k) = 0) :
    ∑ k ∈ Finset.range (m + 1), dopWordOperator q u k (c k) = 0 :=
  Finset.sum_eq_zero fun k hk => dopWordOperator_eq_zero_of_symbolSym q u k (c k)
    (h k (by rw [Finset.mem_range] at hk; omega))

/-- **The criterion holds as soon as its necessity half does.** -/
theorem isVanishingCriterion_of_necessary (q u : L) (h : IsVanishingCriterionNecessary q u) :
    IsVanishingCriterion q u :=
  fun m c => ⟨h m c, sum_dopWordOperator_eq_zero q u m c⟩

/-- **With the necessity half of the criterion the kernel of `π` is `σ`-stable.** The two hypotheses
of `HJO.Sym.raiseStableKernel_of_dopWordOperator` — that a sum over distinct word lengths vanishes
only if each length does, and that raising every index preserves vanishing — both follow: the first
from necessity and sufficiency together, and the second from necessity, the invariance of the
vanishing of `Ξ` under raising (`symbolSym_dopWordRaise_eq_zero_iff`) and sufficiency. So the whole
of `HJO.Bglx.exists_isIndexShift_param` waits on exactly one statement, and this is where it
enters. -/
theorem raiseStableKernel_of_criterionNecessary (q u : L)
    (h : IsVanishingCriterionNecessary q u) : RaiseStableKernel q u := by
  classical
  refine raiseStableKernel_of_dopWordOperator (fun s c hsum k hk => ?_) (fun k c hc => ?_)
  · set c' : ∀ j : ℕ, (Fin j → ℕ) →₀ L := fun j => if j ∈ s then c j else 0 with hc'
    have hsub : s ⊆ Finset.range (s.sup id + 1) := fun j hj => by
      rw [Finset.mem_range]
      exact Nat.lt_succ_of_le (Finset.le_sup (f := id) hj)
    have hsum' : ∑ j ∈ Finset.range (s.sup id + 1), dopWordOperator q u j (c' j) = 0 := by
      rw [← Finset.sum_subset hsub (fun j _ hj => ?_), ← hsum]
      · refine Finset.sum_congr rfl fun j hj => ?_
        change dopWordOperator q u j (if j ∈ s then c j else 0) = dopWordOperator q u j (c j)
        rw [ite_eq_left hj]
      · change dopWordOperator q u j (if j ∈ s then c j else 0) = 0
        rw [ite_eq_right hj, map_zero]
    have hk' : symbolSym q u k (c k) = 0 := by
      have hx := h _ c' hsum' k (Nat.lt_succ_iff.1 (Finset.mem_range.1 (hsub hk)))
      change symbolSym q u k (if k ∈ s then c k else 0) = 0 at hx
      rwa [ite_eq_left hk] at hx
    exact dopWordOperator_eq_zero_of_symbolSym q u k (c k) hk'
  · set c'' : ∀ j : ℕ, (Fin j → ℕ) →₀ L := fun j => if hj : j = k then hj ▸ c else 0 with hc''
    have hck : c'' k = c := by rw [hc'']; simp
    have hsum' : ∑ j ∈ Finset.range (k + 1), dopWordOperator q u j (c'' j) = 0 := by
      refine (Finset.sum_eq_single_of_mem k (Finset.mem_range.2 (Nat.lt_succ_self k))
        fun j _ hj => ?_).trans ?_
      · change dopWordOperator q u j (if hj : j = k then hj ▸ c else 0) = 0
        rw [dite_eq_right hj, map_zero]
      · rw [hck, hc]
    have hxi : symbolSym q u k c = 0 := by
      have hx := h k c'' hsum' k le_rfl
      rwa [hck] at hx
    exact dopWordOperator_eq_zero_of_symbolSym q u k (dopWordRaise L k c)
      ((symbolSym_dopWordRaise_eq_zero_iff q u k c).2 hxi)

end HJO.Bglx
