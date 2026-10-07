/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.Collinear.SSSPairing
public import HJO.Collinear.SymbolSymSupport
public import HJO.Collinear.TopLengthSeparation
public meta import HJO.Attr

/-! # The identities at the top word length, unpacked

Step 3 of the proof of `HJO.Bglx.criterionNecessary` leaves, for every `l ≥ 1`, the
vanishing of the functional `⟨z^{-l𝟏}⟩_m` of `HJO/Collinear/SymbolCT.lean`. Step 4 unpacks that
into BGLX's equation (2.14),

`∑_{γ ∈ ℕ^m} (-1)^{γ₁+⋯+γ_m} e_{γ₁} ⋯ e_{γ_m} (Ξ_c)_{l𝟏-γ} = 0`,

a relation among the *coefficients* of the symmetrised symbol with elementary monomials as
multipliers. This file does that, and restates the residual of the necessity half in that form:
`HJO.Bglx.IsExpPairingSeparating`, which mentions only the exponential factor's coefficients
`HJO.Bglx.expAlphabetCoeff` and the symmetrised symbol. Everything above it — the cone rings, the
Laurent polynomials, the finite alphabet, the descent — is proved.

Two things are needed to get there and both are supplied here. First the Stanton--Stembridge step
has to be available at a *symmetric* first factor rather than only at the displaced exponential
factor: `HJO.Bglx.ct_mul_eq_ct_mul_relabel_of_coeff` is `HJO.Bglx.ct_mul_eq_ct_mul_relabel` with
that hypothesis made explicit, and `HJO.Bglx.symbolCT_eq_pairing` is
`HJO.Bglx.dopWordOperator_eq_pairing` reproved from it. Second the monomial has to be shifted out of
the pairing, which is a reindexing of the formal sum along `α ↦ β + α`.

## Main definitions

* `HJO.Bglx.IsExpPairingSeparating`: **the residual** of the necessity half, in the form of
  BGLX's equation (2.14).

## Main statements

* `HJO.Bglx.ct_mul_eq_ct_mul_relabel_of_coeff`: the symmetrisation step at any symmetric factor.
* `HJO.Bglx.symbolCT_eq_pairing`: the functional at a symmetric monomial is the pairing against the
  symmetrised symbol.
* `HJO.Bglx.symbolCT_single_eq_expPairing`: Step 4 — the functional at `z^β` with `β` symmetric is
  `∑_γ (E_m)_γ (Ξ_c)_{-β-γ}`.
* `HJO.Bglx.criterionNecessary_of_isExpPairingSeparating` and
  `HJO.Bglx.exists_isIndexShift_of_isExpPairingSeparating`: the residual carries the whole of
  necessity, and with it the index shift.

## Implementation notes

**The symmetry hypothesis is on the exponent, not on the element.** What
`symbolCT_single_eq_expPairing` needs of `β` is that every permutation of the variables fixes it,
`relabelExp σ β = β`; the monomial `z^β` is then symmetric, `E_m` is symmetric
(`HJO.Bglx.relabel_coeff_expAlphabet`), and so their product is. At `β = -l𝟏` that holds by
`HJO.Bglx.relabelExp_allOnes`.

**The reindexing is `finsum_comp_equiv` along `Equiv.addLeft β`**, which needs no finiteness
hypothesis: it is a bijection of the index type, and the formal sum is over all of it.

## References

The reference is F. Bergeron,
A. M. Garsia, E. Leven and G. Xin, *Some remarkable new plethystic operators in the theory of
Macdonald polynomials*, arXiv:1405.0316v1, J. Comb. **7** (2016) 671--714, whose equation (2.14) is
the identity this file arrives at.
-/

@[expose] public section

namespace HJO.Bglx

open HJO.Sym

variable {L : Type*} [Field L] [Algebra ℚ L] {k : ℕ}

/-! ### The symmetrisation step at a symmetric factor -/

omit [Algebra ℚ L] in
/-- **The Stanton--Stembridge step at any symmetric factor.** For a cone ring element `x` whose
coefficient family is fixed by the relabelling `τ`, the constant term of `x g` formed in `R^{id}_k`
is the constant term of `x τ_*g` formed in `R^τ_k`. This is `HJO.Bglx.ct_mul_eq_ct_mul_relabel` with
the symmetry of the first factor made a hypothesis instead of being read off the displaced
exponential factor. -/
theorem ct_mul_eq_ct_mul_relabel_of_coeff (τ : Equiv.Perm (Fin k)) (x : ConeRing k 1 (Lambda L))
    (x' : ConeRing k τ (Lambda L)) (hx : x'.coeff = x.coeff)
    (hsymm : relabel τ x.coeff = x.coeff) (g : ConeRing k 1 (Lambda L))
    (g' : ConeRing k τ (Lambda L)) (hg' : g'.coeff = relabel τ g.coeff) :
    ct k (Lambda L) (x * g).coeff = ct k (Lambda L) (x' * g').coeff := by
  have hrel := ConeRing.coeff_relabelAlgEquiv τ 1 (x * g)
  have hkey : relabel τ (x * g).coeff = (x' * g').coeff := by
    funext α
    rw [← hrel α, map_mul]
    refine congrFun (ConeRing.coeff_mul_congr _ _ _ _ ?_ ?_) α
    · funext γ
      rw [ConeRing.coeff_relabelAlgEquiv, hx]
      exact congrFun hsymm γ
    · funext γ
      rw [ConeRing.coeff_relabelAlgEquiv, hg']
  rw [← hkey, ct_relabel]

/-! ### The functional at a symmetric monomial -/

omit [Algebra ℚ L] in
/-- A Laurent monomial with unit coefficient, read in the cone ring, is the cone ring's monomial. -/
lemma laurentToCone_single (τ : Equiv.Perm (Fin k)) (β : Fin k →₀ ℤ) :
    laurentToCone τ (AddMonoidAlgebra.single β (1 : Lambda L)) = monoElem τ β := by
  refine ConeRing.ext (funext fun α => ?_)
  rw [coeff_laurentToCone, coeff_monoElem, AddMonoidAlgebra.coeff_single, Finsupp.single_apply]
  rcases eq_or_ne α β with h | h
  · rw [ite_eq_left (show β = α from h.symm), ite_eq_left h]
  · rw [ite_eq_right (show ¬(β = α) from fun hc => h hc.symm), ite_eq_right h]

/-- The coefficients of `z^β E_k` do not depend on the ordering the product is formed in. -/
lemma coeff_monoElem_mul_expAlphabet (τ : Equiv.Perm (Fin k)) (β : Fin k →₀ ℤ) :
    (monoElem τ β * expAlphabet L k τ).coeff = monoMul β (expAlphabetCoeff L k) := by
  rw [coeff_monoElem_mul]
  rfl

/-- **`z^β E_k` is symmetric whenever `β` is**: the exponential factor is symmetric and relabelling
carries the monomial's exponent to its relabelling. -/
lemma relabel_coeff_monoElem_mul_expAlphabet (σ τ : Equiv.Perm (Fin k)) {β : Fin k →₀ ℤ}
    (hβ : relabelExp σ β = β) :
    relabel σ (monoElem τ β * expAlphabet L k τ).coeff
      = (monoElem τ β * expAlphabet L k τ).coeff := by
  rw [coeff_monoElem_mul_expAlphabet, relabel_monoMul, hβ]
  exact congrArg (monoMul β) (relabel_coeff_expAlphabet (K := L) (τ := τ) σ)

/-- **The functional at a symmetric monomial is the pairing against the symmetrised symbol.** This
is `HJO.Bglx.dopWordOperator_eq_pairing` with the displaced exponential factor replaced by
`z^β E_k`, which is legitimate because the only property of the first factor that proof uses is its
symmetry. -/
theorem symbolCT_eq_pairing (q u : L) (k : ℕ) (c : (Fin k → ℕ) →₀ L) {β : Fin k →₀ ℤ}
    (hβ : ∀ σ : Equiv.Perm (Fin k), relabelExp σ β = β) :
    symbolCT q u k c (AddMonoidAlgebra.single β 1)
      = ∑ᶠ α : Fin k →₀ ℤ, monoMul β (expAlphabetCoeff L k) α * symbolSym q u k c (-α) := by
  classical
  set g := symbolElem (1 : Equiv.Perm (Fin k)) c * kernelExpansion q u k with hg
  set X : ∀ τ : Equiv.Perm (Fin k), ConeRing k τ (Lambda L) :=
    fun τ => monoElem τ β * expAlphabet L k τ with hX
  have hXcoeff : ∀ τ : Equiv.Perm (Fin k), (X τ).coeff = monoMul β (expAlphabetCoeff L k) :=
    fun τ => coeff_monoElem_mul_expAlphabet τ β
  have hstart : symbolCT q u k c (AddMonoidAlgebra.single β 1)
      = ct k (Lambda L) (X 1 * g).coeff := by
    rw [symbolCT, ← hg, hX, laurentToCone_single, mul_assoc]
  have hfac : (Nat.factorial k : L) ≠ 0 := by
    rw [← map_natCast (algebraMap ℚ L) (Nat.factorial k)]
    intro hc
    have h0 := (map_eq_zero_iff (algebraMap ℚ L) (algebraMap ℚ L).injective).1 hc
    exact absurd (Nat.cast_eq_zero.1 h0) (Nat.factorial_ne_zero k)
  have hτ : ∀ τ : Equiv.Perm (Fin k), symbolCT q u k c (AddMonoidAlgebra.single β 1)
      = ∑ᶠ α : Fin k →₀ ℤ, monoMul β (expAlphabetCoeff L k) α * relabel τ g.coeff (-α) := by
    intro τ
    rw [hstart, ct_mul_eq_ct_mul_relabel_of_coeff τ (X 1) (X τ)
        ((hXcoeff τ).trans (hXcoeff 1).symm)
        (relabel_coeff_monoElem_mul_expAlphabet τ 1 (hβ τ)) g
        (ConeRing.relabelAlgEquiv τ 1 g) (funext fun α => ConeRing.coeff_relabelAlgEquiv τ 1 g α),
      ct_mul_eq_finsum (X τ) (ConeRing.relabelAlgEquiv τ 1 g)]
    refine finsum_congr fun α => ?_
    rw [ConeRing.coeff_relabelAlgEquiv, hXcoeff τ]
  have hcard : ∑ _τ : Equiv.Perm (Fin k), symbolCT q u k c (AddMonoidAlgebra.single β 1)
      = (Nat.factorial k : L) • symbolCT q u k c (AddMonoidAlgebra.single β 1) := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin,
      ← Nat.cast_smul_eq_nsmul L]
  have hswap : ∑ τ : Equiv.Perm (Fin k),
      (∑ᶠ α : Fin k →₀ ℤ, monoMul β (expAlphabetCoeff L k) α * relabel τ g.coeff (-α))
      = ∑ᶠ α : Fin k →₀ ℤ, ∑ τ : Equiv.Perm (Fin k),
        monoMul β (expAlphabetCoeff L k) α * relabel τ g.coeff (-α) := by
    refine (finsum_sum_comm Finset.univ
      (fun (α : Fin k →₀ ℤ) (τ : Equiv.Perm (Fin k)) =>
        monoMul β (expAlphabetCoeff L k) α * relabel τ g.coeff (-α)) fun τ _ => ?_).symm
    refine (finite_support_pairing (X τ) (ConeRing.relabelAlgEquiv τ 1 g)).subset fun α hα => ?_
    rw [Function.mem_support] at hα ⊢
    rw [ConeRing.coeff_relabelAlgEquiv, hXcoeff τ]
    exact hα
  have hinner : ∀ α : Fin k →₀ ℤ,
      ∑ τ : Equiv.Perm (Fin k), monoMul β (expAlphabetCoeff L k) α * relabel τ g.coeff (-α)
        = (Nat.factorial k : L) •
          (monoMul β (expAlphabetCoeff L k) α * symbolSym q u k c (-α)) := by
    intro α
    rw [symbolSym, ← hg, Pi.smul_apply, Finset.sum_apply, mul_smul_comm, smul_smul,
      mul_inv_cancel₀ hfac, one_smul, Finset.mul_sum]
  refine smul_right_injective (Lambda L) hfac ?_
  calc (Nat.factorial k : L) • symbolCT q u k c (AddMonoidAlgebra.single β 1)
      = ∑ _τ : Equiv.Perm (Fin k), symbolCT q u k c (AddMonoidAlgebra.single β 1) := hcard.symm
    _ = ∑ τ : Equiv.Perm (Fin k),
        (∑ᶠ α : Fin k →₀ ℤ, monoMul β (expAlphabetCoeff L k) α * relabel τ g.coeff (-α)) :=
        Finset.sum_congr rfl fun τ _ => hτ τ
    _ = ∑ᶠ α : Fin k →₀ ℤ, ∑ τ : Equiv.Perm (Fin k),
        monoMul β (expAlphabetCoeff L k) α * relabel τ g.coeff (-α) := hswap
    _ = ∑ᶠ α : Fin k →₀ ℤ, (Nat.factorial k : L) •
        (monoMul β (expAlphabetCoeff L k) α * symbolSym q u k c (-α)) := finsum_congr hinner
    _ = (Nat.factorial k : L) •
        ∑ᶠ α : Fin k →₀ ℤ, monoMul β (expAlphabetCoeff L k) α * symbolSym q u k c (-α) :=
        (smul_finsum _ _).symm

/-! ### Step 4: the monomial shifted out of the pairing -/

/-- **Step 4 of the proof.** The functional at a symmetric monomial `z^β` is the pairing
of the exponential factor against the symmetrised symbol shifted by `β`. This is BGLX's
equation (2.14) once `β = -l𝟏` is substituted and the coefficients of `E_m` are written out. -/
theorem symbolCT_single_eq_expPairing (q u : L) (k : ℕ) (c : (Fin k → ℕ) →₀ L) {β : Fin k →₀ ℤ}
    (hβ : ∀ σ : Equiv.Perm (Fin k), relabelExp σ β = β) :
    symbolCT q u k c (AddMonoidAlgebra.single β 1)
      = ∑ᶠ γ : Fin k →₀ ℤ, expAlphabetCoeff L k γ * symbolSym q u k c (-β - γ) := by
  rw [symbolCT_eq_pairing q u k c hβ,
    ← finsum_comp_equiv (Equiv.addLeft β)
      (f := fun α : Fin k →₀ ℤ => monoMul β (expAlphabetCoeff L k) α * symbolSym q u k c (-α))]
  refine finsum_congr fun γ => ?_
  rw [show (Equiv.addLeft β) γ = β + γ from rfl, monoMul_apply, add_sub_cancel_left,
    show -(β + γ) = -β - γ from by abel]

/-- The exponent `-l𝟏` is fixed by every permutation of the variables. -/
lemma relabelExp_neg_nsmul_allOnes (σ : Equiv.Perm (Fin k)) (l : ℕ) :
    relabelExp σ (-(l • allOnes k)) = -(l • allOnes k) := by
  rw [map_neg, map_nsmul, relabelExp_allOnes]

/-- **Step 4 at the monomials Step 3 produces**: for every `l ≥ 1` the exponential factor pairs to
zero against the symmetrised symbol shifted by `l𝟏`. Writing out
`(E_m)_γ = (-1)^{γ₁+⋯+γ_m} e_{γ₁}⋯e_{γ_m}` on `ℕ^m` and `0` elsewhere, this is BGLX's
equation (2.14). -/
theorem expPairing_eq_zero (q u : L) (m : ℕ) (c : ∀ k : ℕ, (Fin k → ℕ) →₀ L)
    (hκ : ∀ j : ℕ, 1 ≤ j → paramPleth q u (powerSum L j) ≠ 0)
    (hsum : ∑ k ∈ Finset.range (m + 1), dopWordOperator q u k (c k) = 0) {l : ℕ} (hl : 1 ≤ l) :
    ∑ᶠ γ : Fin m →₀ ℤ,
      expAlphabetCoeff L m γ * symbolSym q u m (c m) (l • allOnes m - γ) = 0 := by
  have h := symbolCT_monomial_eq_zero q u m c hκ hsum hl
  rw [symbolCT_single_eq_expPairing q u m (c m) (relabelExp_neg_nsmul_allOnes · l)] at h
  refine (finsum_congr fun γ => ?_).trans h
  rw [show l • allOnes m - γ = -(-(l • allOnes m)) - γ from by abel]

/-! ### The residual, in the form of BGLX's equation (2.14) -/

/-- **The residual of the necessity half of the BGLX criterion**, in the form the argument as
usually written leaves it: that the relations

`∑_{γ ∈ ℕ^m} (-1)^{γ₁+⋯+γ_m} e_{γ₁} ⋯ e_{γ_m} (Ξ_c)_{l𝟏-γ} = 0`, one for each `l ≥ 1`,

force `Ξ_c` to vanish. These are BGLX's equation (2.14), and the coefficients
`HJO.Bglx.expAlphabetCoeff` are exactly the elementary monomials with their signs.

This is Steps 5 and 6 of the proof and nothing else. What proving it takes: the sum is
finite, because `Ξ_c` is bounded below in total degree
(`HJO.Bglx.symbolSym_eq_zero_of_coordSum_lt_neg_bound`); grouping its terms by the partition
`λ(γ)` obtained from `γ` by deleting the zeros and sorting is legitimate because `Ξ_c` is symmetric
(`HJO.Bglx.relabel_symbolSym`), so `(Ξ_c)_{l𝟏-γ}` depends only on that partition; the coefficients
of the resulting relation `∑_λ N_λ (-1)^{|λ|} ξ_λ e_λ = 0` are *scalars*, by
`HJO.Bglx.scalar_symbolSym`, so it forces every `ξ_λ` to vanish as soon as the elementary monomials
`e_λ` are linearly independent over `𝕜` — which is
`HJO.Sym.linearIndependent_elemSymmMonomial`. Step 6 then
reaches an arbitrary exponent `γ` by taking `l` large.

The appeal to `scalar_symbolSym` is not a formality: the relation lives in `Λ` and the `e_λ` are
*not* independent over `Λ`, so without it Step 5 as usually written — which calls that relation a
`𝕜`-linear combination without saying why — would not be an appeal to
`HJO.Sym.linearIndependent_elemSymmMonomial` at all. -/
def IsExpPairingSeparating (q u : L) : Prop :=
  ∀ (m : ℕ) (c : (Fin m → ℕ) →₀ L),
    (∀ l : ℕ, 1 ≤ l → ∑ᶠ γ : Fin m →₀ ℤ,
        expAlphabetCoeff L m γ * symbolSym q u m c (l • allOnes m - γ) = 0) →
      symbolSym q u m c = 0

/-- **The residual in the form of equation (2.14) gives the residual in the form of Step 3.** -/
theorem isTopMonomialSeparating_of_isExpPairingSeparating (q u : L)
    (h : IsExpPairingSeparating q u) : IsTopMonomialSeparating q u := by
  intro m c hmono
  refine h m c fun l hl => ?_
  have hx := hmono l hl
  rw [symbolCT_single_eq_expPairing q u m c (relabelExp_neg_nsmul_allOnes · l)] at hx
  refine (finsum_congr fun γ => ?_).trans hx
  rw [show l • allOnes m - γ = -(-(l • allOnes m)) - γ from by abel]

/-- **The residual carries the whole of the necessity half of the criterion**, at parameters neither
of which is a root of unity. -/
theorem criterionNecessary_of_isExpPairingSeparating (q u : L)
    (hκ : ∀ j : ℕ, 1 ≤ j → paramPleth q u (powerSum L j) ≠ 0)
    (h : IsExpPairingSeparating q u) : IsVanishingCriterionNecessary q u :=
  criterionNecessary_of_isTopMonomialSeparating q u hκ
    (isTopMonomialSeparating_of_isExpPairingSeparating q u h)

/-- **The index shift exists as soon as the residual does**, at algebraically independent
parameters. This is the exact shape of the `hshift` hypothesis of
`HJO.CollinearNarrowed.collinearCommute_of_structures`, conditional on
`HJO.Bglx.IsExpPairingSeparating` and nothing else. -/
theorem exists_isIndexShift_of_isExpPairingSeparating (q u : L)
    (hqu : AlgebraicIndependent ℤ ![q, u]) (h : IsExpPairingSeparating q u) :
    ∃ S : DopAlgebra q u →ₐ[L] DopAlgebra q u, IsIndexShift q u S :=
  exists_isIndexShift_of_isTopMonomialSeparating q u hqu
    (isTopMonomialSeparating_of_isExpPairingSeparating q u h)

end HJO.Bglx
