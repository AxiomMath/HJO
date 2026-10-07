/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.Collinear.KernelExpansion
public import HJO.Collinear.WordCriterion
public meta import HJO.Attr

/-! # The symmetrised symbol and the statement of the BGLX vanishing criterion

The criterion BGLX prove as their Theorem 2.1 decides when a combination of words in the basic
operators acts by zero, and the object it decides with is the **symmetrised symbol**

`Ξ_c = (1/k!) ∑_τ τ_*(Π_c Ω̂_k)`,

the average over the `k!` orderings of the relabellings of the product of the symbol `Π_c` of the
coefficient family with the expansion `Ω̂_k` of the kernel factor. The summand indexed by `τ` lies
in the cone ring `R^τ_k` and in general in no other, so the average lies in none of them: it is
recorded in the module `M_k` of *all* formal sums, where addition needs no support condition. That
is why `Ξ_c` is a `HJO.Bglx.Family`, not a `HJO.Bglx.ConeRing`.

With `Ξ` available the criterion can be *stated*, which is what this file is for. Its two halves are
of very different sizes and do not carry the same hypotheses: sufficiency is a formal identity and
is proved in `HJO/Collinear/CriterionSufficient.lean`, while necessity needs a hypothesis on
the parameters and so is recorded here as a named predicate, in the same style as
`HJO.Sym.RaiseStableKernel` in `HJO/Collinear/IndexShift.lean`, so that what rests on it stays
visible. Necessity itself is proved in `HJO/Collinear/ExpPairingSeparating.lean`.

## Main definitions

* `HJO.Bglx.symbolFamily`: the symbol `Π_c` of `HJO.Sym.dopWordSymbol`, read as a formal sum with
  coefficients in `Λ`; `HJO.Bglx.symbolElem` is the same thing in the cone ring of an ordering.
* `HJO.Bglx.symbolSym`: the symmetrised symbol `Ξ_c`.
* `HJO.Bglx.IsVanishingCriterion`: the criterion itself, as a statement about the parameters.
* `HJO.Bglx.IsVanishingCriterionNecessary`: its necessity half, the half that constrains the
  parameters.

## Main statements

* `HJO.Bglx.symbolSym_one`: at one variable the symmetrised symbol is the symbol itself.
* `HJO.Bglx.monoMul_allOnes_symbolSym_dopWordRaise`: raising every index of every word divides the
  symmetrised symbol by `z₁z₂⋯z_k`.
* `HJO.Bglx.symbolSym_dopWordRaise_eq_zero_iff`: hence the vanishing of the symmetrised symbol is
  invariant under raising every index — the part of
  `HJO.Sym.dopWordOperator_dopWordRaise_eq_zero_iff` that needs no criterion.

## Implementation notes

**The coefficients of `Π_c` are pushed into `Λ`.** `HJO.Sym.dopWordSymbol` is a Laurent polynomial
with coefficients in the base field, and `Ω̂_k` lives in a cone ring whose coefficients are
symmetric functions; the product is formed there, so the symbol is read through
`algebraMap L (Lambda L)`. That is the standard reading — `𝕜 ⊆ Λ` — and it is what makes
`Ξ_c` a member of `M_k`, as required.

**Why the criterion is a predicate and not a theorem here.** Its sufficiency half is a short
consequence of the pairing of the operator against the symmetrised symbol; its necessity half is a
seven-step induction over the finite alphabets whose fifth step divides by
`κ(p_j) = (1-q^j)(1-u^j)`, one factor for each part `j` of a partition, and so needs `q^j ≠ 1` and
`u^j ≠ 1` for every `j ≥ 1`. That is not true at every pair of parameters over a general field,
though it is true at the standing field `𝕜 = ℚ(q,u)`, where the algebraic independence of the two
indeterminates supplies it (`HJO.Bglx.paramPleth_powerSum_ne_zero_of_algebraicIndependent`) — which
is why necessity is usually stated without the hypothesis its proof uses. Carrying
necessity as a predicate keeps that hypothesis out of everything between here and
`HJO.Bglx.criterionNecessary`, which is where it enters.

**`monoMul_allOnes_symbolSym_dopWordRaise` needs no criterion and no hypothesis on the parameters.**
It is the formal half of `HJO.Sym.dopWordOperator_dopWordRaise_eq_zero_iff`: `Π_c = z₁⋯z_k Π_{c⁺}`
(`HJO.Sym.prod_single_mul_dopWordSymbol_dopWordRaise`), and the symmetric monomial passes across
every relabelling (`HJO.Bglx.relabel_monoMul_allOnes`), so the average is multiplied by it too.
Injectivity of multiplication by a monomial enters only afterwards, to turn that identity into the
equivalence `symbolSym_dopWordRaise_eq_zero_iff` (`HJO.Bglx.monoMul_eq_zero_iff`). What none of it
gives is the operator statement: passing from `Ξ_{c⁺} = 0` to `V_{c⁺} = 0` is sufficiency, and from
`V_c = 0` to `Ξ_c = 0` is necessity.

## References

The reference is F. Bergeron, A. M. Garsia, E. Leven and G. Xin, *Some remarkable new plethystic
operators in the theory of Macdonald polynomials*, arXiv:1405.0316v1, J. Comb. **7** (2016)
671--714, whose Theorem 2.1 is the criterion and whose equation (2.11) is the left-hand side `Ξ_c`.
-/

@[expose] public section

namespace HJO.Bglx

open HJO.Sym

variable {L : Type*} [Field L] [Algebra ℚ L] {k : ℕ}

/-! ### The symbol as a formal sum -/

/-- The symbol `Π_c = ∑_a c_a z₁^{-a₁}⋯z_k^{-a_k}` of a coefficient family, read as a formal sum
with coefficients in `Λ`. -/
noncomputable def symbolFamily (c : (Fin k → ℕ) →₀ L) : Family k (Lambda L) :=
  fun α => algebraMap L (Lambda L) ((dopWordSymbol L k c).coeff α)

omit [Algebra ℚ L] in
/-- The symbol has finite support, being the coefficient family of a Laurent polynomial. -/
lemma finite_support_symbolFamily (c : (Fin k → ℕ) →₀ L) :
    (Function.support (symbolFamily c)).Finite :=
  Set.Finite.subset (dopWordSymbol L k c).coeff.support.finite_toSet fun α hα =>
    Finsupp.mem_support_iff.2 fun h => hα (by rw [symbolFamily, h, map_zero])

/-- The symbol `Π_c` as an element of the cone ring of an ordering: it has finite support, so it
lies there for every ordering. -/
noncomputable def symbolElem (τ : Equiv.Perm (Fin k)) (c : (Fin k → ℕ) →₀ L) :
    ConeRing k τ (Lambda L) where
  coeff := symbolFamily c
  isConeBounded := isConeBounded_of_finite (finite_support_symbolFamily c)

omit [Algebra ℚ L] in
@[simp] lemma coeff_symbolElem (τ : Equiv.Perm (Fin k)) (c : (Fin k → ℕ) →₀ L) :
    (symbolElem τ c).coeff = symbolFamily c := rfl

/-! ### The symmetrised symbol -/

/-- **The symmetrised symbol** `Ξ_c = (1/k!) ∑_τ τ_*(Π_c Ω̂_k)`, the product being formed in the
cone ring of the identity ordering and the average recorded in the module of all formal sums,
where the `k!` summands — each cone-bounded for its own ordering and in general for no other — may
be added. At `k ≤ 1` the only permutation is the identity and the kernel expansion is `1`, so
`Ξ_c = Π_c`. -/
@[hjo "def_bglx_symbol_symmetrisation"]
noncomputable def symbolSym (q u : L) (k : ℕ) (c : (Fin k → ℕ) →₀ L) : Family k (Lambda L) :=
  (Nat.factorial k : L)⁻¹ • ∑ σ : Equiv.Perm (Fin k),
    relabel σ (symbolElem 1 c * kernelExpansion q u k).coeff

/-- At one variable the kernel expansion is the empty product, hence `1`. -/
lemma kernelExpansion_one (q u : L) : kernelExpansion q u 1 = 1 := by
  rw [kernelExpansion]
  exact Finset.prod_eq_one fun i _ => Finset.prod_eq_one fun j hj =>
    absurd (Finset.mem_Ioi.1 hj) (by omega)

/-- **At one variable the symmetrised symbol is the symbol itself**, the only permutation being the
identity and the kernel expansion being `1`. This is the degenerate case, and
it shows the definition is not vacuous. -/
theorem symbolSym_one (q u : L) (c : (Fin 1 → ℕ) →₀ L) :
    symbolSym q u 1 c = symbolFamily c := by
  rw [symbolSym, kernelExpansion_one, mul_one,
    Finset.sum_eq_single_of_mem (1 : Equiv.Perm (Fin 1)) (Finset.mem_univ _)
      fun σ _ hσ => absurd (Subsingleton.elim σ 1) hσ,
    relabel_one, coeff_symbolElem, Nat.factorial_one, Nat.cast_one, inv_one, one_smul]

/-! ### Raising every index -/

/-- The exponent `𝟏` is the sum of the standard basis vectors. -/
lemma allOnes_eq_sum (k : ℕ) : allOnes k = ∑ i : Fin k, Finsupp.single i (1 : ℤ) :=
  Finsupp.ext fun i => by
    rw [allOnes_apply, Finsupp.finsetSum_apply, Finset.sum_eq_single_of_mem i (Finset.mem_univ i)
      fun j _ hj => Finsupp.single_eq_of_ne (Ne.symm hj), Finsupp.single_eq_same]

omit [Algebra ℚ L] in
/-- **The symbol of a raised family is the symbol divided by `z₁⋯z_k`.** This is
`HJO.Sym.prod_single_mul_dopWordSymbol_dopWordRaise` read on coefficient families. -/
theorem symbolFamily_eq_monoMul (c : (Fin k → ℕ) →₀ L) :
    symbolFamily c = monoMul (allOnes k) (symbolFamily (dopWordRaise L k c)) := by
  have hprod := prod_single_mul_dopWordSymbol_dopWordRaise (K := L) (k := k) c
  rw [show (∏ i : Fin k, AddMonoidAlgebra.single (Finsupp.single i (1 : ℤ)) (1 : L))
      = AddMonoidAlgebra.single (allOnes k) (1 : L) by
    rw [allOnes_eq_sum]; simp] at hprod
  funext α
  rw [monoMul_apply, symbolFamily, symbolFamily, ← hprod]
  congr 1
  rw [AddMonoidAlgebra.coeff_single_mul_eq_mul_coeff (α - allOnes k)
    fun y _ => by rw [eq_sub_iff_add_eq, add_comm (allOnes k) y], one_mul]

omit [Algebra ℚ L] in
/-- The monomial multiplication of a scalar multiple. -/
lemma monoMul_smul (β : Fin k →₀ ℤ) (a : L) (f : Family k (Lambda L)) :
    monoMul β (a • f) = a • monoMul β f := rfl

omit [Algebra ℚ L] in
/-- The monomial multiplication of a finite sum. -/
lemma monoMul_sum {ι : Type*} (s : Finset ι) (β : Fin k →₀ ℤ) (f : ι → Family k (Lambda L)) :
    monoMul β (∑ i ∈ s, f i) = ∑ i ∈ s, monoMul β (f i) := by
  funext α
  simp only [monoMul_apply, Finset.sum_apply]

/-- **Raising every index of every word multiplies the symmetrised symbol by `z₁z₂⋯z_k`.** No
hypothesis on the parameters, and no criterion: the symbol of the raised family is the symbol
divided by the symmetric monomial, and that monomial passes across every relabelling. -/
theorem monoMul_allOnes_symbolSym_dopWordRaise (q u : L) (k : ℕ) (c : (Fin k → ℕ) →₀ L) :
    monoMul (allOnes k) (symbolSym q u k (dopWordRaise L k c)) = symbolSym q u k c := by
  have hsymb : symbolElem (1 : Equiv.Perm (Fin k)) c
      = monoElem 1 (allOnes k) * symbolElem 1 (dopWordRaise L k c) :=
    ConeRing.ext (by rw [coeff_monoElem_mul, coeff_symbolElem, coeff_symbolElem,
      symbolFamily_eq_monoMul c])
  have hmul : (symbolElem (1 : Equiv.Perm (Fin k)) c * kernelExpansion q u k).coeff
      = monoMul (allOnes k)
        (symbolElem 1 (dopWordRaise L k c) * kernelExpansion q u k).coeff := by
    rw [hsymb, mul_assoc, coeff_monoElem_mul]
  rw [symbolSym, symbolSym, monoMul_smul, monoMul_sum]
  congr 1
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [← relabel_monoMul_allOnes, ← hmul]

/-- **The vanishing of the symmetrised symbol is invariant under raising every index.** -/
theorem symbolSym_dopWordRaise_eq_zero_iff (q u : L) (k : ℕ) (c : (Fin k → ℕ) →₀ L) :
    symbolSym q u k (dopWordRaise L k c) = 0 ↔ symbolSym q u k c = 0 := by
  rw [← monoMul_allOnes_symbolSym_dopWordRaise q u k c]
  exact (monoMul_eq_zero_iff _ _).symm

/-! ### The criterion, as a statement -/

/-- **The BGLX vanishing criterion**, as a statement about the parameters: a combination of words of
lengths at most `m` in the basic operators acts by zero on the symmetric functions if and only if
the symmetrised symbol of each of its homogeneous parts vanishes. This is BGLX's Theorem 2.1 in the
form their equations (2.10) and (2.11) state it. -/
def IsVanishingCriterion (q u : L) : Prop :=
  ∀ (m : ℕ) (c : ∀ k : ℕ, (Fin k → ℕ) →₀ L),
    (∑ k ∈ Finset.range (m + 1), dopWordOperator q u k (c k)) = 0
      ↔ ∀ k ≤ m, symbolSym q u k (c k) = 0

/-- **The necessity half of the criterion**: an operator acting by zero forces the symmetrised
symbol of each homogeneous part to vanish. This is the half BGLX prove by induction over the
finite alphabets, and it is discharged here by `HJO.Bglx.criterionNecessary`, whose one hypothesis
on the parameters is the one usually left unstated: `κ(p_j) = (1-q^j)(1-u^j) ≠ 0` for
every `j ≥ 1`, that is, neither parameter is a root of unity. It stays a named predicate because
`HJO.Bglx.isVanishingCriterion_of_necessary` consumes it, so what rests on the necessity half
remains visible. -/
def IsVanishingCriterionNecessary (q u : L) : Prop :=
  ∀ (m : ℕ) (c : ∀ k : ℕ, (Fin k → ℕ) →₀ L),
    (∑ k ∈ Finset.range (m + 1), dopWordOperator q u k (c k)) = 0
      → ∀ k ≤ m, symbolSym q u k (c k) = 0

end HJO.Bglx
