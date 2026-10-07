/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.CarlssonMellit.InsertRealisation
public import HJO.CarlssonMellit.SeriesGrading
public meta import HJO.Attr

/-! # The insertion is injective where it is defined

One lemma, `HJO.Sym.injOn_insertFront`: `Φ_k` is injective on the series of `P_k` whose `x₁`-degree
is bounded at each letter-monomial, equivalently on each graded piece `P^gr_{k,d}` of
`HJO.Sym.pGraded`.

The unrestricted statement, injectivity of `Φ_k` on all of `P_k`, is false at the only total
rendering of `Φ_k`: `HJO.Sym.not_injective_insertFront` of `HJO.CarlssonMellit.InsertNotInjective`
sends `∑_{a ≥ 0}x₁^a` to `0`. This lemma is the cancellation its consumer
`HJO.Dyck.isSigmaCharacter_dminusCM'` actually needs, and the bound is what makes it true — the
arguments `HJO.Dyck.isSigmaCharacter_dminusCM'` cancels are values of `ι∘θ` and of `ν`, of bounded
degree, not that pathological series.

## Main definitions

* `HJO.Sym.BoundedFrontDegree`: the `x₁`-degree is bounded at each letter-monomial — for
  every letter-monomial `e` in `x₂, x₃, …` the coefficients of `F` at `x₁^a e` vanish for all large
  `a`. This is exactly the condition under which the defining sum of `HJO.Sym.insertFront` at `e`
  is finite, hence under which `Φ_k` takes its intended value, the full sum, there.

## Main results

* `HJO.Sym.injOn_insertFront` in its stated form — `Φ_k` is
  injective on `{F | BoundedFrontDegree F}`.
* `HJO.Sym.injOn_insertFront_isHomogeneous`: the same on each graded piece
  `P^gr_{k,d}`; `HJO.Sym.boundedFrontDegree_of_isHomogeneous` is the
  implication that makes the two readings agree, and `HJO.Sym.mem_pGraded_auxToFrac_iff` identifies
  the homogeneity condition on `P_k` with membership in `P^gr_{k,d}` read through the inclusion
  `HJO.Sym.auxToFrac` of `P_k` in `P°_k`, which is where `HJO.Sym.pGraded` states it.
* `HJO.Sym.coeff_coeff_insertFront`: the extraction that carries the proof — the coefficient of
  `Φ_k(F)` at the monomial `y_{k+1}^b y^μ` of `e` pushed up one letter is the coefficient of `F` at
  `y^μ` of `x₁^b e`. So every coefficient of `F` is *read off* `Φ_k(F)`, which is injectivity with
  a left inverse rather than a cancellation argument.

## Implementation notes

*The proof is a left inverse, not a span argument.* The natural argument is that `Φ_k`
carries distinct monomials to distinct monomials and that a linear map injective on a basis is
injective on finite spans. An element of `P_k` is not in a finite span of monomials — it is a power
series — so "finite span" there means the bounded-degree condition, and the argument that survives
the translation is the sharper one: under the bound the defining sum is a `Finset` sum, and the
coefficient of `F` at `x₁^b·e·y^μ` is recovered from a single coefficient of `Φ_k(F)`. That
recovery is `HJO.Sym.coeff_coeff_insertFront` and it needs no injectivity input at all.

*What the recovery rests on.* `Φ_k`'s value at `e` is `∑_a y_{k+1}^a·ρ(c_a)` with
`ρ = MvPolynomial.rename Fin.castSucc` and `c_a` the coefficient of `F` at `x₁^a e`. The exponents
`Finsupp.single (Fin.last k) b + Finsupp.mapDomain Fin.castSucc μ` separate the summands: `ρ` lands
in the monomials whose `y_{k+1}`-exponent is `0`, so the `a`-th summand contributes to that
exponent only when `a = b`, and there it contributes `c_b`'s coefficient at `μ`. That is
`HJO.Sym.coeff_X_last_pow_mul_rename`, proved from `MvPolynomial.coeff_monomial_mul'` and
`MvPolynomial.coeff_rename_mapDomain`; no ring isomorphism `𝕂[y₁,…,y_{k+1}] ≅ 𝕂[y₁,…,y_k][y_{k+1}]`
is introduced, the two coefficient lemmas being the whole content of one.

*The bound is stated as a bound and used as a finite sum.* `BoundedFrontDegree` says the
coefficients vanish above some `N`;
`HJO.Sym.coeff_insertFront_eq_sum` turns it into the `Finset` sum over `Finset.range (N + 1)` that
the extraction reads. Over `ℕ` the bound and the finiteness of the support of the defining family
are the same condition, and the sum is taken over any range large enough, so the value does not
depend on which `N` the hypothesis supplies.

*No hypothesis on `K` beyond `CommRing`, except for the bridge to `P^gr_{k,d}`.* The extraction is
an identity between coefficients and needs nothing. `HJO.Sym.mem_pGraded_auxToFrac_iff` compares
homogeneity in `P_k` with homogeneity in `P°_k` and so needs the coefficient inclusion
`𝕂[y₁,…,y_k] → 𝕂(y₁,…,y_k)` to be injective, which is `[IsDomain K]`; the intended base
`𝕂 = ℚ(q,u)` is a field.

## References

E. Carlsson and A. Mellit, *A proof of the shuffle conjecture*, J. Amer. Math. Soc. **31** (2018)
661--697, Section 4, where the substitution is an identification of rings of rational functions and
its injectivity is not discussed. The lemma `HJO.Sym.injOn_insertFront` uses
`HJO.Sym.AuxAlphabetSeries`, `HJO.Sym.pGraded` and `HJO.Sym.insertFront`; it is the form of
injectivity `HJO.Dyck.isSigmaCharacter_dminusCM'` needs, the unrestricted form being refuted in
`HJO.CarlssonMellit.InsertNotInjective`.
-/

@[expose] public section

namespace HJO.Sym

variable {K : Type*} [CommRing K] {k : ℕ}

/-! ### Separating the powers of the new auxiliary variable -/

/-- The last auxiliary variable is not a renamed lower one: `Fin.last k` is outside the range of
`Fin.castSucc`. -/
theorem last_notMem_range_castSucc (k : ℕ) :
    (Fin.last k) ∉ Set.range (Fin.castSucc : Fin k → Fin (k + 1)) := by
  rintro ⟨i, hi⟩
  exact absurd hi (Fin.castSucc_lt_last i).ne

/-- The exponent `y_{k+1}^b y^μ`, read at the new auxiliary variable, is `b`. -/
theorem single_last_add_mapDomain_apply_last (b : ℕ) (μ : Fin k →₀ ℕ) :
    (Finsupp.single (Fin.last k) b + Finsupp.mapDomain Fin.castSucc μ) (Fin.last k) = b := by
  rw [Finsupp.add_apply, Finsupp.single_eq_same,
    Finsupp.mapDomain_of_notMem_range μ _ (last_notMem_range_castSucc k), add_zero]

/-- The exponent `y_{k+1}^b y^μ`, read at a lower auxiliary variable, is the exponent in `μ`. -/
theorem single_last_add_mapDomain_apply_castSucc (b : ℕ) (μ : Fin k →₀ ℕ) (i : Fin k) :
    (Finsupp.single (Fin.last k) b + Finsupp.mapDomain Fin.castSucc μ) (Fin.castSucc i) = μ i := by
  rw [Finsupp.add_apply, Finsupp.single_eq_of_ne (Fin.castSucc_lt_last i).ne,
    Finsupp.mapDomain_apply (Fin.castSucc_injective k), zero_add]

/-- Subtracting a power of the new auxiliary variable from the exponent `y_{k+1}^b y^μ` lowers that
power and leaves `μ` alone. -/
theorem single_last_add_mapDomain_sub (a b : ℕ) (μ : Fin k →₀ ℕ) :
    Finsupp.single (Fin.last k) b + Finsupp.mapDomain Fin.castSucc μ
        - Finsupp.single (Fin.last k) a
      = Finsupp.single (Fin.last k) (b - a) + Finsupp.mapDomain Fin.castSucc μ := by
  refine Finsupp.ext fun j => ?_
  rw [Finsupp.tsub_apply]
  refine Fin.lastCases ?_ ?_ j
  · rw [single_last_add_mapDomain_apply_last, single_last_add_mapDomain_apply_last,
      Finsupp.single_eq_same]
  · intro i
    rw [single_last_add_mapDomain_apply_castSucc, single_last_add_mapDomain_apply_castSucc,
      Finsupp.single_eq_of_ne (Fin.castSucc_lt_last i).ne, Nat.sub_zero]

/-- A renamed lower polynomial has no coefficient at an exponent involving the new auxiliary
variable. -/
theorem coeff_rename_castSucc_eq_zero {b : ℕ} (hb : b ≠ 0) (μ : Fin k →₀ ℕ)
    (p : MvPolynomial (Fin k) K) :
    MvPolynomial.coeff (Finsupp.single (Fin.last k) b + Finsupp.mapDomain Fin.castSucc μ)
        (MvPolynomial.rename Fin.castSucc p) = 0 := by
  refine MvPolynomial.coeff_rename_eq_zero _ _ _ fun u hu => absurd ?_ hb
  rw [← single_last_add_mapDomain_apply_last b μ, ← hu,
    Finsupp.mapDomain_of_notMem_range u _ (last_notMem_range_castSucc k)]

/-- **The powers of the new auxiliary variable are separated by a coefficient.** In a term
`y_{k+1}^a ρ(p)` with `ρ = MvPolynomial.rename Fin.castSucc`, the coefficient at the exponent
`y_{k+1}^b y^μ` is the coefficient of `p` at `μ` when `a = b` and `0` otherwise: `ρ(p)` is supported
where the exponent of `y_{k+1}` is `0`, so the power `a` is visible in the exponent.

This is the whole content of the isomorphism `𝕂[y₁,…,y_{k+1}] ≅ 𝕂[y₁,…,y_k][y_{k+1}]`, in the one
form the extraction below needs. -/
theorem coeff_X_last_pow_mul_rename (a b : ℕ) (μ : Fin k →₀ ℕ) (p : MvPolynomial (Fin k) K) :
    MvPolynomial.coeff (Finsupp.single (Fin.last k) b + Finsupp.mapDomain Fin.castSucc μ)
        (MvPolynomial.X (Fin.last k) ^ a * MvPolynomial.rename Fin.castSucc p)
      = if a = b then MvPolynomial.coeff μ p else 0 := by
  have hle : (Finsupp.single (Fin.last k) a
      ≤ Finsupp.single (Fin.last k) b + Finsupp.mapDomain Fin.castSucc μ) ↔ a ≤ b := by
    rw [Finsupp.single_le_iff, single_last_add_mapDomain_apply_last]
  rw [MvPolynomial.X_pow_eq_monomial, MvPolynomial.coeff_monomial_mul']
  by_cases hab : a ≤ b
  · rw [ite_eq_left (hle.2 hab), single_last_add_mapDomain_sub, one_mul]
    by_cases hb : a = b
    · rw [ite_eq_left hb, show b - a = 0 from by omega, Finsupp.single_zero, zero_add,
        MvPolynomial.coeff_rename_mapDomain _ (Fin.castSucc_injective k)]
    · rw [ite_eq_right hb, coeff_rename_castSucc_eq_zero (by omega)]
  · rw [ite_eq_right fun h => hab (hle.1 h), ite_eq_right (by omega)]

/-! ### Series of bounded degree in the first letter -/

/-- Homogeneity, read with `Finsupp.degree` rather than `Finsupp.weight 1`. Mathlib's
`MvPowerSeries.IsHomogeneous` is the weighted notion at the constant weight `1`, and the two
functions agree by `Finsupp.degree_eq_weight_one`; this is the form in which the condition "every
monomial has total degree `d`" is read. The binder is explicit here, the one in `IsHomogeneous`
being strict-implicit. -/
theorem isHomogeneous_iff_forall_degree {σ R : Type*} [Semiring R] {G : MvPowerSeries σ R}
    {d : ℕ} :
    MvPowerSeries.IsHomogeneous G d ↔
      ∀ α : σ →₀ ℕ, MvPowerSeries.coeff α G ≠ 0 → Finsupp.degree α = d := by
  have h : (Finsupp.weight (1 : σ → ℕ) : (σ →₀ ℕ) →+ ℕ) = Finsupp.degree :=
    Finsupp.degree_eq_weight_one.symm
  have hw : ∀ α : σ →₀ ℕ, Finsupp.weight (1 : σ → ℕ) α = Finsupp.degree α := fun α => by rw [h]
  exact ⟨fun hG α hα => (hw α).symm.trans (hG hα), fun hG α hα => (hw α).trans (hG α hα)⟩

/-- **The bounded `x₁`-degree at each letter-monomial**: for every letter-monomial `e` in
`x₂, x₃, …` the coefficients of `F` at `x₁^a e` vanish for all `a` above a bound. This is exactly
the condition under which the defining sum of `HJO.Sym.insertFront` at `e` is finite, hence under
which `Φ_k` takes its intended value, the full sum, there — the substitution `x₁ ↦ y_{k+1}` turning
an unbounded `x₁`-degree into a `y_{k+1}`-degree no polynomial coefficient can carry. -/
def BoundedFrontDegree (F : AuxAlphabetSeries K k) : Prop :=
  ∀ e : ℕ →₀ ℕ, ∃ N : ℕ, ∀ a : ℕ, N < a →
    MvPowerSeries.coeff (Finsupp.single 0 a + e.mapDomain Nat.succ) F = 0

/-- **A graded series has bounded `x₁`-degree**: if every letter-monomial of `F` has total degree
`d`, then a nonzero coefficient at `x₁^a e` forces `a ≤ d`, the exponent of `x₁` being at most the
total degree. This is what makes the bounded reading and the graded reading, on each graded piece
`P^gr_{k,d}`, agree. -/
theorem boundedFrontDegree_of_isHomogeneous {F : AuxAlphabetSeries K k} {d : ℕ}
    (hF : MvPowerSeries.IsHomogeneous F d) : BoundedFrontDegree F := fun e =>
  ⟨d, fun a ha => by
    by_contra hne
    have hdeg : Finsupp.degree (Finsupp.single 0 a + e.mapDomain Nat.succ) = d :=
      isHomogeneous_iff_forall_degree.1 hF _ hne
    have hle : a ≤ Finsupp.degree (Finsupp.single 0 a + e.mapDomain Nat.succ) := by
      have h : (Finsupp.single 0 a + e.mapDomain Nat.succ : ℕ →₀ ℕ) 0 = a := by
        rw [Finsupp.add_apply, Finsupp.single_eq_same,
          Finsupp.mapDomain_of_notMem_range e 0 (by simp), add_zero]
      have h2 := Finsupp.le_degree (R := ℕ) 0 (Finsupp.single 0 a + e.mapDomain Nat.succ)
      rwa [h] at h2
    omega⟩

/-- **Under the bound the defining sum of `Φ_k` is a `Finset` sum**, over any range carrying every
power of `x₁` that occurs. This is the form in which the value is read. -/
theorem coeff_insertFront_eq_sum {F : AuxAlphabetSeries K k} {e : ℕ →₀ ℕ} {N : ℕ}
    (hN : ∀ a : ℕ, N < a → MvPowerSeries.coeff (Finsupp.single 0 a + e.mapDomain Nat.succ) F = 0) :
    MvPowerSeries.coeff e (insertFront K k F)
      = ∑ a ∈ Finset.range (N + 1), MvPolynomial.X (Fin.last k) ^ a *
          MvPolynomial.rename Fin.castSucc
            (MvPowerSeries.coeff (Finsupp.single 0 a + e.mapDomain Nat.succ) F) := by
  rw [coeff_insertFront]
  refine finsum_eq_sum_of_support_subset _ fun a ha => ?_
  rw [Finset.coe_range, Set.mem_Iio, Nat.lt_succ_iff, ← Nat.not_lt]
  intro haN
  rw [Function.mem_support, hN a haN, map_zero, mul_zero] at ha
  exact ha rfl

/-! ### Every coefficient is read off the image -/

/-- **The extraction**: for a series of bounded `x₁`-degree, the coefficient of `Φ_k(F)` at the
monomial `y_{k+1}^b y^μ` of the letter-monomial `e` pushed up one letter is the coefficient of `F`
at `y^μ` of `x₁^b e`. So `Φ_k(F)` carries every coefficient of `F`, and
`HJO.Sym.injOn_insertFront` is immediate.

The bound is what makes this true: at a letter-monomial where the defining sum is infinite the value
is `0` by `HJO.Sym.insertFront`'s total extension, and nothing is recoverable — which is exactly how
`HJO.Sym.not_injective_insertFront` refutes the unrestricted statement. -/
theorem coeff_coeff_insertFront {F : AuxAlphabetSeries K k} (hF : BoundedFrontDegree F)
    (b : ℕ) (e : ℕ →₀ ℕ) (μ : Fin k →₀ ℕ) :
    MvPolynomial.coeff (Finsupp.single (Fin.last k) b + Finsupp.mapDomain Fin.castSucc μ)
        (MvPowerSeries.coeff e (insertFront K k F))
      = MvPolynomial.coeff μ
          (MvPowerSeries.coeff (Finsupp.single 0 b + e.mapDomain Nat.succ) F) := by
  obtain ⟨N, hN⟩ := hF e
  have hN' : ∀ a : ℕ, max N b < a →
      MvPowerSeries.coeff (Finsupp.single 0 a + e.mapDomain Nat.succ) F = 0 :=
    fun a ha => hN a (by omega)
  rw [coeff_insertFront_eq_sum hN', MvPolynomial.coeff_sum,
    Finset.sum_congr rfl fun a _ => coeff_X_last_pow_mul_rename a b μ _]
  refine (Finset.sum_eq_single_of_mem b (Finset.mem_range.2 (by omega))
    fun a _ hab => ite_eq_right hab).trans (ite_eq_left rfl)

/-! ### The injectivity -/

/-- **Insertion is injective where it is defined**: `Φ_k` is injective on the series of `P_k` whose
`x₁`-degree is bounded at each letter-monomial. Every coefficient of `F` is read off `Φ_k(F)` by
`HJO.Sym.coeff_coeff_insertFront`, each letter-monomial `β` of `P_k` being `x₁^{β_1}` times its own
tail pushed up one letter (`HJO.Sym.single_add_mapDomain_dropFirst`).

This is the cancellation `HJO.Dyck.isSigmaCharacter_dminusCM'` needs. The unrestricted form of
`HJO.Sym.injOn_insertFront` is false at the total extension `HJO.Sym.insertFront`
(`HJO.Sym.not_injective_insertFront`), and the bound is not a convenience: it is the condition under
which `Φ_k` takes its intended value at all. -/
@[hjo "lem_cm_insert_injective_bounded"]
theorem injOn_insertFront (K : Type*) [CommRing K] (k : ℕ) :
    Set.InjOn (insertFront K k) {F : AuxAlphabetSeries K k | BoundedFrontDegree F} := by
  intro F hF F' hF' h
  refine MvPowerSeries.ext fun β => ?_
  refine MvPolynomial.ext _ _ fun ν => ?_
  have hβ : Finsupp.single 0 (β 0) + (dropFirst β).mapDomain Nat.succ = β :=
    single_add_mapDomain_dropFirst β
  rw [← hβ, ← coeff_coeff_insertFront hF, ← coeff_coeff_insertFront hF', h]

attribute [hjo "lem_cm_insert_injective"] injOn_insertFront

/-- **The same on a graded piece**, which is the second reading of the statement: `Φ_k` is
injective on the series every letter-monomial of which has total degree `d`. By
`HJO.Sym.boundedFrontDegree_of_isHomogeneous` such a series has bounded `x₁`-degree, the exponent of
`x₁` being at most the total degree. -/
@[hjo "lem_cm_insert_injective_bounded"]
theorem injOn_insertFront_isHomogeneous (K : Type*) [CommRing K] (k d : ℕ) :
    Set.InjOn (insertFront K k) {F : AuxAlphabetSeries K k | MvPowerSeries.IsHomogeneous F d} :=
  fun _ hF _ hF' h => injOn_insertFront K k (boundedFrontDegree_of_isHomogeneous hF)
    (boundedFrontDegree_of_isHomogeneous hF') h

/-- **The graded condition on `P_k` is membership in `P^gr_{k,d}`**, read through the inclusion
`HJO.Sym.auxToFrac` of `P_k` in `P°_k`, which is where `HJO.Sym.pGraded` states the grading. The
inclusion acts on each coefficient by the injection of the coefficient ring into its fraction field,
so it neither creates nor destroys a nonzero coefficient. -/
theorem mem_pGraded_auxToFrac_iff [IsDomain K] {F : AuxAlphabetSeries K k} {d : ℕ} :
    auxToFrac K k F ∈ pGraded K k d ↔ MvPowerSeries.IsHomogeneous F d := by
  have hinj : Function.Injective
      (algebraMap (MvPolynomial (Fin k) K) (AuxFrac K k)) :=
    IsFractionRing.injective _ _
  rw [mem_pGraded_iff, isHomogeneous_iff_forall_degree]
  refine ⟨fun h α hα => h α ?_, fun h α hα => h α ?_⟩
  · rw [coeff_auxToFrac]
    exact fun hz => hα (hinj (by rw [hz, map_zero]))
  · rw [coeff_auxToFrac] at hα
    exact fun hz => hα (by rw [hz, map_zero])

end HJO.Sym
