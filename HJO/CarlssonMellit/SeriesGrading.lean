/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Mathlib.RingTheory.MvPowerSeries.Order
public import HJO.CarlssonMellit.PSwap
public meta import HJO.Attr

/-! # The two gradings of the Carlsson--Mellit series ring

The lowering step of the Carlsson--Mellit analysis needs two gradings of
`P°_k = 𝕂(y₁, …, y_k)⟦x₁, x₂, …⟧`, and they are different gradings.

The first, `P^gr_{k,d}`, counts the total degree in the *free variables* `x₁, x₂, …` alone. It is
the home in which the swapping operator's division by `x_{r+1} - x_r` is legitimate: that
difference has no constant term, so it is not invertible in `P°_k`, and the division has to be
justified rather than performed — degreewise, one group of terms at a time.

The second, `Z^{(k)}_d`, counts the total degree in the *merged alphabet* `y_k, x₁, x₂, …`, the
last auxiliary variable together with all the letters. It exists because the operators the lowering
step applies interchange `y_k` with `x₁`, and such an interchange is not an automorphism of `P°_k`
— it carries `∑_{a ≥ 0} y_k x₁^a`, whose coefficients are polynomial in `y_k`, to a series whose
coefficient at `x₁` is `∑_{a ≥ 0} y_k^a`. What it does preserve is the degree in the merged
alphabet, so the graded pieces of that alphabet are where these operators live.

## Main definitions

* `HJO.Sym.pGraded`: the piece `P^gr_{k,d}`, as a `𝕂(y₁, …, y_k)`-submodule of `P°_k`.
* `HJO.Sym.pGradedAll`: the graded part `P^gr_k = ⨆_d P^gr_{k,d}`.
* `HJO.Sym.auxFracCastSucc`: the inclusion `𝕂(y₁, …, y_k) → 𝕂(y₁, …, y_{k+1})` of coefficient
  fields, which is what "the coefficients lie in `𝕂(y₁, …, y_{k-1})`" means one level up.
* `HJO.Sym.zGraded`: the piece `Z^{(k+1)}_d`, as a subset of `P°_{k+1}`.

## Main results

* `HJO.Sym.mem_pGraded_iff`, `HJO.Sym.coeff_eq_zero_of_mem_pGraded`: membership in `P^gr_{k,d}` is
  the vanishing of every coefficient off total degree `d`.
* `HJO.Sym.pGraded_mul_pGraded_le`, `HJO.Sym.one_mem_pGraded`: the free-variable degree is
  multiplicative, and `1` is homogeneous of degree `0`.
* `HJO.Sym.iSupIndep_pGraded`: the pieces `P^gr_{k,d}` are independent, so the supremum
  `HJO.Sym.pGradedAll` is their direct sum.
* `HJO.Sym.coeff_eq_zero_of_mem_zGraded`: a series in `Z^{(k+1)}_d` has no monomial whose
  free-variable degree exceeds `d` — the clause that makes the definition non-vacuous in the right
  direction.
* `HJO.Sym.zero_mem_zGraded`, `HJO.Sym.add_mem_zGraded`, `HJO.Sym.neg_mem_zGraded`,
  `HJO.Sym.smul_mem_zGraded`: `Z^{(k+1)}_d` is closed under formal `𝕂(y₁, …, y_k)`-linear
  combinations.
* `HJO.Sym.monomial_mem_zGraded`: the monomials of degree `d` in the merged alphabet do lie in it.

## Implementation notes

*The total degree of a letter-monomial is `Finsupp.degree`.* An exponent vector is an
`α : ℕ →₀ ℕ` and its total degree is `∑ i ∈ α.support, α i`. Three spellings of that sum are in
play. `Finsupp.degree` is Mathlib's, and it is the one Mathlib's own graded machinery for power
series is stated with, so it is the one used here; this library already reads the total degree
that way in `HJO.Shuffle.TotalGrading` and `HJO.AmbientCombinatorics`.
`HJO.Sym.degHom` of `HJO.Classical.IotaPmonomial` is the same function, packaged as an
`AddMonoidHom` exactly as `Finsupp.degree` is, and no bridge is stated here because stating one
would make the `CarlssonMellit` tree depend on the `Classical` tree for a definitional identity.
`HJO.Sym.degOfExp` of `HJO.Classical.RealisationInjective` is *not* this function: it is the
weight `∑_i (i+1)α_i`, which is the degree of the *power-sum symmetric function* that an exponent
vector names through `HJO.Sym.partitionOfExp`, not the degree of a letter-monomial; using it here
would grade by the wrong number.

*The graded pieces are not rolled by hand.* `MvPowerSeries.IsHomogeneous G d` — Mathlib's
`∀ α, coeff α G ≠ 0 → degree α = d` — is exactly the condition that every monomial has total degree
`d` in `x₁, x₂, …`, together with the additivity and multiplicativity proofs
(`MvPowerSeries.IsHomogeneous.add`, `.mul`) and the projections
(`MvPowerSeries.homogeneousComponent`) that the independence of the pieces is read off. So `pGraded`
only supplies the `Submodule` packaging: `P°_k` is an algebra over its own coefficient ring
`HJO.Sym.AuxFrac K k = 𝕂(y₁, …, y_k)`, which is the base for this grading, so no new structure is
needed and the scalar closure is one line.

*An element of `P^gr_{k,d}` is not a polynomial in finitely many letters*, and the definition is
accordingly a condition on the coefficient support of a power series and not a polynomial subring:
`ι_k(p_d) = ∑_{i ≥ 1} x_i^d` must lie in `P^gr_{k,d}` and is supported on infinitely many
monomials.

*Directness is proved, not asserted.* `iSupIndep_pGraded` says the family `(P^gr_{k,d})_d` is
independent, which is what the notation `⨁_{d ≥ 0}` claims about the supremum `pGradedAll` defining
`P^gr_k`; the proof is that `MvPowerSeries.homogeneousComponent d` kills every piece but the `d`-th
and fixes that one. `DirectSum.IsInternal` is not stated: it asks for the supremum to be everything,
which is false in `P°_k` — `P^gr_k` is a proper submodule, the series `1 + x₁` lying outside it —
and inside `P^gr_k` it is the same content as the independence above, reached through
`DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top` after a `Submodule.comap` along the
inclusion.

*The level of the merged alphabet is written `k + 1`.* The piece `Z^{(k)}_d` is defined for
`k ≥ 1` and its coefficients lie in `𝕂(y₁, …, y_{k-1})`; with auxiliary variables indexed by
`Fin k` from `0` as everywhere in this layer, that field at level `k + 1` is
`HJO.Sym.AuxFrac K k` and the distinguished letter `y_k` of the merged alphabet is
`HJO.Sym.yFrac K (Fin.last k)`. So `zGraded K k d` is `Z^{(k+1)}_d`, and no
truncated subtraction appears on the level.

*Nor on the exponent.* Writing the coefficient of `x^α` as `c_α y_k^{d - |α|}` would be a
`ℕ`-subtraction that would silently clip to `0` when `|α| > d` and so would make the condition
hold vacuously on the monomials it is meant to exclude. The condition here is phrased with a
witness: `b + |α| = d`, where `b` is the exponent of `y_k`. That equation has no solution when
`|α| > d`, so the first clause of `zGraded` says nothing there, and the *second* clause is what
excludes those monomials, by demanding the coefficient vanish; `coeff_eq_zero_of_mem_zGraded` is
that clause, and `monomial_mem_zGraded` shows the two clauses together are satisfiable.

*`Z^{(k+1)}_d` is defined as a `Set`, with its closure properties as lemmas, and not as a
`Submodule`.* Making it a `Submodule` over `𝕂(y₁, …, y_k)` would need a
`Module (AuxFrac K k) (AuxAlphabetSeriesFrac K (k+1))` instance, hence a global `Algebra` instance
between two fraction fields of polynomial rings in a different number of variables, for the sole
benefit of the `SetLike` notation; what is *gained* by the lighter shape is that no such instance is
introduced, and what is *given up* is `Submodule`'s automatic API — `Submodule.mul_le`,
`Submodule.sum_mem`, `⨆` — so the four closure lemmas are proved by hand instead. The ring map
itself is needed either way, to say what "the coefficients lie in `𝕂(y₁, …, y_{k-1})`" means, and is
`auxFracCastSucc`. The consumers agree with this choice: the statement of
`HJO.Dyck.auxToFrac_unnormalisedCharPart_mem_zGraded` pins membership in `⨁_{d=0}^N Z^{(k)}_d` as a
coefficient condition, since what is named there is a subset and not a map, and
`HJO.Sym.zPerm_image_zGraded_subset` and the swapping operator `HJO.Sym.IsZDelta` need `Z^{(k)}_d`
only as a set the operators carry into itself.

*`auxFracCastSucc` needs `[IsDomain K]`, and the grading by the free variables does not.* The map is
the renaming `MvPolynomial.rename Fin.castSucc` pushed through the fraction rings by
`IsFractionRing.map`, which asks the target polynomial ring to be a domain so that the injective
renaming carries non-zerodivisors to non-zerodivisors. The base `𝕂 = ℚ(q, u)` of interest is a
field, so the hypothesis holds in the only case the layer instantiates; it is carried by the
`Z`-grading and by nothing above it, exactly as `HJO.CarlssonMellit.PowerRing` prescribes. `pGraded`
carries no such hypothesis.

*What this file deliberately does not prove.* `Z^{(k)}_dZ^{(k)}_e ⊆ Z^{(k)}_{d+e}`
(`HJO.Sym.zGraded_mul_zGraded_subset`, whose finite-sum-over-factorisations step is
`HJO.Sym.finite_setOf_add_eq` of `HJO.CarlssonMellit.ZMonomialFactorisations`), the directness of
the alphabet grading (`HJO.Sym.eq_zero_of_sum_eq_zero_of_mem_zGraded`), the ring `Z^{(k)}` itself
(`HJO.Sym.zRing`) and the uniqueness statements that rest on
`HJO.Sym.isDomain_auxAlphabetSeriesFrac` of `HJO.CarlssonMellit.PowerRingDomain` are separate
results and are not proved here. The relation between the two gradings — an element of `Z^{(k)}_d`
is the sum of its parts of free-variable degree `e ≤ d`, so `Z^{(k)}_d ⊆ P^gr_k` — is not stated
here either.

## References

E. Carlsson and A. Mellit, *A proof of the shuffle conjecture*, J. Amer. Math. Soc. **31** (2018)
661--697, Section 4. Both gradings belong to this formalisation rather than to the paper: the
paper's divided differences act on series over a field of rational functions, and this
formalisation replaces that by the graded pieces on which the operators are defined.
-/

@[expose] public section

namespace HJO.Sym

variable {K : Type*} [CommRing K]

/-! ### The grading by the free variables -/

/-- **The graded part of the series ring**: for `k ≥ 0` and `d ≥ 0`, the `𝕂(y₁, …, y_k)`-submodule
`P^gr_{k,d}` of `P°_k` consisting of those series every monomial of which has total degree `d` in
the free variables `x₁, x₂, …`. The condition is on the coefficient support, through Mathlib's
`MvPowerSeries.IsHomogeneous`, and not a polynomial subring: an element is not in general a
polynomial in finitely many letters, since `ι_k(p_d) = ∑_{i ≥ 1}x_i^d` must lie in `P^gr_{k,d}` and
is supported on infinitely many monomials. The base `HJO.Sym.AuxFrac K k` is the field
`𝕂(y₁, …, y_k)`, the coefficient ring of `P°_k` itself, so the submodule needs no new structure. -/
@[hjo "def_cm_pring_graded"]
def pGraded (K : Type*) [CommRing K] (k d : ℕ) :
    Submodule (AuxFrac K k) (AuxAlphabetSeriesFrac K k) where
  carrier := {G | MvPowerSeries.IsHomogeneous G d}
  zero_mem' := by
    intro α hα
    exact absurd (MvPowerSeries.coeff_zero α) hα
  add_mem' hG hH := MvPowerSeries.IsHomogeneous.add hG hH
  smul_mem' c G hG := by
    intro α hα
    rw [MvPowerSeries.coeff_smul] at hα
    exact hG (right_ne_zero_of_mul hα)

/-- Membership in `P^gr_{k,d}`, unfolded: every coefficient at a letter-monomial of total degree
other than `d` vanishes. This is the condition that every monomial has total degree `d`. -/
theorem mem_pGraded_iff {k d : ℕ} {G : AuxAlphabetSeriesFrac K k} :
    G ∈ pGraded K k d ↔
      ∀ α : ℕ →₀ ℕ, MvPowerSeries.coeff α G ≠ 0 → Finsupp.degree α = d := by
  have hw : ∀ α : ℕ →₀ ℕ, Finsupp.weight (1 : ℕ → ℕ) α = Finsupp.degree α := by
    have h : (Finsupp.weight (1 : ℕ → ℕ) : (ℕ →₀ ℕ) →+ ℕ) = Finsupp.degree :=
      Finsupp.degree_eq_weight_one.symm
    exact fun α => by rw [h]
  refine ⟨fun hG α hα => ?_, fun hG α hα => ?_⟩
  · rw [← hw α]
    exact hG hα
  · rw [hw α]
    exact hG α hα

/-- The contrapositive form of `HJO.Sym.mem_pGraded_iff`, which is how a consumer reads a graded
series: off total degree `d` the coefficient is `0`. -/
theorem coeff_eq_zero_of_mem_pGraded {k d : ℕ} {G : AuxAlphabetSeriesFrac K k}
    (hG : G ∈ pGraded K k d) {α : ℕ →₀ ℕ} (hα : Finsupp.degree α ≠ d) :
    MvPowerSeries.coeff α G = 0 :=
  MvPowerSeries.IsHomogeneous.coeff_eq_zero hG hα

/-- **The free-variable degree is multiplicative**: `P^gr_{k,d}P^gr_{k,d'} ⊆ P^gr_{k,d+d'}`. The
coefficient of a letter-monomial in a product is a finite sum over its factorisations, and a pair
contributes only when the degrees of the factors are `d` and `d'`. -/
theorem pGraded_mul_pGraded_le (K : Type*) [CommRing K] (k d d' : ℕ) :
    pGraded K k d * pGraded K k d' ≤ pGraded K k (d + d') := by
  rw [Submodule.mul_le]
  exact fun G hG H hH => MvPowerSeries.IsHomogeneous.mul hG hH

/-- The unit series is homogeneous of degree `0`: its only nonzero coefficient sits at the empty
letter-monomial. Together with `HJO.Sym.pGraded_mul_pGraded_le` this is what makes `P^gr_k` a
subring of `P°_k`. -/
theorem one_mem_pGraded (K : Type*) [CommRing K] (k : ℕ) :
    (1 : AuxAlphabetSeriesFrac K k) ∈ pGraded K k 0 := by
  refine mem_pGraded_iff.2 fun α hα => ?_
  rcases eq_or_ne α 0 with rfl | h
  · exact map_zero Finsupp.degree
  · exact absurd (MvPowerSeries.coeff_monomial_ne h 1) hα

/-- **The graded part of the series ring**, assembled: `P^gr_k = ⨁_{d ≥ 0}P^gr_{k,d}`, realised as
the supremum of the graded pieces inside `P°_k`. The supremum is the direct sum because the family
is independent, which is `HJO.Sym.iSupIndep_pGraded`. -/
@[hjo "def_cm_pring_graded"]
noncomputable def pGradedAll (K : Type*) [CommRing K] (k : ℕ) :
    Submodule (AuxFrac K k) (AuxAlphabetSeriesFrac K k) :=
  ⨆ d, pGraded K k d

/-- The graded pieces span `P^gr_k` by definition. -/
theorem pGraded_le_pGradedAll (K : Type*) [CommRing K] (k d : ℕ) :
    pGraded K k d ≤ pGradedAll K k :=
  le_iSup (fun d => pGraded K k d) d

/-- **The grading is direct**: the family `(P^gr_{k,d})_{d ≥ 0}` is independent, so the supremum
`HJO.Sym.pGradedAll` defining `P^gr_k` really is the direct sum `⨁_{d ≥ 0}P^gr_{k,d}`. The
projection `MvPowerSeries.homogeneousComponent d` annihilates every piece but the `d`-th and fixes
the `d`-th, so a series lying in the `d`-th piece and in the supremum of the others is its own
`d`-th component and that component is `0`. -/
theorem iSupIndep_pGraded (K : Type*) [CommRing K] (k : ℕ) :
    iSupIndep (pGraded K k) := by
  rw [iSupIndep_def]
  intro d
  refine Submodule.disjoint_def.2 fun G hG hG' => ?_
  have hle : (⨆ (j) (_ : j ≠ d), pGraded K k j) ≤
      LinearMap.ker (MvPowerSeries.homogeneousComponent (σ := ℕ) (R := AuxFrac K k) d) := by
    refine iSup_le fun j => iSup_le fun hj H hH => LinearMap.mem_ker.2 (MvPowerSeries.ext ?_)
    intro α
    rw [MvPowerSeries.coeff_homogeneousComponent, MvPowerSeries.coeff_zero]
    rcases eq_or_ne (Finsupp.degree α) d with hα | hα
    · rw [ite_eq_left hα]
      exact coeff_eq_zero_of_mem_pGraded hH (hα.trans_ne (Ne.symm hj))
    · exact ite_eq_right hα
  have hker : MvPowerSeries.homogeneousComponent d G = 0 := LinearMap.mem_ker.1 (hle hG')
  rw [MvPowerSeries.isHomogeneous_iff_eq_homogeneousComponent.1 hG, hker]

/-! ### The inclusion of the lower coefficient field -/

/-- The inclusion `𝕂(y₁, …, y_k) → 𝕂(y₁, …, y_{k+1})` of coefficient fields: the renaming
`MvPolynomial.rename Fin.castSucc`, which keeps the first `k` auxiliary variables and introduces
`y_{k+1}`, pushed through the fraction rings. This is what "the coefficients `c_α`
lie in `𝕂(y₁, …, y_{k-1})`" means at the level `k + 1`. The renaming is injective, and the
hypothesis `[IsDomain K]` is what makes the target polynomial ring a domain, so that injectivity
carries non-zerodivisors to non-zerodivisors and `IsFractionRing.map` applies. -/
noncomputable def auxFracCastSucc (K : Type*) [CommRing K] [IsDomain K] (k : ℕ) :
    AuxFrac K k →+* AuxFrac K (k + 1) :=
  IsLocalization.map (M := nonZeroDivisors (MvPolynomial (Fin k) K)) (AuxFrac K (k + 1))
    (MvPolynomial.rename Fin.castSucc).toRingHom
    (nonZeroDivisors_le_comap_nonZeroDivisors_of_injective _
      (MvPolynomial.rename_injective _ (Fin.castSucc_injective k)))

/-- The inclusion of coefficient fields on an honest polynomial: it renames along `Fin.castSucc`. -/
@[simp]
theorem auxFracCastSucc_algebraMap [IsDomain K] {k : ℕ} (p : MvPolynomial (Fin k) K) :
    auxFracCastSucc K k (algebraMap (MvPolynomial (Fin k) K) (AuxFrac K k) p) =
      algebraMap (MvPolynomial (Fin (k + 1)) K) (AuxFrac K (k + 1))
        (MvPolynomial.rename Fin.castSucc p) :=
  IsLocalization.map_eq _ p

/-- The inclusion of coefficient fields sends the auxiliary variable `y_{l+1}` to the auxiliary
variable of the same index one level up: it is the containment
`𝕂(y₁, …, y_k) ⊆ 𝕂(y₁, …, y_{k+1})` and not some other map. -/
@[simp]
theorem auxFracCastSucc_yFrac [IsDomain K] {k : ℕ} (l : Fin k) :
    auxFracCastSucc K k (yFrac K l) = yFrac K l.castSucc := by
  rw [yFrac, auxFracCastSucc_algebraMap, MvPolynomial.rename_X, yFrac]

/-- The inclusion of coefficient fields is injective, so the coefficients of a series in
`Z^{(k+1)}_d` genuinely form a copy of `𝕂(y₁, …, y_k)`: a ring homomorphism out of a field into a
nontrivial ring with no zero divisors is injective. -/
theorem auxFracCastSucc_injective (K : Type*) [CommRing K] [IsDomain K] (k : ℕ) :
    Function.Injective (auxFracCastSucc K k) :=
  (injective_iff_map_eq_zero _).2 fun _ h => (map_eq_zero _).1 h

/-! ### The grading by the merged alphabet -/

/-- **The alphabet-graded part of the series ring**: for `d ≥ 0`, the set `Z^{(k+1)}_d` of those
series in `P°_{k+1}` that are formal `𝕂(y₁, …, y_k)`-linear combinations of the monomials of total
degree `d` in the merged alphabet `y_{k+1}, x₁, x₂, …`. Concretely, the coefficient at a
letter-monomial `x^α` is `c_α y_{k+1}^b` with `c_α` in the lower coefficient field and
`b + |α| = d`, and it vanishes when no such `b` exists, that is when `|α| > d`.

The level `k ≥ 1` of `Z^{(k)}_d` is `k + 1` here, so its `𝕂(y₁, …, y_{k-1})` is
`HJO.Sym.AuxFrac K k` included by `HJO.Sym.auxFracCastSucc` and its `y_k` is
`HJO.Sym.yFrac K (Fin.last k)`, with no subtraction on the level. The exponent of `y_{k+1}` is a
witness `b` to `b + |α| = d` rather than the difference `d - |α|`, for the same reason: a
`ℕ`-subtraction clips to `0` when `|α| > d` and would make the condition hold on exactly the
monomials it must exclude. The second clause is what excludes them. -/
@[hjo "def_cm_zgraded"]
def zGraded (K : Type*) [CommRing K] [IsDomain K] (k d : ℕ) :
    Set (AuxAlphabetSeriesFrac K (k + 1)) :=
  {G | (∀ (α : ℕ →₀ ℕ) (b : ℕ), b + Finsupp.degree α = d →
          ∃ c : AuxFrac K k, MvPowerSeries.coeff α G
            = auxFracCastSucc K k c * yFrac K (Fin.last k) ^ b) ∧
        ∀ α : ℕ →₀ ℕ, d < Finsupp.degree α → MvPowerSeries.coeff α G = 0}

variable [IsDomain K] {k d : ℕ} {G H : AuxAlphabetSeriesFrac K (k + 1)}

/-- Membership in `Z^{(k+1)}_d`, unfolded into its two clauses: below the degree the coefficient is
`c_α y_{k+1}^b` for the `b` with `b + |α| = d`, and above it the coefficient vanishes. -/
theorem mem_zGraded_iff :
    G ∈ zGraded K k d ↔
      (∀ (α : ℕ →₀ ℕ) (b : ℕ), b + Finsupp.degree α = d →
          ∃ c : AuxFrac K k, MvPowerSeries.coeff α G
            = auxFracCastSucc K k c * yFrac K (Fin.last k) ^ b) ∧
        ∀ α : ℕ →₀ ℕ, d < Finsupp.degree α → MvPowerSeries.coeff α G = 0 :=
  Iff.rfl

/-- The coefficients of a series in `Z^{(k+1)}_d` at the letter-monomials `x^α` with
`|α| > d`: the definition lets `α` run over the multi-indices with `|α| ≤ d`, and
this is the assertion that nothing lies outside that range. It is the clause the witness
formulation `b + |α| = d` makes necessary — with the exponent of `y_{k+1}^{d-|α|}` read as a
`ℕ`-subtraction the region `|α| > d` would be unconstrained. -/
theorem coeff_eq_zero_of_mem_zGraded (hG : G ∈ zGraded K k d) {α : ℕ →₀ ℕ}
    (hα : d < Finsupp.degree α) : MvPowerSeries.coeff α G = 0 :=
  hG.2 α hα

/-- The coefficient of a series in `Z^{(k+1)}_d` at a reachable letter-monomial: it is a multiple of
`y_{k+1}^b` by a scalar of the lower coefficient field, for the `b` with `b + |α| = d`. -/
theorem exists_coeff_eq_of_mem_zGraded (hG : G ∈ zGraded K k d) (α : ℕ →₀ ℕ) {b : ℕ}
    (hb : b + Finsupp.degree α = d) :
    ∃ c : AuxFrac K k, MvPowerSeries.coeff α G
      = auxFracCastSucc K k c * yFrac K (Fin.last k) ^ b :=
  hG.1 α b hb

/-- `Z^{(k+1)}_d` contains `0`: take every coefficient scalar to be `0`. -/
theorem zero_mem_zGraded : (0 : AuxAlphabetSeriesFrac K (k + 1)) ∈ zGraded K k d :=
  ⟨fun α _ _ => ⟨0, by rw [MvPowerSeries.coeff_zero, map_zero, zero_mul]⟩,
    fun α _ => MvPowerSeries.coeff_zero α⟩

/-- `Z^{(k+1)}_d` is closed under addition: the coefficient scalars add. -/
theorem add_mem_zGraded (hG : G ∈ zGraded K k d) (hH : H ∈ zGraded K k d) :
    G + H ∈ zGraded K k d := by
  refine ⟨fun α b hb => ?_, fun α hα => ?_⟩
  · obtain ⟨c, hc⟩ := hG.1 α b hb
    obtain ⟨c', hc'⟩ := hH.1 α b hb
    exact ⟨c + c', by rw [map_add, hc, hc', map_add, add_mul]⟩
  · rw [map_add, hG.2 α hα, hH.2 α hα, add_zero]

/-- `Z^{(k+1)}_d` is closed under negation: the coefficient scalars negate. -/
theorem neg_mem_zGraded (hG : G ∈ zGraded K k d) : -G ∈ zGraded K k d := by
  refine ⟨fun α b hb => ?_, fun α hα => ?_⟩
  · obtain ⟨c, hc⟩ := hG.1 α b hb
    exact ⟨-c, by rw [map_neg, hc, map_neg, neg_mul]⟩
  · rw [map_neg, hG.2 α hα, neg_zero]

/-- `Z^{(k+1)}_d` is closed under the scalars of `𝕂(y₁, …, y_k)`, which act on `P°_{k+1}` through
`HJO.Sym.auxFracCastSucc`: this together with `HJO.Sym.zero_mem_zGraded` and
`HJO.Sym.add_mem_zGraded` is what closure under formal `𝕂(y₁, …, y_{k-1})`-linear
combinations asks of the set. -/
theorem smul_mem_zGraded (a : AuxFrac K k) (hG : G ∈ zGraded K k d) :
    auxFracCastSucc K k a • G ∈ zGraded K k d := by
  refine ⟨fun α b hb => ?_, fun α hα => ?_⟩
  · obtain ⟨c, hc⟩ := hG.1 α b hb
    exact ⟨a * c, by rw [MvPowerSeries.coeff_smul, hc, map_mul, mul_assoc]⟩
  · rw [MvPowerSeries.coeff_smul, hG.2 α hα, mul_zero]

/-- **The monomials of the merged alphabet lie in the graded pieces**: for `b + |α| = d` the series
`c y_{k+1}^b x^α` is in `Z^{(k+1)}_d`. So the definition is not vacuous, and the two clauses of
`HJO.Sym.zGraded` are jointly satisfiable — the second one excludes the monomials with `|α| > d`
without excluding the ones with `|α| ≤ d`. -/
theorem monomial_mem_zGraded {b : ℕ} {α : ℕ →₀ ℕ} (hb : b + Finsupp.degree α = d)
    (c : AuxFrac K k) :
    MvPowerSeries.monomial α (auxFracCastSucc K k c * yFrac K (Fin.last k) ^ b)
      ∈ zGraded K k d := by
  refine ⟨fun α' b' hb' => ?_, fun α' hα' => ?_⟩
  · rcases eq_or_ne α' α with rfl | hne
    · have : b' = b := Nat.add_right_cancel (hb'.trans hb.symm)
      subst this
      exact ⟨c, MvPowerSeries.coeff_monomial_same _ _⟩
    · exact ⟨0, by rw [MvPowerSeries.coeff_monomial_ne hne, map_zero, zero_mul]⟩
  · refine MvPowerSeries.coeff_monomial_ne (fun hαα => ?_) _
    rw [hαα] at hα'
    omega

end HJO.Sym
