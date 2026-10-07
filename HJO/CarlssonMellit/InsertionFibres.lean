/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.CarlssonMellit.InsertInjectiveBounded
public import HJO.CarlssonMellit.InsertNotInjective
public meta import HJO.Attr

/-! # The exact fibres of the insertion

One would expect the insertion `Φ_k : P_k → P_{k+1}`, the substitution
`x₁ ↦ y_{k+1}`, `x_r ↦ x_{r-1}`, to be injective. It is not, and the failure is not an artefact of a
choice made in formalizing: the coefficients of `P_{k+1}` are *polynomials* in `y₁, …, y_{k+1}`,
so the substitution has no value at a series whose `x₁`-degree is unbounded at some letter-monomial,
and `HJO.Sym.insertFront` extends it by `0` there. This file measures exactly how much that
extension forgets.

The answer is that it forgets exactly the unbounded part, and nothing else. Write `F♭` for the
series obtained from `F` by deleting its coefficients at every letter-monomial where the `x₁`-degree
is unbounded (`HJO.Sym.boundedPart`). Then `F♭` has bounded `x₁`-degree, `Φ_k(F♭) = Φ_k(F)`, and

  `Φ_k(F) = Φ_k(G) ↔ F♭ = G♭`,

so the fibres of `Φ_k` are precisely the classes of the relation "same bounded part". Two
consequences bracket the injectivity statement. `Φ_k` is injective on the bounded series, which is
`HJO.Sym.injOn_insertFront` and is what is used downstream; and `Φ_k` is injective on all of `P_k`
if and only if every series of `P_k` has bounded `x₁`-degree, which is false whenever the base ring
is nontrivial. So the hypothesis of `HJO.Sym.injOn_insertFront` is not a convenience that a
better proof could remove — it is equivalent to the conclusion it is used to draw.

## Main definitions

* `HJO.Sym.BoundedFrontDegreeAt`: `HJO.Sym.BoundedFrontDegree` localized at one letter-monomial `e`
  — the coefficients of `F` at `x₁^a e` vanish for all large `a`. This is the condition under which
  the defining sum of `Φ_k` at `e` is finite, hence under which `Φ_k` takes its intended value
  at `e` rather than its extension's value `0`.
* `HJO.Sym.boundedPart`: the bounded part `F♭` of `F`, agreeing with `F` at every letter-monomial
  whose `x₁`-degree is bounded and vanishing at the rest. It is the canonical representative of the
  fibre of `Φ_k` through `F`.

## Main results

* `HJO.Sym.insertFront_eq_insertFront_iff`: the fibres — `Φ_k(F) = Φ_k(G)` if and only if
  `F♭ = G♭`. With `HJO.Sym.insertFront_boundedPart` and
  `HJO.Sym.boundedFrontDegree_boundedPart` this exhibits `F♭` as the unique bounded point of its
  fibre (`HJO.Sym.existsUnique_boundedFrontDegree_insertFront_eq`), so `Φ_k` restricted to the
  bounded series has the same image as `Φ_k` on all of `P_k`.
* `HJO.Sym.injective_insertFront_iff`: `Φ_k` is injective exactly when every series of `P_k` has
  bounded `x₁`-degree. Unboundedness is therefore the only obstruction, and over a nontrivial base
  the obstruction is present: `HJO.Sym.not_boundedFrontDegree_firstLetterGeometric` exhibits
  `∑_{a ≥ 0} x₁^a` as a series of unbounded `x₁`-degree, whence
  `HJO.Sym.not_forall_boundedFrontDegree`, which with the equivalence recovers
  `HJO.Sym.not_injective_insertFront`.
* `HJO.Sym.boundedPart_eq_self_iff`: `F♭ = F` if and only if `F` has bounded `x₁`-degree, so the
  bounded series are exactly the fixed points of `F ↦ F♭`.

## Implementation notes

*Why a canonical representative rather than a kernel.* For a linear map, injectivity is triviality
of the kernel, and one would expect the failure to be measured by a subgroup. `HJO.Sym.insertFront`
is not additive: at a letter-monomial where `F` and `G` both have unbounded `x₁`-degree but `F + G`
does not, the extension gives `Φ_k(F) = Φ_k(G) = 0` while `Φ_k(F + G)` may be nonzero there. So the
fibres are not cosets, and the right invariant is the pointwise truncation `F ↦ F♭`, which is
idempotent but not additive. The characterization `Φ_k(F) = Φ_k(G) ↔ F♭ = G♭` is therefore
strictly stronger than any statement about a kernel, and it is what pins the injectivity domain
down exactly.

*The truncation is taken letter-monomial by letter-monomial.* Boundedness of the `x₁`-degree is a
condition on one *ray* `{x₁^a e | a ≥ 0}` at a time, and `Φ_k`'s defining sum at `e` ranges over
exactly that ray. So `F♭` is defined by deciding, at each letter-monomial `β`, whether the ray
through `β` — that is, the ray of `HJO.Sym.dropFirst β` — is bounded, and keeping `β`'s coefficient
precisely when it is. This is what makes `Φ_k(F♭) = Φ_k(F)` a statement checked one ray at a time:
on a bounded ray the two series agree, and on an unbounded ray `F♭` contributes an empty sum while
`F` contributes one of infinite support, both of which the extension evaluates to `0`.

*Over `ℕ` a bound and a finite support are the same condition*, which is why the unbounded case
gives an infinite support and hence the extension's value. `HJO.Sym.BoundedFrontDegreeAt` is stated
as a bound; `HJO.Sym.boundedFrontDegreeAt_iff_finite_support` is the
equivalence, and with `HJO.Sym.support_X_last_pow_mul_rename_coeff` — the defining family and the
coefficients have one support — it turns the negation into the `finsum` hypothesis.

*No hypothesis on the base beyond `CommRing`.* Every statement about `F♭` and the fibres is an
identity or an equivalence between coefficients. Nontriviality of `K` enters only where a witness of
unbounded degree is produced, and so only in reading `HJO.Sym.injective_insertFront_iff` as a
refutation rather than as a criterion.

## References

The lemma `HJO.Sym.injOn_insertFront`, with `HJO.Sym.AuxAlphabetSeries` and `HJO.Sym.insertFront`.
E. Carlsson and A. Mellit, *A proof of the shuffle conjecture*, J. Amer. Math. Soc. **31** (2018)
661--697, Section 4, where the substitution is read as an identification of rings of rational
functions, for which the question of its domain does not arise.
-/

@[expose] public section

namespace HJO.Sym

variable {K : Type*} [CommRing K] {k : ℕ}

/-! ### A term of the defining sum vanishes only with its coefficient -/

/-- A summand `y_{k+1}^a ρ(p)` of the defining sum of `Φ_k`, with
`ρ = MvPolynomial.rename Fin.castSucc`, vanishes exactly when `p` does. So the support of the
defining family is the set of `a` at which the coefficient of `F` is nonzero, and no cancellation
between the powers of `y_{k+1}` can shorten it. Both factors are harmless separately and for the
same reason in each case — a monomial with unit coefficient and an injection of the variables —
which is `MvPolynomial.isRegular_X_pow` and `MvPolynomial.rename_injective`; no hypothesis on `K` is
needed, in particular no absence of zero divisors. -/
theorem X_last_pow_mul_rename_eq_zero_iff (a : ℕ) (p : MvPolynomial (Fin k) K) :
    MvPolynomial.X (Fin.last k) ^ a * MvPolynomial.rename Fin.castSucc p = 0 ↔ p = 0 := by
  rw [(MvPolynomial.isRegular_X_pow a).left.mul_left_eq_zero_iff,
    map_eq_zero_iff _ (MvPolynomial.rename_injective _ (Fin.castSucc_injective k))]

/-! ### Bounded degree at a single letter-monomial -/

/-- **The `x₁`-degree is bounded at the letter-monomial `e`**: the coefficients of `F` at `x₁^a e`
vanish for all `a` above a bound. This is `HJO.Sym.BoundedFrontDegree` localized at `e`, and it is
the condition under which the defining sum of `HJO.Sym.insertFront` at `e` is finite, hence under
which `Φ_k` takes at `e` the value of that sum instead of the extension's `0`. -/
def BoundedFrontDegreeAt (F : AuxAlphabetSeries K k) (e : ℕ →₀ ℕ) : Prop :=
  ∃ N : ℕ, ∀ a : ℕ, N < a → MvPowerSeries.coeff (Finsupp.single 0 a + e.mapDomain Nat.succ) F = 0

theorem boundedFrontDegree_iff_forall_boundedFrontDegreeAt {F : AuxAlphabetSeries K k} :
    BoundedFrontDegree F ↔ ∀ e : ℕ →₀ ℕ, BoundedFrontDegreeAt F e :=
  Iff.rfl

/-- On a bounded ray the defining sum of `Φ_k` is a finite sum, which is
`HJO.Sym.coeff_insertFront_eq_sum` read through `HJO.Sym.BoundedFrontDegreeAt`. -/
theorem coeff_insertFront_eq_sum_of_boundedFrontDegreeAt {F : AuxAlphabetSeries K k} {e : ℕ →₀ ℕ}
    (he : BoundedFrontDegreeAt F e) :
    ∃ N : ℕ, MvPowerSeries.coeff e (insertFront K k F)
      = ∑ a ∈ Finset.range (N + 1), MvPolynomial.X (Fin.last k) ^ a *
          MvPolynomial.rename Fin.castSucc
            (MvPowerSeries.coeff (Finsupp.single 0 a + e.mapDomain Nat.succ) F) :=
  ⟨he.choose, coeff_insertFront_eq_sum he.choose_spec⟩

/-- **Over `ℕ` a bound and a finite support are the same condition**: the `x₁`-degree is bounded at
`e` exactly when only finitely many powers of `x₁` occur at `e`. The bound is the word
for the condition and is what `HJO.Sym.coeff_insertFront_eq_sum` consumes; finiteness of the support
is what the `finsum` defining `HJO.Sym.insertFront` asks for. -/
theorem boundedFrontDegreeAt_iff_finite_support {F : AuxAlphabetSeries K k} {e : ℕ →₀ ℕ} :
    BoundedFrontDegreeAt F e ↔ (Function.support fun a : ℕ =>
      MvPowerSeries.coeff (Finsupp.single 0 a + e.mapDomain Nat.succ) F).Finite := by
  refine ⟨fun ⟨N, hN⟩ => (Set.finite_Iic N).subset fun a ha =>
      Set.mem_Iic.2 (not_lt.1 fun h => ha (hN a h)), fun h => ?_⟩
  obtain ⟨N, hN⟩ := h.bddAbove
  exact ⟨N, fun a ha => by by_contra hc; exact absurd (hN (Function.mem_support.2 hc)) (by omega)⟩

/-- The defining family of `Φ_k` at `e` has the same support as the coefficients of `F` along the
ray of `e`: no cancellation between the powers of `y_{k+1}` can shorten it, by
`HJO.Sym.X_last_pow_mul_rename_eq_zero_iff`. -/
theorem support_X_last_pow_mul_rename_coeff (F : AuxAlphabetSeries K k) (e : ℕ →₀ ℕ) :
    (Function.support fun a : ℕ => MvPolynomial.X (Fin.last k) ^ a *
        MvPolynomial.rename Fin.castSucc
          (MvPowerSeries.coeff (Finsupp.single 0 a + e.mapDomain Nat.succ) F))
      = Function.support fun a : ℕ =>
          MvPowerSeries.coeff (Finsupp.single 0 a + e.mapDomain Nat.succ) F :=
  Set.ext fun a => not_congr (X_last_pow_mul_rename_eq_zero_iff a _)

/-- **An unbounded ray has infinite support**, so the defining sum of `Φ_k` there is the `finsum` of
a family of infinite support and the extension evaluates it to `0`. -/
theorem infinite_support_of_not_boundedFrontDegreeAt {F : AuxAlphabetSeries K k} {e : ℕ →₀ ℕ}
    (he : ¬ BoundedFrontDegreeAt F e) :
    (Function.support fun a : ℕ => MvPolynomial.X (Fin.last k) ^ a *
      MvPolynomial.rename Fin.castSucc
        (MvPowerSeries.coeff (Finsupp.single 0 a + e.mapDomain Nat.succ) F)).Infinite :=
  (support_X_last_pow_mul_rename_coeff F e).symm ▸
    fun h => he (boundedFrontDegreeAt_iff_finite_support.2 h)

/-- At an unbounded letter-monomial the insertion takes its extended value `0`. -/
theorem coeff_insertFront_of_not_boundedFrontDegreeAt {F : AuxAlphabetSeries K k} {e : ℕ →₀ ℕ}
    (he : ¬ BoundedFrontDegreeAt F e) : MvPowerSeries.coeff e (insertFront K k F) = 0 :=
  (coeff_insertFront k F e).trans
    (finsum_of_infinite_support (infinite_support_of_not_boundedFrontDegreeAt he))

/-! ### The bounded part -/

open scoped Classical in
/-- **The bounded part `F♭` of `F`**: the series agreeing with `F` at every letter-monomial whose
ray `{x₁^a e}` has bounded `x₁`-degree, and vanishing at the rest. Deleting the unbounded rays is
exactly what `Φ_k` does — it has no value there and `HJO.Sym.insertFront` extends it by `0` — so
`F♭` is the canonical representative of the fibre of `Φ_k` through `F`
(`HJO.Sym.insertFront_eq_insertFront_iff`), and the bounded series are the fixed points of
`F ↦ F♭` (`HJO.Sym.boundedPart_eq_self_iff`). -/
noncomputable def boundedPart (F : AuxAlphabetSeries K k) : AuxAlphabetSeries K k := fun β =>
  if BoundedFrontDegreeAt F (dropFirst β) then MvPowerSeries.coeff β F else 0

open scoped Classical in
theorem coeff_boundedPart (F : AuxAlphabetSeries K k) (β : ℕ →₀ ℕ) :
    MvPowerSeries.coeff β (boundedPart F) =
      if BoundedFrontDegreeAt F (dropFirst β) then MvPowerSeries.coeff β F else 0 :=
  rfl

/-- The ray through `x₁^a e` is the ray of `e`: dropping the first letter of `x₁^a e` gives `e`. -/
theorem dropFirst_single_add_mapDomain (a : ℕ) (e : ℕ →₀ ℕ) :
    dropFirst (Finsupp.single 0 a + e.mapDomain Nat.succ) = e :=
  Finsupp.ext fun n => by
    rw [dropFirst_apply, Finsupp.add_apply, Finsupp.single_eq_of_ne (by omega),
      Finsupp.mapDomain_apply Nat.succ_injective, zero_add]

/-- On a bounded ray the bounded part agrees with the series. -/
theorem coeff_boundedPart_of_boundedFrontDegreeAt {F : AuxAlphabetSeries K k} {e : ℕ →₀ ℕ}
    (he : BoundedFrontDegreeAt F e) (a : ℕ) :
    MvPowerSeries.coeff (Finsupp.single 0 a + e.mapDomain Nat.succ) (boundedPart F)
      = MvPowerSeries.coeff (Finsupp.single 0 a + e.mapDomain Nat.succ) F := by
  rw [coeff_boundedPart, dropFirst_single_add_mapDomain, ite_eq_left he]

/-- On an unbounded ray the bounded part vanishes. -/
theorem coeff_boundedPart_of_not_boundedFrontDegreeAt {F : AuxAlphabetSeries K k} {e : ℕ →₀ ℕ}
    (he : ¬ BoundedFrontDegreeAt F e) (a : ℕ) :
    MvPowerSeries.coeff (Finsupp.single 0 a + e.mapDomain Nat.succ) (boundedPart F) = 0 := by
  rw [coeff_boundedPart, dropFirst_single_add_mapDomain, ite_eq_right he]

/-- **The bounded part has bounded `x₁`-degree.** On a bounded ray it inherits the bound; on an
unbounded one all its coefficients vanish, so any bound will do. -/
theorem boundedFrontDegree_boundedPart (F : AuxAlphabetSeries K k) :
    BoundedFrontDegree (boundedPart F) := fun e => by
  by_cases he : BoundedFrontDegreeAt F e
  · exact ⟨he.choose, fun a ha => (coeff_boundedPart_of_boundedFrontDegreeAt he a).trans
      (he.choose_spec a ha)⟩
  · exact ⟨0, fun a _ => coeff_boundedPart_of_not_boundedFrontDegreeAt he a⟩

/-- **The insertion does not see the unbounded part**: `Φ_k(F♭) = Φ_k(F)`. On a bounded ray the two
series agree; on an unbounded one `F♭` contributes an empty sum and `F` one of infinite support, and
`HJO.Sym.insertFront` evaluates both to `0`. -/
@[simp]
theorem insertFront_boundedPart (F : AuxAlphabetSeries K k) :
    insertFront K k (boundedPart F) = insertFront K k F := by
  refine MvPowerSeries.ext fun e => ?_
  by_cases he : BoundedFrontDegreeAt F e
  · rw [coeff_insertFront, coeff_insertFront]
    exact finsum_congr fun a => by
      rw [coeff_boundedPart_of_boundedFrontDegreeAt he a]
  · rw [coeff_insertFront_of_not_boundedFrontDegreeAt he, coeff_insertFront]
    exact finsum_eq_zero_of_forall_eq_zero fun a => by
      rw [coeff_boundedPart_of_not_boundedFrontDegreeAt he a, map_zero, mul_zero]

/-- **The bounded series are the fixed points of `F ↦ F♭`.** -/
theorem boundedPart_eq_self_iff {F : AuxAlphabetSeries K k} :
    boundedPart F = F ↔ BoundedFrontDegree F := by
  refine ⟨fun h => h ▸ boundedFrontDegree_boundedPart F, fun h => MvPowerSeries.ext fun β => ?_⟩
  rw [coeff_boundedPart,
    ite_eq_left (boundedFrontDegree_iff_forall_boundedFrontDegreeAt.1 h (dropFirst β))]

@[simp]
theorem boundedPart_boundedPart (F : AuxAlphabetSeries K k) :
    boundedPart (boundedPart F) = boundedPart F :=
  boundedPart_eq_self_iff.2 (boundedFrontDegree_boundedPart F)

/-! ### The fibres -/

/-- **The exact fibres of the insertion**: `Φ_k(F) = Φ_k(G)` if and only if `F` and `G` have the
same bounded part. So `Φ_k` identifies two series exactly when they differ only on
letter-monomials whose `x₁`-degree is unbounded — where `Φ_k` has no value and
`HJO.Sym.insertFront` extends it by `0`.

This is the sharp form of `HJO.Sym.injOn_insertFront`. Unrestricted injectivity would say that the
right-hand side can be replaced by `F = G`, which fails; the bounded statement
`HJO.Sym.injOn_insertFront` is the case of bounded `F` and `G`, where `F♭ = F` and `G♭ = G`, and it
is what the forward implication is proved from. -/
theorem insertFront_eq_insertFront_iff {F G : AuxAlphabetSeries K k} :
    insertFront K k F = insertFront K k G ↔ boundedPart F = boundedPart G := by
  refine ⟨fun h => injOn_insertFront K k (boundedFrontDegree_boundedPart F)
    (boundedFrontDegree_boundedPart G) ?_, fun h => ?_⟩
  · rw [insertFront_boundedPart, insertFront_boundedPart, h]
  · rw [← insertFront_boundedPart F, ← insertFront_boundedPart G, h]

/-- **The bounded part is the unique bounded point of its fibre.** In particular `Φ_k` restricted to
the bounded series of `P_k` has the same image as `Φ_k` on all of `P_k`: nothing is lost by giving
`Φ_k` the domain on which it is defined. -/
theorem existsUnique_boundedFrontDegree_insertFront_eq (F : AuxAlphabetSeries K k) :
    ∃! G : AuxAlphabetSeries K k, BoundedFrontDegree G ∧ insertFront K k G = insertFront K k F :=
  ⟨boundedPart F, ⟨boundedFrontDegree_boundedPart F, insertFront_boundedPart F⟩,
    fun G ⟨hG, hGF⟩ => by
      rw [← boundedPart_eq_self_iff.2 hG, insertFront_eq_insertFront_iff.1 hGF]⟩

/-- **Unboundedness is the only obstruction to injectivity**: `Φ_k` is injective on `P_k` if and
only if every series of `P_k` has bounded `x₁`-degree at each letter-monomial. Unrestricted
injectivity asserts the left-hand side; over a nontrivial base the right-hand side
fails, the series `∑_{a ≥ 0} x₁^a` being unbounded, and
`HJO.Sym.not_injective_insertFront` is that refutation carried out at the witness. Conversely the
hypothesis of `HJO.Sym.injOn_insertFront` cannot be dropped by any improvement of its proof:
it is equivalent to the conclusion. -/
theorem injective_insertFront_iff :
    Function.Injective (insertFront K k) ↔ ∀ F : AuxAlphabetSeries K k, BoundedFrontDegree F :=
  ⟨fun h F => boundedPart_eq_self_iff.1 (h (insertFront_boundedPart F)),
    fun h {F G} hFG => (boundedPart_eq_self_iff.2 (h F)).symm.trans
      ((insertFront_eq_insertFront_iff.1 hFG).trans (boundedPart_eq_self_iff.2 (h G)))⟩

/-! ### The obstruction is present -/

/-- **The geometric series in the first letter has unbounded `x₁`-degree.** Its coefficient at
`x₁^a` is `1` for every `a`, so no bound holds at the empty letter-monomial. This is the series
`∑_{a ≥ 0} x₁^a` that the note on `HJO.Sym.insertFront` names, and it is a series of `P_k` —
nothing in a formal power series bounds its degrees. -/
theorem not_boundedFrontDegree_firstLetterGeometric [Nontrivial K] (k : ℕ) :
    ¬ BoundedFrontDegree (firstLetterGeometric K k) := by
  intro h
  obtain ⟨N, hN⟩ := h 0
  have h1 : MvPowerSeries.coeff
      (Finsupp.single 0 (N + 1) + (0 : ℕ →₀ ℕ).mapDomain Nat.succ) (firstLetterGeometric K k)
      = 1 := by
    rw [Finsupp.mapDomain_zero, add_zero, coeff_firstLetterGeometric,
      ite_eq_left Finsupp.support_single_subset]
  rw [hN (N + 1) (by omega)] at h1
  exact zero_ne_one h1

/-- **Not every series of `P_k` has bounded `x₁`-degree**, over any nontrivial base. This is the
negation of the right-hand side of `HJO.Sym.injective_insertFront_iff`, so with that equivalence it
is a second proof of `HJO.Sym.not_injective_insertFront` — and it locates the failure of the
statement `HJO.Sym.injOn_insertFront` in the domain rather than in the map: the obstruction that
equivalence identifies is not merely conceivable but realized. -/
theorem not_forall_boundedFrontDegree (K : Type*) [CommRing K] [Nontrivial K] (k : ℕ) :
    ¬ ∀ F : AuxAlphabetSeries K k, BoundedFrontDegree F :=
  fun h => not_boundedFrontDegree_firstLetterGeometric k (h _)

end HJO.Sym
