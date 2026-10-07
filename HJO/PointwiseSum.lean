/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Mathlib.Algebra.BigOperators.Finprod
public import Mathlib.RingTheory.MvPowerSeries.Basic
public meta import HJO.Attr

/-! # Sums over infinite index sets

Several statements of the library sum a family indexed by an infinite set — over all words in
`ℤ_{>0}^n`, over all cylindric partitions of a profile, over all monomials of bounded degree. No
ordering of the index set is available, so the sum is not a sum of a sequence; what makes it
meaningful is that each family is finite in the only sense that matters, namely that fixing a
coefficient leaves only finitely many members reaching it. This file fixes the two notions the
library needs, for a family of functions and then for a family of power series.

## Main definitions

* `HJO.Sym.PointwiseFinite`: the family `(f_l)_{l ∈ I}` of functions is *pointwise finite* —
  `{l : f_l b ≠ 0}` is finite for every `b`.
* `HJO.Sym.pointwiseSum`: the function `b ↦ ∑_{l : f_l b ≠ 0} f_l b`.
* `HJO.Sym.coeffFunction`: the coefficient function of a formal power series.
* `HJO.Sym.IsSummableFamily`: a family in a power series ring is *summable* — its family of
  coefficient functions is pointwise finite.
* `HJO.Sym.summableSum`: the power series whose coefficient function is the pointwise sum of the
  coefficient functions of the members.

## Main results

* `HJO.Sym.coeff_summableSum_eq_sum`: the coefficient of a monomial in the sum of a summable family
  is an honest `Finset` sum, over any finite set carrying all the members that reach that monomial.
  This is the form in which every consumer reads the definition.
* `HJO.Sym.IsSummableFamily.map` and `HJO.Sym.map_summableSum`: an additive map applied to every
  coefficient carries a summable family to a summable family and commutes with its sum. This is what
  makes a coefficientwise operator — the swapping operator `Δ_i` in particular — respect
  monomialwise sums.

## Implementation notes

*The notion is `Mathlib`'s `finsum`, and is not reproved here.* `finsum` — the `∑ᶠ` notation of
`Mathlib.Algebra.BigOperators.Finprod` — is by definition the sum over the (finite) support of its
argument, and `0` when that support is infinite; that is literally the "sum over the finite set
`{l : f_l(b) ≠ 0}`" that `pointwiseSum` is meant to be. So `pointwiseSum` is `finsum` applied
pointwise, and `PointwiseFinite` is `Mathlib`'s `Function.HasFiniteSupport` applied pointwise.
Nothing of the topological `Summable`/`HasSum` hierarchy is used: a family indexed by an unordered
infinite set has no net of partial sums to converge.

*The coefficient function of a power series is the series.* `Mathlib` represents
`MvPowerSeries σ K` as the functions from monomials `σ →₀ ℕ` to `K`, and `MvPowerSeries.coeff e f`
is `f e`; so `coeffFunction` is the identity up to that representation, recorded here because it is
cited by name, and `coeffFunction_injective` is the property its consumers use — an
element of the ring is determined by its coefficients.

*Values lie in an additive commutative monoid, not in a field `𝕂`.* Nothing below
needs more, and the consumers instantiate at the coefficient ring of `P_k` and at its fraction
field alike.

## References

This file formalises Definitions `HJO.Sym.PointwiseFinite`, `HJO.Sym.pointwiseSum`,
`HJO.Sym.coeffFunction`, `HJO.Sym.IsSummableFamily` and `HJO.Sym.summableSum`: sums over infinite
index sets.
-/

@[expose] public section

namespace HJO.Sym

/-! ### Pointwise finite families of functions -/

/-- **A pointwise finite family**: the family `(f_l)_{l ∈ I}` of functions from `B` to the values is
pointwise finite if for every `b ∈ B` the set `{l ∈ I : f_l b ≠ 0}` is finite. This is
`Function.HasFiniteSupport` applied to each `b` separately; it is strictly weaker than finiteness of
the support of `f` itself, which would ask that only finitely many *members* be nonzero. -/
@[hjo "def_pointwise_finite"]
def PointwiseFinite {I B M : Type*} [Zero M] (f : I → B → M) : Prop :=
  ∀ b, Function.HasFiniteSupport fun l => f l b

/-- **The sum of a pointwise finite family**: the function whose value at `b` is the sum of `f_l b`
over the finitely many `l` with `f_l b ≠ 0`. That description is exactly `Mathlib`'s `finsum`, which
sums over the support when it is finite; at a `b` where the family is *not* pointwise finite the
value is `0`, a junk value no consumer reads, every family summed below being pointwise finite. -/
@[hjo "def_pointwise_sum"]
noncomputable def pointwiseSum {I B M : Type*} [AddCommMonoid M] (f : I → B → M) : B → M :=
  fun b => ∑ᶠ l, f l b

variable {I B M N : Type*}

theorem pointwiseSum_apply [AddCommMonoid M] (f : I → B → M) (b : B) :
    pointwiseSum f b = ∑ᶠ l, f l b :=
  rfl

/-- **The sum of a pointwise finite family is a `Finset` sum**, over any finite set of indices
carrying every member that is nonzero at `b`. This is the form in which the definition is read:
whichever finite `s` is convenient, the value is `∑ l ∈ s, f l b`. -/
theorem pointwiseSum_eq_sum [AddCommMonoid M] {f : I → B → M} {b : B} {s : Finset I}
    (hs : ∀ l, f l b ≠ 0 → l ∈ s) : pointwiseSum f b = ∑ l ∈ s, f l b :=
  finsum_eq_sum_of_support_subset _ fun l hl => hs l hl

/-- The sum of the empty family, and of any family vanishing at `b`, is `0` there. -/
@[simp]
theorem pointwiseSum_eq_zero [AddCommMonoid M] {f : I → B → M} {b : B} (h : ∀ l, f l b = 0) :
    pointwiseSum f b = 0 := by
  rw [pointwiseSum_eq_sum (s := (∅ : Finset I)) fun l hl => absurd (h l) hl, Finset.sum_empty]

/-- A family that vanishes at `b` for all but the members of a finite set is pointwise finite
there; stated as the criterion that produces `PointwiseFinite` in practice. -/
theorem pointwiseFinite_of_forall_exists_finset [Zero M] {f : I → B → M}
    (h : ∀ b, ∃ s : Finset I, ∀ l, f l b ≠ 0 → l ∈ s) : PointwiseFinite f := fun b => by
  obtain ⟨s, hs⟩ := h b
  exact Set.Finite.subset s.finite_toSet fun _ hl => hs _ hl

/-- A pointwise finite family has, at each point, a finite set of indices carrying every nonzero
member: the converse of `pointwiseFinite_of_forall_exists_finset`. -/
theorem PointwiseFinite.exists_finset [Zero M] {f : I → B → M} (hf : PointwiseFinite f) (b : B) :
    ∃ s : Finset I, ∀ l, f l b ≠ 0 → l ∈ s :=
  ⟨(hf b).toFinset, fun _ hl => (Set.Finite.mem_toFinset _).2 hl⟩

/-- Applying a map that kills `0` to every member of a pointwise finite family leaves it pointwise
finite: a member that was zero at `b` stays zero there, so the surviving indices are among the old
ones. -/
theorem PointwiseFinite.comp [Zero M] [Zero N] {f : I → B → M} (hf : PointwiseFinite f)
    {D : M → N} (hD : D 0 = 0) : PointwiseFinite fun l b => D (f l b) := by
  refine pointwiseFinite_of_forall_exists_finset fun b => ?_
  obtain ⟨s, hs⟩ := hf.exists_finset b
  exact ⟨s, fun l hl => hs l fun h => hl (by rw [h, hD])⟩

/-- **An additive map commutes with the sum of a pointwise finite family.** The sum being a finite
`Finset` sum at each point, this is `map_sum`. -/
theorem map_pointwiseSum [AddCommMonoid M] [AddCommMonoid N] {f : I → B → M}
    (hf : PointwiseFinite f) (D : M →+ N) (b : B) :
    D (pointwiseSum f b) = pointwiseSum (fun l b => D (f l b)) b := by
  obtain ⟨s, hs⟩ := hf.exists_finset b
  rw [pointwiseSum_eq_sum hs, map_sum,
    pointwiseSum_eq_sum (s := s) fun l hl => hs l fun h => hl (by rw [h, map_zero])]

/-! ### Summable families of power series -/

/-- **The coefficient function of a series**: the function sending a monomial to its coefficient in
`f`. `Mathlib` represents `MvPowerSeries σ K` by exactly these functions, so this is the identity
read through `MvPowerSeries.coeff`; it is named because the notion of a summable family
is phrased through it. -/
@[hjo "def_coeff_function"]
def coeffFunction {σ K : Type*} [Semiring K] (f : MvPowerSeries σ K) : (σ →₀ ℕ) → K :=
  fun e => MvPowerSeries.coeff e f

@[simp]
theorem coeffFunction_apply {σ K : Type*} [Semiring K] (f : MvPowerSeries σ K) (e : σ →₀ ℕ) :
    coeffFunction f e = MvPowerSeries.coeff e f :=
  rfl

/-- A series is determined by its coefficient function: the property of `coeffFunction` that every
consumer of the definition actually uses. -/
theorem coeffFunction_injective {σ K : Type*} [Semiring K] :
    Function.Injective (coeffFunction (σ := σ) (K := K)) := fun _ _ h =>
  MvPowerSeries.ext fun e => congrFun h e

/-- **A summable family of series**: the family `(f_l)_{l ∈ I}` in a formal power series ring is
summable if the family of its coefficient functions is pointwise finite, that is if for every
monomial only finitely many members have a nonzero coefficient there. When the variables are
displayed such a family is also called *monomialwise finite*. -/
@[hjo "def_summable_family"]
def IsSummableFamily {I σ K : Type*} [Semiring K] (f : I → MvPowerSeries σ K) : Prop :=
  PointwiseFinite fun l => coeffFunction (f l)

/-- **The sum of a summable family**: the element of the power series ring whose coefficient
function is the pointwise sum of the coefficient functions of the members. -/
@[hjo "def_summable_sum"]
noncomputable def summableSum {I σ K : Type*} [Semiring K] (f : I → MvPowerSeries σ K) :
    MvPowerSeries σ K :=
  pointwiseSum fun l => coeffFunction (f l)

variable {σ K : Type*} [Semiring K] {f : I → MvPowerSeries σ K}

@[simp]
theorem coeff_summableSum (f : I → MvPowerSeries σ K) (e : σ →₀ ℕ) :
    MvPowerSeries.coeff e (summableSum f) = ∑ᶠ l, MvPowerSeries.coeff e (f l) :=
  rfl

theorem isSummableFamily_iff : IsSummableFamily f ↔
    ∀ e : σ →₀ ℕ, (Function.support fun l => MvPowerSeries.coeff e (f l)).Finite :=
  Iff.rfl

/-- **The coefficient of a monomial in the sum of a summable family is a `Finset` sum**, over any
finite set of indices carrying every member with a nonzero coefficient at that monomial. This is
how the definition is read at a coefficient. -/
theorem coeff_summableSum_eq_sum {e : σ →₀ ℕ} {s : Finset I}
    (hs : ∀ l, MvPowerSeries.coeff e (f l) ≠ 0 → l ∈ s) :
    MvPowerSeries.coeff e (summableSum f) = ∑ l ∈ s, MvPowerSeries.coeff e (f l) :=
  pointwiseSum_eq_sum hs

/-- A summable family has, at each monomial, a finite set of indices carrying every member that
reaches it. -/
theorem IsSummableFamily.exists_finset (hf : IsSummableFamily f) (e : σ →₀ ℕ) :
    ∃ s : Finset I, ∀ l, MvPowerSeries.coeff e (f l) ≠ 0 → l ∈ s :=
  PointwiseFinite.exists_finset hf e

/-- **A coefficientwise additive operator carries a summable family to a summable family**: a
member whose coefficient at a monomial was `0` still has `0` there, so the indices reaching a
monomial after the operator are among those reaching it before. -/
theorem IsSummableFamily.map {L : Type*} [Semiring L] (hf : IsSummableFamily f) (D : K →+ L)
    {Φ : MvPowerSeries σ K → MvPowerSeries σ L}
    (hΦ : ∀ (F : MvPowerSeries σ K) (e : σ →₀ ℕ),
      MvPowerSeries.coeff e (Φ F) = D (MvPowerSeries.coeff e F)) :
    IsSummableFamily fun l => Φ (f l) := fun e => by
  simpa only [coeffFunction_apply, hΦ] using
    (PointwiseFinite.comp (f := fun l => coeffFunction (f l)) hf (D := D) (map_zero D)) e

/-- **A coefficientwise additive operator commutes with the sum of a summable family**: the sum of
the images is the image of the sum. -/
theorem map_summableSum {L : Type*} [Semiring L] (hf : IsSummableFamily f) (D : K →+ L)
    {Φ : MvPowerSeries σ K → MvPowerSeries σ L}
    (hΦ : ∀ (F : MvPowerSeries σ K) (e : σ →₀ ℕ),
      MvPowerSeries.coeff e (Φ F) = D (MvPowerSeries.coeff e F)) :
    Φ (summableSum f) = summableSum fun l => Φ (f l) :=
  MvPowerSeries.ext fun e => by
    rw [hΦ, coeff_summableSum, coeff_summableSum]
    simp only [hΦ]
    simpa only [coeffFunction_apply, pointwiseSum_apply] using
      map_pointwiseSum (f := fun l => coeffFunction (f l)) hf D e

end HJO.Sym
