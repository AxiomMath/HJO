/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Mathlib.RingTheory.Localization.AsSubring
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import HJO.Paths.Primitive
public import HJO.Symmetric.ReesRegular
public meta import HJO.Attr

/-! # The rank data of a primitive path, and the scalars regular at `u = 1`

The hook count of a concatenation of primitive blocks splits into the internal count of each
block and one term for each ordered pair of blocks, and the pair term is a count of ranks:
north steps of the earlier block against east steps of the later one. The first half of this
file records the vocabulary that term is expressed in. The reading of an order filter `F ⊆ G`
used there is the flag extension of `1_F` at level `N = 1`, at which a nonnegative non-gap
counts as present; the flag set `F̂` collects the integers it marks. The north rank
`ρ_F(i) = b min{r : y_r ≥ i} - ai` and the east rank `σ_F(r) = rb - a y_r` label the north and
the east steps of the primitive path `P_F` by the integer the flag set sees them at, the rank
window `w(t) = 1_{-b < t ≤ a}` cuts out the range in which a north rank and an east rank
interact, and the pair kernel `K*` assembles four shifted windows. Two counts attached to an
ordered pair of order filters follow: the cross count `J(F, H)` of pairs of ranks inside the
window, and the ordered part `I(F, H)`, an alternating count of the translates of `F` by
`0, a, b` and `d = a + b` that land in `Ĥ`.

The second half is about specialising `u` to `1`. The base field `𝕜 = ℚ(q, u)` admits no
specialisation at all, `u - 1` being invertible there, so the operation is taken on the
localisation `R` of `ℚ(q)[u]` at the prime ideal `(u - 1)`, a local ring inside `𝕜`. The
specialisation `sp : R → ℚ(q)` evaluates `u` at `1`. A symmetric function is regular at `u = 1`
when all of its coefficients in the products of power sums lie in `R`, an operator is regular
when it preserves those, and a regular operator induces an endomorphism of
`Λ_R / ℏΛ_R`, with `ℏ = 1 - u`. The last definition is the `ℏ`-adic convergence of a family of
operators at a symmetric function, the sense in which an operator of the order filtration is
the sum of its graded pieces.

## Main definitions

* `HJO.Primitive.flagSet`: the flag set `F̂` of an order filter.
* `HJO.Primitive.northRank`, `HJO.Primitive.eastRank`: the ranks `ρ_F(i)` and `σ_F(r)`.
* `HJO.Primitive.window`, `HJO.Primitive.pairKernel`: the rank window `w` and the pair
  kernel `K*`.
* `HJO.Primitive.crossCount`, `HJO.Primitive.orderedPart`: the counts `J(F, H)` and `I(F, H)`.
* `HJO.ReesRegular.regularScalars`: the scalars regular at `u = 1`.
* `HJO.ReesRegular.specialise`: the specialisation `sp` of a regular scalar.
* `HJO.ReesRegular.IsRegularOver`: an operator regular at `u = 1`.
* `HJO.ReesRegular.specialiseEnd`: the specialisation `P|_{u=1}` of a regular operator.
* `HJO.ReesRegular.ConvergesAt`: `ℏ`-adic convergence of a family of operators at a symmetric
  function.

## Main results

* `HJO.Primitive.crossCount_eq_sum`, `HJO.Primitive.orderedPart_eq_sum`: the two counts as
  sums of windows and of indicators.
* `HJO.ReesRegular.mem_regSub_iff_forall_coeff_mem`: a symmetric function is regular at `u = 1`
  exactly when each of its coefficients is.
* `HJO.ReesRegular.hbar_smul_eq_zero`: `ℏ` annihilates `Λ_R / ℏΛ_R`, so the action of `R` there
  factors through `R/ℏR ≅ ℚ(q)` and the induced endomorphism is `ℚ(q)`-linear.
* `HJO.ReesRegular.convergesAt_of_eventually_zero`: a family with finitely many nonzero values
  at `f`, all regular at `u = 1`, converges at `f` to the corresponding finite sum.

## Implementation notes

The ranks and the two counts are integer valued, negative values of a rank being the ones the
flag set does not see. The window and the pair kernel are integer valued on all of `ℤ`, with no
hypothesis relating `a` and `b`; the geometric readings apply for coprime `1 < a < b` and `F`,
`H` order filters of the gap set.

The symmetric functions regular at `u = 1` are the image `regSub R L` of the coefficientwise
inclusion, already available over an arbitrary coefficient ring; the definition by coefficients
is recorded here as `mem_regSub_iff_forall_coeff_mem`. In the same spirit the regular scalars are
built over an arbitrary field, read as `ℚ(q)`, and everything after them over an arbitrary
coefficient ring mapping into the base.

The submodule `(u-1)Λ_R` is written `ℏΛ_R` with `ℏ = 1 - u`; the two agree, `-1` being a unit.
The specialisation of an operator is recorded as an `R`-linear endomorphism of the quotient;
`ℚ(q)`-linearity is the restriction of scalars along `ℚ(q) → R`, legitimate because the action of
`R` on the quotient kills `ℏ`. Convergence is stated for an arbitrary family of maps rather than
for `ℚ(q)`-linear operators, the condition reading only their values at `f`.

## References

This file formalises the rank data of the multiplicative evaluation, `HJO.Primitive.flagSet`,
`HJO.Primitive.northRank`, `HJO.Primitive.eastRank`, `HJO.Primitive.window`,
`HJO.Primitive.pairKernel`, `HJO.Primitive.crossCount` and `HJO.Primitive.orderedPart`, and the
specialisation at `u = 1`, `HJO.ReesRegular.regularScalars`, `HJO.ReesRegular.specialise`,
`HJO.ReesRegular.mem_regSub_iff_forall_coeff_mem`, `HJO.ReesRegular.IsRegularOver`,
`HJO.ReesRegular.specialiseEnd` and `HJO.ReesRegular.ConvergesAt`.
-/

@[expose] public section

open Finset NumericalSemigroup

namespace HJO.Primitive

/-! ### The flag set of an order filter -/

/-- The flag set `F̂` of an order filter `F` of the gap set: the integers marked by the flag
extension of the indicator vector `1_F` at level `N = 1`. At that level a nonnegative non-gap is
marked, a negative integer is not, and a gap is marked exactly when it lies in `F`. -/
@[hjo "def_ret_flag_set"]
def flagSet (a b : ℕ) (F : Finset ℕ) : Set ℤ :=
  {j | Gaps.flag a b 1 (fun g => if (g : ℕ) ∈ F then 1 else 0) j = 1}

instance (a b : ℕ) (F : Finset ℕ) : DecidablePred (· ∈ flagSet a b F) :=
  fun j => inferInstanceAs (Decidable (Gaps.flag a b 1 _ j = 1))

/-- Membership in the flag set is the flag extension of the indicator vector taking the
value `1`. -/
theorem mem_flagSet_iff {a b : ℕ} {F : Finset ℕ} {j : ℤ} :
    j ∈ flagSet a b F ↔ Gaps.flag a b 1 (fun g => if (g : ℕ) ∈ F then 1 else 0) j = 1 := Iff.rfl

/-- The flag set contains no negative integer. -/
theorem notMem_flagSet_of_neg {a b : ℕ} {F : Finset ℕ} {j : ℤ} (hj : j < 0) :
    j ∉ flagSet a b F := by
  simp [mem_flagSet_iff, Gaps.flag, hj]

/-- A nonnegative integer that is not a gap lies in the flag set. -/
theorem mem_flagSet_of_notMem_gaps {a b : ℕ} {F : Finset ℕ} {j : ℤ} (hj : 0 ≤ j)
    (hg : j.toNat ∉ (finspan {a, b}).gaps) : j ∈ flagSet a b F := by
  simp [mem_flagSet_iff, Gaps.flag, hg, not_lt.mpr hj]

/-- A gap lies in the flag set exactly when it lies in the order filter. -/
theorem mem_flagSet_iff_mem {a b : ℕ} {F : Finset ℕ} {j : ℤ} (hj : 0 ≤ j)
    (hg : j.toNat ∈ (finspan {a, b}).gaps) : j ∈ flagSet a b F ↔ j.toNat ∈ F := by
  simp [mem_flagSet_iff, Gaps.flag, hg, not_lt.mpr hj, HJO.extendNat]

/-! ### The ranks of the north and the east steps -/

/-- The north rank `ρ_F(i) = b min{r : y_r ≥ i} - ai` of the primitive path `P_F` of an order
filter, with `y` the height vector of `P_F`. The geometric reading is the one for
`1 ≤ i ≤ b`, indexing the north steps of `P_F`. -/
@[hjo "def_ret_north_rank"]
def northRank (a b : ℕ) (F : Finset ℕ) (i : ℕ) : ℤ :=
  (b : ℤ) * Paths.firstReach (primitivePath a b F) i - (a : ℤ) * i

/-- The east rank `σ_F(r) = rb - a y_r` of the primitive path `P_F` of an order filter, with `y`
the height vector of `P_F`. The geometric reading is the one for `0 ≤ r ≤ a - 1`, indexing the
east steps of `P_F`. -/
@[hjo "def_ret_east_rank"]
def eastRank (a b : ℕ) (F : Finset ℕ) (r : ℕ) : ℤ :=
  (r : ℤ) * b - (a : ℤ) * Paths.ht (primitivePath a b F) r

/-- Below the endpoint the east rank is read off the counting formula for the heights of the
primitive path. -/
theorem eastRank_of_lt {a b : ℕ} (F : Finset ℕ) {r : ℕ} (hr : r < a) :
    eastRank a b F r = (r : ℤ) * b - (a : ℤ) * primitiveHeight a b F r := by
  rw [eastRank, ht_primitivePath_of_lt F hr]

/-- The north rank at an index the path does reach is the rank of the first column reaching it. -/
theorem northRank_eq {a b : ℕ} (F : Finset ℕ) (i : ℕ) :
    northRank a b F i =
      (b : ℤ) * Paths.firstReach (primitivePath a b F) i - (a : ℤ) * i := rfl

/-! ### The rank window and the pair kernel -/

/-- The rank window `w(t) = 1_{-b < t ≤ a}`, the range in which an east rank and a north rank
interact. -/
@[hjo "def_ret_window"]
def window (a b : ℕ) (t : ℤ) : ℤ := if -(b : ℤ) < t ∧ t ≤ (a : ℤ) then 1 else 0

/-- The rank window is `1` exactly on its range. -/
theorem window_eq_one_iff {a b : ℕ} {t : ℤ} :
    window a b t = 1 ↔ -(b : ℤ) < t ∧ t ≤ (a : ℤ) := by
  rw [window]; split <;> simp_all

/-- The rank window is `0` off its range. -/
theorem window_eq_zero_iff {a b : ℕ} {t : ℤ} :
    window a b t = 0 ↔ ¬ (-(b : ℤ) < t ∧ t ≤ (a : ℤ)) := by
  rw [window]; split <;> simp_all

/-- The pair kernel `K*(t) = w(t) - w(t+a) - w(t-b) + w(t+a-b)`. -/
@[hjo "def_ret_pair_kernel"]
def pairKernel (a b : ℕ) (t : ℤ) : ℤ :=
  window a b t - window a b (t + a) - window a b (t - b) + window a b (t + a - b)

/-! ### The two counts attached to a pair of order filters -/

/-- The cross count `J(F, H)`: the number of pairs `(i, r)` with `1 ≤ i ≤ b`, `0 ≤ r ≤ a - 1`
and `σ_H(r) - ρ_F(i)` inside the rank window. -/
@[hjo "def_ret_cross_count"]
def crossCount (a b : ℕ) (F H : Finset ℕ) : ℕ :=
  #{p ∈ Icc 1 b ×ˢ range a | -(b : ℤ) < eastRank a b H p.2 - northRank a b F p.1 ∧
      eastRank a b H p.2 - northRank a b F p.1 ≤ (a : ℤ)}

/-- The cross count is the sum of the rank window over the pairs of ranks. -/
theorem crossCount_eq_sum (a b : ℕ) (F H : Finset ℕ) :
    (crossCount a b F H : ℤ) =
      ∑ i ∈ Icc 1 b, ∑ r ∈ range a, window a b (eastRank a b H r - northRank a b F i) := by
  rw [crossCount, ← Finset.sum_product', Finset.card_filter]
  push_cast
  refine Finset.sum_congr rfl fun p _ => ?_
  simp [window]

/-- The ordered part `I(F, H)` of a pair of order filters: the translates of `F` by `a` and by
`b` that land in `Ĥ`, less those by `0` and by `d = a + b`. -/
@[hjo "def_ret_ordered_part"]
def orderedPart (a b : ℕ) (F H : Finset ℕ) : ℤ :=
  #{g ∈ F | ((g : ℕ) : ℤ) + a ∈ flagSet a b H}
      + #{g ∈ F | ((g : ℕ) : ℤ) + b ∈ flagSet a b H}
    - #{g ∈ F | ((g : ℕ) : ℤ) ∈ flagSet a b H}
    - #{g ∈ F | ((g : ℕ) : ℤ) + (a + b) ∈ flagSet a b H}

/-- The ordered part is a sum over the order filter of the alternating indicator of the four
translates. -/
theorem orderedPart_eq_sum (a b : ℕ) (F H : Finset ℕ) :
    orderedPart a b F H = ∑ g ∈ F,
      ((if ((g : ℤ) + a) ∈ flagSet a b H then (1 : ℤ) else 0)
        + (if ((g : ℤ) + b) ∈ flagSet a b H then 1 else 0)
        - (if ((g : ℤ)) ∈ flagSet a b H then 1 else 0)
        - (if ((g : ℤ) + (a + b)) ∈ flagSet a b H then 1 else 0)) := by
  simp only [orderedPart, Finset.card_filter, Finset.sum_sub_distrib, Finset.sum_add_distrib]
  push_cast
  ring

end HJO.Primitive

namespace HJO.ReesRegular

open HJO.Sym

/-! ### The regular scalars and their specialisation -/

section Scalars

variable (K : Type*) [Field K]

/-- The prime ideal `(u - 1)` of `ℚ(q)[u]`. -/
noncomputable def idealOne : Ideal (Polynomial K) := Ideal.span {Polynomial.X - 1}

instance : (idealOne K).IsPrime := by
  rw [idealOne, Ideal.span_singleton_prime (by simpa using Polynomial.X_sub_C_ne_zero (1 : K))]
  simpa using Polynomial.prime_X_sub_C (1 : K)

/-- The scalars regular at `u = 1`: the localisation of `ℚ(q)[u]` at the prime ideal `(u - 1)`,
as a subalgebra of `𝕜 = ℚ(q, u)`. -/
@[hjo "def_regular_scalar"]
noncomputable def regularScalars : Subalgebra (Polynomial K) (RatFunc K) :=
  Localization.subalgebra (RatFunc K) (idealOne K).primeCompl
    (Ideal.primeCompl_le_nonZeroDivisors _)

instance : IsLocalization (idealOne K).primeCompl (regularScalars K) :=
  inferInstanceAs (IsLocalization _ (Localization.subalgebra ..))

instance : IsLocalRing (regularScalars K) :=
  IsLocalization.AtPrime.isLocalRing (regularScalars K) (idealOne K)

/-- A polynomial not divisible by `u - 1` has a unit value at `u = 1`. -/
theorem isUnit_eval_one_of_mem_primeCompl (y : (idealOne K).primeCompl) :
    IsUnit ((Polynomial.evalRingHom (1 : K)) (y : Polynomial K)) := by
  obtain ⟨y, hy⟩ := y
  simp only [idealOne, Ideal.primeCompl, Submonoid.mem_mk] at hy
  refine isUnit_iff_ne_zero.mpr fun h => hy ?_
  exact Ideal.mem_span_singleton.mpr (Polynomial.dvd_iff_isRoot.mpr h)

/-- The specialisation `sp` of a regular scalar: the ring homomorphism from the regular scalars
to `ℚ(q)` evaluating `u` at `1`. -/
@[hjo "def_specialisation"]
noncomputable def specialise : regularScalars K →+* K :=
  IsLocalization.lift (isUnit_eval_one_of_mem_primeCompl K)

variable {K}

/-- The specialisation of a polynomial is its value at `u = 1`. -/
@[simp] theorem specialise_algebraMap (p : Polynomial K) :
    specialise K (algebraMap (Polynomial K) (regularScalars K) p) = p.eval 1 :=
  IsLocalization.lift_eq _ _

/-- The specialisation sends `u` to `1`. -/
@[simp] theorem specialise_u :
    specialise K (algebraMap (Polynomial K) (regularScalars K) Polynomial.X) = 1 := by
  simp

/-- The specialisation kills `ℏ = 1 - u`. -/
@[simp] theorem specialise_hbar :
    specialise K (1 - algebraMap (Polynomial K) (regularScalars K) Polynomial.X) = 0 := by
  simp

end Scalars

/-! ### The regular symmetric functions and the regular operators -/

section Reg

variable (R : Type*) [CommRing R] (L : Type*) [CommRing L] [Algebra R L]

/-- A symmetric function is regular at `u = 1` exactly when each of its coefficients in the
products of power sums is: `Λ_R` is the coefficientwise image of the symmetric functions
over `R`. -/
@[hjo "def_regular_symm"]
theorem mem_regSub_iff_forall_coeff_mem {x : Lambda L} :
    x ∈ regSub R L ↔ ∀ d : ℕ →₀ ℕ, MvPolynomial.coeff d x ∈ Set.range (algebraMap R L) := by
  rw [regSub, show LinearMap.range (coeffInc R L).toLinearMap
      = (coeffInc R L).range.toSubmodule from rfl, coeffInc, MvPolynomial.range_mapAlgHom,
    MvPolynomial.mem_coeffsIn]
  simp [Algebra.mem_bot]

/-- The multiples `cΛ_R` of the symmetric functions with coefficients in `R` by a scalar
`c ∈ R`. -/
noncomputable def smulRegSub (c : R) : Submodule R (Lambda L) :=
  Submodule.map (c • (LinearMap.id : Lambda L →ₗ[R] Lambda L)) (regSub R L)

variable {R L}

/-- Membership in `cΛ_R`. -/
theorem mem_smulRegSub {c : R} {x : Lambda L} :
    x ∈ smulRegSub R L c ↔ ∃ y ∈ regSub R L, c • y = x := Iff.rfl

/-- A multiple of the symmetric functions with coefficients in `R` has coefficients in `R`. -/
theorem smulRegSub_le_regSub (c : R) : smulRegSub R L c ≤ regSub R L := by
  rintro x ⟨y, hy, rfl⟩
  exact Submodule.smul_mem _ _ hy

/-- An operator regular at `u = 1`: one carrying the symmetric functions with coefficients in
`R` to symmetric functions with coefficients in `R`. -/
@[hjo "def_regular_operator"]
def IsRegularOver (R : Type*) [CommRing R] {L : Type*} [CommRing L] [Algebra R L]
    (P : Module.End L (Lambda L)) : Prop := ∀ f ∈ regSub R L, P f ∈ regSub R L

/-- A composite of regular operators is regular. -/
theorem IsRegularOver.mul {P Q : Module.End L (Lambda L)} (hP : IsRegularOver R P)
    (hQ : IsRegularOver R Q) : IsRegularOver R (P * Q) :=
  fun f hf => hP _ (hQ f hf)

/-- A sum of regular operators is regular. -/
theorem IsRegularOver.add {P Q : Module.End L (Lambda L)} (hP : IsRegularOver R P)
    (hQ : IsRegularOver R Q) : IsRegularOver R (P + Q) :=
  fun f hf => Submodule.add_mem _ (hP f hf) (hQ f hf)

/-! ### The specialisation of a regular operator -/

/-- The submodule `ℏΛ_R` of `Λ_R`, with `ℏ = 1 - u`. -/
noncomputable def hbarSubmodule (R : Type*) [CommRing R] (L : Type*) [CommRing L] [Algebra R L]
    (u : R) : Submodule R (regSub R L) :=
  (smulRegSub R L (1 - u)).comap (regSub R L).subtype

/-- The quotient `Λ_R / ℏΛ_R`, with `ℏ = 1 - u`. -/
noncomputable abbrev regQuot (R : Type*) [CommRing R] (L : Type*) [CommRing L] [Algebra R L]
    (u : R) : Type _ := regSub R L ⧸ hbarSubmodule R L u

/-- `ℏ` annihilates `Λ_R / ℏΛ_R`, so the action of `R` on the quotient factors through
`R/ℏR`. -/
@[simp] theorem hbar_smul_eq_zero {u : R} (x : regQuot R L u) : (1 - u) • x = 0 := by
  obtain ⟨y, rfl⟩ := (hbarSubmodule R L u).mkQ_surjective x
  rw [← map_smul, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
  exact ⟨y, y.2, rfl⟩

/-- The specialisation `P|_{u=1}` of an operator regular at `u = 1`: the endomorphism of
`Λ_R / ℏΛ_R` induced by the restriction of `P` to `Λ_R`. -/
@[hjo "def_operator_specialisation"]
noncomputable def specialiseEnd {u : R} {P : Module.End L (Lambda L)} (hP : IsRegularOver R P) :
    Module.End R (regQuot R L u) :=
  Submodule.mapQ _ _ (LinearMap.restrict (P.restrictScalars R) fun x hx => hP x hx) (by
    rintro ⟨x, hx⟩ hmem
    obtain ⟨y, hy, rfl⟩ := mem_smulRegSub.mp hmem
    exact mem_smulRegSub.mpr
      ⟨P y, hP y hy, (map_smul (P.restrictScalars R) (1 - u) y).symm⟩)

/-- The specialisation of a regular operator is the operator itself on representatives. -/
theorem specialiseEnd_mkQ {u : R} {P : Module.End L (Lambda L)} (hP : IsRegularOver R P)
    (x : regSub R L) :
    specialiseEnd (u := u) hP ((hbarSubmodule R L u).mkQ x)
      = (hbarSubmodule R L u).mkQ ⟨P x, hP x x.2⟩ :=
  Submodule.mapQ_apply _ _ _ x

/-! ### `ℏ`-adic convergence on a symmetric function -/

/-- The family `P` of operators converges at `f` to `g`: for every `n` the difference
`g - ∑_{j < n} ℏ^j P_j f` lies in `ℏ^n Λ_R`, with `ℏ = 1 - u`. Only the values `P j f` enter, so
no linearity of the members of the family is required. -/
@[hjo "def_hbar_convergent"]
def ConvergesAt (R : Type*) [CommRing R] {L : Type*} [CommRing L] [Algebra R L] (u : R)
    (P : ℕ → Lambda L → Lambda L) (f g : Lambda L) : Prop :=
  ∀ n : ℕ, g - ∑ j ∈ range n, ((1 - u) ^ j) • P j f ∈ smulRegSub R L ((1 - u) ^ n)

/-- A limit of a convergent family has coefficients in `R`. -/
theorem ConvergesAt.mem_regSub {u : R} {P : ℕ → Lambda L → Lambda L} {f g : Lambda L}
    (h : ConvergesAt R u P f g) : g ∈ regSub R L := by
  have h0 := h 0
  simp only [range_zero, Finset.sum_empty, sub_zero, pow_zero] at h0
  exact smulRegSub_le_regSub 1 h0

/-- A family whose values at `f` all have coefficients in `R` and vanish from `N` on converges
at `f` to the finite sum of its first `N` terms. -/
theorem convergesAt_of_eventually_zero {u : R} {P : ℕ → Lambda L → Lambda L} {f g : Lambda L}
    {N : ℕ} (hmem : ∀ j, P j f ∈ regSub R L) (hzero : ∀ j, N ≤ j → P j f = 0)
    (hg : g = ∑ j ∈ range N, ((1 - u) ^ j) • P j f) : ConvergesAt R u P f g := by
  intro n
  rcases le_or_gt n N with hn | hn
  · have key : ∑ j ∈ range n, ((1 - u) ^ j) • P j f
        + ∑ j ∈ Ico n N, ((1 - u) ^ j) • P j f = ∑ j ∈ range N, ((1 - u) ^ j) • P j f := by
      rw [range_eq_Ico, range_eq_Ico, Finset.sum_Ico_consecutive _ (Nat.zero_le n) hn]
    rw [hg, ← key, add_sub_cancel_left]
    refine mem_smulRegSub.mpr ⟨∑ j ∈ Ico n N, ((1 - u) ^ (j - n)) • P j f,
      Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (hmem j), ?_⟩
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [smul_smul, ← pow_add]
    congr 2
    exact Nat.add_sub_cancel' (mem_Ico.mp hj).1
  · have key : ∑ j ∈ range N, ((1 - u) ^ j) • P j f
        = ∑ j ∈ range n, ((1 - u) ^ j) • P j f := by
      have hsub : range N ⊆ range n := fun j hj =>
        mem_range.mpr ((mem_range.mp hj).trans_le hn.le)
      refine Finset.sum_subset hsub fun j _ hj => ?_
      rw [hzero j (by simpa using hj), smul_zero]
    rw [hg, key, sub_self]
    exact Submodule.zero_mem _

end Reg

end HJO.ReesRegular
