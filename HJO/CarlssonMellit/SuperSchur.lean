/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.CarlssonMellit.SuperStd
public import HJO.CarlssonMellit.SuperTableaux
public import HJO.PointwiseSum
public meta import HJO.Attr

/-! # The super fundamental quasisymmetric functions, the super Schur series, and the
standardisation of a super tableau

Three ingredients of the super expansion live here: the super fundamental `F̃_{n,S}`, the sum of
`z_v` over the super words that increase weakly and repeat a letter only in the manner the sign and
the step set `S` permit; the super Schur series `sch̃(D)`, the sum of `z_T` over the super tableaux
of a Young diagram; and the bijection that identifies the second sum with a sum of the first, namely
that a super tableau factors in exactly one way as such a word composed with a standard tableau
whose descents are prescribed by the repetitions of the word.

## Main definitions

* `HJO.Sym.superFundamental`: `F̃_{n,S}`.
* `HJO.Sym.superSchurSeries`: `sch̃(D)`.
* `HJO.Sym.SuperStdPair`: the set `P` of admissible pairs `(S, v)`.
* `HJO.Sym.superTableauOfPair`: the map `(S, v) ↦ (c ↦ v_{S(c)})`.

## Main results

* `HJO.Sym.isSummableFamily_superFundamental`, `HJO.Sym.isSummableFamily_superSchurSeries`: the
  well-definedness the two definitions carry — only finitely many summands reach any one
  coefficient.
* `HJO.Sym.superTableauOfPair_bijective`: super tableaux are exactly the standardised admissible
  pairs.

## Implementation notes

*The two series are sums of summable families, not indicator functions.* `HJO.Sym.msymmSeries` and
`HJO.Sym.schurSeries` can be written by their coefficients because each of their monomials occurs
with coefficient the number of contributing tableaux; here `z_v` and `z_T` are *scalar multiples* of
monomials — the scalar being `q` for each positive letter and `-1` for each negative one — so two
words with the same absolute values contribute different scalars and the coefficient is a signed
sum, not a count. The sums are taken with the summability layer of `HJO/PointwiseSum.lean`:
`HJO.Sym.summableSum` of a family whose `HJO.Sym.IsSummableFamily` is proved separately, that proof
being exactly the well-definedness argument of the two definitions. Nothing of the
topological `Summable`/`HasSum` hierarchy appears; the index sets carry no order.
`HJO.Sym.prod_superVar` is what both summability proofs run on: a product of super variables is one
monomial, at the exponent vector of the absolute values, with the product of the scalars for its
coefficient — so a nonzero coefficient pins the absolute values inside the (finite) support of the
monomial, and the signs range over a finite set of possibilities because the index set of a super
word or a super tableau is finite.

*The index set of `F̃_{n,S}` is the whole of `𝒜^n`, with the inadmissible words contributing `0`.*
That is the same shape `HJO.ParkingFunctions.gessel` has: a total definition for arbitrary `S`, with
no claim that a step outside the window `{1, …, n-1}` is meaningful.

*The index set of `F̃_{n,S}` is `HJO.Sym.IsSuperAscendingWord`, which is already in the library.*
That predicate — of `HJO/CarlssonMellit/SuperStd.lean`, where the fibres of the super
standardisation need it — carries the three defining clauses as its three fields, with the weak
increase stated between adjacent positions exactly as it is usually stated; it is reused here
rather than restated, and `HJO.Sym.IsSuperAscendingWord.monotone` chains that weak increase, which
is the first preliminary of the proof of `HJO.Sym.superTableauOfPair_bijective`. Steps are `1`-based
and positions `0`-based there as here: the step named by the index `j` in `v_j = v_{j+1}` is
the `0`-based index of the *later* of the two positions, matching
`HJO.Sym.IsAscendingWord.lt_of_mem` and `HJO.Sym.sytDescentSet`, so the condition and `Des(S)` are
indexed alike and nothing is shifted between them.

*The bijection is stated on a subtype and proved through the canonical ordering of a super tableau.*
As a set, `P` consists of pairs, and its image is all of `SSYT^±(D)`; since a
`HJO.Sym.SuperYoungTableau` carries its own proofs, the map cannot be total on unconstrained pairs,
so `P` is the subtype `HJO.Sym.SuperStdPair` and the statement is `Function.Bijective`. The proof is
the standard one, with the block analysis carried by one key. `HJO.Sym.superCellKey` orders the
cells by their letter, then by column — *increasing* for a positive letter and *decreasing* for a
negative one, which is why the column enters as an integer and is negated — and then by row. That
key is injective on all of `ℕ × ℕ`, so `HJO.Sym.superRank`, the number of cells whose key is
smaller, is a bijection from the cells onto `{0, …, n-1}` and is order-isomorphic to the key; it is
the unique admissible `S`, and `HJO.Sym.eq_of_lt_iff_lt` is what turns "the same comparisons" into
"the same bijection". The two range statements about `Des(S)` are
`HJO.Sym.col_lt_of_forall_notMem_sytDescentSet` and `HJO.Sym.col_le_of_forall_mem_sytDescentSet`,
proved by induction along the values from the adjacent case.

*The hypothesis `n ≥ 1` is dropped.* At `n = 0` the diagram is empty, both sides are singletons and
the statement holds; no step of the proof uses positivity.

## References

Definitions `HJO.Sym.superFundamental` and `HJO.Sym.superSchurSeries` and lemma
`HJO.Sym.superTableauOfPair_bijective`; E. Carlsson and A. Mellit, *A proof of the shuffle
conjecture*, J. Amer. Math. Soc. **31** (2018) 661--697, Section 3.
-/

@[expose] public section

open Finset

namespace HJO.Sym

/-! ### A product of super variables is one monomial -/

section Monomial

variable {K : Type*} [CommRing K]

/-- The scalar the variable of a super letter carries: `q` for a positive letter and `-1` for a
negative one. It is the whole difference between `z_v` and the plain monomial `x_{|v|}`. -/
def superScalar (q : K) (α : SuperLetter) : K :=
  cond (ofLex α).2 (-1) q

@[simp]
theorem superScalar_of_isNegative (q : K) {α : SuperLetter} (h : α.IsNegative) :
    superScalar q α = -1 := by
  rw [superScalar, show (ofLex α).2 = true from h, Bool.cond_true]

@[simp]
theorem superScalar_of_isPositive (q : K) {α : SuperLetter} (h : α.IsPositive) :
    superScalar q α = q := by
  rw [superScalar, show (ofLex α).2 = false from h, Bool.cond_false]

/-- **The variable of a super letter is a scaled letter of the alphabet**: the monomial `x_a` at the
absolute value, with the scalar `HJO.Sym.superScalar`. -/
theorem superVar_eq_monomial (q : K) (α : SuperLetter) :
    superVar q α = MvPowerSeries.monomial (Finsupp.single α.absVal 1) (superScalar q α) := by
  by_cases h : α.IsNegative
  · rw [superVar_of_isNegative q h, superScalar_of_isNegative q h, MvPowerSeries.X]
    simp
  · have hp : α.IsPositive := (SuperLetter.isPositive_iff_not_isNegative α).2 h
    rw [superVar_of_isPositive q hp, superScalar_of_isPositive q hp,
      show (MvPowerSeries.C q : AlphabetSeries K) = MvPowerSeries.monomial 0 q from rfl,
      MvPowerSeries.X, MvPowerSeries.monomial_mul_monomial, zero_add, mul_one]

/-- **A product of super variables is one monomial**: the exponent vector is the one of the absolute
values and the coefficient is the product of the scalars. This is what makes the super fundamental
and the super Schur series summable families: a nonzero coefficient at `x^d` forces every absolute
value into the support of `d`. -/
theorem prod_superVar {ι : Type*} (q : K) (s : Finset ι) (f : ι → SuperLetter) :
    ∏ i ∈ s, superVar q (f i)
      = MvPowerSeries.monomial (∑ i ∈ s, Finsupp.single (f i).absVal 1)
          (∏ i ∈ s, superScalar q (f i)) := by
  induction s using Finset.cons_induction with
  | empty => simp
  | cons a s ha ih =>
    rw [Finset.prod_cons, Finset.prod_cons, Finset.sum_cons, ih, superVar_eq_monomial,
      MvPowerSeries.monomial_mul_monomial]

/-- The coefficients of a product of super variables: the product of the scalars at the exponent
vector of the absolute values, and `0` elsewhere. -/
theorem coeff_prod_superVar {ι : Type*} (q : K) (s : Finset ι) (f : ι → SuperLetter)
    (d : ℕ →₀ ℕ) :
    MvPowerSeries.coeff d (∏ i ∈ s, superVar q (f i))
      = if d = ∑ i ∈ s, Finsupp.single (f i).absVal 1 then ∏ i ∈ s, superScalar q (f i) else 0 := by
  rw [prod_superVar, MvPowerSeries.coeff_monomial]

/-- Every absolute value of an indexed family of super letters occurs in the exponent vector the
family produces. -/
theorem absVal_mem_support_sum {ι : Type*} (s : Finset ι) (f : ι → SuperLetter) {i : ι}
    (hi : i ∈ s) :
    (f i).absVal ∈ (∑ j ∈ s, Finsupp.single (f j).absVal 1).support := by
  rw [Finsupp.mem_support_iff, Finset.sum_apply']
  refine Nat.pos_iff_ne_zero.1 (Finset.sum_pos' (fun _ _ => Nat.zero_le _) ⟨i, hi, ?_⟩)
  simp

end Monomial

/-! ### The letters of a bounded absolute value -/

/-- The super letters whose absolute value lies in a given finite set: finitely many, two for each
absolute value. This is the finite set the summability of both series is read off. -/
def letterFinset (u : Finset ℕ) : Finset SuperLetter :=
  (u ×ˢ (univ : Finset Bool)).image fun p => SuperLetter.mk p.1 p.2

@[simp]
theorem mem_letterFinset {u : Finset ℕ} {β : SuperLetter} :
    β ∈ letterFinset u ↔ β.absVal ∈ u := by
  simp only [letterFinset, Finset.mem_image, Finset.mem_product, Finset.mem_univ, and_true]
  refine ⟨fun ⟨p, hp, hpb⟩ => ?_, fun h => ⟨(β.absVal, (ofLex β).2), h, SuperLetter.ext rfl rfl⟩⟩
  rw [← hpb, SuperLetter.absVal_mk]
  exact hp

/-- The set of super letters of bounded absolute value is finite. -/
theorem finite_absVal_mem (u : Finset ℕ) : {β : SuperLetter | β.absVal ∈ u}.Finite :=
  Set.Finite.ofFinset (letterFinset u) fun _ => by simp

/-! ### The words the super fundamental sums over -/

namespace IsSuperAscendingWord

variable {n : ℕ} {S : Finset ℕ} {v : Fin n → SuperLetter}

/-- **The weak increase chains**: a super ascending word is monotone, the positions of `Fin n` being
contiguous. This is the first preliminary of the proof of `HJO.Sym.superTableauOfPair_bijective`,
read on a word rather than on a row of a diagram. -/
theorem monotone (h : IsSuperAscendingWord n S v) : Monotone v := by
  cases n with
  | zero => exact fun a => a.elim0
  | succ N => exact Fin.monotone_iff_le_succ.2 fun i => h.le_of_step _ _ (by simp)

/-- A super ascending word is constant between two positions carrying the same letter. -/
theorem eq_of_between (h : IsSuperAscendingWord n S v) {p r i : Fin n} (hpr : v p = v r)
    (h1 : p ≤ i) (h2 : i ≤ r) : v i = v p :=
  le_antisymm (hpr ▸ h.monotone h2) (h.monotone h1)

end IsSuperAscendingWord

/-! ### The super fundamental quasisymmetric function -/

/-- **The super fundamental quasisymmetric function** `F̃_{n,S}`: the
sum of `z_v` over the super words `v ∈ 𝒜^n` that increase weakly, repeat a positive letter only at a
step outside `S`, and repeat a negative letter only at a step of `S`.

The sum runs over all of `𝒜^n`, the inadmissible words contributing `0`, and it is a sum in the
sense of `HJO.Sym.summableSum`: the family is summable by
`HJO.Sym.isSummableFamily_superFundamental`, so no coefficient of the result is the junk value that
definition takes at a monomial reached by infinitely many summands. -/
@[hjo "def_cm_super_fundamental"]
noncomputable def superFundamental (K : Type*) [CommRing K] (q : K) (n : ℕ) (S : Finset ℕ) :
    AlphabetSeries K :=
  summableSum fun v : Fin n → SuperLetter =>
    if IsSuperAscendingWord n S v then superMonomial K q v else 0

variable {K : Type*} [CommRing K]

/-- **The super fundamental is a well-defined element of `𝒫`**: only finitely many of its summands
reach a given monomial. A word contributing to `x^d` has every absolute value in the support of `d`,
by `HJO.Sym.prod_superVar`, and there are two letters of each absolute value, so the contributing
words lie in a finite set of tuples. -/
@[hjo "def_cm_super_fundamental"]
theorem isSummableFamily_superFundamental (q : K) (n : ℕ) (S : Finset ℕ) :
    IsSummableFamily fun v : Fin n → SuperLetter =>
      if IsSuperAscendingWord n S v then superMonomial K q v else 0 := by
  refine pointwiseFinite_of_forall_exists_finset fun d =>
    ⟨Fintype.piFinset fun _ => letterFinset d.support, fun v hv => ?_⟩
  simp only [Fintype.mem_piFinset, mem_letterFinset]
  intro i
  have hv' : MvPowerSeries.coeff d
      (if IsSuperAscendingWord n S v then superMonomial K q v else 0) ≠ 0 := hv
  by_cases hadm : IsSuperAscendingWord n S v
  · rw [ite_eq_left hadm, superMonomial, coeff_prod_superVar] at hv'
    by_cases hd : d = ∑ j : Fin n, Finsupp.single (v j).absVal 1
    · rw [hd]
      exact absVal_mem_support_sum univ v (mem_univ i)
    · exact absurd (ite_eq_right hd) hv'
  · exact absurd (by rw [ite_eq_right hadm, map_zero]) hv' 

/-- **The coefficients of the super fundamental**: the sum, over the finitely many super words
reaching the monomial, of the coefficient each contributes. -/
@[hjo "def_cm_super_fundamental"]
theorem coeff_superFundamental (q : K) (n : ℕ) (S : Finset ℕ) (d : ℕ →₀ ℕ) :
    MvPowerSeries.coeff d (superFundamental K q n S)
      = ∑ᶠ v : Fin n → SuperLetter,
          MvPowerSeries.coeff d (if IsSuperAscendingWord n S v then superMonomial K q v else 0) :=
  rfl

/-- The coefficient of the super fundamental as a `Finset` sum, over any finite set of words
carrying every contribution to the monomial. This is the form in which the definition is read. -/
theorem coeff_superFundamental_eq_sum (q : K) (n : ℕ) (S : Finset ℕ) {d : ℕ →₀ ℕ}
    {s : Finset (Fin n → SuperLetter)}
    (hs : ∀ v, MvPowerSeries.coeff d
        (if IsSuperAscendingWord n S v then superMonomial K q v else 0) ≠ 0 → v ∈ s) :
    MvPowerSeries.coeff d (superFundamental K q n S)
      = ∑ v ∈ s, MvPowerSeries.coeff d
          (if IsSuperAscendingWord n S v then superMonomial K q v else 0) :=
  coeff_summableSum_eq_sum hs

/-! ### The super Schur series of a Young diagram -/

/-- **The super Schur series of a Young diagram**
`sch̃(D) = ∑_{T ∈ SSYT^±(D)} z_T`.

As for the super fundamental the sum is `HJO.Sym.summableSum` of a family whose summability is
proved separately: that is the well-definedness argument of the definition, which is
`HJO.Sym.isSummableFamily_superSchurSeries` — `z_T` is a scalar multiple of a monomial of total
degree `#D`, so a tableau reaching a given monomial takes its absolute values among the finitely
many indices occurring in it and its signs among the `2^{#D}` possibilities. -/
@[hjo "def_cm_super_schur_series"]
noncomputable def superSchurSeries (K : Type*) [CommRing K] (q : K) (μ : YoungDiagram) :
    AlphabetSeries K :=
  summableSum fun T : SuperYoungTableau μ => superTableauMonomial K q T

/-- **The super Schur series is a well-defined element of `𝒫`**: only finitely many super tableaux
reach a given monomial. A super tableau is determined by its values on the cells, and a tableau
contributing to `x^d` takes, at each cell, one of the finitely many letters whose absolute value
lies in the support of `d`. -/
@[hjo "def_cm_super_schur_series"]
theorem isSummableFamily_superSchurSeries (q : K) (μ : YoungDiagram) :
    IsSummableFamily fun T : SuperYoungTableau μ => superTableauMonomial K q T := by
  intro d
  have hinj : Function.Injective
      fun (T : SuperYoungTableau μ) => fun c : ↥μ.cells => T (c : ℕ × ℕ).1 (c : ℕ × ℕ).2 := by
    intro T T' h
    refine SuperYoungTableau.ext fun i j => ?_
    by_cases hc : (i, j) ∈ μ
    · exact congrFun h ⟨(i, j), by simpa using hc⟩
    · rw [T.outside hc, T'.outside hc]
  refine Set.Finite.of_finite_image ?_ hinj.injOn
  refine Set.Finite.subset (Set.Finite.pi fun _ : ↥μ.cells => finite_absVal_mem d.support) ?_
  rintro g ⟨T, hT, rfl⟩
  refine fun c _ => ?_
  have hT' : MvPowerSeries.coeff d (superTableauMonomial K q T) ≠ 0 := hT
  rw [superTableauMonomial, coeff_prod_superVar] at hT'
  by_cases hd : d = ∑ e ∈ μ.cells, Finsupp.single (T (e : ℕ × ℕ).1 (e : ℕ × ℕ).2).absVal 1
  · simp only [Set.mem_ofPred_eq, hd]
    exact Finset.mem_coe.2 (absVal_mem_support_sum μ.cells _ c.2)
  · exact absurd (ite_eq_right hd) hT'

/-! ### Standard tableaux increase strictly along a row -/

variable {μ : YoungDiagram}

/-- **A standard tableau increases strictly along a row**: weakly by
`SemistandardYoungTableau.row_weak`, and strictly because no value is repeated. -/
theorem IsStandard.row_lt {S : SemistandardYoungTableau μ} (hS : IsStandard S) {i j1 j2 : ℕ}
    (hj : j1 < j2) (hcell : (i, j2) ∈ μ) : S i j1 < S i j2 := by
  have hcell1 : ((i, j1) : ℕ × ℕ) ∈ μ := μ.up_left_mem le_rfl hj.le hcell
  refine lt_of_le_of_ne (S.row_weak hj hcell) fun heq => ?_
  have hc : ((i, j1) : ℕ × ℕ) = (i, j2) :=
    hS.injOn (by simpa using hcell1) (by simpa using hcell) heq
  exact absurd (congrArg Prod.snd hc) (by omega)

/-! ### The descent set of a standard tableau, read on a range of values -/

/-- **The adjacent case of the range statement, at a non-descent**: if the step from the
value of `c` to the next value is not a descent, then `c` lies strictly to the left of the cell
carrying that next value. -/
theorem col_lt_of_notMem_sytDescentSet {S : SemistandardYoungTableau μ} (hS : IsStandard S)
    {c c' : ℕ × ℕ} (hc : c ∈ μ.cells) (hc' : c' ∈ μ.cells)
    (hstep : S c'.1 c'.2 = S c.1 c.2 + 1) (hnot : S c.1 c.2 + 1 ∉ sytDescentSet S) :
    c.2 < c'.2 := by
  by_contra hle
  refine hnot (mem_sytDescentSet.2 ⟨Nat.le_add_left 1 _, hstep ▸ hS.lt_card hc', ?_⟩)
  intro e he e' he' hea hea'
  have hee : e = c' := hS.injOn (by simpa using he) (by simpa using hc')
    (show S e.1 e.2 = S c'.1 c'.2 by rw [hea, hstep])
  have hee' : e' = c := hS.injOn (by simpa using he') (by simpa using hc)
    (show S e'.1 e'.2 = S c.1 c.2 by rw [hea']; omega)
  rw [hee, hee']
  omega

/-- **The adjacent case of the range statement, at a descent**: if the step from the
value of `c` to the next value is a descent, then the cell carrying that next value lies weakly to
the left of `c`. -/
theorem col_le_of_mem_sytDescentSet {S : SemistandardYoungTableau μ} {c c' : ℕ × ℕ}
    (hc : c ∈ μ.cells) (hc' : c' ∈ μ.cells) (hstep : S c'.1 c'.2 = S c.1 c.2 + 1)
    (hmem : S c.1 c.2 + 1 ∈ sytDescentSet S) : c'.2 ≤ c.2 := by
  obtain ⟨-, -, h⟩ := mem_sytDescentSet.1 hmem
  exact h c' hc' c hc hstep (by omega)

private theorem col_lt_aux {S : SemistandardYoungTableau μ} (hS : IsStandard S) (r : ℕ) :
    ∀ c c' : ℕ × ℕ, c ∈ μ.cells → c' ∈ μ.cells → S c.1 c.2 < r → S c'.1 c'.2 = r →
      (∀ a, S c.1 c.2 < a → a ≤ r → a ∉ sytDescentSet S) → c.2 < c'.2 := by
  induction r with
  | zero => intro c c' _ _ h _ _; omega
  | succ R ih =>
    intro c c' hc hc' hlt hval hnot
    have hRcard : R < μ.card := by have := hS.lt_card hc'; omega
    obtain ⟨e, he, hev⟩ := hS.exists_eq hRcard
    have hstep : S c'.1 c'.2 = S e.1 e.2 + 1 := by rw [hval, hev]
    rcases Nat.lt_or_ge (S c.1 c.2) R with hcR | hcR
    · have h1 : c.2 < e.2 := ih c e hc he hcR hev fun a ha1 ha2 => hnot a ha1 (by omega)
      have h2 : e.2 < c'.2 := col_lt_of_notMem_sytDescentSet hS he hc' hstep
        (hnot (S e.1 e.2 + 1) (by omega) (by omega))
      omega
    · have hce : c = e := hS.injOn (by simpa using hc) (by simpa using he)
        (show S c.1 c.2 = S e.1 e.2 by rw [hev]; omega)
      subst hce
      exact col_lt_of_notMem_sytDescentSet hS hc hc' hstep
        (hnot (S c.1 c.2 + 1) (by omega) (by omega))

private theorem col_le_aux {S : SemistandardYoungTableau μ} (hS : IsStandard S) (r : ℕ) :
    ∀ c c' : ℕ × ℕ, c ∈ μ.cells → c' ∈ μ.cells → S c.1 c.2 < r → S c'.1 c'.2 = r →
      (∀ a, S c.1 c.2 < a → a ≤ r → a ∈ sytDescentSet S) → c'.2 ≤ c.2 := by
  induction r with
  | zero => intro c c' _ _ h _ _; omega
  | succ R ih =>
    intro c c' hc hc' hlt hval hmem
    have hRcard : R < μ.card := by have := hS.lt_card hc'; omega
    obtain ⟨e, he, hev⟩ := hS.exists_eq hRcard
    have hstep : S c'.1 c'.2 = S e.1 e.2 + 1 := by rw [hval, hev]
    rcases Nat.lt_or_ge (S c.1 c.2) R with hcR | hcR
    · have h1 : e.2 ≤ c.2 := ih c e hc he hcR hev fun a ha1 ha2 => hmem a ha1 (by omega)
      have h2 : c'.2 ≤ e.2 := col_le_of_mem_sytDescentSet he hc' hstep
        (hmem (S e.1 e.2 + 1) (by omega) (by omega))
      omega
    · have hce : c = e := hS.injOn (by simpa using hc) (by simpa using he)
        (show S c.1 c.2 = S e.1 e.2 by rw [hev]; omega)
      subst hce
      exact col_le_of_mem_sytDescentSet hc hc' hstep
        (hmem (S c.1 c.2 + 1) (by omega) (by omega))

/-- **The range statement, at a stretch of non-descents**: if no step from the value of
`c` up to the value of `c'` is a descent, then the columns increase strictly, so `c` lies strictly
to the left of `c'`. -/
theorem col_lt_of_forall_notMem_sytDescentSet {S : SemistandardYoungTableau μ} (hS : IsStandard S)
    {c c' : ℕ × ℕ} (hc : c ∈ μ.cells) (hc' : c' ∈ μ.cells) (hlt : S c.1 c.2 < S c'.1 c'.2)
    (hnot : ∀ a, S c.1 c.2 < a → a ≤ S c'.1 c'.2 → a ∉ sytDescentSet S) : c.2 < c'.2 :=
  col_lt_aux hS _ c c' hc hc' hlt rfl hnot

/-- **The range statement, at a stretch of descents**: if every step from the value of
`c` up to the value of `c'` is a descent, then the columns decrease weakly, so `c'` lies weakly to
the left of `c`. -/
theorem col_le_of_forall_mem_sytDescentSet {S : SemistandardYoungTableau μ} (hS : IsStandard S)
    {c c' : ℕ × ℕ} (hc : c ∈ μ.cells) (hc' : c' ∈ μ.cells) (hlt : S c.1 c.2 < S c'.1 c'.2)
    (hmem : ∀ a, S c.1 c.2 < a → a ≤ S c'.1 c'.2 → a ∈ sytDescentSet S) : c'.2 ≤ c.2 :=
  col_le_aux hS _ c c' hc hc' hlt rfl hmem

/-! ### The filling of an admissible pair -/

/-- The filling `c ↦ v_{S(c)}` of a pair, totalised off the diagram by the least letter
so that it can be a `HJO.Sym.SuperYoungTableau`. -/
def pairEntry (S : SemistandardYoungTableau μ) (v : Fin μ.card → SuperLetter) :
    ℕ → ℕ → SuperLetter := fun i j =>
  if h : (i, j) ∈ μ ∧ S i j < μ.card then v ⟨S i j, h.2⟩ else SuperLetter.mk 0 false

theorem pairEntry_of_mem {S : SemistandardYoungTableau μ} {v : Fin μ.card → SuperLetter}
    (hS : IsStandard S) {c : ℕ × ℕ} (hc : c ∈ μ.cells) :
    pairEntry S v c.1 c.2 = v ⟨S c.1 c.2, hS.lt_card hc⟩ :=
  dite_eq_left ⟨by simpa using hc, hS.lt_card hc⟩

theorem pairEntry_of_notMem {S : SemistandardYoungTableau μ} {v : Fin μ.card → SuperLetter}
    {i j : ℕ} (h : (i, j) ∉ μ) : pairEntry S v i j = SuperLetter.mk 0 false :=
  dite_eq_right fun hc => h hc.1

/-! ### The two blocks of an admissible pair -/

section Block

variable {S : SemistandardYoungTableau μ} {v : Fin μ.card → SuperLetter}

/-- **The positive block of an admissible pair**: two cells carrying the same *positive* letter have
their columns in the order of their values. The word is constant between the two values, so the
positive clause of admissibility puts no descent in that range and the range statement
applies. -/
theorem col_lt_of_isPositive (hS : IsStandard S)
    (hadm : IsSuperAscendingWord μ.card (sytDescentSet S) v) {c c' : ℕ × ℕ}
    (hc : c ∈ μ.cells) (hc' : c' ∈ μ.cells) (hlt : S c.1 c.2 < S c'.1 c'.2)
    (heq : v ⟨S c.1 c.2, hS.lt_card hc⟩ = v ⟨S c'.1 c'.2, hS.lt_card hc'⟩)
    (hpos : (v ⟨S c.1 c.2, hS.lt_card hc⟩).IsPositive) : c.2 < c'.2 := by
  refine col_lt_of_forall_notMem_sytDescentSet hS hc hc' hlt fun a ha1 ha2 => ?_
  have haN : a < μ.card := lt_of_le_of_lt ha2 (hS.lt_card hc')
  have hk : a - 1 < μ.card := by omega
  have hvk : v ⟨a - 1, hk⟩ = v ⟨S c.1 c.2, hS.lt_card hc⟩ :=
    hadm.eq_of_between heq (Fin.mk_le_mk.2 (by omega)) (Fin.mk_le_mk.2 (by omega))
  have hvl : v ⟨a, haN⟩ = v ⟨S c.1 c.2, hS.lt_card hc⟩ :=
    hadm.eq_of_between heq (Fin.mk_le_mk.2 (by omega)) (Fin.mk_le_mk.2 (by omega))
  exact hadm.notMem_of_isPositive ⟨a - 1, hk⟩ ⟨a, haN⟩ (show a - 1 + 1 = a by omega)
    (by rw [hvk, hvl]) (by rw [hvk]; exact hpos)

/-- **The negative block of an admissible pair**: two cells carrying the same *negative* letter have
their columns in the reverse order of their values. -/
theorem col_le_of_isNegative (hS : IsStandard S)
    (hadm : IsSuperAscendingWord μ.card (sytDescentSet S) v) {c c' : ℕ × ℕ}
    (hc : c ∈ μ.cells) (hc' : c' ∈ μ.cells) (hlt : S c.1 c.2 < S c'.1 c'.2)
    (heq : v ⟨S c.1 c.2, hS.lt_card hc⟩ = v ⟨S c'.1 c'.2, hS.lt_card hc'⟩)
    (hneg : (v ⟨S c.1 c.2, hS.lt_card hc⟩).IsNegative) : c'.2 ≤ c.2 := by
  refine col_le_of_forall_mem_sytDescentSet hS hc hc' hlt fun a ha1 ha2 => ?_
  have haN : a < μ.card := lt_of_le_of_lt ha2 (hS.lt_card hc')
  have hk : a - 1 < μ.card := by omega
  have hvk : v ⟨a - 1, hk⟩ = v ⟨S c.1 c.2, hS.lt_card hc⟩ :=
    hadm.eq_of_between heq (Fin.mk_le_mk.2 (by omega)) (Fin.mk_le_mk.2 (by omega))
  have hvl : v ⟨a, haN⟩ = v ⟨S c.1 c.2, hS.lt_card hc⟩ :=
    hadm.eq_of_between heq (Fin.mk_le_mk.2 (by omega)) (Fin.mk_le_mk.2 (by omega))
  exact hadm.mem_of_isNegative ⟨a - 1, hk⟩ ⟨a, haN⟩ (show a - 1 + 1 = a by omega)
    (by rw [hvk, hvl]) (by rw [hvk]; exact hneg)

end Block

/-! ### The super tableau of an admissible pair -/

/-- **The set `P` of admissible pairs**: a standard tableau `S` of the diagram together
with a super word `v` of length `#D` that increases weakly, repeats a positive letter only outside
`Des(S)` and repeats a negative letter only inside it. -/
def SuperStdPair (μ : YoungDiagram) : Type :=
  {p : SemistandardYoungTableau μ × (Fin μ.card → SuperLetter) //
    IsStandard p.1 ∧ IsSuperAscendingWord μ.card (sytDescentSet p.1) p.2}

/-- **The map**: the filling `c ↦ v_{S(c)}` of an admissible pair is a super tableau.
The weak increase in both directions is the weak increase of `v` along the strictly increasing
values of `S`; the two strip conditions are the two block lemmas `HJO.Sym.col_lt_of_isPositive` and
`HJO.Sym.col_le_of_isNegative`, which is the block analysis of the proof. -/
def superTableauOfPair (p : SuperStdPair μ) : SuperYoungTableau μ where
  entry := pairEntry p.1.1 p.1.2
  row_weak' := by
    intro i j1 j2 hj hcell
    have hc2 : ((i, j2) : ℕ × ℕ) ∈ μ.cells := by simpa using hcell
    have hc1 : ((i, j1) : ℕ × ℕ) ∈ μ.cells := by
      simpa using μ.up_left_mem (le_refl i) hj.le hcell
    rw [pairEntry_of_mem p.2.1 hc1, pairEntry_of_mem p.2.1 hc2]
    exact p.2.2.monotone (Fin.mk_le_mk.2 (p.2.1.row_lt hj hcell).le)
  col_weak' := by
    intro i1 i2 j hi hcell
    have hc2 : ((i2, j) : ℕ × ℕ) ∈ μ.cells := by simpa using hcell
    have hc1 : ((i1, j) : ℕ × ℕ) ∈ μ.cells := by
      simpa using μ.up_left_mem hi.le (le_refl j) hcell
    rw [pairEntry_of_mem p.2.1 hc1, pairEntry_of_mem p.2.1 hc2]
    exact p.2.2.monotone (Fin.mk_le_mk.2 (p.1.1.col_strict hi hcell).le)
  col_isNegative' := by
    intro i1 i2 j hi hcell heq
    have hc2 : ((i2, j) : ℕ × ℕ) ∈ μ.cells := by simpa using hcell
    have hc1 : ((i1, j) : ℕ × ℕ) ∈ μ.cells := by
      simpa using μ.up_left_mem hi.le (le_refl j) hcell
    rw [pairEntry_of_mem p.2.1 hc1] at heq ⊢
    rw [pairEntry_of_mem p.2.1 hc2] at heq
    by_contra hneg
    exact absurd (col_lt_of_isPositive p.2.1 p.2.2 hc1 hc2 (p.1.1.col_strict hi hcell) heq
      ((SuperLetter.isPositive_iff_not_isNegative _).2 hneg)) (lt_irrefl j)
  row_isPositive' := by
    intro i j1 j2 hj hcell heq
    have hc2 : ((i, j2) : ℕ × ℕ) ∈ μ.cells := by simpa using hcell
    have hc1 : ((i, j1) : ℕ × ℕ) ∈ μ.cells := by
      simpa using μ.up_left_mem (le_refl i) hj.le hcell
    rw [pairEntry_of_mem p.2.1 hc1] at heq ⊢
    rw [pairEntry_of_mem p.2.1 hc2] at heq
    rw [SuperLetter.isPositive_iff_not_isNegative]
    intro hneg
    exact absurd (col_le_of_isNegative p.2.1 p.2.2 hc1 hc2 (p.2.1.row_lt hj hcell) heq hneg)
      (by omega)
  outside' := fun h => pairEntry_of_notMem h

@[simp]
theorem coe_superTableauOfPair (p : SuperStdPair μ) :
    ⇑(superTableauOfPair p) = pairEntry p.1.1 p.1.2 :=
  rfl

/-! ### The canonical ordering of the cells of a super tableau -/

/-- The column of a cell, read in the direction the sign of its letter prescribes: forwards at a
positive letter and backwards at a negative one. The column enters as an integer precisely so that
the negative direction is available. -/
def superColKey (α : SuperLetter) (j : ℕ) : ℤ :=
  if α.IsNegative then -(j : ℤ) else (j : ℤ)

theorem superColKey_lt_iff_of_isPositive {α : SuperLetter} (h : α.IsPositive) (j j' : ℕ) :
    superColKey α j < superColKey α j' ↔ j < j' := by
  have hn : ¬α.IsNegative := (SuperLetter.isPositive_iff_not_isNegative α).1 h
  rw [superColKey, superColKey, ite_eq_right hn, ite_eq_right hn, Nat.cast_lt]

theorem superColKey_lt_iff_of_isNegative {α : SuperLetter} (h : α.IsNegative) (j j' : ℕ) :
    superColKey α j < superColKey α j' ↔ j' < j := by
  rw [superColKey, superColKey, ite_eq_left h, ite_eq_left h, neg_lt_neg_iff, Nat.cast_lt]

theorem superColKey_injective (α : SuperLetter) {j j' : ℕ}
    (h : superColKey α j = superColKey α j') : j = j' := by
  by_cases hn : α.IsNegative
  · rw [superColKey, superColKey, ite_eq_left hn, ite_eq_left hn, neg_inj, Nat.cast_inj] at h
    exact h
  · rw [superColKey, superColKey, ite_eq_right hn, ite_eq_right hn, Nat.cast_inj] at h
    exact h

/-- **The canonical key of a cell of a super tableau**: its letter, then its column read in the
direction the sign of the letter prescribes, then its row. The block analysis is exactly
that this key is a strict total order on the cells whose associated numbering is the unique
admissible `S`: inside a positive block the columns increase, inside a negative block they decrease
and ties are broken by the row. -/
def superCellKey (T : ℕ → ℕ → SuperLetter) (c : ℕ × ℕ) : SuperLetter ×ₗ (ℤ ×ₗ ℕ) :=
  toLex (T c.1 c.2, toLex (superColKey (T c.1 c.2) c.2, c.1))

theorem superCellKey_lt_iff (T : ℕ → ℕ → SuperLetter) (c c' : ℕ × ℕ) :
    superCellKey T c < superCellKey T c' ↔ T c.1 c.2 < T c'.1 c'.2 ∨
      (T c.1 c.2 = T c'.1 c'.2 ∧
        (superColKey (T c.1 c.2) c.2 < superColKey (T c'.1 c'.2) c'.2 ∨
          (superColKey (T c.1 c.2) c.2 = superColKey (T c'.1 c'.2) c'.2 ∧ c.1 < c'.1))) := by
  rw [superCellKey, superCellKey, Prod.Lex.toLex_lt_toLex, Prod.Lex.toLex_lt_toLex]

theorem superCellKey_injective (T : ℕ → ℕ → SuperLetter) :
    Function.Injective (superCellKey T) := by
  intro c c' h
  have h1 : T c.1 c.2 = T c'.1 c'.2 := congrArg (fun p => (ofLex p).1) h
  have h2 : superColKey (T c.1 c.2) c.2 = superColKey (T c'.1 c'.2) c'.2 :=
    congrArg (fun p => (ofLex (ofLex p).2).1) h
  have h3 : c.1 = c'.1 := congrArg (fun p => (ofLex (ofLex p).2).2) h
  rw [← h1] at h2
  exact Prod.ext h3 (superColKey_injective _ h2)

/-- **Two cells carrying the same positive letter are ordered by their columns.** With the same
letter the key compares the columns forwards, and two cells of one column cannot carry the same
positive letter, so the row never decides. -/
theorem col_lt_of_key_lt_of_isPositive (T : SuperYoungTableau μ) {c c' : ℕ × ℕ} (hc' : c' ∈ μ)
    (hk : superCellKey (⇑T) c < superCellKey (⇑T) c') (heq : T c.1 c.2 = T c'.1 c'.2)
    (hpos : (T c.1 c.2).IsPositive) : c.2 < c'.2 := by
  obtain ⟨i, j⟩ := c
  obtain ⟨i', j'⟩ := c'
  rw [superCellKey_lt_iff] at hk
  rcases hk with h1 | ⟨-, h2⟩
  · exact absurd heq (ne_of_lt h1)
  rw [← heq] at h2
  rcases h2 with h3 | ⟨h3, h4⟩
  · exact (superColKey_lt_iff_of_isPositive hpos j j').1 h3
  · have hcol : j = j' := superColKey_injective _ h3
    subst hcol
    exact absurd (T.col_isNegative h4 hc' heq)
      ((SuperLetter.isPositive_iff_not_isNegative _).1 hpos)

/-- **Two cells carrying the same negative letter are ordered by their columns, reversed.** -/
theorem col_le_of_key_lt_of_isNegative (T : SuperYoungTableau μ) {c c' : ℕ × ℕ}
    (hk : superCellKey (⇑T) c < superCellKey (⇑T) c') (heq : T c.1 c.2 = T c'.1 c'.2)
    (hneg : (T c.1 c.2).IsNegative) : c'.2 ≤ c.2 := by
  rw [superCellKey_lt_iff] at hk
  rcases hk with h1 | ⟨-, h2⟩
  · exact absurd heq (ne_of_lt h1)
  rw [← heq] at h2
  rcases h2 with h3 | ⟨h3, -⟩
  · exact le_of_lt ((superColKey_lt_iff_of_isNegative hneg c.2 c'.2).1 h3)
  · exact le_of_eq (superColKey_injective _ h3).symm

/-! ### The canonical numbering of the cells -/

/-- **The canonical value of a cell**: the number of cells whose key is smaller. -/
def superRank (μ : YoungDiagram) (T : ℕ → ℕ → SuperLetter) (c : ℕ × ℕ) : ℕ :=
  #{c' ∈ μ.cells | superCellKey T c' < superCellKey T c}

theorem superRank_lt_superRank_of_key_lt (T : ℕ → ℕ → SuperLetter) {c c' : ℕ × ℕ}
    (hc : c ∈ μ.cells) (h : superCellKey T c < superCellKey T c') :
    superRank μ T c < superRank μ T c' := by
  have hsub : {e ∈ μ.cells | superCellKey T e < superCellKey T c}
      ⊆ {e ∈ μ.cells | superCellKey T e < superCellKey T c'} := by
    intro e he
    rw [mem_filter] at he ⊢
    exact ⟨he.1, he.2.trans h⟩
  refine Finset.card_lt_card ((Finset.ssubset_iff_of_subset hsub).2 ⟨c, mem_filter.2 ⟨hc, h⟩, ?_⟩)
  rw [mem_filter]
  exact fun hcc => absurd hcc.2 (lt_irrefl _)

theorem superRank_lt_card (T : ℕ → ℕ → SuperLetter) {c : ℕ × ℕ} (hc : c ∈ μ.cells) :
    superRank μ T c < μ.card := by
  refine Finset.card_lt_card
    ((Finset.ssubset_iff_of_subset (Finset.filter_subset _ _)).2 ⟨c, hc, ?_⟩)
  rw [mem_filter]
  exact fun hcc => absurd hcc.2 (lt_irrefl _)

theorem superRank_lt_superRank_iff (T : ℕ → ℕ → SuperLetter) {c c' : ℕ × ℕ} (hc : c ∈ μ.cells)
    (hc' : c' ∈ μ.cells) :
    superRank μ T c < superRank μ T c' ↔ superCellKey T c < superCellKey T c' := by
  refine ⟨fun h => ?_, superRank_lt_superRank_of_key_lt T hc⟩
  rcases lt_trichotomy (superCellKey T c) (superCellKey T c') with hk | hk | hk
  · exact hk
  · exact absurd (congrArg (superRank μ T) (superCellKey_injective T hk)) (by omega)
  · exact absurd (superRank_lt_superRank_of_key_lt T hc' hk) (by omega)

theorem superRank_injOn (T : ℕ → ℕ → SuperLetter) : Set.InjOn (superRank μ T) ↑μ.cells := by
  intro c hc c' hc' h
  refine superCellKey_injective T ?_
  rcases lt_trichotomy (superCellKey T c) (superCellKey T c') with hk | hk | hk
  · exact absurd ((superRank_lt_superRank_iff T (by simpa using hc) (by simpa using hc')).2 hk)
      (by omega)
  · exact hk
  · exact absurd ((superRank_lt_superRank_iff T (by simpa using hc') (by simpa using hc)).2 hk)
      (by omega)

/-- **The canonical numbering is a bijection from the cells onto the values**, which is what makes
it a standard tableau. -/
theorem superRank_bijOn (T : ℕ → ℕ → SuperLetter) :
    Set.BijOn (superRank μ T) ↑μ.cells ↑(range μ.card) := by
  have himg : Finset.image (superRank μ T) μ.cells = range μ.card := by
    refine Finset.eq_of_subset_of_card_le (fun a ha => ?_) ?_
    · obtain ⟨c, hc, rfl⟩ := Finset.mem_image.1 ha
      exact mem_range.2 (superRank_lt_card T hc)
    · rw [Finset.card_range, Finset.card_image_of_injOn (superRank_injOn T)]
  refine ⟨fun c hc => ?_, superRank_injOn T, fun a ha => ?_⟩
  · simpa using superRank_lt_card T (by simpa using hc)
  · rw [Finset.mem_coe, ← himg, Finset.mem_image] at ha
    obtain ⟨c, hc, rfl⟩ := ha
    exact ⟨c, by simpa using hc, rfl⟩

theorem superRank_cells_bijective (T : SuperYoungTableau μ) :
    Function.Bijective fun c : ↥μ.cells =>
      (⟨superRank μ (⇑T) (c : ℕ × ℕ), superRank_lt_card (⇑T) c.2⟩ : Fin μ.card) := by
  refine (Fintype.bijective_iff_injective_and_card _).2 ⟨fun c c' h => ?_, ?_⟩
  · exact Subtype.ext (superRank_injOn (⇑T) (by simp) (by simp)
      (show superRank μ (⇑T) (c : ℕ × ℕ) = superRank μ (⇑T) (c' : ℕ × ℕ) from congrArg Fin.val h))
  · rw [Fintype.card_coe, Fintype.card_fin]

/-! ### The canonical standard tableau and word of a super tableau -/

/-- **The canonical standard tableau of a super tableau**: the cells numbered by their key. -/
def superStdTableau (T : SuperYoungTableau μ) : SemistandardYoungTableau μ where
  entry i j := if (i, j) ∈ μ then superRank μ (⇑T) (i, j) else 0
  row_weak' := by
    intro i j1 j2 hj hcell
    have hc1 : ((i, j1) : ℕ × ℕ) ∈ μ := μ.up_left_mem (le_refl i) hj.le hcell
    rw [ite_eq_left hc1, ite_eq_left hcell]
    refine le_of_lt (superRank_lt_superRank_of_key_lt _ (by simpa using hc1) ?_)
    rw [superCellKey_lt_iff]
    rcases lt_or_eq_of_le (T.row_weak hj hcell) with h | h
    · exact Or.inl h
    · refine Or.inr ⟨h, Or.inl ?_⟩
      rw [show T (i, j2).1 (i, j2).2 = T (i, j1).1 (i, j1).2 from h.symm,
        superColKey_lt_iff_of_isPositive (T.row_isPositive hj hcell h)]
      exact hj
  col_strict' := by
    intro i1 i2 j hi hcell
    have hc1 : ((i1, j) : ℕ × ℕ) ∈ μ := μ.up_left_mem hi.le (le_refl j) hcell
    rw [ite_eq_left hc1, ite_eq_left hcell]
    refine superRank_lt_superRank_of_key_lt _ (by simpa using hc1) ?_
    rw [superCellKey_lt_iff]
    rcases lt_or_eq_of_le (T.col_weak hi hcell) with h | h
    · exact Or.inl h
    · exact Or.inr ⟨h, Or.inr ⟨by rw [show T (i2, j).1 (i2, j).2 = T (i1, j).1 (i1, j).2 from
        h.symm], hi⟩⟩
  zeros' := fun h => ite_eq_right h

theorem superStdTableau_apply (T : SuperYoungTableau μ) {c : ℕ × ℕ} (hc : c ∈ μ) :
    superStdTableau T c.1 c.2 = superRank μ (⇑T) c :=
  ite_eq_left hc

/-- The canonical standard tableau of a super tableau is standard. -/
theorem isStandard_superStdTableau (T : SuperYoungTableau μ) :
    IsStandard (superStdTableau T) :=
  (superRank_bijOn (⇑T)).congr fun c hc => (superStdTableau_apply T (by simpa using hc)).symm

/-- The cell of a super tableau carrying a given canonical value. -/
noncomputable def superStdCell (T : SuperYoungTableau μ) (i : Fin μ.card) : ℕ × ℕ :=
  ((Equiv.ofBijective _ (superRank_cells_bijective T)).symm i : ↥μ.cells)

theorem superStdCell_mem (T : SuperYoungTableau μ) (i : Fin μ.card) :
    superStdCell T i ∈ μ.cells :=
  ((Equiv.ofBijective _ (superRank_cells_bijective T)).symm i).2

@[simp]
theorem superRank_superStdCell (T : SuperYoungTableau μ) (i : Fin μ.card) :
    superRank μ (⇑T) (superStdCell T i) = (i : ℕ) :=
  congrArg Fin.val
    ((Equiv.ofBijective _ (superRank_cells_bijective T)).apply_symm_apply i)

theorem superStdCell_superRank (T : SuperYoungTableau μ) {c : ℕ × ℕ} (hc : c ∈ μ.cells) :
    superStdCell T ⟨superRank μ (⇑T) c, superRank_lt_card (⇑T) hc⟩ = c := by
  have h : (Equiv.ofBijective _ (superRank_cells_bijective T)) ⟨c, hc⟩
      = ⟨superRank μ (⇑T) c, superRank_lt_card (⇑T) hc⟩ := rfl
  rw [superStdCell, ← h, Equiv.symm_apply_apply]

/-- **The canonical super word of a super tableau**: its letters listed in the canonical order of
the cells. -/
noncomputable def superStdWord (T : SuperYoungTableau μ) (i : Fin μ.card) : SuperLetter :=
  T (superStdCell T i).1 (superStdCell T i).2

theorem superStdWord_eq (T : SuperYoungTableau μ) {a : ℕ} (ha : a < μ.card) {c : ℕ × ℕ}
    (hc : c ∈ μ.cells) (hval : superRank μ (⇑T) c = a) :
    superStdWord T ⟨a, ha⟩ = T c.1 c.2 := by
  subst hval
  rw [superStdWord, superStdCell_superRank T hc]

theorem superCellKey_superStdCell_lt_iff (T : SuperYoungTableau μ) (i i' : Fin μ.card) :
    superCellKey (⇑T) (superStdCell T i) < superCellKey (⇑T) (superStdCell T i') ↔
      (i : ℕ) < (i' : ℕ) := by
  rw [← superRank_lt_superRank_iff (⇑T) (superStdCell_mem T i) (superStdCell_mem T i'),
    superRank_superStdCell, superRank_superStdCell]

theorem monotone_superStdWord (T : SuperYoungTableau μ) : Monotone (superStdWord T) := by
  intro i i' h
  rcases eq_or_lt_of_le h with rfl | hlt
  · exact le_rfl
  · have hk := (superCellKey_superStdCell_lt_iff T i i').2 hlt
    rw [superCellKey_lt_iff] at hk
    rcases hk with h1 | ⟨h1, -⟩
    · exact le_of_lt h1
    · exact le_of_eq h1

/-- **The canonical pair of a super tableau is admissible**: the word increases weakly, and the two
repetition clauses are the two cases of the canonical key — a repeated positive letter has
increasing columns, so its step is not a descent of the canonical tableau, and a repeated negative
letter has
weakly decreasing columns, so its step is one. -/
theorem isSuperAdmissibleWord_superStdWord (T : SuperYoungTableau μ) :
    IsSuperAscendingWord μ.card (sytDescentSet (superStdTableau T)) (superStdWord T) := by
  have hval : ∀ i : Fin μ.card,
      superStdTableau T (superStdCell T i).1 (superStdCell T i).2 = (i : ℕ) := by
    intro i
    rw [superStdTableau_apply T (by simpa using superStdCell_mem T i), superRank_superStdCell]
  refine ⟨fun k l hkl => monotone_superStdWord T (Fin.le_def.2 (by omega)), ?_, ?_⟩
  · intro k l hkl heq hpos hmem
    obtain ⟨-, -, hdes⟩ := mem_sytDescentSet.1 hmem
    have hle := hdes _ (superStdCell_mem T l) _ (superStdCell_mem T k) (hval l)
      (by rw [hval k]; omega)
    have hk := (superCellKey_superStdCell_lt_iff T k l).2 (by omega)
    exact absurd (col_lt_of_key_lt_of_isPositive T
      (by simpa using superStdCell_mem T l) hk heq hpos) (by omega)
  · intro k l hkl heq hneg
    refine mem_sytDescentSet.2 ⟨by omega, l.isLt, fun e he e' he' hea hea' => ?_⟩
    have hel : e = superStdCell T l := (isStandard_superStdTableau T).injOn
      (by simpa using he) (by simpa using superStdCell_mem T l)
      (show superStdTableau T e.1 e.2
        = superStdTableau T (superStdCell T l).1 (superStdCell T l).2 by rw [hea, hval l])
    have hek : e' = superStdCell T k := (isStandard_superStdTableau T).injOn
      (by simpa using he') (by simpa using superStdCell_mem T k)
      (show superStdTableau T e'.1 e'.2
        = superStdTableau T (superStdCell T k).1 (superStdCell T k).2 by rw [hea', hval k]; omega)
    rw [hel, hek]
    exact col_le_of_key_lt_of_isNegative T
      ((superCellKey_superStdCell_lt_iff T k l).2 (by omega)) heq hneg

/-- The map sends the canonical pair of a super tableau back to that tableau. -/
theorem superTableauOfPair_canonical (T : SuperYoungTableau μ)
    (h1 : IsStandard (superStdTableau T))
    (h2 : IsSuperAscendingWord μ.card (sytDescentSet (superStdTableau T)) (superStdWord T)) :
    superTableauOfPair ⟨(superStdTableau T, superStdWord T), h1, h2⟩ = T := by
  refine SuperYoungTableau.ext fun i j => ?_
  by_cases hc : ((i, j) : ℕ × ℕ) ∈ μ
  · rw [show ⇑(superTableauOfPair ⟨(superStdTableau T, superStdWord T), h1, h2⟩)
        = pairEntry (superStdTableau T) (superStdWord T) from rfl,
      pairEntry_of_mem h1 (show ((i, j) : ℕ × ℕ) ∈ μ.cells by simpa using hc)]
    exact superStdWord_eq T _ (by simpa using hc) (superStdTableau_apply T hc).symm
  · rw [T.outside hc]
    exact pairEntry_of_notMem hc

/-! ### The comparisons of an admissible pair are the canonical ones -/

/-- **An admissible pair orders the cells by the canonical key.** This is the uniqueness half of the
proof: the value of `S` at a cell determines, and is determined by, the key of that
cell. -/
theorem superCellKey_lt_of_lt (p : SuperStdPair μ) {c c' : ℕ × ℕ} (hc : c ∈ μ.cells)
    (hc' : c' ∈ μ.cells) (hlt : p.1.1 c.1 c.2 < p.1.1 c'.1 c'.2) :
    superCellKey (⇑(superTableauOfPair p)) c < superCellKey (⇑(superTableauOfPair p)) c' := by
  have hTc : (superTableauOfPair p) c.1 c.2 = p.1.2 ⟨p.1.1 c.1 c.2, p.2.1.lt_card hc⟩ :=
    pairEntry_of_mem p.2.1 hc
  have hTc' : (superTableauOfPair p) c'.1 c'.2 = p.1.2 ⟨p.1.1 c'.1 c'.2, p.2.1.lt_card hc'⟩ :=
    pairEntry_of_mem p.2.1 hc'
  rw [superCellKey_lt_iff]
  rcases lt_or_eq_of_le (show (superTableauOfPair p) c.1 c.2 ≤ (superTableauOfPair p) c'.1 c'.2 from
    by rw [hTc, hTc']; exact p.2.2.monotone (Fin.mk_le_mk.2 hlt.le)) with h | h
  · exact Or.inl h
  refine Or.inr ⟨h, ?_⟩
  have heq : p.1.2 ⟨p.1.1 c.1 c.2, p.2.1.lt_card hc⟩
      = p.1.2 ⟨p.1.1 c'.1 c'.2, p.2.1.lt_card hc'⟩ := by rw [← hTc, ← hTc', h]
  by_cases hneg : (p.1.2 ⟨p.1.1 c.1 c.2, p.2.1.lt_card hc⟩).IsNegative
  · have hcol := col_le_of_isNegative p.2.1 p.2.2 hc hc' hlt heq hneg
    rcases Nat.lt_or_ge c'.2 c.2 with h1 | h1
    · refine Or.inl ?_
      rw [show (superTableauOfPair p) c'.1 c'.2 = (superTableauOfPair p) c.1 c.2 from h.symm,
        superColKey_lt_iff_of_isNegative (by rw [hTc]; exact hneg)]
      exact h1
    · refine Or.inr ⟨by rw [show (superTableauOfPair p) c'.1 c'.2
        = (superTableauOfPair p) c.1 c.2 from h.symm, show c.2 = c'.2 from by omega], ?_⟩
      rcases Nat.lt_trichotomy c.1 c'.1 with h2 | h2 | h2
      · exact h2
      · exfalso
        rw [show c = c' from Prod.ext h2 (by omega)] at hlt
        omega
      · exfalso
        have hstr : p.1.1 c'.1 c.2 < p.1.1 c.1 c.2 := p.1.1.col_strict h2 (by simpa using hc)
        rw [show c'.2 = c.2 from by omega] at hlt
        omega
  · have hpos : (p.1.2 ⟨p.1.1 c.1 c.2, p.2.1.lt_card hc⟩).IsPositive :=
      (SuperLetter.isPositive_iff_not_isNegative _).2 hneg
    refine Or.inl ?_
    rw [show (superTableauOfPair p) c'.1 c'.2 = (superTableauOfPair p) c.1 c.2 from h.symm,
      superColKey_lt_iff_of_isPositive (by rw [hTc]; exact hpos)]
    exact col_lt_of_isPositive p.2.1 p.2.2 hc hc' hlt heq hpos

/-- **The value of an admissible pair at a cell is the canonical one**: the two bijections from the
cells onto the values induce the same comparisons, so they are equal, by
`HJO.Sym.eq_of_lt_iff_lt`. -/
theorem entry_eq_superRank (p : SuperStdPair μ) {c : ℕ × ℕ} (hc : c ∈ μ.cells) :
    p.1.1 c.1 c.2 = superRank μ (⇑(superTableauOfPair p)) c := by
  have hcard : Fintype.card ↥μ.cells = μ.card := by rw [Fintype.card_coe]
  set F : ↥μ.cells → Fin μ.card := fun d =>
    ⟨p.1.1 (d : ℕ × ℕ).1 (d : ℕ × ℕ).2, p.2.1.lt_card d.2⟩ with hF
  set G : ↥μ.cells → Fin μ.card := fun d =>
    ⟨superRank μ (⇑(superTableauOfPair p)) (d : ℕ × ℕ),
      superRank_lt_card (⇑(superTableauOfPair p)) d.2⟩ with hG
  have hFbij : Function.Bijective F := by
    refine (Fintype.bijective_iff_injective_and_card F).2
      ⟨fun d d' h => ?_, by rw [hcard, Fintype.card_fin]⟩
    exact Subtype.ext (p.2.1.injOn (by simp) (by simp)
      (show p.1.1 (d : ℕ × ℕ).1 (d : ℕ × ℕ).2 = p.1.1 (d' : ℕ × ℕ).1 (d' : ℕ × ℕ).2 from
        congrArg Fin.val h))
  have hGbij : Function.Bijective G := superRank_cells_bijective (superTableauOfPair p)
  have hkey : ∀ d d' : ↥μ.cells, F d < F d' ↔ G d < G d' := by
    intro d d'
    rw [hF, hG, Fin.lt_def, Fin.lt_def]
    rw [superRank_lt_superRank_iff _ d.2 d'.2]
    refine ⟨fun h => superCellKey_lt_of_lt p d.2 d'.2 h, fun h => ?_⟩
    rcases lt_trichotomy (p.1.1 (d : ℕ × ℕ).1 (d : ℕ × ℕ).2)
      (p.1.1 (d' : ℕ × ℕ).1 (d' : ℕ × ℕ).2) with h1 | h1 | h1
    · exact h1
    · exact absurd (congrArg (superCellKey (⇑(superTableauOfPair p)))
        (p.2.1.injOn (by simp) (by simp) h1)) (ne_of_lt h)
    · exact absurd (superCellKey_lt_of_lt p d'.2 d.2 h1) (asymm h)
  set e : ↥μ.cells ≃ Fin μ.card := Fintype.equivFinOfCardEq hcard with he
  have hcomp := eq_of_lt_iff_lt (hFbij.comp e.symm.bijective) (hGbij.comp e.symm.bijective)
    fun i i' => hkey (e.symm i) (e.symm i')
  have hFG : F = G := by
    funext d
    have := congrFun hcomp (e d)
    simpa using this
  exact congrArg Fin.val (congrFun hFG ⟨c, hc⟩)

theorem superStdTableau_superTableauOfPair (p : SuperStdPair μ) :
    superStdTableau (superTableauOfPair p) = p.1.1 := by
  refine SemistandardYoungTableau.ext fun i j => ?_
  by_cases hc : ((i, j) : ℕ × ℕ) ∈ μ
  · rw [superStdTableau_apply _ hc, ← entry_eq_superRank p (by simpa using hc)]
  · rw [(superStdTableau (superTableauOfPair p)).zeros hc, p.1.1.zeros hc]

theorem superStdWord_superTableauOfPair (p : SuperStdPair μ) :
    superStdWord (superTableauOfPair p) = p.1.2 := by
  funext i
  obtain ⟨c, hc, hcv⟩ := p.2.1.exists_eq i.isLt
  have hrank : superRank μ (⇑(superTableauOfPair p)) c = (i : ℕ) := by
    rw [← entry_eq_superRank p hc, hcv]
  rw [superStdWord_eq _ i.isLt hc hrank,
    show ⇑(superTableauOfPair p) = pairEntry p.1.1 p.1.2 from rfl,
    pairEntry_of_mem p.2.1 hc]
  exact congrArg p.1.2 (Fin.ext hcv)

/-! ### The bijection -/

/-- **Super tableaux are the standardised admissible pairs.** The map
sending an admissible pair `(S, v)` to the filling `c ↦ v_{S(c)}` is a bijection from the pairs onto
the super tableaux of the diagram.

Surjectivity is the canonical pair of a super tableau: its cells numbered by
`HJO.Sym.superCellKey` — letter, then column forwards at a positive letter and backwards at a
negative one, then row — and its letters listed in that order. Injectivity is the uniqueness half of
the block analysis: an admissible pair orders the cells by exactly that key
(`HJO.Sym.superCellKey_lt_of_lt`), and two bijections from the cells onto the values with the same
comparisons are equal.

The hypothesis `n ≥ 1` is not needed: at `n = 0` both sides are singletons. -/
@[hjo "lem_cm_super_tableau_std"]
theorem superTableauOfPair_bijective (μ : YoungDiagram) :
    Function.Bijective (superTableauOfPair (μ := μ)) := by
  refine ⟨fun p p' h => Subtype.ext (Prod.ext ?_ ?_), fun T => ⟨⟨(superStdTableau T,
    superStdWord T), isStandard_superStdTableau T, isSuperAdmissibleWord_superStdWord T⟩,
    superTableauOfPair_canonical T (isStandard_superStdTableau T)
      (isSuperAdmissibleWord_superStdWord T)⟩⟩
  · rw [← superStdTableau_superTableauOfPair p, ← superStdTableau_superTableauOfPair p', h]
  · rw [← superStdWord_superTableauOfPair p, ← superStdWord_superTableauOfPair p', h]

end HJO.Sym
