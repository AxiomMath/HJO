/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.CarlssonMellit.SuperSchurGessel
public import HJO.Classical.SchurBasis
public import HJO.SignExtraction.Basic
public meta import HJO.Attr

/-! # Gessel's fundamental expansion of a Schur series

The Schur series of a Young diagram is the sum of the Gessel fundamentals at the descent sets of
its standard tableaux, `sch(D) = ∑_{S ∈ SYT(D)} F_{n,Des(S)}`. This is
`HJO.Sym.schurSeries_eq_sum_gessel`, and it is not a quotation of Gessel
but the *restriction to positive letters* of `HJO.Sym.superTableauOfPair_bijective`.

That restriction is made here, and it is the place where the super tableaux of
`HJO/CarlssonMellit/SuperTableaux.lean` are identified with `Mathlib`'s semistandard tableaux:
`HJO.Sym.superOfSsyt` and `HJO.Sym.ssytOfSuper` are mutually inverse bijections between
`SemistandardYoungTableau D` and the super tableaux all of whose letters are positive, so
`SSYT(D)` needs no second definition.

## Main definitions

* `HJO.Sym.superOfSsyt`, `HJO.Sym.ssytOfSuper`: the identification of `SSYT(D)` with the positive
  part of `SSYT^±(D)`.
* `HJO.Sym.superWordOfWord`: the identification of a word of natural numbers with a super word of
  positive letters.
* `HJO.Sym.ssytStd`, `HJO.Sym.ssytWord`: the standardisation of a semistandard tableau and the
  weakly increasing word it factors through.
* `HJO.Sym.HasAscendingWord`: the condition under which a standard tableau contributes a given
  monomial, namely that some `Des(S)`-ascending word carries that exponent vector.

## Main results

* `HJO.Sym.isSuperAscendingWord_superWordOfWord`: a super word of positive letters is super
  ascending exactly when the word of its absolute values is ascending.
* `HJO.Sym.bijOn_ssytStd`: the standardisation is a bijection from the semistandard tableaux of a
  given content onto the standard tableaux whose descent set admits the corresponding word. This
  is the counting content of `HJO.Sym.schurSeries_eq_sum_gessel`.
* `HJO.Sym.schurSeries_eq_sum_gessel`.

## Implementation notes

*Only the positive letters of the super alphabet are used, and they are used through their absolute
values.* `HJO.Sym.SuperLetter.lt_iff_absVal_lt_of_isPositive` and its weak companion say that the
super order restricts to the order of the natural numbers on the positive letters, and
`HJO.Sym.SuperLetter.eq_mk_false_of_isPositive` says that a positive letter *is* the letter built
from its absolute value. Those three facts are the whole of the identification of
`(a, 1)` with `a`; everything else about the alphabet is untouched.

*The restriction of `HJO.Sym.SuperYoungTableau` to positive values is `Mathlib`'s
`SemistandardYoungTableau`, and that is proved by exhibiting the two maps.* Along a row weak
increase of the letters is weak increase of the absolute values; down a column the letters increase
weakly and cannot repeat, since a letter repeated in a column is negative, so the absolute values
increase *strictly*; and the clause forbidding a repeated negative letter in a row is vacuous. The
converse readings are the same three observations run backwards, which is why `HJO.Sym.superOfSsyt`
and `HJO.Sym.ssytOfSuper` are inverse.

*The proof is a count, not an identity of sums of monomials.* `HJO.Sym.schurSeries` is written by
its coefficients — the coefficient at `x^α` is the Kostka number `K_D(α)`, a `Set.ncard` — and
`HJO.ParkingFunctions.gessel` likewise, its coefficient at `x^α` being `1` exactly when some
`Des(S)`-ascending word has exponent vector `α` and `0` otherwise
(`HJO.ParkingFunctions.coeff_wordExponent_gessel`). So the expansion is the statement that
standardisation is a bijection
`{T ∈ SSYT(D) : ct(T) = α} → {S ∈ SYT(D) : α is the exponent vector of a Des(S)-ascending word}`,
which is `HJO.Sym.bijOn_ssytStd`. Its three halves are exactly the three steps of the standard
argument: the image of a tableau is standard and its word is ascending, the word is determined by
`α` alone (`HJO.Sym.eq_of_monotone_of_wordExponent_eq`) so the bijection of
`HJO.Sym.superTableauOfPair_bijective` is injective on a fixed content, and every admissible
`(S, u)` is filled back by that same bijection.

*No case distinction on the total degree of the monomial is needed.* A word of length `n` has an
exponent vector of total degree `n`, so at a monomial of any other degree the condition
`HJO.Sym.HasAscendingWord` fails for every `S` and the set of tableaux of that content is empty;
both sides are then `0` with no separate argument.

*The `n ≥ 1` is dropped.* At `n = 0` the diagram is empty, each side is `1`, and no step
of the proof uses positivity — `HJO.Sym.superTableauOfPair_bijective` is stated without it for the
same reason.

*`SYT(D)` is given a `Fintype` instance here*, since the sum runs over it: a standard
tableau is determined by its values on the cells and each value is below the number of cells, which
is `HJO.Sym.instFiniteSYT`.

## References

E. Carlsson and A. Mellit, *A proof of the shuffle conjecture*, J. Amer. Math. Soc. **31** (2018)
661--697, Section 3.
-/

@[expose] public section

open Finset

namespace HJO.Sym

/-! ### The positive letters are the natural numbers -/

/-- **The super order restricts to the order of the natural numbers on the positive letters**: a
letter lies below a *positive* letter exactly when its absolute value is smaller, the tie-break of
`HJO.Sym.SuperLetter.lt_iff` needing a negative upper letter to fire. -/
theorem SuperLetter.lt_iff_absVal_lt_of_isPositive {α β : SuperLetter} (hb : β.IsPositive) :
    α < β ↔ α.absVal < β.absVal := by
  rw [SuperLetter.lt_iff]
  exact or_iff_left fun h =>
    absurd h.2.2 ((SuperLetter.isPositive_iff_not_isNegative β).1 hb)

/-- The weak form of the restriction: a *positive* letter lies weakly below a letter exactly when
its absolute value does. -/
theorem SuperLetter.le_iff_absVal_le_of_isPositive {α β : SuperLetter} (ha : α.IsPositive) :
    α ≤ β ↔ α.absVal ≤ β.absVal := by
  rw [← not_lt, ← not_lt, SuperLetter.lt_iff_absVal_lt_of_isPositive ha]

/-- **A positive letter is the letter built from its absolute value**: the
identification of the positive letter `(a, 1)` with `a`, read on a letter. -/
theorem SuperLetter.eq_mk_false_of_isPositive {α : SuperLetter} (h : α.IsPositive) :
    α = SuperLetter.mk α.absVal false :=
  SuperLetter.ext rfl h

/-- Two positive letters of the same absolute value are equal. -/
theorem SuperLetter.eq_of_absVal_eq_of_isPositive {α β : SuperLetter} (ha : α.IsPositive)
    (hb : β.IsPositive) (h : α.absVal = β.absVal) : α = β :=
  SuperLetter.ext h (ha.trans hb.symm)

/-- Two positive letters are compared by the natural numbers they come from. -/
theorem SuperLetter.mk_false_le_mk_false {a b : ℕ} :
    SuperLetter.mk a false ≤ SuperLetter.mk b false ↔ a ≤ b :=
  SuperLetter.le_iff_absVal_le_of_isPositive (SuperLetter.sign_mk a false)

/-- Two positive letters are equal exactly when the natural numbers they come from are. -/
theorem SuperLetter.mk_false_eq_mk_false {a b : ℕ} :
    SuperLetter.mk a false = SuperLetter.mk b false ↔ a = b :=
  ⟨fun h => congrArg SuperLetter.absVal h, fun h => by rw [h]⟩

/-! ### Semistandard tableaux are the super tableaux with positive letters -/

variable {μ : YoungDiagram}

/-- **The super tableau of a semistandard tableau**: the same filling read in positive letters.
Weak increase along a row is weak increase of the letters; two cells of one column carry different
letters because the entries increase strictly down a column, so the prohibition of a repeated
positive letter in a column holds vacuously; and a letter repeated in a row is positive because
every letter is. -/
def superOfSsyt (T : SemistandardYoungTableau μ) : SuperYoungTableau μ where
  entry i j := SuperLetter.mk (T i j) false
  row_weak' := by
    intro i j1 j2 hj hcell
    rw [SuperLetter.mk_false_le_mk_false]
    exact T.row_weak hj hcell
  col_weak' := by
    intro i1 i2 j hi hcell
    rw [SuperLetter.mk_false_le_mk_false]
    exact (T.col_strict hi hcell).le
  col_isNegative' := by
    intro i1 i2 j hi hcell heq
    exact absurd (SuperLetter.mk_false_eq_mk_false.1 heq) (ne_of_lt (T.col_strict hi hcell))
  row_isPositive' := by
    intro i j1 j2 _ _ _
    exact SuperLetter.sign_mk _ _
  outside' := by
    intro i j h
    rw [T.zeros h]

/-- The letter the super tableau of a semistandard tableau puts in a cell. -/
@[simp]
theorem superOfSsyt_apply (T : SemistandardYoungTableau μ) (i j : ℕ) :
    superOfSsyt T i j = SuperLetter.mk (T i j) false :=
  rfl

/-- Every letter of the super tableau of a semistandard tableau is positive. -/
theorem isPositive_superOfSsyt (T : SemistandardYoungTableau μ) (i j : ℕ) :
    (superOfSsyt T i j).IsPositive :=
  SuperLetter.sign_mk _ _

/-- A semistandard tableau is determined by the super tableau it gives. -/
theorem superOfSsyt_injective : Function.Injective (superOfSsyt (μ := μ)) := fun _ _ h =>
  SemistandardYoungTableau.ext fun i j =>
    congrArg SuperLetter.absVal (congrFun (DFunLike.congr_fun h i) j)

/-- **The semistandard tableau of a super tableau whose letters are all positive**: the absolute
values. Weak increase along a row is weak increase of the absolute values; down a column the
letters increase weakly and cannot repeat, a letter repeated in a column being negative, so the
absolute values increase strictly. -/
def ssytOfSuper (T : SuperYoungTableau μ) (h : ∀ i j : ℕ, (T i j).IsPositive) :
    SemistandardYoungTableau μ where
  entry i j := (T i j).absVal
  row_weak' := by
    intro i j1 j2 hj hcell
    rw [← SuperLetter.le_iff_absVal_le_of_isPositive (h i j1)]
    exact T.row_weak hj hcell
  col_strict' := by
    intro i1 i2 j hi hcell
    refine lt_of_le_of_ne
      ((SuperLetter.le_iff_absVal_le_of_isPositive (h i1 j)).1 (T.col_weak hi hcell)) fun heq => ?_
    exact absurd (T.col_isNegative hi hcell
        (SuperLetter.eq_of_absVal_eq_of_isPositive (h i1 j) (h i2 j) heq))
      ((SuperLetter.isPositive_iff_not_isNegative _).1 (h i1 j))
  zeros' := by
    intro i j hij
    rw [T.outside hij]
    exact SuperLetter.absVal_mk 0 false

/-- The entry the semistandard tableau of a positive super tableau puts in a cell. -/
@[simp]
theorem ssytOfSuper_apply (T : SuperYoungTableau μ) (h : ∀ i j : ℕ, (T i j).IsPositive)
    (i j : ℕ) : ssytOfSuper T h i j = (T i j).absVal :=
  rfl

/-- **The two identifications are mutually inverse**, in the direction that starts from a
semistandard tableau. -/
theorem ssytOfSuper_superOfSsyt (T : SemistandardYoungTableau μ) :
    ssytOfSuper (superOfSsyt T) (isPositive_superOfSsyt T) = T :=
  SemistandardYoungTableau.ext fun _ _ => rfl

/-- **The two identifications are mutually inverse**, in the direction that starts from a super
tableau with positive letters. -/
theorem superOfSsyt_ssytOfSuper (T : SuperYoungTableau μ)
    (h : ∀ i j : ℕ, (T i j).IsPositive) : superOfSsyt (ssytOfSuper T h) = T :=
  SuperYoungTableau.ext fun i j => (SuperLetter.eq_mk_false_of_isPositive (h i j)).symm

/-! ### Words of positive letters are words of natural numbers -/

/-- **The super word of a word of natural numbers**: each letter read as a positive letter. -/
def superWordOfWord {n : ℕ} (u : Fin n → ℕ) : Fin n → SuperLetter :=
  fun k => SuperLetter.mk (u k) false

/-- Every letter of the super word of a word of natural numbers is positive. -/
theorem isPositive_superWordOfWord {n : ℕ} (u : Fin n → ℕ) (k : Fin n) :
    (superWordOfWord u k).IsPositive :=
  SuperLetter.sign_mk _ _

/-- **A super word of positive letters is super ascending exactly when the word of its absolute
values is ascending**: the weak increase of `HJO.Sym.superFundamental` is the weak increase of
`HJO.Sym.IsAscendingWord`, the clause on a repeated positive letter is the strict increase at a step
of the step set, and the clause on a repeated negative letter is vacuous. -/
theorem isSuperAscendingWord_superWordOfWord {n : ℕ} {S : Finset ℕ} {u : Fin n → ℕ} :
    IsSuperAscendingWord n S (superWordOfWord u) ↔ IsAscendingWord n S u := by
  constructor
  · intro h
    refine ⟨monotone_of_le_succ fun k l hkl =>
      SuperLetter.mk_false_le_mk_false.1 (h.le_of_step k l hkl), fun k l hkl hmem => ?_⟩
    refine lt_of_le_of_ne (SuperLetter.mk_false_le_mk_false.1 (h.le_of_step k l hkl))
      fun heq => ?_
    exact h.notMem_of_isPositive k l hkl (SuperLetter.mk_false_eq_mk_false.2 heq)
      (isPositive_superWordOfWord u k) hmem
  · intro h
    refine ⟨fun k l hkl => SuperLetter.mk_false_le_mk_false.2
      (h.monotone (Fin.le_def.2 (by omega))), fun k l hkl heq _ hmem => ?_,
      fun k l _ _ hneg => ?_⟩
    · exact absurd (SuperLetter.mk_false_eq_mk_false.1 heq)
        (ne_of_lt (h.lt_of_mem k l hkl hmem))
    · exact absurd hneg
        ((SuperLetter.isPositive_iff_not_isNegative _).1 (isPositive_superWordOfWord u k))

/-! ### The content of a tableau filled from a word -/

/-- **The content of a tableau read off a word along a standard tableau**: if the entry of a cell is
the letter of the word at the value the standard tableau gives that cell, then the multidegree of
the tableau is the exponent vector of the word. The values of a standard tableau run over the
positions once each, so the two sums of unit vectors are one sum reindexed. -/
theorem wt_eq_wordExponent {S : SemistandardYoungTableau μ} (hS : IsStandard S)
    {T : SemistandardYoungTableau μ} {u : Fin μ.card → ℕ}
    (hT : ∀ (c : ℕ × ℕ) (hc : c ∈ μ.cells), T c.1 c.2 = u ⟨S c.1 c.2, hS.lt_card hc⟩) :
    T.wt = wordExponent u := by
  have hbij : Function.Bijective fun c : ↥μ.cells =>
      (⟨S (c : ℕ × ℕ).1 (c : ℕ × ℕ).2, hS.lt_card c.2⟩ : Fin μ.card) := by
    refine (Fintype.bijective_iff_injective_and_card _).2 ⟨fun c c' h => ?_, ?_⟩
    · exact Subtype.ext (hS.injOn (by simp) (by simp) (congrArg Fin.val h))
    · rw [Fintype.card_coe, Fintype.card_fin]
  rw [SemistandardYoungTableau.wt, wordExponent,
    ← Finset.sum_coe_sort μ.cells fun c : ℕ × ℕ => Finsupp.single (T c.1 c.2) 1]
  exact Fintype.sum_bijective _ hbij _ _ fun c => by rw [hT (c : ℕ × ℕ) c.2]

/-! ### The standardisation of a semistandard tableau -/

/-- **The standardisation of a semistandard tableau**: the canonical standard tableau of the super
tableau it gives, that is its cells numbered by their entry and then by their column. -/
def ssytStd (T : SemistandardYoungTableau μ) : SYT μ :=
  ⟨superStdTableau (superOfSsyt T), isStandard_superStdTableau _⟩

/-- The standardisation of a semistandard tableau, as a semistandard tableau. -/
theorem coe_ssytStd (T : SemistandardYoungTableau μ) :
    (ssytStd T).1 = superStdTableau (superOfSsyt T) :=
  rfl

/-- **The word of a semistandard tableau**: its entries listed in the canonical order of the cells,
that is the absolute values of the canonical super word. -/
noncomputable def ssytWord (T : SemistandardYoungTableau μ) (k : Fin μ.card) : ℕ :=
  (superStdWord (superOfSsyt T) k).absVal

/-- The canonical super word of the super tableau of a semistandard tableau consists of positive
letters. -/
theorem isPositive_superStdWord_superOfSsyt (T : SemistandardYoungTableau μ) (k : Fin μ.card) :
    (superStdWord (superOfSsyt T) k).IsPositive :=
  isPositive_superOfSsyt T _ _

/-- The canonical super word of the super tableau of a semistandard tableau is the word of that
tableau read in positive letters. -/
theorem superWordOfWord_ssytWord (T : SemistandardYoungTableau μ) :
    superWordOfWord (ssytWord T) = superStdWord (superOfSsyt T) :=
  funext fun k =>
    (SuperLetter.eq_mk_false_of_isPositive (isPositive_superStdWord_superOfSsyt T k)).symm

/-- **The word of a semistandard tableau is ascending for the descent set of its standardisation**:
this is the admissibility of the canonical pair of `HJO.Sym.superTableauOfPair_bijective`, read at
positive letters. -/
theorem isAscendingWord_ssytWord (T : SemistandardYoungTableau μ) :
    IsAscendingWord μ.card (sytDescentSet (ssytStd T).1) (ssytWord T) := by
  rw [← isSuperAscendingWord_superWordOfWord, superWordOfWord_ssytWord]
  exact isSuperAdmissibleWord_superStdWord (superOfSsyt T)

/-- **The admissible pair of a standard tableau and an ascending word**: the `P` at
positive letters, the word read in positive letters being super ascending for the same step set. -/
def stdPairOfWord {S : SYT μ} {u : Fin μ.card → ℕ}
    (hu : IsAscendingWord μ.card (sytDescentSet S.1) u) : SuperStdPair μ :=
  ⟨(S.1, superWordOfWord u), S.2, isSuperAscendingWord_superWordOfWord.2 hu⟩

/-- The filling of the admissible pair of a standard tableau and an ascending word, on a cell. -/
theorem superTableauOfPair_stdPairOfWord {S : SYT μ} {u : Fin μ.card → ℕ}
    (hu : IsAscendingWord μ.card (sytDescentSet S.1) u) {c : ℕ × ℕ} (hc : c ∈ μ.cells) :
    superTableauOfPair (stdPairOfWord hu) c.1 c.2
      = superWordOfWord u ⟨S.1 c.1 c.2, S.2.lt_card hc⟩ :=
  pairEntry_of_mem S.2 hc

/-- **The canonical pair of a semistandard tableau fills it back**: the map applied to
the standardisation and the word returns the tableau one started from, which is the surjectivity
half of `HJO.Sym.superTableauOfPair_bijective` read at positive letters. -/
theorem superTableauOfPair_stdPairOfWord_ssytWord (T : SemistandardYoungTableau μ) :
    superTableauOfPair (stdPairOfWord (isAscendingWord_ssytWord T)) = superOfSsyt T := by
  have hp : stdPairOfWord (isAscendingWord_ssytWord T)
      = ⟨(superStdTableau (superOfSsyt T), superStdWord (superOfSsyt T)),
        isStandard_superStdTableau _, isSuperAdmissibleWord_superStdWord _⟩ :=
    Subtype.ext (Prod.ext rfl (superWordOfWord_ssytWord T))
  rw [hp]
  exact superTableauOfPair_canonical (superOfSsyt T) (isStandard_superStdTableau _)
    (isSuperAdmissibleWord_superStdWord _)

/-- The entry of a cell is the letter of the word of the tableau at the value the standardisation
gives that cell: the factorisation of `HJO.Sym.superTableauOfPair_bijective` read at positive
letters. -/
theorem entry_eq_ssytWord (T : SemistandardYoungTableau μ) {c : ℕ × ℕ} (hc : c ∈ μ.cells) :
    T c.1 c.2 = ssytWord T ⟨(ssytStd T).1 c.1 c.2, (ssytStd T).2.lt_card hc⟩ := by
  have hcoe : superOfSsyt T c.1 c.2
      = superTableauOfPair (stdPairOfWord (isAscendingWord_ssytWord T)) c.1 c.2 := by
    rw [superTableauOfPair_stdPairOfWord_ssytWord T]
  exact congrArg SuperLetter.absVal
    (hcoe.trans (superTableauOfPair_stdPairOfWord (isAscendingWord_ssytWord T) hc))

/-- **The multidegree of a semistandard tableau is the exponent vector of its word.** -/
theorem wt_eq_wordExponent_ssytWord (T : SemistandardYoungTableau μ) :
    T.wt = wordExponent (ssytWord T) :=
  wt_eq_wordExponent (ssytStd T).2 fun _ hc => entry_eq_ssytWord T hc

/-! ### The standardisation is a bijection at a fixed content -/

/-- **The condition under which a standard tableau contributes a monomial**: some
`Des(S)`-ascending word of length `#D` has that exponent vector. There is at most one such word
(`HJO.Sym.eq_of_wordExponent_eq`), so this is exactly the coefficient of `F_{n,Des(S)}` at the
monomial, and it fails for every `S` when the monomial does not have total degree `#D`. -/
def HasAscendingWord (S : SYT μ) (α : ℕ →₀ ℕ) : Prop :=
  ∃ u : Fin μ.card → ℕ, IsAscendingWord μ.card (sytDescentSet S.1) u ∧ α = wordExponent u

/-- **The coefficient of a fundamental at the descent set of a standard tableau**: `1` when the
monomial is carried by a `Des(S)`-ascending word and `0` otherwise, the descent set lying in the
window `{1, …, n-1}` where `HJO.ParkingFunctions.gessel` has content. -/
theorem coeff_gessel_sytDescentSet (K : Type*) [CommRing K] (S : SYT μ) (α : ℕ →₀ ℕ)
    [Decidable (HasAscendingWord S α)] :
    MvPowerSeries.coeff α (ParkingFunctions.gessel K μ.card (sytDescentSet S.1))
      = if HasAscendingWord S α then 1 else 0 := by
  by_cases h : HasAscendingWord S α
  · obtain ⟨u, hu, rfl⟩ := h
    rw [ite_eq_left ⟨u, hu, rfl⟩]
    exact ParkingFunctions.coeff_wordExponent_gessel K (sytDescentSet_subset_Ico S.1) hu
  · rw [ite_eq_right h]
    exact ParkingFunctions.coeff_gessel_eq_zero_of_forall_ne K fun u hu heq => h ⟨u, hu, heq⟩

/-- **The standardisation is a bijection from the semistandard tableaux of a given content onto the
standard tableaux whose descent set admits the corresponding word.** This is the counting content
of `HJO.Sym.schurSeries_eq_sum_gessel`: the bijection of `HJO.Sym.superTableauOfPair_bijective`,
restricted to positive letters and cut at a fixed content.

Well-definedness is `HJO.Sym.isAscendingWord_ssytWord` together with
`HJO.Sym.wt_eq_wordExponent_ssytWord`; injectivity is the uniqueness of a weakly increasing word
with a given exponent vector, which makes the two pairs coincide; and surjectivity fills the
tableau back from the pair. -/
theorem bijOn_ssytStd (α : ℕ →₀ ℕ) :
    Set.BijOn (ssytStd (μ := μ)) {T : SemistandardYoungTableau μ | T.wt = α}
      {S : SYT μ | HasAscendingWord S α} := by
  refine ⟨fun T hT => ⟨ssytWord T, isAscendingWord_ssytWord T, ?_⟩, fun T hT T' hT' heq => ?_,
    fun S hS => ?_⟩
  · rw [← show T.wt = α from hT]
    exact wt_eq_wordExponent_ssytWord T
  · have hu : ssytWord T = ssytWord T' :=
      eq_of_monotone_of_wordExponent_eq (isAscendingWord_ssytWord T).monotone
        (isAscendingWord_ssytWord T').monotone
        (by rw [← wt_eq_wordExponent_ssytWord, ← wt_eq_wordExponent_ssytWord,
          show T.wt = α from hT, show T'.wt = α from hT'])
    refine SemistandardYoungTableau.ext fun i j => ?_
    by_cases hc : ((i, j) : ℕ × ℕ) ∈ μ
    · have hc' : ((i, j) : ℕ × ℕ) ∈ μ.cells := by simpa using hc
      rw [entry_eq_ssytWord T hc', entry_eq_ssytWord T' hc', hu]
      exact congrArg (ssytWord T') (Fin.ext (by rw [heq]))
    · rw [T.zeros hc, T'.zeros hc]
  · obtain ⟨u, hu, hα⟩ := hS
    have hpos : ∀ i j : ℕ, ((superTableauOfPair (stdPairOfWord hu)) i j).IsPositive := by
      intro i j
      by_cases hc : ((i, j) : ℕ × ℕ) ∈ μ
      · rw [superTableauOfPair_stdPairOfWord hu (show ((i, j) : ℕ × ℕ) ∈ μ.cells by simpa using hc)]
        exact isPositive_superWordOfWord u _
      · rw [(superTableauOfPair (stdPairOfWord hu)).outside hc]
        exact SuperLetter.sign_mk _ _
    refine ⟨ssytOfSuper (superTableauOfPair (stdPairOfWord hu)) hpos, ?_, ?_⟩
    · have hwt : (ssytOfSuper (superTableauOfPair (stdPairOfWord hu)) hpos).wt = α := by
        rw [hα]
        exact wt_eq_wordExponent S.2 fun c hc =>
          congrArg SuperLetter.absVal (superTableauOfPair_stdPairOfWord hu hc)
      exact hwt
    · refine Subtype.ext ?_
      rw [coe_ssytStd, superOfSsyt_ssytOfSuper]
      exact superStdTableau_superTableauOfPair (stdPairOfWord hu)

/-! ### Gessel's expansion -/

/-- **The Schur series of a Young diagram is the sum of the Gessel
fundamentals at the descent sets of its standard tableaux**,
`sch(D) = ∑_{S ∈ SYT(D)} F_{n,Des(S)}` with `n = #D`.

Both sides are read at one monomial. On the left the coefficient is the Kostka number, the number of
semistandard tableaux of that content; on the right each summand contributes `1` exactly when the
monomial is carried by a `Des(S)`-ascending word. The two counts agree because standardisation is a
bijection between the two sets (`HJO.Sym.bijOn_ssytStd`), which is the restriction of
`HJO.Sym.superTableauOfPair_bijective` to positive letters.

The `n ≥ 1` is dropped: at `n = 0` the diagram is empty and both sides are `1`. -/
@[hjo "lem_cm_gessel_schur"]
theorem schurSeries_eq_sum_gessel (K : Type*) [CommRing K] (μ : YoungDiagram) :
    schurSeries K μ = ∑ S : SYT μ, ParkingFunctions.gessel K μ.card (sytDescentSet S.1) := by
  classical
  refine MvPowerSeries.ext fun α => ?_
  rw [coeff_schurSeries, map_sum,
    Finset.sum_congr rfl fun S _ => coeff_gessel_sytDescentSet K S α, Finset.sum_boole]
  refine congrArg Nat.cast ?_
  rw [kostka, ← (bijOn_ssytStd α).injOn.ncard_image, (bijOn_ssytStd α).image_eq,
    ← Set.ncard_coe_finset]
  congr 1
  ext S
  simp

end HJO.Sym
