/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.CarlssonMellit.SuperAlphabet
public import HJO.Classical.Standardisation
public import HJO.DyckWordMonomial
public meta import HJO.Attr

/-! # Words over the super alphabet: their variables, monomials, absolute values, inversions and
standardisation

The expansion of the characteristic series that Carlsson and Mellit use runs over words in the
doubled alphabet `HJO.Sym.SuperLetter`. Five things are read off such a word, and this file defines
them: the variable `ζ_α` a single letter carries, the monomial `z_v` of a word, the word `|v|` of
absolute values, the super inversion set `Inv^±(R, v)` with its cardinality, and the super
standardisation `Std^±(v)`.

## Main definitions

* `HJO.Sym.superVar`: `ζ_α`.
* `HJO.Sym.superMonomial`: `z_v`.
* `HJO.Sym.superAbs`: `|v|`.
* `HJO.Dyck.superInvSet`, `HJO.Dyck.superInvNumber`: `Inv^±(R, v)` and `inv^±(R, v)`.
* `HJO.Sym.superStd`: `Std^±(v)`.

## Main results

* `HJO.Sym.superStd_lt_superStd_iff`: the order `Std^±(v)` induces on the positions, the two
  tie-breaking rules read off the definition.
* `HJO.Sym.superStd_bijective`: `Std^±(v)` is a permutation of the positions.
* `HJO.Dyck.superInvSet_eq_invSet_superStd`: `Inv^±(R, v) = Inv(R, Std^±(v))`.

## Implementation notes

Positions are indexed from `0` and taken as tuples `Fin n → SuperLetter`, matching
`HJO.Sym.wordMonomial` and `HJO.Sym.std`; absolute values are indexed from `0` as in
`HJO.Sym.SuperLetter.absVal`, so `superAbs v` is a word in the sense of `HJO.Sym.wordMonomial` and
`x_{|v|}` is `wordMonomial K (superAbs v)` with nothing shifted. The parameter `q` is a ring element
of the base, as everywhere in this layer.

`superInvSet` is *not* `HJO.Dyck.invSet` at a super-letter-valued word: the paper's set admits a
pair whose two letters are equal and negative, which no plain inversion set does. It is
`invSet R v` together with those pairs, and `superInvSet_eq_invSet_union` records the splitting.

`superStd` is `HJO.Sym.std` at a *key*, not a second standardisation: the two tie-breaking rules —
increasing index among equal positive letters, decreasing index among equal negative ones — are
exactly the statement that the order being ranked is the lexicographic one on the pair
`(v i, if v i is negative then n - 1 - i else i)`, and that key is injective, so the rank is the
position in the sorted listing. Reusing `std` is what makes `superStd_bijective` free, through
`HJO.Sym.std_bijective`, and keeps the value a `0`-based position of type `ℕ` so that
`HJO.Dyck.invSet R (superStd v)` typechecks — which is the shape the paper's identity
`Inv^±(R, v) = Inv(R, Std^±(v))` is stated in. The paper's rank in `{1, …, n}` is
`superStd v i + 1`.

The truncated subtraction `n - 1 - i` in the key is harmless and is not an index into
anything: it is read only through the comparison `n - 1 - j < n - 1 - i`, which for positions of
`Fin n` is `i < j`, and the tie it breaks only ever arises at two positions of one word.

## References

E. Carlsson and A. Mellit, *A proof of the shuffle
conjecture*, J. Amer. Math. Soc. **31** (2018) 661--697, Section 3.
-/

@[expose] public section

open Finset

namespace HJO.Sym

/-! ### The variable of a super letter, and the monomial of a word -/

/-- **The variable of a super letter** `ζ_α`: the series `q x_a` when `α` is the positive letter of
absolute value `a`, and `-x_a` when it is the negative one. These are the paper's `z_i = x_i` and
`z_{ī} = -y_i` after the specialisation `X ↦ qX`, `Y ↦ X` that carries `F[X - Y]` to `F[(q-1)X]`.
The absolute value is indexed from `0`, so the paper's `x_a` is `MvPowerSeries.X (a - 1)`, and `q`
is an element of the base ring. -/
@[hjo "def_cm_super_variable"]
noncomputable def superVar {K : Type*} [CommRing K] (q : K) (α : SuperLetter) : AlphabetSeries K :=
  cond (ofLex α).2 (-MvPowerSeries.X α.absVal) (MvPowerSeries.C q * MvPowerSeries.X α.absVal)

/-- The variable of a negative letter is `-x_a`. -/
@[simp]
theorem superVar_of_isNegative {K : Type*} [CommRing K] (q : K) {α : SuperLetter}
    (h : α.IsNegative) : superVar q α = -MvPowerSeries.X α.absVal := by
  rw [superVar, show (ofLex α).2 = true from h, Bool.cond_true]

/-- The variable of a positive letter is `q x_a`. -/
@[simp]
theorem superVar_of_isPositive {K : Type*} [CommRing K] (q : K) {α : SuperLetter}
    (h : α.IsPositive) : superVar q α = MvPowerSeries.C q * MvPowerSeries.X α.absVal := by
  rw [superVar, show (ofLex α).2 = false from h, Bool.cond_false]

/-- **The monomial of a super word** `z_v = ∏_i ζ_{v_i}`, the empty product being `1`. -/
@[hjo "def_cm_super_monomial"]
noncomputable def superMonomial (K : Type*) [CommRing K] (q : K) {n : ℕ}
    (v : Fin n → SuperLetter) : AlphabetSeries K :=
  ∏ i, superVar q (v i)

/-- The monomial of the empty super word is `1`: the empty product. -/
@[simp]
theorem superMonomial_zero (K : Type*) [CommRing K] (q : K) (v : Fin 0 → SuperLetter) :
    superMonomial K q v = 1 :=
  Finset.prod_empty.trans rfl

/-! ### The absolute value of a super word -/

/-- **The absolute value of a super word** `|v|`: the word whose `i`-th letter is the absolute value
of `v_i`. Absolute values are indexed from `0`, so this is a word in the sense of
`HJO.Sym.wordMonomial` and the paper's monomial `x_{|v|}` is `wordMonomial K (superAbs v)`. -/
@[hjo "def_cm_super_abs"]
def superAbs {n : ℕ} (v : Fin n → SuperLetter) : Fin n → ℕ := fun i => (v i).absVal

@[simp]
theorem superAbs_apply {n : ℕ} (v : Fin n → SuperLetter) (i : Fin n) :
    superAbs v i = (v i).absVal :=
  rfl

/-- Two super words with the same letters have the same absolute values, and equal letters at a
position have equal absolute values there: the absolute value is read letterwise. -/
theorem superAbs_congr {n : ℕ} {v w : Fin n → SuperLetter} (h : v = w) : superAbs v = superAbs w :=
  congrArg superAbs h

/-! ### The super standardisation -/

section Std

variable {n : ℕ}

/-- The tie-break of the super standardisation at a letter: the position itself when the letter is
positive and the mirrored position `n - 1 - i` when it is negative. Comparing these is comparing the
positions in the direction the two tie-breaking rules prescribe — increasing index among
equal positive letters, decreasing index among equal negative ones. Written with `cond` on the sign
bit rather than with a decidable `if`, the sign being a `Bool`. -/
def superTie (n : ℕ) (α : SuperLetter) (i : ℕ) : ℕ := cond (ofLex α).2 (n - 1 - i) i

@[simp]
theorem superTie_of_isPositive {α : SuperLetter} (h : α.IsPositive) (i : ℕ) :
    superTie n α i = i := by
  rw [superTie, show (ofLex α).2 = false from h, Bool.cond_false]

@[simp]
theorem superTie_of_isNegative {α : SuperLetter} (h : α.IsNegative) (i : ℕ) :
    superTie n α i = n - 1 - i := by
  rw [superTie, show (ofLex α).2 = true from h, Bool.cond_true]

/-- The tie-break compares the positions the way the letter's sign prescribes, and is injective on
the positions: `n - 1 - ·` is strictly antitone below `n`. -/
theorem superTie_lt_superTie_iff (α : SuperLetter) {i j : Fin n} :
    superTie n α i < superTie n α j ↔
      (α.IsPositive ∧ (i : ℕ) < (j : ℕ)) ∨ (α.IsNegative ∧ (j : ℕ) < (i : ℕ)) := by
  have hi := i.isLt
  have hj := j.isLt
  by_cases h : α.IsNegative
  · rw [superTie_of_isNegative h, superTie_of_isNegative h]
    have hnp : ¬α.IsPositive := fun hp =>
      absurd h ((SuperLetter.isPositive_iff_not_isNegative α).1 hp)
    simp only [hnp, false_and, h, true_and, false_or]
    omega
  · have hp : α.IsPositive := (SuperLetter.isPositive_iff_not_isNegative α).2 h
    rw [superTie_of_isPositive hp, superTie_of_isPositive hp]
    simp only [hp, true_and, h, false_and, or_false]

/-- The key whose rank the super standardisation is: the letter at the position, paired with the
tie-break `HJO.Sym.superTie`, compared lexicographically. -/
def superKey (v : Fin n → SuperLetter) (i : Fin n) : SuperLetter ×ₗ ℕ :=
  toLex (v i, superTie n (v i) (i : ℕ))

/-- The comparison of two keys: the letters decide, and at equal letters the tie-breaks do. -/
theorem superKey_lt_superKey_iff (v : Fin n → SuperLetter) (i j : Fin n) :
    superKey v i < superKey v j ↔
      v i < v j ∨ (v i = v j ∧ superTie n (v i) (i : ℕ) < superTie n (v j) (j : ℕ)) := by
  rw [superKey, superKey, Prod.Lex.toLex_lt_toLex]

/-- **The super standardisation `Std^±(v)`.** The position of `v_i` when the
entries of `v` are sorted increasingly for the order of the super alphabet, ties among equal
positive letters broken by increasing index and ties among equal negative letters by decreasing
index. The value is a `0`-based position, so the paper's rank in `{1, …, n}` is
`superStd v i + 1`, exactly as for `HJO.Sym.std`.

It is `HJO.Sym.std` at `HJO.Sym.superKey`: ranking the key is ranking the letters with the two
tie-breaks built in, so nothing about permutations has to be redone — `superStd_bijective` is
`HJO.Sym.std_bijective`. -/
@[hjo "def_cm_super_std"]
def superStd (v : Fin n → SuperLetter) (i : Fin n) : ℕ := std (superKey v) i

/-- **The super standardisation orders distinct letters by the alphabet**: a smaller letter gets a
smaller rank, which is what sorting the entries of `v` increasingly means. -/
theorem superStd_lt_superStd_of_lt {v : Fin n → SuperLetter} {i j : Fin n} (h : v i < v j) :
    superStd v i < superStd v j :=
  (std_lt_std_iff (superKey v) i j).2
    (Or.inl ((superKey_lt_superKey_iff v i j).2 (Or.inl h)))

/-- **The first tie-breaking rule**: ties among equal *positive* letters are broken by increasing
index. This is the clause that forbids a repetition of a positive letter to be a
descent of the indexing permutation. -/
theorem superStd_lt_superStd_iff_of_isPositive {v : Fin n → SuperLetter} {i j : Fin n}
    (heq : v i = v j) (hp : (v i).IsPositive) :
    superStd v i < superStd v j ↔ (i : ℕ) < (j : ℕ) := by
  rw [superStd, superStd, std_lt_std_iff, superKey_lt_superKey_iff]
  have hnlt : ¬ v i < v j := by rw [heq]; exact lt_irrefl _
  have hpj : (v j).IsPositive := heq ▸ hp
  rw [superTie_of_isPositive hp, superTie_of_isPositive hpj]
  refine ⟨fun h => ?_, fun h => Or.inl (Or.inr ⟨heq, h⟩)⟩
  rcases h with h | h
  · exact h.elim (fun hc => absurd hc hnlt) fun hc => hc.2
  · exact h.2

/-- **The second tie-breaking rule**: ties among equal *negative* letters are broken by decreasing
index. This is the clause that requires a repetition of a negative letter to be a
descent of the indexing permutation, and it is the one that makes the two rules opposite. -/
theorem superStd_lt_superStd_iff_of_isNegative {v : Fin n → SuperLetter} {i j : Fin n}
    (heq : v i = v j) (hneg : (v i).IsNegative) :
    superStd v i < superStd v j ↔ (j : ℕ) < (i : ℕ) := by
  have hi := i.isLt
  have hj := j.isLt
  rw [superStd, superStd, std_lt_std_iff, superKey_lt_superKey_iff]
  have hnlt : ¬ v i < v j := by rw [heq]; exact lt_irrefl _
  have hnj : (v j).IsNegative := heq ▸ hneg
  rw [superTie_of_isNegative hneg, superTie_of_isNegative hnj]
  refine ⟨fun h => ?_, fun h => Or.inl (Or.inr ⟨heq, by omega⟩)⟩
  rcases h with h | h
  · rcases h with hc | hc
    · exact absurd hc hnlt
    · omega
  · have hij : (i : ℕ) < (j : ℕ) := h.2
    have hkey : superKey v i = superKey v j := h.1
    have h2 : superTie n (v i) (i : ℕ) = superTie n (v j) (j : ℕ) :=
      congrArg (fun p => (ofLex p).2) hkey
    rw [superTie_of_isNegative hneg, superTie_of_isNegative hnj] at h2
    omega

/-- The super standardisation takes values among the positions. -/
theorem superStd_lt (v : Fin n → SuperLetter) (i : Fin n) : superStd v i < n :=
  std_lt _ i

/-- The super standardisation is injective on the positions. -/
theorem superStd_injective (v : Fin n → SuperLetter) : Function.Injective (superStd v) :=
  std_injective (superKey v)

/-- **The super standardisation is a permutation of the positions**, a bijection of
`{1, …, n}` in one-based indexing. -/
theorem superStd_bijective (v : Fin n → SuperLetter) :
    Function.Bijective fun i => (⟨superStd v i, superStd_lt v i⟩ : Fin n) :=
  std_bijective (superKey v)

end Std

end HJO.Sym

namespace HJO.Dyck

open HJO.Sym

/-! ### The super inversion set -/

/-- **The super inversion set** `Inv^±(R, v)`: the pairs `(i, j)` of `R`
whose earlier position carries the larger letter, together with those whose two letters are equal
and negative. The second clause is what distinguishes it from `HJO.Dyck.invSet`, and it is the
paper's own: a repetition of a negative letter counts as an inversion while a repetition of a
positive letter does not. -/
@[hjo "def_cm_super_inv_set"]
def superInvSet {ι : Type*} (R : Finset (ι × ι)) (v : ι → SuperLetter) : Finset (ι × ι) :=
  {p ∈ R | v p.2 < v p.1 ∨ (v p.1 = v p.2 ∧ (v p.1).IsNegative)}

/-- Membership in the super inversion set: the paper's two alternatives. -/
@[simp]
theorem mem_superInvSet {ι : Type*} {R : Finset (ι × ι)} {v : ι → SuperLetter} {p : ι × ι} :
    p ∈ superInvSet R v ↔
      p ∈ R ∧ (v p.2 < v p.1 ∨ (v p.1 = v p.2 ∧ (v p.1).IsNegative)) :=
  Finset.mem_filter

/-- **The super inversion number** `inv^±(R, v) = #Inv^±(R, v)`. -/
@[hjo "def_cm_super_inv"]
def superInvNumber {ι : Type*} (R : Finset (ι × ι)) (v : ι → SuperLetter) : ℕ :=
  #(superInvSet R v)

/-- Every super inversion is a pair of `R`. -/
theorem superInvSet_subset {ι : Type*} (R : Finset (ι × ι)) (v : ι → SuperLetter) :
    superInvSet R v ⊆ R :=
  Finset.filter_subset _ _

/-- The super inversion set splits into the plain inversions and the equal negative pairs, which is
the form in which the paper's two clauses are used one at a time. -/
theorem superInvSet_eq_invSet_union {ι : Type*} [DecidableEq ι] (R : Finset (ι × ι))
    (v : ι → SuperLetter) :
    superInvSet R v = invSet R v ∪ {p ∈ R | v p.1 = v p.2 ∧ (v p.1).IsNegative} := by
  rw [superInvSet, invSet, ← Finset.filter_or]

/-- A super word all of whose letters are distinct along the pairs of `R` has the plain inversion
set: the second clause of the definition never fires. This is the step that reads the super
inversion set of a repetition-free word as an ordinary one. -/
theorem superInvSet_eq_invSet {ι : Type*} {R : Finset (ι × ι)} {v : ι → SuperLetter}
    (h : ∀ p ∈ R, v p.1 ≠ v p.2) : superInvSet R v = invSet R v :=
  Finset.filter_congr fun p hp =>
    ⟨fun hc => hc.elim id fun hc' => absurd hc'.1 (h p hp), Or.inl⟩

/-! ### Super standardisation preserves the super inversions -/

/-- **Super standardisation preserves the super inversions.** For a set `R`
of increasing pairs of positions, `Inv^±(R, v) = Inv(R, Std^±(v))`: the super inversion set of a
super word is the *plain* inversion set of its super standardisation.

This is where the two opposite tie-breaks earn their keep, and it is the paper's first displayed
property. A pair `(i, j) ∈ R` has `i < j`, so at distinct letters the standardisation orders the two
positions by the alphabet and both sides agree; at equal letters the tie-break decides, and it was
chosen to: a repeated *positive* letter is ordered by increasing index, so `(i, j)` is an inversion
of neither side, matching the clause of `superInvSet` that excludes an equal positive pair, while a
repeated *negative* letter is ordered by decreasing index, so `(i, j)` is an inversion of both. -/
@[hjo "lem_cm_super_inv_std"]
theorem superInvSet_eq_invSet_superStd {n : ℕ} (R : Finset (Fin n × Fin n))
    (hR : ∀ p ∈ R, p.1 < p.2) (v : Fin n → SuperLetter) :
    superInvSet R v = invSet R (superStd v) := by
  rw [superInvSet, invSet]
  refine Finset.filter_congr fun p hp => ?_
  have hlt : p.1 < p.2 := hR p hp
  have hltval : (p.1 : ℕ) < (p.2 : ℕ) := hlt
  rcases lt_trichotomy (v p.1) (v p.2) with h | h | h
  · refine iff_of_false (fun hc => ?_) (asymm (superStd_lt_superStd_of_lt h))
    exact hc.elim (fun hc' => absurd hc' (asymm h)) fun hc' => absurd hc'.1 (ne_of_lt h)
  · by_cases hneg : (v p.1).IsNegative
    · refine iff_of_true (Or.inr ⟨h, hneg⟩) ?_
      rw [superStd_lt_superStd_iff_of_isNegative h.symm (h ▸ hneg)]
      exact hltval
    · have hp2 : (v p.2).IsPositive :=
        h ▸ (SuperLetter.isPositive_iff_not_isNegative (v p.1)).2 hneg
      refine iff_of_false (fun hc => ?_) ?_
      · exact hc.elim (fun hc' => absurd hc' (h ▸ lt_irrefl _))
          fun hc' => absurd hc'.2 hneg
      · rw [superStd_lt_superStd_iff_of_isPositive h.symm hp2]
        omega
  · exact iff_of_true (Or.inl h) (superStd_lt_superStd_of_lt h)

end HJO.Dyck
