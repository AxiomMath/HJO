/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.AmbientCombinatorics
public import HJO.DyckAttackSets
public import HJO.DyckDelete
public import HJO.DyckInversions
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.MvPolynomial.Rename
public meta import HJO.Attr

/-! # The two-letter characteristic polynomial

Carlsson--Mellit prove the symmetry of the characteristic series `χ(R, n)` in two neighbouring
letters by reducing it to a polynomial identity in two indeterminates. The polynomial is

`χ₂(R, m) = ∑_{v ∈ {1,2}^m} q ^ inv(R, v) · ξ₁ ^ #{i : v_i = 1} · ξ₂ ^ #{i : v_i = 2}`,

the two-letter specialisation of `χ`, and the identity is that it is invariant under interchanging
`ξ₁` and `ξ₂` whenever `R` is a transitive attack set. This file carries that identity and the
induction that proves it.

The induction is on `#R`, over all lengths `m` at once. At `#R = 0` the polynomial is `(ξ₁ + ξ₂)^m`.
Otherwise a *maximal* pair `(a, b) ∈ R` is chosen — one that can be widened at neither end,
`HJO.Dyck.IsMaximalPair` — and the difference `χ₂(R, m) - χ₂(R ∖ {(a,b)}, m)` is computed. Only the
words with `v_a = 2` and `v_b = 1` contribute to it, since `(a, b)` is an inversion of exactly
those;
for such a word the pair is worth a factor `q - 1`, the positions strictly between `a` and `b`
contribute `q ^ (b - a - 1)` no matter what they carry, and deleting the two positions leaves
an arbitrary word of length `m - 2` for the restricted set. So the difference is
`(q - 1) q ^ (b-a-1) ξ₁ξ₂ χ₂((R ∖ {(a,b)})_S, m-2)`, visibly symmetric, and both `R ∖ {(a,b)}` and
its restriction are transitive attack sets of strictly smaller size.

## Main definitions

* `HJO.Dyck.finPairs`: a set of pairs of positions of `{1, …, m}` read as a set of pairs of `Fin m`,
  the form in which `HJO.Dyck.invSet` is applied to a tuple of letters.
* `HJO.Dyck.IsMaximalPair`: `(a, b) ∈ R` can be widened inside `R` at neither end.
* `HJO.Dyck.twoLetterChar`: `χ₂(R, m)`.

## Main results

* `HJO.Dyck.IsTransitiveAttackSet.erase`: `R ∖ {(a,b)}` is again a transitive attack set.
* `HJO.Dyck.IsMaximalPair.mem_erase_fst_iff`, `HJO.Dyck.IsMaximalPair.mem_erase_snd_iff`: the
  neighbours of a maximal pair, `(a,j) ∈ R'` ↔ `(j,b) ∈ R'` ↔ `a < j < b`.
* `HJO.Dyck.IsMaximalPair.card_invSet_erase`: the inversion count at a maximal pair splits as
  `(b - a - 1) + inv((R')_S, v^{(a,b)})`.
* `HJO.Dyck.IsMaximalPair.twoLetterChar_sub_twoLetterChar_erase`: the two-letter difference.
* `HJO.Dyck.rename_swap_twoLetterChar`: `χ₂(R, m)` is invariant under `ξ₁ ↔ ξ₂`.
* `HJO.Dyck.getD_sort_range_sdiff_pair`: the two deletions renumber along the same enumeration.

## Implementation notes

*The two letters are `Fin 2` and so are the two indeterminates*, so a word of length `m` is a tuple
`v : Fin m → Fin 2` and the monomial `ξ₁ ^ #{i : v_i = 1} ξ₂ ^ #{i : v_i = 2}` is the product
`∏ i, X (v i)` in `MvPolynomial (Fin 2) K`. Letters are numbered from `0`, as positions are
everywhere in this library, so the paper's letter `1` is `0` and its letter `2` is `1`; the
order is the one the paper uses, `1 < 2`, and an inversion of `(i, j)` is `v_j < v_i`.

*Sets of pairs are `Finset (ℕ × ℕ)` and words are indexed by `Fin m`*, which is the convention of
`HJO.Dyck.attackSet`, of `HJO.Dyck.IsTransitiveAttackSet` and of the marked characteristic series:
`HJO.Dyck.finPairs` is the coercion between the two, and `HJO.Dyck.invSet` is formed at
`finPairs m R`. A pair of `R` outside `range m ×ˢ range m` is invisible to `χ₂(R, m)`, exactly as a
pair outside the square is invisible to the marked series.

*The difference of the two polynomials is a subtraction in `MvPolynomial (Fin 2) K`, not in `ℕ`*, so
`K` is a commutative ring and no positivity is needed. The one natural-number subtraction that does
occur is the exponent `b - a - 1`, and it is not truncated: a maximal pair has `a < b`, so
`b - a - 1` is the number of positions strictly between them, which is what
`HJO.Dyck.IsMaximalPair.card_invSet_erase` counts and `Fin.card_Ioo` returns.

*The scalar `q ^ (b - a - 1)` is present*, where the paper's display drops it one line after
deriving the exponent that produces it. No later use reads more of that scalar than that it is a
unit, and the symmetry proof reads nothing of it at all.

*The bridge between the two deletions.* The restriction `(R')_S` is `HJO.Dyck.attackRestrict`, which
renumbers along the increasing enumeration `Finset.sort` of `S ⊆ ℕ`, while the shortened word
`v^{(a,b)}` is `HJO.Dyck.removePair`, which renumbers along `Finset.orderEmbOfFin` of
`({a,b}ᶜ : Finset (Fin m))`. The two enumerations are the same map read in two types, and
`HJO.Dyck.getD_sort_range_sdiff_pair` is that identification; it is what lets the count of the
inversions internal to `S` be transported between the two.

## References

E. Carlsson and A. Mellit, *A proof of the shuffle conjecture*, arXiv:1508.06239, Proposition 3.2
and the two-letter reduction inside its proof. Used by `HJO.Dyck.letterPerm_swap_charSeries`. -/

@[expose] public section

open Finset

namespace HJO.Dyck

/-! ### Positions of `Fin m` -/

/-- A set `R` of pairs of positions of `{1, …, m}`, recorded as a `Finset (ℕ × ℕ)`, read as a set of
pairs of `Fin m`: the coercion along `Fin.val` under which `HJO.Dyck.invSet` is formed at a tuple
`Fin m → α`. Pairs of `R` outside `range m ×ˢ range m` are discarded, and no other pair is. -/
def finPairs (m : ℕ) (R : Finset (ℕ × ℕ)) : Finset (Fin m × Fin m) :=
  {p : Fin m × Fin m | ((p.1 : ℕ), (p.2 : ℕ)) ∈ R}

@[simp]
theorem mem_finPairs {m : ℕ} {R : Finset (ℕ × ℕ)} {p : Fin m × Fin m} :
    p ∈ finPairs m R ↔ ((p.1 : ℕ), (p.2 : ℕ)) ∈ R :=
  mem_filter_univ p

/-! ### Maximal pairs -/

/-- `(a, b)` is a **maximal pair** of `R`: it belongs to `R` and can be widened inside `R` at
neither end, so `(a, j) ∉ R` for every `j > b` and `(j, b) ∉ R` for every `j < a`. This is the
hypothesis under which the paper removes a pair from a transitive attack set; a nonempty `R` has
one by `Finset.exists_maximal_prod`. -/
structure IsMaximalPair (R : Finset (ℕ × ℕ)) (a b : ℕ) : Prop where
  /-- The pair belongs to `R`. -/
  mem : (a, b) ∈ R
  /-- It cannot be widened upwards: the paper's `(a, j) ∉ R` for `j > b`. -/
  notMem_of_lt : ∀ j, b < j → (a, j) ∉ R
  /-- It cannot be widened downwards: the paper's `(j, b) ∉ R` for `j < a`. -/
  notMem_of_gt : ∀ j, j < a → (j, b) ∉ R

/-- Every nonempty finite set of pairs of natural numbers has a maximal pair:
`Finset.exists_maximal_prod` packaged as `HJO.Dyck.IsMaximalPair`. -/
theorem exists_isMaximalPair {R : Finset (ℕ × ℕ)} (hR : R.Nonempty) :
    ∃ a b, IsMaximalPair R a b := by
  obtain ⟨a, b, h1, h2, h3⟩ := Finset.exists_maximal_prod hR
  exact ⟨a, b, ⟨h1, h2, h3⟩⟩

variable {m : ℕ} {R : Finset (ℕ × ℕ)} {a b : ℕ}

/-- A maximal pair of a set of increasing pairs is increasing. -/
theorem IsMaximalPair.lt (h : IsTransitiveAttackSet m R) (hab : IsMaximalPair R a b) : a < b :=
  h.fst_lt_snd _ hab.mem

/-- **Removing a maximal pair**: if `R` is a transitive attack set on `{1, …, m}` and `(a, b)` is a
maximal pair of `R`, then `R ∖ {(a,b)}` is a transitive attack set on `{1, …, m}`.

Only the splitting clauses need an argument. Splitting a pair `(j, j'') ∈ R ∖ {(a,b)}` at `j'`
returns two pairs of `R`, and neither can be `(a, b)`: were the lower half `(a, b)`, the pair being
split would be `(a, j'')` with `j'' > b`, and were the upper half `(a, b)`, it would be `(j, b)`
with `j < a`. Maximality excludes both. -/
@[hjo "lem_cm_remove_transitive"]
theorem IsTransitiveAttackSet.erase (h : IsTransitiveAttackSet m R)
    (hab : IsMaximalPair R a b) : IsTransitiveAttackSet m (R.erase (a, b)) where
  fst_lt_snd p hp := h.fst_lt_snd p (Finset.mem_of_mem_erase hp)
  snd_lt p hp := h.snd_lt p (Finset.mem_of_mem_erase hp)
  mem_lower {j j' j''} hjj' hj'j'' hp := by
    have hpR := Finset.mem_of_mem_erase hp
    refine Finset.mem_erase.2 ⟨fun hc => ?_, h.mem_lower hjj' hj'j'' hpR⟩
    obtain ⟨rfl, rfl⟩ := Prod.mk.injEq .. ▸ hc
    exact hab.notMem_of_lt j'' hj'j'' hpR
  mem_upper {j j' j''} hjj' hj'j'' hp := by
    have hpR := Finset.mem_of_mem_erase hp
    refine Finset.mem_erase.2 ⟨fun hc => ?_, h.mem_upper hjj' hj'j'' hpR⟩
    obtain ⟨rfl, rfl⟩ := Prod.mk.injEq .. ▸ hc
    exact hab.notMem_of_gt j hjj' hpR

/-- **The neighbours of a maximal pair**, first half: for a maximal pair `(a, b)` of a transitive
attack set `R`, the pairs of `R ∖ {(a,b)}` with first entry `a` are exactly the `(a, j)` with
`a < j < b`.

Forwards: `j > a` because the pairs are increasing, `j ≠ b` because `(a,b)` has been removed, and
`j > b` is excluded by maximality. Backwards: splitting `(a, b)` at `j` gives `(a, j) ∈ R`, which is
not `(a, b)` since `j ≠ b`. -/
@[hjo "lem_cm_max_pair_between"]
theorem IsMaximalPair.mem_erase_fst_iff (h : IsTransitiveAttackSet m R)
    (hab : IsMaximalPair R a b) {j : ℕ} : (a, j) ∈ R.erase (a, b) ↔ a < j ∧ j < b := by
  refine ⟨fun hj => ?_, fun hj => Finset.mem_erase.2 ⟨fun hc => ?_, ?_⟩⟩
  · have hjR := Finset.mem_of_mem_erase hj
    refine ⟨h.fst_lt_snd _ hjR, ?_⟩
    rcases lt_trichotomy j b with hlt | rfl | hgt
    · exact hlt
    · exact absurd (Finset.mem_erase.1 hj).1 (by simp)
    · exact absurd hjR (hab.notMem_of_lt j hgt)
  · exact absurd (Prod.mk.injEq .. ▸ hc).2 hj.2.ne
  · exact h.mem_lower hj.1 hj.2 hab.mem

/-- **The neighbours of a maximal pair**, second half: the pairs of `R ∖ {(a,b)}` with second entry
`b` are exactly the `(j, b)` with `a < j < b`. Together with
`HJO.Dyck.IsMaximalPair.mem_erase_fst_iff` this is the three-way equivalence. -/
@[hjo "lem_cm_max_pair_between"]
theorem IsMaximalPair.mem_erase_snd_iff (h : IsTransitiveAttackSet m R)
    (hab : IsMaximalPair R a b) {j : ℕ} : (j, b) ∈ R.erase (a, b) ↔ a < j ∧ j < b := by
  refine ⟨fun hj => ?_, fun hj => Finset.mem_erase.2 ⟨fun hc => ?_, ?_⟩⟩
  · have hjR := Finset.mem_of_mem_erase hj
    refine ⟨?_, h.fst_lt_snd _ hjR⟩
    rcases lt_trichotomy j a with hlt | rfl | hgt
    · exact absurd hjR (hab.notMem_of_gt j hlt)
    · exact absurd (Finset.mem_erase.1 hj).1 (by simp)
    · exact hgt
  · exact absurd (Prod.mk.injEq .. ▸ hc).1 hj.1.ne'
  · exact h.mem_upper hj.1 hj.2 hab.mem

/-! ### The bridge between the two deletions -/

section Delete

variable {a' b' : Fin m}

/-- The positions of `{1, …, m}` other than two distinct positions `a` and `b` are `m - 2` in
number: the cardinality of the `S = {1, …, m} ∖ {a, b}`. -/
theorem card_range_sdiff_pair (hab : a' ≠ b') :
    #(range m \ ({(a' : ℕ), (b' : ℕ)} : Finset ℕ)) = m - 2 := by
  have hne : (a' : ℕ) ≠ (b' : ℕ) := fun hc => hab (Fin.ext hc)
  have hsub : ({(a' : ℕ), (b' : ℕ)} : Finset ℕ) ⊆ range m := by
    intro i hi
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi
    rcases hi with rfl | rfl <;> simp [Fin.is_lt]
  rw [Finset.card_sdiff, Finset.inter_eq_left.2 hsub, Finset.card_range, Finset.card_pair hne]

/-- **The two deletions renumber along the same enumeration.** `HJO.Dyck.attackRestrict` renumbers a
set of pairs along the increasing enumeration `Finset.sort` of `S = {1, …, m} ∖ {a, b}` inside `ℕ`,
while `HJO.Dyck.removePair` renumbers a word along `Finset.orderEmbOfFin` of
`({a, b}ᶜ : Finset (Fin m))`. Both are the increasing enumeration of the positions other than `a`
and `b`, so they agree: this is the identification that transports a statement about one deletion to
the other, and it is what makes the `inv((R')_S, v^{(a,b)})` a single assertion rather
than two. -/
theorem getD_sort_range_sdiff_pair (hab : a' ≠ b') (j : Fin (m - 2)) :
    ((range m \ ({(a' : ℕ), (b' : ℕ)} : Finset ℕ)).sort).getD (j : ℕ) 0 =
      ((pairComplEmb hab j : Fin m) : ℕ) := by
  have hcard := card_range_sdiff_pair hab
  have hj' : (j : ℕ) < #(range m \ ({(a' : ℕ), (b' : ℕ)} : Finset ℕ)) := by
    rw [hcard]; exact j.isLt
  have hmem : ∀ i : Fin #(range m \ ({(a' : ℕ), (b' : ℕ)} : Finset ℕ)),
      ((pairComplEmb hab (Fin.cast hcard i) : Fin m) : ℕ) ∈
        range m \ ({(a' : ℕ), (b' : ℕ)} : Finset ℕ) := by
    intro i
    simp only [Finset.mem_sdiff, Finset.mem_range, Finset.mem_insert, Finset.mem_singleton]
    refine ⟨Fin.is_lt _, ?_⟩
    rintro (hc | hc)
    · exact pairComplEmb_ne_left hab _ (Fin.ext hc)
    · exact pairComplEmb_ne_right hab _ (Fin.ext hc)
  have hmono : StrictMono fun i : Fin #(range m \ ({(a' : ℕ), (b' : ℕ)} : Finset ℕ)) =>
      ((pairComplEmb hab (Fin.cast hcard i) : Fin m) : ℕ) := by
    intro i i' hii'
    refine Fin.val_strictMono ((pairComplEmb hab).strictMono ?_)
    rw [Fin.lt_def, Fin.val_cast, Fin.val_cast]
    exact hii'
  have hfe := Finset.orderEmbOfFin_unique
    (rfl : #(range m \ ({(a' : ℕ), (b' : ℕ)} : Finset ℕ)) = _) hmem hmono
  rw [Finset.getD_sort_eq_orderEmbOfFin _ 0 hj', ← hfe]
  exact congrArg (fun z : Fin (m - 2) => ((pairComplEmb hab z : Fin m) : ℕ)) (Fin.ext rfl)

end Delete

/-! ### The two-letter characteristic polynomial -/

variable {K : Type*} [CommRing K]

/-- **The two-letter characteristic polynomial** `χ₂(R, m)` of a set `R` of pairs of positions of
`{1, …, m}`:

`χ₂(R, m) = ∑_{v} q ^ inv(R, v) · ξ₁ ^ #{i : v_i = 1} · ξ₂ ^ #{i : v_i = 2}`,

the sum over the `2 ^ m` words `v` of length `m` in the two letters. Words are tuples
`v : Fin m → Fin 2`, the letters numbered from `0`, and the monomial in the two indeterminates
`ξ₁ = X 0`, `ξ₂ = X 1` of `MvPolynomial (Fin 2) K` is the product `∏ i, X (v i)`, which collects the
letters of `v` with their multiplicities. -/
@[hjo "def_cm_chi_two"]
noncomputable def twoLetterChar (q : K) (m : ℕ) (R : Finset (ℕ × ℕ)) : MvPolynomial (Fin 2) K :=
  ∑ v : Fin m → Fin 2,
    MvPolynomial.C (q ^ #(invSet (finPairs m R) v)) * ∏ i, MvPolynomial.X (v i)

/-- The two-letter polynomial of the empty set of pairs is `(ξ₁ + ξ₂) ^ m`: no word has an
inversion, so the sum is the expansion of that power over the words of length `m`. This is the base
of the induction proving the symmetry. -/
theorem twoLetterChar_empty (q : K) (m : ℕ) :
    twoLetterChar q m (∅ : Finset (ℕ × ℕ)) =
      (MvPolynomial.X 0 + MvPolynomial.X 1 : MvPolynomial (Fin 2) K) ^ m := by
  have hfin : finPairs m (∅ : Finset (ℕ × ℕ)) = ∅ := by ext p; simp
  rw [twoLetterChar]
  simp only [hfin, invSet_empty, Finset.card_empty, pow_zero, map_one, one_mul]
  rw [show (MvPolynomial.X 0 + MvPolynomial.X 1 : MvPolynomial (Fin 2) K)
      = ∑ j : Fin 2, MvPolynomial.X j by simp [Fin.sum_univ_two],
    Fintype.sum_pow]

/-! ### The inversion count at a maximal pair -/

/-- The two letters are ordered `0 < 1`, and that is the only strict inequality between them: a
position carries the larger letter exactly when it does not carry the smaller, which is how the
two-letter analysis reads an inversion of a two-letter word. -/
theorem fin_two_lt_iff {y z : Fin 2} : y < z ↔ y = 0 ∧ z = 1 := by
  revert y z; decide

/-- **The inversion count at a maximal pair.** Let `R` be a transitive attack set on `{1, …, m}`,
let `(a, b)` be a maximal pair of `R`, and let `v` be a word of length `m` in the two letters
carrying the larger letter at `a` and the smaller at `b`, so that `(a, b)` is an inversion of `v`.
Then, writing `R'` for `R ∖ {(a,b)}` and `S` for `{1, …, m} ∖ {a, b}`,

`inv(R', v) = (b - a - 1) + inv((R')_S, v^{(a,b)})`.

The inversions of `R'` split into those internal to `S` and those touching `a` or `b`. The first
block is carried bijectively onto the inversions of the restricted set by the common enumeration of
`S`, which is `HJO.Dyck.getD_sort_range_sdiff_pair`. In the second block the pairs `(j, a)` and
`(b, j)` can never be inversions, `a` carrying the larger letter and `b` the smaller, while the
pairs `(a, j)` and `(j, b)` of `R'` are by `HJO.Dyck.IsMaximalPair.mem_erase_fst_iff` and
`HJO.Dyck.IsMaximalPair.mem_erase_snd_iff` exactly those with `a < j < b`; each such `j` is an
inversion through the first kind if it carries the smaller letter and through the second if it
carries the larger, so exactly once, and the block has `b - a - 1` elements.

The two positions are given as elements of `Fin m` because `HJO.Dyck.removePair` cannot be written
without the proof that they are distinct; `hne` is that proof, and no clause of the statement reads
more of it. -/
@[hjo "lem_cm_inv_split_max"]
theorem IsMaximalPair.card_invSet_erase {a' b' : Fin m} (h : IsTransitiveAttackSet m R)
    (hab : IsMaximalPair R (a' : ℕ) (b' : ℕ)) (hne : a' ≠ b') {v : Fin m → Fin 2}
    (hva : v a' = 1) (hvb : v b' = 0) :
    #(invSet (finPairs m (R.erase ((a' : ℕ), (b' : ℕ)))) v) =
      ((b' : ℕ) - (a' : ℕ) - 1) +
        #(invSet (finPairs (m - 2) (attackRestrict (R.erase ((a' : ℕ), (b' : ℕ)))
            (range m \ ({(a' : ℕ), (b' : ℕ)} : Finset ℕ)))) (removePair hne v)) := by
  classical
  have hcard := card_range_sdiff_pair hne
  have key : ∀ i j : Fin m,
      ((i, j) ∈ invSet (finPairs m (R.erase ((a' : ℕ), (b' : ℕ)))) v ∧
          (i = a' ∨ i = b' ∨ j = a' ∨ j = b')) ↔
        ((i = a' ∧ a' < j ∧ j < b' ∧ v j = 0) ∨ (j = b' ∧ a' < i ∧ i < b' ∧ v i = 1)) := by
    intro i j
    simp only [mem_invSet, mem_finPairs]
    constructor
    · rintro ⟨⟨hpR, hpv⟩, hcase⟩
      obtain ⟨hv2, hv1⟩ := fin_two_lt_iff.1 hpv
      rcases hcase with hc | hc | hc | hc
      · subst hc
        obtain ⟨h1, h2⟩ := (hab.mem_erase_fst_iff h).1 hpR
        exact Or.inl ⟨rfl, Fin.lt_def.2 h1, Fin.lt_def.2 h2, hv2⟩
      · subst hc
        rw [hvb] at hv1; exact absurd hv1 (by decide)
      · subst hc
        rw [hva] at hv2; exact absurd hv2 (by decide)
      · subst hc
        obtain ⟨h1, h2⟩ := (hab.mem_erase_snd_iff h).1 hpR
        exact Or.inr ⟨rfl, Fin.lt_def.2 h1, Fin.lt_def.2 h2, hv1⟩
    · rintro (⟨hc, h1, h2, hv⟩ | ⟨hc, h1, h2, hv⟩)
      · subst hc
        refine ⟨⟨(hab.mem_erase_fst_iff h).2 ⟨Fin.lt_def.1 h1, Fin.lt_def.1 h2⟩, ?_⟩, Or.inl rfl⟩
        rw [hv, hva]; decide
      · subst hc
        refine ⟨⟨(hab.mem_erase_snd_iff h).2 ⟨Fin.lt_def.1 h1, Fin.lt_def.1 h2⟩, ?_⟩,
          Or.inr (Or.inr (Or.inr rfl))⟩
        rw [hv, hvb]; decide
  rw [← Finset.card_filter_add_card_filter_not
    (s := invSet (finPairs m (R.erase ((a' : ℕ), (b' : ℕ)))) v)
    (fun p : Fin m × Fin m => p.1 = a' ∨ p.1 = b' ∨ p.2 = a' ∨ p.2 = b')]
  congr 1
  · rw [← Fin.card_Ioo a' b']
    refine Finset.card_nbij (fun p => if p.1 = a' then p.2 else p.1) (fun p hp => ?_)
      (fun p hp p' hp' hpp' => ?_) fun j hj => ?_
    · rw [Finset.mem_coe, Finset.mem_filter] at hp
      rcases (key p.1 p.2).1 hp with ⟨hc, h1, h2, -⟩ | ⟨hc, h1, h2, -⟩
      · simp only [Finset.mem_coe, Finset.mem_Ioo, hc, ↓reduceIte]
        exact ⟨h1, h2⟩
      · simp only [Finset.mem_coe, Finset.mem_Ioo, h1.ne', ↓reduceIte]
        exact ⟨h1, h2⟩
    · rw [Finset.mem_coe, Finset.mem_filter] at hp hp'
      rcases (key p.1 p.2).1 hp with ⟨hc, h1, h2, hv⟩ | ⟨hc, h1, h2, hv⟩ <;>
        rcases (key p'.1 p'.2).1 hp' with ⟨hc', h1', h2', hv'⟩ | ⟨hc', h1', h2', hv'⟩
      · simp only [hc, hc', ↓reduceIte] at hpp'
        exact Prod.ext (hc.trans hc'.symm) hpp'
      · simp only [hc, h1'.ne', ↓reduceIte] at hpp'
        rw [← hpp'] at hv'
        exact absurd (hv.symm.trans hv') (by decide)
      · simp only [hc', h1.ne', ↓reduceIte] at hpp'
        rw [hpp'] at hv
        exact absurd (hv'.symm.trans hv) (by decide)
      · simp only [h1.ne', h1'.ne', ↓reduceIte] at hpp'
        exact Prod.ext hpp' (hc.trans hc'.symm)
    · rw [Finset.mem_coe, Finset.mem_Ioo] at hj
      by_cases hv : v j = 0
      · refine ⟨(a', j), ?_, by simp⟩
        rw [Finset.mem_coe, Finset.mem_filter]
        exact (key a' j).2 (Or.inl ⟨rfl, hj.1, hj.2, hv⟩)
      · have hv1 : v j = 1 := by revert hv; generalize v j = y; revert y; decide
        refine ⟨(j, b'), ?_, by simp [hj.1.ne']⟩
        rw [Finset.mem_coe, Finset.mem_filter]
        exact (key j b').2 (Or.inr ⟨rfl, hj.1, hj.2, hv1⟩)
  · refine (Finset.card_nbij (fun p => ((pairComplEmb hne p.1 : Fin m), pairComplEmb hne p.2))
      (fun p hp => ?_) (fun p _ p' _ hpp' => ?_) fun p hp => ?_).symm
    · rw [Finset.mem_coe, mem_invSet, mem_finPairs, mem_attackRestrict] at hp
      obtain ⟨⟨-, -, hpR⟩, hpv⟩ := hp
      rw [getD_sort_range_sdiff_pair hne p.1, getD_sort_range_sdiff_pair hne p.2] at hpR
      rw [Finset.mem_coe, Finset.mem_filter]
      refine ⟨mem_invSet.2 ⟨mem_finPairs.2 hpR, hpv⟩, ?_⟩
      simp only [not_or]
      exact ⟨pairComplEmb_ne_left hne _, pairComplEmb_ne_right hne _,
        pairComplEmb_ne_left hne _, pairComplEmb_ne_right hne _⟩
    · obtain ⟨e1, e2⟩ := Prod.mk.injEq .. ▸ hpp'
      exact Prod.ext ((pairComplEmb hne).injective e1) ((pairComplEmb hne).injective e2)
    · rw [Finset.mem_coe, Finset.mem_filter] at hp
      obtain ⟨hp1, hp2⟩ := hp
      simp only [not_or] at hp2
      obtain ⟨j1, hj1⟩ := exists_pairComplEmb_eq hne hp2.1 hp2.2.1
      obtain ⟨j2, hj2⟩ := exists_pairComplEmb_eq hne hp2.2.2.1 hp2.2.2.2
      rw [mem_invSet, mem_finPairs] at hp1
      have hR1 : (((pairComplEmb hne j1 : Fin m) : ℕ), ((pairComplEmb hne j2 : Fin m) : ℕ)) ∈
          R.erase ((a' : ℕ), (b' : ℕ)) := by rw [hj1, hj2]; exact hp1.1
      refine ⟨(j1, j2), ?_, ?_⟩
      · rw [Finset.mem_coe, mem_invSet, mem_finPairs, mem_attackRestrict]
        have hlt : (j1 : ℕ) < (j2 : ℕ) := by
          have hv := h.fst_lt_snd _ (Finset.mem_of_mem_erase hR1)
          exact Fin.lt_def.1 ((pairComplEmb hne).lt_iff_lt.1 (Fin.lt_def.2 hv))
        refine ⟨⟨hlt, by rw [hcard]; exact j2.isLt, ?_⟩, ?_⟩
        · rw [getD_sort_range_sdiff_pair hne j1, getD_sort_range_sdiff_pair hne j2]
          exact hR1
        · change removePair hne v j2 < removePair hne v j1
          rw [removePair_apply, removePair_apply, hj1, hj2]
          exact hp1.2
      · rw [Prod.ext_iff]
        exact ⟨hj1, hj2⟩


/-! ### The two-letter difference at a maximal pair -/

section Difference

open MvPolynomial

/-- **The two-letter difference at a maximal pair.** For a transitive attack set `R` on
`{1, …, m}` and a maximal pair `(a, b)` of `R`, writing `R'` for `R ∖ {(a,b)}` and `S` for
`{1, …, m} ∖ {a, b}`,

`χ₂(R, m) - χ₂(R', m) = (q - 1) q ^ (b-a-1) ξ₁ ξ₂ χ₂((R')_S, m-2)`.

Only the words with the larger letter at `a` and the smaller at `b` contribute: `(a, b)` is an
inversion of exactly those, so for every other word the two exponents of `q` agree and the term
cancels. For such a word the exponent drops by one when the pair is removed, which is the factor
`q - 1`; `HJO.Dyck.IsMaximalPair.card_invSet_erase` splits what is left as `q ^ (b-a-1)` times the
inversion count of the deleted word; and the monomial factors as `ξ₁ξ₂` times the monomial of the
deleted word, one letter of each kind being deleted.

The sum over the surviving words is turned into a sum over the words of length `m - 2` by the map
`v ↦ (v^{(a,b)}, v_a, v_b)`, which is injective by `HJO.Dyck.eq_of_removePair_eq` and therefore
bijective, source and target having `2 ^ m` elements each — the two distinct positions `a` and `b`
force `m ≥ 2`, so the count `2 ^ (m-2) · 2 · 2` is `2 ^ m` with no truncation. -/
@[hjo "lem_cm_chi_two_difference"]
theorem IsMaximalPair.twoLetterChar_sub_twoLetterChar_erase {a b : ℕ}
    (h : IsTransitiveAttackSet m R) (hab : IsMaximalPair R a b)
    (q : K) :
    twoLetterChar q m R - twoLetterChar q m (R.erase (a, b)) =
      C ((q - 1) * q ^ (b - a - 1)) * (X 0 * X 1) *
        twoLetterChar q (m - 2) (attackRestrict (R.erase (a, b))
          (Finset.range m \ ({a, b} : Finset ℕ))) := by
  classical
  have hb : b < m := h.snd_lt _ hab.mem
  have halt : a < b := h.fst_lt_snd _ hab.mem
  have ha : a < m := halt.trans hb
  obtain ⟨a', rfl⟩ : ∃ a' : Fin m, (a' : ℕ) = a := ⟨⟨a, ha⟩, rfl⟩
  obtain ⟨b', rfl⟩ : ∃ b' : Fin m, (b' : ℕ) = b := ⟨⟨b, hb⟩, rfl⟩
  have hne : a' ≠ b' := fun hc => absurd (congrArg Fin.val hc) halt.ne
  have hm : 2 ≤ m := by omega
  have hfp : finPairs m (R.erase ((a' : ℕ), (b' : ℕ))) = (finPairs m R).erase (a', b') := by
    ext p
    simp only [mem_finPairs, Finset.mem_erase]
    refine and_congr_left fun _ => ?_
    rw [not_iff_not, Prod.ext_iff, Prod.ext_iff, Fin.ext_iff, Fin.ext_iff]
  have hmemR : ((a', b') : Fin m × Fin m) ∈ finPairs m R := mem_finPairs.2 hab.mem
  have hsucc : ∀ v : Fin m → Fin 2, v a' = 1 → v b' = 0 →
      #(invSet (finPairs m R) v) = #(invSet (finPairs m (R.erase ((a' : ℕ), (b' : ℕ)))) v) + 1 := by
    intro v h1 h0
    have hin : ((a', b') : Fin m × Fin m) ∈ invSet (finPairs m R) v :=
      mem_invSet.2 ⟨hmemR, by rw [h1, h0]; decide⟩
    have hpos : 0 < #(invSet (finPairs m R) v) := Finset.card_pos.2 ⟨_, hin⟩
    rw [hfp, invSet_erase, Finset.card_erase_of_mem hin]
    omega
  have heq : ∀ v : Fin m → Fin 2, ¬(v a' = 1 ∧ v b' = 0) →
      #(invSet (finPairs m (R.erase ((a' : ℕ), (b' : ℕ)))) v) = #(invSet (finPairs m R) v) := by
    intro v hv
    rw [hfp, invSet_erase, Finset.erase_eq_of_notMem fun hc => ?_]
    exact hv ((fin_two_lt_iff.1 (mem_invSet.1 hc).2).symm.imp id id)
  have hsplit := fun (v : Fin m → Fin 2) (h1 : v a' = 1) (h0 : v b' = 0) =>
    hab.card_invSet_erase h hne h1 h0
  set S : Finset ℕ := Finset.range m \ ({(a' : ℕ), (b' : ℕ)} : Finset ℕ) with hSdef
  set R' : Finset (ℕ × ℕ) := R.erase ((a' : ℕ), (b' : ℕ)) with hR'def
  set N : (Fin (m - 2) → Fin 2) → ℕ :=
    fun w => #(invSet (finPairs (m - 2) (attackRestrict R' S)) w) with hNdef
  set F : (Fin m → Fin 2) → ((Fin (m - 2) → Fin 2) × Fin 2 × Fin 2) :=
    fun v => (removePair hne v, v a', v b') with hFdef
  have hFinj : Function.Injective F := by
    intro v w hvw
    rw [hFdef] at hvw
    obtain ⟨e1, e2, e3⟩ := Prod.mk.injEq .. ▸ (Prod.mk.injEq .. ▸ hvw : _ ∧ _)
    exact eq_of_removePair_eq hne e2 e3 e1
  have hFcard : Fintype.card (Fin m → Fin 2) =
      Fintype.card ((Fin (m - 2) → Fin 2) × Fin 2 × Fin 2) := by
    simp only [Fintype.card_fun, Fintype.card_prod, Fintype.card_fin]
    conv_lhs => rw [show m = m - 2 + 2 from by omega]
    rw [pow_add]
    norm_num
  have hFbij : Function.Bijective F :=
    (Fintype.bijective_iff_injective_and_card F).2 ⟨hFinj, hFcard⟩
  rw [twoLetterChar, twoLetterChar, ← Finset.sum_sub_distrib]
  rw [Fintype.sum_bijective F hFbij _
    (fun t => if t.2.1 = 1 ∧ t.2.2 = 0 then
      (C ((q - 1) * q ^ ((b' : ℕ) - (a' : ℕ) - 1)) * (X 0 * X 1)) *
        (C (q ^ N t.1) * ∏ j, X (t.1 j)) else 0) ?_]
  · rw [Fintype.sum_prod_type]
    have hinner : ∀ w : Fin (m - 2) → Fin 2,
        (∑ t : Fin 2 × Fin 2, if t.1 = 1 ∧ t.2 = 0 then
          (C ((q - 1) * q ^ ((b' : ℕ) - (a' : ℕ) - 1)) * (X 0 * X 1)) *
            (C (q ^ N w) * ∏ j, X (w j)) else 0) =
          (C ((q - 1) * q ^ ((b' : ℕ) - (a' : ℕ) - 1)) * (X 0 * X 1)) *
            (C (q ^ N w) * ∏ j, X (w j)) := by
      intro w
      rw [Fintype.sum_prod_type]
      simp [Fin.sum_univ_two]
    simp only [hinner]
    rw [twoLetterChar, Finset.mul_sum]
  · intro v
    by_cases hv : v a' = 1 ∧ v b' = 0
    · obtain ⟨h1, h0⟩ := hv
      rw [hFdef]
      simp only [h1, h0, and_self, ↓reduceIte]
      have hprod : ∏ i, (X (v i) : MvPolynomial (Fin 2) K) =
          (∏ j, X (removePair hne v j)) * (X 1 * X 0) := by
        rw [← prod_removePair hne (fun y => (X y : MvPolynomial (Fin 2) K)) v, h1, h0]
      rw [hsucc v h1 h0, hsplit v h1 h0, hprod]
      simp only [map_mul, map_pow, map_sub, map_one, pow_add, pow_succ]
      ring
    · rw [hFdef]
      simp only [hv, ↓reduceIte]
      rw [heq v hv, sub_self]

/-! ### The two-letter polynomial is symmetric -/

/-- The two-letter polynomial of the empty set of pairs is symmetric: it is `(ξ₁ + ξ₂) ^ m`, and
that is the base of the induction proving the general case. -/
theorem rename_swap_twoLetterChar_empty (q : K) (m : ℕ) :
    rename (Equiv.swap (0 : Fin 2) 1) (twoLetterChar q m (∅ : Finset (ℕ × ℕ))) =
      twoLetterChar q m ∅ := by
  rw [twoLetterChar_empty, map_pow, map_add, rename_X, rename_X,
    Equiv.swap_apply_left, Equiv.swap_apply_right, add_comm]

/-- The induction behind `HJO.Dyck.rename_swap_twoLetterChar`: the symmetry of `χ₂(R, m)` for every
transitive attack set `R` of size at most `n`, over all lengths `m` at once.

At `R = ∅` the polynomial is `(ξ₁ + ξ₂) ^ m`. Otherwise a maximal pair `(a, b)` is chosen; both
`R ∖ {(a,b)}`, by `HJO.Dyck.IsTransitiveAttackSet.erase`, and its restriction `(R ∖ {(a,b)})_S`, by
`HJO.Dyck.isTransitiveAttackSet_attackRestrict`, are transitive attack sets of size at most `n` —
the second by `HJO.Dyck.card_attackRestrict_le` — so both are symmetric by induction, and
`HJO.Dyck.IsMaximalPair.twoLetterChar_sub_twoLetterChar_erase` writes `χ₂(R, m)` as the sum of the
first and a scalar multiple of `ξ₁ξ₂` times the second. -/
theorem rename_swap_twoLetterChar_of_card_le (q : K) :
    ∀ (n m : ℕ) (R : Finset (ℕ × ℕ)), #R ≤ n → IsTransitiveAttackSet m R →
    rename (Equiv.swap (0 : Fin 2) 1) (twoLetterChar q m R) = twoLetterChar q m R := by
  intro n
  induction n with
  | zero =>
    intro m R hc _
    obtain rfl : R = ∅ := Finset.card_eq_zero.1 (Nat.le_zero.1 hc)
    exact rename_swap_twoLetterChar_empty q m
  | succ n ih =>
    intro m R hc hR
    rcases R.eq_empty_or_nonempty with rfl | hRne
    · exact rename_swap_twoLetterChar_empty q m
    obtain ⟨a, b, hab⟩ := exists_isMaximalPair hRne
    have hR' : IsTransitiveAttackSet m (R.erase (a, b)) := hR.erase hab
    have hc' : #(R.erase (a, b)) ≤ n := by
      rw [Finset.card_erase_of_mem hab.mem]
      have : 0 < #R := Finset.card_pos.2 hRne
      omega
    have hb : b < m := hR.snd_lt _ hab.mem
    have ha : a < m := (hR.fst_lt_snd _ hab.mem).trans hb
    have hcS : #(Finset.range m \ ({a, b} : Finset ℕ)) = m - 2 :=
      card_range_sdiff_pair (a' := ⟨a, ha⟩) (b' := ⟨b, hb⟩)
        (Fin.ne_of_val_ne (hR.fst_lt_snd _ hab.mem).ne)
    have hrest : IsTransitiveAttackSet (m - 2)
        (attackRestrict (R.erase (a, b)) (Finset.range m \ ({a, b} : Finset ℕ))) := by
      have hx := isTransitiveAttackSet_attackRestrict
        (Finset.range m \ ({a, b} : Finset ℕ)) hR'
      rwa [hcS] at hx
    have h1 := ih m _ hc' hR'
    have h2 := ih (m - 2) _ ((card_attackRestrict_le _ _).trans hc') hrest
    have hd := hab.twoLetterChar_sub_twoLetterChar_erase hR q
    have hsum : twoLetterChar q m R = twoLetterChar q m (R.erase (a, b)) +
        C ((q - 1) * q ^ (b - a - 1)) * (X 0 * X 1) *
          twoLetterChar q (m - 2) (attackRestrict (R.erase (a, b))
            (Finset.range m \ ({a, b} : Finset ℕ))) := by
      rw [← hd]; ring
    rw [hsum, map_add, h1]
    simp only [map_mul, rename_C, rename_X, Equiv.swap_apply_left, Equiv.swap_apply_right]
    rw [h2, mul_comm (X (1 : Fin 2)) (X 0)]


/-- **The two-letter polynomial is symmetric**: for every `m` and every transitive attack set `R` on
`{1, …, m}`, `χ₂(R, m)` is invariant under interchanging the two indeterminates `ξ₁` and `ξ₂`.

This is `HJO.Dyck.rename_swap_twoLetterChar_of_card_le` at `n = #R`. The transitivity of `R` is used
through the whole induction and not only at the top: the pair removed at each step is maximal, and
it is transitivity that makes the remainder and its restriction transitive again. -/
@[hjo "lem_cm_chi_two_symmetric"]
theorem rename_swap_twoLetterChar (q : K) {m : ℕ} {R : Finset (ℕ × ℕ)}
    (hR : IsTransitiveAttackSet m R) :
    rename (Equiv.swap (0 : Fin 2) 1) (twoLetterChar q m R) = twoLetterChar q m R :=
  rename_swap_twoLetterChar_of_card_le q #R m R le_rfl hR

end Difference

end HJO.Dyck
