/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.DyckAttackSets
public import HJO.DyckInversions
public import HJO.DyckWordMonomial
public meta import HJO.Attr

/-! # The characteristic series of a marked Dyck path

The definition `HJO.Dyck.pathMarkedCharSeries`: for a Dyck path `π` of length `n` and a marking
`T ⊆ c(π)` of its corners,

`χ(π, T) = ∑_w q ^ inv(At(π), w) · x_w ∈ 𝒫`,

the sum over the labellings `w` with `w_i > w_j` for every `(i, j) ∈ T`. The two extremes are
`T = ∅`, which is the unconstrained `χ(π)` of `HJO.Dyck.pathCharSeries`, and `T = c(π)`, which is
Carlsson and Mellit's weighted `χ(π, wt)` at the identically-zero weight; the general `T` is what
`HJO.Mellit.constantCoeff_psiWord_one_mem_lambdaComp_and_map_eq_sweepChar` needs, its constraint set
being a proper subset of the corners of the relevant square path.

The constraint is *exactly* that every pair of `T` is an inversion of `w`: `(i, j) ∈ T` asks for
`w j < w i`, which is the membership condition of `HJO.Dyck.invSet`. So the marking and the weight
read the labelling through the same relation, one as a constraint and the other as a count, and
`HJO.Dyck.IsMarkedLabelling` is stated so.

## Main definitions

* `HJO.Dyck.IsMarkedLabelling`: the constraint, `w j < w i` for every `(i, j) ∈ T`.
* `HJO.Dyck.markedCharSeries`: `χ(R, n, T)`, the series at an arbitrary finite set `R` of pairs.
* `HJO.Dyck.pathMarkedCharSeries`: `χ(π, T) = χ(At(π), n, T)`, the main definition.

## Main results

The definition is used through these, not by unfolding it.

* `HJO.Dyck.coeff_markedCharSeries`: the coefficient of a monomial is the finite sum of
  `q ^ inv(R, w)` over the *marked* labellings `w` with that exponent vector — the defining
  property.
* `HJO.Dyck.coeff_markedCharSeries_of_support_subset`: the same sum over the labellings with letters
  in any finite set containing the letters of the monomial, the form in which a bound on the letters
  is chosen freely.
* `HJO.Dyck.coeff_pathMarkedCharSeries_eq_coeff_sum_wordMonomial` and its set form: `χ(π, T)` is the
  displayed sum of the monomials `HJO.Sym.wordMonomial`, restricted to the marked labellings.
* `HJO.Dyck.coeff_markedCharSeries_eq_zero_of_sum_ne`: only monomials of total degree `n` occur.
* `HJO.Dyck.markedCharSeries_congr`: which pairs of `R` and of `T` the series reads.

## Implementation notes

*The series is built coefficient by coefficient*, as the `χ(R, n)` must be: the sum has
infinitely many terms and is nevertheless an element of `𝒫`, because `x_w` is the monomial at the
exponent vector of `w`, so only the finitely many labellings with a given exponent vector contribute
to a given monomial. That finite sum *is* the definition here, and
`coeff_markedCharSeries_eq_coeff_sum_wordMonomial` is the identification with the displayed sum.

*The set of pairs `R` and the marking `T` are both `Finset (ℕ × ℕ)`, and the labelling is a tuple
`Fin n → ℕ`*, read along `Fin.val`: this is the carrier of `HJO.Dyck.attackSet` and of
`HJO.Dyck.corner`, so `χ(π, T)` may be formed at the attack set of a path and at a set of its
corners, and it is the carrier of `HJO.Sym.wordMonomial`. Positions are indexed from `0` where
Carlsson and Mellit count from `1`.

*The two junk conventions are not the same for `R` and for `T`, and the difference is real.* A pair
outside `range n ×ˢ range n` is read by neither. A pair on the diagonal is discarded by `R`, since
`w i < w i` is false, so it is never an inversion; but a diagonal pair in `T` is *not* discarded —
it makes the constraint unsatisfiable and the series `0`. So `markedCharSeries_congr` quantifies
over the off-diagonal pairs for `R` and over all pairs inside the square for `T`. Neither case
arises for the sets formed from a Dyck path: a corner of a square Dyck path is `(x k - 1, k)` with
`x k ≤ k` and `0 < x k`, hence off the diagonal and inside the square.

*No hypothesis is imposed on `R`, on `T` or on `x`.* The sum reads of `R` and `T` only which pairs
they contain, so `T ⊆ c(π)` and `π` being a square Dyck path are hypotheses of the *lemmas* about
`χ(π, T)`, exactly as `HJO.Dyck.charSeries` is stated before any
condition on `R` is imposed.

*The unmarked series is the case `T = ∅`.* `HJO.Dyck.charSeries`, the unconstrained `χ(R, n)`, is
*defined* in `HJO/CarlssonMellit/CharSeries.lean` as `markedCharSeries q n R ∅` rather than written
out again, `IsMarkedLabelling ∅` being vacuous.

*The weight is an element of an arbitrary commutative ring*, rather than an element `q` of the base
field `𝕜 = ℚ(q, u)`, matching `HJO.Sym.AlphabetSeries` and `HJO.Sym.wordMonomial`: the
characteristic functions of partial Dyck paths live in `AlphabetSeries (MvPolynomial (Fin k) K)`, so
the series is needed over a coefficient ring that is not the base field.

## References

E. Carlsson and A. Mellit, *A
proof of the shuffle conjecture*, §3.1, and A. Mellit's Theorem 3.7, the marked form. Consumed by
`HJO.Dyck.pathMarkedCharSeries_inclusion_exclusion`, the corner inclusion--exclusion
`(1 - q)^{#T} χ(π, T) = ∑_{S ⊆ T} (-1)^{#S} χ(π_S)`, and by
`HJO.Mellit.map_constantCoeff_markedWordOp'`, which presents `χ(π, T)` as a word in the operators
`d_±`; through the latter it reaches
`HJO.Mellit.constantCoeff_psiWord_one_mem_lambdaComp_and_map_eq_sweepChar`.
-/

@[expose] public section

open Finset HJO.Sym

namespace HJO.Dyck

/-- The labelling `w` is *marked* by `T`: every pair `(i, j) ∈ T` inside the square has
`w_i > w_j`, a strict descent at each marked corner. Equivalently every such pair is an
inversion of `w`, which is the membership condition of `HJO.Dyck.invSet`. Pairs of `T` outside
`range n ×ˢ range n` impose nothing; a pair on the diagonal makes the condition unsatisfiable. -/
def IsMarkedLabelling {n : ℕ} (T : Finset (ℕ × ℕ)) (w : Fin n → ℕ) : Prop :=
  ∀ p : Fin n × Fin n, ((p.1 : ℕ), (p.2 : ℕ)) ∈ T → w p.2 < w p.1

instance instDecidableIsMarkedLabelling {n : ℕ} (T : Finset (ℕ × ℕ)) (w : Fin n → ℕ) :
    Decidable (IsMarkedLabelling T w) := by
  unfold IsMarkedLabelling; infer_instance

/-- Every labelling is marked by the empty marking. -/
@[simp]
theorem isMarkedLabelling_empty {n : ℕ} (w : Fin n → ℕ) : IsMarkedLabelling ∅ w :=
  fun _ h => absurd h (notMem_empty _)

/-- Being marked is the containment of `T`, read on the positions, in the inversion set. -/
theorem isMarkedLabelling_iff_subset_invSet {n : ℕ} {T : Finset (ℕ × ℕ)} {w : Fin n → ℕ} :
    IsMarkedLabelling T w ↔
      ({p : Fin n × Fin n | ((p.1 : ℕ), (p.2 : ℕ)) ∈ T} : Finset (Fin n × Fin n)) ⊆
        invSet {p : Fin n × Fin n | ((p.1 : ℕ), (p.2 : ℕ)) ∈ T} w := by
  rw [Finset.subset_iff]
  constructor
  · intro h p hp
    exact mem_invSet.2 ⟨hp, h p ((mem_filter_univ p).1 hp)⟩
  · intro h p hp
    exact (mem_invSet.1 (h ((mem_filter_univ p).2 hp))).2

/-- The characteristic series `χ(R, n, T) = ∑_w q ^ inv(R, w) · x_w` of a finite set `R` of pairs
of positions and a marking `T`, the sum being over the labellings `w` of the `n` positions that are
marked by `T`. Only finitely many labellings contribute to each monomial, so the series is given one
coefficient at a time: the coefficient of the monomial with exponent vector `d` is the sum of
`q ^ inv(R, w)` over the marked labellings `w` whose exponent vector is `d`. -/
noncomputable def markedCharSeries {K : Type*} [CommRing K] (q : K) (n : ℕ)
    (R T : Finset (ℕ × ℕ)) : AlphabetSeries K := fun d =>
  ∑ w ∈ {w ∈ Fintype.piFinset fun _ : Fin n => d.support |
      wordExponent w = d ∧ IsMarkedLabelling T w},
    q ^ #(invSet {p : Fin n × Fin n | ((p.1 : ℕ), (p.2 : ℕ)) ∈ R} w)

/-- **The characteristic series `χ(π, T) = χ(At(π), n, T)` of the marked Dyck path `(π, T)`**, where
`π` has coarea sequence `x`: the labellings of its `n` rows that carry a strict descent at every
marked corner, each weighted by `q` to the number of attacking pairs it inverts. At `T = ∅` this is
the unconstrained `χ(π)` of `HJO.Dyck.pathCharSeries`; at `T = c(π)` it is Carlsson and Mellit's
weighted `χ(π, wt)` at the identically-zero weight. -/
@[hjo "def_cm_chi_zero"]
noncomputable abbrev pathMarkedCharSeries {K : Type*} [CommRing K] (q : K) {n : ℕ}
    (x : Fin n → ℕ) (T : Finset (ℕ × ℕ)) : AlphabetSeries K :=
  markedCharSeries q n (attackSet x) T

variable {K : Type*} [CommRing K] {q : K} {n : ℕ} {R T : Finset (ℕ × ℕ)} {d : ℕ →₀ ℕ}

/-- The coefficient of a monomial in `χ(R, n, T)`, with the labellings summed over cut out of the
tuples with letters in any finite set `s` containing the letters of the monomial: the form in which
a bound on the letters is chosen. -/
theorem coeff_markedCharSeries_of_support_subset {s : Finset ℕ} (hs : d.support ⊆ s) :
    MvPowerSeries.coeff d (markedCharSeries q n R T) =
      ∑ w ∈ {w ∈ Fintype.piFinset fun _ : Fin n => s |
          wordExponent w = d ∧ IsMarkedLabelling T w},
        q ^ #(invSet {p : Fin n × Fin n | ((p.1 : ℕ), (p.2 : ℕ)) ∈ R} w) := by
  rw [MvPowerSeries.coeff_apply]
  change ∑ w ∈ _, _ = _
  refine Finset.sum_congr (Finset.ext fun w => ?_) fun _ _ => rfl
  simp only [mem_filter, Fintype.mem_piFinset]
  exact ⟨fun ⟨_, h⟩ => ⟨fun k => hs (h.1 ▸ (mem_support_wordExponent w (w k)).2 ⟨k, rfl⟩), h⟩,
    fun ⟨_, h⟩ => ⟨fun k => h.1 ▸ (mem_support_wordExponent w (w k)).2 ⟨k, rfl⟩, h⟩⟩

/-- **The defining property of the marked characteristic series**: the coefficient of the monomial
with exponent vector `d` is the finite sum of `q ^ inv(R, w)` over the labellings `w` of exponent
vector `d` that are marked by `T`. -/
theorem coeff_markedCharSeries :
    MvPowerSeries.coeff d (markedCharSeries q n R T) =
      ∑ w ∈ {w ∈ Fintype.piFinset fun _ : Fin n => d.support |
          wordExponent w = d ∧ IsMarkedLabelling T w},
        q ^ #(invSet {p : Fin n × Fin n | ((p.1 : ℕ), (p.2 : ℕ)) ∈ R} w) :=
  MvPowerSeries.coeff_apply _ _

/-- **The marked characteristic series is the displayed sum**
`χ(π, T) = ∑_w q ^ inv(R, w) · x_w`, the sum over the marked labellings: on the monomials supported
in a finite set `s` of letters, `χ(R, n, T)` agrees with the honest finite sum of
`q ^ inv(R, w) · x_w` over the marked labellings with letters in `s`. Every monomial is supported in
some such `s`, so this determines `χ(R, n, T)` and identifies it with the series
summed over all marked labellings; that sum cannot be formed in `𝒫`, which is why the definition
is coefficientwise. -/
theorem coeff_markedCharSeries_eq_coeff_sum_wordMonomial {s : Finset ℕ} (hs : d.support ⊆ s) :
    MvPowerSeries.coeff d (markedCharSeries q n R T) =
      MvPowerSeries.coeff d (∑ w ∈ {w ∈ Fintype.piFinset fun _ : Fin n => s |
          IsMarkedLabelling T w},
        q ^ #(invSet {p : Fin n × Fin n | ((p.1 : ℕ), (p.2 : ℕ)) ∈ R} w) • wordMonomial K w) := by
  rw [coeff_markedCharSeries_of_support_subset hs, map_sum]
  rw [show {w ∈ Fintype.piFinset fun _ : Fin n => s | wordExponent w = d ∧ IsMarkedLabelling T w}
      = {w ∈ {w ∈ Fintype.piFinset fun _ : Fin n => s | IsMarkedLabelling T w} |
        wordExponent w = d} from Finset.ext fun w => by
      simp only [mem_filter]; exact ⟨fun h => ⟨⟨h.1, h.2.2⟩, h.2.1⟩, fun h => ⟨h.1.1, h.2, h.1.2⟩⟩,
    Finset.sum_filter]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [map_smul, coeff_wordMonomial, smul_eq_mul]
  by_cases h : wordExponent w = d
  · simp [h]
  · simp [h, Ne.symm h]

/-- **`HJO.Dyck.pathMarkedCharSeries` is the display**: the value `χ(π, T)` at a path with coarea
sequence `x` is the sum of `q ^ inv(At(π), w) · x_w` over the labellings `w` with `w_i > w_j` at
every `(i, j) ∈ T`, read one monomial at a time. -/
@[hjo "def_cm_chi_zero"]
theorem coeff_pathMarkedCharSeries_eq_coeff_sum_wordMonomial {x : Fin n → ℕ} {s : Finset ℕ}
    (hs : d.support ⊆ s) :
    MvPowerSeries.coeff d (pathMarkedCharSeries q x T) =
      MvPowerSeries.coeff d (∑ w ∈ {w ∈ Fintype.piFinset fun _ : Fin n => s |
          IsMarkedLabelling T w},
        q ^ #(invSet {p : Fin n × Fin n | ((p.1 : ℕ), (p.2 : ℕ)) ∈ attackSet x} w) •
          wordMonomial K w) :=
  coeff_markedCharSeries_eq_coeff_sum_wordMonomial hs

/-- Only monomials of total degree `n` occur in `χ(R, n, T)`: it is homogeneous of degree `n`, the
labellings summed over having `n` letters. -/
theorem coeff_markedCharSeries_eq_zero_of_sum_ne (h : (d.sum fun _ e => e) ≠ n) :
    MvPowerSeries.coeff d (markedCharSeries q n R T) = 0 := by
  have hempty : {w ∈ Fintype.piFinset fun _ : Fin n => d.support |
      wordExponent w = d ∧ IsMarkedLabelling T w} = ∅ := by
    refine Finset.eq_empty_iff_forall_notMem.2 fun w hw => ?_
    rw [mem_filter] at hw
    have hall : ∀ k, w k ∈ d.support := fun k =>
      hw.2.1 ▸ (mem_support_wordExponent w (w k)).2 ⟨k, rfl⟩
    have hsum := sum_wordExponent w hall
    rw [hw.2.1] at hsum
    exact h (by simpa [Finsupp.sum] using hsum)
  rw [coeff_markedCharSeries, hempty, Finset.sum_empty]

/-- **Which pairs the series reads**: a pair of `R` is read as a pair of *distinct* positions below
`n`, a pair `(i, i)` never being an inversion; a pair of `T` is read as a pair of positions below
`n`, the diagonal *included*, a diagonal pair making the constraint unsatisfiable. So two data
agreeing there give the same series. -/
theorem markedCharSeries_congr {R' T' : Finset (ℕ × ℕ)}
    (hR : ∀ i j : ℕ, i < n → j < n → i ≠ j → ((i, j) ∈ R ↔ (i, j) ∈ R'))
    (hT : ∀ i j : ℕ, i < n → j < n → ((i, j) ∈ T ↔ (i, j) ∈ T')) :
    markedCharSeries q n R T = markedCharSeries q n R' T' := by
  have hmark : ∀ w : Fin n → ℕ, IsMarkedLabelling T w ↔ IsMarkedLabelling T' w := fun w =>
    forall_congr' fun p => imp_congr_left (hT _ _ p.1.isLt p.2.isLt)
  funext d
  refine Finset.sum_congr (Finset.filter_congr fun w _ => by rw [hmark w]) fun w _ => ?_
  congr 2
  refine Finset.ext fun p => ?_
  simp only [mem_invSet, mem_filter, Finset.mem_univ, true_and]
  refine and_congr_left fun hlt => hR _ _ p.1.isLt p.2.isLt fun he => ?_
  rw [Fin.val_inj.1 he] at hlt
  exact absurd hlt (lt_irrefl _)

/-- The monomial `x_i ^ n` in a single letter occurs in `χ(R, n, T)` with coefficient `1` when the
marking is empty and `0` as soon as the marking contains a pair of positions below `n`: the constant
labelling is the only one with that exponent vector, it inverts no pair, and it carries no strict
descent. This is the non-degeneracy witness, and it separates the markings. -/
theorem coeff_markedCharSeries_single (q : K) (n : ℕ) (R T : Finset (ℕ × ℕ)) (i : ℕ) :
    MvPowerSeries.coeff (Finsupp.single i n) (markedCharSeries q n R T) =
      if IsMarkedLabelling T (fun _ : Fin n => i) then 1 else 0 := by
  have hexp : wordExponent (fun _ : Fin n => i) = Finsupp.single i n := by
    simp [wordExponent, Finset.sum_const, Finsupp.smul_single]
  have hfib : {w ∈ Fintype.piFinset fun _ : Fin n => (Finsupp.single i n : ℕ →₀ ℕ).support |
      wordExponent w = Finsupp.single i n ∧ IsMarkedLabelling T w} =
      {w ∈ ({fun _ => i} : Finset (Fin n → ℕ)) | IsMarkedLabelling T w} := by
    refine Finset.ext fun w => ?_
    simp only [mem_filter, Fintype.mem_piFinset, mem_singleton]
    refine ⟨fun ⟨hw, _, hm⟩ => ⟨funext fun k =>
      Finset.mem_singleton.1 (Finsupp.support_single_subset (hw k)), hm⟩, ?_⟩
    rintro ⟨rfl, hm⟩
    exact ⟨fun k => hexp ▸ (mem_support_wordExponent _ i).2 ⟨k, rfl⟩, hexp, hm⟩
  rw [coeff_markedCharSeries, hfib, Finset.sum_filter, Finset.sum_singleton, invSet_const,
    Finset.card_empty, pow_zero]

end HJO.Dyck
