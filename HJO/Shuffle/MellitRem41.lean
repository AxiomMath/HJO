/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.Shuffle.MellitRem41Level

/-! # `HJO.Mellit.isAdmissibleColouring_and_sum_sweepChar_eq_smul_dsc`: the composition sum as an
invariant, reduced

`HJO.Mellit.Rem41` is one of the four conjuncts of `HJO.Mellit.MellitInput`, the input of the
shuffle side. The proof of `HJO.Mellit.isAdmissibleColouring_and_sum_sweepChar_eq_smul_dsc` is
one paragraph, and it cites exactly one lemma: `HJO.Mellit.sweepComputes`, "the sweep process
computes the summand". Everything else in that paragraph is the reading-off of the sweep word at the
`N + 1` diagonal points of the rectangle, and the identification of the paths of return composition
`α` with the paths coloured `c_α`.

This file carries out all of that, and nothing else is needed: the result is
`HJO.Mellit.rem41_of_sweepComputes`, which derives the clause from the single named `Prop`
`HJO.Mellit.SweepComputes` — the statement of `HJO.Mellit.sweepComputes`, whose proof belongs to
Mellit's Section 4 and is given in `HJO/CarlssonMellit/LoweringSumClosed.lean`. So this file
**reduces** the clause, and what remains of it is precisely that lemma.

## The across-`ι` shape

`HJO.Mellit.Rem41` is an identity in `𝒫`, not in `Λ`: its left-hand side is a sum of
characteristic functions and its right-hand side is `ι(u^{N-ℓ} d_-^ℓ D_{η,c_α})`. That is the
shape of the statement, and everything below respects it: the
reading of `V_0 = Λ` is the constant coefficient of `Λ[y_1, y_2, …]`, and the realisation is
applied to that.

## What is proved here

The geometry of a separating level is in `HJO/Shuffle/MellitRem41Level.lean`: there
`HJO.Mellit.colouring_eq_compColouring_iff` identifies the paths coloured `c_α` with the paths of
return composition `α`, and `HJO.Mellit.dsc_compColouring_eq_sum_partialSweepWord` turns
`D_{η,c_α}` into `∑_{P̂} W_η(P̂)(1)`. What is left, and is here:

* `HJO.Mellit.sortByRank_sweptRegion_eq` — the `List.mergeSort` listing of the swept region *is* the
  listing of the diagonal points followed by the listing of the points above the level. This is what
  makes the "the sweep word is the operators at the diagonal points after the partial
  word `W_η(P̂)`" an identity rather than a picture; it rests on the rank being injective there,
  `HJO.Mellit.pointRank_inj_of_mem_sweptRegion`.
* `HJO.Mellit.sweepWord_vac_eq` — **`W(P̂)(1) = u^{N-ℓ} d_-^ℓ(W_η(P̂)(1))`**, the proof
  paragraph above, checked clause by clause: the returns below the top carry event type `B`
  and contribute `d_-` (`HJO.Mellit.eventType_diag_eq_B`), the corner carries type `D` with exponent
  `0` and contributes the identity (`HJO.Mellit.eventType_corner`,
  `HJO.Mellit.sweepRight_corner`), and the remaining `N - ℓ` diagonal points carry type `E` and
  contribute `u` each (`HJO.Mellit.nonRetCount_top`). The graded indices of `d_-` come out right:
  the `j`-th return carries `d_-` of index `j + 1` (`HJO.Mellit.sweepWidth_diag_of_return`), so the
  composite is `d_-` of index `1` after … after `d_-` of index `ℓ`, which is `HJO.Mellit.lowerRun`.
* `HJO.Mellit.rem41_of_sweepComputes` — the reduction.

## The graded `d_-`, and the pinning hypotheses

`HJO.Mellit.rem41_of_sweepComputes` pins the abstract sweep system to the concrete operators by two
hypotheses, in the style of `HJO.Mellit.rhsSumsAgree_of_chi_eq_sweepChar`, which discharged
`RhsSumsAgree` the same way: `χ` is `HJO.Paths.sweepChar`, and `proj ∘ d_-^ℓ ∘ D` is the
substrate's.

The second is not the conjunction of two separate pinnings, and cannot be: `HJO.Sweep.dminus` reads
`d_-` as a map `V_k → V_{k-1}`, so the `d_-^ℓ` is the composite of `ℓ` *different*
operators, whereas `HJO.Mellit.SweepSystem.dminus` is a single endomorphism raised to the power `ℓ`.
No faithful sweep system can have `SweepSystem.dminus` equal to `HJO.Sweep.dminus q k` for every
`k`, the graded pieces being nested rather than a direct sum, so there is nothing to pin it to on
its own. This is a defect of the top layer's encoding, not of the mathematics, and the pinning is
therefore stated for the composite; `HJO.Mellit.lowerRun` is the composite the sweep actually
produces, and `HJO.Mellit.sweepWidth_diag_of_return` is why those are its indices. The pinning is
scoped to the colourings `c_α`, where it is consistent: `c_α` determines `N` by
`HJO.Mellit.sum_eq_of_compColouring_eq`, so the `N` that `HJO.Mellit.dsc` needs and
`HJO.Mellit.SweepSystem.D` lacks is recoverable.

## Where genericity is spent: nowhere

`HJO.Mellit.rem41_of_sweepComputes` carries no hypothesis on `q` or `u` — not `q ≠ 0`, not
`u ≠ 0`, not `AlgebraicIndependent ℤ ![q, u]`. It carries **less** than the standing
hypotheses on the rectangle too: `0 < a`, `0 < b` and `Nat.Coprime a b`, where the standing
hypothesis is `1 < a < b`. Coprimality is genuinely used and is not cosmetic — it is what makes the
diagonal points of the swept region exhaust `(ak, bk)`, `0 ≤ k ≤ N`
(`HJO.Mellit.filter_diag_sweptRegion`).

The reason there is no genericity is structural, and `HJO.Mellit.sub_length_nonneg` records it: the
exponent `N - ℓ` of `u` on the right of the clause is **nonnegative**, a composition having at most
as many parts as its sum, so no inverse is taken. The clause it shares that scalar family with,
`HJO.Mellit.MellitInduction`, carries the opposite exponent `ℓ - N ≤ 0` on `qu`, and that is where
`HJO.Mellit.not_mellitInput_unrestricted` finds three of the four clauses of
`HJO.Mellit.MellitInput` jointly contradictory at `q = 0`. `Rem41` is the clause that *transports*
that vanishing to the path sum; it is not the clause that is false. The reduction also covers
`N = 0`, which is a live instance of the clause — `SeparatesDiagonal a b 0 η` says only `0 ≤ η` —
and `HJO.Mellit.dsc_empty_eq_zero` is the corner check at the other end.

## A redundant conjunct

`HJO.Mellit.isAdmissibleColouring_and_sum_sweepChar_eq_smul_dsc` asserts, besides the displayed
identity, that `c_α` *is* an admissible colouring at `η`. `HJO.Mellit.Rem41` omits that conjunct,
which is safe — the predicate is a hypothesis of `HJO.Mellit.MellitInput`, so omitting a conjunct
only weakens what is assumed — and `HJO.Mellit.colouring_eq_compColouring_iff` reduces it to a
statement with no operators in it, the existence of an above-diagonal `(aN, bN)`-path of return
composition `α`.

The defect in `HJO.Paths.abovePointRank_lt_iff` and `HJO.Paths.abovePointRank_injOn` is recorded in
`HJO/Shuffle/MellitRem41Level.lean`.

## Implementation notes

The results here are steps of the *proof* of
`HJO.Mellit.isAdmissibleColouring_and_sum_sweepChar_eq_smul_dsc` rather than separate results, and
`HJO.Mellit.SweepComputes` is a predicate encoding the statement of a lemma, which is the convention
`HJO.Mellit.Rem41` itself follows.

## References

`HJO.Mellit.isAdmissibleColouring_and_sum_sweepChar_eq_smul_dsc`, and its citations
`HJO.Mellit.sweepComputes`, `HJO.Paths.eventType`, `HJO.Mellit.sweepWord`,
`HJO.Mellit.partialSweepWord`, `HJO.Mellit.dsc`, `HJO.Mellit.colouring`,
`HJO.Mellit.IsAdmissibleColouring`, `HJO.Mellit.compColouring`, `HJO.Sweep.dminus`,
`HJO.Sym.IsRealisation`; `HJO.Paths.abovePointRank_lt_iff`, `HJO.Paths.abovePointRank_injOn`,
`HJO.Mellit.isAdmissibleColouring_empty_and_dsc_eq_one`,
`HJO.Mellit.partialSweepWord_eq_of_levelTrace_eq`. Transcribing A. Mellit, *Toric braids and
`(m, n)`-parking functions*, Remark 4.1 and §4.
-/

@[expose] public section

open Finset

namespace HJO.Mellit

open ParkingFunctions Paths Sweep

variable {a b N : ℕ}

/-! ### Splitting the rank listing at the level

`HJO.Mellit.sweepWord` and `HJO.Mellit.partialSweepWord` list their index sets by `List.mergeSort`,
so the only facts available about the two lists are that each is sorted by rank and enumerates its
set. Because the rank is injective on the swept region those two facts determine the list, which is
what lets the full listing be split into the diagonal points followed by the points above the
level. -/

/-- **A list sorted by a key injective on it is determined by its members.** Mathlib's
`List.eq_of_perm_of_sorted` wants a globally antisymmetric relation, and `≤` pulled back along the
rank is antisymmetric only where the rank is injective; so the comparison is made through the key,
where `ℤ` supplies the antisymmetry. -/
private theorem eq_of_perm_of_pairwise_key {α : Type*} {K : α → ℤ} :
    ∀ {l₁ l₂ : List α}, l₁.Perm l₂ → l₁.Pairwise (fun x z => K x ≤ K z) →
      l₂.Pairwise (fun x z => K x ≤ K z) →
      (∀ x ∈ l₁, ∀ z ∈ l₁, K x = K z → x = z) → l₁ = l₂ := by
  intro l₁
  induction l₁ with
  | nil => exact fun hp _ _ _ => (hp.symm.eq_nil).symm
  | cons x t ih =>
    intro l₂ hp h₁ h₂ hinj
    match l₂ with
    | [] => exact absurd hp.eq_nil (by simp)
    | (w :: s) =>
      have hxw : x = w := by
        by_contra hne
        have hw2 : w ∈ t := by
          rcases List.mem_cons.1 (hp.mem_iff.2 (List.mem_cons_self ..)) with h | h
          · exact absurd h.symm hne
          · exact h
        have hx2 : x ∈ s := by
          rcases List.mem_cons.1 (hp.mem_iff.1 (List.mem_cons_self ..)) with h | h
          · exact absurd h hne
          · exact h
        exact hne (hinj x (List.mem_cons_self ..) w (List.mem_cons_of_mem _ hw2)
          (le_antisymm ((List.pairwise_cons.1 h₁).1 w hw2) ((List.pairwise_cons.1 h₂).1 x hx2)))
      subst hxw
      rw [ih hp.cons_inv (List.pairwise_cons.1 h₁).2 (List.pairwise_cons.1 h₂).2
        fun p hp' q hq' hpq => hinj p (List.mem_cons_of_mem _ hp') q
          (List.mem_cons_of_mem _ hq') hpq]

/-- **The rank listing of a disjoint union split by rank.** If every member of `s` is outranked by
every member of `t`, and the rank is injective on the two together, the listing of `s ∪ t` is the
listing of `s` followed by that of `t`. -/
theorem sortByRank_union (ha : 0 < a) {y : Heights a b N} {s t : Finset (ℕ × ℕ)}
    (hsub : s ∪ t ⊆ sweptRegion y) (hdisj : Disjoint s t)
    (hlt : ∀ P ∈ s, ∀ Q ∈ t, pointRank a b N P < pointRank a b N Q) :
    sortByRank a b N (s ∪ t) = sortByRank a b N s ++ sortByRank a b N t := by
  have hnodupR : (sortByRank a b N s ++ sortByRank a b N t).Nodup :=
    List.Nodup.append (sortByRank_nodup a b N s) (sortByRank_nodup a b N t)
      fun P hPs hPt =>
        Finset.disjoint_left.1 hdisj (mem_sortByRank.1 hPs) (mem_sortByRank.1 hPt)
  have hmem : ∀ P, P ∈ sortByRank a b N (s ∪ t) ↔
      P ∈ sortByRank a b N s ++ sortByRank a b N t := fun P => by
    rw [mem_sortByRank, List.mem_append, mem_sortByRank, mem_sortByRank, Finset.mem_union]
  refine eq_of_perm_of_pairwise_key (K := pointRank a b N)
    ((List.perm_ext_iff_of_nodup (sortByRank_nodup a b N (s ∪ t)) hnodupR).2 hmem)
    (sortByRank_pairwise a b N (s ∪ t)) ?_ ?_
  · exact List.pairwise_append.2 ⟨sortByRank_pairwise a b N s, sortByRank_pairwise a b N t,
      fun P hP Q hQ => (hlt P (mem_sortByRank.1 hP) Q (mem_sortByRank.1 hQ)).le⟩
  · exact fun P hP Q hQ h => pointRank_inj_of_mem_sweptRegion ha
      (hsub (mem_sortByRank.1 hP)) (hsub (mem_sortByRank.1 hQ)) h

/-- **The listing of the swept region is the diagonal points followed by the points above the
level.** This is the sentence "the sweep word is the composite of the operators at the
diagonal points, taken in decreasing order of rank, after the partial word `W_η(P̂)`", as an
identity between the two `List.mergeSort` outputs. -/
theorem sortByRank_sweptRegion_eq {η : ℚ} (hηa : IsAdmissibleLevel η)
    (hηs : SeparatesDiagonal a b N η) (hab : Nat.Coprime a b) (ha : 0 < a) {y : Heights a b N}
    (hy : IsAboveDiagonal y) :
    sortByRank a b N (sweptRegion y)
      = sortByRank a b N (diagPoints a b N) ++ sortByRank a b N (sweptAbove y η) := by
  have hunion := sweptRegion_eq_diagPoints_union hηs hab ha hy
  rw [hunion]
  refine sortByRank_union ha (by rw [← hunion]) (disjoint_diagPoints_sweptAbove hηs hab ha hy)
    fun P hP Q hQ => ?_
  obtain ⟨k, hk, rfl⟩ := mem_diagPoints_iff.1 hP
  have h1 : ((pointRank a b N (a * k, b * k) : ℤ) : ℚ) < η :=
    pointRank_lt_of_diag hηa hηs (Nat.mul_le_mul_left a hk) (Nat.mul_le_mul_left b hk) (by ring)
  have h2 : η < ((pointRank a b N Q : ℤ) : ℚ) := (Finset.mem_filter.1 hQ).2
  exact_mod_cast h1.trans h2

section Word

variable {L : Type*} [Field L] [Algebra ℚ L]

/-- The product of the event operators along the diagonal points of the rectangle, in increasing
order of rank — the part of `HJO.Mellit.sweepWord` that a separating level has already passed. -/
noncomputable def diagWord (q u : L) (y : Heights a b N) : Module.End L (Total L) :=
  ((sortByRank a b N (diagPoints a b N)).map (sweepOperator q u y)).prod

end Word

/-! ### Counting the returns -/

/-- The number of returns of the path strictly below `M` that are not the top: the graded index the
factor `d_-^ℓ` carries at the `M`-th diagonal point. -/
def retCount {a b N : ℕ} (y : Heights a b N) (M : ℕ) : ℕ :=
  #{m ∈ range M | m < N ∧ ht y (a * m) = b * m}

/-- The number of diagonal points strictly below `M` at which the path does not return: these are
the type-`E` events, each contributing one factor `u`. -/
def nonRetCount {a b N : ℕ} (y : Heights a b N) (M : ℕ) : ℕ :=
  #{m ∈ range M | ¬(ht y (a * m) = b * m)}

theorem retCount_succ_of {y : Heights a b N} {M : ℕ} (h : M < N)
    (hret : ht y (a * M) = b * M) : retCount y (M + 1) = retCount y M + 1 := by
  rw [retCount, retCount, Finset.range_add_one, Finset.filter_insert, ite_eq_left ⟨h, hret⟩,
    Finset.card_insert_of_notMem (by simp)]

theorem retCount_succ_of_not {y : Heights a b N} {M : ℕ} (h : ¬(M < N ∧ ht y (a * M) = b * M)) :
    retCount y (M + 1) = retCount y M := by
  rw [retCount, retCount, Finset.range_add_one, Finset.filter_insert, ite_eq_right h]

theorem nonRetCount_succ_of {y : Heights a b N} {M : ℕ} (h : ht y (a * M) ≠ b * M) :
    nonRetCount y (M + 1) = nonRetCount y M + 1 := by
  rw [nonRetCount, nonRetCount, Finset.range_add_one, Finset.filter_insert, ite_eq_left h,
    Finset.card_insert_of_notMem (by simp)]

theorem nonRetCount_succ_of_not {y : Heights a b N} {M : ℕ} (h : ht y (a * M) = b * M) :
    nonRetCount y (M + 1) = nonRetCount y M := by
  rw [nonRetCount, nonRetCount, Finset.range_add_one, Finset.filter_insert,
    ite_eq_right (by simpa using h)]

/-! ### The event at a diagonal point

The proof of `HJO.Mellit.isAdmissibleColouring_and_sum_sweepChar_eq_smul_dsc` reads off the event
type at each of the `N + 1` diagonal points: "the touch points of `P̂` other than `(aN, bN)` carry
event type `B` and contribute `d_-`; the point `(aN, bN)` carries type `D` with exponent `0` and
contributes the identity; and the remaining `N - ℓ` diagonal points lie strictly below the path,
carry type `E` and contribute `u` each". Every clause of that sentence is proved here. -/

/-- **At a return below the top the event type is `B`**, so the sweep applies `d_-`: the path
arrives along an east step, because its height at `a k` equals the diagonal one, and leaves along a
north step by `HJO.Mellit.lt_ht_succ_of_diag`. -/
theorem eventType_diag_eq_B {y : Heights a b N} (hy : IsAboveDiagonal y) (ha : 0 < a) (hb : 0 < b)
    {k : ℕ} (hk : k < N) (hret : ht y (a * k) = b * k) :
    eventType y (a * k, b * k) = EventType.B := by
  have hak : a * k + 1 ≤ a * N := by
    have h1 : a * k + a ≤ a * N := by
      calc a * k + a = a * (k + 1) := by ring
        _ ≤ a * N := Nat.mul_le_mul_left a hk
    omega
  have hlt := lt_ht_succ_of_diag hy hb hak
  rw [eventType, ite_eq_right (by simp only; omega), ite_eq_right (by simp only; omega),
    ite_eq_left (show a * k + 1 ≤ a * N ∧ b * k < ht y (a * k + 1) from ⟨hak, hlt⟩)]

/-- **At the corner the event type is `D`**, the path arriving and leaving along east steps — the
leaving one being outside the rectangle, which is what the guard `x + 1 ≤ aN` of
`HJO.Paths.eventType` records. -/
theorem eventType_corner {y : Heights a b N} (hy : IsAboveDiagonal y) :
    eventType y (a * N, b * N) = EventType.D := by
  rw [eventType, ite_eq_right (by simp only [hy.2.1]; omega),
    ite_eq_right (by simp only [hy.2.1]; omega), ite_eq_right (by simp only; omega)]

/-- **At the corner there is no live north step to the right**, so the exponent of `q` at the
corner's type-`D` event is `0` and the event operator is the identity. -/
theorem sweepRight_corner (y : Heights a b N) : sweepRight y (a * N, b * N) = 0 := by
  rw [sweepRight, Finset.card_eq_zero]
  refine Finset.filter_eq_empty_iff.2 fun {P} hP => ?_
  have h := mem_northSteps_iff.1 (liveSteps_subset y _ hP)
  simp only
  omega

section Word

variable {L : Type*} [Field L] [Algebra ℚ L]

/-- The event operator at a diagonal point that is not a return: multiplication by `u`. -/
theorem sweepOperator_diag_of_not_return (q u : L) {y : Heights a b N} {k : ℕ}
    (h : b * k < ht y (a * k)) : sweepOperator q u y (a * k, b * k) = u • 1 :=
  sweepOperator_of_eventType_E q u y _ (eventType_eq_E_iff.2 h)

/-- The event operator at a return below the top: `d_-` at the width of the point. -/
theorem sweepOperator_diag_of_return (q u : L) {y : Heights a b N} (hy : IsAboveDiagonal y)
    (ha : 0 < a) (hb : 0 < b) {k : ℕ} (hk : k < N) (hret : ht y (a * k) = b * k) :
    sweepOperator q u y (a * k, b * k) = dminus q (sweepWidth y (a * k, b * k)) := by
  rw [sweepOperator, eventType_diag_eq_B hy ha hb hk hret]

/-- The event operator at the corner: the identity. -/
theorem sweepOperator_corner (q u : L) {y : Heights a b N} (hy : IsAboveDiagonal y) :
    sweepOperator q u y (a * N, b * N) = 1 :=
  sweepOperator_of_eventType_D_of_sweepRight_eq_zero q u y _ (eventType_corner hy)
    (sweepRight_corner y)

end Word

/-! ### The width at a diagonal point -/

/-- **The live north steps at a diagonal point are the returns of the path weakly to its left.** A
north step whose rank is at most `ak ≤ aN` stands on the diagonal by
`HJO.Mellit.diag_of_pointRank_le`, and a diagonal north step is a return below the top; the upper
half of the window condition is free, the window exceeding `aN`. -/
theorem liveSteps_diag (hab : Nat.Coprime a b) (ha : 0 < a) (hb : 0 < b) (hN : 0 < N)
    {y : Heights a b N} (hy : IsAboveDiagonal y) {k : ℕ} (hk : k ≤ N) :
    liveSteps y (a * k, b * k)
      = ({m ∈ range N | m ≤ k ∧ ht y (a * m) = b * m}).image fun m => (a * m, b * m) := by
  have haN : 1 ≤ a * N := Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero ha.ne' hN.ne')
  have hωgt : a * N < attackWindow a N := by
    rw [attackWindow]
    calc a * N = 1 * (a * N) := by ring
      _ < (a * N + 1) * (a * N) := by
        exact Nat.mul_lt_mul_of_lt_of_le (by omega) (le_refl (a * N)) (by omega)
  have hkN : a * k ≤ a * N := Nat.mul_le_mul_left a hk
  ext P
  rw [liveSteps, Finset.mem_filter, Finset.mem_image]
  constructor
  · rintro ⟨hmemP, hle, -⟩
    have hns := mem_northSteps_iff.1 hmemP
    have hdiagle : b * P.1 ≤ a * P.2 :=
      (hy.2.2.2 P.1 hns.1.le).trans (Nat.mul_le_mul_left a hns.2.1)
    have hrk : pointRank a b N P ≤ ((a * N : ℕ) : ℤ) := by
      refine le_trans ?_ (by exact_mod_cast hkN : ((a * k : ℕ) : ℤ) ≤ ((a * N : ℕ) : ℤ))
      rw [pointRank]
      simpa only [abovePointRank_diag] using hle
    have hdiag : b * P.1 = a * P.2 := diag_of_pointRank_le hN hns.1.le hdiagle hrk
    obtain ⟨m, hm⟩ : a ∣ P.1 := Nat.Coprime.dvd_of_dvd_mul_left hab ⟨P.2, hdiag⟩
    have hm2 : P.2 = b * m := by
      refine Nat.eq_of_mul_eq_mul_left ha ?_
      rw [← hdiag, hm]; ring
    have hmN : m < N := Nat.lt_of_mul_lt_mul_left (hm ▸ hns.1)
    have hmk : m ≤ k := by
      rw [show P = (a * m, b * m) from Prod.ext hm hm2] at hle
      simp only [abovePointRank_diag] at hle
      exact Nat.le_of_mul_le_mul_left (by exact_mod_cast hle) ha
    refine ⟨m, Finset.mem_filter.2 ⟨Finset.mem_range.2 hmN, hmk, ?_⟩,
      (Prod.ext hm hm2).symm⟩
    exact le_antisymm (by rw [← hm, ← hm2]; exact hns.2.1)
      (IsAboveDiagonal.le_ht_diag hy ha hmN.le)
  · rintro ⟨m, hmem, rfl⟩
    rw [Finset.mem_filter, Finset.mem_range] at hmem
    obtain ⟨hmN, hmk, hret⟩ := hmem
    have hamN : a * m + 1 ≤ a * N := by
      have h1 : a * m + a ≤ a * N := by
        calc a * m + a = a * (m + 1) := by ring
          _ ≤ a * N := Nat.mul_le_mul_left a hmN
      omega
    refine ⟨mem_northSteps_iff.2 ⟨by omega, hret.le, lt_ht_succ_of_diag hy hb hamN⟩, ?_, ?_⟩
    · simp only [abovePointRank_diag]
      exact_mod_cast Nat.mul_le_mul_left a hmk
    · simp only [abovePointRank_diag]
      have hlt2 : a * k < a * m + attackWindow a N := by omega
      exact_mod_cast hlt2

/-- **The width at a return below the top is one more than the number of returns before it**, which
is the graded index the `d_-^ℓ` carries there: the `j`-th return, counted from `0`,
carries `d_-` of index `j + 1`. -/
theorem sweepWidth_diag_of_return (hab : Nat.Coprime a b) (ha : 0 < a) (hb : 0 < b)
    {y : Heights a b N} (hy : IsAboveDiagonal y) {k : ℕ} (hk : k < N)
    (hret : ht y (a * k) = b * k) : sweepWidth y (a * k, b * k) = retCount y k + 1 := by
  have hN : 0 < N := by omega
  have hinj : Function.Injective (fun m : ℕ => (a * m, b * m)) := by
    intro m m' hmm
    exact Nat.eq_of_mul_eq_mul_left ha (congrArg Prod.fst hmm)
  rw [sweepWidth, liveSteps_diag hab ha hb hN hy hk.le,
    Finset.card_image_of_injective _ hinj, retCount]
  rw [show {m ∈ range N | m ≤ k ∧ ht y (a * m) = b * m}
      = insert k {m ∈ range k | m < N ∧ ht y (a * m) = b * m} from ?_]
  · exact Finset.card_insert_of_notMem (by simp)
  · ext m
    simp only [Finset.mem_insert, Finset.mem_filter, Finset.mem_range]
    constructor
    · rintro ⟨h1, h2, h3⟩
      rcases eq_or_lt_of_le h2 with rfl | h4
      · exact Or.inl rfl
      · exact Or.inr ⟨h4, h1, h3⟩
    · rintro (rfl | ⟨h1, h2, h3⟩)
      · exact ⟨hk, le_rfl, hret⟩
      · exact ⟨h2, h1.le, h3⟩

/-! ### The diagonal points, listed -/

/-- **The rank listing of the diagonal points is `(0,0), (a,b), …, (aN,bN)`.** Their ranks are the
multiples `ak` of `a`, so the listing is by `k`. -/
theorem sortByRank_diagPoints (ha : 0 < a) :
    sortByRank a b N (diagPoints a b N) = (List.range (N + 1)).map fun k => (a * k, b * k) := by
  have hinj : Function.Injective (fun k : ℕ => (a * k, b * k)) := fun m m' hmm =>
    Nat.eq_of_mul_eq_mul_left ha (congrArg Prod.fst hmm)
  have hmem : ∀ P, P ∈ sortByRank a b N (diagPoints a b N) ↔
      P ∈ (List.range (N + 1)).map fun k => (a * k, b * k) := fun P => by
    rw [mem_sortByRank, mem_diagPoints_iff, List.mem_map]
    simp only [List.mem_range]
    exact ⟨fun ⟨k, hk, h⟩ => ⟨k, by omega, h.symm⟩, fun ⟨k, hk, h⟩ => ⟨k, by omega, h.symm⟩⟩
  refine eq_of_perm_of_pairwise_key (K := pointRank a b N)
    ((List.perm_ext_iff_of_nodup (sortByRank_nodup a b N _)
      (List.nodup_range.map hinj)).2 hmem) (sortByRank_pairwise a b N _) ?_ ?_
  · rw [List.pairwise_map]
    refine List.pairwise_lt_range.imp fun {m m'} h => ?_
    rw [pointRank_diag, pointRank_diag]
    exact_mod_cast Nat.mul_le_mul_left a h.le
  · intro P hP Q hQ h
    obtain ⟨k, -, rfl⟩ := mem_diagPoints_iff.1 (mem_sortByRank.1 hP)
    obtain ⟨k', -, rfl⟩ := mem_diagPoints_iff.1 (mem_sortByRank.1 hQ)
    rw [pointRank_diag, pointRank_diag] at h
    rw [show k = k' from Nat.eq_of_mul_eq_mul_left ha (by exact_mod_cast h)]

/-! ### Counting the returns at the top -/

/-- The returns of a path are the prefix sums of its return composition, as `Finset`s. -/
theorem filter_return_eq_filter_scanl {y : Heights a b N} {α : List ℕ}
    (hret : ∀ k ≤ N, (ht y (a * k) = b * k ↔ k ∈ α.scanl (· + ·) 0)) :
    {m ∈ range (N + 1) | ht y (a * m) = b * m} = {m ∈ range (N + 1) | m ∈ α.scanl (· + ·) 0} :=
  Finset.filter_congr fun m hm => hret m (by rw [Finset.mem_range] at hm; omega)

/-- **A composition of `N` with `ℓ` parts has `ℓ + 1` prefix sums in `{0, …, N}`.** This is where
the positivity of the parts is spent a second time: it makes the prefix sums distinct. -/
theorem card_filter_mem_scanl {α : List ℕ} (hpos : ∀ x ∈ α, 0 < x) (hsum : α.sum = N) :
    #{k ∈ range (N + 1) | k ∈ α.scanl (· + ·) 0} = α.length + 1 := by
  have hfull : (α.take α.length).sum = N := by rw [List.take_length, hsum]
  have hle : ∀ i ≤ α.length, (α.take i).sum ≤ N := by
    intro i hi
    rcases Nat.lt_or_ge i α.length with h | h
    · have := sum_take_lt hpos h le_rfl
      omega
    · rw [show i = α.length from by omega, hfull]
  have hset : {k ∈ range (N + 1) | k ∈ α.scanl (· + ·) 0}
      = (range (α.length + 1)).image fun i => (α.take i).sum := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_image, mem_scanl_add_iff,
      Nat.zero_add]
    constructor
    · rintro ⟨-, m, hm, rfl⟩
      exact ⟨m, by omega, rfl⟩
    · rintro ⟨i, hi, rfl⟩
      exact ⟨by have := hle i (by omega); omega, i, by omega, rfl⟩
  rw [hset, Finset.card_image_of_injOn ?_, Finset.card_range]
  intro i hi j hj hij
  rw [Finset.mem_coe, Finset.mem_range] at hi hj
  dsimp only at hij
  rcases lt_trichotomy i j with h | h | h
  · exact absurd hij (by have := sum_take_lt hpos h (by omega); omega)
  · exact h
  · exact absurd hij.symm (by have := sum_take_lt hpos h (by omega); omega)

/-- **The number of returns below the top is the number of parts of the return composition.** This
is the `ℓ`, and it is the number of factors `d_-` the sweep contributes along the
diagonal. -/
theorem retCount_top {y : Heights a b N} {α : List ℕ} (h : HasAboveReturns α y) :
    retCount y (N + 1) = α.length := by
  obtain ⟨hy, hpos, hsum, hretiff⟩ := h
  have hcard : #{m ∈ range (N + 1) | ht y (a * m) = b * m} = α.length + 1 := by
    rw [filter_return_eq_filter_scanl hretiff]
    exact card_filter_mem_scanl hpos hsum
  have hins : {m ∈ range (N + 1) | ht y (a * m) = b * m}
      = insert N {m ∈ range (N + 1) | m < N ∧ ht y (a * m) = b * m} := by
    ext m
    simp only [Finset.mem_insert, Finset.mem_filter, Finset.mem_range]
    constructor
    · rintro ⟨h1, h2⟩
      rcases eq_or_lt_of_le (show m ≤ N from by omega) with rfl | h3
      · exact Or.inl rfl
      · exact Or.inr ⟨h1, h3, h2⟩
    · rintro (rfl | ⟨h1, h2, h3⟩)
      · exact ⟨by omega, hy.2.1⟩
      · exact ⟨h1, h3⟩
  rw [hins, Finset.card_insert_of_notMem (by simp)] at hcard
  rw [retCount]
  omega

/-- **The number of diagonal points the path misses is `N - ℓ`.** These are the
type-`E` events, and they are what the factor `u^{N-ℓ}` of
`HJO.Mellit.isAdmissibleColouring_and_sum_sweepChar_eq_smul_dsc` counts. -/
theorem nonRetCount_top {y : Heights a b N} {α : List ℕ} (h : HasAboveReturns α y) :
    nonRetCount y (N + 1) = N - α.length := by
  obtain ⟨hy, hpos, hsum, hretiff⟩ := h
  have hcard : #{m ∈ range (N + 1) | ht y (a * m) = b * m} = α.length + 1 := by
    rw [filter_return_eq_filter_scanl hretiff]
    exact card_filter_mem_scanl hpos hsum
  have hsplit := Finset.card_filter_add_card_filter_not (s := range (N + 1))
    (fun m => ht y (a * m) = b * m)
  rw [Finset.card_range] at hsplit
  rw [nonRetCount]
  omega

section WordTwo

variable {L : Type*} [Field L] [Algebra ℚ L]

/-- **`d_-^n` at its graded indices.** `HJO.Sweep.dminus` reads `d_-` as a
map `V_k → V_{k-1}`, so the `d_-^ℓ` on `V_ℓ` is `d_-` of index `1` after `d_-` of index
`2` after … after `d_-` of index `ℓ`; `HJO.Sweep.dminus` carries that index, and a single
endomorphism cannot stand for all of them, the graded pieces being nested rather than a direct sum.
`HJO.Mellit.sweepWidth_diag_of_return` is what shows these are the indices the sweep actually
produces. -/
noncomputable def lowerRun (q : L) : ℕ → Module.End L (Total L)
  | 0 => 1
  | n + 1 => lowerRun q n * dminus q (n + 1)

/-- **The diagonal prefix of the sweep word.** Along the first `M` diagonal points the sweep
contributes one factor `u` at every point the path misses and one factor `d_-`, at the running
index, at every return below the top; the corner contributes the identity. This is proved
by induction on `M`. -/
theorem prod_sweepOperator_diag (q u : L) (hab : Nat.Coprime a b) (ha : 0 < a) (hb : 0 < b)
    {y : Heights a b N} (hy : IsAboveDiagonal y) : ∀ M ≤ N + 1,
    ((List.range M).map fun k => sweepOperator q u y (a * k, b * k)).prod
      = (u ^ nonRetCount y M) • lowerRun q (retCount y M) := by
  intro M
  induction M with
  | zero => exact fun _ => by simp [nonRetCount, retCount, lowerRun]
  | succ M ih =>
    intro hM
    have hMN : M ≤ N := by omega
    rw [List.range_succ, List.map_append, List.prod_append, ih (by omega)]
    simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
    by_cases hret : ht y (a * M) = b * M
    · rcases eq_or_lt_of_le hMN with rfl | hMlt
      · rw [sweepOperator_corner q u hy, mul_one, nonRetCount_succ_of_not hret,
          retCount_succ_of_not fun hc => absurd hc.1 (lt_irrefl M)]
      · rw [sweepOperator_diag_of_return q u hy ha hb hMlt hret,
          sweepWidth_diag_of_return hab ha hb hy hMlt hret, nonRetCount_succ_of_not hret,
          retCount_succ_of hMlt hret, lowerRun, smul_mul_assoc]
    · rw [sweepOperator_diag_of_not_return q u
          (lt_of_le_of_ne (IsAboveDiagonal.le_ht_diag hy ha hMN) (Ne.symm hret)),
        nonRetCount_succ_of hret, retCount_succ_of_not fun hc => hret hc.2, pow_succ,
        smul_mul_assoc, mul_smul_comm, mul_one, smul_smul]

/-- **The diagonal word is `u^{N-ℓ} d_-^ℓ`.** This is the proof paragraph for
`HJO.Mellit.isAdmissibleColouring_and_sum_sweepChar_eq_smul_dsc`, machine-checked: `ℓ` factors `d_-`
at the indices `1, …, ℓ`, `N - ℓ` factors `u`, and the identity at the corner. -/
theorem diagWord_eq (q u : L) (hab : Nat.Coprime a b) (ha : 0 < a) (hb : 0 < b)
    {y : Heights a b N} {α : List ℕ} (hy : HasAboveReturns α y) :
    diagWord q u y = (u ^ (N - α.length)) • lowerRun q α.length := by
  rw [diagWord, sortByRank_diagPoints ha, List.map_map]
  rw [show ((sweepOperator q u y) ∘ fun k => (a * k, b * k))
      = fun k => sweepOperator q u y (a * k, b * k) from rfl,
    prod_sweepOperator_diag q u hab ha hb hy.1 (N + 1) le_rfl, retCount_top hy,
    nonRetCount_top hy]

end WordTwo

section WordThree

variable {L : Type*} [Field L] [Algebra ℚ L]

/-- **The sweep word factors as the diagonal word after the partial word.** That is,
`W(P̂) = (the operators at the diagonal points) ∘ W_η(P̂)`, for every admissible level that
separates the diagonal. -/
theorem sweepWord_eq_diagWord_mul (q u : L) {η : ℚ} (hηa : IsAdmissibleLevel η)
    (hηs : SeparatesDiagonal a b N η) (hab : Nat.Coprime a b) (ha : 0 < a) {y : Heights a b N}
    (hy : IsAboveDiagonal y) :
    sweepWord q u y = diagWord q u y * partialSweepWord q u y η := by
  rw [sweepWord, partialSweepWord, diagWord, sortByRank_sweptRegion_eq hηa hηs hab ha hy,
    List.map_append, List.prod_append]

/-- **The sweep word at the vacuum, factored.** `W(P̂)(1) = u^{N-ℓ} d_-^ℓ(W_η(P̂)(1))` for every
admissible separating level, on an above-diagonal path of return composition `α`. This is the
identity the proof of `HJO.Mellit.isAdmissibleColouring_and_sum_sweepChar_eq_smul_dsc` asserts, with
the graded indices of `d_-` supplied by `HJO.Mellit.sweepWidth_diag_of_return`. -/
theorem sweepWord_vac_eq (q u : L) {η : ℚ} (hηa : IsAdmissibleLevel η)
    (hηs : SeparatesDiagonal a b N η) (hab : Nat.Coprime a b) (ha : 0 < a) (hb : 0 < b)
    {y : Heights a b N} {α : List ℕ} (hy : HasAboveReturns α y) :
    sweepWord q u y (1 : Total L)
      = (u ^ (N - α.length)) • lowerRun q α.length (partialSweepWord q u y η (1 : Total L)) := by
  rw [sweepWord_eq_diagWord_mul q u hηa hηs hab ha hy.1, Module.End.mul_apply,
    diagWord_eq q u hab ha hb hy, LinearMap.smul_apply]

end WordThree

/-! ### The residual: `HJO.Mellit.sweepComputes`, and the reduction -/

section Reduction

variable {L : Type*} [Field L] [Algebra ℚ L]

/-- A composition has at most as many parts as its sum. -/
private theorem length_le_sum {α : List ℕ} (hpos : ∀ x ∈ α, 0 < x) : α.length ≤ α.sum := by
  induction α with
  | nil => simp
  | cons x l ih =>
    have hx := hpos x (by simp)
    have hl := ih fun z hz => hpos z (by simp [hz])
    simp only [List.length_cons, List.sum_cons]
    omega

/-- **`HJO.Mellit.sweepComputes`, as a named `Prop`.** The sweep process computes the
summand: for every above-diagonal `(aN, bN)`-path `P̂` and every realisation `ι`, the element
`W(P̂)(1)` of `V_0 = Λ` — read back in `Λ` by the constant coefficient of `Λ[y_1, y_2, …]` —
satisfies
`ι(W(P̂)(1)) = u^{ârea(P̂)} q^{ĥ(P̂) - max t̂dinv(P̂)} χ(P̂)`.

This is the whole of what `HJO.Mellit.Rem41` needs beyond this file; everything else in
the proof of `HJO.Mellit.isAdmissibleColouring_and_sum_sweepChar_eq_smul_dsc` is proved above.

The statement itself is proved: it is discharged by `HJO.Mellit.sweepComputes`
(`HJO/CarlssonMellit/LoweringSumClosed.lean`), and carried to the shape the assembly uses by
`HJO.Mellit.sweepComputes_of_algebraicIndependent` (`HJO/Shuffle/SweepComputesClosed.lean`). The
argument for it rests on five lemmas, all of them proved:

* `HJO.Paths.card_filter_eventType_E`;
* `HJO.Paths.sweepWidth_sub_sweepWidth_of_rankAdjacent`;
* `HJO.Mellit.sweepWord_mem_piece_zero`;
* `HJO.Mellit.constantCoeff_psiWord_one_mem_lambdaComp_and_map_eq_sweepChar`
  (`HJO/Shuffle/SweepComputesClosed.lean`);
* `HJO.Paths.sum_sweepRight_D_sub_sum_sweepRight_C_eq_aboveHookCount_sub_aboveMaxTdinv`.

The last two are the substantial ones, each a whole argument of its own. The assembly
`HJO.Mellit.shuffle_of_lhs_and_induction` (`HJO/Shuffle/SweepComputesClosed.lean`) takes only
`LhsComputes` and `MellitInduction`, this `Prop` being already supplied. -/
def SweepComputes (q u : L) (a b : ℕ) : Prop :=
  ∀ (ι : Sym.Lambda L →ₐ[L] Sym.AlphabetSeries L), Sym.IsRealisation ι →
    ∀ (N : ℕ) (y : Heights a b N), IsAboveDiagonal y →
      ι (MvPolynomial.constantCoeff (sweepWord q u y (1 : Total L)))
        = (u ^ Paths.aboveArea y *
            q ^ ((Paths.aboveHookCount y : ℤ) - (aboveMaxTdinv y : ℤ))) • Paths.sweepChar q y

/-- **`HJO.Mellit.Rem41` follows from `HJO.Mellit.sweepComputes` alone.** The clause is *reduced*:
what remains of it is the single named `Prop` `HJO.Mellit.SweepComputes`, the statement of
`HJO.Mellit.sweepComputes`, whose proof belongs to Mellit's Section 4.

Two hypotheses pin the abstract sweep system to the concrete operators, in the style of
`HJO.Mellit.rhsSumsAgree_of_chi_eq_sweepChar`, which discharged `RhsSumsAgree` the same way.
`hchi` is that `χ` is `HJO.Paths.sweepChar`. `hD` is that `D_{η,c}` is `HJO.Mellit.dsc` and that the
factor `d_-^ℓ` is `d_-` at the graded indices `1, …, ℓ`, the two being read together because
the top layer's `HJO.Mellit.SweepSystem.dminus` is a single operator where the `d_-` is
graded; see `HJO.Mellit.lowerRun`. `hD` is scoped to the colourings `c_α`, where it is consistent:
`c_α` determines `N` by `HJO.Mellit.sum_eq_of_compColouring_eq`, so the `N` that
`HJO.Mellit.dsc` needs and `HJO.Mellit.SweepSystem.D` lacks is recoverable.

`hD` REQUIRES THE COMPOSITION TO BE POSITIVE, and that is not decoration. Without it the hypothesis
is unsatisfiable by the witness `HJO.Mellit.sweepWitness`:
`HJO.Mellit.colourParts_compColouring_zero_part` exhibits `α = [0]`, where the two cell families of
`c_α` coincide, `c_α = {(0,0)}`, and the `colourParts` that `HJO.Mellit.sweepWitness` uses to
recover the grading reads `0` where `ℓ = 1`. So the unrestricted `hD` asked for an identity that is
false of the witness at that composition, and a `Rem41` derived from it would be a true theorem
resting on an unsatisfiable hypothesis. The narrowing costs nothing -- `hpos` is already in hand at
the single `rw [hD …]` below -- and it strengthens this theorem, a hypothesis required of fewer
compositions being easier to supply. It is a condition on the composition, not genericity in the
parameters.

No genericity is spent: the statement holds at `q = 0`, at `u = 0` and at every root of unity. The
exponent of `u` on the right of `HJO.Mellit.isAdmissibleColouring_and_sum_sweepChar_eq_smul_dsc` is
`N - ℓ ≥ 0`, so no inverse is taken there, and the negative exponent of `q` on the left is carried
through untouched by `HJO.Mellit.SweepComputes`. -/
theorem rem41_of_sweepComputes {q u : L} {a b : ℕ} (S : SweepSystem L q u)
    (hab : Nat.Coprime a b) (ha : 0 < a) (hb : 0 < b)
    (hchi : ∀ (a' b' N' : ℕ) (y : Heights a' b' N'), S.chi a' b' N' y = Paths.sweepChar q y)
    (hD : ∀ (N : ℕ) (η : ℚ) (α : List ℕ), (∀ x ∈ α, 0 < x) → α.sum = N →
      S.proj ((S.dminus ^ α.length) (S.D η (compColouring a b α)))
        = MvPolynomial.constantCoeff (lowerRun q α.length (dsc q u a b N η (compColouring a b α))))
    (h : SweepComputes q u a b) : Rem41 S a b := by
  intro ι hι N η hηa hηs α hpos hsum
  have ha0 : 0 < a := ha
  have hb0 : 0 < b := hb
  have hlen : α.length ≤ N := hsum ▸ length_le_sum hpos
  have hzpow : (u : L) ^ ((N : ℤ) - (α.length : ℤ)) = u ^ (N - α.length) := by
    rw [show (N : ℤ) - (α.length : ℤ) = ((N - α.length : ℕ) : ℤ) from by omega, zpow_natCast]
  rw [hD N η α hpos hsum,
    dsc_compColouring_eq_sum_partialSweepWord q u hηa hηs hab ha hb0 hpos hsum,
    hzpow]
  simp only [map_sum]
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun y hy => ?_
  rw [aboveReturnPaths, Finset.mem_filter] at hy
  rw [hchi, ← h ι hι N y hy.2.1, sweepWord_vac_eq q u hηa hηs hab ha0 hb0 hy.2.2,
    MvPolynomial.constantCoeff_smul, map_smul]

/-! ### Corner checks -/

/-- **`HJO.Mellit.isAdmissibleColouring_and_sum_sweepChar_eq_smul_dsc` takes no inverse of `u`.**
The exponent `N - ℓ` of `u` on its right-hand side is nonnegative, a composition having at most as
many parts as its sum, so the clause is a statement about natural-number powers and imposes no
genericity of its own — which is why `HJO.Mellit.rem41_of_sweepComputes` carries none.

This is worth recording because the clause shares its scalar family with
`HJO.Mellit.MellitInduction`, whose factor `(qu)^{ℓ-N}` carries the *opposite*, nonpositive
exponent, and which is therefore `0` at `q = 0`. That is exactly where
`HJO.Mellit.not_mellitInput_unrestricted` finds three of the four clauses of
`HJO.Mellit.MellitInput` jointly contradictory. The contradiction is not located here: `Rem41` is
the clause that *transports* the vanishing to the path sum, and it does so at every `q` and `u`. -/
theorem sub_length_nonneg {α : List ℕ} (hpos : ∀ x ∈ α, 0 < x) {N : ℕ} (hsum : α.sum = N) :
    0 ≤ (N : ℤ) - (α.length : ℤ) := by
  have h := length_le_sum hpos
  omega

/-- **Corner check: at a separating level and `N ≥ 1` the invariant at the empty colouring
vanishes.** No above-diagonal path is coloured `∅` there, the north step at the origin always being
crossed, so `∅` is an inadmissible colouring and
`HJO.Mellit.dsc_eq_zero_of_not_isAdmissibleColouring` reads off the value. Every hypothesis is spent
on the inadmissibility; the vanishing itself asks nothing of the level.

This is not in tension with `HJO.Mellit.isAdmissibleColouring_empty_and_dsc_eq_one`, `D_{η,∅} = 1`:
that is the value at a level *above every rank* of the region, which is not a separating level — a
separating level has already passed all `N + 1` diagonal points. The check is recorded because the
two readings of `D_{η,∅}` are easy to conflate, and because it shows the sum of
`HJO.Mellit.dsc_compColouring_eq_sum_partialSweepWord` is not vacuously indexed. -/
theorem dsc_empty_eq_zero (q u : L) {η : ℚ} (hηa : IsAdmissibleLevel η)
    (hηs : SeparatesDiagonal a b N η) (hab : Nat.Coprime a b) (ha : 0 < a) (hb : 0 < b)
    (hN : 0 < N) : dsc q u a b N η ∅ = 0 := by
  refine dsc_eq_zero_of_not_isAdmissibleColouring q u ?_
  rintro ⟨y, hy, hc⟩
  have horigin : ((0 : ℕ), (0 : ℕ)) ∈ colouring y η := by
    refine (mem_colouring_iff hηa hηs hab ha hb hN hy).2 (Or.inl ⟨0, hN, ?_, by simp⟩)
    simpa using hy.1
  rw [hc] at horigin
  exact absurd horigin (by simp)

end Reduction

end HJO.Mellit
