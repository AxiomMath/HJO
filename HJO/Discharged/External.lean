/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Mathlib.Algebra.CharP.Algebra
public import HJO.Defs
public import HJO.CreationSeeds.Basic
public import HJO.RankOneDinv.Basic
public import HJO.SignExtraction.Basic
public meta import HJO.Attr

/-! # Three quoted results that are not assumptions

`HJO/Defs.lean` states the results this library quotes from the literature as `Prop`-valued
assumptions, so that a consumer carries the assumption it depends on and no quoted result is used
silently. Three of them are inhabited: the rank-one dinv identity, the Macdonald--Gessel reading of
sign extraction, and the expansion of the elementary symmetric functions in the creation seeds are
proved here, from `HJO/RankOneDinv/`, `HJO/SignExtraction/` and `HJO/CreationSeeds/`. Nothing in
this library assumes those three.
-/

@[expose] public section

namespace HJO.ExternalDischarged

/-- **`CreationExpansion` is not an assumption.** The elementary symmetric function is the sum of
the creation seeds over compositions, by `HJO.CreationSeeds.sum_copComp_eq_elemSymm`. The
positivity hypothesis of the quoted form is not needed. -/
theorem creationExpansion (L : Type*) [Field L] [Algebra ℚ L] :
    HJO.External.CreationExpansion L :=
  fun q N _ => (HJO.CreationSeeds.sum_copComp_eq_elemSymm q N).symm

open Finset in
/-- **`EpsilonGessel` is not an assumption.** Sign extraction reads the full-descent coefficient,
proved by polynomiality in the number of letters instead of through the Schur basis.

Apply the evaluation `E_m` at `m` letters to the hypothesis and read the coefficient of `y^{n}`.
On the left `Sym.letterEval_realisation` gives the value `ν_f(m)` of the letter-count polynomial,
this being the one place the homogeneity of `f` is used; on the right
`ParkingFunctions.coeff_letterEval_gessel` gives the value at `m` of the descent polynomial
`D_{n, #S_i}` of each term. The two polynomials therefore agree at every non-negative integer, so
they are equal by `Sym.eq_zero_of_eval_natCast_eq_zero`, and `t = -1` may be substituted: a term
whose descent set has fewer than `n - 1` elements sits at a root of its descent polynomial by
`Sym.eval_descentPoly_intCast_eq_zero` and dies, and a full one contributes `(-1)^n` by
`Sym.eval_descentPoly_neg_one_succ`. Since sign extraction is `(-1)^n ν_f(-1)` by
`Sym.signExtract_eq_eval_letterCount`, the two signs cancel. Finally a descent set of the maximal
size is the full set by `Sym.eq_Ico_of_card_eq`, which identifies the surviving index set with the
one the statement sums over. -/
theorem epsilonGessel (L : Type*) [Field L] [Algebra ℚ L] :
    HJO.External.EpsilonGessel L := by
  intro ι hι n hn I J w S f hf hSsub hexp
  obtain ⟨N, rfl⟩ : ∃ N, n = N + 1 := ⟨n - 1, by omega⟩
  have hchar : CharZero L := charZero_of_injective_algebraMap (algebraMap ℚ L).injective
  -- Every letter count gives one numerical identity.
  have key : ∀ m : ℕ, (Sym.letterCount L f -
      ∑ i ∈ J, w i • Sym.descentPoly L (N + 1) #(S i)).eval (m : L) = 0 := by
    intro m
    have h1 : PowerSeries.coeff (N + 1) (Sym.letterEval m (ι f))
        = (Sym.letterCount L f).eval (m : L) := by
      rw [Sym.letterEval_realisation hι m hf, PowerSeries.coeff_C_mul_X_pow]
      simp
    have hlin : Sym.letterEval m (∑ i ∈ J, w i • ParkingFunctions.gessel L (N + 1) (S i))
        = ∑ i ∈ J, w i • Sym.letterEval m (ParkingFunctions.gessel L (N + 1) (S i)) := by
      change Sym.letterEvalHom L m _ = _
      rw [map_sum]
      exact sum_congr rfl fun i _ => map_smul (Sym.letterEvalHom L m) _ _
    have h2 : PowerSeries.coeff (N + 1) (Sym.letterEval m (ι f))
        = ∑ i ∈ J, w i * (Sym.descentPoly L (N + 1) #(S i)).eval (m : L) := by
      rw [hexp, hlin, map_sum]
      refine sum_congr rfl fun i hi => ?_
      rw [PowerSeries.coeff_smul, smul_eq_mul,
        ParkingFunctions.coeff_letterEval_gessel L (hSsub i hi)]
    rw [Polynomial.eval_sub, ← h1, h2, Polynomial.eval_finsetSum]
    simp
  -- Two polynomials agreeing at every letter count are equal.
  have hpoly : Sym.letterCount L f = ∑ i ∈ J, w i • Sym.descentPoly L (N + 1) #(S i) :=
    sub_eq_zero.mp (Sym.eq_zero_of_eval_natCast_eq_zero key)
  -- Substituting `t = -1` kills every term whose descent set is not full.
  have hval : (Sym.letterCount L f).eval (-1 : L)
      = (-1) ^ (N + 1) * ∑ i ∈ J with S i = Ico 1 (N + 1), w i := by
    rw [hpoly, Polynomial.eval_finsetSum, mul_sum,
      ← sum_filter_add_sum_filter_not J fun i => S i = Ico 1 (N + 1)]
    have hzero : ∀ i ∈ {i ∈ J | ¬ (S i = Ico 1 (N + 1))},
        (w i • Sym.descentPoly L (N + 1) #(S i)).eval (-1 : L) = 0 := by
      intro i hi
      rw [mem_filter] at hi
      have hsub := hSsub i hi.1
      have hcard : #(S i) ≤ N := by
        have h := card_le_card hsub
        rwa [Nat.card_Ico] at h
      have hne : #(S i) ≠ N := fun h => hi.2 (Sym.eq_Ico_of_card_eq hsub (by omega))
      have h0 : (Sym.descentPoly L (N + 1) #(S i)).eval (-1 : L) = 0 := by
        have h := Sym.eval_descentPoly_intCast_eq_zero L (N + 1) #(S i) (x := (-1 : ℤ))
          (by omega) (by omega)
        rwa [show ((-1 : ℤ) : L) = -1 by push_cast; ring] at h
      rw [Polynomial.eval_smul, h0, smul_zero]
    rw [sum_congr rfl hzero, sum_const_zero, add_zero]
    refine sum_congr rfl fun i hi => ?_
    rw [mem_filter] at hi
    have hcard : #(S i) = N := by rw [hi.2, Nat.card_Ico]; omega
    rw [Polynomial.eval_smul, hcard, Sym.eval_descentPoly_neg_one_succ L N, smul_eq_mul, mul_comm]
  rw [Sym.signExtract_eq_eval_letterCount hf, hval, ← mul_assoc, ← pow_add, ← two_mul, pow_mul]
  simp

/-! ### Sums over an integer interval

Four arithmetic facts about sums indexed by `Finset.Icc`, used only to regroup the alternating
sum of tail counts below. -/

/-- The bottom term of a sum over `Finset.Icc 0 A` splits off. -/
theorem sum_Icc_zero_split {M : Type*} [AddCommMonoid M] (A : ℕ) (f : ℕ → M) :
    ∑ u ∈ Finset.Icc 0 A, f u = f 0 + ∑ u ∈ Finset.Icc 1 A, f u := by
  rw [show Finset.Icc 0 A = insert 0 (Finset.Icc 1 A) from by
        ext x
        simp only [Finset.mem_Icc, Finset.mem_insert]
        omega,
    Finset.sum_insert (by simp only [Finset.mem_Icc]; omega)]

/-- The top term of a sum over `Finset.Icc 0 (A + 1)` splits off. -/
theorem sum_Icc_zero_top {M : Type*} [AddCommMonoid M] (A : ℕ) (f : ℕ → M) :
    ∑ u ∈ Finset.Icc 0 (A + 1), f u = (∑ u ∈ Finset.Icc 0 A, f u) + f (A + 1) := by
  rw [show Finset.Icc 0 (A + 1) = insert (A + 1) (Finset.Icc 0 A) from by
        ext x
        simp only [Finset.mem_Icc, Finset.mem_insert]
        omega,
    Finset.sum_insert (by simp only [Finset.mem_Icc]; omega)]
  exact add_comm _ _

/-- The top term of a sum over `Finset.Icc 1 (A + 1)` splits off. -/
theorem sum_Icc_one_top {M : Type*} [AddCommMonoid M] (A : ℕ) (f : ℕ → M) :
    ∑ u ∈ Finset.Icc 1 (A + 1), f u = (∑ u ∈ Finset.Icc 1 A, f u) + f (A + 1) := by
  rw [show Finset.Icc 1 (A + 1) = insert (A + 1) (Finset.Icc 1 A) from by
        ext x
        simp only [Finset.mem_Icc, Finset.mem_insert]
        omega,
    Finset.sum_insert (by simp only [Finset.mem_Icc]; omega)]
  exact add_comm _ _

/-- Reindexing a sum by the shift `u ↦ u + 1`. -/
theorem sum_Icc_shift {M : Type*} [AddCommMonoid M] (A : ℕ) (f : ℕ → M) :
    ∑ u ∈ Finset.Icc 0 A, f (u + 1) = ∑ v ∈ Finset.Icc 1 (A + 1), f v := by
  induction A with
  | zero => simp
  | succ n ih => rw [sum_Icc_zero_top n fun u => f (u + 1), ih, sum_Icc_one_top (n + 1) f]

/-- Reindexing a sum by the shift `u ↦ u + 1` when the term that leaves the range vanishes. -/
theorem sum_Icc_shift_of_top_eq_zero {M : Type*} [AddCommMonoid M] (A : ℕ) (f : ℕ → M)
    (h : f (A + 1) = 0) : ∑ u ∈ Finset.Icc 0 A, f (u + 1) = ∑ v ∈ Finset.Icc 1 A, f v := by
  rw [sum_Icc_shift A f, sum_Icc_one_top A f, h, add_zero]

/-- **The recombination behind the rank-one dinv identity.** The four sums of the alternating
expression regroup, after reindexing two of them by `u ↦ u + 1`, into the two window counts.

`E` stands for the tail count `E_P`, `β` for the staircase bound, `γ` and `δ` for its values one
step down and one step up -- passed separately because in the application the staircase bound is a
function on `ℤ` and the shifted arguments `u - 1`, `u + 1` are formed there, not in `ℕ` -- and `c`
for its value at `1`. The hypothesis `hz` is the vanishing of the tail counts past the width. -/
theorem sum_tails_identity (E : ℕ → ℕ → ℕ) (β γ δ : ℕ → ℕ) (c A : ℕ)
    (hz : ∀ v : ℕ, E (A + 1) v = 0) (hβ : β 0 = 0)
    (hγ : ∀ u : ℕ, 1 ≤ u → γ u = β (u - 1)) (hδ : ∀ u : ℕ, δ u = β (u + 1)) (hc : c = δ 0) :
    ∑ u ∈ Finset.Icc 0 A, ((E u (β u) : ℤ) - (E (u + 1) (β u) : ℤ)
        - (E u (δ u + 1) : ℤ) + (E (u + 1) (δ u + 1) : ℤ))
      = ((E 0 0 + ∑ u ∈ Finset.Icc 1 A, (E u (β u) + E u (β u + 1)) : ℕ) : ℤ)
        - ((E 0 (c + 1)
            + ∑ u ∈ Finset.Icc 1 A, (E u (γ u) + E u (δ u + 1)) : ℕ) : ℤ) := by
  -- The two reindexings. Both discard a term at `A + 1`, which vanishes by `hz`.
  have key1 : ∑ u ∈ Finset.Icc 0 A, E (u + 1) (β (u + 1) + 1)
      = ∑ v ∈ Finset.Icc 1 A, E v (β v + 1) :=
    sum_Icc_shift_of_top_eq_zero A (fun v => E v (β v + 1)) (hz _)
  have key2 : ∑ u ∈ Finset.Icc 0 A, E (u + 1) (β u)
      = ∑ v ∈ Finset.Icc 1 A, E v (β (v - 1)) := by
    refine Eq.trans (Finset.sum_congr rfl fun u _ => ?_)
      (sum_Icc_shift_of_top_eq_zero A (fun v => E v (β (v - 1))) (hz _))
    simp
  -- The first window: the terms with short arm and the reindexed terms with long leg.
  have e1 : ∑ u ∈ Finset.Icc 0 A, (E u (β u) + E (u + 1) (δ u + 1))
      = E 0 0 + ∑ u ∈ Finset.Icc 1 A, (E u (β u) + E u (β u + 1)) := by
    have hstep : ∀ u ∈ Finset.Icc 0 A, E u (β u) + E (u + 1) (δ u + 1)
        = E u (β u) + E (u + 1) (β (u + 1) + 1) := fun u _ => by rw [hδ]
    rw [Finset.sum_congr rfl hstep]
    simp only [Finset.sum_add_distrib]
    rw [key1, sum_Icc_zero_split A fun u => E u (β u), hβ]
    ring
  -- The second window: the reindexed terms with long arm and the terms with long leg.
  have e2 : ∑ u ∈ Finset.Icc 0 A, (E (u + 1) (β u) + E u (δ u + 1))
      = E 0 (c + 1) + ∑ u ∈ Finset.Icc 1 A, (E u (γ u) + E u (δ u + 1)) := by
    have hstep : ∀ u ∈ Finset.Icc 1 A, E u (γ u) + E u (δ u + 1)
        = E u (β (u - 1)) + E u (δ u + 1) := by
      intro u hu
      rw [Finset.mem_Icc] at hu
      rw [hγ u hu.1]
    rw [Finset.sum_congr rfl hstep]
    simp only [Finset.sum_add_distrib]
    rw [key2, sum_Icc_zero_split A fun u => E u (δ u + 1), hc]
    ring
  -- Each summand is the difference of the two windows' contributions at that arm.
  have hcast : ∀ u ∈ Finset.Icc 0 A, ((E u (β u) : ℤ) - (E (u + 1) (β u) : ℤ)
      - (E u (δ u + 1) : ℤ) + (E (u + 1) (δ u + 1) : ℤ))
      = ((E u (β u) + E (u + 1) (δ u + 1) : ℕ) : ℤ)
        - ((E (u + 1) (β u) + E u (δ u + 1) : ℕ) : ℤ) := by
    intro u _
    push_cast
    ring
  rw [Finset.sum_congr rfl hcast, Finset.sum_sub_distrib, ← Nat.cast_sum, ← Nat.cast_sum, e1, e2]

/-- **`RankOneDinv` is not an assumption.** The hook count of the primitive path of an order filter
is the quadratic form at that filter's indicator vector, proved through the gap coordinates
`(r, i) ↦ rb - ai` of `HJO.RankOneDinv`.

Both sides become sums of the tail counts `E(u, v)` of the primitive path -- the cells whose arm
is at least `u` and whose leg is at least `v`. On the left, `HJO.RankOneDinv.hookCount_eq_sum`
partitions the cells by the value `u` of the arm, the hook condition at a cell being exactly
`β(arm) ≤ leg ≤ β(arm + 1)` for the staircase bound `β u = ⌊ub/a⌋`, and reads each block as
`(E(u, β u) - E(u+1, β u)) - (E(u, β(u+1)+1) - E(u+1, β(u+1)+1))`. On the right,
`HJO.RankOneDinv.q_indicator_eq` turns the form into the pairs of `F` whose difference lies in
`[0, a)` minus those whose difference lies in `[b, a+b)`, and
`HJO.RankOneDinv.card_window_zero` and `HJO.RankOneDinv.card_window_b` evaluate those two window
counts as sums of tail counts, the reflection `β(-u) = -β u - 1` folding the pairs with `r' < r`
onto the pairs with `r' > r`.

What remains is the regrouping `sum_tails_identity`: reindexing the sum of `E(u+1, β u)` and the
sum of `E(u+1, β(u+1)+1)` by `u ↦ u + 1` moves them onto `Finset.Icc 1 (a-2)`, their terms at
`a - 1` vanishing by `HJO.RankOneDinv.tailCount_eq_zero` since no cell has arm `a - 1`; then the
first and fourth sums are the first window count and the second and third are the second. The
below-diagonal hypothesis of the hook count is
`HJO.ReturnPath.isBelowDiagonal_primitivePath`, and the subset hypothesis of the two window
counts is the first component of `HJO.Gaps.IsOrderFilter`. -/
theorem rankOneDinv : HJO.External.RankOneDinv := by
  intro a b hco ha hab F hF
  have hb : 0 < b := by omega
  have hbd := HJO.ReturnPath.isBelowDiagonal_primitivePath hco (show 0 < a by omega) hF
  rw [HJO.RankOneDinv.hookCount_eq_sum hco ha hbd,
    HJO.RankOneDinv.q_indicator_eq hab hF.1,
    HJO.RankOneDinv.card_window_zero hco ha hb hF hF.1,
    HJO.RankOneDinv.card_window_b hco ha hb hF hF.1]
  refine sum_tails_identity
    (fun u v => HJO.Paths.tailCount (HJO.Primitive.primitivePath a b F) u v)
    (fun u => (HJO.Gaps.beta a b (u : ℤ)).toNat)
    (fun u => (HJO.Gaps.beta a b ((u : ℤ) - 1)).toNat)
    (fun u => (HJO.Gaps.beta a b ((u : ℤ) + 1)).toNat)
    (HJO.Gaps.beta a b 1).toNat (a - 2) ?_ ?_ ?_ ?_ ?_
  · intro v
    exact HJO.RankOneDinv.tailCount_eq_zero ha hbd (by omega)
  · show (HJO.Gaps.beta a b ((0 : ℕ) : ℤ)).toNat = 0
    simp [HJO.Gaps.beta]
  · intro u hu
    show (HJO.Gaps.beta a b ((u : ℤ) - 1)).toNat
      = (HJO.Gaps.beta a b (((u - 1 : ℕ) : ℤ))).toNat
    rw [show (((u - 1 : ℕ) : ℤ)) = (u : ℤ) - 1 from by omega]
  · intro u
    show (HJO.Gaps.beta a b ((u : ℤ) + 1)).toNat
      = (HJO.Gaps.beta a b (((u + 1 : ℕ) : ℤ))).toNat
    rw [Nat.cast_add, Nat.cast_one]
  · show (HJO.Gaps.beta a b 1).toNat = (HJO.Gaps.beta a b (((0 : ℕ) : ℤ) + 1)).toNat
    norm_num

end HJO.ExternalDischarged
