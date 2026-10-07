/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.Evaluation.PhiMul
public import HJO.Shuffle.Mellit

/-! # The Mellit interface is contradictory at `q = 0`

`HJO.Mellit.MellitInput` quantifies over *generic* parameters, and this file is why. Quantified
over all `q u : L`, it would not merely be an unproved statement but a **false** one: three of its
four clauses are jointly contradictory at `q = 0`, `u = 1`.

## The argument

Fix `(a, b) = (2, 3)`, `N = 2`, `α = (2)` — one part, so `ℓ = 1 < N` — and `η := aN + 1/2`, which
is admissible and separating by `HJO.Mellit.separatesDiagonal_sepLevel`.

* `MellitInduction` evaluates `D_{η,c_α}` as `(-1)^{(a-1)N}(qu)^{ℓ-N} • G_ℓ ⋯ G_1(1)`. At `q = 0`
  the factor `(qu)^{ℓ-N} = 0^{-1}` is `0`, so `D_{η,c_α} = 0` whatever the sweep system is.
* `Rem41` then reads the path sum as `u^{N-ℓ} • ι(d_-^ℓ D_{η,c_α}) = 0`.
* `RhsSumsAgree` equates the path sum with the sum over above-diagonal parking functions. So that
  sum must vanish.

It does not. The coefficient of the squarefree monomial `x_1 x_2 ⋯ x_{bN}` in `F_{bN,D}` is `1` for
every descent set `D` — the strictly increasing tuple `(1, …, bN)` meets every constraint — so
reading that coefficient turns the parking-function sum into `∑_{π̂} q^{d̂inv(π̂)} u^{ârea(P̂_π̂)}`,
which at `q = 0`, `u = 1` counts the above-diagonal parking functions of return composition `α`
with `d̂inv = 0`. That count is at least one: the **top path** `P̂ = (0, bN, …, bN)` has return
composition `(N)`, no cells above it and hence `ĥ(P̂) = 0`, and all of its `bN` north steps sit in
column `0`, so their above-diagonal ranks are the distinct multiples `0, ω, 2ω, …` of the attack
window `ω = (aN+1)aN`, and no labelling of it has a single `t̂dinv` pair. So `t̂dinv` and
`max t̂dinv` are both `0` there and `d̂inv = ĥ + t̂dinv - max t̂dinv = 0`.

## What this does and does not show

It shows that the genericity is necessary, not that the mathematics is wrong. The standing
coefficient field is `𝕜 = ℚ(q, u)` with `q, u` indeterminates, and that `q, u` are invertible,
`qu ≠ 1`, no power of `u` equals `1` and `(1-q)(1-u) ≠ 0` are all load-bearing in the layer below.
Generalising to an arbitrary coefficient field while dropping the genericity produces a false
statement.

This is not a step of the proof of the shuffle identity; it justifies the genericity hypotheses of
`HJO.Mellit.MellitInput`.
-/

@[expose] public section

open Finset

namespace HJO.Mellit

open Paths ParkingFunctions

/-! ### Reading one coefficient of a fundamental quasisymmetric function -/

/-- **The squarefree monomial occurs in every fundamental quasisymmetric function of its degree,
with coefficient `1`.** `F_{n,S}` sums `x_{i_1} ⋯ x_{i_n}` over tuples that increase weakly along
`1, …, n` and strictly at each member of `S`; the tuple `i_j = j` increases strictly everywhere, so
it is admissible for every `S`, and by `HJO.ParkingFunctions.gessel` each monomial has coefficient
the indicator of being so realised. This is the linear functional the witness below applies: it is
`1` on every `gessel`, so it turns a sum of them into the sum of its scalars. -/
theorem coeff_squarefree_gessel {K : Type*} [CommRing K] (n : ℕ) (S : Finset ℕ) :
    MvPowerSeries.coeff (∑ j ∈ Icc 1 n, Finsupp.single j 1) (gessel K n S) = 1 := by
  have hmem : (∑ j ∈ Icc 1 n, Finsupp.single j 1) ∈
      {d : ℕ →₀ ℕ | ∃ i : ℕ → ℕ, (∀ j ∈ Ico 1 n, i j ≤ i (j + 1)) ∧
        (∀ j ∈ S, i j < i (j + 1)) ∧ d = ∑ j ∈ Icc 1 n, Finsupp.single (i j) 1} :=
    ⟨id, fun _ _ => Nat.le_succ _, fun _ _ => Nat.lt_succ_self _, rfl⟩
  rw [MvPowerSeries.coeff_apply, gessel, Set.indicator_of_mem hmem]
  rfl

/-! ### Two lemmas about above-diagonal parking functions -/

/-- Membership in `PF̂^α_{aN,bN}` is a condition on the underlying path alone. -/
theorem mem_aboveWithReturns {a b N : ℕ} {α : List ℕ} {π : AboveParkingFunction a b N} :
    π ∈ aboveWithReturns α a b N ↔ HasAboveReturns α (abovePath π) := by
  simp [aboveWithReturns]

/-- **`max t̂dinv(P̂) = 0` when no labelling of `P̂` has a `t̂dinv` pair.** The maximum is a
`Finset` supremum over the labellings, so it is `0` as soon as every term is. -/
theorem aboveMaxTdinv_eq_zero {a b N : ℕ} {y : Heights a b N}
    (h : ∀ π : AboveParkingFunction a b N, abovePath π = y → aboveTdinv π = 0) :
    aboveMaxTdinv y = 0 :=
  Nat.le_zero.1 <| Finset.sup_le fun π hπ => (h π (Finset.mem_filter.1 hπ).2).le

/-! ### The top path of the `4 × 6` rectangle, and its unique labelling -/

/-- **The top path of the `4 × 6` rectangle**: `ŷ_0 = 0` and `ŷ_r = 6` for `1 ≤ r ≤ 4`. Its whole
diagram lies below it, so it has no cells and `ĥ = 0`, and all six of its north steps are in column
`0`. -/
def topPath : Heights 2 3 2 := fun r => if r = 0 then 0 else 6

/-- The top path is above the diagonal. -/
theorem isAboveDiagonal_topPath : IsAboveDiagonal topPath := ⟨rfl, rfl, by decide, by decide⟩

/-- The parts of the one-part composition `(2)` are positive. -/
theorem forall_pos_two : ∀ x ∈ ([2] : List ℕ), 0 < x := by simp

/-- The top path returns to the diagonal only at `0` and at `N`, so its return composition is the
one-part composition `(2)`: of the three ranks `k ≤ 2` only `k = 0` and `k = 2` have `ŷ_{2k} = 3k`,
and the partial sums of `(2)` are `0` and `2`. Proved by cases on `k` rather than by `decide`,
which gets stuck unfolding `List.scanl` through the module boundary. -/
theorem hasAboveReturns_topPath : HasAboveReturns [2] topPath := by
  refine ⟨isAboveDiagonal_topPath, forall_pos_two, rfl, fun k hk => ?_⟩
  interval_cases k <;> simp [ht, topPath]

/-- The top path has no cell above it, so its above-diagonal hook count is `0`. -/
theorem aboveHookCount_topPath : aboveHookCount topPath = 0 := by decide

/-- Every north step of the top path is in column `0`: the last abscissa at which the path is still
strictly below height `i + 1 ≤ 6` is `0`, the path having height `6` from abscissa `1` on. -/
theorem aboveColumn_topPath {i : ℕ} (hi : i < 6) : aboveColumn topPath i = 0 := by
  rw [aboveColumn, lastBelow, Nat.findGreatest_eq_zero_iff]
  intro m hm hm4
  interval_cases m <;> simp [ht, topPath] <;> omega

/-- **No labelling of the top path has a `t̂dinv` pair.** All six north steps lie in column `0`, so
the rank of the step indexed by `i` is `(aN+1)N·a·i = 20i`, and `t̂dinv` counts pairs of labels
whose ranks differ by less than the window `(aN+1)aN = 20`, in the strict order. Distinct multiples
of `20` never do. This holds for *every* labelling, which is what makes `max t̂dinv` computable
without enumerating them. -/
theorem aboveTdinv_eq_zero_of_topPath (π : AboveParkingFunction 2 3 2)
    (hπ : abovePath π = topPath) : aboveTdinv π = 0 := by
  have hrk : ∀ i : Fin 6, aboveStepRank π i = 20 * (i : ℕ) := fun i => by
    rw [aboveStepRank, hπ, aboveColumn_topPath i.isLt, abovePointRank]; push_cast; ring
  rw [aboveTdinv, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  rintro ⟨s, t⟩ - ⟨h1, h2, h3⟩
  rw [aboveLabelRank, aboveLabelRank, hrk, hrk] at h2 h3
  push_cast at h2 h3
  omega

/-- **The top path carries an above-diagonal parking function.** Its six north steps are all in one
column, so the labelling must be strictly increasing on all of them, and the identity is such a
labelling. -/
def topParking : AboveParkingFunction 2 3 2 :=
  ⟨(topPath, id), isAboveDiagonal_topPath, Function.bijective_id, fun _ _ h _ => h⟩

/-- **`d̂inv` of the top parking function is `0`**: `ĥ(P̂) = 0` and `t̂dinv = max t̂dinv = 0`. -/
theorem aboveDinv_topParking : aboveDinv topParking = 0 := by
  rw [aboveDinv, aboveTdinv_eq_zero_of_topPath topParking rfl,
    show abovePath topParking = topPath from rfl,
    aboveMaxTdinv_eq_zero aboveTdinv_eq_zero_of_topPath, aboveHookCount_topPath]
  ring

/-- The top parking function has return composition `(2)`. -/
theorem mem_aboveWithReturns_topParking : topParking ∈ aboveWithReturns [2] 2 3 2 := by
  rw [mem_aboveWithReturns, show abovePath topParking = topPath from rfl]
  exact hasAboveReturns_topPath

/-! ### The right-hand side does not vanish at `q = 0`, `u = 1` -/

/-- **A weighted sum of fundamental quasisymmetric functions at `q = 0`, `u = 1` is nonzero as soon
as one index has vanishing exponent.** Reading the coefficient of `x_1 ⋯ x_n` turns the sum into
`∑_i 0^{d i}`, which is the number of indices with `d i = 0`; that count is positive and a positive
natural number is nonzero in characteristic zero.

Stated over an abstract index set on purpose. Applied directly at
`HJO.ParkingFunctions.aboveWithReturns [2] 2 3 2`, the step that consumes the membership hypothesis
tries to identify two copies of that `Finset` at default transparency, which unfolds `Finset.univ`
for a `Fintype` of some `10^9` elements and does not return; with the index set a variable the same
step is syntactic. -/
private theorem filter_exponent_eq_zero_of_sum_gessel_eq_zero {K : Type*} [Field K] [CharZero K]
    {ι : Type*} (s : Finset ι) (d : ι → ℤ) (e : ι → ℕ) (n : ℕ) (T : ι → Finset ℕ)
    (hz : ∑ i ∈ s, ((0 : K) ^ d i * (1 : K) ^ e i) • gessel K n (T i) = 0) :
    {i ∈ s | d i = 0} = ∅ := by
  have h := congrArg (MvPowerSeries.coeff (∑ j ∈ Icc 1 n, Finsupp.single j 1)) hz
  rw [map_zero, map_sum] at h
  simp only [map_smul, smul_eq_mul, coeff_squarefree_gessel, mul_one, one_pow] at h
  rw [Finset.sum_congr rfl fun i _ => show (0 : K) ^ d i = if d i = 0 then 1 else 0 from by
      rcases eq_or_ne (d i) 0 with hh | hh
      · simp [hh]
      · simp [zero_zpow _ hh, hh],
    Finset.sum_boole, Nat.cast_eq_zero, Finset.card_eq_zero] at h
  exact h

/-- **The parking-function side of the shuffle identity is nonzero at `q = 0`, `u = 1`.** The number
of summands with `d̂inv = 0` is positive, because `HJO.Mellit.topParking` is one of them. -/
theorem aboveSum_ne_zero_at_zero (L : Type) [Field L] [Algebra ℚ L] :
    ∑ π ∈ aboveWithReturns [2] 2 3 2,
        ((0 : L) ^ aboveDinv π * (1 : L) ^ aboveArea (abovePath π)) •
          gessel L (3 * 2) (descentReverse (3 * 2) (aboveIdes π)) ≠ 0 := by
  have hcz : CharZero L := charZero_of_injective_algebraMap (algebraMap ℚ L).injective
  intro hz
  have h := filter_exponent_eq_zero_of_sum_gessel_eq_zero _ aboveDinv
    (fun π => aboveArea (abovePath π)) (3 * 2)
    (fun π => descentReverse (3 * 2) (aboveIdes π)) hz
  rw [Finset.eq_empty_iff_forall_notMem] at h
  refine h topParking ?_
  rw [Finset.mem_filter, mem_aboveWithReturns, show abovePath topParking = topPath from rfl]
  exact ⟨hasAboveReturns_topPath, aboveDinv_topParking⟩

/-! ### The three clauses are contradictory at `q = 0` -/

/-- **Three of the four clauses of the interface are jointly contradictory at `q = 0`, `u = 1`.**
`MellitInduction` kills `D_{η,c_α}` through the factor `(qu)^{ℓ-N}`, `Rem41` then kills the path
sum, and `RhsSumsAgree` equates that with a sum that is nonzero by
`HJO.Mellit.aboveSum_ne_zero_at_zero`.

`LhsRewrite` is not used, and neither is any property of the sweep system beyond the three gradings
every one carries: the replication family the induction clause is applied to is supplied by
`HJO.Mellit.replExists`, and the realisation the remark clause is applied to by
`HJO.PhiMul.isRealisation_realise`. So no choice of substrate can rescue the conjunction. -/
theorem false_of_clauses_at_zero {L : Type} [Field L] [Algebra ℚ L] (S : SweepSystem L 0 1)
    (hind : MellitInduction S 2 3) (hrem : Rem41 S 2 3) (hrhs : RhsSumsAgree S 2 3) : False := by
  obtain ⟨Ω, hΩ⟩ := replExists S
  have hlevel : IsAdmissibleLevel (sepLevel 2 2) := isAdmissibleLevel_sepLevel 2 2
  have hsep : SeparatesDiagonal 2 3 2 (sepLevel 2 2) := separatesDiagonal_sepLevel two_pos
  have hD : S.D (sepLevel 2 2) (compColouring 2 3 [2]) = 0 := by
    rw [hind Ω hΩ 2 _ hlevel hsep [2] forall_pos_two rfl]
    norm_num
  have hpath := hrem (PhiMul.realise L) (PhiMul.isRealisation_realise L) 2 _ hlevel hsep [2]
    forall_pos_two rfl
  rw [hD] at hpath
  simp only [map_zero, smul_zero] at hpath
  have hrhs2 := hrhs 2 two_pos [2] forall_pos_two rfl
  rw [hpath] at hrhs2
  exact aboveSum_ne_zero_at_zero L hrhs2.symm

/-- **The interface read at all parameters is false.** This is `HJO.Mellit.MellitInput` without
its genericity hypothesis: for every field of
characteristic zero there is no such family of sweep systems, because there is none at `q = 0`,
`u = 1`, `(a, b) = (2, 3)`.

So that statement cannot be proved, and a reduction of anything to it is vacuous. The witness is
small and specific on purpose: it names the parameter values, the composition and the single
parking function that break it. -/
theorem not_mellitInput_unrestricted (L : Type) [Field L] [Algebra ℚ L] :
    ¬ ∀ (q u : L) (a b : ℕ), Nat.Coprime a b → 1 < a → a < b →
        ∃ S : SweepSystem L q u,
          LhsRewrite S a b ∧ MellitInduction S a b ∧ Rem41 S a b ∧ RhsSumsAgree S a b := by
  intro h
  obtain ⟨S, -, hind, hrem, hrhs⟩ := h 0 1 2 3 (by decide) (by decide) (by decide)
  exact false_of_clauses_at_zero S hind hrem hrhs

end HJO.Mellit
