/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.Shuffle.SweepWordValuesTwoThreeTwoAlpha
public import HJO.Shuffle.SweepWordValuesTwoThreeTwoAlphaUpper

/-! # `HJO.Mellit.MellitInduction` at `(a,b) = (2,3)`, `N = 2`, `α = (2)`: decided

This is the first instance of the clause of `HJO.Mellit.mellitInduction_sweepWitness` with `ℓ < N`,
where the factor `(qu)^{ℓ-N}` is a genuine inverse power rather than absent.
`HJO/Shuffle/SweepInductionInstanceTwo.lean` reduces it to one identity in `HJO.Sweep.Total L`
— that the invariant of the `4 × 6` rectangle at the colouring `c_{(2)}` and the level `9/2` is
`(qu)^{-1}Z^{(1)}_{2,3}` applied to minus the `N = 1` invariant. This file evaluates that
invariant and discharges the equivalence.

## The four steps

1. `HJO.Mellit.filter_aboveDiagonal_compColouring_two_three_alphaTwo`: the index set is the nineteen
   paths named in `HJO/Shuffle/SweepWordsTwoThreeTwoAlpha.lean`, all of them with `ŷ_2 ≥ 4`.
   `HJO.Mellit.aboveReturnPaths_two_three_two_alphaTwo` reads that through the return composition,
   and `HJO.Mellit.dsc_compColouring_eq_sum_partialSweepWord` then turns the sum over
   *traces* into a sum over those nineteen paths with no multiplicity —
   `HJO.Mellit.card_traceIndex_two_three_two` already having checked that the traces do not
   collapse below the path count.
2. `HJO/Shuffle/SweepWordValuesTwoThreeTwoAlpha.lean` evaluates each of the nineteen partial
   sweep words on the vacuum.
3. `HJO.Mellit.dsc_two_three_two_alphaTwo` adds the nineteen values: eleven monomials survive,
   over the `y_1`-degrees `2` to `6`.
4. `HJO.Mellit.dsc_two_three_two_alphaTwo_eq_smul_stageWordTotal` matches that against the
   closed form `HJO.Mellit.stageWordTotal_two_three_two_eq` of the right-hand side, divided by `qu`.
   Every one of the eleven coefficients of the stage word is divisible by `qu`, which is what makes
   the `ℓ < N` factor cancel rather than leave a denominator.

## The inverse power

The clause carries `(qu)^{ℓ-N} = (qu)^{-1}` here, and the replicated letter `Z^{(1)}_{2,3}` carries
the inverse `(qu)^{-1}z_1` of `HJO.Sweep.slopeOperator`. Neither cancels the other: the eleven
coefficients of `HJO.Mellit.stageWordTotal_two_three_two_eq` are each divisible by `qu` exactly
once, and dividing by `qu` is what produces the sweep side. So the reduced identity contains no
inverse power, but `q ≠ 0` and `u ≠ 0` are still what make it an identity rather than a statement
about the zero map.

## What this decides

`HJO.Mellit.mellitInduction_two_three_alphaTwo` is the clause of `HJO.Mellit.MellitInduction` at
`(a,b) = (2,3)`, `N = 2`, `α = (2)` — both quantifiers, over replication families and over
admissible separating levels, in both directions — proved outright. It is the first instance with
`ℓ < N` to be decided, and the first at all whose left-hand side is a sum of nineteen sweep words.

## Genericity

`q ≠ 0`, `u ≠ 0` and `q ≠ 1`, and no more; `HJO.Mellit.two_three_two_in_range` derives all three
from the `AlgebraicIndependent ℤ ![q, u]` that `HJO.Mellit.MellitInput` carries, so
`HJO.Mellit.mellitInduction_two_three_alphaTwo_of_input` assumes nothing beyond that hypothesis.
Each of the three is the inverse-becomes-zero hazard and not bookkeeping: at `q = 0` or `u = 0` the
letter `(qu)^{-1}z_1` of `HJO.Sweep.slopeOperator` is the zero map, at `q = 1` the scalar
`q^2/(1-q)` of `HJO.Sweep.zop` is undefined, and `HJO.Sweep.corner` divides by `q - 1`; a verdict at
any of them would be false rather than vacuous. `(2,3)` is coprime with `1 < 2 < 3`, so the instance
is strictly inside `HJO.Mellit.MellitInput`'s quantification and is not the degenerate `a = 1`
case.

## What is not claimed

These are values of `HJO.Mellit.dsc` and `HJO.Mellit.sweepOperator` at one instance, and one
clause of `HJO.Mellit.mellitInduction_sweepWitness` discharged at one instance, not the general
statements themselves.

## References

The file evaluates `HJO.Mellit.dsc`, `HJO.Mellit.compColouring`, `HJO.Mellit.sweepOperator`,
`HJO.Mellit.stage` and `HJO.Mellit.replicatedLetter` at one instance of
`HJO.Mellit.mellitInduction_sweepWitness`.
-/

@[expose] public section

-- The eleven scalar identities and the two closing normalisations are written in one uniform shape:
-- which members of the rewrite set fire, and whether a closing `ring` is needed at all, depends on
-- the coefficient. So a step may leave a simp argument unused, or reach its value before the
-- normalisation runs. This is the arrangement of
-- `HJO/Shuffle/SweepStageWordTwoThreeTwoValue.lean`, and its linter exemption too.
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace HJO.Mellit

open Finset HJO.Paths HJO.Sweep HJO.Sym

set_option maxRecDepth 4000000 in
/-- **The nineteen paths of the `α = (2)` instance.** The above-diagonal paths of the `4 × 6`
rectangle whose colouring at the level `9/2` is `c_{(2)}` are exactly the nineteen named in
`HJO/Shuffle/SweepWordsTwoThreeTwoAlpha.lean`: each is above-diagonal and coloured `c_{(2)}` —
one `decide` apiece — and the count
`HJO.Mellit.card_aboveDiagonal_compColouring_two_three_two` says there are no others.

They are the nineteen weakly increasing `(ŷ_1, ŷ_2, ŷ_3)` with `ŷ_1 ≥ 2`, `ŷ_2 ≥ 4` and `ŷ_3 ≥ 5`;
`ŷ_2 ≥ 4` is the whole of what separates `c_{(2)}` from `c_{(1,1)}`, the level `9/2` acquiring the
extra cells `(1,3)` and `(2,3)` exactly when `ŷ_2 = 3`. -/
theorem filter_aboveDiagonal_compColouring_two_three_alphaTwo :
    ({y : Paths.Heights 2 3 2 | Paths.IsAboveDiagonal y ∧
        colouring y (sepLevel 2 2) = compColouring 2 3 [2]} : Finset (Paths.Heights 2 3 2))
      = {alphaTwoPath245, alphaTwoPath246, alphaTwoPath255, alphaTwoPath256, alphaTwoPath266,
          alphaTwoPath345, alphaTwoPath346, alphaTwoPath355, alphaTwoPath356, alphaTwoPath366,
          alphaTwoPath445, alphaTwoPath446, alphaTwoPath455, alphaTwoPath456, alphaTwoPath466,
          alphaTwoPath555, alphaTwoPath556, alphaTwoPath566, alphaTwoPath666} := by
  symm
  apply Finset.eq_of_subset_of_card_le
  · intro y hy
    simp only [Finset.mem_insert, Finset.mem_singleton] at hy
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl | rfl | rfl | rfl
    all_goals rw [Finset.mem_filter]
    all_goals exact ⟨Finset.mem_univ _, by decide +kernel, by decide +kernel⟩
  · rw [card_aboveDiagonal_compColouring_two_three_two]
    decide +kernel

/-- **The index set of the `α = (2)` sum at `(a,b) = (2,3)`, `N = 2`**, read through the return
composition rather than the colouring: `HJO.Mellit.aboveReturnPaths` is what
`HJO.Mellit.dsc_compColouring_eq_sum_partialSweepWord` sums over, and
`HJO.Mellit.colouring_eq_compColouring_iff` says the two descriptions agree on an above-diagonal
path at an admissible separating level.

Deriving it rather than deciding it is not a stylistic choice: the whole `Finset` equality does not
reduce in the module system, the `Fintype` instance on `HJO.Paths.Heights 2 3 2` getting stuck on
`Multiset.Pi.cons`. -/
theorem aboveReturnPaths_two_three_two_alphaTwo :
    aboveReturnPaths 2 3 2 [2] = {alphaTwoPath245, alphaTwoPath246, alphaTwoPath255,
        alphaTwoPath256, alphaTwoPath266, alphaTwoPath345, alphaTwoPath346, alphaTwoPath355,
        alphaTwoPath356, alphaTwoPath366, alphaTwoPath445, alphaTwoPath446, alphaTwoPath455,
        alphaTwoPath456, alphaTwoPath466, alphaTwoPath555, alphaTwoPath556, alphaTwoPath566,
        alphaTwoPath666} := by
  have hiff : ∀ y : Paths.Heights 2 3 2, Paths.IsAboveDiagonal y →
      (colouring y (sepLevel 2 2) = compColouring 2 3 [2] ↔ Paths.HasAboveReturns [2] y) :=
    fun y hy => colouring_eq_compColouring_iff (isAdmissibleLevel_sepLevel 2 2)
      (separatesDiagonal_sepLevel' 2 3 2) (by decide) (by omega) (by omega) (by simp) rfl hy
  rw [← filter_aboveDiagonal_compColouring_two_three_alphaTwo]
  ext y
  rw [mem_aboveReturnPaths_iff, Finset.mem_filter]
  refine ⟨fun h => ⟨Finset.mem_univ y, h.1, (hiff y h.1).2 h⟩,
    fun h => (hiff y h.2.1).1 h.2.2⟩

section Value

variable {L : Type*} [Field L] [Algebra ℚ L] {q u : L}

/-- **`D_{9/2,c_{(2)}}` in the `4 × 6` rectangle**, for `q ∉ {0,1}`: the sum of the nineteen words
of `HJO.Mellit.aboveReturnPaths_two_three_two_alphaTwo`, in the grading `ℓ = 1`, so a polynomial in
`y_1` alone.

Eleven monomials survive out of the nineteen words' fifty-odd terms, and the collapse is genuine:
`e_1^2e_2y_1^2` has coefficient `1` although no single word contributes `1` there, and the
`e_4y_1^2` coefficient `(q + u - 1)(q^2 + u^2 - 1)` is assembled from five different paths. -/
theorem dsc_two_three_two_alphaTwo (hq0 : q ≠ 0) (hq1 : q ≠ 1) :
    dsc q u 2 3 2 (sepLevel 2 2) (compColouring 2 3 [2])
      = ((q + u - 1)*(q ^ 2 + u ^ 2 - 1) : L) • (MvPolynomial.C (elemSymm L 4) * ((auxVar 1 : Total
          L) ^ 2))
        + (q + u - 1 : L) • (MvPolynomial.C (elemSymm L 2 ^ 2) * ((auxVar 1 : Total L) ^ 2))
        + (q ^ 2 + q*u + u ^ 2 - 1 : L) • (MvPolynomial.C (elemSymm L 1 * elemSymm L 3) *
            ((auxVar 1 : Total L) ^ 2))
        + (1 : L) • (MvPolynomial.C (elemSymm L 1 ^ 2 * elemSymm L 2) * ((auxVar 1 : Total L) ^ 2))
        + (-u ^ 2*(q + u ^ 2 - 1) : L) • (MvPolynomial.C (elemSymm L 3) * ((auxVar 1 : Total L)
            ^ 3))
        + (-u*(q + u ^ 2 + 2*u - 1) : L) • (MvPolynomial.C (elemSymm L 1 * elemSymm L 2) *
            ((auxVar 1 : Total L) ^ 3))
        + (-u : L) • (MvPolynomial.C (elemSymm L 1 ^ 3) * ((auxVar 1 : Total L) ^ 3))
        + (u ^ 2*(q + u ^ 3 + u - 1) : L) • (MvPolynomial.C (elemSymm L 2) * ((auxVar 1 : Total L)
            ^ 4))
        + (u ^ 2*(u ^ 2 + u + 1) : L) • (MvPolynomial.C (elemSymm L 1 ^ 2) * ((auxVar 1 : Total L)
            ^ 4))
        + (-u ^ 4*(u ^ 2 + u + 1) : L) • (MvPolynomial.C (elemSymm L 1) * ((auxVar 1 : Total L)
            ^ 5))
        + (u ^ 7 : L) • ((auxVar 1 : Total L) ^ 6) := by
  rw [dsc_compColouring_eq_sum_partialSweepWord q u (isAdmissibleLevel_sepLevel 2 2)
      (separatesDiagonal_sepLevel' 2 3 2) (by decide) (by omega) (by omega) (by simp) rfl,
    aboveReturnPaths_two_three_two_alphaTwo,
    Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_insert (by decide), Finset.sum_singleton,
    partialSweepWord_alphaTwoPath245_apply_one hq0 hq1,
      partialSweepWord_alphaTwoPath246_apply_one hq0 hq1,
      partialSweepWord_alphaTwoPath255_apply_one hq0 hq1,
      partialSweepWord_alphaTwoPath256_apply_one hq0 hq1,
      partialSweepWord_alphaTwoPath266_apply_one hq0 hq1,
      partialSweepWord_alphaTwoPath345_apply_one hq0 hq1,
      partialSweepWord_alphaTwoPath346_apply_one hq0 hq1,
      partialSweepWord_alphaTwoPath355_apply_one hq0 hq1,
      partialSweepWord_alphaTwoPath356_apply_one hq0 hq1,
      partialSweepWord_alphaTwoPath366_apply_one hq0 hq1,
      partialSweepWord_alphaTwoPath445_apply_one hq0 hq1,
      partialSweepWord_alphaTwoPath446_apply_one hq0 hq1,
      partialSweepWord_alphaTwoPath455_apply_one hq0 hq1,
      partialSweepWord_alphaTwoPath456_apply_one hq0 hq1,
      partialSweepWord_alphaTwoPath466_apply_one hq0 hq1,
      partialSweepWord_alphaTwoPath555_apply_one hq0 hq1,
      partialSweepWord_alphaTwoPath556_apply_one hq0 hq1,
      partialSweepWord_alphaTwoPath566_apply_one hq0 hq1,
      partialSweepWord_alphaTwoPath666_apply_one hq1]
  simp only [smul_eq_scal_mul, MvPolynomial.smul_eq_C_mul, scal, map_add, map_sub, map_neg,
    map_mul, map_one, map_pow, map_ofNat]
  ring

/-- **The right-hand side of the clause, evaluated: `(qu)^{-1}G_{1,2}(1)` is the same eleven
monomials.** `HJO.Mellit.stageWordTotal_two_three_two_eq` is the closed form of the stage
word at `α = (2)`, every coefficient of it divisible by `qu`; dividing by `qu` — the clause's own
`(qu)^{ℓ-N}` — gives exactly the value `HJO.Mellit.dsc_two_three_two_alphaTwo` computed on the sweep
side.

The eleven scalar identities are where `q ≠ 0` and `u ≠ 0` are spent, and they are not bookkeeping:
in a field `0⁻¹ = 0`, so at `q = 0` or `u = 0` the left-hand side collapses to `0` while the sweep
side does not. -/
theorem dsc_two_three_two_alphaTwo_eq_smul_stageWordTotal (hq0 : q ≠ 0) (hu0 : u ≠ 0)
    (hq1 : q ≠ 1) :
    ((q * u)⁻¹ • stageWordTotal q u 2 3 [2] : Total L)
      = ((q + u - 1)*(q ^ 2 + u ^ 2 - 1) : L) • (MvPolynomial.C (elemSymm L 4) * ((auxVar 1 : Total
          L) ^ 2))
        + (q + u - 1 : L) • (MvPolynomial.C (elemSymm L 2 ^ 2) * ((auxVar 1 : Total L) ^ 2))
        + (q ^ 2 + q*u + u ^ 2 - 1 : L) • (MvPolynomial.C (elemSymm L 1 * elemSymm L 3) *
            ((auxVar 1 : Total L) ^ 2))
        + (1 : L) • (MvPolynomial.C (elemSymm L 1 ^ 2 * elemSymm L 2) * ((auxVar 1 : Total L) ^ 2))
        + (-u ^ 2*(q + u ^ 2 - 1) : L) • (MvPolynomial.C (elemSymm L 3) * ((auxVar 1 : Total L)
            ^ 3))
        + (-u*(q + u ^ 2 + 2*u - 1) : L) • (MvPolynomial.C (elemSymm L 1 * elemSymm L 2) *
            ((auxVar 1 : Total L) ^ 3))
        + (-u : L) • (MvPolynomial.C (elemSymm L 1 ^ 3) * ((auxVar 1 : Total L) ^ 3))
        + (u ^ 2*(q + u ^ 3 + u - 1) : L) • (MvPolynomial.C (elemSymm L 2) * ((auxVar 1 : Total L)
            ^ 4))
        + (u ^ 2*(u ^ 2 + u + 1) : L) • (MvPolynomial.C (elemSymm L 1 ^ 2) * ((auxVar 1 : Total L)
            ^ 4))
        + (-u ^ 4*(u ^ 2 + u + 1) : L) • (MvPolynomial.C (elemSymm L 1) * ((auxVar 1 : Total L)
            ^ 5))
        + (u ^ 7 : L) • ((auxVar 1 : Total L) ^ 6) := by
  have hs0 : (q * u)⁻¹ * (q * u ^ 4 + q ^ 2 * u ^ 3 + q ^ 3 * u ^ 2 + q ^ 4 * u - q * u ^ 3 - q ^ 3
      * u - q * u ^ 2
          - q ^ 2 * u + q * u) = ((q + u - 1)*(q ^ 2 + u ^ 2 - 1) : L) := by
    field_simp
    all_goals ring
  have hs1 : (q * u)⁻¹ * (q * u ^ 2 + q ^ 2 * u - q * u) = (q + u - 1 : L) := by
    field_simp
    all_goals ring
  have hs2 : (q * u)⁻¹ * (q * u ^ 3 + q ^ 2 * u ^ 2 + q ^ 3 * u - q * u) = (q ^ 2 + q*u + u ^ 2 - 1
      : L) := by
    field_simp
    all_goals ring
  have hs3 : (q * u)⁻¹ * (q * u) = (1 : L) := by
    field_simp
    all_goals ring
  have hs4 : (q * u)⁻¹ * (-(q * u ^ 5) - q ^ 2 * u ^ 3 + q * u ^ 3) = (-u ^ 2*(q + u ^ 2 - 1) : L)
      := by
    field_simp
    all_goals ring
  have hs5 : (q * u)⁻¹ * (-(q * u ^ 4) - 2 * q * u ^ 3 - q ^ 2 * u ^ 2 + q * u ^ 2) = (-u*(q + u
      ^ 2 + 2*u - 1) : L) := by
    field_simp
    all_goals ring
  have hs6 : (q * u)⁻¹ * (-(q * u ^ 2)) = (-u : L) := by
    field_simp
    all_goals ring
  have hs7 : (q * u)⁻¹ * (q * u ^ 6 + q * u ^ 4 + q ^ 2 * u ^ 3 - q * u ^ 3) = (u ^ 2*(q + u ^ 3 +
      u - 1) : L) := by
    field_simp
    all_goals ring
  have hs8 : (q * u)⁻¹ * (q * u ^ 5 + q * u ^ 4 + q * u ^ 3) = (u ^ 2*(u ^ 2 + u + 1) : L) := by
    field_simp
    all_goals ring
  have hs9 : (q * u)⁻¹ * (-(q * u ^ 7) - q * u ^ 6 - q * u ^ 5) = (-u ^ 4*(u ^ 2 + u + 1) : L) := by
    field_simp
    all_goals ring
  have hs10 : (q * u)⁻¹ * (q * u ^ 8) = (u ^ 7 : L) := by
    field_simp
    all_goals ring
  rw [stageWordTotal_two_three_two_eq hq0 hu0 hq1]
  simp only [smul_add, smul_smul, hs0, hs1, hs2, hs3, hs4, hs5, hs6, hs7, hs8, hs9, hs10]
  simp only [smul_eq_scal_mul, MvPolynomial.smul_eq_C_mul, scal, map_add, map_sub, map_neg,
    map_mul, map_one, map_pow, map_ofNat]
  ring

/-! ### The clause, decided -/

/-- **`D_{9/2,c_{(2)}} = -(qu)^{-1}Z^{(1)}_{2,3}(D_{5/2,c_{(1)}})`**: the reduced identity that
`HJO.Mellit.mellitInduction_two_three_two_iff_dsc` says the clause at this instance *is*.

Both sides are now computed: the left by
`HJO.Mellit.dsc_two_three_two_alphaTwo` out of the nineteen sweep words, the right by
`HJO.Sweep.stageWordTotal_two_three_two_eq_replicated_neg_dsc` — which rewrites the replicated
letter on the `N = 1` invariant as the stage word — followed by
`HJO.Mellit.dsc_two_three_two_alphaTwo_eq_smul_stageWordTotal`. The two routes share no lemma: the
left runs through `HJO.Mellit.sweepOperator` on the `4 × 6` rectangle, the right through
`HJO.Sweep.slopeOperator` and `HJO.Sweep.zop` on `V_1`. -/
theorem dsc_two_three_two_alphaTwo_eq_replicated (hq0 : q ≠ 0) (hu0 : u ≠ 0) (hq1 : q ≠ 1) :
    dsc q u 2 3 2 (sepLevel 2 2) (compColouring 2 3 [2])
      = (q * u)⁻¹ • replicatedTotal q u 2 3 0
          (-(dsc q u 2 3 1 (sepLevel 2 1) (compColouring 2 3 [1]))) := by
  rw [← stageWordTotal_two_three_two_eq_replicated_neg_dsc hq0 hu0 hq1,
    dsc_two_three_two_alphaTwo_eq_smul_stageWordTotal hq0 hu0 hq1,
    dsc_two_three_two_alphaTwo hq0 hq1]

/-- **The clause of `HJO.Mellit.mellitInduction_sweepWitness` at `(a,b) = (2,3)`, `N = 2`,
`α = (2)`, proved.**

Both quantifiers of `HJO.Mellit.MellitInduction`'s body are discharged — over replication families
and over admissible separating levels — because
`HJO.Mellit.mellitInduction_two_three_two_iff_dsc` removes them in both directions, and what it
leaves is `HJO.Mellit.dsc_two_three_two_alphaTwo_eq_replicated`. The statement is not transcribed:
it is the left-hand side of that equivalence, and
`HJO.Mellit.mellitInduction_two_three_two_apply_of_clause` is what says that side is
`HJO.Mellit.MellitInduction`'s own body at `N = 2` and this composition, instantiated and nothing
else — so a statement that had drifted from the clause could not be closed this way.

This is the first instance with `ℓ < N`: the scalar is `(-1)^2(qu)^{1-2} = (qu)^{-1}`, a genuine
inverse power. `q ≠ 0`, `u ≠ 0`, `q ≠ 1`: see the module docstring on why none of the three is
removable. -/
theorem mellitInduction_two_three_alphaTwo (hq0 : q ≠ 0) (hu0 : u ≠ 0) (hq1 : q ≠ 1) :
    ∀ Ω, IsReplicationFamily (sweepWitness q u 2 3) Ω →
      ∀ η : ℚ, IsAdmissibleLevel η → SeparatesDiagonal 2 3 2 η →
        (sweepWitness q u 2 3).D η (compColouring 2 3 [2])
          = ((-1 : L) ^ ((2 - 1) * 2)
              * (q * u) ^ ((([2] : List ℕ).length : ℤ) - ((2 : ℕ) : ℤ))) •
              stageWord (sweepWitness q u 2 3) Ω 2 3 [2] :=
  (mellitInduction_two_three_two_iff_dsc hq0 hu0 hq1).2
    (dsc_two_three_two_alphaTwo_eq_replicated hq0 hu0 hq1)

/-- **The statement proved above is the clause's own body, not a transcription of it.** The whole of
this proof is `HJO.Mellit.mellitInduction_two_three_two_apply_of_clause` instantiated at `α = (2)`,
and that lemma's own proof is `fun Ω hΩ η hηa hηs => h Ω hΩ 2 η hηa hηs α hpos hsum` — every
argument one of `HJO.Mellit.MellitInduction`'s binders, with nothing adjusted on the way. So the
`Prop` that `HJO.Mellit.mellitInduction_two_three_alphaTwo` proves is exactly what
`HJO.Mellit.MellitInduction (HJO.Mellit.sweepWitness q u 2 3) 2 3` asserts at this composition; a
statement that had drifted from the clause could not be closed by instantiation.

This is the check that decides whether the verdict is worth anything: a hand-transcribed `Prop` that
merely looks like the clause is worth nothing. -/
theorem mellitInduction_two_three_alphaTwo_of_clause
    (h : MellitInduction (sweepWitness q u 2 3) 2 3) :
    ∀ Ω, IsReplicationFamily (sweepWitness q u 2 3) Ω →
      ∀ η : ℚ, IsAdmissibleLevel η → SeparatesDiagonal 2 3 2 η →
        (sweepWitness q u 2 3).D η (compColouring 2 3 [2])
          = ((-1 : L) ^ ((2 - 1) * 2)
              * (q * u) ^ ((([2] : List ℕ).length : ℤ) - ((2 : ℕ) : ℤ))) •
              stageWord (sweepWitness q u 2 3) Ω 2 3 [2] :=
  mellitInduction_two_three_two_apply_of_clause h (by simp) rfl

/-- **The clause at this instance, from the hypothesis of `HJO.Mellit.MellitInput` alone.** The
three parameter exclusions are *derived* from `AlgebraicIndependent ℤ ![q, u]` by
`HJO.Mellit.two_three_two_in_range`, so nothing is assumed of `q` and `u` beyond what
`HJO.Mellit.MellitInput` carries. This is the check against a verdict at `q = 1` or `u = 0`, each
of which lies outside the quantification and at each of which a letter of
`HJO.Sweep.slopeOperator` or `HJO.Sweep.zop` degenerates to the zero map. -/
theorem mellitInduction_two_three_alphaTwo_of_input (hqu : AlgebraicIndependent ℤ ![q, u]) :
    ∀ Ω, IsReplicationFamily (sweepWitness q u 2 3) Ω →
      ∀ η : ℚ, IsAdmissibleLevel η → SeparatesDiagonal 2 3 2 η →
        (sweepWitness q u 2 3).D η (compColouring 2 3 [2])
          = ((-1 : L) ^ ((2 - 1) * 2)
              * (q * u) ^ ((([2] : List ℕ).length : ℤ) - ((2 : ℕ) : ℤ))) •
              stageWord (sweepWitness q u 2 3) Ω 2 3 [2] :=
  have h := two_three_two_in_range hqu
  mellitInduction_two_three_alphaTwo h.2.2.2.1 h.2.2.2.2.1 h.2.2.2.2.2

/-- **The clause at this instance is not vacuous.** A replication family exists and `9/2` is an
admissible separating level, so `HJO.Mellit.mellitInduction_two_three_alphaTwo` asserts an identity
that is actually made — the trap being that every statement of the Mellit layer
opens "let `Ω` be a replication family" and would be vacuously true with none exhibited. -/
theorem mellitInduction_two_three_alphaTwo_nonvacuous (hq0 : q ≠ 0) (hu0 : u ≠ 0) (hq1 : q ≠ 1) :
    ∃ Ω, IsReplicationFamily (sweepWitness q u 2 3) Ω ∧
      IsAdmissibleLevel (sepLevel 2 2) ∧ SeparatesDiagonal 2 3 2 (sepLevel 2 2) ∧
        (sweepWitness q u 2 3).D (sepLevel 2 2) (compColouring 2 3 [2])
          = ((-1 : L) ^ ((2 - 1) * 2)
              * (q * u) ^ ((([2] : List ℕ).length : ℤ) - ((2 : ℕ) : ℤ))) •
              stageWord (sweepWitness q u 2 3) Ω 2 3 [2] := by
  obtain ⟨Ω, hΩ⟩ := exists_isReplicationFamily (sweepWitness q u 2 3)
  exact ⟨Ω, hΩ, isAdmissibleLevel_sepLevel 2 2, separatesDiagonal_sepLevel' 2 3 2,
    mellitInduction_two_three_alphaTwo hq0 hu0 hq1 Ω hΩ (sepLevel 2 2)
      (isAdmissibleLevel_sepLevel 2 2) (separatesDiagonal_sepLevel' 2 3 2)⟩

end Value

end HJO.Mellit

end
