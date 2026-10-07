/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.Shuffle.BraidValueBOrigin
public import HJO.Shuffle.SweepAppendTwoThree
public import HJO.Shuffle.MellitSweepSecondZ
public import HJO.Shuffle.MellitSlopeLadder
public import HJO.CarlssonMellit.BopModified

/-! # The invariant below the level zero, evaluated at the `2 × 3` witness

`HJO.Mellit.dsc_eq_one_of_lt_zero_of_braid_recursions` is a proved conditional: if
`HJO.Mellit.braidValueColouring` satisfies `HJO.Mellit.SweepRecursionACD`,
`HJO.Mellit.SweepRecursionBE` and `HJO.Mellit.SweepRecursionUnswept` as those `Prop`s stand, then
`HJO.Mellit.dsc q u a b N η ∅ = 1` at every admissible `η < 0`. This file computes that value, at
`(a, b) = (2, 3)`, `N = 1`, and it is **not** `1`.

## The value

`HJO.Mellit.dsc_two_three_one_below_zero`: for `q ∉ {0, 1}` and **every** rational `η < 0`,

`D_{η,∅} = e_1e_2 + (q - 1 + u)e_3`,

an element of `Λ = V_0`. `HJO.Mellit.dsc_two_three_one_below_zero_ne_one` says it is not `1`;
`HJO.Mellit.braidValueColouring_ne_dsc_two_three_one` and
`HJO.Mellit.not_braid_recursions_two_three_one` draw the two consequences. The same computation with
the arithmetic left undone is `HJO.Mellit.dsc_two_three_one_below_zero_eq_dminus_dsc_sepLevel`:
`D_{η,∅} = d_-^{(1)}(D_{5/2,c_{(1)}})`, which exhibits
`HJO.Mellit.dsc_two_three_one` inside the answer, and which
`HJO.Mellit.dsc_two_three_one_below_zero_eq_dminus_dsc_sepLevel_of_recursion` proves again through
the proved recursion clauses instead of the sweep word —
`HJO.Mellit.dsc_below_zero_routes_agree` is the check that the two routes state the same identity.

## How

At `η < 0` every rank of the swept region is nonnegative (`HJO.Mellit.pointRank_nonneg` on the
weak-above-diagonal condition that `HJO.Paths.mem_sweptRegion` carries), so
`HJO.Mellit.sweptAbove` is the whole swept region and the partial word is the *full* sweep word
(`HJO.Mellit.partialSweepWord_eq_sweepWord_of_lt_zero`). Three steps then close the computation.

* **The index set.** `HJO.Mellit.dsc` sums over traces, not paths, and at a level that is not
  separating `HJO.Mellit.traceRep_eq_self` is unavailable. So the sum-over-traces is
  turned into a sum-over-paths by the weakest hypothesis that does it — that `HJO.Mellit.levelTrace`
  separates the paths of the fibre: `HJO.Mellit.dsc_eq_sum_of_levelTrace_injOn`. At `(2, 3)` with
  `N = 1` there are exactly two above-diagonal paths (`HJO.Mellit.eq_baseTwoThree`), both coloured
  `∅` below `0` (`HJO.Mellit.colouring_eq_empty_of_lt_zero`), and their traces differ because the
  point `(0,3)` is swept by `(0,3,3)` and not by `(0,2,3)`.

* **The two words.** Below `0` the sweep word picks up exactly two events beyond the ones the
  separating level `5/2` sees: the origin `(0,0)`, of rank `0`, and the far corner `(2,3)`, of rank
  `2`. The corner is a type-`D` event with nothing live to its right, so its operator is the
  identity (`HJO.Mellit.sweepOperator_of_eventType_D_of_sweepRight_eq_zero`); the origin is a
  type-`B` event of width `1` for both paths, so its operator is `d_-^{(1)}`. Hence
  `W_η(P̂) = d_-^{(1)}W_{5/2}(P̂)`, and the two values at `5/2` are the known
  `e_1y_1²` and `-uy_1³`.

* **The lowering operator.** `d_-^{(1)}(y_1^mC(A)) = C(B_mA)` is
  `HJO.Sweep.dminus_auxVar_pow_mul_C`, and `B_2(e_1) = e_1e_2 - (1-q)e_3` is the
  Hall--Littlewood value `HJO.Sym.bop_two_elemSymm_one`. On the scalar `u` the shift `τ^-_{1,1}`
  does nothing and `HJO.Sweep.dminus_auxVar_pow` gives `-ue_3`. Adding: `e_1e_2 + (q - 1 + u)e_3`.

## Why that is not `1`

`HJO.Sym.evalZero` kills every `e_{k+1}` (`HJO.Sym.evalZero_elemSymm_succ`), so it kills both
degree-`3` terms, while it sends `1` to `1`. No hypothesis on `q` or `u` is spent here: the value
misses the vacuum for **every** pair of parameters, generic or not.

## What this says about the braid candidate

`HJO.Mellit.dsc_recursions` says `HJO.Mellit.dsc` satisfies all five properties, so the three
`Prop`s are consistent statements and nothing here refutes any of them. What is refuted is
that `HJO.Mellit.braidValueColouring` satisfies them: it is `1` below the level `0`
(`HJO.Mellit.braidValueColouring_eq_one_of_lt_zero`) while `HJO.Mellit.dsc` is not, so the two
functions differ there, at least one of the three `Prop`s fails for the braid candidate, and
`HJO.Mellit.agreesWithDsc_of_recursions` cannot be applied to it as it stands. **The braid route
needs a level restriction.** Which of the three fails is not decided here — see "What is not
claimed".

## Genericity

The value needs `q ≠ 0` and `q ≠ 1`, both inherited from
`HJO.Mellit.dsc_two_three_one`: the corner operator of the `(0,2,3)` word carries `(q-1)⁻¹`, which
is the zero map at `q = 1`, and the type-`C` event carries `q^{-1}`. **No exclusion on `u`** — the
`u` enters only as the scalar of the type-`E` event of the `(0,3,3)` word and the answer is a
polynomial in it. So the refutation holds at every `u`, including `u = 0`, and at every `q` outside
`{0, 1}`; the braid candidate's own further exclusions `q + 1 ≠ 0` and `r² = q` are carried along
only because `HJO.Mellit.braidValueColouring` is defined under them.

## What is *not* claimed

Three things are left open, and the quantifiers matter.

* **Which of the three `Prop`s fails is not identified.** What is proved is that their conjunction
  fails for `HJO.Mellit.braidValueColouring` at `(a,b,N) = (2,3,1)`. The region to look at is
  unchanged: the proved per-event braid clauses each carry `aN < ηlo`
  (types `A`, `C`, `D`) or `0 < ηlo` (the unswept bulk), and none of the three `Prop`s does.
  `HJO.Mellit.not_sweepRecursionACD_of_dminus_braidValueColouring_sepLevel_ne_one` reduces the
  localization to one number — `d_-^{(1)}` of the braid candidate's value at `5/2` on the colouring
  `c_{(1)}` — and that number is a **missing evaluation**, not an obstruction: it is
  `HJO.Mellit.braidValueOfData` at one-letter data, and nothing here computes it.
* **Only `(a, b, N) = (2, 3, 1)` is computed.** The value at larger parameters is not; the two-path
  index set is what makes this one short.
* **`HJO.Mellit.dsc` is not claimed to fail any clause.** It satisfies all five
  (`HJO.Mellit.dsc_recursions`); the failure is the braid candidate's.

## References

A. Mellit, *Toric braids and `(m, n)`-parking functions*, Section 5, for `HJO.Mellit.dsc`,
`HJO.Mellit.isAdmissibleColouring_empty_and_dsc_eq_one`,
`HJO.Mellit.braidValueColouring_sweepRecursionsFloor`, `HJO.Mellit.braidValueColouring_eq_dsc_floor`
and `HJO.Sym.Bop`.
-/

@[expose] public section

open Finset

namespace HJO.Sym

variable {L : Type*} [Field L] [Algebra ℚ L]

/-- **A degree-`3` combination of the `e_k` is not the vacuum.** `HJO.Sym.evalZero` kills every
`e_{k+1}` and fixes `1`. No hypothesis on the coefficient: the two terms are killed whatever it
is. -/
theorem elemSymm_one_mul_two_add_C_mul_three_ne_one (c : L) :
    elemSymm L 1 * elemSymm L 2 + MvPolynomial.C c * elemSymm L 3 ≠ (1 : Lambda L) := by
  intro h
  have h1 : evalZero L (elemSymm L 1) = 0 := evalZero_elemSymm_succ (L := L) 0
  have h3 : evalZero L (elemSymm L 3) = 0 := evalZero_elemSymm_succ (L := L) 2
  have := congrArg (evalZero L) h
  rw [map_add, map_mul, map_mul, h1, h3, map_one, MvPolynomial.algHom_C] at this
  simp at this

end HJO.Sym

namespace HJO.Mellit

open ParkingFunctions Paths Sweep _root_.HJO.Sym

variable {a b N : ℕ}

/-! ### Below the level zero the partial sweep word is the whole sweep word

Every point of the swept region lies weakly above the diagonal, so its rank is nonnegative; a level
below `0` is therefore below every rank the sweep sees. -/

/-- **Below the level `0` nothing of the swept region is cut off.** The filter of
`HJO.Mellit.sweptAbove` is vacuous there, `HJO.Mellit.pointRank_nonneg` applying to every point of
the region. -/
theorem sweptAbove_eq_sweptRegion_of_lt_zero (y : Heights a b N) {η : ℚ} (hη : η < 0) :
    sweptAbove y η = sweptRegion y := by
  refine Finset.filter_true_of_mem fun P hP => ?_
  have h1 : (0 : ℤ) ≤ pointRank a b N P := pointRank_nonneg (N := N) (mem_sweptRegion.1 hP).2.1
  have h2 : (0 : ℚ) ≤ ((pointRank a b N P : ℤ) : ℚ) := by exact_mod_cast h1
  linarith

/-- **Below the level `0` the partial sweep word is the full sweep word.** The companion of
`HJO.Mellit.partialSweepWord_of_forall_le`, which makes it the identity above every rank. -/
theorem partialSweepWord_eq_sweepWord_of_lt_zero {L : Type*} [Field L] [Algebra ℚ L] (q u : L)
    (y : Heights a b N) {η : ℚ} (hη : η < 0) : partialSweepWord q u y η = sweepWord q u y := by
  refine partialSweepWord_eq_sweepWord q u y η fun P hP => ?_
  have h1 : (0 : ℤ) ≤ pointRank a b N P := pointRank_nonneg (N := N) (mem_sweptRegion.1 hP).2.1
  have h2 : (0 : ℚ) ≤ ((pointRank a b N P : ℤ) : ℚ) := by exact_mod_cast h1
  linarith

/-- **The trace below the level `0` is the whole swept region with its event data**, and in
particular does not depend on the level. -/
theorem levelTrace_eq_of_lt_zero (y : Heights a b N) {η : ℚ} (hη : η < 0) :
    levelTrace y η = (sweptRegion y).image fun P => (P, eventType y P, sweepRight y P) := by
  rw [levelTrace, sweptAbove_eq_sweptRegion_of_lt_zero y hη]

/-! ### The sum over traces is a sum over paths whenever the trace separates the fibre

`HJO.Mellit.dsc_compColouring_eq_sum_partialSweepWord` does this at a *separating* level, where
`HJO.Mellit.eq_of_levelTrace_eq` supplies the separation from `HJO.Mellit.SeparatesDiagonal`. Below
`0` the level is not separating — every point of the region outranks it, the on-diagonal ones
included — so the separation has to be supplied by hand, and the lemma is stated with it as the
hypothesis. -/

section Substrate

variable {L : Type*} [Field L] [Algebra ℚ L]

/-- **`D_{η,c}` is the sum of `W_η(P̂)(1)` over the above-diagonal paths coloured `c`, as soon as
the trace separates them.** The index set of `HJO.Mellit.dsc` is the image of that fibre under
`τ_η(·)`, so the hypothesis is exactly what makes the image sum a fibre sum
(`Finset.sum_image`) and what pins `HJO.Mellit.traceRep` to the path it came from. Nothing is asked
of `η`, `a`, `b`, `N`, `q` or `u`. -/
theorem dsc_eq_sum_of_levelTrace_injOn (q u : L) {η : ℚ} {c : Finset (ℕ × ℕ)}
    (hinj : ∀ y₁ y₂ : Heights a b N, IsAboveDiagonal y₁ → colouring y₁ η = c →
      IsAboveDiagonal y₂ → colouring y₂ η = c → levelTrace y₁ η = levelTrace y₂ η → y₁ = y₂) :
    dsc q u a b N η c
      = ∑ y ∈ {y ∈ (univ : Finset (Heights a b N)) | IsAboveDiagonal y ∧ colouring y η = c},
          partialSweepWord q u y η (1 : Total L) := by
  have hinj' : ∀ y₁ ∈ {y ∈ (univ : Finset (Heights a b N)) |
        IsAboveDiagonal y ∧ colouring y η = c},
      ∀ y₂ ∈ {y ∈ (univ : Finset (Heights a b N)) | IsAboveDiagonal y ∧ colouring y η = c},
      levelTrace y₁ η = levelTrace y₂ η → y₁ = y₂ := by
    intro y₁ h₁ y₂ h₂ h
    rw [Finset.mem_filter] at h₁ h₂
    exact hinj _ _ h₁.2.1 h₁.2.2 h₂.2.1 h₂.2.2 h
  rw [dsc, traceIndex, Finset.sum_image hinj']
  refine Finset.sum_congr rfl fun y hy => ?_
  have hmem : levelTrace y η ∈ traceIndex a b N η c := by
    rw [traceIndex]
    exact Finset.mem_image_of_mem _ hy
  obtain ⟨h1, h2, h3⟩ := traceRep_spec hmem
  rw [Finset.mem_filter] at hy
  rw [hinj _ _ h1 h2 hy.2.1 hy.2.2 h3]

/-- **The separating-level case, re-derived through `HJO.Mellit.dsc_eq_sum_of_levelTrace_injOn`.**
The statement is a character-for-character copy of
`HJO.Mellit.dsc_compColouring_eq_sum_partialSweepWord`, and
`HJO.Mellit.dsc_compColouring_sum_routes_agree` checks that. This is the consistency check on the
general lemma: at a separating level `HJO.Mellit.eq_of_levelTrace_eq` supplies the separation and
`HJO.Mellit.colouring_eq_compColouring_iff` identifies the fibre with
`HJO.Mellit.aboveReturnPaths`. -/
theorem dsc_compColouring_eq_sum_partialSweepWord_of_injOn (q u : L) {η : ℚ}
    (hηa : IsAdmissibleLevel η) (hηs : SeparatesDiagonal a b N η) (hab : Nat.Coprime a b)
    (ha : 0 < a) (hb : 0 < b) {α : List ℕ} (hpos : ∀ x ∈ α, 0 < x) (hsum : α.sum = N) :
    dsc q u a b N η (compColouring a b α)
      = ∑ y ∈ aboveReturnPaths a b N α, partialSweepWord q u y η (1 : Total L) := by
  have hset : {y ∈ (univ : Finset (Heights a b N)) |
      IsAboveDiagonal y ∧ colouring y η = compColouring a b α} = aboveReturnPaths a b N α := by
    ext y
    simp only [aboveReturnPaths, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨fun h => ⟨h.1, (colouring_eq_compColouring_iff hηa hηs hab ha hb hpos hsum h.1).1 h.2⟩,
      fun h => ⟨h.1, (colouring_eq_compColouring_iff hηa hηs hab ha hb hpos hsum h.1).2 h.2⟩⟩
  rw [dsc_eq_sum_of_levelTrace_injOn q u
    (fun _ _ h1 _ h2 _ h => eq_of_levelTrace_eq hηs hb h1 h2 h), hset]

/-- **The two routes to the separating-level sum state the same thing.** Both sides are proofs of
one `Prop`, so this typechecks exactly when the two statements are identical. -/
theorem dsc_compColouring_sum_routes_agree (q u : L) {η : ℚ}
    (hηa : IsAdmissibleLevel η) (hηs : SeparatesDiagonal a b N η) (hab : Nat.Coprime a b)
    (ha : 0 < a) (hb : 0 < b) {α : List ℕ} (hpos : ∀ x ∈ α, 0 < x) (hsum : α.sum = N) :
    dsc_compColouring_eq_sum_partialSweepWord (L := L) q u hηa hηs hab ha hb hpos hsum
      = dsc_compColouring_eq_sum_partialSweepWord_of_injOn q u hηa hηs hab ha hb hpos hsum :=
  rfl

end Substrate

/-! ### The fibre of the empty colouring at `(a, b) = (2, 3)`, `N = 1`, below the level zero

There are exactly two above-diagonal paths, both coloured `∅`, and their traces differ. -/

/-- **The two extra ranks below the separating level `5/2`.** `HJO.Mellit.pointRank_origin` gives
the first; the corner is the second. -/
theorem pointRank_two_three_corner : pointRank 2 3 1 ((2, 3) : ℕ × ℕ) = 2 := by decide

/-- **Both above-diagonal paths of the `2 × 3` rectangle are coloured `∅` below the level `0`, and
nothing else is.** `HJO.Mellit.eq_baseTwoThree` supplies the enumeration and
`HJO.Mellit.colouring_eq_empty_of_lt_zero` the colouring. -/
theorem filter_colouring_empty_two_three_one {η : ℚ} (hη : η < 0) :
    {y ∈ (univ : Finset (Heights 2 3 1)) |
        IsAboveDiagonal y ∧ colouring y η = (∅ : Finset (ℕ × ℕ))}
      = {baseTwoThreeA, baseTwoThreeB} := by
  ext y
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
    Finset.mem_singleton]
  refine ⟨fun h => eq_baseTwoThree h.1, ?_⟩
  rintro (rfl | rfl)
  · exact ⟨by decide, colouring_eq_empty_of_lt_zero (by decide) hη⟩
  · exact ⟨by decide, colouring_eq_empty_of_lt_zero (by decide) hη⟩

/-- **`(0,3)` is swept by `(0,3,3)` below the level `0`**, its rank being `18`. -/
theorem mem_sweptAbove_baseTwoThreeB_zero_three {η : ℚ} (hη : η < 0) :
    ((0, 3) : ℕ × ℕ) ∈ sweptAbove baseTwoThreeB η := by
  rw [sweptAbove_eq_sweptRegion_of_lt_zero _ hη]
  decide

/-- **The two paths have different traces below the level `0`.** The point `(0,3)` is swept by
`(0,3,3)` and not by `(0,2,3)`, and a trace records the point itself in its first component. This is
the separation `HJO.Mellit.dsc_eq_sum_of_levelTrace_injOn` asks for, supplied where
`HJO.Mellit.eq_of_levelTrace_eq` cannot reach. -/
theorem levelTrace_baseTwoThreeA_ne_levelTrace_baseTwoThreeB {η : ℚ} (hη : η < 0) :
    levelTrace baseTwoThreeA η ≠ levelTrace baseTwoThreeB η := by
  intro h
  have hmem : (((0, 3) : ℕ × ℕ), eventType baseTwoThreeB ((0, 3) : ℕ × ℕ),
      sweepRight baseTwoThreeB ((0, 3) : ℕ × ℕ)) ∈ levelTrace baseTwoThreeB η := by
    rw [levelTrace]
    exact Finset.mem_image_of_mem _ (mem_sweptAbove_baseTwoThreeB_zero_three hη)
  rw [← h, levelTrace, Finset.mem_image] at hmem
  obtain ⟨P, hP, hPe⟩ := hmem
  have hP3 : P = ((0, 3) : ℕ × ℕ) := congrArg Prod.fst hPe
  rw [hP3, sweptAbove_eq_sweptRegion_of_lt_zero _ hη] at hP
  revert hP
  decide

/-- **The fibre sum below the level `0`**: at `(a,b) = (2,3)`, `N = 1` the invariant of the empty
colouring is the sum of the two full sweep words on the vacuum. -/
theorem dsc_two_three_one_empty_eq_add {L : Type*} [Field L] [Algebra ℚ L] (q u : L) {η : ℚ}
    (hη : η < 0) :
    dsc q u 2 3 1 η (∅ : Finset (ℕ × ℕ))
      = partialSweepWord q u baseTwoThreeA η (1 : Total L)
        + partialSweepWord q u baseTwoThreeB η (1 : Total L) := by
  rw [dsc_eq_sum_of_levelTrace_injOn q u (c := (∅ : Finset (ℕ × ℕ)))
      (fun y₁ y₂ h1 _ h2 _ h => by
        rcases eq_baseTwoThree h1 with rfl | rfl <;> rcases eq_baseTwoThree h2 with rfl | rfl
        · rfl
        · exact absurd h (levelTrace_baseTwoThreeA_ne_levelTrace_baseTwoThreeB hη)
        · exact absurd h.symm (levelTrace_baseTwoThreeA_ne_levelTrace_baseTwoThreeB hη)
        · rfl),
    filter_colouring_empty_two_three_one hη,
    Finset.sum_insert (by simpa using (by decide : baseTwoThreeA ≠ baseTwoThreeB)),
    Finset.sum_singleton]

/-! ### The two words below the level zero

Beyond the events the separating level `5/2` sees, the sweep below `0` picks up the corner `(2,3)`,
of rank `2`, and the origin `(0,0)`, of rank `0`. The first is a type-`D` event with nothing live to
its right and so contributes the identity; the second is a type-`B` event of width `1` and so
contributes `d_-^{(1)}`. -/

section Words

variable {L : Type*} [Field L] [Algebra ℚ L]

/-- **The corner of the `2 × 3` rectangle contributes the identity, on either path.** -/
theorem sweepOperator_two_three_corner (q u : L) (y : Heights 2 3 1)
    (hD : eventType y ((2, 3) : ℕ × ℕ) = EventType.D)
    (h0 : sweepRight y ((2, 3) : ℕ × ℕ) = 0) :
    sweepOperator q u y ((2, 3) : ℕ × ℕ) = (1 : Module.End L (Total L)) :=
  sweepOperator_of_eventType_D_of_sweepRight_eq_zero q u y _ hD h0

/-- **The origin contributes `d_-^{(1)}` on `(0,2,3)`:** a type-`B` event of width `1`. -/
theorem sweepOperator_baseTwoThreeA_origin (q u : L) :
    sweepOperator q u baseTwoThreeA ((0, 0) : ℕ × ℕ) = dminus q 1 := by
  rw [sweepOperator, show eventType baseTwoThreeA ((0, 0) : ℕ × ℕ) = EventType.B from by decide,
    show sweepWidth baseTwoThreeA ((0, 0) : ℕ × ℕ) = 1 from by decide]

/-- **The origin contributes `d_-^{(1)}` on `(0,3,3)` too.** -/
theorem sweepOperator_baseTwoThreeB_origin (q u : L) :
    sweepOperator q u baseTwoThreeB ((0, 0) : ℕ × ℕ) = dminus q 1 := by
  rw [sweepOperator, show eventType baseTwoThreeB ((0, 0) : ℕ × ℕ) = EventType.B from by decide,
    show sweepWidth baseTwoThreeB ((0, 0) : ℕ × ℕ) = 1 from by decide]

/-- **The word of `(0,2,3)` below the level `0` is `d_-^{(1)}` of its word at `5/2`.** The two
extra events are peeled by `HJO.Mellit.partialSweepWord_step` through the windows `(-1, 0]` and
`(0, 2]`, each of which isolates a single rank of the rectangle. -/
theorem partialSweepWord_baseTwoThreeA_of_lt_zero (q u : L) {η : ℚ} (hη : η < 0) :
    partialSweepWord q u baseTwoThreeA η
      = dminus q 1 * ((1 : Module.End L (Total L))
        * partialSweepWord q u baseTwoThreeA (sepLevel 2 1)) := by
  rw [partialSweepWord_eq_sweepWord_of_lt_zero q u _ hη,
    ← partialSweepWord_eq_sweepWord_of_lt_zero q u baseTwoThreeA
      (show ((-1 : ℤ) : ℚ) + 1 / 2 < 0 from by norm_num),
    partialSweepWord_step q u (m := -1) (n := 0) (r := 0) (by decide) (pointRank_origin 2 3 1)
      (by norm_num) (by norm_num) (by decide : ((0, 0) : ℕ × ℕ) ∈ sweptRegion baseTwoThreeA),
    partialSweepWord_step q u (m := 0) (n := 2) (r := 2) (by decide) pointRank_two_three_corner
      (by norm_num) (by norm_num) (by decide : ((2, 3) : ℕ × ℕ) ∈ sweptRegion baseTwoThreeA),
    ← sepLevel_two_one, sweepOperator_baseTwoThreeA_origin,
    sweepOperator_two_three_corner q u _ (by decide) (by decide)]

/-- **The word of `(0,3,3)` below the level `0` is `d_-^{(1)}` of its word at `5/2`.** -/
theorem partialSweepWord_baseTwoThreeB_of_lt_zero (q u : L) {η : ℚ} (hη : η < 0) :
    partialSweepWord q u baseTwoThreeB η
      = dminus q 1 * ((1 : Module.End L (Total L))
        * partialSweepWord q u baseTwoThreeB (sepLevel 2 1)) := by
  rw [partialSweepWord_eq_sweepWord_of_lt_zero q u _ hη,
    ← partialSweepWord_eq_sweepWord_of_lt_zero q u baseTwoThreeB
      (show ((-1 : ℤ) : ℚ) + 1 / 2 < 0 from by norm_num),
    partialSweepWord_step q u (m := -1) (n := 0) (r := 0) (by decide) (pointRank_origin 2 3 1)
      (by norm_num) (by norm_num) (by decide : ((0, 0) : ℕ × ℕ) ∈ sweptRegion baseTwoThreeB),
    partialSweepWord_step q u (m := 0) (n := 2) (r := 2) (by decide) pointRank_two_three_corner
      (by norm_num) (by norm_num) (by decide : ((2, 3) : ℕ × ℕ) ∈ sweptRegion baseTwoThreeB),
    ← sepLevel_two_one, sweepOperator_baseTwoThreeB_origin,
    sweepOperator_two_three_corner q u _ (by decide) (by decide)]

end Words

/-! ### The lowering operator on the two values at the separating level -/

section Lowering

variable {L : Type*} [Field L] [Algebra ℚ L]

omit [Algebra ℚ L] in
/-- **A scalar of `L` passes through `C` from `Λ`.** -/
theorem smul_C_eq_C_C_mul (x : L) (f : Lambda L) :
    (x • MvPolynomial.C f : Total L) = MvPolynomial.C (MvPolynomial.C x * f) := by
  rw [smul_eq_scal_mul, scal, ← map_mul]

/-- **`d_-^{(1)}(e_1y_1^2) = e_1e_2 - (1-q)e_3`.** The coefficient extraction of
`HJO.Sweep.dminus_auxVar_pow_mul_C` at `m = 2`, whose value is the Hall--Littlewood
`HJO.Sym.bop_two_elemSymm_one`. -/
theorem dminus_one_C_elemSymm_one_mul_sq (q : L) :
    dminus q 1 (MvPolynomial.C (elemSymm L 1) * (MvPolynomial.X 0 : Total L) ^ 2)
      = MvPolynomial.C (elemSymm L 1 * elemSymm L 2
          - MvPolynomial.C (1 - q) * elemSymm L 3) := by
  have hav : (auxVar 1 : Total L) = MvPolynomial.X 0 := rfl
  rw [show (MvPolynomial.C (elemSymm L 1) * (MvPolynomial.X 0 : Total L) ^ 2)
      = (auxVar 1 : Total L) ^ 2 * MvPolynomial.C (elemSymm L 1) from by rw [hav]; ring]
  have h := dminus_auxVar_pow_mul_C q 0 2 (elemSymm L 1)
  rw [show (0 : ℕ) + 1 = 1 from rfl] at h
  rw [h, bop_two_elemSymm_one]

/-- **`d_-^{(1)}(uy_1^3) = -ue_3`.** The shift `τ^-_{1,1}` fixes a scalar, so only
`HJO.Sweep.dminus_auxVar_pow` is spent. -/
theorem dminus_one_scal_mul_cube (q u : L) :
    dminus q 1 (scal u * (MvPolynomial.X 0 : Total L) ^ 3)
      = -(u • MvPolynomial.C (elemSymm L 3)) := by
  have hav : (auxVar 1 : Total L) = MvPolynomial.X 0 := rfl
  rw [show (scal u * (MvPolynomial.X 0 : Total L) ^ 3) = u • ((auxVar 1 : Total L) ^ 3) from by
      rw [hav, smul_eq_scal_mul], map_smul]
  have h := dminus_auxVar_pow q 0 3
  rw [show (0 : ℕ) + 1 = 1 from rfl] at h
  rw [h, smul_eq_scal_mul, smul_eq_scal_mul]
  ring

/-- **`d_-^{(1)}(e_1y_1^2 - uy_1^3) = e_1e_2 + (q - 1 + u)e_3`**, the lowering of the value
of `HJO.Mellit.dsc_two_three_one`. -/
theorem dminus_one_dsc_two_three_one_value (q u : L) :
    dminus q 1 (MvPolynomial.C (elemSymm L 1) * (MvPolynomial.X 0 : Total L) ^ 2
        - scal u * (MvPolynomial.X 0 : Total L) ^ 3)
      = MvPolynomial.C (elemSymm L 1 * elemSymm L 2
          + MvPolynomial.C (q - 1 + u) * elemSymm L 3) := by
  rw [map_sub, dminus_one_C_elemSymm_one_mul_sq, dminus_one_scal_mul_cube, sub_neg_eq_add,
    smul_C_eq_C_C_mul, ← map_add]
  congr 1
  rw [show (MvPolynomial.C (1 - q) : Lambda L) = 1 - MvPolynomial.C q from by simp,
    show (MvPolynomial.C (q - 1 + u) : Lambda L) = MvPolynomial.C q - 1 + MvPolynomial.C u
      from by simp]
  ring

end Lowering

/-! ### The value, and the verdict -/

section Value

variable {L : Type*} [Field L] [Algebra ℚ L]

/-- **The two-path value at the separating level, re-derived through
`HJO.Mellit.dsc_eq_sum_of_levelTrace_injOn`.** Statement copied from
`HJO.Mellit.dsc_two_three_one`; `HJO.Mellit.dsc_two_three_one_routes_agree` checks the copy. -/
theorem dsc_two_three_one_of_injOn (q u : L) (hq0 : q ≠ 0) (hq1 : q ≠ 1) :
    dsc q u 2 3 1 (sepLevel 2 1) (compColouring 2 3 [1])
      = MvPolynomial.C (Sym.elemSymm L 1) * (MvPolynomial.X 0 : Total L) ^ 2
        - scal u * (MvPolynomial.X 0 : Total L) ^ 3 := by
  rw [dsc_compColouring_eq_sum_partialSweepWord_of_injOn q u (isAdmissibleLevel_sepLevel 2 1)
      (separatesDiagonal_sepLevel' 2 3 1) (by decide) (by omega) (by omega) (by simp) (by simp),
    aboveReturnPaths_two_three_one,
    Finset.sum_insert (by simpa using (by decide : baseTwoThreeA ≠ baseTwoThreeB)),
    Finset.sum_singleton, partialSweepWord_baseTwoThreeA_apply_one q u hq0 hq1,
    partialSweepWord_baseTwoThreeB_apply_one q u hq1]
  ring

/-- **The two routes to the `2 × 3` value at `5/2` state the same thing.** -/
theorem dsc_two_three_one_routes_agree (q u : L) (hq0 : q ≠ 0) (hq1 : q ≠ 1) :
    dsc_two_three_one q u hq0 hq1 = dsc_two_three_one_of_injOn q u hq0 hq1 :=
  rfl

/-- **`D_{η,∅} = e_1e_2 + (q - 1 + u)e_3` at `(a,b) = (2,3)`, `N = 1`, for every `η < 0`.**

The invariant the conditional `HJO.Mellit.dsc_eq_one_of_lt_zero_of_braid_recursions` predicts
to be `1`, computed. Below the level `0` the colouring of every above-diagonal path is empty and the
partial sweep word is the full one, so this is the whole sweep word on the vacuum summed over the
two above-diagonal paths of the rectangle — and it is the image under `d_-^{(1)}` of the known
value `e_1y_1^2 - uy_1^3` at the separating level `5/2`.

Only `q ≠ 0` and `q ≠ 1` are spent, both inherited from `HJO.Mellit.dsc_two_three_one`; there is no
exclusion on `u`, and admissibility of `η` is not needed either — every rational below `0` gives the
same value. -/
theorem dsc_two_three_one_below_zero (q u : L) (hq0 : q ≠ 0) (hq1 : q ≠ 1) {η : ℚ} (hη : η < 0) :
    dsc q u 2 3 1 η (∅ : Finset (ℕ × ℕ))
      = MvPolynomial.C (elemSymm L 1 * elemSymm L 2
          + MvPolynomial.C (q - 1 + u) * elemSymm L 3) := by
  rw [dsc_two_three_one_empty_eq_add q u hη, partialSweepWord_baseTwoThreeA_of_lt_zero q u hη,
    partialSweepWord_baseTwoThreeB_of_lt_zero q u hη]
  simp only [Module.End.mul_apply, Module.End.one_apply]
  rw [partialSweepWord_baseTwoThreeA_apply_one q u hq0 hq1,
    partialSweepWord_baseTwoThreeB_apply_one q u hq1, ← map_add, ← sub_eq_add_neg,
    dminus_one_dsc_two_three_one_value]

/-- **The value below the level `0` is `d_-^{(1)}` of the known value at the separating level.**
The same computation with the arithmetic left undone, so that
`HJO.Mellit.dsc_two_three_one` appears in it unaltered: the only events the sweep adds below `0` are
the identity at the corner and `d_-^{(1)}` at the origin. -/
theorem dsc_two_three_one_below_zero_eq_dminus_dsc_sepLevel (q u : L) (hq0 : q ≠ 0) (hq1 : q ≠ 1)
    {η : ℚ} (hη : η < 0) :
    dsc q u 2 3 1 η (∅ : Finset (ℕ × ℕ))
      = dminus q 1 (dsc q u 2 3 1 (sepLevel 2 1) (compColouring 2 3 [1])) := by
  rw [dsc_two_three_one_empty_eq_add q u hη, partialSweepWord_baseTwoThreeA_of_lt_zero q u hη,
    partialSweepWord_baseTwoThreeB_of_lt_zero q u hη]
  simp only [Module.End.mul_apply, Module.End.one_apply]
  rw [← map_add, dsc_two_three_one q u hq0 hq1,
    partialSweepWord_baseTwoThreeA_apply_one q u hq0 hq1,
    partialSweepWord_baseTwoThreeB_apply_one q u hq1, ← sub_eq_add_neg]

/-! #### The same value through the proved recursion clauses

The computation above never uses the level recursion: it peels the sweep word with
`HJO.Mellit.partialSweepWord_step` and reads the index set off the two-path enumeration. The
recursion clauses `HJO.Mellit.dsc` is *known* to satisfy give a second route to the same identity —
one drop at the corner by the `ACD` clause and one at the origin by the origin clause — and
`HJO.Mellit.dsc_below_zero_routes_agree` checks that the two routes state the same thing. -/

/-- **The bracketing pair at the origin**: the window `(-1/2, 1/2)` isolates the rank `0`. -/
theorem isolates_two_three_one_origin :
    Isolates 2 3 1 0 0 (((-1 : ℤ) : ℚ) + 1 / 2) (((0 : ℤ) : ℚ) + 1 / 2) where
  lo := isAdmissibleLevel_int_add_half (-1)
  hi := isAdmissibleLevel_int_add_half 0
  ltP := by rw [pointRank_origin]; norm_num
  Plt := by rw [pointRank_origin]; norm_num
  iso := iso_of_window (by decide) (pointRank_origin 2 3 1)
  xle := by omega
  yle := by omega

/-- **The bracketing pair at the corner**: the window `(1/2, 5/2)` isolates the rank `2`. -/
theorem isolates_two_three_one_corner :
    Isolates 2 3 1 2 3 (((0 : ℤ) : ℚ) + 1 / 2) (((2 : ℤ) : ℚ) + 1 / 2) where
  lo := isAdmissibleLevel_int_add_half 0
  hi := isAdmissibleLevel_int_add_half 2
  ltP := by rw [pointRank_two_three_corner]; norm_num
  Plt := by rw [pointRank_two_three_corner]; norm_num
  iso := iso_of_window (by decide) pointRank_two_three_corner
  xle := by omega
  yle := by omega

/-- **The `(0,2,3)` path is coloured `c_{(1)}` at the separating level**, its return composition
being `[1]`. -/
theorem colouring_baseTwoThreeA_sepLevel :
    colouring baseTwoThreeA (sepLevel 2 1) = compColouring 2 3 [1] :=
  (colouring_eq_compColouring_iff (isAdmissibleLevel_sepLevel 2 1)
    (separatesDiagonal_sepLevel' 2 3 1) (by decide) (by omega) (by omega) (by simp) (by simp)
    (by decide)).2 hasAboveReturns_baseTwoThreeA

/-- **`D_{-1/2,∅} = d_-^{(1)}(D_{5/2,c_{(1)}})`, through the level recursion.** Two drops of the
proved recursion for `HJO.Mellit.dsc`: the corner `(2,3)` by `HJO.Mellit.dsc_sweepRecursionACD`,
whose event operator there is the identity, and the origin by
`HJO.Mellit.dsc_lo_eq_dminus_dsc_hi_origin`, whose index is the width `1`. Neither `q ≠ 0` nor
`q ≠ 1` is needed: no value is evaluated, only two transitions composed. -/
theorem dsc_two_three_one_below_zero_eq_dminus_dsc_sepLevel_of_recursion (q u : L) :
    dsc q u 2 3 1 (((-1 : ℤ) : ℚ) + 1 / 2) (∅ : Finset (ℕ × ℕ))
      = dminus q 1 (dsc q u 2 3 1 (sepLevel 2 1) (compColouring 2 3 [1])) := by
  have hy : IsAboveDiagonal baseTwoThreeA := by decide
  have hlo : colouring baseTwoThreeA (((-1 : ℤ) : ℚ) + 1 / 2) = (∅ : Finset (ℕ × ℕ)) :=
    colouring_eq_empty_of_lt_zero hy (by norm_num)
  have h1 := dsc_lo_eq_dminus_dsc_hi_origin q u (a := 2) (b := 3) (N := 1)
    (by omega) (by omega) (by omega) isolates_two_three_one_origin hy
  have h2 := dsc_sweepRecursionACD q u (a := 2) (b := 3) (N := 1) (by omega) (by omega) (by omega)
    2 3 _ _ isolates_two_three_one_corner baseTwoThreeA hy (by decide) (by decide)
  rw [hlo] at h1
  rw [h1, show sweepWidth baseTwoThreeA ((0 : ℕ), (0 : ℕ)) = 1 from by decide, h2,
    sweepOperator_two_three_corner q u _ (by decide) (by decide), ← sepLevel_two_one,
    colouring_baseTwoThreeA_sepLevel]
  simp

/-- **The sweep-word route and the recursion route state the same identity.** Both sides are proofs
of one `Prop`, so this typechecks exactly when the two statements coincide. -/
theorem dsc_below_zero_routes_agree (q u : L) (hq0 : q ≠ 0) (hq1 : q ≠ 1) :
    dsc_two_three_one_below_zero_eq_dminus_dsc_sepLevel q u hq0 hq1
        (show ((-1 : ℤ) : ℚ) + 1 / 2 < 0 from by norm_num)
      = dsc_two_three_one_below_zero_eq_dminus_dsc_sepLevel_of_recursion q u :=
  rfl

/-- **The invariant below the level `0` is not the vacuum**, at `(a,b) = (2,3)`, `N = 1`, at every
`η < 0` and for every `q ∉ {0, 1}` and every `u`. This is the falsification: the consequent of
`HJO.Mellit.dsc_eq_one_of_lt_zero_of_braid_recursions` is false at these parameters. -/
theorem dsc_two_three_one_below_zero_ne_one (q u : L) (hq0 : q ≠ 0) (hq1 : q ≠ 1) {η : ℚ}
    (hη : η < 0) : dsc q u 2 3 1 η (∅ : Finset (ℕ × ℕ)) ≠ (1 : Total L) := by
  rw [dsc_two_three_one_below_zero q u hq0 hq1 hη]
  intro h
  rw [← map_one MvPolynomial.C] at h
  exact elemSymm_one_mul_two_add_C_mul_three_ne_one (q - 1 + u) (MvPolynomial.C_injective ℕ _ h)

/-- **The braid candidate is not `HJO.Mellit.dsc` below the level `0`.** The structural half of the
finding, stated without the recursion clauses: the braid candidate is the vacuum at every level
below `0` (`HJO.Mellit.braidValueColouring_eq_one_of_lt_zero`) and
`HJO.Mellit.dsc q u 2 3 1 η ∅ = e_1e_2 + (q - 1 + u)e_3` is not. So
`HJO.Mellit.agreesWithDsc_of_recursions` — whose conclusion is that the candidate *is* `dsc` at
every admissible level and admissible colouring — cannot be applied to
`HJO.Mellit.braidValueColouring` as it stands, and the braid route needs a level restriction. -/
theorem braidValueColouring_ne_dsc_two_three_one (q u : L) {r : L} (hq : q ≠ 0) (hq1 : q ≠ 1)
    (hqp : q + 1 ≠ 0) (hr : r * r = q) {η : ℚ} (hη : η < 0) :
    braidValueColouring q u hq hq1 hqp hr 2 3 1 η (∅ : Finset (ℕ × ℕ))
      ≠ dsc q u 2 3 1 η (∅ : Finset (ℕ × ℕ)) := by
  rw [braidValueColouring_eq_one_of_lt_zero q u hq hq1 hqp hr (by omega) hη]
  exact fun h => dsc_two_three_one_below_zero_ne_one q u hq hq1 hη h.symm

/-- **The `ACD` clause alone fails for the braid candidate, as soon as one number is computed.**

This is the localization the conjunction above leaves open, reduced to a single evaluation. The
origin clause **is** proved for the braid candidate
(`HJO.Mellit.braidValueColouring_sweepRecursionBOrigin`), and it fixes the transition across the
rank `0`: `1 = R(-1/2, ∅) = d_-^{(1)}(R(1/2, c_{1/2}))`. The `ACD` clause at the corner `(2,3)`,
whose event operator is the identity, would then fix the transition across the rank `2` and give
`1 = d_-^{(1)}(R(5/2, c_{(1)}))`. So the `ACD` clause is false at `(a,b,N) = (2,3,1)` as soon as
`d_-^{(1)}` of the braid candidate's value at the separating level is not the vacuum — and for
`HJO.Mellit.dsc` in its place that number is `e_1e_2 + (q - 1 + u)e_3`, not `1`
(`HJO.Mellit.dsc_two_three_one_below_zero`).

**The hypothesis is the missing evaluation, not an obstruction.** What is owed is
`HJO.Mellit.braidValueColouring q u ⋯ 2 3 1 (sepLevel 2 1) (compColouring 2 3 [1])`, i.e.
`HJO.Mellit.braidValueOfData` at the one-letter data of
`HJO.Mellit.braidDataOfColouring 2 3 1 · (5/2) 1`. Nothing here computes it, so nothing here says
which of the three clauses fails; this theorem says exactly what would settle it. -/
theorem not_sweepRecursionACD_of_dminus_braidValueColouring_sepLevel_ne_one (q u : L) {r : L}
    (hq : q ≠ 0) (hq1 : q ≠ 1) (hqp : q + 1 ≠ 0) (hr : r * r = q)
    (h : dminus q 1 (braidValueColouring q u hq hq1 hqp hr 2 3 1 (sepLevel 2 1)
        (compColouring 2 3 [1])) ≠ (1 : Total L)) :
    ¬ SweepRecursionACD q u 2 3 1 (braidValueColouring q u hq hq1 hqp hr 2 3 1) := by
  intro hACD
  have hy : IsAboveDiagonal baseTwoThreeA := by decide
  have hB0 := braidValueColouring_sweepRecursionBOrigin (a := 2) (b := 3) (N := 1) q u hq hq1 hqp hr
    _ _ isolates_two_three_one_origin baseTwoThreeA hy
  rw [colouring_eq_empty_of_lt_zero hy (show ((-1 : ℤ) : ℚ) + 1 / 2 < 0 from by norm_num),
    braidValueColouring_eq_one_of_lt_zero q u hq hq1 hqp hr (by omega)
      (show ((-1 : ℤ) : ℚ) + 1 / 2 < 0 from by norm_num),
    show sweepWidth baseTwoThreeA ((0 : ℕ), (0 : ℕ)) = 1 from by decide,
    hACD 2 3 _ _ isolates_two_three_one_corner baseTwoThreeA hy (by decide) (by decide),
    sweepOperator_two_three_corner q u _ (by decide) (by decide), Module.End.one_apply,
    ← sepLevel_two_one, colouring_baseTwoThreeA_sepLevel] at hB0
  exact h hB0.symm

/-- **The braid candidate does not satisfy the three remaining clauses of the level recursion.**

`HJO.Mellit.dsc_eq_one_of_lt_zero_of_braid_recursions` would force
`HJO.Mellit.dsc q u 2 3 1 (-1/2) ∅ = 1`, and `HJO.Mellit.dsc_two_three_one_below_zero_ne_one` says
it is not. So the conjunction fails, for every `q ∉ {0, 1, -1}` with a square root and every `u`.

**What this is and is not.** `HJO.Mellit.dsc_recursions` proves that `HJO.Mellit.dsc` satisfies all
five properties, so they are consistent and none of them is wrong. The failure is
`HJO.Mellit.braidValueColouring`'s: it is `1` below the level `0`
(`HJO.Mellit.braidValueColouring_eq_one_of_lt_zero`) where `HJO.Mellit.dsc` is not, so the two
functions are different there and `HJO.Mellit.agreesWithDsc_of_recursions` cannot be applied to the
braid candidate as it stands — the braid route needs a level restriction. **Which** of the three
fails is not decided here; the region to look at is the one every proved per-event braid clause
excludes by `aN < ηlo` (types `A`, `C`, `D`) or `0 < ηlo` (the unswept bulk), which none of the
three `Prop`s carries. -/
theorem not_braid_recursions_two_three_one (q u : L) {r : L} (hq : q ≠ 0) (hq1 : q ≠ 1)
    (hqp : q + 1 ≠ 0) (hr : r * r = q) :
    ¬ (SweepRecursionACD q u 2 3 1 (braidValueColouring q u hq hq1 hqp hr 2 3 1) ∧
        SweepRecursionBE q u 2 3 1 (braidValueColouring q u hq hq1 hqp hr 2 3 1) ∧
        SweepRecursionUnswept 2 3 1 (braidValueColouring q u hq hq1 hqp hr 2 3 1)) := by
  rintro ⟨hACD, hBE, hUn⟩
  refine dsc_two_three_one_below_zero_ne_one q u hq hq1
    (show ((-1 : ℤ) : ℚ) + 1 / 2 < 0 from by norm_num) ?_
  exact dsc_eq_one_of_lt_zero_of_braid_recursions q u hq hq1 hqp hr (by omega) (by omega)
    (by omega) hACD hBE hUn ⟨-1, by push_cast; ring⟩ (by norm_num)

end Value

end HJO.Mellit

end
