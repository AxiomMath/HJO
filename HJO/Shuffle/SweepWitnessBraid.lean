/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.Shuffle.SweepWitnessColour
public meta import HJO.Attr

/-! # Two of the three conjuncts of `HJO.Mellit.BraidClosedForm`, at the sweep witness

`HJO.Mellit.BraidClosedForm` — what `HJO.Mellit.MellitInduction` is *equivalent* to, by
`HJO.Mellit.mellitInduction_iff_braidClosedForm` — asks for a replication family `Ω` and a braid
value `B : List ℕ → W` with `HJO.Mellit.IsReplicationFamily`,
`HJO.Mellit.IsBraidValue` and `HJO.Mellit.IsColouringValue`. This file settles, at
`HJO.Mellit.sweepWitness`, everything in that statement except the `append` field of
`HJO.Mellit.IsBraidValue`, which has the shape of `HJO.Mellit.braidRep_specialBraid_dplusIter` and
is not treated here.

## The replication family costs nothing

`HJO.Mellit.replExists` is a theorem about every `HJO.Mellit.SweepSystem`, so
`HJO.Mellit.replExists_sweepWitness` is the first conjunct at the witness with no work at all.

## `B` is forced, and what forces it is that the level drops out

`HJO.Mellit.IsColouringValue S a b B` reads `S.D η (c_α) = B α` for **every** admissible level `η`
separating the diagonal, while `B` takes no level. So the clause *demands* that `D_{η,c_α}` not
depend on `η` across the separating admissible levels, and once that holds `B` has exactly one
possible value, `B α := D_{η₀,c_α}` at any convenient such `η₀`.

At the witness the demand is met, and the reason is already in the sweep combinatorics. By
`HJO.Mellit.dsc_compColouring_eq_sum_partialSweepWord`,
`D_{η,c_α} = ∑_{P̂} W_η(P̂)(1)` over the above-diagonal paths of return composition `α` — an index
set with no `η` in it — and by `HJO.Mellit.sweptAbove_eq_filter` a separating level cuts the swept
region at the diagonal, so `Sw(P̂) ∩ {rk̂ > η}` is `{P ∈ Sw(P̂) : bP_x < aP_y}` whatever the
separating level. Both halves of `W_η(P̂)` are then level-free, which is
`HJO.Mellit.partialSweepWord_congr_of_separatesDiagonal`, and the sum with them:
`HJO.Mellit.dsc_compColouring_congr_level`.

This is **not** `HJO.Mellit.invFin_eq_invIni_of_separatesDiagonal`. That lemma says
`inv_fin(v, α^br) = inv_ini(v, α^br)` for the special-braid data of `c_α`, in the vocabulary of
special braids (Section 5 of A. Mellit, *Toric braids and `(m, n)`-parking functions*,
arXiv:1604.07456) of `HJO.Braid.IsSpecialBraidData`, `HJO.Braid.invIni` and `HJO.Braid.invFin`,
none of which this file uses. What the two share is their *consequence* — that the `q`-power of
`HJO.Mellit.braidValueColouring_eq_dsc_floor` is `1`, hence that `D_{η,c_α}` carries no level — and
it is that consequence, proved here from the sweep combinatorics instead, that makes `B` definable.

`HJO.Mellit.braidValue` is that forced value, taken at `η₀ = aN + 1/2`, which separates the
diagonal at every `N` by `HJO.Mellit.separatesDiagonal_sepLevel'`; `HJO.Mellit.sepLevel a 0` is
`1/2` and the `N = 0` corner is `HJO.Mellit.separatesDiagonal_zero`.

## What is settled

* `HJO.Mellit.replExists_sweepWitness` — the `Ω` conjunct.
* `HJO.Mellit.isColouringValue_sweepWitness` — `HJO.Mellit.IsColouringValue` at the witness, for
  `HJO.Mellit.braidValue`.
* `HJO.Mellit.braidValue_nil` — the `nil` field of `HJO.Mellit.IsBraidValue`, `B(∅) = 1`. This is
  `HJO.Mellit.isAdmissibleColouring_empty_and_dsc_eq_one` in the one corner the clause reads it:
  `c_∅ = ∅`, `N = 0`, and at `N = 0` no point of the swept region lies strictly above the diagonal,
  so `W_η(P̂) = 1` and the sum of `HJO.Mellit.dsc` over the single above-diagonal path of
  `Heights a b 0` is `1` (`HJO.Mellit.dsc_empty_eq_one`).
* `HJO.Mellit.sweepWitness_D_empty_eq_vac` — the corner check: the necessary condition
  `HJO.Mellit.d_empty_eq_vac_of_mellitInduction` extracts from the clause, verified of the witness.

The `append` field is `HJO.Mellit.braidRep_specialBraid_dplusIter` verbatim and is not touched here.

## Corners

Every statement below carries `0 < a`, `0 < b` and `Nat.Coprime a b`, which are the hypotheses of
`HJO.Mellit.dsc_compColouring_eq_sum_partialSweepWord`, and the two identities of
`HJO/Shuffle/SweepWitnessColour.lean` need them too. The composition is asked to have positive
parts exactly where `HJO.Mellit.IsColouringValue` asks it, so `α = [0]` — the composition at which
`HJO.Mellit.colourParts_compColouring_zero_part` shows the witness's `colourParts` convention reads
the wrong grading — is never reached; `α = []` is reached, and is the `nil` corner above. There is
no tension with `HJO.Mellit.dsc_empty_eq_zero`, `D_{η,∅} = 0` at a separating level: that is the
value at `N ≥ 1`, where `∅` is not `c_α` for any composition of `N`, and the `nil` corner is at
`N = 0`.
-/

@[expose] public section

open Finset

namespace HJO.Mellit

open HJO.Sweep Paths

/-! ### The replication family at the witness

The first conjunct of `HJO.Mellit.BraidClosedForm` is free: `HJO.Mellit.replExists` holds of every
`HJO.Mellit.SweepSystem`. -/

variable {L : Type*} [Field L] [Algebra ℚ L]

/-- **A replication family exists at the witness.** The `Ω` of `HJO.Mellit.BraidClosedForm` costs
nothing: `HJO.Mellit.replExists` — `HJO.Mellit.exists_isReplicationFamily`, proved for every
`HJO.Mellit.SweepSystem` in `HJO/Shuffle/Mellit.lean` — applies to
`HJO.Mellit.sweepWitness` as it stands, the family being `HJO.Mellit.replFamily` of that system. -/
theorem replExists_sweepWitness (q u : L) (a b : ℕ) : ReplExists (sweepWitness q u a b) :=
  replExists _

/-! ### A separating level does not reach the partial sweep word

The only place a level enters `HJO.Mellit.partialSweepWord` is the index set
`HJO.Mellit.sweptAbove`, and `HJO.Mellit.sweptAbove_eq_filter` computes that away for a separating
level. -/

variable {a b N : ℕ}

/-- **Two separating levels sweep the same points.** Both sides are
`{P ∈ Sw(P̂) : bP_x < aP_y}` by `HJO.Mellit.sweptAbove_eq_filter`, which is where the separating
property is spent and the only place a level appears. Admissibility of the levels is not needed. -/
theorem sweptAbove_congr_of_separatesDiagonal {η η' : ℚ} (hηs : SeparatesDiagonal a b N η)
    (hη's : SeparatesDiagonal a b N η') (y : Heights a b N) :
    sweptAbove y η = sweptAbove y η' := by
  rw [sweptAbove_eq_filter hηs, sweptAbove_eq_filter hη's]

/-- **The partial sweep word at a separating level does not depend on the level.** The word is the
product of the event operators `HJO.Mellit.sweepOperator` along the rank listing of
`HJO.Mellit.sweptAbove`, and that set is level-free among separating levels. -/
theorem partialSweepWord_congr_of_separatesDiagonal (q u : L) {η η' : ℚ}
    (hηs : SeparatesDiagonal a b N η) (hη's : SeparatesDiagonal a b N η') (y : Heights a b N) :
    partialSweepWord q u y η = partialSweepWord q u y η' := by
  rw [partialSweepWord, partialSweepWord, sweptAbove_congr_of_separatesDiagonal hηs hη's]

/-- **`D_{η,c_α}` does not depend on the separating admissible level.** This is what
`HJO.Mellit.IsColouringValue` demands and what makes its `B` definable: the clause equates
`S.D η (c_α)` with a value carrying no level.

By `HJO.Mellit.dsc_compColouring_eq_sum_partialSweepWord` the invariant is the sum of the partial
sweep words over `HJO.Mellit.aboveReturnPaths`, whose index set has no level in it, and the summands
agree by `HJO.Mellit.partialSweepWord_congr_of_separatesDiagonal`.

The braid-theoretic route reaches the same conclusion through
`HJO.Mellit.braidValueColouring_eq_dsc_floor` and
`HJO.Mellit.invFin_eq_invIni_of_separatesDiagonal`, reading `D_{η,c}` as
`q^{(inv_fin - inv_ini)/2} π_k(B_{s,v,α})d_+^k(1)` and then showing the exponent vanishes at
`c = c_α`; the route here is off the existing combinatorics and needs neither the braid
representation nor the inversion counts. -/
theorem dsc_compColouring_congr_level (q u : L) {η η' : ℚ} (hηa : IsAdmissibleLevel η)
    (hηs : SeparatesDiagonal a b N η) (hη'a : IsAdmissibleLevel η')
    (hη's : SeparatesDiagonal a b N η') (hab : Nat.Coprime a b) (ha : 0 < a) (hb : 0 < b)
    {α : List ℕ} (hpos : ∀ x ∈ α, 0 < x) (hsum : α.sum = N) :
    dsc q u a b N η (compColouring a b α) = dsc q u a b N η' (compColouring a b α) := by
  rw [dsc_compColouring_eq_sum_partialSweepWord q u hηa hηs hab ha hb hpos hsum,
    dsc_compColouring_eq_sum_partialSweepWord q u hη'a hη's hab ha hb hpos hsum]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [partialSweepWord_congr_of_separatesDiagonal q u hηs hη's y]

/-- **The witness's `D` at `c_α` does not depend on the separating admissible level.** The witness
reads the multiplier back off the colouring, and `HJO.Mellit.colourMult_compColouring` says that
reading is `α.sum`, so the level is the only argument left to vary. -/
theorem sweepWitness_D_compColouring_congr_level (q u : L) {a b : ℕ} (hab : Nat.Coprime a b)
    (ha : 0 < a) (hb : 0 < b) {α : List ℕ} (hpos : ∀ x ∈ α, 0 < x) {η η' : ℚ}
    (hηa : IsAdmissibleLevel η) (hηs : SeparatesDiagonal a b α.sum η)
    (hη'a : IsAdmissibleLevel η') (hη's : SeparatesDiagonal a b α.sum η') :
    (sweepWitness q u a b).D η (compColouring a b α)
      = (sweepWitness q u a b).D η' (compColouring a b α) := by
  change gradedIn L (colourParts (compColouring a b α))
      (dsc q u a b (colourMult b (compColouring a b α)) η (compColouring a b α))
    = gradedIn L (colourParts (compColouring a b α))
      (dsc q u a b (colourMult b (compColouring a b α)) η' (compColouring a b α))
  rw [colourMult_compColouring hb,
    dsc_compColouring_congr_level q u hηa hηs hη'a hη's hab ha hb hpos rfl]

/-! ### The level the braid value is read at

`HJO.Mellit.separatesDiagonal_sepLevel` takes `0 < N`, and the empty composition is a live instance
of `HJO.Mellit.IsColouringValue`. At `N = 0` the level `aN + 1/2` is `1/2`, where
`HJO.Mellit.separatesDiagonal_zero` applies. -/

/-- **`η = aN + 1/2` separates the diagonal at every `N`.** For `N ≥ 1` this is
`HJO.Mellit.separatesDiagonal_sepLevel`; at `N = 0` the level is `1/2` and the only lattice point
in range is the origin, which is `HJO.Mellit.separatesDiagonal_zero`. -/
theorem separatesDiagonal_sepLevel' (a b N : ℕ) : SeparatesDiagonal a b N (sepLevel a N) := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · have h : sepLevel a 0 = 1 / 2 := by simp [sepLevel]
    rw [h]
    exact separatesDiagonal_zero a b
  · exact separatesDiagonal_sepLevel hN

/-! ### The `nil` corner

`c_∅ = ∅` and `N = 0`, so the `nil` field of `HJO.Mellit.IsBraidValue` at the witness is the value
of `HJO.Mellit.dsc` at the empty colouring of a `0 × 0` rectangle. It is `1`, as in
`HJO.Mellit.isAdmissibleColouring_empty_and_dsc_eq_one`: at `N = 0` no point of the swept region
lies strictly above the diagonal, so a separating level leaves no factor in the partial sweep word,
and `Heights a b 0` has one element. -/

/-- **`D_{η,∅} = 1` at `N = 0`.** `HJO.Mellit.isAdmissibleColouring_empty_and_dsc_eq_one` in the one
corner the interface reads it. The path space `HJO.Paths.Heights a b 0` is a subsingleton — every
height is at most `b · 0` — its single element is above-diagonal with return composition `∅`, and
its swept region is the origin alone, which a separating level does not reach since `b · 0 < a · 0`
is false. So the sum of `HJO.Mellit.dsc` has one term and that term is the empty product.

This is the `N = 0` companion of `HJO.Mellit.dsc_empty_eq_zero`, which gives the value `0` at the
same colouring for `N ≥ 1`. The two are not in tension: at `N ≥ 1` the north step at the origin is
always crossed, so `∅` is admissible at no separating level, while at `N = 0` there is nothing to
cross. -/
theorem dsc_empty_eq_one (q u : L) {a b : ℕ} {η : ℚ} (hηa : IsAdmissibleLevel η)
    (hηs : SeparatesDiagonal a b 0 η) (hab : Nat.Coprime a b) (ha : 0 < a) (hb : 0 < b) :
    dsc q u a b 0 η (∅ : Finset (ℕ × ℕ)) = (1 : Total L) := by
  have hc : compColouring a b ([] : List ℕ) = (∅ : Finset (ℕ × ℕ)) := by simp [compColouring]
  have hzero : ∀ y : Heights a b 0, partialSweepWord q u y η (1 : Total L) = 1 := by
    intro y
    have hemp : sweptAbove y η = ∅ := by
      rw [sweptAbove_eq_filter hηs]
      refine Finset.filter_eq_empty_iff.2 fun {P} hP => ?_
      rw [mem_sweptRegion] at hP
      have hy := ht_le_mul y (P.1 + 1)
      have hp1 : P.1 = 0 := by omega
      have hp2 : P.2 = 0 := by omega
      simp [hp1, hp2]
    rw [partialSweepWord, hemp, sortByRank_empty, List.map_nil, List.prod_nil]
    rfl
  have hsub : ∀ y₁ y₂ : Heights a b 0, y₁ = y₂ := fun y₁ y₂ =>
    heights_ext fun r _ => by
      have h1 := ht_le_mul y₁ r
      have h2 := ht_le_mul y₂ r
      omega
  have hall : ∀ y : Heights a b 0, y ∈ aboveReturnPaths a b 0 ([] : List ℕ) := by
    intro y
    have h0 : ∀ r, ht y r = 0 := fun r => by have := ht_le_mul y r; omega
    have habove : IsAboveDiagonal y := by
      refine ⟨h0 0, by rw [h0]; omega, fun r hr => by omega, fun r hr => ?_⟩
      have hr0 : r = 0 := by omega
      subst hr0
      rw [h0]
      omega
    rw [aboveReturnPaths, Finset.mem_filter]
    refine ⟨Finset.mem_univ _, habove, habove, List.forall_mem_nil _, rfl, fun k hk => ?_⟩
    have hk0 : k = 0 := by omega
    subst hk0
    simp [h0]
  have hcard : (aboveReturnPaths a b 0 ([] : List ℕ)).card = 1 :=
    Finset.card_eq_one.2 ⟨(fun _ => 0 : Heights a b 0),
      Finset.eq_singleton_iff_unique_mem.2 ⟨hall _, fun y _ => hsub y _⟩⟩
  rw [← hc, dsc_compColouring_eq_sum_partialSweepWord q u hηa hηs hab ha hb
    (List.forall_mem_nil _) rfl, Finset.sum_congr rfl fun y _ => hzero y, Finset.sum_const,
    hcard, one_smul]

/-! ### The braid value at the witness -/

/-- **The braid value the clause forces at the witness.** `HJO.Mellit.IsColouringValue` equates
`S.D η (c_α)` with `B α` at every admissible level separating the diagonal, so `B` has exactly one
possible value; this is it, read at `η = a·α.sum + 1/2`, which separates the diagonal at every sum
by `HJO.Mellit.separatesDiagonal_sepLevel'`.

The choice of level is immaterial by `HJO.Mellit.sweepWitness_D_compColouring_congr_level`, which is
also what makes this a *correct* choice rather than merely a definable one. -/
noncomputable def braidValue (q u : L) (a b : ℕ) (α : List ℕ) : (sweepWitness q u a b).W :=
  (sweepWitness q u a b).D (sepLevel a α.sum) (compColouring a b α)

/-- **`HJO.Mellit.IsColouringValue` holds of the witness.** The third conjunct of
`HJO.Mellit.BraidClosedForm`, for `HJO.Mellit.braidValue`. Nothing is asked of the level beyond
what the clause asks, and nothing of `q` or `u` at all: the level drops out of
`HJO.Mellit.dsc` at `c_α` by `HJO.Mellit.dsc_compColouring_congr_level`, so the clause's
`η`-indexed family of demands is one demand, and `HJO.Mellit.braidValue` meets it by
construction. -/
theorem isColouringValue_sweepWitness (q u : L) {a b : ℕ} (hab : Nat.Coprime a b) (ha : 0 < a)
    (hb : 0 < b) : IsColouringValue (sweepWitness q u a b) a b (braidValue q u a b) := by
  intro N η hηa hηs α hpos hsum
  subst hsum
  exact sweepWitness_D_compColouring_congr_level q u hab ha hb hpos hηa hηs
    (isAdmissibleLevel_sepLevel a α.sum) (separatesDiagonal_sepLevel' a b α.sum)

/-- **The `nil` field of `HJO.Mellit.IsBraidValue` holds of `HJO.Mellit.braidValue`.**
`B(∅) = 1`: the empty composition has `c_∅ = ∅` and sum `0`, the witness's `HJO.Mellit.colourParts`
puts the value in the grading `0`, and `HJO.Mellit.dsc_empty_eq_one` reads it as the vacuum. -/
theorem braidValue_nil (q u : L) {a b : ℕ} (hab : Nat.Coprime a b) (ha : 0 < a) (hb : 0 < b) :
    braidValue q u a b ([] : List ℕ) = (sweepWitness q u a b).vac := by
  have hc : compColouring a b ([] : List ℕ) = (∅ : Finset (ℕ × ℕ)) := by simp [compColouring]
  have hp : colourParts (∅ : Finset (ℕ × ℕ)) = 0 := by simp [colourParts]
  have hm : colourMult b (∅ : Finset (ℕ × ℕ)) = 0 := by simp [colourMult]
  have hval : dsc q u a b 0 (sepLevel a 0) (∅ : Finset (ℕ × ℕ)) = (1 : Total L) :=
    dsc_empty_eq_one q u (isAdmissibleLevel_sepLevel a 0) (separatesDiagonal_sepLevel' a b 0)
      hab ha hb
  change gradedIn L (colourParts (compColouring a b ([] : List ℕ)))
      (dsc q u a b (colourMult b (compColouring a b ([] : List ℕ))) (sepLevel a 0)
        (compColouring a b ([] : List ℕ)))
    = gradedIn L 0 1
  rw [hc, hp, hm, hval]

/-! ### Corner check -/

/-- **The witness passes the one test the clause can be failed on at the empty composition.**
`HJO.Mellit.d_empty_eq_vac_of_mellitInduction` extracts from `HJO.Mellit.MellitInduction` the
necessary condition `D_{1/2,∅} = 1`, and observes that a sweep system with `D = 0` and `vac ≠ 0`
refutes the clause outright. The witness satisfies it: `HJO.Mellit.sepLevel a 0` is `1/2` and
`HJO.Mellit.braidValue_nil` is that value.

This is the check that `HJO.Mellit.isColouringValue_sweepWitness` is not discharging a demand that
`HJO.Mellit.IsBraidValue` would then contradict — the two clauses meet at `α = []`, where one asks
`B(∅) = D_{η,∅}` and the other asks `B(∅) = 1`. -/
theorem sweepWitness_D_empty_eq_vac (q u : L) {a b : ℕ} (hab : Nat.Coprime a b) (ha : 0 < a)
    (hb : 0 < b) :
    (sweepWitness q u a b).D (1 / 2) (∅ : Finset (ℕ × ℕ)) = (sweepWitness q u a b).vac := by
  have h : sepLevel a 0 = 1 / 2 := by simp [sepLevel]
  have hc : compColouring a b ([] : List ℕ) = (∅ : Finset (ℕ × ℕ)) := by simp [compColouring]
  rw [← h, ← hc]
  exact braidValue_nil q u hab ha hb

end HJO.Mellit
