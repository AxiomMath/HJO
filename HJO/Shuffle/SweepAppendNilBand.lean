/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.Shuffle.SweepAppendNilDegenerate

/-! # The band factorisation DOES reach `α = []`: the `hzero` clause is the band clause at `N = 0`

`HJO.Mellit.sweepAppend_of_forall_band` asks for two hypotheses, and its docstring says of the first
that it "is the raw per-path identity at the one composition with `α.sum = 0`, namely `α = []`,
**which the band factorisation cannot reach** because `HJO.Paths.sweepWidth_appendHeights` needs
`0 < N`". That is true of the *route* through the width shift and false of the *statement*: at
`N = 0` the band is the whole rectangle and the outer word is the identity for a reason that needs
no path geometry at all.

## Why

The threshold of the factorisation is `d = a·bA`, and every point of the swept region of a path in
the `aM × bM` rectangle has diagonal excess `ay - bx ≤ a·bM`
(`HJO.Mellit.diagExcess_le_of_mem_sweptRegion` — the `y ≤ bM` of `HJO.Paths.sweptRegion` and
`bx ≥ 0`, nothing else). So as soon as `M ≤ A` the filter `d < diagExcess` is empty:

* `HJO.Mellit.outerSweepWord_eq_one_of_le` — the outer word is `1`;
* `HJO.Mellit.bandSweepWord_eq_partialSweepWord_of_le` — the band word is the whole partial word.

At `α.sum = 0` this applies on both sides at once: to the base path `z`, where `M = 0`, and to the
extension `appendHeights z w`, where `M = 0 + A = A`. So the band clause and the raw clause are the
*same sentence*, and `HJO.Mellit.hzero_of_band_nil` derives the second from the first with no
genericity, no coprimality and no hypothesis on `a` or `b`.

**Consequence.** `HJO.Mellit.sweepAppend_of_forall_band_uniform` obtains
`HJO.Mellit.SweepAppend` from the band identity **alone**, quantified over every `α` with positive
parts including `α = []`. There is no second obligation. A proof of the band identity uniformly
in `N ≥ 0` gives `HJO.Mellit.SweepAppend`, and the `0 < α.sum` of
`HJO.Mellit.sweepAppend_of_forall_band`'s second hypothesis is a restriction that can be
dropped.

This does **not** make the `α = []` case easier. At `N = 0` the band identity reads
`∑_w W(w)(1) = (-1)^{(a-1)A}(qu)^{1-A} G_{1,A}(1)` over the rational Catalan set
`HJO.Mellit.aboveReturnPaths a b A (A)`, which is exactly `HJO.Mellit.mellitInduction_sweepWitness`
at `ℓ = 1` — the base step of that induction, with
`HJO.Mellit.isAdmissibleColouring_empty_and_dsc_eq_one` (`HJO.Mellit.dsc_empty_eq_one`) as its
`ℓ = 0`. What is removed is the belief that it is a *different kind* of statement from the step.

## The `dsc` form is an equivalence, not just a consequence

`HJO.Mellit.dsc_singleton_of_hzero` reads the `hzero` clause as one equation per `A`. The converse
holds too — `HJO.Mellit.hzero_of_dsc_singleton` — because at `N = 0` the base index set is a
singleton (`HJO.Mellit.aboveReturnPaths_zero_nil_eq_singleton`: a height vector of `Heights a b 0`
is determined, all its heights being `≤ b·0`) and the base word is the identity
(`HJO.Mellit.partialSweepWord_zero_eq_one`: the only swept point is the origin, of rank `0 < 1/2`).
So `HJO.Mellit.hzero_iff_dsc_singleton` makes

`D_{aA+1/2, c_{(A)}} = (-1)^{(a-1)A}(qu)^{1-A} G_{1,A}(1)`, one equation per `A`,

a *working form* of the clause rather than a necessary condition extracted from it: a proof of it
gives `hzero` back.

## References

This file concerns `HJO.Mellit.mellitInduction_sweepWitness`,
`HJO.Mellit.braidRep_specialBraid_dplusIter`, `HJO.Paths.sweptRegion`, `HJO.Mellit.stage`,
`HJO.Mellit.isAdmissibleColouring_empty_and_dsc_eq_one`. Transcribing A. Mellit, *Toric braids and
`(m, n)`-parking functions*, sections 4 and 6.
-/

@[expose] public section

namespace HJO.Mellit

open HJO.Sweep HJO.Sym HJO.Paths Finset

variable {L : Type*} [Field L] [Algebra ℚ L] {q u : L} {a b M : ℕ}

/-! ### The band exhausts the rectangle once the threshold reaches `a·bM` -/

/-- **A swept point lies under the top of the rectangle.** The `y ≤ bM` clause of
`HJO.Paths.sweptRegion`, read off `HJO.Paths.sweptRegion`'s own `Iic (b * M)` factor. -/
theorem snd_le_of_mem_sweptRegion {y : Heights a b M} {P : ℕ × ℕ} (hP : P ∈ sweptRegion y) :
    P.2 ≤ b * M := by
  simp only [sweptRegion, Finset.mem_filter, Finset.mem_product, Finset.mem_Iic] at hP
  exact hP.1.2

/-- **The diagonal excess of a swept point is at most `a·bM`.** `ay ≤ a·bM` because `y ≤ bM`, and
`bx ≥ 0`. Nothing about the path, the level or the above-diagonal condition enters: this is the
bounding box of `HJO.Paths.sweptRegion`.

This is the inequality that makes the threshold `a·bA` of
`HJO.Mellit.partialSweepWord_eq_bandSweepWord_mul` vacuous at `M ≤ A`, and hence the reason the
`α = []` clause of `HJO.Mellit.sweepAppend_of_forall_band` is its band clause. -/
theorem diagExcess_le_of_mem_sweptRegion {y : Heights a b M} {P : ℕ × ℕ}
    (hP : P ∈ sweptRegion y) : diagExcess a b P ≤ (a : ℤ) * (b * M) := by
  have h2 : (P.2 : ℤ) ≤ (b : ℤ) * M := by
    have := snd_le_of_mem_sweptRegion hP
    exact_mod_cast this
  have ha0 : (0 : ℤ) ≤ (a : ℤ) := Int.natCast_nonneg a
  have hmul : (a : ℤ) * P.2 ≤ (a : ℤ) * ((b : ℤ) * M) := mul_le_mul_of_nonneg_left h2 ha0
  have hb1 : (0 : ℤ) ≤ (b : ℤ) * P.1 := by positivity
  rw [diagExcess]
  linarith

/-- **Above a threshold of `a·bM` or more there is nothing to sweep**, so the outer word of
`HJO.Mellit.partialSweepWord_eq_bandSweepWord_mul` is the identity. -/
theorem outerSweepWord_eq_one_of_le (q u : L) (y : Heights a b M) (η : ℚ) {d : ℤ}
    (hd : (a : ℤ) * (b * M) ≤ d) : outerSweepWord q u y η d = 1 := by
  have hempty : {P ∈ sweptAbove y η | d < diagExcess a b P} = (∅ : Finset (ℕ × ℕ)) :=
    Finset.filter_eq_empty_iff.2 fun {P} hP =>
      not_lt.2 ((diagExcess_le_of_mem_sweptRegion (Finset.mem_filter.1 hP).1).trans hd)
  rw [outerSweepWord, hempty, sortByRank_empty, List.map_nil, List.prod_nil]

/-- **Below a threshold of `a·bM` or more everything is swept**, so the band word of
`HJO.Mellit.partialSweepWord_eq_bandSweepWord_mul` is the whole partial word. Note that no `0 < M`
is needed — the factorisation lemma's hypothesis is about splitting the rank listing in two, and
here one of the two halves is empty. -/
theorem bandSweepWord_eq_partialSweepWord_of_le (q u : L) (y : Heights a b M) (η : ℚ) {d : ℤ}
    (hd : (a : ℤ) * (b * M) ≤ d) : bandSweepWord q u y η d = partialSweepWord q u y η := by
  have hall : {P ∈ sweptAbove y η | diagExcess a b P ≤ d} = sweptAbove y η :=
    Finset.filter_true_of_mem fun {P} hP =>
      (diagExcess_le_of_mem_sweptRegion (Finset.mem_filter.1 hP).1).trans hd
  rw [bandSweepWord, hall, partialSweepWord]

/-! ### The `α = []` clause is the band clause at `N = 0` -/

/-- **`HJO.Mellit.sweepAppend_of_forall_band`'s `hzero` follows from its `hband` extended to
`α.sum = 0`.** At `α.sum = 0` the outer word of the base is the identity and both band words are
whole partial words, by `HJO.Mellit.outerSweepWord_eq_one_of_le` and
`HJO.Mellit.bandSweepWord_eq_partialSweepWord_of_le` at `M = 0` and at `M = 0 + A`. So the two
clauses are the same sentence read twice.

No coprimality, no positivity of `a` or `b`, and no genericity in `q` or `u`: the only input is that
the rectangle of a `0`-part path is a point and the rectangle of an `A`-part extension has excess at
most `a·bA`. -/
theorem hzero_of_band_nil
    (hband : ∀ (α : List ℕ) (A : ℕ), (∀ x ∈ α, 0 < x) → 0 < A →
      ∀ z ∈ aboveReturnPaths a b α.sum α,
        ∑ w ∈ aboveReturnPaths a b A [A],
            bandSweepWord q u (appendHeights z w) (sepLevel a (α.sum + A)) ((a : ℤ) * (b * A))
              (outerSweepWord q u z (sepLevel a α.sum) ((a : ℤ) * (b * A)) (1 : Total L))
          = ((-1 : L) ^ ((a - 1) * A) * (q * u) ^ (1 - (A : ℤ))) •
              stageTotal q u a b α.length A
                (bandSweepWord q u z (sepLevel a α.sum) ((a : ℤ) * (b * A))
                  (outerSweepWord q u z (sepLevel a α.sum) ((a : ℤ) * (b * A)) (1 : Total L)))) :
    ∀ (α : List ℕ) (A : ℕ), (∀ x ∈ α, 0 < x) → 0 < A → α.sum = 0 →
      ∀ z ∈ aboveReturnPaths a b α.sum α,
        ∑ w ∈ aboveReturnPaths a b A [A],
            partialSweepWord q u (appendHeights z w) (sepLevel a (α.sum + A)) (1 : Total L)
          = ((-1 : L) ^ ((a - 1) * A) * (q * u) ^ (1 - (A : ℤ))) •
              stageTotal q u a b α.length A
                (partialSweepWord q u z (sepLevel a α.sum) (1 : Total L)) := by
  intro α A hpos hA hs z hz
  have hbase : (a : ℤ) * (b * α.sum) ≤ (a : ℤ) * (b * A) := by
    rw [hs]
    push_cast
    positivity
  have hext : (a : ℤ) * (b * (α.sum + A)) ≤ (a : ℤ) * (b * A) :=
    le_of_eq (by rw [hs]; push_cast; ring)
  have houter : outerSweepWord q u z (sepLevel a α.sum) ((a : ℤ) * (b * A)) = 1 :=
    outerSweepWord_eq_one_of_le q u z _ hbase
  have hbz : bandSweepWord q u z (sepLevel a α.sum) ((a : ℤ) * (b * A))
      = partialSweepWord q u z (sepLevel a α.sum) :=
    bandSweepWord_eq_partialSweepWord_of_le q u z _ hbase
  have hsum : ∑ w ∈ aboveReturnPaths a b A [A],
        bandSweepWord q u (appendHeights z w) (sepLevel a (α.sum + A)) ((a : ℤ) * (b * A))
          (1 : Total L)
      = ∑ w ∈ aboveReturnPaths a b A [A],
        partialSweepWord q u (appendHeights z w) (sepLevel a (α.sum + A)) (1 : Total L) :=
    Finset.sum_congr rfl fun w _ => by
      rw [bandSweepWord_eq_partialSweepWord_of_le q u (appendHeights z w)
        (sepLevel a (α.sum + A)) hext]
  have h := hband α A hpos hA z hz
  rw [houter] at h
  simp only [Module.End.one_apply] at h
  rw [hbz, hsum] at h
  exact h

/-- **`HJO.Mellit.SweepAppend` from the band identity alone.** The strengthening of
`HJO.Mellit.sweepAppend_of_forall_band` that `HJO.Mellit.hzero_of_band_nil` buys: one hypothesis
instead of two, quantified over every composition with positive parts — `α = []` included — and with
no `0 < α.sum`.

So the residual content of `HJO.Mellit.SweepAppend` is a single family of identities, not a family
plus a degenerate case, and the `α = []` clause is not an extra obligation. -/
theorem sweepAppend_of_forall_band_uniform {a b : ℕ} (hab : Nat.Coprime a b) (ha : 0 < a)
    (hb : 0 < b)
    (hband : ∀ (α : List ℕ) (A : ℕ), (∀ x ∈ α, 0 < x) → 0 < A →
      ∀ z ∈ aboveReturnPaths a b α.sum α,
        ∑ w ∈ aboveReturnPaths a b A [A],
            bandSweepWord q u (appendHeights z w) (sepLevel a (α.sum + A)) ((a : ℤ) * (b * A))
              (outerSweepWord q u z (sepLevel a α.sum) ((a : ℤ) * (b * A)) (1 : Total L))
          = ((-1 : L) ^ ((a - 1) * A) * (q * u) ^ (1 - (A : ℤ))) •
              stageTotal q u a b α.length A
                (bandSweepWord q u z (sepLevel a α.sum) ((a : ℤ) * (b * A))
                  (outerSweepWord q u z (sepLevel a α.sum) ((a : ℤ) * (b * A)) (1 : Total L)))) :
    SweepAppend q u a b :=
  sweepAppend_of_forall_band hab ha hb (hzero_of_band_nil hband)
    fun α A hpos hA _ => hband α A hpos hA

/-! ### The `dsc` form of the clause is an equivalence -/

/-- **A height vector of the `0 × 0` rectangle is determined.** Every height is at most
`b·0 = 0`. -/
theorem eq_of_heights_zero (y₁ y₂ : Heights a b 0) : y₁ = y₂ :=
  heights_ext fun r _ => by
    have h1 := HJO.RankOneDinv.ht_le_mul y₁ r
    have h2 := HJO.RankOneDinv.ht_le_mul y₂ r
    omega

/-- **The base index set of the `α = []` clause is the singleton containing any of its members.**
With `HJO.Mellit.eq_of_heights_zero` there is nothing to choose. -/
theorem aboveReturnPaths_zero_nil_eq_singleton {z : Heights a b 0}
    (hz : z ∈ aboveReturnPaths a b 0 ([] : List ℕ)) :
    aboveReturnPaths a b 0 ([] : List ℕ) = {z} :=
  Finset.eq_singleton_iff_unique_mem.2 ⟨hz, fun y _ => eq_of_heights_zero y z⟩

/-- **The partial sweep word of a `0`-part path at `η = 1/2` is the identity.** Its swept region is
the single point `(0,0)`, whose above-diagonal rank is `0`, and `sepLevel a 0 = 1/2`. This is
`HJO.Mellit.isAdmissibleColouring_empty_and_dsc_eq_one` one path at a time, and it is what makes the
base side of the `α = []` clause the bare vacuum. -/
theorem partialSweepWord_zero_eq_one (q u : L) (z : Heights a b 0) :
    partialSweepWord q u z (sepLevel a 0) = 1 := by
  refine partialSweepWord_of_forall_le q u z _ fun P hP => ?_
  rw [mem_sweptRegion] at hP
  have hy := HJO.RankOneDinv.ht_le_mul z (P.1 + 1)
  have h1 : P.1 = 0 := by omega
  have h2 : P.2 = 0 := by omega
  rw [pointRank, h1, h2]
  simp only [ParkingFunctions.abovePointRank, sepLevel]
  norm_num

/-- **The `dsc` form of the `α = []` clause, at one base path and one `A`, implies the clause.**
The left-hand sum over the tails is the whole sum over
`HJO.Mellit.aboveReturnPaths a b (0 + A) ([] ++ (A))`, because the fibres of the truncation are all
the same set (`HJO.Mellit.sum_aboveReturnPaths_append_singleton`) and the base index set is a
singleton (`HJO.Mellit.aboveReturnPaths_zero_nil_eq_singleton`); and the base word on the right is
the identity (`HJO.Mellit.partialSweepWord_zero_eq_one`). -/
theorem hzero_nil_of_dsc_singleton (hab : Nat.Coprime a b) (ha : 0 < a) (hb : 0 < b)
    {z : Heights a b 0} (hz : z ∈ aboveReturnPaths a b 0 ([] : List ℕ)) {A : ℕ} (hA : 0 < A)
    (h : dsc q u a b (0 + A) (sepLevel a (0 + A)) (compColouring a b (([] : List ℕ) ++ [A]))
        = ((-1 : L) ^ ((a - 1) * A) * (q * u) ^ (1 - (A : ℤ))) •
            stageTotal q u a b 0 A (1 : Total L)) :
    ∑ w ∈ aboveReturnPaths a b A [A],
        partialSweepWord q u (appendHeights z w) (sepLevel a (0 + A)) (1 : Total L)
      = ((-1 : L) ^ ((a - 1) * A) * (q * u) ^ (1 - (A : ℤ))) •
          stageTotal q u a b 0 A (partialSweepWord q u z (sepLevel a 0) (1 : Total L)) := by
  have hsplit := sum_aboveReturnPaths_append_singleton (a := a) (b := b) (N := 0) (A := A)
    (α := ([] : List ℕ))
    (f := fun y => partialSweepWord q u y (sepLevel a (0 + A)) (1 : Total L))
  rw [aboveReturnPaths_zero_nil_eq_singleton hz, Finset.sum_singleton] at hsplit
  rw [partialSweepWord_zero_eq_one q u z, Module.End.one_apply, ← h,
    dsc_compColouring_eq_sum_partialSweepWord q u (isAdmissibleLevel_sepLevel a (0 + A))
      (separatesDiagonal_sepLevel' a b (0 + A)) hab ha hb (by simpa using hA) (by simp), hsplit]

/-- **The `dsc` form of the `hzero` clause implies it back.** The converse of
`HJO.Mellit.dsc_singleton_of_hzero`, and what makes that reading a working form rather than a
necessary condition: the left-hand sum over the tails is the whole sum over
`HJO.Mellit.aboveReturnPaths a b (0 + A) ([] ++ (A))` because the base index set is a singleton
(`HJO.Mellit.aboveReturnPaths_zero_nil_eq_singleton`), and the base word on the right is the
identity (`HJO.Mellit.partialSweepWord_zero_eq_one`).

`α` is forced to be `[]` by `α.sum = 0` with positive parts, so `α.length = 0` and nothing about the
shape of `α` is lost. -/
theorem hzero_of_dsc_singleton (hab : Nat.Coprime a b) (ha : 0 < a) (hb : 0 < b)
    (h : ∀ A : ℕ, 0 < A →
      dsc q u a b (0 + A) (sepLevel a (0 + A)) (compColouring a b (([] : List ℕ) ++ [A]))
        = ((-1 : L) ^ ((a - 1) * A) * (q * u) ^ (1 - (A : ℤ))) •
            stageTotal q u a b 0 A (1 : Total L)) :
    ∀ (α : List ℕ) (A : ℕ), (∀ x ∈ α, 0 < x) → 0 < A → α.sum = 0 →
      ∀ z ∈ aboveReturnPaths a b α.sum α,
        ∑ w ∈ aboveReturnPaths a b A [A],
            partialSweepWord q u (appendHeights z w) (sepLevel a (α.sum + A)) (1 : Total L)
          = ((-1 : L) ^ ((a - 1) * A) * (q * u) ^ (1 - (A : ℤ))) •
              stageTotal q u a b α.length A
                (partialSweepWord q u z (sepLevel a α.sum) (1 : Total L)) := by
  intro α A hpos hA hs z hz
  have hnil : α = ([] : List ℕ) := by
    match α with
    | [] => rfl
    | x :: t =>
      exact absurd hs (by
        have hx : 0 < x := hpos x (List.mem_cons_self ..)
        simp only [List.sum_cons]
        omega)
  subst hnil
  exact hzero_nil_of_dsc_singleton hab ha hb hz hA (h A hA)

/-- **The `hzero` clause of `HJO.Mellit.sweepAppend_of_forall_band` IS one equation per `A`.** Both
directions: `HJO.Mellit.dsc_singleton_of_hzero` forward and `HJO.Mellit.hzero_of_dsc_singleton`
back. The right-hand side is `HJO.Mellit.mellitInduction_sweepWitness` at `ℓ = 1`,
`D_{aA+1/2, c_{(A)}} = (-1)^{(a-1)A}(qu)^{1-A} G_{1,A}(1)`, and this says the per-path clause
carries no more information than it. -/
theorem hzero_iff_dsc_singleton (hab : Nat.Coprime a b) (ha : 0 < a) (hb : 0 < b) :
    (∀ (α : List ℕ) (A : ℕ), (∀ x ∈ α, 0 < x) → 0 < A → α.sum = 0 →
        ∀ z ∈ aboveReturnPaths a b α.sum α,
          ∑ w ∈ aboveReturnPaths a b A [A],
              partialSweepWord q u (appendHeights z w) (sepLevel a (α.sum + A)) (1 : Total L)
            = ((-1 : L) ^ ((a - 1) * A) * (q * u) ^ (1 - (A : ℤ))) •
                stageTotal q u a b α.length A
                  (partialSweepWord q u z (sepLevel a α.sum) (1 : Total L)))
      ↔ ∀ A : ℕ, 0 < A →
          dsc q u a b (0 + A) (sepLevel a (0 + A)) (compColouring a b (([] : List ℕ) ++ [A]))
            = ((-1 : L) ^ ((a - 1) * A) * (q * u) ^ (1 - (A : ℤ))) •
                stageTotal q u a b 0 A (1 : Total L) :=
  ⟨fun hzero _A hA => dsc_singleton_of_hzero hab ha hb hzero hA,
    hzero_of_dsc_singleton hab ha hb⟩

/-! ### The uniform band hypothesis is refuted exactly where `hzero` is

These two are the check that `HJO.Mellit.hzero_of_band_nil` lands on the `hzero` clause **verbatim**
rather than on something of the same shape: they are the composite of it with the refutations
`HJO.Mellit.not_hzero_one_two_of_q_zero` and `HJO.Mellit.not_hzero_one_two_of_u_zero`, and they
typecheck only if the two statements are literally the same sentence. So the genericity the uniform
band hypothesis must spend is the same genericity `hzero` must spend, and no more is hidden in the
band reading: `q ≠ 0` and `u ≠ 0` are real exclusions there too, at `a = 1`, from `A = 2` on. -/

/-- **The uniform band hypothesis is FALSE at `q = 0`, `(a,b) = (1,2)`, for every `u ≠ 0`.** Its
`α = []`, `A = 2` clause is `HJO.Mellit.not_hzero_one_two_of_q_zero` through
`HJO.Mellit.hzero_of_band_nil`. -/
theorem not_band_uniform_one_two_of_q_zero (u : L) (hu : u ≠ 0) :
    ¬ (∀ (α : List ℕ) (A : ℕ), (∀ x ∈ α, 0 < x) → 0 < A →
        ∀ z ∈ aboveReturnPaths 1 2 α.sum α,
          ∑ w ∈ aboveReturnPaths 1 2 A [A],
              bandSweepWord (0 : L) u (appendHeights z w) (sepLevel 1 (α.sum + A))
                  ((1 : ℤ) * (2 * A))
                (outerSweepWord (0 : L) u z (sepLevel 1 α.sum) ((1 : ℤ) * (2 * A)) (1 : Total L))
            = ((-1 : L) ^ ((1 - 1) * A) * ((0 : L) * u) ^ (1 - (A : ℤ))) •
                stageTotal (0 : L) u 1 2 α.length A
                  (bandSweepWord (0 : L) u z (sepLevel 1 α.sum) ((1 : ℤ) * (2 * A))
                    (outerSweepWord (0 : L) u z (sepLevel 1 α.sum) ((1 : ℤ) * (2 * A))
                      (1 : Total L)))) :=
  fun h => not_hzero_one_two_of_q_zero u hu (hzero_of_band_nil h)

/-- **The uniform band hypothesis is FALSE at `u = 0`, `(a,b) = (1,2)`, for every `q ∉ {0,1}`.** -/
theorem not_band_uniform_one_two_of_u_zero (q : L) (hq0 : q ≠ 0) (hq1 : q ≠ 1) :
    ¬ (∀ (α : List ℕ) (A : ℕ), (∀ x ∈ α, 0 < x) → 0 < A →
        ∀ z ∈ aboveReturnPaths 1 2 α.sum α,
          ∑ w ∈ aboveReturnPaths 1 2 A [A],
              bandSweepWord q (0 : L) (appendHeights z w) (sepLevel 1 (α.sum + A))
                  ((1 : ℤ) * (2 * A))
                (outerSweepWord q (0 : L) z (sepLevel 1 α.sum) ((1 : ℤ) * (2 * A)) (1 : Total L))
            = ((-1 : L) ^ ((1 - 1) * A) * (q * (0 : L)) ^ (1 - (A : ℤ))) •
                stageTotal q (0 : L) 1 2 α.length A
                  (bandSweepWord q (0 : L) z (sepLevel 1 α.sum) ((1 : ℤ) * (2 * A))
                    (outerSweepWord q (0 : L) z (sepLevel 1 α.sum) ((1 : ℤ) * (2 * A))
                      (1 : Total L)))) :=
  fun h => not_hzero_one_two_of_u_zero q hq0 hq1 (hzero_of_band_nil h)

end HJO.Mellit

end
