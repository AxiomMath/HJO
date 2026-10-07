/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.Shuffle.Colouring

/-! # What a separating admissible level does to the swept region, the colouring and the trace

`HJO.Mellit.isAdmissibleColouring_and_sum_sweepChar_eq_smul_dsc` and
`HJO.Mellit.mellitInduction_sweepWitness` both read `D_{η,c}` at a level `η` that *separates the
diagonal*: among the lattice points of the `aN × bN` rectangle weakly above the diagonal, the ones
outranking `η` are exactly the ones strictly above it. `HJO.Mellit.separatesDiagonal_sepLevel`
exhibits such a level, `η = aN + 1/2`. This file computes what that property makes of the objects of
`HJO/Shuffle/Colouring.lean`, which is everything `HJO.Mellit.Rem41` needs of them; the clause
itself is reduced in `HJO/Shuffle/MellitRem41.lean`.

## Main results

* `HJO.Mellit.sweptRegion_eq_diagPoints_union` — the swept region splits as the `N + 1` diagonal
  points `(ak, bk)` together with the points the level has not yet reached. Coprimality is what
  makes the first list exhaustive.
* `HJO.Mellit.mem_colouring_iff` — `HJO.Mellit.colouring` computed: a separating level crosses
  exactly the north steps standing on a return of the path other than the top, and exactly the east
  steps arriving at a return other than the origin.
* `HJO.Mellit.colouring_eq_compColouring_iff` — **an above-diagonal path is coloured `c_α` at a
  separating admissible level exactly when its return composition is `α`.** This is the
  identification of two index sets that the proof of
  `HJO.Mellit.isAdmissibleColouring_and_sum_sweepChar_eq_smul_dsc` performs silently: its left-hand
  sum runs over the paths of return composition `α`, while `HJO.Mellit.dsc` runs over the traces of
  the paths whose *colouring* is `c_α`.
* `HJO.Mellit.eq_of_levelTrace_eq` — at a separating level the trace of an above-diagonal path
  determines the path, so the representative `HJO.Mellit.traceRep` chooses is forced.
* `HJO.Mellit.dsc_compColouring_eq_sum_partialSweepWord` — **`D_{η,c_α} = ∑_{P̂} W_η(P̂)(1)`**, the
  statement that `HJO.Mellit.dsc` collects the partial words into `D_{η,c_α}`. `HJO.Mellit.dsc`
  sums over *traces*, one summand per trace however many paths realise it; the previous item is what
  turns that back into a sum over paths, and it is why
  `HJO.Mellit.partialSweepWord_eq_of_levelTrace_eq` — that the partial word depends only on the
  trace — is not needed here.
* `HJO.Mellit.pointRank_inj_of_le` — the injectivity of the rank on the strip, in the form of
  `HJO.Paths.abovePointRank_injOn`.

Nothing here has a hypothesis on `q` or `u`: every step is combinatorial.

## Implementation notes

`HJO.Paths.abovePointRank_lt_iff` and `HJO.Paths.abovePointRank_injOn` both need the hypothesis
`N ≥ 1`, and both carry it: without it they are false, and `HJO.Mellit.not_injective_pointRank_zero`
refutes the second at `N = 0`. The point is set out in full above
`HJO.Mellit.pointRank_inj_of_le`, which carries the same hypothesis.

## References

This file concerns `HJO.Paths.abovePointRank_lt_iff`, `HJO.Paths.abovePointRank_injOn`,
`HJO.Paths.sweptRegion`, `HJO.Mellit.IsAdmissibleLevel`, `HJO.Mellit.colouring`,
`HJO.Mellit.IsAdmissibleColouring`, `HJO.Mellit.partialSweepWord`, `HJO.Mellit.levelTrace`,
`HJO.Mellit.dsc`, `HJO.Mellit.compColouring`, `HJO.Paths.HasAboveReturns`,
`HJO.Mellit.partialSweepWord_eq_of_levelTrace_eq`,
`HJO.Mellit.isAdmissibleColouring_empty_and_dsc_eq_one` and
`HJO.Mellit.isAdmissibleColouring_and_sum_sweepChar_eq_smul_dsc`.
-/

@[expose] public section

open Finset

namespace HJO.Mellit

open ParkingFunctions Paths Sweep

variable {a b N : ℕ}

/-! ### East steps -/

/-- Membership in `HJO.Mellit.eastSteps`, read off the image. -/
theorem mem_eastSteps_iff {y : Heights a b N} {P : ℕ × ℕ} :
    P ∈ eastSteps y ↔ P.1 < a * N ∧ P.2 = ht y (P.1 + 1) := by
  simp only [eastSteps, Finset.mem_image, Finset.mem_range, Prod.ext_iff]
  refine ⟨?_, fun h => ⟨P.1, h.1, rfl, h.2.symm⟩⟩
  rintro ⟨x, hx, rfl, hx2⟩
  exact ⟨hx, hx2.symm⟩

/-! ### The rank at a lattice point against a separating level

Four readings of `HJO.Mellit.SeparatesDiagonal` and `HJO.Mellit.IsAdmissibleLevel`, which between
them are everything the argument below uses of the level. -/

/-- The above-diagonal rank of a diagonal lattice point `(ak, bk)` is `ak`: the weight `M` is
multiplied by `a(bk) - b(ak) = 0`. Stated in the uncurried form `HJO.Paths.liveSteps` writes. -/
theorem abovePointRank_diag (a b N k : ℕ) :
    abovePointRank a b N (a * k) (b * k) = ((a * k : ℕ) : ℤ) := by
  simp only [abovePointRank]
  push_cast
  ring

/-- The above-diagonal rank of a diagonal lattice point `(ak, bk)` is `ak`. -/
theorem pointRank_diag (a b N k : ℕ) : pointRank a b N (a * k, b * k) = ((a * k : ℕ) : ℤ) :=
  abovePointRank_diag a b N k

/-- No integer is an admissible level, a level being a half-integer. This is what turns the weak
inequality a separating level gives at a diagonal point into the strict one
`HJO.Mellit.colouring` asks for. -/
theorem intCast_ne_of_isAdmissibleLevel {η : ℚ} (hη : IsAdmissibleLevel η) (z : ℤ) :
    (z : ℚ) ≠ η := by
  obtain ⟨n, rfl⟩ := hη
  intro hz
  have h2 : ((2 * z : ℤ) : ℚ) = ((2 * n + 1 : ℤ) : ℚ) := by push_cast at hz ⊢; linarith
  have h3 : 2 * z = 2 * n + 1 := Int.cast_injective h2
  omega

/-- **A separating level separates, at a point of the rectangle.** The point form of
`HJO.Mellit.SeparatesDiagonal`: a lattice point of the rectangle weakly above the diagonal
outranks the level exactly when it lies strictly above the diagonal. -/
theorem lt_pointRank_iff {η : ℚ} (hηs : SeparatesDiagonal a b N η) {P : ℕ × ℕ}
    (h1 : P.1 ≤ a * N) (h2 : P.2 ≤ b * N) (h3 : b * P.1 ≤ a * P.2) :
    η < (pointRank a b N P : ℚ) ↔ b * P.1 < a * P.2 := by
  have h3' : (b : ℤ) * P.1 ≤ (a : ℤ) * P.2 := by exact_mod_cast h3
  rw [pointRank, hηs P.1 P.2 h1 h2 h3']
  exact ⟨fun h => by exact_mod_cast h, fun h => by exact_mod_cast h⟩

/-- **A diagonal point of the rectangle is under a separating admissible level.** -/
theorem pointRank_lt_of_diag {η : ℚ} (hηa : IsAdmissibleLevel η) (hηs : SeparatesDiagonal a b N η)
    {P : ℕ × ℕ} (h1 : P.1 ≤ a * N) (h2 : P.2 ≤ b * N) (h3 : b * P.1 = a * P.2) :
    (pointRank a b N P : ℚ) < η := by
  refine lt_of_le_of_ne (not_lt.1 fun hc => ?_) (intCast_ne_of_isAdmissibleLevel hηa _)
  exact absurd ((lt_pointRank_iff hηs h1 h2 h3.le).1 hc) (by omega)

/-- **A separating level is under the attack window.** The window `ω = (aN+1)aN` is the rank of
the lattice point `(0, 1)`, which lies strictly above the diagonal, so a separating level is below
it. This is what makes the upper half of the north-step condition of `HJO.Mellit.colouring`
automatic at a diagonal north step. -/
theorem lt_attackWindow {η : ℚ} (hηs : SeparatesDiagonal a b N η) (ha : 0 < a) (hb : 0 < b)
    (hN : 0 < N) : η < (attackWindow a N : ℚ) := by
  have hrank : abovePointRank a b N 0 1 = ((attackWindow a N : ℕ) : ℤ) := by
    simp only [abovePointRank, attackWindow]
    push_cast
    ring
  have h1 : (1 : ℕ) ≤ b * N := Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero hb.ne' hN.ne')
  have hapos : (0 : ℤ) < (a : ℤ) := by exact_mod_cast ha
  have h2 : (b : ℤ) * (0 : ℕ) ≤ (a : ℤ) * (1 : ℕ) := by simp
  have h3 : (b : ℤ) * (0 : ℕ) < (a : ℤ) * (1 : ℕ) := by simpa using hapos
  have := (hηs 0 1 (Nat.zero_le _) h1 h2).2 h3
  rw [hrank] at this
  exact_mod_cast this

/-! ### The rank is injective on the strip

`HJO.Paths.abovePointRank_injOn` and its input `HJO.Paths.abovePointRank_lt_iff`.

**Both statements are false without `N ≥ 1`**, and both proofs use it: they turn on
`M = (aN+1)N ≥ aN + 1 > aN`, which fails at `N = 0`, where `M = 0` and the rank is identically `0`
on the whole column `x = 0`. `HJO.Mellit.not_injective_pointRank_zero` is the witness. Nothing
downstream is affected — every use of the injectivity has `N ≥ 1` — and the same hypothesis is
spelled out in the proof of `HJO.ParkingFunctions.mul_add_mem_window_iff` ("which exceeds `aN`
because `N ≥ 1`"). -/

/-- **The above-diagonal rank is injective on the strip `0 ≤ x ≤ aN`.** This is
`HJO.Paths.abovePointRank_injOn`, with the `N ≥ 1` its proof uses: the rank is
`M(ay - bx) + x` with `M = (aN+1)N > aN`, so the leading term dominates the abscissa and the pair
`(ay - bx, x)` is read off. `0 < a` is needed for the last step, `ay = ay' ⟹ y = y'`. -/
theorem pointRank_inj_of_le (ha : 0 < a) (hN : 0 < N) {P Q : ℕ × ℕ} (hP : P.1 ≤ a * N)
    (hQ : Q.1 ≤ a * N) (h : pointRank a b N P = pointRank a b N Q) : P = Q := by
  have hN' : (1 : ℤ) ≤ (N : ℤ) := by exact_mod_cast hN
  have hapos : (0 : ℤ) < (a : ℤ) := by exact_mod_cast ha
  have hP' : ((P.1 : ℕ) : ℤ) ≤ (a : ℤ) * N := by exact_mod_cast hP
  have hQ' : ((Q.1 : ℕ) : ℤ) ≤ (a : ℤ) * N := by exact_mod_cast hQ
  have hWgt : (a : ℤ) * N < ((a : ℤ) * N + 1) * N := by nlinarith
  have hkey : ((a : ℤ) * N + 1) * N * ((a : ℤ) * P.2 - (b : ℤ) * P.1) + ((P.1 : ℕ) : ℤ)
      = ((a : ℤ) * N + 1) * N * ((a : ℤ) * Q.2 - (b : ℤ) * Q.1) + ((Q.1 : ℕ) : ℤ) := by
    simpa only [pointRank, abovePointRank] using h
  have hdd : (a : ℤ) * P.2 - (b : ℤ) * P.1 = (a : ℤ) * Q.2 - (b : ℤ) * Q.1 := by
    rcases lt_trichotomy ((a : ℤ) * P.2 - (b : ℤ) * P.1) ((a : ℤ) * Q.2 - (b : ℤ) * Q.1) with
      hlt | heq | hgt
    · exfalso
      have h1 : (a : ℤ) * P.2 - (b : ℤ) * P.1 + 1 ≤ (a : ℤ) * Q.2 - (b : ℤ) * Q.1 := by omega
      nlinarith
    · exact heq
    · exfalso
      nlinarith
  have hx : ((P.1 : ℕ) : ℤ) = ((Q.1 : ℕ) : ℤ) := by rw [hdd] at hkey; omega
  have hx' : P.1 = Q.1 := by exact_mod_cast hx
  have hy2 : (a : ℤ) * P.2 = (a : ℤ) * Q.2 := by rw [hx'] at hdd; omega
  exact Prod.ext hx' (by exact_mod_cast mul_left_cancel₀ (ne_of_gt hapos) hy2)

/-- **`HJO.Paths.abovePointRank_injOn` is false as printed.** At `N = 0` the rank is
identically zero on the strip `0 ≤ x ≤ aN`, which is the single column `x = 0`; the statement
carries no `N ≥ 1`, and its proof — like that of `HJO.Paths.abovePointRank_lt_iff`, which it cites —
needs one. The two points `(0,0)` and `(0,1)` refute it. -/
theorem not_injective_pointRank_zero (a b : ℕ) :
    ¬ Function.Injective (pointRank a b 0) := fun hinj => by
  have := hinj (a₁ := (0, 0)) (a₂ := (0, 1)) (by simp [pointRank, abovePointRank])
  simp at this

/-- Every lattice point weakly above the diagonal has nonnegative rank. -/
theorem pointRank_nonneg {P : ℕ × ℕ} (h : b * P.1 ≤ a * P.2) : 0 ≤ pointRank a b N P := by
  have h' : (b : ℤ) * P.1 ≤ (a : ℤ) * P.2 := by exact_mod_cast h
  have hW : (0 : ℤ) ≤ ((a : ℤ) * N + 1) * N := by positivity
  simp only [pointRank, abovePointRank]
  have := mul_nonneg hW (by omega : (0 : ℤ) ≤ (a : ℤ) * P.2 - (b : ℤ) * P.1)
  omega

/-- **A lattice point of the strip whose rank is at most `aN` lies on the diagonal.** The rank is
`M(ay - bx) + x` with `M > aN ≥ x`, so `ay - bx` must vanish. This is the fact that makes the level
line of a separating level pass above every point of the region but the diagonal ones, and it is
where `N ≥ 1` is spent. -/
theorem diag_of_pointRank_le (hN : 0 < N) {P : ℕ × ℕ} (hP : P.1 ≤ a * N)
    (hdiag : b * P.1 ≤ a * P.2) (h : pointRank a b N P ≤ ((a * N : ℕ) : ℤ)) :
    b * P.1 = a * P.2 := by
  have hN' : (1 : ℤ) ≤ (N : ℤ) := by exact_mod_cast hN
  have hdiag' : (b : ℤ) * P.1 ≤ (a : ℤ) * P.2 := by exact_mod_cast hdiag
  have hP' : ((P.1 : ℕ) : ℤ) ≤ (a : ℤ) * N := by exact_mod_cast hP
  have hWgt : (a : ℤ) * N < ((a : ℤ) * N + 1) * N := by nlinarith
  have h' : ((a : ℤ) * N + 1) * N * ((a : ℤ) * P.2 - (b : ℤ) * P.1) + ((P.1 : ℕ) : ℤ)
      ≤ (a : ℤ) * N := by
    have hcast : ((a * N : ℕ) : ℤ) = (a : ℤ) * N := by push_cast; ring
    simpa only [pointRank, abovePointRank, hcast] using h
  have hzero : (a : ℤ) * P.2 - (b : ℤ) * P.1 = 0 := by
    by_contra hc
    have h1 : (1 : ℤ) ≤ (a : ℤ) * P.2 - (b : ℤ) * P.1 := by omega
    nlinarith
  have : (b : ℤ) * P.1 = (a : ℤ) * P.2 := by omega
  exact_mod_cast this

/-- **The rank is injective on the swept region**, which is what makes the listings of
`HJO.Mellit.sweepWord` and `HJO.Mellit.partialSweepWord` unambiguous. Stated without `N ≥ 1`: at
`N = 0` the swept region is the single point `(0,0)`, where injectivity is free, so the hypothesis
the strip form needs is not needed here. -/
theorem pointRank_inj_of_mem_sweptRegion (ha : 0 < a) {y : Heights a b N} {P Q : ℕ × ℕ}
    (hP : P ∈ sweptRegion y) (hQ : Q ∈ sweptRegion y)
    (h : pointRank a b N P = pointRank a b N Q) : P = Q := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · have hcol : ∀ R : ℕ × ℕ, R ∈ sweptRegion y → R = (0, 0) := by
      intro R hR
      rw [mem_sweptRegion] at hR
      have h1 : R.1 = 0 := by omega
      have h2 : ht y (R.1 + 1) = b * 0 := ht_of_gt y (by omega)
      exact Prod.ext h1 (by omega)
    rw [hcol P hP, hcol Q hQ]
  · exact pointRank_inj_of_le ha hN (mem_sweptRegion.1 hP).1 (mem_sweptRegion.1 hQ).1 h

/-! ### The returns of an above-diagonal path, and the diagonal points of the swept region -/

/-- On an above-diagonal path the height at a diagonal abscissa is at least the diagonal height:
`ŷ_{ak} ≥ bk`. A *return* is where equality holds. -/
theorem IsAboveDiagonal.le_ht_diag {y : Heights a b N} (hy : IsAboveDiagonal y) (ha : 0 < a)
    {k : ℕ} (hk : k ≤ N) : b * k ≤ ht y (a * k) := by
  have h : a * (b * k) ≤ a * ht y (a * k) := by
    calc a * (b * k) = b * (a * k) := by ring
      _ ≤ a * ht y (a * k) := hy.2.2.2 (a * k) (Nat.mul_le_mul_left a hk)
  exact Nat.le_of_mul_le_mul_left h ha

/-- **An above-diagonal path is strictly above the diagonal height one step past a diagonal
abscissa**: `ŷ_{ak+1} > bk` whenever `ak + 1 ≤ aN`, because `(ak+1, bk)` lies strictly below the
diagonal. No return hypothesis is needed — the sentence "the path goes north out of a
touch point" is this inequality, and it holds at every diagonal abscissa. Applied at a return it
says the return is the foot of a north step; this is where `0 < b` is spent. -/
theorem lt_ht_succ_of_diag {y : Heights a b N} (hy : IsAboveDiagonal y) (hb : 0 < b) {k : ℕ}
    (hk : a * k + 1 ≤ a * N) : b * k < ht y (a * k + 1) := by
  by_contra hc
  rw [not_lt] at hc
  have h2 : a * ht y (a * k + 1) ≤ a * (b * k) := Nat.mul_le_mul_left a hc
  have h3 : b * (a * k + 1) ≤ a * ht y (a * k + 1) := hy.2.2.2 (a * k + 1) hk
  linarith

/-- The diagonal lattice points of the rectangle, `(ak, bk)` for `0 ≤ k ≤ N`. Every one of them is
swept by every above-diagonal path, and by `HJO.Mellit.sweptRegion_eq_diagPoints_union` they are
exactly the swept points a separating level does not reach. -/
def diagPoints (a b N : ℕ) : Finset (ℕ × ℕ) := (range (N + 1)).image fun k => (a * k, b * k)

theorem mem_diagPoints_iff {P : ℕ × ℕ} :
    P ∈ diagPoints a b N ↔ ∃ k ≤ N, P = (a * k, b * k) := by
  simp only [diagPoints, Finset.mem_image, Finset.mem_range]
  exact ⟨fun ⟨k, hk, h⟩ => ⟨k, by omega, h.symm⟩, fun ⟨k, hk, h⟩ => ⟨k, by omega, h.symm⟩⟩

theorem diag_mem_diagPoints {k : ℕ} (hk : k ≤ N) : (a * k, b * k) ∈ diagPoints a b N :=
  mem_diagPoints_iff.2 ⟨k, hk, rfl⟩

/-- **The diagonal points of the swept region are `(ak, bk)`, `0 ≤ k ≤ N`.** Coprimality is what
makes the list exhaustive: a swept point with `bx = ay` has `a ∣ x`. Every one of them is swept,
whatever the above-diagonal path does. -/
theorem filter_diag_sweptRegion (hab : Nat.Coprime a b) (ha : 0 < a) {y : Heights a b N}
    (hy : IsAboveDiagonal y) : {P ∈ sweptRegion y | b * P.1 = a * P.2} = diagPoints a b N := by
  ext P
  rw [Finset.mem_filter, mem_sweptRegion, mem_diagPoints_iff]
  constructor
  · rintro ⟨⟨h1, -, -⟩, hdiag⟩
    obtain ⟨k, hk⟩ : a ∣ P.1 := Nat.Coprime.dvd_of_dvd_mul_left hab ⟨P.2, hdiag⟩
    have hk2 : P.2 = b * k := by
      refine Nat.eq_of_mul_eq_mul_left ha ?_
      rw [← hdiag, hk]
      ring
    exact ⟨k, Nat.le_of_mul_le_mul_left (hk ▸ h1) ha, Prod.ext hk hk2⟩
  · rintro ⟨k, hk, rfl⟩
    refine ⟨⟨Nat.mul_le_mul_left a hk, le_of_eq (by ring), ?_⟩, by ring⟩
    rcases lt_or_eq_of_le (Nat.mul_le_mul_left a hk : a * k ≤ a * N) with hlt | heq
    · exact (IsAboveDiagonal.le_ht_diag hy ha hk).trans (hy.2.2.1 (a * k) hlt)
    · rw [ht_of_gt y (by omega)]
      exact Nat.mul_le_mul_left b hk

/-- **A separating level cuts the swept region at the diagonal.** -/
theorem sweptAbove_eq_filter {η : ℚ} (hηs : SeparatesDiagonal a b N η) (y : Heights a b N) :
    sweptAbove y η = {P ∈ sweptRegion y | b * P.1 < a * P.2} := by
  rw [sweptAbove]
  refine Finset.filter_congr fun P hP => ?_
  rw [mem_sweptRegion] at hP
  exact lt_pointRank_iff hηs hP.1 (hP.2.2.trans (ht_le_mul y _)) hP.2.1

/-- **The swept region is the diagonal points together with the points above a separating level.**
This is the split the proof of `HJO.Mellit.isAdmissibleColouring_and_sum_sweepChar_eq_smul_dsc`
performs on the sweep word: the diagonal points are the `N + 1` events the level line has already
passed, and the rest are the partial sweep word `W_η(P̂)`. -/
theorem sweptRegion_eq_diagPoints_union {η : ℚ} (hηs : SeparatesDiagonal a b N η)
    (hab : Nat.Coprime a b) (ha : 0 < a) {y : Heights a b N} (hy : IsAboveDiagonal y) :
    sweptRegion y = diagPoints a b N ∪ sweptAbove y η := by
  rw [sweptAbove_eq_filter hηs, ← filter_diag_sweptRegion hab ha hy]
  ext P
  simp only [Finset.mem_union, Finset.mem_filter]
  refine ⟨fun hP => ?_, fun hP => hP.elim (fun h => h.1) fun h => h.1⟩
  have := (mem_sweptRegion.1 hP).2.1
  rcases lt_or_eq_of_le this with h | h
  · exact Or.inr ⟨hP, h⟩
  · exact Or.inl ⟨hP, h⟩

/-- The diagonal points and the points above a separating level are disjoint. -/
theorem disjoint_diagPoints_sweptAbove {η : ℚ} (hηs : SeparatesDiagonal a b N η)
    (hab : Nat.Coprime a b) (ha : 0 < a) {y : Heights a b N} (hy : IsAboveDiagonal y) :
    Disjoint (diagPoints a b N) (sweptAbove y η) := by
  rw [sweptAbove_eq_filter hηs, ← filter_diag_sweptRegion hab ha hy]
  refine Finset.disjoint_left.2 fun P hP hP' => ?_
  rw [Finset.mem_filter] at hP hP'
  omega

/-! ### The colouring of an above-diagonal path at a separating level

The two halves of `HJO.Mellit.colouring` are computed here: a separating admissible level crosses
exactly the north steps standing on a return of the path, and exactly the east steps arriving at
one. -/

/-- **The north steps a separating level crosses are the returns below the top.** The lower
condition `rk̂(u) < η` forces the foot of `u` onto the diagonal, and the upper condition
`η < rk̂(u) + ω` is then automatic by `HJO.Mellit.lt_attackWindow`. -/
theorem mem_colouring_north_iff {η : ℚ} (hηa : IsAdmissibleLevel η)
    (hηs : SeparatesDiagonal a b N η) (hab : Nat.Coprime a b) (ha : 0 < a) (hb : 0 < b)
    (hN : 0 < N) {y : Heights a b N} (hy : IsAboveDiagonal y) {P : ℕ × ℕ} :
    (P ∈ northSteps y ∧ (pointRank a b N P : ℚ) < η ∧
        η < (pointRank a b N P : ℚ) + (attackWindow a N : ℚ)) ↔
      ∃ k, k < N ∧ ht y (a * k) = b * k ∧ P = (a * k, b * k) := by
  constructor
  · rintro ⟨hmem, hlt, -⟩
    rw [mem_northSteps_iff] at hmem
    have h2 : P.2 ≤ b * N := (hmem.2.2.le.trans (ht_le_mul y _))
    have hdiagle : b * P.1 ≤ a * P.2 :=
      (hy.2.2.2 P.1 hmem.1.le).trans (Nat.mul_le_mul_left a hmem.2.1)
    have hdiag : b * P.1 = a * P.2 := by
      by_contra hc
      exact absurd hlt (not_lt.2
        (lt_pointRank_iff hηs hmem.1.le h2 hdiagle |>.2 (by omega)).le)
    obtain ⟨k, hk⟩ : a ∣ P.1 := Nat.Coprime.dvd_of_dvd_mul_left hab ⟨P.2, hdiag⟩
    have hk2 : P.2 = b * k := by
      refine Nat.eq_of_mul_eq_mul_left ha ?_
      rw [← hdiag, hk]; ring
    have hkN : k < N := by
      have : a * k < a * N := hk ▸ hmem.1
      exact Nat.lt_of_mul_lt_mul_left this
    refine ⟨k, hkN, le_antisymm ?_ (IsAboveDiagonal.le_ht_diag hy ha hkN.le), Prod.ext hk hk2⟩
    rw [← hk, ← hk2]; exact hmem.2.1
  · rintro ⟨k, hkN, hret, rfl⟩
    have hak : a * k + 1 ≤ a * N := by
      have : a * k + a ≤ a * N := by
        calc a * k + a = a * (k + 1) := by ring
          _ ≤ a * N := Nat.mul_le_mul_left a hkN
      omega
    refine ⟨mem_northSteps_iff.2 ⟨by omega, hret.le, lt_ht_succ_of_diag hy hb hak⟩, ?_, ?_⟩
    · exact pointRank_lt_of_diag hηa hηs (by omega) (Nat.mul_le_mul_left b hkN.le) (by ring)
    · have hω := lt_attackWindow hηs ha hb hN
      have h0 : (0 : ℚ) ≤ (pointRank a b N (a * k, b * k) : ℚ) := by
        rw [pointRank_diag]; positivity
      linarith

/-- **The east steps a separating level crosses are those arriving at a return.** The condition
`rk̂(v + (1,0)) < η` forces the *right* end of `v` onto the diagonal, and `η < rk̂(v)` then says
only that the left end is off it, which `0 < b` gives. -/
theorem mem_colouring_east_iff {η : ℚ} (hηa : IsAdmissibleLevel η)
    (hηs : SeparatesDiagonal a b N η) (hab : Nat.Coprime a b) (ha : 0 < a) (hb : 0 < b)
    {y : Heights a b N} (hy : IsAboveDiagonal y) {P : ℕ × ℕ} :
    (P ∈ eastSteps y ∧ (pointRank a b N (P.1 + 1, P.2) : ℚ) < η ∧
        η < (pointRank a b N P : ℚ)) ↔
      ∃ k, 1 ≤ k ∧ k ≤ N ∧ ht y (a * k) = b * k ∧ P = (a * k - 1, b * k) := by
  constructor
  · rintro ⟨hmem, hlt, -⟩
    rw [mem_eastSteps_iff] at hmem
    have h2 : P.2 ≤ b * N := hmem.2 ▸ ht_le_mul y _
    have hdiagle : b * (P.1 + 1) ≤ a * P.2 := by
      rw [hmem.2]; exact hy.2.2.2 (P.1 + 1) (by omega)
    have hdiag : b * (P.1 + 1) = a * P.2 := by
      by_contra hc
      refine absurd hlt (not_lt.2 (lt_pointRank_iff hηs (P := (P.1 + 1, P.2))
        (show P.1 + 1 ≤ a * N from by omega) h2 hdiagle |>.2
        (show b * (P.1 + 1) < a * P.2 from lt_of_le_of_ne hdiagle hc)).le)
    obtain ⟨k, hk⟩ : a ∣ P.1 + 1 := Nat.Coprime.dvd_of_dvd_mul_left hab ⟨P.2, hdiag⟩
    have hk2 : P.2 = b * k := by
      refine Nat.eq_of_mul_eq_mul_left ha ?_
      rw [← hdiag, hk]; ring
    have hk1 : 1 ≤ k := Nat.pos_of_ne_zero fun h0 => by simp [h0] at hk
    have hkN : k ≤ N := by
      have : a * k ≤ a * N := by omega
      exact Nat.le_of_mul_le_mul_left this ha
    refine ⟨k, hk1, hkN, ?_, Prod.ext (by omega) hk2⟩
    rw [← hk, hmem.2.symm, hk2]
  · rintro ⟨k, hk1, hkN, hret, rfl⟩
    have haN : a * k ≤ a * N := Nat.mul_le_mul_left a hkN
    have hbN : b * k ≤ b * N := Nat.mul_le_mul_left b hkN
    have hak1 : 1 ≤ a * k := by
      calc 1 ≤ a * 1 := by omega
        _ ≤ a * k := Nat.mul_le_mul_left a hk1
    have hsucc : a * k - 1 + 1 = a * k := by omega
    have hsplit : b * (a * k) = b * (a * k - 1) + b := by
      obtain ⟨m, hm⟩ : ∃ m, a * k = m + 1 := ⟨a * k - 1, by omega⟩
      rw [hm]
      simp [Nat.mul_succ]
    have hcomm : a * (b * k) = b * (a * k) := by ring
    have hmem : (a * k - 1, b * k) ∈ eastSteps y :=
      mem_eastSteps_iff.2 ⟨show a * k - 1 < a * N from by omega, by rw [hsucc, hret]⟩
    refine ⟨hmem, ?_, ?_⟩
    · rw [show ((a * k - 1, b * k) : ℕ × ℕ).1 + 1 = a * k from hsucc]
      exact pointRank_lt_of_diag hηa hηs haN hbN (by ring)
    · exact (lt_pointRank_iff hηs (P := (a * k - 1, b * k))
        (show a * k - 1 ≤ a * N from by omega) hbN
        (show b * (a * k - 1) ≤ a * (b * k) from by omega)).2
        (show b * (a * k - 1) < a * (b * k) from by omega)

/-- **The colouring of an above-diagonal path at a separating admissible level**: the north steps
standing on a return other than the top, together with the east steps arriving at a return other
than the origin. This is `HJO.Mellit.colouring` computed at the levels
`HJO.Mellit.isAdmissibleColouring_and_sum_sweepChar_eq_smul_dsc` speaks about. -/
theorem mem_colouring_iff {η : ℚ} (hηa : IsAdmissibleLevel η) (hηs : SeparatesDiagonal a b N η)
    (hab : Nat.Coprime a b) (ha : 0 < a) (hb : 0 < b) (hN : 0 < N) {y : Heights a b N}
    (hy : IsAboveDiagonal y) {P : ℕ × ℕ} :
    P ∈ colouring y η ↔
      (∃ k, k < N ∧ ht y (a * k) = b * k ∧ P = (a * k, b * k)) ∨
      ∃ k, 1 ≤ k ∧ k ≤ N ∧ ht y (a * k) = b * k ∧ P = (a * k - 1, b * k) := by
  rw [colouring, Finset.mem_union, Finset.mem_filter, Finset.mem_filter,
    ← mem_colouring_north_iff hηa hηs hab ha hb hN hy,
    ← mem_colouring_east_iff hηa hηs hab ha hb hy]

/-! ### The colouring of a composition

`HJO.Mellit.compColouring` is indexed by the positions `1 ≤ i ≤ ℓ` of the composition; the
colouring of a path is indexed by the *values* of the partial sums. The two indexings are
identified here, which is where the positivity of the parts of a composition is spent: it makes
the partial sums strictly increasing, so `A_i = N` only at `i = ℓ` and `A_i = 0` only at `i = 0`. -/

/-- Membership in the list of prefix sums of `l` offset by `c`. -/
theorem mem_scanl_add_iff (l : List ℕ) (c k : ℕ) :
    k ∈ l.scanl (· + ·) c ↔ ∃ m ≤ l.length, c + (l.take m).sum = k := by
  induction l generalizing c with
  | nil => simp; omega
  | cons x l ih =>
    rw [List.scanl_cons, List.mem_cons, ih]
    constructor
    · rintro (rfl | ⟨m, hm, hsum⟩)
      · exact ⟨0, Nat.zero_le _, by simp⟩
      · refine ⟨m + 1, by simpa using hm, ?_⟩
        simp only [List.take_succ_cons, List.sum_cons]; omega
    · rintro ⟨m, hm, hsum⟩
      match m with
      | 0 => simp at hsum; omega
      | (m + 1) =>
        refine Or.inr ⟨m, by simpa using hm, ?_⟩
        simp only [List.take_succ_cons, List.sum_cons] at hsum; omega

/-- A composition's partial sums increase by at least one at every step. -/
theorem sum_take_lt_succ {α : List ℕ} (hpos : ∀ x ∈ α, 0 < x) {i : ℕ}
    (hi : i < α.length) : (α.take i).sum < (α.take (i + 1)).sum := by
  rw [List.sum_take_succ α i hi]
  exact Nat.lt_add_of_pos_right (hpos α[i] (List.getElem_mem hi))

/-- **A composition's partial sums are strictly increasing.** One strict step at `i`, then
monotonicity the rest of the way. -/
theorem sum_take_lt {α : List ℕ} (hpos : ∀ x ∈ α, 0 < x) {i j : ℕ} (hij : i < j)
    (hj : j ≤ α.length) : (α.take i).sum < (α.take j).sum :=
  (sum_take_lt_succ hpos (by omega)).trans_le (List.monotone_sum_take α hij)

/-- **The colouring of a composition, indexed by the values of its partial sums.** The first family
of `HJO.Mellit.compColouring` is the partial sums other than `N`, the second the partial sums other
than `0`. -/
theorem mem_compColouring_iff {α : List ℕ} (hpos : ∀ x ∈ α, 0 < x) (hsum : α.sum = N)
    {P : ℕ × ℕ} :
    P ∈ compColouring a b α ↔
      (∃ k, k < N ∧ k ∈ α.scanl (· + ·) 0 ∧ P = (a * k, b * k)) ∨
      ∃ k, 1 ≤ k ∧ k ≤ N ∧ k ∈ α.scanl (· + ·) 0 ∧ P = (a * k - 1, b * k) := by
  have hfull : (α.take α.length).sum = N := by rw [List.take_length, hsum]
  rw [compColouring, Finset.mem_union, Finset.mem_image, Finset.mem_image]
  simp only [Finset.mem_range, mem_scanl_add_iff, Nat.zero_add]
  constructor
  · rintro (⟨i, hi, rfl⟩ | ⟨i, hi, rfl⟩)
    · exact Or.inl ⟨_, hfull ▸ sum_take_lt hpos hi le_rfl, ⟨i, hi.le, rfl⟩, rfl⟩
    · refine Or.inr ⟨_, ?_, ?_, ⟨i + 1, hi, rfl⟩, rfl⟩
      · have h0 := sum_take_lt hpos (show 0 < i + 1 by omega) hi
        simp only [List.take_zero, List.sum_nil] at h0
        omega
      · rcases Nat.lt_or_ge (i + 1) α.length with h | h
        · exact (hfull ▸ sum_take_lt hpos h le_rfl).le
        · have : i + 1 = α.length := by omega
          rw [this, hfull]
  · rintro (⟨k, hkN, ⟨m, hm, rfl⟩, rfl⟩ | ⟨k, hk1, hkN, ⟨m, hm, rfl⟩, rfl⟩)
    · refine Or.inl ⟨m, ?_, rfl⟩
      rcases Nat.lt_or_ge m α.length with h | h
      · exact h
      · rw [show m = α.length from by omega, hfull] at hkN; omega
    · obtain ⟨i, rfl⟩ : ∃ i, m = i + 1 := by
        match m with
        | 0 => simp at hk1
        | (i + 1) => exact ⟨i, rfl⟩
      exact Or.inr ⟨i, by omega, rfl⟩

/-! ### The colouring of a composition is the colouring of its paths -/

/-- **A diagonal point above the origin meets the two families of `HJO.Mellit.compColouring` only
in the first, and there only at its own index.** Both `HJO.Mellit.mem_colouring_iff` and
`HJO.Mellit.mem_compColouring_iff` present their set as a family `(ak', bk')` of diagonal points
united with the family `(ak' - 1, bk')` of their western neighbours, taken over the indices
satisfying some condition `Q`; this reads the point `(ak, bk)` off either union as `Q k`.

A collision with the second family would need `bk = bk'`, hence `k = k'` because `0 < b`, and then
`ak = ak - 1`, which `0 < a` and `0 < k` forbid. -/
theorem diag_mem_union_iff (ha : 0 < a) (hb : 0 < b) {Q : ℕ → Prop} {k : ℕ} (hk0 : 0 < k)
    (hkN : k < N) :
    ((∃ k', k' < N ∧ Q k' ∧ ((a * k, b * k) : ℕ × ℕ) = (a * k', b * k')) ∨
      ∃ k', 1 ≤ k' ∧ k' ≤ N ∧ Q k' ∧ ((a * k, b * k) : ℕ × ℕ) = (a * k' - 1, b * k')) ↔ Q k := by
  refine ⟨?_, fun h => Or.inl ⟨k, hkN, h, rfl⟩⟩
  rintro (⟨k', -, hQ, hP⟩ | ⟨k', -, -, -, hP⟩) <;> rw [Prod.mk.injEq] at hP
  · rwa [Nat.eq_of_mul_eq_mul_left hb hP.2]
  · have h1 : 0 < a * k := Nat.mul_pos ha hk0
    obtain rfl : k = k' := Nat.eq_of_mul_eq_mul_left hb hP.2
    exact absurd hP.1 (by omega)

/-- **A separating admissible level colours an above-diagonal path by `c_α` exactly when the path's
return composition is `α`.** This is the identification of the two index sets that the proof of
`HJO.Mellit.isAdmissibleColouring_and_sum_sweepChar_eq_smul_dsc` performs silently: the left-hand
sum of that statement runs over the above-diagonal paths of return composition `α`, while
`D_{η,c_α}` of `HJO.Mellit.dsc` runs over the traces of the paths whose *colouring* is `c_α`.

No lower bound on `a` beyond positivity is spent, so the colouring still determines the returns at
`a = 1`: by `HJO.Mellit.diag_mem_union_iff` a diagonal point `(A_i, b A_i)` above the origin lies
in either union only through the first family, a collision with the second needing
`b A_i = b A_{i'}`, hence `A_i = A_{i'}` because `0 < b`, and then `a A_i = a A_i - 1`. The
standing `1 < a < b` is therefore inherited here and not used in its strength, which is
why the statement is given under `0 < a` and `0 < b`. -/
theorem colouring_eq_compColouring_iff {η : ℚ} (hηa : IsAdmissibleLevel η)
    (hηs : SeparatesDiagonal a b N η) (hab : Nat.Coprime a b) (ha : 0 < a) (hb : 0 < b)
    {α : List ℕ} (hpos : ∀ x ∈ α, 0 < x) (hsum : α.sum = N) {y : Heights a b N}
    (hy : IsAboveDiagonal y) : colouring y η = compColouring a b α ↔ HasAboveReturns α y := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · have hα : α = [] := by
      match α with
      | [] => rfl
      | (x :: l) =>
        have hx := hpos x (by simp)
        simp only [List.sum_cons] at hsum
        omega
    subst hα
    have hns : northSteps y = ∅ := by simp [northSteps]
    have hes : eastSteps y = ∅ := by simp [eastSteps]
    refine iff_of_true ?_ ⟨hy, hpos, hsum, fun k hk => ?_⟩
    · rw [colouring, hns, hes, compColouring]
      simp
    · have hk0 : k = 0 := by omega
      subst hk0
      exact iff_of_true (by simpa using hy.1) (by simp)
  constructor
  · intro heq
    refine ⟨hy, hpos, hsum, fun k hk => ?_⟩
    rcases Nat.eq_zero_or_pos k with rfl | hk0
    · refine iff_of_true (by simpa using hy.1) ?_
      exact (mem_scanl_add_iff α 0 0).2 ⟨0, Nat.zero_le _, by simp⟩
    rcases eq_or_lt_of_le hk with rfl | hkN
    · exact iff_of_true hy.2.1 ((mem_scanl_add_iff α 0 k).2 ⟨α.length, le_rfl, by simpa using hsum⟩)
    have hleft : (a * k, b * k) ∈ colouring y η ↔ ht y (a * k) = b * k :=
      (mem_colouring_iff hηa hηs hab ha hb hN hy).trans
        (diag_mem_union_iff (Q := fun k' => ht y (a * k') = b * k') ha hb hk0 hkN)
    have hright : (a * k, b * k) ∈ compColouring a b α ↔ k ∈ α.scanl (· + ·) 0 :=
      (mem_compColouring_iff hpos hsum).trans
        (diag_mem_union_iff (Q := fun k' => k' ∈ α.scanl (· + ·) 0) ha hb hk0 hkN)
    rw [← hleft, heq, hright]
  · rintro ⟨-, -, -, hret⟩
    ext P
    rw [mem_colouring_iff hηa hηs hab ha hb hN hy, mem_compColouring_iff hpos hsum]
    constructor
    · rintro (⟨k, hkN, h, hP⟩ | ⟨k, hk1, hkN, h, hP⟩)
      · exact Or.inl ⟨k, hkN, (hret k hkN.le).1 h, hP⟩
      · exact Or.inr ⟨k, hk1, hkN, (hret k hkN).1 h, hP⟩
    · rintro (⟨k, hkN, h, hP⟩ | ⟨k, hk1, hkN, h, hP⟩)
      · exact Or.inl ⟨k, hkN, (hret k hkN.le).2 h, hP⟩
      · exact Or.inr ⟨k, hk1, hkN, (hret k hkN).2 h, hP⟩

/-! ### A trace at a separating level determines its path

`HJO.Mellit.dsc` sums over *traces*, one summand per trace however many paths realise it. At a
separating level the trace of an above-diagonal path determines the path, so the sum over traces of
`HJO.Mellit.dsc` is a sum over paths after all — which is what lets the left-hand sum of
`HJO.Mellit.isAdmissibleColouring_and_sum_sweepChar_eq_smul_dsc`, indexed by paths, be compared with
it. Nothing here needs `HJO.Mellit.partialSweepWord_eq_of_levelTrace_eq`: the representative
`HJO.Mellit.traceRep` chooses out of a fibre with one element. -/

/-- A height vector is determined by its heights inside the rectangle; the heights past `aN`
are held at `bN` and carry nothing. -/
theorem heights_ext {y₁ y₂ : Heights a b N} (h : ∀ r ≤ a * N, ht y₁ r = ht y₂ r) : y₁ = y₂ :=
  funext fun i => Fin.ext (by
    rw [← ht_coe y₁ i, ← ht_coe y₂ i]; exact h i.val (by omega))

/-- The point set of the trace is the swept region above the level, so two paths with the same
trace sweep the same points above the level. -/
theorem mem_sweptAbove_of_levelTrace_eq {η : ℚ} {y₁ y₂ : Heights a b N}
    (h : levelTrace y₁ η = levelTrace y₂ η) {P : ℕ × ℕ} (hP : P ∈ sweptAbove y₁ η) :
    P ∈ sweptAbove y₂ η := by
  have h1 : (P, eventType y₁ P, sweepRight y₁ P) ∈ levelTrace y₂ η := by
    rw [← h, levelTrace]
    exact Finset.mem_image_of_mem _ hP
  rw [levelTrace, Finset.mem_image] at h1
  obtain ⟨Q, hQ, hQ'⟩ := h1
  rw [Prod.mk.injEq] at hQ'
  exact hQ'.1 ▸ hQ

/-- **At a separating level the trace of an above-diagonal path determines the path.** The top
`(x, ŷ_{x+1})` of the path's column at `x` is swept, and it lies *strictly* above the diagonal
because `bx < b(x+1) ≤ aŷ_{x+1}` — which is where `0 < b` is spent; so it belongs to the trace's
point set, and the two paths bound each other column by column. -/
theorem eq_of_levelTrace_eq {η : ℚ} (hηs : SeparatesDiagonal a b N η) (hb : 0 < b)
    {y₁ y₂ : Heights a b N} (h1 : IsAboveDiagonal y₁) (h2 : IsAboveDiagonal y₂)
    (h : levelTrace y₁ η = levelTrace y₂ η) : y₁ = y₂ := by
  have key : ∀ z₁ z₂ : Heights a b N, IsAboveDiagonal z₁ →
      (∀ P ∈ sweptAbove z₁ η, P ∈ sweptAbove z₂ η) →
      ∀ x, x < a * N → ht z₁ (x + 1) ≤ ht z₂ (x + 1) := by
    intro z₁ z₂ hz₁ hsub x hx
    have hbd : b * (x + 1) ≤ a * ht z₁ (x + 1) := hz₁.2.2.2 (x + 1) (by omega)
    have hexp : b * (x + 1) = b * x + b := by ring
    have hmem : (x, ht z₁ (x + 1)) ∈ sweptAbove z₁ η := by
      rw [sweptAbove_eq_filter hηs, Finset.mem_filter, mem_sweptRegion]
      exact ⟨⟨by omega, show b * x ≤ a * ht z₁ (x + 1) from by omega, le_rfl⟩,
        show b * x < a * ht z₁ (x + 1) from by omega⟩
    have hmem2 := hsub _ hmem
    rw [sweptAbove_eq_filter hηs, Finset.mem_filter, mem_sweptRegion] at hmem2
    exact hmem2.1.2.2
  refine heights_ext fun r hr => ?_
  rcases Nat.eq_zero_or_pos r with rfl | hr0
  · rw [h1.1, h2.1]
  · obtain ⟨x, rfl⟩ : ∃ x, r = x + 1 := ⟨r - 1, by omega⟩
    exact le_antisymm
      (key y₁ y₂ h1 (fun _ hP => mem_sweptAbove_of_levelTrace_eq h hP) x (by omega))
      (key y₂ y₁ h2 (fun _ hP => mem_sweptAbove_of_levelTrace_eq h.symm hP) x (by omega))

/-- **The path `HJO.Mellit.traceRep` chooses for the trace of an above-diagonal path is that path.**
At a separating level the fibre has one element, so the choice is forced and
`HJO.Mellit.partialSweepWord_eq_of_levelTrace_eq` — that the partial word depends only on the trace
— is not needed. -/
theorem traceRep_eq_self {η : ℚ} (hηs : SeparatesDiagonal a b N η) (hb : 0 < b)
    {c : Finset (ℕ × ℕ)} {y : Heights a b N} (hy : IsAboveDiagonal y) (hc : colouring y η = c) :
    traceRep a b N η c (levelTrace y η) = y := by
  have hτ : levelTrace y η ∈ traceIndex a b N η c :=
    Finset.mem_image_of_mem _ (Finset.mem_filter.2 ⟨Finset.mem_univ y, hy, hc⟩)
  obtain ⟨hab1, -, hab3⟩ := traceRep_spec hτ
  exact eq_of_levelTrace_eq hηs hb hab1 hy hab3

/-! ### `D_{η,c_α}` is the sum of the partial sweep words over the paths of return composition `α`

This is the sentence "`HJO.Mellit.dsc` collects the partial words into
`D_{η,c_α}`", proved. -/

section Substrate

variable {L : Type*} [Field L] [Algebra ℚ L]

/-- **`D_{η,c_α}` is the sum of `W_η(P̂)(1)` over the above-diagonal paths of return composition
`α`.** Both identifications usually left implicit are discharged here: the paths coloured
`c_α` at a separating level are exactly those of return composition `α`
(`HJO.Mellit.colouring_eq_compColouring_iff`), and the trace determines the path
(`HJO.Mellit.eq_of_levelTrace_eq`), so the sum over traces of `HJO.Mellit.dsc` is a sum over
paths with no multiplicity.

This is a theorem about the concrete operators, with no hypothesis on `q` or `u`: every step is
combinatorial. -/
theorem dsc_compColouring_eq_sum_partialSweepWord (q u : L) {η : ℚ} (hηa : IsAdmissibleLevel η)
    (hηs : SeparatesDiagonal a b N η) (hab : Nat.Coprime a b) (ha : 0 < a) (hb : 0 < b)
    {α : List ℕ} (hpos : ∀ x ∈ α, 0 < x) (hsum : α.sum = N) :
    dsc q u a b N η (compColouring a b α)
      = ∑ y ∈ aboveReturnPaths a b N α, partialSweepWord q u y η (1 : Total L) := by
  have hiff : ∀ y : Heights a b N, IsAboveDiagonal y →
      (colouring y η = compColouring a b α ↔ HasAboveReturns α y) := fun y hy =>
    colouring_eq_compColouring_iff hηa hηs hab ha hb hpos hsum hy
  have hset : {y ∈ (univ : Finset (Heights a b N)) |
      IsAboveDiagonal y ∧ colouring y η = compColouring a b α} = aboveReturnPaths a b N α := by
    ext y
    simp only [aboveReturnPaths, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨fun h => ⟨h.1, (hiff y h.1).1 h.2⟩, fun h => ⟨h.1, (hiff y h.1).2 h.2⟩⟩
  have hinj : ∀ y₁ ∈ aboveReturnPaths a b N α, ∀ y₂ ∈ aboveReturnPaths a b N α,
      levelTrace y₁ η = levelTrace y₂ η → y₁ = y₂ := by
    intro y₁ h₁ y₂ h₂ h
    rw [aboveReturnPaths, Finset.mem_filter] at h₁ h₂
    exact eq_of_levelTrace_eq hηs hb h₁.2.1 h₂.2.1 h
  rw [dsc, traceIndex, hset, Finset.sum_image hinj]
  refine Finset.sum_congr rfl fun y hy => ?_
  rw [aboveReturnPaths, Finset.mem_filter] at hy
  rw [traceRep_eq_self hηs hb hy.2.1 ((hiff y hy.2.1).2 hy.2.2)]

end Substrate

end HJO.Mellit
