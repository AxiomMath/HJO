/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.Shuffle.BraidOfColouring

/-! # Where the level line meets the antidiagonal, and where it does not

`HJO.Mellit.isSpecialBraidData_braidDataOfColouring` has six clauses. Four of them — that the
crossings lie in `(0,1)` on the torus, that none of them is the puncture `θ`, that they are pairwise
distinct, and that the components lie inside the rectangle — are analytic statements about a single
crossing abscissa and need nothing about how the crossings are grouped into components. Those four
are proved here. The two that remain, that each component has at least one crossing and that
distinct components are disjoint, need the pairing of crossed north with crossed east steps, and are
not here.

The three arguments are those of the usual proof, and each reduces to one fact:

* **no crossing sits on a vertical lattice line.** If it did, the point of the level line above it
  would be a lattice point of rank exactly `η`, which an admissible level forbids.
* **no crossing sits at the puncture.** If a crossing has fractional part `θ` then, since
  `(1+s)θ = 1`, subtracting the integer part again produces a lattice point of rank `η`.
* **two crossings with the same fractional part coincide.** Their difference `d` is an integer with
  `s·d` an integer, so `(aN+1)Na ∣ ((aN+1)Nb - 1)d`; `(aN+1)N` and `(aN+1)Nb - 1` are coprime, so
  `(aN+1)N ∣ d`, and `|d| ≤ aN < (aN+1)N` forces `d = 0`.

## Main results

* `HJO.Mellit.pointRank_ne_of_on_level` — a lattice point on the level line is impossible.
* `HJO.Mellit.fract_crossingAbscissa_ne_zero`, `HJO.Mellit.fract_crossingAbscissa_ne_sweepTheta`.
* `HJO.Mellit.crossingAbscissa_injOn_fract` — the coprimality argument.
* `HJO.Mellit.componentRight_le` — every component ends inside the rectangle, which is what bounds
  `|d|` above.

## References

The objects involved are `HJO.Mellit.isSpecialBraidData_braidDataOfColouring`,
`HJO.Mellit.braidDataOfColouring`, `HJO.Mellit.colouringComponent`, `HJO.Braid.IsSpecialBraidData`,
`HJO.Braid.nextCrossing`, `HJO.Mellit.sweepSlope`, `HJO.Mellit.IsAdmissibleLevel`.
-/

@[expose] public section

open Finset

namespace HJO.Mellit

open ParkingFunctions Paths Sweep

variable {a b N : ℕ}

/-! ### Preliminaries on the slope, the intercept and `θ` -/

/-- The antidiagonal coordinate `θ = 1/(1 + s_{a,b,N})` of `HJO.Braid.nextCrossing` at the sweep
slope. -/
def sweepTheta (a b N : ℕ) : ℚ := 1 / (1 + sweepSlope a b N)

/-- `θ(s + 1) = 1`, which is what `HJO.Braid.IsSpecialBraidData` asks of `θ`. -/
theorem sweepTheta_mul (hs : 1 + sweepSlope a b N ≠ 0) :
    sweepTheta a b N * (sweepSlope a b N + 1) = 1 := by
  rw [sweepTheta, div_mul_eq_mul_div, one_mul, div_eq_one_iff_eq hs]
  ring

/-- `θ` lies in `(0, 1)`: the slope is positive, so `1 + s > 1`. -/
theorem sweepTheta_mem_Ioo (ha : 0 < a) (hb : 0 < b) (hN : 0 < N) :
    sweepTheta a b N ∈ Set.Ioo (0 : ℚ) 1 := by
  have hs := sweepSlope_pos (a := a) (b := b) (N := N) ha hb hN
  constructor
  · exact div_pos one_pos (by linarith)
  · rw [sweepTheta, div_lt_one (by linarith)]
    linarith

/-- The intercept of a level above the diagonal is positive. -/
theorem levelIntercept_pos (ha : 0 < a) (hN : 0 < N) {η : ℚ} (hη : 0 < η) :
    0 < levelIntercept a N η := by
  have hden : (0 : ℚ) < (a : ℚ) * ((a : ℚ) * N + 1) * N := by
    have ha' : (0 : ℚ) < a := by exact_mod_cast ha
    have hN' : (0 : ℚ) < N := by exact_mod_cast hN
    positivity
  exact div_pos hη hden

/-! ### A lattice point never sits on the level line -/

/-- The above-diagonal rank of a lattice point over `ℚ`, in the shape
`HJO.Mellit.abovePointRank_sub_level` produces. -/
theorem cast_pointRank_eq' (a b N e w : ℕ) :
    ((pointRank a b N (e, w) : ℤ) : ℚ) =
      (((a : ℚ) * N + 1) * N) * ((a : ℚ) * w - (b : ℚ) * e) + e := by
  simp only [pointRank, abovePointRank]
  push_cast
  ring

/-- **No lattice point lies on the level line.** If the level line passes through `(e, w)` with
`e, w` natural then `rk̂(e, w) = η`, which `HJO.Mellit.IsAdmissibleLevel` forbids. This is the
single fact the next two lemmas both run on. -/
theorem pointRank_ne_of_on_level (ha : 0 < a) (hN : 0 < N) {η : ℚ} (hη : IsAdmissibleLevel η)
    (e w : ℕ) : sweepSlope a b N * (e : ℚ) + levelIntercept a N η ≠ (w : ℚ) := by
  intro h
  have hkey := abovePointRank_sub_level (a := a) (b := b) (N := N) ha.ne' hN.ne' η (e : ℚ) (w : ℚ)
  rw [h, sub_self, mul_zero] at hkey
  exact cast_pointRank_ne_of_isAdmissibleLevel hη a b N (e, w)
    (by rw [cast_pointRank_eq']; linarith)

/-! ### The fractional part of a crossing -/

/-- The defining property of `HJO.Mellit.crossingAbscissa`. -/
theorem one_add_sweepSlope_mul_crossingAbscissa (hs : 1 + sweepSlope a b N ≠ 0) (η : ℚ) (n : ℤ) :
    (1 + sweepSlope a b N) * crossingAbscissa a b N η n + levelIntercept a N η = (n : ℚ) := by
  rw [crossingAbscissa, mul_div_cancel₀ _ hs]
  ring

/-- **No crossing sits on a vertical lattice line**, so the torus coordinate of a crossing is
strictly positive — the lower half of the `v ∈ (0,1)^k` clause of `HJO.Braid.IsSpecialBraidData`. -/
theorem fract_crossingAbscissa_ne_zero (ha : 0 < a) (hb : 0 < b) (hN : 0 < N) {η : ℚ}
    (hη : IsAdmissibleLevel η) (hηpos : 0 < η) {n : ℤ}
    (hx : 0 ≤ crossingAbscissa a b N η n) : Int.fract (crossingAbscissa a b N η n) ≠ 0 := by
  set x := crossingAbscissa a b N η n with hxdef
  have hspos := sweepSlope_pos (a := a) (b := b) (N := N) ha hb hN
  have hs : 1 + sweepSlope a b N ≠ 0 := by linarith
  have hhpos := levelIntercept_pos (a := a) (N := N) ha hN hηpos
  intro hfr
  -- `x` is a nonnegative integer `e`
  have hxe : x = ((⌊x⌋ : ℤ) : ℚ) := by
    have := Int.fract_add_floor x
    rw [hfr] at this
    linarith
  have hfl : 0 ≤ ⌊x⌋ := Int.le_floor.2 (by exact_mod_cast hx)
  obtain ⟨e, he⟩ : ∃ e : ℕ, (⌊x⌋ : ℤ) = (e : ℤ) := ⟨⌊x⌋.toNat, by omega⟩
  -- the ordinate of the level line above it is a positive integer `w`
  have hval := one_add_sweepSlope_mul_crossingAbscissa (a := a) (b := b) (N := N) hs η n
  have hord : sweepSlope a b N * (e : ℚ) + levelIntercept a N η = ((n - e : ℤ) : ℚ) := by
    rw [← hxdef] at hval
    rw [hxe] at hval
    rw [he] at hval
    push_cast at hval ⊢
    linarith
  have hwpos : 0 < ((n - e : ℤ) : ℚ) := by
    rw [← hord]
    have : (0 : ℚ) ≤ (e : ℚ) := Nat.cast_nonneg _
    nlinarith
  obtain ⟨w, hw⟩ : ∃ w : ℕ, (n - e : ℤ) = (w : ℤ) := ⟨(n - e).toNat, by
    have : (0 : ℤ) < n - e := by exact_mod_cast hwpos
    omega⟩
  exact pointRank_ne_of_on_level (b := b) ha hN hη e w (by rw [hord, hw]; norm_num)

/-- **No crossing sits at the puncture.** A crossing with torus coordinate `θ` would, after
subtracting its integer part and using `(1+s)θ = 1`, put a lattice point on the level line. This is
the `ne_theta` clause of `HJO.Braid.IsSpecialBraidData`. -/
theorem fract_crossingAbscissa_ne_sweepTheta (ha : 0 < a) (hb : 0 < b) (hN : 0 < N) {η : ℚ}
    (hη : IsAdmissibleLevel η) (hηpos : 0 < η) {n : ℤ}
    (hx : 0 ≤ crossingAbscissa a b N η n) :
    Int.fract (crossingAbscissa a b N η n) ≠ sweepTheta a b N := by
  set x := crossingAbscissa a b N η n with hxdef
  have hspos := sweepSlope_pos (a := a) (b := b) (N := N) ha hb hN
  have hs : 1 + sweepSlope a b N ≠ 0 := by linarith
  have hhpos := levelIntercept_pos (a := a) (N := N) ha hN hηpos
  obtain ⟨hθ0, hθ1⟩ := sweepTheta_mem_Ioo (a := a) (b := b) (N := N) ha hb hN
  have hθ : (1 + sweepSlope a b N) * sweepTheta a b N = 1 := by
    rw [sweepTheta, mul_one_div, div_self hs]
  intro hfr
  have hxe : x = ((⌊x⌋ : ℤ) : ℚ) + sweepTheta a b N := by
    have := Int.fract_add_floor x
    rw [hfr] at this
    linarith
  have hfl : 0 ≤ ⌊x⌋ := by
    by_contra hcon
    have h1 : (⌊x⌋ : ℚ) ≤ -1 := by exact_mod_cast (by omega : (⌊x⌋ : ℤ) ≤ -1)
    rw [hxe] at hx
    linarith
  obtain ⟨e, he⟩ : ∃ e : ℕ, (⌊x⌋ : ℤ) = (e : ℤ) := ⟨⌊x⌋.toNat, by omega⟩
  have hval := one_add_sweepSlope_mul_crossingAbscissa (a := a) (b := b) (N := N) hs η n
  have hord : sweepSlope a b N * (e : ℚ) + levelIntercept a N η = ((n - 1 - e : ℤ) : ℚ) := by
    rw [← hxdef] at hval
    rw [hxe, he] at hval
    push_cast at hval ⊢
    nlinarith [hval, hθ]
  have hwpos : 0 < ((n - 1 - e : ℤ) : ℚ) := by
    rw [← hord]
    have : (0 : ℚ) ≤ (e : ℚ) := Nat.cast_nonneg _
    nlinarith
  obtain ⟨w, hw⟩ : ∃ w : ℕ, (n - 1 - e : ℤ) = (w : ℤ) := ⟨(n - 1 - e).toNat, by
    have : (0 : ℤ) < n - 1 - e := by exact_mod_cast hwpos
    omega⟩
  exact pointRank_ne_of_on_level (b := b) ha hN hη e w (by rw [hord, hw]; norm_num)

/-! ### Distinctness: the coprimality argument -/

/-- `(aN+1)N` and `(aN+1)Nb - 1` are coprime over `ℤ`: a common divisor divides both `(aN+1)Nb`
and `(aN+1)Nb - 1`. -/
theorem isCoprime_window (a b N : ℕ) :
    IsCoprime (((a * N + 1) * N : ℕ) : ℤ) ((((a * N + 1) * N * b : ℕ) : ℤ) - 1) :=
  ⟨(b : ℤ), -1, by push_cast; ring⟩

/-- **If `s·d` is an integer for an integer `d`, then `(aN+1)N` divides `d`.** Clearing the
denominator of `s` gives `(aN+1)Na ∣ ((aN+1)Nb - 1)d`, and `HJO.Mellit.isCoprime_window` strips the
second factor. -/
theorem dvd_of_sweepSlope_mul_int (ha : 0 < a) (hN : 0 < N) {d t : ℤ}
    (h : sweepSlope a b N * (d : ℚ) = (t : ℚ)) :
    (((a * N + 1) * N : ℕ) : ℤ) ∣ d := by
  have hMa : (0 : ℚ) < (a : ℚ) * ((a : ℚ) * N + 1) * N := by
    have ha' : (0 : ℚ) < a := by exact_mod_cast ha
    have hN' : (0 : ℚ) < N := by exact_mod_cast hN
    positivity
  have hQ : ((((a * N + 1) * N * b : ℕ) : ℚ) - 1) * (d : ℚ)
      = ((a : ℚ) * ((a : ℚ) * N + 1) * N) * (t : ℚ) := by
    rw [sweepSlope, div_mul_eq_mul_div, div_eq_iff hMa.ne'] at h
    push_cast at h ⊢
    linarith
  have hZ : ((((a * N + 1) * N * b : ℕ) : ℤ) - 1) * d
      = (((a * N + 1) * N : ℕ) : ℤ) * (a : ℤ) * t := by
    have hq : (((((((a * N + 1) * N * b : ℕ) : ℤ) - 1) * d : ℤ)) : ℚ)
        = ((((((a * N + 1) * N : ℕ) : ℤ) * (a : ℤ) * t : ℤ)) : ℚ) := by
      push_cast
      push_cast at hQ
      linarith
    exact_mod_cast hq
  obtain ⟨u, v, huv⟩ := isCoprime_window a b N
  exact ⟨d * u + v * ((a : ℤ) * t), by linear_combination (-d) * huv + v * hZ⟩

/-- **Two crossings inside the rectangle with the same torus coordinate coincide.** The
distinctness argument: the difference `d` of the two abscissae is an integer with `s·d` an integer,
so `(aN+1)N ∣ d` by `HJO.Mellit.dvd_of_sweepSlope_mul_int`, and `|d| ≤ aN < (aN+1)N` forces
`d = 0`. -/
theorem crossingAbscissa_injOn_fract (ha : 0 < a) (hb : 0 < b) (hN : 0 < N) {η : ℚ} {m n : ℤ}
    (hm0 : 0 ≤ crossingAbscissa a b N η m) (hm1 : crossingAbscissa a b N η m ≤ (a * N : ℕ))
    (hn0 : 0 ≤ crossingAbscissa a b N η n) (hn1 : crossingAbscissa a b N η n ≤ (a * N : ℕ))
    (h : Int.fract (crossingAbscissa a b N η m) = Int.fract (crossingAbscissa a b N η n)) :
    m = n := by
  have hspos := sweepSlope_pos (a := a) (b := b) (N := N) ha hb hN
  have hs : 1 + sweepSlope a b N ≠ 0 := by linarith
  have hvm := one_add_sweepSlope_mul_crossingAbscissa (a := a) (b := b) (N := N) hs η m
  have hvn := one_add_sweepSlope_mul_crossingAbscissa (a := a) (b := b) (N := N) hs η n
  have hdiff : crossingAbscissa a b N η m - crossingAbscissa a b N η n =
      ((⌊crossingAbscissa a b N η m⌋ - ⌊crossingAbscissa a b N η n⌋ : ℤ) : ℚ) := by
    have h1 := Int.fract_add_floor (crossingAbscissa a b N η m)
    have h2 := Int.fract_add_floor (crossingAbscissa a b N η n)
    push_cast
    rw [Int.fract] at h
    linarith
  have hsd : sweepSlope a b N *
      ((⌊crossingAbscissa a b N η m⌋ - ⌊crossingAbscissa a b N η n⌋ : ℤ) : ℚ) =
      ((m - n - (⌊crossingAbscissa a b N η m⌋ - ⌊crossingAbscissa a b N η n⌋) : ℤ) : ℚ) := by
    push_cast at hdiff ⊢
    linear_combination hvm - hvn - (1 + sweepSlope a b N) * hdiff
  have hdvd := dvd_of_sweepSlope_mul_int (b := b) ha hN hsd
  have hbound : |⌊crossingAbscissa a b N η m⌋ - ⌊crossingAbscissa a b N η n⌋| <
      (((a * N + 1) * N : ℕ) : ℤ) := by
    have h1 : ((⌊crossingAbscissa a b N η m⌋ - ⌊crossingAbscissa a b N η n⌋ : ℤ) : ℚ)
        ≤ ((a * N : ℕ) : ℚ) := by rw [← hdiff]; linarith
    have h2 : -((a * N : ℕ) : ℚ) ≤
        ((⌊crossingAbscissa a b N η m⌋ - ⌊crossingAbscissa a b N η n⌋ : ℤ) : ℚ) := by
      rw [← hdiff]; linarith
    have h1' : ⌊crossingAbscissa a b N η m⌋ - ⌊crossingAbscissa a b N η n⌋
        ≤ ((a * N : ℕ) : ℤ) := by exact_mod_cast h1
    have h2' : -((a * N : ℕ) : ℤ) ≤
        ⌊crossingAbscissa a b N η m⌋ - ⌊crossingAbscissa a b N η n⌋ := by exact_mod_cast h2
    have hMbig : ((a * N : ℕ) : ℤ) < (((a * N + 1) * N : ℕ) : ℤ) := by
      have hone : (a * N + 1) * 1 ≤ (a * N + 1) * N := Nat.mul_le_mul_left _ hN
      have h2n : a * N < (a * N + 1) * N := by omega
      exact_mod_cast h2n
    rw [abs_lt]
    omega
  have hd0 : ⌊crossingAbscissa a b N η m⌋ - ⌊crossingAbscissa a b N η n⌋ = 0 :=
    Int.eq_zero_of_abs_lt_dvd hdvd hbound
  have hfin : ((m - n : ℤ) : ℚ) = 0 := by
    have hxx : crossingAbscissa a b N η m = crossingAbscissa a b N η n := by
      have h0 := hdiff
      rw [hd0] at h0
      push_cast at h0
      linarith
    push_cast
    rw [← hvm, ← hvn, hxx]
    ring
  have hmn0 : (m : ℤ) - n = 0 := by exact_mod_cast hfin
  omega

/-! ### The components lie inside the rectangle -/

/-- **A component ends inside the rectangle.** The level line reaches the ordinate `bN` only past
the abscissa `aN`, because `η > aN`; so the abscissa at which it reaches the ordinate of any east
step — at most `bN` — is at most `aN`. This is the bound the distinctness argument spends. -/
theorem componentRight_le (ha : 0 < a) (hb : 0 < b) (hN : 0 < N) {η : ℚ}
    (hηa : ((a * N : ℕ) : ℚ) < η) (y : Heights a b N) (i : ℕ)
    (hi : (((sortByColumn (colouringEast y η)).getD i (0, 0)).2 : ℚ) ≤ ((b * N : ℕ) : ℚ)) :
    componentRight a b N y η i ≤ ((a * N : ℕ) : ℚ) := by
  have hspos := sweepSlope_pos (a := a) (b := b) (N := N) ha hb hN
  have ha' : (0 : ℚ) < a := by exact_mod_cast ha
  have hN' : (0 : ℚ) < N := by exact_mod_cast hN
  have hMa : (0 : ℚ) < (a : ℚ) * ((a : ℚ) * N + 1) * N := by positivity
  -- the level line at abscissa `aN` is above `bN`
  have hid : sweepSlope a b N * ((a * N : ℕ) : ℚ) + levelIntercept a N η
      = ((b * N : ℕ) : ℚ) + (η - ((a * N : ℕ) : ℚ)) / ((a : ℚ) * ((a : ℚ) * N + 1) * N) := by
    rw [sweepSlope, levelIntercept]
    field_simp
    push_cast
    ring
  have hline : ((b * N : ℕ) : ℚ) <
      sweepSlope a b N * ((a * N : ℕ) : ℚ) + levelIntercept a N η := by
    rw [hid]
    have : 0 < (η - ((a * N : ℕ) : ℚ)) / ((a : ℚ) * ((a : ℚ) * N + 1) * N) :=
      div_pos (by linarith) hMa
    linarith
  rw [componentRight, div_le_iff₀ hspos]
  linarith

end HJO.Mellit
