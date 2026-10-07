/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Mathlib.Data.Nat.ModEq
public import Mathlib.Data.Nat.GCD.Basic
public import Mathlib.Data.List.Basic
public import Mathlib.Tactic.Ring
public meta import HJO.Attr

/-! # Mellit's slope word

Mellit's Section 6 reads the slope `b/a` line on the torus as a trajectory that crosses a vertical
wall (the letter `z`) or a horizontal wall (the letter `y`) at each step, and records the sequence
of crossings as a word `β_{m,n}` in two letters. The trajectory reduces to a
residue: with `M := m + n`, one step subtracts `m` modulo `M`, so the wall crossed after `i` steps
is determined by `ϱ_{m,n}(i)`, the representative of `i·m` modulo `M` in `{1, …, M-1}`. This file
is that arithmetic: the residue, the two-letter alphabet, the word, and the three small facts about
them that the recursion of `HJO.Mellit.euclid` rests on.

## Main definitions

* `HJO.Mellit.slopeResidue`: the slope residue `ϱ_{m,n}(i)`.
* `HJO.Mellit.SlopeLetter`: the two-letter alphabet `{y, z}`, the free generators of the monoid the
  slope word lives in — a `List SlopeLetter` *is* an element of that free monoid.
* `HJO.Mellit.slopeLetter`: the letter `λ(i)`.
* `HJO.Mellit.slopeWord`: the slope word `β_{m,n}`.

## Main results

* `HJO.Mellit.eq_slopeResidue_iff`: the closed formula below *is* the unique `r`, which
  is the existence-and-uniqueness content of `HJO.Mellit.slopeResidue`.
* `HJO.Mellit.slopeResidue_ne`: `ϱ_{m,n}(i) ≠ n` for
  `1 ≤ i ≤ m+n-2`.
* `HJO.Mellit.slopeWord_one_left`: `β_{1,n} = y^{n-1}`.
* `HJO.Mellit.slopeWord_one_right`: `β_{m,1} = z^{m-1}`.

## Implementation notes

Everything is over `ℕ`, not `ℤ`. The natural setting is the integers, but `m`, `n`, `i` and the
residue are all positive wherever the library reads them, and `Nat.mod` already returns the
representative in `{0, …, M-1}`; over `ℤ` the same definition would need `Int.emod` and a further
argument that the representative is non-negative. The price is truncated subtraction in `m + n - 1`
and `m + n - 2`, which is harmless: the standing hypotheses `1 ≤ m` and `1 ≤ n` give `m + n ≥ 2`, so
both subtractions are exact.

`slopeResidue` and `slopeWord` are **total**: they take no hypotheses, per the convention of
`HJO.Mellit.sbParent` and `HJO.Sym.Split`, and the range and congruence facts that the definition
as usually written folds into the phrase "the unique integer `r`" are theorems — `slopeResidue_le`,
`one_le_slopeResidue`, `slopeResidue_modEq`, and the two of them together with uniqueness in
`eq_slopeResidue_iff`. The closed formula `i * m % (m + n)` lands in `{0, …, M-1}` and the
definition wants `{1, …, M-1}`; the two agree exactly because the residue is never `0` in range,
which is `one_le_slopeResidue` and needs the coprimality.

`slopeLetter` is the total two-way test `if ϱ < n then y else z`. The `λ` is given by the two cases
`ϱ < n` and `ϱ > n`, which are exhaustive only by `HJO.Mellit.slopeResidue_ne`; a Lean function must
decide the excluded case `ϱ = n` as well, and the fallback here sends it to `z`. That branch is
unreachable on the range `1 ≤ i ≤ m+n-2` that `slopeWord` uses, so the definition agrees with the
`λ` there, and `slopeResidue_top` records that it is the *only* unreachable case: at `i = m+n-1` the
residue is exactly `n`.

The order is load-bearing, since `HJO.Sweep.slopeOperator` composes the factors "in the order in
which they are written": the head of `slopeWord m n` is `λ(m+n-2)` and its last letter is `λ(1)`.
That is pinned by `getElem_slopeWord` together with `length_slopeWord`, and checked outright on two
examples, `slopeWord_three_two` and `slopeWord_two_three`.

## References

The slope word: the definitions `HJO.Mellit.slopeResidue` and `HJO.Mellit.slopeWord`, and the lemmas
`HJO.Mellit.slopeResidue_ne`, `HJO.Mellit.slopeWord_one_left` and `HJO.Mellit.slopeWord_one_right`.
`HJO.Mellit.slopeWord_mediant` and `HJO.Mellit.slopeWord_mediant_rev` are not here.
-/

@[expose] public section

namespace HJO.Mellit

/-! ### The slope residue -/

/-- **The slope residue `ϱ_{m,n}(i)`.** The representative of `i·m` modulo `m + n` lying in
`{1, …, m+n-1}`, given by the closed formula `i * m % (m + n)`.

The definition as usually stated asks for the *unique* integer `r` with `1 ≤ r ≤ m+n-1`
and `r ≡ i·m (mod m+n)`; it exists and is unique because `gcd(m, m+n) = gcd(m, n) = 1`, so `m + n`
divides `i·m` only when it divides `i`, which it does not for `1 ≤ i ≤ m+n-1`. This definition is
total and takes no hypotheses: `Nat.mod` returns the representative in `{0, …, m+n-1}`, and it is
never `0` in that range for coprime `m, n ≥ 1` (`one_le_slopeResidue`), which is exactly why the
formula and the `r` agree. That agreement, in both directions, is
`eq_slopeResidue_iff`. -/
@[hjo "def_mellit_slope_residue"]
def slopeResidue (m n i : ℕ) : ℕ := i * m % (m + n)

/-- The slope residue is congruent to `i·m` modulo `m + n`. -/
theorem slopeResidue_modEq (m n i : ℕ) : slopeResidue m n i ≡ i * m [MOD m + n] :=
  Nat.mod_modEq _ _

/-- The slope residue is less than `m + n`. -/
theorem slopeResidue_lt {m n : ℕ} (hM : 0 < m + n) (i : ℕ) : slopeResidue m n i < m + n :=
  Nat.mod_lt _ hM

/-- The slope residue is at most `m + n - 1`, the upper end of the range. -/
theorem slopeResidue_le {m n : ℕ} (hM : 0 < m + n) (i : ℕ) : slopeResidue m n i ≤ m + n - 1 :=
  Nat.le_sub_one_of_lt (slopeResidue_lt hM i)

/-- The slope residue is at least `1`, the lower end of the range. This is where
coprimality enters: were the residue `0`, then `m + n` would divide `i·m`, hence `i`, as
`gcd(m + n, m) = gcd(n, m) = 1`, and `1 ≤ i ≤ m+n-1` forbids that. -/
theorem one_le_slopeResidue {m n i : ℕ} (hmn : Nat.Coprime m n) (hm : 1 ≤ m) (hn : 1 ≤ n)
    (hi1 : 1 ≤ i) (hi2 : i ≤ m + n - 1) : 1 ≤ slopeResidue m n i := by
  rcases Nat.eq_zero_or_pos (slopeResidue m n i) with h | h
  · have hcop : Nat.Coprime (m + n) m := (Nat.coprime_self_add_right.mpr hmn).symm
    have hd : (m + n) ∣ i := hcop.dvd_of_dvd_mul_right (Nat.dvd_of_mod_eq_zero h)
    have := Nat.le_of_dvd hi1 hd
    omega
  · exact h

/-- **`slopeResidue` is the unique residue.** For coprime `m, n ≥ 1` and
`1 ≤ i ≤ m+n-1`, a natural number `r` equals `ϱ_{m,n}(i)` exactly when it satisfies the three
conditions of `HJO.Mellit.slopeResidue`. The forward direction is existence, the backward one
uniqueness, so this single statement carries the whole content of the "the unique
integer `r`". -/
@[hjo "def_mellit_slope_residue"]
theorem eq_slopeResidue_iff {m n i r : ℕ} (hmn : Nat.Coprime m n) (hm : 1 ≤ m) (hn : 1 ≤ n)
    (hi1 : 1 ≤ i) (hi2 : i ≤ m + n - 1) :
    r = slopeResidue m n i ↔ 1 ≤ r ∧ r ≤ m + n - 1 ∧ r ≡ i * m [MOD m + n] := by
  constructor
  · rintro rfl
    exact ⟨one_le_slopeResidue hmn hm hn hi1 hi2, slopeResidue_le (by omega) i,
      slopeResidue_modEq m n i⟩
  · rintro ⟨hr1, hr2, hr⟩
    rw [Nat.ModEq] at hr
    rw [slopeResidue, ← hr, Nat.mod_eq_of_lt (by omega)]

/-- **The slope residue avoids the threshold.** `HJO.Mellit.slopeResidue_ne`:
for coprime `m, n ≥ 1` and `1 ≤ i ≤ m+n-2`, `ϱ_{m,n}(i) ≠ n`. Writing `M = m + n`, if
`ϱ_{m,n}(i) = n` then `i·m ≡ n ≡ -m (mod M)`, so `M ∣ (i+1)m`; as `gcd(m, M) = 1` this gives
`M ∣ i + 1`, while `1 ≤ i + 1 ≤ M - 1`.

The bound `i ≤ m+n-2` is sharp, not a slip: `slopeResidue_top` shows the residue *is* `n` at the
one further index `i = m+n-1` allowed by `HJO.Mellit.slopeResidue`. -/
@[hjo "lem_mellit_slope_residue_ne"]
theorem slopeResidue_ne {m n i : ℕ} (hmn : Nat.Coprime m n) (hm : 1 ≤ m) (hn : 1 ≤ n)
    (hi1 : 1 ≤ i) (hi2 : i ≤ m + n - 2) : slopeResidue m n i ≠ n := by
  intro h
  have h0 : (i + 1) * m % (m + n) = 0 := by
    have e : (i + 1) * m = i * m + m := by ring
    rw [e, Nat.add_mod, ← slopeResidue, h, Nat.mod_eq_of_lt (show m < m + n by omega),
      Nat.add_comm n m, Nat.mod_self]
  have hcop : Nat.Coprime (m + n) m := (Nat.coprime_self_add_right.mpr hmn).symm
  have hdvd : (m + n) ∣ i + 1 := hcop.dvd_of_dvd_mul_right (Nat.dvd_of_mod_eq_zero h0)
  have := Nat.le_of_dvd (by omega) hdvd
  omega

/-- **The threshold is attained at the top of the range.** For `m, n ≥ 1`,
`ϱ_{m,n}(m+n-1) = n`, because `(M-1)m ≡ -m ≡ n (mod M)`. So the index range `1 ≤ i ≤ m+n-2` of
`HJO.Mellit.slopeResidue_ne` is exactly right: at the remaining index of
`HJO.Mellit.slopeResidue`'s range the conclusion fails. `slopeWord` never reads that index. -/
theorem slopeResidue_top {m n : ℕ} (hm : 1 ≤ m) (hn : 1 ≤ n) :
    slopeResidue m n (m + n - 1) = n := by
  obtain ⟨p, rfl⟩ : ∃ p, m = p + 1 := ⟨m - 1, by omega⟩
  have e : (p + 1 + n - 1) * (p + 1) = (p + 1 + n) * (p + 1 - 1) + n := by
    have h1 : p + 1 + n - 1 = p + n := by omega
    have h2 : p + 1 - 1 = p := by omega
    rw [h1, h2]; ring
  rw [slopeResidue, e, Nat.mul_add_mod, Nat.mod_eq_of_lt (by omega)]

/-! ### The slope word -/

/-- The two letters `y` and `z` of the free monoid the slope word lives in. A word in that monoid
is a `List SlopeLetter`, concatenation being `List.append`. -/
inductive SlopeLetter where
  /-- The letter `y`, recording a crossing of the horizontal wall of the torus. -/
  | y : SlopeLetter
  /-- The letter `z`, recording a crossing of the vertical wall of the torus. -/
  | z : SlopeLetter
  deriving DecidableEq

/-- The letter `λ(i)` of `HJO.Mellit.slopeWord`: `y` if `ϱ_{m,n}(i) < n`, and `z` otherwise.

The two cases are `ϱ_{m,n}(i) < n` and `ϱ_{m,n}(i) > n`; they are exhaustive only by
`slopeResidue_ne`, so this total function must also decide `ϱ_{m,n}(i) = n`, and the fallback
branch sends that case to `z`. On the range `1 ≤ i ≤ m+n-2` used by `slopeWord` the fallback is
unreachable, so this agrees with the `λ` throughout. -/
def slopeLetter (m n i : ℕ) : SlopeLetter :=
  if slopeResidue m n i < n then .y else .z

/-- **The slope word `β_{m,n}`.** `HJO.Mellit.slopeWord`: the word
`λ(m+n-2) λ(m+n-3) ⋯ λ(1)` in the free monoid on `y` and `z`, as a list whose head is `λ(m+n-2)`
and whose last letter is `λ(1)`.

The letters are listed in *decreasing* order of `i`, the reverse of the order in which the
crossings happen, because `HJO.Braid.braidWord` puts the factor of the earliest move rightmost, and
`HJO.Sweep.slopeOperator` composes the factors in the order in which they are written. That
order is stated by `getElem_slopeWord`. The definition is total: outside the coprime
`m, n ≥ 1` it is still a list, of length `m + n - 2` with truncated subtraction, and it is `[]`
whenever `m + n ≤ 2`. -/
@[hjo "def_mellit_slope_word"]
def slopeWord (m n : ℕ) : List SlopeLetter :=
  (List.range (m + n - 2)).map fun j => slopeLetter m n (m + n - 2 - j)

/-- The slope word has length `m + n - 2`, one letter for each index `1 ≤ i ≤ m+n-2`. -/
theorem length_slopeWord (m n : ℕ) : (slopeWord m n).length = m + n - 2 := by
  simp [slopeWord]

/-- The order of the letters of the slope word: the letter at position `j` is `λ(m+n-2-j)`, so the
head is `λ(m+n-2)` and the last letter is `λ(1)`. -/
theorem getElem_slopeWord (m n j : ℕ) (hj : j < (slopeWord m n).length) :
    (slopeWord m n)[j] = slopeLetter m n (m + n - 2 - j) := by
  simp [slopeWord]

/-- **The slope word of a unit denominator.** `HJO.Mellit.slopeWord_one_left`:
`β_{1,n} = y^{n-1}` for `n ≥ 1`. Here `M = 1 + n` and `m = 1`, so for `1 ≤ i ≤ n-1` the residue of
`i·m = i` modulo `M` is `i` itself, and `i ≤ n-1 < n`; every letter is therefore `y`, and there are
`M - 2 = n - 1` of them. -/
@[hjo "lem_mellit_slope_word_y"]
theorem slopeWord_one_left {n : ℕ} (hn : 1 ≤ n) : slopeWord 1 n = List.replicate (n - 1) .y := by
  rw [List.eq_replicate_iff]
  refine ⟨by rw [length_slopeWord]; omega, ?_⟩
  intro b hb
  simp only [slopeWord, List.mem_map, List.mem_range] at hb
  obtain ⟨j, hj, rfl⟩ := hb
  have hres : slopeResidue 1 n (1 + n - 2 - j) = 1 + n - 2 - j := by
    rw [slopeResidue, mul_one]
    exact Nat.mod_eq_of_lt (by omega)
  rw [slopeLetter, hres, ite_eq_left (show 1 + n - 2 - j < n by omega)]

/-- **The slope word of a unit numerator.** `HJO.Mellit.slopeWord_one_right`:
`β_{m,1} = z^{m-1}` for `m ≥ 1`. Here `M = m + 1` and `n = 1`, so `ϱ_{m,1}(i) ≠ 1` for
`1 ≤ i ≤ m-1` by `slopeResidue_ne`, whence `ϱ_{m,1}(i) > 1 = n` and every letter is `z`; there are
`M - 2 = m - 1` of them. -/
@[hjo "lem_mellit_slope_word_z"]
theorem slopeWord_one_right {m : ℕ} (hm : 1 ≤ m) : slopeWord m 1 = List.replicate (m - 1) .z := by
  rw [List.eq_replicate_iff]
  refine ⟨by rw [length_slopeWord]; omega, ?_⟩
  intro b hb
  simp only [slopeWord, List.mem_map, List.mem_range] at hb
  obtain ⟨j, hj, rfl⟩ := hb
  have hne : slopeResidue m 1 (m + 1 - 2 - j) ≠ 1 :=
    slopeResidue_ne (Nat.coprime_one_right m) hm le_rfl (by omega) (by omega)
  have hpos : 1 ≤ slopeResidue m 1 (m + 1 - 2 - j) :=
    one_le_slopeResidue (Nat.coprime_one_right m) hm le_rfl (by omega) (by omega)
  rw [slopeLetter, ite_eq_right (show ¬ slopeResidue m 1 (m + 1 - 2 - j) < 1 by omega)]

/-- `β_{3,2} = z y z`, computed outright. Both the letters and their order are pinned: with
`M = 5` the residues of `1·3, 2·3, 3·3` are `3, 1, 4`, so `λ(1) = z`, `λ(2) = y`, `λ(3) = z`, and
the word lists them as `λ(3) λ(2) λ(1)`. -/
theorem slopeWord_three_two : slopeWord 3 2 = [.z, .y, .z] := by decide

/-- `β_{2,3} = y z y`, computed outright — the mirror of `slopeWord_three_two`, and the value
`HJO.Mellit.slopeWord_mediant` predicts from `β_{1,1} y z β_{1,2}`. -/
theorem slopeWord_two_three : slopeWord 2 3 = [.y, .z, .y] := by decide

end HJO.Mellit
