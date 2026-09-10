/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Mathlib.Algebra.MvPolynomial.PDeriv
public meta import HJO.Attr
public import HJO.Defs

/-! # The split of a slope, the slope operators and the differential-order filtration

The split `Split m n` of a slope is defined by a search with a default value, and the slope
operators `Qop` through a recursion fuelled by a counter. This file proves that on the domain of
the recursion neither the default nor the exhaustion of the fuel is reached, and reads off the
unfolding equations that result.

For the split: the search succeeds on the interior of the coprime domain instead of falling
through to its default, both halves of a split are again coprime, so the recursion stays inside
the primitive regime, and the first entries of the two halves lie in `[1, m - 1]`, so the
subtractions forming the complement are genuine rather than truncated. The same bounds hold for
`primitiveSplit` and for `slopeSplit`.

For the slope operators: any two amounts of fuel that reach the base case compute the same
operator, so `QopPrim` satisfies the two-term recursion in the halves of `Split m n`, and `Qop`
is `D_n` at width one, that same recursion at a coprime slope, and the normalised commutator of
the two halves of `slopeSplit m n` at a noncoprime one.

The remaining sections define the evaluation map `Phi` attached to a slope homomorphism with its
coefficients `phiCoeff` on the power sums, the partial derivatives `pderivEnd` of the ring of
symmetric functions with the spanning-set predicate `HasDiffOrderAtMost` for the differential
order, and the order-filtered algebra `Rees` of the operators admitting an expansion in
`ℏ = 1 - u` whose coefficient of `ℏ ^ j` has differential order at most `j`.
-/

@[expose] public section

open Finset

namespace HJO.Sym

/-! ### The split of a slope: the search succeeds, the bounds, and coprimality -/

/-- Whatever the search list of `Split m n` contains, if it is nonempty -- witnessed here by a
member `p` -- then `Split m n` is one of its members, so it satisfies all four conditions the
search filters on. This is the statement that the totalized default is not reached. -/
theorem split_props {m n : ℕ} {p : ℕ × ℕ}
    (hp : p ∈ (List.range m ×ˢ List.range n).filter
      fun p => 1 ≤ p.1 ∧ 1 ≤ p.2 ∧ m * p.2 + 1 = n * p.1) :
    1 ≤ (Split m n).1 ∧ 1 ≤ (Split m n).2 ∧ (Split m n).1 < m ∧ (Split m n).2 < n ∧
      m * (Split m n).2 + 1 = n * (Split m n).1 := by
  rw [Split]
  rcases hl : (List.range m ×ˢ List.range n).filter
      (fun p => 1 ≤ p.1 ∧ 1 ≤ p.2 ∧ m * p.2 + 1 = n * p.1) with _ | ⟨x, xs⟩
  · rw [hl] at hp; simp at hp
  · have hx : (x.1, x.2) ∈ (List.range m ×ˢ List.range n).filter
        (fun p => 1 ≤ p.1 ∧ 1 ≤ p.2 ∧ m * p.2 + 1 = n * p.1) := by
      rw [hl]; exact List.mem_cons_self ..
    rw [List.mem_filter, List.mem_product, List.mem_range, List.mem_range,
      decide_eq_true_eq] at hx
    rw [hl]
    exact ⟨hx.2.1, hx.2.2.1, hx.1.1, hx.1.2, hx.2.2.2⟩

/-- The value of `Split m n` when the search finds nothing: its default `(1, 0)`. -/
theorem split_default {m n : ℕ}
    (hl : (List.range m ×ˢ List.range n).filter
      (fun p => 1 ≤ p.1 ∧ 1 ≤ p.2 ∧ m * p.2 + 1 = n * p.1) = []) : Split m n = (1, 0) := by
  rw [Split, hl]; rfl

/-- The first entry of `Split m n` is at least `1`, on a search hit and on the default alike. -/
theorem one_le_split_fst (m n : ℕ) : 1 ≤ (Split m n).1 := by
  rcases hl : (List.range m ×ˢ List.range n).filter
      (fun p => 1 ≤ p.1 ∧ 1 ≤ p.2 ∧ m * p.2 + 1 = n * p.1) with _ | ⟨x, xs⟩
  · rw [split_default hl]
  · exact (split_props (p := x) (by rw [hl]; exact List.mem_cons_self ..)).1

/-- The first entry of `Split m n` is less than `m` as soon as `m > 1`: a search hit lies in
`List.range m`, and the default `(1, 0)` has first entry `1`. -/
theorem split_fst_lt {m : ℕ} (n : ℕ) (hm : 1 < m) : (Split m n).1 < m := by
  rcases hl : (List.range m ×ˢ List.range n).filter
      (fun p => 1 ≤ p.1 ∧ 1 ≤ p.2 ∧ m * p.2 + 1 = n * p.1) with _ | ⟨x, xs⟩
  · rw [split_default hl]; exact hm
  · exact (split_props (p := x) (by rw [hl]; exact List.mem_cons_self ..)).2.2.1

/-- The clamp of `splitFst` is inactive: for `m > 1` it returns exactly `(Split m n).1`. -/
theorem splitFst_eq {m : ℕ} (n : ℕ) (hm : 1 < m) : splitFst m n = (Split m n).1 := by
  have h1 := one_le_split_fst m n
  have h2 := split_fst_lt n hm
  rw [splitFst]
  omega

/-- On the interior of the coprime domain a split exists: `b` is invertible modulo `a`, and its
inverse taken in `[1, a - 1]` is the first entry, the second being the quotient it forces. -/
theorem exists_split {a b : ℕ} (ha : 1 < a) (hb : 1 < b) (hab : Nat.Coprime a b) :
    ∃ r s : ℕ, r < a ∧ s < b ∧ 1 ≤ r ∧ 1 ≤ s ∧ a * s + 1 = b * r := by
  obtain ⟨r, hra, hr⟩ := Nat.exists_mul_mod_eq_one_of_coprime hab.symm ha
  have hr1 : 1 ≤ r := by
    rcases Nat.eq_zero_or_pos r with rfl | h
    · simp at hr
    · exact h
  have hkey : a * (b * r / a) + 1 = b * r := by
    have h := Nat.div_add_mod (b * r) a
    rwa [hr] at h
  have hbr : b ≤ b * r := Nat.le_mul_of_pos_right b hr1
  have hle : b * (r + 1) ≤ b * a := Nat.mul_le_mul_left b hra
  have hmul : b * (r + 1) = b * r + b := by ring
  have hba : b * a = a * b := Nat.mul_comm _ _
  refine ⟨r, b * r / a, hra, ?_, hr1, ?_, hkey⟩
  · exact Nat.lt_of_mul_lt_mul_left (a := a) (by omega)
  · rcases Nat.eq_zero_or_pos (b * r / a) with h | h
    · rw [h, Nat.mul_zero] at hkey; omega
    · exact h

/-- Hence on the interior of the coprime domain the search of `Split` succeeds, and its result
is a genuine split: the default is not reached there. -/
theorem split_spec_interior {a b : ℕ} (ha : 1 < a) (hb : 1 < b) (hab : Nat.Coprime a b) :
    1 ≤ (Split a b).1 ∧ 1 ≤ (Split a b).2 ∧ (Split a b).1 < a ∧ (Split a b).2 < b ∧
      a * (Split a b).2 + 1 = b * (Split a b).1 := by
  obtain ⟨r, s, hr, hs, hr1, hs1, heq⟩ := exists_split ha hb hab
  refine split_props (p := (r, s)) ?_
  rw [List.mem_filter, List.mem_product, List.mem_range, List.mem_range, decide_eq_true_eq]
  exact ⟨⟨hr, hs⟩, hr1, hs1, heq⟩

/-- `Split m n` at a coprime slope with `m > 1`, the domain of the primitive recursion. The
second entry is only bounded above: at `n = 1` the source's split is `(1, 0)`, which is what
the empty search returns, and there the second entry is `0`. -/
theorem split_spec {m n : ℕ} (hm : 1 < m) (h : Nat.Coprime m n) :
    1 ≤ (Split m n).1 ∧ (Split m n).1 < m ∧ (Split m n).2 < n ∧
      m * (Split m n).2 + 1 = n * (Split m n).1 := by
  rcases Nat.lt_or_ge n 2 with hn | hn
  · interval_cases n
    · rw [Nat.coprime_zero_right] at h; omega
    · have hl : ((List.range m ×ˢ List.range 1).filter
          fun p => 1 ≤ p.1 ∧ 1 ≤ p.2 ∧ m * p.2 + 1 = 1 * p.1) = [] := by
        rw [List.filter_eq_nil_iff]
        rintro ⟨r, s⟩ hmem hpred
        rw [List.mem_product, List.mem_range, List.mem_range] at hmem
        simp only [decide_eq_true_eq] at hpred
        omega
      rw [split_default hl]
      exact ⟨le_refl 1, hm, Nat.zero_lt_one, by omega⟩
  · obtain ⟨h1, -, h3, h4, h5⟩ := split_spec_interior hm hn h
    exact ⟨h1, h3, h4, h5⟩

/-- A Bezout relation `c * y + 1 = d * x` makes `x` and `y` coprime: their greatest common
divisor divides both `d * x` and `c * y`, hence divides `1`. -/
theorem coprime_of_bezout {x y c d : ℕ} (h : c * y + 1 = d * x) : Nat.Coprime x y := by
  refine Nat.dvd_one.mp ?_
  have h1 : Nat.gcd x y ∣ d * x := (Nat.gcd_dvd_left x y).mul_left d
  have h2 : Nat.gcd x y ∣ c * y := (Nat.gcd_dvd_right x y).mul_left c
  have hsub : d * x - c * y = 1 := by omega
  simpa [hsub] using Nat.dvd_sub h1 h2

/-- Both halves of the split of a coprime slope are again coprime, so the primitive recursion
stays inside the coprime regime: it never reaches the noncoprime branch of `Qop`. -/
theorem coprime_halves_of_coprime {m n : ℕ} (hm : 1 < m) (h : Nat.Coprime m n) :
    Nat.Coprime (Split m n).1 (Split m n).2 ∧
      Nat.Coprime (m - (Split m n).1) (n - (Split m n).2) := by
  obtain ⟨hr1, hrm, hsn, heq⟩ := split_spec hm h
  refine ⟨coprime_of_bezout heq, ?_⟩
  have h1 : m * (n - (Split m n).2) + m * (Split m n).2 = m * n := by
    rw [← Nat.mul_add, Nat.sub_add_cancel (le_of_lt hsn)]
  have h2 : n * (m - (Split m n).1) + n * (Split m n).1 = n * m := by
    rw [← Nat.mul_add, Nat.sub_add_cancel (le_of_lt hrm)]
  have h3 : m * n = n * m := Nat.mul_comm _ _
  exact (coprime_of_bezout (c := n) (d := m) (by omega)).symm

/-- The primitive split of a positive coprime pair satisfies the source's split equation, its
first entry lies in `[1, a]` and its second in `[0, b - 1]`. -/
theorem primitiveSplit_spec {a b : ℕ} (ha : 0 < a) (hb : 0 < b) (hab : Nat.Coprime a b) :
    1 ≤ (primitiveSplit a b).1 ∧ (primitiveSplit a b).1 ≤ a ∧ (primitiveSplit a b).2 < b ∧
      a * (primitiveSplit a b).2 + 1 = b * (primitiveSplit a b).1 := by
  rw [primitiveSplit]
  split_ifs with h1 h2
  · subst h1; exact ⟨le_refl 1, le_refl 1, by omega, by omega⟩
  · subst h2; exact ⟨le_refl 1, by omega, Nat.zero_lt_one, by omega⟩
  · obtain ⟨k1, -, k3, k4, k5⟩ := split_spec_interior (by omega) (by omega) hab
    exact ⟨k1, le_of_lt k3, k4, k5⟩

/-- Away from the primitive width one the first entry of the primitive split is `< a`. -/
theorem primitiveSplit_fst_lt {a b : ℕ} (ha : 1 < a) (hb : 0 < b) (hab : Nat.Coprime a b) :
    (primitiveSplit a b).1 < a := by
  rw [primitiveSplit]
  split_ifs with h1 h2
  · omega
  · omega
  · exact (split_spec_interior ha (by omega) hab).2.2.1

/-- Away from the primitive height one the second entry of the primitive split is `≥ 1`. -/
theorem primitiveSplit_snd_pos {a b : ℕ} (ha : 0 < a) (hb : 1 < b) (hab : Nat.Coprime a b) :
    1 ≤ (primitiveSplit a b).2 := by
  rw [primitiveSplit]
  split_ifs with h1 h2
  · omega
  · omega
  · exact (split_spec_interior (by omega) hb hab).2.1

/-- The primitive normalisation of a noncoprime positive slope: it is `k` times a positive
coprime pair with `k ≥ 2`, and `slopeSplit` is the primitive split of that pair. -/
theorem exists_primitive {m n : ℕ} (hm : 1 < m) (hn : 0 < n) (h : ¬ Nat.Coprime m n) :
    ∃ k a b : ℕ, 2 ≤ k ∧ 0 < a ∧ 0 < b ∧ Nat.Coprime a b ∧ m = k * a ∧ n = k * b ∧
      slopeSplit m n = primitiveSplit a b := by
  have hk : 0 < Nat.gcd m n := Nat.gcd_pos_of_pos_left n (by omega)
  refine ⟨Nat.gcd m n, m / Nat.gcd m n, n / Nat.gcd m n, ?_,
    Nat.div_pos (Nat.le_of_dvd (by omega) (Nat.gcd_dvd_left m n)) hk,
    Nat.div_pos (Nat.le_of_dvd hn (Nat.gcd_dvd_right m n)) hk,
    Nat.coprime_div_gcd_div_gcd hk,
    (Nat.mul_div_cancel' (Nat.gcd_dvd_left m n)).symm,
    (Nat.mul_div_cancel' (Nat.gcd_dvd_right m n)).symm, rfl⟩
  rcases Nat.lt_or_ge (Nat.gcd m n) 2 with h2 | h2
  · exact absurd (show Nat.Coprime m n from by unfold Nat.Coprime; omega) h
  · exact h2

/-- The split of a noncoprime positive slope `(m, n)`: its first entry `r` lies in `[1, m - 1]`
and its second entry `s` is `< n`, so the complement `(m - r, n - s)` is formed by genuine
subtractions and again has first entry in `[1, m - 1]`; and both `(r, s)` and `(m - r, n - s)`
are coprime, the latter because `a * (n - s) - b * (m - r) = b * r - a * s = 1`. -/
theorem slopeSplit_spec {m n : ℕ} (hm : 1 < m) (hn : 0 < n) (h : ¬ Nat.Coprime m n) :
    1 ≤ (slopeSplit m n).1 ∧ (slopeSplit m n).1 < m ∧ (slopeSplit m n).2 < n ∧
      1 ≤ m - (slopeSplit m n).1 ∧ m - (slopeSplit m n).1 < m ∧
      Nat.Coprime (slopeSplit m n).1 (slopeSplit m n).2 ∧
      Nat.Coprime (m - (slopeSplit m n).1) (n - (slopeSplit m n).2) := by
  obtain ⟨k, a, b, hk2, ha, hb, hab, hmk, hnk, hsp⟩ := exists_primitive hm hn h
  obtain ⟨hr1, hra, hsb, heq⟩ := primitiveSplit_spec ha hb hab
  rw [hsp]
  have hka : 2 * a ≤ k * a := Nat.mul_le_mul_right a hk2
  have hkb : 1 * b ≤ k * b := Nat.mul_le_mul_right b (by omega)
  have hrm : (primitiveSplit a b).1 < m := by omega
  have hsn : (primitiveSplit a b).2 < n := by omega
  refine ⟨hr1, hrm, hsn, by omega, by omega, coprime_of_bezout heq, ?_⟩
  have h1 : a * (n - (primitiveSplit a b).2) + a * (primitiveSplit a b).2 = a * n := by
    rw [← Nat.mul_add, Nat.sub_add_cancel (le_of_lt hsn)]
  have h2 : b * (m - (primitiveSplit a b).1) + b * (primitiveSplit a b).1 = b * m := by
    rw [← Nat.mul_add, Nat.sub_add_cancel (le_of_lt hrm)]
  have h3 : a * n = b * m := by rw [hmk, hnk]; ring
  exact (coprime_of_bezout (c := b) (d := a) (by omega)).symm

/-! ### The slope operators and the evaluation map -/

section Field

variable {L : Type*} [Field L] [Algebra ℚ L]

omit [Algebra ℚ L] in
/-- The axis alphabet as a diagonal substitution, the form its coefficients are read off from. -/
theorem plethAxis_eq_diagScale (v : L) :
    plethAxis v = diagScale fun index => (v ^ (index + 1))⁻¹ - 1 := rfl

/-- The zero-fuel value of the fuelled recursion. -/
theorem qopAux_zero (q u : L) (m n : ℕ) : QopAux q u 0 m n = Dop q u n := rfl

/-- One step of the fuelled recursion. -/
theorem qopAux_succ_def (q u : L) (fuel m n : ℕ) :
    QopAux q u (fuel + 1) m n =
      if m ≤ 1 then Dop q u n
      else ((1 - q) * (1 - u))⁻¹ •
        (QopAux q u fuel (m - splitFst m n) (n - (Split m n).2) *
            QopAux q u fuel (splitFst m n) (Split m n).2 -
          QopAux q u fuel (splitFst m n) (Split m n).2 *
            QopAux q u fuel (m - splitFst m n) (n - (Split m n).2)) := rfl

/-- **Fuel to spare is fuel unused.** With at least `m - 1` units of fuel, one more unit changes
nothing: each half of the split of `(m, n)` has first entry in `[1, m - 1]`, so the recursion
that `m - 1` units of fuel can run to its base case is the same recursion. -/
theorem qopAux_succ (q u : L) : ∀ (fuel m n : ℕ), m ≤ fuel + 1 →
    QopAux q u (fuel + 1) m n = QopAux q u fuel m n := by
  intro fuel
  induction fuel with
  | zero =>
    intro m n hm
    rw [qopAux_succ_def, qopAux_zero]
    split_ifs with hm1
    · rfl
    · exact absurd hm hm1
  | succ fuel ih =>
    intro m n hm
    rw [qopAux_succ_def q u (fuel + 1) m n, qopAux_succ_def q u fuel m n]
    split_ifs with hm1
    · rfl
    · have h1 : 1 < m := by omega
      have hfst : splitFst m n = (Split m n).1 := splitFst_eq n h1
      have hb1 : 1 ≤ (Split m n).1 := one_le_split_fst m n
      have hb2 : (Split m n).1 < m := split_fst_lt n h1
      rw [ih (splitFst m n) _ (by rw [hfst]; omega),
        ih (m - splitFst m n) _ (by rw [hfst]; omega)]

/-- Any amount of fuel to spare is fuel unused. -/
theorem qopAux_add (q u : L) (fuel m n d : ℕ) (hm : m ≤ fuel + 1) :
    QopAux q u (fuel + d) m n = QopAux q u fuel m n := by
  induction d with
  | zero => rfl
  | succ d ih => rw [← Nat.add_assoc, qopAux_succ q u (fuel + d) m n (by omega), ih]

/-- **Sufficient fuel.** Any two fuel values that are at least `m - 1` compute the same
operator, so no evaluation with that much fuel reaches the zero-fuel fallback prematurely. -/
theorem qopAux_fuel_eq (q u : L) {fuel fuel' m n : ℕ} (h : m ≤ fuel + 1) (h' : m ≤ fuel' + 1) :
    QopAux q u fuel m n = QopAux q u fuel' m n := by
  rcases Nat.le_total fuel fuel' with hle | hle
  · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hle
    exact (qopAux_add q u fuel m n d h).symm
  · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hle
    exact qopAux_add q u fuel' m n d h'

/-- The primitive evaluator is the fuelled recursion at any sufficient amount of fuel. -/
theorem qopPrim_eq_qopAux (q u : L) {fuel : ℕ} (m n : ℕ) (h : m ≤ fuel + 1) :
    QopPrim q u m n = QopAux q u fuel m n :=
  qopAux_fuel_eq q u (Nat.le_succ m) h

/-- The base case of the primitive recursion, `Q_{1,n} = D_n`. -/
theorem qopPrim_of_le_one (q u : L) {m : ℕ} (n : ℕ) (hm : m ≤ 1) :
    QopPrim q u m n = Dop q u n := by
  rw [qopPrim_eq_qopAux q u (fuel := 0) m n (by omega), qopAux_zero]

/-- The recursive case of the primitive recursion, with the fuel discharged on both halves. -/
theorem qopPrim_of_one_lt (q u : L) {m : ℕ} (n : ℕ) (hm : 1 < m) :
    QopPrim q u m n = ((1 - q) * (1 - u))⁻¹ •
      (QopPrim q u (m - (Split m n).1) (n - (Split m n).2) *
          QopPrim q u (Split m n).1 (Split m n).2 -
        QopPrim q u (Split m n).1 (Split m n).2 *
          QopPrim q u (m - (Split m n).1) (n - (Split m n).2)) := by
  obtain ⟨j, rfl⟩ : ∃ j, m = j + 1 := ⟨m - 1, by omega⟩
  have h1 : 1 ≤ (Split (j + 1) n).1 := one_le_split_fst _ _
  have h2 : (Split (j + 1) n).1 < j + 1 := split_fst_lt n hm
  have hfst : splitFst (j + 1) n = (Split (j + 1) n).1 := splitFst_eq n hm
  rw [qopPrim_eq_qopAux q u (fuel := j) (Split (j + 1) n).1 (Split (j + 1) n).2 (by omega),
    qopPrim_eq_qopAux q u (fuel := j) (j + 1 - (Split (j + 1) n).1)
      (n - (Split (j + 1) n).2) (by omega),
    QopPrim, qopAux_succ_def]
  split_ifs with hj
  · exact absurd hj (by omega)
  · rw [hfst]

/-- The base case of `Qop`, which also fixes its two totalized values at `m = 0`. -/
theorem qop_of_le_one (q u : L) {m : ℕ} (n : ℕ) (hm : m ≤ 1) : Qop q u m n = Dop q u n := by
  rw [Qop]
  split_ifs
  rfl

/-- `Q_{1,n} = D_n`, including the boundary operator `Q_{1,0} = D_0`. -/
theorem qop_one (q u : L) (n : ℕ) : Qop q u 1 n = Dop q u n := qop_of_le_one q u n (le_refl 1)

/-- **Agreement on coprime input**: at a coprime slope `Qop` is the primitive evaluator. -/
theorem qop_eq_qopPrim (q u : L) {m n : ℕ} (h : Nat.Coprime m n) :
    Qop q u m n = QopPrim q u m n := by
  rw [Qop]
  split_ifs with h1
  · rw [qopPrim_of_le_one q u n h1]
  · rfl

/-- The noncoprime branch of `Qop`, as evaluated. -/
theorem qop_of_not_coprime (q u : L) {m n : ℕ} (hm : 1 < m) (h : ¬ Nat.Coprime m n) :
    Qop q u m n = ((1 - q) * (1 - u))⁻¹ •
      (QopPrim q u (m - (slopeSplit m n).1) (n - (slopeSplit m n).2) *
          QopPrim q u (slopeSplit m n).1 (slopeSplit m n).2 -
        QopPrim q u (slopeSplit m n).1 (slopeSplit m n).2 *
          QopPrim q u (m - (slopeSplit m n).1) (n - (slopeSplit m n).2)) := by
  rw [Qop]
  split_ifs with h1
  · exact absurd h1 (by omega)
  · rfl

/-- **The source's noncoprime extension at `v = 1`, in terms of the slope operators
themselves.** Both halves of `slopeSplit m n` are coprime, so the primitive evaluators
appearing in the definition are the slope operators of those two slopes. -/
theorem qop_eq_bracket (q u : L) {m n : ℕ} (hm : 1 < m) (hn : 0 < n) (h : ¬ Nat.Coprime m n) :
    Qop q u m n = ((1 - q) * (1 - u))⁻¹ •
      (Qop q u (m - (slopeSplit m n).1) (n - (slopeSplit m n).2) *
          Qop q u (slopeSplit m n).1 (slopeSplit m n).2 -
        Qop q u (slopeSplit m n).1 (slopeSplit m n).2 *
          Qop q u (m - (slopeSplit m n).1) (n - (slopeSplit m n).2)) := by
  obtain ⟨-, -, -, -, -, hc1, hc2⟩ := slopeSplit_spec hm hn h
  rw [qop_eq_qopPrim q u hc1, qop_eq_qopPrim q u hc2, qop_of_not_coprime q u hm h]

/-- **The source's primitive recursion, in terms of the slope operators themselves.** -/
theorem qop_of_coprime (q u : L) {m n : ℕ} (hm : 1 < m) (h : Nat.Coprime m n) :
    Qop q u m n = ((1 - q) * (1 - u))⁻¹ •
      (Qop q u (m - (Split m n).1) (n - (Split m n).2) *
          Qop q u (Split m n).1 (Split m n).2 -
        Qop q u (Split m n).1 (Split m n).2 *
          Qop q u (m - (Split m n).1) (n - (Split m n).2)) := by
  obtain ⟨hc1, hc2⟩ := coprime_halves_of_coprime hm h
  rw [qop_eq_qopPrim q u hc1, qop_eq_qopPrim q u hc2, qop_eq_qopPrim q u h,
    qopPrim_of_one_lt q u n hm]

end Field

section Evaluation

variable {L : Type*} [Field L] [Algebra ℚ L] {F : Type*} [CommRing F]

/-- The evaluation map attached to a slope homomorphism `Θ` at `(a, b)`: on the part of `f`
of degree `N` (the degree in which `p_k` counts for `k`) it is `(-1) ^ (N * (b + 1))` times
the sign extraction of `Θ f` applied to `1`, specialised at `u = 1`, and it is extended
additively over the homogeneous parts. The specialisation is supplied as the ring
homomorphism `spec`, since on `ℚ(q, u)` setting `u = 1` is defined only on the elements
regular there. -/
@[hjo "def_phi"]
noncomputable def Phi (b : ℕ) (spec : L →+* F) (Θ : Lambda L →ₐ[L] Module.End L (Lambda L))
    (f : Lambda L) : F :=
  ∑ N ∈ range (MvPolynomial.weightedTotalDegree (fun i => i + 1) f + 1),
    (-1) ^ (N * (b + 1)) * signExtract F (MvPolynomial.map spec
      (Θ (MvPolynomial.weightedHomogeneousComponent (fun i => i + 1) N f) 1))

/-- The evaluation coefficient `r_k`, the value of the evaluation map on the power sum
`p_k`. -/
@[hjo "def_phi_coeff"]
noncomputable def phiCoeff (b : ℕ) (spec : L →+* F)
    (Θ : Lambda L →ₐ[L] Module.End L (Lambda L)) (k : ℕ) : F :=
  Phi b spec Θ (powerSum L k)

end Evaluation

/-! ### The differential order filtration -/

section Order

variable (K : Type*) [CommRing K]

/-- The partial derivative with respect to the generator `p_{i+1}`, as a `K`-linear
endomorphism of `Lambda K`. -/
noncomputable def pderivEnd (i : ℕ) : Module.End K (Lambda K) :=
  (MvPolynomial.pderiv i).toLinearMap

end Order

section OrderProp

variable {K : Type*} [CommRing K]

/-- A `K`-linear endomorphism of `Lambda K` has differential order at most `n` when it lies
in the `Lambda K`-module generated by the iterated partial derivatives
`∂ʲ / ∂p_{i₁} ⋯ ∂p_{iⱼ}` with `j ≤ n`, spelled out here as the `K`-span of the products of
such a derivative with a multiplication operator.

Everything this predicate recognises has differential order at most `n` in the commutator sense of
`HJO.DiffOrder.HasDiffOrder`, which is the coarser measure the filtration arguments use. -/
def HasDiffOrderAtMost (n : ℕ) (P : Module.End K (Lambda K)) : Prop :=
  P ∈ Submodule.span K {Q : Module.End K (Lambda K) | ∃ (f : Lambda K) (l : List ℕ),
    l.length ≤ n ∧ Q = LinearMap.mulLeft K f * (l.map (pderivEnd K)).prod}

end OrderProp

section Rees

variable {L : Type*} [Field L]

/-- The order-filtered algebra of operators: those `P` admitting an expansion
`P = ∑_{j ≥ 0} ℏ ^ j * P j` in `ℏ = 1 - u` with `P j` of differential order at most `j`.
Convergence on each fixed symmetric function is rendered as termination there: for every
`f`, all but finitely many `P j` kill `f` and `P f` is the resulting finite sum. The
requirement that the coefficients `P j` be free of `u` is not tracked; the refinement that does
track them over a coefficient ring is `HJO.DiffOrder.ReesRegComm`. -/
def Rees (u : L) : Set (Module.End L (Lambda L)) :=
  {P | ∃ Q : ℕ → Module.End L (Lambda L), (∀ j, HasDiffOrderAtMost j (Q j)) ∧
    ∀ f : Lambda L, ∃ N : ℕ, (∀ j, N ≤ j → Q j f = 0) ∧
      P f = ∑ j ∈ range N, (1 - u) ^ j • Q j f}

end Rees

end HJO.Sym
