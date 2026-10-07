/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.Symmetric.SymmetricFunctions
public meta import HJO.Attr

/-! # The split of a slope under the two Euclidean steps

The collinear commutation argument moves along the lattice by the two steps
`(a, b) ↦ (a + b, b)` and `(a, b) ↦ (a, a + b)`, and at each step it has to know what the split
of the moved slope is. This file answers that: the split equation has at most one solution, so
the bounded search of `Sym.Split` is pinned by exhibiting a solution, and the primitive split
transforms as `(r, s) ↦ (r + s, s)` under the first step and `(r, s) ↦ (r, r + s)` under the
second.

Alongside that it records the three facts about the split of a general slope `(m, n)` with
`m ≥ 2` and `n ≥ 1` that every induction along the recursion of `Sym.Qop` needs: the first entry
`r` lies in `[1, m - 1]`, so the complementary first entry `m - r` does too; the complementary
second entry `n - s` is positive; and a vanishing `s` forces `r = 1`, which is what keeps the pair
`(r, s)` inside the domain `m ≥ 1, (n ≥ 1 or m = 1)` on which the recursion is stated.

These are all statements about `Sym.slopeSplit`, the split of the *primitive* pair of `(m, n)`:
the existing `Sym.slopeSplit_spec` proves the first two of them on the noncoprime branch only,
whereas the recursion needs them on both branches at once. The bridge is `slopeSplit_eq_split`,
which identifies the two branches' splits above width one.
-/

@[expose] public section

namespace HJO.Sym

/-! ### The split equation has at most one solution -/

/-- **The split equation has at most one solution.** Two solutions of `m s + 1 = n r` whose
second entries lie below `n` agree: subtracting the equations makes `n` divide `m (s₁ - s₂)`,
hence `s₁ - s₂` since `m` and `n` are coprime, and `|s₁ - s₂| < n` then forces `s₁ = s₂`. No
upper bound on the first entries is used. -/
@[hjo "lem_split_unique"]
theorem split_unique {m n : ℕ} (hn : 0 < n) (h : Nat.Coprime m n) {r₁ s₁ r₂ s₂ : ℕ}
    (hs₁ : s₁ < n) (hs₂ : s₂ < n) (he₁ : m * s₁ + 1 = n * r₁) (he₂ : m * s₂ + 1 = n * r₂) :
    r₁ = r₂ ∧ s₁ = s₂ := by
  have hz₁ : (m : ℤ) * s₁ + 1 = (n : ℤ) * r₁ := by exact_mod_cast he₁
  have hz₂ : (m : ℤ) * s₂ + 1 = (n : ℤ) * r₂ := by exact_mod_cast he₂
  have hn' : (0 : ℤ) < n := by exact_mod_cast hn
  have hdvd : (n : ℤ) ∣ (m : ℤ) * ((s₁ : ℤ) - s₂) := ⟨(r₁ : ℤ) - r₂, by linarith⟩
  have hcop : IsCoprime (n : ℤ) (m : ℤ) := Nat.isCoprime_iff_coprime.mpr h.symm
  have hs : (s₁ : ℤ) - s₂ = 0 := by
    refine Int.eq_zero_of_abs_lt_dvd (hcop.dvd_of_dvd_mul_left hdvd) ?_
    have h₁ : (s₁ : ℤ) < n := by exact_mod_cast hs₁
    have h₂ : (s₂ : ℤ) < n := by exact_mod_cast hs₂
    have h₃ : (0 : ℤ) ≤ s₁ := Int.natCast_nonneg _
    have h₄ : (0 : ℤ) ≤ s₂ := Int.natCast_nonneg _
    rw [abs_lt]
    constructor <;> linarith
  have hseq : s₁ = s₂ := by
    have : (s₁ : ℤ) = s₂ := by linarith
    exact_mod_cast this
  refine ⟨?_, hseq⟩
  subst hseq
  exact Nat.eq_of_mul_eq_mul_left hn (by omega)

/-- **A solution pins the search.** If some pair meets the four conditions the search of
`Sym.Split` filters on, then, the solution being unique, the search returns exactly that pair --
whatever its internal enumeration order. -/
theorem split_eq_of_spec {m n r s : ℕ} (hn : 0 < n) (h : Nat.Coprime m n)
    (hr : 1 ≤ r) (hrm : r < m) (hs : 1 ≤ s) (hsn : s < n) (he : m * s + 1 = n * r) :
    Split m n = (r, s) := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := split_props (m := m) (n := n) (p := (r, s)) (by
    rw [List.mem_filter, List.mem_product, List.mem_range, List.mem_range, decide_eq_true_eq]
    exact ⟨⟨hrm, hsn⟩, hr, hs, he⟩)
  obtain ⟨hr', hs'⟩ := split_unique hn h h4 hsn h5 he
  exact Prod.ext hr' hs'

/-! ### The split at the boundaries -/

/-- At height one the search of `Sym.Split` finds nothing -- its filter asks for `1 ≤ s < 1` --
so it returns its default `(1, 0)`, which is the split the recursion uses there. -/
theorem split_snd_one (m : ℕ) : Split m 1 = (1, 0) := by
  refine split_default ?_
  rw [List.filter_eq_nil_iff]
  rintro ⟨r, s⟩ hmem hpred
  rw [List.mem_product, List.mem_range, List.mem_range] at hmem
  simp only [decide_eq_true_eq] at hpred
  omega

/-- The primitive split at height one is `(1, 0)`, by either of its first two clauses. -/
theorem primitiveSplit_snd_one (a : ℕ) : primitiveSplit a 1 = (1, 0) := by
  rw [primitiveSplit]
  split_ifs with h1 h2
  · rfl
  · rfl
  · exact absurd rfl h2

/-- The primitive split at width one is `(1, b - 1)`, by its first clause. -/
theorem primitiveSplit_fst_one (b : ℕ) : primitiveSplit 1 b = (1, b - 1) := by
  rw [primitiveSplit]
  simp

/-- Above width one the primitive split of a pair is the bounded search itself: the clause at
width one is inactive, and at height one the search already returns the intended `(1, 0)`. -/
theorem primitiveSplit_eq_split {a b : ℕ} (ha : 1 < a) : primitiveSplit a b = Split a b := by
  rw [primitiveSplit]
  split_ifs with h1 h2
  · exact absurd h1 (by omega)
  · rw [h2, split_snd_one]
  · rfl

/-- Consecutive naturals are coprime. -/
theorem coprime_succ_self (k : ℕ) : Nat.Coprime (k + 1) k := by
  rw [Nat.add_comm]
  exact Nat.coprime_add_self_left.mpr (Nat.coprime_one_left k)

/-- **The split just below the diagonal.** For `k ≥ 2`, `Split (k + 1) k = (k, k - 1)`: that pair
solves the split equation, `(k+1)(k-1) + 1 = k²`, and the solution is unique. -/
@[hjo "lem_split_pred_diag"]
theorem split_pred_diag {k : ℕ} (hk : 2 ≤ k) : Split (k + 1) k = (k, k - 1) := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 2 := ⟨k - 2, by omega⟩
  refine split_eq_of_spec (by omega) (coprime_succ_self _) (by omega) (by omega) (by omega)
    (by omega) ?_
  have hsub : j + 2 - 1 = j + 1 := rfl
  rw [hsub]
  ring

/-- **The split just above the diagonal.** For `a ≥ 2`, `Split a (a + 1) = (1, 1)`: that pair
solves the split equation, `a + 1 = (a+1)·1`, and the solution is unique. -/
@[hjo "lem_split_succ_one"]
theorem split_succ_one {a : ℕ} (ha : 2 ≤ a) : Split a (a + 1) = (1, 1) := by
  refine split_eq_of_spec (by omega) ?_ (by omega) (by omega) (by omega) (by omega) (by omega)
  rw [Nat.add_comm]
  exact Nat.coprime_add_self_right.mpr (Nat.coprime_one_right a)

/-! ### The primitive split under the two Euclidean steps -/

/-- **The primitive split under the first step.** For a coprime pair `(a, b)` with `a, b ≥ 1`
whose primitive split is `(r, s)`, the primitive split of `(a + b, b)` is `(r + s, s)`. -/
@[hjo "lem_prim_split_up"]
theorem primitiveSplit_up {a b : ℕ} (ha : 0 < a) (hb : 0 < b) (hab : Nat.Coprime a b) :
    primitiveSplit (a + b) b =
      ((primitiveSplit a b).1 + (primitiveSplit a b).2, (primitiveSplit a b).2) := by
  have hcop : Nat.Coprime (a + b) b := Nat.coprime_add_self_left.mpr hab
  rcases Nat.lt_or_ge a 2 with ha1 | ha1
  · -- width one: the primitive split of `(1, b)` is `(1, b - 1)`
    have ha' : a = 1 := by omega
    subst ha'
    rw [primitiveSplit_fst_one]
    rcases Nat.lt_or_ge b 2 with hb1 | hb1
    · have hb' : b = 1 := by omega
      subst hb'
      rw [primitiveSplit_snd_one]
      rfl
    · rw [primitiveSplit_eq_split (by omega), Nat.add_comm 1 b,
        split_pred_diag (by omega)]
      simp only [Prod.mk.injEq, and_true]
      omega
  · rcases Nat.lt_or_ge b 2 with hb1 | hb1
    · -- height one: both sides are `(1, 0)`
      have hb' : b = 1 := by omega
      subst hb'
      rw [primitiveSplit_snd_one, primitiveSplit_snd_one]
      rfl
    · -- the interior: exhibit the solution and appeal to uniqueness
      rw [primitiveSplit_eq_split (by omega), primitiveSplit_eq_split (by omega)]
      obtain ⟨hr1, hs1, hra, hsb, he⟩ := split_spec_interior (by omega) (by omega) hab
      refine split_eq_of_spec (by omega) hcop (by omega) (by omega) hs1 hsb ?_
      calc (a + b) * (Split a b).2 + 1 = a * (Split a b).2 + 1 + b * (Split a b).2 := by ring
        _ = b * (Split a b).1 + b * (Split a b).2 := by rw [he]
        _ = b * ((Split a b).1 + (Split a b).2) := by ring

/-- **The primitive split under the second step.** For a coprime pair `(a, b)` with `a, b ≥ 1`
whose primitive split is `(r, s)`, the primitive split of `(a, a + b)` is `(r, r + s)`. -/
@[hjo "lem_prim_split_right"]
theorem primitiveSplit_right {a b : ℕ} (ha : 0 < a) (hb : 0 < b) (hab : Nat.Coprime a b) :
    primitiveSplit a (a + b) =
      ((primitiveSplit a b).1, (primitiveSplit a b).1 + (primitiveSplit a b).2) := by
  have hcop : Nat.Coprime a (a + b) := by
    rw [Nat.add_comm]; exact Nat.coprime_add_self_right.mpr hab
  rcases Nat.lt_or_ge a 2 with ha1 | ha1
  · -- width one on both sides: `(1, b - 1) ↦ (1, (1 + b) - 1)`
    have ha' : a = 1 := by omega
    subst ha'
    rw [primitiveSplit_fst_one, primitiveSplit_fst_one]
    simp only [Prod.mk.injEq, true_and]
    omega
  · rcases Nat.lt_or_ge b 2 with hb1 | hb1
    · -- height one: the primitive split of `(a, a + 1)` is `(1, 1)`
      have hb' : b = 1 := by omega
      subst hb'
      rw [primitiveSplit_snd_one, primitiveSplit_eq_split (by omega),
        split_succ_one (by omega)]
      rfl
    · -- the interior: exhibit the solution and appeal to uniqueness
      rw [primitiveSplit_eq_split (by omega), primitiveSplit_eq_split (by omega)]
      obtain ⟨hr1, hs1, hra, hsb, he⟩ := split_spec_interior (by omega) (by omega) hab
      refine split_eq_of_spec (by omega) hcop hr1 hra (by omega) (by omega) ?_
      calc a * ((Split a b).1 + (Split a b).2) + 1
            = a * (Split a b).1 + (a * (Split a b).2 + 1) := by ring
        _ = a * (Split a b).1 + b * (Split a b).1 := by rw [he]
        _ = (a + b) * (Split a b).1 := by ring

/-! ### The split of a slope: the primitive normalisation on both branches -/

/-- Every slope with `m ≥ 1` and `n ≥ 1` is a positive multiple of a positive coprime pair, and
its split is the primitive split of that pair. This is `exists_primitive` without the noncoprime
hypothesis: the multiplicity is only claimed positive, not `≥ 2`. -/
theorem exists_primitive_pair {m n : ℕ} (hm : 0 < m) (hn : 0 < n) :
    ∃ k a b : ℕ, 0 < k ∧ 0 < a ∧ 0 < b ∧ Nat.Coprime a b ∧ m = k * a ∧ n = k * b ∧
      slopeSplit m n = primitiveSplit a b := by
  have hk : 0 < Nat.gcd m n := Nat.gcd_pos_of_pos_left n hm
  exact ⟨Nat.gcd m n, m / Nat.gcd m n, n / Nat.gcd m n, hk,
    Nat.div_pos (Nat.le_of_dvd hm (Nat.gcd_dvd_left m n)) hk,
    Nat.div_pos (Nat.le_of_dvd hn (Nat.gcd_dvd_right m n)) hk,
    Nat.coprime_div_gcd_div_gcd hk,
    (Nat.mul_div_cancel' (Nat.gcd_dvd_left m n)).symm,
    (Nat.mul_div_cancel' (Nat.gcd_dvd_right m n)).symm, rfl⟩

/-- On the coprime branch the split of a slope above width one is the bounded search on the
slope itself: the primitive pair is the slope. -/
theorem slopeSplit_eq_split {m n : ℕ} (hm : 1 < m) (h : Nat.Coprime m n) :
    slopeSplit m n = Split m n := by
  rw [slopeSplit, h.gcd_eq_one, Nat.div_one, Nat.div_one, primitiveSplit_eq_split hm]

/-- **The split of a slope under the first step.** The step `(m, n) ↦ (m + n, n)` fixes the
multiplicity and acts on the primitive pair as `(a, b) ↦ (a + b, b)`, so it sends the split
`(r, s)` to `(r + s, s)`. -/
theorem slopeSplit_up {m n : ℕ} (hm : 0 < m) (hn : 0 < n) :
    slopeSplit (m + n) n = ((slopeSplit m n).1 + (slopeSplit m n).2, (slopeSplit m n).2) := by
  have hk : 0 < Nat.gcd m n := Nat.gcd_pos_of_pos_left n hm
  have hdm : Nat.gcd m n ∣ m := Nat.gcd_dvd_left m n
  simp only [slopeSplit, Nat.gcd_add_self_left n m, Nat.add_div_of_dvd_right hdm]
  exact primitiveSplit_up (Nat.div_pos (Nat.le_of_dvd hm hdm) hk)
    (Nat.div_pos (Nat.le_of_dvd hn (Nat.gcd_dvd_right m n)) hk) (Nat.coprime_div_gcd_div_gcd hk)

/-- **The split of a slope under the second step.** The step `(m, n) ↦ (m, n + m)` fixes the
multiplicity and acts on the primitive pair as `(a, b) ↦ (a, a + b)`, so it sends the split
`(r, s)` to `(r, r + s)`. -/
theorem slopeSplit_right {m n : ℕ} (hm : 0 < m) (hn : 0 < n) :
    slopeSplit m (n + m) = ((slopeSplit m n).1, (slopeSplit m n).1 + (slopeSplit m n).2) := by
  have hk : 0 < Nat.gcd m n := Nat.gcd_pos_of_pos_left n hm
  have hdn : Nat.gcd m n ∣ n := Nat.gcd_dvd_right m n
  simp only [slopeSplit, Nat.gcd_add_self_right m n, Nat.add_div_of_dvd_right hdn,
    Nat.add_comm (n / Nat.gcd m n) (m / Nat.gcd m n)]
  exact primitiveSplit_right (Nat.div_pos (Nat.le_of_dvd hm (Nat.gcd_dvd_left m n)) hk)
    (Nat.div_pos (Nat.le_of_dvd hn hdn) hk) (Nat.coprime_div_gcd_div_gcd hk)

/-- **The split on the ray below the diagonal.** For `k ≥ 1` the split of `(k + 1, k)` is
`(k, k - 1)`: the pair is coprime, so its primitive pair is itself, and the bounded search returns
`(k, k - 1)` -- at `k = 1` as its default `(1, 0)`, above that by `split_pred_diag`. -/
theorem slopeSplit_succ_self {k : ℕ} (hk : 1 ≤ k) : slopeSplit (k + 1) k = (k, k - 1) := by
  rw [slopeSplit_eq_split (by omega) (coprime_succ_self k)]
  rcases Nat.lt_or_ge k 2 with hk1 | hk1
  · have hk' : k = 1 := by omega
    subst hk'
    rw [split_snd_one]
  · exact split_pred_diag hk1

/-! ### The three bounds every induction along the recursion of `Qop` needs -/

/-- **The split index drops.** For `m ≥ 2` and `n ≥ 1` the first entry of the split of `(m, n)`
lies in `[1, m - 1]`. -/
@[hjo "lem_qop_split_r_lt"]
theorem one_le_slopeSplit_fst_lt {m n : ℕ} (hm : 1 < m) (hn : 0 < n) :
    1 ≤ (slopeSplit m n).1 ∧ (slopeSplit m n).1 < m := by
  obtain ⟨k, a, b, hk, ha, hb, hab, hmk, hnk, hsp⟩ :=
    exists_primitive_pair (m := m) (n := n) (by omega) hn
  obtain ⟨hr1, hra, hsb, he⟩ := primitiveSplit_spec ha hb hab
  rw [hsp]
  refine ⟨hr1, ?_⟩
  rcases Nat.lt_or_ge k 2 with hk1 | hk1
  · have hk' : k = 1 := by omega
    subst hk'
    rw [Nat.one_mul] at hmk
    subst hmk
    exact primitiveSplit_fst_lt hm hb hab
  · have : 2 * a ≤ k * a := Nat.mul_le_mul_right a (by omega)
    omega

/-- **The complementary second index is positive.** For `m ≥ 2` and `n ≥ 1` the second entry of
the split of `(m, n)` is `< n`, so `n - s ≥ 1`. -/
@[hjo "lem_qop_split_e_ge"]
theorem one_le_sub_slopeSplit_snd {m n : ℕ} (hm : 1 < m) (hn : 0 < n) :
    1 ≤ n - (slopeSplit m n).2 := by
  obtain ⟨k, a, b, hk, ha, hb, hab, hmk, hnk, hsp⟩ :=
    exists_primitive_pair (m := m) (n := n) (by omega) hn
  obtain ⟨hr1, hra, hsb, he⟩ := primitiveSplit_spec ha hb hab
  rw [hsp]
  have : 1 * b ≤ k * b := Nat.mul_le_mul_right b hk
  omega

/-- **A vanishing split second index forces the first to be one.** For `m ≥ 2` and `n ≥ 1`, if
the second entry of the split of `(m, n)` vanishes then its first entry is `1`. -/
@[hjo "lem_qop_split_s_zero"]
theorem slopeSplit_fst_eq_one {m n : ℕ} (hm : 1 < m) (hn : 0 < n)
    (hs : (slopeSplit m n).2 = 0) : (slopeSplit m n).1 = 1 := by
  obtain ⟨k, a, b, hk, ha, hb, hab, hmk, hnk, hsp⟩ :=
    exists_primitive_pair (m := m) (n := n) (by omega) hn
  rw [hsp] at hs ⊢
  rcases Nat.lt_or_ge b 2 with hb1 | hb1
  · have hb' : b = 1 := by omega
    subst hb'
    rw [primitiveSplit_snd_one]
  · exact absurd hs (by have := primitiveSplit_snd_pos ha (by omega) hab; omega)

end HJO.Sym
