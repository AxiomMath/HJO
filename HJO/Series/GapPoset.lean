/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Mathlib.Data.Int.Interval
public import QSeriesLib.Data.Nat.ModEq
public import HJO.Series.Gaps
public meta import HJO.Attr

/-! # The Frobenius gap is the top of the gap poset

For coprime `1 < a < b` the Frobenius gap `f = a * b - a - b` is a gap of `⟨a, b⟩` and dominates
every gap in the gap order. Two consequences are recorded: the index set of the finite HJO
polynomial is finite, and the coercivity bound at `f` reads `n_f ^ 2 ≤ |G| * Q 𝐧` on the
monotonicity cone.
-/

@[expose] public section

open Finset NumericalSemigroup HJO.Gaps

namespace HJO.GapPoset

/-! ### Residues and the Frobenius gap -/

/-- Two naturals that agree modulo `a` and are strictly ordered differ by at least `a`. -/
theorem add_le_of_mod_eq_of_lt {a m n : ℕ} (h : m % a = n % a) (hmn : m < n) : m + a ≤ n := by
  have hdvd : a ∣ n - m := (Nat.modEq_iff_dvd' hmn.le).mp (show Nat.ModEq a m n from h)
  have hle : a ≤ n - m := Nat.le_of_dvd (by omega) hdvd
  omega

/-- With `a` and `b` coprime and `a` positive, every natural is congruent modulo `a` to `j * b`
for some `j < a`. -/
theorem exists_lt_mod_eq_mul (a b : ℕ) (hco : a.Coprime b) (ha : 0 < a) (t : ℕ) :
    ∃ j < a, t % a = j * b % a := by
  obtain ⟨j, hja, hj⟩ :=
    Nat.exists_mul_mod_eq_of_coprime (k := a) (n := b) t hco.symm (by omega)
  exact ⟨j, hja, by rw [mul_comm j b]; exact hj.symm⟩

/-- `f + a + b = a * b`: the Frobenius gap subtracts `a` and `b` from `a * b` without
truncation. -/
theorem frobeniusGap_add_add (a b : ℕ) (ha : 1 < a) (hb : 1 < b) :
    frobeniusGap a b + a + b = a * b := by
  change a * b - a - b + a + b = a * b
  rw [Nat.sub_sub, Nat.add_assoc, Nat.sub_add_cancel (add_le_mul ha hb)]

/-- `(a - 1) * b = f + a`: the last residue class of `b` modulo `a` starts just above `f`. -/
theorem sub_one_mul_eq (a b : ℕ) (ha : 1 < a) (hb : 1 < b) :
    (a - 1) * b = frobeniusGap a b + a := by
  have h1 : (a - 1) * b + b = a * b := by
    obtain ⟨c, rfl⟩ : ∃ c, a = c + 1 := ⟨a - 1, by omega⟩
    simp [Nat.add_mul]
  exact Nat.add_right_cancel (h1.trans (frobeniusGap_add_add a b ha hb).symm)

/-- The arithmetic core of Sylvester symmetry: when `J' + J = f + a` and `n ≤ f`, the value `n`
falls short of `J` exactly when `J'` fits below `f - n`. -/
theorem lt_iff_le_sub {J J' f n a : ℕ} (ha : 0 < a) (hsum : J' + J = f + a) (hn : n ≤ f)
    (hstep : n < J → n + a ≤ J) : n < J ↔ J' ≤ f - n := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · have h2 := hstep h
    omega
  · omega

/-! ### Sylvester symmetry and maximality -/

/-- Sylvester symmetry: for `n ≤ f`, exactly one of `n` and `f - n` is a gap of `⟨a, b⟩`. -/
theorem mem_gaps_iff_sub_notMem (a b : ℕ) (hco : a.Coprime b) (ha : 1 < a) (hb : 1 < b)
    {n : ℕ} (hn : n ≤ frobeniusGap a b) :
    n ∈ (finspan {a, b}).gaps ↔ frobeniusGap a b - n ∉ (finspan {a, b}).gaps := by
  obtain ⟨j, hja, hmod⟩ := exists_lt_mod_eq_mul a b hco (by omega) n
  have hja' : a - 1 - j < a := by omega
  have hsum : (a - 1 - j) * b + j * b = frobeniusGap a b + a := by
    rw [← Nat.add_mul, show a - 1 - j + j = a - 1 by omega]
    exact sub_one_mul_eq a b ha hb
  have h2 : Nat.ModEq a (frobeniusGap a b - n + n) ((a - 1 - j) * b + j * b) := by
    rw [Nat.sub_add_cancel hn, hsum]
    exact (Nat.add_mod_right _ _).symm
  have hmod' : (frobeniusGap a b - n) % a = (a - 1 - j) * b % a :=
    Nat.ModEq.add_right_cancel (show Nat.ModEq a n (j * b) from hmod) h2
  rw [mem_gaps_iff_not_exists a b hco n,
    mem_gaps_iff_not_exists a b hco (frobeniusGap a b - n),
    Nat.exists_mul_add_mul_eq_iff_mul_le_of_coprime hco hja hmod,
    Nat.exists_mul_add_mul_eq_iff_mul_le_of_coprime hco hja' hmod', not_not, not_le]
  exact lt_iff_le_sub (by omega) hsum hn fun h => add_le_of_mod_eq_of_lt hmod h

/-- Every gap of `⟨a, b⟩` is at most the Frobenius gap. -/
theorem le_frobeniusGap (a b : ℕ) (hco : a.Coprime b) (ha : 1 < a) (hb : 1 < b)
    {g : ℕ} (hg : g ∈ (finspan {a, b}).gaps) : g ≤ frobeniusGap a b := by
  obtain ⟨j, hja, hmod⟩ := exists_lt_mod_eq_mul a b hco (by omega) g
  rw [mem_gaps_iff_not_exists a b hco g,
    Nat.exists_mul_add_mul_eq_iff_mul_le_of_coprime hco hja hmod, not_le] at hg
  have h2 : g + a ≤ j * b := add_le_of_mod_eq_of_lt hmod hg
  have h3 : j * b ≤ (a - 1) * b := Nat.mul_le_mul (by omega) le_rfl
  have h4 : g + a ≤ frobeniusGap a b + a := by
    rw [← sub_one_mul_eq a b ha hb]
    exact h2.trans h3
  omega

/-- The Frobenius gap is a gap: `a * b - a - b` is not a nonnegative combination of `a` and
`b`. -/
theorem frobeniusGap_mem (a b : ℕ) (hco : a.Coprime b) (ha : 1 < a) (hb : 1 < b) :
    frobeniusGap a b ∈ (finspan {a, b}).gaps := by
  by_contra hc
  refine NumericalSemigroup.zero_notMem_gaps (finspan {a, b}) ?_
  have h := mem_gaps_iff_sub_notMem a b hco ha hb (n := 0) (Nat.zero_le _)
  rw [Nat.sub_zero] at h
  exact h.mpr hc

/-- The Frobenius gap is a gap, and every gap precedes it in the gap order. -/
@[hjo "lem_frobenius_max"]
theorem frobeniusGap_max (a b : ℕ) (hco : a.Coprime b) (ha : 1 < a) (hab : a < b) :
    frobeniusGap a b ∈ (finspan {a, b}).gaps ∧
      ∀ g ∈ (finspan {a, b}).gaps, GapLE a b g (frobeniusGap a b) := by
  have hb : 1 < b := ha.trans hab
  refine ⟨frobeniusGap_mem a b hco ha hb, fun g hg => ?_⟩
  have hgf : g ≤ frobeniusGap a b := le_frobeniusGap a b hco ha hb hg
  have hnot : frobeniusGap a b - g ∉ (finspan {a, b}).gaps :=
    (mem_gaps_iff_sub_notMem a b hco ha hb hgf).mp hg
  rw [mem_gaps_iff_not_exists a b hco, not_not] at hnot
  obtain ⟨u, v, huv⟩ := hnot
  exact ⟨u, v, by rw [huv]; exact Nat.add_sub_cancel' hgf⟩

/-! ### Finiteness of the index set -/

/-- At a gap, the zero-extension of an integer gap vector is the vector's own value. -/
theorem extend_of_mem {a b : ℕ} (n : (finspan {a, b}).gaps → ℤ) {g : ℕ}
    (hg : g ∈ (finspan {a, b}).gaps) : HJO.extend n g = n ⟨g, hg⟩ := by
  simp [HJO.extend, hg]

/-- At a gap, the zero-extension of a natural gap vector is the vector's own value. -/
theorem extendNat_of_mem {a b : ℕ} (n : (finspan {a, b}).gaps → ℕ) {g : ℕ}
    (hg : g ∈ (finspan {a, b}).gaps) : HJO.extendNat n g = n ⟨g, hg⟩ := by
  simp [HJO.extendNat, hg]

/-- The set of cone points whose value at the Frobenius gap is at most `N` is finite: on the cone
every coordinate is bounded by that value. -/
@[hjo "lem_finite_index"]
theorem finite_cone_frobeniusGap_le (a b N : ℕ) (hco : a.Coprime b) (ha : 1 < a) (hab : a < b) :
    {n ∈ HJO.cone a b | HJO.extend n (frobeniusGap a b) ≤ (N : ℤ)}.Finite := by
  have hf := (frobeniusGap_max a b hco ha hab).1
  have hfin : {m : (finspan {a, b}).gaps → ℤ | ∀ g, m g ∈ Set.Icc (0 : ℤ) (N : ℤ)}.Finite :=
    Set.Finite.pi' fun _ => Set.finite_Icc _ _
  refine hfin.subset ?_
  rintro n ⟨hcone, hle⟩
  rw [cone_eq a b hco] at hcone
  obtain ⟨hpos, hmono⟩ := hcone
  have hext : HJO.extend n (frobeniusGap a b) = n ⟨frobeniusGap a b, hf⟩ := extend_of_mem n hf
  intro g
  refine Set.mem_Icc.mpr ⟨hpos g, ?_⟩
  refine (hmono g ⟨frobeniusGap a b, hf⟩ ((frobeniusGap_max a b hco ha hab).2 g g.2)).trans ?_
  rw [← hext]
  exact hle

/-- The same finiteness for the natural-number presentation of the cone. -/
theorem finite_coneNat_frobeniusGap_le (a b N : ℕ) (hco : a.Coprime b) (ha : 1 < a) (hab : a < b) :
    {n : (finspan {a, b}).gaps → ℕ | (fun i => (n i : ℤ)) ∈ HJO.cone a b ∧
      HJO.extendNat n (frobeniusGap a b) ≤ N}.Finite := by
  have hf := (frobeniusGap_max a b hco ha hab).1
  have hfin : {m : (finspan {a, b}).gaps → ℕ | ∀ g, m g ∈ Set.Iic N}.Finite :=
    Set.Finite.pi' fun _ => Set.finite_Iic _
  refine hfin.subset ?_
  rintro n ⟨hcone, hle⟩
  rw [cone_eq a b hco] at hcone
  have hext : HJO.extendNat n (frobeniusGap a b) = n ⟨frobeniusGap a b, hf⟩ :=
    extendNat_of_mem n hf
  intro g
  have h1 : ((n g : ℤ)) ≤ ((n ⟨frobeniusGap a b, hf⟩ : ℕ) : ℤ) :=
    hcone.2 g ⟨frobeniusGap a b, hf⟩ ((frobeniusGap_max a b hco ha hab).2 g g.2)
  exact Set.mem_Iic.mpr ((Nat.cast_le.mp h1).trans (hext ▸ hle))

/-! ### Coercivity at the Frobenius gap -/

/-- Coercivity at the Frobenius gap: on the monotonicity cone `n_f ^ 2 ≤ |G| * Q 𝐧`, given the
coercivity bound at every gap. -/
@[hjo "lem_coercivity_frobenius"]
theorem coercivity_frobeniusGap
    (huang : ∀ a b : ℕ, Nat.Coprime a b → 1 < a → a < b →
      ∀ n : (finspan {a, b}).gaps → ℤ, n ∈ HJO.cone a b →
        ∀ i : (finspan {a, b}).gaps, n i ^ 2 ≤ ((finspan {a, b}).gaps.card : ℤ) * HJO.Q a b n)
    (a b : ℕ) (hco : a.Coprime b) (ha : 1 < a) (hab : a < b)
    (n : (finspan {a, b}).gaps → ℤ) (hn : n ∈ HJO.cone a b) :
    HJO.extend n (frobeniusGap a b) ^ 2 ≤ ((finspan {a, b}).gaps.card : ℤ) * HJO.Q a b n := by
  have hf := (frobeniusGap_max a b hco ha hab).1
  rw [extend_of_mem n hf]
  exact huang a b hco ha hab n hn ⟨frobeniusGap a b, hf⟩

end HJO.GapPoset
