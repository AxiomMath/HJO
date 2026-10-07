/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.Series.GapForms
public import HJO.GoodTraverse.Boundary
public meta import HJO.Attr

/-! # The good traverse factorisation

For coprime `1 < a < b` this file proves the factorisation of the generalised Gaussian
multinomial over the gap set `G` of `⟨a, b⟩` factor for factor, by matching the two products.
The route needs neither the Sylvester coordinates nor the two-dimensional diagram: the
structural input is that at a gap `g` the upper shift `g + b` leaves `G` exactly when
`a ∣ g + b`, which makes the upper boundary `𝓑 = HJO.Defs.upperBoundary a b` a single
`⟨a⟩`-chain `{f - j * a : 0 ≤ j ≤ L}` topped by the Frobenius gap `f`, of length
`L = HJO.Defs.boundaryLength a b`. Along that chain the boundary factors telescope, the interior
factors match under the `b`-shift, and the lower boundary factors are `1`.

The ambient ring is `ℤ⟦X⟧` with `q = X`, as everywhere in this library, rather than the field
`ℚ(q)` in which the identity is usually stated: the `q`-factorial `(q)_k = (X; X)_k` has constant
term `1`, so it is a unit, and division by it is multiplication by `PowerSeries.invOfUnit`. That
the `q`-factorial is nonzero -- the reason one may divide by it in `ℚ(q)` -- is
`qPochhammer_ne_zero`, and the two-sided inverse property is
`HJO.ReturnPathSolves.qPochhammer_mul_inv`.

Indices are natural numbers and the differences of coordinates appearing in them are truncated
subtractions, as in `HJO.multiplicand` and `HJO.Gaps.flag`. Under the hypotheses of the identity
-- `𝐧` in the monotonicity cone with `n_f ≤ N` -- no truncation occurs, since every difference
appearing in it is then nonnegative; the lemmas proving that are `extend_sub_le`,
`extend_le_frobenius` and `le_flag_add`. Because the truncated readings agree with the untruncated
ones there, the product identities `prod_upperBoundary_telescope`, `prod_interior_match` and
`reduced_traverse` need no cone hypothesis at all: off the cone the truncation is exactly the
usual convention that a `q`-factorial at a negative index contributes nothing new to the
identity, and the proofs are the same reindexings.
-/

@[expose] public section

open Finset NumericalSemigroup PowerSeries
open scoped QTheory

namespace HJO.GoodTraverse

/-! ### The `q`-factorial and telescoping products -/

/-- The `q`-factorial `(q)_k = (X; X)_k` is nonzero: its constant term is `1`. Over `ℚ(q)` this
is what licenses dividing by it; here the stronger statement that it is a unit is
`HJO.ReturnPathSolves.qPochhammer_mul_inv`. -/
@[hjo "lem_qfac_ne_zero"]
theorem qPochhammer_ne_zero (k : ℕ) : ((X; X)_k : ℤ⟦X⟧) ≠ 0 := fun hk => by
  simpa [hk] using ReturnPathSolves.constantCoeff_qPochhammer k

/-- A product of ratios telescopes, in the form in which a commutative monoid can state it: if
`d j` is inverse to `c j` for every `j ≤ L`, then `∏_{j=0}^{L} c_{j+1} * d_j = c_{L+1} * d_0`. -/
theorem prod_mul_inv_telescope {M : Type*} [CommMonoid M] {c d : ℕ → M} {L : ℕ}
    (h : ∀ j ≤ L, c j * d j = 1) :
    ∏ j ∈ range (L + 1), c (j + 1) * d j = c (L + 1) * d 0 := by
  induction L with
  | zero => simp
  | succ L ih =>
    rw [Finset.prod_range_succ, ih fun j hj => h j (by omega)]
    calc c (L + 1) * d 0 * (c (L + 1 + 1) * d (L + 1))
        = c (L + 1) * d (L + 1) * (c (L + 1 + 1) * d 0) := by
          simp only [mul_comm, mul_left_comm]
      _ = c (L + 1 + 1) * d 0 := by rw [h (L + 1) (by omega), one_mul]

/-- Telescoping a product of ratios of nonzero field elements: for `c₀, …, c_{M+1}` nonzero,
`∏_{j=0}^{M} c_{j+1} / c_j = c_{M+1} / c_0`. This is the statement over the field `ℚ(q)`; the
library uses the `ℤ⟦X⟧` form `prod_mul_inv_telescope`. -/
@[hjo "lem_telescope"]
theorem prod_div_telescope {K : Type*} [Field K] {c : ℕ → K} {M : ℕ}
    (hc : ∀ j ≤ M + 1, c j ≠ 0) :
    ∏ j ∈ range (M + 1), c (j + 1) / c j = c (M + 1) / c 0 := by
  simp only [div_eq_mul_inv]
  exact prod_mul_inv_telescope fun j hj => mul_inv_cancel₀ (hc j (by omega))

/-! ### The semigroup and the gap set -/

/-- Coprimality of the pair as the `gcd` condition that the generated numerical semigroup
`finspan {a, b}` needs. -/
theorem gcd_pair_eq_one {a b : ℕ} (hco : a.Coprime b) : ({a, b} : Finset ℕ).gcd id = 1 := by
  gcd_tac

/-- The semigroup `Γ = {u * a + v * b}` is closed under addition. -/
@[hjo "lem_semigroup_closed"]
theorem add_mem_finspan {a b s t : ℕ} (hs : s ∈ finspan {a, b}) (ht : t ∈ finspan {a, b}) :
    s + t ∈ finspan {a, b} :=
  (finspan {a, b}).add_mem hs ht

/-- Every multiple of the first generator lies in the semigroup. -/
theorem mul_mem_finspan_left {a b : ℕ} (hgcd : ({a, b} : Finset ℕ).gcd id = 1) (j : ℕ) :
    j * a ∈ finspan {a, b} := by
  rw [mem_finspan_iff _ hgcd]
  simp only [Finset.coe_insert, Finset.coe_singleton, AddSubmonoid.mem_closure_pair]
  exact ⟨j, 0, by simp⟩

/-- Subtracting a semigroup element from a gap leaves a gap, as long as it stays nonnegative. -/
@[hjo "lem_gap_shift_down"]
theorem sub_mem_gaps {a b g s : ℕ} (hg : g ∈ (finspan {a, b}).gaps)
    (hs : s ∈ finspan {a, b}) (hsg : s ≤ g) : g - s ∈ (finspan {a, b}).gaps :=
  NumericalSemigroup.sub_mem_gaps_of_mem hg hs hsg

/-- A missing lower neighbour is negative: if `g` is a gap, `s` lies in the semigroup and
`g - s` is not a gap, then `g - s < 0`, which over the naturals reads `g < s`. -/
@[hjo "lem_gap_shift_down_neg"]
theorem lt_of_sub_notMem_gaps {a b g s : ℕ} (hg : g ∈ (finspan {a, b}).gaps)
    (hs : s ∈ finspan {a, b}) (h : g - s ∉ (finspan {a, b}).gaps) : g < s := by
  by_contra hc
  exact h (sub_mem_gaps hg hs (by omega))

/-- A gap whose upper shift leaves the gap set: if `g` is a gap and `g + b` is not, then
`a ∣ g + b`. -/
@[hjo "lem_boundary_div"]
theorem dvd_add_of_add_notMem_gaps {a b g : ℕ} (hco : a.Coprime b)
    (hg : g ∈ (finspan {a, b}).gaps) (h : g + b ∉ (finspan {a, b}).gaps) : a ∣ g + b :=
  (ReturnPathSolves.add_right_notMem_gaps_iff hco hg).mp h

/-- A multiple of `a` is not a gap: if `g` is a gap and `a ∣ g + b`, then `g + b` is not a
gap. -/
@[hjo "lem_div_boundary"]
theorem add_notMem_gaps_of_dvd_add {a b g : ℕ} (hco : a.Coprime b)
    (hg : g ∈ (finspan {a, b}).gaps) (h : a ∣ g + b) : g + b ∉ (finspan {a, b}).gaps :=
  (ReturnPathSolves.add_right_notMem_gaps_iff hco hg).mpr h

/-! ### The monotonicity cone along semigroup shifts -/

/-- The zero-extension of a natural gap vector, read in `ℤ`, is the cast of its natural
zero-extension. -/
theorem extend_natCast {a b : ℕ} (n : (finspan {a, b}).gaps → ℕ) (i : ℕ) :
    HJO.extend (fun g => (n g : ℤ)) i = (HJO.extendNat n i : ℤ) := by
  by_cases h : i ∈ (finspan {a, b}).gaps
  · rw [HJO.extend_of_mem h, HJO.extendNat_of_mem h]
  · rw [HJO.extend_of_not_mem h, HJO.extendNat_of_not_mem h, Nat.cast_zero]

/-- The cone increases along semigroup shifts: for `𝐧` in the monotonicity cone, a gap `g` and a
semigroup element `s`, the extended value at `g - s` is at most the value at `g`. -/
@[hjo "lem_cone_le_shift"]
theorem extend_sub_le {a b : ℕ} (hco : a.Coprime b) {n : (finspan {a, b}).gaps → ℤ}
    (hn : n ∈ HJO.cone a b) {g s : ℕ} (hg : g ∈ (finspan {a, b}).gaps)
    (hs : s ∈ finspan {a, b}) : HJO.extend n (g - s) ≤ HJO.extend n g := by
  have hgcd := gcd_pair_eq_one hco
  by_cases h : g - s ∈ (finspan {a, b}).gaps
  · have hsg : s ≤ g := by
      by_contra hc
      rw [Nat.sub_eq_zero_of_le (by omega)] at h
      exact (finspan {a, b}).zero_notMem_gaps h
    rw [mem_finspan_iff _ hgcd] at hs
    simp only [Finset.coe_insert, Finset.coe_singleton, AddSubmonoid.mem_closure_pair] at hs
    obtain ⟨u, v, huv⟩ := hs
    simp only [smul_eq_mul] at huv
    rw [HJO.extend_of_mem h, HJO.extend_of_mem hg]
    exact Gaps.cone_mono hgcd hn u v (g - s) g h hg (by rw [Nat.add_assoc, huv]; omega)
  · rw [HJO.extend_of_not_mem h, HJO.extend_of_mem hg]
    exact hn.1 _

/-- The natural-number form of `extend_sub_le`. -/
theorem extendNat_sub_le {a b : ℕ} (hco : a.Coprime b) {n : (finspan {a, b}).gaps → ℕ}
    (hn : (fun g => (n g : ℤ)) ∈ HJO.cone a b) {g s : ℕ} (hg : g ∈ (finspan {a, b}).gaps)
    (hs : s ∈ finspan {a, b}) : HJO.extendNat n (g - s) ≤ HJO.extendNat n g := by
  have h := extend_sub_le hco hn hg hs
  rwa [extend_natCast, extend_natCast, Nat.cast_le] at h

/-- The Frobenius coordinate dominates: on the monotonicity cone the value at any gap is at most
the value at the Frobenius gap. -/
@[hjo "lem_cone_le_frobenius"]
theorem extend_le_frobenius {a b : ℕ} (hco : a.Coprime b) (ha : 1 < a) (hab : a < b)
    {n : (finspan {a, b}).gaps → ℤ} (hn : n ∈ HJO.cone a b) {g : ℕ}
    (hg : g ∈ (finspan {a, b}).gaps) :
    HJO.extend n g ≤ HJO.extend n (Gaps.frobeniusGap a b) := by
  obtain ⟨hf, hmax⟩ := GapPoset.frobeniusGap_max a b hco ha hab
  rw [Gaps.cone_eq a b hco] at hn
  rw [HJO.extend_of_mem hg, HJO.extend_of_mem hf]
  exact hn.2 ⟨g, hg⟩ ⟨_, hf⟩ (hmax g hg)

/-- The natural-number form of `extend_le_frobenius`. -/
theorem extendNat_le_frobenius {a b : ℕ} (hco : a.Coprime b) (ha : 1 < a) (hab : a < b)
    {n : (finspan {a, b}).gaps → ℕ} (hn : (fun g => (n g : ℤ)) ∈ HJO.cone a b) {g : ℕ}
    (hg : g ∈ (finspan {a, b}).gaps) :
    HJO.extendNat n g ≤ HJO.extendNat n (Gaps.frobeniusGap a b) := by
  have h := extend_le_frobenius hco ha hab hn hg
  rwa [extend_natCast, extend_natCast, Nat.cast_le] at h

/-! ### The flag extension at the upper shift -/

/-- At a gap whose upper shift is again a gap, the flag extension reads the cone value there. -/
theorem flag_add_of_mem {a b N g : ℕ} (n : (finspan {a, b}).gaps → ℕ)
    (h : g + b ∈ (finspan {a, b}).gaps) :
    Gaps.flag a b N n ((g : ℤ) + b) = HJO.extendNat n (g + b) := by
  have hcast : ((g : ℤ) + b).toNat = g + b := by omega
  have hneg : ¬ ((g : ℤ) + b < 0) := by omega
  simp only [Gaps.flag, hneg, ite_false, hcast, h, ite_true]

/-- At a gap whose upper shift leaves the gap set, the flag extension reads the level `N`. -/
theorem flag_add_of_notMem {a b N g : ℕ} (n : (finspan {a, b}).gaps → ℕ)
    (h : g + b ∉ (finspan {a, b}).gaps) : Gaps.flag a b N n ((g : ℤ) + b) = N := by
  have hcast : ((g : ℤ) + b).toNat = g + b := by omega
  have hneg : ¬ ((g : ℤ) + b < 0) := by omega
  simp only [Gaps.flag, hneg, ite_false, hcast, h, ite_false]

/-- The flag dominates the upper successor: for `𝐧` in the monotonicity cone with `n_f ≤ N`, the
value at a gap `g` is at most the flag value at `g + b`. -/
@[hjo "lem_flag_succ_ge"]
theorem le_flag_add {a b N : ℕ} (hco : a.Coprime b) (ha : 1 < a) (hab : a < b)
    {n : (finspan {a, b}).gaps → ℕ} (hn : (fun g => (n g : ℤ)) ∈ HJO.cone a b)
    (hfN : HJO.extendNat n (Gaps.frobeniusGap a b) ≤ N) {g : ℕ}
    (hg : g ∈ (finspan {a, b}).gaps) :
    HJO.extendNat n g ≤ Gaps.flag a b N n ((g : ℤ) + b) := by
  by_cases h : g + b ∈ (finspan {a, b}).gaps
  · rw [flag_add_of_mem n h]
    have hstep := extendNat_sub_le hco hn h (Gaps.mem_finspan_right (gcd_pair_eq_one hco))
    rwa [Nat.add_sub_cancel] at hstep
  · rw [flag_add_of_notMem n h]
    exact (extendNat_le_frobenius hco ha hab hn hg).trans hfN

/-! ### The upper boundary is the `a`-chain below the Frobenius gap -/

/-- Subtracting a multiple of `a` from the Frobenius gap lands on the upper boundary. -/
theorem sub_mem_upperBoundary {a b : ℕ} (hco : a.Coprime b) (ha : 1 < a) (hab : a < b) {m : ℕ}
    (hm : m ≤ Gaps.frobeniusGap a b) (hdvd : a ∣ m) :
    Gaps.frobeniusGap a b - m ∈ Defs.upperBoundary a b := by
  have hb : 1 < b := ha.trans hab
  have hf := Defs.frobeniusGap_mem_upperBoundary a b hco ha hb
  have hfb : a ∣ Gaps.frobeniusGap a b + b := ((Defs.mem_upperBoundary_iff_dvd hco).mp hf).2
  have hfG : Gaps.frobeniusGap a b ∈ (finspan {a, b}).gaps := (Defs.mem_upperBoundary.mp hf).1
  have hmem : m ∈ finspan {a, b} := by
    obtain ⟨c, rfl⟩ := hdvd
    simpa [Nat.mul_comm] using mul_mem_finspan_left (gcd_pair_eq_one hco) c
  refine (Defs.mem_upperBoundary_iff_dvd hco).mpr ⟨sub_mem_gaps hfG hmem hm, ?_⟩
  rw [show Gaps.frobeniusGap a b - m + b = Gaps.frobeniusGap a b + b - m from by omega]
  exact Nat.dvd_sub hfb hdvd

/-- The upper boundary is the `a`-chain below the Frobenius gap:
`𝓑 = {f - j * a : 0 ≤ j ≤ L}` with `L = ⌊f / a⌋`. -/
@[hjo "lem_boundary_eq_chain"]
theorem upperBoundary_eq_image {a b : ℕ} (hco : a.Coprime b) (ha : 1 < a) (hab : a < b) :
    Defs.upperBoundary a b =
      (range (Defs.boundaryLength a b + 1)).image fun j => Gaps.frobeniusGap a b - j * a := by
  have hb : 1 < b := ha.trans hab
  have ha0 : 0 < a := by omega
  ext g
  simp only [Finset.mem_image, Finset.mem_range]
  refine ⟨fun hg => ?_, ?_⟩
  · obtain ⟨hgG, hdvd⟩ := (Defs.mem_upperBoundary_iff_dvd hco).mp hg
    have hf := Defs.frobeniusGap_mem_upperBoundary a b hco ha hb
    have hfb : a ∣ Gaps.frobeniusGap a b + b := ((Defs.mem_upperBoundary_iff_dvd hco).mp hf).2
    have hgf : g ≤ Gaps.frobeniusGap a b := GapPoset.le_frobeniusGap a b hco ha hb hgG
    have hdf : a ∣ Gaps.frobeniusGap a b - g := by
      rw [show Gaps.frobeniusGap a b - g = Gaps.frobeniusGap a b + b - (g + b) from by omega]
      exact Nat.dvd_sub hfb hdvd
    refine ⟨(Gaps.frobeniusGap a b - g) / a, ?_, ?_⟩
    · exact Nat.lt_succ_of_le (Nat.div_le_div_right (by omega))
    · rw [Nat.div_mul_cancel hdf]
      omega
  · rintro ⟨j, hj, rfl⟩
    refine sub_mem_upperBoundary hco ha hab ?_ ⟨j, by ring⟩
    exact (Nat.mul_le_mul (Nat.le_of_lt_succ hj) (le_refl a)).trans
      (Nat.div_mul_le_self _ _)

/-- The chain stops below zero: `f - (L + 1) * a < 0`, which over the naturals reads
`f < (L + 1) * a`. -/
@[hjo "lem_chain_bottom_neg"]
theorem frobeniusGap_lt (a b : ℕ) (ha : 0 < a) :
    Gaps.frobeniusGap a b < (Defs.boundaryLength a b + 1) * a := by
  calc Gaps.frobeniusGap a b
      = a * (Gaps.frobeniusGap a b / a) + Gaps.frobeniusGap a b % a := (Nat.div_add_mod _ _).symm
    _ < a * (Gaps.frobeniusGap a b / a) + a := Nat.add_lt_add_left (Nat.mod_lt _ ha) _
    _ = (Defs.boundaryLength a b + 1) * a := by rw [Defs.boundaryLength]; ring

/-! ### The three families of factors -/

/-- The upper boundary factors telescope:
`∏_{g ∈ 𝓑} (q)_{N - n_{g-a}} / (q)_{N - n_g} = (q)_N / (q)_{N - n_f}`. -/
@[hjo "lem_boundary_telescope"]
theorem prod_upperBoundary_telescope {a b : ℕ} (hco : a.Coprime b) (ha : 1 < a) (hab : a < b)
    (N : ℕ) (n : (finspan {a, b}).gaps → ℕ) :
    ∏ g ∈ Defs.upperBoundary a b,
        (((X; X)_(N - HJO.extendNat n (g - a)) : ℤ⟦X⟧) *
          invOfUnit (X; X)_(N - HJO.extendNat n g) 1)
      = ((X; X)_N : ℤ⟦X⟧) *
          invOfUnit (X; X)_(N - HJO.extendNat n (Gaps.frobeniusGap a b)) 1 := by
  have ha0 : 0 < a := by omega
  have hle : ∀ j ≤ Defs.boundaryLength a b, j * a ≤ Gaps.frobeniusGap a b := fun j hj =>
    (Nat.mul_le_mul hj (le_refl a)).trans (Nat.div_mul_le_self _ _)
  have hinj : Set.InjOn (fun j => Gaps.frobeniusGap a b - j * a)
      ↑(range (Defs.boundaryLength a b + 1)) := by
    intro j hj k hk hjk
    simp only [Finset.coe_range, Set.mem_Iio] at hj hk
    have hjk' : Gaps.frobeniusGap a b - j * a = Gaps.frobeniusGap a b - k * a := hjk
    have h1 := Nat.sub_sub_self (hle j (by omega))
    have h2 := Nat.sub_sub_self (hle k (by omega))
    rw [hjk'] at h1
    exact Nat.eq_of_mul_eq_mul_right ha0 (h1.symm.trans h2)
  rw [upperBoundary_eq_image hco ha hab, Finset.prod_image hinj]
  calc ∏ j ∈ range (Defs.boundaryLength a b + 1),
          (((X; X)_(N - HJO.extendNat n (Gaps.frobeniusGap a b - j * a - a)) : ℤ⟦X⟧) *
            invOfUnit (X; X)_(N - HJO.extendNat n (Gaps.frobeniusGap a b - j * a)) 1)
      = ∏ j ∈ range (Defs.boundaryLength a b + 1),
          (((X; X)_(N - HJO.extendNat n (Gaps.frobeniusGap a b - (j + 1) * a)) : ℤ⟦X⟧) *
            invOfUnit (X; X)_(N - HJO.extendNat n (Gaps.frobeniusGap a b - j * a)) 1) :=
        Finset.prod_congr rfl fun j _ => by rw [Nat.sub_sub, Nat.succ_mul]
    _ = ((X; X)_(N - HJO.extendNat n
            (Gaps.frobeniusGap a b - (Defs.boundaryLength a b + 1) * a)) : ℤ⟦X⟧) *
          invOfUnit (X; X)_(N - HJO.extendNat n (Gaps.frobeniusGap a b - 0 * a)) 1 :=
        prod_mul_inv_telescope
          (c := fun j => ((X; X)_(N - HJO.extendNat n (Gaps.frobeniusGap a b - j * a)) : ℤ⟦X⟧))
          (d := fun j => invOfUnit (X; X)_(N - HJO.extendNat n (Gaps.frobeniusGap a b - j * a)) 1)
          fun j _ => ReturnPathSolves.qPochhammer_mul_inv _
    _ = _ := by
        rw [Nat.sub_eq_zero_of_le (frobeniusGap_lt a b ha0).le]
        simp

/-- The lower boundary factors are trivial: at a gap `h` whose lower shift `h - b` leaves the gap
set, `(q)_{n_h - n_{h-a-b}} / (q)_{n_h - n_{h-b}} = 1`. -/
@[hjo "lem_lower_boundary_trivial"]
theorem lower_boundary_factor_eq_one {a b h : ℕ} (hco : a.Coprime b)
    (n : (finspan {a, b}).gaps → ℕ) (hh : h ∈ (finspan {a, b}).gaps)
    (hhb : h - b ∉ (finspan {a, b}).gaps) :
    ((X; X)_(HJO.extendNat n h - HJO.extendNat n (h - (a + b))) : ℤ⟦X⟧) *
        invOfUnit (X; X)_(HJO.extendNat n h - HJO.extendNat n (h - b)) 1 = 1 := by
  have hlt : h < b :=
    lt_of_sub_notMem_gaps hh (Gaps.mem_finspan_right (gcd_pair_eq_one hco)) hhb
  rw [Nat.sub_eq_zero_of_le (by omega : h ≤ b), Nat.sub_eq_zero_of_le (by omega : h ≤ a + b),
    HJO.extendNat_gaps_zero, Nat.sub_zero]
  exact ReturnPathSolves.qPochhammer_mul_inv _

/-- The interior factors match under the `b`-shift: the product over the gaps whose upper shift
stays in the gap set equals the product over the gaps whose lower shift stays in it. -/
@[hjo "lem_interior_match"]
theorem prod_interior_match {a b : ℕ} (n : (finspan {a, b}).gaps → ℕ) :
    ∏ g ∈ {g ∈ (finspan {a, b}).gaps | g + b ∈ (finspan {a, b}).gaps},
        (((X; X)_(HJO.extendNat n (g + b) - HJO.extendNat n (g - a)) : ℤ⟦X⟧) *
          invOfUnit (X; X)_(HJO.extendNat n (g + b) - HJO.extendNat n g) 1)
      = ∏ h ∈ {h ∈ (finspan {a, b}).gaps | h - b ∈ (finspan {a, b}).gaps},
        (((X; X)_(HJO.extendNat n h - HJO.extendNat n (h - (a + b))) : ℤ⟦X⟧) *
          invOfUnit (X; X)_(HJO.extendNat n h - HJO.extendNat n (h - b)) 1) := by
  have hb : ∀ h ∈ {h ∈ (finspan {a, b}).gaps | h - b ∈ (finspan {a, b}).gaps}, b ≤ h := by
    intro h hh
    simp only [Finset.mem_filter] at hh
    by_contra hc
    rw [Nat.sub_eq_zero_of_le (by omega)] at hh
    exact (finspan {a, b}).zero_notMem_gaps hh.2
  refine Finset.prod_nbij' (fun g => g + b) (fun h => h - b) ?_ ?_ ?_ ?_ ?_
  · intro g hg
    simp only [Finset.mem_filter] at hg ⊢
    exact ⟨hg.2, by rw [Nat.add_sub_cancel]; exact hg.1⟩
  · intro h hh
    have hbh := hb h hh
    simp only [Finset.mem_filter] at hh ⊢
    exact ⟨hh.2, by rw [Nat.sub_add_cancel hbh]; exact hh.1⟩
  · exact fun g _ => Nat.add_sub_cancel g b
  · exact fun h hh => Nat.sub_add_cancel (hb h hh)
  · intro g _
    rw [show g + b - (a + b) = g - a from by omega, Nat.add_sub_cancel]

/-! ### Expansion of the Gaussian factors -/

/-- The Gaussian binomial at integer arguments in range, expanded as a quotient of
`q`-factorials. -/
theorem gaussBinom_eq_of_le {p q r : ℕ} (hqp : q ≤ p) (hpr : p ≤ r) :
    HJO.Defs.gaussBinom ((r : ℤ) - (q : ℤ)) ((p : ℤ) - (q : ℤ))
      = ((X; X)_(r - q) : ℤ⟦X⟧) * invOfUnit (X; X)_(p - q) 1 * invOfUnit (X; X)_(r - p) 1 := by
  have hguard : 0 ≤ (p : ℤ) - (q : ℤ) ∧ (p : ℤ) - (q : ℤ) ≤ (r : ℤ) - (q : ℤ) :=
    ⟨by omega, by omega⟩
  rw [HJO.Defs.gaussBinom,
    show ((r : ℤ) - (q : ℤ)).toNat = r - q from by omega,
    show ((p : ℤ) - (q : ℤ)).toNat = p - q from by omega,
    show ((r : ℤ) - (q : ℤ) - ((p : ℤ) - (q : ℤ))).toNat = r - p from by omega]
  simp only [hguard, and_self, ite_true]

/-- Expansion of the Gaussian factors of the traverse: each Gaussian binomial coefficient
`[n̂_{g+b} - n_{g-a}, n_g - n_{g-a}]_q` is the quotient
`(q)_{n̂_{g+b} - n_{g-a}} / ((q)_{n_g - n_{g-a}} (q)_{n̂_{g+b} - n_g})`. -/
@[hjo "lem_gauss_factor_expand"]
theorem prod_gaussBinom_expand {a b N : ℕ} (hco : a.Coprime b) (ha : 1 < a) (hab : a < b)
    {n : (finspan {a, b}).gaps → ℕ} (hn : (fun g => (n g : ℤ)) ∈ HJO.cone a b)
    (hfN : HJO.extendNat n (Gaps.frobeniusGap a b) ≤ N) :
    ∏ g : (finspan {a, b}).gaps,
        HJO.Defs.gaussBinom
          ((Gaps.flag a b N n (((g : ℕ) : ℤ) + b) : ℤ) - (HJO.extendNat n ((g : ℕ) - a) : ℤ))
          ((n g : ℤ) - (HJO.extendNat n ((g : ℕ) - a) : ℤ))
      = ∏ g : (finspan {a, b}).gaps,
          (((X; X)_(Gaps.flag a b N n (((g : ℕ) : ℤ) + b) -
              HJO.extendNat n ((g : ℕ) - a)) : ℤ⟦X⟧) *
            invOfUnit (X; X)_(n g - HJO.extendNat n ((g : ℕ) - a)) 1 *
            invOfUnit (X; X)_(Gaps.flag a b N n (((g : ℕ) : ℤ) + b) - n g) 1) := by
  refine Finset.prod_congr rfl fun g _ => ?_
  have hlow := extendNat_sub_le hco hn g.2 (Gaps.mem_finspan_left (gcd_pair_eq_one hco))
  have hup := le_flag_add hco ha hab hn hfN g.2
  rw [← HJO.extendNat_subtype n g] at hlow hup
  exact gaussBinom_eq_of_le hlow hup

/-! ### The reduced traverse identity -/

/-- The interior part of the traverse product, with the flag resolved to the cone value. -/
theorem prod_interior_flag {a b N : ℕ} (n : (finspan {a, b}).gaps → ℕ) :
    ∏ j ∈ {j ∈ (finspan {a, b}).gaps | j + b ∈ (finspan {a, b}).gaps},
        (((X; X)_(Gaps.flag a b N n ((j : ℤ) + b) - HJO.extendNat n (j - a)) : ℤ⟦X⟧) *
          invOfUnit (X; X)_(Gaps.flag a b N n ((j : ℤ) + b) - HJO.extendNat n j) 1)
      = ∏ j ∈ {j ∈ (finspan {a, b}).gaps | j - b ∈ (finspan {a, b}).gaps},
        (((X; X)_(HJO.extendNat n j - HJO.extendNat n (j - (a + b))) : ℤ⟦X⟧) *
          invOfUnit (X; X)_(HJO.extendNat n j - HJO.extendNat n (j - b)) 1) := by
  rw [← prod_interior_match n]
  refine Finset.prod_congr rfl fun j hj => ?_
  simp only [Finset.mem_filter] at hj
  rw [flag_add_of_mem n hj.2]

/-- The boundary part of the traverse product, evaluated by the telescope. -/
theorem prod_boundary_flag {a b : ℕ} (hco : a.Coprime b) (ha : 1 < a) (hab : a < b)
    (N : ℕ) (n : (finspan {a, b}).gaps → ℕ) :
    ∏ j ∈ {j ∈ (finspan {a, b}).gaps | ¬ (j + b ∈ (finspan {a, b}).gaps)},
        (((X; X)_(Gaps.flag a b N n ((j : ℤ) + b) - HJO.extendNat n (j - a)) : ℤ⟦X⟧) *
          invOfUnit (X; X)_(Gaps.flag a b N n ((j : ℤ) + b) - HJO.extendNat n j) 1)
      = ((X; X)_N : ℤ⟦X⟧) *
          invOfUnit (X; X)_(N - HJO.extendNat n (Gaps.frobeniusGap a b)) 1 := by
  rw [show {j ∈ (finspan {a, b}).gaps | ¬ (j + b ∈ (finspan {a, b}).gaps)}
      = Defs.upperBoundary a b from rfl, ← prod_upperBoundary_telescope hco ha hab N n]
  refine Finset.prod_congr rfl fun j hj => ?_
  rw [flag_add_of_notMem n (Defs.mem_upperBoundary.mp hj).2]

/-- The lower boundary part of the gap product is trivial. -/
theorem prod_lower_boundary_eq_one {a b : ℕ} (hco : a.Coprime b)
    (n : (finspan {a, b}).gaps → ℕ) :
    ∏ j ∈ {j ∈ (finspan {a, b}).gaps | ¬ (j - b ∈ (finspan {a, b}).gaps)},
        (((X; X)_(HJO.extendNat n j - HJO.extendNat n (j - (a + b))) : ℤ⟦X⟧) *
          invOfUnit (X; X)_(HJO.extendNat n j - HJO.extendNat n (j - b)) 1) = 1 := by
  refine Finset.prod_eq_one fun j hj => ?_
  simp only [Finset.mem_filter] at hj
  exact lower_boundary_factor_eq_one hco n hj.1 hj.2

/-- The reduced traverse identity:
`(q)_N / (q)_{N - n_f} * ∏_{g ∈ G} (q)_{n_g - n_{g-a-b}} / (q)_{n_g - n_{g-b}}
  = ∏_{g ∈ G} (q)_{n̂_{g+b} - n_{g-a}} / (q)_{n̂_{g+b} - n_g}`. -/
@[hjo "lem_reduced_traverse"]
theorem reduced_traverse {a b : ℕ} (hco : a.Coprime b) (ha : 1 < a) (hab : a < b)
    (N : ℕ) (n : (finspan {a, b}).gaps → ℕ) :
    ((X; X)_N : ℤ⟦X⟧) * invOfUnit (X; X)_(N - HJO.extendNat n (Gaps.frobeniusGap a b)) 1 *
        ∏ g : (finspan {a, b}).gaps,
          (((X; X)_(n g - HJO.extendNat n ((g : ℕ) - (a + b))) : ℤ⟦X⟧) *
            invOfUnit (X; X)_(n g - HJO.extendNat n ((g : ℕ) - b)) 1)
      = ∏ g : (finspan {a, b}).gaps,
          (((X; X)_(Gaps.flag a b N n (((g : ℕ) : ℤ) + b) -
              HJO.extendNat n ((g : ℕ) - a)) : ℤ⟦X⟧) *
            invOfUnit (X; X)_(Gaps.flag a b N n (((g : ℕ) : ℤ) + b) - n g) 1) := by
  have hLprod : ∏ g : (finspan {a, b}).gaps,
        (((X; X)_(n g - HJO.extendNat n ((g : ℕ) - (a + b))) : ℤ⟦X⟧) *
          invOfUnit (X; X)_(n g - HJO.extendNat n ((g : ℕ) - b)) 1)
      = ∏ j ∈ (finspan {a, b}).gaps,
        (((X; X)_(HJO.extendNat n j - HJO.extendNat n (j - (a + b))) : ℤ⟦X⟧) *
          invOfUnit (X; X)_(HJO.extendNat n j - HJO.extendNat n (j - b)) 1) := by
    refine Eq.trans (Finset.prod_congr rfl fun g _ => ?_)
      (ReturnPathSolves.prod_gaps_type a b fun j =>
        ((X; X)_(HJO.extendNat n j - HJO.extendNat n (j - (a + b))) : ℤ⟦X⟧) *
          invOfUnit (X; X)_(HJO.extendNat n j - HJO.extendNat n (j - b)) 1)
    rw [HJO.extendNat_subtype n g]
  have hRprod : ∏ g : (finspan {a, b}).gaps,
        (((X; X)_(Gaps.flag a b N n (((g : ℕ) : ℤ) + b) -
            HJO.extendNat n ((g : ℕ) - a)) : ℤ⟦X⟧) *
          invOfUnit (X; X)_(Gaps.flag a b N n (((g : ℕ) : ℤ) + b) - n g) 1)
      = ∏ j ∈ (finspan {a, b}).gaps,
        (((X; X)_(Gaps.flag a b N n ((j : ℤ) + b) - HJO.extendNat n (j - a)) : ℤ⟦X⟧) *
          invOfUnit (X; X)_(Gaps.flag a b N n ((j : ℤ) + b) - HJO.extendNat n j) 1) := by
    refine Eq.trans (Finset.prod_congr rfl fun g _ => ?_)
      (ReturnPathSolves.prod_gaps_type a b fun j =>
        ((X; X)_(Gaps.flag a b N n ((j : ℤ) + b) - HJO.extendNat n (j - a)) : ℤ⟦X⟧) *
          invOfUnit (X; X)_(Gaps.flag a b N n ((j : ℤ) + b) - HJO.extendNat n j) 1)
    rw [HJO.extendNat_subtype n g]
  rw [hLprod, hRprod,
    ← Finset.prod_filter_mul_prod_filter_not (finspan {a, b}).gaps
      (fun j => j - b ∈ (finspan {a, b}).gaps),
    ← Finset.prod_filter_mul_prod_filter_not (finspan {a, b}).gaps
      (fun j => j + b ∈ (finspan {a, b}).gaps),
    prod_lower_boundary_eq_one hco n, prod_interior_flag n,
    prod_boundary_flag hco ha hab N n, mul_one]
  ring

end HJO.GoodTraverse
