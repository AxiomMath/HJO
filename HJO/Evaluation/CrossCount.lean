/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.Paths.ReturnPath
public meta import HJO.Attr

/-! # The multiplicative evaluation of the cross count of two order filters

For coprime `1 < a < b` an order filter `F` of the gap set `G` of `Γ = ⟨a, b⟩` is read through
its flag set `F̂`, the integers marked by the flag extension of the indicator vector `1_F` at
level `N = 1`. The flag set is the union `F ∪ Γ`, it is closed under adding elements of `Γ`, and
it sees the primitive path `P_F` through the heights of that path: `rb - ai ∈ F̂` exactly when
`i ≤ y_r`. That reading is what labels the steps of `P_F` by the integers the flag set sees
them at: the north rank `ρ_F(i)` and the east rank `σ_F(r)`.

On that dictionary the cross count `J(F, H)` of the primitive blocks is evaluated. Against the
empty filter its value is the baseline `d - 1`, corrected on the left by the indicator of the
Frobenius gap `f`, and its second difference in the two arguments is a bilinear sum of the pair
kernel `K*`. The pair kernel is the shifted sum `K(t-1) + K(-t)` of two kernels, so it exceeds
the symmetrised kernel `K(t) + K(-t)` by four point masses, at `0`, `a`, `b` and `d`. Since `f`
is the only gap both of whose translates by `a` and by `b` lie in `Γ`, those masses collect into
the ordered part `I(F, H)`, and `J(F, H)` is the baseline plus the symmetric kernel term plus
`I(F, H)`. The symmetric kernel term is the cross term of the polarisation of the quadratic
form `Q` of the gap set.

## Main results

* `flag_eq_one_iff`: the flag set is the filter together with the semigroup.
* `flag_add_eq_one`: the flag set is closed under adding an element of `Γ`.
* `flag_eq_one_iff_le_ht`: the flag set reads the heights of `P_F`.
* `pairKernel_eq`, `pairKernel_sub_kernel`: the pair kernel as a shifted sum of two kernels, and
  its excess over the symmetrised kernel.
* `crossCount_empty_left`, `crossCount_empty_right`, `crossCount_sub_crossCount`: the cross count
  against the empty filter, and the second difference of the cross count.
* `indicator_add_mem_finspan`: the Frobenius gap is the only gap whose translates by `a` and by
  `b` both lie in the semigroup.
* `orderedPart_eq_card`, `crossCount_eq`: the ordered part as a signed count of translates, and
  the evaluation of the cross count.

## Implementation notes

The flag set `F̂` is not given a name of its own here: membership of `j` in it is spelled as the
level-one flag extension of `1_F` taking the value `1` at `j`, which is the form in which
`HJO.Gaps.flag` is available, and `flag_eq_one_iff` is the characterisation that lets the
remaining results be read without unfolding it. Membership in the union `F ∪ Γ` is likewise
recorded pointwise: a subset of `ℕ` is read inside `ℤ` through `Int.toNat`, so it is `0 ≤ j`
together with `j.toNat ∈ F ∪ Γ`.

The rank window `w`, the pair kernel `K*`, the cross count `J` and the ordered part `I` are the
`HJO.ReturnPath` vocabulary `rankWeight`, `crossKernel`, `crossCount` and `orderedPart`, and
`J(F, H)` is the cross count of the primitive blocks `P_F` and `P_H`. The evaluation of `J` against
the empty filter, its second difference and its ordered form are read off the already-available
evaluation `HJO.ReturnPath.crossCount_primitivePath_eq`, which combines three statements; the usual
argument derives that combination from the three, and the file records the three as its
consequences instead.

The two rank bijections `HJO.MultiplicativeEvaluation.bijOn_northRank` and
`HJO.MultiplicativeEvaluation.bijOn_eastRank`, and its polarisation `HJO.Gaps.q_sum_eq` of the
quadratic form at a sum of gap vectors, are proved downstream of this file:
`HJO.MultiplicativeEvaluation.bijOn_northRank` and `HJO.MultiplicativeEvaluation.bijOn_eastRank` in
`HJO/Complements.lean`, and `HJO.Gaps.q_sum_eq` in `HJO/Corollaries.lean`.

The counts are integer valued throughout, including the cross count, which is a cardinality: the
evaluations subtract, and the baseline `d - 1` is a difference.

## References

The multiplicative evaluation: the lemmas `HJO.MultiplicativeEvaluation.flag_eq_one_iff`,
`HJO.MultiplicativeEvaluation.flag_add_eq_one`,
`HJO.MultiplicativeEvaluation.flag_eq_one_iff_le_ht`, `HJO.MultiplicativeEvaluation.pairKernel_eq`,
`HJO.MultiplicativeEvaluation.pairKernel_sub_kernel`,
`HJO.MultiplicativeEvaluation.crossCount_empty_left`,
`HJO.MultiplicativeEvaluation.crossCount_empty_right`,
`HJO.MultiplicativeEvaluation.crossCount_sub_crossCount`,
`HJO.MultiplicativeEvaluation.indicator_add_mem_finspan`,
`HJO.MultiplicativeEvaluation.orderedPart_eq_card`, `HJO.MultiplicativeEvaluation.crossCount_eq`.
-/

@[expose] public section

open Finset NumericalSemigroup

namespace HJO.MultiplicativeEvaluation

open HJO.ReturnPath HJO.Primitive

variable {a b : ℕ} {F H : Finset ℕ}

/-! ### The flag set of an order filter -/

/-- A natural number lies in `Γ = ⟨a, b⟩` exactly when it is a nonnegative combination of the
generators: the positive counterpart of `HJO.Gaps.mem_gaps_iff_not_exists`. -/
private theorem mem_finspan_iff_exists (hco : a.Coprime b) (n : ℕ) :
    n ∈ finspan {a, b} ↔ ∃ u v : ℕ, u * a + v * b = n := by
  rw [← not_iff_not, ← (finspan {a, b}).mem_gaps_iff, Gaps.mem_gaps_iff_not_exists a b hco]

/-- Membership in a numerical semigroup is decidable: its complement in `ℕ` is the finite set
of gaps. -/
instance decidableMemNumericalSemigroup (s : NumericalSemigroup) (n : ℕ) :
    Decidable (n ∈ s) :=
  decidable_of_iff (n ∉ s.gaps) (by rw [s.mem_gaps_iff, not_not])

/-- **The flag set is the filter together with the semigroup**: `F̂ = F ∪ Γ`, read pointwise
inside `ℤ`. -/
@[hjo "lem_ret_flag_semigroup"]
theorem flag_eq_one_iff {j : ℤ} :
    Gaps.flag a b 1 (fun g => if (g : ℕ) ∈ F then 1 else 0) j = 1 ↔
      0 ≤ j ∧ (j.toNat ∈ F ∨ j.toNat ∈ finspan {a, b}) := by
  rw [Gaps.flag]
  split_ifs with hj hg
  · have hj0 : ¬ (0 ≤ j) := by omega
    simp [hj0]
  · have hn : j.toNat ∉ finspan {a, b} := ((finspan {a, b}).mem_gaps_iff).mp hg
    have hj0 : 0 ≤ j := by omega
    rw [GapPoset.extendNat_of_mem _ hg]
    simp only [hj0, true_and, hn, or_false]
    split_ifs with hmem <;> simp [hmem]
  · have hm : j.toNat ∈ finspan {a, b} := by
      by_contra h
      exact hg (((finspan {a, b}).mem_gaps_iff).mpr h)
    exact iff_of_true rfl ⟨by omega, Or.inr hm⟩

/-- **The flag set is closed under adding an element of the semigroup**. -/
@[hjo "lem_ret_flag_monotone"]
theorem flag_add_eq_one (hco : a.Coprime b) (hF : Gaps.IsOrderFilter a b F) {j : ℤ} {s : ℕ}
    (hs : s ∈ finspan {a, b})
    (hj : Gaps.flag a b 1 (fun g => if (g : ℕ) ∈ F then 1 else 0) j = 1) :
    Gaps.flag a b 1 (fun g => if (g : ℕ) ∈ F then 1 else 0) (j + s) = 1 := by
  rw [flag_eq_one_iff] at hj ⊢
  obtain ⟨hj0, hcase⟩ := hj
  obtain ⟨u, v, huv⟩ := (mem_finspan_iff_exists hco s).mp hs
  refine ⟨by omega, ?_⟩
  have htn : (j + s).toNat = j.toNat + s := by omega
  rw [htn]
  rcases hcase with hmem | hmem
  · by_cases hgap : j.toNat + s ∈ (finspan {a, b}).gaps
    · exact Or.inl (hF.2 _ hmem _ hgap ⟨u, v, by omega⟩)
    · refine Or.inr ?_
      by_contra h
      exact hgap (((finspan {a, b}).mem_gaps_iff).mpr h)
  · obtain ⟨u', v', huv'⟩ := (mem_finspan_iff_exists hco _).mp hmem
    exact Or.inr ((mem_finspan_iff_exists hco _).mpr ⟨u' + u, v' + v, by ring_nf; omega⟩)

/-! ### The flag set and the heights of the primitive path -/

/-- **The flag set reads the heights of the primitive path**: `rb - ai ∈ F̂` exactly when the
`r`-th height of `P_F` reaches `i`. -/
@[hjo "lem_ret_flag_heights"]
theorem flag_eq_one_iff_le_ht (hco : a.Coprime b) (ha : 0 < a)
    (hF : Gaps.IsOrderFilter a b F) {r i : ℕ} (hr : r ≤ a) :
    Gaps.flag a b 1 (fun g => if (g : ℕ) ∈ F then 1 else 0) ((r : ℤ) * b - a * i) = 1 ↔
      i ≤ Paths.ht (primitivePath a b F) r := by
  have ha' : (0 : ℤ) < a := by exact_mod_cast ha
  rw [flag_eq_one_iff]
  rcases Nat.eq_zero_or_pos i with rfl | hi1
  · have hcast : ((r : ℤ) * b - a * ((0 : ℕ) : ℤ)) = ((r * b : ℕ) : ℤ) := by
      push_cast; ring
    have htn : (((r * b : ℕ) : ℤ)).toNat = r * b := by omega
    rw [hcast, htn]
    exact iff_of_true ⟨Int.natCast_nonneg _,
      Or.inr ((mem_finspan_iff_exists hco (r * b)).mpr ⟨0, r, by ring⟩)⟩ (Nat.zero_le _)
  · have hi' : (0 : ℤ) < i := by exact_mod_cast hi1
    rcases Nat.eq_zero_or_pos r with rfl | hr1
    · have hneg : ((0 : ℕ) : ℤ) * b - a * i < 0 := by
        have : (0 : ℤ) < (a : ℤ) * i := by positivity
        simpa using this
      rw [ht_primitivePath_zero F ha]
      exact iff_of_false (fun h => absurd h.1 (not_le.mpr hneg)) (by omega)
    · rcases eq_or_lt_of_le hr with rfl | hra
      · rw [ht_primitivePath_self]
        rcases lt_or_ge b i with hib | hib
        · have hb' : (b : ℤ) < i := by exact_mod_cast hib
          have hneg : (r : ℤ) * b - r * i < 0 := by nlinarith
          exact iff_of_false (fun h => absurd h.1 (not_le.mpr hneg)) (by omega)
        · have hcast : ((r : ℤ) * b - r * i) = ((r * (b - i) : ℕ) : ℤ) := by
            rw [Nat.cast_mul, Nat.cast_sub hib]
            ring
          have htn : (((r * (b - i) : ℕ) : ℤ)).toNat = r * (b - i) := by omega
          rw [hcast, htn]
          exact iff_of_true ⟨Int.natCast_nonneg _,
            Or.inr ((mem_finspan_iff_exists hco (r * (b - i))).mpr ⟨b - i, 0, by ring⟩)⟩ hib
      · rw [ht_primitivePath_of_lt F hra]
        rcases lt_or_ge (a * i) (r * b) with hlt | hge
        · have hgap : r * b - a * i ∈ (finspan {a, b}).gaps := mem_gaps_of_sub hco hra hi1 hlt
          have hn : (r * b - a * i) ∉ finspan {a, b} :=
            ((finspan {a, b}).mem_gaps_iff).mp hgap
          have hcast : ((r : ℤ) * b - a * i) = ((r * b - a * i : ℕ) : ℤ) := by
            rw [Nat.cast_sub hlt.le]
            push_cast
            ring
          have hib : i < b := by
            have h1 : a * i < a * b :=
              lt_of_lt_of_le hlt (Nat.mul_le_mul (by omega) le_rfl)
            exact Nat.lt_of_mul_lt_mul_left h1
          have htn : (((r * b - a * i : ℕ) : ℤ)).toNat = r * b - a * i := by omega
          rw [hcast, htn]
          refine ⟨fun h => ?_, fun h => ?_⟩
          · refine (le_primitiveHeight_iff hco hF hra hi1).mpr ⟨hib.le, hlt, ?_⟩
            rcases h.2 with h2 | h2
            · exact h2
            · exact absurd h2 hn
          · obtain ⟨-, -, hmem⟩ := (le_primitiveHeight_iff hco hF hra hi1).mp h
            exact ⟨Int.natCast_nonneg _, Or.inl hmem⟩
        · have hgt : r * b < a * i := by
            have hne : a * i ≠ r * b := mul_ne_mul_of_lt hco hr1 hra
            omega
          have hneg : ((r : ℤ) * b - a * i) < 0 := by
            have h2 : ((r * b : ℕ) : ℤ) < ((a * i : ℕ) : ℤ) := by exact_mod_cast hgt
            push_cast at h2
            linarith
          refine iff_of_false (fun h => absurd h.1 (not_le.mpr hneg)) fun h => ?_
          obtain ⟨-, h2, -⟩ := (le_primitiveHeight_iff hco hF hra hi1).mp h
          omega

/-! ### The pair kernel -/

/-- **The pair kernel is a shifted sum of two kernels**: `K*(t) = K(t-1) + K(-t)`. -/
@[hjo "lem_ret_kernel_shift"]
theorem pairKernel_eq (a b : ℕ) (t : ℤ) :
    crossKernel a b t = HJO.U a b (t - 1) + HJO.U a b (-t) :=
  crossKernel_eq_u a b t

/-- **The pair kernel exceeds the symmetrised kernel by four point masses**, at `a` and `b`
positively and at `0` and `d = a + b` negatively. -/
@[hjo "lem_ret_kernel_defect"]
theorem pairKernel_sub_kernel (a b : ℕ) (t : ℤ) :
    crossKernel a b t - HJO.U a b t - HJO.U a b (-t)
      = (if t = (a : ℤ) then 1 else 0) + (if t = (b : ℤ) then 1 else 0)
        - (if t = 0 then 1 else 0) - (if t = (a : ℤ) + b then 1 else 0) :=
  crossKernel_sub_u a b t

/-! ### The cross count against the empty filter -/

/-- The empty finset is an order filter of the gap set. -/
private theorem isOrderFilter_empty : Gaps.IsOrderFilter a b ∅ := ⟨by simp, by simp⟩

/-- **The cross count with empty earlier filter is the baseline** `d - 1`. -/
@[hjo "lem_ret_cross_left_empty"]
theorem crossCount_empty_left (hco : a.Coprime b) (ha : 1 < a)
    (hH : Gaps.IsOrderFilter a b H) :
    (crossCount (primitivePath a b ∅) (primitivePath a b H) : ℤ) = (a : ℤ) + b - 1 := by
  rw [crossCount_primitivePath_eq hco ha isOrderFilter_empty hH]
  simp

/-- **The cross count with empty later filter is the baseline corrected by the Frobenius gap**. -/
@[hjo "lem_ret_cross_right_empty"]
theorem crossCount_empty_right (hco : a.Coprime b) (ha : 1 < a)
    (hF : Gaps.IsOrderFilter a b F) :
    (crossCount (primitivePath a b F) (primitivePath a b ∅) : ℤ)
      = (a : ℤ) + b - 1 + (if Gaps.frobeniusGap a b ∈ F then 1 else 0) := by
  rw [crossCount_primitivePath_eq hco ha hF isOrderFilter_empty]
  simp

/-- **The second difference of the cross count is the bilinear pair-kernel sum**. -/
@[hjo "lem_ret_cross_split"]
theorem crossCount_sub_crossCount (hco : a.Coprime b) (ha : 1 < a)
    (hF : Gaps.IsOrderFilter a b F) (hH : Gaps.IsOrderFilter a b H) :
    (crossCount (primitivePath a b F) (primitivePath a b H) : ℤ)
        - (crossCount (primitivePath a b F) (primitivePath a b ∅) : ℤ)
        - (crossCount (primitivePath a b ∅) (primitivePath a b H) : ℤ)
        + (crossCount (primitivePath a b ∅) (primitivePath a b ∅) : ℤ)
      = ∑ g ∈ F, ∑ h ∈ H, crossKernel a b ((h : ℤ) - g) := by
  rw [crossCount_primitivePath_eq hco ha hF hH, crossCount_empty_right hco ha hF,
    crossCount_empty_left hco ha hH, crossCount_empty_left hco ha isOrderFilter_empty]
  ring

/-! ### The ordered part -/

/-- **The ordered part is a signed count of translates of the earlier filter**. -/
@[hjo "lem_ret_ordered_gap_part"]
theorem orderedPart_eq_card (a b : ℕ) (F H : Finset ℕ) :
    orderedPart a b F H = (#{g ∈ F | g + a ∈ H} : ℤ) + (#{g ∈ F | g + b ∈ H} : ℤ)
      - (#(F ∩ H) : ℤ) - (#{g ∈ F | g + a + b ∈ H} : ℤ)
      + (if Gaps.frobeniusGap a b ∈ F then 1 else 0) := by
  have key : ∀ c : ℕ, ∑ g ∈ F, (if g + c ∈ H then (1 : ℤ) else 0)
      = (#{g ∈ F | g + c ∈ H} : ℤ) := by
    intro c
    rw [Finset.card_filter, Nat.cast_sum]
    exact Finset.sum_congr rfl fun g _ => by split_ifs <;> simp
  have key3 : ∑ g ∈ F, (if g + a + b ∈ H then (1 : ℤ) else 0)
      = (#{g ∈ F | g + a + b ∈ H} : ℤ) := by
    rw [Finset.card_filter, Nat.cast_sum]
    exact Finset.sum_congr rfl fun g _ => by split_ifs <;> simp
  have key0 : ∑ g ∈ F, (if g ∈ H then (1 : ℤ) else 0) = (#(F ∩ H) : ℤ) := by
    rw [← Finset.filter_mem_eq_inter, Finset.card_filter, Nat.cast_sum]
    exact Finset.sum_congr rfl fun g _ => by split_ifs <;> simp
  rw [orderedPart_eq, Finset.sum_sub_distrib, Finset.sum_sub_distrib, Finset.sum_add_distrib,
    key a, key b, key0, key3]
  ring

/-- **The evaluation of the cross count**: the baseline `d - 1`, the symmetrised kernel term over
the pairs of gaps, and the ordered part. -/
@[hjo "lem_ret_ordered_pair"]
theorem crossCount_eq (hco : a.Coprime b) (ha : 1 < a) (hF : Gaps.IsOrderFilter a b F)
    (hH : Gaps.IsOrderFilter a b H) :
    (crossCount (primitivePath a b F) (primitivePath a b H) : ℤ)
      = (a : ℤ) + b - 1
        + ∑ g ∈ F, ∑ h ∈ H, (HJO.U a b ((h : ℤ) - g) + HJO.U a b ((g : ℤ) - h))
        + orderedPart a b F H := by
  rw [crossCount_eq_polar hco ha hF hH, polarQ_filterVector hF.1 hH.1]

/-! ### The Frobenius gap among the translates of a gap -/

/-- **The Frobenius gap is the only gap both of whose translates by `a` and by `b` lie in the
semigroup**: the alternating indicator of the translates by `a`, `b` and `d = a + b` detects it. -/
@[hjo "lem_ret_maximal_gap"]
theorem indicator_add_mem_finspan (hco : a.Coprime b) (ha : 1 < a) (hab : a < b) {g : ℕ}
    (hg : g ∈ (finspan {a, b}).gaps) :
    (if g + a ∈ finspan {a, b} then (1 : ℤ) else 0)
        + (if g + b ∈ finspan {a, b} then (1 : ℤ) else 0)
        - (if g + (a + b) ∈ finspan {a, b} then (1 : ℤ) else 0)
      = if g = Gaps.frobeniusGap a b then 1 else 0 := by
  have hb : 1 < b := ha.trans hab
  have hgΓ : g ∉ finspan {a, b} := ((finspan {a, b}).mem_gaps_iff).mp hg
  have hfab := GapPoset.frobeniusGap_add_add a b ha hb
  have hd : g + (a + b) ∈ finspan {a, b} ↔
      (g + a ∈ finspan {a, b} ∨ g + b ∈ finspan {a, b}) := by
    rw [mem_finspan_iff_exists hco, mem_finspan_iff_exists hco, mem_finspan_iff_exists hco]
    constructor
    · rintro ⟨u, v, huv⟩
      rcases Nat.eq_zero_or_pos u with rfl | hu
      · have hv : v ≠ 0 := by rintro rfl; omega
        refine Or.inl ⟨0, v - 1, ?_⟩
        have hstep : (v - 1) * b + b = v * b := by
          obtain ⟨c, rfl⟩ : ∃ c, v = c + 1 := ⟨v - 1, by omega⟩
          simp [Nat.add_mul]
        omega
      · refine Or.inr ⟨u - 1, v, ?_⟩
        have hstep : (u - 1) * a + a = u * a := by
          obtain ⟨c, rfl⟩ : ∃ c, u = c + 1 := ⟨u - 1, by omega⟩
          simp [Nat.add_mul]
        omega
    · rintro (⟨u, v, huv⟩ | ⟨u, v, huv⟩)
      · exact ⟨u, v + 1, by rw [Nat.add_mul, Nat.one_mul]; omega⟩
      · exact ⟨u + 1, v, by rw [Nat.add_mul, Nat.one_mul]; omega⟩
  have hboth : (g + a ∈ finspan {a, b} ∧ g + b ∈ finspan {a, b}) ↔
      g = Gaps.frobeniusGap a b := by
    constructor
    · rintro ⟨hA, hB⟩
      rw [mem_finspan_iff_exists hco] at hA hB
      obtain ⟨u, v, hu⟩ := hA
      obtain ⟨u', v', hu'⟩ := hB
      have hu0 : u = 0 := by
        rcases Nat.eq_zero_or_pos u with h | h
        · exact h
        · refine absurd ((mem_finspan_iff_exists hco g).mpr ⟨u - 1, v, ?_⟩) hgΓ
          have hstep : (u - 1) * a + a = u * a := by
            obtain ⟨c, rfl⟩ : ∃ c, u = c + 1 := ⟨u - 1, by omega⟩
            simp [Nat.add_mul]
          omega
      have hv'0 : v' = 0 := by
        rcases Nat.eq_zero_or_pos v' with h | h
        · exact h
        · refine absurd ((mem_finspan_iff_exists hco g).mpr ⟨u', v' - 1, ?_⟩) hgΓ
          have hstep : (v' - 1) * b + b = v' * b := by
            obtain ⟨c, rfl⟩ : ∃ c, v' = c + 1 := ⟨v' - 1, by omega⟩
            simp [Nat.add_mul]
          omega
      subst hu0
      subst hv'0
      have hkey : (v + 1) * b = (u' + 1) * a := by
        rw [Nat.add_mul, Nat.add_mul, Nat.one_mul, Nat.one_mul]
        omega
      obtain ⟨k, hk⟩ := hco.dvd_of_dvd_mul_right (Dvd.intro (u' + 1) (by rw [hkey]; ring))
      have hgk : g + a + b = a * k * b := by
        have h1 : (v + 1) * b = a * k * b := by rw [hk]
        rw [Nat.add_mul, Nat.one_mul] at h1
        omega
      have hk0 : k ≠ 0 := by
        rintro rfl
        rw [Nat.mul_zero] at hk
        omega
      rcases lt_or_ge k 2 with hk2 | hk2
      · have hk1 : k = 1 := by omega
        rw [hk1, Nat.mul_one] at hgk
        omega
      · obtain ⟨m, rfl⟩ : ∃ m, k = m + 2 := ⟨k - 2, by omega⟩
        obtain ⟨a', rfl⟩ : ∃ a', a = a' + 2 := ⟨a - 2, by omega⟩
        obtain ⟨b', rfl⟩ : ∃ b', b = b' + 2 := ⟨b - 2, by omega⟩
        refine absurd ((mem_finspan_iff_exists hco g).mpr
          ⟨m * (b' + 2) + (b' + 1), a' + 1, ?_⟩) hgΓ
        have hpoly : (m * (b' + 2) + (b' + 1)) * (a' + 2) + (a' + 1) * (b' + 2)
            + (a' + 2) + (b' + 2) = (a' + 2) * (m + 2) * (b' + 2) := by ring
        omega
    · rintro rfl
      refine ⟨(mem_finspan_iff_exists hco _).mpr ⟨0, a - 1, ?_⟩,
        (mem_finspan_iff_exists hco _).mpr ⟨b - 1, 0, ?_⟩⟩
      · have hstep : (a - 1) * b + b = a * b := by
          obtain ⟨c, rfl⟩ : ∃ c, a = c + 1 := ⟨a - 1, by omega⟩
          simp [Nat.add_mul]
        omega
      · have hstep : (b - 1) * a + a = b * a := by
          obtain ⟨c, rfl⟩ : ∃ c, b = c + 1 := ⟨b - 1, by omega⟩
          simp [Nat.add_mul]
        have hba : b * a = a * b := Nat.mul_comm b a
        omega
  by_cases hA : g + a ∈ finspan {a, b}
  · by_cases hB : g + b ∈ finspan {a, b}
    · rw [show (if g = Gaps.frobeniusGap a b then (1 : ℤ) else 0) = 1 from by
        simp [hboth.mp ⟨hA, hB⟩]]
      simp [hA, hB, hd.mpr (Or.inl hA)]
    · have hne : g ≠ Gaps.frobeniusGap a b := fun h => hB (hboth.mpr h).2
      simp [hA, hB, hd.mpr (Or.inl hA), hne]
  · by_cases hB : g + b ∈ finspan {a, b}
    · have hne : g ≠ Gaps.frobeniusGap a b := fun h => hA (hboth.mpr h).1
      simp [hA, hB, hd.mpr (Or.inr hB), hne]
    · have hD : g + (a + b) ∉ finspan {a, b} := fun h => (hd.mp h).elim hA hB
      have hne : g ≠ Gaps.frobeniusGap a b := fun h => hA (hboth.mpr h).1
      simp [hA, hB, hD, hne]

end HJO.MultiplicativeEvaluation
