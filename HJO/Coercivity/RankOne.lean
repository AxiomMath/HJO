/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Mathlib.Data.Finset.Lattice.Fold
public import HJO.RankOneDinv.Basic
public meta import HJO.Attr

/-! # The quadratic form is at least one on a nonempty order filter

The coercivity bound needs a *strictly positive* lower bound for `Q` at the indicator vector of a
nonempty order filter, and this file supplies it. The route is Huang's rank-one identity
`Q (𝟙_F) = h (P_F)`, quoted as `HJO.External.RankOneDinv` and therefore taken as a hypothesis, plus
two facts proved here about the primitive path `P_F` of `HJO.Primitive.primitivePath`:

* a nonempty filter gives a path of positive height somewhere in the interior, because a gap `g` of
  `⟨a, b⟩` is `rb - ai` with `1 ≤ r ≤ a - 1` and `i ≥ 1`, so that `i` is one of the indices the
  height `y_r` counts;
* a below-diagonal `(a, b)`-path of positive interior height has a *balanced* hook, namely the cell
  `(r₀, i₀)` where `i₀` is the largest interior height and `r₀ = A_{i₀}` is the first column
  reaching it. There the arm and the leg both vanish, so the hook conditions read `0 ≤ a` and
  `0 < b`.

The maximum `i₀` is realised as `Finset.sup` over `Finset.Icc 1 (a - 1)`, which is nonempty because
`a > 1`; `Finset.exists_mem_eq_sup` produces the column attaining it, and that column bounds
`r₀ = HJO.Paths.firstReach y i₀` from above.
-/

@[expose] public section

open Finset NumericalSemigroup

namespace HJO.Coercivity

variable {a b : ℕ}

/-! ### A nonempty filter has a positive height -/

/-- **A nonempty filter has a positive height**: the primitive path of a nonempty order filter has
`y_r ≥ 1` for some `r` with `1 ≤ r ≤ a - 1`. -/
@[hjo "lem_primitive_path_nonzero"]
theorem exists_one_le_ht_primitivePath (hco : a.Coprime b) (ha : 1 < a) {F : Finset ℕ}
    (hF : Gaps.IsOrderFilter a b F) (hFne : F.Nonempty) :
    ∃ r, 1 ≤ r ∧ r ≤ a - 1 ∧ 1 ≤ Paths.ht (Primitive.primitivePath a b F) r := by
  obtain ⟨g, hgF⟩ := hFne
  have hgG : g ∈ (finspan {a, b}).gaps := hF.1 hgF
  have hgpos : 0 < g := RankOneDinv.pos_of_mem_gaps hco hgG
  obtain ⟨r, i, hr1, hr2, hi1, hgi⟩ :=
    RankOneDinv.exists_column_form hco (by omega : 0 < a) hgG
  refine ⟨r, hr1, hr2, ?_⟩
  have hlt : a * i < r * b := by
    have : ((a * i : ℕ) : ℤ) < ((r * b : ℕ) : ℤ) := by push_cast; omega
    exact_mod_cast this
  have hsub : r * b - a * i = g := by
    have : ((r * b - a * i : ℕ) : ℤ) = (g : ℤ) := by
      rw [Nat.cast_sub hlt.le]
      push_cast
      omega
    exact_mod_cast this
  have hib : i ≤ b := by
    have h1 : a * i < a * b := lt_of_lt_of_le hlt (Nat.mul_le_mul_right b (by omega))
    exact (Nat.lt_of_mul_lt_mul_left h1).le
  rw [Primitive.ht_primitivePath_of_lt F (by omega : r < a), Primitive.primitiveHeight]
  refine Finset.card_pos.mpr ⟨i, ?_⟩
  simp only [Finset.mem_filter, Finset.mem_Icc]
  exact ⟨⟨hi1, hib⟩, hlt, hsub ▸ hgF⟩

/-! ### A path of positive height has a balanced hook -/

/-- **A nonempty path has a balanced hook**: a below-diagonal `(a, b)`-path with `y_r ≥ 1` for at
least one `r` with `1 ≤ r ≤ a - 1` has `h (P) ≥ 1`. -/
@[hjo "lem_hook_count_positive"]
theorem one_le_hookCount (ha : 1 < a) (hb : 0 < b) {y : Paths.Heights a b 1}
    (hy : Paths.IsBelowDiagonal y) {r : ℕ} (hr1 : 1 ≤ r) (hr2 : r ≤ a - 1)
    (hyr : 1 ≤ Paths.ht y r) : 1 ≤ Paths.hookCount y := by
  have hrI : r ∈ Finset.Icc 1 (a - 1) := Finset.mem_Icc.mpr ⟨hr1, hr2⟩
  obtain ⟨r₁, hr₁I, hr₁⟩ :=
    Finset.exists_mem_eq_sup (Finset.Icc 1 (a - 1)) ⟨r, hrI⟩ (Paths.ht y)
  set i₀ := (Finset.Icc 1 (a - 1)).sup (Paths.ht y)
  have hi₀one : 1 ≤ i₀ := hyr.trans (Finset.le_sup hrI)
  have hi₀b : i₀ ≤ b := by
    rw [hr₁]
    simpa using RankOneDinv.ht_le_mul y r₁
  have hend : Paths.ht y (a * 1) = b * 1 := hy.2.1
  have hi₀ht : i₀ ≤ Paths.ht y (Paths.firstReach y i₀) :=
    ReturnPath.le_ht_firstReach y (by rw [hend]; omega)
  have hr₁le : Paths.firstReach y i₀ ≤ r₁ :=
    ReturnPath.firstReach_le y (by have := (Finset.mem_Icc.mp hr₁I).2; omega) (by rw [hr₁])
  have hr₀2 : Paths.firstReach y i₀ ≤ a - 1 := hr₁le.trans (Finset.mem_Icc.mp hr₁I).2
  have hr₀1 : 1 ≤ Paths.firstReach y i₀ := RankOneDinv.one_le_firstReach hy hi₀one hi₀ht
  have hht₀ : Paths.ht y (Paths.firstReach y i₀) ≤ i₀ :=
    Finset.le_sup (Finset.mem_Icc.mpr ⟨hr₀1, hr₀2⟩)
  have harm : Paths.arm y (Paths.firstReach y i₀) i₀ = 0 := Nat.sub_self _
  have hleg : Paths.leg y (Paths.firstReach y i₀) i₀ = 0 := Nat.sub_eq_zero_of_le hht₀
  rw [Paths.hookCount]
  refine Finset.card_pos.mpr ⟨(Paths.firstReach y i₀, i₀), ?_⟩
  simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_Ico, Finset.mem_Icc, harm, hleg]
  exact ⟨⟨⟨hr₀1, by omega⟩, hi₀one, by omega⟩, hi₀ht, by omega, by omega⟩

/-! ### The form is at least one on a nonempty filter -/

/-- **The form is at least one on a nonempty filter**: `Q (𝟙_F) ≥ 1` for every nonempty order
filter `F` of the gap set. Huang's rank-one identity `HJO.External.RankOneDinv` is a quoted
literature result, so it appears here as a hypothesis. -/
@[hjo "lem_rank_one_positive"]
theorem one_le_q_indicator (hrd : External.RankOneDinv) (hco : a.Coprime b) (ha : 1 < a)
    (hab : a < b) {F : Finset ℕ} (hF : Gaps.IsOrderFilter a b F) (hFne : F.Nonempty) :
    1 ≤ HJO.Q a b fun g => if (g : ℕ) ∈ F then 1 else 0 := by
  rw [← hrd a b hco ha hab F hF]
  obtain ⟨r, hr1, hr2, hr3⟩ := exists_one_le_ht_primitivePath hco ha hF hFne
  have hbd := ReturnPath.isBelowDiagonal_primitivePath hco (by omega : 0 < a) hF
  exact_mod_cast one_le_hookCount ha (by omega) hbd hr1 hr2 hr3

end HJO.Coercivity
