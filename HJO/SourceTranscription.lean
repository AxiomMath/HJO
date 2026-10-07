/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.Coercivity.Basic
public import HJO.Defs
public import HJO.Series.Gaps

/-! # The paper's formulas, transcribed and identified

The definitions behind the two main theorems are stated in a form chosen for proving, not in the
form in which the paper *Rogers-Ramanujan identities from the geometry of `X^a = Y^b`* writes them
in its §1.1 (The HJO conjecture). This file transcribes the paper's formulas literally and proves
the library's definitions equal to the transcriptions, so the identification is a theorem rather
than a reading.

Three transcriptions are proved.

* The quadratic form. The paper writes `Q(𝐧) = ∑_{g,h ∈ G} K(h - g) n_g n_h` (its (1.6)) with `K`
  the four-term indicator combination (its (1.5)), the double sum running over *ordered* pairs and
  the coordinates extended by zero off `G`. `HJO.Q` is instead the quadratic form of the matrix
  `(g, h) ↦ K(h - g)`. `q_eq_sum_sum` identifies them, and `q_34`, `q_45` evaluate the result at the
  two worked parameter pairs `(3, 4)` and `(4, 5)`, where the paper displays the polynomial
  outright.

* The gap product. The paper writes (its (1.7))
  `P_G(𝐧) = ∏_{g ∈ G} (q)_{n_g - n_{g-a-b}} / ((q)_{n_g - n_{g-a}} (q)_{n_g - n_{g-b}})`, in
  which the shifted index `g - a` is an *integer* and a coordinate at a negative index is zero.
  `HJO.multiplicand` shifts by truncated natural subtraction instead, so on the face of it a gap
  `g < a` is read at index `0` rather than at a negative index. `multiplicand_eq_extendInt`
  shows the two agree, and the reason is that `0` is never a gap: the truncation lands on a
  coordinate that the off-`G` convention already sends to zero.

* The balanced profile. `profile_23`, `profile_45` and `profile_47` are the three profiles the
  paper displays, in §1.1 and §1.2.

One consequence is recorded because a definition depends on it: `HJO.Finite.poly` weighs its
summand by `X ^ (Q 𝐧).toNat`, which is the paper's `q^{Q(𝐧)}` only where `Q 𝐧` is
nonnegative. `zero_le_q_of_mem_cone` is that nonnegativity on the monotonicity cone, which is
where the summation runs, and it is unconditional.
-/

@[expose] public section

open Finset NumericalSemigroup PowerSeries
open scoped QTheory PowerSeries.DiscreteTopology

namespace HJO.Source

/-! ### The quadratic form -/

/-- The paper's quadratic form: the sum of `K(h - g) n_g n_h` over *ordered* pairs of gaps. -/
theorem q_eq_sum_sum (a b : ℕ) (n : (finspan {a, b}).gaps → ℤ) :
    HJO.Q a b n = ∑ g ∈ (finspan {a, b}).gaps, ∑ h ∈ (finspan {a, b}).gaps,
      HJO.U a b ((h : ℤ) - (g : ℤ)) * HJO.extend n g * HJO.extend n h := by
  have key : ∀ g : ((finspan {a, b}).gaps : Finset ℕ), n g = HJO.extend n (g : ℕ) :=
    fun g => (HJO.extend_of_mem g.2).symm
  have inner : ∀ g : ℕ, ∑ h : ((finspan {a, b}).gaps : Finset ℕ),
      HJO.U a b ((h : ℤ) - (g : ℤ)) * HJO.extend n g * HJO.extend n (h : ℕ)
        = ∑ h ∈ (finspan {a, b}).gaps,
          HJO.U a b ((h : ℤ) - (g : ℤ)) * HJO.extend n g * HJO.extend n h := fun g => by
    rw [← Finset.attach_eq_univ]
    exact Finset.sum_attach (finspan {a, b}).gaps
      fun h => HJO.U a b ((h : ℤ) - (g : ℤ)) * HJO.extend n g * HJO.extend n h
  have step : HJO.Q a b n = ∑ g : ((finspan {a, b}).gaps : Finset ℕ),
      ∑ h : ((finspan {a, b}).gaps : Finset ℕ),
        HJO.U a b ((h : ℤ) - ((g : ℕ) : ℤ)) * HJO.extend n (g : ℕ) * HJO.extend n (h : ℕ) := by
    rw [HJO.Q, HJO.Q', Matrix.toQuadraticForm_eq_sum_sum]
    simp only [HJO.qMatrix, Matrix.of_apply, key]
  rw [step]
  simp only [inner]
  rw [← Finset.attach_eq_univ]
  exact Finset.sum_attach (finspan {a, b}).gaps fun g =>
    ∑ h ∈ (finspan {a, b}).gaps, HJO.U a b ((h : ℤ) - (g : ℤ)) * HJO.extend n g * HJO.extend n h

/-- The quadratic form at `(a, b) = (3, 4)`, where the gap set is `{1, 2, 5}`. -/
theorem q_34 (n : (finspan {3, 4}).gaps → ℤ) :
    HJO.Q 3 4 n = HJO.extend n 1 ^ 2 + HJO.extend n 2 ^ 2 + HJO.extend n 5 ^ 2
      + HJO.extend n 1 * HJO.extend n 2 - HJO.extend n 1 * HJO.extend n 5 := by
  have hset : ∀ F : ℕ → ℕ → ℤ,
      ∑ g ∈ (finspan {3, 4}).gaps, ∑ h ∈ (finspan {3, 4}).gaps, F g h
        = ∑ g ∈ ({1, 2, 5} : Finset ℕ), ∑ h ∈ ({1, 2, 5} : Finset ℕ), F g h := fun F => by
    rw [show (finspan {3, 4}).gaps = {1, 2, 5} from rfl]
  rw [q_eq_sum_sum, hset fun g h =>
    HJO.U 3 4 ((h : ℤ) - (g : ℤ)) * HJO.extend n g * HJO.extend n h]
  norm_num [HJO.U, Finset.sum_insert, Finset.mem_insert]
  ring

/-- The quadratic form at `(a, b) = (4, 5)`, where the gap set is `{1, 2, 3, 6, 7, 11}`. -/
theorem q_45 (n : (finspan {4, 5}).gaps → ℤ) :
    HJO.Q 4 5 n = HJO.extend n 1 ^ 2 + HJO.extend n 2 ^ 2 + HJO.extend n 3 ^ 2
      + HJO.extend n 6 ^ 2 + HJO.extend n 7 ^ 2 + HJO.extend n 11 ^ 2
      + HJO.extend n 1 * HJO.extend n 2 + HJO.extend n 1 * HJO.extend n 3
      + HJO.extend n 2 * HJO.extend n 3 + HJO.extend n 3 * HJO.extend n 6
      + HJO.extend n 6 * HJO.extend n 7
      - HJO.extend n 1 * HJO.extend n 6 - HJO.extend n 1 * HJO.extend n 7
      - HJO.extend n 2 * HJO.extend n 7 - HJO.extend n 3 * HJO.extend n 11
      - HJO.extend n 6 * HJO.extend n 11 := by
  have hset : ∀ F : ℕ → ℕ → ℤ,
      ∑ g ∈ (finspan {4, 5}).gaps, ∑ h ∈ (finspan {4, 5}).gaps, F g h
        = ∑ g ∈ ({1, 2, 3, 6, 7, 11} : Finset ℕ), ∑ h ∈ ({1, 2, 3, 6, 7, 11} : Finset ℕ),
            F g h := fun F => by
    rw [show (finspan {4, 5}).gaps = {1, 2, 3, 6, 7, 11} from rfl]
  rw [q_eq_sum_sum, hset fun g h =>
    HJO.U 4 5 ((h : ℤ) - (g : ℤ)) * HJO.extend n g * HJO.extend n h]
  norm_num [HJO.U, Finset.sum_insert, Finset.mem_insert]
  ring

/-- On the monotonicity cone the quadratic form is nonnegative, so the natural-number exponent
`(Q 𝐧).toNat` weighing the summand of `HJO.Finite.poly` is the paper's `Q(𝐧)`. -/
theorem zero_le_q_of_mem_cone {a b : ℕ} (hco : a.Coprime b) (ha : 1 < a) (hab : a < b)
    {n : (finspan {a, b}).gaps → ℤ} (hn : n ∈ HJO.cone a b) : 0 ≤ HJO.Q a b n :=
  le_trans (Finset.sum_nonneg fun _ _ => sq_nonneg _)
    (HJO.Coercivity.sum_layerMult_sq_le_q hco ha hab hn)

/-! ### The gap product -/

/-- The paper's off-`G` convention on an *integer* index: the coordinate `n_j` is `n` at `j`
when `j` is a gap, and zero otherwise -- in particular zero at every negative `j`. -/
def extendInt {G : Finset ℕ} (n : G → ℤ) (j : ℤ) : ℤ :=
  if 0 ≤ j then HJO.extend n j.toNat else 0

@[simp] theorem extendInt_natCast {G : Finset ℕ} (n : G → ℤ) (j : ℕ) :
    extendInt n (j : ℤ) = HJO.extend n j := by simp [extendInt]

/-- The truncated natural shift used by `HJO.multiplicand` agrees with the paper's integer
shift, because `0` is never a gap: truncation lands on a coordinate the off-`G` convention
already sends to zero. -/
theorem extend_natSub_eq_extendInt {G : Finset ℕ} (hG : 0 ∉ G) (n : G → ℤ) (g k : ℕ) :
    HJO.extend n (g - k) = extendInt n ((g : ℤ) - (k : ℤ)) := by
  unfold extendInt
  split_ifs with h
  · congr 1
    omega
  · rw [Nat.sub_eq_zero_of_le (by omega : g ≤ k), HJO.extend, dite_eq_right_iff.mpr]
    exact fun h0 => absurd h0 hG

/-- Each factor of `HJO.multiplicand` is the paper's factor of `P_G(𝐧)`: the numerator
`(q)_{n_g - n_{g-a-b}}` and the two denominators `(q)_{n_g - n_{g-a}}`, `(q)_{n_g - n_{g-b}}`,
with every shifted index an integer and every coordinate read off `G` as zero. -/
theorem multiplicand_eq_extendInt (a b : ℕ) (n : (finspan {a, b}).gaps → ℤ)
    (g : (finspan {a, b}).gaps) :
    HJO.multiplicand _ a b n g =
      HJO.extendedSelfQPochhammer
          (extendInt n (g : ℤ) - extendInt n ((g : ℤ) - (a : ℤ) - (b : ℤ))) *
        HJO.extendedSelfQPochhammerInv (extendInt n (g : ℤ) - extendInt n ((g : ℤ) - (a : ℤ))) *
        HJO.extendedSelfQPochhammerInv (extendInt n (g : ℤ) - extendInt n ((g : ℤ) - (b : ℤ))) := by
  have hG : (0 : ℕ) ∉ (finspan {a, b}).gaps := NumericalSemigroup.zero_notMem_gaps _
  have hg : n g = HJO.extend n (g : ℕ) := (HJO.extend_of_mem g.2).symm
  rw [HJO.multiplicand, hg, extendInt_natCast,
    extend_natSub_eq_extendInt hG n g (a + b), extend_natSub_eq_extendInt hG n g a,
    extend_natSub_eq_extendInt hG n g b,
    show ((g : ℕ) : ℤ) - ((a + b : ℕ) : ℤ) = ((g : ℕ) : ℤ) - (a : ℤ) - (b : ℤ) by push_cast; ring]

/-! ### The balanced profile -/

/-- The balanced profile at `(a, b) = (2, 3)`. -/
theorem profile_23 : (List.range 2).map (HJO.Cylindric.profile 2 3) = [1, 2] := rfl

/-- The balanced profile at `(a, b) = (4, 5)`. -/
theorem profile_45 : (List.range 4).map (HJO.Cylindric.profile 4 5) = [1, 1, 1, 2] := rfl

/-- The balanced profile at `(a, b) = (4, 7)`. -/
theorem profile_47 : (List.range 4).map (HJO.Cylindric.profile 4 7) = [1, 2, 2, 2] := rfl

end HJO.Source

end
