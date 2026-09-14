/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Mathlib.Algebra.BigOperators.Field
public import HJO.Series.GapForms
public meta import HJO.Attr

/-! # The polarised form of the quadratic form of the gap set

`HJO.Defs.bilin` polarises `HJO.Q`: it is the symmetric `ℚ`-valued form
`B x y = ½ ∑_{g, h ∈ G} (K (h - g) + K (g - h)) x_g y_h` built from the kernel `K = HJO.U a b`.
This file records its algebra -- symmetry, the diagonal evaluation `B x x = Q x`, linearity in
the left argument, and the expansion of `Q` along a finite decomposition of its argument.

Everything rests on one rewriting, `bilin_eq_sum`, which pushes the halving and the cast to `ℚ`
inside the double sum. After it the coefficient of `x_g y_h` is *symmetric* in `g` and `h`, so
symmetry and the diagonal evaluation are both `Finset.sum_comm` followed by `ring`, and linearity
is `Finset.sum_add_distrib` followed by `ring`.

The form is `ℚ`-valued and the quadratic form is `ℤ`-valued, so the mixed statements -- the
diagonal evaluation and the expansion -- carry a cast of `HJO.Q` on one side. That cast loses
nothing: `Int.cast_injective` turns either of them back into a statement about integers.
-/

@[expose] public section

open Finset NumericalSemigroup

namespace HJO.Coercivity

/-! ### The bilinear form as a rational double sum -/

/-- The bilinear form as a `ℚ`-valued double sum: the halving and the cast to `ℚ` are pushed onto
the individual summands, leaving the coefficient
`K (h - g) + K (g - h)` of `x_g y_h` visibly symmetric in `g` and `h`. Every algebraic property
below is proved from this shape. -/
theorem bilin_eq_sum (G : Finset ℕ) (a b : ℕ) (x y : G → ℤ) :
    Defs.bilin G a b x y =
      ∑ g : G, ∑ h : G,
        (((HJO.U a b ((h : ℕ) - (g : ℕ)) : ℤ) : ℚ)
            + ((HJO.U a b ((g : ℕ) - (h : ℕ)) : ℤ) : ℚ)) * (x g : ℚ) * (y h : ℚ) / 2 := by
  rw [Defs.bilin]
  push_cast
  rw [Finset.sum_div]
  refine Finset.sum_congr rfl fun g _ => ?_
  rw [Finset.sum_div]

/-! ### Symmetry and the diagonal -/

/-- **The polarised form is symmetric**: `B x y = B y x`. -/
@[hjo "lem_bilinear_symmetric"]
theorem bilin_comm (G : Finset ℕ) (a b : ℕ) (x y : G → ℤ) :
    Defs.bilin G a b x y = Defs.bilin G a b y x := by
  rw [bilin_eq_sum, bilin_eq_sum, Finset.sum_comm]
  exact Finset.sum_congr rfl fun g _ => Finset.sum_congr rfl fun h _ => by ring

/-- **The polarised form recovers the quadratic form**: `B x x = Q x`. The quadratic form is
integer valued and the polarised form is rational valued, so the identity is stated with the
integer cast into `ℚ`. -/
@[hjo "lem_bilinear_diagonal"]
theorem bilin_self (a b : ℕ) (x : (finspan {a, b}).gaps → ℤ) :
    Defs.bilin ((finspan {a, b}).gaps) a b x x = ((HJO.Q a b x : ℤ) : ℚ) := by
  rw [bilin_eq_sum, Gaps.q_eq_sum_sum]
  push_cast
  have hswap : ∑ g : (finspan {a, b}).gaps, ∑ h : (finspan {a, b}).gaps,
        ((HJO.U a b ((g : ℕ) - (h : ℕ)) : ℤ) : ℚ) * (x g : ℚ) * (x h : ℚ)
      = ∑ g : (finspan {a, b}).gaps, ∑ h : (finspan {a, b}).gaps,
        ((HJO.U a b ((h : ℕ) - (g : ℕ)) : ℤ) : ℚ) * (x g : ℚ) * (x h : ℚ) := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun g _ => Finset.sum_congr rfl fun h _ => by ring
  have hsplit : ∑ g : (finspan {a, b}).gaps, ∑ h : (finspan {a, b}).gaps,
        (((HJO.U a b ((h : ℕ) - (g : ℕ)) : ℤ) : ℚ)
            + ((HJO.U a b ((g : ℕ) - (h : ℕ)) : ℤ) : ℚ)) * (x g : ℚ) * (x h : ℚ) / 2
      = (∑ g : (finspan {a, b}).gaps, ∑ h : (finspan {a, b}).gaps,
            ((HJO.U a b ((h : ℕ) - (g : ℕ)) : ℤ) : ℚ) * (x g : ℚ) * (x h : ℚ)) / 2
        + (∑ g : (finspan {a, b}).gaps, ∑ h : (finspan {a, b}).gaps,
            ((HJO.U a b ((g : ℕ) - (h : ℕ)) : ℤ) : ℚ) * (x g : ℚ) * (x h : ℚ)) / 2 := by
    simp only [Finset.sum_div]
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun g _ => ?_
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun h _ => by ring
  rw [hsplit, hswap]
  ring

/-! ### Linearity in the left argument -/

/-- **Linearity in the left argument**: `B (c x + y, z) = c B (x, z) + B (y, z)`. -/
@[hjo "lem_bilinear_left_linear"]
theorem bilin_add_left (G : Finset ℕ) (a b : ℕ) (c : ℤ) (x y z : G → ℤ) :
    Defs.bilin G a b (fun g => c * x g + y g) z
      = (c : ℚ) * Defs.bilin G a b x z + Defs.bilin G a b y z := by
  rw [bilin_eq_sum, bilin_eq_sum, bilin_eq_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun g _ => ?_
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun h _ => ?_
  push_cast
  ring

/-- **Finite sums in the left argument**: `B (∑_t c_t x^t, y) = ∑_t c_t B (x^t, y)`. -/
@[hjo "lem_bilinear_left_sum"]
theorem bilin_sum_left {ι : Type*} (G : Finset ℕ) (a b : ℕ) (T : Finset ι) (c : ι → ℤ)
    (x : ι → G → ℤ) (y : G → ℤ) :
    Defs.bilin G a b (fun g => ∑ t ∈ T, c t * x t g) y
      = ∑ t ∈ T, (c t : ℚ) * Defs.bilin G a b (x t) y := by
  induction T using Finset.cons_induction with
  | empty => simp [Defs.bilin]
  | cons t T ht ih =>
    have hfun : (fun g : G => ∑ s ∈ Finset.cons t T ht, c s * x s g)
        = fun g : G => c t * x t g + ∑ s ∈ T, c s * x s g := by
      funext g
      rw [Finset.sum_cons]
    rw [hfun, bilin_add_left, ih, Finset.sum_cons]

/-- **Finite sums in the right argument**: `B (y, ∑_t c_t x^t) = ∑_t c_t B (y, x^t)`. -/
@[hjo "lem_bilinear_right_sum"]
theorem bilin_sum_right {ι : Type*} (G : Finset ℕ) (a b : ℕ) (T : Finset ι) (c : ι → ℤ)
    (x : ι → G → ℤ) (y : G → ℤ) :
    Defs.bilin G a b y (fun g => ∑ t ∈ T, c t * x t g)
      = ∑ t ∈ T, (c t : ℚ) * Defs.bilin G a b y (x t) := by
  rw [bilin_comm, bilin_sum_left]
  exact Finset.sum_congr rfl fun t _ => by rw [bilin_comm]

/-! ### The quadratic form along a finite decomposition -/

/-- **Expansion of the quadratic form along a finite decomposition**:
`Q (∑_t c_t x^t) = ∑_s ∑_t c_s c_t B (x^s, x^t)`. -/
@[hjo "lem_form_finite_expansion"]
theorem q_sum_eq_sum_sum_bilin {ι : Type*} (a b : ℕ) (T : Finset ι) (c : ι → ℤ)
    (x : ι → (finspan {a, b}).gaps → ℤ) :
    ((HJO.Q a b (fun g => ∑ t ∈ T, c t * x t g) : ℤ) : ℚ)
      = ∑ s ∈ T, ∑ t ∈ T,
          ((c s * c t : ℤ) : ℚ) * Defs.bilin ((finspan {a, b}).gaps) a b (x s) (x t) := by
  rw [← bilin_self, bilin_sum_left]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [bilin_sum_right, Finset.mul_sum]
  exact Finset.sum_congr rfl fun t _ => by push_cast; ring

end HJO.Coercivity
