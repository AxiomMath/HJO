/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.CarlssonMellit.SweepCM
public meta import HJO.Attr

/-! # The alphabet scaling commutes with the interchange and with `T_i`

Two results. The scaling `θ_k` of the alphabet by `q - 1` commutes with the interchange `s_i` of two
auxiliary variables (`HJO.Sweep.theta_swapAux`) and hence with the Demazure--Lusztig operator `T_i`
(`HJO.Sweep.theta_braid`). Both are read on the total space, as every operator of
`HJO/Shuffle/SweepModule.lean` is, so the range condition `k ≥ 2`, `1 ≤ i ≤ k - 1` is carried by the
lemmas that use them rather than by the statements.

## Main results

* `HJO.Sweep.theta_swapAux`, `θ(s_i F) = s_i(θ F)`.
* `HJO.Sweep.theta_dividedDiff`: `θ(∂_i F) = ∂_i(θ F)`, the step the proof of
  `HJO.Sweep.theta_braid` interposes.
* `HJO.Sweep.theta_braid`, `θ(T_i F) = T_i(θ F)`.

## Implementation notes

*The interchange moves variables and the scaling moves coefficients, which is why they commute.*
`HJO.Sweep.swapAux` is `MvPolynomial.renameEquiv` over `Λ`, so it permutes the auxiliary variables
`y_j` and fixes every coefficient; `HJO.Sweep.theta` fixes every `y_j`
(`HJO.Sweep.theta_auxVar`) and acts inside the coefficients. The proof is the induction on a
polynomial in the `y_j`, with the coefficient case reduced by a second induction to the two facts
that `θ` fixes a scalar and scales `p_{r+1}` by `q^{r+1} - 1`, neither of which `s_i` notices.

*The `∂_i` step needs no domain hypothesis here.* The textbook proof cancels
`y_{i+1} - y_i` in `V_k`, noting that it is a domain; in Lean `HJO.Sweep.dividedDiff_unique` has
already done that cancellation once and for all, so `theta_dividedDiff` is the uniqueness of the
quotient applied to `θ(F) - s_i(θ F)`. It inherits `dividedDiff_unique`'s `[Field L]` and its
`1 ≤ i`; at the unread index `0` both sides are `0` and the hypothesis is not needed, which is why
`theta_braid` is stated for every `i`.

*`theta_braid` is `Λ`-linear bookkeeping on top of those two.* `T_i F` is
`s_i F + (q-1) y_i ∂_i F` (`HJO.Sweep.braid_apply`); `θ` is an algebra map that fixes the scalar
`q - 1` and the variable `y_i`, so the only content is the two commutations above.

## References

The lemmas `HJO.Sweep.theta_swapAux` and `HJO.Sweep.theta_braid`, on raising and lowering operators,
with the definitions `HJO.Sweep.theta`, `HJO.Sweep.swapAux`, `HJO.Sweep.dividedDiffₗ` and
`HJO.Sweep.braid`. E. Carlsson and A. Mellit, *A proof of the shuffle conjecture*, J. Amer. Math.
Soc. **31** (2018) 661--697, §4.
-/

@[expose] public section

namespace HJO.Sweep

section CommRingBase

variable {L : Type*} [CommRing L]

/-- `θ` fixes every auxiliary variable, in the `HJO.Sweep.auxVar` spelling. -/
@[simp]
theorem theta_auxVar' (q : L) (i : ℕ) : theta q (auxVar i : Total L) = auxVar i :=
  theta_auxVar q (i - 1)

/-- The interchange fixes the image under `θ` of a power sum: `θ` scales `p_{r+1}` by a scalar,
and `s_i` reads neither the scalar nor the coefficient. -/
theorem swapAux_theta_C_X (q : L) (i n : ℕ) :
    swapAux L i (theta q (MvPolynomial.C (MvPolynomial.X n) : Total L))
      = theta q (MvPolynomial.C (MvPolynomial.X n) : Total L) := by
  simp [theta, swapAux]

/-- The interchange fixes the image under `θ` of a coefficient: `θ` carries a symmetric function
to a polynomial in the coefficients alone, which `s_i` does not read. -/
theorem swapAux_theta_C (q : L) (i : ℕ) (a : Sym.Lambda L) :
    swapAux L i (theta q (MvPolynomial.C a : Total L)) = theta q (MvPolynomial.C a : Total L) := by
  induction a using MvPolynomial.induction_on with
  | C c =>
      rw [show (MvPolynomial.C (MvPolynomial.C c) : Total L) = algebraMap L (Total L) c from rfl,
        (theta q).commutes c]
      exact swapAux_C i _
  | add p p' hp hp' => simp only [map_add, hp, hp']
  | mul_X p n hp => simp only [map_mul, hp, swapAux_theta_C_X]

/-- **The plethysm commutes with the interchange.** `θ` fixes every
auxiliary variable and `s_i` fixes every coefficient, so the two act on independent data. -/
@[hjo "lem_cm_theta_commute_swap"]
theorem theta_swapAux (q : L) (i : ℕ) (F : Total L) :
    theta q (swapAux L i F) = swapAux L i (theta q F) := by
  induction F using MvPolynomial.induction_on with
  | C a => rw [swapAux_C, swapAux_theta_C]
  | add p p' hp hp' => simp only [map_add, hp, hp']
  | mul_X p n hp => simp only [map_mul, swapAux_X, theta_auxVar, hp]

end CommRingBase

section Field

variable {L : Type*} [Field L]

/-- `θ` fixes a scalar, being an `L`-algebra map. -/
@[simp]
theorem theta_scal (q : L) (x : L) : theta q (scal x : Total L) = scal x :=
  (theta q).commutes x

/-- **The plethysm commutes with the divided difference.** `θ` fixes `y_{i+1} - y_i`, so applying
it to `(y_{i+1} - y_i)∂_iF = F - s_iF` exhibits `θ(∂_iF)` as *the* quotient of
`θ(F) - s_i(θ F)`, which `HJO.Sweep.dividedDiff_unique` identifies with `∂_i(θ F)`. -/
theorem theta_dividedDiff (q : L) {i : ℕ} (hi : 1 ≤ i) (F : Total L) :
    theta q (dividedDiff i F) = dividedDiff i (theta q F) := by
  refine dividedDiff_unique hi ?_
  have h := congrArg (theta q) (dividedDiff_spec i F)
  rw [map_mul, map_sub, map_sub, theta_auxVar, theta_auxVar, theta_swapAux] at h
  exact h

/-- **The plethysm commutes with the Demazure--Lusztig operator.**
`T_i F = s_i F + (q-1)y_i ∂_i F`, and `θ` is an algebra map fixing the scalar `q - 1` and the
variable `y_i`, so this is `theta_swapAux` together with `theta_dividedDiff`. At the unread index
`0` both `s_0` and `∂_0` are trivial, so no lower bound on `i` is needed. -/
@[hjo "lem_cm_theta_commute_demazure"]
theorem theta_braid (q : L) (i : ℕ) (F : Total L) :
    theta q (braid q i F) = braid q i (theta q F) := by
  rcases Nat.eq_zero_or_pos i with rfl | hi
  · simp only [braid_apply, dividedDiff_zero_index, mul_zero, add_zero]
    exact theta_swapAux q 0 F
  · simp only [braid_apply, map_add, map_mul, theta_swapAux, theta_scal, theta_auxVar',
      theta_dividedDiff q hi]

end Field

end HJO.Sweep
