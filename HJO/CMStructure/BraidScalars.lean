/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.Shuffle.MellitShiftLoc
public meta import HJO.Attr

/-! # The scalar identities behind the braid relation on `V_k`

Verifying the braid relation for the divided-difference operators on `V_k` produces four identities
among rational functions in three consecutive auxiliary variables `y_i, y_{i+1}, y_{i+2}`. Three of
them have the differences of those variables in their denominators; the fourth is a polynomial
identity. This file proves all four.

Each is a consequence of one identity between field elements with the three differences inverted, so
the mathematical content is isolated in a lemma about an arbitrary field with three elements whose
pairwise differences are nonzero, and each identity is that lemma instantiated at
`HJO.Sweep.auxFrac`. This keeps `field_simp` and `ring` away from the `FractionRing` instance tower,
where the same computation is an order of magnitude more expensive.

## Main results

* `HJO.Sweep.auxVar_braid_scalar_aux`: the polynomial identity.
* `HJO.Sweep.auxFrac_braid_scalar_one`, `HJO.Sweep.auxFrac_braid_scalar_two`,
  `HJO.Sweep.auxFrac_braid_scalar_three`: the three rational identities, in the `y`-inverted total
  space `HJO.Sweep.TotalFrac`.

## Implementation notes

**The hypothesis is `1 ≤ i` and nothing else.** Informally each identity is stated for `k ≥ 3` and
`1 ≤ i ≤ k-2` "in `V_k`". In the one-total-space convention of `HJO.Shuffle.SweepModule` the
three variables `y_i, y_{i+1}, y_{i+2}` live in the single ambient space for every `i`, and they lie
in `V_k` exactly when `i + 2 ≤ k` (`HJO.Sweep.auxVar_mem_piece`); the identity itself does not see
`k`. What `1 ≤ i` is needed for is that the three indices are *distinct* variables — at `i = 0` the
convention `y_0 = y_1` makes `y_{i+1} - y_i` zero and the denominators vanish.

**The parameter is an arbitrary element of the field, not the base scalar `q`.** The identities hold
for every `Q`, so the `q` — strictly, its image `algebraMap L (TotalFrac L) q` — is a
special case. This is a generalisation, not a weakening.

**The unit is not needed.** Its proofs begin by cancelling
`(q-1)^2y_i(y_{i+2}-qy_{i+1})`, "a unit because `q ≠ 1` in `𝕂` and `y_i`, `y_{i+2}-qy_{i+1}` are
nonzero". That is a legitimate route but the hypotheses are not: the identities are true with no
condition on `Q` at all (at `Q = 1` both sides of the first two are `0`), so neither `q ≠ 1` nor the
nonvanishing of `y_{i+2}-qy_{i+1}` appears here. Only the three differences must be invertible, and
they are, by `HJO.Sweep.auxFrac_sub_ne_zero`.

## References

The lemmas `HJO.Sweep.auxVar_braid_scalar_aux`, `HJO.Sweep.auxFrac_braid_scalar_one`,
`HJO.Sweep.auxFrac_braid_scalar_two` and `HJO.Sweep.auxFrac_braid_scalar_three`, on the raising and
lowering operators.
-/

@[expose] public section

namespace HJO.Sweep

/-! ### The identities in an arbitrary field -/

section FieldIdentities

variable {F : Type*} [Field F] {x y z : F} (Q : F)

/-- The first scalar identity, with the three differences inverted in an arbitrary field. -/
theorem braid_scalar_one_of_field (hyx : y - x ≠ 0) (hzy : z - y ≠ 0) (hzx : z - x ≠ 0) :
    (Q - 1) ^ 2 * x ^ 2 * (z - Q * y) / ((y - x) * (z - y) * (z - x))
      = (Q - 1) ^ 2 * x * y * (z - Q * y) / ((z - y) ^ 2 * (y - x))
        - (Q - 1) ^ 2 * x * z * (z - Q * y) / ((z - y) ^ 2 * (z - x)) := by
  field_simp
  ring

/-- The second scalar identity, with the three differences inverted in an arbitrary field. -/
theorem braid_scalar_two_of_field (hyx : y - x ≠ 0) (hzy : z - y ≠ 0) (hzx : z - x ≠ 0) :
    (Q - 1) ^ 2 * x * y * (y - Q * x) / ((y - x) ^ 2 * (z - y))
        - (Q - 1) ^ 2 * x * y * (y - Q * x) / ((y - x) ^ 2 * (z - x))
      = (Q - 1) ^ 2 * x * y * (y - Q * x) / ((y - x) * (z - y) * (z - x)) := by
  field_simp
  ring

/-- The third scalar identity, with the three differences inverted in an arbitrary field. -/
theorem braid_scalar_three_of_field (hyx : y - x ≠ 0) (hzy : z - y ≠ 0) (hzx : z - x ≠ 0) :
    (Q - 1) ^ 3 * x ^ 2 * y / ((y - x) ^ 2 * (z - y))
        - (Q - 1) * x * (y - Q * x) * (x - Q * y) / ((y - x) ^ 2 * (z - x))
      = (Q - 1) ^ 3 * x * y ^ 2 / ((z - y) ^ 2 * (y - x))
        - (Q - 1) * x * (z - Q * y) * (y - Q * z) / ((z - y) ^ 2 * (z - x)) := by
  field_simp
  ring

end FieldIdentities

/-! ### The polynomial identity -/

section Polynomial

variable {L : Type*} [CommRing L]

/-- **The polynomial identity among three consecutive auxiliary variables**:
`(y_{i+2}-y_i)(y_iy_{i+2}-y_{i+1}^2) = y_i(y_{i+1}^2+y_{i+2}^2) - y_{i+2}(y_i^2+y_{i+1}^2)`. It is
usually stated in `V_k` for `k ≥ 3` and `1 ≤ i ≤ k-2`; it is an identity of the ambient total
space at every index, and `HJO.Sweep.auxVar_mem_piece` places the three variables in `V_k` in that
range. -/
@[hjo "lem_cm_braid_scalar_aux"]
theorem auxVar_braid_scalar_aux (i : ℕ) :
    ((auxVar (i + 2) : Total L) - auxVar i)
        * (auxVar i * auxVar (i + 2) - (auxVar (i + 1) : Total L) ^ 2)
      = auxVar i * ((auxVar (i + 1) : Total L) ^ 2 + (auxVar (i + 2) : Total L) ^ 2)
        - auxVar (i + 2) * ((auxVar i : Total L) ^ 2 + (auxVar (i + 1) : Total L) ^ 2) := by
  ring

end Polynomial

/-! ### The rational identities in the `y`-inverted total space -/

section Frac

variable {L : Type*} [Field L]

/-- **Two distinct auxiliary variables differ**, in the `y`-inverted total space. Both indices must
be at least `1`: the convention `y_0 = y_1` of `HJO.Sweep.auxVar` makes the index `0` a repeat. -/
theorem auxFrac_sub_ne_zero {i j : ℕ} (hi : 1 ≤ i) (hj : 1 ≤ j) (hij : i ≠ j) :
    auxFrac L i - auxFrac L j ≠ 0 := by
  rw [auxFrac, auxFrac, toFrac, toFrac, ← map_sub, ne_eq,
    map_eq_zero_iff _ (IsFractionRing.injective (Total L) (TotalFrac L)), auxVar, auxVar]
  refine sub_ne_zero.2 fun h => ?_
  have := MvPolynomial.X_injective (R := Sym.Lambda L) h
  omega

/-- **The first scalar identity of the braid verification.** -/
@[hjo "lem_cm_braid_scalar_one"]
theorem auxFrac_braid_scalar_one {i : ℕ} (hi : 1 ≤ i) (Q : TotalFrac L) :
    (Q - 1) ^ 2 * auxFrac L i ^ 2 * (auxFrac L (i + 2) - Q * auxFrac L (i + 1))
        / ((auxFrac L (i + 1) - auxFrac L i) * (auxFrac L (i + 2) - auxFrac L (i + 1))
          * (auxFrac L (i + 2) - auxFrac L i))
      = (Q - 1) ^ 2 * auxFrac L i * auxFrac L (i + 1)
          * (auxFrac L (i + 2) - Q * auxFrac L (i + 1))
          / ((auxFrac L (i + 2) - auxFrac L (i + 1)) ^ 2 * (auxFrac L (i + 1) - auxFrac L i))
        - (Q - 1) ^ 2 * auxFrac L i * auxFrac L (i + 2)
            * (auxFrac L (i + 2) - Q * auxFrac L (i + 1))
          / ((auxFrac L (i + 2) - auxFrac L (i + 1)) ^ 2
            * (auxFrac L (i + 2) - auxFrac L i)) :=
  braid_scalar_one_of_field Q (auxFrac_sub_ne_zero (by omega) (by omega) (by omega))
    (auxFrac_sub_ne_zero (by omega) (by omega) (by omega))
    (auxFrac_sub_ne_zero (by omega) (by omega) (by omega))

/-- **The second scalar identity of the braid verification.** -/
@[hjo "lem_cm_braid_scalar_two"]
theorem auxFrac_braid_scalar_two {i : ℕ} (hi : 1 ≤ i) (Q : TotalFrac L) :
    (Q - 1) ^ 2 * auxFrac L i * auxFrac L (i + 1) * (auxFrac L (i + 1) - Q * auxFrac L i)
          / ((auxFrac L (i + 1) - auxFrac L i) ^ 2 * (auxFrac L (i + 2) - auxFrac L (i + 1)))
        - (Q - 1) ^ 2 * auxFrac L i * auxFrac L (i + 1) * (auxFrac L (i + 1) - Q * auxFrac L i)
          / ((auxFrac L (i + 1) - auxFrac L i) ^ 2 * (auxFrac L (i + 2) - auxFrac L i))
      = (Q - 1) ^ 2 * auxFrac L i * auxFrac L (i + 1) * (auxFrac L (i + 1) - Q * auxFrac L i)
          / ((auxFrac L (i + 1) - auxFrac L i) * (auxFrac L (i + 2) - auxFrac L (i + 1))
            * (auxFrac L (i + 2) - auxFrac L i)) :=
  braid_scalar_two_of_field Q (auxFrac_sub_ne_zero (by omega) (by omega) (by omega))
    (auxFrac_sub_ne_zero (by omega) (by omega) (by omega))
    (auxFrac_sub_ne_zero (by omega) (by omega) (by omega))

/-- **The third scalar identity of the braid verification.** -/
@[hjo "lem_cm_braid_scalar_three"]
theorem auxFrac_braid_scalar_three {i : ℕ} (hi : 1 ≤ i) (Q : TotalFrac L) :
    (Q - 1) ^ 3 * auxFrac L i ^ 2 * auxFrac L (i + 1)
          / ((auxFrac L (i + 1) - auxFrac L i) ^ 2 * (auxFrac L (i + 2) - auxFrac L (i + 1)))
        - (Q - 1) * auxFrac L i * (auxFrac L (i + 1) - Q * auxFrac L i)
            * (auxFrac L i - Q * auxFrac L (i + 1))
          / ((auxFrac L (i + 1) - auxFrac L i) ^ 2 * (auxFrac L (i + 2) - auxFrac L i))
      = (Q - 1) ^ 3 * auxFrac L i * auxFrac L (i + 1) ^ 2
          / ((auxFrac L (i + 2) - auxFrac L (i + 1)) ^ 2 * (auxFrac L (i + 1) - auxFrac L i))
        - (Q - 1) * auxFrac L i * (auxFrac L (i + 2) - Q * auxFrac L (i + 1))
            * (auxFrac L (i + 1) - Q * auxFrac L (i + 2))
          / ((auxFrac L (i + 2) - auxFrac L (i + 1)) ^ 2
            * (auxFrac L (i + 2) - auxFrac L i)) :=
  braid_scalar_three_of_field Q (auxFrac_sub_ne_zero (by omega) (by omega) (by omega))
    (auxFrac_sub_ne_zero (by omega) (by omega) (by omega))
    (auxFrac_sub_ne_zero (by omega) (by omega) (by omega))

end Frac

end HJO.Sweep
