/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.Shuffle.MellitShiftLoc
public import HJO.CMStructure.BraidScalars
public meta import HJO.Attr

/-! # Other forms of the braid operator on `V_k`

`HJO.Shuffle.SweepModule` defines the braid operator as `T_iF = s_iF + (q-1)y_i∂_iF`, which is
the form that visibly lands in `V_k`. The Carlsson--Mellit layer uses three other forms of the same
operator and one identity in which it appears twice, and this file supplies them:

* cleared of its denominator, `(y_{i+1}-y_i)T_iF = (q-1)y_iF + (y_{i+1}-qy_i)s_iF`;
* as a displacement of the identity, `T_iF - F = (qy_i - y_{i+1})∂_iF`;
* divided, in the `y`-inverted total space, which is the formula Carlsson and Mellit define it by;
* and the conjugation `T_i(y_{i+1}T_i(F)) = qy_iF`.

## Main results

* `HJO.Sweep.auxVar_sub_mul_braid`: the cleared form.
* `HJO.Sweep.braid_sub_self`: the displacement form.
* `HJO.Sweep.toFrac_braid`: the divided form.
* `HJO.Sweep.braid_auxVar_succ_mul_braid`: the conjugation.

## Implementation notes

**The conjugation is proved through an abstract ring lemma.** `braid_conj_of_cancel` states the
content with opaque atoms: three relations among eight elements of a domain, and a conclusion
reached by cancelling `(v-u)^2`. The three relations are the cleared form at `y_{i+1}T_iF`, the
cleared form at `F`, and the cleared form transported by `s_i` (which is where `s_i(y_i) = y_{i+1}`
and
`s_i(y_{i+1}-y_i) = -(y_{i+1}-y_i)` enter). Doing the cancellation abstractly is what keeps a
`linear_combination` over a polynomial ring in countably many variables from being a
`linear_combination` over that ring's own `MvPolynomial` normal form.

**The cleared form is the primitive, not the divided one.** The definition by a quotient puts
`HJO.Sweep.braid` in `Λ ⊗ 𝕜(y_1,…,y_k)`, in which the quotient by `y_{i+1}-y_i` makes sense
before one knows the result is polynomial, so `HJO.Sweep.toFrac_braid` is its formula there. Here
the polynomial form is available first (`HJO.Sweep.dividedDiff` is pinned by `dividedDiff_spec`
inside the polynomial ring), so the divided form is obtained by mapping the cleared form into
`HJO.Sweep.TotalFrac` and dividing — the one place a nonvanishing denominator is needed, and the
only reason `1 ≤ i` appears there.

**`1 ≤ i` is not needed for the first two.** At the unread index `0` the convention `y_0 = y_1`
makes `s_0` the identity and `∂_0` the zero map, and both identities degenerate to `0 = 0`
correctly. So they are stated for every `i`, which is a generalisation of the range
`1 ≤ i ≤ k-1`.

## References

This file formalises Lemmas `HJO.Sweep.auxVar_sub_mul_braid`, `HJO.Sweep.braid_sub_self`,
`HJO.Sweep.toFrac_braid` and `HJO.Sweep.braid_auxVar_succ_mul_braid`. The divided form is the
definition `T_i = Δ^*_{y_iy_{i+1}}` of E. Carlsson and A. Mellit, *A proof of the shuffle
conjecture*, arXiv:1508.06239, §4 (Raising and lowering operators), where
`(Δ^*_{uv}P)(u,v) = ((q-1)uP(u,v) + (v-qu)P(v,u))/(v-u)`.
-/

@[expose] public section

namespace HJO.Sweep

/-! ### The abstract cancellation behind the conjugation -/

/-- The conjugation identity, with opaque atoms. In a domain, three relations of the shape the
cleared braid formula produces force `A = Quf` once `(v-u)^2` is cancelled. -/
theorem braid_conj_of_cancel {R : Type*} [CommRing R] [IsDomain R] {Q u v A B C F S : R}
    (hd : v - u ≠ 0)
    (h1 : (v - u) * A = (Q - 1) * u * (v * B) + (v - Q * u) * (u * C))
    (h2 : (v - u) * B = (Q - 1) * u * F + (v - Q * u) * S)
    (h3 : -((v - u) * C) = (Q - 1) * v * S + (u - Q * v) * F) :
    A = Q * u * F := by
  refine mul_left_cancel₀ (pow_ne_zero 2 hd) ?_
  linear_combination (v - u) * h1 + ((Q - 1) * u * v) * h2 - ((v - Q * u) * u) * h3

section Field

variable {L : Type*} [Field L]

/-- `s_i` sends `y_{i+1}` to `y_i`, for `i ≥ 1`: the other half of
`HJO.Sweep.swapAux_auxVar_self`. -/
theorem swapAux_auxVar_succ {i : ℕ} (hi : 1 ≤ i) :
    swapAux L i (auxVar (i + 1)) = (auxVar i : Total L) := by
  rw [← swapAux_auxVar_self (L := L) hi, swapAux_swapAux]

/-- **The braid operator cleared of its denominator**:
`(y_{i+1} - y_i)T_iF = (q-1)y_iF + (y_{i+1} - qy_i)s_iF`. This is Carlsson and Mellit's defining
formula for `T_i` with the division undone, and it holds at every index — at `i = 0` both sides are
`0` because `y_0 = y_1`. -/
@[hjo "lem_cm_demazure_source"]
theorem auxVar_sub_mul_braid (q : L) (i : ℕ) (F : Total L) :
    ((auxVar (i + 1) : Total L) - auxVar i) * braid q i F
      = scal (q - 1) * auxVar i * F
        + ((auxVar (i + 1) : Total L) - scal q * auxVar i) * swapAux L i F := by
  have hD : ((auxVar (i + 1) : Total L) - auxVar i) * dividedDiff i F = F - swapAux L i F :=
    dividedDiff_spec i F
  have hs : (scal (q - 1) : Total L) = scal q - 1 := by rw [scal_sub, scal_one]
  rw [braid_apply, hs]
  linear_combination ((scal q : Total L) - 1) * (auxVar i : Total L) * hD

/-- **The braid operator as a displacement of the identity**: `T_iF - F = (qy_i - y_{i+1})∂_iF`. The
image of `T_i - 1` is therefore inside the image of `∂_i`, which is what it is used for.
-/
@[hjo "lem_cm_braid_image"]
theorem braid_sub_self (q : L) (i : ℕ) (F : Total L) :
    braid q i F - F
      = (scal q * auxVar i - (auxVar (i + 1) : Total L)) * dividedDiff i F := by
  have hD : ((auxVar (i + 1) : Total L) - auxVar i) * dividedDiff i F = F - swapAux L i F :=
    dividedDiff_spec i F
  have hs : (scal (q - 1) : Total L) = scal q - 1 := by rw [scal_sub, scal_one]
  rw [braid_apply, hs]
  linear_combination hD

/-- **Carlsson and Mellit's divided formula for the braid operator**, in the `y`-inverted total
space: `T_iF = (q-1)y_i/(y_{i+1}-y_i) · F + (y_{i+1}-qy_i)/(y_{i+1}-y_i) · s_iF`. This is
`HJO.Sweep.auxVar_sub_mul_braid` divided by `y_{i+1}-y_i`, which is invertible there exactly because
`i ≥ 1`. -/
@[hjo "lem_cm_demazure_split"]
theorem toFrac_braid (q : L) {i : ℕ} (hi : 1 ≤ i) (F : Total L) :
    toFrac (braid q i F)
      = toFrac (scal (q - 1)) * auxFrac L i / (auxFrac L (i + 1) - auxFrac L i) * toFrac F
        + (auxFrac L (i + 1) - toFrac (scal q) * auxFrac L i)
            / (auxFrac L (i + 1) - auxFrac L i) * toFrac (swapAux L i F) := by
  have hd : auxFrac L (i + 1) - auxFrac L i ≠ 0 :=
    auxFrac_sub_ne_zero (by omega) (by omega) (by omega)
  have hsrc : (auxFrac L (i + 1) - auxFrac L i) * toFrac (braid q i F)
      = toFrac (scal (q - 1)) * auxFrac L i * toFrac F
        + (auxFrac L (i + 1) - toFrac (scal q) * auxFrac L i) * toFrac (swapAux L i F) := by
    have h := congrArg (algebraMap (Total L) (TotalFrac L)) (auxVar_sub_mul_braid q i F)
    simpa only [map_mul, map_add, map_sub] using h
  field_simp
  linear_combination hsrc

/-- **The conjugation of a corner variable by the braid operator**:
`T_i(y_{i+1}T_i(F)) = qy_iF`, for `i ≥ 1`. -/
@[hjo "lem_cm_braid_y_conj"]
theorem braid_auxVar_succ_mul_braid (q : L) {i : ℕ} (hi : 1 ≤ i) (F : Total L) :
    braid q i ((auxVar (i + 1) : Total L) * braid q i F) = scal q * auxVar i * F := by
  have hd : (auxVar (i + 1) : Total L) - auxVar i ≠ 0 := auxVar_sub_ne_zero hi
  have hu : swapAux L i (auxVar i) = (auxVar (i + 1) : Total L) := swapAux_auxVar_self hi
  have hv : swapAux L i (auxVar (i + 1)) = (auxVar i : Total L) := swapAux_auxVar_succ hi
  have hQ : (scal (q - 1) : Total L) = scal q - 1 := by rw [scal_sub, scal_one]
  -- the cleared form at `F`
  have h2 : ((auxVar (i + 1) : Total L) - auxVar i) * braid q i F
      = (scal q - 1) * auxVar i * F
        + ((auxVar (i + 1) : Total L) - scal q * auxVar i) * swapAux L i F := by
    rw [← hQ]
    exact auxVar_sub_mul_braid q i F
  -- the cleared form at `y_{i+1}T_iF`, with `s_i` moved past the variable
  have h1 : ((auxVar (i + 1) : Total L) - auxVar i)
        * braid q i ((auxVar (i + 1) : Total L) * braid q i F)
      = (scal q - 1) * auxVar i * ((auxVar (i + 1) : Total L) * braid q i F)
        + ((auxVar (i + 1) : Total L) - scal q * auxVar i)
          * ((auxVar i : Total L) * swapAux L i (braid q i F)) := by
    rw [← hQ, auxVar_sub_mul_braid q i ((auxVar (i + 1) : Total L) * braid q i F), map_mul, hv]
  -- the cleared form transported by `s_i`, where `s_i(y_i) = y_{i+1}` enters
  have h3 : -(((auxVar (i + 1) : Total L) - auxVar i) * swapAux L i (braid q i F))
      = (scal q - 1) * auxVar (i + 1) * swapAux L i F
        + ((auxVar i : Total L) - scal q * auxVar (i + 1)) * F := by
    have h := congrArg (swapAux L i) h2
    simp only [map_mul, map_add, map_sub, map_one, swapAux_scal, hu, hv, swapAux_swapAux] at h
    linear_combination h
  exact braid_conj_of_cancel hd h1 h2 h3

end Field

end HJO.Sweep
