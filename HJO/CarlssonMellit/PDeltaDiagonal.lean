/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.CarlssonMellit.PDelta
public meta import HJO.Attr

/-! # The numerator of the swapping operator vanishes on the diagonal

The swapping operator `Δ_i` of `HJO.Sym.pdelta` divides

`(q - 1) y_{i+1} F + (y_{i+1} - q y_i) ŝ_i(F)`

by `y_{i+1} - y_i`. This file proves the one fact that makes such a division legitimate where the
divisor is *not* invertible: the numerator vanishes as soon as `y_i` and `y_{i+1}` are identified.

The computation uses nothing about the two variables beyond their being interchanged by the swap, so
it is proved once, `HJO.Sym.map_numerator_eq_zero`, for an arbitrary commutative ring: given a ring
homomorphism `d` that identifies `u` with `v` and collapses the swap `s` to the identity,
`d((Q - 1) v F + (v - Q u) s(F)) = 0`. The consumer in the free variables — the graded part, where
`Δ_{x_r, x_{r+1}}` divides by `x_{r+1} - x_r` — instantiates the same lemma with the letters in
place of the auxiliary variables.

## Main definitions

* `HJO.Sym.swapAuxHom`: the interchange of `y_i` and `y_j` on the polynomial coefficients.
* `HJO.Sym.diagAuxHom`: the identification `y_i = y_j` on the polynomial coefficients.
* `HJO.Sym.pdeltaNumerator`: the numerator of `Δ_i`, read in `P_k`.

## Main results

* `HJO.Sym.map_numerator_eq_zero`: the numerator vanishes under any identification, in any
  commutative ring.
* `HJO.Sym.pdelta_auxToFrac`: `Δ_i` on a series with polynomial coefficients is
  `(y_j - y_i)⁻¹` times `HJO.Sym.pdeltaNumerator`, so the latter is the numerator of
  `HJO.Sym.pdelta` and not merely an expression resembling it.
* `HJO.Sym.map_diagAux_pdeltaNumerator`: that numerator vanishes on identifying `y_i` with `y_j`.

## Implementation notes

*The lemma is stated in `P_k` and not in `P°_k`, where it is naturally posed, because there it
cannot be stated.* "Identifying `y_i` with `y_{i+1}`" is substitution along `y_i ↦ y_{i+1}`, and
that substitution is a ring homomorphism on `𝕂[y_1, …, y_k]` only: it kills `y_{i+1} - y_i`, a
nonzero element — hence a unit — of the coefficient *field* `𝕂(y_1, …, y_k)` of `P°_k`, so no ring
homomorphism out of `P°_k` performs it except the zero map. The two statements below are what
survives: the identity holds in every ring carrying such an identification
(`map_numerator_eq_zero`), and it holds for the numerator of `Δ_i` on every series whose
coefficients are polynomial (`map_diagAux_pdeltaNumerator`), which is the case the divisibility
argument of the graded part is applied to.

*The identification is `MvPolynomial.rename` along `fun l => if l = i then j else l`*, a function
and not an equivalence: the point is that it is not injective. The swap is
`MvPolynomial.rename (Equiv.swap i j)`, which is the map `HJO.Sym.fracSwapAux` is pushed forward
from, so `HJO.Sym.pdelta_auxToFrac` is a rewriting and not a second definition of `Δ_i`.

*No `IsDomain K` on the numerator.* Only the division needs the coefficients to form a field, so
`pdeltaNumerator` and the vanishing hold over any commutative base; `pdelta_auxToFrac`, which names
`Δ_i`, carries the hypothesis.

## References

E. Carlsson and A. Mellit, *A proof of the shuffle conjecture*,
J. Amer. Math. Soc. **31** (2018) 661--697, Section 4.
-/

@[expose] public section

namespace HJO.Sym

/-! ### The numerator vanishes under any identification -/

/-- **The numerator of the swapping operator vanishes on the diagonal.** Let `d` be a ring
homomorphism that identifies `u` with `v` and under which the ring endomorphism `s` becomes the
identity — the two properties an identification of the swapped pair of variables has. Then

`d((Q - 1) v F + (v - Q u) s(F)) = (Q - 1) v F - (Q - 1) v F = 0`,

writing `v` for the common image. This is the computation, which uses no property of the
two variables beyond their being interchanged by the swap; the auxiliary variables `y_i, y_{i+1}`
and the letters `x_r, x_{r+1}` are the two instantiations the layer needs. -/
@[hjo "lem_cm_pdelta_numerator_diagonal"]
theorem map_numerator_eq_zero {A B : Type*} [CommRing A] [CommRing B] (d : A →+* B) (s : A →+* A)
    (hds : ∀ a, d (s a) = d a) {u v : A} (huv : d u = d v) (Q F : A) :
    d ((Q - 1) * v * F + (v - Q * u) * s F) = 0 := by
  simp only [map_add, map_mul, map_sub, map_one, hds, huv]
  ring

/-! ### The two substitutions on the coefficients -/

variable {K : Type*} [CommRing K] {k : ℕ} (i j : Fin k)

/-- The interchange of the auxiliary variables `y_i` and `y_j` on the polynomial coefficients
`𝕂[y_1, …, y_k]` of `P_k`: the renaming along the transposition, which is the map
`HJO.Sym.fracSwapAux` is obtained from by pushing it through the fraction ring. -/
noncomputable def swapAuxHom (K : Type*) [CommRing K] {k : ℕ} (i j : Fin k) :
    MvPolynomial (Fin k) K →+* MvPolynomial (Fin k) K :=
  (MvPolynomial.rename (Equiv.swap i j)).toRingHom

@[simp]
theorem swapAuxHom_apply (p : MvPolynomial (Fin k) K) :
    swapAuxHom K i j p = MvPolynomial.rename (Equiv.swap i j) p :=
  rfl

/-- The identification `y_i = y_j` on the polynomial coefficients `𝕂[y_1, …, y_k]` of `P_k`: the
renaming along the function sending the index `i` to `j` and fixing every other index. It is not a
renaming along an equivalence — collapsing two variables to one is the whole point — so it exists on
the polynomials and not on their fraction field, where it would have to kill the unit
`y_j - y_i`. -/
noncomputable def diagAuxHom (K : Type*) [CommRing K] {k : ℕ} (i j : Fin k) :
    MvPolynomial (Fin k) K →+* MvPolynomial (Fin k) K :=
  (MvPolynomial.rename fun l => if l = i then j else l).toRingHom

@[simp]
theorem diagAuxHom_apply (p : MvPolynomial (Fin k) K) :
    diagAuxHom K i j p = MvPolynomial.rename (fun l => if l = i then j else l) p :=
  rfl

/-- The identification carries `y_i` to `y_j`. -/
@[simp]
theorem diagAuxHom_X_left : diagAuxHom K i j (MvPolynomial.X i) = MvPolynomial.X j := by
  simp

/-- The identification fixes `y_j`, so the two variables have the same image: this is what
"identifying `y_i` with `y_{i+1}`" says. -/
@[simp]
theorem diagAuxHom_X_right : diagAuxHom K i j (MvPolynomial.X j) = MvPolynomial.X j := by
  simp

/-- The identification absorbs the transposition: sending `i` to `j` and then transposing the pair
leaves the same function, both sending `i` and `j` to `j` and fixing everything else. -/
theorem diag_comp_swap :
    ((fun l : Fin k => if l = i then j else l) ∘ (Equiv.swap i j : Fin k → Fin k))
      = fun l : Fin k => if l = i then j else l := by
  funext l
  simp only [Function.comp_apply]
  by_cases hli : l = i
  · subst hli
    simp [Equiv.swap_apply_left]
  · by_cases hlj : l = j
    · subst hlj
      simp [Equiv.swap_apply_right]
    · rw [Equiv.swap_apply_of_ne_of_ne hli hlj]

/-- **The identification collapses the interchange**: after `y_i` and `y_j` have been identified the
transposition of the two acts as the identity. Both composites rename along the function sending `i`
and `j` to `j` and fixing everything else. -/
@[simp]
theorem diagAuxHom_swapAuxHom (p : MvPolynomial (Fin k) K) :
    diagAuxHom K i j (swapAuxHom K i j p) = diagAuxHom K i j p := by
  simp only [diagAuxHom_apply, swapAuxHom_apply, MvPolynomial.rename_rename, diag_comp_swap]

/-! ### The numerator of `Δ_i` -/

/-- **The numerator of the swapping operator `Δ_i`**, read in `P_k`:

`(q - 1) y_j F + (y_j - q y_i) ŝ_i(F)`,

the expression `HJO.Sym.pdelta` divides by `y_j - y_i`, with the coefficients kept polynomial so
that the identification `y_i = y_j` is available. `HJO.Sym.pdelta_auxToFrac` identifies it as the
numerator of `Δ_i` and not merely an expression of the same shape. -/
noncomputable def pdeltaNumerator (q : K) {k : ℕ} (i j : Fin k) (F : AuxAlphabetSeries K k) :
    AuxAlphabetSeries K k :=
  MvPowerSeries.C ((MvPolynomial.C q - 1) * MvPolynomial.X j) * F
    + MvPowerSeries.C (MvPolynomial.X j - MvPolynomial.C q * MvPolynomial.X i) *
      MvPowerSeries.map (swapAuxHom K i j) F

/-- The interchange `ŝ_i` of `P°_k` on a series with polynomial coefficients is the coefficientwise
interchange of `P_k`: `fracSwapAux` is `swapAuxHom` pushed through the fraction ring. -/
theorem auxToFrac_map_swapAuxHom (F : AuxAlphabetSeries K k) :
    auxToFrac K k (MvPowerSeries.map (swapAuxHom K i j) F) = pswap K i j (auxToFrac K k F) :=
  MvPowerSeries.ext fun e => by
    rw [coeff_auxToFrac, coeff_pswap, coeff_auxToFrac, MvPowerSeries.coeff_map, swapAuxHom_apply,
      fracSwapAux_algebraMap]

/-- The numerator on one coefficient, read in the fraction field: the inclusion of the coefficients
carries the polynomial expression to the expression `Δ_i` is built from, the parameter `q` becoming
`HJO.Sym.scalarFrac`, the variables `HJO.Sym.yFrac` and the renaming `HJO.Sym.fracSwapAux`. -/
theorem algebraMap_numerator (q : K) (c : MvPolynomial (Fin k) K) :
    algebraMap (MvPolynomial (Fin k) K) (AuxFrac K k)
        ((MvPolynomial.C q - 1) * MvPolynomial.X j * c
          + (MvPolynomial.X j - MvPolynomial.C q * MvPolynomial.X i) *
            MvPolynomial.rename (Equiv.swap i j) c)
      = (scalarFrac K q - 1) * yFrac K j * algebraMap _ _ c
        + (yFrac K j - scalarFrac K q * yFrac K i) * fracSwapAux K i j (algebraMap _ _ c) := by
  rw [fracSwapAux_algebraMap]
  simp only [scalarFrac, yFrac, map_add, map_mul, map_sub, map_one]

/-- **`HJO.Sym.pdeltaNumerator` is the numerator of `Δ_i`**: on a series with polynomial
coefficients, `Δ_i(F) = (y_j - y_i)⁻¹ · ((q - 1) y_j F + (y_j - q y_i) ŝ_i(F))` with the bracket
computed in `P_k`. -/
theorem pdelta_auxToFrac [IsDomain K] (q : K) (F : AuxAlphabetSeries K k) :
    pdelta q i j (auxToFrac K k F)
      = MvPowerSeries.C (yFrac K j - yFrac K i)⁻¹ * auxToFrac K k (pdeltaNumerator q i j F) := by
  rw [pdelta]
  congr 1
  refine MvPowerSeries.ext fun e => ?_
  rw [map_add, MvPowerSeries.coeff_C_mul, MvPowerSeries.coeff_C_mul, coeff_pswap,
    coeff_auxToFrac, coeff_auxToFrac, pdeltaNumerator, map_add, MvPowerSeries.coeff_C_mul,
    MvPowerSeries.coeff_C_mul, MvPowerSeries.coeff_map, swapAuxHom_apply]
  exact (algebraMap_numerator i j q (MvPowerSeries.coeff e F)).symm

/-- **The numerator of `Δ_i` vanishes on identifying `y_i` with `y_{i+1}`**, that is
`HJO.Sym.map_numerator_eq_zero`: the identification fixes `y_j`, carries `y_i` to `y_j` and
collapses `ŝ_i` to the identity, so the numerator becomes `(q - 1) y_j F - (q - 1) y_j F = 0`. This
is `HJO.Sym.map_numerator_eq_zero` at the coefficientwise identification of `P_k`, the pair of
auxiliary variables read as constant series. -/
@[hjo "lem_cm_pdelta_numerator_diagonal"]
theorem map_diagAux_pdeltaNumerator (q : K) (F : AuxAlphabetSeries K k) :
    MvPowerSeries.map (diagAuxHom K i j) (pdeltaNumerator q i j F) = 0 := by
  have hrw : pdeltaNumerator q i j F
      = (MvPowerSeries.C (MvPolynomial.C q) - 1) * MvPowerSeries.C (MvPolynomial.X j) * F
        + (MvPowerSeries.C (MvPolynomial.X j)
            - MvPowerSeries.C (MvPolynomial.C q) * MvPowerSeries.C (MvPolynomial.X i)) *
          MvPowerSeries.map (swapAuxHom K i j) F := by
    rw [pdeltaNumerator, map_mul, map_sub, map_one, map_sub, map_mul]
  rw [hrw]
  refine map_numerator_eq_zero (MvPowerSeries.map (diagAuxHom K i j))
    (MvPowerSeries.map (swapAuxHom K i j)) (fun G => MvPowerSeries.ext fun e => ?_) ?_ _ _
  · rw [MvPowerSeries.coeff_map, MvPowerSeries.coeff_map, MvPowerSeries.coeff_map,
      diagAuxHom_swapAuxHom]
  · rw [MvPowerSeries.map_C, MvPowerSeries.map_C, diagAuxHom_X_left, diagAuxHom_X_right]

end HJO.Sym
