/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.CarlssonMellit.SwapClass
public import HJO.CarlssonMellit.ZFirClosed
public meta import HJO.Attr

/-! # The merged variables at and above the level are the letters of the merged alphabet

The class-sum layer writes its monomials and its run weights in the merged variables
`HJO.Sym.zvar` of `HJO.Sym.zvar`, inside `P_k`; the swapping operator `Δ_m` of `HJO.Sym.IsZDelta`
and the interchange `ŝ_m` of `HJO.Sym.zSwap` are written in the letters `HJO.Sym.zLetterSeries` of
the merged alphabet, inside `P°_{k+1}`. This file is the dictionary between the two, at the level
`k + 1`: the merged variable at the label `k + r` is the letter at offset `r`, so a monomial of
`P_{k+1}` becomes a monomial of the merged alphabet, and a run weight becomes the run weight the
operator statements are about.

Labels are `0`-based here, so at the level `k + 1` the labels `0, …, k` name the auxiliary variables
`y_1, …, y_{k+1}` and the labels `k + 1, k + 2, …` the letters `x_1, x_2, …`. The letter of the
merged alphabet at offset `r` is `y_{k+1}` for `r = 0` and `x_r` for `r ≥ 1`, so it is the merged
variable at the label `k + r`; the interchange `HJO.Sym.zSwap K k r` is therefore `ŝ_m` at
`m = k + r`, and no `ℕ`-subtraction is needed to say so.

## Main results

* `HJO.Sym.auxToFrac_zvar_level_add`: the merged variable at the label `k + r` is the letter at
  offset `r`.
* `HJO.Sym.auxToFrac_zvar_mem_zRing`: every merged variable lies in `Z^{(k+1)}`, so the
  automorphism `ŝ_ρ` may be pushed through a monomial.
* `HJO.Sym.zSwap_auxToFrac_zvar_of_ne`: the interchange fixes every merged variable but the two it
  moves — the step "each factor of `g` is a `z^{(k)}_{w_i}` with
  `w_i ∉ {m, m+1}`, hence fixed".
* `HJO.Sym.auxToFrac_runWeightZvar_level_add`: the weight of a run at the labels `k + r` and
  `k + r + 1` is the weight the operator statements `HJO.Sym.isZDelta_runWeight` and
  `HJO.Sym.zSwap_runWeight_add_runWeight` are written at.

## References

The definitions `HJO.Sym.zvar`, `HJO.Sym.runWeight`, `HJO.Sym.zSwap` and `HJO.Sym.IsZDelta`, of
swapping operators and the swapping operator on the merged alphabet.
-/

@[expose] public section

namespace HJO.Sym

variable {K : Type*} [CommRing K] [IsDomain K] {k : ℕ}

/-- **The merged variable at the label `k + r` is the letter of the merged alphabet at offset `r`.**
At `r = 0` both are the distinguished letter `y_{k+1}`, a constant series, and at `r ≥ 1` both are
the letter `x_r` of the alphabet. -/
theorem auxToFrac_zvar_level_add (K : Type*) [CommRing K] [IsDomain K] (k r : ℕ) :
    auxToFrac K (k + 1) (zvar K (k + 1) (k + r)) = zLetterSeries K k r := by
  cases r with
  | zero =>
    change auxToFrac K (k + 1) (zvar K (k + 1) k) = zLetterSeries K k 0
    rw [auxToFrac_zvar_of_lt (Nat.lt_succ_self k), zLetterSeries_zero]
    rfl
  | succ r =>
    rw [zLetterSeries_succ, auxToFrac_zvar_of_le (by omega : k + 1 ≤ k + (r + 1))]
    congr 1
    omega

/-- Every merged variable lies in the alphabet-graded subring `Z^{(k+1)}`: below the level it is a
constant of the lower coefficient field, and at or above it a letter of the merged alphabet. -/
theorem auxToFrac_zvar_mem_zRing (K : Type*) [CommRing K] [IsDomain K] (k j : ℕ) :
    auxToFrac K (k + 1) (zvar K (k + 1) j) ∈ zRing K k := by
  by_cases h : j < k
  · rw [auxToFrac_zvar_of_lt (by omega : j < k + 1),
      show (⟨j, by omega⟩ : Fin (k + 1)) = (⟨j, h⟩ : Fin k).castSucc from rfl,
      ← auxFracCastSucc_yFrac]
    exact C_auxFracCastSucc_mem_zRing _
  · obtain ⟨r, rfl⟩ : ∃ r, j = k + r := ⟨j - k, by omega⟩
    rw [auxToFrac_zvar_level_add]
    exact zLetterSeries_mem_zRing r

/-- **The interchange fixes every merged variable but the two it moves.** A merged variable below
the level is a constant of the lower coefficient field, which `ŝ_ρ` fixes by `HJO.Sym.zPerm_C`; one
at or above the level is a letter of the merged alphabet, fixed unless it is one of the two at the
offsets `r`, `r + 1`, which are the labels `k + r` and `k + r + 1`. -/
theorem zSwap_auxToFrac_zvar_of_ne {j r : ℕ} (hj : j ≠ k + r) (hj' : j ≠ k + r + 1) :
    zSwap K k r (auxToFrac K (k + 1) (zvar K (k + 1) j))
      = auxToFrac K (k + 1) (zvar K (k + 1) j) := by
  by_cases h : j < k
  · rw [auxToFrac_zvar_of_lt (by omega : j < k + 1),
      show (⟨j, by omega⟩ : Fin (k + 1)) = (⟨j, h⟩ : Fin k).castSucc from rfl,
      ← auxFracCastSucc_yFrac, zSwap_apply, zPerm_C]
  · obtain ⟨s, rfl⟩ : ∃ s, j = k + s := ⟨j - k, by omega⟩
    rw [auxToFrac_zvar_level_add]
    exact zSwap_zLetterSeries_of_ne (by omega) (by omega)

/-- **The weight of a run at the labels `k + r` and `k + r + 1`** is the weight of a run at the two
letters of the merged alphabet at the offsets `r` and `r + 1`: the containment `P_{k+1} ⊆ P°_{k+1}`
is a ring homomorphism and the weight is a product of powers. This is the form
`HJO.Sym.isZDelta_runWeight` and `HJO.Sym.zSwap_runWeight_add_runWeight` are stated at. -/
theorem auxToFrac_runWeightZvar_level_add (q : K) (k r l : ℕ) (ε : Bool) :
    auxToFrac K (k + 1) (runWeightZvar q (k + 1) (k + r) l ε)
      = runWeight (MvPowerSeries.C (scalarFrac K q)) (zLetterSeries K k r)
          (zLetterSeries K k (r + 1)) l ε := by
  rw [runWeightZvar, map_runWeight (auxToFrac K (k + 1)), auxToFrac_scalarSeries,
    auxToFrac_zvar_level_add, show k + r + 1 = k + (r + 1) from by omega,
    auxToFrac_zvar_level_add]

end HJO.Sym
