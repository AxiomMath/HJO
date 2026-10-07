/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.CarlssonMellit.PDeltaStar
public import HJO.CarlssonMellit.RealisationSwap
public import HJO.CarlssonMellit.RunWeight
public import HJO.CMStructure.DemazureIdentities
public meta import HJO.Attr

/-! # The starred swapping operator realises the Demazure--Lusztig operator

The total space `HJO.Sweep.Total` carries the Demazure--Lusztig operator `T_i` (`HJO.Sweep.braid`)
and `P°_k` carries the starred swapping operator `Δ*_i`. This file proves that the realisation `ι_k`
carries the first to the second on `V_k`: `Δ*_i(ι_k(G)) = ι_k(T_i(G))`.

## Main results

* `HJO.Dyck.auxToFrac_realise_braid`.

## Implementation notes

*The proof is the cleared braid formula divided.* `HJO.Sweep.auxVar_sub_mul_braid` is Carlsson and
Mellit's formula for `T_i` with the denominator undone,
`(y_{i+1}-y_i)T_iG = (q-1)y_iG + (y_{i+1}-qy_i)s_iG`. Pushing it through `ι_k` and the
coefficientwise inclusion `HJO.Sym.auxToFrac` — both algebra homomorphisms — turns it into the
identity `(y_{i+1}-y_i)·ι_k(T_iG) = (q-1)y_i·ι_k(G) + (y_{i+1}-qy_i)·ŝ_i(ι_k(G))` of `P°_k`, the
last term by `HJO.Dyck.realise_swapAux`. The right-hand side is exactly the numerator of `Δ*_i`, so
the lemma is that identity multiplied by the inverse of the constant series `y_{i+1}-y_i`, a unit of
`P°_k` by `HJO.Sym.sub_yFrac_ne_zero`. Nothing here re-derives either the braid formula or the
intertwining of the interchanges.

*`HJO.Sweep.braid_mem_piece` is not needed.* A proof on `V_k` would open by recording
`T_i(G) ∈ V_k`, which is `HJO.Sweep.braid_mem_piece`. That is what makes `ι_k(T_i(G))` a legitimate
value of `ι_k : V_k → P°_k`; here `ι_k` is a homomorphism defined on the whole total space and
pinned on `V_k`, so the value exists unconditionally and the membership is not a hypothesis of the
identity. The membership of `G` itself *is* needed, through `HJO.Dyck.realise_swapAux`.

*The range conditions are structural.* `k ≥ 2` and `1 ≤ i ≤ k-1` say exactly that there are two
adjacent auxiliary indices below the level, which here is the data `i j : Fin k` together with
`(j : ℕ) = (i : ℕ) + 1`; the `i` is `(i : ℕ) + 1` on the side of `HJO.Sweep.braid`. So no range
hypothesis is carried, matching `HJO.Dyck.auxToFrac_realise_swapAux` and `HJO.Sym.pdeltaStar`.

*The base is a field.* `HJO.Sweep.auxVar_sub_mul_braid` is stated over a field — the braid operator
is built from `HJO.Sweep.dividedDiff` — so the identity is proved there; `HJO.Sym.pdeltaStar` itself
needs only `[CommRing K] [IsDomain K]`.

## References

E. Carlsson and A. Mellit, *A proof of the shuffle conjecture*, J. Amer. Math. Soc. **31** (2018)
661--697, Section 4.
-/

@[expose] public section

namespace HJO.Dyck

variable {K : Type*} [Field K] {k : ℕ}

/-- A realisation carries a scalar of the base to the constant series with constant coefficient:
`ι_k` is a `𝕜`-algebra homomorphism, and `HJO.Sweep.scal` is the structure map of the total space.
Stated for an arbitrary algebra homomorphism, no property of `ι_k` entering. -/
theorem auxToFrac_apply_scal (ι : Sweep.Total K →ₐ[K] Sym.AuxAlphabetSeries K k) (x : K) :
    Sym.auxToFrac K k (ι (Sweep.scal x)) = MvPowerSeries.C (Sym.scalarFrac K x) := by
  rw [Sweep.scal_eq_algebraMap, ι.commutes, MvPowerSeries.algebraMap_apply,
    MvPolynomial.algebraMap_eq, ← Sym.scalarSeries, Sym.auxToFrac_scalarSeries]

/-- A realisation carries the auxiliary variable `y_{l+1}` to the constant series `y_{l+1}` of the
coefficient field: this is `HJO.Dyck.IsAuxRealisation.map_auxVar` read in `P°_k`. -/
theorem auxToFrac_realise_auxVar {ι : Sweep.Total K →ₐ[K] Sym.AuxAlphabetSeries K k}
    (hι : IsAuxRealisation k ι) (l : Fin k) :
    Sym.auxToFrac K k (ι (Sweep.auxVar ((l : ℕ) + 1))) = MvPowerSeries.C (Sym.yFrac K l) := by
  rw [hι.map_auxVar l, Sym.auxToFrac_C]
  rfl

/-- **The starred swapping operator realises the Demazure--Lusztig operator**,
`HJO.Dyck.auxToFrac_realise_braid`: for `k ≥ 2`, `1 ≤ i ≤ k-1` and `G ∈ V_k`,

`Δ*_i(ι_k(G)) = ι_k(T_i(G))`

inside `P°_k`, the containment `P_k ⊆ P°_k` being the coefficientwise inclusion
`HJO.Sym.auxToFrac`.

The proof is `HJO.Sweep.auxVar_sub_mul_braid` — Carlsson and Mellit's formula for `T_i` cleared of
its denominator — pushed through `ι_k` and the inclusion, with `ŝ_i` produced on the last term by
`HJO.Dyck.auxToFrac_realise_swapAux`, and then divided by the constant series `y_{i+1} - y_i`, a
unit of `P°_k`. -/
@[hjo "lem_cm_pdeltastar_realisation"]
theorem auxToFrac_realise_braid (q : K) {ι : Sweep.Total K →ₐ[K] Sym.AuxAlphabetSeries K k}
    (hι : IsAuxRealisation k ι) (i j : Fin k) (hj : (j : ℕ) = (i : ℕ) + 1)
    {G : Sweep.Total K} (hG : G ∈ Sweep.piece K k) :
    Sym.pdeltaStar q i j (Sym.auxToFrac K k (ι G))
      = Sym.auxToFrac K k (ι (Sweep.braid q ((i : ℕ) + 1) G)) := by
  have hij : i ≠ j := by rintro rfl; omega
  have hd : Sym.yFrac K j - Sym.yFrac K i ≠ (0 : Sym.AuxFrac K k) := Sym.sub_yFrac_ne_zero hij
  have hsucc : (i : ℕ) + 1 + 1 = (j : ℕ) + 1 := by omega
  -- The cleared braid formula, pushed through `ι_k` and the inclusion `P_k ⊆ P°_k`.
  have hsrc := congrArg (fun F => Sym.auxToFrac K k (ι F))
    (Sweep.auxVar_sub_mul_braid q ((i : ℕ) + 1) G)
  simp only [map_add, map_sub, map_mul, hsucc, auxToFrac_apply_scal,
    auxToFrac_realise_auxVar hι, auxToFrac_realise_swapAux hι i j hj hG] at hsrc
  -- The right-hand side is the numerator of `Δ*_i`, so multiplying by the inverse of the unit
  -- `y_{i+1} - y_i` gives the claim.
  have hinv : (MvPowerSeries.C (Sym.yFrac K j - Sym.yFrac K i)⁻¹ *
        (MvPowerSeries.C (Sym.yFrac K j) - MvPowerSeries.C (Sym.yFrac K i)) :
      Sym.AuxAlphabetSeriesFrac K k) = 1 := by
    rw [← map_sub, ← map_mul, inv_mul_cancel₀ hd, map_one]
  rw [show Sym.scalarFrac K (q - 1) = Sym.scalarFrac K q - 1 by
    simp only [Sym.scalarFrac, map_sub, map_one]] at hsrc
  rw [Sym.pdeltaStar]
  simp only [map_mul, map_sub, map_one] at hsrc ⊢
  rw [← hsrc, ← mul_assoc, hinv, one_mul]

end HJO.Dyck
