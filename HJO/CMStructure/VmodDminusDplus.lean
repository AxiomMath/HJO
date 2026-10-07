/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.CMStructure.CmCommutator
public import HJO.CMStructure.VmodRaising
public meta import HJO.Attr

/-! # The modified lowering operator commutes with the raising operator

Mellit's `HJO.Sweep.dminus_cmDPlus`: for `k ≥ 1` and `F ∈ V_k`,
`d^♭_-(d_+F) = d_+(d^♭_-F)`, with `d_+` the unmodified raising operator of `HJO.Sweep.cmDPlus` and
`d^♭_-` the modified lowering operator of `HJO.Sweep.dminus`.

The proof is a comparison of two evaluations of `HJO.Sweep.dminusCM_cmDPlus_sub_cmDPlus_dminusCM`.
That lemma gives `(d_-d_+ - d_+d_-)G = (1-q)T_{1↑k}(y_kG)` for `G ∈ V_k`, with `d_-`
the *unmodified* lowering operator of `HJO.Sweep.dminusCM`; reading it at `G = ϑ_kF` and comparing
with the result of applying `ϑ_k` to it at `F` makes every `d_-` term cancel and leaves exactly
`(d^♭_-d_+ - d_+d^♭_-)(ϑ_kF) = 0`. The surviving `d^♭_-` comes from
`HJO.Sweep.unitShiftTotal_dminusCM`, which is the statement that `ϑ` commutes with `d_-` only up to
`d^♭_-ϑ`.

## Main results

* `HJO.Sweep.dminus_cmDPlus`.
* `HJO.Sweep.unitShiftTotal_unitShiftNegTotal`, `HJO.Sweep.unitShiftTotal_mem_piece`,
  `HJO.Sweep.unitShiftNegTotal_mem_piece`, `HJO.Sweep.exists_unitShiftTotal_eq_of_mem_piece` —
  the bijectivity of `ϑ` on `V_k`, which the last step of the proof spends.

## Implementation notes

**The bijectivity of `ϑ` is used in the surjective direction.** The argument as usually written
ends "finally `ϑ_k` is bijective, its inverse being the endomorphism sending `p_r` to `p_r-1`".
That inverse is
`HJO.Sweep.unitShiftNegTotal`, and
`HJO.Sweep.unitShiftNegTotal_unitShiftTotal` is the composite in the direction that gives
injectivity (`HJO.Sweep.unitShiftTotal_injective`). What the proof needs is the *other* direction —
every `G ∈ V_k` is `ϑ_kF` for an `F ∈ V_k`, since the vanishing is obtained at `ϑ_kF` — so the other
composite and the stability of `V_k` under both maps are proved here. Both are the same two-line
computations as their twins: `ϑ` and its inverse fix every auxiliary variable and move `p_r`
by the constant `1`.

**No membership hypothesis is spent twice.** `HJO.Sweep.dminusCM_cmDPlus_sub_cmDPlus_dminusCM` is
read at `F` and at `ϑ_kF`, and `HJO.Sweep.unitShiftTotal_mem_piece` supplies the second; nothing
else in the comparison reads `F ∈ V_k`, every step being an identity of operators on the whole total
space.

## References

The lemma `HJO.Sweep.dminus_cmDPlus`, on the modified lowering operator, using `HJO.Sweep.piece`,
`HJO.Sweep.cmDPlus`, `HJO.Braid.wordUp`, `HJO.Sweep.dminus`, `HJO.Sweep.unitShiftTotal`,
`HJO.Sweep.dminusCM_cmDPlus_sub_cmDPlus_dminusCM`, `HJO.Sweep.unitShiftTotal_dminusCM`,
`HJO.Sweep.unitShiftTotal_cmDPlus` and `HJO.Sweep.unitShiftTotal_braid`. Following A.
Mellit, *Toric braids and `(m, n)`-parking functions*, §3.
-/

@[expose] public section

namespace HJO.Sweep

section Field

variable {L : Type*} [Field L]

/-! ### The unit shift is bijective, and preserves the graded pieces -/

/-- **The composite in the surjective direction**, `ϑ(ϑ^{-1}F) = F`. Together with
`HJO.Sweep.unitShiftNegTotal_unitShiftTotal` this makes `ϑ` an automorphism of the total space,
which is the statement "`ϑ_k` is bijective, its inverse being the endomorphism sending `p_r` to
`p_r - 1`". The computation is the same: both composites fix every auxiliary variable and send `p_r`
to `p_r - 1 + 1`. -/
theorem unitShiftTotal_unitShiftNegTotal (F : Total L) :
    unitShiftTotal L (unitShiftNegTotal L F) = F := by
  have key : (unitShiftTotal L).comp (unitShiftNegTotal L) = AlgHom.id L (Total L) := by
    refine MvPolynomial.algHom_ext' ?_ fun n => ?_
    · refine MvPolynomial.algHom_ext fun r => ?_
      have hC : (algebraMap (Sym.Lambda L) (Total L)) (MvPolynomial.X r)
          = MvPolynomial.C (Sym.powerSum L (r + 1)) := by
        simp [Sym.powerSum]
      simp only [AlgHom.comp_apply, IsScalarTower.coe_toAlgHom', hC, unitShiftNegTotal_powerSum,
        map_sub, map_one, unitShiftTotal_powerSum, AlgHom.id_apply]
      ring
    · simp only [AlgHom.comp_apply, unitShiftNegTotal_X, unitShiftTotal_X, AlgHom.id_apply]
  exact congrArg (fun f : Total L →ₐ[L] Total L => f F) key

/-- **`ϑ` preserves `V_k`**: it fixes every auxiliary variable and moves a coefficient of `Λ` by a
constant, so it introduces no new variable. -/
theorem unitShiftTotal_mem_piece {k : ℕ} {F : Total L} (hF : F ∈ piece L k) :
    unitShiftTotal L F ∈ piece L k := by
  refine mem_piece_of_algHom (φ := unitShiftTotal L) (fun c => ?_) (fun j hj => ?_) hF
  · rw [unitShiftTotal, MvPolynomial.aevalTower_C]
    refine aeval_mem_piece (fun j => ?_) c
    exact add_mem ((piece L k).algebraMap_mem _) (one_mem _)
  · rw [unitShiftTotal_X]
    exact X_mem_piece hj

/-- **`ϑ^{-1}` preserves `V_k`**, for the same reason as `ϑ`. -/
theorem unitShiftNegTotal_mem_piece {k : ℕ} {F : Total L} (hF : F ∈ piece L k) :
    unitShiftNegTotal L F ∈ piece L k := by
  refine mem_piece_of_algHom (φ := unitShiftNegTotal L) (fun c => ?_) (fun j hj => ?_) hF
  · rw [unitShiftNegTotal, MvPolynomial.aevalTower_C]
    refine aeval_mem_piece (fun j => ?_) c
    exact sub_mem ((piece L k).algebraMap_mem _) (one_mem _)
  · rw [unitShiftNegTotal_X]
    exact X_mem_piece hj

/-- **`ϑ_k` is surjective on `V_k`**: every element of `V_k` is `ϑ_kF` for an `F` of `V_k`. This is
the half of the bijectivity of `ϑ_k` that the last step of
`HJO.Sweep.dminus_cmDPlus` spends, the vanishing there being obtained at `ϑ_kF`. -/
theorem exists_unitShiftTotal_eq_of_mem_piece {k : ℕ} {G : Total L} (hG : G ∈ piece L k) :
    ∃ F : Total L, F ∈ piece L k ∧ unitShiftTotal L F = G :=
  ⟨unitShiftNegTotal L G, unitShiftNegTotal_mem_piece hG, unitShiftTotal_unitShiftNegTotal G⟩

end Field

section Newton

variable {L : Type*} [Field L] [Algebra ℚ L]

/-! ### The commutation -/

/-- **The modified lowering operator commutes with the raising operator**: for `k ≥ 1` and
`F ∈ V_k`, `d^♭_-(d_+F) = d_+(d^♭_-F)`, with `d_+` the unmodified raising operator of
`HJO.Sweep.cmDPlus` and `d^♭_-` the modified lowering operator of `HJO.Sweep.dminus`.

Read at `k = m + 1`, so that the indices of the four operators — `d^♭_-` from `V_{m+2}` and from
`V_{m+1}`, `d_+` from `V_{m+1}` and from `V_m` — are written with nothing truncated.

The proof. By `HJO.Sweep.exists_unitShiftTotal_eq_of_mem_piece` it is enough to prove
the identity at `ϑF` for `F ∈ V_{m+1}`. Applying `ϑ` to
`HJO.Sweep.dminusCM_cmDPlus_sub_cmDPlus_dminusCM` at `F` and using
`HJO.Sweep.unitShiftTotal_dminusCM` (`ϑd_- = d_-ϑ + d^♭_-ϑ`), `HJO.Sweep.unitShiftTotal_cmDPlus`
(`ϑd_+ = d_+ϑ`) and the commutation of `ϑ` with the word and with `y_{m+1}` turns the left-hand side
into `(d_-d_+ - d_+d_-)(ϑF) + (d^♭_-d_+ - d_+d^♭_-)(ϑF)` and the right-hand side into the right-hand
side of `HJO.Sweep.dminusCM_cmDPlus_sub_cmDPlus_dminusCM` at `ϑF`; subtracting that instance leaves
the claim. -/
@[hjo "lem_vmod_dminus_dplus_commute"]
theorem dminus_cmDPlus (q : L) (m : ℕ) {G : Total L} (hG : G ∈ piece L (m + 1)) :
    dminus q (m + 2) (cmDPlus q (m + 1) G) = cmDPlus q m (dminus q (m + 1) G) := by
  obtain ⟨F, hF, rfl⟩ := exists_unitShiftTotal_eq_of_mem_piece hG
  have hcomF := dminusCM_cmDPlus_sub_cmDPlus_dminusCM q m hF
  have hcom := dminusCM_cmDPlus_sub_cmDPlus_dminusCM q m (unitShiftTotal_mem_piece hF)
  have h1 : unitShiftTotal L (dminusCM q (m + 2) (cmDPlus q (m + 1) F))
      = dminusCM q (m + 2) (cmDPlus q (m + 1) (unitShiftTotal L F))
        + dminus q (m + 2) (cmDPlus q (m + 1) (unitShiftTotal L F)) := by
    rw [unitShiftTotal_dminusCM, unitShiftTotal_cmDPlus]
  have h2 : unitShiftTotal L (cmDPlus q m (dminusCM q (m + 1) F))
      = cmDPlus q m (dminusCM q (m + 1) (unitShiftTotal L F))
        + cmDPlus q m (dminus q (m + 1) (unitShiftTotal L F)) := by
    rw [unitShiftTotal_cmDPlus, unitShiftTotal_dminusCM, map_add]
  have h3 : unitShiftTotal L
        (scal (1 - q) * cmAscWord q 1 m ((auxVar (m + 1) : Total L) * F))
      = scal (1 - q)
          * cmAscWord q 1 m ((auxVar (m + 1) : Total L) * unitShiftTotal L F) := by
    rw [map_mul, unitShiftTotal_scal, unitShiftTotal_cmAscWord q (by omega), map_mul,
      unitShiftTotal_auxVar]
  have hshift := congrArg (unitShiftTotal L) hcomF
  rw [map_sub, h1, h2, h3] at hshift
  linear_combination hshift - hcom

end Newton

end HJO.Sweep

end
