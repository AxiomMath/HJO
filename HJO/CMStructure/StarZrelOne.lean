/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.CMStructure.VmodDplusRelations
public import HJO.CMStructure.ZBraid
public meta import HJO.Attr

/-! # The mixed relation at the first index

Carlsson and Mellit's mixed relation at the first index: on `V_k`, `z_1d_+ = -uq^{k+1}y_1d^*_+`. It
is the third of the three mixed relations of `HJO.Sweep.exists_isDpaAction_star`, and the one
Mellit's §3.7 reads as `-(qu)^{-1}z_1d_+ = q^ky_1d^*_+` — the generator value of the replicating
homomorphism of `HJO.Sweep.exists_isDpaAction_replication`, which is what pins `Φ_c` in the
bigrading statement `HJO.Dyck.Tilde.rel_biHomogeneous`.

## Main results

* `HJO.Sweep.lowerCoeffShift_of_mem_piece` — the extraction of `HJO.Sweep.dminusCM` on `V_j` is
  multiplication by `e_1`.
* `HJO.Sweep.dplusStar_qshift_of_mem_piece` — `d^*_+τ_{k+1,k+1} = τ_{k+2,k+2}d^*_+` on `V_k`.
* `HJO.Sweep.dplusStar_dminusCM_sub_dminusCM_dplusStar_qshift` — **the computation**, shared by both
  readings below: `[d^*_+, d_-]τ_{k+1,k+1} = (q-1)uy_1d^*_+` on `V_k`, with `d_-` Carlsson and
  Mellit's own lowering operator.
* `HJO.Sweep.zopOneStar_dplus` — the relation in Mellit's convention, with `z_1` the operator
  `HJO.Sweep.zopOneStar` of `HJO.Sweep.zop` and `d^♭_+` the modified raising operator.
* `HJO.Sweep.starCommCM_trainUpEnd_star_cmDPlus` — the relation in the all-Carlsson--Mellit
  reading, with `d_+` of `HJO.Sweep.cmDPlus` and `d_-` of `HJO.Sweep.dminusCM`.

## The statement mixes the two `d_+` conventions, and mixed it is false

This library carries two raising operators and two lowering operators, and the relation as usually
written pairs one convention's `z_1` with the other's `d_+`.

* `z_1` is `HJO.Sweep.zop`'s, which is built on `HJO.Sweep.dminus` — the *modified* lowering
  operator `d^♭_-`. The usual proof, however, computes `d_-(1) = X`, and that is Carlsson and
  Mellit's `d_-` of `HJO.Sweep.dminusCM`, the modified one giving `d^♭_-(1) = 1`.
* `d_+` is Carlsson and Mellit's `HJO.Sweep.cmDPlus`, not `HJO.Sweep.dplus` (Mellit's `d^♭_+`).

Read literally — `HJO.Sweep.zop`'s `z_1` against `HJO.Sweep.cmDPlus`'s `d_+` — the relation is
FALSE, and the witness is the evaluation point `F = 1` that the usual proof uses. `d_+(1) = 1` for
`HJO.Sweep.cmDPlus` (`HJO.Sweep.cmDPlus_map_one`), the train fixes `1`, and
`[d^*_+, d^♭_-](1) = 1 - 1 = 0` because both operators fix `1` (`HJO.Sweep.dplusStar_map_one`, and
`d^♭_-(1) = 1`). So the left side is `0` at `F = 1`, while the right side is `-uq^{k+1}y_1`.

The two *matched* pairings are both true, and — the point of this file — both reduce to the single
computation `HJO.Sweep.dplusStar_dminusCM_sub_dminusCM_dplusStar_qshift`. They must, because
Mellit's operators are Carlsson and Mellit's displaced by the last letter:
`HJO.Sweep.dminusCM_eq_neg_dminus_auxVar_mul` and `HJO.Sweep.dplus_eq_neg_cmAscWord_cmDPlus`
(`HJO.Sweep.trainUpEnd_star_cmDPlus`) are the two displacements, and in the composite `z_1d_+` the
two cancel. So the defect is one of conventions and no mathematics is lost: reading `d_+` as
`HJO.Sweep.dplus`, or building `z_1` on `HJO.Sweep.dminusCM` instead of `HJO.Sweep.dminus`, repairs
it either way, and this file proves both readings.

## `q ≠ 1` is an ambient hypothesis of the statement, not a convenience

`HJO.Sweep.zop`'s prefactor is `q^k/(1-q)`, so the relation presupposes `1 - q` invertible; the
extended algebra `HJO.Dyck.Tilde.Atilde` is built over a ring with exactly `q` and `q-1` invertible,
which is the same assumption. In Lean `x/0 = 0`, so at `q = 1` the operator `HJO.Sweep.zopOneStar`
is `0` and the identity fails rather than failing to typecheck — the division-convention trap
already recorded at `HJO.Sweep.exists_isDpaAction_replication`. `q ≠ 0` is carried for the train
cancellation.

## How the computation goes, and why `F ∈ V_k` is what makes it short

Against `HJO.Sweep.trainUpEnd_star_mul_cmAscWord` the train of `z_1` undoes the train of `d_+`
outright, so what is left of `z_1d_+` is the commutator applied to `y_{k+1}τ_{k+1,k+1}(F)`. The two
displacement lemmas turn that into the commutator of `d^*_+` with Carlsson and Mellit's `d_-`
applied to `τ_{k+1,k+1}(F)`, and there both terms collapse:

* `τ^-_{k+1,k+1}` cancels `τ_{k+1,k+1}`, and the extraction of `d_-` then meets an element of `V_k`,
  where it is multiplication by `e_1` (`HJO.Sweep.lowerCoeffShift_of_mem_piece`);
* in the other term `d^*_+` passes `τ_{k+1,k+1}` at the cost of one index
  (`HJO.Sweep.dplusStar_qshift_of_mem_piece`), the substitutions cancel again, and the extraction
  meets `d^*_+F ∈ V_{k+1}`, where it is multiplication by `e_1` for the same reason.

The difference is therefore `(d^*_+(e_1) - e_1)d^*_+F`, and `d^*_+` adds the single letter
`(q-1)uy_1` to the alphabet, so `d^*_+(e_1) - e_1 = (q-1)uy_1`. That is the whole content, and
`F ∈ V_k` is read three times: twice for the two extractions and once for
`HJO.Sweep.dplusStar_qshift_of_mem_piece`, which is false on `y_{k+1}`.

## References

E. Carlsson and A. Mellit, *A proof of the shuffle conjecture*, Section 5, and A. Mellit, *Toric
braids and `(m, n)`-parking functions*, §3.7. -/

@[expose] public section

namespace HJO.Sweep

section Newton

variable {L : Type*} [Field L] [Algebra ℚ L]

/-! ### The extraction of Carlsson and Mellit's lowering operator on a piece -/

/-- **The extraction of `HJO.Sweep.dminusCM` sends `1` to `e_1`.** The unit is the monomial at the
zero exponent, so the single surviving term carries `e_{0+1}`. -/
theorem lowerCoeffShift_one (j : ℕ) :
    lowerCoeffShift L j (1 : Total L) = MvPolynomial.C (Sym.elemSymm L 1) := by
  have h1 : (1 : Total L) = MvPolynomial.monomial (0 : ℕ →₀ ℕ) 1 := by
    rw [MvPolynomial.monomial_zero', MvPolynomial.C_1]
  rw [h1, lowerCoeffShift_monomial]
  simp

/-- **On `V_j` the extraction of `HJO.Sweep.dminusCM` is multiplication by `e_1`**: an element free
of `y_{j+1}` comes out of the extraction (`HJO.Sweep.lowerCoeffShift_mul_of_mem_piece`), leaving
`HJO.Sweep.lowerCoeffShift_one`. -/
theorem lowerCoeffShift_of_mem_piece {j : ℕ} {F : Total L} (hF : F ∈ piece L j) :
    lowerCoeffShift L j F = MvPolynomial.C (Sym.elemSymm L 1) * F := by
  calc lowerCoeffShift L j F = lowerCoeffShift L j (F * 1) := by rw [mul_one]
    _ = F * lowerCoeffShift L j 1 := lowerCoeffShift_mul_of_mem_piece hF 1
    _ = MvPolynomial.C (Sym.elemSymm L 1) * F := by rw [lowerCoeffShift_one, mul_comm]

/-! ### The starred raising operator against the substitution -/

omit [Algebra ℚ L] in
private theorem qshift_scal' (q : L) (i : ℕ) (x : L) :
    qshift q i (scal x : Total L) = scal x := by
  rw [scal_eq_algebraMap, AlgHom.commutes]

omit [Algebra ℚ L] in
/-- The power-sum half of `HJO.Sweep.dplusStar_qshift_of_mem_piece`: both composites add the two
letters `(q-1)uy_1` and `(q-1)y_{k+2}` to `p_{r+1}`, in the two orders. -/
private theorem dplusStarAlg_qshift_C_powerSum (q u : L) (k r : ℕ) :
    dplusStarAlg q u (k + 1) (qshift q (k + 1) (MvPolynomial.C (Sym.powerSum L (r + 1))))
      = qshift q (k + 1 + 1) (dplusStarAlg q u k (MvPolynomial.C (Sym.powerSum L (r + 1)))) := by
  have hav : (auxVar (k + 1) : Total L) = MvPolynomial.X k := by rw [auxVar, Nat.add_sub_cancel]
  have hav' : (auxVar (k + 1 + 1) : Total L) = MvPolynomial.X (k + 1) := by
    rw [auxVar, Nat.add_sub_cancel]
  have hone : (auxVar 1 : Total L) = MvPolynomial.X 0 := rfl
  have hL : dplusStarAlg q u (k + 1)
      (qshift q (k + 1) (MvPolynomial.C (Sym.powerSum L (r + 1))))
      = MvPolynomial.C (Sym.powerSum L (r + 1))
        + scal (q ^ (r + 1) - 1) * (scal u * (auxVar 1 : Total L)) ^ (r + 1)
        + scal (q ^ (r + 1) - 1) * (MvPolynomial.X (k + 1) : Total L) ^ (r + 1) := by
    rw [qshift_powerSum, map_add, map_mul, map_pow, dplusStarAlg_C_powerSum, dplusStarAlg_scal,
      hav, dplusStarAlg_X_of_lt q u (show k < k + 1 by omega)]
  have hR : qshift q (k + 1 + 1)
      (dplusStarAlg q u k (MvPolynomial.C (Sym.powerSum L (r + 1))))
      = MvPolynomial.C (Sym.powerSum L (r + 1))
        + scal (q ^ (r + 1) - 1) * (MvPolynomial.X (k + 1) : Total L) ^ (r + 1)
        + scal (q ^ (r + 1) - 1) * (scal u * (auxVar 1 : Total L)) ^ (r + 1) := by
    rw [dplusStarAlg_C_powerSum, map_add, qshift_powerSum, map_mul, map_pow, map_mul,
      qshift_scal', qshift_scal', hone, qshift_auxVar, ← hone, hav']
  rw [hL, hR]
  ring

omit [Algebra ℚ L] in
/-- The `Λ`-coefficient half of `HJO.Sweep.dplusStar_qshift_of_mem_piece`, by induction on the
coefficient off `HJO.Sweep.dplusStarAlg_qshift_C_powerSum`. -/
private theorem dplusStarAlg_qshift_C (q u : L) (k : ℕ) (c : Sym.Lambda L) :
    dplusStarAlg q u (k + 1) (qshift q (k + 1) (MvPolynomial.C c))
      = qshift q (k + 1 + 1) (dplusStarAlg q u k (MvPolynomial.C c)) := by
  induction c using MvPolynomial.induction_on with
  | C x =>
    have hx : (MvPolynomial.C (MvPolynomial.C x : Sym.Lambda L) : Total L) = scal x := rfl
    rw [hx, qshift_scal', dplusStarAlg_scal, dplusStarAlg_scal, qshift_scal']
  | add p r hp hr => rw [MvPolynomial.C_add, map_add, map_add, map_add, map_add, hp, hr]
  | mul_X p j hp =>
    have hpsj : (MvPolynomial.X j : Sym.Lambda L) = Sym.powerSum L (j + 1) := by
      rw [Sym.powerSum, Nat.add_sub_cancel]
    rw [MvPolynomial.C_mul, map_mul, map_mul, map_mul, map_mul, hp, hpsj,
      dplusStarAlg_qshift_C_powerSum]

/-- **`d^*_+τ_{k+1,k+1} = τ_{k+2,k+2}d^*_+` on `V_k`.** Both composites are `𝕜`-algebra maps; on
`p_r` each adds the two letters `(q-1)uy_1` and `(q-1)y_{k+2}` — the first because `d^*_+` wraps the
letter it adds, the second because `d^*_+` carries the letter `y_{k+1}` that `τ_{k+1,k+1}` added up
to `y_{k+2}` — and on `y_j` with `j ≤ k` each gives `y_{j+1}`.

`F ∈ V_k` is load-bearing: at `F = y_{k+1}` the left side reads `y_{k+2}` where the right side reads
`y_{k+2}` shifted once more by the substitution, and the two differ. -/
theorem dplusStar_qshift_of_mem_piece (q u : L) {k : ℕ} {F : Total L} (hF : F ∈ piece L k) :
    dplusStar q u (k + 1) (qshift q (k + 1) F) = qshift q (k + 1 + 1) (dplusStar q u k F) := by
  rw [← dplusStarAlg_eq_dplusStar, ← dplusStarAlg_eq_dplusStar]
  suffices h : ((dplusStarAlg q u (k + 1)).comp (qshift q (k + 1))) F
      = ((qshift q (k + 1 + 1)).comp (dplusStarAlg q u k)) F from h
  refine algHom_eq_of_mem_piece (k := k) (fun c => ?_) (fun j hj => ?_) hF
  · rw [AlgHom.comp_apply, AlgHom.comp_apply]
    exact dplusStarAlg_qshift_C q u k c
  · rw [AlgHom.comp_apply, AlgHom.comp_apply, qshift_auxVar,
      dplusStarAlg_X_of_lt q u (show j < k + 1 by omega), dplusStarAlg_X_of_lt q u hj,
      qshift_auxVar]

/-! ### The computation both readings share -/

/-- **`[d^*_+, d_-]τ_{k+1,k+1} = (q-1)uy_1d^*_+` on `V_k`**, with `d_-` Carlsson and Mellit's own
lowering operator of `HJO.Sweep.dminusCM`. This is the whole content of
`HJO.Sweep.zopOneStar_dplus`: the two readings below differ from it only by the displacements that
turn Mellit's operators into Carlsson and Mellit's.

Both terms collapse to a multiplication by `e_1`. In the first, `τ^-_{k+1,k+1}` cancels
`τ_{k+1,k+1}` and the extraction meets `F ∈ V_k`; in the second, `d^*_+` passes the substitution by
`HJO.Sweep.dplusStar_qshift_of_mem_piece`, the substitutions cancel again, and the extraction meets
`d^*_+F ∈ V_{k+1}`. The difference is `(d^*_+(e_1) - e_1)d^*_+F`, and `d^*_+` adds the one letter
`(q-1)uy_1` to the alphabet, so the bracket is `(q-1)uy_1`. -/
theorem dplusStar_dminusCM_sub_dminusCM_dplusStar_qshift (q u : L) {k : ℕ} {F : Total L}
    (hF : F ∈ piece L k) :
    dplusStar q u k (dminusCM q (k + 1) (qshift q (k + 1) F))
        - dminusCM q (k + 1 + 1) (dplusStar q u (k + 1) (qshift q (k + 1) F))
      = scal ((q - 1) * u) * (auxVar 1 : Total L) * dplusStar q u k F := by
  have he1 : Sym.elemSymm L 1 = Sym.powerSum L (0 + 1) := by
    have he0 : Sym.elemSymm L 0 = 1 := by rw [Sym.elemSymm]
    rw [Sym.elemSymm]
    simp [he0]
  have h1 : dminusCM q (k + 1) (qshift q (k + 1) F)
      = MvPolynomial.C (Sym.powerSum L (0 + 1)) * F := by
    rw [dminusCM_succ_apply, qshiftNeg_qshift, lowerCoeffShift_of_mem_piece hF, he1]
  have h2 : dminusCM q (k + 1 + 1) (dplusStar q u (k + 1) (qshift q (k + 1) F))
      = MvPolynomial.C (Sym.powerSum L (0 + 1)) * dplusStar q u k F := by
    rw [dplusStar_qshift_of_mem_piece q u hF, dminusCM_succ_apply, qshiftNeg_qshift,
      lowerCoeffShift_of_mem_piece (dplusStar_mem_piece q u hF), he1]
  have hsm : scal (q ^ (0 + 1) - 1) * (scal u * (auxVar 1 : Total L)) ^ (0 + 1)
      = scal ((q - 1) * u) * (auxVar 1 : Total L) := by
    simp only [zero_add, pow_one, ← mul_assoc, ← scal_mul]
  rw [h1, h2, ← dplusStarAlg_eq_dplusStar, map_mul, dplusStarAlg_C_powerSum,
    dplusStarAlg_eq_dplusStar, hsm]
  ring

/-! ### The relation, in the two readings -/

/-- **The mixed relation at the first index, in Mellit's convention**: on `V_k`,
`z_1d^♭_+ = -uq^{k+1}y_1d^*_+`, with `z_1` the operator `HJO.Sweep.zopOneStar` of `HJO.Sweep.zop`
and `d^♭_+` the modified raising operator `HJO.Sweep.dplus`.

This is the pairing used in this library — `HJO.Sweep.zop` and `HJO.Sweep.zRep` are built on
`HJO.Sweep.zopOneStar` — and it is *not* the pairing with `HJO.Sweep.cmDPlus` of the relation as
usually written; see this file's module docstring for why that pairing is false and this one is
not.

The train of `z_1` undoes the train inside `d^♭_+` outright
(`HJO.Sweep.trainUpEnd_star_mul_cmAscWord`), and the two displacements by the last letter — one on
each lowering operator, through `HJO.Sweep.dminusCM_eq_neg_dminus_auxVar_mul`, and one on the
starred raising operator, through `HJO.Sweep.dplusStar_braidInv`'s `d^*_+y_i = y_{i+1}d^*_+` — turn
what is left into `HJO.Sweep.dplusStar_dminusCM_sub_dminusCM_dplusStar_qshift`. -/
@[hjo "lem_cm_star_zrel_one"]
theorem zopOneStar_dplus (q u : L) (hq : q ≠ 0) (hq1 : q ≠ 1) {k : ℕ} {F : Total L}
    (hF : F ∈ piece L k) :
    zopOneStar q u (k + 1) (dplus q k F)
      = -(u * q ^ (k + 1)) • ((auxVar 1 : Total L) * dplusStar q u k F) := by
  have hq1' : (1 : L) - q ≠ 0 := sub_ne_zero_of_ne (Ne.symm hq1)
  set G : Total L := qshift q (k + 1) F with hG
  -- the train of `z_1` undoes the train of `d^♭_+`
  have hcancel : trainUpEnd q (k + 1) 1 (trainUpEnd q 1 (k + 1) ((auxVar (k + 1) : Total L) * G))
      = (auxVar (k + 1) : Total L) * G := by
    have h := LinearMap.congr_fun (trainUpEnd_star_mul_cmAscWord q hq k)
      ((auxVar (k + 1) : Total L) * G)
    rw [Module.End.mul_apply, Module.End.one_apply] at h
    exact h
  -- the two displacements by the last letter
  have hlow : dminus q (k + 1) ((auxVar (k + 1) : Total L) * G) = -dminusCM q (k + 1) G := by
    rw [dminusCM_eq_neg_dminus_auxVar_mul, neg_neg]
  have hstar : dplusStar q u (k + 1) ((auxVar (k + 1) : Total L) * G)
      = (auxVar (k + 1 + 1) : Total L) * dplusStar q u (k + 1) G :=
    dplusStar_auxVar_mul q u (by omega) (le_refl (k + 1)) G
  have hlow' : dminus q (k + 1 + 1) ((auxVar (k + 1 + 1) : Total L) * dplusStar q u (k + 1) G)
      = -dminusCM q (k + 1 + 1) (dplusStar q u (k + 1) G) := by
    rw [dminusCM_eq_neg_dminus_auxVar_mul, neg_neg]
  have hkey := dplusStar_dminusCM_sub_dminusCM_dplusStar_qshift q u hF
  rw [← hG] at hkey
  rw [dplus_apply, zopOneStar, LinearMap.smul_apply, map_neg, Module.End.mul_apply,
    Nat.add_sub_cancel, hcancel, LinearMap.sub_apply, Module.End.mul_apply, Module.End.mul_apply,
    hlow, hstar, hlow', map_neg, neg_sub_neg, neg_sub, hkey, mul_assoc, scal_eq_algebraMap,
    ← Algebra.smul_def, smul_smul]
  refine congrArg (fun x : L => x • ((auxVar 1 : Total L) * dplusStar q u k F)) ?_
  field_simp
  ring

/-- **The mixed relation at the first index, in the all-Carlsson--Mellit reading**: on `V_k`, with
`d_+` the unmodified raising operator of `HJO.Sweep.cmDPlus` and `d_-` the unmodified lowering
operator of `HJO.Sweep.dminusCM`, `[d^*_+, d_-](T^*_{k+1↓1}(d_+F)) = (q-1)uy_1d^*_+F`, which is
`z_1d_+ = -uq^{k+1}y_1d^*_+` once the prefactor `q^{k+1}/(1-q)` of `HJO.Sweep.zop` is put back.

The prefactor is left off the statement on purpose. Reinstating it would need a second `z_1`
operator in the library — `HJO.Sweep.zop`'s formula read with `HJO.Sweep.dminusCM` in place of
`HJO.Sweep.dminus` — and that operator is genuinely different from `HJO.Sweep.zopOneStar`; naming it
would put two `z_1`s in the library for one symbol. What is stated here is the part with
mathematical content, and it is the same computation
`HJO.Sweep.dplusStar_dminusCM_sub_dminusCM_dplusStar_qshift` that the Mellit-convention reading
uses, applied through `HJO.Sweep.trainUpEnd_star_cmDPlus`. -/
@[hjo "lem_cm_star_zrel_one"]
theorem starCommCM_trainUpEnd_star_cmDPlus (q u : L) (hq : q ≠ 0) {k : ℕ} {F : Total L}
    (hF : F ∈ piece L k) :
    dplusStar q u k (dminusCM q (k + 1) (trainUpEnd q (k + 1) 1 (cmDPlus q k F)))
        - dminusCM q (k + 1 + 1)
            (dplusStar q u (k + 1) (trainUpEnd q (k + 1) 1 (cmDPlus q k F)))
      = scal ((q - 1) * u) * (auxVar 1 : Total L) * dplusStar q u k F := by
  rw [trainUpEnd_star_cmDPlus q hq]
  exact dplusStar_dminusCM_sub_dminusCM_dplusStar_qshift q u hF

end Newton

end HJO.Sweep
