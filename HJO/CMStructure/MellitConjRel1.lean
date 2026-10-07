/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.CMStructure.MellitLowerTwist
public import HJO.CMStructure.StarConjRel1
public import HJO.CMStructure.ZBraid
public meta import HJO.Attr

/-! # The first starred commutator relation in Mellit's convention

The `extra_lower` relation of `HJO.Sweep.IsDpaOperators` for the triple `(T_i^{-1}, d^♭_-, d^*_+)`:
for `k ≥ 2`, on `V_k`,

`d^♭_-(d^*_+d^♭_- - d^♭_-d^*_+)T_{k-1}^{-1} = q^{-1}(d^*_+d^♭_- - d^♭_-d^*_+)d^♭_-`.

This is `HJO.Sweep.dminusCM_starCommCM_braidInv` with the lowering operator `HJO.Sweep.dminus`
(Mellit's `d^♭_-`, pairing `F_j` with `e_j`) in place of
`HJO.Sweep.dminusCM` (pairing `F_j` with `e_{j+1}`). The commutator is
`HJO.Sweep.starComm`, the one `HJO.Sweep.zopOneStar`, `HJO.Sweep.zop` and `HJO.Sweep.zRep` rest on.

**It is not a corollary of `HJO.Sweep.dminusCM_starCommCM_braidInv`** -- see the module docstring of
`HJO/CMStructure/MellitConjRel2.lean`: the bridge between the two lowering operators holds at
argument `y_{k+1}F` and multiplication by `y_{k+1}` is not surjective on `V_{k+1}`.

## Main results

* `HJO.Sweep.dminus_starComm_braidInv` -- the relation, in the expanded form the
  `extra_lower` field of `HJO.Sweep.IsDpaOperators` reads.
* `HJO.Sweep.starComm_succ_apply` -- `HJO.Sweep.starComm` at a successor index, applied.
* `HJO.Sweep.mellitConj1_auxVar_pow` -- the evaluation:
  `A(y_{k+1}^ay_{k+2}^b) = Γ_+(-uy_1)(uy_1(1-q)(B_{a-1}B_b - qB_aB_{b-1}))(1)`.
* `HJO.Sweep.mellitConj1_auxVar_pow_add_swap` -- the evaluation is antisymmetric in `(a, b)`.
* `HJO.Sweep.mellitConj1_braid_add_q` -- `A(T_{k+1}+q) = 0`, the reduced form.

## Implementation notes

**The three stages of the proof survive the change of convention, and only the
evaluation changes.** The intertwining of the twisted multiplications is
`HJO.Sweep.dminus_twistedActionMult_C` and the corner shifts are `HJO.Sweep.dminus_auxVar_mul`, both
the same shape as their unmodified counterparts, because the only difference between the two
lowering operators is which `V_k`-linear coefficient extraction follows `τ^-_{k+1,k+1}`.

**Where the index shift goes, and why it costs nothing.** Reading the evaluation through
`HJO.Sweep.dminus_auxVar_pow_mul` (`d^♭_-(y_{k+1}^iF) = B_iF`) rather than
`HJO.Sweep.dminusCM_auxVar_pow_mul` (`d_-(y_{k+1}^iF) = -B_{i+1}F`) drops every `B`-index by one and
removes two cancelling signs. So the displayed bracket is `B_{a-1}B_b - qB_aB_{b-1}` where the
unmodified relation has `B_aB_{b+1} - qB_{a+1}B_b`, and the antisymmetry is
`HJO.Sweep.bopExt_pair_antisymm` at `(a-2, b-2)` rather than `(a-1, b-1)`.
That lemma is stated over `ℤ`, so the shifted indices are literally in range and nothing has to be
re-proved: the Haglund--Morse--Zabrocki antisymmetry is convention-free.

**`q + 1 ≠ 0` is carried for the same reason as at the unmodified relation.** The
reduced form `A(T_{k+1}+q) = 0` is proved here for every `q`
(`HJO.Sweep.mellitConj1_braid_add_q`); turning it back into the relation multiplies by `1 + q`, and
at `q = -1` it gives nothing, `T_{k+1}` being unipotent there. `q ≠ 0` is what makes `T_{k+1}^{-1}`
an inverse and `q^{-1}` the scalar named. Every use instantiates it at parameters algebraically
independent over `ℤ`, where both hold.

## References

Transcribing E. Carlsson and A. Mellit, *A proof of the shuffle conjecture*, §5, in A. Mellit's
convention for the lowering operator.
-/

@[expose] public section

namespace HJO.Sweep

/-! ### The operator `A`, in Mellit's convention -/

section Operator

variable {L : Type*} [Field L] [Algebra ℚ L]

/-- **`A = d^*_+d^{♭2}_- - (q+1)d^♭_-d^*_+d^♭_- + qd^{♭2}_-d^*_+`**, the operator the proof of
`HJO.Sweep.dminusCM_starCommCM_braidInv` reduces the statement to, in Mellit's convention. On
`V_{k+2}` it lands in `V_{k+1}`; the `k ≥ 2` is read as `k + 2`, so that nothing is truncated. -/
noncomputable def mellitConj1 (q u : L) (k : ℕ) : Module.End L (Total L) :=
  dplusStar q u k * dminus q (k + 1) * dminus q (k + 2)
    - (1 + q) • (dminus q (k + 2) * dplusStar q u (k + 1) * dminus q (k + 2))
    + q • (dminus q (k + 2) * dminus q (k + 3) * dplusStar q u (k + 2))

omit [Algebra ℚ L] in
/-- The `𝕜`-linear combination of `B`-words the three composites of `A` reduce to, with the
`B`-words left free: the identity `ring` verifies once the three shifts have been moved to the
right. This is `HJO.Sweep.starConj1_cancel` of `HJO/CMStructure/StarConjRel1.lean`, which is
`private` there; it is convention-free -- the four `B`-words enter as opaque elements and only their
indices differ between the two conventions. -/
private theorem mellitConj1_cancel (q : L) (w P P' P'' P''' : Total L) :
    (P - scal q * w * P' - scal q * w * P''
        + scal q * w * (scal q * w * P'''))
      - (1 + scal q) * (P - scal q * w * P' - w * (P'' - scal q * w * P'''))
      + scal q * (P - w * P' - w * P'' + w * (w * P'''))
      = w * ((1 - scal q) * (P'' - scal q * P')) := by
  ring

theorem mellitConj1_apply (q u : L) (k : ℕ) (F : Total L) :
    mellitConj1 q u k F
      = dplusStar q u k (dminus q (k + 1) (dminus q (k + 2) F))
        - (1 + q) • dminus q (k + 2) (dplusStar q u (k + 1) (dminus q (k + 2) F))
        + q • dminus q (k + 2) (dminus q (k + 3) (dplusStar q u (k + 2) F)) := rfl

/-- **The evaluation, the display in Mellit's convention.** For every `a, b`,

`A(y_{k+1}^ay_{k+2}^b) = Γ_+(-uy_1)(uy_1(1-q)(B_{a-1}B_b - qB_aB_{b-1}))(1)`.

The two double lowerings are `HJO.Sweep.dminus_dminus_auxVar_pow_mul` at `H = 1`, the middle term is
`HJO.Sweep.dminus_auxVar_pow_mul` twice with the corner shift of `HJO.Sweep.dplusStar_braidInv` in
between, and the three shifts are moved to the right by `HJO.Sweep.alphabetShift_bopExt`. What is
left is `HJO.Sweep.mellitConj1_cancel`, the `𝕜`-linear combination of `B`-words that is
convention-free.

Against `HJO.Sweep.starConj1_auxVar_pow` every `B`-index is one lower and the two signs the
unmodified proof cancels are absent. -/
theorem mellitConj1_auxVar_pow (q u : L) (k a b : ℕ) :
    mellitConj1 q u k ((auxVar (k + 1) : Total L) ^ a * (auxVar (k + 2) : Total L) ^ b)
      = starGammaNeg u (starLetter u * (scal (1 - q) *
          (bopExt q ((a : ℤ) - 1) (bopExt q (b : ℤ) 1)
            - scal q * bopExt q (a : ℤ) (bopExt q ((b : ℤ) - 1) 1)))) := by
  have hwmem : starLetter u ∈ auxSubalg L := starLetter_mem_auxSubalg u
  have hvmem : scal q * starLetter u ∈ auxSubalg L :=
    mul_mem (scal_mem_auxSubalg q) hwmem
  have hA : ∀ j : ℕ, (auxVar (j + 1) : Total L) = MvPolynomial.X j := fun j => by
    rw [auxVar, Nat.add_sub_cancel]
  -- the two double lowerings, at `H = 1`
  have hdd : dminus q (k + 1) (dminus q (k + 2)
        ((auxVar (k + 1) : Total L) ^ a * (auxVar (k + 2) : Total L) ^ b))
      = bopExt q (a : ℤ) (bopExt q (b : ℤ) 1) := by
    have h := dminus_dminus_auxVar_pow_mul q k a b (H := (1 : Total L)) (one_mem _)
    rwa [mul_one] at h
  have hstar3 : dplusStar q u (k + 2)
        ((auxVar (k + 1) : Total L) ^ a * (auxVar (k + 2) : Total L) ^ b)
      = (auxVar (k + 2) : Total L) ^ a * (auxVar (k + 3) : Total L) ^ b := by
    have hx1 : dplusStarAlg q u (k + 2) (auxVar (k + 1) : Total L) = auxVar (k + 2) := by
      rw [hA k, dplusStarAlg_X_of_lt q u (show k < k + 2 by omega), ← hA (k + 1)]
    have hx2 : dplusStarAlg q u (k + 2) (auxVar (k + 2) : Total L) = auxVar (k + 3) := by
      rw [hA (k + 1), dplusStarAlg_X_of_lt q u (show k + 1 < k + 2 by omega), ← hA (k + 2)]
    rw [← dplusStarAlg_eq_dplusStar, map_mul, map_pow, map_pow, hx1, hx2]
  have hdd3 : dminus q (k + 2) (dminus q (k + 3)
        ((auxVar (k + 2) : Total L) ^ a * (auxVar (k + 3) : Total L) ^ b))
      = bopExt q (a : ℤ) (bopExt q (b : ℤ) 1) := by
    have h := dminus_dminus_auxVar_pow_mul q (k + 1) a b (H := (1 : Total L)) (one_mem _)
    rwa [mul_one] at h
  -- the middle term
  have hpull : ∀ r : ℤ, bopExt q r ((auxVar (k + 1) : Total L) ^ a)
      = (auxVar (k + 1) : Total L) ^ a * bopExt q r 1 := fun r => by
    have h := bopExt_auxSubalg_mul q r (pow_mem (auxVar_mem_auxSubalg (k + 1)) a) (1 : Total L)
    rwa [mul_one] at h
  have hd2 : dminus q (k + 2)
        ((auxVar (k + 1) : Total L) ^ a * (auxVar (k + 2) : Total L) ^ b)
      = (auxVar (k + 1) : Total L) ^ a * bopExt q (b : ℤ) 1 := by
    have hre : ((auxVar (k + 1) : Total L) ^ a * (auxVar (k + 2) : Total L) ^ b)
        = (auxVar (k + 2) : Total L) ^ b * (auxVar (k + 1) : Total L) ^ a := by ring
    have h : dminus q (k + 2) ((auxVar (k + 2) : Total L) ^ b
          * (auxVar (k + 1) : Total L) ^ a)
        = bopExt q (b : ℤ) ((auxVar (k + 1) : Total L) ^ a) :=
      dminus_auxVar_pow_mul q (k + 1) b (pow_mem (auxVar_mem_piece (by omega) (le_refl _)) a)
    rw [hre, h, hpull]
  have hs2 : dplusStar q u (k + 1) ((auxVar (k + 1) : Total L) ^ a
        * bopExt q (b : ℤ) 1)
      = (auxVar (k + 2) : Total L) ^ a * dplusStar q u (k + 1) (bopExt q (b : ℤ) 1) := by
    have hstep : ∀ G : Total L, dplusStar q u (k + 1) ((auxVar (k + 1) : Total L) * G)
        = (auxVar (k + 2) : Total L) * dplusStar q u (k + 1) G := fun G =>
      dplusStar_auxVar_mul q u (by omega) (le_refl (k + 1)) G
    exact map_auxVar_pow_mul_of_map_auxVar_mul hstep a _
  have hmemV : dplusStar q u (k + 1) (bopExt q (b : ℤ) (1 : Total L)) ∈ piece L (k + 1) := by
    rw [bopExt_one, dplusStar_C_eq_starGamma, starGammaNeg_apply, starGammaQ_apply]
    refine alphabetShift_mem_piece
      (fun r => neg_mem (pow_mem (starLetter_mem_piece u (k + 1) (by omega)) r)) ?_
    exact alphabetShift_mem_piece
      (fun r => pow_mem (mul_mem (scal_mem_piece q _)
        (starLetter_mem_piece u (k + 1) (by omega))) r) (Subalgebra.algebraMap_mem _ _)
  have hd2' : dminus q (k + 2) ((auxVar (k + 2) : Total L) ^ a
        * dplusStar q u (k + 1) (bopExt q (b : ℤ) 1))
      = bopExt q (a : ℤ) (dplusStar q u (k + 1) (bopExt q (b : ℤ) 1)) :=
    dminus_auxVar_pow_mul q (k + 1) a hmemV
  -- the three shifts moved to the right
  have ht1 : dplusStar q u k (bopExt q (a : ℤ) (bopExt q (b : ℤ) (1 : Total L)))
      = starGammaNeg u (starGammaQ q u (bopExt q (a : ℤ) (bopExt q (b : ℤ) 1))) := by
    rw [show bopExt q (a : ℤ) (bopExt q (b : ℤ) (1 : Total L))
        = MvPolynomial.C (Sym.Bop q (a : ℤ) (Sym.elemSymmAlt L (b : ℤ))) from by
      rw [bopExt_one, bopExt_C], dplusStar_C_eq_starGamma]
  have ht2 : dplusStar q u (k + 1) (bopExt q (b : ℤ) (1 : Total L))
      = starGammaNeg u (starGammaQ q u (bopExt q (b : ℤ) 1)) := by
    rw [bopExt_one, dplusStar_C_eq_starGamma]
  have hX1 : starGammaQ q u (bopExt q (a : ℤ) (bopExt q (b : ℤ) (1 : Total L)))
      = bopExt q (a : ℤ) (bopExt q (b : ℤ) 1)
        - scal q * starLetter u * bopExt q (a : ℤ) (bopExt q ((b : ℤ) - 1) 1)
        - scal q * starLetter u * bopExt q ((a : ℤ) - 1) (bopExt q (b : ℤ) 1)
        + scal q * starLetter u
          * (scal q * starLetter u * bopExt q ((a : ℤ) - 1) (bopExt q ((b : ℤ) - 1) 1)) := by
    rw [starGammaQ_apply]
    exact alphabetShift_bopExt_bopExt_one q hvmem (a : ℤ) (b : ℤ)
  have hX3 : starGammaPos u (bopExt q (a : ℤ) (bopExt q (b : ℤ) (1 : Total L)))
      = bopExt q (a : ℤ) (bopExt q (b : ℤ) 1)
        - starLetter u * bopExt q (a : ℤ) (bopExt q ((b : ℤ) - 1) 1)
        - starLetter u * bopExt q ((a : ℤ) - 1) (bopExt q (b : ℤ) 1)
        + starLetter u
          * (starLetter u * bopExt q ((a : ℤ) - 1) (bopExt q ((b : ℤ) - 1) 1)) := by
    rw [starGammaPos_apply]
    exact alphabetShift_bopExt_bopExt_one q hwmem (a : ℤ) (b : ℤ)
  have hXW : starGammaQ q u (bopExt q (b : ℤ) (1 : Total L))
      = bopExt q (b : ℤ) 1 - scal q * starLetter u * bopExt q ((b : ℤ) - 1) 1 := by
    rw [starGammaQ_apply]
    exact alphabetShift_bopExt_one q hvmem (b : ℤ)
  have hmove : ∀ Y : Total L, bopExt q (a : ℤ) (starGammaNeg u Y)
      = starGammaNeg u (bopExt q (a : ℤ) Y - starLetter u * bopExt q ((a : ℤ) - 1) Y) := by
    intro Y
    rw [starGammaNeg_apply, starGammaNeg_apply]
    exact bopExt_alphabetShift_neg q (a : ℤ) hwmem Y
  have hexp : ∀ i : ℤ, bopExt q i (bopExt q (b : ℤ) (1 : Total L)
        - scal q * starLetter u * bopExt q ((b : ℤ) - 1) 1)
      = bopExt q i (bopExt q (b : ℤ) 1)
        - scal q * starLetter u * bopExt q i (bopExt q ((b : ℤ) - 1) 1) := fun i => by
    rw [map_sub, bopExt_auxSubalg_mul q i hvmem]
  -- the three terms
  have hterm1 : dplusStar q u k (dminus q (k + 1) (dminus q (k + 2)
        ((auxVar (k + 1) : Total L) ^ a * (auxVar (k + 2) : Total L) ^ b)))
      = starGammaNeg u (bopExt q (a : ℤ) (bopExt q (b : ℤ) 1)
          - scal q * starLetter u * bopExt q (a : ℤ) (bopExt q ((b : ℤ) - 1) 1)
          - scal q * starLetter u * bopExt q ((a : ℤ) - 1) (bopExt q (b : ℤ) 1)
          + scal q * starLetter u
            * (scal q * starLetter u
              * bopExt q ((a : ℤ) - 1) (bopExt q ((b : ℤ) - 1) 1))) := by
    rw [hdd, ht1, hX1]
  have hterm2 : dminus q (k + 2) (dplusStar q u (k + 1) (dminus q (k + 2)
        ((auxVar (k + 1) : Total L) ^ a * (auxVar (k + 2) : Total L) ^ b)))
      = starGammaNeg u ((bopExt q (a : ℤ) (bopExt q (b : ℤ) 1)
            - scal q * starLetter u * bopExt q (a : ℤ) (bopExt q ((b : ℤ) - 1) 1))
          - starLetter u * (bopExt q ((a : ℤ) - 1) (bopExt q (b : ℤ) 1)
            - scal q * starLetter u
              * bopExt q ((a : ℤ) - 1) (bopExt q ((b : ℤ) - 1) 1))) := by
    rw [hd2, hs2, hd2', ht2, hmove, hXW, hexp, hexp]
  have hterm3 : dminus q (k + 2) (dminus q (k + 3) (dplusStar q u (k + 2)
        ((auxVar (k + 1) : Total L) ^ a * (auxVar (k + 2) : Total L) ^ b)))
      = starGammaNeg u (bopExt q (a : ℤ) (bopExt q (b : ℤ) 1)
          - starLetter u * bopExt q (a : ℤ) (bopExt q ((b : ℤ) - 1) 1)
          - starLetter u * bopExt q ((a : ℤ) - 1) (bopExt q (b : ℤ) 1)
          + starLetter u
            * (starLetter u
              * bopExt q ((a : ℤ) - 1) (bopExt q ((b : ℤ) - 1) 1))) := by
    rw [hstar3, hdd3, ← hX3]
    exact (starGammaNeg_starGammaPos u _).symm
  rw [mellitConj1_apply, hterm1, hterm2, hterm3, ← scal_mul_eq_smul, ← scal_mul_eq_smul]
  have hkey := mellitConj1_cancel q (starGammaNeg u (starLetter u))
    (starGammaNeg u (bopExt q (a : ℤ) (bopExt q (b : ℤ) 1)))
    (starGammaNeg u (bopExt q (a : ℤ) (bopExt q ((b : ℤ) - 1) 1)))
    (starGammaNeg u (bopExt q ((a : ℤ) - 1) (bopExt q (b : ℤ) 1)))
    (starGammaNeg u (bopExt q ((a : ℤ) - 1) (bopExt q ((b : ℤ) - 1) 1)))
  simp only [map_sub, map_add, map_mul, map_one, starGammaNeg_scal, scal_add, scal_sub, scal_one]
  linear_combination hkey

/-- **The evaluation is antisymmetric in `(a, b)`.** This is `HJO.Sym.bop_pair_antisymm`, read
through `HJO.Sweep.bopExt_pair_antisymm` at `(a-2, b-2)`: the displayed bracket
`B_{a-1}B_b - qB_aB_{b-1}` is the Haglund--Morse--Zabrocki combination, and the relation says
exactly that interchanging `a` and `b` negates it.

The unmodified relation reads the same lemma at `(a-1, b-1)`. That the shift is free is the point:
`HJO.Sweep.bopExt_pair_antisymm` quantifies over `ℤ`, so the antisymmetry is available at the
Mellit-convention indices without any new mathematics -- it is the one statement in this chain that
comes from outside the Dyck path algebra, and it does not know which lowering operator produced the
bracket. -/
theorem mellitConj1_auxVar_pow_add_swap (q u : L) (k a b : ℕ) :
    mellitConj1 q u k ((auxVar (k + 1) : Total L) ^ a * (auxVar (k + 2) : Total L) ^ b)
        + mellitConj1 q u k ((auxVar (k + 1) : Total L) ^ b * (auxVar (k + 2) : Total L) ^ a)
      = 0 := by
  have hanti := bopExt_pair_antisymm q ((a : ℤ) - 2) ((b : ℤ) - 2) (1 : Total L)
  rw [show (a : ℤ) - 2 + 2 = (a : ℤ) from by ring,
    show (b : ℤ) - 2 + 1 = (b : ℤ) - 1 from by ring,
    show (a : ℤ) - 2 + 1 = (a : ℤ) - 1 from by ring,
    show (b : ℤ) - 2 + 2 = (b : ℤ) from by ring] at hanti
  simp only [← scal_mul_eq_smul] at hanti
  have hzero : starLetter u * (scal (1 - q) *
          (bopExt q ((a : ℤ) - 1) (bopExt q (b : ℤ) 1)
            - scal q * bopExt q (a : ℤ) (bopExt q ((b : ℤ) - 1) 1)))
        + starLetter u * (scal (1 - q) *
          (bopExt q ((b : ℤ) - 1) (bopExt q (a : ℤ) 1)
            - scal q * bopExt q (b : ℤ) (bopExt q ((a : ℤ) - 1) 1))) = 0 := by
    linear_combination (-(starLetter u * scal (1 - q)) : Total L) * hanti
  rw [mellitConj1_auxVar_pow, mellitConj1_auxVar_pow, ← map_add, hzero, map_zero]

end Operator

/-! ### The hypotheses of the reduction -/

section Reduction

variable {L : Type*} [Field L] [Algebra ℚ L]

/-- **The intertwining of the twisted multiplications.** `A` carries `∗_{0,k+2}` to `∗_{1,k+1}`: it
carries one starred raising, which moves the index of the twist up by one
(`HJO.Sweep.dplusStar_twistedActionMult`), and three lowerings, which leave it alone
(`HJO.Sweep.dminus_twistedActionMult_C`). -/
theorem mellitConj1_twist_mul (q u : L) (k : ℕ) (c : Sym.Lambda L) (G : Total L) :
    mellitConj1 q u k (twist L q (k + 2) c * G)
      = twistedMult q u 1 (k + 1) (MvPolynomial.C c) * mellitConj1 q u k G := by
  have hc : (twist L q (k + 2) c : Total L) * G
      = twistedActionMult L q u 0 (k + 2) (MvPolynomial.C c) G := by
    rw [twistedActionMult_apply, twistedMult_C]
  have hm2 : ∀ H : Total L,
      dminus q (k + 2) (twistedActionMult L q u 0 (k + 2) (MvPolynomial.C c) H)
        = twistedActionMult L q u 0 (k + 1) (MvPolynomial.C c) (dminus q (k + 2) H) :=
    fun H => dminus_twistedActionMult_C q u (show 0 ≤ k + 1 by omega) c H
  have hm1 : ∀ H : Total L,
      dminus q (k + 1) (twistedActionMult L q u 0 (k + 1) (MvPolynomial.C c) H)
        = twistedActionMult L q u 0 k (MvPolynomial.C c) (dminus q (k + 1) H) :=
    fun H => dminus_twistedActionMult_C q u (Nat.zero_le k) c H
  have hp0 : ∀ H : Total L,
      dplusStar q u k (twistedActionMult L q u 0 k (MvPolynomial.C c) H)
        = twistedActionMult L q u 1 (k + 1) (MvPolynomial.C c) (dplusStar q u k H) :=
    fun H => dplusStar_twistedActionMult q u (Nat.zero_le k) c H
  have hp1 : ∀ H : Total L,
      dplusStar q u (k + 1) (twistedActionMult L q u 0 (k + 1) (MvPolynomial.C c) H)
        = twistedActionMult L q u 1 (k + 2) (MvPolynomial.C c) (dplusStar q u (k + 1) H) :=
    fun H => dplusStar_twistedActionMult q u (show 0 ≤ k + 1 by omega) c H
  have hp2 : ∀ H : Total L,
      dplusStar q u (k + 2) (twistedActionMult L q u 0 (k + 2) (MvPolynomial.C c) H)
        = twistedActionMult L q u 1 (k + 3) (MvPolynomial.C c) (dplusStar q u (k + 2) H) :=
    fun H => dplusStar_twistedActionMult q u (show 0 ≤ k + 2 by omega) c H
  have hn2 : ∀ H : Total L,
      dminus q (k + 2) (twistedActionMult L q u 1 (k + 2) (MvPolynomial.C c) H)
        = twistedActionMult L q u 1 (k + 1) (MvPolynomial.C c) (dminus q (k + 2) H) :=
    fun H => dminus_twistedActionMult_C q u (show 1 ≤ k + 1 by omega) c H
  have hn3 : ∀ H : Total L,
      dminus q (k + 3) (twistedActionMult L q u 1 (k + 3) (MvPolynomial.C c) H)
        = twistedActionMult L q u 1 (k + 2) (MvPolynomial.C c) (dminus q (k + 3) H) :=
    fun H => dminus_twistedActionMult_C q u (show 1 ≤ k + 2 by omega) c H
  rw [mellitConj1_apply, mellitConj1_apply, hc, hm2, hm1, hp0, hp1, hn2, hp2, hn3, hn2]
  simp only [twistedActionMult_apply, ← scal_mul_eq_smul]
  ring

/-- **The corner shifts.** `A` carries `y_i` to `y_{i+1}` for `1 ≤ i ≤ k`, one starred raising
shifting the index once and the lowerings not at all. The range is exact for the same reason as at
the unmodified relation: at `i = k+1` the second lowering of the first term would have to pass
`y_{k+1}` on `V_{k+1}`, which `HJO.Sweep.dminus_auxVar_mul` does not allow. -/
theorem mellitConj1_auxVar_mul (q u : L) {i k : ℕ} (hi : 1 ≤ i) (hik : i ≤ k) (G : Total L) :
    mellitConj1 q u k ((auxVar i : Total L) * G) = auxVar (i + 1) * mellitConj1 q u k G := by
  have hd1 : ∀ j : ℕ, 1 ≤ j → j ≤ k + 1 → ∀ H : Total L,
      dminus q (k + 2) ((auxVar j : Total L) * H) = auxVar j * dminus q (k + 2) H :=
    fun j hj hjk H => dminus_auxVar_mul q hj hjk H
  have hd0 : ∀ j : ℕ, 1 ≤ j → j ≤ k → ∀ H : Total L,
      dminus q (k + 1) ((auxVar j : Total L) * H) = auxVar j * dminus q (k + 1) H :=
    fun j hj hjk H => dminus_auxVar_mul q hj hjk H
  have hd3 : ∀ j : ℕ, 1 ≤ j → j ≤ k + 2 → ∀ H : Total L,
      dminus q (k + 3) ((auxVar j : Total L) * H) = auxVar j * dminus q (k + 3) H :=
    fun j hj hjk H => dminus_auxVar_mul q hj hjk H
  rw [mellitConj1_apply, mellitConj1_apply, hd1 i hi (by omega), hd0 i hi hik,
    dplusStar_auxVar_mul q u hi hik, dplusStar_auxVar_mul q u hi (show i ≤ k + 1 by omega),
    hd1 (i + 1) (by omega) (by omega), dplusStar_auxVar_mul q u hi (show i ≤ k + 2 by omega),
    hd3 (i + 1) (by omega) (by omega), hd1 (i + 1) (by omega) (by omega)]
  simp only [← scal_mul_eq_smul]
  ring

/-- **`A` vanishes on the elements of `V_{k+2}` symmetric in `y_{k+1}` and `y_{k+2}`.**

`A(1 + s_{k+1})` and `0` both intertwine the twisted multiplications with the multiplier
`σ_{1,k+1}(c)` and shift the corners `y_1, …, y_k` by `y_i ↦ y_{i+1}`, so by
`HJO.Sweep.eq_of_agree_auxVar_pow_two` it is enough that they agree on the monomials
`y_{k+1}^ay_{k+2}^b`, and there `1 + s_{k+1}` symmetrises and
`HJO.Sweep.mellitConj1_auxVar_pow_add_swap` applies. Halving is free, `L` being a `ℚ`-algebra. -/
theorem mellitConj1_of_swapAux_eq (q u : L) {k : ℕ} {F : Total L} (hF : F ∈ piece L (k + 2))
    (hsym : swapAux L (k + 1) F = F) : mellitConj1 q u k F = 0 := by
  have : CharZero L := charZero_of_injective_algebraMap (algebraMap ℚ L).injective
  have hkey : (mellitConj1 q u k * (swapAuxEnd L (k + 1) + 1)) F
      = (0 : Module.End L (Total L)) F := by
    refine eq_of_agree_auxVar_pow_two q u
      (T := fun c => twistedMult q u 1 (k + 1) (MvPolynomial.C c))
      (S := fun i => auxVar (i + 1)) (fun c G => ?_) (fun c G => by simp)
      (fun i hi hik G => ?_) (fun i hi hik G => by simp) (fun a b => ?_) hF
    · have hsw : swapAux L (k + 1) (twist L q (k + 2) c) = twist L q (k + 2) c :=
        swapAux_twist q (by omega) (by omega) c
      simp only [Module.End.mul_apply, LinearMap.add_apply, Module.End.one_apply, swapAuxEnd_apply]
      rw [map_mul, hsw, ← mul_add, mellitConj1_twist_mul]
    · have hsw : swapAux L (k + 1) (auxVar i : Total L) = auxVar i :=
        swapAux_auxVar_of_ne hi (by omega) (by omega)
      simp only [Module.End.mul_apply, LinearMap.add_apply, Module.End.one_apply, swapAuxEnd_apply]
      rw [map_mul, hsw, ← mul_add, mellitConj1_auxVar_mul q u hi hik]
    · have hs1 : swapAux L (k + 1) (auxVar (k + 1) : Total L) = auxVar (k + 2) :=
        swapAux_auxVar_self (by omega)
      have hs2 : swapAux L (k + 1) (auxVar (k + 2) : Total L) = auxVar (k + 1) :=
        swapAux_auxVar_succ (by omega)
      have hswap : swapAux L (k + 1)
            ((auxVar (k + 1) : Total L) ^ a * (auxVar (k + 2) : Total L) ^ b)
          = (auxVar (k + 1) : Total L) ^ b * (auxVar (k + 2) : Total L) ^ a := by
        rw [map_mul, map_pow, map_pow, hs1, hs2]
        ring
      simp only [Module.End.mul_apply, LinearMap.add_apply, Module.End.one_apply, swapAuxEnd_apply,
        LinearMap.zero_apply]
      rw [hswap, map_add, add_comm]
      exact mellitConj1_auxVar_pow_add_swap q u k a b
  simp only [Module.End.mul_apply, LinearMap.add_apply, Module.End.one_apply, swapAuxEnd_apply,
    LinearMap.zero_apply, hsym] at hkey
  rw [map_add] at hkey
  have h2 : (2 : L) • mellitConj1 q u k F = 0 := by
    rw [two_smul L]
    exact hkey
  exact (smul_eq_zero.mp h2).resolve_left two_ne_zero

/-- **`A(T_{k+1}+q) = 0`**, the reduced form of the relation: the image of
`T_{k+1}+q` consists of the elements symmetric in `y_{k+1}` and `y_{k+2}`
(`HJO.Sweep.swapAux_braid_add_q`), and `A` vanishes on those. No hypothesis on `q`. -/
theorem mellitConj1_braid_add_q (q u : L) {k : ℕ} {F : Total L} (hF : F ∈ piece L (k + 2)) :
    mellitConj1 q u k (braid q (k + 1) F + scal q * F) = 0 :=
  mellitConj1_of_swapAux_eq q u
    (add_mem (braid_mem_piece q (by omega) (by omega) hF)
      (mul_mem (scal_mem_piece q (k + 2)) hF))
    (swapAux_braid_add_q q (k + 1) F)

end Reduction

/-! ### The relation -/

section Node

variable {L : Type*} [Field L] [Algebra ℚ L]

/-- `HJO.Sweep.starComm` at a successor index, applied, with no truncated subtraction. This is the
`HJO.Sweep.starCommCM_succ_apply` of Mellit's convention. -/
theorem starComm_succ_apply (q u : L) (m : ℕ) (F : Total L) :
    starComm q u (m + 1) F
      = dplusStar q u m (dminus q (m + 1) F) - dminus q (m + 2) (dplusStar q u (m + 1) F) := rfl

/-- **The first starred commutator relation in Mellit's convention.** For `k ≥ 2`, on `V_k`,

`d^♭_-(d^*_+d^♭_- - d^♭_-d^*_+)T_{k-1}^{-1} = q^{-1}(d^*_+d^♭_- - d^♭_-d^*_+)d^♭_-`,

read at `k = m + 2`, so that the hypothesis `k ≥ 2` is carried by the shape of the index. The
commutator is `HJO.Sweep.starComm`, the operators are `HJO.Sweep.dminus` (Mellit's
`d^♭_-`), `HJO.Sweep.dplusStar` and `HJO.Sweep.braidInv`
(`HJO.Sweep.braid`), each at the graded piece its argument lives at.

This is the `extra_lower` field of `HJO.Sweep.IsDpaOperators` for the triple
`(T_i^{-1}, d^♭_-, d^*_+)` at the scalar `q^{-1}`, proved in this convention rather than transported
from `HJO.Sweep.dminusCM_starCommCM_braidInv` -- see the module docstring for why no transport
exists.

`F ∈ V_{k+2}` is load-bearing: the reduction to the monomials `y_{k+1}^ay_{k+2}^b` is a statement
about `V_{k+2}`. So are the two hypotheses on `q`; both are accounted for in the module docstring.

Three steps. `HJO.Sweep.mellitConj1_braid_add_q` is `A(T_{k+1}+q) = 0`;
`d^{♭2}_-T_{k+1} = d^{♭2}_-` (`HJO.Sweep.dminus_dminus_braid`) kills the
braid operator in the first and third terms of `A`, the third after `d^*_+T_{k+1} = T_{k+2}d^*_+`
(`HJO.Sweep.dplusStar_braidInv`) has moved it past the raising; and what is left is `(1+q)` times
the relation. -/
theorem dminus_starComm_braidInv (q u : L) (hq : q ≠ 0) (hq1 : q + 1 ≠ 0) {k : ℕ}
    {F : Total L} (hF : F ∈ piece L (k + 2)) :
    dminus q (k + 2) (dplusStar q u (k + 1) (dminus q (k + 2) (braidInv q (k + 1) F))
        - dminus q (k + 3) (dplusStar q u (k + 2) (braidInv q (k + 1) F)))
      = q⁻¹ • (dplusStar q u k (dminus q (k + 1) (dminus q (k + 2) F))
          - dminus q (k + 2) (dplusStar q u (k + 1) (dminus q (k + 2) F))) := by
  set G := braidInv q (k + 1) F with hGdef
  have hGmem : G ∈ piece L (k + 2) := braidInv_mem_piece q (by omega) hF
  have hFG : braid q (k + 1) G = F := braid_braidInv q hq (k + 1) F
  -- the first term of `A` does not see the braid operator
  have h1 : dplusStar q u k (dminus q (k + 1) (dminus q (k + 2) (braid q (k + 1) G)))
      = dplusStar q u k (dminus q (k + 1) (dminus q (k + 2) G)) := by
    rw [dminus_dminus_braid q k hGmem]
  -- nor does the third, once the raising has carried it up
  have h2 : dminus q (k + 2) (dminus q (k + 3) (dplusStar q u (k + 2) (braid q (k + 1) G)))
      = dminus q (k + 2) (dminus q (k + 3) (dplusStar q u (k + 2) G)) := by
    rw [dplusStar_braid q u (show 1 ≤ k + 1 by omega) (show k + 1 < k + 2 by omega),
      dminus_dminus_braid q (k + 1) (dplusStar_mem_piece q u hGmem)]
  have hA := mellitConj1_braid_add_q q u hGmem
  rw [map_add, scal_mul_eq_smul, map_smul, mellitConj1_apply, mellitConj1_apply, h1, h2] at hA
  simp only [← scal_mul_eq_smul, scal_add, scal_one] at hA
  rw [map_sub, ← hFG, h1, ← scal_mul_eq_smul]
  set tp := dplusStar q u k (dminus q (k + 1) (dminus q (k + 2) G)) with htp
  set tq0 := dminus q (k + 2) (dplusStar q u (k + 1) (dminus q (k + 2) G)) with htq0
  set tr := dminus q (k + 2) (dminus q (k + 3) (dplusStar q u (k + 2) G)) with htr
  set tq1 := dminus q (k + 2) (dplusStar q u (k + 1)
    (dminus q (k + 2) (braid q (k + 1) G))) with htq1
  have hcollect : (q + 1) • (tp - tq1 - scal q * tq0 + scal q * tr) = 0 := by
    rw [← scal_mul_eq_smul, scal_add, scal_one]
    linear_combination hA
  have hdiv := (smul_eq_zero.mp hcollect).resolve_left hq1
  have hqq : (scal q⁻¹ : Total L) * scal q = 1 := by
    rw [← scal_mul, inv_mul_cancel₀ hq, scal_one]
  have hE : tp - tq1 = scal q * (tq0 - tr) := by linear_combination hdiv
  rw [hE, ← mul_assoc, hqq, one_mul]

/-- `HJO.Sweep.dminus_starComm_braidInv` written through `HJO.Sweep.starComm`, which is the
commutator `HJO.Sweep.zopOneStar` and hence `HJO.Sweep.zRep` are built on. -/
theorem dminus_starComm_braidInv' (q u : L) (hq : q ≠ 0) (hq1 : q + 1 ≠ 0) {k : ℕ}
    {F : Total L} (hF : F ∈ piece L (k + 2)) :
    dminus q (k + 2) (starComm q u (k + 2) (braidInv q (k + 1) F))
      = q⁻¹ • starComm q u (k + 1) (dminus q (k + 2) F) := by
  rw [starComm_succ_apply, starComm_succ_apply]
  exact dminus_starComm_braidInv q u hq hq1 hF

end Node

end HJO.Sweep

end
