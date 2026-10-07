/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.CMStructure.BopAntisym
public import HJO.CMStructure.DemazureIdentities
public import HJO.CarlssonMellit.BopModified
public import HJO.CarlssonMellit.DminusSquare
public import HJO.Shuffle.SweepBasis
public meta import HJO.Attr

/-! # The square of a lowering operator kills the braid defect

Both lowering operators of this library — Carlsson and Mellit's own `d_-` of `HJO.Sweep.dminusCM`
and Mellit's modified `d^♭_-` of `HJO.Sweep.dminus` — satisfy `d_-^2T_{k-1} = d_-^2` on `V_k` for
`k ≥ 2`. The two proofs are the same argument run against two computations of the operator on a
monomial in the last two variables, and both end at the Haglund--Morse--Zabrocki antisymmetry.

## Main results

* `HJO.Sweep.eq_of_braid_defect_last` — the shared reduction: an operator that kills every
  `(qy_{k-1} - y_k)(y_{k-1}^ay_k^b + y_{k-1}^by_k^a)H` with `H ∈ V_{k-2}` is unchanged by
  precomposition with `T_{k-1}`.
* `HJO.Sweep.dminusCM_dminusCM_braid`.
* `HJO.Sweep.dminus_dminus_auxVar_pow_mul` — the modified operator twice on a monomial,
  `d^♭_-d^♭_-(y_{k-1}^ay_k^bH) = B_aB_bH`.
* `HJO.Sweep.dminus_dminus_braid`.

## Implementation notes

**Why the reduction is factored out.** Both lemmas' proofs open identically: `T_{k-1}F - F`
lies in the image of `∂_{k-1}` by `HJO.Sweep.braid_sub_self` (which
gives the factorisation `(qy_{k-1} - y_k)∂_{k-1}F` outright rather than an inclusion of images);
`G = ∂_{k-1}F` lies in `V_k` by `HJO.Sweep.dividedDiff_mem_piece` and is `s_{k-1}`-symmetric by
`HJO.Sweep.swapAux_dividedDiff`; and `HJO.Sweep.exists_symmetrised_sum` then writes it as a finite
sum of symmetrised monomials. Nothing in that chain mentions which lowering operator is meant, so it
is stated once for an arbitrary `𝕜`-linear `Φ`, and each lemma supplies only the vanishing on a
single symmetrised monomial. The "both sides are `𝕜`-linear in `G`" is the linearity of `Φ`.

**The level is read at `k = m + 2`, so nothing is truncated.** The `k ≥ 2` is what makes
`T_{k-1}` a genuine braid operator and `V_{k-2}` a genuine graded piece; writing `k = m + 2` turns
`k-1` into `m+1` and `k-2` into `m`, and the `ℕ`-subtractions of
`HJO.Sweep.exists_symmetrised_sum`'s statement are discharged once, where it is invoked.

**The two computations on a monomial differ by a sign and a shift, and that is the whole
difference.** `HJO.Sweep.dminusCM_dminusCM_auxVar_pow_mul` gives
`d_-d_-(y_{k-1}^ay_k^bH) = B_{a+1}B_{b+1}H`, so the defect becomes
`qB_{a+2}B_{b+1}H - B_{a+1}B_{b+2}H` and the antisymmetry needed is `HJO.Sweep.bopExt_pair_antisymm`
at `(a, b)`. `HJO.Sweep.dminus_dminus_auxVar_pow_mul` — the same computation for `d^♭_-`, from
`HJO.Sweep.dminus_auxVar_pow_mul` applied twice — gives `B_aB_bH` instead, so the defect is
`qB_{a+1}B_bH - B_aB_{b+1}H` and what is needed is the relation itself (`HJO.Sweep.bopExt_hmz`) at
`m = a`, `n = b+1`. Both are the same `HJO.Sym.bop_pair_antisymm`.

**Scalars are converted to `HJO.Sweep.scal q`** before the final cancellation, so that the four
`B`-words can be combined by `ring`; `HJO.Sweep.scal_mul_eq_smul` is that conversion, and it is
available here because this file works over a field, as both operators require.

## References

Lemmas `HJO.Sweep.dminusCM_dminusCM_braid` (a Carlsson--Mellit relation) and
`HJO.Sweep.dminus_dminus_braid` (its analogue for the modified generators), using `HJO.Sweep.piece`,
`HJO.Sweep.braid`, `HJO.Sweep.dminusCM`, `HJO.Sweep.dminus` and `HJO.Sym.Bop`, and proved from
`HJO.Sweep.braid_sub_self`, `HJO.Sweep.swapAux_dividedDiff`, `HJO.Sweep.exists_symmetrised_sum`,
`HJO.Sweep.dminusCM_dminusCM_auxVar_pow_mul`, `HJO.Sweep.dminus_auxVar_pow_mul`,
`HJO.Sweep.bopExt_pair_antisymm` and `HJO.Sym.bop_pair_antisymm`. Transcribing E. Carlsson and A.
Mellit, *A proof of the shuffle conjecture*, Lemma 5.3, and A. Mellit, *Toric braids and
`(m, n)`-parking functions*, §3.
-/

@[expose] public section

namespace HJO.Sweep

section DminusSq

variable {L : Type*} [Field L] [Algebra ℚ L]

omit [Algebra ℚ L] in
/-- Multiplication by the doubly constant polynomial `scal x` is the action of `x` on the total
space: `scal x * F = x • F`. -/
theorem scal_mul_eq_smul (x : L) (F : Total L) : (scal x : Total L) * F = x • F := by
  rw [scal_eq_algebraMap, ← Algebra.smul_def]

/-- **The shared reduction.** If a `𝕜`-linear operator `Φ` kills every element
`(qy_{k-1} - y_k)(y_{k-1}^ay_k^b + y_{k-1}^by_k^a)H` with `H ∈ V_{k-2}`, then
`Φ(T_{k-1}F) = Φ(F)` for every `F ∈ V_k`, at `k = m + 2`.

`HJO.Sweep.braid_sub_self` factors `T_{k-1}F - F` as `(qy_{k-1} - y_k)∂_{k-1}F`; the factor
`∂_{k-1}F` lies in `V_k` by `HJO.Sweep.dividedDiff_mem_piece` and is fixed by `s_{k-1}` by
`HJO.Sweep.swapAux_dividedDiff`, so `HJO.Sweep.exists_symmetrised_sum` expands it as a finite sum of
symmetrised monomials, over which `Φ` distributes. -/
theorem eq_of_braid_defect_last (q : L) (Φ : Total L →ₗ[L] Total L) (m : ℕ) {F : Total L}
    (hF : F ∈ piece L (m + 2))
    (hzero : ∀ (a b : ℕ) (H : Total L), H ∈ piece L m →
      Φ (((scal q : Total L) * auxVar (m + 1) - auxVar (m + 2)) *
          (((auxVar (m + 1) : Total L) ^ a * auxVar (m + 2) ^ b
            + (auxVar (m + 1) : Total L) ^ b * auxVar (m + 2) ^ a) * H)) = 0) :
    Φ (braid q (m + 1) F) = Φ F := by
  have hG : dividedDiff (m + 1) F ∈ piece L (m + 2) :=
    dividedDiff_mem_piece (by omega) (by omega) hF
  have hsym : swapAux L (m + 2 - 1) (dividedDiff (m + 1) F) = dividedDiff (m + 1) F := by
    rw [show m + 2 - 1 = m + 1 by omega]
    exact swapAux_dividedDiff (m + 1) F
  obtain ⟨s, H, hH, hGsum⟩ := exists_symmetrised_sum (L := L) (k := m + 2) (by omega) hG hsym
  simp only [show m + 2 - 2 = m by omega] at hH
  rw [show m + 2 - 1 = m + 1 by omega] at hGsum
  have hdiff : braid q (m + 1) F - F
      = ((scal q : Total L) * auxVar (m + 1) - auxVar (m + 2)) * dividedDiff (m + 1) F := by
    have h := braid_sub_self q (m + 1) F
    rwa [show m + 1 + 1 = m + 2 by omega] at h
  refine sub_eq_zero.1 ?_
  rw [← map_sub, hdiff, hGsum, Finset.mul_sum, map_sum]
  exact Finset.sum_eq_zero fun p _ => hzero p.1 p.2 (H p) (hH p)

/-! ### Carlsson and Mellit's own lowering operator -/

/-- **The square of the lowering operator kills the braid defect.** For
`k ≥ 2`, read at `k = m + 2`, and every `F ∈ V_k`,
`d_-(d_-(T_{k-1}F)) = d_-(d_-F)`.

By `HJO.Sweep.eq_of_braid_defect_last` what has to be shown is that `d_-d_-` kills
`(qy_{k-1} - y_k)(y_{k-1}^ay_k^b + y_{k-1}^by_k^a)H`. Expanding, that is four monomials, and
`HJO.Sweep.dminusCM_dminusCM_auxVar_pow_mul` turns them into `qB_{a+2}B_{b+1}H - B_{a+1}B_{b+2}H`
and the same with `a, b` interchanged; those are negatives of each other by
`HJO.Sweep.bopExt_pair_antisymm`. -/
@[hjo "lem_cm_rel_dminus_sq"]
theorem dminusCM_dminusCM_braid (q : L) (m : ℕ) {F : Total L} (hF : F ∈ piece L (m + 2)) :
    dminusCM q (m + 1) (dminusCM q (m + 2) (braid q (m + 1) F))
      = dminusCM q (m + 1) (dminusCM q (m + 2) F) := by
  have hzero : ∀ (a b : ℕ) (H : Total L), H ∈ piece L m →
      ((dminusCM q (m + 1)).comp (dminusCM q (m + 2)))
          (((scal q : Total L) * auxVar (m + 1) - auxVar (m + 2)) *
            (((auxVar (m + 1) : Total L) ^ a * auxVar (m + 2) ^ b
              + (auxVar (m + 1) : Total L) ^ b * auxVar (m + 2) ^ a) * H)) = 0 := by
    intro a b H hH
    have hmon : ∀ c d : ℕ, dminusCM q (m + 1) (dminusCM q (m + 2)
          ((auxVar (m + 1) : Total L) ^ c * auxVar (m + 2) ^ d * H))
        = bopExt q ((c : ℤ) + 1) (bopExt q ((d : ℤ) + 1) H) :=
      fun c d => dminusCM_dminusCM_auxVar_pow_mul q m c d hH
    have h1 : dminusCM q (m + 1) (dminusCM q (m + 2)
          ((auxVar (m + 1) : Total L) ^ (a + 1) * auxVar (m + 2) ^ b * H))
        = bopExt q ((a : ℤ) + 2) (bopExt q ((b : ℤ) + 1) H) := by
      rw [hmon, show (((a + 1 : ℕ) : ℤ) + 1) = (a : ℤ) + 2 by push_cast; ring]
    have h2 : dminusCM q (m + 1) (dminusCM q (m + 2)
          ((auxVar (m + 1) : Total L) ^ a * auxVar (m + 2) ^ (b + 1) * H))
        = bopExt q ((a : ℤ) + 1) (bopExt q ((b : ℤ) + 2) H) := by
      rw [hmon, show (((b + 1 : ℕ) : ℤ) + 1) = (b : ℤ) + 2 by push_cast; ring]
    have h3 : dminusCM q (m + 1) (dminusCM q (m + 2)
          ((auxVar (m + 1) : Total L) ^ (b + 1) * auxVar (m + 2) ^ a * H))
        = bopExt q ((b : ℤ) + 2) (bopExt q ((a : ℤ) + 1) H) := by
      rw [hmon, show (((b + 1 : ℕ) : ℤ) + 1) = (b : ℤ) + 2 by push_cast; ring]
    have h4 : dminusCM q (m + 1) (dminusCM q (m + 2)
          ((auxVar (m + 1) : Total L) ^ b * auxVar (m + 2) ^ (a + 1) * H))
        = bopExt q ((b : ℤ) + 1) (bopExt q ((a : ℤ) + 2) H) := by
      rw [hmon, show (((a + 1 : ℕ) : ℤ) + 1) = (a : ℤ) + 2 by push_cast; ring]
    have hexp : ((scal q : Total L) * auxVar (m + 1) - auxVar (m + 2)) *
        (((auxVar (m + 1) : Total L) ^ a * auxVar (m + 2) ^ b
          + (auxVar (m + 1) : Total L) ^ b * auxVar (m + 2) ^ a) * H)
        = q • ((auxVar (m + 1) : Total L) ^ (a + 1) * auxVar (m + 2) ^ b * H)
          - (auxVar (m + 1) : Total L) ^ a * auxVar (m + 2) ^ (b + 1) * H
          + (q • ((auxVar (m + 1) : Total L) ^ (b + 1) * auxVar (m + 2) ^ a * H)
            - (auxVar (m + 1) : Total L) ^ b * auxVar (m + 2) ^ (a + 1) * H) := by
      simp only [← scal_mul_eq_smul]
      ring
    have key := bopExt_pair_antisymm q (a : ℤ) (b : ℤ) H
    simp only [LinearMap.comp_apply, hexp, map_add, map_sub, map_smul, h1, h2, h3, h4]
    simp only [← scal_mul_eq_smul] at key ⊢
    linear_combination key
  have h := eq_of_braid_defect_last q ((dminusCM q (m + 1)).comp (dminusCM q (m + 2))) m hF hzero
  simpa only [LinearMap.comp_apply] using h

/-! ### The modified lowering operator -/

/-- **The modified lowering operator twice on a monomial in the last two variables**:
`d^♭_-(d^♭_-(y_{k-1}^ay_k^bH)) = B_a(B_b(H))` for `H ∈ Λ ⊗ 𝕜[y_1, …, y_{k-2}]`, read at the
stated `k` equal to `k + 2` so that the hypothesis is `H ∈ V_k`.

This is `HJO.Sweep.dminus_auxVar_pow_mul` applied twice — first in the
variable `y_{k+2}`, then in `y_{k+1}` — the factor `y_{k+1}^a` passing the inner operator by its
`𝕜[y]`-linearity. It is the modified counterpart of `HJO.Sweep.dminusCM_dminusCM_auxVar_pow_mul`,
and differs from it exactly as the two operators do: no sign, and no shift of the two indices. -/
theorem dminus_dminus_auxVar_pow_mul (q : L) (k a b : ℕ) {H : Total L} (hH : H ∈ piece L k) :
    dminus q (k + 1) (dminus q (k + 2)
        ((auxVar (k + 1) : Total L) ^ a * (auxVar (k + 2) : Total L) ^ b * H))
      = bopExt q (a : ℤ) (bopExt q (b : ℤ) H) := by
  have hH1 : (auxVar (k + 1) : Total L) ^ a * H ∈ piece L (k + 1) :=
    mul_mem (pow_mem (auxVar_mem_piece (by omega) le_rfl) a) (piece_mono (by omega) hH)
  have key := dminus_auxVar_pow_mul q (k + 1) b hH1
  rw [show k + 1 + 1 = k + 2 from rfl] at key
  have hmono : (auxVar (k + 1) : Total L) ^ a = MvPolynomial.monomial (Finsupp.single k a) 1 := by
    rw [auxVar, Nat.add_sub_cancel, MvPolynomial.X_pow_eq_monomial]
  have hbop : bopExt q (b : ℤ) H ∈ piece L k := bopExt_mem_piece q _ hH
  calc dminus q (k + 1) (dminus q (k + 2)
        ((auxVar (k + 1) : Total L) ^ a * (auxVar (k + 2) : Total L) ^ b * H))
      = dminus q (k + 1) (dminus q (k + 2)
          ((auxVar (k + 2) : Total L) ^ b * ((auxVar (k + 1) : Total L) ^ a * H))) := by
        rw [show (auxVar (k + 1) : Total L) ^ a * (auxVar (k + 2) : Total L) ^ b * H
          = (auxVar (k + 2) : Total L) ^ b * ((auxVar (k + 1) : Total L) ^ a * H) from by ring]
    _ = dminus q (k + 1) (bopExt q (b : ℤ) ((auxVar (k + 1) : Total L) ^ a * H)) := by rw [key]
    _ = dminus q (k + 1) ((auxVar (k + 1) : Total L) ^ a * bopExt q (b : ℤ) H) := by
        rw [hmono, bopExt_monomial_mul]
    _ = bopExt q (a : ℤ) (bopExt q (b : ℤ) H) := dminus_auxVar_pow_mul q k a hbop

/-- **The modified lowering operator squared kills the braid defect.** For
`k ≥ 2`, read at `k = m + 2`, and every `F ∈ V_k`,
`d^♭_-(d^♭_-(T_{k-1}F)) = d^♭_-(d^♭_-F)`.

The reduction is `HJO.Sweep.eq_of_braid_defect_last`, as for the unmodified operator; the four
monomials are evaluated by `HJO.Sweep.dminus_dminus_auxVar_pow_mul`, giving
`qB_{a+1}B_bH - B_aB_{b+1}H` and the same with `a, b` interchanged, and those are negatives of each
other by the Haglund--Morse--Zabrocki relation at `m = a`, `n = b+1`. -/
@[hjo "lem_vmod_dminus_sq_mod"]
theorem dminus_dminus_braid (q : L) (m : ℕ) {F : Total L} (hF : F ∈ piece L (m + 2)) :
    dminus q (m + 1) (dminus q (m + 2) (braid q (m + 1) F))
      = dminus q (m + 1) (dminus q (m + 2) F) := by
  have hzero : ∀ (a b : ℕ) (H : Total L), H ∈ piece L m →
      ((dminus q (m + 1)).comp (dminus q (m + 2)))
          (((scal q : Total L) * auxVar (m + 1) - auxVar (m + 2)) *
            (((auxVar (m + 1) : Total L) ^ a * auxVar (m + 2) ^ b
              + (auxVar (m + 1) : Total L) ^ b * auxVar (m + 2) ^ a) * H)) = 0 := by
    intro a b H hH
    have hmon : ∀ c d : ℕ, dminus q (m + 1) (dminus q (m + 2)
          ((auxVar (m + 1) : Total L) ^ c * auxVar (m + 2) ^ d * H))
        = bopExt q (c : ℤ) (bopExt q (d : ℤ) H) :=
      fun c d => dminus_dminus_auxVar_pow_mul q m c d hH
    have h1 : dminus q (m + 1) (dminus q (m + 2)
          ((auxVar (m + 1) : Total L) ^ (a + 1) * auxVar (m + 2) ^ b * H))
        = bopExt q ((a : ℤ) + 1) (bopExt q (b : ℤ) H) := by
      rw [hmon, show (((a + 1 : ℕ) : ℤ)) = (a : ℤ) + 1 by push_cast; ring]
    have h2 : dminus q (m + 1) (dminus q (m + 2)
          ((auxVar (m + 1) : Total L) ^ a * auxVar (m + 2) ^ (b + 1) * H))
        = bopExt q (a : ℤ) (bopExt q ((b : ℤ) + 1) H) := by
      rw [hmon, show (((b + 1 : ℕ) : ℤ)) = (b : ℤ) + 1 by push_cast; ring]
    have h3 : dminus q (m + 1) (dminus q (m + 2)
          ((auxVar (m + 1) : Total L) ^ (b + 1) * auxVar (m + 2) ^ a * H))
        = bopExt q ((b : ℤ) + 1) (bopExt q (a : ℤ) H) := by
      rw [hmon, show (((b + 1 : ℕ) : ℤ)) = (b : ℤ) + 1 by push_cast; ring]
    have h4 : dminus q (m + 1) (dminus q (m + 2)
          ((auxVar (m + 1) : Total L) ^ b * auxVar (m + 2) ^ (a + 1) * H))
        = bopExt q (b : ℤ) (bopExt q ((a : ℤ) + 1) H) := by
      rw [hmon, show (((a + 1 : ℕ) : ℤ)) = (a : ℤ) + 1 by push_cast; ring]
    have hexp : ((scal q : Total L) * auxVar (m + 1) - auxVar (m + 2)) *
        (((auxVar (m + 1) : Total L) ^ a * auxVar (m + 2) ^ b
          + (auxVar (m + 1) : Total L) ^ b * auxVar (m + 2) ^ a) * H)
        = q • ((auxVar (m + 1) : Total L) ^ (a + 1) * auxVar (m + 2) ^ b * H)
          - (auxVar (m + 1) : Total L) ^ a * auxVar (m + 2) ^ (b + 1) * H
          + (q • ((auxVar (m + 1) : Total L) ^ (b + 1) * auxVar (m + 2) ^ a * H)
            - (auxVar (m + 1) : Total L) ^ b * auxVar (m + 2) ^ (a + 1) * H) := by
      simp only [← scal_mul_eq_smul]
      ring
    have key := bopExt_hmz q (a : ℤ) ((b : ℤ) + 1) H
    rw [show (b : ℤ) + 1 - 1 = (b : ℤ) by ring] at key
    simp only [LinearMap.comp_apply, hexp, map_add, map_sub, map_smul, h1, h2, h3, h4]
    simp only [← scal_mul_eq_smul] at key ⊢
    linear_combination -key
  have h := eq_of_braid_defect_last q ((dminus q (m + 1)).comp (dminus q (m + 2))) m hF hzero
  simpa only [LinearMap.comp_apply] using h

end DminusSq

end HJO.Sweep
