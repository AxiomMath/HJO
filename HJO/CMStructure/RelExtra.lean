/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.CMStructure.CmCommutator
public import HJO.CMStructure.QShiftNegBraid
public import HJO.CMStructure.VmodCommutatorMod
public import HJO.CarlssonMellit.ConjugationOperator
public meta import HJO.Attr

/-! # The two relations of the corner element

The last two of the nine relation families of `HJO.Dyck.Aq`, read on Carlsson and Mellit's own
operators `d_±` of `HJO.Sweep.cmDPlus` and `HJO.Sweep.dminusCM`. Writing `C_k` for the commutator
`d_+d_- - d_-d_+` on `V_k`, which `HJO.Sweep.dminusCM_cmDPlus_sub_cmDPlus_dminusCM` evaluates to
`(q-1)T_{[1,k-1]}(y_k\cdot)`:

* `HJO.Sweep.dminusCM_commutator_braid`: `d_-(C_k(T_{k-1}F)) = q C_{k-1}(d_-F)` for `k ≥ 2`;
* `HJO.Sweep.braid_one_commutator_cmDPlus`: `T_1(C_{k+1}(d_+F)) = q d_+(C_kF)` for `k ≥ 1`.

Both are consequences of `HJO.Sweep.dminusCM_cmDPlus_sub_cmDPlus_dminusCM` alone: each side becomes
a braid word applied to a variable times something, and the two words are identified by one
conjugation, `HJO.Sweep.braid_auxVar_succ_mul_braid`.

## Main results

* `HJO.Sweep.dminusCM_commutator_braid`.
* `HJO.Sweep.braid_one_commutator_cmDPlus`.

## Implementation notes

**These are the unstarred siblings of `HJO.Sweep.dminus_commutator_braid` and
`HJO.Sweep.braid_one_commutator_dplus`** (in `VmodExtraMod.lean`), which are the same two relations
for the *modified* operators `d^♭_±`. The first proof here is the first proof there, letter for
letter, with `d^♭_-` replaced by `d_-`; the second is *not*, and the difference is worth recording.
For the modified operators the second relation is routed through
`HJO.Sweep.cmAscWord_auxVar_last_mul`, which rewrites the word on the last variable as
`q^ky_1T^*_{1↑k}` and therefore needs `q ≠ 0` for the starred word to exist. The proof of
`HJO.Sweep.braid_one_commutator_cmDPlus` uses no starred word: it moves `y_{k+1}` inwards past
`T_1, …, T_{k-1}` by `HJO.Sweep.braid_mul_mem_supported`, applies `HJO.Sweep.cmAscWord_word_shift`
twice and `HJO.Sweep.braid_auxVar_succ_mul_braid` once. So **neither lemma here carries `q ≠ 0`**,
where both modified siblings do.

**The commutator is written out rather than named**, as in `VmodExtraMod.lean`: it occurs at three
different vertices across the two statements and is not needed as an operator in its own right, so
spelling it out keeps each statement's operator indices visible. The sign is `d_+d_- - d_-d_+`,
which is `HJO.Sweep.dminusCM_cmDPlus_sub_cmDPlus_dminusCM` negated — that lemma states
`(d_-d_+ - d_+d_-)F = (1-q)T_{[1,k-1]}(y_kF)`, and negating both sides gives the `(q-1)` form the
two proofs quote.

**Indices.** `HJO.Sweep.dminusCM_commutator_braid` is read at `k = m + 2`, its `k ≥ 2` being what
makes `T_{k-1}` one of `V_k`'s own braid operators and what puts
`HJO.Sweep.dminusCM_cmDPlus_sub_cmDPlus_dminusCM` at the vertex `k-1` in range;
`HJO.Sweep.braid_one_commutator_cmDPlus` is read at `k = m + 1`, its `k ≥ 1` being what the factor
`T_1` on `V_{k+1}` needs. No subtraction is truncated in either.

**The scalar is `HJO.Sweep.scal q`**, the doubly constant polynomial, matching
`HJO.Sweep.dminusCM_cmDPlus_sub_cmDPlus_dminusCM`'s own `scal (1-q)` and the modified siblings; the
operators are `𝕜`-linear, so `HJO.Sweep.cmAscWord_scal_mul`, `HJO.Sweep.dminusCM_scal_mul`,
`HJO.Sweep.cmDPlus_scal_mul` and `HJO.Sweep.braid_scal_mul` move it out of each of them.

## References

This file proves `HJO.Sweep.dminusCM_commutator_braid` and `HJO.Sweep.braid_one_commutator_cmDPlus`,
using `HJO.Sweep.piece`, `HJO.Sweep.braid`, `HJO.Sweep.cmDPlus` and `HJO.Sweep.dminusCM`, from
`HJO.Sweep.cmAscWord`, `HJO.Sweep.dminusCM_cmDPlus_sub_cmDPlus_dminusCM`,
`HJO.Sweep.braid_auxVar_succ_mul_braid`, `HJO.Sweep.dminusCM_auxVar_mul`,
`HJO.Sweep.dminusCM_braid`, `HJO.Sweep.cmDPlus_apply`, `HJO.Sweep.braid_mul_mem_supported`,
`HJO.Sweep.cmAscWord_word_shift` and `HJO.Sweep.cmDPlus_braid`; both are consumed by
`HJO.Sweep.exists_isDpaAction_cm`. E. Carlsson and A. Mellit, *A proof of the shuffle conjecture*,
Lemma 5.3.
-/

@[expose] public section

namespace HJO.Sweep

section Field

variable {L : Type*} [Field L]

/-- **`d_+` commutes with a scalar**, being `𝕜`-linear. -/
theorem cmDPlus_scal_mul (q : L) (k : ℕ) (x : L) (F : Total L) :
    cmDPlus q k (scal x * F) = scal x * cmDPlus q k F := by
  rw [scal_eq_algebraMap, ← Algebra.smul_def, map_smul, Algebra.smul_def, ← scal_eq_algebraMap]

/-- **`d_+T_{[1,m]} = T_{[2,m+1]}d_+` on `V_{m+1}`**, the word-level form of
`HJO.Sweep.cmDPlus_braid`: the raising operator shifts each letter of the word up by one
(`HJO.Sweep.cmDPlus_mul_braidEnd`, whose range `1 ≤ i ≤ m` is exactly the word's), and shifting an
index range by one turns `T_{[1,m]}` into `T_{[2,m+1]}`. -/
theorem cmDPlus_mul_cmAscWord (q : L) (m : ℕ) :
    cmDPlus q (m + 1) * cmAscWord q 1 m = cmAscWord q 2 (m + 1) * cmDPlus q (m + 1) := by
  rw [cmAscWord_eq_ascendingWord q (a := 1) (b := m) (by omega),
    cmAscWord_eq_ascendingWord q (a := 2) (b := m + 1) (by omega)]
  exact Braid.mul_ascendingWord (by omega) fun i hi him => cmDPlus_mul_braidEnd q hi (by omega)

/-- `d_+(T_{[1,m]}F) = T_{[2,m+1]}(d_+F)`, the applied form. -/
theorem cmDPlus_cmAscWord (q : L) (m : ℕ) (F : Total L) :
    cmDPlus q (m + 1) (cmAscWord q 1 m F) = cmAscWord q 2 (m + 1) (cmDPlus q (m + 1) F) :=
  LinearMap.congr_fun (cmDPlus_mul_cmAscWord q m) F

/-- **`s_j` fixes `y_{m+2}` for `j ≤ m`**: the transposition moves `y_j` and `y_{j+1}` only, and
`j + 1 ≤ m + 1 < m + 2`. This is the instance of `HJO.Sweep.braid_mul_mem_supported` the proof of
`HJO.Sweep.braid_one_commutator_cmDPlus` reads, in the form `HJO.Sweep.cmAscWord_mul_of_swapAux_eq`
takes. -/
theorem swapAux_auxVar_last (L : Type*) [Field L] {j m : ℕ} (hjm : j ≤ m) :
    swapAux L j ((auxVar (m + 2) : Total L)) = auxVar (m + 2) := by
  rw [show (auxVar (m + 2) : Total L) = MvPolynomial.X (m + 1) from by rw [auxVar]; congr 1,
    swapAux_X, Equiv.swap_apply_of_ne_of_ne (by omega) (by omega)]

end Field

section Newton

variable {L : Type*} [Field L] [Algebra ℚ L]

/-- **`HJO.Sweep.dminusCM_cmDPlus_sub_cmDPlus_dminusCM` with the sign**:
`(d_+d_- - d_-d_+)F = (q-1)T_{[1,k-1]}(y_kF)` for `F ∈ V_k`, read at `k = m + 1`. The lemma as
stated there has the negative of both sides. -/
theorem cmDPlus_dminusCM_sub_dminusCM_cmDPlus (q : L) (m : ℕ) {F : Total L}
    (hF : F ∈ piece L (m + 1)) :
    cmDPlus q m (dminusCM q (m + 1) F) - dminusCM q (m + 2) (cmDPlus q (m + 1) F)
      = scal (q - 1) * cmAscWord q 1 m ((auxVar (m + 1) : Total L) * F) := by
  have h := dminusCM_cmDPlus_sub_cmDPlus_dminusCM q m hF
  rw [show (scal (q - 1) : Total L) = -scal (1 - q) from by
    rw [show q - 1 = -(1 - q) from by ring, scal_neg]]
  linear_combination -h

/-! ### The lowering relation of the corner element -/

/-- **The lowering relation of the corner element.** For `k ≥ 2`, read at
`k = m + 2`, and every `F ∈ V_k`,

`d_-((d_+d_- - d_-d_+)(T_{k-1}F)) = q (d_+d_- - d_-d_+)(d_-F)`.

The proof. `HJO.Sweep.dminusCM_cmDPlus_sub_cmDPlus_dminusCM` at the vertex `k` turns the left-hand
side into `(q-1)d_-T_{[1,k-1]}(y_kT_{k-1}F)`; splitting the last letter off the word
(`HJO.Sweep.cmAscWord_one_succ_apply`) exposes `T_{k-1}(y_kT_{k-1}F)`, which is `qy_{k-1}F` by
`HJO.Sweep.braid_auxVar_succ_mul_braid`; and `d_-` then passes the shorter word `T_{[1,k-2]}`
(`HJO.Sweep.dminusCM_cmAscWord`, off `HJO.Sweep.dminusCM_braid`, whose index range `1 ≤ i ≤ k-2` is
exactly the one occurring) and the variable `y_{k-1}` (`HJO.Sweep.dminusCM_auxVar_mul`), leaving
`q(q-1)T_{[1,k-2]}(y_{k-1}d_-F)` — which is `HJO.Sweep.dminusCM_cmDPlus_sub_cmDPlus_dminusCM` at the
vertex `k-1`, applied to `d_-F`. -/
@[hjo "lem_cm_rel_extra_down"]
theorem dminusCM_commutator_braid (q : L) (m : ℕ) {F : Total L} (hF : F ∈ piece L (m + 2)) :
    dminusCM q (m + 2) (cmDPlus q (m + 1) (dminusCM q (m + 2) (braid q (m + 1) F))
        - dminusCM q (m + 3) (cmDPlus q (m + 2) (braid q (m + 1) F)))
      = scal q * (cmDPlus q m (dminusCM q (m + 1) (dminusCM q (m + 2) F))
        - dminusCM q (m + 2) (cmDPlus q (m + 1) (dminusCM q (m + 2) F))) := by
  have hc2 : ∀ X : Total L, X ∈ piece L (m + 2) →
      cmDPlus q (m + 1) (dminusCM q (m + 2) X) - dminusCM q (m + 3) (cmDPlus q (m + 2) X)
        = scal (q - 1) * cmAscWord q 1 (m + 1) ((auxVar (m + 2) : Total L) * X) := by
    intro X hX
    have h := cmDPlus_dminusCM_sub_dminusCM_cmDPlus q (m + 1) hX
    simpa only [show m + 1 + 1 = m + 2 by omega, show m + 1 + 2 = m + 3 by omega] using h
  have hTF : braid q (m + 1) F ∈ piece L (m + 2) := braid_mem_piece q (by omega) (by omega) hF
  have hdF : dminusCM q (m + 2) F ∈ piece L (m + 1) := dminusCM_mem_piece q (m + 1) hF
  have hconj : braid q (m + 1) ((auxVar (m + 2) : Total L) * braid q (m + 1) F)
      = scal q * auxVar (m + 1) * F :=
    braid_auxVar_succ_mul_braid q (i := m + 1) (by omega) F
  rw [hc2 _ hTF, cmDPlus_dminusCM_sub_dminusCM_cmDPlus q m hdF,
    cmAscWord_one_succ_apply q m, hconj,
    show (scal q : Total L) * auxVar (m + 1) * F = scal q * ((auxVar (m + 1) : Total L) * F)
      from by ring,
    cmAscWord_scal_mul, dminusCM_scal_mul, dminusCM_scal_mul,
    dminusCM_cmAscWord q (le_refl m), dminusCM_auxVar_mul q (by omega) (le_refl (m + 1))]
  ring

/-! ### The raising relation of the corner element -/

omit [Algebra ℚ L] in
/-- **The word identity behind `HJO.Sweep.braid_one_commutator_cmDPlus`**:

`T_1T_{[1,k]}(y_{k+1}d_+F) = q d_+T_{[1,k-1]}(y_kF)` for `k = m + 1`.

Both sides are brought to `T_{[2,k]}T_{[1,k]}(y_kG)` with `G = τ_{k+1,k+1}(F)`. On the left,
`d_+F = T_{[1,k]}G` (`HJO.Sweep.cmDPlus_apply`); `y_{k+1}` moves inside `T_{[1,k-1]}` by
`HJO.Sweep.braid_mul_mem_supported`, admissible because every letter index `j ≤ k-1` has
`k+1 ∉ {j, j+1}` (`HJO.Sweep.swapAux_auxVar_last`); `HJO.Sweep.cmAscWord_word_shift` moves the long
word past the short one; and `T_k(y_{k+1}T_kG) = qy_kG` is `HJO.Sweep.braid_auxVar_succ_mul_braid`.
Applying `T_1` recombines `T_1T_{[2,k]} = T_{[1,k]}` and `HJO.Sweep.cmAscWord_word_shift` is used
once more. On the right, `d_+` moves inwards through `T_{[1,k-1]}` by `HJO.Sweep.cmDPlus_braid`
(`HJO.Sweep.cmDPlus_cmAscWord`), and `d_+(y_kF) = T_{[1,k]}(y_kG)` because `τ_{k+1,k+1}` fixes
`y_k`. -/
theorem braid_one_cmAscWord_auxVar_mul_cmDPlus (q : L) (m : ℕ) (F : Total L) :
    braid q 1 (cmAscWord q 1 (m + 1) ((auxVar (m + 2) : Total L) * cmDPlus q (m + 1) F))
      = scal q * cmDPlus q (m + 1) (cmAscWord q 1 m ((auxVar (m + 1) : Total L) * F)) := by
  have hfix : ∀ j, 1 ≤ j → j ≤ m → swapAux L j ((auxVar (m + 2) : Total L)) = auxVar (m + 2) :=
    fun j _ hjm => swapAux_auxVar_last L hjm
  have h1 : (auxVar (m + 2) : Total L) * cmDPlus q (m + 1) F
      = cmAscWord q 1 m ((auxVar (m + 2) : Total L)
        * braid q (m + 1) (qshift q (m + 2) F)) := by
    rw [cmDPlus_apply, cmAscWord_one_succ_apply q m,
      cmAscWord_mul_of_swapAux_eq q (b := m) (by omega) hfix]
  calc braid q 1 (cmAscWord q 1 (m + 1) ((auxVar (m + 2) : Total L) * cmDPlus q (m + 1) F))
      = braid q 1 (cmAscWord q 1 (m + 1) (cmAscWord q 1 m ((auxVar (m + 2) : Total L)
          * braid q (m + 1) (qshift q (m + 2) F)))) := by rw [h1]
    _ = braid q 1 (cmAscWord q 2 (m + 1) (cmAscWord q 1 (m + 1) ((auxVar (m + 2) : Total L)
          * braid q (m + 1) (qshift q (m + 2) F)))) := by rw [cmAscWord_word_shift_apply]
    _ = braid q 1 (cmAscWord q 2 (m + 1) (cmAscWord q 1 m (braid q (m + 1)
          ((auxVar (m + 2) : Total L) * braid q (m + 1) (qshift q (m + 2) F))))) := by
        rw [cmAscWord_one_succ_apply]
    _ = braid q 1 (cmAscWord q 2 (m + 1) (cmAscWord q 1 m
          (scal q * ((auxVar (m + 1) : Total L) * qshift q (m + 2) F)))) := by
        rw [braid_auxVar_succ_mul_braid q (i := m + 1) (by omega),
          show (scal q : Total L) * auxVar (m + 1) * qshift q (m + 2) F
            = scal q * ((auxVar (m + 1) : Total L) * qshift q (m + 2) F) from by ring]
    _ = scal q * cmAscWord q 1 (m + 1) (cmAscWord q 1 m
          ((auxVar (m + 1) : Total L) * qshift q (m + 2) F)) := by
        rw [cmAscWord_scal_mul, cmAscWord_scal_mul, braid_scal_mul,
          ← cmAscWord_apply_succ_left q (show 1 ≤ m + 1 by omega)]
    _ = scal q * cmAscWord q 2 (m + 1) (cmAscWord q 1 (m + 1)
          ((auxVar (m + 1) : Total L) * qshift q (m + 2) F)) := by
        rw [cmAscWord_word_shift_apply]
    _ = scal q * cmDPlus q (m + 1) (cmAscWord q 1 m ((auxVar (m + 1) : Total L) * F)) := by
        have hq2 : qshift q (m + 1 + 1) ((auxVar (m + 1) : Total L) * F)
            = (auxVar (m + 1) : Total L) * qshift q (m + 2) F := by
          rw [show m + 1 + 1 = m + 2 by omega, map_mul, qshift_auxVar_apply]
        rw [cmDPlus_cmAscWord, cmDPlus_apply, hq2]

/-- **The raising relation of the corner element.** For `k ≥ 1`, read at
`k = m + 1`, and every `F ∈ V_k`,

`T_1((d_+d_- - d_-d_+)(d_+F)) = q d_+((d_+d_- - d_-d_+)F)`.

`HJO.Sweep.dminusCM_cmDPlus_sub_cmDPlus_dminusCM` at the vertex `k+1` makes the left-hand side
`(q-1)T_1T_{[1,k]}(y_{k+1}d_+F)` and at the vertex `k` makes the right-hand side
`q(q-1)d_+T_{[1,k-1]}(y_kF)`; the two are equal by
`HJO.Sweep.braid_one_cmAscWord_auxVar_mul_cmDPlus`, which is the word computation of the usual
proof. No hypothesis on `q` is needed — see the note at the head of this file. -/
@[hjo "lem_cm_rel_extra_up"]
theorem braid_one_commutator_cmDPlus (q : L) (m : ℕ) {F : Total L} (hF : F ∈ piece L (m + 1)) :
    braid q 1 (cmDPlus q (m + 1) (dminusCM q (m + 2) (cmDPlus q (m + 1) F))
        - dminusCM q (m + 3) (cmDPlus q (m + 2) (cmDPlus q (m + 1) F)))
      = scal q * cmDPlus q (m + 1) (cmDPlus q m (dminusCM q (m + 1) F)
        - dminusCM q (m + 2) (cmDPlus q (m + 1) F)) := by
  have hc2 : ∀ X : Total L, X ∈ piece L (m + 2) →
      cmDPlus q (m + 1) (dminusCM q (m + 2) X) - dminusCM q (m + 3) (cmDPlus q (m + 2) X)
        = scal (q - 1) * cmAscWord q 1 (m + 1) ((auxVar (m + 2) : Total L) * X) := by
    intro X hX
    have h := cmDPlus_dminusCM_sub_dminusCM_cmDPlus q (m + 1) hX
    simpa only [show m + 1 + 1 = m + 2 by omega, show m + 1 + 2 = m + 3 by omega] using h
  have hX : cmDPlus q (m + 1) F ∈ piece L (m + 2) := cmDPlus_mem_piece q (m + 1) hF
  rw [hc2 _ hX, cmDPlus_dminusCM_sub_dminusCM_cmDPlus q m hF, braid_scal_mul,
    braid_one_cmAscWord_auxVar_mul_cmDPlus, cmDPlus_scal_mul]
  ring

end Newton

end HJO.Sweep
