/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.Shuffle.SweepTruncate
public import HJO.Shuffle.CMRaising

/-! # The width shift of an extension is not a conjugation: what the trains can and cannot do

`HJO.Mellit.sweepAppend_of_forall_path` reduces `HJO.Mellit.SweepAppend` to one identity per base
path, and `HJO.Paths.sweepWidth_appendHeights_eq` says what appending a part does to the sweep at a
point of the base: it raises the width by `δ = #(tailLiveSteps w (diagExcess a b P))`. At a type-`D`
event that is a scalar `q^δ` (`HJO.Mellit.sweepOperator_appendHeights_of_eventType_D`); at types
`A`, `B` and `C` the operator is `d_+`, `d_-` or `Δ` read at the *shifted* width. The question this
file answers is whether the two trains and the replicated letter of `HJO.Mellit.replicatedLetter`
inside `HJO.Mellit.stageTotal` can absorb that shift.

## They cannot, and the reason is the grading

Every factor of `HJO.Mellit.stageTotal` except one preserves the graded piece it is read on:

* the trains `T_{k+1↘1}` and `T_{1↗k+1}` — `HJO.Sweep.trainDownEnd_mem_piece`,
  `HJO.Sweep.trainUpEnd_mem_piece`;
* the replicated letter `z_1` — `HJO.Sweep.zopOneStar_mem_piece`;
* the slope operator `Ξ_{a,b}` — `HJO.Sweep.slopeOperator_mem_piece`, proved here: its letters are
  `-y_1·` and `(qu)^{-1}z_1`, and both preserve `V_k`;
* multiplication by `y_1`.

So `HJO.Mellit.replTwoTotal` and `HJO.Mellit.replicatedTotal` are endomorphisms of `V_{k+1}`
(`HJO.Mellit.replTwoTotal_mem_piece`, `HJO.Mellit.replicatedTotal_mem_piece`), and the *only*
index-raising factor in the whole stage is the single `d^*_+` inside
`HJO.Mellit.replOneTotal` — which raises by exactly one. Hence
`HJO.Mellit.stageTotal_mem_piece`: the stage carries `V_k` into `V_{k+1}` and nothing else.

Since `HJO.Sweep.sweepWidth` *is* the graded index the partial sweep word has reached
(`HJO.Mellit.sweepOperator_mem_piece`, `HJO.Mellit.nextWidth`), a relation absorbing the shift
termwise would have to read `d_+` at index `k + δ` as `X d_+^{(k)} Y` with `X` and `Y` built from
those grading-preserving factors. That is impossible, and not for want of a scalar:
`HJO.Sweep.dplus_apply_powerSum_not_mem_piece` exhibits `F ∈ V_0` with
`d_+^{(1)}F ∉ V_1`, so `d_+` at a shifted index is not even a map `V_k → V_{k+1}`, while
`X d_+^{(k)} Y` always is (`HJO.Sweep.dplus_ne_conj_of_mapsTo_piece`). The witness is
`F = p_1`: the substitution `τ_{2,2}` puts the *new* letter `y_2` into the coefficient, the divided
difference of `y_2^2` leaves a residue `y_1y_2`, and that residue is what no conjugation can
remove. It vanishes only at `q = 1`, where the sweep has no corner operator anyway.

**All three of the event types that read the width resist, and each has its own witness.** Type `A`
is `d_+` above. At type `B`, `d_-^{(2)}(y_1) = y_1` (`HJO.Sweep.dminus_two_X_zero`) is not in `V_0`
although `d_-^{(1)}` lands there, so `HJO.Sweep.dminus_ne_conj_of_mapsTo_piece`. At type `C`,
`Δ^{(1)}(1) = -y_1` (`HJO.Sweep.corner_one_one`) is not in `V_0` although `Δ^{(0)}` is an
endomorphism of it, so `HJO.Sweep.corner_ne_conj_of_mapsTo_piece`. Type `D` is the only one that
*is* a scalar and the only one already settled. The vacuum is no witness for any of this —
`d_+^{(1)}(1) = -qy_1 = q·d_+^{(0)}(1)` (`HJO.Sweep.dplus_one_one`,
`HJO.Sweep.dplus_zero_one`), so on `1` the shifted index does cost only a power of `q`, which is
exactly the trap: the identity has to hold on the whole of `V_k`, and it fails one coefficient up.

## What the trains do supply, for the record

At a *fixed* width the train layer is now complete, and none of it moves the width:

* `HJO.Sweep.dplus_braid` — `d_+(T_iF) = T_{i+1}(d_+F)`: the braid index shifts, the width does not.
* `HJO.Sweep.braid_dplusIter`, `T_i d_+^j(1) = d_+^j(1)`.
* `HJO.Braid.trainUp_mul_trainUp`, `HJO.Braid.trainUp_eq_trainUp_one_mul`,
  `HJO.Braid.trainDown_mul_trainDown_self` — peeling, gluing and cancelling words of `T_i`.

All of these are identities between operators read at one and the same index. The width index of
`HJO.Sweep.dplus` is carried twice — by the train `T_{1↗k+1}` *and* by the letter `y_{k+1}` that
`τ_{k+1,k+1}` adds — and the train relations say nothing about the second. The index-raising device
in this theory is `y_1d^*_+`, `HJO.Sweep.braidRep_phiPlusStar_comp_negYOneDPlusStarPiece`
(`d^*_+y_i = y_{i+1}d^*_+` and `T_{i+1}y_1d^*_+ = y_1d^*_+T_i`), and it raises by exactly one,
whereas `δ` ranges over the whole band `1 ≤ rk P ≤ a·bA` and is not constant on a fibre
(`HJO.Paths.card_liveSteps_high_appendHeights_ne`).

## Where that leaves `SweepAppend`

Not with a missing lemma about `d_+` at two indices, but with the interleaving. The sweep word is
ordered by increasing rank and the product applies its rightmost factor first
(`HJO.Mellit.partialSweepWord`), so the tail's own events — all of diagonal excess at most `a·bA` —
are applied *last*, on the same side as the stage, while the base's events of small excess are
interleaved with them. The extension's word is therefore not the base's word with shifted indices;
it is a shuffle, in which the tail's events raise the grading and lower it again, and the sum over
tails is what reassembles the stage. That is Mellit's Section 6 geometry, and it is what
`HJO.Braid.IsAppendSetup.specialBraid_eq_appendRhs` does inside the braid monoid, before any
representation is applied.

The last section of this file cuts that shuffle down to size. The sweep word factors at any
threshold of diagonal excess (`HJO.Mellit.partialSweepWord_eq_bandSweepWord_mul`), because the rank
order on the strip is lexicographic in `(ay - bx, x)`; and at the threshold `a·bA` the outer factor
of the extension is the base's own, tail and all
(`HJO.Mellit.outerSweepWord_appendHeights`). So `HJO.Mellit.sweepAppend_of_forall_band`:
`HJO.Mellit.SweepAppend` is one identity per base path *inside the band*
`1 ≤ ay - bx ≤ a·bA`, whose height depends on the appended part alone, read on the one vector the
outer word produces.
-/

@[expose] public section

open Finset

namespace HJO.Sweep

/-! ### The slope operator preserves the grading -/

section Slope

variable {L : Type*} [Field L] [Algebra ℚ L]

/-- **`Ξ_{m,n}` is an endomorphism of `V_k` for `k ≥ 1`.** Its letters are multiplication by `-y_1`
and `(qu)^{-1}z_1` (`HJO.Sweep.slopeOperator`), and each preserves `V_k`: the first because
`y_1 ∈ V_k`, the second by `HJO.Sweep.zopOneStar_mem_piece`. So the whole word does. -/
theorem slopeOperator_mem_piece (q u : L) {k m n : ℕ} (hk : 1 ≤ k) {F : Total L}
    (hF : F ∈ piece L k) : slopeOperator q u k m n F ∈ piece L k := by
  rw [slopeOperator]
  refine listProd_mem_piece (fun f hf G hG => ?_) hF
  obtain ⟨l, -, rfl⟩ := List.mem_map.1 hf
  cases l with
  | y =>
      change (-LinearMap.mulLeft L (auxVar 1 : Total L)) G ∈ piece L k
      rw [LinearMap.neg_apply, LinearMap.mulLeft_apply]
      exact neg_mem (mul_mem (auxVar_mem_piece (by omega) hk) hG)
  | z =>
      change ((q * u)⁻¹ • zop q u k 1) G ∈ piece L k
      rw [LinearMap.smul_apply, zop_one]
      exact smul_mem_piece (zopOneStar_mem_piece q u hk hG)

end Slope

/-! ### `d_+` at a shifted index is not a map `V_k → V_{k+1}`

The whole of the obstruction is one residue, visible at the smallest index. `d_+^{(1)}` is read on
`V_1` and the witness is a coefficient of `V_0`; the same computation one variable higher is the
same statement at every index. -/

section Shift

variable {L : Type*} [Field L]

/-- `∂_1(y_2) = 1`. -/
theorem dividedDiff_one_X_one : dividedDiff 1 (MvPolynomial.X 1 : Total L) = 1 := by
  refine (dividedDiff_unique (by omega) ?_).symm
  rw [mul_one, swapAux_X]
  simp [Equiv.swap_apply_right]

/-- `∂_1(y_2^2) = y_1 + y_2`. -/
theorem dividedDiff_one_X_one_sq : dividedDiff 1 ((MvPolynomial.X 1 : Total L) ^ 2)
    = MvPolynomial.X 0 + MvPolynomial.X 1 := by
  refine (dividedDiff_unique (by omega) ?_).symm
  rw [map_pow, swapAux_X]
  simp [Equiv.swap_apply_right]
  ring

/-- `1 + (q - 1) = q`, on the scalars of the total space. -/
theorem scal_one_add_scal_sub_one (q : L) : (scal 1 : Total L) + scal (q - 1) = scal q := by
  rw [← scal_add]
  norm_num

/-- **`T_1(y_2) = qy_1`.** The transposition sends `y_2` to `y_1` and the divided difference
contributes `(q-1)y_1`. -/
theorem braid_one_X_one (q : L) :
    braid q 1 (MvPolynomial.X 1 : Total L) = scal q * MvPolynomial.X 0 := by
  rw [braid_apply, dividedDiff_one_X_one, swapAux_X, mul_one, Equiv.swap_apply_right]
  have h : (auxVar 1 : Total L) = MvPolynomial.X 0 := rfl
  rw [h, show ((1 : ℕ) - 1) = 0 from rfl, ← scal_one_add_scal_sub_one q, scal_one]
  ring

/-- **`T_1(y_2^2) = qy_1^2 + (q-1)y_1y_2`.** The second term is the residue the divided difference
leaves in the *new* variable, and it is the whole obstruction to shifting the width of `d_+`. -/
theorem braid_one_X_one_sq (q : L) : braid q 1 ((MvPolynomial.X 1 : Total L) ^ 2)
    = scal q * MvPolynomial.X 0 ^ 2 + scal (q - 1) * (MvPolynomial.X 0 * MvPolynomial.X 1) := by
  rw [braid_apply, dividedDiff_one_X_one_sq, map_pow, swapAux_X, Equiv.swap_apply_right]
  have h : (auxVar 1 : Total L) = MvPolynomial.X 0 := rfl
  rw [h, show ((1 : ℕ) - 1) = 0 from rfl, ← scal_one_add_scal_sub_one q, scal_one]
  ring

/-- `T_i` is `Λ`-linear, so a coefficient passes through it. -/
theorem braid_C_mul (q : L) (i : ℕ) (c : Sym.Lambda L) (F : Total L) :
    braid q i (MvPolynomial.C c * F) = MvPolynomial.C c * braid q i F := by
  rw [← MvPolynomial.smul_eq_C_mul, map_smul, MvPolynomial.smul_eq_C_mul]

/-- The one-letter ascending train. -/
theorem trainUpEnd_one_two (q : L) : trainUpEnd q 1 2 = braidEnd q 1 := by
  rw [trainUpEnd_eq_ascendingWord q (by omega), Braid.ascendingWord_succ_self]

/-- `τ_{2,2}(p_1) = p_1 + (q-1)y_2`: the substitution puts the new letter into the coefficient. -/
theorem qshift_two_powerSum (q : L) : qshift q 2 (MvPolynomial.C (Sym.powerSum L 1) : Total L)
    = MvPolynomial.C (Sym.powerSum L 1) + scal (q - 1) * MvPolynomial.X 1 := by
  have h := qshift_powerSum q 2 0
  norm_num at h
  rw [h]
  norm_num [auxVar]

/-- **`d_+^{(1)}(p_1)`, computed.** The last term, `(q-1)^2y_1y_2`, uses the variable `y_2`, which
`V_1` does not have. -/
theorem dplus_one_apply_powerSum [Algebra ℚ L] (q : L) :
    dplus q 1 (MvPolynomial.C (Sym.powerSum L 1) : Total L)
      = -(scal q * (MvPolynomial.C (Sym.powerSum L 1) * MvPolynomial.X 0)
          + scal (q * (q - 1)) * MvPolynomial.X 0 ^ 2
          + scal ((q - 1) ^ 2) * (MvPolynomial.X 0 * MvPolynomial.X 1)) := by
  rw [dplus_apply, trainUpEnd_one_two]
  have hbe : ∀ G : Total L, braidEnd q 1 G = braid q 1 G := fun _ => rfl
  rw [hbe, qshift_two_powerSum]
  have hav : (auxVar 2 : Total L) = MvPolynomial.X 1 := by norm_num [auxVar]
  rw [hav, mul_add, map_add,
    mul_comm ((MvPolynomial.X 1 : Total L)) (MvPolynomial.C (Sym.powerSum L 1)), braid_C_mul,
    braid_one_X_one]
  have e2 : (MvPolynomial.X 1 : Total L) * (scal (q - 1) * MvPolynomial.X 1)
      = scal (q - 1) * MvPolynomial.X 1 ^ 2 := by ring
  rw [e2, braid_scal_mul, braid_one_X_one_sq]
  have h1 : (scal (q * (q - 1)) : Total L) = scal q * scal (q - 1) := by rw [scal_mul]
  have h2 : (scal ((q - 1) ^ 2) : Total L) = scal (q - 1) * scal (q - 1) := by rw [sq, scal_mul]
  rw [h1, h2]
  ring

/-- `cy_1y_2` written as a monomial, the shape in which its variables are read off. -/
theorem scal_mul_X_zero_mul_X_one (c : L) :
    (scal c * (MvPolynomial.X 0 * MvPolynomial.X 1) : Total L)
      = MvPolynomial.monomial (Finsupp.single 0 1 + Finsupp.single 1 1) (MvPolynomial.C c) := by
  rw [MvPolynomial.monomial_single_add, MvPolynomial.monomial_eq]
  simp [scal, Finsupp.prod_single_index]
  ring

/-- **`cy_1y_2 ∉ V_1` for `c ≠ 0`.** `V_1` is the elements using only `y_1`. -/
theorem scal_mul_X_zero_mul_X_one_not_mem_piece {c : L} (hc : c ≠ 0) :
    (scal c * (MvPolynomial.X 0 * MvPolynomial.X 1) : Total L) ∉ piece L 1 := by
  intro h
  rw [piece, MvPolynomial.mem_supported, scal_mul_X_zero_mul_X_one,
    MvPolynomial.vars_monomial (by simpa using hc)] at h
  have h1 : (1 : ℕ) ∈ (Finsupp.single 0 1 + Finsupp.single 1 1 : ℕ →₀ ℕ).support := by
    simp [Finsupp.mem_support_iff]
  have := h (by exact_mod_cast h1)
  simp at this

/-- **`d_+` at a shifted index does not respect the grading.** `p_1 ∈ V_0`, but `d_+^{(1)}(p_1)`
uses `y_2` and so does not lie in `V_1`, for every `q ≠ 1`.

This is the exact obstruction to absorbing the width shift of an extension. `d_+^{(0)}` carries
`V_0` into `V_1` (`HJO.Sweep.dplus_mem_piece`) and so does `X d_+^{(0)} Y` for any `X`, `Y` that
preserve the pieces — which every factor of `HJO.Mellit.stageTotal` but one does. So no such
conjugation is `d_+^{(1)}`, and the discrepancy is not a scalar: it is the residue `(q-1)^2y_1y_2`
of `HJO.Sweep.dplus_one_apply_powerSum`, which the trains cannot see because they never touch the
letter that `τ_{k+1,k+1}` adds. -/
theorem dplus_apply_powerSum_not_mem_piece [Algebra ℚ L] {q : L} (hq : q ≠ 1) :
    dplus q 1 (MvPolynomial.C (Sym.powerSum L 1) : Total L) ∉ piece L 1 := by
  intro h
  have hmem : (scal ((q - 1) ^ 2) * (MvPolynomial.X 0 * MvPolynomial.X 1) : Total L)
      ∈ piece L 1 := by
    have hneg : -(dplus q 1 (MvPolynomial.C (Sym.powerSum L 1) : Total L)) ∈ piece L 1 :=
      neg_mem h
    rw [dplus_one_apply_powerSum, neg_neg] at hneg
    have h1 : (scal q * (MvPolynomial.C (Sym.powerSum L 1) * MvPolynomial.X 0) : Total L)
        ∈ piece L 1 := by
      refine mul_mem (scal_mem_piece q 1) (mul_mem ?_ ?_)
      · rw [MvPolynomial.C_eq_algebraMap]
        exact (piece L 1).algebraMap_mem _
      · exact auxVar_mem_piece (i := 1) (by omega) (by omega)
    have h2 : (scal (q * (q - 1)) * MvPolynomial.X 0 ^ 2 : Total L) ∈ piece L 1 :=
      mul_mem (scal_mem_piece _ 1) (pow_mem (auxVar_mem_piece (i := 1) (by omega) (by omega)) 2)
    have heq : (scal ((q - 1) ^ 2) * (MvPolynomial.X 0 * MvPolynomial.X 1) : Total L)
        = scal q * (MvPolynomial.C (Sym.powerSum L 1) * MvPolynomial.X 0)
              + scal (q * (q - 1)) * MvPolynomial.X 0 ^ 2
              + scal ((q - 1) ^ 2) * (MvPolynomial.X 0 * MvPolynomial.X 1)
            - scal q * (MvPolynomial.C (Sym.powerSum L 1) * MvPolynomial.X 0)
            - scal (q * (q - 1)) * MvPolynomial.X 0 ^ 2 := by ring
    rw [heq]
    exact sub_mem (sub_mem hneg h1) h2
  exact scal_mul_X_zero_mul_X_one_not_mem_piece (pow_ne_zero 2 (sub_ne_zero.2 hq)) hmem

/-- **No conjugation by grading-preserving operators shifts the width of `d_+`.** If `Y` is an
endomorphism of `V_0` and `X` one of `V_1` — which every train, every `z_1`, every `Ξ_{m,n}` and
multiplication by `y_1` is, by `HJO.Sweep.trainUpEnd_mem_piece`,
`HJO.Sweep.trainDownEnd_mem_piece`, `HJO.Sweep.zopOneStar_mem_piece` and
`HJO.Sweep.slopeOperator_mem_piece` — then `Xd_+^{(0)}Y` is a map `V_0 → V_1` and `d_+^{(1)}` is
not, so they are different operators.

The statement is at the smallest index because that is where the witness is smallest; the
computation at index `k` is the same one, one variable higher. -/
theorem dplus_ne_conj_of_mapsTo_piece [Algebra ℚ L] {q : L} (hq : q ≠ 1)
    {X Y : Module.End L (Total L)} (hX : ∀ F ∈ piece L 1, X F ∈ piece L 1)
    (hY : ∀ F ∈ piece L 0, Y F ∈ piece L 0) : X * dplus q 0 * Y ≠ dplus q 1 := by
  intro h
  refine dplus_apply_powerSum_not_mem_piece hq ?_
  have h0 : (MvPolynomial.C (Sym.powerSum L 1) : Total L) ∈ piece L 0 := by
    rw [MvPolynomial.C_eq_algebraMap]
    exact (piece L 0).algebraMap_mem _
  have := hX _ (dplus_mem_piece q 0 (hY _ h0))
  rw [← Module.End.mul_apply, ← Module.End.mul_apply, h] at this
  exact this

end Shift

/-! ### The same obstruction at types `B` and `C`

`d_-` and `Δ` are read at the width too, so the verdict has to cover them. Both do, with smaller
witnesses than `d_+`'s: `y_1 ∈ V_1` but `d_-^{(2)}(y_1) = y_1 ∉ V_0`, and `1 ∈ V_0` but
`Δ^{(1)}(1) = -y_1 ∉ V_0`. -/

section ShiftOthers

variable {L : Type*} [Field L] [Algebra ℚ L]

omit [Algebra ℚ L] in
/-- `y_1 ∉ V_0`: the graded piece `V_0` is the coefficients alone. -/
theorem X_zero_not_mem_piece_zero : (MvPolynomial.X 0 : Total L) ∉ piece L 0 := by
  intro h
  rw [piece, MvPolynomial.mem_supported, MvPolynomial.vars_X] at h
  have h0 : (0 : ℕ) ∈ (↑({0} : Finset ℕ) : Set ℕ) := by simp
  have := h h0
  simp at this

/-- `e_0 = 1`. -/
theorem elemSymm_zero_eq_one : (Sym.elemSymm L 0) = 1 := by rw [Sym.elemSymm]

/-- The coefficient extraction of `d_-` at index `1` fixes `y_1`: the monomial has no `y_2` in it,
so the exponent it deletes is `0` and the symmetric function it multiplies by is `e_0 = 1`. -/
theorem lowerCoeff_one_X_zero :
    lowerCoeff L 1 (MvPolynomial.X 0 : Total L) = MvPolynomial.X 0 := by
  have hX : (MvPolynomial.X 0 : Total L)
      = MvPolynomial.monomial (Finsupp.single 0 1) (1 : Sym.Lambda L) := by
    rw [← MvPolynomial.X_pow_eq_monomial, pow_one]
  rw [hX, lowerCoeff_monomial]
  have h1 : (Finsupp.single 0 1 : ℕ →₀ ℕ) 1 = 0 := by simp
  have h2 : Finsupp.erase 1 (Finsupp.single 0 1 : ℕ →₀ ℕ) = Finsupp.single 0 1 := by simp
  rw [h1, h2, elemSymm_zero_eq_one]
  simp

/-- The coefficient extraction of `d_-` at index `0` fixes `1`. -/
theorem lowerCoeff_zero_one : lowerCoeff L 0 (1 : Total L) = 1 := by
  have hX : (1 : Total L) = MvPolynomial.monomial (0 : ℕ →₀ ℕ) (1 : Sym.Lambda L) := by simp
  rw [hX, lowerCoeff_monomial]
  simp [elemSymm_zero_eq_one]

/-- **`d_-^{(2)}(y_1) = y_1`.** `τ^-_{2,2}` fixes the auxiliary variables and the extraction at
index `1` does not see `y_1`. -/
theorem dminus_two_X_zero (q : L) :
    dminus q 2 (MvPolynomial.X 0 : Total L) = MvPolynomial.X 0 := by
  rw [dminus_apply, qshiftNeg_auxVar]
  exact lowerCoeff_one_X_zero

/-- **`d_-^{(1)}(1) = 1`.** -/
theorem dminus_one_one (q : L) : dminus q 1 (1 : Total L) = 1 := by
  rw [dminus_apply, map_one]
  exact lowerCoeff_zero_one

omit [Algebra ℚ L] in
/-- **`d_+^{(0)}(1) = -y_1`.** The train is empty at index `0`. -/
theorem dplus_zero_one (q : L) : dplus q 0 (1 : Total L) = -MvPolynomial.X 0 := by
  rw [dplus_apply, map_one, mul_one, show (0 : ℕ) + 1 = 1 from rfl, trainUpEnd,
    Braid.trainUp_self]
  have h : (auxVar 1 : Total L) = MvPolynomial.X 0 := rfl
  rw [h]
  rfl

omit [Algebra ℚ L] in
/-- **`d_+^{(1)}(1) = -qy_1`.** On the vacuum the shifted index costs only the scalar `q` — which is
why the vacuum is no witness for the obstruction, and why the witness of
`HJO.Sweep.dplus_apply_powerSum_not_mem_piece` has to carry a coefficient. -/
theorem dplus_one_one (q : L) :
    dplus q 1 (1 : Total L) = -(scal q * MvPolynomial.X 0) := by
  rw [dplus_apply, map_one, mul_one, trainUpEnd_one_two]
  have hbe : ∀ G : Total L, braidEnd q 1 G = braid q 1 G := fun _ => rfl
  have hav : (auxVar 2 : Total L) = MvPolynomial.X 1 := by norm_num [auxVar]
  rw [hbe, hav, braid_one_X_one]

omit [Algebra ℚ L] in
/-- `x • F = (scal x)F`. -/
theorem smul_eq_scal_mul (x : L) (F : Total L) : x • F = scal x * F := by
  rw [scal_eq_algebraMap, Algebra.smul_def]

/-- **`Δ^{(1)}(1) = -y_1`.** The two composites of `HJO.Sweep.corner` give `-qy_1` and `-y_1`, whose
difference divided by `q - 1` is `-y_1`. So `Δ` read one index too high takes `V_0` outside
`V_0`. -/
theorem corner_one_one {q : L} (hq : q ≠ 1) :
    corner q 1 (1 : Total L) = -MvPolynomial.X 0 := by
  have hq' : q - 1 ≠ 0 := sub_ne_zero.2 hq
  have h2 : dminus q (1 + 1) (-(scal q * MvPolynomial.X 0) : Total L)
      = -(scal q * MvPolynomial.X 0) := by
    rw [show (1 + 1 : ℕ) = 2 from rfl, ← smul_eq_scal_mul, ← smul_neg, map_smul, map_neg,
      dminus_two_X_zero]
  have hsub : (-(scal q * MvPolynomial.X 0) - -(MvPolynomial.X 0) : Total L)
      = (1 - q) • (MvPolynomial.X 0 : Total L) := by
    rw [← smul_eq_scal_mul]
    module
  have hscal : (q - 1)⁻¹ * (1 - q) = -1 := by
    field_simp
    ring
  rw [corner_of_pos q one_ne_zero, LinearMap.smul_apply, LinearMap.sub_apply,
    Module.End.mul_apply, Module.End.mul_apply, dplus_one_one, h2,
    show (1 : ℕ) - 1 = 0 from rfl, dminus_one_one, dplus_zero_one, hsub, smul_smul, hscal,
    neg_one_smul]

/-- **No conjugation by grading-preserving operators shifts the width of `d_-` either.** `d_-^{(1)}`
carries `V_1` into `V_0` (`HJO.Sweep.dminus_mem_piece`), so `Xd_-^{(1)}Y` does whenever `Y` is an
endomorphism of `V_1` and `X` one of `V_0`; `d_-^{(2)}` does not, by
`HJO.Sweep.dminus_two_X_zero`. -/
theorem dminus_ne_conj_of_mapsTo_piece (q : L) {X Y : Module.End L (Total L)}
    (hX : ∀ F ∈ piece L 0, X F ∈ piece L 0) (hY : ∀ F ∈ piece L 1, Y F ∈ piece L 1) :
    X * dminus q 1 * Y ≠ dminus q 2 := by
  intro h
  refine X_zero_not_mem_piece_zero (L := L) ?_
  have h1 : (MvPolynomial.X 0 : Total L) ∈ piece L 1 :=
    auxVar_mem_piece (i := 1) (by omega) (by omega)
  have h2 : dminus q 1 (Y (MvPolynomial.X 0 : Total L)) ∈ piece L 0 := by
    simpa using dminus_mem_piece q 1 (hY _ h1)
  have := hX _ h2
  rw [← Module.End.mul_apply, ← Module.End.mul_apply, h, dminus_two_X_zero] at this
  exact this

/-- **No conjugation by grading-preserving operators shifts the width of `Δ` either.** `Δ^{(0)}` is
an endomorphism of `V_0` (`HJO.Sweep.corner_mem_piece`) and so is any `XΔ^{(0)}Y` with `X`, `Y`
endomorphisms of `V_0`; `Δ^{(1)}` is not, by `HJO.Sweep.corner_one_one`.

With `HJO.Sweep.dplus_ne_conj_of_mapsTo_piece` and
`HJO.Sweep.dminus_ne_conj_of_mapsTo_piece` this closes the question for all three of the event
types that read `HJO.Paths.sweepWidth`: none of `d_+`, `d_-`, `Δ` at a shifted width is a conjugate
of itself at the original width by operators that preserve the grading — and every factor of
`HJO.Mellit.stageTotal` except its single `d^*_+` preserves the grading. -/
theorem corner_ne_conj_of_mapsTo_piece {q : L} (hq : q ≠ 1) {X Y : Module.End L (Total L)}
    (hX : ∀ F ∈ piece L 0, X F ∈ piece L 0) (hY : ∀ F ∈ piece L 0, Y F ∈ piece L 0) :
    X * corner q 0 * Y ≠ corner q 1 := by
  intro h
  refine X_zero_not_mem_piece_zero (L := L) ?_
  have h1 : (1 : Total L) ∈ piece L 0 := one_mem _
  have := hX _ (corner_mem_piece q 0 (hY _ h1))
  rw [← Module.End.mul_apply, ← Module.End.mul_apply, h, corner_one_one hq] at this
  exact neg_mem_iff.1 this

end ShiftOthers

end HJO.Sweep

namespace HJO.Mellit

open Sweep

/-! ### The stage raises the grading by exactly one

`HJO.Mellit.stage` says `G_{k+1,A} : V_k → V_{k+1}`. Read on `HJO.Mellit.stageTotal` that is a
factorwise statement, and the point of making it one is *which* factor does the raising: only the
single `d^*_+` inside `HJO.Mellit.replOneTotal`. -/

section Stage

variable {L : Type*} [Field L] [Algebra ℚ L]

/-- **`Ω(1;a,b)` carries `V_k` into `V_{k+1}`.** The `d^*_+` raises the index by one
(`HJO.Sweep.dplusStar_mem_piece`); the multiplication by `y_1` and the slope operator then stay in
`V_{k+1}`. This is the only factor of the stage that changes the grading. -/
theorem replOneTotal_mem_piece (q u : L) (a b k : ℕ) {F : Total L} (hF : F ∈ piece L k) :
    replOneTotal q u a b k F ∈ piece L (k + 1) := by
  rw [replOneTotal, LinearMap.smul_apply, Module.End.mul_apply, LinearMap.neg_apply,
    Module.End.mul_apply, LinearMap.mulLeft_apply]
  refine smul_mem_piece (slopeOperator_mem_piece q u (by omega) (neg_mem (mul_mem ?_ ?_)))
  · exact auxVar_mem_piece (by omega) (by omega)
  · exact dplusStar_mem_piece q u hF

/-- **`Ω(2;a,b)` is an endomorphism of `V_{k+1}`.** `z_1` preserves the grading
(`HJO.Sweep.zopOneStar_mem_piece`), and so do the other two factors. -/
theorem replTwoTotal_mem_piece (q u : L) (a b k : ℕ) {F : Total L} (hF : F ∈ piece L (k + 1)) :
    replTwoTotal q u a b k F ∈ piece L (k + 1) := by
  rw [replTwoTotal, LinearMap.smul_apply, Module.End.mul_apply, LinearMap.neg_apply,
    Module.End.mul_apply, LinearMap.mulLeft_apply]
  refine smul_mem_piece (slopeOperator_mem_piece q u (by omega) (neg_mem (mul_mem ?_ ?_)))
  · exact auxVar_mem_piece (by omega) (by omega)
  · exact zopOneStar_mem_piece q u (by omega) hF

/-- **`Z^{(k+1)}_{a,b}` is an endomorphism of `V_{k+1}`**, the domain and codomain
`HJO.Mellit.replicatedLetter` gives it: the two trains read only letters of index at most `k`, and
`Ω(2;a,b)` between them preserves the grading. So the replicated letter cannot shift the index of
anything it is conjugated with. -/
theorem replicatedTotal_mem_piece (q u : L) (a b k : ℕ) {F : Total L}
    (hF : F ∈ piece L (k + 1)) : replicatedTotal q u a b k F ∈ piece L (k + 1) := by
  rw [replicatedTotal, LinearMap.smul_apply, Module.End.mul_apply, Module.End.mul_apply]
  refine smul_mem_piece (trainDownEnd_mem_piece q (by omega) (by omega) ?_)
  exact replTwoTotal_mem_piece q u a b k (trainUpEnd_mem_piece q (by omega) (by omega) hF)

/-- **Every power of the replicated letter is an endomorphism of `V_{k+1}`.** -/
theorem replicatedTotal_pow_mem_piece (q u : L) (a b k n : ℕ) {F : Total L}
    (hF : F ∈ piece L (k + 1)) : (replicatedTotal q u a b k ^ n) F ∈ piece L (k + 1) := by
  induction n generalizing F with
  | zero => simpa using hF
  | succ n ih =>
      rw [pow_succ, Module.End.mul_apply]
      exact ih (replicatedTotal_mem_piece q u a b k hF)

/-- **The stage carries `V_k` into `V_{k+1}`, and raises the grading by exactly one.** This is
`HJO.Mellit.stage`'s own domain and codomain, and it is the formal content of the negative answer
to whether `HJO.Mellit.stageTotal` can absorb the width shift of an extension: the power of the
replicated letter and the descending train both preserve the grading
(`HJO.Mellit.replicatedTotal_pow_mem_piece`, `HJO.Sweep.trainDownEnd_mem_piece`), so the single
`d^*_+` of `HJO.Mellit.replOneTotal` is the only index-raising device in the word, and it raises by
one however large `A` is. -/
theorem stageTotal_mem_piece (q u : L) (a b k A : ℕ) {F : Total L} (hF : F ∈ piece L k) :
    stageTotal q u a b k A F ∈ piece L (k + 1) := by
  rw [stageTotal, Module.End.mul_apply, Module.End.mul_apply]
  exact replicatedTotal_pow_mem_piece q u a b k _
    (trainDownEnd_mem_piece q (by omega) (by omega) (replOneTotal_mem_piece q u a b k hF))

end Stage

/-! ### Where the correction does live: the band `1 ≤ ay - bx ≤ a·bA`

The verdict above is negative about *absorbing* the shift, and the shape of the positive statement
is fixed by the same two facts. `HJO.Paths.tailLiveSteps_eq_empty_of_nonpos` and
`HJO.Paths.tailLiveSteps_eq_empty_of_gt` confine the whole discrepancy to a band of diagonal excess
whose height `a·bA` depends on the appended part alone, and the rank order on the strip is
lexicographic in `(ay - bx, x)` (`HJO.Mellit.abovePointRank_le_iff`) — so the band is an *initial
segment* of the rank listing, and the sweep word factors accordingly.

`HJO.Mellit.partialSweepWord_eq_bandSweepWord_mul` is that factorisation at an arbitrary threshold
`d` of diagonal excess: the word is the events of excess at most `d` (applied last, standing to the
left) after the events of excess above `d`. At `d = a·bA` the right-hand factor of the extension is
the base's own — same index set (`HJO.Mellit.sweptAbove_high_appendHeights`), same operators
(`HJO.Mellit.highWord_appendHeights`), same listing
(`HJO.Mellit.outerSweepWord_appendHeights`, through
`HJO.Mellit.sortByRank_congr`) — and in particular does not depend on the tail `w`.

`HJO.Mellit.sweepAppend_of_forall_band` is the resulting reduction: `HJO.Mellit.SweepAppend`
follows from one identity per base path *inside the band*, read on the single vector the outer word
produces. The `α = []` corner is separated out because the band factorisation needs `0 < N`, the
same corner `HJO.Paths.sweepWidth_appendHeights` carries. -/

section Band

open ParkingFunctions Paths Sweep

variable {L : Type*} [Field L] [Algebra ℚ L] {q u : L} {a b M : ℕ}

/-- Splitting a swept index set at a threshold of diagonal excess. -/
theorem filter_union_filter_diagExcess (y : Heights a b M) (η : ℚ) (d : ℤ) :
    {P ∈ sweptAbove y η | diagExcess a b P ≤ d} ∪ {P ∈ sweptAbove y η | d < diagExcess a b P}
      = sweptAbove y η := by
  ext P
  simp only [Finset.mem_union, Finset.mem_filter]
  constructor
  · rintro (⟨h, -⟩ | ⟨h, -⟩) <;> exact h
  · intro h
    rcases le_or_gt (diagExcess a b P) d with hd | hd
    · exact Or.inl ⟨h, hd⟩
    · exact Or.inr ⟨h, hd⟩

/-- **The rank listing is split by a threshold of diagonal excess**, the band first. The rank order
on the strip is lexicographic in `(ay - bx, x)` with the excess deciding first
(`HJO.Mellit.abovePointRank_le_iff`), so a threshold in the excess cuts the listing in two. -/
theorem sortByRank_sweptAbove_split_diagExcess (ha : 0 < a) (hM : 0 < M) (y : Heights a b M)
    (η : ℚ) (d : ℤ) :
    sortByRank a b M (sweptAbove y η)
      = sortByRank a b M {P ∈ sweptAbove y η | diagExcess a b P ≤ d}
        ++ sortByRank a b M {P ∈ sweptAbove y η | d < diagExcess a b P} := by
  conv_lhs => rw [← filter_union_filter_diagExcess y η d]
  refine sortByRank_union (y := y) ha ?_ ?_ ?_
  · rw [filter_union_filter_diagExcess y η d]
    exact fun P hP => (Finset.mem_filter.1 hP).1
  · rw [Finset.disjoint_left]
    intro P hP hP'
    have h1 := (Finset.mem_filter.1 hP).2
    have h2 := (Finset.mem_filter.1 hP').2
    omega
  · intro P hP Q hQ
    have hPs : P ∈ sweptAbove y η := (Finset.mem_filter.1 hP).1
    have hQs : Q ∈ sweptAbove y η := (Finset.mem_filter.1 hQ).1
    have hP1 : P.1 ≤ a * M := (mem_sweptRegion.1 (Finset.mem_filter.1 hPs).1).1
    have hQ1 : Q.1 ≤ a * M := (mem_sweptRegion.1 (Finset.mem_filter.1 hQs).1).1
    have hlow := (Finset.mem_filter.1 hP).2
    have hhigh := (Finset.mem_filter.1 hQ).2
    have hkey : ¬ (pointRank a b M Q ≤ pointRank a b M P) := by
      rw [pointRank, pointRank, abovePointRank_le_iff hM hQ1 hP1]
      simp only [diagExcess] at hlow hhigh
      push Not
      refine ⟨by omega, fun h => absurd h (by omega)⟩
    omega

/-- **The events of diagonal excess at most `d`**, in the order the sweep applies them. The factor
of `HJO.Mellit.partialSweepWord` that an appended part can change. -/
noncomputable def bandSweepWord (q u : L) {a b M : ℕ} (y : Heights a b M) (η : ℚ) (d : ℤ) :
    Module.End L (Total L) :=
  ((sortByRank a b M {P ∈ sweptAbove y η | diagExcess a b P ≤ d}).map (sweepOperator q u y)).prod

/-- **The events of diagonal excess above `d`**: the factor of `HJO.Mellit.partialSweepWord` that
is applied first, and that an appended part of size `A` leaves alone once `d = a·bA`. -/
noncomputable def outerSweepWord (q u : L) {a b M : ℕ} (y : Heights a b M) (η : ℚ) (d : ℤ) :
    Module.End L (Total L) :=
  ((sortByRank a b M {P ∈ sweptAbove y η | d < diagExcess a b P}).map (sweepOperator q u y)).prod

/-- **The partial sweep word factors at any threshold of diagonal excess.** The outer word stands to
the right, hence is applied first: the sweep runs inwards, from high excess to the diagonal. -/
theorem partialSweepWord_split_diagExcess (ha : 0 < a) (hM : 0 < M) (y : Heights a b M)
    (η : ℚ) (d : ℤ) :
    partialSweepWord q u y η
      = ((sortByRank a b M {P ∈ sweptAbove y η | diagExcess a b P ≤ d}).map
            (sweepOperator q u y)).prod
        * ((sortByRank a b M {P ∈ sweptAbove y η | d < diagExcess a b P}).map
            (sweepOperator q u y)).prod := by
  rw [partialSweepWord, sortByRank_sweptAbove_split_diagExcess ha hM y η d, List.map_append,
    List.prod_append]

/-- `HJO.Mellit.partialSweepWord` as the band word after the outer word. -/
theorem partialSweepWord_eq_bandSweepWord_mul (ha : 0 < a) (hM : 0 < M) (y : Heights a b M)
    (η : ℚ) (d : ℤ) :
    partialSweepWord q u y η = bandSweepWord q u y η d * outerSweepWord q u y η d :=
  partialSweepWord_split_diagExcess ha hM y η d

/-- **Above the band the extension's index set is the base's.** A point of the extension's swept
region at or beyond the corner column has `y ≤ b(N+A)` and `x ≥ aN`, so its excess is at most
`a·bA`; the points of higher excess are therefore all base points, and there
`HJO.Mellit.sweptAbove_filter_lt_appendHeights` identifies the two index sets. -/
theorem sweptAbove_high_appendHeights {N A : ℕ} {z : Heights a b N} {w : Heights a b A} {η η' : ℚ}
    (hη : SeparatesDiagonal a b (N + A) η) (hη' : SeparatesDiagonal a b N η') :
    {P ∈ sweptAbove (appendHeights z w) η | (a : ℤ) * (b * A) < diagExcess a b P}
      = {P ∈ sweptAbove z η' | (a : ℤ) * (b * A) < diagExcess a b P} := by
  have hset := sweptAbove_filter_lt_appendHeights (z := z) (w := w) hη hη'
  ext P
  simp only [Finset.mem_filter]
  constructor
  · rintro ⟨hP, hd⟩
    refine ⟨?_, hd⟩
    have hlt : P.1 < a * N := by
      by_contra hcon
      have hge : a * N ≤ P.1 := by omega
      have hreg := (mem_sweptRegion.1 (Finset.mem_filter.1 hP).1)
      have hht : P.2 ≤ b * (N + A) := hreg.2.2.trans (ht_le_mul (appendHeights z w) _)
      have h1 : (P.2 : ℤ) ≤ (b : ℤ) * ((N : ℤ) + A) := by exact_mod_cast hht
      have h2 : (a : ℤ) * N ≤ (P.1 : ℤ) := by exact_mod_cast hge
      have ha0 : (0 : ℤ) ≤ (a : ℤ) := Int.natCast_nonneg _
      have hb0 : (0 : ℤ) ≤ (b : ℤ) := Int.natCast_nonneg _
      simp only [diagExcess] at hd
      nlinarith
    have : P ∈ {P ∈ sweptAbove (appendHeights z w) η | P.1 < a * N} :=
      Finset.mem_filter.2 ⟨hP, hlt⟩
    rwa [hset] at this
  · rintro ⟨hP, hd⟩
    refine ⟨?_, hd⟩
    rw [← hset] at hP
    exact (Finset.mem_filter.1 hP).1

/-- **Above the band the extension's word is the base's own operators.** The index sets agree by
`HJO.Mellit.sweptAbove_high_appendHeights` and each operator by
`HJO.Mellit.sweepOperator_appendHeights_of_diagExcess_outside`: outside the band the width
correction is empty, so the two event operators are literally equal. -/
theorem highWord_appendHeights {N A : ℕ} {z : Heights a b N} {w : Heights a b A} {η η' : ℚ}
    (hz : IsAboveDiagonal z) (hw : IsAboveDiagonal w) (hN : 0 < N)
    (hη : SeparatesDiagonal a b (N + A) η) (hη' : SeparatesDiagonal a b N η') :
    ((sortByRank a b (N + A) {P ∈ sweptAbove (appendHeights z w) η |
          (a : ℤ) * (b * A) < diagExcess a b P}).map
        (sweepOperator q u (appendHeights z w))).prod
      = ((sortByRank a b (N + A) {P ∈ sweptAbove z η' |
          (a : ℤ) * (b * A) < diagExcess a b P}).map (sweepOperator q u z)).prod := by
  have hset := sweptAbove_filter_lt_appendHeights (z := z) (w := w) hη hη'
  rw [sweptAbove_high_appendHeights hη hη']
  congr 1
  refine List.map_congr_left fun P hP => ?_
  have hmem := Finset.mem_filter.1 (mem_sortByRank.1 hP)
  have hlt : P.1 < a * N := by
    have : P ∈ {P ∈ sweptAbove (appendHeights z w) η | P.1 < a * N} := by
      rw [hset]; exact hmem.1
    exact (Finset.mem_filter.1 this).2
  exact sweepOperator_appendHeights_of_diagExcess_outside hz hw hN (by omega) (Or.inr hmem.2)

/-- **A list sorted by a key injective on it is determined by its members.** Mathlib's
`List.eq_of_perm_of_sorted` wants a globally antisymmetric relation, and `≤` pulled back along the
rank is antisymmetric only where the rank is injective, so the comparison is made through the key.

`HJO/Shuffle/MellitRem41.lean` carries the same argument as a `private` lemma, where
`HJO.Mellit.sortByRank_union` consumes it. It is stated here because the rectangle-independence of
the listing needs it too and a `private` lemma cannot be reached from another module; when that file
is next edited the private copy should go in favour of this one. -/
theorem list_eq_of_perm_of_pairwise_key {α : Type*} {K : α → ℤ} :
    ∀ {l₁ l₂ : List α}, l₁.Perm l₂ → l₁.Pairwise (fun x z => K x ≤ K z) →
      l₂.Pairwise (fun x z => K x ≤ K z) →
      (∀ x ∈ l₁, ∀ z ∈ l₁, K x = K z → x = z) → l₁ = l₂ := by
  intro l₁
  induction l₁ with
  | nil => exact fun hp _ _ _ => (hp.symm.eq_nil).symm
  | cons x t ih =>
    intro l₂ hp h₁ h₂ hinj
    match l₂ with
    | [] => exact absurd hp.eq_nil (by simp)
    | (w :: s) =>
      have hxw : x = w := by
        by_contra hne
        have hw2 : w ∈ t := by
          rcases List.mem_cons.1 (hp.mem_iff.2 (List.mem_cons_self ..)) with h | h
          · exact absurd h.symm hne
          · exact h
        have hx2 : x ∈ s := by
          rcases List.mem_cons.1 (hp.mem_iff.1 (List.mem_cons_self ..)) with h | h
          · exact absurd h hne
          · exact h
        exact hne (hinj x (List.mem_cons_self ..) w (List.mem_cons_of_mem _ hw2)
          (le_antisymm ((List.pairwise_cons.1 h₁).1 w hw2) ((List.pairwise_cons.1 h₂).1 x hx2)))
      subst hxw
      rw [ih hp.cons_inv (List.pairwise_cons.1 h₁).2 (List.pairwise_cons.1 h₂).2
        fun p hp' q hq' hpq => hinj p (List.mem_cons_of_mem _ hp') q
          (List.mem_cons_of_mem _ hq') hpq]

/-- **The rank listing does not depend on the rectangle it is computed in.** This is
`HJO.Mellit.abovePointRank_le_congr` — on the strip the order is rectangle-free — turned into the
statement about `HJO.Mellit.sortByRank` that comparing the two words of
`HJO.Mellit.SweepAppend` needs: the two sums live in the rectangles `aN × bN` and
`a(N+A) × b(N+A)`, and a set of points lying in both strips is listed in the same order by
both. -/
theorem sortByRank_congr {N : ℕ} (ha : 0 < a) (hN : 0 < N) (hM : 0 < M) {y : Heights a b N}
    {s : Finset (ℕ × ℕ)} (hs : s ⊆ sweptRegion y) (hsM : ∀ P ∈ s, P.1 ≤ a * M) :
    sortByRank a b M s = sortByRank a b N s := by
  have hbound : ∀ P ∈ s, P.1 ≤ a * N := fun P hP => (mem_sweptRegion.1 (hs hP)).1
  refine list_eq_of_perm_of_pairwise_key (K := pointRank a b N)
    ((sortByRank_perm a b M s).trans (sortByRank_perm a b N s).symm) ?_
    (sortByRank_pairwise a b N s) ?_
  · refine List.Pairwise.imp_of_mem (fun {P Q} hP hQ h => ?_) (sortByRank_pairwise a b M s)
    have hPs := mem_sortByRank.1 hP
    have hQs := mem_sortByRank.1 hQ
    rw [pointRank, pointRank, abovePointRank_le_congr hN hM (hbound P hPs) (hbound Q hQs)
      (hsM P hPs) (hsM Q hQs)]
    exact h
  · intro P hP Q hQ h
    exact pointRank_inj_of_mem_sweptRegion ha (hs (mem_sortByRank.1 hP))
      (hs (mem_sortByRank.1 hQ)) h

/-- **The outer word of an extension is the base's own outer word, tail and all.** Everything of
diagonal excess above `a·bA` is untouched by appending a part of size `A`: the same points, the same
operators, and — by `HJO.Mellit.sortByRank_congr` — in the same order, although the two words are
read in different rectangles. In particular it does not depend on the tail `w`, so it comes out of
the sum over tails. -/
theorem outerSweepWord_appendHeights {N A : ℕ} (ha : 0 < a) {z : Heights a b N}
    {w : Heights a b A} {η η' : ℚ} (hz : IsAboveDiagonal z) (hw : IsAboveDiagonal w) (hN : 0 < N)
    (hη : SeparatesDiagonal a b (N + A) η) (hη' : SeparatesDiagonal a b N η') :
    outerSweepWord q u (appendHeights z w) η ((a : ℤ) * (b * A))
      = outerSweepWord q u z η' ((a : ℤ) * (b * A)) := by
  have hsub : {P ∈ sweptAbove z η' | (a : ℤ) * (b * A) < diagExcess a b P} ⊆ sweptRegion z :=
    fun P hP => (Finset.mem_filter.1 (Finset.mem_filter.1 hP).1).1
  have hbound : ∀ P ∈ {P ∈ sweptAbove z η' | (a : ℤ) * (b * A) < diagExcess a b P},
      P.1 ≤ a * (N + A) := by
    intro P hP
    have := (mem_sweptRegion.1 (hsub hP)).1
    have hle : a * N ≤ a * (N + A) := Nat.mul_le_mul_left a (by omega)
    omega
  rw [outerSweepWord, outerSweepWord, highWord_appendHeights hz hw hN hη hη',
    sortByRank_congr (y := z) ha hN (by omega) hsub hbound]

/-- **`HJO.Mellit.SweepAppend` is one identity per base path inside the band.** Sharpening
`HJO.Mellit.sweepAppend_of_forall_path`: the outer word comes out of the sum over tails and off both
sides, leaving an identity about the events of diagonal excess at most `a·bA` — a band whose height
depends on the appended part alone — read on the single vector `G` that the outer word produces from
`1`.

The two hypotheses are the same identity read two ways. `hzero` is the raw per-path identity at the
one composition with `α.sum = 0`, namely `α = []`, which the band factorisation cannot reach because
`HJO.Paths.sweepWidth_appendHeights` needs `0 < N`; in closed form that case is
`HJO.Mellit.dsc_singleton_of_sweepAppend`. `hband` is the band identity everywhere else. -/
theorem sweepAppend_of_forall_band {a b : ℕ} (hab : Nat.Coprime a b) (ha : 0 < a) (hb : 0 < b)
    (hzero : ∀ (α : List ℕ) (A : ℕ), (∀ x ∈ α, 0 < x) → 0 < A → α.sum = 0 →
      ∀ z ∈ aboveReturnPaths a b α.sum α,
        ∑ w ∈ aboveReturnPaths a b A [A],
            partialSweepWord q u (appendHeights z w) (sepLevel a (α.sum + A)) (1 : Total L)
          = ((-1 : L) ^ ((a - 1) * A) * (q * u) ^ (1 - (A : ℤ))) •
              stageTotal q u a b α.length A
                (partialSweepWord q u z (sepLevel a α.sum) (1 : Total L)))
    (hband : ∀ (α : List ℕ) (A : ℕ), (∀ x ∈ α, 0 < x) → 0 < A → 0 < α.sum →
      ∀ z ∈ aboveReturnPaths a b α.sum α,
        ∑ w ∈ aboveReturnPaths a b A [A],
            bandSweepWord q u (appendHeights z w) (sepLevel a (α.sum + A)) ((a : ℤ) * (b * A))
              (outerSweepWord q u z (sepLevel a α.sum) ((a : ℤ) * (b * A)) (1 : Total L))
          = ((-1 : L) ^ ((a - 1) * A) * (q * u) ^ (1 - (A : ℤ))) •
              stageTotal q u a b α.length A
                (bandSweepWord q u z (sepLevel a α.sum) ((a : ℤ) * (b * A))
                  (outerSweepWord q u z (sepLevel a α.sum) ((a : ℤ) * (b * A)) (1 : Total L)))) :
    SweepAppend q u a b := by
  refine sweepAppend_of_forall_path hab ha hb fun α A hpos hA z hz => ?_
  rcases Nat.eq_zero_or_pos α.sum with hs | hs
  · exact hzero α A hpos hA hs z hz
  · have hzd : IsAboveDiagonal z := (mem_aboveReturnPaths_iff.1 hz).1
    have hη : SeparatesDiagonal a b (α.sum + A) (sepLevel a (α.sum + A)) :=
      separatesDiagonal_sepLevel' a b (α.sum + A)
    have hη' : SeparatesDiagonal a b α.sum (sepLevel a α.sum) :=
      separatesDiagonal_sepLevel' a b α.sum
    have hlhs : ∀ w ∈ aboveReturnPaths a b A [A],
        partialSweepWord q u (appendHeights z w) (sepLevel a (α.sum + A)) (1 : Total L)
          = bandSweepWord q u (appendHeights z w) (sepLevel a (α.sum + A)) ((a : ℤ) * (b * A))
              (outerSweepWord q u z (sepLevel a α.sum) ((a : ℤ) * (b * A)) (1 : Total L)) := by
      intro w hw
      have hwd : IsAboveDiagonal w := (mem_aboveReturnPaths_iff.1 hw).1
      rw [partialSweepWord_eq_bandSweepWord_mul ha (show 0 < α.sum + A by omega) _ _
          ((a : ℤ) * (b * A)), Module.End.mul_apply,
        outerSweepWord_appendHeights ha hzd hwd hs hη hη']
    rw [Finset.sum_congr rfl hlhs,
      partialSweepWord_eq_bandSweepWord_mul ha hs z (sepLevel a α.sum) ((a : ℤ) * (b * A)),
      Module.End.mul_apply]
    exact hband α A hpos hA hs z hz

end Band

end HJO.Mellit

end
