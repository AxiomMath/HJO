/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.CMStructure.BraidRepReduce

/-! # `HJO.Sweep.braidRep` does not descend to the total space

`HJO.Sweep.BraidRepResidualTotal` carries one clause, `z_iz_j = z_jz_i`, as an equality in
`Module.End L (Total L)`. **That clause is false**, and so is
`HJO.Sweep.BraidRepRespectsTotal q u r 2`: this file exhibits the witness. The representation of
Mellit's Proposition 5.3, `HJO.Sweep.braidRep`, builds `π_k` on `End(V_k ⊗ 𝕜[q^{1/2}])`, and the
total-space variant of `HJO/Shuffle/BraidRep.lean` strengthens that to the whole of
`V_* = Λ[y_1, y_2, …]`. For the four other clauses the strengthening is harmless — `y_i` acts by
multiplication, and `HJO.Sweep.zop_mul_braidEnd` is an identity of operator words — but for
`z_iz_j = z_jz_i` it is not, and the failure is visible on the first auxiliary variable the graded
piece does not contain.

## The witness

At `k = 2` the train of `HJO.Sweep.zop` is `HJO.Sweep.trainUpEnd q 2 1 = T_1^{-1}`, so
`z_1 = c·[d^*_+, d_-]·T_1^{-1}` with `c = q^2/(1-q)`, and `z_2 = q^{-1}T_1z_1T_1` collapses to
`q^{-1}c·T_1·[d^*_+, d_-]`. Commutation of `z_1` with `z_2` is therefore commutation of
`[d^*_+, d_-]^2` with `T_1`, and on `y_3` the two sides differ:

* `[d^*_+, d_-](y_3) = y_3 - uy_1`, because the two halves of the commutator read `cy` at
  *different* levels — `cy_3` wraps `y_3` to `uy_1` where `cy_2` fixes it. On `V_2` the variable is
  absent and the discrepancy cannot arise; off `V_2` it does.
* `[d^*_+, d_-](y_1) = 0` and `[d^*_+, d_-](y_2) = -(q-1)uy_1`, so `[d^*_+, d_-]^2(y_3)` is
  `y_3 - uy_1` as well.
* `T_1(y_3) = y_3` while `T_1(y_1) = y_2 - (q-1)y_1`, so the two composites disagree.

The difference of the two composites at `y_3` is `q^{-1}c^2u·(y_2 - qy_1)`, nonzero exactly when
`q ≠ 0`, `q ≠ 1` and `u ≠ 0` — all three of which hold over the base `ℚ(q, u)`.

## What this costs, and the typing on `V_k`

`HJO.Sweep.braidRepTotal` is a homomorphism into `Module.End L (Total L)` and takes
`HJO.Sweep.BraidRepRespectsTotal` as an argument;
`HJO.Sweep.braidRepRespectsTotal_two_false` says that argument can never be supplied at rank `2`.
So every statement taking that argument at rank `2` is vacuous —
`HJO.Sweep.braidRepTotal_phiPlusStar_mul_negYOneDPlusStar` in
`HJO/Shuffle/MellitPhiIntertwine.lean` takes `BraidRepRespectsTotal q u r (k+1)` with
`1 ≤ k`, so it is vacuous at `k = 1` through that hypothesis and at `k = 2` through its other
one. Ranks `k ≥ 3` are **not** refuted here: the witness is at `k = 2` only, and the mechanism —
the two halves of `[d^*_+, d_-]` reading `cy` at two levels — says the same discrepancy should
appear at `y_{k+1}` for every `k ≥ 2`, but that is a prediction and not a theorem of this file.
`HJO.Sweep.braidRepRespectsTotal_one` is unaffected: at rank `1` the clause is an element with
itself and `HJO.Sweep.braidRepResidualTotal_one` proves it outright, which is why
`HJO.Sweep.slopeOperator` may still call itself the rank-one case of `HJO.Sweep.braidRep`.

Weakening the clause would not help: `HJO.Sweep.BraidRepRespectsTotal` asks for an equality
of the images of two *words* under `HJO.Sweep.braidRepFreeTotal`, so a clause restricted to
`V_k` would not discharge it. The target of `HJO.Sweep.braidRep` is therefore the one of Mellit's
construction, the endomorphisms of `V_k` (`HJO.Sweep.pieceSub L k`):
`HJO.Sweep.braidRep` and `HJO.Sweep.braidRepFree` in `HJO/Shuffle/BraidRep.lean` are typed
there, `HJO.Sweep.BraidRepResidual` asks the residual clause on `V_k`, and the total-space versions
are kept under the `...Total` names so that the failure above can be stated.
`HJO.Sweep.braidRepFree_eq_of_total` is the one-way bridge: everything proved on the total space
descends, and the converse is what `HJO.Sweep.zop_two_not_comm` denies.

The operators do restrict, which is what makes the clause on `V_k` well posed:
`HJO.Sweep.dplusStar_mem_piece`, `HJO.Sweep.dminus_mem_piece` and
`HJO.Sweep.braid_mem_piece` are the three memberships `zop q u k i` needs for `1 ≤ i ≤ k`, and
`HJO.Sweep.zop_mem_piece` below assembles them.

Transporting `HJO.Dyck.Aq.yElt_comm` across the starred action of
`HJO.Sweep.exists_isDpaAction_star` cannot supply the total-space clause, and the reason is the
reason recorded on `HJO.Sweep.IsDpaOperators`: an action of the Dyck path algebra exists on
`HJO.Sweep.Vstar` and *not* on `HJO.Sweep.Total`, two of the nine defining relations of the Dyck
path algebra being false there. A transport through `Vstar` yields the clause on the summand `V_k`
and nothing beyond it, which is exactly the statement that is true.

**And even the transport to `V_k` is not immediate, because the two sides are in different `d_-`
conventions.** `HJO.Sweep.zop` is built on `HJO.Sweep.starComm`, whose lowering operator is
`HJO.Sweep.dminus` — Mellit's `d^♭_-` of `HJO.Sweep.dminus`, pairing `F_j` with `e_j`. The
starred action sends `d_-` to `HJO.Sweep.dminusPiece`, restricting `HJO.Sweep.dminusCM` —
Carlsson and Mellit's `d_-` of `HJO.Sweep.dminusCM`, pairing `F_j` with `e_{j+1}`, and the operator
`HJO.Sweep.starCommCM` is built from. The two are related by
`HJO.Sweep.dminusCM_eq_neg_dminus_auxVar_mul`, but carrying that through the commutator and the
braid train of `z_1` fails (`HJO.Sweep.mulLeft_auxVar_two_not_comm_trainUpEnd` below), on top of
`HJO.Dyck.Tilde.Atilde.zElt_one_eq_wordDownStar` and `HJO.Dyck.Tilde.Atilde.zElt_succ_eq`, which
are needed to identify `ρ^*(y_i)` with `z_i` at all. The clause on `V_k` is instead
`HJO.Sweep.braidRepResidual_mellit` (`HJO/CMStructure/MellitBraidRep.lean`), proved from an action
of the Dyck path algebra in Mellit's own convention.

## Main results

* `HJO.Sweep.zop_two_not_comm` — `z_1z_2 ≠ z_2z_1` on `Total L` at `k = 2`.
* `HJO.Sweep.zop_mem_piece` — `z_i` carries `V_k` into itself for `1 ≤ i ≤ k`, so the clause is
  well posed on the graded piece.
* `HJO.Sweep.braidRepResidualTotal_two_false` — `¬ BraidRepResidualTotal q u r 2`.
* `HJO.Sweep.braidRepRespectsTotal_two_false` — `¬ BraidRepRespectsTotal q u r 2`, so
  `HJO.Sweep.braidRep` has no rank-`2` instance **on the total space**. The piece-level
  `HJO.Sweep.BraidRepRespects` is a different statement and is not refuted by anything here.

`HJO.Sweep.braidRepRespects_mellit` is not proved by this file; what is shown is that its
total-space form `HJO.Sweep.BraidRepRespectsTotal` fails at rank `2`.

## References

A. Mellit, *Toric braids and `(m, n)`-parking functions*, Proposition 5.3.
-/

@[expose] public section

namespace HJO.Sweep

open MvPolynomial

variable {L : Type*} [Field L] [Algebra ℚ L]

omit [Algebra ℚ L] in
private theorem scal_mul_smul (x : L) (F : Total L) : scal x * F = x • F := by
  rw [scal_eq_algebraMap, Algebra.smul_def]

omit [Algebra ℚ L] in
private theorem push (T : Module.End L (Total L)) (x : L) (F : Total L) :
    T (scal x * F) = scal x * T F := by
  rw [scal_mul_smul, map_smul, scal_mul_smul]

omit [Algebra ℚ L] in
private theorem comb (a b : L) (F : Total L) : scal a * (scal b * F) = scal (a * b) * F := by
  rw [← mul_assoc, ← scal_mul]

omit [Algebra ℚ L] in
private theorem scal_ne_zero {x : L} (hx : x ≠ 0) : (scal x : Total L) ≠ 0 := by
  simp only [scal, ne_eq, MvPolynomial.C_eq_zero]
  exact hx

omit [Algebra ℚ L] in
private theorem coeff_one_X_zero :
    MvPolynomial.coeff (Finsupp.single 1 1) (MvPolynomial.X 0 : Total L) = 0 := by
  rw [MvPolynomial.coeff_X]
  split_ifs with h0
  · exact absurd (congrArg (fun d : ℕ →₀ ℕ => d 0) h0) (by simp)
  · rfl

omit [Algebra ℚ L] in
private theorem coeff_one_X_one :
    MvPolynomial.coeff (Finsupp.single 1 1) (MvPolynomial.X 1 : Total L) = 1 := by
  rw [MvPolynomial.coeff_X]
  split_ifs with h0
  · rfl
  · exact absurd rfl h0

/-! ### The lowering and starred raising operators on a single auxiliary variable -/

/-- **The coefficient extraction of `d_-` fixes a variable it does not read.** -/
theorem lowerCoeff_X_of_ne {i j : ℕ} (h : i ≠ j) :
    lowerCoeff L j (MvPolynomial.X i : Total L) = MvPolynomial.X i := by
  have hm : (MvPolynomial.X i : Total L) = MvPolynomial.monomial (Finsupp.single i 1) 1 :=
    (pow_one _).symm.trans MvPolynomial.X_pow_eq_monomial
  have h0 : (Finsupp.single i 1 : ℕ →₀ ℕ) j = 0 := Finsupp.single_eq_of_ne (Ne.symm h)
  have h1 : Finsupp.erase j (Finsupp.single i 1 : ℕ →₀ ℕ) = Finsupp.single i 1 :=
    Finsupp.erase_single_ne (Ne.symm h)
  rw [hm, lowerCoeff_monomial, h0, h1, Sym.elemSymm_zero]
  simp

/-- **`d_-` at level `k` fixes `y_{i+1}` for `i ≠ k-1`**: `τ^-_{k,k}` fixes the auxiliary variables
and the extraction reads only `y_k`. -/
theorem dminus_X_of_ne (q : L) {k i : ℕ} (h : i ≠ k - 1) :
    dminus q k (MvPolynomial.X i : Total L) = MvPolynomial.X i := by
  rw [dminus_apply, qshiftNeg_auxVar, lowerCoeff_X_of_ne h]

/-- **`d_-(y_k) = -e_1`**, `dminus_auxVar_pow` at exponent `1`. -/
theorem dminus_X_self (q : L) (k : ℕ) :
    dminus q (k + 1) (MvPolynomial.X k : Total L) = -MvPolynomial.C (Sym.elemSymm L 1) := by
  have h := dminus_auxVar_pow (L := L) q k 1
  rw [pow_one, show (auxVar (k + 1) : Total L) = MvPolynomial.X k by
    rw [auxVar, Nat.add_sub_cancel]] at h
  rw [h]
  ring

omit [Algebra ℚ L] in
/-- **`d^*_+` on an auxiliary variable is the cyclic shift alone**, `τ_{k+1,k+1}` fixing it. -/
theorem dplusStar_X_eq_cycleShift (q u : L) (k j : ℕ) :
    dplusStar q u k (MvPolynomial.X j : Total L) = cycleShift u k (MvPolynomial.X j) := by
  rw [dplusStar_apply, qshift_auxVar]

omit [Algebra ℚ L] in
/-- **`cy_{k+1}(y_{k+1}) = uy_1`**, `cycleShift_auxVar_last` on the variables. -/
theorem cycleShift_X_self (u : L) (k : ℕ) :
    cycleShift u k (MvPolynomial.X k : Total L) = scal u * MvPolynomial.X 0 := by
  have h := cycleShift_auxVar_last (L := L) u k
  rw [show (auxVar (k + 1) : Total L) = MvPolynomial.X k by rw [auxVar, Nat.add_sub_cancel],
    show (auxVar 1 : Total L) = MvPolynomial.X 0 by rw [auxVar]] at h
  exact h

/-! ### The starred commutator at level `2` on `y_1`, `y_2`, `y_3`

`d^*_+d_- - d_-d^*_+` read as `V_2 → V_2`, but applied to the whole total space. The third value is
the one that breaks the clause: it is not in `V_2`. -/

private theorem starComm_X_zero (q u : L) :
    dplusStar q u 1 (dminus q 2 (MvPolynomial.X 0 : Total L))
      - dminus q 3 (dplusStar q u 2 (MvPolynomial.X 0 : Total L)) = 0 := by
  rw [dminus_X_of_ne q (by norm_num), dplusStar_X_eq_cycleShift,
    cycleShift_X_of_lt u (by norm_num), dplusStar_X_eq_cycleShift,
    cycleShift_X_of_lt u (by norm_num), dminus_X_of_ne q (by norm_num), sub_self]

private theorem starComm_X_one (q u : L) :
    dplusStar q u 1 (dminus q 2 (MvPolynomial.X 1 : Total L))
      - dminus q 3 (dplusStar q u 2 (MvPolynomial.X 1 : Total L))
      = scal (-((q - 1) * u)) * MvPolynomial.X 0 := by
  have h1 : dminus q 2 (MvPolynomial.X 1 : Total L) = -MvPolynomial.C (Sym.elemSymm L 1) :=
    dminus_X_self q 1
  have hq := qshift_powerSum (L := L) q 2 0
  have h2 : dplusStar q u 1 (MvPolynomial.C (Sym.elemSymm L 1) : Total L)
      = MvPolynomial.C (Sym.powerSum L 1) + scal (q - 1) * (scal u * MvPolynomial.X 0) := by
    rw [Sym.elemSymm_one, dplusStar_apply]
    simp only [zero_add, pow_one] at hq
    rw [hq, map_add, cycleShift_C, map_mul, cycleShift_scal,
      show (auxVar 2 : Total L) = MvPolynomial.X 1 by rw [auxVar], cycleShift_X_self u 1]
  have h3 : dplusStar q u 2 (MvPolynomial.X 1 : Total L) = MvPolynomial.X 2 := by
    rw [dplusStar_X_eq_cycleShift, cycleShift_X_of_lt u (by norm_num)]
  have hs : (scal (-((q - 1) * u)) : Total L) = -(scal (q - 1) * scal u) := by
    rw [← scal_mul, ← scal_neg]
  rw [h1, map_neg, h2, h3, dminus_X_self q 2, Sym.elemSymm_one, hs]
  ring

private theorem starComm_X_two (q u : L) :
    dplusStar q u 1 (dminus q 2 (MvPolynomial.X 2 : Total L))
      - dminus q 3 (dplusStar q u 2 (MvPolynomial.X 2 : Total L))
      = MvPolynomial.X 2 - scal u * MvPolynomial.X 0 := by
  rw [dminus_X_of_ne q (by norm_num), dplusStar_X_eq_cycleShift,
    cycleShift_X_of_gt u (by norm_num), dplusStar_X_eq_cycleShift, cycleShift_X_self u 2, push,
    dminus_X_of_ne q (by norm_num)]

/-! ### `T_1` on `y_1`, `y_2`, `y_3` -/

section BraidValues

variable {L : Type*} [Field L]

private theorem dd_X_zero : dividedDiff 1 (MvPolynomial.X 0 : Total L) = -1 := by
  refine (dividedDiff_unique (by norm_num) ?_).symm
  rw [swapAux_X, show (1 : ℕ) - 1 = 0 from rfl, Equiv.swap_apply_left]
  ring

private theorem dd_X_one : dividedDiff 1 (MvPolynomial.X 1 : Total L) = 1 := by
  refine (dividedDiff_unique (by norm_num) ?_).symm
  rw [swapAux_X, show (1 : ℕ) - 1 = 0 from rfl, Equiv.swap_apply_right]
  ring

private theorem dd_X_two : dividedDiff 1 (MvPolynomial.X 2 : Total L) = 0 := by
  refine (dividedDiff_unique (by norm_num) ?_).symm
  rw [swapAux_X, show (1 : ℕ) - 1 = 0 from rfl,
    Equiv.swap_apply_of_ne_of_ne (by norm_num) (by norm_num)]
  ring

/-- **`T_1(y_1) = y_2 - (q-1)y_1`.** -/
theorem braidEnd_X_zero (q : L) :
    braidEnd q 1 (MvPolynomial.X 0 : Total L)
      = MvPolynomial.X 1 - scal (q - 1) * MvPolynomial.X 0 := by
  rw [show braidEnd q 1 (MvPolynomial.X 0 : Total L) = braid q 1 (MvPolynomial.X 0) from rfl,
    braid_apply, swapAux_X, dd_X_zero,
    show (auxVar 1 : Total L) = MvPolynomial.X 0 by rw [auxVar],
    show (1 : ℕ) - 1 = 0 from rfl, Equiv.swap_apply_left]
  ring

/-- **`T_1(y_2) = qy_1`.** -/
theorem braidEnd_X_one (q : L) :
    braidEnd q 1 (MvPolynomial.X 1 : Total L) = scal q * (MvPolynomial.X 0 : Total L) := by
  have hq : (scal q : Total L) = scal (q - 1) + 1 := by
    rw [← scal_one (L := L), ← scal_add]
    congr 1
    ring
  rw [show braidEnd q 1 (MvPolynomial.X 1 : Total L) = braid q 1 (MvPolynomial.X 1) from rfl,
    braid_apply, swapAux_X, dd_X_one,
    show (auxVar 1 : Total L) = MvPolynomial.X 0 by rw [auxVar], hq,
    show (1 : ℕ) - 1 = 0 from rfl, Equiv.swap_apply_right]
  ring

/-- **`T_1` fixes `y_3`**, being far from it. -/
theorem braidEnd_X_two (q : L) :
    braidEnd q 1 (MvPolynomial.X 2 : Total L) = (MvPolynomial.X 2 : Total L) := by
  rw [show braidEnd q 1 (MvPolynomial.X 2 : Total L) = braid q 1 (MvPolynomial.X 2) from rfl,
    braid_apply, swapAux_X, dd_X_two, show (1 : ℕ) - 1 = 0 from rfl,
    Equiv.swap_apply_of_ne_of_ne (by norm_num) (by norm_num)]
  ring

private theorem braidInv_of_braid (q : L) (i : ℕ) (F : Total L) :
    braidInvEnd q i F = scal q⁻¹ * (braidEnd q i F + scal (q - 1) * F) :=
  braidInv_apply q i F

/-- **`T_1^{-1}(y_1) = q^{-1}y_2`.** -/
theorem braidInvEnd_X_zero (q : L) :
    braidInvEnd q 1 (MvPolynomial.X 0 : Total L) = scal q⁻¹ * MvPolynomial.X 1 := by
  rw [braidInv_of_braid, braidEnd_X_zero]
  ring

/-- **`T_1^{-1}(y_2) = y_1 + q^{-1}(q-1)y_2`.** -/
theorem braidInvEnd_X_one (q : L) (hq : q ≠ 0) :
    braidInvEnd q 1 (MvPolynomial.X 1 : Total L)
      = MvPolynomial.X 0 + scal (q⁻¹ * (q - 1)) * MvPolynomial.X 1 := by
  have h1 : (scal q⁻¹ : Total L) * scal q = 1 := by
    rw [← scal_mul, inv_mul_cancel₀ hq, scal_one]
  rw [braidInv_of_braid, braidEnd_X_one,
    show (scal (q⁻¹ * (q - 1)) : Total L) = scal q⁻¹ * scal (q - 1) by rw [← scal_mul]]
  linear_combination (MvPolynomial.X 0 : Total L) * h1

/-- **`T_1^{-1}` fixes `y_3`.** -/
theorem braidInvEnd_X_two (q : L) (hq : q ≠ 0) :
    braidInvEnd q 1 (MvPolynomial.X 2 : Total L) = (MvPolynomial.X 2 : Total L) := by
  have h1 : (scal q⁻¹ : Total L) * scal q = 1 := by
    rw [← scal_mul, inv_mul_cancel₀ hq, scal_one]
  have hq2 : (scal q : Total L) = scal (q - 1) + 1 := by
    rw [← scal_one (L := L), ← scal_add]
    congr 1
    ring
  rw [braidInv_of_braid, braidEnd_X_two]
  linear_combination (MvPolynomial.X 2 : Total L) * h1
    - (scal q⁻¹ * MvPolynomial.X 2 : Total L) * hq2

/-- **The train of `HJO.Sweep.zop` at `k = 2` is `T_1^{-1}`.** -/
theorem trainUpEnd_two_one (q : L) : trainUpEnd (L := L) q 2 1 = braidInvEnd q 1 := by
  rw [trainUpEnd, Braid.trainUp]
  norm_num [Braid.descendingWord]

end BraidValues

/-! ### `z_1` and `z_2` at `k = 2` -/

private theorem zop_one_apply (q u : L) (F : Total L) :
    zop q u 2 1 F = scal (q ^ 2 / (1 - q))
      * (dplusStar q u 1 (dminus q 2 (braidInvEnd q 1 F))
          - dminus q 3 (dplusStar q u 2 (braidInvEnd q 1 F))) := by
  rw [zop_one, zopOneStar, trainUpEnd_two_one, LinearMap.smul_apply, scal_mul_smul]
  rfl

private theorem zop_two_apply (q u : L) (F : Total L) :
    zop q u 2 2 F = scal q⁻¹ * braidEnd q 1 (zop q u 2 1 (braidEnd q 1 F)) := by
  rw [show (2 : ℕ) = 0 + 2 from rfl, zop_succ, LinearMap.smul_apply, scal_mul_smul]
  rfl

private theorem z1_X_zero (q u : L) :
    zop q u 2 1 (MvPolynomial.X 0 : Total L)
      = scal (q ^ 2 / (1 - q) * (q⁻¹ * -((q - 1) * u))) * MvPolynomial.X 0 := by
  rw [zop_one_apply, braidInvEnd_X_zero]
  simp only [push]
  rw [← mul_sub, starComm_X_one]
  simp only [comb]

private theorem z1_X_one (q u : L) (hq : q ≠ 0) :
    zop q u 2 1 (MvPolynomial.X 1 : Total L)
      = scal (q ^ 2 / (1 - q) * (q⁻¹ * (q - 1) * -((q - 1) * u))) * MvPolynomial.X 0 := by
  rw [zop_one_apply, braidInvEnd_X_one q hq]
  simp only [map_add, push]
  rw [add_sub_add_comm, starComm_X_zero, ← mul_sub, starComm_X_one, zero_add]
  simp only [comb]

private theorem z1_X_two (q u : L) (hq : q ≠ 0) :
    zop q u 2 1 (MvPolynomial.X 2 : Total L)
      = scal (q ^ 2 / (1 - q)) * (MvPolynomial.X 2 - scal u * MvPolynomial.X 0) := by
  rw [zop_one_apply, braidInvEnd_X_two q hq, starComm_X_two]

/-- **`z_1` kills `T_1(y_1)`** at `k = 2`: the two terms carry the same scalar
`-cq^{-1}(q-1)^2u`. This is the cancellation that makes `z_2` kill `y_1`. -/
private theorem z1_braid_X_zero (q u : L) (hq : q ≠ 0) :
    zop q u 2 1 (MvPolynomial.X 1 : Total L)
      - scal (q - 1) * zop q u 2 1 (MvPolynomial.X 0 : Total L) = 0 := by
  rw [z1_X_one q u hq, z1_X_zero, comb,
    show (q - 1) * (q ^ 2 / (1 - q) * (q⁻¹ * -((q - 1) * u)))
      = q ^ 2 / (1 - q) * (q⁻¹ * (q - 1) * -((q - 1) * u)) by ring, sub_self]

private theorem z2_X_zero (q u : L) (hq : q ≠ 0) :
    zop q u 2 2 (MvPolynomial.X 0 : Total L) = 0 := by
  rw [zop_two_apply, braidEnd_X_zero, map_sub, push, z1_braid_X_zero q u hq, map_zero, mul_zero]

private theorem z2_X_two (q u : L) (hq : q ≠ 0) :
    zop q u 2 2 (MvPolynomial.X 2 : Total L)
      = scal q⁻¹ * (scal (q ^ 2 / (1 - q))
          * (MvPolynomial.X 2 - scal u * (MvPolynomial.X 1
              - scal (q - 1) * MvPolynomial.X 0))) := by
  rw [zop_two_apply, braidEnd_X_two, z1_X_two q u hq, push, map_sub, braidEnd_X_two, push,
    braidEnd_X_zero]

/-! ### The two composites at `y_3`, and the refutation -/

private theorem comp_one_two (q u : L) (hq : q ≠ 0) :
    (zop q u 2 1 * zop q u 2 2) (MvPolynomial.X 2 : Total L)
      = scal (q⁻¹ * (q ^ 2 / (1 - q) * (q ^ 2 / (1 - q))))
          * (MvPolynomial.X 2 - scal u * MvPolynomial.X 0) := by
  rw [Module.End.mul_apply, z2_X_two q u hq, push, push, map_sub, push, map_sub, push,
    z1_braid_X_zero q u hq, mul_zero, sub_zero, z1_X_two q u hq]
  simp only [comb]

private theorem comp_two_one (q u : L) (hq : q ≠ 0) :
    (zop q u 2 2 * zop q u 2 1) (MvPolynomial.X 2 : Total L)
      = scal (q ^ 2 / (1 - q) * (q⁻¹ * (q ^ 2 / (1 - q))))
          * (MvPolynomial.X 2
              - scal u * (MvPolynomial.X 1 - scal (q - 1) * MvPolynomial.X 0)) := by
  rw [Module.End.mul_apply, z1_X_two q u hq, push, map_sub, push, z2_X_zero q u hq, mul_zero,
    sub_zero, z2_X_two q u hq]
  simp only [comb]

/-- **`z_i` does carry `V_k` into itself** for `1 ≤ i ≤ k`, so the intended clause — commutation on
the graded piece — is well posed, and `HJO.Sweep.braidRep` can be typed on
`HJO.Sweep.pieceSub L k`. `z_1` is `HJO.Sweep.zopOneStar_mem_piece` and the recursion
adds two braid letters of index `i - 1 < k`, each `HJO.Sweep.braid_mem_piece`. -/
theorem zop_mem_piece (q u : L) {k : ℕ} :
    ∀ i : ℕ, 1 ≤ i → i ≤ k → ∀ {F : Total L}, F ∈ piece L k → zop q u k i F ∈ piece L k := by
  intro i
  induction i with
  | zero => intro h1; omega
  | succ m ih =>
    match m with
    | 0 => intro _ hik _ hF; exact zopOneStar_mem_piece q u hik hF
    | n + 1 =>
      intro _ hik F hF
      have hbr : ∀ {G : Total L}, G ∈ piece L k → braidEnd q (n + 1) G ∈ piece L k := fun hG =>
        braid_mem_piece q (by omega) (by omega) hG
      rw [zop_succ]
      exact smul_mem_piece (hbr (ih (by omega) (by omega) (hbr hF)))

/-- **`z_1z_2 ≠ z_2z_1` on the total space at `k = 2`.** The two composites disagree on `y_3`, the
first auxiliary variable outside `V_2`: the difference is `q^{-1}c^2u(y_2 - qy_1)` with
`c = q^2/(1-q)`. On `V_2` the clause is not refuted by this, and it holds there
(`HJO.Sweep.braidRepResidual_mellit`); what fails is
the extension of the operators past the graded piece they are defined between. -/
theorem zop_two_not_comm (q u : L) (hq : q ≠ 0) (hq1 : q ≠ 1) (hu : u ≠ 0) :
    zop q u 2 1 * zop q u 2 2 ≠ zop q u 2 2 * zop q u 2 1 := by
  intro h
  have h2 : (zop q u 2 1 * zop q u 2 2) (MvPolynomial.X 2 : Total L)
      = (zop q u 2 2 * zop q u 2 1) (MvPolynomial.X 2 : Total L) := by rw [h]
  rw [comp_one_two q u hq, comp_two_one q u hq,
    show q ^ 2 / (1 - q) * (q⁻¹ * (q ^ 2 / (1 - q)))
      = q⁻¹ * (q ^ 2 / (1 - q) * (q ^ 2 / (1 - q))) from by ring] at h2
  have hc : q ^ 2 / (1 - q) ≠ 0 :=
    div_ne_zero (pow_ne_zero 2 hq) fun h0 => hq1 (sub_eq_zero.mp h0).symm
  have hD : (scal (q⁻¹ * (q ^ 2 / (1 - q) * (q ^ 2 / (1 - q))) : L) : Total L) ≠ 0 :=
    scal_ne_zero (mul_ne_zero (inv_ne_zero hq) (mul_ne_zero hc hc))
  have h4 := sub_right_inj.mp (mul_left_cancel₀ hD h2)
  have h5 := mul_left_cancel₀ (scal_ne_zero (L := L) hu) h4
  have h6 := congrArg (MvPolynomial.coeff (Finsupp.single 1 1)) h5
  rw [MvPolynomial.coeff_sub, coeff_one_X_zero, coeff_one_X_one, scal,
    MvPolynomial.coeff_C_mul, coeff_one_X_zero, mul_zero, sub_zero] at h6
  exact zero_ne_one h6

/-- **The residual clause of Mellit's Proposition 5.3 is false on the total space.**
`BraidRepResidualTotal.zRepTotal_comm` asks for an equality in `Module.End L (Total L)`, and
`HJO.Sweep.zRepTotal_eq_smul_zop` turns it into the one refuted by
`HJO.Sweep.zop_two_not_comm`, the normalising scalar `(qu)^{-1}` being invertible.

The piece-level clause `HJO.Sweep.BraidRepResidual.zRep_comm` is **not** refuted by this: the two
composites are shown to differ at `y_3`, which is outside `V_2`. -/
theorem braidRepResidualTotal_two_false (q u : L) {r : L} (hr : r * r = q) (hq : q ≠ 0)
    (hq1 : q ≠ 1) (hu : u ≠ 0) : ¬ BraidRepResidualTotal q u r 2 := by
  intro h
  have hz := h.zRepTotal_comm 1 2 le_rfl (by norm_num) (by norm_num) le_rfl
  rw [zRepTotal_eq_smul_zop q u hr 1 le_rfl (by norm_num),
    zRepTotal_eq_smul_zop q u hr 2 (by norm_num) le_rfl, smul_mul_smul_comm,
    smul_mul_smul_comm] at hz
  have hqu : (q * u)⁻¹ * (q * u)⁻¹ ≠ 0 := by simp [hq, hu]
  exact zop_two_not_comm q u hq hq1 hu (smul_right_injective _ hqu hz)

/-- **`HJO.Sweep.braidRep` has no rank-`2` instance on the total space.** The relation family
`HJO.Braid.BraidRel.zWord_comm` forces the clause
`HJO.Sweep.braidRepResidualTotal_two_false` refutes, so the hypothesis
`HJO.Sweep.braidRepTotal` takes cannot be supplied at `k = 2`. This is why `HJO.Sweep.braidRep` is
typed at `HJO.Sweep.pieceSub L k` and takes `HJO.Sweep.BraidRepRespects` instead. -/
theorem braidRepRespectsTotal_two_false (q u : L) {r : L} (hr : r * r = q) (hq : q ≠ 0)
    (hq1 : q ≠ 1) (hu : u ≠ 0) : ¬ BraidRepRespectsTotal q u r 2 := by
  intro h
  refine braidRepResidualTotal_two_false q u hr hq hq1 hu ⟨fun i j hi hik hj hjk => ?_⟩
  have hw := h _ _ (Braid.BraidRel.zWord_comm i j hi hik hj hjk)
  rwa [map_mul, map_mul, ← zRepTotal_def, ← zRepTotal_def] at hw

/-! ### The transport to the piece-level clause needs one further relation

On `V_k` the clause `HJO.Sweep.BraidRepResidual.zRep_comm` is *statable*, and one would like to
obtain it as a transport:
`z_iz_j = z_jz_i` is Carlsson–Mellit's `y_iy_j = y_jy_i` (`HJO.Sweep.map_yElt_low_comm`) carried
across `HJO.Sweep.exists_slopeActions`, the reading being licensed by a prefactor computation: that
`q^k/(1-q)[d^*_+,d_-]T_{k↗1}` is their `y_1` formula verbatim under `q ↦ q⁻¹`, `d_+ ↦ d^*_+`,
`T_i ↦ T_i^{-1}`.

**That substitution list omits `d_-`, and the two sides do not use the same one.** Mellit's `z_1`
(`HJO.Sweep.zop`, `HJO.Sweep.zopOneStar`) is built on `HJO.Sweep.starComm`, the commutator of
`d^*_+` with `HJO.Sweep.dminus` — Mellit's `d^♭_-`, pairing `F_j` with `e_j`. The starred
action `HJO.Sweep.exists_isDpaAction_star` is all-Carlsson–Mellit
(`HJO/CMStructure/StarAction.lean`) and realises its loop through
`HJO.Sweep.starCommCM`, the commutator with `HJO.Sweep.dminusCM`, pairing `F_j` with `e_{j+1}`.

Inside the commutator the bridge settles this and costs nothing:
`HJO.Sweep.starCommCM_eq_neg_starComm_auxVar_mul` is `[d^*_+, d_-] = -[d^*_+, d^♭_-] ∘ (y_k ·)`
on `V_k`, and it is `HJO.Sweep.dminusCM_eq_neg_dminus_auxVar_mul`
applied to both summands together with `HJO.Sweep.dplusStar_auxVar_mul`.

**It does not settle the clause, because `z_1` is the commutator followed by a train and the
displacement lands between them.** The theorem below is the obstruction at the smallest rank: the
inserted `(y_k ·)` cannot be moved through `T_{k↗1}`, so the two `z_1`s are two operators and not
two spellings of one. `HJO/CMStructure/StarAction.lean` records the same conclusion from
the other side — reinstating the prefactors "would need a second `z` operator in the library
… which is a genuinely different operator from `HJO.Sweep.zopOneStar`".

So the missing relation is the conjugate of multiplication by `y_k` by the train, and it is not a
multiplication operator: `HJO.Sweep.braid_sub_self` makes `T_1y_1T_1^{-1}` equal
`y_2 + (q-1)y_1T_1^{-1}`. The displacement is harmless in the
one composite the starred action needs — `z_1d_+`, where it cancels
(`HJO/CMStructure/StarAction.lean`) — and `z_iz_j` supplies no `d_+` to cancel against. -/

section Convention

variable {L : Type*} [Field L] [Algebra ℚ L]

omit [Algebra ℚ L] in
private theorem coeff_zero_X_zero :
    MvPolynomial.coeff (Finsupp.single 0 1) (MvPolynomial.X 0 : Total L) = 1 := by
  rw [MvPolynomial.coeff_X]
  split_ifs with h0
  · rfl
  · exact absurd rfl h0

omit [Algebra ℚ L] in
private theorem coeff_zero_X_one :
    MvPolynomial.coeff (Finsupp.single 0 1) (MvPolynomial.X 1 : Total L) = 0 := by
  rw [MvPolynomial.coeff_X]
  split_ifs with h0
  · exact absurd (congrArg (fun d : ℕ →₀ ℕ => d 1) h0) (by simp)
  · rfl

omit [Algebra ℚ L] in
/-- **`T_1^{-1}` fixes the vacuum.** -/
private theorem braidInvEnd_one_vac (q : L) (hq : q ≠ 0) :
    braidInvEnd q 1 (1 : Total L) = 1 := by
  have h1 : (scal q⁻¹ : Total L) * scal q = 1 := by
    rw [← scal_mul, inv_mul_cancel₀ hq, scal_one]
  have hq2 : (scal q : Total L) = scal (q - 1) + 1 := by
    rw [← scal_one (L := L), ← scal_add]
    congr 1
    ring
  rw [braidInv_of_braid, show braidEnd q 1 (1 : Total L) = 1 from braid_map_one q 1]
  linear_combination h1 - (scal q⁻¹ : Total L) * hq2

omit [Algebra ℚ L] in
/-- **The convention displacement does not pass the train of `HJO.Sweep.zop`.** At `k = 2` the train
is `T_1^{-1}` (`HJO.Sweep.trainUpEnd_two_one`) and the displacement is multiplication by `y_2`, and
the two do not commute: on the vacuum one side gives `y_2` and the other
`T_1^{-1}(y_2) = y_1 + q^{-1}(q-1)y_2` (`HJO.Sweep.braidInvEnd_X_one`), which differ in their
`y_1`-coefficient. `y_2` is exactly the letter the relation `y_iT_j = T_jy_i` excludes at `j = 1`.

This is what stands between `HJO.Sweep.starCommCM_eq_neg_starComm_auxVar_mul` and an
identification of the two `z_1`s, hence between `HJO.Sweep.exists_slopeActions` and
`HJO.Sweep.BraidRepResidual.zRep_comm`. Only `q ≠ 0` is used, so no genericity assumption removes
it. -/
theorem mulLeft_auxVar_two_not_comm_trainUpEnd (q : L) (hq : q ≠ 0) :
    LinearMap.mulLeft L (auxVar 2 : Total L) * trainUpEnd q 2 1
      ≠ trainUpEnd q 2 1 * LinearMap.mulLeft L (auxVar 2 : Total L) := by
  intro h
  have h1 : (LinearMap.mulLeft L (auxVar 2 : Total L) * trainUpEnd q 2 1) (1 : Total L)
      = (trainUpEnd q 2 1 * LinearMap.mulLeft L (auxVar 2 : Total L)) (1 : Total L) := by rw [h]
  rw [Module.End.mul_apply, Module.End.mul_apply, LinearMap.mulLeft_apply,
    LinearMap.mulLeft_apply, mul_one, trainUpEnd_two_one, braidInvEnd_one_vac q hq, mul_one,
    show (auxVar 2 : Total L) = MvPolynomial.X 1 by rw [auxVar], braidInvEnd_X_one q hq] at h1
  have h2 := congrArg (MvPolynomial.coeff (Finsupp.single 0 1)) h1
  rw [coeff_zero_X_one, MvPolynomial.coeff_add, coeff_zero_X_zero, scal,
    MvPolynomial.coeff_C_mul, coeff_zero_X_one, mul_zero, add_zero] at h2
  exact zero_ne_one h2

end Convention

end HJO.Sweep
