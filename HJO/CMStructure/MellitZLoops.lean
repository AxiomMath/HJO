/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.CMStructure.BraidRepNotTotal
public import HJO.CMStructure.BraidRepReduce
public import HJO.CMStructure.StarAction
public import HJO.CMStructure.VmodActionMod
public import HJO.CarlssonMellit.CornerCommute
public meta import HJO.Attr

/-! # Mellit's `z_i` are the corner elements of the Mellit-convention action

`HJO.Sweep.BraidRepResidual.zRep_comm` — all that is left of `HJO.Sweep.braidRep`'s well-definedness
after `HJO.Sweep.braidRepRespects_of_residual` — asks that the operators `z_i` of `HJO.Sweep.zop`
commute with one another on `V_k`. This file proves that they do, given an action of the Dyck path
algebra in *Mellit's convention*: the triple `(T_i^{-1}, d^♭_-, d^*_+)` at the scalar `q^{-1}`.

The identification is exact, scalars included, and it is the whole content of the file:

`ρ(y_i) = z_i on V_k`, for `1 ≤ i ≤ k`,

where `y_i` is `HJO.Dyck.Aq.yElt`'s corner element of `HJO.Dyck.Aq L q⁻¹`. Commutation then comes
free from `HJO.Dyck.Aq.yElt_comm`, which holds in the algebra itself.

## Why the two families match, and why this is not the refuted transport

Mellit's `z_1` must not be read as the Carlsson--Mellit loop `y_1` carried across
`HJO.Sweep.exists_slopeActions` ("`z_iz_j = z_jz_i` is NOT a transport"): those two sit in different
`d_-` conventions, and `HJO.Sweep.mulLeft_auxVar_two_not_comm_trainUpEnd` shows the displacement
between them does not commute with the train. Nothing of that transport is used here. What is used
is an action whose lowering operator is `HJO.Sweep.dminus` — Mellit's `d^♭_-`, the one
`HJO.Sweep.starComm` and hence `HJO.Sweep.zop` are built on — so no bridge between conventions is
crossed at all.

With that convention fixed, the two families are the same family read from opposite ends.

* **The recursions agree.** `HJO.Dyck.Aq.yElt` walks *down*, `y_i = q'^{-1}T_iy_{i+1}T_i`; here
  `q' = q^{-1}` and the loop `T_i` goes to `T_i^{-1}`, so the image recursion is
  `ρ(y_{i+1}) = q^{-1}T_iρ(y_i)T_i`, which is `HJO.Sweep.zop`'s recursion for `z_{i+1}` on the nose
  (`HJO.Sweep.zop_eq_smul_conj_braidInv`).
* **The anchors agree, prefactor included.** `HJO.Dyck.Aq.yElt_self` anchors the family at the top,
  `y_k = (q'-1)^{-1}T̂_{k-1} ⋯ T̂_1 (d_+d_- - d_-d_+)e_k`; the inverted loops make
  `ρ(T̂_i) = T_i`, so `ρ(tinvWord)` is the descending train `T_{k↘1}` of uninverted letters and
  `ρ(Δ)` is `HJO.Sweep.starComm`. `HJO.Sweep.zop` anchors at the bottom, and unwinding its recursion
  with `HJO.Sweep.zop_eq_conj` gives `z_k = q/(1-q)T_{k↘1}[d^*_+,d^♭_-]`
  (`HJO.Sweep.zop_self_eq`) — the two trains of the conjugation cancelling against the train inside
  `z_1`. Since `(q^{-1}-1)^{-1} = q/(1-q)`, the two anchors are the same operator.

So the descending induction from `i = k` to `i = 1` closes, and the residual clause follows.

## Main results

* `HJO.Sweep.zop_self_eq` — `z_k = q/(1-q)T_{k↘1}[d^*_+,d^♭_-]`, the closed form at the top index.
* `HJO.Sweep.map_yElt_ofPiece_mellit` — the identification `ρ(y_i) = z_i` on `V_k`.
* `HJO.Sweep.zop_comm_of_mellitAction` — `z_iz_j = z_jz_i` on `V_k`.
* `HJO.Sweep.braidRepResidual_of_mellitAction`, `HJO.Sweep.braidRepRespects_of_mellitAction` —
  the residual clause and, through `HJO.Sweep.braidRepRespects_of_residual`, the whole of
  `HJO.Sweep.braidRep`'s well-definedness.

The hypotheses are the *conclusion* of the Mellit-convention instance, not its existential, exactly
as `HJO/CMStructure/VmodYMultiplication.lean` does for the modified action: the statements
quantify over any `ρ` with those four clauses. `HJO/CMStructure/MellitBraidRep.lean` supplies
one and states the result.

## Implementation notes

**`q ≠ 1` is where `HJO.Dyck.Aq.yElt` divides.** The corner elements carry `(q'-1)^{-1}` with
`q' = q^{-1}`, so the algebra is only written down when `q^{-1} - 1` is invertible, that is when
`q ∉ {0, 1}`. That is the same scalar `HJO.Sweep.zop` divides by, `q^k/(1-q)`, so no hypothesis is
introduced that the target operator does not already need. Every use instantiates it at
parameters algebraically independent over `ℤ`.

**No membership is ever carried.** Each statement is written with the value as an explicit second
element of `HJO.Sweep.pieceSub` and an equation on the underlying element of `HJO.Sweep.Total`,
which is this library's idiom for an operator known to preserve the piece; the preservation
facts used are `HJO.Sweep.zop_mem_piece`, `HJO.Sweep.trainDownEnd_mem_piece` and
`HJO.Sweep.braidInv_mem_piece`.

## References

The lemma `HJO.Sweep.braidRepRespects_mellit` and the definitions `HJO.Sweep.braidRep`,
`HJO.Sweep.zop`, `HJO.Dyck.Aq.yElt`, `HJO.Dyck.Aq`, `HJO.Sweep.IsDpaAction`; also
`HJO.Dyck.Aq.yElt_comm`. Transcribing A. Mellit, *Toric braids and `(m, n)`-parking functions*,
Proposition 5.3, and E. Carlsson and A. Mellit, *A proof of the shuffle conjecture*, §3.
-/

@[expose] public section

namespace HJO.Sweep

/-! ### Two readings of `HJO.Sweep.zop`'s recursion -/

section Zop

variable {L : Type*} [Field L] [Algebra ℚ L]

omit [Algebra ℚ L] in
/-- **The descending train grows by its top letter**: `T_{n+2↘1} = T_{n+1}T_{n+1↘1}`, by
`HJO.Braid.trainDown_mul_trainDown` with the single-letter train
`HJO.Sweep.trainDownEnd_succ_self`. -/
theorem trainDownEnd_succ_one (q : L) (hq : q ≠ 0) {k n : ℕ} (hn : n + 2 ≤ k) :
    trainDownEnd q (n + 2) 1 = braidEnd q (n + 1) * trainDownEnd q (n + 1) 1 := by
  have hbs := isBraidSystem_braidEnd q hq k
  rw [← trainDownEnd_succ_self q (n + 1)]
  exact (Braid.trainDown_mul_trainDown hbs (by omega) hn (by omega) (by omega) le_rfl
    (by omega)).symm

/-- **`HJO.Sweep.zop`'s recursion read backwards**: `z_i = qT_i^{-1}z_{i+1}T_i^{-1}`. This is the
form the descending recursion of `HJO.Dyck.Aq.yElt` meets, the corner elements walking down from
the top while `HJO.Sweep.zop` walks up from `z_1`. -/
theorem zop_eq_smul_conj_braidInv (q u : L) (hq : q ≠ 0) (k i : ℕ) :
    zop q u k (i + 1)
      = q • (braidInvEnd q (i + 1) * zop q u k (i + 2) * braidInvEnd q (i + 1)) := by
  rw [zop_succ, mul_smul_comm, smul_mul_assoc, smul_smul, mul_inv_cancel₀ hq, one_smul]
  simp only [mul_assoc]
  rw [braidEnd_mul_braidInvEnd q hq, mul_one, ← mul_assoc, braidInvEnd_mul_braidEnd q hq, one_mul]

/-- **The top `z` is the commutator preceded by the descending train**:
`z_k = q/(1-q)T_{k↘1}[d^*_+,d^♭_-]` on `V_k`.

Unwind `HJO.Sweep.zop`'s recursion with `HJO.Sweep.zop_eq_conj`: `z_k` is `z_1` conjugated by
`T_{k↘1}` and `T_{1↗k}`, and the train `T^*_{k↘1}` sitting inside `z_1` is the two-sided inverse
of `T_{1↗k}` (`HJO.Braid.trainUp_mul_trainUp_self`), so the right-hand trains cancel and only the
left one survives. The scalars combine as `q^{-(k-1)}q^k/(1-q) = q/(1-q)`, which is
`(q^{-1}-1)^{-1}` — the prefactor `HJO.Dyck.Aq.yElt` carries for the algebra at `q^{-1}`. -/
theorem zop_self_eq (q u : L) (hq : q ≠ 0) {k : ℕ} (hk : 1 ≤ k) :
    zop q u k k = (q / (1 - q)) • (trainDownEnd q k 1 * starComm q u k) := by
  obtain ⟨i, rfl⟩ : ∃ i, k = i + 1 := ⟨k - 1, by omega⟩
  have hbs := isBraidSystem_braidEnd q hq (i + 1)
  have hcancel : trainUpEnd q (i + 1) 1 * trainUpEnd q 1 (i + 1) = 1 :=
    Braid.trainUp_mul_trainUp_self hbs (by omega) le_rfl le_rfl (by omega)
  have hop : trainDownEnd q (i + 1) 1 * (starComm q u (i + 1) * trainUpEnd q (i + 1) 1)
      * trainUpEnd q 1 (i + 1)
      = trainDownEnd q (i + 1) 1 * starComm q u (i + 1) := by
    simp only [mul_assoc, hcancel, mul_one]
  have hs : (q ^ i)⁻¹ * (q ^ (i + 1) / (1 - q)) = q / (1 - q) := by
    rw [div_eq_mul_inv, div_eq_mul_inv, pow_succ, ← mul_assoc, ← mul_assoc,
      inv_mul_cancel₀ (pow_ne_zero i hq), one_mul]
  rw [zop_eq_conj q u hq i le_rfl, zopOneStar_eq, mul_smul_comm, smul_mul_assoc, smul_smul, hop,
    hs]

end Zop

/-! ### The corner elements of a Mellit-convention action -/

section MellitAction

variable {L : Type*} [Field L] [Algebra ℚ L] {q u : L}
  [Invertible (q⁻¹ : L)] [Invertible (q⁻¹ - 1 : L)]
  {ρ : Dyck.Aq L q⁻¹ →ₐ[L] Module.End L (Vstar L)}

variable (hact : IsDpaAction q⁻¹ ρ)
  (hT : ∀ k i : ℕ, ρ (Dyck.Aq.Tg L q⁻¹ k i) = loopVstar (braidInvModPiece q) k i)
  (hD : ∀ k : ℕ, ρ (Dyck.Aq.dMinus L q⁻¹ k) = lowerVstar (dminusModPiece q) k)
  (hU : ∀ k : ℕ, ρ (Dyck.Aq.dPlus L q⁻¹ k) = raiseVstar (dplusStarPiece q u) k)

omit [Algebra ℚ L] [Invertible (q⁻¹ - 1 : L)] in
/-- The scalar `HJO.Dyck.braidInvGen` divides by, at the algebra's own parameter `q^{-1}`. -/
theorem invOf_inv_eq (hq : q ≠ 0) : (⅟(q⁻¹ : L) : L) = q :=
  invOf_eq_right_inv (inv_mul_cancel₀ hq)

omit [Algebra ℚ L] [Invertible (q⁻¹ : L)] in
/-- The scalar `HJO.Dyck.Aq.yElt` divides by, at the algebra's own parameter `q^{-1}`: it is
`HJO.Sweep.zop`'s own `q/(1-q)`. -/
theorem invOf_inv_sub_one_eq (hq : q ≠ 0) (hq1 : q ≠ 1) :
    (⅟(q⁻¹ - 1 : L) : L) = q / (1 - q) := by
  have h1 : (1 : L) - q ≠ 0 := sub_ne_zero.2 (Ne.symm hq1)
  refine invOf_eq_right_inv ?_
  field_simp

omit [Algebra ℚ L] in
/-- Two elements of a summand agree as soon as their images in `V_*` do. -/
theorem eq_of_ofPiece_eq {k : ℕ} {X Y : pieceSub L k} (h : ofPiece L k X = ofPiece L k Y) :
    X = Y := by
  have h' := congrArg (toPiece L k) h
  rwa [toPiece_ofPiece, toPiece_ofPiece] at h'

omit [Algebra ℚ L] [Invertible (q⁻¹ - 1 : L)] in
include hact hT in
/-- **The action sends the polynomial inverse of a loop to the uninverted braid operator.** The
loops go to `T_{i+1}^{-1}`, so their inverses go to `T_{i+1}`; no scalar computation is needed,
`HJO.Dyck.Aq.Tinv_mul_Tg` and `HJO.Sweep.IsDpaAction`'s clause on the idempotents doing the work. -/
theorem map_Tinv_ofPiece (hq : q ≠ 0) {k i : ℕ} (hik : i + 2 ≤ k) (F G : pieceSub L k)
    (hG : (G : Total L) = braidEnd q (i + 1) F) :
    ρ (Dyck.Aq.Tinv L q⁻¹ k i) (ofPiece L k F) = ofPiece L k G := by
  have hFG : ρ (Dyck.Aq.Tg L q⁻¹ k i) (ofPiece L k G) = ofPiece L k F := by
    rw [hT, loopVstar_ofPiece]
    refine congrArg (ofPiece L k) (Subtype.ext ?_)
    rw [coe_braidInvModPiece q hik, hG]
    exact braidInv_braid q hq (i + 1) F
  calc ρ (Dyck.Aq.Tinv L q⁻¹ k i) (ofPiece L k F)
      = ρ (Dyck.Aq.Tinv L q⁻¹ k i) (ρ (Dyck.Aq.Tg L q⁻¹ k i) (ofPiece L k G)) := by rw [hFG]
    _ = ρ (Dyck.Aq.Tinv L q⁻¹ k i * Dyck.Aq.Tg L q⁻¹ k i) (ofPiece L k G) := by
        rw [map_mul]; rfl
    _ = ofPiece L k G := by rw [Dyck.Aq.Tinv_mul_Tg hik, hact.map_e, pieceProj_ofPiece]

omit [Algebra ℚ L] [Invertible (q⁻¹ - 1 : L)] in
include hact hT in
/-- **The action sends the descending word of inverses to the descending train**:
`ρ(T̂_n ⋯ T̂_1) = T_{n+1↘1}` on `V_k`, the uninverted train of `HJO.Braid.trainDown`. -/
theorem map_tinvWord_ofPiece (hq : q ≠ 0) {k : ℕ} :
    ∀ n : ℕ, n + 1 ≤ k → ∀ F G : pieceSub L k,
      (G : Total L) = trainDownEnd q (n + 1) 1 F →
      ρ (Dyck.Aq.tinvWord L q⁻¹ k n) (ofPiece L k F) = ofPiece L k G := by
  intro n
  induction n with
  | zero =>
    intro _ F G hG
    rw [Dyck.Aq.tinvWord_zero, hact.map_e, pieceProj_ofPiece]
    refine congrArg (ofPiece L k) (Subtype.ext ?_)
    rw [hG, trainDownEnd, Braid.trainDown_self]
    rfl
  | succ n ih =>
    intro hn F G hG
    have hmem : trainDownEnd q (n + 1) 1 (F : Total L) ∈ pieceSub L k :=
      trainDownEnd_mem_piece q (by omega) (by omega) F.2
    have hstep : ρ (Dyck.Aq.tinvWord L q⁻¹ k n) (ofPiece L k F)
        = ofPiece L k ⟨trainDownEnd q (n + 1) 1 (F : Total L), hmem⟩ :=
      ih (by omega) F _ rfl
    rw [Dyck.Aq.tinvWord_succ, map_mul, Module.End.mul_apply, hstep]
    refine map_Tinv_ofPiece hact hT hq (by omega) _ G ?_
    rw [hG, trainDownEnd_succ_one q hq (k := k) (by omega), Module.End.mul_apply]

omit [Invertible (q⁻¹ : L)] [Invertible (q⁻¹ - 1 : L)] in
include hD hU in
/-- **The action sends the commutator to `HJO.Sweep.starComm`**, the commutator
`d^*_+d^♭_- - d^♭_-d^*_+` that `HJO.Sweep.zop` is built on. -/
theorem map_Delta_ofPiece_mellit (m : ℕ) (F G : pieceSub L (m + 1))
    (hG : (G : Total L) = starComm q u (m + 1) F) :
    ρ (Dyck.Aq.Delta L q⁻¹ m) (ofPiece L (m + 1) F) = ofPiece L (m + 1) G := by
  have hdel : ρ (Dyck.Aq.Delta L q⁻¹ m)
      = deltaVstar (dminusModPiece q) (dplusStarPiece q u) m := by
    rw [Dyck.Aq.Delta, map_sub, map_mul, map_mul, hU, hD, hD, hU, deltaVstar]
  rw [hdel, deltaVstar_ofPiece]
  refine congrArg (ofPiece L (m + 1)) (Subtype.ext ?_)
  rw [hG]
  rfl

include hact hT hD hU in
/-- **The top corner element is the top `z`**: `ρ(y_k) = z_k` on `V_k`.

`HJO.Dyck.Aq.yElt_self` reads `y_k` as the commutator preceded by the descending word of inverted
loops and scaled by `(q^{-1}-1)^{-1}`; `HJO.Sweep.zop_self_eq` reads `z_k` as the same commutator
preceded by the same train and scaled by `q/(1-q)`, and those two scalars are equal. -/
theorem map_yElt_self_ofPiece_mellit (hq : q ≠ 0) (hq1 : q ≠ 1) (m : ℕ)
    (F G : pieceSub L (m + 1)) (hG : (G : Total L) = zop q u (m + 1) (m + 1) F) :
    ρ (Dyck.Aq.yElt L q⁻¹ (m + 1) (m + 1)) (ofPiece L (m + 1) F) = ofPiece L (m + 1) G := by
  set G₁ : pieceSub L (m + 1) := dplusStarPiece q u m (dminusModPiece q m F)
    - dminusModPiece q (m + 1) (dplusStarPiece q u (m + 1) F) with hG₁
  have h1 : ρ (Dyck.Aq.Delta L q⁻¹ m) (ofPiece L (m + 1) F) = ofPiece L (m + 1) G₁ :=
    map_Delta_ofPiece_mellit hD hU m F G₁ rfl
  have hmem2 : trainDownEnd q (m + 1) 1 (G₁ : Total L) ∈ pieceSub L (m + 1) :=
    trainDownEnd_mem_piece q le_rfl (by omega) G₁.2
  have h2 : ρ (Dyck.Aq.tinvWord L q⁻¹ (m + 1) m) (ofPiece L (m + 1) G₁)
      = ofPiece L (m + 1) ⟨trainDownEnd q (m + 1) 1 (G₁ : Total L), hmem2⟩ :=
    map_tinvWord_ofPiece hact hT hq m le_rfl G₁ _ rfl
  rw [Dyck.Aq.yElt_self, Nat.add_sub_cancel, map_smul, map_mul, map_mul, LinearMap.smul_apply,
    Module.End.mul_apply, Module.End.mul_apply, hact.map_e, pieceProj_ofPiece, h1, h2, ← map_smul]
  refine congrArg (ofPiece L (m + 1)) (Subtype.ext ?_)
  rw [SetLike.val_smul, hG, zop_self_eq q u hq (by omega), LinearMap.smul_apply,
    Module.End.mul_apply, invOf_inv_sub_one_eq hq hq1]
  rfl

include hact hT hD hU in
/-- **The corner elements are Mellit's `z` operators**: `ρ(y_i) = z_i` on `V_k`, for
`1 ≤ i ≤ k`.

The two families satisfy the same recursion — `HJO.Dyck.Aq.yElt`'s downward
`y_i = q'^{-1}T_iy_{i+1}T_i` becomes `z_i = qT_i^{-1}z_{i+1}T_i^{-1}` once the loops are inverted
and `q' = q^{-1}` (`HJO.Sweep.zop_eq_smul_conj_braidInv`) — and they agree at the top index by
`HJO.Sweep.map_yElt_self_ofPiece_mellit`, so the descending induction closes. -/
theorem map_yElt_ofPiece_mellit (hq : q ≠ 0) (hq1 : q ≠ 1) {k : ℕ} :
    ∀ (d i : ℕ), i + d = k → 1 ≤ i → ∀ F G : pieceSub L k,
      (G : Total L) = zop q u k i F →
      ρ (Dyck.Aq.yElt L q⁻¹ k i) (ofPiece L k F) = ofPiece L k G := by
  intro d
  induction d with
  | zero =>
    intro i hik h1 F G hG
    obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
    obtain rfl : i = m + 1 := by omega
    exact map_yElt_self_ofPiece_mellit hact hT hD hU hq hq1 m F G hG
  | succ d ih =>
    intro i hik h1 F G hG
    have hlt : i < k := by omega
    have hmemF : braidInv q i (F : Total L) ∈ pieceSub L k := braidInv_mem_piece q hlt F.2
    set F' : pieceSub L k := ⟨braidInv q i (F : Total L), hmemF⟩ with hF'
    have hmemG : zop q u k (i + 1) (F' : Total L) ∈ pieceSub L k :=
      zop_mem_piece q u (i + 1) (by omega) (by omega) F'.2
    have hstep : ρ (Dyck.Aq.yElt L q⁻¹ k (i + 1)) (ofPiece L k F')
        = ofPiece L k ⟨zop q u k (i + 1) (F' : Total L), hmemG⟩ :=
      ih (i + 1) (by omega) (by omega) F' _ rfl
    have hTi : ρ (Dyck.Aq.Tg L q⁻¹ k (i - 1)) (ofPiece L k F) = ofPiece L k F' := by
      rw [hT, loopVstar_ofPiece]
      refine congrArg (ofPiece L k) (Subtype.ext ?_)
      have h := coe_braidInvModPiece q (show i - 1 + 2 ≤ k from by omega) F
      rw [show i - 1 + 1 = i from by omega] at h
      rw [h, hF']
    have hTi' : ρ (Dyck.Aq.Tg L q⁻¹ k (i - 1))
          (ofPiece L k ⟨zop q u k (i + 1) (F' : Total L), hmemG⟩)
        = ofPiece L k (braidInvModPiece q k (i - 1)
            ⟨zop q u k (i + 1) (F' : Total L), hmemG⟩) := by
      rw [hT, loopVstar_ofPiece]
    rw [Dyck.Aq.yElt_recursion h1 hlt, map_smul, map_mul, map_mul, LinearMap.smul_apply,
      Module.End.mul_apply, Module.End.mul_apply, hTi, hstep, hTi', ← map_smul]
    refine congrArg (ofPiece L k) (Subtype.ext ?_)
    have hb := coe_braidInvModPiece q (show i - 1 + 2 ≤ k from by omega)
      (⟨zop q u k (i + 1) (F' : Total L), hmemG⟩ : pieceSub L k)
    rw [show i - 1 + 1 = i from by omega] at hb
    rw [SetLike.val_smul, hb, hG, invOf_inv_eq hq]
    obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
    rw [zop_eq_smul_conj_braidInv q u hq k j, LinearMap.smul_apply, Module.End.mul_apply,
      Module.End.mul_apply]
    rfl

include hact hT hD hU in
/-- **Mellit's `z` operators commute on `V_k`**, which is what
`HJO.Sweep.BraidRepResidual.zRep_comm` asks. The commutation is `HJO.Dyck.Aq.yElt_comm`, a theorem
of `HJO.Dyck.Aq` carrying no hypothesis beyond `1 ≤ i, j ≤ k`, read through the identification
`HJO.Sweep.map_yElt_ofPiece_mellit`. -/
theorem zop_comm_of_mellitAction (hq : q ≠ 0) (hq1 : q ≠ 1) {k : ℕ} :
    ∀ i j : ℕ, 1 ≤ i → i ≤ k → 1 ≤ j → j ≤ k → ∀ F ∈ piece L k,
      zop q u k i (zop q u k j F) = zop q u k j (zop q u k i F) := by
  intro i j hi hik hj hjk F hF
  have hmemj : zop q u k j F ∈ pieceSub L k := zop_mem_piece q u j hj hjk hF
  have hmemi : zop q u k i F ∈ pieceSub L k := zop_mem_piece q u i hi hik hF
  have hmemij : zop q u k i (zop q u k j F) ∈ pieceSub L k :=
    zop_mem_piece q u i hi hik hmemj
  have hmemji : zop q u k j (zop q u k i F) ∈ pieceSub L k :=
    zop_mem_piece q u j hj hjk hmemi
  have h1 : ρ (Dyck.Aq.yElt L q⁻¹ k j) (ofPiece L k ⟨F, hF⟩)
      = ofPiece L k ⟨zop q u k j F, hmemj⟩ :=
    map_yElt_ofPiece_mellit hact hT hD hU hq hq1 (k - j) j (by omega) hj _ _ rfl
  have h2 : ρ (Dyck.Aq.yElt L q⁻¹ k i) (ofPiece L k ⟨zop q u k j F, hmemj⟩)
      = ofPiece L k ⟨zop q u k i (zop q u k j F), hmemij⟩ :=
    map_yElt_ofPiece_mellit hact hT hD hU hq hq1 (k - i) i (by omega) hi _ _ rfl
  have h3 : ρ (Dyck.Aq.yElt L q⁻¹ k i) (ofPiece L k ⟨F, hF⟩)
      = ofPiece L k ⟨zop q u k i F, hmemi⟩ :=
    map_yElt_ofPiece_mellit hact hT hD hU hq hq1 (k - i) i (by omega) hi _ _ rfl
  have h4 : ρ (Dyck.Aq.yElt L q⁻¹ k j) (ofPiece L k ⟨zop q u k i F, hmemi⟩)
      = ofPiece L k ⟨zop q u k j (zop q u k i F), hmemji⟩ :=
    map_yElt_ofPiece_mellit hact hT hD hU hq hq1 (k - j) j (by omega) hj _ _ rfl
  have hcomm : ρ (Dyck.Aq.yElt L q⁻¹ k i * Dyck.Aq.yElt L q⁻¹ k j)
      = ρ (Dyck.Aq.yElt L q⁻¹ k j * Dyck.Aq.yElt L q⁻¹ k i) := by
    rw [Dyck.Aq.yElt_comm hi hik hj hjk]
  have happ := congrArg (fun f : Module.End L (Vstar L) => f (ofPiece L k ⟨F, hF⟩)) hcomm
  simp only [map_mul, Module.End.mul_apply, h1, h2, h3, h4] at happ
  exact congrArg Subtype.val (eq_of_ofPiece_eq happ)

include hact hT hD hU in
/-- **The residual clause of Mellit's Proposition 5.3**, `HJO.Sweep.BraidRepResidual`: the one
family of relations `HJO.Sweep.braidRepRespects_of_residual` leaves open. The normalising scalar
`(qu)^{-1}` of `HJO.Sweep.zRepTotal_eq_smul_zop` appears on both sides and needs no cancelling, so
no hypothesis on `u` is used. -/
theorem braidRepResidual_of_mellitAction (hq : q ≠ 0) (hq1 : q ≠ 1) {r : L} (hr : r * r = q)
    (k : ℕ) : BraidRepResidual q u r k := by
  have key : ∀ a b : ℕ, 1 ≤ a → a ≤ k → 1 ≤ b → b ≤ k → ∀ x : pieceSub L k,
      ((zRep q u r k a * zRep q u r k b) x : Total L)
        = ((q * u)⁻¹ * (q * u)⁻¹) • zop q u k a (zop q u k b x) := by
    intro a b ha hak hb hbk x
    rw [Module.End.mul_apply, coe_zRep, zRepTotal_eq_smul_zop q u hr a ha hak,
      LinearMap.smul_apply, coe_zRep, zRepTotal_eq_smul_zop q u hr b hb hbk,
      LinearMap.smul_apply, map_smul, smul_smul]
  refine ⟨fun i j hi hik hj hjk => ?_⟩
  refine LinearMap.ext fun x => Subtype.ext ?_
  rw [key i j hi hik hj hjk, key j i hj hjk hi hik,
    zop_comm_of_mellitAction hact hT hD hU hq hq1 i j hi hik hj hjk x x.2]

include hact hT hD hU in
/-- **The assignment of `HJO.Sweep.braidRep` respects the presentation**, given a Mellit-convention
action: `HJO.Sweep.braidRepRespects_of_residual` discharges nine of the ten relation families and
`HJO.Sweep.braidRepResidual_of_mellitAction` the tenth. -/
theorem braidRepRespects_of_mellitAction (hq : q ≠ 0) (hq1 : q ≠ 1) {r : L} (hr : r * r = q)
    (k : ℕ) : BraidRepRespects q u r k :=
  braidRepRespects_of_residual q u hq hr k
    (braidRepResidual_of_mellitAction hact hT hD hU hq hq1 hr k)

end MellitAction

end HJO.Sweep

end
