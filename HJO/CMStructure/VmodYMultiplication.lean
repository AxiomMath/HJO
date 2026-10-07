/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.CMStructure.DemazureIdentities
public import HJO.CMStructure.VmodActionMod
public import HJO.CMStructure.VmodCommutatorMod
public import HJO.CarlssonMellit.CornerCalculus
public meta import HJO.Attr

/-! # The loops of the modified action are the variables

`HJO.Sweep.map_yElt_eq_auxMulPiece`: for `k ≥ 1` and `1 ≤ i ≤ k` the operator `ρ^♭(y_i)` on `V_k` —
the image under the action of `HJO.Sweep.exists_isDpaAction_mod` of the loop `y_i` of
`HJO.Dyck.Aq.yElt` — is multiplication by `y_i`.

## Main definitions

* `HJO.Sweep.auxMulPiece` — multiplication by `y_i` on the graded piece `V_k`, and `0` when `y_i`
  is not one of the variables `V_k` reads. This is the operator the statement names.
* `HJO.Sweep.ascPiece` — the image of the ascending word `T_{1↑k}` of `HJO.Sweep.cmAscWord` on the
  summand, as the composite of the loops the action sends `Tg k 0, …, Tg k (n-1)` to.

## Main results

* `HJO.Sweep.map_yElt_eq_auxMulPiece`, as an equality of
  endomorphisms of `V_*`.
* `HJO.Sweep.map_yElt_ofPiece` — the same, read on the summand.
* `HJO.Sweep.cmAscWord_one_injective` — the ascending word `T_{1↑k}` is injective, which is what
  the invertibility of `T_{1↑k}` by `HJO.Sweep.braid_braidInv` is used for.

## Implementation notes

**The hypotheses are the conclusion of `HJO.Sweep.exists_isDpaAction_mod`, not its existential.**
The statement speaks of *the* action `ρ^♭`, so it is stated here for any `ρ` satisfying the four
clauses `HJO.Sweep.exists_isDpaAction_mod` produces. That is strictly stronger than a statement
about one chosen witness and it is what `HJO.Sweep.isIntertwinedPair_replication_pairs` needs of it.

**`(q-1)` is cancelled through `Invertible (q - 1)`, not through `q ≠ 1`.** The argument compares
`(q-1)T_{1↑k}ρ^♭(y_k)F` with `(q-1)T_{1↑k}(y_kF)` and cancels the scalar. Here the scalar is
cancelled by `⅟(q-1)`, which is already in scope: `HJO.Dyck.Aq.yElt` divides by `q - 1` and so every
statement naming `HJO.Dyck.Aq.yElt` carries `[Invertible (q - 1)]`. No hypothesis `q ≠ 1` is
introduced, and none is needed.

**`T_{1↑k}` is cancelled by injectivity, and injectivity is the letterwise one.** The word is
`T_1 ∘ ⋯ ∘ T_m` and each letter has the two-sided inverse of `HJO.Sweep.braid_braidInv`; peeling
the *last* letter (`HJO.Sweep.cmAscWord_one_succ_apply`) keeps the left end of the word fixed and
makes the induction structural.

**`q ≠ 0` is inherited.** It is the hypothesis of `HJO.Sweep.exists_isDpaAction_mod` and of
`HJO.Sweep.dplus_dminus_sub_dminus_dplus`; here it comes from `[Invertible q]`, which
`HJO.Dyck.Aq.yElt` already requires. No further side condition on `q` appears.

## References

This file proves `HJO.Sweep.map_yElt_eq_auxMulPiece`, using `HJO.Sweep.piece`, `HJO.Dyck.Aq.yElt`,
`HJO.Braid.wordUp`, `HJO.Sweep.exists_isDpaAction_mod`, `HJO.Sweep.braid_braidInv`,
`HJO.Dyck.Aq.Delta_eq_wordUp`, `HJO.Sweep.braid_auxVar_succ_mul_braid` and
`HJO.Sweep.dplus_dminus_sub_dminus_dplus`. A. Mellit, *Toric braids and `(m, n)`-parking functions*,
§3.
-/

@[expose] public section

namespace HJO.Sweep

/-! ### Multiplication by a variable on the summand -/

section Mul

variable {L : Type*} [CommRing L]

/-- The two readings of the graded piece — the `Λ`-subalgebra `HJO.Sweep.piece` and the
`L`-submodule `HJO.Sweep.pieceSub` — have the same elements, so a membership in one is a membership
in the other. -/
theorem mem_piece_of_mem_pieceSub {k : ℕ} {x : Total L} (hx : x ∈ pieceSub L k) :
    x ∈ piece L k := hx

/-- The converse reading of `HJO.Sweep.mem_piece_of_mem_pieceSub`. -/
theorem mem_pieceSub_of_mem_piece {k : ℕ} {x : Total L} (hx : x ∈ piece L k) :
    x ∈ pieceSub L k := hx

/-- **Multiplication by the auxiliary variable `y_i` on the graded piece `V_k`**, and `0` when `y_i`
is not one of the variables `V_k` reads, that is when `i = 0` or `i > k`. This is the operator
`HJO.Sweep.map_yElt_eq_auxMulPiece` names, in the shape `HJO.Sweep.loopVstar` reads a loop family
in. -/
noncomputable def auxMulPiece (L : Type*) [CommRing L] (k i : ℕ) :
    pieceSub L k →ₗ[L] pieceSub L k :=
  if h : 1 ≤ i ∧ i ≤ k then
    (LinearMap.mulLeft L (auxVar i : Total L)).restrict
      (fun x hx => by
        rw [LinearMap.mulLeft_apply]
        exact mem_pieceSub_of_mem_piece
          (mul_mem (auxVar_mem_piece h.1 h.2) (mem_piece_of_mem_pieceSub hx)))
  else 0

theorem coe_auxMulPiece {k i : ℕ} (h1 : 1 ≤ i) (hik : i ≤ k) (F : pieceSub L k) :
    (auxMulPiece L k i F : Total L) = (auxVar i : Total L) * F := by
  have hc : 1 ≤ i ∧ i ≤ k := ⟨h1, hik⟩
  rw [auxMulPiece]
  simp only [hc, and_self, ↓reduceDIte, LinearMap.coe_restrict_apply, LinearMap.mulLeft_apply]

end Mul

/-! ### The ascending word, read on the summand -/

section Word

variable {L : Type*} [Field L] {q : L}

/-- **The image of the ascending word on the summand**: the composite
`T_1 ∘ ⋯ ∘ T_n` of `HJO.Sweep.braidModPiece`, which is what an action sends
`HJO.Dyck.Aq.tSegUp k 0 n` to. -/
noncomputable def ascPiece (q : L) (k : ℕ) : ℕ → (pieceSub L k →ₗ[L] pieceSub L k)
  | 0 => LinearMap.id
  | n + 1 => (ascPiece q k n).comp (braidModPiece q k n)

@[simp]
theorem ascPiece_zero (q : L) (k : ℕ) : ascPiece q k 0 = LinearMap.id := rfl

theorem ascPiece_succ (q : L) (k n : ℕ) :
    ascPiece q k (n + 1) = (ascPiece q k n).comp (braidModPiece q k n) := rfl

theorem cmAscWord_one_zero (q : L) : cmAscWord q 1 0 = 1 := by
  simp

/-- **The ascending word `T_{1↑k}` is injective**, which is the use the argument makes of
`HJO.Sweep.braid_braidInv`: every letter has the two-sided inverse `T_i^{-1}`, and the last letter
is peeled off by `HJO.Sweep.cmAscWord_one_succ_apply`. -/
theorem cmAscWord_one_injective (q : L) (hq : q ≠ 0) (m : ℕ) :
    Function.Injective (cmAscWord q 1 m) := by
  induction m with
  | zero =>
    intro x y h
    rw [cmAscWord_one_zero] at h
    simp only [Module.End.one_apply] at h
    exact h
  | succ m ih =>
    intro x y h
    rw [cmAscWord_one_succ_apply, cmAscWord_one_succ_apply] at h
    have hb := ih h
    rw [← braidInv_braid q hq (m + 1) x, ← braidInv_braid q hq (m + 1) y, hb]

/-- The value of `HJO.Sweep.ascPiece` is the ascending word of `HJO.Sweep.cmAscWord`. -/
theorem coe_ascPiece (q : L) {k : ℕ} :
    ∀ (n : ℕ), n + 1 ≤ k → ∀ F : pieceSub L k,
      (ascPiece q k n F : Total L) = cmAscWord q 1 n F := by
  intro n
  induction n with
  | zero => intro _ F; rw [ascPiece_zero, cmAscWord_one_zero]; rfl
  | succ n ih =>
    intro hn F
    rw [ascPiece_succ, LinearMap.comp_apply, ih (by omega), cmAscWord_one_succ_apply,
      coe_braidModPiece q (show n + 2 ≤ k from by omega)]

end Word

/-! ### The loops of the modified action -/

section YMul

variable {L : Type*} [Field L] [Algebra ℚ L] {q : L} [Invertible q] [Invertible (q - 1)]
  {ρ : Dyck.Aq L q →ₐ[L] Module.End L (Vstar L)}

variable (hact : IsDpaAction q ρ)
  (hT : ∀ k i : ℕ, ρ (Dyck.Aq.Tg L q k i) = loopVstar (braidModPiece q) k i)
  (hD : ∀ k : ℕ, ρ (Dyck.Aq.dMinus L q k) = lowerVstar (dminusModPiece q) k)
  (hU : ∀ k : ℕ, ρ (Dyck.Aq.dPlus L q k) = raiseVstar (dplusModPiece q) k)

omit [Algebra ℚ L] [Invertible q] [Invertible (q - 1)] in
include hT in
/-- **The action sends the ascending word of loops to `HJO.Sweep.ascPiece`.** -/
theorem map_tSegUp_ofPiece (hact : IsDpaAction q ρ) {k : ℕ} :
    ∀ (n : ℕ) (F : pieceSub L k),
      ρ (Dyck.Aq.tSegUp L q k 0 n) (ofPiece L k F) = ofPiece L k (ascPiece q k n F) := by
  intro n
  induction n with
  | zero =>
    intro F
    rw [Dyck.Aq.tSegUp_zero, hact.map_e, pieceProj_ofPiece, ascPiece_zero, LinearMap.id_apply]
  | succ n ih =>
    intro F
    rw [Dyck.Aq.tSegUp_succ, map_mul, Module.End.mul_apply, Nat.zero_add, hT, loopVstar_ofPiece,
      ih, ascPiece_succ, LinearMap.comp_apply]

omit [Invertible (q - 1)] in
include hD hU in
/-- **The commutator of the modified operators, read through the action**: this is
`HJO.Sweep.dplus_dminus_sub_dminus_dplus` transported to `ρ^♭(d_+d_- - d_-d_+)`. -/
theorem map_Delta_ofPiece (m : ℕ) (F : pieceSub L (m + 1)) :
    (toPiece L (m + 1) (ρ (Dyck.Aq.Delta L q m) (ofPiece L (m + 1) F)) : Total L)
      = (q - 1) • cmAscWord q 1 m ((auxVar (m + 1) : Total L) * F) := by
  have hq : q ≠ 0 := Invertible.ne_zero q
  have hdel : ρ (Dyck.Aq.Delta L q m) = deltaVstar (dminusModPiece q) (dplusModPiece q) m := by
    rw [Dyck.Aq.Delta, map_sub, map_mul, map_mul, hU, hD, hD, hU, deltaVstar]
  rw [hdel, deltaVstar_ofPiece, toPiece_ofPiece]
  have hcoe : ((dplusModPiece q m (dminusModPiece q m F)
        - dminusModPiece q (m + 1) (dplusModPiece q (m + 1) F) : pieceSub L (m + 1)) : Total L)
      = dplus q m (dminus q (m + 1) F) - dminus q (m + 2) (dplus q (m + 1) F) := rfl
  rw [hcoe, dplus_dminus_sub_dminus_dplus q hq m F.2, smul_eq_scal_mul]

include hact hT hD hU in
/-- **The top loop of the modified action is multiplication by the top variable**: the first half of
`HJO.Sweep.map_yElt_eq_auxMulPiece`, at `i = k`.

The proof. `HJO.Dyck.Aq.Delta_eq_wordUp` writes `(d_+d_- - d_-d_+)𝟏_k` as
`(q-1)T_{1↑k}y_k𝟏_k` in `𝔸_q`; applying `ρ^♭` and comparing with
`HJO.Sweep.dplus_dminus_sub_dminus_dplus` gives `(q-1)T_{1↑k}ρ^♭(y_k)F = (q-1)T_{1↑k}(y_kF)`; the
scalar is cancelled by `⅟(q-1)` and the word by `HJO.Sweep.cmAscWord_one_injective`. -/
theorem map_yElt_self_ofPiece (m : ℕ) (F G : pieceSub L (m + 1))
    (hG : (G : Total L) = (auxVar (m + 1) : Total L) * F) :
    ρ (Dyck.Aq.yElt L q (m + 1) (m + 1)) (ofPiece L (m + 1) F) = ofPiece L (m + 1) G := by
  have hq : q ≠ 0 := Invertible.ne_zero q
  -- the value of `ρ(y_k)` on the summand lands in the summand
  have hland : ρ (Dyck.Aq.yElt L q (m + 1) (m + 1)) (ofPiece L (m + 1) F)
      = ofPiece L (m + 1)
        (toPiece L (m + 1) (ρ (Dyck.Aq.yElt L q (m + 1) (m + 1)) (ofPiece L (m + 1) F))) := by
    have hsand :=
      hact.eq_pieceProj_mul_mul_pieceProj (Dyck.Aq.e_mul_yElt_mul_e (q := q) (m + 1) (m + 1))
    conv_lhs => rw [hsand]
    rw [Module.End.mul_apply, Module.End.mul_apply, pieceProj_ofPiece, pieceProj_apply]
  -- the commutator, computed twice
  have hcomm : Dyck.Aq.Delta L q m
      = (q - 1) • (Dyck.Aq.tSegUp L q (m + 1) 0 m * Dyck.Aq.yElt L q (m + 1) (m + 1)) := by
    have h := Dyck.Aq.Delta_eq_smul_tSegUp_mul_yElt (K := L) (q := q) (k := m + 1)
      (by omega : 1 ≤ m + 1)
    rwa [Nat.add_sub_cancel] at h
  have hleft : (toPiece L (m + 1) (ρ (Dyck.Aq.Delta L q m) (ofPiece L (m + 1) F)) : Total L)
      = (q - 1) • cmAscWord q 1 m
        (toPiece L (m + 1) (ρ (Dyck.Aq.yElt L q (m + 1) (m + 1)) (ofPiece L (m + 1) F))
          : Total L) := by
    rw [hcomm, map_smul, map_mul, LinearMap.smul_apply, Module.End.mul_apply, hland,
      map_tSegUp_ofPiece hT hact m _, map_smul, toPiece_ofPiece, SetLike.val_smul,
      coe_ascPiece q m (by omega) _, toPiece_ofPiece]
  have hright := map_Delta_ofPiece hD hU m F
  rw [hleft] at hright
  -- cancel the scalar and the word
  have hscal : cmAscWord q 1 m
        (toPiece L (m + 1) (ρ (Dyck.Aq.yElt L q (m + 1) (m + 1)) (ofPiece L (m + 1) F))
          : Total L)
      = cmAscWord q 1 m ((auxVar (m + 1) : Total L) * F) := by
    have h := congrArg (fun X : Total L => ⅟(q - 1) • X) hright
    simpa only [smul_smul, invOf_mul_self, one_smul] using h
  rw [hland]
  refine congrArg (ofPiece L (m + 1)) (Subtype.ext ?_)
  exact (cmAscWord_one_injective q hq m hscal).trans hG.symm

include hact hT hD hU in
/-- **The loops of the modified action are the variables**, read on the summand: the lemma
`HJO.Sweep.map_yElt_eq_auxMulPiece`. The downward recursion `y_i = q^{-1}T_iy_{i+1}T_i` of
`HJO.Dyck.Aq.yElt` and `HJO.Sweep.braid_auxVar_succ_mul_braid` carry the top case down. -/
theorem map_yElt_ofPiece {k : ℕ} :
    ∀ (d i : ℕ), i + d = k → 1 ≤ i → ∀ F G : pieceSub L k,
      (G : Total L) = (auxVar i : Total L) * F →
      ρ (Dyck.Aq.yElt L q k i) (ofPiece L k F) = ofPiece L k G := by
  intro d
  induction d with
  | zero =>
    intro i hik h1 F G hG
    obtain ⟨m, hm⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
    subst hm
    obtain rfl : i = m + 1 := by omega
    exact map_yElt_self_ofPiece hact hT hD hU m F G hG
  | succ d ih =>
    intro i hik h1 F G hG
    have hlt : i < k := by omega
    have hmem : braid q i (F : Total L) ∈ piece L k :=
      braid_mem_piece q h1 hlt F.2
    set F' : pieceSub L k := braidModPiece q k (i - 1) F with hF'
    have hF'coe : (F' : Total L) = braid q i (F : Total L) := by
      have h := coe_braidModPiece q (show i - 1 + 2 ≤ k from by omega) F
      rwa [show i - 1 + 1 = i from by omega] at h
    have hmem' : (auxVar (i + 1) : Total L) * braid q i (F : Total L) ∈ pieceSub L k :=
      show (auxVar (i + 1) : Total L) * braid q i (F : Total L) ∈ piece L k from
        mul_mem (auxVar_mem_piece (show 1 ≤ i + 1 by omega) (show i + 1 ≤ k by omega)) hmem
    set G' : pieceSub L k :=
      ⟨(auxVar (i + 1) : Total L) * braid q i (F : Total L), hmem'⟩ with hG'
    have hstep : ρ (Dyck.Aq.yElt L q k (i + 1)) (ofPiece L k F') = ofPiece L k G' :=
      ih (i + 1) (by omega) (by omega) F' G' (by rw [hG', hF'coe])
    have hTi : ρ (Dyck.Aq.Tg L q k (i - 1)) (ofPiece L k F) = ofPiece L k F' := by
      rw [hT, loopVstar_ofPiece]
    have hTi' : ρ (Dyck.Aq.Tg L q k (i - 1)) (ofPiece L k G')
        = ofPiece L k (braidModPiece q k (i - 1) G') := by
      rw [hT, loopVstar_ofPiece]
    have hconj : (braidModPiece q k (i - 1) G' : Total L)
        = scal q * (auxVar i : Total L) * F := by
      have h := coe_braidModPiece q (show i - 1 + 2 ≤ k from by omega) G'
      rw [show i - 1 + 1 = i from by omega] at h
      rw [h, hG']
      exact braid_auxVar_succ_mul_braid q h1 (F : Total L)
    rw [Dyck.Aq.yElt_recursion h1 hlt, map_smul, map_mul, map_mul, LinearMap.smul_apply,
      Module.End.mul_apply, Module.End.mul_apply, hTi, hstep, hTi', ← map_smul]
    refine congrArg (ofPiece L k) (Subtype.ext ?_)
    rw [SetLike.val_smul, hconj, hG, ← smul_eq_scal_mul, smul_mul_assoc, smul_smul,
      invOf_mul_self, one_smul]

include hact hT hD hU in
/-- **The loops of the modified action are the variables**, the lemma
`HJO.Sweep.map_yElt_eq_auxMulPiece`: for `k ≥ 1` and `1 ≤ i ≤ k` the operator `ρ^♭(y_i)` is
multiplication by `y_i` on `V_k` and `0` on every other summand, which is what it means for it to be
"multiplication by `y_i`" as an operator on `V_k`. -/
@[hjo "lem_vmod_y_multiplication"]
theorem map_yElt_eq_auxMulPiece {k i : ℕ} (h1 : 1 ≤ i) (hik : i ≤ k) :
    ρ (Dyck.Aq.yElt L q k i) = loopVstar (auxMulPiece L) k i := by
  refine vstar_ext fun l F => ?_
  rcases eq_or_ne k l with rfl | hl
  · rw [loopVstar_ofPiece]
    exact map_yElt_ofPiece hact hT hD hU (k - i) i (by omega) h1 F (auxMulPiece L k i F)
      (coe_auxMulPiece h1 hik F)
  · rw [loopVstar_ofPiece_of_ne i (Ne.symm hl),
      hact.apply_ofPiece_of_ne (Ne.symm hl) (Dyck.Aq.e_mul_yElt_mul_e (q := q) k i) F]

end YMul

end HJO.Sweep

end
