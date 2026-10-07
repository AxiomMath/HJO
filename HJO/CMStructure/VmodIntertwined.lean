/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.CMStructure.MellitDpaAction
public import HJO.CMStructure.MellitZLoops
public import HJO.CMStructure.MellitZrelShift
public import HJO.CMStructure.StarZrelOne
public import HJO.CMStructure.VmodYMultiplication
public import HJO.Shuffle.DpaIntertwined
public import HJO.Shuffle.SlopeActions
public meta import HJO.Attr

/-! # The modified pair is correctly intertwined

`HJO.Sweep.exists_isIntertwinedPair_vmod`: the pair `(ρ^♭, ρ^{♭*})` of
`HJO.Sweep.exists_isDpaAction_mod` and `HJO.Sweep.exists_isDpaAction_mellit` is correctly
intertwined in the sense of `HJO.Sweep.IsIntertwinedPair`.

## Which `d_-` convention each side uses — both sides use Mellit's, and that is forced

`HJO.Sweep.IsIntertwinedPair`'s second condition is `ρ^*(d_-) = ρ(d_-)`: the two actions must send
the lowering arrow to the **same** operator. There are two lowering operators in play and they are
not interchangeable — Mellit's `d^♭_-` (`HJO.Sweep.dminus`, pairing `F_j` with `e_j`) and Carlsson
and Mellit's `d_-` (`HJO.Sweep.dminusCM`, pairing `F_j` with `e_{j+1}`) —
so the condition decides the convention of the whole pair, and it decides it in Mellit's favour:
`HJO.Sweep.exists_isDpaAction_mod` sends `d_-` to `HJO.Sweep.dminusModPiece`, which restricts
`HJO.Sweep.dminus`.

So the starred half must be `HJO.Sweep.exists_isDpaAction_mellit`, whose
lowering arrow is the same `HJO.Sweep.dminusModPiece`, and **not**
`HJO.Sweep.exists_isDpaAction_star`, which has the same loops and the same raising arrow `d^*_+` but
Carlsson and Mellit's own `d_-`. The two are genuinely different actions:
`HJO.Sweep.dminusCM_eq_neg_dminus_auxVar_mul` relates the operators only after multiplication by the
last variable, and multiplication by `y_{k+1}` is injective but not surjective on `V_{k+1}`, so a
relation known for one at every argument constrains the other only on the ideal `(y_{k+1})`.

Consequently the commutator of `d^*_+` with the lowering arrow is `HJO.Sweep.starComm` throughout
this file and never `HJO.Sweep.starCommCM`, and the `z_i` are `HJO.Sweep.zop` — which is what
`HJO.Sweep.zopOneStar`, `HJO.Sweep.zop` and `HJO.Sweep.zRep` are built on. The raising arrows are
the two different ones the definition intends: `ρ^♭(d_+) = d^♭_+` (`HJO.Sweep.dplus`) and
`ρ^{♭*}(d_+) = d^*_+` (`HJO.Sweep.dplusStar`).

## Main results

* `HJO.Sweep.map_yElt_ofPiece_mellitInv` — `HJO.Sweep.map_yElt_ofPiece_mellit` at the base `⅟q`,
  which is the base `HJO.Sweep.IsIntertwinedPair` reads.
* `HJO.Sweep.map_Tg_star_vmod`, `HJO.Sweep.map_dMinus_star_vmod`,
  `HJO.Sweep.dPlusStar_mul_yElt_vmod`, `HJO.Sweep.zElt_one_mul_dPlus_vmod` — four of the five
  conditions of `HJO.Sweep.IsIntertwinedPair`, discharged outright.
* `HJO.Sweep.isIntertwinedPair_vmod`, `HJO.Sweep.exists_isIntertwinedPair_vmod` — the main result.
* `HJO.Sweep.exists_slopeActions_vmod` — `HJO.Sweep.exists_slopeActions` at the modified pair, i.e.
  its base-pair hypothesis discharged.

## Where each of the five conditions comes from

* `ρ^*(T_i) = ρ(T̂_i)` — `HJO.Sweep.braidInv_apply` and `invOf_eq_inv`. Not quite "by construction":
  `HJO.Sweep.IsIntertwinedPair` asks for `ρ^*(T_i) = ρ(T̂_i)` with `T̂_i` the *polynomial*
  inverse of `HJO.Dyck.braidInvGen`, an element of the algebra, while
  `HJO.Sweep.exists_isDpaAction_mellit` supplies the *operator* `HJO.Sweep.braidInv`; matching them
  is the identity `T_i^{-1} = q^{-1}(T_i + (q-1))`.
* `ρ^*(d_-) = ρ(d_-)` — both are `HJO.Sweep.dminusModPiece`; see above. This one *is* by
  construction.
* `d^*_+y_i = y_{i+1}d^*_+` — `HJO.Sweep.map_yElt_eq_auxMulPiece` and
  `HJO.Sweep.dplusStar_braidInv`'s third clause.
* `z_1d^♭_+ = -uq^{k+1}y_1d^*_+` — `HJO.Sweep.zopOneStar_dplus`, the relation in its *matched
  Mellit* reading, which carries exactly this scalar.
* `d^♭_+z_i = z_{i+1}d^♭_+` — `HJO.Sweep.dplus_zop`
  (`HJO/CMStructure/MellitZrelShift.lean`), the one genuinely new piece of mathematics the
  lemma needs. Its all-Carlsson--Mellit reading is proved separately
  (`HJO.Sweep.trainDown_starCommCM_trainUp_cmDPlus`, `HJO.Sweep.starCommCM_cmDPlus`) and is **not**
  this statement: both the commutator and the raising operator differ, `starCommCM` against
  `starComm` and `cmDPlus` against `dplus`. What makes the same argument go through, rather than a
  transport, is that `HJO.Sweep.cmAscWord q a b` *is* `HJO.Sweep.trainUpEnd q a (b+1)`, so `d^♭_+`
  and `d_+` carry the identical braid word and differ only by the sign and the letter `y_{k+1}`.

## `HJO.Standing.exists_action_atilde_ker_eq_param` is not used, in either half

The argument for this lemma as usually written gets the two `z`
conditions from `HJO.Standing.exists_action_atilde_ker_eq_param` "for the *old* raising operator"
and then substitutes twice. Nothing here does: the fifth condition comes from
`HJO.Sweep.zopOneStar_dplus`'s Mellit reading directly, and no action of `HJO.Dyck.Tilde.Atilde`'s
`Ã` is constructed or consumed anywhere in this file, and neither is
`HJO.Sweep.exists_action_atilde`. So neither the action half nor the kernel half of
`HJO.Standing.exists_action_atilde_ker_eq_param` is on this lemma's path.

## Side conditions not in the statement as usually given

`q ≠ 0` and `q ≠ 1`, carried as `Invertible q` and `Invertible (q - 1)` exactly as
`HJO.Sweep.IsIntertwinedPair` itself carries them — its corner elements divide by `q` and by
`base - 1` and do not exist otherwise — and `q + 1 ≠ 0`, inherited from
`HJO.Sweep.exists_isDpaAction_mellit` and through it from `HJO.Sweep.dminusCM_starCommCM_braidInv`.
`q ≠ 1` is additionally load-bearing in `HJO.Sweep.zopOneStar_dplus`: Lean makes `x/0 = 0`, so at
`q = 1` the prefactor `q^k/(1-q)` of `HJO.Sweep.zop` collapses and the fifth condition would be
silently false rather than ill-typed. Every consumer instantiates at parameters algebraically
independent over `ℤ`, where all three hold.

## References

A. Mellit, *Toric braids and `(m, n)`-parking functions*, §3. -/

@[expose] public section

namespace HJO.Sweep

section Bridge

variable {L : Type*} [Field L] [Algebra ℚ L] {q u : L}

set_option linter.style.haveILetI false in
/-- **`HJO.Sweep.map_yElt_ofPiece_mellit` read at the base `⅟q`.**

`HJO/CMStructure/MellitZLoops.lean` states the identification `ρ^{♭*}(y_i) = z_i` for an action
out of `HJO.Dyck.Aq L q⁻¹`, while `HJO.Sweep.IsIntertwinedPair` takes its second action out of
`HJO.Dyck.AqInv L q`, which is `HJO.Dyck.Aq L ⅟q`. Those two base scalars are equal
(`invOf_eq_inv`) and not syntactically so, and the corner elements `HJO.Dyck.Aq.yElt` are *data*
built from `⅟(base - 1)`, so the two readings are two terms and the bridge has to be made
explicitly. It is made by replacing the ambient `Invertible q` with `invertibleOfNonzero`, under
which `⅟q` reduces to `q⁻¹`; `Invertible` is a subsingleton in a monoid, so the replacement is an
equality of instances and nothing is assumed.

`letI` rather than `have` for the four instances, against the style linter, and the reason is not
cosmetic: `Invertible` is a *data* class, the goal's corner element is
`@Dyck.Aq.yElt L _ (⅟q) invertibleInvOf Dyck.invertibleInvOfSubOne k i` with those instances
elaborated at the substituted base, and an opaque `have` would put a fresh free variable there
instead of the term the goal names, so the two corner elements would no longer be the same term. -/
theorem map_yElt_ofPiece_mellitInv (q u : L) (hq : q ≠ 0) (hq1 : q ≠ 1) [iq : Invertible q]
    [iq1 : Invertible (q - 1)] {ρ' : Dyck.Aq L (⅟q) →ₐ[L] Module.End L (Vstar L)}
    (hact : IsDpaAction (⅟q) ρ')
    (hT : ∀ k i : ℕ, ρ' (Dyck.Aq.Tg L (⅟q) k i) = loopVstar (braidInvModPiece q) k i)
    (hD : ∀ k : ℕ, ρ' (Dyck.Aq.dMinus L (⅟q) k) = lowerVstar (dminusModPiece q) k)
    (hU : ∀ k : ℕ, ρ' (Dyck.Aq.dPlus L (⅟q) k) = raiseVstar (dplusStarPiece q u) k)
    {k : ℕ} (d i : ℕ) (hik : i + d = k) (h1 : 1 ≤ i) (F G : pieceSub L k)
    (hG : (G : Total L) = zop q u k i F) :
    ρ' (Dyck.Aq.yElt L (⅟q) k i) (ofPiece L k F) = ofPiece L k G := by
  obtain rfl : iq = invertibleOfNonzero hq := Subsingleton.elim _ _
  obtain rfl : iq1 = invertibleOfNonzero (sub_ne_zero_of_ne hq1) := Subsingleton.elim _ _
  letI : Invertible q := invertibleOfNonzero hq
  letI : Invertible (q - 1) := invertibleOfNonzero (sub_ne_zero_of_ne hq1)
  letI : Invertible (q⁻¹ : L) := invertibleInvOf (a := q)
  letI : Invertible (q⁻¹ - 1 : L) := Dyck.invertibleInvOfSubOne (q := q)
  exact map_yElt_ofPiece_mellit hact hT hD hU hq hq1 d i hik h1 F G hG

end Bridge

/-! ### The five conditions -/

section Pair

variable {L : Type*} [Field L] [Algebra ℚ L] {q u : L} [Invertible q] [Invertible (q - 1)]
  {ρ : Dyck.Aq L q →ₐ[L] Module.End L (Vstar L)}
  {ρ' : Dyck.Aq L (⅟q) →ₐ[L] Module.End L (Vstar L)}

variable (hact : IsDpaAction q ρ)
  (hT : ∀ k i : ℕ, ρ (Dyck.Aq.Tg L q k i) = loopVstar (braidModPiece q) k i)
  (hD : ∀ k : ℕ, ρ (Dyck.Aq.dMinus L q k) = lowerVstar (dminusModPiece q) k)
  (hU : ∀ k : ℕ, ρ (Dyck.Aq.dPlus L q k) = raiseVstar (dplusModPiece q) k)
  (hact' : IsDpaAction (⅟q) ρ')
  (hT' : ∀ k i : ℕ, ρ' (Dyck.Aq.Tg L (⅟q) k i) = loopVstar (braidInvModPiece q) k i)
  (hD' : ∀ k : ℕ, ρ' (Dyck.Aq.dMinus L (⅟q) k) = lowerVstar (dminusModPiece q) k)
  (hU' : ∀ k : ℕ, ρ' (Dyck.Aq.dPlus L (⅟q) k) = raiseVstar (dplusStarPiece q u) k)

omit [Algebra ℚ L] [Invertible (q - 1)] in
include hact hT hT' in
/-- **The first condition of `HJO.Sweep.IsIntertwinedPair` for the modified pair**: `ρ^{♭*}(T_i)` is
`ρ^♭(T̂_i)`, the image of `HJO.Dyck.braidInvGen`'s polynomial inverse. Both sides are read off the
two actions and what is left is `HJO.Sweep.braidInv_apply`, the definition of `T_i^{-1}` as
`q^{-1}(T_i + (q-1))`, together with `invOf_eq_inv`. -/
theorem map_Tg_star_vmod {k s : ℕ} (hs : s + 2 ≤ k) :
    ρ' (Dyck.Aq.Tg L (⅟q) k s) = ρ (Dyck.Aq.Tinv L q k s) := by
  rw [hT', Dyck.Aq.Tinv_eq, map_smul, map_add, map_smul, hT, hact.map_e]
  refine vstar_ext fun l F => ?_
  rcases eq_or_ne k l with rfl | hl
  · rw [loopVstar_ofPiece, LinearMap.smul_apply, LinearMap.add_apply, LinearMap.smul_apply,
      loopVstar_ofPiece, pieceProj_ofPiece, ← map_smul, ← map_add, ← map_smul]
    refine ofPiece_congr ?_
    rw [coe_braidInvModPiece q hs, SetLike.val_smul, AddMemClass.coe_add, SetLike.val_smul,
      coe_braidModPiece q hs, braidInv_apply, smul_eq_scal_mul, smul_eq_scal_mul, invOf_eq_inv]
  · rw [loopVstar_ofPiece_of_ne s (Ne.symm hl), LinearMap.smul_apply, LinearMap.add_apply,
      LinearMap.smul_apply, loopVstar_ofPiece_of_ne s (Ne.symm hl),
      pieceProj_ofPiece_of_ne (Ne.symm hl), smul_zero, add_zero, smul_zero]

omit [Invertible (q - 1)] in
include hD hD' in
/-- **The second condition of `HJO.Sweep.IsIntertwinedPair` for the modified pair**: `ρ^{♭*}(d_-)`
is `ρ^♭(d_-)`. Both are `HJO.Sweep.dminusModPiece` — Mellit's `d^♭_-` of `HJO.Sweep.dminus` — and
this is the whole reason `HJO.Sweep.exists_isDpaAction_mellit` and not
`HJO.Sweep.exists_isDpaAction_star` is the starred half of the pair: the all-Carlsson--Mellit
action sends `d_-` to `HJO.Sweep.dminusCM` instead, and
`HJO.Sweep.dminusCM_eq_neg_dminus_auxVar_mul` relates the two only after multiplication by the last
variable. -/
theorem map_dMinus_star_vmod (k : ℕ) :
    ρ' (Dyck.Aq.dMinus L (⅟q) k) = ρ (Dyck.Aq.dMinus L q k) := by
  rw [hD', hD]

include hact hT hD hU hU' in
/-- **The fourth condition of `HJO.Sweep.IsIntertwinedPair` for the modified pair**:
`d^*_+y_i = y_{i+1}d^*_+`. The loops of the unstarred action are multiplication by the variables
(`HJO.Sweep.map_yElt_eq_auxMulPiece`), and the cyclic shift inside `d^*_+` raises the index of the
variable by one (`HJO.Sweep.dplusStar_braidInv`'s third clause). -/
theorem dPlusStar_mul_yElt_vmod {k i : ℕ} (h1 : 1 ≤ i) (hik : i ≤ k) :
    ρ' (Dyck.Aq.dPlus L (⅟q) k) * ρ (Dyck.Aq.yElt L q k i)
      = ρ (Dyck.Aq.yElt L q (k + 1) (i + 1)) * ρ' (Dyck.Aq.dPlus L (⅟q) k) := by
  rw [hU', map_yElt_eq_auxMulPiece hact hT hD hU h1 hik,
    map_yElt_eq_auxMulPiece hact hT hD hU (show 1 ≤ i + 1 by omega)
      (show i + 1 ≤ k + 1 by omega)]
  refine vstar_ext fun l F => ?_
  simp only [Module.End.mul_apply]
  rcases eq_or_ne k l with rfl | hl
  · rw [loopVstar_ofPiece, raiseVstar_ofPiece, raiseVstar_ofPiece, loopVstar_ofPiece]
    refine ofPiece_congr ?_
    rw [coe_auxMulPiece (show 1 ≤ i + 1 by omega) (show i + 1 ≤ k + 1 by omega),
      coe_dplusStarPiece, coe_dplusStarPiece, coe_auxMulPiece h1 hik]
    exact dplusStar_auxVar_mul q u h1 hik (F : Total L)
  · rw [loopVstar_ofPiece_of_ne i (Ne.symm hl), raiseVstar_ofPiece_of_ne (Ne.symm hl), map_zero,
      map_zero]

include hact hT hD hU hact' hT' hD' hU' in
/-- **The fifth condition of `HJO.Sweep.IsIntertwinedPair` for the modified pair**:
`z_1d^♭_+ = -uq^{k+1}y_1d^*_+`.

This is `HJO.Sweep.zopOneStar_dplus`, the relation in its *matched Mellit* reading, proved with
exactly this scalar: the `z_1` of `HJO.Sweep.zop` — built on
`HJO.Sweep.starComm`, the commutator of `d^*_+` with Mellit's `d^♭_-` — against the modified raising
operator `d^♭_+` of `HJO.Sweep.dplus_eq_ascWord`. Pairing that `z_1` with `HJO.Sweep.cmDPlus`'s
`d_+` instead gives a false identity; see `HJO/CMStructure/StarZrelOne.lean`. The identification
of `ρ^{♭*}(y_1)` with `z_1` is `HJO.Sweep.exists_isDpaAction_mellit`'s own corner family,
`HJO.Sweep.map_yElt_ofPiece_mellitInv`. -/
theorem zElt_one_mul_dPlus_vmod (hq1 : q ≠ 1) (k : ℕ) :
    ρ' (Dyck.Aq.yElt L (⅟q) (k + 1) 1) * ρ (Dyck.Aq.dPlus L q k)
      = (-(u * q ^ (k + 1))) • (ρ (Dyck.Aq.yElt L q (k + 1) 1)
          * ρ' (Dyck.Aq.dPlus L (⅟q) k)) := by
  have hq : q ≠ 0 := Invertible.ne_zero q
  rw [hU, hU', map_yElt_eq_auxMulPiece hact hT hD hU (le_refl 1) (show 1 ≤ k + 1 by omega)]
  refine vstar_ext fun l F => ?_
  simp only [Module.End.mul_apply, LinearMap.smul_apply]
  rcases eq_or_ne k l with rfl | hl
  · have hmem : dplus q k (F : Total L) ∈ piece L (k + 1) := dplus_mem_piece q k F.2
    have hz : zopOneStar q u (k + 1) (dplus q k (F : Total L))
        ∈ pieceSub L (k + 1) := zop_mem_piece q u 1 le_rfl (by omega) hmem
    rw [raiseVstar_ofPiece,
      map_yElt_ofPiece_mellitInv q u hq hq1 hact' hT' hD' hU' k 1 (by omega) le_rfl
        (dplusModPiece q k F) ⟨_, hz⟩ rfl,
      raiseVstar_ofPiece, loopVstar_ofPiece, ← map_smul]
    have hcoe : ((⟨_, hz⟩ : pieceSub L (k + 1)) : Total L)
        = zopOneStar q u (k + 1) (dplus q k (F : Total L)) := rfl
    refine ofPiece_congr ?_
    rw [SetLike.val_smul, smul_eq_scal_mul,
      coe_auxMulPiece (le_refl 1) (show 1 ≤ k + 1 by omega), coe_dplusStarPiece, hcoe,
      zopOneStar_dplus q u hq hq1 F.2, smul_eq_scal_mul, ← mul_assoc]
  · rw [raiseVstar_ofPiece_of_ne (Ne.symm hl), raiseVstar_ofPiece_of_ne (Ne.symm hl), map_zero,
      map_zero, smul_zero]

/-! ### The pair is correctly intertwined -/

include hact hT hD hU hact' hT' hD' hU' in
/-- **The modified pair is correctly intertwined**, `HJO.Sweep.exists_isIntertwinedPair_vmod`,
stated for any two actions carrying the generator values of `HJO.Sweep.exists_isDpaAction_mod` and
`HJO.Sweep.exists_isDpaAction_mellit` rather than for one chosen witness.

The five conditions of `HJO.Sweep.IsIntertwinedPair` are the four lemmas above together with
`HJO.Sweep.dplus_zop`, which is the first mixed relation `d_+z_i = z_{i+1}d_+` read in the Mellit
convention; the file header says where each comes from. -/
theorem isIntertwinedPair_vmod (hq1 : q ≠ 1) : IsIntertwinedPair q u ρ ρ' where
  isAction := hact
  isActionStar := hact'
  map_Tg_star _ _ hs := map_Tg_star_vmod hact hT hT' hs
  map_dMinus_star := map_dMinus_star_vmod hD hD'
  dPlus_mul_zElt := by
    have hq : q ≠ 0 := Invertible.ne_zero q
    intro k i h1 hik
    rw [hU]
    refine vstar_ext fun l F => ?_
    simp only [Module.End.mul_apply]
    rcases eq_or_ne k l with rfl | hl
    · have hzk : zop q u k i (F : Total L) ∈ pieceSub L k := zop_mem_piece q u i h1 hik F.2
      have hmem : dplus q k (F : Total L) ∈ piece L (k + 1) := dplus_mem_piece q k F.2
      have hzk' : zop q u (k + 1) (i + 1) (dplus q k (F : Total L)) ∈ pieceSub L (k + 1) :=
        zop_mem_piece q u (i + 1) (by omega) (by omega) hmem
      rw [map_yElt_ofPiece_mellitInv q u hq hq1 hact' hT' hD' hU' (k - i) i (by omega) h1 F
          ⟨_, hzk⟩ rfl,
        raiseVstar_ofPiece, raiseVstar_ofPiece,
        map_yElt_ofPiece_mellitInv q u hq hq1 hact' hT' hD' hU' (k - i) (i + 1) (by omega)
          (by omega) (dplusModPiece q k F) ⟨_, hzk'⟩ rfl]
      refine ofPiece_congr ?_
      exact dplus_zop q u hq h1 hik F.2
    · rw [raiseVstar_ofPiece_of_ne (Ne.symm hl),
        hact'.apply_ofPiece_of_ne (Ne.symm hl) (Dyck.Aq.e_mul_yElt_mul_e (q := (⅟q : L)) k i) F,
        map_zero, map_zero]
  dPlusStar_mul_yElt _ _ h1 hik := dPlusStar_mul_yElt_vmod hact hT hD hU hU' h1 hik
  zElt_one_mul_dPlus := zElt_one_mul_dPlus_vmod hact hT hD hU hact' hT' hD' hU' hq1

end Pair

/-! ### The existence statement, and the base pair of `HJO.Sweep.exists_slopeActions` -/

section Node

variable {L : Type*} [Field L] [Algebra ℚ L]

/-- **The modified pair exists and is correctly intertwined**,
`HJO.Sweep.exists_isIntertwinedPair_vmod`, the fifth condition coming from the operator identity
`d^♭_+z_i = z_{i+1}d^♭_+` of `HJO.Sweep.dplus_zop`.

The four generator clauses pin the pair down as *the* pair of `HJO.Sweep.exists_isDpaAction_mod` and
`HJO.Sweep.exists_isDpaAction_mellit` rather than merely some intertwined pair, which is what the
statement asserts and what `HJO.Sweep.exists_slopeActions` needs in order to read `ρ_{0,1} = ρ^♭`
and `ρ^*_{1,0} = ρ^{♭*}`. -/
@[hjo "lem_vmod_intertwined"]
theorem exists_isIntertwinedPair_vmod (q u : L) [Invertible q] [Invertible (q - 1)]
    (hq1' : q + 1 ≠ 0) :
    ∃ (ρ : Dyck.Aq L q →ₐ[L] Module.End L (Vstar L))
      (ρ' : Dyck.AqInv L q →ₐ[L] Module.End L (Vstar L)),
      IsIntertwinedPair q u ρ ρ'
        ∧ (∀ k i : ℕ, ρ (Dyck.Aq.Tg L q k i) = loopVstar (braidModPiece q) k i)
        ∧ (∀ k : ℕ, ρ (Dyck.Aq.dMinus L q k) = lowerVstar (dminusModPiece q) k)
        ∧ (∀ k : ℕ, ρ (Dyck.Aq.dPlus L q k) = raiseVstar (dplusModPiece q) k)
        ∧ (∀ k i : ℕ, ρ' (Dyck.Aq.Tg L (⅟q) k i) = loopVstar (braidInvModPiece q) k i)
        ∧ (∀ k : ℕ, ρ' (Dyck.Aq.dMinus L (⅟q) k) = lowerVstar (dminusModPiece q) k)
        ∧ (∀ k : ℕ, ρ' (Dyck.Aq.dPlus L (⅟q) k) = raiseVstar (dplusStarPiece q u) k) := by
  have hq : q ≠ 0 := Invertible.ne_zero q
  have hq1 : q ≠ 1 := fun h => Invertible.ne_zero (q - 1) (by rw [h, sub_self])
  obtain ⟨ρ, hact, hT, hD, hU⟩ := exists_isDpaAction_mod q hq
  obtain ⟨ρ', hact', hT', hD', hU'⟩ := exists_isDpaAction_mellitInv q u hq1'
  exact ⟨ρ, ρ', isIntertwinedPair_vmod hact hT hD hU hact' hT' hD' hU' hq1,
    hT, hD, hU, hT', hD', hU'⟩

/-- **The base pair of `HJO.Sweep.exists_slopeActions`, discharged.**

`HJO.Sweep.exists_slopeActions` is stated parametrised over its base
intertwined pair. This instantiates it at the modified pair, which gives the statement
`ρ_{0,1} = ρ^♭` and
`ρ^*_{1,0} = ρ^{♭*}` for the two actions of `HJO.Sweep.exists_isDpaAction_mod` and
`HJO.Sweep.exists_isDpaAction_mellit`. -/
theorem exists_slopeActions_vmod (q u : L) [Invertible q] [Invertible (q - 1)]
    (hq1' : q + 1 ≠ 0) (c : L) :
    ∃ (ρb : Dyck.Aq L q →ₐ[L] Module.End L (Vstar L))
      (ρb' : Dyck.AqInv L q →ₐ[L] Module.End L (Vstar L))
      (R : ℕ × ℕ → (Dyck.Aq L q →ₐ[L] Module.End L (Vstar L)))
      (R' : ℕ × ℕ → (Dyck.AqInv L q →ₐ[L] Module.End L (Vstar L))),
      (∀ k i : ℕ, ρb (Dyck.Aq.Tg L q k i) = loopVstar (braidModPiece q) k i)
      ∧ (∀ k : ℕ, ρb (Dyck.Aq.dMinus L q k) = lowerVstar (dminusModPiece q) k)
      ∧ (∀ k : ℕ, ρb (Dyck.Aq.dPlus L q k) = raiseVstar (dplusModPiece q) k)
      ∧ (∀ k i : ℕ, ρb' (Dyck.Aq.Tg L (⅟q) k i) = loopVstar (braidInvModPiece q) k i)
      ∧ (∀ k : ℕ, ρb' (Dyck.Aq.dMinus L (⅟q) k) = lowerVstar (dminusModPiece q) k)
      ∧ (∀ k : ℕ, ρb' (Dyck.Aq.dPlus L (⅟q) k) = raiseVstar (dplusStarPiece q u) k)
      ∧ R (0, 1) = ρb ∧ R' (0, 1) = ρb' ∧ R (1, 0) = ρb ∧ R' (1, 0) = ρb'
      ∧ (∀ p : ℕ × ℕ, IsDpaAction q (R p))
      ∧ (∀ p : ℕ × ℕ, IsDpaAction (⅟q) (R' p))
      ∧ (∀ p p' : ℕ × ℕ, Mellit.IsUnimodular p p' →
          IsIntertwinedPair q u (R p) (R' p')
            ∧ IsReplicated c (R p) (R' p') (R (p.1 + p'.1, p.2 + p'.2))
            ∧ IsReplicatedStar (R p) (R' p') (R' (p.1 + p'.1, p.2 + p'.2)))
      ∧ (∀ m n : ℕ, Nat.Coprime m n → (m, n) ≠ (0, 1) → (m, n) ≠ (1, 0) →
          ∃ p p' : ℕ × ℕ, Mellit.IsUnimodular p p' ∧ m = p.1 + p'.1 ∧ n = p.2 + p'.2
            ∧ IsIntertwinedPair q u (R p) (R' p')
            ∧ IsReplicated c (R p) (R' p') (R (m, n))
            ∧ IsReplicatedStar (R p) (R' p') (R' (m, n))) := by
  obtain ⟨ρb, ρb', hpair, hT, hD, hU, hT', hD', hU'⟩ :=
    exists_isIntertwinedPair_vmod q u hq1'
  obtain ⟨R, R', h1, h2, h3, h4, h5, h6, h7, h8⟩ := exists_slopeActions hpair c
  exact ⟨ρb, ρb', R, R', hT, hD, hU, hT', hD', hU', h1, h2, h3, h4, h5, h6, h7, h8⟩

end Node

end HJO.Sweep

end
