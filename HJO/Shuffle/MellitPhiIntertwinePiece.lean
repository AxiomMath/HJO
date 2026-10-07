/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.CMStructure.MellitBraidRep
public import HJO.CMStructure.ZyMixed
public import HJO.Shuffle.MellitPhiIntertwine
public meta import HJO.Attr

/-! # The index-raising diagram at the codomain

`HJO.Sweep.braidRep_phiPlusStar_comp_negYOneDPlusStarPiece` is the first of the two commutative
diagrams of Mellit's Section 5.5: for `B ∈ 𝔹^+_k(𝕋_0)`,

`π_{k+1}(φ^*_+(B)) ∘ (-y_1d^*_+) = (-y_1d^*_+) ∘ π_k(B)`

as maps `V_k → V_{k+1}`. This file states it there — between the graded pieces, with `π` the
`HJO.Sweep.braidRep` of `HJO.Sweep.braidRep` — rather than on `HJO.Sweep.Total`.

## Why the total-space form could not be the statement

`HJO/Shuffle/MellitPhiIntertwine.lean` proves the diagram on `HJO.Sweep.Total` from the four
letters of `HJO.Braid.braidGenT`, but its assembled form
`HJO.Sweep.braidRepTotal_phiPlusStar_mul_negYOneDPlusStar` carries two
`HJO.Sweep.BraidRepRespectsTotal` hypotheses, and at rank `≥ 2`
`HJO.Sweep.braidRepRespectsTotal_two_false` refutes that predicate: the statement is vacuous for
every `k ≥ 1`, which is its whole range. Retyping is therefore not a matter of taste.

At the graded piece `HJO.Sweep.BraidRepRespects` — the predicate `HJO.Sweep.braidRep` is actually
typed at — is not refuted, and `HJO.Sweep.braidRepRespects_mellit` proves
it outright, so the statement has content and nothing is left owed.

## How the `z` letter is discharged, and why the obvious route fails

Three of the four letters of `HJO.Braid.braidGenT` are relations between `d^*_+` and
a *multiplication* operator, hence one-line consequences of `cy_{k+1}(y_i) = y_{i+1}`; they are
proved on `HJO.Sweep.Total` in `HJO/Shuffle/MellitPhiIntertwine.lean` and read off here. The
relation for `z_i` looks as though it were of the same kind. It is not: `z_1` is by `HJO.Sweep.zop`
the commutator `[d^*_+, d^♭_-]` followed by a train.

The route through `HJO.Sweep.zopOneStar_dplus` reduces that letter to `HJO.Sweep.starCommCM_cmDPlus`
at `i = 1` in the convention `HJO.Sweep.zop` is written in, and **that is not available**: the
relation is proved only in the Carlsson--Mellit convention
(`HJO.Sweep.trainDown_starCommCM_trainUp_cmDPlus`), and
`HJO.Sweep.starCommCM_eq_neg_starComm_auxVar_mul` inserts `(y_k \cdot)` between the commutator and
the train of `z_1`, where `HJO.Sweep.mulLeft_auxVar_two_not_comm_trainUpEnd` shows it cannot be
moved. That route also needs `z_1z_2 = z_2z_1`, whose total-space form is refuted
(`HJO.Sweep.zop_two_not_comm`).

What works instead uses no `d_-` reconciliation and no commutation. `d^*_+` **is** the raising
operator of the Dyck path algebra in Mellit's own convention — the triple `(T_i^{-1}, d^♭_-, d^*_+)`
at the scalar `q^{-1}` of `HJO.Sweep.isDpaOperators_mellit` — and
`HJO.Sweep.map_yElt_ofPiece_mellit` identifies the `z_i` with that algebra's corner elements. So
the `z` letter is:

* `HJO.Dyck.Aq.dPlus_mul_yElt_one`, transported — the only step that
  touches the commutator, and it touches it inside the abstract algebra;
* the mixed relation of `HJO.Braid.BraidMonoid`, `z_1T_1y_1\bar T_1 = y_2z_1`, which absorbs the
  `T_1` of `HJO.Sweep.zop`'s recursion;
* `HJO.Sweep.braid_auxVar_succ_mul_braid` as `y_2 = qT_1^{-1}y_1T_1^{-1}`.

## Main definitions

* `HJO.Braid.phiPlusFreeWord` — `HJO.Braid.phiPlusStar` lifted to the free monoid, so that the
  diagram can be checked with no well-definedness hypothesis at either rank.
* `HJO.Sweep.negYOneDPlusStarPiece` — the vertical arrow `-y_1d^*_+` as a map `V_k → V_{k+1}`.

## Main results

* `HJO.Sweep.dplusStar_zop_one_of_mellitAction` — `d^*_+z_1^{(k)} = T_1^{-1}z_1^{(k+1)}T_1d^*_+`.
* `HJO.Sweep.zRep_two_comp_negYOneDPlusStarPiece` — the `z` letter.
* `HJO.Sweep.braidRepFree_phiPlusFreeWord_comp_negYOneDPlusStarPiece` — the diagram at the free
  level, with no well-definedness hypothesis at all.
* `HJO.Sweep.braidRep_phiPlusStar_comp_negYOneDPlusStarPiece` — the main result; and
  `HJO.Sweep.braidRep_phiPlusStar_comp_mellit`, the same with `HJO.Sweep.braidRep`'s argument
  discharged.

## References

A. Mellit, *Toric braids and `(m, n)`-parking functions*, §5.5, the append-a-part recursion: Lemma
`HJO.Sweep.braidRep_phiPlusStar_comp_negYOneDPlusStarPiece`, using `HJO.Sweep.piece`,
`HJO.Braid.BraidMonoid`, `HJO.Braid.phiPlusStar`, `HJO.Sweep.dplusStar` and `HJO.Sweep.braidRep`,
and the lemmas `HJO.Sweep.dplusStar_braidInv`, `HJO.Sweep.braid_auxVar_succ_mul_braid`,
`HJO.Dyck.Aq.dPlus_mul_yElt_one` and `HJO.Sweep.braidRepRespects_mellit`.
-/

@[expose] public section

namespace HJO.Braid

/-! ### The index-raising assignment, lifted to the free monoid

`HJO.Braid.phiPlusLetter` lands in `𝔹^+_{k+1}(𝕋_0)`, so every statement made through it needs the
target rank's well-definedness before it can be read at all. The same assignment lands in the free
monoid, and `HJO.Braid.toBraidMonoid_phiPlusFreeWord` says the two agree. -/

/-- **`HJO.Braid.phiPlusStar` on the letters, valued in the free monoid**: `T_i ↦ T_{i+1}`,
`T̄_i ↦ T̄_{i+1}`, `y_1 ↦ 𝗒_2`, `z_1 ↦ 𝗓_2`, with the same `i = 0` guard as
`HJO.Braid.phiPlusLetter`. -/
def phiPlusLetterWord : Letter → FreeMonoid Letter
  | Letter.T i => if i = 0 then 1 else FreeMonoid.of (Letter.T (i + 1))
  | Letter.Tbar i => if i = 0 then 1 else FreeMonoid.of (Letter.Tbar (i + 1))
  | Letter.y1 => yWord 2
  | Letter.z1 => zWord 2

theorem phiPlusLetterWord_T {i : ℕ} (hi : 1 ≤ i) :
    phiPlusLetterWord (Letter.T i) = FreeMonoid.of (Letter.T (i + 1)) := by
  have h0 : i ≠ 0 := by omega
  simp [phiPlusLetterWord, h0]

theorem phiPlusLetterWord_Tbar {i : ℕ} (hi : 1 ≤ i) :
    phiPlusLetterWord (Letter.Tbar i) = FreeMonoid.of (Letter.Tbar (i + 1)) := by
  have h0 : i ≠ 0 := by omega
  simp [phiPlusLetterWord, h0]

theorem phiPlusLetterWord_T_zero : phiPlusLetterWord (Letter.T 0) = 1 := by
  simp [phiPlusLetterWord]

theorem phiPlusLetterWord_Tbar_zero : phiPlusLetterWord (Letter.Tbar 0) = 1 := by
  simp [phiPlusLetterWord]

/-- **`HJO.Braid.phiPlusStar` on the free monoid, valued in the free monoid.** -/
def phiPlusFreeWord : FreeMonoid Letter →* FreeMonoid Letter :=
  FreeMonoid.lift phiPlusLetterWord

@[simp]
theorem phiPlusFreeWord_of (c : Letter) :
    phiPlusFreeWord (FreeMonoid.of c) = phiPlusLetterWord c := rfl

theorem toBraidMonoid_phiPlusLetterWord (k : ℕ) (c : Letter) :
    toBraidMonoid (k + 1) (phiPlusLetterWord c) = phiPlusLetter k c := by
  match c with
  | Letter.T i =>
    rcases Nat.eq_zero_or_pos i with rfl | hi
    · rw [phiPlusLetterWord_T_zero, phiPlusLetter_T_zero, map_one]
    · rw [phiPlusLetterWord_T hi, phiPlusLetter_T hi, braidGenT]
  | Letter.Tbar i =>
    rcases Nat.eq_zero_or_pos i with rfl | hi
    · rw [phiPlusLetterWord_Tbar_zero, phiPlusLetter_Tbar_zero, map_one]
    · rw [phiPlusLetterWord_Tbar hi, phiPlusLetter_Tbar hi, braidGenTinv]
  | Letter.y1 => rfl
  | Letter.z1 => rfl

/-- **The two lifts of `HJO.Braid.phiPlusStar` agree.** -/
theorem toBraidMonoid_phiPlusFreeWord (k : ℕ) (w : FreeMonoid Letter) :
    toBraidMonoid (k + 1) (phiPlusFreeWord w) = phiPlusFree k w := by
  induction w using FreeMonoid.inductionOn' with
  | one => rw [map_one, map_one, map_one]
  | of_mul c w ih =>
    rw [map_mul, map_mul, map_mul, phiPlusFreeWord_of, toBraidMonoid_phiPlusLetterWord, ih,
      phiPlusFree_of]

end HJO.Braid

namespace HJO.Sweep

open Braid

/-! ### The vertical arrow between the graded pieces -/

section Field

variable {L : Type*} [Field L]

/-- **`-y_1d^*_+` carries `V_k` into `V_{k+1}`**: `HJO.Sweep.dplusStar_mem_piece` at the index
`HJO.Sweep.dplusStar` gives it, and `y_1 ∈ V_{k+1}`. -/
theorem negYOneDPlusStar_mem_piece (q u : L) {k : ℕ} {F : Total L} (hF : F ∈ piece L k) :
    negYOneDPlusStar q u k F ∈ piece L (k + 1) := by
  rw [negYOneDPlusStar_apply]
  exact neg_mem (mul_mem (auxVar_mem_piece le_rfl (by omega)) (dplusStar_mem_piece q u hF))

/-- **The vertical arrow of the first commutative diagram of Mellit's Section 5.5, with codomain
`V_{k+1}`**: the map `-y_1d^*_+` from `V_k` to `V_{k+1}`, which is also the right-hand side of
`HJO.Sweep.dplus_dplusIter`. -/
noncomputable def negYOneDPlusStarPiece (q u : L) (k : ℕ) :
    pieceSub L k →ₗ[L] pieceSub L (k + 1) :=
  (negYOneDPlusStar q u k).restrict fun _ hx => negYOneDPlusStar_mem_piece q u hx

@[simp]
theorem coe_negYOneDPlusStarPiece (q u : L) (k : ℕ) (x : pieceSub L k) :
    (negYOneDPlusStarPiece q u k x : Total L) = negYOneDPlusStar q u k x := rfl

end Field

section Rational

variable {L : Type*} [Field L] [Algebra ℚ L]

/-! ### The three letters that are relations between `d^*_+` and a multiplication operator -/

/-- **The `T` and `T̄` and `y` letters of
`HJO.Sweep.braidRep_phiPlusStar_comp_negYOneDPlusStarPiece`, at the graded piece.** Each is the
corresponding total-space identity of `HJO/Shuffle/MellitPhiIntertwine.lean` read on `V_k`, the
arrow being the restriction of the same map; the `z` letter is not here. -/
theorem braidRepLetter_phiPlusLetterWord_comp_negYOneDPlusStarPiece (q u : L) {r : L} (hq : q ≠ 0)
    (hr : r * r = q) {k : ℕ} (hk : 1 ≤ k) {c : Letter} (hc : c ≠ Letter.z1) :
    braidRepFree q u r (k + 1) (phiPlusLetterWord c) ∘ₗ negYOneDPlusStarPiece q u k
      = negYOneDPlusStarPiece q u k ∘ₗ braidRepLetter q u r k c := by
  refine LinearMap.ext fun x => Subtype.ext ?_
  have hx : (x : Total L) ∈ piece L k := x.2
  simp only [LinearMap.coe_comp, Function.comp_apply, braidRepFree_coe,
    coe_negYOneDPlusStarPiece, coe_braidRepLetter]
  match c with
  | Letter.T i =>
    rcases Nat.eq_zero_or_pos i with rfl | hi
    · rw [phiPlusLetterWord_T_zero, map_one,
        braidRepLetterTotal_of_not_inRank q u r
          (show ¬ Letter.InRank k (Letter.T 0) by simp only [Letter.InRank]; omega)]
      rfl
    · by_cases hik : i + 1 ≤ k
      · rw [phiPlusLetterWord_T hi, braidRepFreeTotal_of,
          braidRepLetterTotal_T q u r (by omega) (by omega),
          braidRepLetterTotal_T q u r hi hik]
        have h := LinearMap.congr_fun
          (braidEnd_mul_negYOneDPlusStar q u hi (show i < k by omega)) (x : Total L)
        simp only [Module.End.mul_apply, LinearMap.smul_apply, map_smul] at h ⊢
        rw [h]
      · rw [phiPlusLetterWord_T hi, braidRepFreeTotal_of,
          braidRepLetterTotal_of_not_inRank q u r
            (show ¬ Letter.InRank (k + 1) (Letter.T (i + 1)) by
              simp only [Letter.InRank]; omega),
          braidRepLetterTotal_of_not_inRank q u r
            (show ¬ Letter.InRank k (Letter.T i) by simp only [Letter.InRank]; omega)]
        rfl
  | Letter.Tbar i =>
    rcases Nat.eq_zero_or_pos i with rfl | hi
    · rw [phiPlusLetterWord_Tbar_zero, map_one,
        braidRepLetterTotal_of_not_inRank q u r
          (show ¬ Letter.InRank k (Letter.Tbar 0) by simp only [Letter.InRank]; omega)]
      rfl
    · by_cases hik : i + 1 ≤ k
      · rw [phiPlusLetterWord_Tbar hi, braidRepFreeTotal_of,
          braidRepLetterTotal_Tbar q u r (by omega) (by omega),
          braidRepLetterTotal_Tbar q u r hi hik]
        have h := LinearMap.congr_fun
          (braidInvEnd_mul_negYOneDPlusStar q u hq hi (show i < k by omega)) (x : Total L)
        simp only [Module.End.mul_apply, LinearMap.smul_apply, map_smul] at h ⊢
        rw [h]
      · rw [phiPlusLetterWord_Tbar hi, braidRepFreeTotal_of,
          braidRepLetterTotal_of_not_inRank q u r
            (show ¬ Letter.InRank (k + 1) (Letter.Tbar (i + 1)) by
              simp only [Letter.InRank]; omega),
          braidRepLetterTotal_of_not_inRank q u r
            (show ¬ Letter.InRank k (Letter.Tbar i) by simp only [Letter.InRank]; omega)]
        rfl
  | Letter.y1 =>
    have hphi : phiPlusLetterWord Letter.y1 = yWord 2 := rfl
    rw [hphi, ← yRepTotal_def, braidRepLetterTotal_y1 q u r hk, ← yRepTotal_one q u r hk]
    exact LinearMap.congr_fun
      (yRepTotal_two_mul_negYOneDPlusStar q u hq hr hk) (x : Total L)
  | Letter.z1 => exact absurd rfl hc

end Rational

/-! ### The `z` letter, through the Mellit-convention action of the Dyck path algebra

The relation for `z_i` looks as though it were of the same kind as the two relations between
`d^*_+` and a multiplication operator. It is not: `z_1` is by
`HJO.Sweep.zop` the commutator `[d^*_+, d^♭_-]` followed by a train, so no algebra-map argument
reaches it. What does reach it is that `d^*_+` is **the raising operator of the Dyck path algebra in
Mellit's own convention** — the triple `(T_i^{-1}, d^♭_-, d^*_+)` at the scalar `q^{-1}` of
`HJO.Sweep.isDpaOperators_mellit` — and that `HJO.Sweep.map_yElt_ofPiece_mellit` identifies `z_i`
with that algebra's corner elements. Under that identification the `z` letter is three proved
relations:

* `HJO.Dyck.Aq.dPlus_mul_yElt_one`, transported: it is the *only*
  place the commutator is touched, and it is touched in the abstract algebra rather than here;
* the mixed relation of `HJO.Braid.BraidMonoid`, `z_1T_1y_1\bar T_1 = y_2z_1`
  (`HJO.Sweep.zopOneStar_mul_braidEnd_mul_mulLeft_auxVar_one`);
* `HJO.Sweep.braid_auxVar_succ_mul_braid` in the form `y_2 = qT_1^{-1}y_1T_1^{-1}`
  (`HJO.Sweep.mulLeft_auxVar_succ_eq`).

Nothing about the two `d_-` conventions has to be reconciled, and no commutation `z_1z_2 = z_2z_1`
is needed: the `T_1` of `HJO.Sweep.zop`'s recursion is absorbed by the mixed relation instead. -/

section MellitAction

variable {L : Type*} [Field L] [Algebra ℚ L] {q u : L}
  [Invertible (q⁻¹ : L)] [Invertible (q⁻¹ - 1 : L)]
  {ρ : Dyck.Aq L q⁻¹ →ₐ[L] Module.End L (Vstar L)}

variable (hact : IsDpaAction q⁻¹ ρ)
  (hT : ∀ k i : ℕ, ρ (Dyck.Aq.Tg L q⁻¹ k i) = loopVstar (braidInvModPiece q) k i)
  (hD : ∀ k : ℕ, ρ (Dyck.Aq.dMinus L q⁻¹ k) = lowerVstar (dminusModPiece q) k)
  (hU : ∀ k : ℕ, ρ (Dyck.Aq.dPlus L q⁻¹ k) = raiseVstar (dplusStarPiece q u) k)

include hact hT hD hU in
/-- **`HJO.Dyck.Aq.dPlus_mul_yElt_one` in Mellit's convention**:
`d^*_+z_1^{(k)} = T_1^{-1}z_1^{(k+1)}T_1d^*_+` on `V_k`.

`HJO.Dyck.Aq.dPlus_mul_yElt_one` is the abstract statement
`d_+y_1^{(k)} = T_1y_1^{(k+1)}T_1^{-1}d_+`, a theorem of `HJO.Dyck.Aq` whose content is the relation
`T_1(d_+d_- - d_-d_+)d_+ = qd_+(d_+d_- - d_-d_+)` acting on the commutator in the closed form of
`HJO.Dyck.Aq.yElt`. Reading it through this action turns the abstract `d_+` into `d^*_+`, the
abstract loops into the **inverses** `T_i^{-1}` — which is why the two braid letters come out
swapped relative to the abstract statement — and the corner elements into the `z_i` of
`HJO.Sweep.zop` (`HJO.Sweep.map_yElt_ofPiece_mellit`). `HJO.Sweep.map_Tinv_ofPiece` handles the one
inverted loop.

This is the only step of `HJO.Sweep.braidRep_phiPlusStar_comp_negYOneDPlusStarPiece` that touches
the commutator, and it does so inside the abstract algebra. In particular it needs no reconciliation
of the two `d_-` conventions, which `HJO.Sweep.mulLeft_auxVar_two_not_comm_trainUpEnd` shows is
unavailable. -/
theorem dplusStar_zop_one_of_mellitAction (hq : q ≠ 0) (hq1 : q ≠ 1) {k : ℕ} (hk : 1 ≤ k)
    {F : Total L} (hF : F ∈ piece L k) :
    dplusStar q u k (zop q u k 1 F)
      = braidInv q 1 (zop q u (k + 1) 1 (braid q 1 (dplusStar q u k F))) := by
  have hk2 : 0 + 2 ≤ k + 1 := by omega
  have hz : zop q u k 1 F ∈ pieceSub L k := zop_mem_piece q u 1 le_rfl hk hF
  have hAm : dplusStar q u k F ∈ pieceSub L (k + 1) := dplusStar_mem_piece q u hF
  have hBm : braid q 1 (dplusStar q u k F) ∈ pieceSub L (k + 1) :=
    braid_mem_piece q (show 1 ≤ 1 from le_rfl) (by omega) hAm
  have hCm : zop q u (k + 1) 1 (braid q 1 (dplusStar q u k F)) ∈ pieceSub L (k + 1) :=
    zop_mem_piece q u 1 le_rfl (by omega) hBm
  have hDm : dplusStar q u k (zop q u k 1 F) ∈ pieceSub L (k + 1) :=
    dplusStar_mem_piece q u hz
  -- the raising arrow on a summand
  have eU : ∀ (G : pieceSub L k) (H : pieceSub L (k + 1)), (H : Total L) = dplusStar q u k G →
      ρ (Dyck.Aq.dPlus L q⁻¹ k) (ofPiece L k G) = ofPiece L (k + 1) H := by
    intro G H hGH
    rw [hU, raiseVstar_ofPiece]
    exact congrArg (ofPiece L (k + 1)) (Subtype.ext hGH.symm)
  -- the four transport steps
  have e1 : ρ (Dyck.Aq.yElt L q⁻¹ k 1) (ofPiece L k ⟨F, hF⟩)
      = ofPiece L k ⟨zop q u k 1 F, hz⟩ :=
    map_yElt_ofPiece_mellit hact hT hD hU hq hq1 (k - 1) 1 (by omega) le_rfl _ _ rfl
  have e3 : ρ (Dyck.Aq.Tinv L q⁻¹ (k + 1) 0)
        (ofPiece L (k + 1) ⟨dplusStar q u k F, hAm⟩)
      = ofPiece L (k + 1) ⟨braid q 1 (dplusStar q u k F), hBm⟩ :=
    map_Tinv_ofPiece hact hT hq hk2 _ _ rfl
  have e4 : ρ (Dyck.Aq.yElt L q⁻¹ (k + 1) 1)
        (ofPiece L (k + 1) ⟨braid q 1 (dplusStar q u k F), hBm⟩)
      = ofPiece L (k + 1) ⟨zop q u (k + 1) 1 (braid q 1 (dplusStar q u k F)), hCm⟩ :=
    map_yElt_ofPiece_mellit hact hT hD hU hq hq1 k 1 (by omega) le_rfl _ _ rfl
  have e5 : ρ (Dyck.Aq.Tg L q⁻¹ (k + 1) 0)
        (ofPiece L (k + 1) ⟨zop q u (k + 1) 1 (braid q 1 (dplusStar q u k F)), hCm⟩)
      = ofPiece L (k + 1) (braidInvModPiece q (k + 1) 0
          ⟨zop q u (k + 1) 1 (braid q 1 (dplusStar q u k F)), hCm⟩) := by
    rw [hT, loopVstar_ofPiece]
  -- read the abstract identity through the action
  have habs := congrArg (fun f : Module.End L (Vstar L) => f (ofPiece L k ⟨F, hF⟩))
    (congrArg ρ (Dyck.Aq.dPlus_mul_yElt_one (K := L) (q := (q⁻¹ : L)) (k := k) hk))
  simp only [map_mul, Module.End.mul_apply] at habs
  rw [e1, eU ⟨zop q u k 1 F, hz⟩ ⟨_, hDm⟩ rfl, eU ⟨F, hF⟩ ⟨_, hAm⟩ rfl, e3, e4, e5] at habs
  have hfin := congrArg Subtype.val (eq_of_ofPiece_eq habs)
  rw [coe_braidInvModPiece q hk2] at hfin
  exact hfin

include hact hT hD hU in
/-- **The `z` letter of `HJO.Sweep.braidRep_phiPlusStar_comp_negYOneDPlusStarPiece`, before the
normalisation**: `z_2^{(k+1)}(y_1d^*_+F) = y_1d^*_+(z_1^{(k)}F)` for `F ∈ V_k`.

`HJO.Sweep.zop`'s recursion writes `z_2 = q^{-1}T_1z_1T_1`, so the left-hand side is
`q^{-1}T_1z_1^{(k+1)}T_1(y_1d^*_+F)`. The mixed relation of `HJO.Braid.BraidMonoid` carries `y_1`
out through `z_1T_1` as `y_2`, `HJO.Sweep.braid_auxVar_succ_mul_braid` replaces that `y_2` by
`qT_1^{-1}y_1T_1^{-1}`, the outer `T_1` cancels one inverse and the factor `q` cancels the `q^{-1}`;
what is left is `y_1T_1^{-1}z_1^{(k+1)}T_1d^*_+F`, which is
`HJO.Sweep.dplusStar_zop_one_of_mellitAction` read backwards. -/
theorem zop_two_auxVar_one_dplusStar_of_mellitAction (hq : q ≠ 0) (hq1 : q ≠ 1) {k : ℕ}
    (hk : 1 ≤ k) {F : Total L} (hF : F ∈ piece L k) :
    zop q u (k + 1) 2 ((auxVar 1 : Total L) * dplusStar q u k F)
      = (auxVar 1 : Total L) * dplusStar q u k (zop q u k 1 F) := by
  set A : Total L := dplusStar q u k F with hAdef
  set W : Total L := zop q u (k + 1) 1 (braid q 1 A) with hWdef
  -- the mixed relation of `HJO.Braid.BraidMonoid`, applied at `T_1A`
  have hmix : zop q u (k + 1) 1 (braid q 1 ((auxVar 1 : Total L) * A))
      = (auxVar 2 : Total L) * W := by
    have h := LinearMap.congr_fun
      (zopOneStar_mul_braidEnd_mul_mulLeft_auxVar_one q u hq (show 2 ≤ k + 1 by omega))
      (braid q 1 A)
    simp only [Module.End.mul_apply, LinearMap.mulLeft_apply] at h
    rw [show braidInvEnd q 1 (braid q 1 A) = A from braidInv_braid q hq 1 A] at h
    rw [hWdef, zop_one]
    exact h
  -- `y_2 = qT_1^{-1}y_1T_1^{-1}`, the operator form of `HJO.Sweep.braid_auxVar_succ_mul_braid`
  have hy2 : (auxVar 2 : Total L) * W
      = q • braidInv q 1 ((auxVar 1 : Total L) * braidInv q 1 W) := by
    have h := LinearMap.congr_fun (mulLeft_auxVar_succ_eq q hq (i := 1) le_rfl) W
    rw [show (1 : ℕ) + 1 = 2 from by norm_num] at h
    exact h
  have hi := dplusStar_zop_one_of_mellitAction hact hT hD hU hq hq1 hk hF
  have hbeE : ∀ Z : Total L, braidEnd q 1 Z = braid q 1 Z := fun _ => rfl
  calc zop q u (k + 1) 2 ((auxVar 1 : Total L) * A)
      = (q⁻¹ : L) •
          braidEnd q 1 (zop q u (k + 1) 1 (braid q 1 ((auxVar 1 : Total L) * A))) := by
        rw [zop_succ]
        rfl
    _ = (q⁻¹ : L) • braidEnd q 1 ((auxVar 2 : Total L) * W) := by rw [hmix]
    _ = (q⁻¹ : L) •
          (q • braidEnd q 1 (braidInv q 1 ((auxVar 1 : Total L) * braidInv q 1 W))) := by
        rw [hy2, map_smul]
    _ = (q⁻¹ : L) • (q • ((auxVar 1 : Total L) * braidInv q 1 W)) := by
        rw [hbeE, braid_braidInv q hq]
    _ = (auxVar 1 : Total L) * braidInv q 1 W := by
        rw [smul_smul, inv_mul_cancel₀ hq, one_smul]
    _ = (auxVar 1 : Total L) * dplusStar q u k (zop q u k 1 F) := by rw [hWdef, ← hi]

include hact hT hD hU in
/-- **The `z` letter at the graded piece**:
`π_{k+1}(z_2)\,(-y_1d^*_+) = (-y_1d^*_+)\,π_k(z_1)` as maps `V_k → V_{k+1}`.

`HJO.Sweep.zRepTotal_eq_smul_zop` strips the normalising scalar `(qu)^{-1}` that
`HJO.Sweep.braidRep` puts on each `z`; it appears once on each side and is never cancelled, so no
hypothesis on `u` is used. The sign of the arrow cancels likewise. -/
theorem zRep_two_comp_negYOneDPlusStarPiece_of_mellitAction (hq : q ≠ 0) (hq1 : q ≠ 1) {r : L}
    (hr : r * r = q) {k : ℕ} (hk : 1 ≤ k) :
    zRep q u r (k + 1) 2 ∘ₗ negYOneDPlusStarPiece q u k
      = negYOneDPlusStarPiece q u k ∘ₗ zRep q u r k 1 := by
  refine LinearMap.ext fun x => Subtype.ext ?_
  have hx : (x : Total L) ∈ piece L k := x.2
  have hkey := zop_two_auxVar_one_dplusStar_of_mellitAction hact hT hD hU hq hq1 hk hx
  simp only [LinearMap.coe_comp, Function.comp_apply, coe_zRep, coe_negYOneDPlusStarPiece]
  rw [zRepTotal_eq_smul_zop q u hr 2 (by omega) (by omega),
    zRepTotal_eq_smul_zop q u hr 1 le_rfl hk]
  simp only [LinearMap.smul_apply, negYOneDPlusStar_apply, map_smul, map_neg, smul_neg, hkey]

end MellitAction

/-! ### The diagram -/

section Rational

variable {L : Type*} [Field L] [Algebra ℚ L]

/-- **The `z` letter, unconditionally**: `HJO.Sweep.exists_isDpaAction_mellit` supplies the
Mellit-convention action. The three side conditions are the ones that action costs — `q ≠ 0` and
`q + 1 ≠ 0` from `HJO.Sweep.isDpaOperators_mellit`, and `q ≠ 1` because `HJO.Dyck.Aq.yElt` divides
by `q' - 1` at `q' = q^{-1}`, which is `HJO.Sweep.zop`'s own `q^k/(1-q)`. -/
theorem zRep_two_comp_negYOneDPlusStarPiece (q u : L) (hq : q ≠ 0) (hq1 : q ≠ 1) (hqp : q + 1 ≠ 0)
    {r : L} (hr : r * r = q) {k : ℕ} (hk : 1 ≤ k) :
    zRep q u r (k + 1) 2 ∘ₗ negYOneDPlusStarPiece q u k
      = negYOneDPlusStarPiece q u k ∘ₗ zRep q u r k 1 := by
  obtain ⟨ρ, hact, hT, hD, hU⟩ := exists_isDpaAction_mellit q u hq hqp
  have hqi : (q⁻¹ : L) ≠ 0 := inv_ne_zero hq
  have hqi1 : (q⁻¹ - 1 : L) ≠ 0 := fun h => hq1 (inv_eq_one.1 (sub_eq_zero.1 h))
  let _ : Invertible (q⁻¹ : L) := invertibleOfNonzero hqi
  let _ : Invertible (q⁻¹ - 1 : L) := invertibleOfNonzero hqi1
  exact zRep_two_comp_negYOneDPlusStarPiece_of_mellitAction hact hT hD hU hq hq1 hr hk

/-- **All four letters of `HJO.Braid.braidGenT` at once.** -/
theorem braidRepFree_phiPlusLetterWord_comp_negYOneDPlusStarPiece (q u : L) (hq : q ≠ 0)
    (hq1 : q ≠ 1) (hqp : q + 1 ≠ 0) {r : L} (hr : r * r = q) {k : ℕ} (hk : 1 ≤ k) (c : Letter) :
    braidRepFree q u r (k + 1) (phiPlusLetterWord c) ∘ₗ negYOneDPlusStarPiece q u k
      = negYOneDPlusStarPiece q u k ∘ₗ braidRepLetter q u r k c := by
  by_cases hc : c = Letter.z1
  · subst hc
    have hL : phiPlusLetterWord Letter.z1 = zWord 2 := rfl
    have hR : braidRepLetter q u r k Letter.z1 = zRep q u r k 1 := by
      rw [zRep_def, zWord_one, braidRepFree_of]
    rw [hL, hR, ← zRep_def]
    exact zRep_two_comp_negYOneDPlusStarPiece q u hq hq1 hqp hr hk
  · exact braidRepLetter_phiPlusLetterWord_comp_negYOneDPlusStarPiece q u hq hr hk hc

/-- **The diagram at the free level**, with no well-definedness hypothesis at either rank: for
every word `w`,

`π_{k+1}(φ^*_+(w)) ∘ (-y_1d^*_+) = (-y_1d^*_+) ∘ π_k(w)`.

Both sides are monoid homomorphisms in `w` composed with a fixed map, so the induction is the
evident one: the empty word gives the identity on both sides and the four
letters are `HJO.Sweep.braidRepFree_phiPlusLetterWord_comp_negYOneDPlusStarPiece`. -/
theorem braidRepFree_phiPlusFreeWord_comp_negYOneDPlusStarPiece (q u : L) (hq : q ≠ 0)
    (hq1 : q ≠ 1) (hqp : q + 1 ≠ 0) {r : L} (hr : r * r = q) {k : ℕ} (hk : 1 ≤ k)
    (w : FreeMonoid Letter) :
    braidRepFree q u r (k + 1) (phiPlusFreeWord w) ∘ₗ negYOneDPlusStarPiece q u k
      = negYOneDPlusStarPiece q u k ∘ₗ braidRepFree q u r k w := by
  induction w using FreeMonoid.inductionOn' with
  | one =>
    refine LinearMap.ext fun x => ?_
    simp only [map_one, LinearMap.coe_comp, Function.comp_apply, Module.End.one_apply]
  | of_mul c w ih =>
    refine LinearMap.ext fun x => ?_
    have hstep := LinearMap.congr_fun ih x
    have hletter := LinearMap.congr_fun
      (braidRepFree_phiPlusLetterWord_comp_negYOneDPlusStarPiece q u hq hq1 hqp hr hk c)
      (braidRepFree q u r k w x)
    simp only [map_mul, phiPlusFreeWord_of, Module.End.mul_apply, braidRepFree_of,
      LinearMap.coe_comp, Function.comp_apply] at hstep hletter ⊢
    rw [hstep, hletter]

/-- **`HJO.Sweep.braidRep_phiPlusStar_comp_negYOneDPlusStarPiece`**: the first of the two
commutative diagrams of Mellit's Section 5.5. For `k ≥ 1` and `B ∈ 𝔹^+_k(𝕋_0)`,

`π_{k+1}(φ^*_+(B)) ∘ (-y_1d^*_+) = (-y_1d^*_+) ∘ π_k(B)`

as maps `V_k → V_{k+1}`.

The two `HJO.Sweep.BraidRepRespects` arguments are not hypotheses of the mathematics but of the
notation: the statement names `π_k` and `π_{k+1}`, which is `HJO.Sweep.braidRep`, and that
definition takes its well-definedness as an argument. Both are supplied by
`HJO.Sweep.braidRepRespects_mellit` at exactly the side conditions
already present here, so nothing is left owed; `HJO.Sweep.braidRep_phiPlusStar_comp_mellit` is the
form with them discharged.

The three letters `T_i`, `T̄_i`, `y_1` are `HJO.Sweep.dplusStar_braidInv` and
`HJO.Sweep.braid_auxVar_succ_mul_braid`; the letter `z_1` is
`HJO.Sweep.zRep_two_comp_negYOneDPlusStarPiece`. **The total-space form of this statement is
vacuous** — its assembly needs `HJO.Sweep.BraidRepRespectsTotal`, which
`HJO.Sweep.braidRepRespectsTotal_two_false` refutes at every rank in the range `1 ≤ k`. -/
@[hjo "lem_mellit_phi_intertwine"]
theorem braidRep_phiPlusStar_comp_negYOneDPlusStarPiece (q u : L) (hq : q ≠ 0) (hq1 : q ≠ 1)
    (hqp : q + 1 ≠ 0) {r : L} (hr : r * r = q) {k : ℕ} (hk : 1 ≤ k)
    (h : BraidRepRespects q u r k) (h' : BraidRepRespects q u r (k + 1)) (B : BraidMonoid k) :
    braidRep q u r (k + 1) h' (phiPlusStar k hk B) ∘ₗ negYOneDPlusStarPiece q u k
      = negYOneDPlusStarPiece q u k ∘ₗ braidRep q u r k h B := by
  obtain ⟨w, rfl⟩ := toBraidMonoid_surjective k B
  rw [phiPlusStar_apply, braidRep_apply, ← toBraidMonoid_phiPlusFreeWord, braidRep_apply]
  exact braidRepFree_phiPlusFreeWord_comp_negYOneDPlusStarPiece q u hq hq1 hqp hr hk w

/-- **`HJO.Sweep.braidRep_phiPlusStar_comp_negYOneDPlusStarPiece` with `HJO.Sweep.braidRep`'s
well-definedness discharged**, `π` being the `HJO.Sweep.braidRepMellit` of
`HJO.Sweep.braidRepRespects_mellit`. -/
@[hjo "lem_mellit_phi_intertwine"]
theorem braidRep_phiPlusStar_comp_mellit (q u : L) (hq : q ≠ 0) (hq1 : q ≠ 1) (hqp : q + 1 ≠ 0)
    {r : L} (hr : r * r = q) {k : ℕ} (hk : 1 ≤ k) (B : BraidMonoid k) :
    braidRepMellit q u hq hq1 hqp hr (k + 1) (phiPlusStar k hk B)
        ∘ₗ negYOneDPlusStarPiece q u k
      = negYOneDPlusStarPiece q u k ∘ₗ braidRepMellit q u hq hq1 hqp hr k B :=
  braidRep_phiPlusStar_comp_negYOneDPlusStarPiece q u hq hq1 hqp hr hk _ _ B

end Rational

end HJO.Sweep
