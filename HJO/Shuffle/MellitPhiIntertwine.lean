/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.CMStructure.DemazureIdentities
public import HJO.CMStructure.StarEasy
public import HJO.Shuffle.BraidPhiPlus
public import HJO.Shuffle.BraidRep
public meta import HJO.Attr

/-! # The index-raising homomorphism against `-y_1d^*_+`

`HJO.Sweep.braidRep_phiPlusStar_comp_negYOneDPlusStarPiece` is the first of the two commutative
diagrams of Mellit's Section 5.5: for `B ∈ 𝔹^+_k(𝕋_0)`,

`π_{k+1}(φ^*_+(B)) ∘ (-y_1d^*_+) = (-y_1d^*_+) ∘ π_k(B)`.

Both sides are monoid homomorphisms in `B` composed with a fixed map, so it suffices to check it
on the letters of `HJO.Braid.braidGenT`. This file discharges **three
of the four letters** and isolates the fourth.

* `T_i` and `T̄_i`: `HJO.Sweep.braidEnd_mul_negYOneDPlusStar` and
  `HJO.Sweep.braidInvEnd_mul_negYOneDPlusStar`, the relation `T_{i+1}\,y_1d^*_+ = y_1d^*_+\,T_i`,
  the first of the two named relations. It is `HJO.Sweep.dplusStar_braidInv`'s first clause
  `d^*_+T_i = T_{i+1}d^*_+` together with the fact that `T_{i+1}` is linear over `y_1` — which holds
  because `s_{i+1}` fixes `y_1` for every `i ≥ 1`, and *fails* at `i = 0`, where `s_1` moves it.
* `y_1`: `HJO.Sweep.yRepTotal_two_mul_negYOneDPlusStar`. This is the other named relation,
  `d^*_+y_i = y_{i+1}d^*_+` (`HJO.Sweep.dplusStar_braidInv`'s third clause), combined with
  `y_2 = qT_1^{-1}y_1T_1^{-1}` — the operator form of `HJO.Sweep.braid_auxVar_succ_mul_braid`, which
  is what makes `π(y_2)` multiplication by `-y_2` in spite of the `q^{1/2}` normalisation of the
  braid letters.
* `z_1`: **not discharged.** The clause is `HJO.Sweep.PhiIntertwineZ`, and
  `HJO.Sweep.braidRepTotal_phiPlusStar_mul_negYOneDPlusStar` takes it as a hypothesis. See below.

Because the fourth clause is not discharged here, what this file proves is the reduction of
`HJO.Sweep.braidRep_phiPlusStar_comp_negYOneDPlusStarPiece` to one relation, not the statement
itself; that is proved, at the graded pieces, in `HJO/Shuffle/MellitPhiIntertwinePiece.lean`.

## This file is still written on the total space, and its assembled form is vacuous

`HJO.Sweep.negYOneDPlusStar` is a map `V_k → V_{k+1}`, so it is not an endomorphism of any one
graded piece; every statement here is therefore in `Module.End L (Total L)`, and the three
discharged letters and the `z` clause `HJO.Sweep.PhiIntertwineZ` are unconditional identities
there — nothing about them is vacuous and nothing is lost.

What *is* vacuous is the assembled
`HJO.Sweep.braidRepTotal_phiPlusStar_mul_negYOneDPlusStar`: it needs monoid homomorphisms out of
`𝔹^+_k(𝕋_0)` and `𝔹^+_{k+1}(𝕋_0)`, so it takes `HJO.Sweep.BraidRepRespectsTotal q u r k` and
`... (k + 1)`, and with `1 ≤ k` the second is at rank `≥ 2` where
`HJO.Sweep.braidRepRespectsTotal_two_false` refutes it. Since `HJO.Sweep.braidRep` is typed at
`HJO.Sweep.pieceSub L k`, the way out is a **free-level** assembly, with no
respecting hypothesis at all: the `main` induction inside that theorem already proves
`braidRepFreeTotal q u r (k+1) (φ^*_+ w) ∘ (-y_1d^*_+) = (-y_1d^*_+) ∘ braidRepFreeTotal q u r k w`
for every word `w`, which is the statement
`HJO.Sweep.braidRep_phiPlusStar_comp_negYOneDPlusStarPiece` actually needs and which no refuted
hypothesis touches. Extracting it is not done here.

## Why the `z` clause is not here

The relation for `z_i` looks as if it were of the same kind as the two named relations. It is
not. The two named relations are relations between `d^*_+` and
*multiplication operators*, and `d^*_+` is a composite of two algebra maps, so each is a one-line
consequence of `cy_{k+1}(y_i) = y_{i+1}`. The `z` clause is
`z_2^{(k+1)}(y_1d^*_+) = (y_1d^*_+)z_1^{(k)}`, and `z_1` is by `HJO.Sweep.zop` the operator
`q^k/(1-q)(d^*_+d_- - d_-d^*_+)T^*_{k↘1}` — it involves `d_-` and a train, so the clause is a
statement about the *commutation of `d^*_+` past the starred commutator across the wrap*, which is
the content of `HJO.Sweep.exists_isDpaAction_mellit` (the action of `e_0Ãe_0` on `Λ`), not
of `HJO.Sweep.dplusStar_braidInv`. Moreover multiplication by `y_1` does not commute with `z_2`:
`HJO.Braid.BraidMonoid` imposes no relation between `y_1` and `z_2`, its only mixed relation being
`z_1T_1y_1T̄_1 = T̄_1y_1T̄_1z_1`. So the clause cannot be assembled from the `y`-side argument, and
it is stated here as a hypothesis rather than bent into something provable.

## Main definitions

* `HJO.Sweep.negYOneDPlusStar` — the map `-y_1d^*_+` from `V_k` to `V_{k+1}`, the vertical arrow of
  the diagram. It is also the right-hand side of `HJO.Sweep.dplus_dplusIter`,
  `d_+^{k+1}(1) = -y_1d^*_+d_+^k(1)`.
* `HJO.Sweep.PhiIntertwineZ` — the one letter clause not discharged here.

## Main results

* `HJO.Sweep.braidEnd_mul_negYOneDPlusStar`, `HJO.Sweep.braidInvEnd_mul_negYOneDPlusStar`,
  `HJO.Sweep.yRepTotal_two_mul_negYOneDPlusStar` — the three discharged letters.
* `HJO.Sweep.braidRepTotal_phiPlusStar_mul_negYOneDPlusStar` — the reduction: given
  `HJO.Sweep.PhiIntertwineZ`, the diagram commutes for every `B`. Its two
  `HJO.Sweep.BraidRepRespectsTotal` hypotheses make it vacuous for `1 ≤ k`; see above.

## References

Lemma `HJO.Sweep.braidRep_phiPlusStar_comp_negYOneDPlusStarPiece`, using `HJO.Sweep.piece`,
`HJO.Braid.BraidMonoid`, `HJO.Braid.phiPlusStar`, `HJO.Sweep.dplusStar` and `HJO.Sweep.braidRep`;
and `HJO.Sweep.dplusStar_braidInv`, `HJO.Sweep.braid_auxVar_succ_mul_braid`. Transcribing
A. Mellit, *Toric braids and `(m, n)`-parking functions*, §5.5.
-/

@[expose] public section

namespace HJO.Sweep

open Braid

section Field

variable {L : Type*} [Field L]

/-! ### Multiplication by `y_1` against the braid operators and their inverses -/

/-- **`T_j` is linear over `y_1` for every `j ≥ 2`**: `s_j` fixes `y_1` there, so
`HJO.Sweep.braid_mul_of_swapAux_eq` applies. At `j = 1` this is false: `s_1` sends `y_1` to
`y_2`. -/
theorem braid_auxVar_one_mul (q : L) {j : ℕ} (hj : 2 ≤ j) (F : Total L) :
    braid q j ((auxVar 1 : Total L) * F) = auxVar 1 * braid q j F :=
  braid_mul_of_swapAux_eq q (swapAux_auxVar_of_ne (by omega) (by omega) (by omega)) F

/-- **`T_j^{-1}` is linear over `y_1` for every `j ≥ 2`**: the same statement for the inverse, which
is a polynomial in `T_j`. -/
theorem braidInv_auxVar_one_mul (q : L) {j : ℕ} (hj : 2 ≤ j) (F : Total L) :
    braidInv q j ((auxVar 1 : Total L) * F) = auxVar 1 * braidInv q j F := by
  rw [braidInv_apply, braidInv_apply, braid_auxVar_one_mul q hj]
  ring

/-- `T_i^{-1}` is linear over the scalars of `𝕜`, being a polynomial in `T_i`. -/
theorem braidInv_scal_mul (q : L) (i : ℕ) (x : L) (G : Total L) :
    braidInv q i (scal x * G) = scal x * braidInv q i G := by
  rw [braidInv_apply, braidInv_apply, braid_scal_mul]
  ring

/-- **`y_{i+1}H = qT_i^{-1}(y_i\,T_i^{-1}H)`**: the operator form of
`HJO.Sweep.braid_auxVar_succ_mul_braid`, with both braid operators inverted. This is what makes the
braid representation send `y_2` to multiplication by `-y_2` in spite of the `q^{1/2}` normalisation
of the braid letters. -/
theorem auxVar_succ_mul_eq (q : L) (hq : q ≠ 0) {i : ℕ} (hi : 1 ≤ i) (H : Total L) :
    (auxVar (i + 1) : Total L) * H
      = scal q * braidInv q i ((auxVar i : Total L) * braidInv q i H) := by
  have h : braid q i ((auxVar (i + 1) : Total L) * H)
      = scal q * auxVar i * braidInv q i H := by
    have h0 := braid_auxVar_succ_mul_braid q hi (braidInv q i H)
    rwa [braid_braidInv q hq i H] at h0
  have h1 : braidInv q i (scal q * ((auxVar i : Total L) * braidInv q i H))
      = (auxVar (i + 1) : Total L) * H := by
    rw [show (scal q : Total L) * ((auxVar i : Total L) * braidInv q i H)
        = scal q * auxVar i * braidInv q i H from by ring, ← h, braidInv_braid q hq]
  rw [← h1]
  exact braidInv_scal_mul q i q _

/-! ### The vertical arrow of the diagram -/

/-- **The map `-y_1d^*_+`** from `V_k` to `V_{k+1}`: the vertical arrow of the first commutative
diagram of Mellit's Section 5.5, and the right-hand side of `HJO.Sweep.dplus_dplusIter`. -/
noncomputable def negYOneDPlusStar (q u : L) (k : ℕ) : Module.End L (Total L) :=
  -(LinearMap.mulLeft L (auxVar 1 : Total L) ∘ₗ dplusStar q u k)

theorem negYOneDPlusStar_apply (q u : L) (k : ℕ) (F : Total L) :
    negYOneDPlusStar q u k F = -((auxVar 1 : Total L) * dplusStar q u k F) := rfl

/-! ### The braid letters -/

/-- **`T_{i+1}\,y_1d^*_+ = y_1d^*_+\,T_i`** for `1 ≤ i < k`, the first of the two relations
between `d^*_+` and a multiplication operator that
`HJO.Sweep.braidRep_phiPlusStar_comp_negYOneDPlusStarPiece` uses.

`d^*_+T_i = T_{i+1}d^*_+` is `HJO.Sweep.dplusStar_braidInv`'s first clause
(`HJO.Sweep.dplusStar_braid`), and `T_{i+1}` passes the factor `y_1` because `s_{i+1}` fixes it,
`i + 1` being at least `2`. The range `i < k` is the exact range of that clause: at `i = k` the
cyclic shift sends `y_{k+1}` to `uy_1` and the conjugation fails. -/
theorem braidEnd_mul_negYOneDPlusStar (q u : L) {i k : ℕ} (hi : 1 ≤ i) (hik : i < k) :
    braidEnd q (i + 1) * negYOneDPlusStar q u k = negYOneDPlusStar q u k * braidEnd q i := by
  refine LinearMap.ext fun F => ?_
  change braid q (i + 1) (negYOneDPlusStar q u k F)
    = negYOneDPlusStar q u k (braid q i F)
  rw [negYOneDPlusStar_apply, negYOneDPlusStar_apply, map_neg,
    braid_auxVar_one_mul q (by omega), dplusStar_braid q u hi hik]

/-- **`T_{i+1}^{-1}\,y_1d^*_+ = y_1d^*_+\,T_i^{-1}`** for `1 ≤ i < k`: the inverted form, from
the first clause of `HJO.Sweep.dplusStar_braidInv`, which is where
`q ≠ 0` enters. -/
theorem braidInvEnd_mul_negYOneDPlusStar (q u : L) (hq : q ≠ 0) {i k : ℕ} (hi : 1 ≤ i)
    (hik : i < k) :
    braidInvEnd q (i + 1) * negYOneDPlusStar q u k
      = negYOneDPlusStar q u k * braidInvEnd q i := by
  refine LinearMap.ext fun F => ?_
  change braidInv q (i + 1) (negYOneDPlusStar q u k F)
    = negYOneDPlusStar q u k (braidInv q i F)
  rw [negYOneDPlusStar_apply, negYOneDPlusStar_apply, map_neg,
    braidInv_auxVar_one_mul q (by omega), dplusStar_braidInv q u hq hi hik]

end Field

/-! ### The `y` letter, and the reduction -/

section Rational

variable {L : Type*} [Field L] [Algebra ℚ L]

/-- **`π_{k+1}(y_2)\,(-y_1d^*_+) = (-y_1d^*_+)\,π_k(y_1)`**, the `y` letter of
`HJO.Sweep.braidRep_phiPlusStar_comp_negYOneDPlusStarPiece`.

Two steps. `π_k(y_1)` is multiplication by `-y_1` and `d^*_+y_1 = y_2d^*_+`
(`HJO.Sweep.dplusStar_auxVar_mul`), so the right-hand side is `y_1y_2d^*_+`. On the left,
`π_{k+1}(y_2) = q\,T_1^{-1}(-y_1·)T_1^{-1}` — the `q` being what the `q^{1/2}` normalisation of the
braid letters leaves behind (`HJO.Sweep.yRepTotal_succ`) — and that operator is multiplication by
`-y_2` by `HJO.Sweep.auxVar_succ_mul_eq`. -/
theorem yRepTotal_two_mul_negYOneDPlusStar (q u : L) {r : L} (hq : q ≠ 0) (hr : r * r = q) {k : ℕ}
    (hk : 1 ≤ k) :
    yRepTotal q u r (k + 1) 2 * negYOneDPlusStar q u k
      = negYOneDPlusStar q u k * yRepTotal q u r k 1 := by
  have hy2 : yRepTotal q u r (k + 1) 2
      = q • (braidInvEnd q 1 * yRepTotal q u r (k + 1) 1 * braidInvEnd q 1) :=
    yRepTotal_succ q u hr (i := 0) (by omega)
  rw [hy2, yRepTotal_one q u r (by omega), yRepTotal_one q u r hk]
  refine LinearMap.ext fun F => ?_
  set S : Total L := dplusStar q u k F with hS
  have hsmul : ∀ W : Total L, q • W = scal q * W := fun W => by
    rw [Algebra.smul_def, ← scal_eq_algebraMap]
  have key := auxVar_succ_mul_eq q hq (i := 1) le_rfl ((auxVar 1 : Total L) * S)
  have hstar : dplusStar q u k ((auxVar 1 : Total L) * F) = auxVar 2 * S :=
    dplusStar_auxVar_mul q u (by omega) hk F
  have hL : (q • (braidInvEnd q 1 * (-LinearMap.mulLeft L (auxVar 1 : Total L)) *
        braidInvEnd q 1) * negYOneDPlusStar q u k) F
      = (auxVar 2 : Total L) * ((auxVar 1 : Total L) * S) := by
    have hstep : (q • (braidInvEnd q 1 * (-LinearMap.mulLeft L (auxVar 1 : Total L)) *
          braidInvEnd q 1) * negYOneDPlusStar q u k) F
        = q • braidInv q 1 (-((auxVar 1 : Total L) *
            braidInv q 1 (-((auxVar 1 : Total L) * S)))) := rfl
    have hinner : braidInv q 1 (-((auxVar 1 : Total L) * S))
        = -braidInv q 1 ((auxVar 1 : Total L) * S) := map_neg (braidInv q 1) _
    rw [hstep, hinner, mul_neg, neg_neg, hsmul, ← key]
  have hR : (negYOneDPlusStar q u k * (-LinearMap.mulLeft L (auxVar 1 : Total L))) F
      = (auxVar 2 : Total L) * ((auxVar 1 : Total L) * S) := by
    have hstep : (negYOneDPlusStar q u k * (-LinearMap.mulLeft L (auxVar 1 : Total L))) F
        = -((auxVar 1 : Total L) * dplusStar q u k (-((auxVar 1 : Total L) * F))) := rfl
    rw [hstep, map_neg, hstar]
    ring
  rw [hL, hR]

/-- **The one clause of `HJO.Sweep.braidRep_phiPlusStar_comp_negYOneDPlusStarPiece` that is not
discharged here**: `π_{k+1}(z_2)\,(-y_1d^*_+) = (-y_1d^*_+)\,π_k(z_1)`.

It is phrased through `HJO.Sweep.zRepTotal`, the operator the word `𝗓_i` is sent to, rather than
through `HJO.Sweep.zop`, so that it says the same thing however `HJO.Sweep.zop`'s `z_1` is
spelled. See the
module docstring for why it is not of the same kind as the three clauses above. -/
def PhiIntertwineZ (q u r : L) (k : ℕ) : Prop :=
  zRepTotal q u r (k + 1) 2 * negYOneDPlusStar q u k = negYOneDPlusStar q u k * zRepTotal q u r k 1

/-- A braid letter outside the rank goes to the identity under the representation. -/
theorem braidRepTotal_braidGenT_of_not_inRank (q u r : L) {k i : ℕ}
    (hh : BraidRepRespectsTotal q u r k) (hc : ¬ Braid.Letter.InRank k (Braid.Letter.T i)) :
    braidRepTotal q u r k hh (Braid.braidGenT k i) = 1 := by
  have hb : Braid.braidGenT k i
      = Braid.toBraidMonoid k (FreeMonoid.of (Braid.Letter.T i)) := rfl
  rw [hb, braidRepTotal_apply, braidRepFreeTotal_of, braidRepLetterTotal_of_not_inRank q u r hc]

theorem braidRepTotal_braidGenTinv_of_not_inRank (q u r : L) {k i : ℕ}
    (hh : BraidRepRespectsTotal q u r k) (hc : ¬ Braid.Letter.InRank k (Braid.Letter.Tbar i)) :
    braidRepTotal q u r k hh (Braid.braidGenTinv k i) = 1 := by
  have hb : Braid.braidGenTinv k i
      = Braid.toBraidMonoid k (FreeMonoid.of (Braid.Letter.Tbar i)) := rfl
  rw [hb, braidRepTotal_apply, braidRepFreeTotal_of, braidRepLetterTotal_of_not_inRank q u r hc]

/-- **The reduction of `HJO.Sweep.braidRep_phiPlusStar_comp_negYOneDPlusStarPiece` to one letter.**
Given the `z` clause, the first commutative diagram of Mellit's Section 5.5 commutes for every
`B ∈ 𝔹^+_k(𝕋_0)`:

`π_{k+1}(φ^*_+(B)) ∘ (-y_1d^*_+) = (-y_1d^*_+) ∘ π_k(B)`.

Both `π_{k+1} ∘ φ^*_+` and `π_k` factor through the free monoid as monoid homomorphisms, so the
property is closed under products and holds at `1`; `HJO.Braid.toBraidMonoid_surjective` reduces it
to the letters, and the four letters are the three lemmas above together with the hypothesis. The
letters outside the rank cost nothing: `HJO.Sweep.braidRepLetterTotal` sends them to the identity
on both sides, since `T_i` is out of rank at `k` exactly when `T_{i+1}` is out of rank at `k+1`.

**This is not yet `HJO.Sweep.braidRep_phiPlusStar_comp_negYOneDPlusStarPiece`**, the hypothesis
`hz` being undischarged here. -/
theorem braidRepTotal_phiPlusStar_mul_negYOneDPlusStar (q u : L) {r : L} (hq : q ≠ 0)
    (hr : r * r = q) {k : ℕ} (hk : 1 ≤ k) (h : BraidRepRespectsTotal q u r k)
    (h' : BraidRepRespectsTotal q u r (k + 1))
    (hz : PhiIntertwineZ q u r k) (B : Braid.BraidMonoid k) :
    braidRepTotal q u r (k + 1) h' (Braid.phiPlusStar k hk B) * negYOneDPlusStar q u k
      = negYOneDPlusStar q u k * braidRepTotal q u r k h B := by
  have hgen : ∀ c : Braid.Letter,
      braidRepTotal q u r (k + 1) h' (Braid.phiPlusLetter k c) * negYOneDPlusStar q u k
        = negYOneDPlusStar q u k * braidRepLetterTotal q u r k c := by
    intro c
    match c with
    | Braid.Letter.T i =>
      rcases Nat.eq_zero_or_pos i with rfl | hi
      · rw [Braid.phiPlusLetter_T_zero, map_one,
          braidRepLetterTotal_of_not_inRank q u r
            (show ¬ Braid.Letter.InRank k (Braid.Letter.T 0) by
              simp only [Braid.Letter.InRank]; omega),
          one_mul, mul_one]
      · by_cases hik : i + 1 ≤ k
        · rw [Braid.phiPlusLetter_T hi, braidRepTotal_T q u r h' (by omega) (by omega),
            braidRepLetterTotal_T q u r hi hik, smul_mul_assoc, mul_smul_comm,
            braidEnd_mul_negYOneDPlusStar q u hi (by omega)]
        · rw [Braid.phiPlusLetter_T hi,
            braidRepTotal_braidGenT_of_not_inRank q u r h'
              (show ¬ Braid.Letter.InRank (k + 1) (Braid.Letter.T (i + 1)) by
                simp only [Braid.Letter.InRank]; omega),
            braidRepLetterTotal_of_not_inRank q u r
              (show ¬ Braid.Letter.InRank k (Braid.Letter.T i) by
                simp only [Braid.Letter.InRank]; omega),
            one_mul, mul_one]
    | Braid.Letter.Tbar i =>
      rcases Nat.eq_zero_or_pos i with rfl | hi
      · rw [Braid.phiPlusLetter_Tbar_zero, map_one,
          braidRepLetterTotal_of_not_inRank q u r
            (show ¬ Braid.Letter.InRank k (Braid.Letter.Tbar 0) by
              simp only [Braid.Letter.InRank]; omega),
          one_mul, mul_one]
      · by_cases hik : i + 1 ≤ k
        · rw [Braid.phiPlusLetter_Tbar hi, braidRepTotal_Tbar q u r h' (by omega) (by omega),
            braidRepLetterTotal_Tbar q u r hi hik, smul_mul_assoc, mul_smul_comm,
            braidInvEnd_mul_negYOneDPlusStar q u hq hi (by omega)]
        · rw [Braid.phiPlusLetter_Tbar hi,
            braidRepTotal_braidGenTinv_of_not_inRank q u r h'
              (show ¬ Braid.Letter.InRank (k + 1) (Braid.Letter.Tbar (i + 1)) by
                simp only [Braid.Letter.InRank]; omega),
            braidRepLetterTotal_of_not_inRank q u r
              (show ¬ Braid.Letter.InRank k (Braid.Letter.Tbar i) by
                simp only [Braid.Letter.InRank]; omega),
            one_mul, mul_one]
    | Braid.Letter.y1 =>
      have hphi : Braid.phiPlusLetter k Braid.Letter.y1 = Braid.braidGenY (k + 1) 2 := rfl
      rw [hphi, braidRepTotal_y, braidRepLetterTotal_y1 q u r hk, ← yRepTotal_one q u r hk]
      exact yRepTotal_two_mul_negYOneDPlusStar q u hq hr hk
    | Braid.Letter.z1 =>
      have hphi : Braid.phiPlusLetter k Braid.Letter.z1 = Braid.braidGenZ (k + 1) 2 := rfl
      rw [hphi, braidRepTotal_z, braidRepLetterTotal_z1 q u r hk, ← zRepTotal_one q u r hk]
      exact hz
  have main : ∀ w : FreeMonoid Braid.Letter,
      braidRepTotal q u r (k + 1) h' (Braid.phiPlusFree k w) * negYOneDPlusStar q u k
        = negYOneDPlusStar q u k * braidRepFreeTotal q u r k w := by
    intro w
    induction w using FreeMonoid.inductionOn' with
    | one => rw [map_one, map_one, map_one, one_mul, mul_one]
    | of_mul c w ih =>
      rw [map_mul, map_mul, map_mul, mul_assoc, ih, ← mul_assoc, Braid.phiPlusFree_of,
        braidRepFreeTotal_of, hgen c, mul_assoc]
  obtain ⟨w, rfl⟩ := Braid.toBraidMonoid_surjective k B
  rw [Braid.phiPlusStar_apply, braidRepTotal_apply]
  exact main w

end Rational

end HJO.Sweep
