/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.CMStructure.CmCommutator
public import HJO.CMStructure.StarZrelOne
public meta import HJO.Attr

/-! # The mixed relation shifts

Carlsson and Mellit's `HJO.Sweep.starCommCM_cmDPlus`: for `k ≥ 1` and `1 ≤ i ≤ k`, on `V_k`,
`z_{i+1}d_+ = d_+z_i`. It is the first of the three mixed relations of `HJO.Dyck.Tilde.Atilde`,
collected with the other two in `HJO.Sweep.mixed_relations_star`.

## Main results

* `HJO.Sweep.starCommCM` — the starred commutator `d^*_+d_- - d_-d^*_+` in Carlsson and Mellit's own
  vocabulary, with `d_-` the unmodified lowering operator of `HJO.Sweep.dminusCM`.
* `HJO.Sweep.braid_one_dplusStar_cmDPlus` — `T_1d^*_+d_+ = d_+d^*_+` on `V_k`, the relation of the
  extended algebra that carries the proof.
* `HJO.Sweep.starCommCM_cmDPlus` — **the identity at `i = 1`**, in the equivalent
  form `T_1^{-1}d_+(d^*_+d_- - d_-d^*_+) = (d^*_+d_- - d_-d^*_+)d_+` on `V_k`.
* `HJO.Sweep.trainDown_starCommCM_trainUp_cmDPlus` — the relation at every `1 ≤ i ≤ k`, obtained
  from it by conjugating with the braid trains.

## The two evaluations of the reduction argument are not needed

The usual proof reduces the identity, through the two `∗`-intertwining lemmas and the spanning
principle `HJO.Sweep.exists_basis_vstar_prod_bop`, to an evaluation of both sides on `y_k^a`, and
each of the two evaluations is stated as the result of a calculation that is not displayed.

**Neither evaluation is needed, and neither is the spanning principle.** The identity
`T_1^{-1}d_+(d^*_+d_- - d_-d^*_+) = (d^*_+d_- - d_-d^*_+)d_+` is an identity of operators on the
whole of `V_k`, and it follows from three proved inputs with no expansion in the letters `y_1` and
`y_{k+1}` at all:

* `HJO.Sweep.dminusCM_cmDPlus_sub_cmDPlus_dminusCM`, read twice — once on
  `F ∈ V_k` and once on `d^*_+F ∈ V_{k+1}`;
* `T_1d^*_+d_+ = d_+d^*_+` (`HJO.Sweep.braid_one_dplusStar_cmDPlus`), also read twice — once on
  `F` and once on `d_-F ∈ V_{k-1}`;
* `d^*_+(T_{[1,k-1]}(y_kF)) = T_{[2,k]}(y_{k+1}d^*_+F)`
  (`HJO.Sweep.dplusStar_cmAscWord_auxVar_mul`), the leftover of the two commutator terms.

Both terms of `(d^*_+d_- - d_-d^*_+)d_+` are moved past `d_+` by the commutator lemma; the two
`d_+d_-` halves that come out are exactly the two terms of `T_1^{-1}d_+(d^*_+d_- - d_-d^*_+)` once
`T_1d^*_+d_+ = d_+d^*_+` is applied, and what survives is the difference of the two `(1-q)`-terms,
which is the third input. So the relation costs three rewrites and no plethysm.

The displayed comparison is nevertheless correct, and the proof here reproduces it: on `F = y_k^a`
the two `(1-q)`-terms are both `(1-q)y_{k+1}^{a+1}`, a constant that cancels in the difference, and
the surviving difference is the single expression both displays below equal. See the note on the
displays below.

## The usual proof's cancellation of its two displays is correct

The display (I) of the usual proof is
`-h_{a+1}[-X - u(q-1)y_1 - (q-1)y_{k+1}] + h_{a+1}[-X - (q-1)y_{k+1}]`
and display (II) is `F[X + u(q-1)y_1] - F[X]` with
`F[X] = -h_{a+1}[-X + (1-q)y_{k+1}] + (1-q)y_{k+1}^{a+1}`. Since `1 - q = -(q-1)` the second term of
`F` is free of `X`, so it cancels in the difference, and substituting `X + u(q-1)y_1` for `X` turns
`-X - (q-1)y_{k+1}` into `-X - u(q-1)y_1 - (q-1)y_{k+1}`: the difference is (I) term for term. Only
`1 - q = -(q-1)` and the `X`-independence of `(1-q)y_{k+1}^{a+1}` are used, and the `-X` convention
does not spoil it — the substitution acts in the `X` slot, and the letters `y_1`, `y_{k+1}` are
variables of the total space and not part of `X`. So the comparison of the two
displays is a one-line cancellation and not a plethystic computation.

Independently of the displays, the value of the evaluation is recoverable here: with
`Ω_n = (-1)^ne_n = h_n[-X]` the alternating elementary family of `HJO.Sym.elemSymmAlt`,
`(d^*_+d_- - d_-d^*_+)(y_k^a) = Ω_{a+1} - d^*_+(Ω_{a+1})` on `V_k`, which is the expression
`-h_{a+1}[-X - u(q-1)y_1] + h_{a+1}[-X]` before the substitution `τ_{k+1,k+1}` is applied.

## Which convention, and which hypotheses

The relation is stated in the **all-Carlsson--Mellit** vocabulary: `d_+` is
`HJO.Sweep.cmDPlus`, `d_-` is `HJO.Sweep.dminusCM` — the one
`HJO.Dyck.Tilde.Atilde` builds `z_i` from — and `d^*_+` is `HJO.Sweep.dplusStar`. It is therefore
free of the convention defect recorded at `HJO.Sweep.zopOneStar_dplus`, whose `z_1` is
`HJO.Sweep.zop`'s and whose `d_-` is `HJO.Sweep.dminus`.

**`q ≠ 1` is not needed.** `HJO.Dyck.Tilde.Atilde`'s `z_i` carries the prefactor `q^k/(q^{-1}-1)`,
and that prefactor is the origin of the hidden `q ≠ 1` at `HJO.Sweep.zopOneStar_dplus`. Here it
cancels: the two sides of `z_{i+1}d_+ = d_+z_i` carry the *same* scalar `q^{k+1-i}/(1-q)` —
`q^{-i}q^{k+1}` on the left against `q^{1-i}q^k` on the right — so the statements below carry no
scalar and hold for every `q`, with `q ≠ 0` read only for the braid inverses. That is strictly
stronger than the relation with the prefactor.

**The prefactor is left off the statement, as at `HJO.Sweep.zopOneStar_dplus`.** Putting it back
would need a second `z_1` in the library — `HJO.Dyck.Tilde.Atilde`'s formula read with
`HJO.Sweep.dminusCM` in place of `HJO.Sweep.dminus` — and that operator is genuinely different from
`HJO.Sweep.zopOneStar`; naming it would put two `z_1`s in the library for one symbol. What is stated
is `z_{i+1}d_+ = d_+z_i` with the common scalar removed from both sides, which is equivalent to the
identity wherever the scalar is nonzero and holds where it is not.

## The index range `1 ≤ i ≤ k` is exact at both ends

Only one relation about `d_+` is read in the passage from `i = 1` to general `i`, namely
`d_+T_j = T_{j+1}d_+` of `HJO.Sweep.cmDPlus_braid`, valid for `1 ≤ j ≤ k-1`. The trains involved are
`T_{i+1↘1}` and `T_{1↗i+1}` on `V_{k+1}` and `T_{i↘1}`, `T_{1↗i}` on `V_k`, whose letters have index
at most `i - 1`, so every use is at `j ≤ i - 1 ≤ k - 1`: the top index `i = k` is covered, and this
is not the `i = k` failure of `HJO.Sweep.dplusStar_braid`, where the cyclic shift wraps `y_{k+1}` to
`uy_1`. At `i = k + 1` the statement is not about `V_k` at all, `z_{k+2}` being outside the range
`HJO.Dyck.Aq.yElt` gives the corner elements on `V_{k+1}`. So `1 ≤ i ≤ k` is exactly right.

## References

The lemma `HJO.Sweep.starCommCM_cmDPlus`, with `HJO.Sweep.piece`, `HJO.Sweep.cmDPlus`,
`HJO.Sweep.dplusStar`, `HJO.Dyck.Tilde.Atilde` and `HJO.Dyck.Aq.yElt`; consumed by
`HJO.Sweep.exists_isDpaAction_star`. Proved here from
`HJO.Sweep.dminusCM_cmDPlus_sub_cmDPlus_dminusCM`, `HJO.Sweep.dplusStar_braidInv`,
`HJO.Sweep.cmDPlus_braid` and `HJO.Sweep.dminusCM_braid` rather than from
`HJO.Sweep.dplusStar_twistedActionMult`, `HJO.Sweep.dminusCM_twistedActionMult`,
`HJO.Sweep.braid_add_q_completeHomog_twist` and `HJO.Sweep.exists_basis_vstar_prod_bop`, none of
which is read. Transcribing E. Carlsson and A. Mellit, *A proof of the shuffle conjecture*, Section
5, and A. Mellit, *Toric braids and `(m, n)`-parking functions*, §3.6.
-/

@[expose] public section

namespace HJO

/-! ### Moving an element through a descending word -/

namespace Braid

variable {M : Type*} [Monoid M]

/-- **A conjugation carries a descending word to its shift**, the mirror of
`HJO.Braid.mul_ascendingWord`: every letter of `T_{a-1} ⋯ T_b` moves to the next index, and the
shifted word is `T_a ⋯ T_{b+1}` because shifting an index range by one is
`HJO.Braid.map_range'_succ`. -/
theorem mul_descendingWord {T : ℕ → M} {W : M} {a b : ℕ}
    (key : ∀ i, b ≤ i → i < a → W * T i = T (i + 1) * W) :
    W * descendingWord T a b = descendingWord T (a + 1) (b + 1) * W := by
  have h2 : descendingWord T (a + 1) (b + 1)
      = ((List.range' b (a - b)).reverse.map (T ∘ (· + 1))).prod := by
    rw [descendingWord, show a + 1 - (b + 1) = a - b from by omega,
      ← map_range'_succ b (a - b), ← List.map_reverse, List.map_map]
  rw [descendingWord, h2]
  refine mul_prod_shift fun j hj => ?_
  rw [List.mem_reverse, List.mem_range'_1] at hj
  exact key j (by omega) (by omega)

end Braid

namespace Sweep

section Field

variable {L : Type*} [Field L]

/-! ### The starred raising operator against the word of `d_+` -/

/-- `T_i^{-1}` is linear over the scalars of `𝕜`, being a polynomial in `T_i`. -/
private theorem braidInv_scal_mul' (q : L) (i : ℕ) (x : L) (G : Total L) :
    braidInv q i (scal x * G) = scal x * braidInv q i G := by
  rw [braidInv_apply, braidInv_apply, braid_scal_mul]
  ring

private theorem qshift_scal' (q : L) (i : ℕ) (x : L) :
    qshift q i (scal x : Total L) = scal x := by
  rw [scal_eq_algebraMap, AlgHom.commutes]

/-- `d^*_+` is linear over the scalars of `𝕜`, both its factors being algebra maps. -/
theorem dplusStar_scal_mul (q u : L) (k : ℕ) (x : L) (F : Total L) :
    dplusStar q u k (scal x * F) = scal x * dplusStar q u k F := by
  rw [dplusStar_apply, dplusStar_apply, map_mul, qshift_scal', map_mul, cycleShift_scal]

/-- **`d^*_+` conjugates the word of `d_+` up by one**: `d^*_+T_{[1,b]} = T_{[2,b+1]}d^*_+` on
`V_{b+1}`, every letter of the word having index below `b + 1`
(`HJO.Sweep.dplusStar_mul_braidEnd`). -/
theorem dplusStar_mul_cmAscWord (q u : L) (b : ℕ) :
    dplusStar q u (b + 1) * cmAscWord q 1 b
      = cmAscWord q 2 (b + 1) * dplusStar q u (b + 1) := by
  rw [cmAscWord_eq_ascendingWord q (by omega), cmAscWord_eq_ascendingWord q (by omega)]
  exact Braid.mul_ascendingWord (by omega) fun i hi hib =>
    dplusStar_mul_braidEnd q u hi (by omega)

/-- **`d^*_+(T_{[1,m]}(y_{m+1}F)) = T_{[2,m+1]}(y_{m+2}d^*_+F)`.** The `(1-q)`-terms of the two
readings of `HJO.Sweep.dminusCM_cmDPlus_sub_cmDPlus_dminusCM` used in `HJO.Sweep.starCommCM_cmDPlus`
differ by exactly this identity: `d^*_+` shifts every letter of the word up by one
(`HJO.Sweep.dplusStar_mul_cmAscWord`) and raises the index of the multiplier
(`HJO.Sweep.dplusStar_auxVar_mul`, the third clause of `HJO.Sweep.dplusStar_braidInv`), and the two
shifts are the two the right-hand side displays. -/
theorem dplusStar_cmAscWord_auxVar_mul (q u : L) (m : ℕ) (F : Total L) :
    dplusStar q u (m + 1) (cmAscWord q 1 m ((auxVar (m + 1) : Total L) * F))
      = cmAscWord q 2 (m + 1) ((auxVar (m + 1 + 1) : Total L) * dplusStar q u (m + 1) F) := by
  have h := LinearMap.congr_fun (dplusStar_mul_cmAscWord q u m)
    ((auxVar (m + 1) : Total L) * F)
  rw [Module.End.mul_apply, Module.End.mul_apply] at h
  rw [h, dplusStar_auxVar_mul q u (show 1 ≤ m + 1 by omega) (le_refl (m + 1))]

/-! ### The raising operator against the braid trains -/

private theorem trainDownEnd_pos_eq_descendingWord (q : L) {j : ℕ} (hj : 1 ≤ j) :
    trainDownEnd q j 1 = Braid.descendingWord (braidEnd q) j 1 := by
  rw [trainDownEnd, Braid.trainDown]
  exact ite_eq_left_of_eq_true _ _ (eq_true hj)

private theorem trainUpEnd_one_pos_eq_ascendingWord (q : L) {j : ℕ} (hj : 1 ≤ j) :
    trainUpEnd q 1 j = Braid.ascendingWord (braidEnd q) 1 j := by
  rw [trainUpEnd, Braid.trainUp]
  exact ite_eq_left_of_eq_true _ _ (eq_true hj)

/-- `d_+T_j^{-1} = T_{j+1}^{-1}d_+` for `1 ≤ j ≤ k-1`, `HJO.Sweep.cmDPlus_braid` read on an inverted
letter. -/
private theorem cmDPlus_mul_braidInvEnd (q : L) (hq : q ≠ 0) {k j : ℕ} (hj : 1 ≤ j)
    (hjk : j + 1 ≤ k) :
    cmDPlus q k * braidInvEnd q j = braidInvEnd q (j + 1) * cmDPlus q k :=
  Braid.comm_shift_inv (braidEnd_mul_braidInvEnd q hq j)
    (braidInvEnd_mul_braidEnd q hq (j + 1)) (cmDPlus_mul_braidEnd q hj hjk)

/-- **`T_{1↗i+1}d_+ = T_1d_+T_{1↗i}`** for `1 ≤ i ≤ k`: the ascending train absorbs the letter
`d_+` produces at every index it passes, and the head letter `T_1` is what is left over. -/
private theorem trainUpEnd_one_succ_mul_cmDPlus (q : L) {k i : ℕ} (hi : 1 ≤ i) (hik : i ≤ k) :
    trainUpEnd q 1 (i + 1) * cmDPlus q k
      = braidEnd q 1 * cmDPlus q k * trainUpEnd q 1 i := by
  have hshift : cmDPlus q k * Braid.ascendingWord (braidEnd q) 1 i
      = Braid.ascendingWord (braidEnd q) 2 (i + 1) * cmDPlus q k :=
    Braid.mul_ascendingWord (by omega) fun j hj hji =>
      cmDPlus_mul_braidEnd q hj (by omega)
  have hsplit : Braid.ascendingWord (braidEnd q) 1 (i + 1)
      = braidEnd q 1 * Braid.ascendingWord (braidEnd q) 2 (i + 1) := by
    rw [← Braid.ascendingWord_succ_self (braidEnd q) 1,
      Braid.ascendingWord_mul (braidEnd q) (by omega) (by omega)]
  rw [trainUpEnd_one_pos_eq_ascendingWord q (show 1 ≤ i + 1 by omega),
    trainUpEnd_one_pos_eq_ascendingWord q hi, hsplit]
  simp only [mul_assoc]
  rw [hshift]

/-- **`d_+T_{i↘1} = T_{i+1↘1}T_1^{-1}d_+`** for `1 ≤ i ≤ k`: `d_+` shifts every letter of the
descending train up by one, and the shifted train is `T_{i+1↘2} = T_{i+1↘1}T_1^{-1}`. -/
private theorem cmDPlus_mul_trainDownEnd (q : L) (hq : q ≠ 0) {k i : ℕ} (hi : 1 ≤ i)
    (hik : i ≤ k) :
    cmDPlus q k * trainDownEnd q i 1
      = trainDownEnd q (i + 1) 1 * braidInvEnd q 1 * cmDPlus q k := by
  have hshift : cmDPlus q k * Braid.descendingWord (braidEnd q) i 1
      = Braid.descendingWord (braidEnd q) (i + 1) 2 * cmDPlus q k :=
    Braid.mul_descendingWord fun j hj hji => cmDPlus_mul_braidEnd q hj (by omega)
  have hsplit : Braid.descendingWord (braidEnd q) (i + 1) 1
      = Braid.descendingWord (braidEnd q) (i + 1) 2 * braidEnd q 1 := by
    rw [← Braid.descendingWord_succ_self (braidEnd q) 1,
      Braid.descendingWord_mul (braidEnd q) (by omega) (by omega)]
  have hsplit' : Braid.descendingWord (braidEnd q) (i + 1) 2
      = Braid.descendingWord (braidEnd q) (i + 1) 1 * braidInvEnd q 1 := by
    rw [hsplit, mul_assoc, braidEnd_mul_braidInvEnd q hq, mul_one]
  rw [trainDownEnd_pos_eq_descendingWord q hi,
    trainDownEnd_pos_eq_descendingWord q (show 1 ≤ i + 1 by omega), hshift, hsplit']

/-- **`T^*_{k+1↘1}T_1d_+ = d_+T^*_{k↘1}`**: the starred train of the inverted letters is shortened
by the letter `T_1` to `T^*_{k+1↘2}`, and `d_+` shifts every letter of `T^*_{k↘1}` into exactly
that word. -/
private theorem trainUpEnd_star_mul_braidEnd_one_mul_cmDPlus (q : L) (hq : q ≠ 0) (c : ℕ) :
    trainUpEnd q (c + 1 + 1) 1 * braidEnd q 1 * cmDPlus q (c + 1)
      = cmDPlus q (c + 1) * trainUpEnd q (c + 1) 1 := by
  have hshift : cmDPlus q (c + 1) * Braid.descendingWord (braidInvEnd q) (c + 1) 1
      = Braid.descendingWord (braidInvEnd q) (c + 1 + 1) 2 * cmDPlus q (c + 1) :=
    Braid.mul_descendingWord fun j hj hjk => cmDPlus_mul_braidInvEnd q hq hj (by omega)
  have hsplit : Braid.descendingWord (braidInvEnd q) (c + 1 + 1) 1
      = Braid.descendingWord (braidInvEnd q) (c + 1 + 1) 2 * braidInvEnd q 1 := by
    rw [← Braid.descendingWord_succ_self (braidInvEnd q) 1,
      Braid.descendingWord_mul (braidInvEnd q) (by omega) (by omega)]
  have hsplit' : Braid.descendingWord (braidInvEnd q) (c + 1 + 1) 1 * braidEnd q 1
      = Braid.descendingWord (braidInvEnd q) (c + 1 + 1) 2 := by
    rw [hsplit, mul_assoc, braidInvEnd_mul_braidEnd q hq, mul_one]
  rw [trainUpEnd_eq_descendingWord q (c + 1), trainUpEnd_eq_descendingWord q c, hsplit', ← hshift]

end Field

/-! ### The starred commutator in Carlsson and Mellit's vocabulary -/

section Newton

variable {L : Type*} [Field L] [Algebra ℚ L]

/-- The commutator `d^*_+d_- - d_-d^*_+` on `V_k`, with `d_-` the **unmodified** lowering operator
of `HJO.Sweep.dminusCM` — the one `HJO.Dyck.Tilde.Atilde` writes `z_i` with. The indices record the
graded piece each factor is read on.

This is not `HJO.Sweep.starComm`, which is the same expression with the modified lowering operator
`d^♭_-` of `HJO.Sweep.dminus` that `HJO.Sweep.zop` names; the two differ by the last letter,
`HJO.Sweep.dminusCM_eq_neg_dminus_auxVar_mul` being the displacement. -/
noncomputable def starCommCM (q u : L) (k : ℕ) : Module.End L (Total L) :=
  dplusStar q u (k - 1) * dminusCM q k - dminusCM q (k + 1) * dplusStar q u k

/-- The starred commutator at a successor index, applied, with no truncated subtraction. -/
theorem starCommCM_succ_apply (q u : L) (m : ℕ) (F : Total L) :
    starCommCM q u (m + 1) F
      = dplusStar q u m (dminusCM q (m + 1) F)
        - dminusCM q (m + 1 + 1) (dplusStar q u (m + 1) F) := rfl

/-- **The two starred commutators differ by the last letter and nothing else**:
`[d^*_+, d_-] = -[d^*_+, d^♭_-] \circ (y_k \cdot)` on `V_k`, for `k = m + 1`.

This is the displacement `HJO.Sweep.dminusCM_eq_neg_dminus_auxVar_mul` carried through *both*
summands of the commutator, and it closes because the second summand's displacement is by `y_{k+1}`
where the first's is by `y_k`, and `HJO.Sweep.dplusStar_auxVar_mul`
(`HJO.Sweep.dplusStar_braidInv`'s third clause) turns the one into the other. So the whole
reconciliation of the two `d_-` conventions *inside the commutator* is these two lemmas and
no new mathematics.

**It does not reconcile the two `z_1`s.** `HJO.Sweep.zopOneStar` — the operator
`HJO.Sweep.zop` and `HJO.Sweep.zRep` are built on — is
`q^k/(1-q) \cdot [d^*_+, d^♭_-] \circ T^*_{k↘1}`, while the `z_1` of `HJO.Dyck.Tilde.Atilde` that
the starred action `HJO.Sweep.exists_isDpaAction_star` realises is the same scalar times
`[d^*_+, d_-] \circ T^*_{k↘1}`. By this lemma the second is the first with `-(y_k \cdot)`
inserted **between the commutator and the train**, and `y_k` does not commute with
`T^*_{k↘1}`: that word contains `T_{k-1}^{-1}`, which moves `y_k`. (What *is* proved is the
neighbouring fact that `y_1` commutes with the shortened train `T^*_{k↘2}`, whose letters all have
index `≥ 2`.) So the two `z_1`s are two different operators, not two spellings of one, and
transporting a commutation statement from `HJO.Dyck.Aq` across that action gives it for the
Carlsson--Mellit family, not for `HJO.Sweep.zop`. -/
theorem starCommCM_eq_neg_starComm_auxVar_mul (q u : L) (m : ℕ) :
    starCommCM q u (m + 1)
      = -(starComm q u (m + 1) * LinearMap.mulLeft L (auxVar (m + 1) : Total L)) := by
  refine LinearMap.ext fun F => ?_
  have hshift : (auxVar (m + 1 + 1) : Total L) * dplusStar q u (m + 1) F
      = dplusStar q u (m + 1) ((auxVar (m + 1) : Total L) * F) :=
    (dplusStar_auxVar_mul q u (show 1 ≤ m + 1 by omega) le_rfl F).symm
  rw [starCommCM_succ_apply, dminusCM_eq_neg_dminus_auxVar_mul q m,
    dminusCM_eq_neg_dminus_auxVar_mul q (m + 1), map_neg, hshift]
  simp only [starComm, LinearMap.neg_apply, Module.End.mul_apply, LinearMap.sub_apply,
    LinearMap.mulLeft_apply, Nat.add_sub_cancel]
  ring

/-- **`d_-` carries `V_{k+1}` into `V_k`**, the codomain `HJO.Sweep.dminusCM` gives it, read through
the comparison `d_-F = -d^♭_-(y_{k+1}F)` of `HJO.Sweep.dminusCM_eq_neg_dminus_auxVar_mul`. -/
private theorem dminusCM_mem_piece' (q : L) (k : ℕ) {F : Total L} (hF : F ∈ piece L (k + 1)) :
    dminusCM q (k + 1) F ∈ piece L k := by
  rw [dminusCM_eq_neg_dminus_auxVar_mul]
  refine neg_mem ?_
  have h := dminus_mem_piece q (k + 1)
    (mul_mem (auxVar_mem_piece (by omega) le_rfl) hF)
  simpa using h

/-! ### `T_1d^*_+d_+ = d_+d^*_+` -/

/-- **`T_1d^*_+d_+ = d_+d^*_+` on `V_k`.** Both composites add the two letters `(q-1)y_{k+2}` and
`(q-1)uy_1` to the alphabet and carry `y_1, …, y_k` to `y_2, …, y_{k+1}`; the words differ by the
single letter `T_1`.

`d^*_+` conjugates the word `T_{[1,k]}` of `d_+` into `T_{[2,k+1]}`
(`HJO.Sweep.dplusStar_mul_cmAscWord`) and passes the substitution at the cost of one index
(`HJO.Sweep.dplusStar_qshift_of_mem_piece`), which is where `F ∈ V_k` is read; what is left is
`T_{[1,k+1]} = T_1T_{[2,k+1]}`.

This relation of `HJO.Dyck.Tilde.Atilde` is not one of its three further relations: it is the
relation between the two raising arrows, and it is what lets the commutator of
`HJO.Sweep.dminusCM_cmDPlus_sub_cmDPlus_dminusCM` be read on `d^*_+F` in the proof of
`HJO.Sweep.starCommCM_cmDPlus`. -/
theorem braid_one_dplusStar_cmDPlus (q u : L) {k : ℕ} {F : Total L} (hF : F ∈ piece L k) :
    braid q 1 (dplusStar q u (k + 1) (cmDPlus q k F))
      = cmDPlus q (k + 1) (dplusStar q u k F) := by
  have hstep : dplusStar q u (k + 1) (cmAscWord q 1 k (qshift q (k + 1) F))
      = cmAscWord q 2 (k + 1) (dplusStar q u (k + 1) (qshift q (k + 1) F)) := by
    have h := LinearMap.congr_fun (dplusStar_mul_cmAscWord q u k) (qshift q (k + 1) F)
    rw [Module.End.mul_apply, Module.End.mul_apply] at h
    exact h
  rw [cmDPlus_apply, hstep, dplusStar_qshift_of_mem_piece q u hF, cmDPlus_apply,
    cmAscWord_apply_succ_left q (show 1 ≤ k + 1 by omega)]

/-! ### The relation at the first index -/

/-- **`HJO.Sweep.starCommCM_cmDPlus` at `i = 1`**, in the equivalent displayed form: for
`k ≥ 1` and `F ∈ V_k`,

`(d^*_+d_- - d_-d^*_+)(d_+F) = T_1^{-1}(d_+((d^*_+d_- - d_-d^*_+)F))`,

read at `k = m + 1`. Every operator is Carlsson and Mellit's own: `d_+` of `HJO.Sweep.cmDPlus`,
`d_-` of `HJO.Sweep.dminusCM`, `d^*_+` of `HJO.Sweep.dplusStar`.

Three rewrites, no plethysm and no spanning principle.
`HJO.Sweep.dminusCM_cmDPlus_sub_cmDPlus_dminusCM` moves `d_-` past `d_+` on `F` and again on
`d^*_+F`, leaving the two `d_+d_-` halves and two `(1-q)`-terms;
`HJO.Sweep.braid_one_dplusStar_cmDPlus` identifies the halves with the two terms of the right-hand
side — once on `F`, once on `d_-F ∈ V_{k-1}`; and `HJO.Sweep.dplusStar_cmAscWord_auxVar_mul` cancels
the two `(1-q)`-terms against each other.

`q ≠ 0` is read only for the braid inverses; `q ≠ 1` is not read at all. -/
@[hjo "lem_cm_star_zrel_shift"]
theorem starCommCM_cmDPlus (q u : L) (hq : q ≠ 0) {m : ℕ} {F : Total L}
    (hF : F ∈ piece L (m + 1)) :
    starCommCM q u (m + 1 + 1) (cmDPlus q (m + 1) F)
      = braidInv q 1 (cmDPlus q (m + 1) (starCommCM q u (m + 1) F)) := by
  have hAmem : dminusCM q (m + 1) F ∈ piece L m := dminusCM_mem_piece' q m hF
  have hGmem : dplusStar q u (m + 1) F ∈ piece L (m + 1 + 1) := dplusStar_mem_piece q u hF
  -- `HJO.Sweep.dminusCM_cmDPlus_sub_cmDPlus_dminusCM` on `F`
  have hc1 : dminusCM q (m + 1 + 1) (cmDPlus q (m + 1) F)
      = cmDPlus q m (dminusCM q (m + 1) F)
        + scal (1 - q) * cmAscWord q 1 m ((auxVar (m + 1) : Total L) * F) := by
    have h := dminusCM_cmDPlus_sub_cmDPlus_dminusCM q m hF
    linear_combination h
  -- `HJO.Sweep.dminusCM_cmDPlus_sub_cmDPlus_dminusCM` on `d^*_+F`
  have hc2 : dminusCM q (m + 1 + 1 + 1) (cmDPlus q (m + 1 + 1) (dplusStar q u (m + 1) F))
      = cmDPlus q (m + 1) (dminusCM q (m + 1 + 1) (dplusStar q u (m + 1) F))
        + scal (1 - q) * cmAscWord q 1 (m + 1)
            ((auxVar (m + 1 + 1) : Total L) * dplusStar q u (m + 1) F) := by
    have h := dminusCM_cmDPlus_sub_cmDPlus_dminusCM q (m + 1) hGmem
    linear_combination h
  -- `T_1d^*_+d_+ = d_+d^*_+` on `F`, read backwards
  have hs1 : dplusStar q u (m + 1 + 1) (cmDPlus q (m + 1) F)
      = braidInv q 1 (cmDPlus q (m + 1 + 1) (dplusStar q u (m + 1) F)) := by
    rw [← braid_one_dplusStar_cmDPlus q u hF, braidInv_braid q hq]
  -- `T_1d^*_+d_+ = d_+d^*_+` on `d_-F`
  have hs2 : dplusStar q u (m + 1) (cmDPlus q m (dminusCM q (m + 1) F))
      = braidInv q 1 (cmDPlus q (m + 1) (dplusStar q u m (dminusCM q (m + 1) F))) := by
    rw [← braid_one_dplusStar_cmDPlus q u hAmem, braidInv_braid q hq]
  -- `d_-` passes `T_1^{-1}` on `V_{k+2}`
  have hcomm : ∀ Z : Total L, dminusCM q (m + 1 + 1 + 1) (braidInv q 1 Z)
      = braidInv q 1 (dminusCM q (m + 1 + 1 + 1) Z) := by
    intro Z
    have h := LinearMap.congr_fun (Braid.comm_inv_right (braidEnd_mul_braidInvEnd q hq 1)
      (braidInvEnd_mul_braidEnd q hq 1)
      (dminusCM_mul_braidEnd q (show (1 : ℕ) ≤ m + 1 by omega))) Z
    rw [Module.End.mul_apply, Module.End.mul_apply] at h
    exact h
  -- the two `(1-q)`-terms
  have hleft : dplusStar q u (m + 1)
        (scal (1 - q) * cmAscWord q 1 m ((auxVar (m + 1) : Total L) * F))
      = scal (1 - q) * cmAscWord q 2 (m + 1)
          ((auxVar (m + 1 + 1) : Total L) * dplusStar q u (m + 1) F) := by
    rw [dplusStar_scal_mul, dplusStar_cmAscWord_auxVar_mul]
  have hright : braidInv q 1 (scal (1 - q) * cmAscWord q 1 (m + 1)
        ((auxVar (m + 1 + 1) : Total L) * dplusStar q u (m + 1) F))
      = scal (1 - q) * cmAscWord q 2 (m + 1)
          ((auxVar (m + 1 + 1) : Total L) * dplusStar q u (m + 1) F) := by
    rw [braidInv_scal_mul', cmAscWord_apply_succ_left q (show 1 ≤ m + 1 by omega),
      braidInv_braid q hq]
  rw [starCommCM_succ_apply, starCommCM_succ_apply, hc1, hs1, hcomm, hc2, map_add, map_add,
    map_sub, map_sub, hs2, hleft, hright]
  abel

/-! ### The evaluation point -/

/-- **The starred commutator on `y_k^a`**, the element the usual proof evaluates both
sides of the relation on: for `k ≥ 1`, written at `k = m + 1`,

`(d^*_+d_- - d_-d^*_+)(y_k^a) = Ω_{a+1} - d^*_+(Ω_{a+1})`,

with `Ω_n = (-1)^ne_n` the alternating elementary family of `HJO.Sym.elemSymmAlt`, which is
`h_n[-X]`. In the plethystic notation the right-hand side is
`-h_{a+1}[-X - u(q-1)y_1] + h_{a+1}[-X]`, `d^*_+` adding the single letter `u(q-1)y_1` to the
alphabet; applying `τ_{k+1,k+1}` to it gives the first display
`-h_{a+1}[-X - u(q-1)y_1 - (q-1)y_{k+1}] + h_{a+1}[-X - (q-1)y_{k+1}]` verbatim.

Both terms are one value of `HJO.Sweep.dminusCM_auxVar_pow_mul`: `d_-(y_k^a) = -Ω_{a+1}` and,
`d^*_+` carrying `y_k` to `y_{k+1}`, also `d_-(d^*_+(y_k^a)) = -Ω_{a+1}`. So the difference is the
failure of `d^*_+` to fix `Ω_{a+1}`, and nothing about the letters is expanded. -/
theorem starCommCM_auxVar_pow (q u : L) (m a : ℕ) :
    starCommCM q u (m + 1) ((auxVar (m + 1) : Total L) ^ a)
      = MvPolynomial.C (Sym.elemSymmAlt L ((a : ℤ) + 1))
        - dplusStar q u m (MvPolynomial.C (Sym.elemSymmAlt L ((a : ℤ) + 1))) := by
  have hlow : ∀ j : ℕ, dminusCM q (j + 1) ((auxVar (j + 1) : Total L) ^ a)
      = -MvPolynomial.C (Sym.elemSymmAlt L ((a : ℤ) + 1)) := by
    intro j
    have h := dminusCM_auxVar_pow_mul q j a (F := (1 : Total L)) (one_mem _)
    rw [mul_one, bopExt_one] at h
    exact h
  have hstar : dplusStar q u (m + 1) ((auxVar (m + 1) : Total L) ^ a)
      = (auxVar (m + 1 + 1) : Total L) ^ a := by
    have hX : (auxVar (m + 1) : Total L) = MvPolynomial.X m := by rw [auxVar, Nat.add_sub_cancel]
    have hX' : (auxVar (m + 1 + 1) : Total L) = MvPolynomial.X (m + 1) := by
      rw [auxVar, Nat.add_sub_cancel]
    rw [← dplusStarAlg_eq_dplusStar, map_pow, hX, hX',
      dplusStarAlg_X_of_lt q u (show m < m + 1 by omega)]
  rw [starCommCM_succ_apply, hlow m, hstar, hlow (m + 1), map_neg, sub_neg_eq_add, neg_add_eq_sub]

/-- **The relation at the evaluation point**: `HJO.Sweep.starCommCM_cmDPlus` at `i = 1` read on
`F = y_k^a`. Both sides of the display are this one element, so the assertion of the usual proof
that its two displays agree is verified here without either being expanded in the letters `y_1` and
`y_{k+1}`. -/
theorem starCommCM_cmDPlus_auxVar_pow (q u : L) (hq : q ≠ 0) (m a : ℕ) :
    starCommCM q u (m + 1 + 1) (cmDPlus q (m + 1) ((auxVar (m + 1) : Total L) ^ a))
      = braidInv q 1 (cmDPlus q (m + 1) (MvPolynomial.C (Sym.elemSymmAlt L ((a : ℤ) + 1))
          - dplusStar q u m (MvPolynomial.C (Sym.elemSymmAlt L ((a : ℤ) + 1))))) := by
  rw [starCommCM_cmDPlus q u hq (pow_mem (auxVar_mem_piece (by omega) (le_refl (m + 1))) a),
    starCommCM_auxVar_pow]

/-! ### The relation at every admissible index -/

/-- **`HJO.Sweep.starCommCM_cmDPlus`**: for `k ≥ 1` and `1 ≤ i ≤ k`, on `V_k`,
`z_{i+1}d_+ = d_+z_i`, with the common prefactor `q^{k+1-i}/(1-q)` of `HJO.Dyck.Tilde.Atilde`
removed from both sides.

Unwinding `HJO.Dyck.Tilde.Atilde`'s recursion `z_i = qT_i^{-1}z_{i+1}T_i^{-1}` writes
`z_{i+1} = q^{-i}T_{i+1↘1}z_1T_{1↗i+1}` with `z_1 = q^k/(1-q)(d^*_+d_- - d_-d^*_+)T^*_{k↘1}`, so the
claim is that

`T_{i+1↘1}CT^*_{k+1↘1}T_{1↗i+1}d_+ = d_+T_{i↘1}CT^*_{k↘1}T_{1↗i}`,
where `C` is the starred commutator `d^*_+d_- - d_-d^*_+` at the level it is read on,

on `V_k`, which is what is stated. The scalars agree on the two sides — `q^{-i}q^{k+1}` against
`q^{1-i}q^k` — which is why `q ≠ 1` never appears.

Three train identities reduce this to `HJO.Sweep.starCommCM_cmDPlus`, the case `i = 1`:
`T_{1↗i+1}d_+ = T_1d_+T_{1↗i}` and `d_+T_{i↘1} = T_{i+1↘1}T_1^{-1}d_+` move `d_+` through the two
conjugating trains, and `T^*_{k+1↘1}T_1d_+ = d_+T^*_{k↘1}` moves it through the train of `z_1`. Each
reads only `d_+T_j = T_{j+1}d_+` at indices `j ≤ i - 1 ≤ k - 1`, which is why the range `1 ≤ i ≤ k`
is exact at the top end. -/
@[hjo "lem_cm_star_zrel_shift"]
theorem trainDown_starCommCM_trainUp_cmDPlus (q u : L) (hq : q ≠ 0) {k i : ℕ} (hi : 1 ≤ i)
    (hik : i ≤ k) {F : Total L} (hF : F ∈ piece L k) :
    trainDownEnd q (i + 1) 1 (starCommCM q u (k + 1)
        (trainUpEnd q (k + 1) 1 (trainUpEnd q 1 (i + 1) (cmDPlus q k F))))
      = cmDPlus q k (trainDownEnd q i 1 (starCommCM q u k
          (trainUpEnd q k 1 (trainUpEnd q 1 i F)))) := by
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
  have hmem : trainUpEnd q (m + 1) 1 (trainUpEnd q 1 i F) ∈ piece L (m + 1) :=
    trainUpEnd_mem_piece q (le_refl (m + 1)) (by omega)
      (trainUpEnd_mem_piece q (by omega) hik hF)
  have h1 := LinearMap.congr_fun (trainUpEnd_one_succ_mul_cmDPlus q hi hik) F
  have h2 := LinearMap.congr_fun
    (trainUpEnd_star_mul_braidEnd_one_mul_cmDPlus q hq m) (trainUpEnd q 1 i F)
  have h3 := LinearMap.congr_fun (cmDPlus_mul_trainDownEnd q hq hi hik)
    (starCommCM q u (m + 1) (trainUpEnd q (m + 1) 1 (trainUpEnd q 1 i F)))
  have hbe : ∀ Z : Total L, braidInvEnd q 1 Z = braidInv q 1 Z := fun _ => rfl
  simp only [Module.End.mul_apply, hbe] at h1 h2 h3
  rw [h1, h2, starCommCM_cmDPlus q u hq hmem, ← h3]

end Newton

end Sweep

end HJO
