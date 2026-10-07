/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.CMStructure.DminusBraid
public import HJO.Shuffle.CMRaising
public meta import HJO.Attr

/-! # The modified generators, at their stated indices

Mellit's §3 works not with the operators of `HJO.Sweep.cmDPlus` and `HJO.Sweep.dminusCM` but with
modified ones, `d^♭_+` and `d^♭_-`. Both are already defined as the operators of the sweep process —
`d^♭_-` is `HJO.Sweep.dminus`, and `d^♭_+` is `HJO.Sweep.dplus`, whose defining formula
`-T_1T_2⋯T_k(y_{k+1}τ_{k+1,k+1}(F))` is *verbatim* the one `HJO.Sweep.dplus_eq_ascWord` displays.
This file states the two facts about them that differ from the existing statements only by index
bookkeeping:

* the modified raising operator: `HJO.Sweep.dplus_eq_ascWord` exhibits `HJO.Sweep.dplus` as the
  displayed composite `T_1(T_2(⋯T_k(y_{k+1}τ(F))⋯))`, with
  `HJO.Sweep.dplus_zero_apply` and `HJO.Sweep.dplus_apply_head` the two boundary conventions — the
  empty composite at `k = 0` and the head letter `T_1` for `k ≥ 1`.
* the modified lowering operator against the distant braid generators: `HJO.Sweep.braid_dminus`,
  at `k ≥ 2`, `1 ≤ i ≤ k-2`.

## Main results

* `HJO.Sweep.dplus_eq_ascWord`, `HJO.Sweep.dplus_zero_apply`, `HJO.Sweep.dplus_apply_head` — the
  modified raising operator as a displayed composite.
* `HJO.Sweep.braid_dminus`.

## Implementation notes

**The modified raising operator is an equation, not a second operator.**
`HJO.Sweep.dplus_eq_ascWord` has `HJO.Sweep.dplus` on its left, so a consumer of
`HJO.Sweep.dplus_eq_ascWord` gets that operator and nothing else; no copy of it is made, and the
content — that the sweep process's raising operator is Mellit's modified one — is exactly what the
equation says.

**The `1 ≤ i` is dropped from `HJO.Sweep.braid_dminus`**, and so is its `F ∈ V_k`:
at the unread index `0` the braid operator is the identity and the statement is trivial, and
`HJO.Sweep.dminus_braid` reads neither hypothesis. The upper bound `i ≤ k-2` is *not*
droppable and is carried as `i + 2 ≤ k`: the extraction `HJO.Sweep.lowerCoeff` deletes the exponent
of `y_k`, so a braid operator touching `y_{k-1}` and `y_k` does not pass it.

## References

A. Mellit, *Toric braids and `(m, n)`-parking functions*, §3.
-/

@[expose] public section

namespace HJO.Sweep

section Field

variable {L : Type*} [Field L]

/-! ### The modified raising operator -/

/-- **The modified raising operator `d^♭_+`**, `HJO.Sweep.dplus_eq_ascWord`: for `k ≥ 0` and
`F ∈ V_k`,
`d^♭_+F = -T_1(T_2(⋯T_k(y_{k+1}τ_{k+1,k+1}(F))⋯))`,
the composite of `T_1, …, T_k` being the identity when `k = 0`.

That composite is the ascending word `T_{[1,k]}` of `HJO.Sweep.cmAscWord`, and the operator is
`HJO.Sweep.dplus` — the raising operator of the sweep process, whose formula is the same one with
the word written as a train. The modified raising operator and that of the sweep process are one
operator, exactly as the modified lowering operator and that of the sweep process are both
`HJO.Sweep.dminus`. -/
@[hjo "def_vmod_dplus_mod"]
theorem dplus_eq_ascWord (q : L) (k : ℕ) (F : Total L) :
    dplus q k F = -cmAscWord q 1 k ((auxVar (k + 1) : Total L) * qshift q (k + 1) F) :=
  dplus_apply q k F

/-- **The empty composite at `k = 0`**: `d^♭_+F = -y_1τ_{1,1}(F)`, the convention that
`T_1 ⋯ T_k` is the identity when `k = 0`. -/
@[hjo "def_vmod_dplus_mod"]
theorem dplus_zero_apply (q : L) (F : Total L) :
    dplus q 0 F = -((auxVar 1 : Total L) * qshift q 1 F) := by
  rw [dplus_eq_ascWord, cmAscWord_self_pred]
  rfl

/-- **The head letter of the composite**: `d^♭_+F = -T_1(T_{[2,k]}(y_{k+1}τ_{k+1,k+1}(F)))` for
`k ≥ 1`. Iterating it strips the word one letter at a time, which is the display. -/
@[hjo "def_vmod_dplus_mod"]
theorem dplus_apply_head (q : L) {k : ℕ} (hk : 1 ≤ k) (F : Total L) :
    dplus q k F
      = -braid q 1 (cmAscWord q 2 k ((auxVar (k + 1) : Total L) * qshift q (k + 1) F)) := by
  rw [dplus_eq_ascWord, cmAscWord_apply_succ_left q hk]

end Field

section Rational

variable {L : Type*} [Field L] [Algebra ℚ L]

/-! ### The modified lowering operator against the distant braid generators -/

/-- **The modified lowering operator commutes with the distant braid generators**, that is
`HJO.Sweep.braid_dminus`: for `k ≥ 2`, `1 ≤ i ≤ k-2` and `F ∈ V_k`,
`T_i(d^♭_-F) = d^♭_-(T_iF)`.

This is `HJO.Sweep.dminus_braid` at the indices stated here: writing `k = m + 2`, its
hypothesis `i ≤ m` is `i + 2 ≤ k`. The `1 ≤ i` and `F ∈ V_k` are not read — at the
unread index `0` both operators are the identity, and the two halves of the proof (the substitution
`HJO.Sweep.qshiftNeg_braid` and the extraction `HJO.Sweep.lowerCoeff_braid`) hold on the whole total
space. -/
@[hjo "lem_vmod_dminus_braid_mod"]
theorem braid_dminus (q : L) {k i : ℕ} (hik : i + 2 ≤ k) (F : Total L) :
    braid q i (dminus q k F) = dminus q k (braid q i F) := by
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 2 := ⟨k - 2, by omega⟩
  exact (dminus_braid q (show i ≤ m by omega) F).symm

/-- `HJO.Sweep.braid_dminus` in the endomorphism monoid, `T_id^♭_- = d^♭_-T_i`. -/
theorem braidEnd_mul_dminus (q : L) {k i : ℕ} (hik : i + 2 ≤ k) :
    braidEnd q i * dminus q k = dminus q k * braidEnd q i :=
  LinearMap.ext fun F => braid_dminus q hik F

end Rational

end HJO.Sweep
