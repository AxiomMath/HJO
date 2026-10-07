/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.CarlssonMellit.CornerCalculus
public import HJO.CarlssonMellit.CornerPairs
public import HJO.CarlssonMellit.CornerTransport
public import HJO.Shuffle.DpaIntertwined
public import HJO.Shuffle.DpaRepBuild
public meta import HJO.Attr

/-! # Mellit's replication

`HJO.Sweep.exists_isDpaAction_replication`: from a correctly intertwined pair `(ρ, ρ*)` there is an
action `ρ_1` of `𝔸_q` on `V_*` with `ρ_1(T_i) = T_i`, `ρ_1(d_-) = d_-` and
`ρ_1(d_+) = -(qu)^{-1}z_1d_+`; and `HJO.Sweep.exists_isDpaAction_replication_star`: there is an
action `ρ_2` of `𝔸_{q^{-1}}` on `V_*` with `ρ_2(T_i) = T_i^{-1}`, `ρ_2(d_-) = d_-` and
`ρ_2(d_+) = -y_1d^*_+`.

Both are instances of one construction, `HJO.Sweep.IsReplicationData.exists_isDpaAction`: the two
results are the *same* verification with the roles of the two actions of the pair exchanged, so what
this file supplies is the two sets of six identities the construction reads — once with
`σ = ρ` and the loops taken in `𝔸_{q^{-1}}`, once with `σ = ρ*` and the loops taken in `𝔸_q`.

## Main results

* `HJO.Sweep.IsIntertwinedPair.isReplicationData`,
  `HJO.Sweep.IsIntertwinedPair.isReplicationDataStar` — the two sets of identities.
* `HJO.Sweep.exists_isDpaAction_replication`,
  `HJO.Sweep.exists_isDpaAction_replication_scalar` — `HJO.Sweep.exists_isDpaAction_replication`.
* `HJO.Sweep.exists_isDpaAction_replication_star`.

## Implementation notes

**The hypothesis `ρ(y_1y_2) = ρ(y_2y_1)` on `V_2` is not carried, because it is a theorem.** The
verification uses the commutation of the two loops at the vertex `2`, which might be taken as an
extra assumption on an action. It is not one: `HJO.Dyck.Aq.yElt_comm` commutes `y_i` and `y_j` at
*every* vertex `k ≥ 1` from `HJO.Dyck.Aq` alone, so the hypothesis holds in the algebra and hence
under every algebra homomorphism out of it (`HJO.Sweep.map_yElt_low_comm`). Where the proof needs it
— the first part of the third relation family, at the vertex `k + 2` — what is used is
`HJO.Dyck.Aq.Tg_mul_yElt_pair`, whose own proof is `yElt_comm` plus the cancellation of the two
Hecke corrections. So the hypothesis is discharged and does not appear here.

**`HJO.Dyck.Aq.Tg_mul_yElt_pair_add_commutator`' correction term is not read.** The usual
argument routes the same step through that lemma and then observes that its correction term vanishes
at the vertex in question. `HJO.Dyck.Aq.Tg_mul_yElt_pair_add_commutator` already has the correction
term identically `0`; the correction-free `HJO.Dyck.Aq.Tg_mul_yElt_pair` is what is used here, which
is the same statement with nothing dropped.

**`HJO.Dyck.Aq.yElt_mul_Tg_comm_mellit` is read in its `y_1` form.** It is cited for "`z_1` commutes
with `T_{i+1}`"; `HJO.Dyck.Aq.yElt_one_mul_Tg` is exactly that statement at `i = 1`, in the range
`2 ≤ j ≤ k-1`, and its route covers the whole range needed. The remark in
`HJO.Sweep.isIntertwinedPair_replication_pairs` that `z_1` commutes with `T_1, …, T_{k-1}` is *not*
used and is in fact false at `T_1`: `y_1` and `T_1` do not commute, the recursion
`y_2 = q^{-1}T_1y_1T_1` being the assertion that they do not.

**`T_i` is recovered from `T_i^{-1}` rather than the other way round.** The intertwining condition
gives `ρ*(T_i) = ρ(T̂_i)`, so what commutes with `z_1` is `ρ(T̂_i)`; the loops of `𝔸_q` are then
reached by `HJO.Dyck.Aq.Tg_eq_smul_Tinv_sub`, `T_i = qT̂_i - (q-1)e_k`, together with `z_1`
commuting with the projection. The starred construction runs the same step through
`HJO.Dyck.braidInvGen` in the other direction.

**The scalar of `HJO.Sweep.exists_isDpaAction_replication` is left free, and `u` is not assumed
invertible.** The value `-(qu)^{-1}` is not expressible at the ambient hypotheses, `u` being nowhere
assumed invertible. Every relation the construction checks is homogeneous in the scalar, so
`HJO.Sweep.exists_isDpaAction_replication` is stated for an arbitrary `c` — which needs no
hypothesis on `u` and implies the statement wherever `u` is a unit;
`HJO.Sweep.exists_isDpaAction_replication_scalar` is the literal form, under `[Invertible u]`.
`HJO.Sweep.exists_isDpaAction_replication_star`'s scalar is `-1` and reads no hypothesis at all.

## References

The lemmas `HJO.Sweep.exists_isDpaAction_replication` and
`HJO.Sweep.exists_isDpaAction_replication_star`, on replication and the actions indexed by coprime
pairs, using `HJO.Dyck.Aq`, `HJO.Dyck.Aq.yElt`, `HJO.Sweep.IsDpaAction`, `HJO.Dyck.AqInv`,
`HJO.Sweep.IsIntertwinedPair`, `HJO.Dyck.Aq.yElt_mul_Tg_comm_mellit`, `HJO.Dyck.Aq.yElt_mul_dMinus`,
`HJO.Dyck.Aq.yElt_comm` and `HJO.Dyck.Aq.Tg_mul_yElt_pair_add_commutator`. Consumed by
`HJO.Sweep.isIntertwinedPair_replication_pairs` and `HJO.Sweep.exists_slopeActions`. Transcribing A.
Mellit, *Toric braids and `(m, n)`-parking functions*, §3.2.
-/

@[expose] public section

namespace HJO.Sweep

/-! ### Commuting with a linear combination of two operators -/

section Commute

variable {L : Type*} [CommRing L]

theorem endMul_add (x y z : Module.End L (Vstar L)) : x * (y + z) = x * y + x * z := by
  refine LinearMap.ext fun v => ?_
  simp [Module.End.mul_apply]

theorem endAdd_mul (x y z : Module.End L (Vstar L)) : (y + z) * x = y * x + z * x := by
  refine LinearMap.ext fun v => ?_
  simp [Module.End.mul_apply]

/-- **An operator commuting with `A` and with `B` commutes with `cA - dB`.** This is what carries
the commutation of a loop with `T̂_i` and with the projection over to `T_i = qT̂_i - (q-1)e_k`. -/
theorem endCommute_smul_sub {x A B : Module.End L (Vstar L)} (c d : L)
    (hA : x * A = A * x) (hB : x * B = B * x) :
    x * (c • A - d • B) = (c • A - d • B) * x := by
  rw [endMul_sub, endSub_mul, mul_smul_comm, mul_smul_comm, smul_mul_assoc, smul_mul_assoc, hA, hB]

/-- **An operator commuting with `A` and with `B` commutes with `c(A + dB)`.** This is the same
transfer in the direction `HJO.Dyck.braidInvGen` writes: `T̂_i = q^{-1}(T_i + (q-1)e_k)`. -/
theorem endCommute_smul_add {x A B : Module.End L (Vstar L)} (c d : L)
    (hA : x * A = A * x) (hB : x * B = B * x) :
    x * (c • (A + d • B)) = (c • (A + d • B)) * x := by
  rw [mul_smul_comm, smul_mul_assoc, endMul_add, endAdd_mul, mul_smul_comm, smul_mul_assoc, hA, hB]

end Commute

/-! ### The identities of the unstarred replication -/

section Replication

variable {L : Type*} [CommRing L] {q u : L} [Invertible q] [Invertible (q - 1)]
  {ρ : Dyck.Aq L q →ₐ[L] Module.End L (Vstar L)}
  {ρ' : Dyck.AqInv L q →ₐ[L] Module.End L (Vstar L)}

/-- **The data `HJO.Sweep.exists_isDpaAction_replication` runs the construction on**: the action `ρ`
of `𝔸_q`, with the loops `z_1, z_2` of `𝔸_{q^{-1}}` read through `ρ*`.

The six identities. `d_+z_i = z_{i+1}d_+` and `d_-z_i = z_id_-` are
`HJO.Sweep.IsIntertwinedPair`'s third condition and `HJO.Dyck.Aq.yElt_mul_dMinus` read in
`𝔸_{q^{-1}}`; `z_1` commutes with the loops above the first by `HJO.Dyck.Aq.yElt_one_mul_Tg` there,
and `z_1z_2` with the first by `HJO.Dyck.Aq.Tg_mul_yElt_pair`, whose proof is
`HJO.Dyck.Aq.yElt_comm` — which is why no hypothesis `ρ*(y_1y_2) = ρ*(y_2y_1)` is carried. Each of
the last two is stated about a loop of `𝔸_q`, reached from the corresponding loop of `𝔸_{q^{-1}}` by
`HJO.Sweep.IsIntertwinedPair`'s first condition and `HJO.Dyck.Aq.Tg_eq_smul_Tinv_sub`. -/
theorem IsIntertwinedPair.isReplicationData (h : IsIntertwinedPair q u ρ ρ') :
    IsReplicationData q ρ (fun k => ρ' (Dyck.Aq.yElt L ⅟q k 1))
      (fun k => ρ' (Dyck.Aq.yElt L ⅟q k 2)) where
  map_e := h.isAction.map_e
  proj_mul_loopVar k := by
    rw [← h.isActionStar.map_e, ← map_mul, Dyck.Aq.e_mul_yElt]
  raise_mul_loopVar k hk := h.dPlus_mul_zElt k 1 le_rfl hk
  lower_mul_loopVar m hm := by
    have hy := congrArg ρ' (Dyck.Aq.yElt_mul_dMinus (K := L) (q := ⅟q) (k := m) (i := 1) le_rfl hm)
    simp only [map_mul] at hy
    rw [← h.map_dMinus_star m]
    exact hy.symm
  lower_mul_loopVar' m hm := by
    have hy := congrArg ρ' (Dyck.Aq.yElt_mul_dMinus (K := L) (q := ⅟q) (k := m) (i := 2)
      (by omega) hm)
    simp only [map_mul] at hy
    rw [← h.map_dMinus_star m]
    exact hy.symm
  loopVar_mul_loop k s h1 hs := by
    have hA : ρ' (Dyck.Aq.yElt L ⅟q k 1) * ρ (Dyck.Aq.Tinv L q k s)
        = ρ (Dyck.Aq.Tinv L q k s) * ρ' (Dyck.Aq.yElt L ⅟q k 1) := by
      rw [← h.map_Tg_star k s hs]
      have hy := congrArg ρ' (Dyck.Aq.yElt_one_mul_Tg (K := L) (q := ⅟q) (k := k) (m := s - 1)
        (by omega))
      simp only [map_mul] at hy
      rw [show s - 1 + 1 = s from by omega] at hy
      exact hy
    have hB : ρ' (Dyck.Aq.yElt L ⅟q k 1) * pieceProj L k
        = pieceProj L k * ρ' (Dyck.Aq.yElt L ⅟q k 1) := by
      rw [← h.isActionStar.map_e]
      simp only [← map_mul]
      rw [Dyck.Aq.yElt_mul_e, Dyck.Aq.e_mul_yElt]
    rw [Dyck.Aq.Tg_eq_smul_Tinv_sub, map_sub, map_smul, map_smul, h.isAction.map_e]
    exact endCommute_smul_sub q (q - 1) hA hB
  loopVar_pair_mul_loop k hk := by
    have hA : ρ' (Dyck.Aq.yElt L ⅟q k 1) * ρ' (Dyck.Aq.yElt L ⅟q k 2) * ρ (Dyck.Aq.Tinv L q k 0)
        = ρ (Dyck.Aq.Tinv L q k 0)
            * (ρ' (Dyck.Aq.yElt L ⅟q k 1) * ρ' (Dyck.Aq.yElt L ⅟q k 2)) := by
      rw [← h.map_Tg_star k 0 (by omega)]
      have hp := congrArg ρ' (Dyck.Aq.Tg_mul_yElt_pair (K := L) (q := ⅟q) (k := k) (j := 1)
        le_rfl (by omega))
      simp only [map_mul] at hp
      exact hp.symm
    have hB : ρ' (Dyck.Aq.yElt L ⅟q k 1) * ρ' (Dyck.Aq.yElt L ⅟q k 2) * pieceProj L k
        = pieceProj L k * (ρ' (Dyck.Aq.yElt L ⅟q k 1) * ρ' (Dyck.Aq.yElt L ⅟q k 2)) := by
      rw [← h.isActionStar.map_e]
      simp only [← map_mul]
      rw [mul_assoc, Dyck.Aq.yElt_mul_e, ← mul_assoc, Dyck.Aq.e_mul_yElt]
    rw [Dyck.Aq.Tg_eq_smul_Tinv_sub, map_sub, map_smul, map_smul, h.isAction.map_e]
    exact endCommute_smul_sub q (q - 1) hA hB

/-- **Mellit, replication**, `HJO.Sweep.exists_isDpaAction_replication`: from a correctly
intertwined pair `(ρ, ρ*)` there is an action `ρ_1` of `𝔸_q` on `V_*` with `ρ_1(T_i) = T_i`,
`ρ_1(d_-) = d_-` and `ρ_1(d_+) = c·z_1d_+`.

The scalar is left free. Its intended value `-(qu)^{-1}` is not expressible at the ambient
hypotheses, `u` being nowhere assumed invertible; every relation the construction checks is
homogeneous in the scalar, so the statement holds for every `c` and this is a generalisation of the
intended statement rather than a weakening of it. `HJO.Sweep.exists_isDpaAction_replication_scalar`
is the literal form.

The standing hypothesis `ρ(y_1y_2) = ρ(y_2y_1)`, `ρ*(y_1y_2) = ρ*(y_2y_1)` on `V_2` is
discharged and not carried: see this file's implementation notes. -/
@[hjo "lem_dpa_replication"]
theorem exists_isDpaAction_replication (h : IsIntertwinedPair q u ρ ρ') (c : L) :
    ∃ ρ₁ : Dyck.Aq L q →ₐ[L] Module.End L (Vstar L), IsDpaAction q ρ₁
      ∧ (∀ k i : ℕ, ρ₁ (Dyck.Aq.Tg L q k i) = ρ (Dyck.Aq.Tg L q k i))
      ∧ (∀ k : ℕ, ρ₁ (Dyck.Aq.dMinus L q k) = ρ (Dyck.Aq.dMinus L q k))
      ∧ (∀ k : ℕ, ρ₁ (Dyck.Aq.dPlus L q k)
          = c • (ρ' (Dyck.Aq.yElt L ⅟q (k + 1) 1) * ρ (Dyck.Aq.dPlus L q k))) :=
  h.isReplicationData.exists_isDpaAction c

/-- **Mellit, replication, at the scalar**: `ρ_1(d_+) = -(qu)^{-1}z_1d_+`, which needs `u`
invertible. Every application instantiates at parameters algebraically independent over `ℤ`, where
that is free. -/
@[hjo "lem_dpa_replication"]
theorem exists_isDpaAction_replication_scalar [Invertible u]
    (h : IsIntertwinedPair q u ρ ρ') :
    ∃ ρ₁ : Dyck.Aq L q →ₐ[L] Module.End L (Vstar L), IsDpaAction q ρ₁
      ∧ (∀ k i : ℕ, ρ₁ (Dyck.Aq.Tg L q k i) = ρ (Dyck.Aq.Tg L q k i))
      ∧ (∀ k : ℕ, ρ₁ (Dyck.Aq.dMinus L q k) = ρ (Dyck.Aq.dMinus L q k))
      ∧ (∀ k : ℕ, ρ₁ (Dyck.Aq.dPlus L q k)
          = (-(⅟q * ⅟u)) • (ρ' (Dyck.Aq.yElt L ⅟q (k + 1) 1) * ρ (Dyck.Aq.dPlus L q k))) :=
  h.isReplicationData.exists_isDpaAction _

/-! ### The identities of the conjugate replication -/

/-- **The data `HJO.Sweep.exists_isDpaAction_replication_star` runs the construction on**: the
action `ρ*` of `𝔸_{q^{-1}}`, with the loops `y_1, y_2` of `𝔸_q` read through `ρ`.

This is `HJO.Sweep.IsIntertwinedPair.isReplicationData` with the roles of the two actions exchanged,
and every step is available in the exchanged form: `d^*_+y_i = y_{i+1}d^*_+` is
`HJO.Sweep.IsIntertwinedPair`'s fourth condition, `d_-y_i = y_id_-` is `HJO.Dyck.Aq.yElt_mul_dMinus`
in `𝔸_q`, and the two commutations with the loops of `𝔸_{q^{-1}}` go through `HJO.Dyck.braidInvGen`
in the direction `T̂_i = q^{-1}(T_i + (q-1)e_k)`. -/
theorem IsIntertwinedPair.isReplicationDataStar (h : IsIntertwinedPair q u ρ ρ') :
    IsReplicationData ⅟q ρ' (fun k => ρ (Dyck.Aq.yElt L q k 1))
      (fun k => ρ (Dyck.Aq.yElt L q k 2)) where
  map_e := h.isActionStar.map_e
  proj_mul_loopVar k := by
    rw [← h.isAction.map_e, ← map_mul, Dyck.Aq.e_mul_yElt]
  raise_mul_loopVar k hk := h.dPlusStar_mul_yElt k 1 le_rfl hk
  lower_mul_loopVar m hm := by
    have hy := congrArg ρ (Dyck.Aq.yElt_mul_dMinus (K := L) (q := q) (k := m) (i := 1) le_rfl hm)
    simp only [map_mul] at hy
    rw [h.map_dMinus_star m]
    exact hy.symm
  lower_mul_loopVar' m hm := by
    have hy := congrArg ρ (Dyck.Aq.yElt_mul_dMinus (K := L) (q := q) (k := m) (i := 2)
      (by omega) hm)
    simp only [map_mul] at hy
    rw [h.map_dMinus_star m]
    exact hy.symm
  loopVar_mul_loop k s h1 hs := by
    have hA : ρ (Dyck.Aq.yElt L q k 1) * ρ (Dyck.Aq.Tg L q k s)
        = ρ (Dyck.Aq.Tg L q k s) * ρ (Dyck.Aq.yElt L q k 1) := by
      have hy := congrArg ρ (Dyck.Aq.yElt_one_mul_Tg (K := L) (q := q) (k := k) (m := s - 1)
        (by omega))
      simp only [map_mul] at hy
      rw [show s - 1 + 1 = s from by omega] at hy
      exact hy
    have hB : ρ (Dyck.Aq.yElt L q k 1) * pieceProj L k
        = pieceProj L k * ρ (Dyck.Aq.yElt L q k 1) := by
      rw [← h.isAction.map_e]
      simp only [← map_mul]
      rw [Dyck.Aq.yElt_mul_e, Dyck.Aq.e_mul_yElt]
    rw [h.map_Tg_star k s hs, Dyck.Aq.Tinv_eq, map_smul, map_add, map_smul, h.isAction.map_e]
    exact endCommute_smul_add ⅟q (q - 1) hA hB
  loopVar_pair_mul_loop k hk := by
    have hA : ρ (Dyck.Aq.yElt L q k 1) * ρ (Dyck.Aq.yElt L q k 2) * ρ (Dyck.Aq.Tg L q k 0)
        = ρ (Dyck.Aq.Tg L q k 0) * (ρ (Dyck.Aq.yElt L q k 1) * ρ (Dyck.Aq.yElt L q k 2)) := by
      have hp := congrArg ρ (Dyck.Aq.Tg_mul_yElt_pair (K := L) (q := q) (k := k) (j := 1)
        le_rfl (by omega))
      simp only [map_mul] at hp
      exact hp.symm
    have hB : ρ (Dyck.Aq.yElt L q k 1) * ρ (Dyck.Aq.yElt L q k 2) * pieceProj L k
        = pieceProj L k * (ρ (Dyck.Aq.yElt L q k 1) * ρ (Dyck.Aq.yElt L q k 2)) := by
      rw [← h.isAction.map_e]
      simp only [← map_mul]
      rw [mul_assoc, Dyck.Aq.yElt_mul_e, ← mul_assoc, Dyck.Aq.e_mul_yElt]
    rw [h.map_Tg_star k 0 (by omega), Dyck.Aq.Tinv_eq, map_smul, map_add, map_smul,
      h.isAction.map_e]
    exact endCommute_smul_add ⅟q (q - 1) hA hB

/-- **Mellit, conjugate replication**, `HJO.Sweep.exists_isDpaAction_replication_star`: from a
correctly intertwined pair `(ρ, ρ*)` there is an action `ρ_2` of `𝔸_{q^{-1}}` on `V_*` with
`ρ_2(T_i) = T_i^{-1}`, `ρ_2(d_-) = d_-` and `ρ_2(d_+) = -y_1d^*_+`.

`T_i^{-1}` is `HJO.Dyck.braidInvGen`'s `T̂_i` read through `ρ`, which by
`HJO.Sweep.IsIntertwinedPair`'s first condition is `ρ*(T_i)`; both readings are recorded. The scalar
`-1` reads no hypothesis, and as in `HJO.Sweep.exists_isDpaAction_replication` the standing
hypothesis on the loops at the vertex `2` is discharged and not carried. -/
@[hjo "lem_dpa_replication_star"]
theorem exists_isDpaAction_replication_star (h : IsIntertwinedPair q u ρ ρ') :
    ∃ ρ₂ : Dyck.AqInv L q →ₐ[L] Module.End L (Vstar L), IsDpaAction ⅟q ρ₂
      ∧ (∀ k i : ℕ, ρ₂ (Dyck.Aq.Tg L ⅟q k i) = ρ' (Dyck.Aq.Tg L ⅟q k i))
      ∧ (∀ k s : ℕ, s + 2 ≤ k → ρ₂ (Dyck.Aq.Tg L ⅟q k s) = ρ (Dyck.Aq.Tinv L q k s))
      ∧ (∀ k : ℕ, ρ₂ (Dyck.Aq.dMinus L ⅟q k) = ρ (Dyck.Aq.dMinus L q k))
      ∧ (∀ k : ℕ, ρ₂ (Dyck.Aq.dPlus L ⅟q k)
          = (-1 : L) • (ρ (Dyck.Aq.yElt L q (k + 1) 1) * ρ' (Dyck.Aq.dPlus L ⅟q k))) := by
  obtain ⟨ρ₂, hact, hT, hD, hU⟩ :=
    h.isReplicationDataStar.exists_isDpaAction (-1 : L)
  refine ⟨ρ₂, hact, hT, fun k s hs => ?_, fun k => ?_, hU⟩
  · rw [hT k s, h.map_Tg_star k s hs]
  · rw [hD k, h.map_dMinus_star k]

end Replication

end HJO.Sweep

end
