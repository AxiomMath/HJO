/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.CarlssonMellit.CornerPowers
public import HJO.CarlssonMellit.CornerRaising
public import HJO.Shuffle.DpaReplication
public meta import HJO.Attr

/-! # The replicated pairs are correctly intertwined

`HJO.Sweep.isIntertwinedPair_replication_pairs`: the two pairs `(ρ, ρ_2)` and `(ρ_1, ρ^*)` built by
`HJO.Sweep.exists_isDpaAction_replication` and `HJO.Sweep.exists_isDpaAction_replication_star` are
again correctly intertwined, and with the same `u`.

## Main results

* `HJO.Sweep.isIntertwinedPair_replication_pairs`.
* `HJO.Sweep.IsReplicationData.map_yElt_one` — the lowest loop of a replicated action:
  `ρ_1(y_1) = c·Ξ_1y_1`, with `Ξ_1` the lowest loop of the other action of the pair.
* `HJO.Sweep.IsReplicationData.map_Tinv`, `HJO.Sweep.IsReplicationData.map_yElt_succ` — the
  replicated action agrees with the old one on the polynomial inverses, and its loops obey
  `HJO.Dyck.Aq.yElt_succ_eq_units` with the *old* inverses.
* `HJO.Sweep.isIntertwinedPair_replication`, `HJO.Sweep.isIntertwinedPair_replicationStar` — the
  two halves, each assembled from the five conditions of `HJO.Sweep.IsIntertwinedPair`.

## Implementation notes

**The usual computation of the loops of `ρ_1` is wrong, and is not followed.** It computes them
from `T_{1↑k}ρ_1(y_k) = (q-1)^{-1}Π` and then uses "`z_1` commutes with `T_1, …, T_{k-1}`". It does
not: `HJO.Dyck.Aq.yElt_one_mul_Tg` gives `y_1T_j = T_jy_1` only for `2 ≤ j ≤ k-1`, and the missing
case is *false*: the recursion `y_2 = q^{-1}T_1y_1T_1` of `HJO.Dyck.Aq.yElt` is exactly the
statement that `y_1` and `T_1` do not commute. The word `T_{1↑k}` ends in `T_1`, so the conjugation
cannot be cancelled and that computation's conclusion `ρ_1(y_i) = -(qu)^{-1}z_1y_i` is unavailable
for `i ≥ 2`. It is in fact false there: were it true, `HJO.Sweep.IsIntertwinedPair`'s fourth
condition for `(ρ_1, ρ^*)` would force `T̂_1z_1T_1 = z_1`, which is the commutation just denied. The
*conclusion* of `HJO.Sweep.isIntertwinedPair_replication_pairs` is true; only that step of the usual
proof is not.

**What replaces it.** The *lowest* loop does obey the formula, for a reason the usual
proof does not use: `HJO.Dyck.Aq.yElt_one_eq_Delta` puts the commutator on the **left** of `y_1`
(`y_1 = q^{1-k}(q-1)^{-1}D_kT_{k↓1}`), and `HJO.Sweep.IsReplicationData.deltaRep_eq` puts `Ξ_1` on
the left of `ρ_1(D_k)`, so the two line up with no commutation at all. That is
`HJO.Sweep.IsReplicationData.map_yElt_one`. The higher loops are then *not* `c·Ξ_1y_i`; they are the
iterated conjugates `ρ_1(y_{i+1}) = qT̂_iρ_1(y_i)T̂_i` of
`HJO.Sweep.IsReplicationData.map_yElt_succ`, and the fourth condition is proved from that recursion
by induction on `i` rather than from a closed form. The base case is
`d^*_+z_1 = T̂_1z_1T_1d^*_+` (`HJO.Dyck.Aq.dPlus_mul_yElt_one` read in `𝔸_{q^{-1}}`) together with
`T_1y_2 = qy_1T̂_1` (`HJO.Dyck.Aq.Tg_mul_yElt_succ_eq`), after which both sides are
`T̂_1z_1y_1T̂_1d^*_+`; the step moves `d^*_+` past `T̂_i` by `HJO.Dyck.Aq`'s `d_+T_i = T_{i+1}d_+`
read in `𝔸_{q^{-1}}`, which raises the index by exactly the one the recursion at the vertex `k+1`
needs.

**Three of the five conditions need no loop of the replicated action at all.** The first two are
immediate, `ρ_1` sharing its braid and lowering parts with `ρ`. The third needs only that two loops
of `𝔸_{q^{-1}}` commute, by `HJO.Dyck.Aq.yElt_comm`, and not what they are. The fifth needs the
lowest loop only.

**`u` is unchanged, and the scalar of `ρ_1` stays free.** The fifth condition's `-uq^{k+1}` survives
the substitution because both of its sides acquire the same factor — `c·z_1` on the left and `c`
inside `ρ_1(y_1) = c·z_1y_1` on the right — so no invertibility of `c`, and in particular none of
`u`, is read. `HJO.Sweep.exists_isDpaAction_replication`'s own note on `-(qu)^{-1}` therefore costs
nothing here.

**`T_i` and `T̂^*_i` are each recovered from the other.** `HJO.Sweep.IsIntertwinedPair`'s first
condition is `ρ^*(T_i) = ρ(T̂_i)`; `HJO.Sweep.IsIntertwinedPair.map_Tinv_star` is the inverted form
`ρ^*(T̂_i) = ρ(T_i)`, obtained by substituting one `HJO.Dyck.braidInvGen` formula into the other and
cancelling `q⅟q = 1`. Both are needed, the induction moving `d^*_+` past inverses on one side and
loops on the other.

## References

Transcribing A. Mellit, *Toric braids
and `(m, n)`-parking functions*, §3.2.
-/

@[expose] public section

/-! ### Two identities of the Dyck path algebra the induction reads -/

namespace HJO.Dyck.Aq

variable {K : Type*} [CommRing K] {q : K} [Invertible q] [Invertible (q - 1)]

/-- **A loop against the corner element one step above it**: `T_iy_{i+1} = qy_iT̂_i`. The upward
recursion `y_{i+1} = qT̂_iy_iT̂_i` of `HJO.Dyck.Aq.yElt_succ_eq_units` with one `T̂_i` cancelled
against the `T_i` in front. -/
theorem Tg_mul_yElt_succ_eq {k i : ℕ} (h1 : 1 ≤ i) (hik : i < k) :
    Tg K q k (i - 1) * yElt K q k (i + 1)
      = q • (yElt K q k i * Tinv K q k (i - 1)) := by
  rw [yElt_succ_eq h1 hik, mul_smul_comm, ← mul_assoc, ← mul_assoc,
    Tg_mul_Tinv (show i - 1 + 2 ≤ k from by omega), e_mul_yElt]

end HJO.Dyck.Aq

namespace HJO.Sweep

/-! ### The loops of a replicated action -/

namespace IsReplicationData

section Loops

variable {L : Type*} [CommRing L] {a : L} [Invertible a] [Invertible (a - 1)]
  {σ : Dyck.Aq L a →ₐ[L] Module.End L (Vstar L)} {Ξ Ξ' : ℕ → Module.End L (Vstar L)}
  {ρ₁ : Dyck.Aq L a →ₐ[L] Module.End L (Vstar L)}

variable (h : IsReplicationData a σ Ξ Ξ') (c : L)
  (h1act : IsDpaAction a ρ₁)
  (h1T : ∀ k i : ℕ, ρ₁ (Dyck.Aq.Tg L a k i) = σ (Dyck.Aq.Tg L a k i))
  (h1D : ∀ k : ℕ, ρ₁ (Dyck.Aq.dMinus L a k) = σ (Dyck.Aq.dMinus L a k))
  (h1U : ∀ k : ℕ, ρ₁ (Dyck.Aq.dPlus L a k) = c • (Ξ (k + 1) * σ (Dyck.Aq.dPlus L a k)))

omit [Invertible a] [Invertible (a - 1)] in
include h h1act in
/-- **A replicated action agrees with the old one on the idempotents**, both sending `𝟏_k` to the
projection onto `V_k` by `HJO.Sweep.IsDpaAction`. -/
theorem map_e_eq (k : ℕ) : ρ₁ (Dyck.Aq.e L a k) = σ (Dyck.Aq.e L a k) := by
  rw [h1act.map_e, h.map_e]

omit [Invertible (a - 1)] in
include h h1act h1T in
/-- **A replicated action agrees with the old one on the polynomial inverses** of
`HJO.Dyck.braidInvGen`, sharing its loops and its idempotents. -/
theorem map_Tinv (k i : ℕ) : ρ₁ (Dyck.Aq.Tinv L a k i) = σ (Dyck.Aq.Tinv L a k i) := by
  simp only [Dyck.Aq.Tinv_eq, map_smul, map_add, h1T, h.map_e_eq h1act]

omit [Invertible a] [Invertible (a - 1)] in
include h h1act h1T in
/-- **A replicated action agrees with the old one on the descending words of loops** of
`HJO.Dyck.Aq.yElt`'s formula, those being words in the loops and the idempotent. -/
theorem map_tSeg (k b : ℕ) : ∀ n : ℕ,
    ρ₁ (Dyck.Aq.tSeg L a k b n) = σ (Dyck.Aq.tSeg L a k b n) := by
  intro n
  induction n with
  | zero =>
    simp only [Dyck.Aq.tSeg_zero]
    exact h.map_e_eq h1act k
  | succ n ih =>
    simp only [Dyck.Aq.tSeg_succ, map_mul]
    rw [h1T, ih]

omit [Invertible a] [Invertible (a - 1)] in
include h h1D h1U in
/-- **The commutator of a replicated action is `c·Ξ_1` times the old one.** This is
`HJO.Sweep.IsReplicationData.deltaRep_eq` read through the action rather than on the operators. -/
theorem map_Delta (m : ℕ) :
    ρ₁ (Dyck.Aq.Delta L a m) = c • (Ξ (m + 1) * σ (Dyck.Aq.Delta L a m)) := by
  rw [Dyck.Aq.Delta_eq_sub, map_sub, map_mul, map_mul, h1U, h1D, h1D, h1U]
  exact h.deltaRep_eq c m

include h h1act h1T h1D h1U in
/-- **The lowest loop of a replicated action**: `ρ_1(y_1) = c·Ξ_1y_1` on `V_k` for every `k ≥ 1`.

This is the one member of the family for which the formula holds, and the reason is that
`HJO.Dyck.Aq.yElt_one_eq_Delta` writes `y_1` with the commutator on the *left*:
`y_1 = q^{1-k}(q-1)^{-1}D_kT_{k↓1}`, while `HJO.Sweep.IsReplicationData.map_Delta` puts `Ξ_1` on the
left of `ρ_1(D_k)`. The two line up and no commutation of `Ξ_1` past a loop is needed — which is
what fails for the higher members; see this file's implementation notes. -/
theorem map_yElt_one (k : ℕ) (hk : 1 ≤ k) :
    ρ₁ (Dyck.Aq.yElt L a k 1) = c • (Ξ k * σ (Dyck.Aq.yElt L a k 1)) := by
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
  have hy := Dyck.Aq.yElt_one_eq_Delta (K := L) (q := a) (k := m + 1) (by omega)
  rw [Nat.add_sub_cancel] at hy
  rw [hy, map_smul ρ₁, map_smul σ, map_mul ρ₁, map_mul σ, h.map_Delta c h1D h1U m,
    h.map_tSeg h1act h1T (m + 1) 0 m, smul_mul_assoc, smul_smul, mul_smul_comm, smul_smul]
  congr 1
  ring

include h h1act h1T in
/-- **The loops of a replicated action obey `HJO.Dyck.Aq.yElt_succ_eq_units` with the old
inverses**: `ρ_1(y_{i+1}) = qT̂_iρ_1(y_i)T̂_i`, the conjugating inverses being `σ`'s because `ρ_1`
shares its loops and idempotents with `σ`. This recursion, not a closed form, is what carries the
lowest loop up. -/
theorem map_yElt_succ {k i : ℕ} (h1 : 1 ≤ i) (hik : i < k) :
    ρ₁ (Dyck.Aq.yElt L a k (i + 1))
      = a • (σ (Dyck.Aq.Tinv L a k (i - 1)) * ρ₁ (Dyck.Aq.yElt L a k i)
          * σ (Dyck.Aq.Tinv L a k (i - 1))) := by
  rw [Dyck.Aq.yElt_succ_eq h1 hik, map_smul ρ₁, map_mul ρ₁, map_mul ρ₁,
    h.map_Tinv h1act h1T]

end Loops

end IsReplicationData

/-! ### Four of the five conditions for the pair `(ρ_1, ρ*)` -/

section Pairs

variable {L : Type*} [CommRing L] {q u : L} [Invertible q] [Invertible (q - 1)]
  {ρ : Dyck.Aq L q →ₐ[L] Module.End L (Vstar L)}
  {ρ' : Dyck.AqInv L q →ₐ[L] Module.End L (Vstar L)}
  {ρ₁ : Dyck.Aq L q →ₐ[L] Module.End L (Vstar L)}

variable (h : IsIntertwinedPair q u ρ ρ') (c : L)
  (h1act : IsDpaAction q ρ₁)
  (h1T : ∀ k i : ℕ, ρ₁ (Dyck.Aq.Tg L q k i) = ρ (Dyck.Aq.Tg L q k i))
  (h1D : ∀ k : ℕ, ρ₁ (Dyck.Aq.dMinus L q k) = ρ (Dyck.Aq.dMinus L q k))
  (h1U : ∀ k : ℕ, ρ₁ (Dyck.Aq.dPlus L q k)
    = c • (ρ' (Dyck.Aq.yElt L ⅟q (k + 1) 1) * ρ (Dyck.Aq.dPlus L q k)))

include h h1act h1T in
/-- `HJO.Sweep.IsIntertwinedPair`'s first condition for `(ρ_1, ρ^*)`: `ρ^*(T_i) = ρ_1(T̂_i)`. The
replicated action shares its braid part and its idempotents with `ρ`, so it shares its polynomial
inverses. -/
theorem replication_map_Tg_star (k s : ℕ) (hs : s + 2 ≤ k) :
    ρ' (Dyck.Aq.Tg L ⅟q k s) = ρ₁ (Dyck.Aq.Tinv L q k s) := by
  rw [h.map_Tg_star k s hs, (h.isReplicationData).map_Tinv h1act h1T k s]

include h h1D in
/-- `HJO.Sweep.IsIntertwinedPair`'s second condition for `(ρ_1, ρ^*)`: `ρ^*(d_-) = ρ_1(d_-)`. -/
theorem replication_map_dMinus_star (k : ℕ) :
    ρ' (Dyck.Aq.dMinus L ⅟q k) = ρ₁ (Dyck.Aq.dMinus L q k) := by
  rw [h.map_dMinus_star k, h1D k]

include h h1U in
/-- `HJO.Sweep.IsIntertwinedPair`'s third condition for `(ρ_1, ρ^*)`:
`ρ_1(d_+)z_i = z_{i+1}ρ_1(d_+)`.

Only the *commutation* of two loops of `𝔸_{q^{-1}}` is used, by `HJO.Dyck.Aq.yElt_comm`, and not
what either of them is: the raising operator of `ρ_1` is `c·z_1d_+`, the `d_+` moves `z_i` up to
`z_{i+1}` by the condition for `(ρ, ρ^*)`, and the resulting `z_1z_{i+1}` is `z_{i+1}z_1`. -/
theorem replication_dPlus_mul_zElt (k i : ℕ) (h1 : 1 ≤ i) (hik : i ≤ k) :
    ρ₁ (Dyck.Aq.dPlus L q k) * ρ' (Dyck.Aq.yElt L ⅟q k i)
      = ρ' (Dyck.Aq.yElt L ⅟q (k + 1) (i + 1)) * ρ₁ (Dyck.Aq.dPlus L q k) := by
  have hcomm : ρ' (Dyck.Aq.yElt L ⅟q (k + 1) 1) * ρ' (Dyck.Aq.yElt L ⅟q (k + 1) (i + 1))
      = ρ' (Dyck.Aq.yElt L ⅟q (k + 1) (i + 1)) * ρ' (Dyck.Aq.yElt L ⅟q (k + 1) 1) := by
    rw [← map_mul, ← map_mul, Dyck.Aq.yElt_comm (by omega) (by omega) (by omega) (by omega)]
  rw [h1U, smul_mul_assoc, mul_smul_comm]
  congr 1
  rw [mul_assoc, h.dPlus_mul_zElt k i h1 hik, ← mul_assoc, hcomm, mul_assoc]

include h h1act h1T h1D h1U in
/-- `HJO.Sweep.IsIntertwinedPair`'s fifth condition for `(ρ_1, ρ^*)`:
`z_1ρ_1(d_+) = -uq^{k+1}ρ_1(y_1)d^*_+`, with the *same* `u` as for `(ρ, ρ^*)`.

This is the one condition that reads a loop of `ρ_1`, and it reads only the lowest one, which
`HJO.Sweep.IsReplicationData.map_yElt_one` supplies. -/
theorem replication_zElt_one_mul_dPlus (k : ℕ) :
    ρ' (Dyck.Aq.yElt L ⅟q (k + 1) 1) * ρ₁ (Dyck.Aq.dPlus L q k)
      = (-(u * q ^ (k + 1))) • (ρ₁ (Dyck.Aq.yElt L q (k + 1) 1) * ρ' (Dyck.Aq.dPlus L ⅟q k)) := by
  rw [h1U, mul_smul_comm, h.zElt_one_mul_dPlus k, mul_smul_comm, smul_smul,
    (h.isReplicationData).map_yElt_one c h1act h1T h1D h1U (k + 1) (by omega), smul_mul_assoc,
    smul_smul]
  congr 1
  ring

include h in
/-- **The starred action's polynomial inverses are the unstarred action's loops**:
`ρ^*(T̂_i) = T_i`. `HJO.Sweep.IsIntertwinedPair`'s first condition says `ρ^*(T_i) = ρ(T̂_i)`;
inverting both sides inside the corner, which is what `HJO.Dyck.braidInvGen` does polynomially,
gives this. -/
theorem IsIntertwinedPair.map_Tinv_star (k s : ℕ) (hs : s + 2 ≤ k) :
    ρ' (Dyck.Aq.Tinv L ⅟q k s) = ρ (Dyck.Aq.Tg L q k s) := by
  have key : ∀ T P : Module.End L (Vstar L),
      q • (⅟q • (T + (q - 1) • P) + (⅟q - 1) • P) = T := by
    intro T P
    have hz : (q - 1) + q * (⅟q - 1) = 0 := by
      rw [mul_sub, mul_invOf_self, mul_one]; ring
    rw [smul_add, smul_smul, smul_smul, mul_invOf_self, one_smul, add_assoc, ← add_smul, hz,
      zero_smul, add_zero]
  rw [Dyck.Aq.Tinv_eq, map_smul ρ', map_add ρ', map_smul ρ', h.map_Tg_star k s hs,
    h.isActionStar.map_e, Dyck.Aq.Tinv_eq, map_smul ρ, map_add ρ, map_smul ρ, h.isAction.map_e,
    invOf_invOf]
  exact key _ _

include h in
/-- **`d^*_+` moves the unstarred polynomial inverses up by one index**:
`d^*_+T̂_i = T̂_{i+1}d^*_+`. Those inverses are `ρ^*`'s own loops by `HJO.Sweep.IsIntertwinedPair`,
and `ρ^*` is an action, so this is `HJO.Dyck.Aq`'s `d_+T_i = T_{i+1}d_+` read in `𝔸_{q^{-1}}`. -/
theorem IsIntertwinedPair.dPlusStar_mul_Tinv {k i : ℕ} (h1 : 1 ≤ i) (hik : i + 1 ≤ k) :
    ρ' (Dyck.Aq.dPlus L ⅟q k) * ρ (Dyck.Aq.Tinv L q k (i - 1))
      = ρ (Dyck.Aq.Tinv L q (k + 1) i) * ρ' (Dyck.Aq.dPlus L ⅟q k) := by
  rw [← h.map_Tg_star k (i - 1) (by omega), ← h.map_Tg_star (k + 1) i (by omega), ← map_mul,
    ← map_mul, Dyck.Aq.dPlus_mul_Tg (show i - 1 + 2 ≤ k from by omega),
    show i - 1 + 1 = i from by omega]

include h h1act h1T h1D h1U in
/-- **The base case of `HJO.Sweep.IsIntertwinedPair`'s fourth condition for `(ρ_1, ρ^*)`**:
`d^*_+ρ_1(y_1) = ρ_1(y_2)d^*_+`.

The closed form for the loops of `ρ_1` is unavailable (see this file's implementation
notes), so the condition is carried by the recursion instead, and this is where it starts.
`HJO.Dyck.Aq.dPlus_mul_yElt_one` read in `𝔸_{q^{-1}}` conjugates `z_1` across `d^*_+`, the surviving
`T_1` is absorbed by `HJO.Dyck.Aq.Tg_mul_yElt_succ_eq`, and what is left on both sides is
`T̂_1z_1y_1T̂_1d^*_+`. -/
theorem replication_dPlusStar_mul_yElt_one (k : ℕ) (hk : 1 ≤ k) :
    ρ' (Dyck.Aq.dPlus L ⅟q k) * ρ₁ (Dyck.Aq.yElt L q k 1)
      = ρ₁ (Dyck.Aq.yElt L q (k + 1) 2) * ρ' (Dyck.Aq.dPlus L ⅟q k) := by
  have hDZ : ρ' (Dyck.Aq.dPlus L ⅟q k) * ρ' (Dyck.Aq.yElt L ⅟q k 1)
      = ρ (Dyck.Aq.Tinv L q (k + 1) 0) * ρ' (Dyck.Aq.yElt L ⅟q (k + 1) 1)
          * ρ (Dyck.Aq.Tg L q (k + 1) 0) * ρ' (Dyck.Aq.dPlus L ⅟q k) := by
    have hx := congrArg ρ' (Dyck.Aq.dPlus_mul_yElt_one (K := L) (q := ⅟q) (k := k) hk)
    simp only [map_mul] at hx
    rw [hx, h.map_Tg_star (k + 1) 0 (by omega), h.map_Tinv_star (k + 1) 0 (by omega)]
  have hDY : ρ' (Dyck.Aq.dPlus L ⅟q k) * ρ (Dyck.Aq.yElt L q k 1)
      = ρ (Dyck.Aq.yElt L q (k + 1) 2) * ρ' (Dyck.Aq.dPlus L ⅟q k) :=
    h.dPlusStar_mul_yElt k 1 le_rfl hk
  have hTY2 : ρ (Dyck.Aq.Tg L q (k + 1) 0) * ρ (Dyck.Aq.yElt L q (k + 1) 2)
      = q • (ρ (Dyck.Aq.yElt L q (k + 1) 1) * ρ (Dyck.Aq.Tinv L q (k + 1) 0)) := by
    have hx := congrArg ρ (Dyck.Aq.Tg_mul_yElt_succ_eq (K := L) (q := q) (k := k + 1) (i := 1)
      le_rfl (by omega))
    rw [map_mul, map_smul, map_mul] at hx
    exact hx
  have h1y : ρ₁ (Dyck.Aq.yElt L q k 1)
      = c • (ρ' (Dyck.Aq.yElt L ⅟q k 1) * ρ (Dyck.Aq.yElt L q k 1)) :=
    (h.isReplicationData).map_yElt_one c h1act h1T h1D h1U k hk
  have h1y' : ρ₁ (Dyck.Aq.yElt L q (k + 1) 1)
      = c • (ρ' (Dyck.Aq.yElt L ⅟q (k + 1) 1) * ρ (Dyck.Aq.yElt L q (k + 1) 1)) :=
    (h.isReplicationData).map_yElt_one c h1act h1T h1D h1U (k + 1) (by omega)
  have h1y2 : ρ₁ (Dyck.Aq.yElt L q (k + 1) 2)
      = (q * c) • (ρ (Dyck.Aq.Tinv L q (k + 1) 0)
          * (ρ' (Dyck.Aq.yElt L ⅟q (k + 1) 1) * ρ (Dyck.Aq.yElt L q (k + 1) 1))
          * ρ (Dyck.Aq.Tinv L q (k + 1) 0)) := by
    have hx := (h.isReplicationData).map_yElt_succ h1act h1T (k := k + 1) (i := 1) le_rfl
      (by omega)
    rw [hx, h1y', mul_smul_comm, smul_mul_assoc, smul_smul]
  -- the left-hand side
  have hL : ρ' (Dyck.Aq.dPlus L ⅟q k) * ρ₁ (Dyck.Aq.yElt L q k 1)
      = (c * q) • (ρ (Dyck.Aq.Tinv L q (k + 1) 0) * ρ' (Dyck.Aq.yElt L ⅟q (k + 1) 1)
          * (ρ (Dyck.Aq.yElt L q (k + 1) 1) * ρ (Dyck.Aq.Tinv L q (k + 1) 0))
          * ρ' (Dyck.Aq.dPlus L ⅟q k)) := by
    rw [h1y, mul_smul_comm, ← mul_assoc, hDZ,
      mul_assoc (ρ (Dyck.Aq.Tinv L q (k + 1) 0) * ρ' (Dyck.Aq.yElt L ⅟q (k + 1) 1)
        * ρ (Dyck.Aq.Tg L q (k + 1) 0)) (ρ' (Dyck.Aq.dPlus L ⅟q k))
        (ρ (Dyck.Aq.yElt L q k 1)), hDY, ← mul_assoc,
      mul_assoc (ρ (Dyck.Aq.Tinv L q (k + 1) 0) * ρ' (Dyck.Aq.yElt L ⅟q (k + 1) 1))
        (ρ (Dyck.Aq.Tg L q (k + 1) 0)) (ρ (Dyck.Aq.yElt L q (k + 1) 2)), hTY2, mul_smul_comm,
      smul_mul_assoc, smul_smul]
  rw [hL, h1y2, smul_mul_assoc]
  congr 1
  ring

include h h1act h1T h1D h1U in
/-- **`HJO.Sweep.IsIntertwinedPair`'s fourth condition for `(ρ_1, ρ^*)`**:
`d^*_+ρ_1(y_i) = ρ_1(y_{i+1})d^*_+` for `1 ≤ i ≤ k`.

Carried by `HJO.Dyck.Aq.yElt_succ_eq_units` rather than by a closed form for the loops of `ρ_1`: the
base case is `HJO.Sweep.replication_dPlusStar_mul_yElt_one`, and each step moves `d^*_+` past the
conjugating inverse `T̂_i` by `HJO.Sweep.IsIntertwinedPair.dPlusStar_mul_Tinv`, which raises its
index by exactly the one the recursion at the vertex `k+1` needs. -/
theorem replication_dPlusStar_mul_yElt :
    ∀ i : ℕ, 1 ≤ i → ∀ k : ℕ, i ≤ k →
      ρ' (Dyck.Aq.dPlus L ⅟q k) * ρ₁ (Dyck.Aq.yElt L q k i)
        = ρ₁ (Dyck.Aq.yElt L q (k + 1) (i + 1)) * ρ' (Dyck.Aq.dPlus L ⅟q k) := by
  intro i h1
  induction i, h1 using Nat.le_induction with
  | base =>
    intro k hk
    exact replication_dPlusStar_mul_yElt_one h c h1act h1T h1D h1U k hk
  | succ i hi ih =>
    intro k hik
    have hrec : ρ₁ (Dyck.Aq.yElt L q k (i + 1))
        = q • (ρ (Dyck.Aq.Tinv L q k (i - 1)) * ρ₁ (Dyck.Aq.yElt L q k i)
            * ρ (Dyck.Aq.Tinv L q k (i - 1))) :=
      (h.isReplicationData).map_yElt_succ h1act h1T (k := k) (i := i) hi (by omega)
    have hrec' : ρ₁ (Dyck.Aq.yElt L q (k + 1) (i + 1 + 1))
        = q • (ρ (Dyck.Aq.Tinv L q (k + 1) i) * ρ₁ (Dyck.Aq.yElt L q (k + 1) (i + 1))
            * ρ (Dyck.Aq.Tinv L q (k + 1) i)) :=
      (h.isReplicationData).map_yElt_succ h1act h1T (k := k + 1) (i := i + 1) (by omega)
        (by omega)
    have hcross := h.dPlusStar_mul_Tinv (k := k) (i := i) hi (by omega)
    rw [hrec, mul_smul_comm, ← mul_assoc, ← mul_assoc, hcross,
      mul_assoc (ρ (Dyck.Aq.Tinv L q (k + 1) i)) (ρ' (Dyck.Aq.dPlus L ⅟q k))
        (ρ₁ (Dyck.Aq.yElt L q k i)),
      ih k (by omega), ← mul_assoc,
      mul_assoc (ρ (Dyck.Aq.Tinv L q (k + 1) i) * ρ₁ (Dyck.Aq.yElt L q (k + 1) (i + 1)))
        (ρ' (Dyck.Aq.dPlus L ⅟q k)) (ρ (Dyck.Aq.Tinv L q k (i - 1))),
      hcross, hrec', smul_mul_assoc, ← mul_assoc]

include h h1act h1T h1D h1U in
/-- **The replicated pair `(ρ_1, ρ^*)` is correctly intertwined**, the first half of
`HJO.Sweep.isIntertwinedPair_replication_pairs`, and with the *same* `u`: the fifth condition's
scalar survives the substitution because both sides acquire the same factor. -/
theorem isIntertwinedPair_replication : IsIntertwinedPair q u ρ₁ ρ' where
  isAction := h1act
  isActionStar := h.isActionStar
  map_Tg_star k s hs := replication_map_Tg_star h h1act h1T k s hs
  map_dMinus_star k := replication_map_dMinus_star h h1D k
  dPlus_mul_zElt k i hi hik := replication_dPlus_mul_zElt h c h1U k i hi hik
  dPlusStar_mul_yElt k i hi hik :=
    replication_dPlusStar_mul_yElt h c h1act h1T h1D h1U i hi k hik
  zElt_one_mul_dPlus k := replication_zElt_one_mul_dPlus h c h1act h1T h1D h1U k

end Pairs

/-! ### Four of the five conditions for the pair `(ρ, ρ_2)` -/

section PairsStar

variable {L : Type*} [CommRing L] {q u : L} [Invertible q] [Invertible (q - 1)]
  {ρ : Dyck.Aq L q →ₐ[L] Module.End L (Vstar L)}
  {ρ' : Dyck.AqInv L q →ₐ[L] Module.End L (Vstar L)}
  {ρ₂ : Dyck.AqInv L q →ₐ[L] Module.End L (Vstar L)}

variable (h : IsIntertwinedPair q u ρ ρ')
  (h2act : IsDpaAction ⅟q ρ₂)
  (h2T : ∀ k i : ℕ, ρ₂ (Dyck.Aq.Tg L ⅟q k i) = ρ' (Dyck.Aq.Tg L ⅟q k i))
  (h2D : ∀ k : ℕ, ρ₂ (Dyck.Aq.dMinus L ⅟q k) = ρ' (Dyck.Aq.dMinus L ⅟q k))
  (h2U : ∀ k : ℕ, ρ₂ (Dyck.Aq.dPlus L ⅟q k)
    = (-1 : L) • (ρ (Dyck.Aq.yElt L q (k + 1) 1) * ρ' (Dyck.Aq.dPlus L ⅟q k)))

include h h2T in
/-- `HJO.Sweep.IsIntertwinedPair`'s first condition for `(ρ, ρ_2)`: `ρ_2(T_i) = ρ(T̂_i)`. -/
theorem replicationStar_map_Tg_star (k s : ℕ) (hs : s + 2 ≤ k) :
    ρ₂ (Dyck.Aq.Tg L ⅟q k s) = ρ (Dyck.Aq.Tinv L q k s) := by
  rw [h2T k s, h.map_Tg_star k s hs]

include h h2D in
/-- `HJO.Sweep.IsIntertwinedPair`'s second condition for `(ρ, ρ_2)`: `ρ_2(d_-) = ρ(d_-)`. -/
theorem replicationStar_map_dMinus_star (k : ℕ) :
    ρ₂ (Dyck.Aq.dMinus L ⅟q k) = ρ (Dyck.Aq.dMinus L q k) := by
  rw [h2D k, h.map_dMinus_star k]

include h h2U in
/-- `HJO.Sweep.IsIntertwinedPair`'s fourth condition for `(ρ, ρ_2)`:
`ρ_2(d_+)y_i = y_{i+1}ρ_2(d_+)`.

As for the mirror condition of the other pair, only the commutation of two loops is used — here of
`𝔸_q`, by `HJO.Dyck.Aq.yElt_comm`. -/
theorem replicationStar_dPlusStar_mul_yElt (k i : ℕ) (h1 : 1 ≤ i) (hik : i ≤ k) :
    ρ₂ (Dyck.Aq.dPlus L ⅟q k) * ρ (Dyck.Aq.yElt L q k i)
      = ρ (Dyck.Aq.yElt L q (k + 1) (i + 1)) * ρ₂ (Dyck.Aq.dPlus L ⅟q k) := by
  have hcomm : ρ (Dyck.Aq.yElt L q (k + 1) 1) * ρ (Dyck.Aq.yElt L q (k + 1) (i + 1))
      = ρ (Dyck.Aq.yElt L q (k + 1) (i + 1)) * ρ (Dyck.Aq.yElt L q (k + 1) 1) := by
    rw [← map_mul, ← map_mul, Dyck.Aq.yElt_comm (by omega) (by omega) (by omega) (by omega)]
  rw [h2U, smul_mul_assoc, mul_smul_comm]
  congr 1
  rw [mul_assoc, h.dPlusStar_mul_yElt k i h1 hik, ← mul_assoc, hcomm, mul_assoc]

include h h2act h2T h2D h2U in
/-- **The lowest loop of `ρ_2`**: `ρ_2(y_1) = -y_1z_1`, the mirror of
`HJO.Sweep.IsReplicationData.map_yElt_one`. -/
theorem replicationStar_map_yElt_one (m : ℕ) (hm : 1 ≤ m) :
    ρ₂ (Dyck.Aq.yElt L ⅟q m 1)
      = (-1 : L) • (ρ (Dyck.Aq.yElt L q m 1) * ρ' (Dyck.Aq.yElt L ⅟q m 1)) :=
  (h.isReplicationDataStar).map_yElt_one (-1 : L) h2act h2T h2D h2U m hm

include h h2act h2T h2D h2U in
/-- `HJO.Sweep.IsIntertwinedPair`'s fifth condition for `(ρ, ρ_2)`, with the same `u`: only the
lowest loop of `ρ_2` is read, and `HJO.Sweep.replicationStar_map_yElt_one` supplies it. -/
theorem replicationStar_zElt_one_mul_dPlus (k : ℕ) :
    ρ₂ (Dyck.Aq.yElt L ⅟q (k + 1) 1) * ρ (Dyck.Aq.dPlus L q k)
      = (-(u * q ^ (k + 1))) • (ρ (Dyck.Aq.yElt L q (k + 1) 1) * ρ₂ (Dyck.Aq.dPlus L ⅟q k)) := by
  rw [replicationStar_map_yElt_one h h2act h2T h2D h2U (k + 1) (by omega), h2U, smul_mul_assoc,
    mul_assoc, h.zElt_one_mul_dPlus k, mul_smul_comm, smul_smul, mul_smul_comm, smul_smul]
  congr 1
  ring

include h in
/-- **`d_+` moves the starred polynomial inverses up by one index**:
`d_+T̂^*_i = T̂^*_{i+1}d_+`, the mirror of `HJO.Sweep.IsIntertwinedPair.dPlusStar_mul_Tinv`. Those
inverses are `ρ`'s own loops by `HJO.Sweep.IsIntertwinedPair`. -/
theorem IsIntertwinedPair.dPlus_mul_TinvStar {k i : ℕ} (h1 : 1 ≤ i) (hik : i + 1 ≤ k) :
    ρ (Dyck.Aq.dPlus L q k) * ρ' (Dyck.Aq.Tinv L ⅟q k (i - 1))
      = ρ' (Dyck.Aq.Tinv L ⅟q (k + 1) i) * ρ (Dyck.Aq.dPlus L q k) := by
  rw [h.map_Tinv_star k (i - 1) (by omega), h.map_Tinv_star (k + 1) i (by omega), ← map_mul,
    ← map_mul, Dyck.Aq.dPlus_mul_Tg (show i - 1 + 2 ≤ k from by omega),
    show i - 1 + 1 = i from by omega]

include h h2act h2T h2D h2U in
/-- **The base case of `HJO.Sweep.IsIntertwinedPair`'s third condition for `(ρ, ρ_2)`**:
`d_+ρ_2(z_1) = ρ_2(z_2)d_+`, the mirror of `HJO.Sweep.replication_dPlusStar_mul_yElt_one`. -/
theorem replicationStar_dPlus_mul_zElt_one (k : ℕ) (hk : 1 ≤ k) :
    ρ (Dyck.Aq.dPlus L q k) * ρ₂ (Dyck.Aq.yElt L ⅟q k 1)
      = ρ₂ (Dyck.Aq.yElt L ⅟q (k + 1) 2) * ρ (Dyck.Aq.dPlus L q k) := by
  have hDZ : ρ (Dyck.Aq.dPlus L q k) * ρ (Dyck.Aq.yElt L q k 1)
      = ρ' (Dyck.Aq.Tinv L ⅟q (k + 1) 0) * ρ (Dyck.Aq.yElt L q (k + 1) 1)
          * ρ' (Dyck.Aq.Tg L ⅟q (k + 1) 0) * ρ (Dyck.Aq.dPlus L q k) := by
    have hx := congrArg ρ (Dyck.Aq.dPlus_mul_yElt_one (K := L) (q := q) (k := k) hk)
    simp only [map_mul] at hx
    rw [hx, ← h.map_Tinv_star (k + 1) 0 (by omega), ← h.map_Tg_star (k + 1) 0 (by omega)]
  have hDY : ρ (Dyck.Aq.dPlus L q k) * ρ' (Dyck.Aq.yElt L ⅟q k 1)
      = ρ' (Dyck.Aq.yElt L ⅟q (k + 1) 2) * ρ (Dyck.Aq.dPlus L q k) :=
    h.dPlus_mul_zElt k 1 le_rfl hk
  have hTY2 : ρ' (Dyck.Aq.Tg L ⅟q (k + 1) 0) * ρ' (Dyck.Aq.yElt L ⅟q (k + 1) 2)
      = ⅟q • (ρ' (Dyck.Aq.yElt L ⅟q (k + 1) 1) * ρ' (Dyck.Aq.Tinv L ⅟q (k + 1) 0)) := by
    have hx := congrArg ρ' (Dyck.Aq.Tg_mul_yElt_succ_eq (K := L) (q := ⅟q) (k := k + 1) (i := 1)
      le_rfl (by omega))
    rw [map_mul, map_smul, map_mul] at hx
    exact hx
  have h2y : ρ₂ (Dyck.Aq.yElt L ⅟q k 1)
      = (-1 : L) • (ρ (Dyck.Aq.yElt L q k 1) * ρ' (Dyck.Aq.yElt L ⅟q k 1)) :=
    replicationStar_map_yElt_one h h2act h2T h2D h2U k hk
  have h2y' : ρ₂ (Dyck.Aq.yElt L ⅟q (k + 1) 1)
      = (-1 : L) • (ρ (Dyck.Aq.yElt L q (k + 1) 1) * ρ' (Dyck.Aq.yElt L ⅟q (k + 1) 1)) :=
    replicationStar_map_yElt_one h h2act h2T h2D h2U (k + 1) (by omega)
  have h2y2 : ρ₂ (Dyck.Aq.yElt L ⅟q (k + 1) 2)
      = (⅟q * (-1 : L)) • (ρ' (Dyck.Aq.Tinv L ⅟q (k + 1) 0)
          * (ρ (Dyck.Aq.yElt L q (k + 1) 1) * ρ' (Dyck.Aq.yElt L ⅟q (k + 1) 1))
          * ρ' (Dyck.Aq.Tinv L ⅟q (k + 1) 0)) := by
    have hx := (h.isReplicationDataStar).map_yElt_succ h2act h2T (k := k + 1) (i := 1) le_rfl
      (by omega)
    rw [hx, h2y', mul_smul_comm, smul_mul_assoc, smul_smul]
  have hL : ρ (Dyck.Aq.dPlus L q k) * ρ₂ (Dyck.Aq.yElt L ⅟q k 1)
      = ((-1 : L) * ⅟q) • (ρ' (Dyck.Aq.Tinv L ⅟q (k + 1) 0) * ρ (Dyck.Aq.yElt L q (k + 1) 1)
          * (ρ' (Dyck.Aq.yElt L ⅟q (k + 1) 1) * ρ' (Dyck.Aq.Tinv L ⅟q (k + 1) 0))
          * ρ (Dyck.Aq.dPlus L q k)) := by
    rw [h2y, mul_smul_comm, ← mul_assoc, hDZ,
      mul_assoc (ρ' (Dyck.Aq.Tinv L ⅟q (k + 1) 0) * ρ (Dyck.Aq.yElt L q (k + 1) 1)
        * ρ' (Dyck.Aq.Tg L ⅟q (k + 1) 0)) (ρ (Dyck.Aq.dPlus L q k))
        (ρ' (Dyck.Aq.yElt L ⅟q k 1)), hDY, ← mul_assoc,
      mul_assoc (ρ' (Dyck.Aq.Tinv L ⅟q (k + 1) 0) * ρ (Dyck.Aq.yElt L q (k + 1) 1))
        (ρ' (Dyck.Aq.Tg L ⅟q (k + 1) 0)) (ρ' (Dyck.Aq.yElt L ⅟q (k + 1) 2)), hTY2,
      mul_smul_comm, smul_mul_assoc, smul_smul]
  rw [hL, h2y2, smul_mul_assoc]
  congr 1
  ring

include h h2act h2T h2D h2U in
/-- **`HJO.Sweep.IsIntertwinedPair`'s third condition for `(ρ, ρ_2)`**:
`d_+ρ_2(z_i) = ρ_2(z_{i+1})d_+` for `1 ≤ i ≤ k`, the mirror of
`HJO.Sweep.replication_dPlusStar_mul_yElt` and carried by the same recursion. -/
theorem replicationStar_dPlus_mul_zElt :
    ∀ i : ℕ, 1 ≤ i → ∀ k : ℕ, i ≤ k →
      ρ (Dyck.Aq.dPlus L q k) * ρ₂ (Dyck.Aq.yElt L ⅟q k i)
        = ρ₂ (Dyck.Aq.yElt L ⅟q (k + 1) (i + 1)) * ρ (Dyck.Aq.dPlus L q k) := by
  intro i h1
  induction i, h1 using Nat.le_induction with
  | base =>
    intro k hk
    exact replicationStar_dPlus_mul_zElt_one h h2act h2T h2D h2U k hk
  | succ i hi ih =>
    intro k hik
    have hrec : ρ₂ (Dyck.Aq.yElt L ⅟q k (i + 1))
        = ⅟q • (ρ' (Dyck.Aq.Tinv L ⅟q k (i - 1)) * ρ₂ (Dyck.Aq.yElt L ⅟q k i)
            * ρ' (Dyck.Aq.Tinv L ⅟q k (i - 1))) :=
      (h.isReplicationDataStar).map_yElt_succ h2act h2T (k := k) (i := i) hi (by omega)
    have hrec' : ρ₂ (Dyck.Aq.yElt L ⅟q (k + 1) (i + 1 + 1))
        = ⅟q • (ρ' (Dyck.Aq.Tinv L ⅟q (k + 1) i) * ρ₂ (Dyck.Aq.yElt L ⅟q (k + 1) (i + 1))
            * ρ' (Dyck.Aq.Tinv L ⅟q (k + 1) i)) :=
      (h.isReplicationDataStar).map_yElt_succ h2act h2T (k := k + 1) (i := i + 1) (by omega)
        (by omega)
    have hcross := h.dPlus_mul_TinvStar (k := k) (i := i) hi (by omega)
    rw [hrec, mul_smul_comm, ← mul_assoc, ← mul_assoc, hcross,
      mul_assoc (ρ' (Dyck.Aq.Tinv L ⅟q (k + 1) i)) (ρ (Dyck.Aq.dPlus L q k))
        (ρ₂ (Dyck.Aq.yElt L ⅟q k i)),
      ih k (by omega), ← mul_assoc,
      mul_assoc (ρ' (Dyck.Aq.Tinv L ⅟q (k + 1) i) * ρ₂ (Dyck.Aq.yElt L ⅟q (k + 1) (i + 1)))
        (ρ (Dyck.Aq.dPlus L q k)) (ρ' (Dyck.Aq.Tinv L ⅟q k (i - 1))),
      hcross, hrec', smul_mul_assoc, ← mul_assoc]

include h h2act h2T h2D h2U in
/-- **The replicated pair `(ρ, ρ_2)` is correctly intertwined**, the second half of
`HJO.Sweep.isIntertwinedPair_replication_pairs`, and with the same `u`. -/
theorem isIntertwinedPair_replicationStar : IsIntertwinedPair q u ρ ρ₂ where
  isAction := h.isAction
  isActionStar := h2act
  map_Tg_star k s hs := replicationStar_map_Tg_star h h2T k s hs
  map_dMinus_star k := replicationStar_map_dMinus_star h h2D k
  dPlus_mul_zElt k i hi hik :=
    replicationStar_dPlus_mul_zElt h h2act h2T h2D h2U i hi k hik
  dPlusStar_mul_yElt k i hi hik := replicationStar_dPlusStar_mul_yElt h h2U k i hi hik
  zElt_one_mul_dPlus k := replicationStar_zElt_one_mul_dPlus h h2act h2T h2D h2U k

end PairsStar

/-! ### The statement -/

section Node

variable {L : Type*} [CommRing L] {q u : L} [Invertible q] [Invertible (q - 1)]
  {ρ : Dyck.Aq L q →ₐ[L] Module.End L (Vstar L)}
  {ρ' : Dyck.AqInv L q →ₐ[L] Module.End L (Vstar L)}
  {ρ₁ : Dyck.Aq L q →ₐ[L] Module.End L (Vstar L)}
  {ρ₂ : Dyck.AqInv L q →ₐ[L] Module.End L (Vstar L)}

/-- **The replicated pairs are correctly intertwined**, which is
`HJO.Sweep.isIntertwinedPair_replication_pairs`: with the hypotheses and notation of
`HJO.Sweep.exists_isDpaAction_replication`, the pairs `(ρ, ρ_2)` and `(ρ_1, ρ^*)` are correctly
intertwined, and with the same `u`.

`ρ_1` and `ρ_2` are read through the value clauses `HJO.Sweep.exists_isDpaAction_replication` and
`HJO.Sweep.exists_isDpaAction_replication_star` produce, which is stronger than a statement about
the two chosen witnesses. The standing hypothesis on the loops at the vertex `2` is discharged and
not carried, and the scalar of `ρ_1` is left free, as in those two results.

The usual computation of the loops of `ρ_1` is wrong and is not followed; see this file's
implementation notes for the defect and for the route taken instead. -/
@[hjo "lem_dpa_replication_pairs"]
theorem isIntertwinedPair_replication_pairs (h : IsIntertwinedPair q u ρ ρ') (c : L)
    (h1act : IsDpaAction q ρ₁)
    (h1T : ∀ k i : ℕ, ρ₁ (Dyck.Aq.Tg L q k i) = ρ (Dyck.Aq.Tg L q k i))
    (h1D : ∀ k : ℕ, ρ₁ (Dyck.Aq.dMinus L q k) = ρ (Dyck.Aq.dMinus L q k))
    (h1U : ∀ k : ℕ, ρ₁ (Dyck.Aq.dPlus L q k)
      = c • (ρ' (Dyck.Aq.yElt L ⅟q (k + 1) 1) * ρ (Dyck.Aq.dPlus L q k)))
    (h2act : IsDpaAction ⅟q ρ₂)
    (h2T : ∀ k i : ℕ, ρ₂ (Dyck.Aq.Tg L ⅟q k i) = ρ' (Dyck.Aq.Tg L ⅟q k i))
    (h2D : ∀ k : ℕ, ρ₂ (Dyck.Aq.dMinus L ⅟q k) = ρ' (Dyck.Aq.dMinus L ⅟q k))
    (h2U : ∀ k : ℕ, ρ₂ (Dyck.Aq.dPlus L ⅟q k)
      = (-1 : L) • (ρ (Dyck.Aq.yElt L q (k + 1) 1) * ρ' (Dyck.Aq.dPlus L ⅟q k))) :
    IsIntertwinedPair q u ρ₁ ρ' ∧ IsIntertwinedPair q u ρ ρ₂ :=
  ⟨isIntertwinedPair_replication h c h1act h1T h1D h1U,
    isIntertwinedPair_replicationStar h h2act h2T h2D h2U⟩

end Node

end HJO.Sweep

end
