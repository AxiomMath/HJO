/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.CarlssonMellit.DPATilde
public import HJO.Shuffle.DpaAction
public meta import HJO.Attr

/-! # A correctly intertwined pair of actions

Mellit's replication takes a pair of actions — one of `𝔸_q` and one of `𝔸_{q^{-1}}` on the same
`V_*` — and builds two new ones from it. What makes the construction go through is not that the two
actions exist but that they are *correctly intertwined*: they share their braid and lowering parts,
each raising operator moves the other's loops up by one index, and the two raising operators are
related by one scalar identity. `HJO.Sweep.IsIntertwinedPair` is that condition, and this file
states it.

## Main definitions

* `HJO.Sweep.IsIntertwinedPair`.

## Implementation notes

**The two algebras are one, at two bases.** As in `HJO/Shuffle/DpaAction.lean`, `𝔸_{q^{-1}}`
is `HJO.Dyck.AqInv L q`, which *is* `HJO.Dyck.Aq L ⅟q` (`HJO.Dyck.AqInv`), so the pair is a
pair of `HJO.Sweep.IsDpaAction`s at the two bases `q` and `⅟q` and no transport appears. The
`z_i` are by definition the images under `ρ*` of the loops `y_i`, so they are
`HJO.Dyck.Aq.yElt L ⅟q k i` — the loops of `HJO.Dyck.Aq.yElt` read in `𝔸_{q^{-1}}` — and nothing of
the double algebra `Ã` is needed to say what they are.

**`(q^{-1}-1)^{-1}` is not a hypothesis.** `HJO.Dyck.Aq.yElt`'s leading scalar at the base `q^{-1}`
is `(q^{-1}-1)^{-1}`, so the loops of `𝔸_{q^{-1}}` need `⅟q - 1` invertible; that is *derivable*
from `Invertible q` and `Invertible (q-1)`, the inverse being the `-q(q-1)^{-1}` that
`HJO.Dyck.Tilde.neg_mul_invOf_sub_one_mul` already identifies as the substituted scalar of
`HJO.Dyck.Tilde.freeZ`. `HJO.Dyck.invertibleInvOfSubOne` below records it as an instance, which is
what keeps `HJO.Dyck.Aq.yElt L ⅟q k i` canonical: `Invertible` is a data class, so an `⅟(⅟q - 1)`
elaborated against an ad-hoc instance at one use site and a different one at another would give two
non-syntactically-equal loops.

**`T_i^{-1}` is the polynomial inverse, not an operator inverse.** The first condition
is `ρ*(T_i) = T_i^{-1}`, and `T_i^{-1}` is `HJO.Dyck.braidInvGen`'s `T̂_i = q^{-1}(T_i + (q-1)e_k)`,
an element of the algebra; so the condition is `ρ*(T_i) = ρ(T̂_i)` and no endomorphism has to be
inverted. That is the right reading and not a weakening: `ρ(T̂_i)` is a two-sided inverse of
`ρ(T_i)` only on `V_k`, since `ρ(T_iT̂_i) = ρ(𝟏_k)` is the projection and not the identity, and
"as maps on `V_k`" is exactly the qualification attached to all five conditions.

**All five conditions are equalities of endomorphisms of the whole of `V_*`.** Each side of each is
the image of a path of `HJO.Dyck.Aq`, so by
`HJO.Sweep.IsDpaAction.eq_pieceProj_mul_mul_pieceProj` it already vanishes off the summand the path
starts at; no restriction map appears and the "as maps on `V_k`" costs nothing.

**The index of the braid condition is the shifted one**, as everywhere in `HJO.Dyck.Aq`: the
`T_i` at the vertex `k` of Definition 3.2 of A. Mellit, *Toric braids and `(m, n)`-parking
functions*, arXiv:1604.07456, is `Tg L q k (i-1)`, so its `1 ≤ i ≤ k-1` is `s + 2 ≤ k` on the
shifted `s`. The loops keep Mellit's index, `yElt L q k i` being `y_i`.

**`u` is a parameter and is not assumed invertible.** The scalar `-uq^{k+1}` of the last condition
is the only place `u` occurs in the definition; `u` belongs to the double algebra `Ã` of
`HJO.Dyck.Tilde.Atilde` and not to `𝔸_q`, so it is carried here as a ring element. It is nowhere
assumed invertible, which is why `HJO.Sweep.exists_isDpaAction_replication` leaves its scalar free.

## References

Definition `HJO.Sweep.IsIntertwinedPair`, using `HJO.Dyck.Aq`, `HJO.Dyck.braidInvGen`,
`HJO.Dyck.Aq.yElt`, `HJO.Sweep.Vstar`, `HJO.Dyck.AqInv` and `HJO.Sweep.IsDpaAction`; consumed by
`HJO.Sweep.exists_isIntertwinedPair_vmod`, `HJO.Sweep.exists_isDpaAction_replication`,
`HJO.Sweep.exists_isDpaAction_replication_star`, `HJO.Sweep.isIntertwinedPair_replication_pairs` and
`HJO.Sweep.exists_slopeActions`. Transcribing A. Mellit, *Toric braids and `(m, n)`-parking
functions*, Definition 3.2, whose `t` is written `u`.
-/

@[expose] public section

namespace HJO.Dyck

/-- **`q^{-1}-1` is invertible as soon as `q` and `q-1` are**, with inverse `-q(q-1)^{-1}`. This is
what lets `HJO.Dyck.Aq.yElt` be read at the base `q^{-1}`, and the scalar is the one
`HJO.Dyck.Tilde.freeZ` substitutes for `(q-1)^{-1}`. -/
instance invertibleInvOfSubOne {K : Type*} [CommRing K] {q : K} [Invertible q]
    [Invertible (q - 1)] : Invertible (⅟q - 1) where
  invOf := -(q * ⅟(q - 1))
  invOf_mul_self := Tilde.neg_mul_invOf_sub_one_mul
  mul_invOf_self := by rw [mul_comm]; exact Tilde.neg_mul_invOf_sub_one_mul

end HJO.Dyck

namespace HJO.Sweep

variable {L : Type*} [CommRing L] {q u : L} [Invertible q] [Invertible (q - 1)]

/-- **A correctly intertwined pair**, `HJO.Sweep.IsIntertwinedPair`: an action `ρ` of `𝔸_q`
on `V_*` and an action `ρ*` of `𝔸_{q^{-1}}` on `V_*` such that, writing `T_i, d_-, d_+, y_i` for the
images under `ρ` of the generators of `HJO.Dyck.Aq` and of the loops of `HJO.Dyck.Aq.yElt`, and
`d^*_+, z_i` for the images under `ρ*` of `d_+` and of those loops, the five conditions

* `ρ*(T_i) = T_i^{-1}` for `1 ≤ i ≤ k-1`,
* `ρ*(d_-) = d_-`,
* `d_+z_i = z_{i+1}d_+` for `1 ≤ i ≤ k`,
* `d^*_+y_i = y_{i+1}d^*_+` for `1 ≤ i ≤ k`,
* `z_1d_+ = -uq^{k+1}y_1d^*_+`

hold for every `k ≥ 0` as maps on `V_k`. The first two say that the two actions share their braid
and lowering parts; the last three are the relations `HJO.Dyck.Tilde.Atilde` imposes on the double
algebra, so a correctly intertwined pair is the same thing as an action of that algebra restricting
to `ρ` and `ρ*`. -/
@[hjo "def_dpa_intertwined"]
structure IsIntertwinedPair (q u : L) [Invertible q] [Invertible (q - 1)]
    (ρ : Dyck.Aq L q →ₐ[L] Module.End L (Vstar L))
    (ρ' : Dyck.AqInv L q →ₐ[L] Module.End L (Vstar L)) : Prop where
  /-- `ρ` is an action of `𝔸_q` on `V_*`. -/
  isAction : IsDpaAction q ρ
  /-- `ρ*` is an action of `𝔸_{q^{-1}}` on `V_*`. -/
  isActionStar : IsDpaAction ⅟q ρ'
  /-- `ρ*(T_i) = T_i^{-1}` for `1 ≤ i ≤ k-1`, the shifted index `s` being Mellit's `i-1`. -/
  map_Tg_star : ∀ k s : ℕ, s + 2 ≤ k →
    ρ' (Dyck.Aq.Tg L ⅟q k s) = ρ (Dyck.Aq.Tinv L q k s)
  /-- `ρ*(d_-) = d_-`. -/
  map_dMinus_star : ∀ k : ℕ, ρ' (Dyck.Aq.dMinus L ⅟q k) = ρ (Dyck.Aq.dMinus L q k)
  /-- `d_+z_i = z_{i+1}d_+` for `1 ≤ i ≤ k`. -/
  dPlus_mul_zElt : ∀ k i : ℕ, 1 ≤ i → i ≤ k →
    ρ (Dyck.Aq.dPlus L q k) * ρ' (Dyck.Aq.yElt L ⅟q k i)
      = ρ' (Dyck.Aq.yElt L ⅟q (k + 1) (i + 1)) * ρ (Dyck.Aq.dPlus L q k)
  /-- `d^*_+y_i = y_{i+1}d^*_+` for `1 ≤ i ≤ k`. -/
  dPlusStar_mul_yElt : ∀ k i : ℕ, 1 ≤ i → i ≤ k →
    ρ' (Dyck.Aq.dPlus L ⅟q k) * ρ (Dyck.Aq.yElt L q k i)
      = ρ (Dyck.Aq.yElt L q (k + 1) (i + 1)) * ρ' (Dyck.Aq.dPlus L ⅟q k)
  /-- `z_1d_+ = -uq^{k+1}y_1d^*_+`. -/
  zElt_one_mul_dPlus : ∀ k : ℕ,
    ρ' (Dyck.Aq.yElt L ⅟q (k + 1) 1) * ρ (Dyck.Aq.dPlus L q k)
      = (-(u * q ^ (k + 1))) • (ρ (Dyck.Aq.yElt L q (k + 1) 1) * ρ' (Dyck.Aq.dPlus L ⅟q k))

variable {ρ : Dyck.Aq L q →ₐ[L] Module.End L (Vstar L)}
  {ρ' : Dyck.AqInv L q →ₐ[L] Module.End L (Vstar L)}

/-- **The two actions of an intertwined pair agree on the idempotents**, both sending `𝟏_k` to the
projection onto `V_k` by `HJO.Sweep.IsDpaAction`. This is the sense in which the two share their
vertices, and it is what lets the five conditions be read as equalities of endomorphisms of the
whole of `V_*`. -/
theorem IsIntertwinedPair.map_e_star (h : IsIntertwinedPair q u ρ ρ') (k : ℕ) :
    ρ' (Dyck.Aq.e L ⅟q k) = ρ (Dyck.Aq.e L q k) := by
  rw [h.isActionStar.map_e, h.isAction.map_e]

end HJO.Sweep
