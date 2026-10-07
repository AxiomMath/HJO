/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.CarlssonMellit.CornerGeneric
public meta import HJO.Attr

/-! # Twisting the raising arrow by a loop variable, inside an algebra

`HJO.Sweep.IsReplicationData` reads off a pair of actions on `V_*` the six identities that let the
raising operator be replaced by `c·Ξ_1d₊` and still satisfy the paper's relations. Every one of
its proofs is a rearrangement of products and scalars; none of them looks at `V_*`. This file is
that construction with `Module.End L (V_*)` replaced by an arbitrary algebra and the action
replaced by a family of elements — so that it can be read *inside* `Ã`, where the two raising
arrows and the loop variables `y_i`, `z_i` all live in one ring and there is no action to speak of.

## Main definitions

* `HJO.Dyck.twistRaise`: the twisted raising family `c·v_{k+1}U_k`.
* `HJO.Dyck.TwistFamily`: the six identities the twist reads off `v` and `w` — `v_k` is a loop at
  its vertex, the raising arrow carries `v` up to `w`, the lowering arrow carries each of them
  down, `v_k` commutes with every loop above the first, and the product `v_kw_k` commutes with the
  first.

## Main results

* `HJO.Dyck.TwistFamily.eq_of_sourceRel_twistRaise`: **the twisted family satisfies the paper's
  relations.** Every instance of `HJO.Dyck.SourceRel` in the twisted raising family is an identity,
  given that every instance in the untwisted one is. This is the algebra-internal
  `Rel`-discharge: at the starred family of `Ã` with `v = y_1`, `w = y_2` and `c = -1` it is the
  half of the index shift that the starred group of `HJO.Dyck.Tilde.Atilde` asks for, and at the
  unstarred family with `v = z_1`, `w = z_2` it is the same half of the conjugator.
* `HJO.Dyck.TwistFamily.commOf_twistRaise`: the twisted commutator is `c·v_{k+1}` times the old one
  — the identity `HJO.Sweep.IsReplicationData.deltaRep_eq` states for `V_*`.
* `HJO.Dyck.TwistFamily.cornerOf_one_twistRaise`: **the twisted first corner element is `c·v_k`
  times the old one**, `y_1 ↦ c·v_ky_1`. This is the only corner element for which the formula is
  that simple, and the reason is `HJO.Dyck.cornerOf_one_eq_comm`: the closed form of `y_1` puts the
  commutator at the *left*, where `commOf_twistRaise` has just put `v_k`, so no commutation is
  needed. For `i ≥ 2` the analogous formula is false — see the implementation notes.

## Implementation notes

**Why only the first corner element gets a closed form.** `cornerOf … k i` for `i ≥ 2` carries the
descending word of polynomial inverses to the left of the commutator, and that word ends in the
*first* inverse `T̂_1`, with which `v_k` does not commute: `v_kT_1 = T_1v_k` is exactly what
`HJO.Dyck.cornerOf_recursion` denies at `i = 1`. So the twisted corner element is the conjugate
`W_{i-1}(c·v_k)W_{i-1}^{-1}` times the old one rather than `c·v_k` times it, and its consumers go
through `HJO.Dyck.cornerOf_recursion` — which reads no property of the family at all, and so holds
verbatim at the twisted one — rather than through a closed form. The same correction is recorded at
`HJO.Sweep.IsReplicationData.map_yElt_succ` for the `V_*` reading, where the naive closed form
`c·v_k` would make the argument for `HJO.Sweep.isIntertwinedPair_replication_pairs` go wrong.

**The index ranges.** They are the ranges of `HJO.Sweep.IsReplicationData`, and they are not
uniform: `lower_mul_w` starts at `2` and not at `1`, because at the vertex `1` the second loop
variable `w_1` is not a loop of the quiver. The relations never read it there.

`w` is not assumed to be anything in particular — in both readings it is the *second* loop
variable, `y_2` or `z_2`, but the construction only ever uses the three identities it appears in.

## References

The lemmas `HJO.Sweep.exists_isDpaAction_replication` and
`HJO.Sweep.exists_isDpaAction_replication_star`, read inside the algebra rather than on `V_*`; and
E. Carlsson and A. Mellit, *A proof of the shuffle conjecture*, J. Amer. Math. Soc. **31** (2018)
661--697, Section 3. -/

@[expose] public section

namespace HJO.Dyck

variable {K : Type*} [CommRing K] {A : Type*} [Ring A] [Algebra K A]

/-! ### The twisted raising family -/

/-- **The twisted raising family** `c·v_{k+1}U_k`: the raising arrow multiplied by a loop variable
at the vertex it lands on, and by a scalar. -/
def twistRaise (c : K) (v U : ℕ → A) (k : ℕ) : A := c • (v (k + 1) * U k)

theorem twistRaise_apply (c : K) (v U : ℕ → A) (k : ℕ) :
    twistRaise c v U k = c • (v (k + 1) * U k) := rfl

/-- **What the twist reads off the loop variables.** The six identities of
`HJO.Sweep.IsReplicationData`, with the action's images replaced by elements of an algebra: `v_k` is
a loop at the vertex `k`, the raising arrow carries `v` up to `w`, the lowering arrow carries each
of `v` and `w` down, `v_k` commutes with every loop of the quiver above the first, and the product
`v_kw_k` commutes with the first. -/
structure TwistFamily (E U D : ℕ → A) (T : ℕ → ℕ → A) (v w : ℕ → A) : Prop where
  /-- `v_k` is a loop at the vertex `k`, absorbed by the idempotent on the left. -/
  e_mul_v : ∀ k : ℕ, E k * v k = v k
  /-- `Uv_k = w_{k+1}U`: the raising arrow carries the first loop variable up to the second. -/
  raise_mul_v : ∀ k : ℕ, 1 ≤ k → U k * v k = w (k + 1) * U k
  /-- `Dv_{m+1} = v_mD`. -/
  lower_mul_v : ∀ m : ℕ, 1 ≤ m → D m * v (m + 1) = v m * D m
  /-- `Dw_{m+1} = w_mD`. At the vertex `1` there is no `w`, and no relation reads it there. -/
  lower_mul_w : ∀ m : ℕ, 2 ≤ m → D m * w (m + 1) = w m * D m
  /-- `v_kT_{s+1} = T_{s+1}v_k` for `1 ≤ s`: the loops `v` does not touch. -/
  v_mul_loop : ∀ k s : ℕ, 1 ≤ s → s + 2 ≤ k → v k * T k s = T k s * v k
  /-- `v_kw_kT_1 = T_1v_kw_k`: the first loop commutes with the *product* of the two variables,
  which is all the relations at the first loop ever need. -/
  vw_mul_loop : ∀ k : ℕ, 2 ≤ k → v k * w k * T k 0 = T k 0 * (v k * w k)

/-! ### The recursion, read upwards

`HJO.Dyck.cornerOf_recursion` computes `y_i` from `y_{i+1}`. The twist's consumers need it the other
way round — `y_{i+1}` from `y_i` — because the only corner element they have a closed form for is
the first one. Inverting it is conjugating by the polynomial inverse instead of by the loop, and
that needs the inverse to invert *on both sides*, which `HJO.Dyck.CornerFamily` gives only on one;
the other side is `HJO.Dyck.CornerFamily.tinvOf_mul_T`, and it is free because a loop commutes with
its own polynomial inverse. -/

namespace CornerFamily

variable {q' qi di : K} {E U D : ℕ → A} {T : ℕ → ℕ → A}

/-- **A loop commutes with its own polynomial inverse**, the inverse being a `K`-combination of the
loop and the idempotent at the same vertex. No range hypothesis: outside the range both products
are the same combination of `T` and `E`. -/
theorem tinvOf_comm (h : CornerFamily q' qi E U D T) (k i : ℕ) :
    tinvOf q' qi (T k i) (E k) * T k i = T k i * tinvOf q' qi (T k i) (E k) := by
  rw [tinvOf, smul_mul_assoc, mul_smul_comm, add_mul, mul_add, smul_mul_assoc, mul_smul_comm,
    h.e_mul_T, h.T_mul_e]

/-- **The polynomial inverse inverts the loop on the left too**, `HJO.Dyck.CornerFamily.T_mul_Tinv`
being the right-hand version. -/
theorem tinvOf_mul_T (h : CornerFamily q' qi E U D T) {k i : ℕ} (hik : i + 2 ≤ k) :
    tinvOf q' qi (T k i) (E k) * T k i = E k := by
  rw [h.tinvOf_comm k i, h.T_mul_Tinv k i hik]

/-- **The paper's recursion read upwards**: `y_{i+1} = q^{-1}T̂_iy_iT̂_i`, where the recursion of
`HJO.Dyck.cornerOf` reads `y_i = q T_iy_{i+1}T_i` downwards. The inverse of `qi` is supplied as the
ring element `qi'`, as everywhere in this cluster. -/
theorem cornerOf_recursion_up (h : CornerFamily q' qi E U D T) {qi' : K} (hqi : qi' * qi = 1)
    {k i : ℕ} (h1 : 1 ≤ i) (hik : i < k) :
    cornerOf q' qi di E U D T k (i + 1)
      = qi' • (tinvOf q' qi (T k (i - 1)) (E k) * cornerOf q' qi di E U D T k i
          * tinvOf q' qi (T k (i - 1)) (E k)) := by
  rw [cornerOf_recursion (q' := q') (qi := qi) (di := di) (U := U) (D := D) h1 hik,
    mul_smul_comm, smul_mul_assoc, smul_smul, hqi, one_smul,
    show tinvOf q' qi (T k (i - 1)) (E k) *
          (T k (i - 1) * cornerOf q' qi di E U D T k (i + 1) * T k (i - 1)) *
          tinvOf q' qi (T k (i - 1)) (E k)
        = tinvOf q' qi (T k (i - 1)) (E k) * T k (i - 1) *
          cornerOf q' qi di E U D T k (i + 1) *
          (T k (i - 1) * tinvOf q' qi (T k (i - 1)) (E k)) from by simp only [mul_assoc],
    h.tinvOf_mul_T (k := k) (i := i - 1) (by omega),
    h.T_mul_Tinv k (i - 1) (by omega), h.e_mul_cornerOf, h.cornerOf_mul_e]

end CornerFamily

namespace TwistFamily

variable {q' qi di : K} {E U D : ℕ → A} {T : ℕ → ℕ → A} {v w : ℕ → A}

/-! ### The commutator and the double raising -/

/-- **The twisted commutator is `c·v_{k+1}` times the old one.** The lowering arrow is the only
generator the commutator puts to the left of a raising arrow, and carrying `v` down past it is
exactly what makes the scalar factor come out in front. This is
`HJO.Sweep.IsReplicationData.deltaRep_eq`. -/
theorem commOf_twistRaise (h : TwistFamily E U D T v w) (c : K) (n : ℕ) :
    commOf (twistRaise c v U) D n = c • (v (n + 1) * commOf U D n) := by
  rw [commOf, commOf, twistRaise_apply, twistRaise_apply, smul_mul_assoc, mul_smul_comm,
    ← smul_sub, mul_sub]
  congr 1
  rw [mul_assoc, ← mul_assoc (D (n + 1)) (v (n + 2)) (U (n + 1)),
    h.lower_mul_v (n + 1) (by omega)]
  simp only [mul_assoc]

/-- **The two twisted raising arrows compose to `c²v_{k+2}w_{k+2}` times the old composite**: the
first `v` is carried up to a `w` across the lower arrow. This is
`HJO.Sweep.IsReplicationData.repRaise_mul_repRaise`. -/
theorem twistRaise_mul_twistRaise (h : TwistFamily E U D T v w) (c : K) (k : ℕ) :
    twistRaise c v U (k + 1) * twistRaise c v U k
      = (c * c) • (v (k + 2) * w (k + 2) * (U (k + 1) * U k)) := by
  rw [twistRaise_apply, twistRaise_apply, smul_mul_assoc, mul_smul_comm, smul_smul]
  congr 1
  rw [mul_assoc (v (k + 2)), ← mul_assoc (U (k + 1)) (v (k + 1)) (U k),
    h.raise_mul_v (k + 1) (by omega)]
  simp only [mul_assoc]

/-- **The old commutator carries `v` up to `w`**, the "the commutator `d_+d_- - d_-d_+`
conjugates `y_1` to `y_2`". This is `HJO.Sweep.IsReplicationData.delta_mul_loopVar`, and it is the
only place `lower_mul_w` is read. -/
theorem commOf_mul_v (h : TwistFamily E U D T v w) (m : ℕ) :
    commOf U D (m + 1) * v (m + 2) = w (m + 2) * commOf U D (m + 1) := by
  have h1 : U (m + 1) * D (m + 1) * v (m + 2) = w (m + 2) * (U (m + 1) * D (m + 1)) := by
    rw [mul_assoc, h.lower_mul_v (m + 1) (by omega), ← mul_assoc,
      h.raise_mul_v (m + 1) (by omega), mul_assoc]
  have h2 : D (m + 2) * U (m + 2) * v (m + 2) = w (m + 2) * (D (m + 2) * U (m + 2)) := by
    rw [mul_assoc, h.raise_mul_v (m + 2) (by omega), ← mul_assoc,
      h.lower_mul_w (m + 2) (by omega), mul_assoc]
  rw [commOf, sub_mul, h1, h2, mul_sub]

/-! ### The twisted family satisfies the paper's relations -/

/-- **The twisted family satisfies the paper's relations.** Every instance of `HJO.Dyck.SourceRel`
read in the twisted raising family `c·v_{k+1}U_k` is an identity of the algebra, given that every
instance read in `U` is.

This is the algebra-internal form of `HJO.Sweep.exists_isDpaAction_replication`:
`HJO.Sweep.IsReplicationData.isDpaRepOps` proves the same eleven relations for operators on `V_*`,
and nothing in that proof looks at `V_*`. The five relations that do not mention the raising arrow
are the untwisted ones verbatim; the six that do are the ones the six identities of
`HJO.Dyck.TwistFamily` are chosen for. -/
theorem eq_of_sourceRel_twistRaise {q : K} (h : TwistFamily E U D T v w)
    (heq : ∀ {x y : A}, SourceRel q E U D T x y → x = y) (c : K) {x y : A}
    (hr : SourceRel q E (twistRaise c v U) D T x y) : x = y := by
  induction hr with
  | vertex_mul_up k =>
    rw [twistRaise_apply, mul_smul_comm, ← mul_assoc, h.e_mul_v (k + 1)]
  | up_mul_vertex k =>
    rw [twistRaise_apply, smul_mul_assoc, mul_assoc, heq (SourceRel.up_mul_vertex k)]
  | quadratic hik => exact heq (SourceRel.quadratic hik)
  | braid_braid hik => exact heq (SourceRel.braid_braid hik)
  | braid_comm hi hj hij => exact heq (SourceRel.braid_comm hi hj hij)
  | braid_down him => exact heq (SourceRel.braid_down him)
  | down_down_braid m => exact heq (SourceRel.down_down_braid m)
  | @up_braid k i hik =>
    rw [twistRaise_apply, smul_mul_assoc, mul_smul_comm]
    congr 1
    rw [mul_assoc, heq (SourceRel.up_braid hik), ← mul_assoc,
      h.v_mul_loop (k + 1) (i + 1) (by omega) (by omega), mul_assoc]
  | braid_up_up k =>
    rw [h.twistRaise_mul_twistRaise c k, mul_smul_comm]
    congr 1
    rw [← mul_assoc, ← h.vw_mul_loop (k + 2) (by omega), mul_assoc (v (k + 2) * w (k + 2)),
      heq (SourceRel.braid_up_up k)]
  | down_delta j =>
    have hd := heq (SourceRel.down_delta (E := E) (U := U) (D := D) (T := T) j)
    have hlv : D (j + 1) * v (j + 2) = v (j + 1) * D (j + 1) := h.lower_mul_v (j + 1) (by omega)
    have hc1 : commOf (twistRaise c v U) D (j + 1) = c • (v (j + 2) * commOf U D (j + 1)) :=
      h.commOf_twistRaise c (j + 1)
    have hc0 : commOf (twistRaise c v U) D j = c • (v (j + 1) * commOf U D j) :=
      h.commOf_twistRaise c j
    have hstep : D (j + 1) * (v (j + 2) * commOf U D (j + 1)) * T (j + 2) j
        = v (j + 1) * (q • (commOf U D j * D (j + 1))) := by
      rw [← mul_assoc, hlv, mul_assoc (v (j + 1)) (D (j + 1)) (commOf U D (j + 1)),
        mul_assoc (v (j + 1)) (D (j + 1) * commOf U D (j + 1)) (T (j + 2) j), hd]
    rw [hc1, hc0]
    simp only [smul_mul_assoc, mul_smul_comm, smul_smul]
    rw [hstep]
    simp only [mul_smul_comm, smul_smul]
    rw [show c * q = q * c from by ring]
    congr 1
    simp only [mul_assoc]
  | braid_delta m =>
    have hb := heq (SourceRel.braid_delta (E := E) (U := U) (D := D) (T := T) m)
    have hcv : commOf U D (m + 1) * v (m + 2) = w (m + 2) * commOf U D (m + 1) := h.commOf_mul_v m
    have hrv : U (m + 1) * v (m + 1) = w (m + 2) * U (m + 1) := h.raise_mul_v (m + 1) (by omega)
    have hvw : v (m + 2) * w (m + 2) * T (m + 2) 0 = T (m + 2) 0 * (v (m + 2) * w (m + 2)) :=
      h.vw_mul_loop (m + 2) (by omega)
    have hc1 : commOf (twistRaise c v U) D (m + 1) = c • (v (m + 2) * commOf U D (m + 1)) :=
      h.commOf_twistRaise c (m + 1)
    have hc0 : commOf (twistRaise c v U) D m = c • (v (m + 1) * commOf U D m) :=
      h.commOf_twistRaise c m
    have hu : twistRaise c v U (m + 1) = c • (v (m + 2) * U (m + 1)) := rfl
    have hstep : T (m + 2) 0 * (v (m + 2) * commOf U D (m + 1)) * (v (m + 2) * U (m + 1))
        = v (m + 2) * w (m + 2) * (q • (U (m + 1) * commOf U D m)) := by
      calc T (m + 2) 0 * (v (m + 2) * commOf U D (m + 1)) * (v (m + 2) * U (m + 1))
          = T (m + 2) 0 * v (m + 2) * (commOf U D (m + 1) * v (m + 2)) * U (m + 1) := by
            simp only [mul_assoc]
        _ = T (m + 2) 0 * v (m + 2) * (w (m + 2) * commOf U D (m + 1)) * U (m + 1) := by rw [hcv]
        _ = v (m + 2) * w (m + 2) * (T (m + 2) 0 * commOf U D (m + 1) * U (m + 1)) := by
            rw [← mul_assoc (T (m + 2) 0 * v (m + 2)) (w (m + 2)) (commOf U D (m + 1)),
              mul_assoc (T (m + 2) 0) (v (m + 2)) (w (m + 2)), ← hvw]
            simp only [mul_assoc]
        _ = v (m + 2) * w (m + 2) * (q • (U (m + 1) * commOf U D m)) := by rw [hb]
    rw [hc1, hc0, hu]
    simp only [smul_mul_assoc, mul_smul_comm, smul_smul]
    rw [hstep]
    simp only [mul_smul_comm, smul_smul]
    rw [show c * c * q = q * (c * c) from by ring]
    congr 1
    simp only [mul_assoc]
    rw [← mul_assoc (w (m + 2)) (U (m + 1)) (commOf U D m), ← hrv]
    simp only [mul_assoc]

/-! ### The twisted corner elements -/

/-- The twisted family is again a `HJO.Dyck.CornerFamily`: the four fields about the idempotents and
the loops are shared, and the two about the commutator follow from
`HJO.Dyck.TwistFamily.commOf_twistRaise` together with `v_k` being a loop at its vertex. -/
theorem cornerFamily_twistRaise (h : TwistFamily E U D T v w) (hc : CornerFamily q' qi E U D T)
    (c : K) : CornerFamily q' qi E (twistRaise c v U) D T where
  e_mul_e := hc.e_mul_e
  e_mul_T := hc.e_mul_T
  T_mul_e := hc.T_mul_e
  T_mul_Tinv := hc.T_mul_Tinv
  e_mul_comm n := by
    rw [h.commOf_twistRaise c n, mul_smul_comm, ← mul_assoc, h.e_mul_v (n + 1)]
  comm_mul_e n := by
    rw [h.commOf_twistRaise c n, smul_mul_assoc, mul_assoc, hc.comm_mul_e n]

/-- **The twisted first corner element is `c·v_k` times the old one**: `y_1 ↦ c·v_ky_1`.

The whole content is `HJO.Dyck.cornerOf_one_eq_comm`, which puts the commutator at the *left* of
`y_1`; `HJO.Dyck.TwistFamily.commOf_twistRaise` has just put `c·v_k` immediately to the left of the
commutator, so the two line up and nothing has to be commuted past a loop. This is
`HJO.Sweep.IsReplicationData.map_yElt_one` read inside the algebra, and — as recorded there — it is
the *only* corner element with a formula this simple. -/
theorem cornerOf_one_twistRaise (h : TwistFamily E U D T v w) (hc : CornerFamily q' qi E U D T)
    (c : K) {k : ℕ} (hk : 1 ≤ k) :
    cornerOf q' qi di E (twistRaise c v U) D T k 1
      = c • (v k * cornerOf q' qi di E U D T k 1) := by
  rw [cornerOf_one_eq_comm (di := di) (h.cornerFamily_twistRaise hc c) hk,
    cornerOf_one_eq_comm (di := di) hc hk, h.commOf_twistRaise c (k - 1), smul_mul_assoc,
    smul_comm, mul_smul_comm]
  congr 2
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
  simp only [Nat.add_sub_cancel, mul_assoc]

end TwistFamily

end HJO.Dyck
