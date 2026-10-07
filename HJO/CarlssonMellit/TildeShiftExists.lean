/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.CarlssonMellit.BiGraded
public import HJO.CarlssonMellit.CornerTwist
public import HJO.CarlssonMellit.CornerCommute
public import HJO.CarlssonMellit.CornerPairs
public import HJO.CarlssonMellit.CornerTransport
public import HJO.CarlssonMellit.DpaMellitWords
public import HJO.CarlssonMellit.KernelStarStep
public import HJO.CarlssonMellit.StarCornerMoves
public meta import HJO.Attr

/-! # The index shift exists as an endomorphism of `Ã`

Mellit's two operators on `Ã` — the conjugator, sending `d₊` to a multiple of `z_1d₊`, and the index
shift, sending `d₊^*` to `-y_1d₊^*` — are carried as *hypotheses* at
`HJO.Dyck.Tilde.Atilde.map_biGrade_le_conj`, at `HJO.Dyck.Tilde.Atilde.map_biGrade_le_shift`, and at
`HJO.Dyck.Tilde.Atilde.biGrading`, which is therefore stated conditionally. They are not supplied by
the two replication lemmas `HJO.Sweep.exists_isDpaAction_replication` and
`HJO.Sweep.exists_isDpaAction_replication_star`, which produce an *action* on `V_*`, not an
endomorphism of `Ã`. This file constructs the index shift, and `HJO.CarlssonMellit.TildeConjExists`
the conjugator.

## Main definitions

* `HJO.Dyck.Tilde.Atilde.shiftRaise`: the raising family `c·y_1d₊^*` the shift puts in place of
  `d₊^*`.
* `HJO.Dyck.Tilde.Atilde.zShift`: the starred corner elements read in that family — what the shift
  does to `z_i`.
* `HJO.Dyck.Tilde.Atilde.starTwist`: **the index shift**, an algebra endomorphism of `Ã` fixing
  every idempotent, every loop, `d₋` and `d₊`, and sending `d₊^*` at the vertex `k` to
  `c·y_1^{(k+1)}d₊^*`. It is named for what it does rather than "index shift", because the index
  shift is the predicate `HJO.Sym.IsIndexShift` on `DopAlgebra q u` and not an
  endomorphism of `Ã` — the distinction `HJO.Dyck.Tilde.Atilde.biGrading` is careful about — and
  `HJO.Sym.indexShift` already has the other name. The parallel is with
  `HJO.Dyck.Tilde.Atilde.signTwist`, built the same way out of the same presentation.

## Main results

* `HJO.Dyck.Tilde.Atilde.twistFamily_star`: the loop variables `y_1, y_2` satisfy the six identities
  of `HJO.Dyck.TwistFamily` at the starred family. Every one of them is already proved: the raising
  clause is the second mixed relation of `HJO.Dyck.Tilde.Atilde` at `i = 1`, the two lowering
  clauses are `HJO.Dyck.Aq.yElt_mul_dMinus`, and the two loop clauses are
  `HJO.Dyck.Aq.yElt_mul_Tg_comm` and `HJO.Dyck.Aq.Tg_mul_yElt_pair`.
* `HJO.Dyck.Tilde.Atilde.zShift_mul_dPlus`: **the first mixed relation survives the shift.** This is
  the one clause with real content, and it is proved by induction on the index from the *bottom*,
  not from a closed form — see the implementation notes.
* `HJO.Dyck.Tilde.Atilde.starTwist_dPlusStar` and its four companions: the shift's values on the
  generators, which is what discharges the hypotheses of `map_biGrade_le_shift` and of `biGrading`.

## Implementation notes

**Why the scalar is free.** The index shift sends `d₊^*` to `-y_1d₊^*`. Nothing in the
construction reads the value `-1`: every relation it discharges is homogeneous in the scalar, in the
sense made precise by `HJO.Dyck.TwistFamily.eq_of_sourceRel_twistRaise`. So the shift is built for
an arbitrary `c : K`, and the operator is the instance `c = -1`, which needs no
invertibility of anything. In particular `u` is not assumed invertible anywhere here.

**Why the first mixed relation needs an induction and not a formula.** The shift moves `z_i`, and
`HJO.Dyck.TwistFamily.cornerOf_one_twistRaise` computes the image of `z_1` — it is `c·y_1z_1`. For
`i ≥ 2` the image is *not* `c·y_1z_i`: the word of polynomial inverses standing to the left of the
commutator in `z_i` ends in `T̂_1`, with which `y_1` does not commute. The same correction is
recorded at `HJO.Sweep.IsReplicationData.map_yElt_succ`, for the proof of
`HJO.Sweep.isIntertwinedPair_replication_pairs`, where the closed form fails in the same way. What
replaces it here is `HJO.Dyck.CornerFamily.cornerOf_recursion_up`: the image of `z_{i+1}` is the
image of `z_i` conjugated by a loop, and conjugating the identity for `z_i` by that loop is exactly
what the relation `d₊T_i = T_{i+1}d₊` of `HJO.Dyck.Aq` does to `d₊`. So the induction runs upwards
from `i = 1`, whose base case is the closed form, and every step is a forward computation needing no
cancellation.

## References

E. Carlsson and A. Mellit, *A proof of the shuffle conjecture*,
J. Amer. Math. Soc. **31** (2018) 661--697, Sections 3.7 and 5. -/

@[expose] public section

namespace HJO.Dyck.Tilde.Atilde

variable {K : Type*} [CommRing K] {q u : K} [Invertible q] [Invertible (q - 1)]

/-! ### Three readings in `Ã` of proved facts about `𝔸_q`

`HJO.Dyck.toTilde` carries the unstarred generators of `𝔸_q` to those of `Ã` and the corner
elements to the corner elements, so each of these is the corresponding lemma about `𝔸_q` read along
it. -/

/-- **The corner elements of `Ã` commute**, `HJO.Dyck.Aq.yElt_comm` read along
`HJO.Dyck.toTilde`. -/
theorem yElt_comm {k i j : ℕ} (hi1 : 1 ≤ i) (hik : i ≤ k) (hj1 : 1 ≤ j) (hjk : j ≤ k) :
    yElt K q u k i * yElt K q u k j = yElt K q u k j * yElt K q u k i := by
  have h := congrArg (HJO.Dyck.toTilde K q u) (Aq.yElt_comm (K := K) (q := q) hi1 hik hj1 hjk)
  simpa using h

/-- **A loop of `Ã` commutes with the product of the two corner elements it moves**,
`HJO.Dyck.Aq.Tg_mul_yElt_pair` read along `HJO.Dyck.toTilde`. -/
theorem Tg_mul_yElt_pair {k j : ℕ} (h1 : 1 ≤ j) (hjk : j < k) :
    Tg K q u k (j - 1) * (yElt K q u k j * yElt K q u k (j + 1))
      = yElt K q u k j * yElt K q u k (j + 1) * Tg K q u k (j - 1) := by
  have h := congrArg (HJO.Dyck.toTilde K q u) (Aq.Tg_mul_yElt_pair (K := K) (q := q) h1 hjk)
  simpa using h

/-- **The unstarred raising arrow of `Ã` moves the first corner element up to a conjugate**,
`HJO.Dyck.Aq.dPlus_mul_yElt_one` read along `HJO.Dyck.toTilde`. -/
theorem dPlus_mul_yElt_one {k : ℕ} (hk : 1 ≤ k) :
    dPlus K q u k * yElt K q u k 1
      = Tg K q u (k + 1) 0 * yElt K q u (k + 1) 1 * Tinv K q u (k + 1) 0 * dPlus K q u k := by
  have h := congrArg (HJO.Dyck.toTilde K q u) (Aq.dPlus_mul_yElt_one (K := K) (q := q) hk)
  simpa using h

/-! ### The loop variables twist the starred raising arrow -/

/-- Commuting with a loop is commuting with its polynomial inverse, for anything the idempotent at
that vertex absorbs on both sides. The inverse is a `K`-combination of the loop and the idempotent,
so there is nothing else to check. -/
theorem mul_Tinv_comm_of_mul_Tg_comm {x : Atilde K q u} {k i : ℕ} (he : e K q u k * x = x)
    (he' : x * e K q u k = x) (h : x * Tg K q u k i = Tg K q u k i * x) :
    x * Tinv K q u k i = Tinv K q u k i * x := by
  rw [Tinv, tinvOf, mul_smul_comm, smul_mul_assoc, mul_add, add_mul, mul_smul_comm,
    smul_mul_assoc, h, he, he']

/-- **The loop variables `y_1, y_2` twist the starred raising arrow of `Ã`.** Every clause is a
proved fact: the raising one is the second mixed relation of `HJO.Dyck.Tilde.Atilde` at `i = 1`, the
two lowering ones are `HJO.Dyck.Aq.yElt_mul_dMinus`, and the two loop ones come from
`HJO.Dyck.Aq.yElt_mul_Tg_comm` and `HJO.Dyck.Aq.Tg_mul_yElt_pair` through
`HJO.Dyck.Tilde.Atilde.mul_Tinv_comm_of_mul_Tg_comm`. -/
theorem twistFamily_star :
    TwistFamily (e K q u) (dPlusStar K q u) (dMinus K q u) (Tinv K q u)
      (fun k => yElt K q u k 1) (fun k => yElt K q u k 2) where
  e_mul_v k := e_mul_yElt k 1
  raise_mul_v k hk := (mixed_y le_rfl hk).symm
  lower_mul_v m hm := (yElt_mul_dMinus le_rfl hm).symm
  lower_mul_w m hm := (yElt_mul_dMinus (by omega) hm).symm
  v_mul_loop k s hs1 hsk :=
    mul_Tinv_comm_of_mul_Tg_comm (e_mul_yElt k 1) (yElt_mul_e k 1)
      (yElt_mul_Tg_comm le_rfl (by omega) hsk (Or.inr hs1))
  vw_mul_loop k hk :=
    mul_Tinv_comm_of_mul_Tg_comm
      (by rw [← mul_assoc, e_mul_yElt]) (by rw [mul_assoc, yElt_mul_e])
      (Tg_mul_yElt_pair (j := 1) le_rfl (by omega)).symm

/-! ### The shifted starred corner elements -/

/-- **The raising family the index shift puts in place of `d₊^*`**: `c·y_1^{(k+1)}d₊^*`. -/
noncomputable def shiftRaise (K : Type*) [CommRing K] (q u : K) [Invertible q] [Invertible (q - 1)]
    (c : K) (k : ℕ) : Atilde K q u := c • (yElt K q u (k + 1) 1 * dPlusStar K q u k)

theorem shiftRaise_eq (c : K) :
    shiftRaise K q u c = twistRaise c (fun j => yElt K q u j 1) (dPlusStar K q u) := rfl

/-- **The starred corner elements read in the shifted family**: what the index shift does to `z_i`.
-/
noncomputable def zShift (K : Type*) [CommRing K] (q u : K) [Invertible q] [Invertible (q - 1)]
    (c : K) (k i : ℕ) : Atilde K q u :=
  cornerOf (⅟q) q (-(q * ⅟(q - 1))) (e K q u) (shiftRaise K q u c) (dMinus K q u) (Tinv K q u) k i

/-- The shifted family is again a corner family, so the whole generic calculus applies to `zShift`.
-/
theorem cornerFamily_shiftRaise (c : K) :
    CornerFamily (⅟q) q (e K q u) (shiftRaise K q u c) (dMinus K q u) (Tinv K q u) := by
  rw [shiftRaise_eq]
  exact twistFamily_star.cornerFamily_twistRaise starFamily c

/-- **The image of the lowest starred corner element is `c·y_1z_1`**: the one corner element for
which the closed form holds, by `HJO.Dyck.TwistFamily.cornerOf_one_twistRaise`. -/
theorem zShift_one (c : K) {k : ℕ} (hk : 1 ≤ k) :
    zShift K q u c k 1 = c • (yElt K q u k 1 * zElt K q u k 1) := by
  rw [zShift, shiftRaise_eq]
  exact twistFamily_star.cornerOf_one_twistRaise starFamily c hk

/-- The recursion for the shifted corner elements, read upwards: `HJO.Dyck.cornerOf`'s own recursion
inverted, the polynomial inverse of `T̂_i` being `T_i` by `HJO.Dyck.Tilde.tinvOf_tinvOf`. -/
theorem zShift_recursion_up (c : K) {k i : ℕ} (h1 : 1 ≤ i) (hik : i < k) :
    zShift K q u c k (i + 1)
      = ⅟q • (Tg K q u k (i - 1) * zShift K q u c k i * Tg K q u k (i - 1)) := by
  have h := CornerFamily.cornerOf_recursion_up (di := -(q * ⅟(q - 1)))
    (cornerFamily_shiftRaise (K := K) (q := q) (u := u) c) (qi' := ⅟q) (invOf_mul_self q) h1 hik
  rwa [show tinvOf (⅟q) q (Tinv K q u k (i - 1)) (e K q u k) = Tg K q u k (i - 1) from
    tinvOf_tinvOf _ _] at h

/-! ### The first mixed relation survives the shift -/

/-- The base case of `HJO.Dyck.Tilde.Atilde.zShift_mul_dPlus`: the lowest index, where the closed
form of `HJO.Dyck.Tilde.Atilde.zShift_one` is available on both sides. -/
theorem zShift_two_mul_dPlus (c : K) {k : ℕ} (hk : 1 ≤ k) :
    zShift K q u c (k + 1) 2 * dPlus K q u k = dPlus K q u k * zShift K q u c k 1 := by
  have hmz : dPlus K q u k * zElt K q u k 1 = zElt K q u (k + 1) 2 * dPlus K q u k :=
    (mixed_z le_rfl hk).symm
  have hrec : zElt K q u (k + 1) 1
      = q • (Tinv K q u (k + 1) 0 * zElt K q u (k + 1) 2 * Tinv K q u (k + 1) 0) :=
    cornerOf_recursion (q' := ⅟q) (qi := q) (di := -(q * ⅟(q - 1))) (E := e K q u)
      (U := dPlusStar K q u) (D := dMinus K q u) (T := Tinv K q u) le_rfl (by omega)
  have hkey : Tinv K q u (k + 1) 0 * (Tg K q u (k + 1) 0 * dPlus K q u k) = dPlus K q u k := by
    rw [← mul_assoc, Tinv_mul_Tg (show 0 + 2 ≤ k + 1 by omega), e_mul_dPlus]
  rw [zShift_recursion_up c (i := 1) le_rfl (by omega), zShift_one c (k := k + 1) (by omega),
    zShift_one c hk, hrec]
  simp only [smul_mul_assoc, mul_smul_comm, smul_smul]
  rw [show ⅟q * (c * q) = c from by rw [mul_comm c q, ← mul_assoc, invOf_mul_self, one_mul]]
  congr 1
  simp only [Nat.sub_self]
  rw [← mul_assoc (dPlus K q u k) (yElt K q u k 1) (zElt K q u k 1), dPlus_mul_yElt_one hk]
  simp only [mul_assoc]
  rw [hmz, hkey]

/-- **The first mixed relation survives the shift**: `z_{i+1}d₊ = d₊z_i` holds for the shifted
corner elements too. The induction runs upwards from the lowest index; see the implementation
notes. -/
theorem zShift_mul_dPlus (c : K) {k i : ℕ} (h1 : 1 ≤ i) (hik : i ≤ k) :
    zShift K q u c (k + 1) (i + 1) * dPlus K q u k = dPlus K q u k * zShift K q u c k i := by
  induction i with
  | zero => omega
  | succ i ih =>
    rcases Nat.eq_zero_or_pos i with rfl | hi
    · exact zShift_two_mul_dPlus c hik
    · have hbraid : dPlus K q u k * Tg K q u k (i - 1) = Tg K q u (k + 1) i * dPlus K q u k := by
        have h := eq_of_sourceRel (K := K) (q := q) (u := u)
          (SourceRel.up_braid (E := e K q u) (U := dPlus K q u) (D := dMinus K q u)
            (T := Tg K q u) (k := k) (i := i - 1) (by omega))
        rwa [show i - 1 + 1 = i from by omega] at h
      rw [zShift_recursion_up (K := K) (q := q) (u := u) c (k := k + 1) (i := i + 1) (by omega)
          (by omega),
        zShift_recursion_up (K := K) (q := q) (u := u) c (k := k) (i := i) hi (by omega),
        smul_mul_assoc, mul_smul_comm]
      congr 1
      simp only [Nat.add_sub_cancel]
      calc Tg K q u (k + 1) i * zShift K q u c (k + 1) (i + 1) * Tg K q u (k + 1) i *
              dPlus K q u k
          = Tg K q u (k + 1) i * zShift K q u c (k + 1) (i + 1) *
              (Tg K q u (k + 1) i * dPlus K q u k) := by simp only [mul_assoc]
        _ = Tg K q u (k + 1) i * (zShift K q u c (k + 1) (i + 1) * dPlus K q u k) *
              Tg K q u k (i - 1) := by rw [← hbraid]; simp only [mul_assoc]
        _ = Tg K q u (k + 1) i * (dPlus K q u k * zShift K q u c k i) * Tg K q u k (i - 1) := by
              rw [ih hi (by omega)]
        _ = Tg K q u (k + 1) i * dPlus K q u k * (zShift K q u c k i * Tg K q u k (i - 1)) := by
              simp only [mul_assoc]
        _ = dPlus K q u k * Tg K q u k (i - 1) * (zShift K q u c k i * Tg K q u k (i - 1)) := by
              rw [← hbraid]
        _ = dPlus K q u k * (Tg K q u k (i - 1) * zShift K q u c k i * Tg K q u k (i - 1)) := by
              simp only [mul_assoc]

/-! ### The index shift -/

/-- The value the index shift takes at each generator of the enlarged quiver: everything is fixed
but the starred raising arrow, which goes to `c·y_1d₊^*`. -/
noncomputable def shiftGen (K : Type*) [CommRing K] (q u : K) [Invertible q] [Invertible (q - 1)]
    (c : K) : Gen → Atilde K q u
  | .vertex k => e K q u k
  | .up k => dPlus K q u k
  | .upStar k => shiftRaise K q u c k
  | .down k => dMinus K q u k
  | .braid k i => Tg K q u k i

/-- The free-algebra lift of the index shift. -/
noncomputable def shiftHom (K : Type*) [CommRing K] (q u : K) [Invertible q] [Invertible (q - 1)]
    (c : K) : FreeAlgebra K Gen →ₐ[K] Atilde K q u :=
  FreeAlgebra.lift K (shiftGen K q u c)

@[simp] theorem shiftHom_freeE (c : K) (k : ℕ) : shiftHom K q u c (freeE K k) = e K q u k :=
  FreeAlgebra.lift_ι_apply _ _

@[simp] theorem shiftHom_freeUp (c : K) (k : ℕ) :
    shiftHom K q u c (freeUp K k) = dPlus K q u k := FreeAlgebra.lift_ι_apply _ _

@[simp] theorem shiftHom_freeUpStar (c : K) (k : ℕ) :
    shiftHom K q u c (freeUpStar K k) = shiftRaise K q u c k := FreeAlgebra.lift_ι_apply _ _

@[simp] theorem shiftHom_freeDown (c : K) (k : ℕ) :
    shiftHom K q u c (freeDown K k) = dMinus K q u k := FreeAlgebra.lift_ι_apply _ _

@[simp] theorem shiftHom_freeT (c : K) (k i : ℕ) :
    shiftHom K q u c (freeT K k i) = Tg K q u k i := FreeAlgebra.lift_ι_apply _ _

@[simp] theorem shiftHom_freeTinv (c : K) (k i : ℕ) :
    shiftHom K q u c (freeTinv K q k i) = Tinv K q u k i :=
  map_tinvOf _ q ⅟q (shiftHom_freeT c k i) (shiftHom_freeE c k)

/-- The unstarred corner elements are fixed: the index shift moves no generator they are built from.
-/
@[simp] theorem shiftHom_freeY (c : K) (k i : ℕ) :
    shiftHom K q u c (freeY K q k i) = yElt K q u k i :=
  map_cornerOf _ q ⅟q ⅟(q - 1) (shiftHom_freeE c) (shiftHom_freeUp c) (shiftHom_freeDown c)
    (shiftHom_freeT c) k i

/-- The starred corner elements go to the shifted ones. -/
@[simp] theorem shiftHom_freeZ (c : K) (k i : ℕ) :
    shiftHom K q u c (freeZ K q k i) = zShift K q u c k i :=
  map_cornerOf _ (⅟q) q (-(q * ⅟(q - 1))) (shiftHom_freeE c) (shiftHom_freeUpStar c)
    (shiftHom_freeDown c) (shiftHom_freeTinv c) k i

/-- **The index shift kills every relation of `Ã`.** The quiver relations and the unstarred group
are untouched, the starred group is `HJO.Dyck.TwistFamily.eq_of_sourceRel_twistRaise` at
`HJO.Dyck.Tilde.Atilde.twistFamily_star`, the second mixed relation needs only that the corner
elements commute, the third is the closed form of `HJO.Dyck.Tilde.Atilde.zShift_one`, and the first
is `HJO.Dyck.Tilde.Atilde.zShift_mul_dPlus`. -/
theorem shiftHom_rel (c : K) {x y : FreeAlgebra K Gen} (h : Rel K q u x y) :
    shiftHom K q u c x = shiftHom K q u c y := by
  induction h with
  | vertex_mul_self k => simp
  | vertex_mul_vertex h => simp [e_mul_e_of_ne h]
  | vertex_mul_down k => simp
  | down_mul_vertex k => simp
  | vertex_mul_braid k i => simp
  | braid_mul_vertex k i => simp
  | braid_eq_zero h => simp [Tg_eq_zero h]
  | source h =>
    refine eq_of_sourceRel ?_
    exact SourceRel.mapBar (bar := RingEquiv.refl K) (f := (shiftHom K q u c).toAddMonoidHom)
      (E' := e K q u) (U' := dPlus K q u) (D' := dMinus K q u) (T' := Tg K q u)
      (fun x y => map_mul (shiftHom K q u c) x y)
      (fun a x => show shiftHom K q u c (a • x) = a • shiftHom K q u c x from map_smul _ a x)
      (fun n => shiftHom_freeE c n) (fun n => shiftHom_freeUp c n)
      (fun n => shiftHom_freeDown c n) (fun n i _ => shiftHom_freeT c n i) h
  | sourceStar h =>
    refine twistFamily_star.eq_of_sourceRel_twistRaise (fun hr => eq_of_sourceRelStar hr) c ?_
    rw [← shiftRaise_eq]
    exact SourceRel.mapBar (bar := RingEquiv.refl K) (f := (shiftHom K q u c).toAddMonoidHom)
      (E' := e K q u) (U' := shiftRaise K q u c) (D' := dMinus K q u) (T' := Tinv K q u)
      (fun x y => map_mul (shiftHom K q u c) x y)
      (fun a x => show shiftHom K q u c (a • x) = a • shiftHom K q u c x from map_smul _ a x)
      (fun n => shiftHom_freeE c n) (fun n => shiftHom_freeUpStar c n)
      (fun n => shiftHom_freeDown c n) (fun n i _ => shiftHom_freeTinv c n i) h
  | @mixed_z k i h1 h2 =>
    simp only [map_mul, shiftHom_freeZ, shiftHom_freeUp]
    exact zShift_mul_dPlus c h1 h2
  | @mixed_y k i h1 h2 =>
    simp only [map_mul, shiftHom_freeY, shiftHom_freeUpStar, shiftRaise]
    rw [mul_smul_comm, smul_mul_assoc, mul_assoc (yElt K q u (k + 1) 1), ← mixed_y h1 h2,
      ← mul_assoc, ← mul_assoc,
      yElt_comm (K := K) (q := q) (u := u) (k := k + 1) (i := i + 1) (j := 1) (by omega)
        (by omega) le_rfl (by omega)]
  | mixed_top k =>
    have hL : zShift K q u c (k + 1) 1 * dPlus K q u k
        = -((c * (u * q ^ (k + 1))) • (yElt K q u (k + 1) 1 *
            (yElt K q u (k + 1) 1 * dPlusStar K q u k))) := by
      rw [zShift_one c (show 1 ≤ k + 1 by omega), smul_mul_assoc, mul_assoc, zElt_one_mul_dPlus,
        mul_neg, mul_smul_comm, smul_neg, smul_smul]
    have hR : (-(u * q ^ (k + 1)) : K) • (yElt K q u (k + 1) 1 * shiftRaise K q u c k)
        = -((c * (u * q ^ (k + 1))) • (yElt K q u (k + 1) 1 *
            (yElt K q u (k + 1) 1 * dPlusStar K q u k))) := by
      rw [shiftRaise, mul_smul_comm, smul_smul,
        show -(u * q ^ (k + 1)) * c = -(c * (u * q ^ (k + 1))) from by ring,
        neg_smul (c * (u * q ^ (k + 1)))]
    simp only [map_mul, map_smul, shiftHom_freeZ, shiftHom_freeY, shiftHom_freeUp,
      shiftHom_freeUpStar]
    rw [hL, hR]

/-- **Mellit's index shift, as an algebra endomorphism of `Ã`** — the `Φ_s` of
`HJO.Dyck.Tilde.Atilde.biGrading`. It fixes every idempotent, every loop, `d₋` and `d₊`, and sends
`d₊^*` at the vertex `k` to `c·y_1^{(k+1)}d₊^*`. The operator is the instance `c = -1`;
the scalar is left free because nothing in the construction reads it, and in particular no
invertibility of `u` is needed anywhere.

Not called `indexShift`: the index shift is the predicate `HJO.Sym.IsIndexShift` on
`DopAlgebra`, and the two are not the same object — see the module docstring and the implementation
notes of `HJO.Dyck.Tilde.Atilde.biGrading`. -/
@[hjo "lem_mellit_ns_shift_exists"]
noncomputable def starTwist (K : Type*) [CommRing K] (q u : K) [Invertible q] [Invertible (q - 1)]
    (c : K) : Atilde K q u →ₐ[K] Atilde K q u :=
  RingQuot.liftAlgHom K ⟨shiftHom K q u c, fun _ _ h => shiftHom_rel c h⟩

@[simp] theorem starTwist_mk (c : K) (x : FreeAlgebra K Gen) :
    starTwist K q u c (mk K q u x) = shiftHom K q u c x :=
  RingQuot.liftAlgHom_mkAlgHom_apply K (shiftHom K q u c) (s := Rel K q u)
    (fun _ _ h => shiftHom_rel c h) x

@[simp] theorem starTwist_e (c : K) (k : ℕ) : starTwist K q u c (e K q u k) = e K q u k := by
  simpa using starTwist_mk c (freeE K k)

@[simp] theorem starTwist_Tg (c : K) (k i : ℕ) :
    starTwist K q u c (Tg K q u k i) = Tg K q u k i := by
  simpa using starTwist_mk c (freeT K k i)

@[simp] theorem starTwist_dMinus (c : K) (k : ℕ) :
    starTwist K q u c (dMinus K q u k) = dMinus K q u k := by
  simpa using starTwist_mk c (freeDown K k)

@[simp] theorem starTwist_dPlus (c : K) (k : ℕ) :
    starTwist K q u c (dPlus K q u k) = dPlus K q u k := by
  simpa using starTwist_mk c (freeUp K k)

/-- **The index shift at the starred raising arrow**: the clause the bigrading lemma reads. -/
@[simp] theorem starTwist_dPlusStar (c : K) (k : ℕ) :
    starTwist K q u c (dPlusStar K q u k)
      = c • (yElt K q u (k + 1) 1 * dPlusStar K q u k) := by
  simpa [shiftRaise] using starTwist_mk c (freeUpStar K k)

/-- The index shift at the scalar `-1` of the operator, which is the shape
`HJO.Dyck.Tilde.Atilde.map_biGrade_le_shift` and `HJO.Dyck.Tilde.Atilde.biGrading` ask for. -/
theorem starTwist_neg_one_dPlusStar (k : ℕ) :
    starTwist K q u (-1) (dPlusStar K q u k)
      = -(yElt K q u (k + 1) 1 * dPlusStar K q u k) := by
  rw [starTwist_dPlusStar, neg_one_smul]

/-! ### What the construction discharges

`HJO.Dyck.Tilde.Atilde.map_biGrade_le_shift` and the second, third and fourth clauses of
`HJO.Dyck.Tilde.Atilde.biGrading` are stated for a *hypothetical* endomorphism of `Ã`. These are the
instances at the one that exists, so those clauses hold unconditionally. The first and third
clauses read the other homomorphism, the conjugator, which this file does not build; it is built in
`HJO.CarlssonMellit.TildeConjExists`. -/

/-- **The index shift carries `Ã_{m,n}` into `Ã_{m,m+n}`**, unconditionally: the hypotheses of
`HJO.Dyck.Tilde.Atilde.map_biGrade_le_shift` discharged at
`HJO.Dyck.Tilde.Atilde.starTwist`. -/
theorem map_biGrade_le_shift_starTwist (m n : ℕ) :
    (biGrade K q u (m, n)).map (starTwist K q u (-1 : K)).toLinearMap
      ≤ biGrade K q u (m, m + n) :=
  map_biGrade_le_shift (starTwist K q u (-1 : K)) (starTwist_e (-1 : K))
    (starTwist_Tg (-1 : K)) (starTwist_dMinus (-1 : K)) (starTwist_dPlus (-1 : K))
    starTwist_neg_one_dPlusStar m n

/-- **The sign clause of the bigrading lemma for the index shift**, unconditionally: conjugating the
index shift by multiplication by `(-1)^{m+n}` rescales it by `(-1)^m` on `Ã_{m,n}`. This is the
fourth clause of `HJO.Dyck.Tilde.Atilde.biGrading` with its hypotheses discharged. -/
theorem signTwist_starTwist_signTwist {m n : ℕ} {x : Atilde K q u} (hx : x ∈ biGrade K q u (m, n)) :
    signTwist K q u (starTwist K q u (-1 : K) (signTwist K q u x))
      = (-1 : K) ^ m • starTwist K q u (-1 : K) x := by
  have hΦ : starTwist K q u (-1 : K) x ∈ biGrade K q u (m, m + n) :=
    map_biGrade_le_shift_starTwist m n ⟨x, hx, rfl⟩
  rw [signTwist_of_mem_biGrade hx, map_smul, map_smul, signTwist_of_mem_biGrade hΦ, smul_smul,
    biSign_mul_biSign_shift]

end HJO.Dyck.Tilde.Atilde
