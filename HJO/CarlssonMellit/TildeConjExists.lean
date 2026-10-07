/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.CarlssonMellit.StarFlipExists
public import HJO.CarlssonMellit.TildeShiftExists
public meta import HJO.Attr

/-! # The conjugator exists as an endomorphism of `Ã`

`HJO.CarlssonMellit.TildeShiftExists` builds the second of Mellit's two endomorphisms of `Ã`,
the one twisting the starred raising arrow. This file builds the first: the *conjugator*, sending
`d₊` at the vertex `k` to `c·z_1^{(k+1)}d₊` and fixing every idempotent, every loop, `d₋` and
`d₊^*`. It is the shape `HJO.Dyck.Tilde.Atilde.map_biGrade_le_conj` and the first and third
clauses of `HJO.Dyck.Tilde.Atilde.biGrading` carry as a hypothesis, and the one
`HJO.Sweep.conj_intertwines` cannot even be stated without.

## Main definitions

* `HJO.Dyck.Tilde.Atilde.conjRaise`: the raising family `c·z_1d₊` the conjugator puts in place of
  `d₊`.
* `HJO.Dyck.Tilde.Atilde.yTwist`: the unstarred corner elements read in that family — what the
  conjugator does to `y_i`.
* `HJO.Dyck.Tilde.Atilde.conjTwist`: **the conjugator**, an algebra endomorphism of `Ã`.

## Main results

* `HJO.Dyck.Tilde.Atilde.zElt_comm`, `HJO.Dyck.Tilde.Atilde.Tinv_mul_zElt_pair`,
  `HJO.Dyck.Tilde.Atilde.dPlusStar_mul_zElt_one`: the three starred facts the construction needs
  that `HJO.CarlssonMellit.StarCornerMoves` did not already have, each the image under a star
  swap of its proved unstarred twin.
* `HJO.Dyck.Tilde.Atilde.twistFamily_unstarred`: the loop variables `z_1, z_2` satisfy the six
  identities of `HJO.Dyck.TwistFamily` at the *unstarred* family.
* `HJO.Dyck.Tilde.Atilde.yTwist_mul_dPlusStar`: the second mixed relation survives the conjugator.
* `HJO.Dyck.Tilde.Atilde.exists_conjTwist`: **the conjugator exists**, stated in exactly the shape
  `map_biGrade_le_conj` and `biGrading` consume.
* `HJO.Dyck.Tilde.Atilde.exists_conjTwist_of_bar`: the same with the star swap discharged, so the
  only hypotheses left are the ones `HJO.Sym.paramInvLambda` names.

## Implementation notes

**Why this half needs the bar and the other did not.** The index shift twists the *starred* arrow by
`y_1`, and every fact about `y_1` it reads is proved outright: the corner elements of `Ã` commute,
`y_1` passes a lowering arrow and the loops above the first, and `d₊` carries `y_1` to a conjugate.
The conjugator twists the *unstarred* arrow by `z_1`, and the starred twins of those facts are not
proved directly anywhere — they are obtained by applying a star swap, which is what
`HJO.CarlssonMellit.StarCornerMoves` already does for `z_1` past a lowering arrow and past an
inverse loop. So the construction carries `HJO.Dyck.IsStarSwap` and `bar q = q⁻¹` exactly as those
lemmas do. `HJO.Dyck.Tilde.Atilde.exists_conjTwist_of_bar` discharges the swap itself through
`HJO.Dyck.Tilde.Atilde.exists_isStarSwap`, leaving the three hypotheses of `HJO.Sym.paramInvLambda`
and `[Invertible u]`.

This is not a weakening hidden in a signature: `u` is inverted by the bar and `[Invertible u]` is
needed for the star swap to exist at all, because the third mixed relation is sent to
`u^{-1}q^{-(k+1)}` times itself. The scalar `c` at `d₊` is still free — no relation the construction
discharges reads its value — so the value `-(qu)^{-1}` is an instance and not a requirement.

**The mirror.** Everything past the three starred facts is the mirror of
`HJO.CarlssonMellit.TildeShiftExists` under `q ↦ q^{-1}`, `d₊ ↔ d₊^*`, `T_i ↔ T̂_i`,
`y_i ↔ z_i`: `HJO.Dyck.TwistFamily.cornerOf_one_twistRaise` gives the image of `y_1` and
`HJO.Dyck.CornerFamily.cornerOf_recursion_up` carries it up the index, the closed form being false
for `i ≥ 2` for the reason recorded there.

## References

E. Carlsson and A. Mellit, *A proof of the shuffle conjecture*, J. Amer. Math. Soc. **31** (2018)
661--697, Sections 3.7 and 5. -/

@[expose] public section

namespace HJO.Dyck.Tilde.Atilde

variable {K : Type*} [CommRing K] {q u : K} [Invertible q] [Invertible (q - 1)]

/-! ### A loop in terms of its polynomial inverse

`HJO.Dyck.Tilde.Atilde.Tinv` is a `K`-combination of the loop and the idempotent, and the
combination is invertible over `K`, so commuting with one is commuting with the other. The starred
facts of `HJO.CarlssonMellit.StarCornerMoves` are stated at `T̂_i` and the relations of the
unstarred group read `T_i`, so this conversion is needed in that direction. -/

theorem Tg_eq_smul_Tinv_sub (k i : ℕ) :
    Tg K q u k i = q • Tinv K q u k i - (q - 1) • e K q u k := by
  rw [Tinv, tinvOf, smul_smul, mul_invOf_self, one_smul, add_sub_cancel_right]

/-- Commuting with the polynomial inverse of a loop is commuting with the loop, for anything the
idempotent at that vertex absorbs on both sides. -/
theorem mul_Tg_comm_of_mul_Tinv_comm {x : Atilde K q u} {k i : ℕ} (he : e K q u k * x = x)
    (he' : x * e K q u k = x) (hi : x * Tinv K q u k i = Tinv K q u k i * x) :
    x * Tg K q u k i = Tg K q u k i * x := by
  rw [Tg_eq_smul_Tinv_sub, mul_sub, sub_mul, mul_smul_comm, mul_smul_comm, smul_mul_assoc,
    smul_mul_assoc, hi, he, he']

/-! ### The three starred facts the conjugator needs

Each is the image under a star swap of a proved unstarred fact, in the idiom of
`HJO.CarlssonMellit.StarCornerMoves`: apply `σ`, and rewrite its values on the generators and
on the corner elements. -/

section StarSwap

variable {bar : K ≃+* K} {σ : Atilde K q u →+ Atilde K q u}
  (h : IsStarSwap q bar (e K q u) (dPlus K q u) (dPlusStar K q u) (dMinus K q u) (Tg K q u) σ)
  (hbar : bar q = ⅟q)

include h hbar

/-- **The starred corner elements commute**, the image of `HJO.Dyck.Aq.yElt_comm`. -/
theorem zElt_comm {k i j : ℕ} (hi1 : 1 ≤ i) (hik : i ≤ k) (hj1 : 1 ≤ j) (hjk : j ≤ k) :
    zElt K q u k i * zElt K q u k j = zElt K q u k j * zElt K q u k i := by
  have hy := congrArg σ (yElt_comm (K := K) (q := q) (u := u) hi1 hik hj1 hjk)
  rw [h.map_mul, h.map_mul, map_yElt h hbar hi1 hik, map_yElt h hbar hj1 hjk] at hy
  exact hy

/-- **An inverse loop commutes with the product of the two starred corner elements it moves**, the
image of `HJO.Dyck.Aq.Tg_mul_yElt_pair`. -/
theorem Tinv_mul_zElt_pair {k j : ℕ} (h1 : 1 ≤ j) (hjk : j < k) :
    Tinv K q u k (j - 1) * (zElt K q u k j * zElt K q u k (j + 1))
      = zElt K q u k j * zElt K q u k (j + 1) * Tinv K q u k (j - 1) := by
  have hy := congrArg σ (Tg_mul_yElt_pair (K := K) (q := q) (u := u) h1 hjk)
  simp only [h.map_mul, h.map_T (show j - 1 + 2 ≤ k by omega),
    map_yElt h hbar h1 (show j ≤ k by omega),
    map_yElt h hbar (show 1 ≤ j + 1 by omega) (show j + 1 ≤ k by omega)] at hy
  exact hy

/-- **The starred raising arrow moves the first starred corner element up to a conjugate**, the
image of `HJO.Dyck.Aq.dPlus_mul_yElt_one`. -/
theorem dPlusStar_mul_zElt_one {k : ℕ} (hk : 1 ≤ k) :
    dPlusStar K q u k * zElt K q u k 1
      = Tinv K q u (k + 1) 0 * zElt K q u (k + 1) 1 * Tg K q u (k + 1) 0 *
        dPlusStar K q u k := by
  have hy := congrArg σ (dPlus_mul_yElt_one (K := K) (q := q) (u := u) hk)
  simp only [h.map_mul, h.map_dPlus, h.map_T (show 0 + 2 ≤ k + 1 by omega),
    map_Tinv h (show 0 + 2 ≤ k + 1 by omega), map_yElt h hbar le_rfl (show 1 ≤ k by omega),
    map_yElt h hbar le_rfl (show 1 ≤ k + 1 by omega)] at hy
  exact hy

/-- The starred corner element commutes with every loop that does not touch it: the loop form of
`HJO.Dyck.Tilde.Atilde.zElt_mul_Tinv_comm`, which is what the unstarred relations read. -/
theorem zElt_mul_Tg_comm {k i s : ℕ} (h1 : 1 ≤ i) (hik : i ≤ k) (hs : s + 2 ≤ k)
    (hadm : s + 3 ≤ i ∨ i ≤ s) :
    zElt K q u k i * Tg K q u k s = Tg K q u k s * zElt K q u k i :=
  mul_Tg_comm_of_mul_Tinv_comm (e_mul_zElt k i) (zElt_mul_e k i)
    (zElt_mul_Tinv_comm h hbar h1 hik hs hadm)

/-- **The loop variables `z_1, z_2` twist the unstarred raising arrow of `Ã`.** The raising clause
is the first mixed relation of `HJO.Dyck.Tilde.Atilde` at `i = 1` and needs nothing; the other five
are the starred facts above and in `HJO.CarlssonMellit.StarCornerMoves`. -/
theorem twistFamily_unstarred :
    TwistFamily (e K q u) (dPlus K q u) (dMinus K q u) (Tg K q u)
      (fun k => zElt K q u k 1) (fun k => zElt K q u k 2) where
  e_mul_v k := e_mul_zElt k 1
  raise_mul_v k hk := (mixed_z le_rfl hk).symm
  lower_mul_v m hm := (zElt_mul_dMinus h hbar le_rfl hm).symm
  lower_mul_w m hm := (zElt_mul_dMinus h hbar (by omega) hm).symm
  v_mul_loop k s hs1 hsk := zElt_mul_Tg_comm h hbar le_rfl (by omega) hsk (Or.inr hs1)
  vw_mul_loop k hk :=
    mul_Tg_comm_of_mul_Tinv_comm
      (by rw [← mul_assoc, e_mul_zElt]) (by rw [mul_assoc, zElt_mul_e])
      (Tinv_mul_zElt_pair h hbar (j := 1) le_rfl (by omega)).symm

end StarSwap

/-! ### The conjugated unstarred corner elements -/

/-- **The raising family the conjugator puts in place of `d₊`**: `c·z_1^{(k+1)}d₊`. -/
noncomputable def conjRaise (K : Type*) [CommRing K] (q u : K) [Invertible q] [Invertible (q - 1)]
    (c : K) (k : ℕ) : Atilde K q u := c • (zElt K q u (k + 1) 1 * dPlus K q u k)

theorem conjRaise_eq (c : K) :
    conjRaise K q u c = twistRaise c (fun j => zElt K q u j 1) (dPlus K q u) := rfl

/-- **The unstarred corner elements read in the conjugated family**: what the conjugator does to
`y_i`. -/
noncomputable def yTwist (K : Type*) [CommRing K] (q u : K) [Invertible q] [Invertible (q - 1)]
    (c : K) (k i : ℕ) : Atilde K q u :=
  cornerOf q ⅟q ⅟(q - 1) (e K q u) (conjRaise K q u c) (dMinus K q u) (Tg K q u) k i

section StarSwap

variable {bar : K ≃+* K} {σ : Atilde K q u →+ Atilde K q u}
  (h : IsStarSwap q bar (e K q u) (dPlus K q u) (dPlusStar K q u) (dMinus K q u) (Tg K q u) σ)
  (hbar : bar q = ⅟q)

include h hbar

/-- The conjugated family is again a corner family. -/
theorem cornerFamily_conjRaise (c : K) :
    CornerFamily q ⅟q (e K q u) (conjRaise K q u c) (dMinus K q u) (Tg K q u) := by
  rw [conjRaise_eq]
  exact (twistFamily_unstarred h hbar).cornerFamily_twistRaise unstarredFamily c

/-- **The image of the lowest unstarred corner element is `c·z_1y_1`**, by
`HJO.Dyck.TwistFamily.cornerOf_one_twistRaise`. -/
theorem yTwist_one (c : K) {k : ℕ} (hk : 1 ≤ k) :
    yTwist K q u c k 1 = c • (zElt K q u k 1 * yElt K q u k 1) := by
  rw [yTwist, conjRaise_eq]
  exact (twistFamily_unstarred h hbar).cornerOf_one_twistRaise unstarredFamily c hk

/-- The recursion for the conjugated corner elements, read upwards. -/
theorem yTwist_recursion_up (c : K) {k i : ℕ} (h1 : 1 ≤ i) (hik : i < k) :
    yTwist K q u c k (i + 1)
      = q • (Tinv K q u k (i - 1) * yTwist K q u c k i * Tinv K q u k (i - 1)) :=
  CornerFamily.cornerOf_recursion_up (di := ⅟(q - 1)) (cornerFamily_conjRaise h hbar c)
    (qi' := q) (mul_invOf_self q) h1 hik

/-! ### The second mixed relation survives the conjugator -/

/-- The base case of `HJO.Dyck.Tilde.Atilde.yTwist_mul_dPlusStar`. -/
theorem yTwist_two_mul_dPlusStar (c : K) {k : ℕ} (hk : 1 ≤ k) :
    yTwist K q u c (k + 1) 2 * dPlusStar K q u k
      = dPlusStar K q u k * yTwist K q u c k 1 := by
  have hmy : dPlusStar K q u k * yElt K q u k 1
      = yElt K q u (k + 1) 2 * dPlusStar K q u k := (mixed_y le_rfl hk).symm
  have hrec : yElt K q u (k + 1) 1
      = ⅟q • (Tg K q u (k + 1) 0 * yElt K q u (k + 1) 2 * Tg K q u (k + 1) 0) :=
    cornerOf_recursion (q' := q) (qi := ⅟q) (di := ⅟(q - 1)) (E := e K q u) (U := dPlus K q u)
      (D := dMinus K q u) (T := Tg K q u) le_rfl (by omega)
  have hkey : Tg K q u (k + 1) 0 * (Tinv K q u (k + 1) 0 * dPlusStar K q u k)
      = dPlusStar K q u k := by
    rw [← mul_assoc, Tg_mul_Tinv (show 0 + 2 ≤ k + 1 by omega), e_mul_dPlusStar]
  rw [yTwist_recursion_up h hbar c (k := k + 1) (i := 1) le_rfl (by omega),
    yTwist_one h hbar c (k := k + 1) (by omega), yTwist_one h hbar c hk, hrec]
  simp only [smul_mul_assoc, mul_smul_comm, smul_smul]
  rw [show q * (c * ⅟q) = c from by rw [mul_comm c ⅟q, ← mul_assoc, mul_invOf_self, one_mul]]
  congr 1
  simp only [Nat.sub_self]
  rw [← mul_assoc (dPlusStar K q u k) (zElt K q u k 1) (yElt K q u k 1),
    dPlusStar_mul_zElt_one h hbar hk]
  simp only [mul_assoc]
  rw [hmy, hkey]

/-- **The second mixed relation survives the conjugator**: `y_{i+1}d₊^* = d₊^*y_i` holds for the
conjugated corner elements too. The mirror of `HJO.Dyck.Tilde.Atilde.zShift_mul_dPlus`. -/
theorem yTwist_mul_dPlusStar (c : K) {k i : ℕ} (h1 : 1 ≤ i) (hik : i ≤ k) :
    yTwist K q u c (k + 1) (i + 1) * dPlusStar K q u k
      = dPlusStar K q u k * yTwist K q u c k i := by
  induction i with
  | zero => omega
  | succ i ih =>
    rcases Nat.eq_zero_or_pos i with rfl | hi
    · exact yTwist_two_mul_dPlusStar h hbar c hik
    · have hbraid : dPlusStar K q u k * Tinv K q u k (i - 1)
          = Tinv K q u (k + 1) i * dPlusStar K q u k := by
        have hs := eq_of_sourceRelStar (K := K) (q := q) (u := u)
          (SourceRel.up_braid (E := e K q u) (U := dPlusStar K q u) (D := dMinus K q u)
            (T := Tinv K q u) (k := k) (i := i - 1) (by omega))
        rwa [show i - 1 + 1 = i from by omega] at hs
      rw [yTwist_recursion_up h hbar c (k := k + 1) (i := i + 1) (by omega) (by omega),
        yTwist_recursion_up h hbar c (k := k) (i := i) hi (by omega), smul_mul_assoc,
        mul_smul_comm]
      congr 1
      simp only [Nat.add_sub_cancel]
      calc Tinv K q u (k + 1) i * yTwist K q u c (k + 1) (i + 1) * Tinv K q u (k + 1) i *
              dPlusStar K q u k
          = Tinv K q u (k + 1) i * yTwist K q u c (k + 1) (i + 1) *
              (Tinv K q u (k + 1) i * dPlusStar K q u k) := by simp only [mul_assoc]
        _ = Tinv K q u (k + 1) i * (yTwist K q u c (k + 1) (i + 1) * dPlusStar K q u k) *
              Tinv K q u k (i - 1) := by rw [← hbraid]; simp only [mul_assoc]
        _ = Tinv K q u (k + 1) i * (dPlusStar K q u k * yTwist K q u c k i) *
              Tinv K q u k (i - 1) := by rw [ih hi (by omega)]
        _ = Tinv K q u (k + 1) i * dPlusStar K q u k *
              (yTwist K q u c k i * Tinv K q u k (i - 1)) := by simp only [mul_assoc]
        _ = dPlusStar K q u k * Tinv K q u k (i - 1) *
              (yTwist K q u c k i * Tinv K q u k (i - 1)) := by rw [← hbraid]
        _ = dPlusStar K q u k *
              (Tinv K q u k (i - 1) * yTwist K q u c k i * Tinv K q u k (i - 1)) := by
              simp only [mul_assoc]

/-! ### The conjugator -/

end StarSwap

/-- The value the conjugator takes at each generator of the enlarged quiver: everything is fixed but
the unstarred raising arrow, which goes to `c·z_1d₊`. -/
noncomputable def conjGen (K : Type*) [CommRing K] (q u : K) [Invertible q] [Invertible (q - 1)]
    (c : K) : Gen → Atilde K q u
  | .vertex k => e K q u k
  | .up k => conjRaise K q u c k
  | .upStar k => dPlusStar K q u k
  | .down k => dMinus K q u k
  | .braid k i => Tg K q u k i

/-- The free-algebra lift of the conjugator. -/
noncomputable def conjHom (K : Type*) [CommRing K] (q u : K) [Invertible q] [Invertible (q - 1)]
    (c : K) : FreeAlgebra K Gen →ₐ[K] Atilde K q u :=
  FreeAlgebra.lift K (conjGen K q u c)

@[simp] theorem conjHom_freeE (c : K) (k : ℕ) : conjHom K q u c (freeE K k) = e K q u k :=
  FreeAlgebra.lift_ι_apply _ _

@[simp] theorem conjHom_freeUp (c : K) (k : ℕ) :
    conjHom K q u c (freeUp K k) = conjRaise K q u c k := FreeAlgebra.lift_ι_apply _ _

@[simp] theorem conjHom_freeUpStar (c : K) (k : ℕ) :
    conjHom K q u c (freeUpStar K k) = dPlusStar K q u k := FreeAlgebra.lift_ι_apply _ _

@[simp] theorem conjHom_freeDown (c : K) (k : ℕ) :
    conjHom K q u c (freeDown K k) = dMinus K q u k := FreeAlgebra.lift_ι_apply _ _

@[simp] theorem conjHom_freeT (c : K) (k i : ℕ) :
    conjHom K q u c (freeT K k i) = Tg K q u k i := FreeAlgebra.lift_ι_apply _ _

@[simp] theorem conjHom_freeTinv (c : K) (k i : ℕ) :
    conjHom K q u c (freeTinv K q k i) = Tinv K q u k i :=
  map_tinvOf _ q ⅟q (conjHom_freeT c k i) (conjHom_freeE c k)

/-- The starred corner elements are fixed: the conjugator moves no generator they are built from. -/
@[simp] theorem conjHom_freeZ (c : K) (k i : ℕ) :
    conjHom K q u c (freeZ K q k i) = zElt K q u k i :=
  map_cornerOf _ (⅟q) q (-(q * ⅟(q - 1))) (conjHom_freeE c) (conjHom_freeUpStar c)
    (conjHom_freeDown c) (conjHom_freeTinv c) k i

/-- The unstarred corner elements go to the conjugated ones. -/
@[simp] theorem conjHom_freeY (c : K) (k i : ℕ) :
    conjHom K q u c (freeY K q k i) = yTwist K q u c k i :=
  map_cornerOf _ q ⅟q ⅟(q - 1) (conjHom_freeE c) (conjHom_freeUp c) (conjHom_freeDown c)
    (conjHom_freeT c) k i

section StarSwap

variable {bar : K ≃+* K} {σ : Atilde K q u →+ Atilde K q u}
  (h : IsStarSwap q bar (e K q u) (dPlus K q u) (dPlusStar K q u) (dMinus K q u) (Tg K q u) σ)
  (hbar : bar q = ⅟q)

include h hbar

/-- **The conjugator kills every relation of `Ã`.** The quiver relations and the starred group are
untouched, the unstarred group is `HJO.Dyck.TwistFamily.eq_of_sourceRel_twistRaise` at
`HJO.Dyck.Tilde.Atilde.twistFamily_unstarred`, the first mixed relation needs only that the starred
corner elements commute, the third is the closed form of `HJO.Dyck.Tilde.Atilde.yTwist_one`, and the
second is `HJO.Dyck.Tilde.Atilde.yTwist_mul_dPlusStar`. -/
theorem conjHom_rel (c : K) {x y : FreeAlgebra K Gen} (hr : Rel K q u x y) :
    conjHom K q u c x = conjHom K q u c y := by
  induction hr with
  | vertex_mul_self k => simp
  | vertex_mul_vertex hkl => simp [e_mul_e_of_ne hkl]
  | vertex_mul_down k => simp
  | down_mul_vertex k => simp
  | vertex_mul_braid k i => simp
  | braid_mul_vertex k i => simp
  | braid_eq_zero hki => simp [Tg_eq_zero hki]
  | source hs =>
    refine (twistFamily_unstarred h hbar).eq_of_sourceRel_twistRaise
      (fun hrr => eq_of_sourceRel hrr) c ?_
    rw [← conjRaise_eq]
    exact SourceRel.mapBar (bar := RingEquiv.refl K) (f := (conjHom K q u c).toAddMonoidHom)
      (E' := e K q u) (U' := conjRaise K q u c) (D' := dMinus K q u) (T' := Tg K q u)
      (fun a b => map_mul (conjHom K q u c) a b)
      (fun a x => show conjHom K q u c (a • x) = a • conjHom K q u c x from map_smul _ a x)
      (fun n => conjHom_freeE c n) (fun n => conjHom_freeUp c n)
      (fun n => conjHom_freeDown c n) (fun n i _ => conjHom_freeT c n i) hs
  | sourceStar hs =>
    refine eq_of_sourceRelStar ?_
    exact SourceRel.mapBar (bar := RingEquiv.refl K) (f := (conjHom K q u c).toAddMonoidHom)
      (E' := e K q u) (U' := dPlusStar K q u) (D' := dMinus K q u) (T' := Tinv K q u)
      (fun a b => map_mul (conjHom K q u c) a b)
      (fun a x => show conjHom K q u c (a • x) = a • conjHom K q u c x from map_smul _ a x)
      (fun n => conjHom_freeE c n) (fun n => conjHom_freeUpStar c n)
      (fun n => conjHom_freeDown c n) (fun n i _ => conjHom_freeTinv c n i) hs
  | @mixed_z k i h1 h2 =>
    simp only [map_mul, conjHom_freeZ, conjHom_freeUp, conjRaise]
    rw [mul_smul_comm, smul_mul_assoc, mul_assoc (zElt K q u (k + 1) 1), ← mixed_z h1 h2,
      ← mul_assoc, ← mul_assoc,
      zElt_comm h hbar (k := k + 1) (i := i + 1) (j := 1) (by omega) (by omega) le_rfl (by omega)]
  | @mixed_y k i h1 h2 =>
    simp only [map_mul, conjHom_freeY, conjHom_freeUpStar]
    exact yTwist_mul_dPlusStar h hbar c h1 h2
  | mixed_top k =>
    have hL : zElt K q u (k + 1) 1 * conjRaise K q u c k
        = -((c * (u * q ^ (k + 1))) • (zElt K q u (k + 1) 1 *
            (yElt K q u (k + 1) 1 * dPlusStar K q u k))) := by
      rw [conjRaise, mul_smul_comm, zElt_one_mul_dPlus, mul_neg, mul_smul_comm, smul_neg,
        smul_smul]
    have hR : (-(u * q ^ (k + 1)) : K) • (yTwist K q u c (k + 1) 1 * dPlusStar K q u k)
        = -((c * (u * q ^ (k + 1))) • (zElt K q u (k + 1) 1 *
            (yElt K q u (k + 1) 1 * dPlusStar K q u k))) := by
      rw [yTwist_one h hbar c (show 1 ≤ k + 1 by omega), smul_mul_assoc, smul_smul,
        show -(u * q ^ (k + 1)) * c = -(c * (u * q ^ (k + 1))) from by ring,
        neg_smul (c * (u * q ^ (k + 1))), mul_assoc]
    simp only [map_mul, map_smul, conjHom_freeZ, conjHom_freeY, conjHom_freeUp,
      conjHom_freeUpStar]
    rw [hL, hR]

/-- **Mellit's conjugator, as an algebra endomorphism of `Ã`** — the `Φ_c` of
`HJO.Dyck.Tilde.Atilde.biGrading`. It fixes every idempotent, every loop, `d₋` and `d₊^*`, and sends
`d₊` at the vertex `k` to `c·z_1^{(k+1)}d₊`. -/
noncomputable def conjTwist (c : K) : Atilde K q u →ₐ[K] Atilde K q u :=
  RingQuot.liftAlgHom K ⟨conjHom K q u c, fun _ _ hr => conjHom_rel h hbar c hr⟩

@[simp] theorem conjTwist_mk (c : K) (x : FreeAlgebra K Gen) :
    conjTwist h hbar c (mk K q u x) = conjHom K q u c x :=
  RingQuot.liftAlgHom_mkAlgHom_apply K (conjHom K q u c) (s := Rel K q u)
    (fun _ _ hr => conjHom_rel h hbar c hr) x

@[simp] theorem conjTwist_e (c : K) (k : ℕ) : conjTwist h hbar c (e K q u k) = e K q u k := by
  simpa using conjTwist_mk h hbar c (freeE K k)

@[simp] theorem conjTwist_Tg (c : K) (k i : ℕ) :
    conjTwist h hbar c (Tg K q u k i) = Tg K q u k i := by
  simpa using conjTwist_mk h hbar c (freeT K k i)

@[simp] theorem conjTwist_dMinus (c : K) (k : ℕ) :
    conjTwist h hbar c (dMinus K q u k) = dMinus K q u k := by
  simpa using conjTwist_mk h hbar c (freeDown K k)

@[simp] theorem conjTwist_dPlusStar (c : K) (k : ℕ) :
    conjTwist h hbar c (dPlusStar K q u k) = dPlusStar K q u k := by
  simpa using conjTwist_mk h hbar c (freeUpStar K k)

/-- **The conjugator at the unstarred raising arrow**: the clause the bigrading lemma reads. -/
@[simp] theorem conjTwist_dPlus (c : K) (k : ℕ) :
    conjTwist h hbar c (dPlus K q u k)
      = c • (zElt K q u (k + 1) 1 * dPlus K q u k) := by
  simpa [conjRaise] using conjTwist_mk h hbar c (freeUp K k)

/-- **The conjugator exists**, in exactly the shape `HJO.Dyck.Tilde.Atilde.map_biGrade_le_conj` and
`HJO.Dyck.Tilde.Atilde.biGrading` carry as hypotheses. -/
theorem exists_conjTwist (c : K) :
    ∃ Φ : Atilde K q u →ₐ[K] Atilde K q u,
      (∀ k, Φ (e K q u k) = e K q u k) ∧ (∀ k i, Φ (Tg K q u k i) = Tg K q u k i) ∧
        (∀ k, Φ (dMinus K q u k) = dMinus K q u k) ∧
        (∀ k, Φ (dPlusStar K q u k) = dPlusStar K q u k) ∧
        (∀ k, Φ (dPlus K q u k) = c • (zElt K q u (k + 1) 1 * dPlus K q u k)) :=
  ⟨conjTwist h hbar c, conjTwist_e h hbar c, conjTwist_Tg h hbar c, conjTwist_dMinus h hbar c,
    conjTwist_dPlusStar h hbar c, conjTwist_dPlus h hbar c⟩

/-! ### The bigrading lemma, unconditionally

`HJO.Dyck.Tilde.Atilde.biGrading` is stated for two *hypothetical* endomorphisms of `Ã`. Both
exist — the conjugator here, the index shift at `HJO.Dyck.Tilde.Atilde.starTwist` — so the
bigrading holds unconditionally. -/

/-- **The conjugator carries `Ã_{m,n}` into `Ã_{m+n,n}`**, unconditionally: the hypotheses of
`HJO.Dyck.Tilde.Atilde.map_biGrade_le_conj` discharged at the map that exists. -/
theorem map_biGrade_le_conj_conjTwist (c : K) (m n : ℕ) :
    (biGrade K q u (m, n)).map (conjTwist h hbar c).toLinearMap
      ≤ biGrade K q u (m + n, n) :=
  map_biGrade_le_conj (conjTwist h hbar c) (conjTwist_e h hbar c) (conjTwist_Tg h hbar c)
    (conjTwist_dMinus h hbar c) c (conjTwist_dPlusStar h hbar c) (conjTwist_dPlus h hbar c) m n

/-- **`HJO.Dyck.Tilde.rel_biHomogeneous`, with both of its endomorphisms supplied.** The bigrading
lemma of `HJO.Dyck.Tilde.Atilde.biGrading` read at the conjugator of this file and the index shift
of `HJO.Dyck.Tilde.Atilde.starTwist`: the two degree shifts and the two sign clauses, with no
endomorphism left as a hypothesis. -/
theorem biGrading_conjTwist_starTwist (c : K) (m n : ℕ) :
    (biGrade K q u (m, n)).map (conjTwist h hbar c).toLinearMap
        ≤ biGrade K q u (m + n, n) ∧
      (biGrade K q u (m, n)).map (starTwist K q u (-1 : K)).toLinearMap
        ≤ biGrade K q u (m, m + n) ∧
      (∀ x ∈ biGrade K q u (m, n),
        signTwist K q u (conjTwist h hbar c (signTwist K q u x))
          = (-1 : K) ^ n • conjTwist h hbar c x) ∧
      (∀ x ∈ biGrade K q u (m, n),
        signTwist K q u (starTwist K q u (-1 : K) (signTwist K q u x))
          = (-1 : K) ^ m • starTwist K q u (-1 : K) x) :=
  biGrading (conjTwist h hbar c) (starTwist K q u (-1 : K)) c (conjTwist_e h hbar c)
    (conjTwist_Tg h hbar c) (conjTwist_dMinus h hbar c) (conjTwist_dPlusStar h hbar c)
    (conjTwist_dPlus h hbar c) (starTwist_e (-1 : K)) (starTwist_Tg (-1 : K))
    (starTwist_dMinus (-1 : K)) (starTwist_dPlus (-1 : K)) starTwist_neg_one_dPlusStar m n

end StarSwap

/-- **The conjugator exists, with the star swap discharged.** The hypotheses left are exactly those
of `HJO.Sym.paramInvLambda` — the bar inverts `q` and `u` and is an involution — together with
`[Invertible u]`, which is what `HJO.Dyck.Tilde.Atilde.exists_isStarSwap` needs for the third mixed
relation. -/
@[hjo "lem_mellit_ns_shift_exists"]
theorem exists_conjTwist_of_bar [Invertible u] (bar : K ≃+* K) (hbar : bar q = ⅟q)
    (hbaru : bar u = ⅟u) (hbb : ∀ c : K, bar (bar c) = c) (c : K) :
    ∃ Φ : Atilde K q u →ₐ[K] Atilde K q u,
      (∀ k, Φ (e K q u k) = e K q u k) ∧ (∀ k i, Φ (Tg K q u k i) = Tg K q u k i) ∧
        (∀ k, Φ (dMinus K q u k) = dMinus K q u k) ∧
        (∀ k, Φ (dPlusStar K q u k) = dPlusStar K q u k) ∧
        (∀ k, Φ (dPlus K q u k) = c • (zElt K q u (k + 1) 1 * dPlus K q u k)) := by
  obtain ⟨σ, hσ⟩ := exists_isStarSwap (K := K) (q := q) (u := u) (bar := bar) hbar hbaru hbb
  exact exists_conjTwist hσ hbar c

end HJO.Dyck.Tilde.Atilde
