/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.CarlssonMellit.CornerRaising
public import HJO.CarlssonMellit.CornerCalculus
public import HJO.CarlssonMellit.TildeZ1
public meta import HJO.Attr

/-! # The unstarred half of `Ã` receives `𝔸_q`

`Ã` is presented on the quiver of `𝔸_q` enlarged by a second raising arrow, and its relations
contain the relations of `𝔸_q` verbatim in the unstarred generators. So the assignment
`e ↦ e`, `d₊ ↦ d₊`, `d₋ ↦ d₋`, `T_i ↦ T_i` is a `K`-algebra map `𝔸_q → Ã`, and every identity of
`𝔸_q` may be read in `Ã`.

The map is not cosmetic: without it the corner-element calculus of `𝔸_q` — the raising arrow's
transport past `y_i`, the commutator read back from the top corner element, the Hecke
straightening rule — would be unavailable inside `Ã`, where the kernel argument of
`HJO.Standing.atildeE0_inf_ker_evalOne_eq_param` needs it. Nothing here is a new
mathematical input; it is the transport the two presentations already entitle one to.

## Main definitions

* `HJO.Dyck.freeToTilde`: the map on the free algebra of `𝔸_q`'s quiver.
* `HJO.Dyck.toTilde`: the algebra map `𝔸_q → Ã`.

## Main results

* `HJO.Dyck.freeToTilde_rel`: the map kills the relations of `𝔸_q`, one constructor at a time.
* `HJO.Dyck.toTilde_yElt`: it carries `𝔸_q`'s corner elements to `Ã`'s.
* `HJO.Dyck.Tilde.Atilde.dPlus_mul_yElt`: the raising arrow's transport past a corner element,
  inside `Ã`.

## Implementation notes

The map is *not* claimed injective, and the kernel argument does not need it to be — that would be
the faithfulness statement `HJO.Standing.atildeE0_inf_ker_evalOne_eq_param` is built to prove. What
is used is only that identities push forward.

`Ã` has no names of its own for the words `T_1 ⋯ T_n` and `T̂_n ⋯ T̂_1`; the generic
`HJO.Dyck.segUpOf` and `HJO.Dyck.tinvWordOf` at `Ã`'s generators are used instead, which is also
what `HJO.Dyck.Tilde.Atilde.yElt` is already defined through.

## References

The file relates the definitions `HJO.Dyck.Aq` and `HJO.Dyck.Tilde.Atilde`, and serves the
proof of `HJO.Dyck.Tilde.Atilde.dPlusStar_mul_mem_aqE0_sup_kernelIdealE0`, which reads `𝔸_q`'s
corner calculus at the algebra level.
-/

@[expose] public section

namespace HJO.Dyck

variable {K : Type*} [CommRing K] {q u : K} [Invertible q] [Invertible (q - 1)]

/-! ### The map on the free algebra -/

/-- Each generator of `𝔸_q`'s quiver, read as the corresponding unstarred generator of `Ã`. -/
noncomputable def genToTilde (K : Type*) [CommRing K] (q u : K) [Invertible q]
    [Invertible (q - 1)] : Gen → Tilde.Atilde K q u
  | Gen.vertex k => Tilde.Atilde.e K q u k
  | Gen.up k => Tilde.Atilde.dPlus K q u k
  | Gen.down k => Tilde.Atilde.dMinus K q u k
  | Gen.braid k i => Tilde.Atilde.Tg K q u k i

/-- **The map on the free algebra**: the algebra map on the path algebra of `𝔸_q`'s quiver sending
each generator to the unstarred generator of `Ã` with the same name. -/
noncomputable def freeToTilde (K : Type*) [CommRing K] (q u : K) [Invertible q]
    [Invertible (q - 1)] : FreeAlgebra K Gen →ₐ[K] Tilde.Atilde K q u :=
  FreeAlgebra.lift K (genToTilde K q u)

@[simp] theorem freeToTilde_freeE (k : ℕ) :
    freeToTilde K q u (freeE K k) = Tilde.Atilde.e K q u k := FreeAlgebra.lift_ι_apply _ _

@[simp] theorem freeToTilde_freeUp (k : ℕ) :
    freeToTilde K q u (freeUp K k) = Tilde.Atilde.dPlus K q u k := FreeAlgebra.lift_ι_apply _ _

@[simp] theorem freeToTilde_freeDown (k : ℕ) :
    freeToTilde K q u (freeDown K k) = Tilde.Atilde.dMinus K q u k := FreeAlgebra.lift_ι_apply _ _

@[simp] theorem freeToTilde_freeT (k i : ℕ) :
    freeToTilde K q u (freeT K k i) = Tilde.Atilde.Tg K q u k i := FreeAlgebra.lift_ι_apply _ _

@[simp] theorem freeToTilde_freeDelta (k : ℕ) :
    freeToTilde K q u (freeDelta K k)
      = commOf (Tilde.Atilde.dPlus K q u) (Tilde.Atilde.dMinus K q u) k := by
  rw [freeDelta, commOf, map_sub, map_mul, map_mul, freeToTilde_freeUp, freeToTilde_freeUp,
    freeToTilde_freeDown, freeToTilde_freeDown]

/-- **The map kills the relations of `𝔸_q`.** Each of the seven quiver relations is an identity of
`Ã`'s own quiver; each of the eleven defining relations of `𝔸_q` is an instance of
`HJO.Dyck.SourceRel` at `Ã`'s unstarred generators, which is
`HJO.Dyck.Tilde.Atilde.eq_of_sourceRel`. -/
theorem freeToTilde_rel {x y : FreeAlgebra K Gen} (h : Rel K q x y) :
    freeToTilde K q u x = freeToTilde K q u y := by
  induction h with
  | vertex_mul_self k => simp
  | vertex_mul_vertex h => simpa using Tilde.Atilde.e_mul_e_of_ne (K := K) (q := q) (u := u) h
  | vertex_mul_up k => simp
  | up_mul_vertex k => simp
  | vertex_mul_down k => simp
  | down_mul_vertex k => simp
  | vertex_mul_braid k i => simp
  | braid_mul_vertex k i => simp
  | braid_eq_zero h => simpa using Tilde.Atilde.Tg_eq_zero (K := K) (q := q) (u := u) h
  | quadratic h =>
    simpa using Tilde.Atilde.eq_of_sourceRel (SourceRel.quadratic (q := q)
      (E := Tilde.Atilde.e K q u) (U := Tilde.Atilde.dPlus K q u)
      (D := Tilde.Atilde.dMinus K q u) (T := Tilde.Atilde.Tg K q u) h)
  | braid_braid h =>
    simpa using Tilde.Atilde.eq_of_sourceRel (SourceRel.braid_braid (q := q)
      (E := Tilde.Atilde.e K q u) (U := Tilde.Atilde.dPlus K q u)
      (D := Tilde.Atilde.dMinus K q u) (T := Tilde.Atilde.Tg K q u) h)
  | braid_comm hi hj hij =>
    simpa using Tilde.Atilde.eq_of_sourceRel (SourceRel.braid_comm (q := q)
      (E := Tilde.Atilde.e K q u) (U := Tilde.Atilde.dPlus K q u)
      (D := Tilde.Atilde.dMinus K q u) (T := Tilde.Atilde.Tg K q u) hi hj hij)
  | braid_down h =>
    simpa using Tilde.Atilde.eq_of_sourceRel (SourceRel.braid_down (q := q)
      (E := Tilde.Atilde.e K q u) (U := Tilde.Atilde.dPlus K q u)
      (D := Tilde.Atilde.dMinus K q u) (T := Tilde.Atilde.Tg K q u) h)
  | up_braid h =>
    simpa using Tilde.Atilde.eq_of_sourceRel (SourceRel.up_braid (q := q)
      (E := Tilde.Atilde.e K q u) (U := Tilde.Atilde.dPlus K q u)
      (D := Tilde.Atilde.dMinus K q u) (T := Tilde.Atilde.Tg K q u) h)
  | braid_up_up k =>
    simpa using Tilde.Atilde.eq_of_sourceRel (SourceRel.braid_up_up (q := q)
      (E := Tilde.Atilde.e K q u) (U := Tilde.Atilde.dPlus K q u)
      (D := Tilde.Atilde.dMinus K q u) (T := Tilde.Atilde.Tg K q u) k)
  | down_down_braid m =>
    simpa using Tilde.Atilde.eq_of_sourceRel (SourceRel.down_down_braid (q := q)
      (E := Tilde.Atilde.e K q u) (U := Tilde.Atilde.dPlus K q u)
      (D := Tilde.Atilde.dMinus K q u) (T := Tilde.Atilde.Tg K q u) m)
  | down_delta =>
    simpa using Tilde.Atilde.eq_of_sourceRel (SourceRel.down_delta (q := q)
      (E := Tilde.Atilde.e K q u) (U := Tilde.Atilde.dPlus K q u)
      (D := Tilde.Atilde.dMinus K q u) (T := Tilde.Atilde.Tg K q u) _)
  | braid_delta =>
    simpa using Tilde.Atilde.eq_of_sourceRel (SourceRel.braid_delta (q := q)
      (E := Tilde.Atilde.e K q u) (U := Tilde.Atilde.dPlus K q u)
      (D := Tilde.Atilde.dMinus K q u) (T := Tilde.Atilde.Tg K q u) _)

/-! ### The algebra map -/

/-- **The algebra map `𝔸_q → Ã`**: `Ã`'s relations contain `𝔸_q`'s verbatim in the unstarred
generators, so the identity on generator names descends to the quotients. -/
noncomputable def toTilde (K : Type*) [CommRing K] (q u : K) [Invertible q] [Invertible (q - 1)] :
    Aq K q →ₐ[K] Tilde.Atilde K q u :=
  RingQuot.liftAlgHom K ⟨freeToTilde K q u, fun _ _ h => freeToTilde_rel h⟩

@[simp] theorem toTilde_mk (x : FreeAlgebra K Gen) :
    toTilde K q u (Aq.mk K q x) = freeToTilde K q u x :=
  RingQuot.liftAlgHom_mkAlgHom_apply K (freeToTilde K q u) (s := Rel K q)
    (fun _ _ h => freeToTilde_rel h) x

@[simp] theorem toTilde_e (k : ℕ) :
    toTilde K q u (Aq.e K q k) = Tilde.Atilde.e K q u k := by rw [Aq.e, toTilde_mk]; simp

@[simp] theorem toTilde_dPlus (k : ℕ) :
    toTilde K q u (Aq.dPlus K q k) = Tilde.Atilde.dPlus K q u k := by
  rw [Aq.dPlus, toTilde_mk]; simp

@[simp] theorem toTilde_dMinus (k : ℕ) :
    toTilde K q u (Aq.dMinus K q k) = Tilde.Atilde.dMinus K q u k := by
  rw [Aq.dMinus, toTilde_mk]; simp

@[simp] theorem toTilde_Tg (k i : ℕ) :
    toTilde K q u (Aq.Tg K q k i) = Tilde.Atilde.Tg K q u k i := by rw [Aq.Tg, toTilde_mk]; simp

@[simp] theorem toTilde_Delta (k : ℕ) :
    toTilde K q u (Aq.Delta K q k)
      = commOf (Tilde.Atilde.dPlus K q u) (Tilde.Atilde.dMinus K q u) k :=
  map_commOf (toTilde K q u) toTilde_dPlus toTilde_dMinus k

@[simp] theorem toTilde_Tinv (k i : ℕ) :
    toTilde K q u (Aq.Tinv K q k i) = Tilde.Atilde.Tinv K q u k i :=
  map_tinvOf (toTilde K q u) q ⅟q (toTilde_Tg k i) (toTilde_e k)

theorem toTilde_tinvWord (k n : ℕ) :
    toTilde K q u (Aq.tinvWord K q k n)
      = tinvWordOf q ⅟q (Tilde.Atilde.e K q u) (Tilde.Atilde.Tg K q u) k n := by
  rw [← Aq.tinvWordOf_eq_tinvWord]
  exact map_tinvWordOf (toTilde K q u) q ⅟q toTilde_e (fun n i => toTilde_Tg n i) k n

@[simp] theorem toTilde_yElt (k i : ℕ) :
    toTilde K q u (Aq.yElt K q k i) = Tilde.Atilde.yElt K q u k i := by
  rw [← Aq.cornerOf_eq_yElt, Tilde.Atilde.yElt]
  exact map_cornerOf (toTilde K q u) q ⅟q ⅟(q - 1) toTilde_e toTilde_dPlus toTilde_dMinus
    (fun n i => toTilde_Tg n i) k i

theorem toTilde_tSegUp (k a n : ℕ) :
    toTilde K q u (Aq.tSegUp K q k a n)
      = segUpOf (Tilde.Atilde.e K q u) (Tilde.Atilde.Tg K q u) k a n := by
  induction n with
  | zero => rw [Aq.tSegUp, segUpOf, toTilde_e]
  | succ n ih => rw [Aq.tSegUp, segUpOf, map_mul, ih, toTilde_Tg]

theorem toTilde_tSeg (k a n : ℕ) :
    toTilde K q u (Aq.tSeg K q k a n)
      = segOf (Tilde.Atilde.e K q u) (Tilde.Atilde.Tg K q u) k a n := by
  induction n with
  | zero => rw [Aq.tSeg, segOf, toTilde_e]
  | succ n ih => rw [Aq.tSeg, segOf, map_mul, ih, toTilde_Tg]

/-! ### What the transport delivers inside `Ã` -/

namespace Tilde.Atilde

/-- **Every corner element of `Ã` transports along the unstarred raising arrow, up to conjugation
by an ascending word of loops**: `d₊y_i^{(k)} = W_iy_i^{(k+1)}W_i^{-1}d₊` for `1 ≤ i ≤ k`. This is
`HJO.Dyck.Aq.dPlus_mul_yElt` read in `Ã` along `HJO.Dyck.toTilde`, and it is the step of
`HJO.Dyck.Tilde.Atilde.dPlusStar_mul_mem_aqE0_sup_kernelIdealE0`'s span argument that moves the
raising arrow past a corner element. -/
theorem dPlus_mul_yElt {k i : ℕ} (h1 : 1 ≤ i) (hik : i ≤ k) :
    dPlus K q u k * yElt K q u k i
      = segUpOf (e K q u) (Tg K q u) (k + 1) 0 i * yElt K q u (k + 1) i *
        tinvWordOf q ⅟q (e K q u) (Tg K q u) (k + 1) i * dPlus K q u k := by
  have h := congrArg (HJO.Dyck.toTilde K q u)
    (Aq.dPlus_mul_yElt (K := K) (q := q) (k := k) i h1 hik)
  simp only [map_mul, toTilde_dPlus, toTilde_yElt, toTilde_tSegUp, toTilde_tinvWord] at h
  exact h

/-- **The unstarred commutator of `Ã`, read back from the top corner element**:
`d₊d₋ - d₋d₊ = (q-1)(T_1 ⋯ T_{k-1})y_k` at the vertex `k`. This is
`HJO.Dyck.Aq.Delta_eq_smul_tSegUp_mul_yElt` read in `Ã`; it is what turns a leading `d₊` into
leading-`y` terms in `HJO.Dyck.Tilde.Atilde.dPlusStar_mul_mem_aqE0_sup_kernelIdealE0`'s span
argument. -/
theorem commOf_eq_smul_segUpOf_mul_yElt {k : ℕ} (hk : 1 ≤ k) :
    commOf (dPlus K q u) (dMinus K q u) (k - 1)
      = (q - 1) • (segUpOf (e K q u) (Tg K q u) k 0 (k - 1) * yElt K q u k k) := by
  have h := congrArg (HJO.Dyck.toTilde K q u)
    (Aq.Delta_eq_smul_tSegUp_mul_yElt (K := K) (q := q) hk)
  simp only [toTilde_Delta, map_smul, map_mul, toTilde_tSegUp, toTilde_yElt] at h
  exact h

end Tilde.Atilde

end HJO.Dyck
