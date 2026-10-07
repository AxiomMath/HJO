/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.CMStructure.TwistHom
public meta import HJO.Attr

/-! # The twisted action of the symmetric functions on `V_k`

`HJO.Sweep.twistedAction`: for `k ≥ 0`, `∗_k` is the map from `Λ × V_k` to `V_k` sending `(F, G)` to
`tw_k(F)·G`.

## What there is to say

The twisting homomorphism `tw_k : Λ → V_k` is `HJO.Sweep.twist`, with
`HJO.Sweep.twist_mem_piece` placing its image in `V_k`, so the definition is one
multiplication. What it adds beyond the homomorphism is the *codomain*: the value
lies in `V_k`, and for that both factors must, which is `HJO.Sweep.twistedAction_mem_piece`.

The action is recorded in three shapes, because different consumers want different ones:

* `HJO.Sweep.twistedAction` — the two-argument map, into the total space;
* `HJO.Sweep.twistedActionToPiece` — the same with both the domain factor `V_k` and the target `V_k`
  carried as subobjects, the literal `Λ × V_k → V_k`;
* `HJO.Sweep.twistedActionₗ` — the `𝕜`-bilinear reading, which is the shape the intertwining lemmas
  `HJO.Sweep.cmDPlus_twistedAction` and `HJO.Sweep.dminusCM_twistedAction` compose with.

That it is an *action* — `(FF')∗_kG = F∗_k(F'∗_kG)` and `1∗_kG = G` — is
`HJO.Sweep.twistedAction_mul` and `HJO.Sweep.twistedAction_one`, and it is exactly the
multiplicativity of `tw_k`. Calling `∗_k` an action asserts exactly these two identities, and
they are what the name means.

## It is the `m = 0` member of the starred family, and not the same definition

`HJO.Sweep.twistedMult` gives a family `∗_m`, `0 ≤ m ≤ k`, twisting by
`(q-1)(u∑_{i≤m}y_i + ∑_{i>m}y_i)`, and records that `∗_0` is this `∗_k`. The two are kept separate
because `HJO.Sweep.twistedAction` is used far earlier, where the parameter `m` would be noise, and
no second twisting homomorphism is defined.

## Main definitions

* `HJO.Sweep.twistedAction`, `HJO.Sweep.twistedActionToPiece`, `HJO.Sweep.twistedActionₗ`: `∗_k`.

## References

Following E. Carlsson and A. Mellit, *A proof of the shuffle conjecture*, §5.
-/

@[expose] public section

namespace HJO.Sweep

section Twisted

variable {L : Type*} [CommRing L]

/-- **The twisted action `∗_k`**, `HJO.Sweep.twistedAction`: `F ∗_k G = tw_k(F)·G`, with
`tw_k` the twisting homomorphism of `HJO.Sweep.twist`.

Stated into the total space, the one-total-space convention of `HJO.Shuffle.SweepModule`;
`HJO.Sweep.twistedAction_mem_piece` is the codomain `V_k` and
`HJO.Sweep.twistedActionToPiece` the corestriction. -/
@[hjo "def_cm_twisted"]
noncomputable def twistedAction (L : Type*) [CommRing L] (q : L) (k : ℕ) (F : Sym.Lambda L)
    (G : Total L) : Total L :=
  twist L q k F * G

@[hjo "def_cm_twisted"]
theorem twistedAction_apply (q : L) (k : ℕ) (F : Sym.Lambda L) (G : Total L) :
    twistedAction L q k F G = twist L q k F * G := rfl

/-- **The twisted action lands in `V_k`**, which is the codomain `HJO.Sweep.twistedAction` names:
the twisting homomorphism lands there by `HJO.Sweep.twist_mem_piece` and `V_k` is a subalgebra. -/
@[hjo "def_cm_twisted"]
theorem twistedAction_mem_piece (q : L) (k : ℕ) (F : Sym.Lambda L) {G : Total L}
    (hG : G ∈ piece L k) : twistedAction L q k F G ∈ piece L k :=
  mul_mem (twist_mem_piece q k F) hG

/-- **`∗_k` as a map `Λ × V_k → V_k`**, with the domain and codomain of its definition. -/
@[hjo "def_cm_twisted"]
noncomputable def twistedActionToPiece (L : Type*) [CommRing L] (q : L) (k : ℕ)
    (F : Sym.Lambda L) (G : (piece L k).restrictScalars L) : (piece L k).restrictScalars L :=
  ⟨twistedAction L q k F G, twistedAction_mem_piece q k F G.2⟩

@[simp]
theorem coe_twistedActionToPiece (q : L) (k : ℕ) (F : Sym.Lambda L)
    (G : (piece L k).restrictScalars L) :
    (twistedActionToPiece L q k F G : Total L) = twistedAction L q k F G := rfl

/-- **`∗_k` is an action**: `(FF') ∗_k G = F ∗_k (F' ∗_k G)`, because `tw_k` is multiplicative. -/
theorem twistedAction_mul (q : L) (k : ℕ) (F F' : Sym.Lambda L) (G : Total L) :
    twistedAction L q k (F * F') G = twistedAction L q k F (twistedAction L q k F' G) := by
  rw [twistedAction, twistedAction, twistedAction, map_mul, mul_assoc]

/-- **`∗_k` is unital**: `1 ∗_k G = G`, because `tw_k` is a ring homomorphism. -/
@[simp]
theorem twistedAction_one (q : L) (k : ℕ) (G : Total L) : twistedAction L q k 1 G = G := by
  rw [twistedAction, map_one, one_mul]

/-- **`∗_k` is `𝕜`-bilinear**, the shape in which the intertwining lemmas
`HJO.Sweep.cmDPlus_twistedAction` and `HJO.Sweep.dminusCM_twistedAction` compose it with `d_±`. -/
@[hjo "def_cm_twisted"]
noncomputable def twistedActionₗ (L : Type*) [CommRing L] (q : L) (k : ℕ) :
    Sym.Lambda L →ₗ[L] Total L →ₗ[L] Total L where
  toFun F := LinearMap.mulLeft L (twist L q k F)
  map_add' F F' := by
    refine LinearMap.ext fun G => ?_
    simp only [LinearMap.mulLeft_apply, LinearMap.add_apply, map_add, add_mul]
  map_smul' c F := by
    refine LinearMap.ext fun G => ?_
    simp only [LinearMap.mulLeft_apply, LinearMap.smul_apply, RingHom.id_apply, map_smul,
      smul_mul_assoc]

@[simp]
theorem twistedActionₗ_apply (q : L) (k : ℕ) (F : Sym.Lambda L) (G : Total L) :
    twistedActionₗ L q k F G = twistedAction L q k F G := rfl

end Twisted

end HJO.Sweep
