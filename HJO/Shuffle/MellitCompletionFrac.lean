/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.Shuffle.MellitShiftLoc
public meta import HJO.Attr

/-! # The completion with the letters inverted, and the two extended operators

The extended operators `d^*_+` and `τ^*_k` (here `HJO.Sweep.hatFracDplusStar` and
`HJO.Sweep.nsShiftStarFrac`) are naturally stated on `V̂°_k`, the **localization** at `y_1⋯y_k` of
the completion of `V_k`, and not on the completion itself. This file supplies an ambient in which
they can be defined: the fraction field of `HJO.Sweep.TotalHat`, into which every `V̂°_k` embeds.

## The completion is a domain

The graded pieces are finite dimensional, and the completion is the ring of formal series in the
`p_r` and the `y_i`; it is a domain, and `y_1⋯y_k` is a non-zerodivisor in it, so the
localization is faithful. The domain half
is `HJO.Sweep.TotalHat.mul_ne_zero'` below, and it is the usual leading-term argument read on the
convolution: if `a` and `b` are the least degrees carrying a nonzero member of `F` and of `G`, then
every term of `(FG)_{a+b} = ∑_{e≤a+b}F_eG_{a+b-e}` vanishes except `F_aG_b`.

That is all the localization needs, so the fraction field is available and each `V̂°_k` is a
subring of it. The operators below are therefore defined on a *larger* domain than `V̂°_k`
and restrict to the operators on `V̂°_k` — the convention `HJO.Sweep.qshift` already follows for
`τ_{k,i}` and `HJO.Sweep.nsShiftExt` for `τ_k`.

## Main definitions

* `HJO.Sweep.HatFrac` — the fraction field of the completion.
* `HJO.Sweep.hatFracDplusStar` — the extended raising operator `d^*_+`.
* `HJO.Sweep.nsShiftStarFrac` — the extended conjugate shift `τ^*_k`.

## Main results

* `HJO.Sweep.hatFracDplusStar_nsShiftStarFrac` —
  `d^*_+(τ^*_kF) = (1-y_1)τ^*_{k+1}(d^*_+F)`, read on the
  ambient the statement lives on.

## The localized completion `V̂°_k` is a different ring

`V̂°_k` is a **per-`k` ring**, the localization of the completion of `V_k` at `y_1⋯y_k`. The
fraction field here is strictly larger — it inverts `1 + p_1` too — so it is not that object, and
using it in place of `V̂°_k` would not be a generalization but a substitution. Defining a *map* on a
larger domain is a generalization, which is why the two operators below are defined on the
ambient. The ring `V̂°_k` itself, the localization of the completion `HJO.Sweep.pieceHat` of
`piece k` at `y_1⋯y_k`, is constructed downstream as `HJO.Sweep.NsAmbient`, in
`HJO/CarlssonMellit/AmbientBrackets.lean`, together with its embedding in this field.

## References

Transcribing A. Mellit, *Toric braids and `(m,n)`-parking functions*, §3.7.
-/

@[expose] public section

open Finset MvPolynomial

namespace HJO.Sweep

namespace TotalHat

variable {L : Type*} [Field L]

/-- The completion is nontrivial: its member in degree zero separates `1` from `0`. -/
instance : Nontrivial (TotalHat L) := by
  refine ⟨⟨1, 0, fun h => ?_⟩⟩
  have h0 : ((1 : TotalHat L) 0 : Total L) = ((0 : TotalHat L) 0 : Total L) := by rw [h]
  rw [coe_one, coe_zero] at h0
  exact one_ne_zero h0

theorem eq_zero_of_forall_coe {F : TotalHat L} (h : ∀ d, (F d : Total L) = 0) : F = 0 :=
  TotalHat.ext fun d => by rw [h d, coe_zero]

/-- **The completion has no zero divisors**, by the leading term: at the sum of the two least
degrees carrying a nonzero member, every term of the convolution but one vanishes. -/
theorem mul_ne_zero' {F G : TotalHat L} (hF : F ≠ 0) (hG : G ≠ 0) : F * G ≠ 0 := by
  classical
  have hF' : ∃ d, (F d : Total L) ≠ 0 := by
    by_contra hc
    push Not at hc
    exact hF (eq_zero_of_forall_coe hc)
  have hG' : ∃ d, (G d : Total L) ≠ 0 := by
    by_contra hc
    push Not at hc
    exact hG (eq_zero_of_forall_coe hc)
  set a := Nat.find hF' with ha
  set b := Nat.find hG' with hb
  have hFa : (F a : Total L) ≠ 0 := Nat.find_spec hF'
  have hGb : (G b : Total L) ≠ 0 := Nat.find_spec hG'
  have hFlt : ∀ e < a, (F e : Total L) = 0 := fun e he => by
    have h := Nat.find_min hF' he
    simpa using h
  have hGlt : ∀ e < b, (G e : Total L) = 0 := fun e he => by
    have h := Nat.find_min hG' he
    simpa using h
  intro hzero
  have hab : ((F * G) (a + b) : Total L) = 0 := by rw [hzero]; rfl
  rw [coe_mul, Finset.sum_eq_single_of_mem a (Finset.mem_range.2 (by omega))
    (fun e he hne => by
      rw [Finset.mem_range] at he
      rcases lt_or_gt_of_ne hne with h | h
      · rw [hFlt e h, zero_mul]
      · rw [hGlt (a + b - e) (by omega), mul_zero])] at hab
  rw [Nat.add_sub_cancel_left] at hab
  exact (mul_ne_zero hFa hGb) hab

noncomputable instance : NoZeroDivisors (TotalHat L) where
  eq_zero_or_eq_zero_of_mul_eq_zero {F G} h := by
    by_contra hc
    push Not at hc
    exact mul_ne_zero' hc.1 hc.2 h

noncomputable instance : IsDomain (TotalHat L) := NoZeroDivisors.to_isDomain _

end TotalHat

/-! ### The fraction field of the completion -/

section HatFrac

variable {L : Type*} [Field L]

/-- **The completion with the letters inverted**: the fraction field of `HJO.Sweep.TotalHat`. Every
localized completion `V̂°_k` is a subring of it, the completion being a domain. -/
abbrev HatFrac (L : Type*) [Field L] : Type _ := FractionRing (TotalHat L)

/-- The image of an element of the completion in its fraction field. -/
noncomputable abbrev toHatFrac (F : TotalHat L) : HatFrac L :=
  algebraMap (TotalHat L) (HatFrac L) F

theorem toHatFrac_mul (F G : TotalHat L) :
    toHatFrac (F * G) = toHatFrac F * toHatFrac G := map_mul _ F G

theorem toHatFrac_sub (F G : TotalHat L) :
    toHatFrac (F - G) = toHatFrac F - toHatFrac G := map_sub _ F G

theorem toHatFrac_one : toHatFrac (1 : TotalHat L) = 1 := map_one _

/-- The componentwise extension of a degree-preserving substitution, bundled as a ring
homomorphism of the completion. -/
noncomputable def hatRingHom {D : Total L →ₐ[L] Total L} (hD : PreservesTotalComp D) :
    TotalHat L →+* TotalHat L where
  toFun := hatMap hD
  map_one' := hatMap_one hD
  map_mul' := hatMap_mul hD
  map_zero' := TotalHat.ext fun d => by rw [coe_hatMap, TotalHat.coe_zero, map_zero]
  map_add' := hatMap_add hD

theorem hatRingHom_apply {D : Total L →ₐ[L] Total L} (hD : PreservesTotalComp D) (F : TotalHat L) :
    hatRingHom hD F = hatMap hD F := rfl

/-- **The extension of an injective substitution is injective**, being injective on each
member. -/
theorem hatRingHom_injective {D : Total L →ₐ[L] Total L} (hD : PreservesTotalComp D)
    (hinj : Function.Injective D) : Function.Injective (hatRingHom hD) := fun F G h =>
  TotalHat.ext fun d => hinj (by
    rw [← coe_hatMap hD F d, ← coe_hatMap hD G d, ← hatRingHom_apply, ← hatRingHom_apply, h])

/-- The extension of an injective substitution to the fraction field of the completion. -/
noncomputable def hatFracLift {D : Total L →ₐ[L] Total L} (hD : PreservesTotalComp D)
    (hinj : Function.Injective D) : HatFrac L →+* HatFrac L :=
  IsFractionRing.lift (A := TotalHat L) (K := HatFrac L)
    (g := (algebraMap (TotalHat L) (HatFrac L)).comp (hatRingHom hD))
    ((IsFractionRing.injective (TotalHat L) (HatFrac L)).comp (hatRingHom_injective hD hinj))

theorem hatFracLift_toHatFrac {D : Total L →ₐ[L] Total L} (hD : PreservesTotalComp D)
    (hinj : Function.Injective D) (F : TotalHat L) :
    hatFracLift hD hinj (toHatFrac F) = toHatFrac (hatMap hD F) := by
  rw [hatFracLift, IsFractionRing.lift_algebraMap]
  rfl

/-- **The starred raising operator on the ambient of Section 3.7.**
`HJO.Sweep.hatFracDplusStar`: `d^*_+F = cy_{k+1}(τ_{k+1,k+1}(F))`, read where the multiplier lives.

Both factors are homogeneous of degree `0`, so the composite acts on the completion memberwise
(`HJO.Sweep.hatMap`), and it is injective for `u ≠ 0`, so it extends to the fraction field in
exactly one way. The `V̂°_k` is a subring of that field and this map restricts to the
operator `d^*_+` on it. -/
@[hjo "def_mellit_ns_dstar_ext"]
noncomputable def hatFracDplusStar (q : L) {u : L} (hu : u ≠ 0) (k : ℕ) :
    HatFrac L →+* HatFrac L :=
  hatFracLift (preservesTotalComp_dplusStarAlg q u k) (dplusStarAlg_injective q hu k)

theorem hatFracDplusStar_toHatFrac (q : L) {u : L} (hu : u ≠ 0) (k : ℕ) (F : TotalHat L) :
    hatFracDplusStar q hu k (toHatFrac F) = toHatFrac (hatDplusStar q u k F) :=
  hatFracLift_toHatFrac _ _ F

end HatFrac

section ShiftStar

variable {L : Type*} [Field L] [Algebra ℚ L]

/-- **The extended conjugate shift `τ^*_k`.** `HJO.Sweep.nsShiftStarFrac`:
`τ^*_kF = F·E_k`, multiplication by the corner multiplier of `HJO.Sweep.cornerMultiplier`, read on
the ambient of Section 3.7. -/
@[hjo "def_mellit_ns_shift_star_ext"]
noncomputable def nsShiftStarFrac (q u : L) (k : ℕ) (F : HatFrac L) : HatFrac L :=
  F * toHatFrac (cornerMultiplier q u k)

theorem nsShiftStarFrac_apply (q u : L) (k : ℕ) (F : HatFrac L) :
    nsShiftStarFrac q u k F = F * toHatFrac (cornerMultiplier q u k) := rfl

/-- **The starred raising operator against the conjugate shift.**
`HJO.Sweep.hatFracDplusStar_nsShiftStarFrac`: `d^*_+(τ^*_kF) = (1-y_1)τ^*_{k+1}(d^*_+F)`.

`d^*_+` is a ring homomorphism here, so the whole content is its value on the multiplier —
`HJO.Sweep.hatDplusStar_cornerMultiplier`, which is `HJO.Sweep.hatMap_qshift_cornerMultiplier`
followed by `HJO.Sweep.hatMap_cycleShift_cornerMultiplier` — and the rest is the field's own
arithmetic. -/
@[hjo "lem_mellit_ns_dstar_shift_star"]
theorem hatFracDplusStar_nsShiftStarFrac (q : L) {u : L} (hu : u ≠ 0)
    (hq : ∀ r : ℕ, 1 ≤ r → q ^ r ≠ 1) (hu1 : ∀ r : ℕ, 1 ≤ r → u ^ r ≠ 1) (k : ℕ)
    (F : HatFrac L) :
    hatFracDplusStar q hu k (nsShiftStarFrac q u k F)
      = (1 - toHatFrac (auxVarOne L)) *
        nsShiftStarFrac q u (k + 1) (hatFracDplusStar q hu k F) := by
  rw [nsShiftStarFrac_apply, map_mul, hatFracDplusStar_toHatFrac,
    hatDplusStar_cornerMultiplier q u hq hu1 k, nsShiftStarFrac_apply]
  rw [toHatFrac_mul, toHatFrac_sub, toHatFrac_one]
  ring

end ShiftStar

end HJO.Sweep

end
