/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.CMStructure.BraidRepReduce
public import HJO.Shuffle.BraidRep
public import HJO.Shuffle.SlopeWord
public meta import HJO.Attr

/-! # The slope braid

`HJO.Mellit.slopeWord` names the word `β_{m,n}` in the two letters `𝗒`, `𝗓`. Mellit's Section 6
reads it inside the braid monoid, as the element `b_{m,n}` of `𝔹^+_k(𝕋_0)` obtained by substituting
the generators `y_1` and `z_1` of `HJO.Braid.braidGenT` for those letters. That is
`HJO.Braid.slopeBraid`, defined here.

It is the braid-monoid twin of `HJO.Sweep.slopeOperator`, which
substitutes the *operators* `-y_1·` and `(qu)^{-1}z_1` instead. The two are related by the rank-one
braid representation, and `HJO.Sweep.braidRepTotal_slopeBraid_one` says so:
`π_1(b_{m,n}) = Ξ_{m,n}`.
That is the value check on the substitution and on the order of the factors at once, since `π_1` is
a monoid homomorphism and the two letter assignments match on the nose.

## Main definitions

* `HJO.Braid.slopeBraid`.

## Main results

* `HJO.Braid.slopeBraid_one_one` — `b_{1,1} = 1`, the slope word being empty there.
* `HJO.Sweep.braidRepTotal_slopeBraid_one` — `π_1(b_{m,n}) = Ξ_{m,n}` on the total space, where
  `HJO.Sweep.slopeOperator` is typed.
* `HJO.Sweep.coe_braidRep_slopeBraid_one` — the same at `HJO.Sweep.braidRep`'s own codomain
  `HJO.Sweep.pieceSub L 1`, which is where `HJO.Sweep.braidRep` lands.

## Implementation notes

**The order of the factors is load-bearing and is `List.prod`'s.** `HJO.Mellit.slopeWord` is a list
whose head is `λ(m+n-2)` and whose last letter is `λ(1)`, and `List.prod` in a monoid multiplies the
head leftmost — which is "the factors composed in the order in which they are written". This is the
same convention `HJO.Sweep.slopeOperator` fixes, where the head becomes the outermost factor of the
composite; `HJO.Sweep.braidRepTotal_slopeBraid_one` is what checks that the two agree.

The definition is total in `(k, m, n)`: outside the coprime `m, n ≥ 1` and `k ≥ 1`,
`HJO.Mellit.slopeWord` is still a list and the product is still an element, and no statement reads
those values. At `k = 0` every letter is out of rank and `b_{m,n} = 1`, which is `𝔹_0^+(𝕋_0)` being
trivial.

## References

A. Mellit, *Toric
braids and `(m, n)`-parking functions*, §6.
-/

@[expose] public section

namespace HJO.Braid

/-- **The slope braid `b_{m,n}`**, `HJO.Braid.slopeBraid`: for coprime `m, n ≥ 1`
and `k ≥ 1`, the element of `𝔹^+_k(𝕋_0)` obtained from the word `β_{m,n}` of
`HJO.Mellit.slopeWord` by replacing each letter `𝗒` by `y_1` and each letter `𝗓` by `z_1`, the
factors composed in the order in which they are written.

That order is `List.prod`'s: the head of `HJO.Mellit.slopeWord m n` is `λ(m+n-2)` and it is the
leftmost factor. -/
@[hjo "def_mellit_slope_braid"]
def slopeBraid (k m n : ℕ) : BraidMonoid k :=
  ((Mellit.slopeWord m n).map fun l =>
    match l with
    | Mellit.SlopeLetter.y => braidGenY k 1
    | Mellit.SlopeLetter.z => braidGenZ k 1).prod

/-- At `(m, n) = (1, 1)` the slope word is empty and the slope braid is the identity. -/
@[simp]
theorem slopeBraid_one_one (k : ℕ) : slopeBraid k 1 1 = 1 := by
  simp [slopeBraid, Mellit.slopeWord]

end HJO.Braid

namespace HJO.Sweep

open Braid

variable {L : Type*} [Field L] [Algebra ℚ L]

/-- **The rank-one braid representation carries the slope braid to the slope operator**:
`π_1(b_{m,n}) = Ξ_{m,n}`.

`HJO.Sweep.slopeOperator` is described as "the image of `β_{m,n}` under the
rank-one case of `HJO.Sweep.braidRep`", and this is that sentence as a theorem. Both sides are the
product of the same list of letters read through assignments that agree — `y_1 ↦ -y_1·` is
`HJO.Sweep.braidRepTotal_one_y1` and `z_1 ↦ (qu)^{-1}z_1` is
`HJO.Sweep.braidRepTotal_one_z1` — and `π_1` exists with no hypothesis
(`HJO.Sweep.braidRepRespectsTotal_one`). In particular the order of the
factors is the same in the two definitions. -/
theorem braidRepTotal_slopeBraid_one (q u : L) {r : L} (hq : q ≠ 0) (hr : r * r = q) (m n : ℕ) :
    braidRepTotal q u r 1 (braidRepRespectsTotal_one q u hq hr) (slopeBraid 1 m n)
      = slopeOperator q u 1 m n := by
  rw [slopeBraid, slopeOperator, map_list_prod, List.map_map]
  congr 1
  refine List.map_congr_left fun l _ => ?_
  cases l with
  | y => exact braidRepTotal_one_y1 q u r _
  | z => exact braidRepTotal_one_z1 q u r _

/-- **The same at `HJO.Sweep.braidRep`'s own codomain**: on `V_1` the retyped rank-one
representation carries `b_{m,n}` to `Ξ_{m,n}`, read through the inclusion `V_1 ↪ V_*`. The two
typings agree by `HJO.Sweep.coe_braidRep`, and rank `1` is exactly where both hypotheses are free
(`HJO.Sweep.braidRepRespects_one`, `HJO.Sweep.braidRepRespectsTotal_one`). So
`HJO.Sweep.slopeOperator`'s rank-one claim survives the retyping unweakened. -/
theorem coe_braidRep_slopeBraid_one (q u : L) {r : L} (hq : q ≠ 0) (hr : r * r = q) (m n : ℕ)
    (x : pieceSub L 1) :
    (braidRep q u r 1 (braidRepRespects_one q u hq hr) (slopeBraid 1 m n) x : Total L)
      = slopeOperator q u 1 m n x := by
  rw [coe_braidRep q u r 1 _ (braidRepRespectsTotal_one q u hq hr),
    braidRepTotal_slopeBraid_one q u hq hr m n]

end HJO.Sweep
