/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Mathlib.Order.Interval.Finset.Nat
public meta import HJO.Attr

/-! # The reverse of a descent set

A descent set in degree `n` is a subset of `{1, …, n-1}`, recorded here — as everywhere in this
library, where `HJO.ParkingFunctions.ides` produces one and `HJO.ParkingFunctions.gessel`
consumes one — as a `Finset ℕ` contained in `Finset.Ico 1 n`. Reflecting the degree-`n` window
about its centre, `j ↦ n - j`, carries such a set to another one; the result is written `S^{∨n}` and
called the reverse of `S`. It is the reversal half of the conjugation
`S ↦ ({1, …, n-1} \ S)^{∨n}` under which Gessel's involution `ω` permutes the fundamental
quasisymmetric functions, and it is also how the half turn of the `aN × bN` rectangle acts on
inverse descent sets, which is where the above-diagonal form of the shuffle identity meets the
below-diagonal one.

## Main definitions

* `HJO.ParkingFunctions.descentReverse`: `S^{∨n} = {n - j : j ∈ S}`.

## Main results

* `HJO.ParkingFunctions.mem_descentReverse`: `i ∈ S^{∨n} ↔ ∃ j ∈ S, n - j = i`.
* `HJO.ParkingFunctions.descentReverse_Ico`: the reflection fixes the degree-`n` window,
  `{1, …, n-1}^{∨n} = {1, …, n-1}`.
* `HJO.ParkingFunctions.descentReverse_subset_Ico`: hence it maps a subset of that window
  back into it.

## Implementation notes

The definition is total: it neither assumes `1 ≤ n` nor `S ⊆ Ico 1 n`, since neither is needed to
form the image, and a hypothesis the value does not use would only be carried by every call site.
Outside that window the truncated subtraction of `ℕ` takes over — every `j > n` is sent to `0` —
so the statements that need the reflection to be a bijection of the window,
`descentReverse_subset_Ico` and involutivity, carry the containment as a hypothesis.

The reflection is the literal `j ↦ n - j` rather than `Polynomial.revAt n`, whose
`if i ≤ n then n - i else i` agrees with it on the window but not off it; the involutivity of the
former on `Ico 1 n` is `Nat.sub_sub_self`.
-/

@[expose] public section

open Finset

namespace HJO.ParkingFunctions

/-- `S^{∨n}`, the reverse of the degree-`n` descent set `S`: the image `{n - j : j ∈ S}` of `S`
under the reflection `j ↦ n - j` of the window `{1, …, n-1}` about its centre. -/
@[hjo "def_set_reverse"]
def descentReverse (n : ℕ) (S : Finset ℕ) : Finset ℕ :=
  S.image (n - ·)

/-- An element of the reverse of `S` is a reflected element of `S`. -/
@[simp]
theorem mem_descentReverse {n i : ℕ} {S : Finset ℕ} :
    i ∈ descentReverse n S ↔ ∃ j ∈ S, n - j = i :=
  mem_image

/-- The reflection fixes the whole degree-`n` window: `{1, …, n-1}^{∨n} = {1, …, n-1}`. -/
@[simp]
theorem descentReverse_Ico (n : ℕ) : descentReverse n (Ico 1 n) = Ico 1 n := by
  obtain _ | n := n
  · simp [descentReverse]
  · simpa [descentReverse] using Nat.Ico_image_const_sub_eq_Ico (b := n + 1) n.succ_pos

/-- The reflection maps a subset of the degree-`n` window `{1, …, n-1}` back into that window. -/
theorem descentReverse_subset_Ico {n : ℕ} {S : Finset ℕ} (hS : S ⊆ Ico 1 n) :
    descentReverse n S ⊆ Ico 1 n :=
  (image_subset_image hS).trans (descentReverse_Ico n).subset

end HJO.ParkingFunctions
