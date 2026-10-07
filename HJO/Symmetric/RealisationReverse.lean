/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.Paths.ReverseDescent
public meta import HJO.Attr

/-! # Reversing the letters of a realisation

Reflecting the degree-`n` window `{1, …, n-1}` about its centre, `j ↦ n - j`, is an involution of
that window, so `S ↦ S^{∨n}` (`HJO.ParkingFunctions.descentReverse`) is an involution of the
descent sets of degree `n`. This is what makes Gessel's conjugation `S ↦ ({1, …, n-1} \ S)^{∨n}` —
under which `ω` permutes the fundamental quasisymmetric functions — a bijection, and it is what
lets the half turn of the `aN × bN` rectangle be undone.

## Main results

* `HJO.ParkingFunctions.descentReverse_descentReverse`: `(S^{∨n})^{∨n} = S` whenever every element
  of `S` is at most `n`.

## Implementation notes

The statement is usually made for `n ≥ 1` and `S ⊆ {1, …, n-1}`; the conclusion needs neither. In
`ℕ` the reflection is truncated subtraction, which is its own inverse exactly on `{0, …, n}`: for
`j ≤ n` one has `n - (n - j) = j` (`Nat.sub_sub_self`), while for `j > n` the subtraction collapses,
`n - j = 0` and so `n - (n - j) = n`, not `j`. The hypothesis recorded is therefore
`S ⊆ Finset.Iic n`, which every descent set of degree `n` meets:
`hS.trans Finset.Ico_subset_Iic_self` turns `S ⊆ Finset.Ico 1 n` into it. `n = 0` is not excluded;
there the hypothesis reads `S ⊆ {0}` and the conclusion still holds.

That hypothesis cannot be dropped, and is not an artefact of the encoding: every element of
`(S^{∨n})^{∨n}` is of the form `n - a`, hence at most `n`, so the conclusion itself forces
`S ⊆ Finset.Iic n`. The collapse above, at `n = 3` and `j = 5`, reads `{5}^{∨3} = {0}` and
`{0}^{∨3} = {3}`.
-/

@[expose] public section

open Finset

namespace HJO.ParkingFunctions

/-- Reversing a degree-`n` descent set twice returns it: `(S^{∨n})^{∨n} = S` whenever every
element of `S` is at most `n`, hence for every `S ⊆ {1, …, n-1}`. -/
@[hjo "lem_set_reverse_involutive"]
theorem descentReverse_descentReverse {n : ℕ} {S : Finset ℕ} (hS : S ⊆ Finset.Iic n) :
    descentReverse n (descentReverse n S) = S := by
  simp only [descentReverse, image_image]
  exact (image_congr fun j hj => Nat.sub_sub_self (mem_Iic.1 (hS hj))).trans image_id

end HJO.ParkingFunctions
