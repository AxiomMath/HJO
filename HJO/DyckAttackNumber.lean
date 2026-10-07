/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.DyckAttackSets
public meta import HJO.Attr

/-! # The attack number of a square Dyck path

One definition, `HJO.Dyck.attackNumber`: `at(π) = #At(π)`, the number of cells between the path
and the main diagonal. It is the exponent the involution on characteristic functions carries,
`ι(ω̄f) = (-1)^n q^{-at(π)}χ(π)`.

## Main definitions

* `HJO.Dyck.attackNumber`: `at(π)`.

## Implementation notes

Carlsson and Mellit write `area(π)` for this count and `Area(π)` for the set; both names are already
in use in this library for statistics of rectangular paths, so they are renamed here to the attack
set and the attack number, and `HJO.Dyck.attackSet` is the set.

No hypothesis is imposed on the sequence: `attackSet` is total, and a path being a square Dyck path
is a hypothesis of the lemmas about `at(π)` rather than of the definition.

`attackNumber_eq_sum` presents the count by rows, which is the form in which it is compared with the
coarea of a path: row `k` contributes `k - x k` cells.

## References

The definition `HJO.Dyck.attackNumber` transcribes E. Carlsson and A. Mellit, *A proof of the
shuffle conjecture*, §3.1.
-/

@[expose] public section

open Finset

namespace HJO.Dyck

/-- **The attack number** `at(π) = #At(π)` of the sequence `x`: the number
of cells of the attack set, which for a square Dyck path with coarea sequence `x` is the number of
cells lying between the path and the main diagonal. -/
@[hjo "def_dyck_attack_number"]
def attackNumber {n : ℕ} (x : Fin n → ℕ) : ℕ := #(attackSet x)

variable {n : ℕ} {x : Fin n → ℕ}

/-- The attack number by rows: row `k` contributes the cells `x k, …, k - 1`, so `k - x k` of them,
truncated where the row is empty. -/
theorem attackNumber_eq_sum (x : Fin n → ℕ) :
    attackNumber x = ∑ k : Fin n, ((k : ℕ) - x k) := by
  classical
  rw [attackNumber, attackSet, card_biUnion]
  · exact Finset.sum_congr rfl fun k _ => by
      rw [card_product, card_singleton, mul_one, Nat.card_Ico]
  · intro k _ l _ hkl
    refine disjoint_left.2 fun p hp hp' => hkl ?_
    rw [mem_product, mem_singleton] at hp hp'
    exact Fin.ext (hp.2.symm.trans hp'.2)

/-- A path of length `0` has no attacking cells. -/
@[simp]
theorem attackNumber_of_isEmpty (x : Fin 0 → ℕ) : attackNumber x = 0 := by
  rw [attackNumber_eq_sum]
  exact Finset.sum_of_isEmpty _

end HJO.Dyck
