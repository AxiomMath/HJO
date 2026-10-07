/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.Shuffle.BraidWords

/-! # The label inversions of special-braid data

A piece of special-braid data starts at the position tuple `v` and ends at
`(nx_θ^{α_i - 1}(v_i))_i`. Each tuple labels its entries by rank, and the two labellings differ by a
permutation; `HJO.Mellit.invFin_eq_invIni_of_separatesDiagonal` compares the inversion counts of the
two, and the `q`-power of `HJO.Mellit.braidValueColouring_eq_dsc_floor` is read off their
difference.

## Main results

* `HJO.Braid.tupleInversions` — the inversion count of the rank function of a tuple.
* `HJO.Braid.invIni`.
* `HJO.Braid.invFin`.
* `HJO.Braid.tupleInversions_eq_card_lt` — the ranks may be dropped: an inversion of the rank
  function is an inversion of the tuple, because `HJO.Braid.entryRank_lt_entryRank_iff` says the
  rank reflects the order.

## Implementation notes

Both definitions take the pair `(v, α)` and the whole position pair, and read the
inversion count off one member of it; `α` is inert in `HJO.Braid.invIni` and enters
`HJO.Braid.invFin` only through `HJO.Braid.positionPair`. The arguments are kept in this
form so that the two definitions take the same arguments, with
`HJO.Braid.invIni_eq_tupleInversions` recording that the first does not read `α`.

The index pairs are counted over `Fin k × Fin k`, the `i < j`.

## References

This file works with `HJO.Braid.invIni`, `HJO.Braid.invFin`, `HJO.Braid.positionPair`,
`HJO.Braid.entryRank`, `HJO.Braid.IsSpecialBraidData`,
`HJO.Mellit.invFin_eq_invIni_of_separatesDiagonal` and
`HJO.Mellit.braidValueColouring_eq_dsc_floor`.
-/

@[expose] public section

open Finset

namespace HJO.Braid

/-- The number of pairs `i < j` at which the rank function of `w` is inverted, `rk_w(i) > rk_w(j)`.
This is the count both definitions below take, of the two tuples of
`HJO.Braid.positionPair`. -/
def tupleInversions {k : ℕ} (w : Fin k → ℚ) : ℕ :=
  #{p ∈ (univ : Finset (Fin k × Fin k)) | p.1 < p.2 ∧ entryRank w p.2 < entryRank w p.1}

/-- **The ranks may be dropped.** An inversion of the rank function is an inversion of the tuple
itself: `HJO.Braid.entryRank_lt_entryRank_iff` says the rank reflects the order, with no injectivity
needed. -/
theorem tupleInversions_eq_card_lt {k : ℕ} (w : Fin k → ℚ) :
    tupleInversions w = #{p ∈ (univ : Finset (Fin k × Fin k)) | p.1 < p.2 ∧ w p.2 < w p.1} := by
  rw [tupleInversions]
  exact Finset.card_nbij id (fun p hp => by
      obtain ⟨-, h1, h2⟩ := Finset.mem_filter.1 hp
      exact Finset.mem_filter.2 ⟨Finset.mem_univ _, h1,
        (entryRank_lt_entryRank_iff w p.2 p.1).1 h2⟩)
    (Function.injective_id.injOn)
    (fun p hp => by
      obtain ⟨-, h1, h2⟩ := Finset.mem_filter.1 hp
      exact ⟨p, Finset.mem_filter.2 ⟨Finset.mem_univ _, h1,
        (entryRank_lt_entryRank_iff w p.2 p.1).2 h2⟩, rfl⟩)

/-- There is no inversion in a tuple of length at most one. -/
@[simp]
theorem tupleInversions_zero (w : Fin 0 → ℚ) : tupleInversions w = 0 := by
  simp [tupleInversions]

/-- **The initial label inversions.** `HJO.Braid.invIni`: for special-braid
data `(v, α)` with position pair `(v, v^fin)`, the number of pairs `i < j` with
`rk_v(i) > rk_v(j)`. -/
@[hjo "def_braid_inv_initial"]
def invIni (θ : ℚ) {k : ℕ} (v : Fin k → ℚ) (α : Fin k → ℕ) : ℕ :=
  tupleInversions (positionPair θ v α).1

/-- **The final label inversions.** `HJO.Braid.invFin`: the number of pairs
`i < j` with `rk_{v^fin}(i) > rk_{v^fin}(j)`, where `v^fin` is the second member of the position
pair. -/
@[hjo "def_braid_inv_final"]
def invFin (θ : ℚ) {k : ℕ} (v : Fin k → ℚ) (α : Fin k → ℕ) : ℕ :=
  tupleInversions (positionPair θ v α).2

/-- The initial count reads only `v`, the first member of the position pair being `v` itself; `θ`
and `α` are carried because the definition is stated for special-braid data. -/
theorem invIni_eq_tupleInversions (θ : ℚ) {k : ℕ} (v : Fin k → ℚ) (α : Fin k → ℕ) :
    invIni θ v α = tupleInversions v := rfl

/-- The final count reads the tuple of last iterates. -/
theorem invFin_eq_tupleInversions (θ : ℚ) {k : ℕ} (v : Fin k → ℚ) (α : Fin k → ℕ) :
    invFin θ v α = tupleInversions fun i => (nextCrossing θ)^[α i - 1] (v i) := rfl

/-- **At multiplicity `1` everywhere the two counts agree**, the final position tuple then being
the initial one. This is the degenerate case of `HJO.Mellit.invFin_eq_invIni_of_separatesDiagonal`,
whose content is that the two agree in the minimal-gap case as well. -/
theorem invFin_eq_invIni_of_mult_eq_one (θ : ℚ) {k : ℕ} (v : Fin k → ℚ) {α : Fin k → ℕ}
    (h : ∀ i, α i = 1) : invFin θ v α = invIni θ v α := by
  rw [invFin, invIni, positionPair_fst]
  congr 1
  exact funext fun i => positionPair_snd_of_mult_eq_one (h i)

end HJO.Braid
