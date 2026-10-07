/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.Shuffle.Colouring

/-! # An admissible level is the rank of no lattice point, and every rank is isolated by two

The sweep is driven downwards through the rectangle by a level `η`, and the recursion of Mellit's
Theorem 4.2 steps it past one lattice point at a time. Two facts make that possible, and both are
arithmetic rather than geometric: a half-integer level is never itself the rank of a lattice point,
and the two half-integers on either side of a rank isolate it, no other rank lying strictly between
them.

## Main results

* `HJO.Mellit.pointRank_ne_of_isAdmissibleLevel`.
* `HJO.Mellit.exists_isolating_isAdmissibleLevel`.

## Implementation notes

The statements are restricted to the lattice points `(x, y)` of the rectangle, `0 ≤ x ≤ aN` and
`0 ≤ y ≤ bN`. Neither restriction is used: the rank is an integer at every point of `ℕ × ℕ`, and
that is the whole argument. The hypotheses are carried all the same, so that each statement has its
natural form, and are named with a leading underscore to record that they are inert.

## References

This file formalises `HJO.Mellit.IsAdmissibleLevel` and proves
`HJO.Mellit.pointRank_ne_of_isAdmissibleLevel` and `HJO.Mellit.exists_isolating_isAdmissibleLevel`,
about the rank `HJO.ParkingFunctions.abovePointRank`.
-/

@[expose] public section

namespace HJO.Mellit

open ParkingFunctions Paths Sweep

variable {a b N : ℕ}

/-- **An admissible level is the rank of no lattice point.**
`HJO.Mellit.pointRank_ne_of_isAdmissibleLevel`: no lattice point `(x, y)` with `0 ≤ x ≤ aN` and
`0 ≤ y ≤ bN` has `rk̂(x, y)` equal to an admissible level.

The above-diagonal rank is an integer and an admissible level is a half-integer, so the two never
meet; the bounds on the point play no part, and are carried only so that the statement has its
natural form. -/
@[hjo "lem_colouring_level_not_rank"]
theorem pointRank_ne_of_isAdmissibleLevel {η : ℚ} (hη : IsAdmissibleLevel η) (a b N : ℕ)
    {P : ℕ × ℕ} (_hx : P.1 ≤ a * N) (_hy : P.2 ≤ b * N) :
    ((pointRank a b N P : ℤ) : ℚ) ≠ η := by
  obtain ⟨n, rfl⟩ := hη
  intro h
  have h2 : ((2 * pointRank a b N P : ℤ) : ℚ) = ((2 * n + 1 : ℤ) : ℚ) := by
    push_cast
    linarith
  have h3 : 2 * pointRank a b N P = 2 * n + 1 := by exact_mod_cast h2
  omega

/-- **Every lattice point is isolated by a pair of admissible levels.**
`HJO.Mellit.exists_isolating_isAdmissibleLevel`: for a lattice point `P` of the rectangle there are
admissible levels `η₋ < rk̂(P) < η₊` such that `rk̂(P)` is the only value taken by `rk̂` on such
lattice points strictly between `η₋` and `η₊`.

The witnesses are `rk̂(P) ± 1/2`. An integer strictly between them equals `rk̂(P)`, and every rank
is an integer, so no other value can occur — and again the bounds on the points play no part, the
conclusion holding for every lattice point of `ℕ × ℕ`.

The conclusion is an equality of *ranks*, not of points: "the only value taken by `rk̂`". That the
point itself is then forced needs the injectivity of the rank, which is
`HJO.Mellit.pointRank_inj_of_mem_sweptRegion` and holds only for `0 < a`. -/
@[hjo "lem_colouring_level_isolates"]
theorem exists_isolating_isAdmissibleLevel (a b N : ℕ) {P : ℕ × ℕ}
    (_hx : P.1 ≤ a * N) (_hy : P.2 ≤ b * N) :
    ∃ ηlo ηhi : ℚ, IsAdmissibleLevel ηlo ∧ IsAdmissibleLevel ηhi ∧
      ηlo < ((pointRank a b N P : ℤ) : ℚ) ∧ ((pointRank a b N P : ℤ) : ℚ) < ηhi ∧
      ∀ Q : ℕ × ℕ, Q.1 ≤ a * N → Q.2 ≤ b * N →
        ηlo < ((pointRank a b N Q : ℤ) : ℚ) → ((pointRank a b N Q : ℤ) : ℚ) < ηhi →
          pointRank a b N Q = pointRank a b N P := by
  refine ⟨(pointRank a b N P : ℚ) - 1 / 2, (pointRank a b N P : ℚ) + 1 / 2,
    ⟨pointRank a b N P - 1, by push_cast; ring⟩, ⟨pointRank a b N P, by norm_num⟩,
    by norm_num, by norm_num, fun Q _ _ hlo hhi => ?_⟩
  have h1 : ((pointRank a b N Q : ℤ) : ℚ) < ((pointRank a b N P + 1 : ℤ) : ℚ) := by
    push_cast
    linarith
  have h2 : ((pointRank a b N P - 1 : ℤ) : ℚ) < ((pointRank a b N Q : ℤ) : ℚ) := by
    push_cast
    linarith
  have h1' : pointRank a b N Q < pointRank a b N P + 1 := by exact_mod_cast h1
  have h2' : pointRank a b N P - 1 < pointRank a b N Q := by exact_mod_cast h2
  omega

end HJO.Mellit
