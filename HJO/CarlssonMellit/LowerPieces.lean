/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.CarlssonMellit.PartialCharSeries
public import HJO.CarlssonMellit.Tuples
public meta import HJO.Attr

/-! # The pieces of the lowered characteristic series

`HJO.Dyck.lowerCharPiece`: for a partial Dyck path `π ∈ 𝔻_{k,N}` of level `k = m + 1 ≥ 1` and
`r ≥ 0`,

`μ_r(π) = ∑_{w ∈ U(π, σ^{[r]})} q ^ inv(At(π), w) · z^{(k)}_{w,♭} ∈ P_k`,

the sum over the no-attack labellings whose first `k` letters are the entries of the lower tuple
`σ^{[r]} = (1, …, k-1, k+r)` of `HJO.Dyck.lowerTuple`. The lowering recursion of Carlsson and
Mellit's Section 4 splits the characteristic series of the path at the level `k - 1` into these
pieces, one for each value of the freed label, and this file names them.

## Main definitions

* `HJO.Dyck.lowerCharPiece`: `μ_r(π)`.

## Main results

* `HJO.Dyck.lowerCharPiece_eq_partialCharSeries`: `μ_r(π) = ν_{σ^{[r]}}(π)`, the definition.
* `HJO.Dyck.coeff_lowerCharPiece`: the coefficient of a monomial.
* `HJO.Dyck.coeff_lowerCharPiece_eq_coeff_sum`: `μ_r(π)` is the displayed sum of the monomials
  `HJO.Sym.ztail`, restricted to the no-attack labellings with the lower tuple prescribed.

## Implementation notes

*`μ_r(π)` is `ν_σ(π)` at `σ = σ^{[r]}`, and is nevertheless its own declaration.* The display for
`μ_r` is the display for `HJO.Dyck.partialCharSeries` with the lower tuple substituted, so no second
construction is needed: the justification that the sum lies in `P_k` — each summand a scalar times a
monomial of the single total degree `N - k`, each monomial reached by finitely many labellings — is
the one `HJO.Dyck.partialCharSeries` is built on. What is new is the *name*: the lowering recursion
reads the whole family `r ↦ μ_r(π)` at once, so the family needs a head symbol of its own.

*The level is `m + 1` and not `k`*, because the lower tuple is: `HJO.Dyck.lowerTuple m r` is a tuple
of `m + 1` entries, `(0, 1, …, m-1, m+r)` on the layer's `0`-based labels, so the condition `k ≥ 1`
is carried in the shape of the type rather than as a hypothesis.

*The index `r` is the last explicit argument*, so that the family the lowering recursion sums is
`HJO.Dyck.lowerCharPiece q m x` with no abstraction. That recursion,
`HJO.Dyck.insertFront_partialCharSeries_identityTuple`, is what fixes this shape: it states
`Φ_{k-1}(ν_{Id_{k-1}}(π)) = ∑_{r ≥ 0} z^{(k)}_{k+r} μ_r(π)` with the right-hand side monomialwise
finite, so it needs the pieces as a single `ℕ`-indexed family in `P_k`, and it obtains them by
splitting a sum over `U(π, Id_{k-1})` along the partition into the sets `U(π, σ^{[r]})` — which is
only a splitting of `ν` if `μ_r` is `ν_{σ^{[r]}}` on the nose.

*No hypothesis on `x`, on `r` or on `m + 1 ≤ N`*, as for `HJO.Dyck.partialCharSeries`: the series
reads `x` only through its attack set, so `π ∈ 𝔻_{k,N}` is a hypothesis of the lemmas about
`μ_r(π)` and not of the definition.

## References

E. Carlsson and A. Mellit, *A proof of the shuffle conjecture*, J. Amer. Math. Soc. **31** (2018)
661--697, Section 4, whose `χ'_{k,r}(π)` is `y_1 ⋯ y_{k-1} z^{(k)}_{k+r} μ_r(π)`.
-/

@[expose] public section

open Finset HJO.Sym

namespace HJO.Dyck

variable {K : Type*} [CommRing K] {N m : ℕ}

/-- **The `r`-th piece `μ_r(π)` of the lowered characteristic series**,

`μ_r(π) = ∑_{w ∈ U(π, σ^{[r]})} q ^ inv(At(π), w) · z^{(k)}_{w,♭} ∈ P_k`,

the sum over the no-attack labellings of `π` whose first `k = m + 1` letters are prescribed by the
lower tuple `σ^{[r]} = (1, …, k-1, k+r)`, each weighted by `q` to the number of attacking pairs it
inverts and by the free part of its labelling monomial.

This is the characteristic series `HJO.Dyck.partialCharSeries` at the prescription
`HJO.Dyck.lowerTuple m r`: the display for `μ_r` is its display for `ν_σ` with that
tuple substituted, and the reason the sum lies in `P_k` — each summand a scalar multiple of a
monomial of the single total degree `N - k`, and each monomial of that degree reached by finitely
many labellings — is the reason `partialCharSeries` is coefficientwise. The name exists because the
lowering recursion reads the whole family `r ↦ μ_r(π)`, which it sums against the merged variables
`z^{(k)}_{k+r}`. -/
@[hjo "def_cm_mu"]
noncomputable def lowerCharPiece (q : K) (m : ℕ) {N : ℕ} (x : Fin N → ℕ) (r : ℕ) :
    AuxAlphabetSeries K (m + 1) :=
  partialCharSeries q (m + 1) x (lowerTuple m r)

variable {q : K} {x : Fin N → ℕ} {r : ℕ} {e : ℕ →₀ ℕ}

/-- **`μ_r(π)` is the characteristic series at the lower tuple**: `μ_r(π) = ν_{σ^{[r]}}(π)`. This is
the definition, and it is the form in which the lowering recursion splits a sum over
`U(π, Id_{k-1})` into the pieces. -/
theorem lowerCharPiece_eq_partialCharSeries :
    lowerCharPiece q m x r = partialCharSeries q (m + 1) x (lowerTuple m r) :=
  rfl

/-- **The defining property of `μ_r(π)`**: the coefficient of the monomial with alphabet exponent
`e` is the finite sum of `q ^ inv(At(π), w) · z^{(k)}_{w,♭}` over the no-attack labellings `w` with
the lower tuple prescribed whose free part has that exponent. -/
theorem coeff_lowerCharPiece :
    MvPowerSeries.coeff e (lowerCharPiece q m x r) =
      ∑ w ∈ {w ∈ Fintype.piFinset fun _ : Fin N => nuLetters (m + 1) e (lowerTuple m r) |
          w ∈ noAttackLabellings x (lowerTuple m r) ∧ ztailExponent (m + 1) w = e},
        q ^ #(invSet (finPairs N (attackSet x)) w) • ztailCoeff K (m + 1) w :=
  coeff_partialCharSeries

/-- **`μ_r(π)` is the sum** `∑_{w ∈ U(π, σ^{[r]})} q ^ inv(At(π), w) z^{(k)}_{w,♭}`: on
the monomials with alphabet exponent `e` it agrees with the honest *finite* sum of
`q ^ inv(At(π), w) · z^{(k)}_{w,♭}` over the no-attack labellings with letters in any finite set
containing `HJO.Dyck.nuLetters (m + 1) e (lowerTuple m r)`. Every exponent is covered by some such
set, so this identifies `μ_r(π)` with the displayed series; the sum over all of
`U(π, σ^{[r]})` cannot be formed in `P_k`, which is why the definition is coefficientwise. -/
theorem coeff_lowerCharPiece_eq_coeff_sum {s : Finset ℕ}
    (hs : nuLetters (m + 1) e (lowerTuple m r) ⊆ s) :
    MvPowerSeries.coeff e (lowerCharPiece q m x r) =
      MvPowerSeries.coeff e (∑ w ∈ {w ∈ Fintype.piFinset fun _ : Fin N => s |
          w ∈ noAttackLabellings x (lowerTuple m r)},
        q ^ #(invSet (finPairs N (attackSet x)) w) • ztail K (m + 1) w) :=
  coeff_partialCharSeries_eq_coeff_sum hs

end HJO.Dyck
