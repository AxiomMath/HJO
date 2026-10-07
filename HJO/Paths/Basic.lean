/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import QSeriesLib.NumberTheory.QTheory.Defs
public import QSeriesLib.RingTheory.PowerSeries.DiscreteTopology
public meta import HJO.Attr
public import HJO.Paths.Defs

/-! # The area polynomial, the rank shifts and the return paths

A below-diagonal `(aN, bN)`-path is recorded as a vector of heights indexed by a finite type, so
that the paths of a given rank form a `Fintype` and every generating function over them is an
honest `Finset` sum. On that encoding this file defines the area generating polynomial, the rank
shift and the block hook shift, and the paths that return to the diagonal after every block.
-/

@[expose] public section

open Finset PowerSeries
open scoped PowerSeries.DiscreteTopology QTheory

namespace HJO.Paths

/-- Inside the rectangle the height function reads off the entry of the height vector. -/
theorem ht_coe {a b N : ℕ} (y : Heights a b N) (r : Fin (a * N + 1)) :
    ht y (r : ℕ) = (y r : ℕ) :=
  dite_eq_left r.isLt

/-- Past the right endpoint the height function is held at `bN`. -/
theorem ht_of_gt {a b N : ℕ} (y : Heights a b N) {r : ℕ} (hr : a * N < r) : ht y r = b * N :=
  dite_eq_right (by omega)

/-- A height of a candidate `(aN, bN)`-path never exceeds `bN`, the value `bN` held past `aN`
included. -/
theorem ht_le_mul {a b N : ℕ} (y : Heights a b N) (r : ℕ) : ht y r ≤ b * N := by
  rw [ht]
  split
  · exact Nat.lt_succ_iff.mp (y _).isLt
  · exact le_rfl

/-- A height vector whose adjacent heights never come back down has monotone height function.
This reads only the adjacent-step clause, which `IsBelowDiagonal` and `IsAboveDiagonal` share, and
it needs no bound on the indices: past the right endpoint the height function is held at its
maximum `bN`. -/
theorem ht_mono {a b N : ℕ} {y : Heights a b N} (hmono : ∀ r < a * N, ht y r ≤ ht y (r + 1)) :
    Monotone (ht y) := by
  intro r s hrs
  induction s, hrs using Nat.le_induction with
  | base => exact le_rfl
  | succ s hrs ih =>
    rcases Nat.lt_or_ge s (a * N) with hs | hs
    · exact ih.trans (hmono s hs)
    · rw [ht_of_gt y (show a * N < s + 1 by omega)]
      exact ht_le_mul y r

/-- The heights of a below-diagonal path are monotone. -/
theorem IsBelowDiagonal.ht_mono {a b N : ℕ} {y : Heights a b N} (hy : IsBelowDiagonal y) :
    Monotone (ht y) :=
  _root_.HJO.Paths.ht_mono hy.2.2.1

/-- `A_N(q) = ∑_P q^{area(P)}`, the area generating polynomial of all below-diagonal
`(aN, bN)`-paths. At `N = 0` the only path is the empty one, so `A_0(q) = 1`. -/
@[hjo "def_area_poly"]
noncomputable def areaPoly (a b N : ℕ) : ℤ⟦X⟧ :=
  ∑ y ∈ (univ : Finset (Heights a b N)).filter IsBelowDiagonal, X ^ area y

/-- The rank shift `γ_N = d⋅C(N,2)`, with `d = a + b`. -/
@[hjo "def_gamma"]
def gammaShift (a b N : ℕ) : ℕ := (a + b) * N.choose 2

/-- The block hook shift `κ_N = (d-1)⋅C(N,2)`, with `d = a + b`. -/
@[hjo "def_kappa"]
def kappaShift (a b N : ℕ) : ℕ := (a + b - 1) * N.choose 2

/-- `y` lies in `R_N`: a below-diagonal `(aN, bN)`-path passing through `(ka, kb)` for every
`0 ≤ k ≤ N`, that is, returning to the diagonal after every block. -/
@[hjo "def_return_paths"]
def IsReturnPath {a b N : ℕ} (y : Heights a b N) : Prop :=
  IsBelowDiagonal y ∧ ∀ k ≤ N, ht y (a * k) = b * k

/-- Whether a height vector is a below-diagonal path through every `(ka, kb)` with `k ≤ N`, that
is, returning to the diagonal after every block, is decidable. -/
instance instDecidableIsReturnPath {a b N : ℕ} (y : Heights a b N) :
    Decidable (IsReturnPath y) := by
  unfold IsReturnPath; infer_instance

end HJO.Paths
