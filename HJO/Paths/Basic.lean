/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import QSeriesLib.NumberTheory.QTheory.Defs
public import QSeriesLib.RingTheory.PowerSeries.DiscreteTopology
public meta import HJO.Attr
public import HJO.Defs

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
