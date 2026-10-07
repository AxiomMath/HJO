/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Mathlib.Data.Fintype.Inv
public import QSeriesLib.NumberTheory.QTheory.Defs
public import QSeriesLib.RingTheory.PowerSeries.DiscreteTopology
public import HJO.Symmetric.Defs
public meta import HJO.Attr

/-! # Below-diagonal paths and rational parking functions

A below-diagonal `(aN, bN)`-path recorded as a vector of heights indexed by a finite type, with its
area, arms, legs and hook count, and the rational parking functions on it with their ranks,
temporary dinv, rational dinv, reading word and inverse descent set, and Gessel's fundamental
quasisymmetric functions.
-/

@[expose] public section

open Finset PowerSeries
open scoped QTheory PowerSeries.DiscreteTopology

namespace HJO.Paths

open Finset

/-! ### Below-diagonal paths and their statistics -/

/-- The height vectors of a candidate `(aN, bN)`-path: a height in `{0, …, bN}` for each
horizontal coordinate in `{0, …, aN}`. The geometric interpretations of the path statistics
below apply to vectors satisfying `IsBelowDiagonal`; their definitions remain total on all
candidate height vectors. -/
abbrev Heights (a b N : ℕ) := Fin (a * N + 1) → Fin (b * N + 1)

/-- The height `y_r` of `y` at horizontal coordinate `r`, held at `bN` for `r > aN`. -/
def ht {a b N : ℕ} (y : Heights a b N) (r : ℕ) : ℕ :=
  if h : r < a * N + 1 then (y ⟨r, h⟩ : ℕ) else b * N

/-- `y` is a below-diagonal `(aN, bN)`-path: `0 = y_0 ≤ y_1 ≤ ⋯ ≤ y_{aN} = bN` with
`y_r ≤ ⌊br/a⌋`, the last condition written multiplicatively as `a y_r ≤ b r`. -/
@[hjo "def_dyck_path"]
def IsBelowDiagonal {a b N : ℕ} (y : Heights a b N) : Prop :=
  ht y 0 = 0 ∧ ht y (a * N) = b * N ∧ (∀ r < a * N, ht y r ≤ ht y (r + 1)) ∧
    ∀ r ≤ a * N, a * ht y r ≤ b * r

/-- Whether a height vector is a below-diagonal `(aN, bN)`-path is decidable. -/
instance instDecidableIsBelowDiagonal {a b N : ℕ} (y : Heights a b N) :
    Decidable (IsBelowDiagonal y) := by
  unfold IsBelowDiagonal; infer_instance

/-- The area of a path: the number `∑_{r=1}^{aN-1} (⌊br/a⌋ - y_r)` of full lattice squares
between it and the diagonal. On paths satisfying `IsBelowDiagonal`, the column bounds make
every difference nonnegative before the natural subtraction is applied. -/
@[hjo "def_area"]
def area {a b N : ℕ} (y : Heights a b N) : ℕ := ∑ r ∈ Ico 1 (a * N), (b * r / a - ht y r)

/-- `A_i = min {r : y_r ≥ i}`, the first coordinate at which `y` reaches height `i`, taken to
be `aN` when no coordinate does. -/
def firstReach {a b N : ℕ} (y : Heights a b N) (i : ℕ) : ℕ :=
  ((List.range (a * N + 1)).find? fun r => i ≤ ht y r).getD (a * N)

/-- The arm `r - A_i` of the cell `(r, i)`, the number of cells strictly to its left in its
row of the diagram cut out by `y`. The subtraction is truncated, which is harmless on the
cells with `1 ≤ i ≤ y_r`. -/
@[hjo "def_arm_leg"]
def arm {a b N : ℕ} (y : Heights a b N) (r i : ℕ) : ℕ := r - firstReach y i

/-- The leg `y_r - i` of the cell `(r, i)`, the number of cells strictly above it in its
column of the diagram cut out by `y`. -/
def leg {a b N : ℕ} (y : Heights a b N) (r i : ℕ) : ℕ := ht y r - i

/-- The hook count `h(P)`: the number of cells `(r, i)` with `1 ≤ r < aN` and `1 ≤ i ≤ y_r`
whose arm and leg satisfy `b⋅arm ≤ a(leg + 1)` and `a⋅leg < b(arm + 1)`. The first inequality
is weak and the second strict. -/
@[hjo "def_hook_count"]
def hookCount {a b N : ℕ} (y : Heights a b N) : ℕ :=
  #{p ∈ Ico 1 (a * N) ×ˢ Icc 1 (b * N) | p.2 ≤ ht y p.1 ∧
      b * arm y p.1 p.2 ≤ a * (leg y p.1 p.2 + 1) ∧ a * leg y p.1 p.2 < b * (arm y p.1 p.2 + 1)}

/-- `y` is a below-diagonal path whose return composition is `α`: the parts of `α` are
positive and sum to `N`, and the ranks `0 = k_0 < k_1 < ⋯ < k_ℓ = N` with `y_{ka} = kb` are
*exactly* the partial sums of `α`, so a path with an unrequested return is excluded. -/
@[hjo "def_path_returns"]
def HasReturns {a b N : ℕ} (α : List ℕ) (y : Heights a b N) : Prop :=
  IsBelowDiagonal y ∧ (∀ x ∈ α, 0 < x) ∧ α.sum = N ∧
    ∀ k ≤ N, (ht y (a * k) = b * k ↔ k ∈ α.scanl (· + ·) 0)

/-- Whether a height vector is a below-diagonal path whose return composition is `α` is
decidable. -/
instance instDecidableHasReturns {a b N : ℕ} (α : List ℕ) (y : Heights a b N) :
    Decidable (HasReturns α y) := by
  unfold HasReturns; infer_instance

end HJO.Paths

namespace HJO.ParkingFunctions

open Finset

/-! ### Parking functions in the rectangle and their statistics -/

/-- The signed rank `P(x,y) = (aN + 1)(a*y - b*x) + x`. Put `m = aN`, `n = bN`, `C = m + 1` and
`A(x,y) = a*y - b*x`. For `N > 0`, the rank `R_i` of a north step in §4.2 (The compositional theorem
and sign extraction) of *Rogers-Ramanujan identities from the geometry of `X^a = Y^b`* is
`N*A(x,y) + x/C`, not `A(x,y) + x/C`: `P` is not simply its denominator-cleared value when `N > 1`.
Nevertheless their order and window comparisons agree on the rectangle.

Indeed `|Δx| ≤ m < C`, so `C*ΔA + Δx` and `C*N*ΔA + Δx` have the same sign, determined by
`(ΔA, Δx)` in lexicographic order. Replacing `ΔA` by `ΔA - a` gives the upper-window comparison:
the window `C*a` for `P` agrees with the paper's window `m = N*a`. Both strict endpoints are
preserved, including equal integral ranks and integral-rank differences exactly `a`.
For `a > 0`, `P` increases up each column, making rank-ordered labelling legal.

Rotating to the paper's above-diagonal path sends a north-step foot `(x, y)` to
`(m - x, n - 1 - y)`, where the paper's rank is `-N*A(x,y) - x/C - m²/C`. Thus rotation reverses
the rank order; it does not preserve it. Complementing labels preserves temporary dinv under
this reversal, while reflecting the inverse descent set. The full shuffle convention change
also uses the fact that the corresponding reversal of fundamental functions fixes symmetric
functions, as explained in `HJO.External.Shuffle`. -/
def pointRank (a b N x y : ℕ) : ℤ := (a * N + 1) * (a * y - b * x) + x

variable {a b N : ℕ}

/-- For a below-diagonal path `y` and `s < bN`, the horizontal coordinate of the north step
whose foot is at height `s`: the least `r` with `y_r > s`. Outside that domain the definition
uses the totalized `firstReach`, with fallback `aN` when no such coordinate exists. -/
def column (y : Paths.Heights a b N) (s : ℕ) : ℕ := Paths.firstReach y (s + 1)

/-- `lab` labels the `bN` north steps of `y` bijectively by `1, …, bN`, the step whose foot is
at height `s` carrying the label `lab s + 1`, in a way that increases upwards along each
column. -/
def IsParkingLabelling (y : Paths.Heights a b N) (lab : Fin (b * N) → Fin (b * N)) : Prop :=
  Function.Bijective lab ∧
    ∀ s t : Fin (b * N), s < t → column y (s : ℕ) = column y (t : ℕ) → lab s < lab t

/-- Whether `lab` labels the north steps of `y` bijectively and increasingly upwards along each
column is decidable. -/
instance instDecidableIsParkingLabelling (y : Paths.Heights a b N)
    (lab : Fin (b * N) → Fin (b * N)) : Decidable (IsParkingLabelling y lab) := by
  unfold IsParkingLabelling; infer_instance

/-- A parking function in the `aN × bN` rectangle: a below-diagonal `(aN, bN)`-path together
with a bijective labelling of its `bN` north steps by `1, …, bN` that increases upwards along
each column. The north step whose foot is at height `s` is indexed by `s`. -/
@[hjo "def_parking"]
abbrev ParkingFunction (a b N : ℕ) : Type :=
  {p : Paths.Heights a b N × (Fin (b * N) → Fin (b * N)) //
    Paths.IsBelowDiagonal p.1 ∧ IsParkingLabelling p.1 p.2}

/-- The path `P_π` underlying the parking function `π`. -/
def path (π : ParkingFunction a b N) : Paths.Heights a b N := π.val.1

/-- The labelling of `π`: the north step whose foot is at height `s` carries the label
`label π s + 1`. -/
def label (π : ParkingFunction a b N) (s : Fin (b * N)) : Fin (b * N) := π.val.2 s

/-- The labelling of a parking function is a bijection. -/
theorem bijective_label (π : ParkingFunction a b N) : Function.Bijective (label π) := π.2.2.1

/-- The north step of `π` carrying the label `i + 1`, indexed by the height of its foot. -/
def labelStep (π : ParkingFunction a b N) (i : Fin (b * N)) : Fin (b * N) :=
  Fintype.bijInv (bijective_label π) i

/-- `PF^α_{aN, bN}`, the parking functions in the `aN × bN` rectangle whose underlying path has
return composition `α`. -/
def withReturns (α : List ℕ) (a b N : ℕ) : Finset (ParkingFunction a b N) :=
  (univ : Finset (ParkingFunction a b N)).filter fun π => Paths.HasReturns α (path π)

/-- The rank of the north step of `π` indexed by `s`: the rank of the lattice point
`(column, s)` at its foot. -/
def stepRank (π : ParkingFunction a b N) (s : Fin (b * N)) : ℤ :=
  pointRank a b N (column (path π) (s : ℕ)) (s : ℕ)

/-- The rank of the label `i + 1` of `π`: the rank of the lattice point at the foot of the
north step that this label marks. -/
@[hjo "def_pf_rank"]
def labelRank (π : ParkingFunction a b N) (i : Fin (b * N)) : ℤ :=
  stepRank π (labelStep π i)

/-- `tdinv(π)`, the number of pairs of labels `i < j` with `rk(i) < rk(j) < rk(i) + (aN + 1)a`. With
the normalization in `pointRank`, this window implements the window `aN` of the paper cited at
`HJO.ParkingFunctions.pointRank`, by the comparison argument there, not by simply scaling the
paper's rank. Both ends are strict and retain the horizontal perturbation: at equal integral ranks
the pair counts exactly when `i` marks the earlier column; when the integral rank of `j` is that of
`i` plus `a`, it counts exactly when `j` marks the earlier column. -/
@[hjo "def_pf_tdinv"]
def tdinv (π : ParkingFunction a b N) : ℕ :=
  #{p ∈ (univ : Finset (Fin (b * N) × Fin (b * N))) | p.1 < p.2 ∧
      labelRank π p.1 < labelRank π p.2 ∧ labelRank π p.2 < labelRank π p.1 + (a * N + 1) * a}

/-- `max tdinv(P)`, the largest `tdinv` of a parking function whose underlying path is `y`. It
is `0` when no parking function has underlying path `y`, that is, when `y` is not a
below-diagonal path. -/
@[hjo "def_pf_maxtdinv"]
def maxTdinv (y : Paths.Heights a b N) : ℕ :=
  ((univ : Finset (ParkingFunction a b N)).filter fun π => path π = y).sup tdinv

/-- `dinv(π) = h(P_π) + tdinv(π) - max tdinv(P_π)`, taken in `ℤ` because the difference of the
last two terms is genuine and need not be non-negative on its own. -/
@[hjo "def_pf_dinv"]
def dinv (π : ParkingFunction a b N) : ℤ :=
  (Paths.hookCount (path π) : ℤ) + tdinv π - maxTdinv (path π)

/-- The north step `s` of `π` is read before the step `t`: its foot has the larger rank, or the
two ranks agree and `s` is the higher step. A column is read downwards because the rank increases
upwards along it. For `a > 0` the second clause never fires: equal perturbed ranks force equal
integral ranks and equal columns, hence the same step. -/
def ReadBefore (π : ParkingFunction a b N) (s t : Fin (b * N)) : Prop :=
  stepRank π t < stepRank π s ∨ (stepRank π s = stepRank π t ∧ t < s)

/-- Whether the north step `s` of `π` is read before the step `t` is decidable. -/
instance instDecidableReadBefore (π : ParkingFunction a b N) (s t : Fin (b * N)) :
    Decidable (ReadBefore π s t) := by unfold ReadBefore; infer_instance

/-- The reading word of `π`: the word in `1, …, bN` listing its labels in decreasing order of
the rank of the north step each one marks, a column being read from the top downwards because the
rank increases upwards along it. -/
def readingWord (π : ParkingFunction a b N) : List ℕ :=
  ((List.finRange (b * N)).mergeSort fun s t => !decide (ReadBefore π t s)).map
    fun s => (label π s : ℕ) + 1

/-- `ides(π)`, the set of those `i` in `1, …, bN - 1` such that `i + 1` precedes `i` in the
reading word of `π`. -/
@[hjo "def_pf_ides"]
def ides (π : ParkingFunction a b N) : Finset ℕ :=
  {i ∈ Ico 1 (b * N) | (readingWord π).idxOf (i + 1) < (readingWord π).idxOf i}

/-- `ides(π)` is a descent set on degree `bN`: it is a subset of `1, …, bN - 1`. -/
theorem ides_subset (π : ParkingFunction a b N) : ides π ⊆ Ico 1 (b * N) :=
  filter_subset _ _

/-- For `S ⊆ Ico 1 n`, Gessel's fundamental quasisymmetric function `F_{n,S}`: the sum of
`x_{i₁} ⋯ x_{iₙ}` over weakly increasing tuples that increase strictly at every `j ∈ S`.
Each such monomial arises from exactly one sorted tuple, so its coefficient is the indicator
of the corresponding exponent vectors. The definition is total for arbitrary `S`, but indices
outside `Ico 1 n` constrain the auxiliary sequence beyond the tuple; that totalization is not
asserted to be a standard fundamental function of degree `n`. -/
@[hjo "def_gessel"]
noncomputable def gessel (K : Type*) [CommRing K] (n : ℕ) (S : Finset ℕ) :
    Sym.AlphabetSeries K :=
  Set.indicator {d : ℕ →₀ ℕ | ∃ i : ℕ → ℕ, (∀ j ∈ Ico 1 n, i j ≤ i (j + 1)) ∧
    (∀ j ∈ S, i j < i (j + 1)) ∧ d = ∑ j ∈ Icc 1 n, Finsupp.single (i j) 1} 1

end HJO.ParkingFunctions
