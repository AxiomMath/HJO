/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

-- Load-bearing for the comparator, NOT for compilation. This import fixes which
-- `PartialOrder ℤ` instance path the statements elaborate against, and `Challenge/Basic.lean`
-- must resolve the same one. The file compiles without it, so `minimize_imports` reports it
-- UNUSED -- removing it changes the exported terms and the comparator then rejects
-- `HJO.PhiMul.Witness.Base._proof_1`. Do not remove.
public import Mathlib.Data.Int.ConditionallyCompleteOrder
public import Mathlib.RingTheory.LaurentSeries
public import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
public import QSeriesLib.NumberTheory.HJO.Defs
public meta import HJO.Attr

/-! # The definitions of the development

The objects the results of this library are stated in, collected in one module: the ring of
symmetric functions and its operators, below-diagonal paths, parking functions, the gap poset,
cylindric partitions, the HJO polynomial, the model types `Target`, `Coeff` and `Base` of the
specialisation, and the results quoted from the literature stated as hypotheses.
-/

@[expose] public section

open Finset HJO NumericalSemigroup PowerSeries
open scoped QTheory PowerSeries.DiscreteTopology

local notation "gaps(" a ", " b ")" => NumericalSemigroup.gaps (NumericalSemigroup.finspan {a, b})

namespace HJO.Sym

/-! ### The ring of symmetric functions and its ambient power series -/

/-- The polynomial algebra over `K` on formal power-sum symbols: generator `i` stands for
`p_{i+1}`, with weight `i + 1`. When `K` is a `ℚ`-algebra, this is the power-sum presentation of
the ring of symmetric functions. That identification is not asserted for arbitrary commutative
rings, where actual power sums need not freely generate the symmetric-function ring. -/
@[hjo "def_lambda"]
abbrev Lambda (K : Type*) [CommRing K] : Type _ := MvPolynomial ℕ K

/-- The generator of `Lambda K` standing for the power sum `p_k`, for `k ≥ 1`. The natural
subtraction in the index means `powerSum K 0` is the same generator as `powerSum K 1`. -/
noncomputable def powerSum (K : Type*) [CommRing K] (k : ℕ) : Lambda K :=
  MvPolynomial.X (k - 1)

/-- The formal power series `K⟦x₁, x₂, …⟧` in countably many commuting variables, the
ambient ring in which the alphabet lives. -/
@[hjo "def_qsym"]
abbrev AlphabetSeries (K : Type*) [CommRing K] : Type _ := MvPowerSeries ℕ K

section CommRing

variable {K : Type*} [CommRing K]

/-- A `K`-algebra homomorphism from `Lambda K` to the power series in the alphabet is a
realisation when it sends the generator `p_k` to the actual power sum `∑ᵢ xᵢ ^ k`, whose
coefficients are `1` on the monomials `xᵢ ^ k` and `0` elsewhere. -/
@[hjo "def_realisation"]
structure IsRealisation (ι : Lambda K →ₐ[K] AlphabetSeries K) : Prop where
  /-- The monomial `xᵢ ^ (k + 1)` occurs in the image of `p_{k+1}` with coefficient `1`. -/
  coeff_pow : ∀ k i : ℕ,
    MvPowerSeries.coeff (Finsupp.single i (k + 1)) (ι (powerSum K (k + 1))) = 1
  /-- No other monomial occurs in the image of `p_{k+1}`. -/
  coeff_of_ne : ∀ (k : ℕ) (d : ℕ →₀ ℕ), (∀ i, d ≠ Finsupp.single i (k + 1)) →
    MvPowerSeries.coeff d (ι (powerSum K (k + 1))) = 0

/-- A diagonal substitution: the `K`-algebra endomorphism of `Lambda K` sending the formal
power sum `p_{i+1}` to `c i * p_{i+1}`. The coefficient of a power-sum monomial in the image is
the matching product of the scalars times its coefficient in the argument. The scaling and
axis substitutions have this form; the affine displacements `plethShift` and `plethCreate`
do not. -/
noncomputable def diagScale (c : ℕ → K) : Lambda K →ₐ[K] Lambda K :=
  MvPolynomial.aeval fun i => MvPolynomial.C (c i) * MvPolynomial.X i

/-- Scaling the alphabet by `c`: the `K`-algebra endomorphism `σ_c` of `Lambda K` sending
`p_k` to `c ^ k * p_k`, written `f[cX]` on elements. It is the diagonal substitution whose scalar
at `p_k` is the `k`-th power of a single element, which is what the plethysm of an honest monomial
alphabet does. -/
@[hjo "def_pleth_scale"]
noncomputable def plethScale (c : K) : Lambda K →ₐ[K] Lambda K :=
  diagScale fun i => c ^ (i + 1)

/-- The plethystic displacement `δ`, sending `p_k` to `p_k + (1 - q ^ k) * (1 - u ^ k) * z⁻ᵏ`
and written `f[X + M/z]` on elements. Its target is the polynomial ring on `w = z⁻¹`, since
only non-negative powers of `w` occur. -/
@[hjo "def_pleth_shift"]
noncomputable def plethShift (q u : K) : Lambda K →ₐ[K] Polynomial (Lambda K) :=
  MvPolynomial.aeval fun i => Polynomial.C (powerSum K (i + 1)) +
    Polynomial.C (MvPolynomial.C ((1 - q ^ (i + 1)) * (1 - u ^ (i + 1)))) * Polynomial.X ^ (i + 1)

/-- Pairing a polynomial in `w = z⁻¹` against the family `c` of symmetric functions: the
`K`-linear map sending `∑ⱼ Aⱼ wʲ` to `∑ⱼ Aⱼ * c j`. -/
noncomputable def coeffPairing (c : ℕ → Lambda K) : Polynomial (Lambda K) →ₗ[K] Lambda K where
  toFun P := P.sum fun j A => A * c j
  map_add' P Q := Polynomial.sum_add_index P Q _ (fun _ => by simp) (fun _ _ _ => by ring)
  map_smul' r P := by
    simp only [RingHom.id_apply]
    rw [Polynomial.sum_smul_index' _ _ _ (fun _ => by simp), Polynomial.smul_sum]
    simp only [smul_mul_assoc]

end CommRing

section Newton

variable (K : Type*) [CommRing K] [Algebra ℚ K]

/-- The complete homogeneous symmetric functions, defined by Newton's identity
`n * hₙ = ∑_{k=1}^{n} p_k * h_{n-k}` from `h₀ = 1`. -/
@[hjo "def_hsymm"]
noncomputable def completeHomog : ℕ → Lambda K
  | 0 => 1
  | n + 1 => MvPolynomial.C (algebraMap ℚ K ((n + 1 : ℚ)⁻¹)) *
      ∑ k ∈ range (n + 1), powerSum K (k + 1) * completeHomog (n - k)
termination_by n => n
decreasing_by omega

/-- The elementary symmetric functions, defined by Newton's identity
`n * eₙ = ∑_{k=1}^{n} (-1) ^ (k - 1) * p_k * e_{n-k}` from `e₀ = 1`. -/
@[hjo "def_esymm"]
noncomputable def elemSymm : ℕ → Lambda K
  | 0 => 1
  | n + 1 => MvPolynomial.C (algebraMap ℚ K ((n + 1 : ℚ)⁻¹)) *
      ∑ k ∈ range (n + 1), (-1) ^ k * powerSum K (k + 1) * elemSymm (n - k)
termination_by n => n
decreasing_by omega

end Newton

/-- Sign extraction: the `K`-algebra homomorphism `Lambda K → K` sending `p_k` to
`(-1) ^ (k - 1)`. -/
@[hjo "def_epsilon"]
noncomputable def signExtract (K : Type*) [CommRing K] : Lambda K →ₐ[K] K :=
  MvPolynomial.aeval fun i => (-1 : K) ^ i

/-! ### The basic operators and the split of a slope -/

section Dop

variable {K : Type*} [CommRing K] [Algebra ℚ K]

/-- The basic operator `Dop q u k`, the `K`-linear endomorphism of `Lambda K` extracting the
coefficient of `zᵏ` from `f[X + M/z] * ∑_{r ≥ 0} (-z) ^ r * e_r`. Written in `w = z⁻¹` the
coefficient of `wʲ` of the displacement is paired with `(-1) ^ (k + j) * e_{k+j}`. -/
@[hjo "def_dop"]
noncomputable def Dop (q u : K) (k : ℕ) : Module.End K (Lambda K) :=
  coeffPairing (fun j => (-1) ^ (k + j) * elemSymm K (k + j)) ∘ₗ (plethShift q u).toLinearMap

end Dop

/-- The split of the slope `(m, n)`: the lexicographically least pair `(r, s)` with
`1 ≤ r < m`, `1 ≤ s < n` and `m * s + 1 = n * r` when one exists, and `(1, 0)` otherwise. -/
@[hjo "def_split"]
def Split (m n : ℕ) : ℕ × ℕ :=
  ((List.range m ×ˢ List.range n).filter
    fun p => 1 ≤ p.1 ∧ 1 ≤ p.2 ∧ m * p.2 + 1 = n * p.1).head?.getD (1, 0)

/-- The first component of the split of `(m, n)`, clamped to the interval `[1, m - 1]`. The
clamp is inactive rather than corrective: for every `m ≥ 2` it returns exactly `(Split m n).1`,
so it hides no indexing error. What makes the recursion of `QopAux` structural is that
recursion's fuel, not this clamp. -/
def splitFst (m n : ℕ) : ℕ := max 1 (min (m - 1) (Split m n).1)

/-- The primitive split of a positive coprime pair `(a, b)`, as in Bergeron--Garsia--Leven--Xin
(2.9): `(1, b - 1)` at `a = 1`, `(1, 0)` at `b = 1 < a`, and otherwise the unique
`(r, s)` with `1 ≤ r < a`, `1 ≤ s < b` and `a * s + 1 = b * r`. On the coprime interior
`a, b > 1`, the bounded search `Split a b` finds this pair. The two boundaries are written out
explicitly here: at `a = 1, b ≥ 2` the raw search incorrectly defaults to `(1, 0)`, whereas at
`b = 1` its fallback `(1, 0)` is already correct. At `(1, 1)` the two also agree. -/
def primitiveSplit (a b : ℕ) : ℕ × ℕ :=
  if a = 1 then (1, b - 1) else if b = 1 then (1, 0) else Split a b

/-- The split of the slope `(m, n)`: the primitive split of the primitive pair
`(m / k, n / k)`, where `k = gcd m n` is the multiplicity. The source splits the *primitive*
pair and never the multiplied one, and the Bezout equation of a split has no solution at a
multiplied pair, so the raw search `Split m n` must not be used there. -/
def slopeSplit (m n : ℕ) : ℕ × ℕ :=
  primitiveSplit (m / Nat.gcd m n) (n / Nat.gcd m n)

/-! ### The slope operators and the creation operators -/

section Field

variable {L : Type*} [Field L] [Algebra ℚ L]

/-- The `L`-algebra endomorphism sending `p_k` to `((v ^ k)⁻¹ - 1) * p_k` for `k ≥ 1`.
For `v ≠ 0`, it represents the virtual alphabet `(1 - v) / v * X`, written
`f[(1 - v)/v * X]`. Here `(1 - v) / v = v⁻¹ - 1` is a difference of monomial alphabets:
`p_k[v⁻¹ X] - p_k[X] = ((v ^ k)⁻¹ - 1) * p_k`, not `((1 - v) / v) ^ k * p_k`.
The definition is totalized at `v = 0`, where it sends every positive power sum to its negative;
the quotient identity used to explain the nonsingular alphabet does not hold there. -/
noncomputable def plethAxis (v : L) : Lambda L →ₐ[L] Lambda L :=
  diagScale fun index => (v ^ (index + 1))⁻¹ - 1

/-- For `k ≥ 1`, the axis generator `U_k` at `v = q * u`, with source formula
`v / (v - 1) * h_k[(1 - v) / v * X]` for `v ≠ 0, 1`. The definition also assigns values at
`v = 0, 1` using totalized field division; these are not evaluations of the source's generic
rational formula. -/
@[hjo "def_axis_gen"]
noncomputable def axisGen (v : L) (k : ℕ) : Lambda L :=
  MvPolynomial.C (v / (v - 1)) * plethAxis v (completeHomog L k)

/-! #### The primitive recursion, run with fuel -/

/-- The slope operators computed with a fuel parameter bounding the recursion depth: for
`m ≤ 1` the basic operator `Dop q u n`, and otherwise the commutator of the two halves of
the split of `(m, n)`, normalised by `M = (1 - q) * (1 - u)`. This is the *coprime* evaluator:
at a coprime slope both halves of a split are again coprime, so it runs the source's primitive
recursion; each half of a split has first entry in `[1, m - 1]`, so the depth is at most
`m - 1` and the `m` units of fuel that `QopPrim` supplies reach the base case. Off that domain,
and at zero fuel, its value is a totalisation with no source content. -/
noncomputable def QopAux (q u : L) : ℕ → ℕ → ℕ → Module.End L (Lambda L)
  | 0, _, n => Dop q u n
  | fuel + 1, m, n =>
    if m ≤ 1 then Dop q u n
    else
      ((1 - q) * (1 - u))⁻¹ •
        (QopAux q u fuel (m - splitFst m n) (n - (Split m n).2) *
            QopAux q u fuel (splitFst m n) (Split m n).2 -
          QopAux q u fuel (splitFst m n) (Split m n).2 *
            QopAux q u fuel (m - splitFst m n) (n - (Split m n).2))

/-- The primitive evaluator: the slope operator of a *coprime* slope `(m, n)`, the source's
primitive recursion run with `m` units of fuel. That is enough: each half of a split of
`(m, n)` has first entry in `[1, m - 1]`, so the recursion has depth at most `m - 1`, and past
that depth extra fuel changes nothing. -/
noncomputable def QopPrim (q u : L) (m n : ℕ) : Module.End L (Lambda L) := QopAux q u m m n

/-! #### The dispatch of the slope operator -/

/-- The slope operator `Qop q u m n`, for `m, n ≥ 1` together with the boundary `(1, 0)`.

At `m = 1` it is the basic operator `Dop q u n`, the source's base case; this includes the
boundary operator `Q_{1,0} = D_0`. At `m > 1` coprime to `n` it is the source's primitive
recursion, `QopPrim`. At `m > 1` not coprime to `n` it is the source's noncoprime extension at
the permitted multiplicity parameter `v = 1`: writing `k = gcd m n` for the multiplicity,
`(a, b) = (m / k, n / k)` for the primitive pair and `(r, s)` for the primitive split of
`(a, b)`, the complement is `((k - 1) a + r, (k - 1) b + s) = (m - r, n - s)` and

  `Q_{m,n} = M⁻¹ (Q_{m-r,n-s} Q_{r,s} - Q_{r,s} Q_{m-r,n-s})`,   `M = (1 - q) (1 - u)`.

Both of those slopes are again coprime, so both are evaluated by `QopPrim`; that is what keeps
the noncoprime branch from being re-entered. The split is taken of the primitive pair, never of
`(m, n)`: the Bezout equation of a split has no solution at a multiplied pair.

Outside `m, n ≥ 1` the value is a totalisation carrying no claim of source agreement: at
`m = 0` it is `Dop q u n`, and at `n = 0` with `m > 1` it is the bracket above with
`(r, s) = (1, 0)`. -/
@[hjo "def_qop"]
noncomputable def Qop (q u : L) (m n : ℕ) : Module.End L (Lambda L) :=
  if m ≤ 1 then Dop q u n
  else if Nat.Coprime m n then QopPrim q u m n
  else
    ((1 - q) * (1 - u))⁻¹ •
      (QopPrim q u (m - (slopeSplit m n).1) (n - (slopeSplit m n).2) *
          QopPrim q u (slopeSplit m n).1 (slopeSplit m n).2 -
        QopPrim q u (slopeSplit m n).1 (slopeSplit m n).2 *
          QopPrim q u (m - (slopeSplit m n).1) (n - (slopeSplit m n).2))

/-- A slope homomorphism at `(a, b)`: an `L`-algebra homomorphism from `Lambda L` to the
`L`-linear endomorphisms of `Lambda L` sending the axis generator `U_k` to the slope
operator `Qop q u (a * k) (b * k)` for every `k ≥ 1`. -/
@[hjo "def_slope_hom"]
def IsSlopeHom (a b : ℕ) (q u : L) (Θ : Lambda L →ₐ[L] Module.End L (Lambda L)) : Prop :=
  ∀ k : ℕ, 0 < k → Θ (axisGen (q * u) k) = Qop q u (a * k) (b * k)

/-- The creation displacement `δ'`, sending `p_k` to `p_k - (1 - q⁻ᵏ) * z⁻ᵏ` and written
`f[X - (1 - q⁻¹)/z]` on elements; the minus sign is a virtual difference, so it is not
squared. Its target is the polynomial ring on `w = z⁻¹`. -/
@[hjo "def_pleth_create"]
noncomputable def plethCreate (q : L) : Lambda L →ₐ[L] Polynomial (Lambda L) :=
  MvPolynomial.aeval fun i => Polynomial.C (powerSum L (i + 1)) -
    Polynomial.C (MvPolynomial.C (1 - (q ^ (i + 1))⁻¹)) * Polynomial.X ^ (i + 1)

/-- The creation operator `Cop q r`, the `L`-linear endomorphism of `Lambda L` sending `f` to
`(-q) ^ (1 - r)` times the coefficient of `zʳ` in `f[X - (1 - q⁻¹)/z] * ∑_{m ≥ 0} h_m * zᵐ`.
Written in `w = z⁻¹` the coefficient of `wʲ` of the displacement is paired with `h_{r+j}`. -/
@[hjo "def_cop"]
noncomputable def Cop (q : L) (r : ℕ) : Module.End L (Lambda L) :=
  coeffPairing (fun j => MvPolynomial.C ((-q) ^ (1 - (r : ℤ))) * completeHomog L (r + j)) ∘ₗ
    (plethCreate q).toLinearMap

/-- The composite creation operator of a composition `α`, the composition
`Cop α₁ ∘ ⋯ ∘ Cop α_ℓ` of the creation operators of its parts in order. -/
@[hjo "def_cop_comp"]
noncomputable def CopComp (q : L) (α : List ℕ) : Module.End L (Lambda L) :=
  (α.map (Cop q)).prod

end Field

end HJO.Sym

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

namespace HJO.Primitive

open Finset

/-! ### The primitive path of an order filter of the gap set -/

/-- The number of indices `i ∈ Icc 1 b` with `ai < rb` and `rb - ai ∈ F`.
For `a > 0`, `r ≤ a` and `F` a set of gaps, this counts all positive indices with gap label
`rb - ai`: `ai < rb ≤ ab` forces `i < b`, and a nonpositive difference cannot be a gap.
These are the bounds supplied by `primitivePath`; the unrestricted definition outside this
column domain makes no claim that the cutoff loses no indices. -/
def primitiveHeight (a b : ℕ) (F : Finset ℕ) (r : ℕ) : ℕ :=
  #{i ∈ Icc 1 b | a * i < r * b ∧ r * b - a * i ∈ F}

/-- The counted indices lie in `Icc 1 b`, so a primitive height never exceeds `b`. -/
theorem primitiveHeight_le (a b : ℕ) (F : Finset ℕ) (r : ℕ) : primitiveHeight a b F r ≤ b :=
  (card_filter_le _ _).trans (by simp)

/-- A candidate height vector, with height `primitiveHeight a b F r` for `r < a` and `b` at
`r = a`. For coprime `1 < a < b` and `F` an order filter of the gap set, this is the primitive
below-diagonal path `P_F`: each interior height counts the positive indices `i` with gap label
`rb - ai` in `F`. The endpoint is set separately because every nonnegative `ab - ai` is a
multiple of `a`, hence not a gap. An arbitrary gap subset need not give monotone heights. -/
@[hjo "def_primitive_path"]
def primitivePath (a b : ℕ) (F : Finset ℕ) : Paths.Heights a b 1 := fun r =>
  if (r : ℕ) = a then ⟨b, Nat.lt_succ_of_le (Nat.le_of_eq (Nat.mul_one b).symm)⟩
  else ⟨primitiveHeight a b F r,
    Nat.lt_succ_of_le ((primitiveHeight_le a b F r).trans (Nat.le_of_eq (Nat.mul_one b).symm))⟩

end HJO.Primitive

namespace HJO.ParkingFunctions

open Finset

/-! ### Parking functions in the rectangle and their statistics -/

/-- The signed rank `P(x,y) = (aN + 1)(a*y - b*x) + x`. Put `m = aN`, `n = bN`,
`C = m + 1` and `A(x,y) = a*y - b*x`. For `N > 0`, the source's rank formula is
`N*A(x,y) + x/C`, not `A(x,y) + x/C`: `P` is not simply its denominator-cleared value when
`N > 1`. Nevertheless their order and window comparisons agree on the rectangle.

Indeed `|Δx| ≤ m < C`, so `C*ΔA + Δx` and `C*N*ΔA + Δx` have the same sign, determined by
`(ΔA, Δx)` in lexicographic order. Replacing `ΔA` by `ΔA - a` gives the upper-window comparison:
the window `C*a` for `P` agrees with the source's window `m = N*a`. Both strict endpoints are
preserved, including equal integral ranks and integral-rank differences exactly `a`.
For `a > 0`, `P` increases up each column, making rank-ordered labelling legal.

Rotating to the source's above-diagonal path sends a north-step foot `(x, y)` to
`(m - x, n - 1 - y)`, where the source rank is `-N*A(x,y) - x/C - m²/C`. Thus rotation reverses
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

/-- `tdinv(π)`, the number of pairs of labels `i < j` with
`rk(i) < rk(j) < rk(i) + (aN + 1)a`. With the normalization in `pointRank`, this window
implements the source's window `aN`, by the comparison argument there, not by simply scaling
the source rank. Both ends are strict and retain the horizontal perturbation: at equal integral
ranks the pair counts exactly when `i` marks the earlier column; when the integral rank of `j`
is that of `i` plus `a`, it counts exactly when `j` marks the earlier column. -/
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

namespace HJO.Gaps

open Finset NumericalSemigroup PowerSeries
open scoped QTheory PowerSeries.DiscreteTopology

/-- The gap order: `g ≼ h` when the signed difference `h - g` lies in the semigroup generated
by `a` and `b`. The natural-number equation below avoids truncated subtraction. -/
@[hjo "def_gap_order"]
def GapLE (a b g h : ℕ) : Prop := ∃ u v : ℕ, g + (u * a + v * b) = h

/-- The totalized natural expression `a * b - a - b`. For coprime `1 < a < b` this is the
Frobenius gap of `⟨a, b⟩`; no gap interpretation is asserted outside that domain. -/
@[hjo "def_frobenius"]
def frobeniusGap (a b : ℕ) : ℕ := a * b - a - b

/-- An order filter of the gap set: a set of gaps closed upwards under the gap order. -/
@[hjo "def_order_filter"]
def IsOrderFilter (a b : ℕ) (F : Finset ℕ) : Prop :=
  F ⊆ (finspan {a, b}).gaps ∧
    ∀ g ∈ F, ∀ h ∈ (finspan {a, b}).gaps, GapLE a b g h → h ∈ F

/-! ### The generalised Gaussian multinomial in integer-vector form, and the flag extension -/

/-- The guarded integer-vector presentation of the generalised Gaussian multinomial.
For coprime `1 < a < b`, on the monotonicity cone with `n_f ≤ N`, it is the source expression
`[N; n] = (q)_N / (q)_{N-n_f} * P_G(n)`, where `f` is the Frobenius gap and division is by
constant-term-one power series. The difference `N-n_f` is taken in `ℤ`; a negative index makes
its extended inverse zero. The gap product likewise uses extended Pochhammer factors and
inverses that are zero at negative indices. These conventions define the value off the source
domain, and differ from the natural subtraction in `HJO.Finite.gaussianMultinomial`, so the two
need not agree when `n_f > N`, though a zero gap product can still make them agree. -/
@[hjo "def_multinomial"]
noncomputable def multinomial (a b N : ℕ) (n : (finspan {a, b}).gaps → ℤ) : ℤ⟦X⟧ :=
  (X; X)_N * HJO.extendedSelfQPochhammerInv ((N : ℤ) - HJO.extend n (frobeniusGap a b)) *
    ∏ g : (finspan {a, b}).gaps, HJO.multiplicand _ a b n g

/-- The flag extension of `n` at level `N`: `n j` at a gap `j`, `N` at a non-gap `j ≥ 0`, and
`0` at a negative `j`. -/
@[hjo "def_flag"]
def flag (a b N : ℕ) (n : (finspan {a, b}).gaps → ℕ) (j : ℤ) : ℕ :=
  if j < 0 then 0 else
    if j.toNat ∈ (finspan {a, b}).gaps then HJO.extendNat n j.toNat else N

end HJO.Gaps

namespace HJO.Cylindric

open PowerSeries
open scoped PowerSeries.DiscreteTopology QTheory

/-! ### Cylindric partitions and their volume generating functions -/

/-- The balanced profile `cᵢ = ⌊(i+1)b/a⌋ - ⌊ib/a⌋`. For `a > 0` it is periodic with
period `a`, and its first `a` entries sum to `b`. -/
@[hjo "def_balanced_profile"]
def profile (a b : ℕ) (i : ℕ) : ℕ := (i + 1) * b / a - i * b / a

/-- A cylindric partition with outgoing profile `c`: an `a`-tuple of partitions, written
here as one row-indexed family with the row index taken modulo `a`, in which row `i + 1`
at position `j + c i` never exceeds row `i` at position `j`. -/
@[hjo "def_cylindric"]
structure IsCylindric (a : ℕ) (c : ℕ → ℕ) (l : ℕ → ℕ → ℕ) : Prop where
  /-- Each row is a partition: weakly decreasing. -/
  antitone : ∀ i, Antitone (l i)
  /-- Each row has finitely many nonzero parts. -/
  eventually_zero : ∀ i, ∃ J, ∀ j, J ≤ j → l i j = 0
  /-- Rows depend only on `i` modulo `a`, closing the cylinder. -/
  periodic : ∀ i j, l (i + a) j = l i j
  /-- The outgoing inequality of the cylinder. -/
  outgoing : ∀ i j, l (i + 1) (j + c i) ≤ l i j

/-- The volume of a cylindric partition: the sum of the entries of its `a` rows. The
inner sum is finite because each row has finitely many nonzero parts. -/
@[hjo "def_cylinder_volume"]
noncomputable def cylVolume (a : ℕ) (l : ℕ → ℕ → ℕ) : ℕ := ∑ i ∈ range a, ∑ᶠ j, l i j

/-- Every entry of the cylinder is at most `N`. -/
def BoundedBy (N : ℕ) (l : ℕ → ℕ → ℕ) : Prop := ∀ i j, l i j ≤ N

/-- `C_{c,≤N}(q)`, the volume generating function of the cylindric partitions with
outgoing profile `c` whose every entry is at most `N`. A positive entry bound need not bound
the number of parts, so the definition uses a formal-series sum. At `N = 0` only the zero
cylinder contributes, giving the constant series `1`. -/
@[hjo "def_bounded_cylinder"]
noncomputable def boundedGF (a b N : ℕ) : ℤ⟦X⟧ :=
  ∑' l : {l : ℕ → ℕ → ℕ // IsCylindric a (profile a b) l ∧ BoundedBy N l},
    X ^ cylVolume a l.val

/-- `C_c(q)`, the volume generating function of the cylindric partitions with outgoing
profile `c` and no bound on their entries. -/
@[hjo "def_cylinder_series"]
noncomputable def unboundedGF (a b : ℕ) : ℤ⟦X⟧ :=
  ∑' l : {l : ℕ → ℕ → ℕ // IsCylindric a (profile a b) l}, X ^ cylVolume a l.val

/-- `j_v = ⌊(v+1)d/a⌋ - ⌊vd/a⌋`, with `d = a + b`. For `a > 0` this is `1 + c_v`
and is periodic in `v` with period `a`. -/
@[hjo "def_jshift"]
def jShift (a b : ℕ) (v : ℕ) : ℕ := (v + 1) * (a + b) / a - v * (a + b) / a

/-- `J_{v,s} = j_v + ⋯ + j_{v+s-1}`. The indices are cyclic, which needs no `mod` here
because `jShift` is itself periodic with period `a`. -/
@[hjo "def_jsum"]
def jSum (a b v s : ℕ) : ℕ := ∑ t ∈ range s, jShift a b (v + t)

end HJO.Cylindric

namespace HJO.Finite

open PowerSeries
open scoped PowerSeries.DiscreteTopology QTheory

/-! ### The HJO polynomial at finite module rank -/

/-- The natural-vector presentation of the generalized Gaussian multinomial. For coprime
`1 < a < b`, on the monotonicity cone with `n_f ≤ N`, this is the source expression
`[N; 𝐧]_{q;G} = (q)_N / (q)_{N-n_f} * P_G(𝐧)`. The middle index uses truncated natural
subtraction: when `n_f > N` its inverse factor is `1`, rather than the zero factor of
`HJO.Gaps.multinomial`. -/
noncomputable def gaussianMultinomial (a b N : ℕ) (n : gaps(a, b) → ℕ) : ℤ⟦X⟧ :=
  (X; X)_N * invOfUnit (X; X)_(N - extendNat n (a * b - a - b)) 1 *
    ∏ i : gaps(a, b), multiplicand gaps(a, b) a b (fun j => (n j : ℤ)) i

/-- `F_N(q) = N_{a,b;N}(q,1)`, the HJO polynomial at module rank `N`: the sum over
gap vectors in the monotonicity cone with `n_f ≤ N` of `[N; 𝐧]_{q;G} q^{Q(𝐧)}`. -/
noncomputable def poly (a b N : ℕ) : ℤ⟦X⟧ :=
  ∑ᶠ n ∈ {n : gaps(a, b) → ℕ |
      (fun i => (n i : ℤ)) ∈ cone a b ∧ extendNat n (a * b - a - b) ≤ N},
    gaussianMultinomial a b N n * X ^ (Q a b (fun i => (n i : ℤ))).toNat

end HJO.Finite

namespace HJO.Literature

open scoped PowerSeries.DiscreteTopology QTheory

/-! ### Huang's coercivity theorem as hypothesis

Y. Huang, with an appendix by K. Lau, *A quadratic form generalization of rational dinv*,
arXiv:2604.13238, Res. Math. Sci. **13** (2026) article 44, doi 10.1007/s40687-026-00631-0,
**Theorem 1.3**: the effective positive definiteness of `Q` on the monotonicity cone. -/

/-- **Huang Theorem 1.3**, specialized to integer vectors in the monotonicity cone:
`|G| · Q(𝐧) ≥ ‖𝐧‖_∞²`, expressed as a bound on every coordinate square. The source proves this
bound on the real cone and also proves nonnegativity of the associated bilinear form on pairs
of cone vectors; those additional assertions are not included in this hypothesis. -/
@[hjo "lem_coercivity"]
def HuangCoercivity : Prop :=
  ∀ a b : ℕ, Nat.Coprime a b → 1 < a → a < b →
    ∀ n : gaps(a, b) → ℤ, n ∈ cone a b →
      ∀ i : gaps(a, b), n i ^ 2 ≤ (gaps(a, b)).card * Q a b n

/-! ### The cylindric product as hypothesis

O. Foda and T. A. Welsh, *Cylindric partitions, `W_r` characters and the
Andrews–Gordon–Bressoud identities*, arXiv:1510.02213, J. Phys. A **49** (2016) 164004,
doi 10.1088/1751-8113/49/16/164004, Sections 2–3, equivalently its normalized
minimal-model form, together with Y. Huang, R. Jiang and A. Oblomkov, *Quot scheme of
points on torus knot singularities*, arXiv:2608.16086v1: the standard product for the
unbounded cylindric series, in its explicit form rather than as an identification with
`charge a b`. -/

/-- **The standard cylindric product**: `(q)_∞ C_c(q)` equals
`(q^d;q^d)_∞^{a-1} / (q;q)_∞^{a-1} · ∏_{s=1}^{a-1} ∏_{v=0}^{a-1} (q^{J_{v,s}}; q^d)_∞`,
with `d = a + b`. Assumed at every coprime pair satisfying `1 < a < b`. -/
@[hjo "lem_cylindric_product"]
def CylindricProduct : Prop :=
  ∀ a b : ℕ, Nat.Coprime a b → 1 < a → a < b →
    (X; X)_∞ * Cylindric.unboundedGF a b =
      (X ^ (a + b); X ^ (a + b))_∞ ^ (a - 1) * invOfUnit ((X; X)_∞) 1 ^ (a - 1) *
        ∏ s ∈ Icc 1 (a - 1), ∏ v ∈ range a,
          (X ^ Cylindric.jSum a b v s; X ^ (a + b))_∞

end HJO.Literature

namespace HJO.External

open ParkingFunctions Paths

/-! ### The gap poset and the quadratic form -/

/-- **Huang, `A quadratic form generalization of rational dinv`, Theorem 1.1**: for every order
filter `F` of the gap poset of `⟨a, b⟩`, the hook count of the primitive path of `F` is the value
of the quadratic form at the indicator vector of `F`. -/
@[hjo "lem_rank_one_dinv"]
def RankOneDinv : Prop :=
  ∀ a b : ℕ, Nat.Coprime a b → 1 < a → a < b →
    ∀ F : Finset ℕ, Gaps.IsOrderFilter a b F →
      (hookCount (Primitive.primitivePath a b F) : ℤ) =
        HJO.Q a b fun g => if (g : ℕ) ∈ F then 1 else 0

/-- **Huang–Jiang–Oblomkov, `Quot scheme of points on torus knot singularities`, Lemma 5.9**
(equation (5.20) with Remark 6.15, specialised to the gap poset): on the monotonicity cone with
`n_f ≤ N` the generalised Gaussian multinomial factors over the gaps, the factor at `g` being the
ordinary Gaussian binomial in the flag values, `(q)_m / ((q)_k (q)_{m-k})` with
`m = n̂_{g+b} - n_{g-a}` and `k = n_g - n_{g-a}`, each division realised by the power series
inverse. -/
@[hjo "lem_good_traverse"]
def GoodTraverse : Prop :=
  ∀ a b : ℕ, Nat.Coprime a b → 1 < a → a < b →
    ∀ (N : ℕ) (n : (finspan {a, b}).gaps → ℕ), (fun g => (n g : ℤ)) ∈ HJO.cone a b →
      HJO.extendNat n (Gaps.frobeniusGap a b) ≤ N →
        Gaps.multinomial a b N (fun g => (n g : ℤ)) =
          ∏ g : (finspan {a, b}).gaps,
            (X; X)_(Gaps.flag a b N n (((g : ℕ) : ℤ) + b) - HJO.extendNat n ((g : ℕ) - a)) *
              invOfUnit (X; X)_(n g - HJO.extendNat n ((g : ℕ) - a)) 1 *
              invOfUnit (X; X)_(Gaps.flag a b N n (((g : ℕ) : ℤ) + b) - n g) 1

/-! ### The slope operators and the shuffle identity as hypotheses

F. Bergeron, A. M. Garsia, E. Leven and G. Xin, *Compositional (km,kn)-shuffle conjectures*,
arXiv:1404.4616v2, Int. Math. Res. Not. IMRN **2016** no. 14, 4229--4270, **Theorem 5.1**, is
`CollinearCommutation`; its **equation (3.7)**, conjectured there and proved by A. Mellit,
*Toric braids and (m,n)-parking functions*, arXiv:1604.07456v1, Duke Math. J. **170** (2021)
4123--4169, **Section 6**, is `Shuffle`. Both are quoted at generic parameters, which is why
both hypotheses ask for `q` and `u` algebraically independent over `ℤ`. -/

/-- **Bergeron–Garsia–Leven–Xin, `Compositional (km,kn)-shuffle conjectures`, Theorem 5.1**:
the collinear slope operators `Q_{ka, kb}`, `k ≥ 1`, pairwise commute. Together with free generation
by the axis generators `U_1, U_2, …`, this gives an algebra homomorphism prescribed by
`U_k ↦ Q_{ka, kb}`. The source works at generic parameters. Algebraic independence over `ℤ`
guarantees both free generation and nonzero operator denominators, but is not necessary for
free generation alone.

Writing `v = q * u`, for `v ≠ 0, 1` the coefficient of `p_k` in `U_k` is
`-v ^ (1 - k) (1 + v + ⋯ + v ^ (k - 1)) / k`. The other terms involve earlier power sums, so
nonvanishing of these coefficients gives an invertible triangular change of generators. It
suffices that `v` be nonzero and not a root of unity; merely `v ≠ 0, 1` is insufficient, since
at `v = -1, k = 2` the coefficient vanishes. For example, `q = 2, u = 3` already gives free
generation without algebraic independence. The recursion separately needs
`M = (1 - q)(1 - u) ≠ 0`; the genericity hypothesis supplies both conditions. -/
@[hjo "lem_collinear"]
def CollinearCommutation (L : Type*) [Field L] [Algebra ℚ L] : Prop :=
  ∀ a b : ℕ, Nat.Coprime a b → 1 < a → a < b →
    ∀ q u : L, AlgebraicIndependent ℤ ![q, u] →
      (∀ k l : ℕ, 0 < k → 0 < l →
        Commute (Sym.Qop q u (a * k) (b * k)) (Sym.Qop q u (a * l) (b * l))) ∧
        ∃ Θ : Sym.Lambda L →ₐ[L] Module.End L (Sym.Lambda L), Sym.IsSlopeHom a b q u Θ

/-- **Bergeron–Garsia–Leven–Xin, equation (3.7)**, conjectured there and proved by
**Mellit, `Toric braids and (m,n)-parking functions`, Section 6**: the compositional rational
shuffle identity. For a slope homomorphism `Θ` at `(a, b)` and a composition `α` of `N`,
`(-1) ^ (N (b + 1)) Θ(C_α 1) 1` is homogeneous of degree `bN`, and in any realisation it expands
over the below-diagonal parking functions of return composition `α.reverse` as
`∑ q ^ dinv(π) u ^ area(P_π) F_{bN, ides(π)}`.

The source uses above-diagonal parking functions. Put `m = aN` and `n = bN`. A half turn of
the rectangle sends a north-step foot `(x, y)` to `(m - x, n - 1 - y)`; complementing each label
`r` to `n + 1 - r` preserves increasing labels up columns. The rank comparisons and window tests
explained in `pointRank` show that this bijection preserves temporary dinv and its maximum;
diagram rotation preserves hooks and area. Diagonal returns are read from the other end, so
source composition `α` becomes below-diagonal composition `α.reverse`.

The fundamental terms are not individually unchanged: if the below reading word is `w`, the
above word is its reversed, label-complemented word, and its inverse descent set is
`{n - j : j ∈ ides(w)}`. In degree `n`, the operation sending `F_{n,S}` to
`F_{n,{n-j : j ∈ S}}` fixes symmetric functions: on each finite alphabet it reverses the variables.
Applying that operation to the source identity gives the displayed below-diagonal expansion.
Thus return reversal alone is not the full justification of the convention change.

The parameters are algebraically independent over `ℤ`, as required here to quote the generic
identity. Without a restriction the assertion is false, but two degenerate examples fail for
different reasons. At `q = u = 1`, all positive axis generators and all relevant slope operators
vanish; mapping every power sum to the identity operator then gives a slope map whose value on
`C_[1] 1` applied to `1` is the nonzero constant `1`, not homogeneous of positive degree `b`.
At `q = 2, u = 1` and slope `(2, 3)`, instead, `U_1 = -p_1` forces every slope map to kill
`p_1 = C_[1] 1`. That zero output is homogeneous; the rank-one shuffle equality fails because
its right side has sign extraction `1 + q = 3`. The genericity hypothesis excludes both cases. -/
@[hjo "lem_shuffle"]
def Shuffle (L : Type*) [Field L] [Algebra ℚ L] : Prop :=
  ∀ a b : ℕ, Nat.Coprime a b → 1 < a → a < b →
    ∀ q u : L, AlgebraicIndependent ℤ ![q, u] →
      ∀ (ι : Sym.Lambda L →ₐ[L] Sym.AlphabetSeries L), Sym.IsRealisation ι →
        ∀ Θ : Sym.Lambda L →ₐ[L] Module.End L (Sym.Lambda L), Sym.IsSlopeHom a b q u Θ →
          ∀ N : ℕ, 0 < N → ∀ α : List ℕ, (∀ x ∈ α, 0 < x) → α.sum = N →
            MvPolynomial.IsWeightedHomogeneous (fun i => i + 1)
                ((-1 : L) ^ (N * (b + 1)) • Θ (Sym.CopComp q α 1) 1) (b * N) ∧
              ι ((-1 : L) ^ (N * (b + 1)) • Θ (Sym.CopComp q α 1) 1) =
                ∑ π ∈ withReturns α.reverse a b N, (q ^ dinv π * u ^ area (path π)) •
                  gessel L (b * N) (ides π)

/-! ### Sign extraction reads the full-descent coefficient

I. G. Macdonald, *Symmetric Functions and Hall Polynomials*, 2nd ed., Chapter I §§3--4, with
I. M. Gessel, *Multipartite P-partitions and inner products of skew Schur functions*,
Contemp. Math. **34** (1984) 289--317. -/

/-- **Macdonald, `Symmetric Functions and Hall Polynomials`, Chapter I §§3–4, with
Gessel, `Multipartite P-partitions and inner products of skew Schur functions`**: on degree `n`
the sign extraction is the coefficient of `s_{(1ⁿ)}`, and a fundamental quasisymmetric function
contributes to it exactly when its descent set is full. So an expansion of a homogeneous `f` of
degree `n` in the fundamental quasisymmetric functions has `ε(f)` the sum of the coefficients of
those with descent set `{1, …, n - 1}`. A descent set on degree `n` is a subset of
`{1, …, n - 1}`, so only expansions whose indices `S i` are subsets of that set are read: an
index outside it is not a descent set of degree `n` and the statement says nothing about it. -/
@[hjo "lem_epsilon_gessel"]
def EpsilonGessel (L : Type*) [Field L] [Algebra ℚ L] : Prop :=
  ∀ ι : Sym.Lambda L →ₐ[L] Sym.AlphabetSeries L, Sym.IsRealisation ι →
    ∀ n : ℕ, 0 < n → ∀ (I : Type) (J : Finset I) (w : I → L) (S : I → Finset ℕ)
      (f : Sym.Lambda L), MvPolynomial.IsWeightedHomogeneous (fun i => i + 1) f n →
      (∀ i ∈ J, S i ⊆ Ico 1 n) →
      ι f = ∑ i ∈ J, w i • gessel L n (S i) →
      Sym.signExtract L f = ∑ i ∈ J with S i = Ico 1 n, w i

/-! ### The elementary symmetric functions as sums of creation seeds

F. Bergeron, A. M. Garsia, E. Leven and G. Xin, *Compositional (km,kn)-shuffle conjectures*,
arXiv:1404.4616v2, Int. Math. Res. Not. IMRN **2016** no. 14, 4229--4270, **equation (1.6)**. -/

/-- **Bergeron–Garsia–Leven–Xin, `Compositional (km,kn)-shuffle conjectures`, equation (1.6)**:
the `N`-th elementary symmetric function is the sum of the creation seeds `C_α 1` over the
compositions `α` of `N`. The source's generic identity specializes to every `q ≠ 0`, since its
coefficients are Laurent polynomials in `q`.

This formulation also includes a valid totalized extension at `q = 0`, not a literal instance
of the source's inverse notation. Then `C_r = 0` for `r ≥ 2`, while `C_1` is the Bernstein
operator with displacement `p_j ↦ p_j - z⁻ʲ`. It sends `e_n` to `e_{n+1}`, since
`∑_{j=0}^n (-1)^j e_{n-j} h_{j+1} = e_{n+1}`. Only the all-ones composition survives, giving
`C_1^N 1 = e_N`. -/
@[hjo "lem_creation_expansion"]
def CreationExpansion (L : Type*) [Field L] [Algebra ℚ L] : Prop :=
  ∀ (q : L) (N : ℕ), 0 < N →
    Sym.elemSymm L N = ∑ c : Composition N, Sym.CopComp q c.blocks 1

end HJO.External

namespace HJO.PhiMul

namespace Witness

/-! ### The model types of the specialisation -/

/-- The target of the specialisation: the field `ℚ((q))` of `q`-Laurent series, in which the
evaluated symmetric functions live. -/
abbrev Target : Type := LaurentSeries ℚ

/-- The coefficient ring: power series over `ℚ((q))` in a formal deformation variable.
It is a local ring, not a field, and taking its constant coefficient gives a specialisation to
`Target` with nonzero kernel. -/
abbrev Coeff : Type := PowerSeries Target

/-- The base field: the field of fractions of the coefficient ring. -/
abbrev Base : Type := FractionRing Coeff

end Witness

end HJO.PhiMul
