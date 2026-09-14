module

-- Load-bearing for the comparator, NOT for compilation. This import fixes which
-- `PartialOrder ℤ` instance path the statements elaborate against, and `HJO/Defs.lean` must
-- resolve the same one. This file compiles without it, so `minimize_imports` reports it
-- UNUSED -- removing it changes the exported terms and the comparator then rejects
-- `HJO.Challenge.thm_finite`. Do not remove.
public import Mathlib.Data.Int.ConditionallyCompleteOrder
public import Mathlib.RingTheory.LaurentSeries
public import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
public import QSeriesLib.NumberTheory.HJO.Defs

/-! # The formal challenge file, written by humans

This is a human-written file certifying the formal statements that this repository proves: the
Huang--Jiang--Oblomkov conjecture, and the finite identity behind it, as consequences of two
results quoted from the literature -- the collinear commutativity of the slope operators and the
compositional rational shuffle identity.
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
abbrev Lambda (K : Type*) [CommRing K] : Type _ := MvPolynomial ℕ K

/-- The generator of `Lambda K` standing for the power sum `p_k`, for `k ≥ 1`. The natural
subtraction in the index means `powerSum K 0` is the same generator as `powerSum K 1`. -/
noncomputable def powerSum (K : Type*) [CommRing K] (k : ℕ) : Lambda K :=
  MvPolynomial.X (k - 1)

/-- The formal power series `K⟦x₁, x₂, …⟧` in countably many commuting variables, the
ambient ring in which the alphabet lives. -/
abbrev AlphabetSeries (K : Type*) [CommRing K] : Type _ := MvPowerSeries ℕ K

section CommRing

variable {K : Type*} [CommRing K]

/-- A `K`-algebra homomorphism from `Lambda K` to the power series in the alphabet is a
realisation when it sends the generator `p_k` to the actual power sum `∑ᵢ xᵢ ^ k`, whose
coefficients are `1` on the monomials `xᵢ ^ k` and `0` elsewhere. -/
structure IsRealisation (ι : Lambda K →ₐ[K] AlphabetSeries K) : Prop where
  /-- The monomial `xᵢ ^ (k + 1)` occurs in the image of `p_{k+1}` with coefficient `1`. -/
  coeff_pow : ∀ k i : ℕ,
    MvPowerSeries.coeff (Finsupp.single i (k + 1)) (ι (powerSum K (k + 1))) = 1
  /-- No other monomial occurs in the image of `p_{k+1}`. -/
  coeff_of_ne : ∀ (k : ℕ) (d : ℕ →₀ ℕ), (∀ i, d ≠ Finsupp.single i (k + 1)) →
    MvPowerSeries.coeff d (ι (powerSum K (k + 1))) = 0

/-- A diagonal substitution: the `K`-algebra endomorphism of `Lambda K` sending the formal
power sum `p_{i+1}` to `c i * p_{i+1}`. The coefficient of a power-sum monomial in the image is
the matching product of the scalars times its coefficient in the argument. The axis substitution
`plethAxis` has this form; the affine displacements `plethShift` and `plethCreate` do not. -/
noncomputable def diagScale (c : ℕ → K) : Lambda K →ₐ[K] Lambda K :=
  MvPolynomial.aeval fun i => MvPolynomial.C (c i) * MvPolynomial.X i

/-- The plethystic displacement `δ`, sending `p_k` to `p_k + (1 - q ^ k) * (1 - u ^ k) * z⁻ᵏ`
and written `f[X + M/z]` on elements. Its target is the polynomial ring on `w = z⁻¹`, since
only non-negative powers of `w` occur. -/
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
noncomputable def completeHomog : ℕ → Lambda K
  | 0 => 1
  | n + 1 => MvPolynomial.C (algebraMap ℚ K ((n + 1 : ℚ)⁻¹)) *
      ∑ k ∈ range (n + 1), powerSum K (k + 1) * completeHomog (n - k)
termination_by n => n
decreasing_by omega

/-- The elementary symmetric functions, defined by Newton's identity
`n * eₙ = ∑_{k=1}^{n} (-1) ^ (k - 1) * p_k * e_{n-k}` from `e₀ = 1`. -/
noncomputable def elemSymm : ℕ → Lambda K
  | 0 => 1
  | n + 1 => MvPolynomial.C (algebraMap ℚ K ((n + 1 : ℚ)⁻¹)) *
      ∑ k ∈ range (n + 1), (-1) ^ k * powerSum K (k + 1) * elemSymm (n - k)
termination_by n => n
decreasing_by omega

end Newton

/-! ### The basic operators and the split of a slope -/

section Dop

variable {K : Type*} [CommRing K] [Algebra ℚ K]

/-- The basic operator `Dop q u k`, the `K`-linear endomorphism of `Lambda K` extracting the
coefficient of `zᵏ` from `f[X + M/z] * ∑_{r ≥ 0} (-z) ^ r * e_r`. Written in `w = z⁻¹` the
coefficient of `wʲ` of the displacement is paired with `(-1) ^ (k + j) * e_{k+j}`. -/
noncomputable def Dop (q u : K) (k : ℕ) : Module.End K (Lambda K) :=
  coeffPairing (fun j => (-1) ^ (k + j) * elemSymm K (k + j)) ∘ₗ (plethShift q u).toLinearMap

end Dop

/-- The split of the slope `(m, n)`: the lexicographically least pair `(r, s)` with
`1 ≤ r < m`, `1 ≤ s < n` and `m * s + 1 = n * r` when one exists, and `(1, 0)` otherwise. -/
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
`a, b > 1`, the bounded search `Split a b` finds this pair. The wrapper makes both boundaries
explicit: at `a = 1, b ≥ 2` the raw search incorrectly defaults to `(1, 0)`, whereas at `b = 1`
its fallback `(1, 0)` is already correct. At `(1, 1)` the wrapper and search also agree. -/
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
noncomputable def axisGen (v : L) (k : ℕ) : Lambda L :=
  MvPolynomial.C (v / (v - 1)) * plethAxis v (completeHomog L k)

/-! #### The primitive recursion, run with fuel

`QopAux` is the source's primitive recursion carrying a bound on its own depth: at `m ≤ 1` the
basic operator `Dop q u n`, and otherwise the commutator of the two halves of the split of
`(m, n)`, normalised by `M = (1 - q) * (1 - u)`. It is the *coprime* evaluator: at a coprime
slope both halves of a split are again coprime, so the recursion stays on the source's domain,
and each half has first entry in `[1, m - 1]`, so the depth is at most `m - 1` and the `m`
units of fuel that `QopPrim` supplies reach the base case. Off that domain, and at zero fuel,
the value is a totalisation with no source content. -/

/-- The slope operator of `(m, n)` by the source's primitive recursion, with `fuel` bounding
the recursion depth. -/
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
primitive recursion run with `m` units of fuel. -/
noncomputable def QopPrim (q u : L) (m n : ℕ) : Module.End L (Lambda L) := QopAux q u m m n

/-! #### The dispatch of the slope operator

At `m = 1`, `Qop` is the basic operator `Dop q u n` — the source's base case, and this includes
the boundary operator `Q_{1,0} = D_0`. At `m > 1` coprime to `n` it is `QopPrim`. At `m > 1`
not coprime to `n` it is the source's noncoprime extension at the permitted multiplicity
parameter `v = 1`: with `k = gcd m n` the multiplicity, `(a, b) = (m / k, n / k)` the primitive
pair and `(r, s)` the primitive split of `(a, b)`, the complement is
`((k - 1) a + r, (k - 1) b + s) = (m - r, n - s)` and
`Q_{m,n} = M⁻¹ (Q_{m-r,n-s} Q_{r,s} - Q_{r,s} Q_{m-r,n-s})`,   `M = (1 - q) (1 - u)`.
Both of those slopes are again coprime, so both are evaluated by `QopPrim`; that is what keeps
the noncoprime branch from being re-entered. -/

/-- The slope operator `Q_{m,n}` at the slope `(m, n)`, for `m, n ≥ 1` together with the
boundary `(1, 0)`; the section above says how its three branches dispatch. Outside
`m, n ≥ 1` the value is a totalisation carrying no claim of source agreement: at `m = 0` it is
`Dop q u n`, and at `n = 0` with `m > 1` it is the noncoprime bracket with
`(r, s) = (1, 0)`. -/
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
def IsSlopeHom (a b : ℕ) (q u : L) (Θ : Lambda L →ₐ[L] Module.End L (Lambda L)) : Prop :=
  ∀ k : ℕ, 0 < k → Θ (axisGen (q * u) k) = Qop q u (a * k) (b * k)

/-- The creation displacement `δ'`, sending `p_k` to `p_k - (1 - q⁻ᵏ) * z⁻ᵏ` and written
`f[X - (1 - q⁻¹)/z]` on elements; the minus sign is a virtual difference, so it is not
squared. Its target is the polynomial ring on `w = z⁻¹`. -/
noncomputable def plethCreate (q : L) : Lambda L →ₐ[L] Polynomial (Lambda L) :=
  MvPolynomial.aeval fun i => Polynomial.C (powerSum L (i + 1)) -
    Polynomial.C (MvPolynomial.C (1 - (q ^ (i + 1))⁻¹)) * Polynomial.X ^ (i + 1)

/-- The creation operator `Cop q r`, the `L`-linear endomorphism of `Lambda L` sending `f` to
`(-q) ^ (1 - r)` times the coefficient of `zʳ` in `f[X - (1 - q⁻¹)/z] * ∑_{m ≥ 0} h_m * zᵐ`.
Written in `w = z⁻¹` the coefficient of `wʲ` of the displacement is paired with `h_{r+j}`. -/
noncomputable def Cop (q : L) (r : ℕ) : Module.End L (Lambda L) :=
  coeffPairing (fun j => MvPolynomial.C ((-q) ^ (1 - (r : ℤ))) * completeHomog L (r + j)) ∘ₗ
    (plethCreate q).toLinearMap

/-- The composite creation operator of a composition `α`, the composition
`Cop α₁ ∘ ⋯ ∘ Cop α_ℓ` of the creation operators of its parts in order. -/
noncomputable def CopComp (q : L) (α : List ℕ) : Module.End L (Lambda L) :=
  (α.map (Cop q)).prod

end Field

end HJO.Sym

namespace HJO.Paths

open Finset

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
def IsBelowDiagonal {a b N : ℕ} (y : Heights a b N) : Prop :=
  ht y 0 = 0 ∧ ht y (a * N) = b * N ∧ (∀ r < a * N, ht y r ≤ ht y (r + 1)) ∧
    ∀ r ≤ a * N, a * ht y r ≤ b * r

/-- Being a below-diagonal path is decidable, all four of its clauses being bounded arithmetic.
Without this the subtype of parking functions has no `Fintype`, and neither the `Finset.filter`
in `withReturns` and `maxTdinv` nor the sums over paths can be formed. -/
instance instDecidableIsBelowDiagonal {a b N : ℕ} (y : Heights a b N) :
    Decidable (IsBelowDiagonal y) := by
  unfold IsBelowDiagonal; infer_instance

/-- The area of a path: the number `∑_{r=1}^{aN-1} (⌊br/a⌋ - y_r)` of full lattice squares
between it and the diagonal. On paths satisfying `IsBelowDiagonal`, the column bounds make
every difference nonnegative before the natural subtraction is applied. -/
def area {a b N : ℕ} (y : Heights a b N) : ℕ := ∑ r ∈ Ico 1 (a * N), (b * r / a - ht y r)

/-- `A_i = min {r : y_r ≥ i}`, the first coordinate at which `y` reaches height `i`, taken to
be `aN` when no coordinate does. -/
def firstReach {a b N : ℕ} (y : Heights a b N) (i : ℕ) : ℕ :=
  ((List.range (a * N + 1)).find? fun r => i ≤ ht y r).getD (a * N)

/-- The arm `r - A_i` of the cell `(r, i)`, the number of cells strictly to its left in its
row of the diagram cut out by `y`. The subtraction is truncated, which is harmless on the
cells with `1 ≤ i ≤ y_r`. -/
def arm {a b N : ℕ} (y : Heights a b N) (r i : ℕ) : ℕ := r - firstReach y i

/-- The leg `y_r - i` of the cell `(r, i)`, the number of cells strictly above it in its
column of the diagram cut out by `y`. -/
def leg {a b N : ℕ} (y : Heights a b N) (r i : ℕ) : ℕ := ht y r - i

/-- The hook count `h(P)`: the number of cells `(r, i)` with `1 ≤ r < aN` and `1 ≤ i ≤ y_r`
whose arm and leg satisfy `b⋅arm ≤ a(leg + 1)` and `a⋅leg < b(arm + 1)`. The first inequality
is weak and the second strict. -/
def hookCount {a b N : ℕ} (y : Heights a b N) : ℕ :=
  #{p ∈ Ico 1 (a * N) ×ˢ Icc 1 (b * N) | p.2 ≤ ht y p.1 ∧
      b * arm y p.1 p.2 ≤ a * (leg y p.1 p.2 + 1) ∧ a * leg y p.1 p.2 < b * (arm y p.1 p.2 + 1)}

/-- `y` is a below-diagonal path whose return composition is `α`: the parts of `α` are
positive and sum to `N`, and the ranks `0 = k_0 < k_1 < ⋯ < k_ℓ = N` with `y_{ka} = kb` are
*exactly* the partial sums of `α`, so a path with an unrequested return is excluded. -/
def HasReturns {a b N : ℕ} (α : List ℕ) (y : Heights a b N) : Prop :=
  IsBelowDiagonal y ∧ (∀ x ∈ α, 0 < x) ∧ α.sum = N ∧
    ∀ k ≤ N, (ht y (a * k) = b * k ↔ k ∈ α.scanl (· + ·) 0)

/-- Having return composition `α` is decidable, the rank condition ranging over `k ≤ N` only.
This is the predicate `withReturns` filters on, so `PF^α_{aN, bN}` is a `Finset`. -/
instance instDecidableHasReturns {a b N : ℕ} (α : List ℕ) (y : Heights a b N) :
    Decidable (HasReturns α y) := by
  unfold HasReturns; infer_instance

end HJO.Paths

namespace HJO.ParkingFunctions

open Finset

/-! ### The rank of a lattice point, and why this normalization is the source's

Put `m = aN`, `n = bN`, `C = m + 1` and `A(x,y) = a*y - b*x`. For `N > 0` the source's rank
formula is `N*A(x,y) + x/C`, not `A(x,y) + x/C`, so `pointRank` is not simply its
denominator-cleared value when `N > 1`. Their order and window comparisons agree on the
rectangle nonetheless. Indeed `|Δx| ≤ m < C`, so `C*ΔA + Δx` and `C*N*ΔA + Δx` have the same
sign, determined by `(ΔA, Δx)` in lexicographic order; replacing `ΔA` by `ΔA - a` gives the
upper-window comparison, so the window `C*a` here agrees with the source's window `m = N*a`.
Both strict endpoints are preserved, including equal integral ranks and integral-rank
differences exactly `a`. For `a > 0` the rank increases up each column, which is what makes
rank-ordered labelling legal. -/

/-- The signed rank `P(x,y) = (aN + 1)(a*y - b*x) + x` of the lattice point `(x, y)`. -/
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

/-- Being a parking labelling is decidable, both clauses quantifying over the finite type
`Fin (b * N)`. With the decidability of `IsBelowDiagonal` this gives `ParkingFunction a b N`,
a subtype of a finite type, its `Fintype` instance, which every sum over it needs. -/
instance instDecidableIsParkingLabelling (y : Paths.Heights a b N)
    (lab : Fin (b * N) → Fin (b * N)) : Decidable (IsParkingLabelling y lab) := by
  unfold IsParkingLabelling; infer_instance

/-- A parking function in the `aN × bN` rectangle: a below-diagonal `(aN, bN)`-path together
with a bijective labelling of its `bN` north steps by `1, …, bN` that increases upwards along
each column. The north step whose foot is at height `s` is indexed by `s`. -/
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
def labelRank (π : ParkingFunction a b N) (i : Fin (b * N)) : ℤ :=
  stepRank π (labelStep π i)

/-- `tdinv(π)`, the number of pairs of labels `i < j` with
`rk(i) < rk(j) < rk(i) + (aN + 1)a`. With the normalization in `pointRank`, this window
implements the source's window `aN`, by the comparison argument there, not by simply scaling
the source rank. Both ends are strict and retain the horizontal perturbation: at equal integral
ranks the pair counts exactly when `i` marks the earlier column; when the integral rank of `j`
is that of `i` plus `a`, it counts exactly when `j` marks the earlier column. -/
def tdinv (π : ParkingFunction a b N) : ℕ :=
  #{p ∈ (univ : Finset (Fin (b * N) × Fin (b * N))) | p.1 < p.2 ∧
      labelRank π p.1 < labelRank π p.2 ∧ labelRank π p.2 < labelRank π p.1 + (a * N + 1) * a}

/-- `max tdinv(P)`, the largest `tdinv` of a parking function whose underlying path is `y`. It
is `0` when no parking function has underlying path `y`, that is, when `y` is not a
below-diagonal path. -/
def maxTdinv (y : Paths.Heights a b N) : ℕ :=
  ((univ : Finset (ParkingFunction a b N)).filter fun π => path π = y).sup tdinv

/-- `dinv(π) = h(P_π) + tdinv(π) - max tdinv(P_π)`, taken in `ℤ` because the difference of the
last two terms is genuine and need not be non-negative on its own. -/
def dinv (π : ParkingFunction a b N) : ℤ :=
  (Paths.hookCount (path π) : ℤ) + tdinv π - maxTdinv (path π)

/-- The north step `s` of `π` is read before the step `t`: its foot has the larger rank, or the
two ranks agree and `s` is the higher step. A column is read downwards because the rank increases
upwards along it. For `a > 0` the second clause never fires: equal perturbed ranks force equal
integral ranks and equal columns, hence the same step. -/
def ReadBefore (π : ParkingFunction a b N) (s t : Fin (b * N)) : Prop :=
  stepRank π t < stepRank π s ∨ (stepRank π s = stepRank π t ∧ t < s)

/-- The reading order of two north steps is decidable, being a comparison of integers. This is
what lets `readingWord` sort the north steps by it. -/
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
def ides (π : ParkingFunction a b N) : Finset ℕ :=
  {i ∈ Ico 1 (b * N) | (readingWord π).idxOf (i + 1) < (readingWord π).idxOf i}

/-- For `S ⊆ Ico 1 n`, Gessel's fundamental quasisymmetric function `F_{n,S}`: the sum of
`x_{i₁} ⋯ x_{iₙ}` over weakly increasing tuples that increase strictly at every `j ∈ S`.
Each such monomial arises from exactly one sorted tuple, so its coefficient is the indicator
of the corresponding exponent vectors. The definition is total for arbitrary `S`, but indices
outside `Ico 1 n` constrain the auxiliary sequence beyond the tuple; that totalization is not
asserted to be a standard fundamental function of degree `n`. -/
noncomputable def gessel (K : Type*) [CommRing K] (n : ℕ) (S : Finset ℕ) :
    Sym.AlphabetSeries K :=
  Set.indicator {d : ℕ →₀ ℕ | ∃ i : ℕ → ℕ, (∀ j ∈ Ico 1 n, i j ≤ i (j + 1)) ∧
    (∀ j ∈ S, i j < i (j + 1)) ∧ d = ∑ j ∈ Icc 1 n, Finsupp.single (i j) 1} 1

end HJO.ParkingFunctions

namespace HJO.Cylindric

open PowerSeries
open scoped PowerSeries.DiscreteTopology QTheory

/-- The balanced profile `cᵢ = ⌊(i+1)b/a⌋ - ⌊ib/a⌋`. For `a > 0` it is periodic with
period `a`, and its first `a` entries sum to `b`. -/
def profile (a b : ℕ) (i : ℕ) : ℕ := (i + 1) * b / a - i * b / a

/-- A cylindric partition with outgoing profile `c`: an `a`-tuple of partitions, written
here as one row-indexed family with the row index taken modulo `a`, in which row `i + 1`
at position `j + c i` never exceeds row `i` at position `j`. -/
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
noncomputable def cylVolume (a : ℕ) (l : ℕ → ℕ → ℕ) : ℕ := ∑ i ∈ range a, ∑ᶠ j, l i j

/-- Every entry of the cylinder is at most `N`. -/
def BoundedBy (N : ℕ) (l : ℕ → ℕ → ℕ) : Prop := ∀ i j, l i j ≤ N

/-- `C_{c,≤N}(q)`, the volume generating function of the cylindric partitions with
outgoing profile `c` whose every entry is at most `N`. A positive entry bound need not bound
the number of parts, so the definition uses a formal-series sum. At `N = 0` only the zero
cylinder contributes, giving the constant series `1`. -/
noncomputable def boundedGF (a b N : ℕ) : ℤ⟦X⟧ :=
  ∑' l : {l : ℕ → ℕ → ℕ // IsCylindric a (profile a b) l ∧ BoundedBy N l},
    X ^ cylVolume a l.val

/-- The cylindric partitions with outgoing profile `c` and every entry at most `N` are
summable by volume. A `tsum` is zero by definition when the family is not summable, so
without this `boundedGF` says nothing. -/
theorem summable_boundedGF (a b N : ℕ) (ha : 0 < a) :
    Summable fun l : {l : ℕ → ℕ → ℕ // IsCylindric a (profile a b) l ∧ BoundedBy N l} =>
      (X : ℤ⟦X⟧) ^ cylVolume a l.val :=
  sorry

/-- The cylindric partitions with outgoing profile `c` and no bound on their entries are
summable by volume. -/
theorem summable_unboundedGF (a b : ℕ) (ha : 0 < a) :
    Summable fun l : {l : ℕ → ℕ → ℕ // IsCylindric a (profile a b) l} =>
      (X : ℤ⟦X⟧) ^ cylVolume a l.val :=
  sorry

end HJO.Cylindric

namespace HJO.Finite

open PowerSeries
open scoped PowerSeries.DiscreteTopology QTheory

/-- The generalized Gaussian multinomial `[N; 𝐧]_{q;G}`: `(q)_N` divided by `(q)_{N - n_f}`,
the difference taken by truncated natural subtraction, times the product of the gap
multiplicands. The index set of `poly` requires `n_f ≤ N`. -/
noncomputable def gaussianMultinomial (a b N : ℕ) (n : gaps(a, b) → ℕ) : ℤ⟦X⟧ :=
  (X; X)_N * invOfUnit (X; X)_(N - extendNat n (a * b - a - b)) 1 *
    ∏ i : gaps(a, b), multiplicand gaps(a, b) a b (fun j => (n j : ℤ)) i

/-- `F_N(q) = N_{a,b;N}(q,1)`, the HJO polynomial at module rank `N`: the sum over
gap vectors in the monotonicity cone with `n_f ≤ N` of `[N; 𝐧]_{q;G} q^{Q(𝐧)}`. -/
noncomputable def poly (a b N : ℕ) : ℤ⟦X⟧ :=
  ∑ᶠ n ∈ {n : gaps(a, b) → ℕ |
      (fun i => (n i : ℤ)) ∈ cone a b ∧ extendNat n (a * b - a - b) ≤ N},
    gaussianMultinomial a b N n * X ^ (Q a b (fun i => (n i : ℤ))).toNat

/-- The index set of `poly` is finite, so its `finsum` is an honest `Finset` sum. A
`finsum` is zero by definition on infinite support, so without this `poly` says nothing. -/
theorem finite_index (a b N : ℕ) (hco : Nat.Coprime a b) (ha : 1 < a) (hab : a < b) :
    {n : gaps(a, b) → ℕ |
      (fun i => (n i : ℤ)) ∈ cone a b ∧ extendNat n (a * b - a - b) ≤ N}.Finite :=
  sorry

end HJO.Finite

namespace HJO.External

open ParkingFunctions Paths

/-! ### The slope operators and the shuffle identity as hypotheses

F. Bergeron, A. M. Garsia, E. Leven and G. Xin, *Compositional (km,kn)-shuffle conjectures*,
arXiv:1404.4616v2, Int. Math. Res. Not. IMRN **2016** no. 14, 4229--4270, **Theorem 5.1**, is
`CollinearCommutation`; its **equation (3.7)**, conjectured there and proved by A. Mellit,
*Toric braids and (m,n)-parking functions*, arXiv:1604.07456v1, Duke Math. J. **170** (2021)
4123--4169, **Section 6**, is `Shuffle`. Both are quoted at generic parameters, which is why
both hypotheses ask for `q` and `u` algebraically independent over `ℤ`. -/

/-! #### What the genericity hypothesis is for

Algebraic independence over `ℤ` guarantees both free generation of `Lambda L` by the axis
generators `U_1, U_2, …` and nonzero operator denominators, and is necessary for neither.
Writing `v = q * u`, for `v ≠ 0, 1` the coefficient of `p_k` in `U_k` is
`-v ^ (1 - k) (1 + v + ⋯ + v ^ (k - 1)) / k`. The other terms involve earlier power sums, so
nonvanishing of these coefficients gives an invertible triangular change of generators. It
suffices that `v` be nonzero and not a root of unity; merely `v ≠ 0, 1` is insufficient, since
at `v = -1, k = 2` the coefficient vanishes. For example, `q = 2, u = 3` already gives free
generation without algebraic independence. The recursion separately needs
`M = (1 - q)(1 - u) ≠ 0`; the genericity hypothesis supplies both conditions. -/

/-- **Collinear commutativity**: the slope operators `Q_{ka, kb}`, `k ≥ 1`, pairwise commute,
and, with free generation by the axis generators, there is an algebra homomorphism prescribed
by `U_k ↦ Q_{ka, kb}`. -/
def CollinearCommutation (L : Type*) [Field L] [Algebra ℚ L] : Prop :=
  ∀ a b : ℕ, Nat.Coprime a b → 1 < a → a < b →
    ∀ q u : L, AlgebraicIndependent ℤ ![q, u] →
      (∀ k l : ℕ, 0 < k → 0 < l →
        Commute (Sym.Qop q u (a * k) (b * k)) (Sym.Qop q u (a * l) (b * l))) ∧
        ∃ Θ : Sym.Lambda L →ₐ[L] Module.End L (Sym.Lambda L), Sym.IsSlopeHom a b q u Θ

/-! #### From the source's above-diagonal parking functions to these

Put `m = aN` and `n = bN`. A half turn of the rectangle sends a north-step foot `(x, y)` to
`(m - x, n - 1 - y)`, where the source rank is `-N*A(x,y) - x/C - m²/C`: rotation reverses the
rank order rather than preserving it. Complementing each label `r` to `n + 1 - r` therefore
still gives labels increasing up each column, and by the rank comparisons and window tests
recorded for `pointRank` this bijection preserves temporary dinv and its maximum, while
rotation of the diagram preserves hooks and area. Diagonal returns are read from the other end,
so a source composition `α` becomes the below-diagonal composition `α.reverse`. -/

/-! #### Why the fundamental terms may then be summed as they stand

They are not individually unchanged: if the below-diagonal reading word is `w`, the above one is
its reversed, label-complemented word, whose inverse descent set is `{n - j : j ∈ ides(w)}`. In
degree `n` the operation sending `F_{n,S}` to `F_{n,{n-j : j ∈ S}}` fixes symmetric functions,
since on each finite alphabet it reverses the variables; applying it to the source identity
gives the below-diagonal expansion stated here. Return reversal alone is therefore not the full
justification of the convention change. -/

/-! #### Two degenerate slope maps that the genericity hypothesis excludes

Without a restriction on the parameters the identity is false, and the two examples fail for
different reasons. At `q = u = 1` all positive axis generators and all relevant slope operators
vanish; mapping every power sum to the identity operator then gives a slope map whose value on
`C_[1] 1` applied to `1` is the nonzero constant `1`, not homogeneous of positive degree `b`.
At `q = 2, u = 1` and slope `(2, 3)`, instead, `U_1 = -p_1` forces every slope map to kill
`p_1 = C_[1] 1`. That zero output is homogeneous; the rank-one shuffle equality fails because
its right side has sign extraction `1 + q = 3`. -/

/-- **The compositional rational shuffle identity**: for a slope homomorphism `Θ` at `(a, b)`
and a composition `α` of `N`, the element `(-1) ^ (N (b + 1)) Θ(C_α 1) 1` is homogeneous of
degree `bN`, and in any realisation it expands over the below-diagonal parking functions of
return composition `α.reverse` as `∑ q ^ dinv(π) u ^ area(P_π) F_{bN, ides(π)}`. -/
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

end HJO.External

namespace HJO.PhiMul

namespace Witness

/-- The target of the specialisation: the field `ℚ((q))` of `q`-Laurent series, in which the
evaluated symmetric functions live. -/
abbrev Target : Type := LaurentSeries ℚ

/-- The coefficient ring: power series over `ℚ((q))` in a formal deformation variable.
It is a local ring, not a field. Taking the constant coefficient gives a specialisation to
`Target` with nonzero kernel. -/
abbrev Coeff : Type := PowerSeries Target

/-- The base field: the field of fractions of the coefficient ring. -/
abbrev Base : Type := FractionRing Coeff

end Witness

end HJO.PhiMul

namespace HJO.Challenge

open HJO.External HJO.PhiMul

/-- **The finite identity.** For coprime `1 < a < b` and every rank `N`, the HJO polynomial is
`(q)_N` times the generating function of the balanced cylindric partitions with largest entry at
most `N`. -/
theorem thm_finite
    (collinear : CollinearCommutation Witness.Base)
    (shuffle : Shuffle Witness.Base)
    (a b : ℕ) (hco : Nat.Coprime a b) (ha : 1 < a) (hab : a < b) (N : ℕ) :
    HJO.Finite.poly a b N = (X; X)_N * HJO.Cylindric.boundedGF a b N :=
  sorry

/-- **The Huang–Jiang–Oblomkov conjecture.** The HJO series equals the HJO product, for every
coprime `1 < a < b`. -/
theorem thm_main
    (collinear : CollinearCommutation Witness.Base)
    (shuffle : Shuffle Witness.Base)
    (a b : ℕ) (hco : Nat.Coprime a b) (ha : 1 < a) (hab : a < b) :
    Conjecture a b :=
  sorry

end HJO.Challenge
