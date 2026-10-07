/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Mathlib.Algebra.MvPolynomial.PDeriv
public import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
public import Mathlib.RingTheory.MvPowerSeries.Basic
public meta import HJO.Attr

/-! # The ring of symmetric functions and its operators

The power-sum presentation `Lambda K` of the ring of symmetric functions, its realisations in an
alphabet, the plethystic substitutions, the complete homogeneous and elementary functions, sign
extraction, the basic operators `Dop`, the split of a slope, and the slope operators `Qop` with
the creation operators `Cop`. The formulas are those of §4.1 (Symmetric functions and the slope
homomorphism) and §4.2 (The compositional theorem and sign extraction) of *Rogers-Ramanujan
identities from the geometry of `X^a = Y^b`*, referred to below as the paper.
-/

@[expose] public section

open Finset

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
power sum `p_{i+1}` to `c i * p_{i+1}`. The scaling and axis substitutions have this form; the
affine displacements `plethShift` and `plethCreate` do not. -/
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
`(m / k, n / k)`, where `k = gcd m n` is the multiplicity. The paper splits the *primitive*
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
@[hjo "def_pleth_diff_qu"]
noncomputable def plethAxis (v : L) : Lambda L →ₐ[L] Lambda L :=
  diagScale fun index => (v ^ (index + 1))⁻¹ - 1

/-- For `k ≥ 1`, the axis generator `U_k` at `v = q * u`, with the paper's formula
(4.4) `v / (v - 1) * h_k[(1 - v) / v * X]` for `v ≠ 0, 1`. The definition also assigns values at
`v = 0, 1` using totalized field division; these are not evaluations of that generic
rational formula. -/
@[hjo "def_axis_gen"]
noncomputable def axisGen (v : L) (k : ℕ) : Lambda L :=
  MvPolynomial.C (v / (v - 1)) * plethAxis v (completeHomog L k)

/-! #### The primitive recursion, run with fuel -/

/-- The slope operators computed with a fuel parameter bounding the recursion depth: for
`m ≤ 1` the basic operator `Dop q u n`, and otherwise the commutator of the two halves of
the split of `(m, n)`, normalised by `M = (1 - q) * (1 - u)`. This is the *coprime* evaluator:
at a coprime slope both halves of a split are again coprime, so it runs the paper's primitive
recursion; each half of a split has first entry in `[1, m - 1]`, so the depth is at most
`m - 1` and the `m` units of fuel that `QopPrim` supplies reach the base case. Off that domain,
and at zero fuel, its value is a totalisation with no mathematical content. -/
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

/-- The primitive evaluator: the slope operator of a *coprime* slope `(m, n)`, the paper's
primitive recursion run with `m` units of fuel. That is enough: each half of a split of
`(m, n)` has first entry in `[1, m - 1]`, so the recursion has depth at most `m - 1`, and past
that depth extra fuel changes nothing. -/
noncomputable def QopPrim (q u : L) (m n : ℕ) : Module.End L (Lambda L) := QopAux q u m m n

/-! #### The dispatch of the slope operator -/

/-- The slope operator `Qop q u m n`, for `m, n ≥ 1` together with the boundary `(1, 0)`.

At `m = 1` it is the basic operator `Dop q u n`, the paper's base case; this includes the
boundary operator `Q_{1,0} = D_0`. At `m > 1` coprime to `n` it is the paper's primitive
recursion, `QopPrim`. At `m > 1` not coprime to `n` it is the paper's noncoprime extension at
the permitted multiplicity parameter `v = 1`: writing `k = gcd m n` for the multiplicity,
`(a, b) = (m / k, n / k)` for the primitive pair and `(r, s)` for the primitive split of
`(a, b)`, the complement is `((k - 1) a + r, (k - 1) b + s) = (m - r, n - s)` and

  `Q_{m,n} = M⁻¹ (Q_{m-r,n-s} Q_{r,s} - Q_{r,s} Q_{m-r,n-s})`,   `M = (1 - q) (1 - u)`.

Both of those slopes are again coprime, so both are evaluated by `QopPrim`; that is what keeps
the noncoprime branch from being re-entered. The split is taken of the primitive pair, never of
`(m, n)`: the Bezout equation of a split has no solution at a multiplied pair.

Outside `m, n ≥ 1` the value is a totalisation carrying no claim of agreement with the paper: at
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
