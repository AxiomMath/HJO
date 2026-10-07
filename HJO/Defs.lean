/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Mathlib.RingTheory.LaurentSeries
public import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
public import QSeriesLib.NumberTheory.HJO.Defs
public import HJO.Definitions
public import HJO.Paths.Defs
public meta import HJO.Attr

/-! # The definitions of this library

The objects the results of this library are stated in that are not already in
`HJO.Symmetric.Defs` (symmetric functions) or `HJO.Paths.Defs` (paths and parking functions): the
primitive path of an order filter, the gap poset, the unbounded cylindric series, the model types
`Target`, `Coeff` and `Base` of the specialisation, and eight results from the literature stated
as `Prop`s, each of which this library proves. The definitions the formal challenge writes out are
in `HJO.Definitions`.
-/

@[expose] public section

open Finset HJO NumericalSemigroup PowerSeries
open scoped QTheory PowerSeries.DiscreteTopology

local notation "gaps(" a ", " b ")" => NumericalSemigroup.gaps (NumericalSemigroup.finspan {a, b})

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
For coprime `1 < a < b`, on the monotonicity cone with `n_f ≤ N`, it is the expression
`[N; n] = (q)_N / (q)_{N-n_f} * P_G(n)`, where `f` is the Frobenius gap and division is by
constant-term-one power series. The difference `N-n_f` is taken in `ℤ`; a negative index makes
its extended inverse zero. The gap product likewise uses extended Pochhammer factors and
inverses that are zero at negative indices. These conventions define the value off that
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

attribute [hjo "def_balanced_profile"] profile
attribute [hjo "def_cylindric"] IsCylindric
attribute [hjo "def_cylinder_volume"] cylVolume
attribute [hjo "def_bounded_cylinder"] boundedGF

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

namespace HJO.Literature

open scoped PowerSeries.DiscreteTopology QTheory

/-! ### Huang's coercivity theorem

Y. Huang, with an appendix by K. Lau, *A quadratic form generalization of rational dinv*,
arXiv:2604.13238, Res. Math. Sci. **13** (2026) article 44, doi 10.1007/s40687-026-00631-0,
**Theorem 1.3**: the effective positive definiteness of `Q` on the monotonicity cone. -/

/-- **Huang Theorem 1.3**, specialized to integer vectors in the monotonicity cone:
`|G| · Q(𝐧) ≥ ‖𝐧‖_∞²`, expressed as a bound on every coordinate square. Huang proves this
bound on the real cone and also proves nonnegativity of the associated bilinear form on pairs
of cone vectors; those additional assertions are not included in this hypothesis. -/
@[hjo "lem_coercivity"]
def HuangCoercivity : Prop :=
  ∀ a b : ℕ, Nat.Coprime a b → 1 < a → a < b →
    ∀ n : gaps(a, b) → ℤ, n ∈ cone a b →
      ∀ i : gaps(a, b), n i ^ 2 ≤ (gaps(a, b)).card * Q a b n

/-! ### The cylindric product

O. Foda and T. A. Welsh, *Cylindric partitions, `W_r` characters and the
Andrews–Gordon–Bressoud identities*, arXiv:1510.02213, J. Phys. A **49** (2016) 164004,
doi 10.1088/1751-8113/49/16/164004, Sections 2–3, equivalently its normalized
minimal-model form, together with Y. Huang, R. Jiang and A. Oblomkov, *Quot scheme of
points on torus knot singularities*, arXiv:2608.16086v1: the standard product for the
unbounded cylindric series, in its explicit form rather than as an identification with
`charge a b`. -/

/-- **The standard cylindric product**: `(q)_∞ C_c(q)` equals
`(q^d;q^d)_∞^{a-1} / (q;q)_∞^{a-1} · ∏_{s=1}^{a-1} ∏_{v=0}^{a-1} (q^{J_{v,s}}; q^d)_∞`,
with `d = a + b`. Stated at every coprime pair satisfying `1 < a < b`. -/
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

/-- **Bergeron–Garsia–Leven–Xin, `Compositional (km,kn)-shuffle conjectures`, Theorem 5.1**: the
collinear slope operators `Q_{ka, kb}`, `k ≥ 1`, pairwise commute. Together with free generation by
the axis generators `U_1, U_2, …`, this gives an algebra homomorphism prescribed by
`U_k ↦ Q_{ka, kb}`. Bergeron–Garsia–Leven–Xin work at generic parameters. Algebraic independence
over `ℤ` guarantees both free generation and nonzero operator denominators, but is not necessary for
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

Equation (3.7) uses above-diagonal parking functions. Put `m = aN` and `n = bN`. A half turn of
the rectangle sends a north-step foot `(x, y)` to `(m - x, n - 1 - y)`; complementing each label
`r` to `n + 1 - r` preserves increasing labels up columns. The rank comparisons and window tests
explained in `pointRank` show that this bijection preserves temporary dinv and its maximum;
diagram rotation preserves hooks and area. Diagonal returns are read from the other end, so
the composition `α` of equation (3.7) becomes below-diagonal composition `α.reverse`.

The fundamental terms are not individually unchanged: if the below reading word is `w`, the
above word is its reversed, label-complemented word, and its inverse descent set is
`{n - j : j ∈ ides(w)}`. In degree `n`, the operation sending `F_{n,S}` to
`F_{n,{n-j : j ∈ S}}` fixes symmetric functions: on each finite alphabet it reverses the variables.
Applying that operation to equation (3.7) gives the displayed below-diagonal expansion.
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
compositions `α` of `N`. Their generic identity specializes to every `q ≠ 0`, since its
coefficients are Laurent polynomials in `q`.

This formulation also includes a valid totalized extension at `q = 0`, not a literal instance
of their inverse notation. Then `C_r = 0` for `r ≥ 2`, while `C_1` is the Bernstein
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
