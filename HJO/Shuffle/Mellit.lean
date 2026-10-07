/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.Evaluation.PhiPoly
public import HJO.Shuffle.ShuffleAbove
public meta import HJO.Attr

/-! # The top layer of Mellit's Section 6, as a named interface

`HJO.ShuffleAbove` — proved as `HJO.shuffleAbove`, the above-diagonal compositional rational
shuffle identity — is the main input of the shuffle side, and its proof is long. This file
formalizes the *top layer* of that proof, so that `ShuffleAbove` follows from a handful of named
statements rather than from an opaque chain of lemmas.

## What is defined outright

* `HJO.Mellit.IsAdmissibleLevel` and
  `HJO.Mellit.compColouring` are absolute definitions, relative to no further data.
* `HJO.Mellit.existsUnique_isSBParent` is proved outright: for coprime
  `m, n ≥ 1` the Stern–Brocot parent pair exists and is unique.
* `HJO.Mellit.exists_isReplicationFamily` is proved outright:
  every `HJO.Mellit.SweepSystem` carries a replication family, built by the recursion of
  `HJO.Mellit.IsReplicationFamily` on the index sum. This is why `HJO.Mellit.ReplExists` is a
  theorem here and not a hypothesis, and why the residual interface is four statements rather than
  five.
* `HJO.Mellit.SeparatesDiagonal` and `HJO.Mellit.separatesDiagonal_sepLevel` are the *separating
  property* the proof of `HJO.shuffleAbove` establishes inline for
  `η = aN + 1/2`. This is the one genuinely mathematical step of the top layer, and it is proved
  here. It is where `N ≥ 1` is used.

## The substrate

Everything else in Mellit's Sections 4–6 lives in the Carlsson–Mellit graded module
`V_k = Λ ⊗ 𝕜[y_1, …, y_k]` (`HJO.Sweep.piece`) with the operators `d_-`, `d^*_+`, `y_1`, `z_1`,
the braid trains, the characteristic function `χ` of a path and the colouring invariant
`D_{η,c}`. None of that is needed to state the top layer, and this file is kept independent of
its construction. It is therefore carried as *data*: a `HJO.Mellit.SweepSystem` bundles
exactly the operators the top layer names, and asserts no relation among them — only the three
*gradings* that `HJO.Sweep.dplusStar`, `HJO.Sweep.zop` and `HJO.Sweep.piece` write into the
operators' own definitions, which is what lets `HJO.Mellit.exists_isReplicationFamily` be proved.
Relative to such a system, `HJO.Mellit.IsReplicationFamily`,
`HJO.Mellit.replicatedLetter` and `HJO.Mellit.stage` are
genuine Lean definitions, and `HJO.Mellit.dsc` is the field `HJO.Mellit.SweepSystem.D` — it
cannot be defined without the traces and partial words of `HJO.Mellit.levelTrace` and
`HJO.Mellit.partialSweepWord`, which are not here.

Because a `SweepSystem` asserts only gradings, it introduces no falsehood; a *degenerate* one
simply cannot satisfy the interface. `HJO.Mellit.RhsSumsAgree` is the guard: its right-hand side is
written entirely in vocabulary defined independently of the system, so a system with `χ = 0`
refutes it.

Those four declarations are faithful to their sources because the substrate named above is built:
`HJO.Mellit.sweepWitness`, in `HJO.Shuffle.SweepWitness`, is a `SweepSystem` whose graded pieces are
`HJO.Sweep.piece` and whose operators are `HJO.Sweep.dplusStar`,
`HJO.Sweep.zopOneStar`, multiplication by `HJO.Sweep.auxVar 1` and the trains
`HJO.Sweep.trainDownEnd`, `HJO.Sweep.trainUpEnd` — the concrete `d^*_+`, `z_1`, `y_1`, `T_{k↘1}`,
`T_{1↗k}`. So `IsReplicationFamily`, `replicatedLetter` and `stage` read at that system are the
three definitions on the concrete objects, and `exists_isReplicationFamily` is the existence
statement there. The generality over `S` is the generality `HJO.Braid.trainUp` and
`HJO.Braid.IsBraidSystem` are already stated at.

## The interface

Six predicates, in the style of `HJO.ShuffleAbove` and `HJO.GesselReverseSum`:
`HJO.Mellit.ReplExists`, `HJO.Mellit.ReplUnique`, `HJO.Mellit.LhsRewrite`,
`HJO.Mellit.MellitInduction`, `HJO.Mellit.Rem41`, `HJO.Mellit.RhsSumsAgree`. Only four of them are
conjuncts of `HJO.Mellit.MellitInput`: `ReplExists` is a theorem, `HJO.Mellit.replExists`, and
`ReplUnique` turns out not to be used at all, for the reason recorded there. Each of the four
is a predicate encoding a lemma that the proof asserts outright, and
`HJO.Mellit.MellitInput` and the theorem below are conditional on it — the same convention
`HJO.ShuffleAbove` follows.

`HJO.Mellit.euclid` and `HJO.Mellit.braidRep_specialBraid_dplusIter` are *not* here. They are
consumed inside the proof of `HJO.Mellit.mellitInduction_sweepWitness`, not by the proof of
`HJO.shuffleAbove`, and neither is statable without the braid monoid `𝔹⁺_k(𝕋_0)`, the special-braid
data and the representation `π_k` — a substantial further construction. See the implementation
notes.

## References

The top layer of the proof in Section 6 of A. Mellit, *Toric braids and `(m, n)`-parking functions*,
arXiv:1604.07456: the definitions `HJO.Mellit.IsAdmissibleLevel`, `HJO.Mellit.dsc`,
`HJO.Mellit.compColouring`, `HJO.Mellit.IsReplicationFamily`, `HJO.Mellit.replicatedLetter`,
`HJO.Mellit.stage` and the lemmas `HJO.Mellit.exists_isReplicationFamily`,
`HJO.Mellit.IsReplicationFamily.eq_index_one`,
`HJO.Mellit.isAdmissibleColouring_and_sum_sweepChar_eq_smul_dsc`,
`HJO.Mellit.mellitInduction_sweepWitness`, `HJO.Mellit.lhsRewrite_sweepWitness`,
`HJO.Mellit.sum_sweepChar_eq_sum_gessel`, `HJO.shuffleAbove`.

## Implementation notes

`HJO.Mellit.compColouring` uses truncated subtraction in `a * A_i - 1`. That never bites where it
is used: the standing hypothesis is `1 < a` and every part of a composition is positive,
so `a * A_i ≥ 1` for `i ≥ 1`. The definition is nevertheless stated over `ℕ × ℕ` rather than
`ℤ × ℤ` so that a colouring is comparable with `HJO.Paths.northSteps`, which is where
`HJO.Mellit.colouring` reads its members from.

Defects are recorded at the declarations they concern: `HJO.Mellit.Rem41` (the missing realisation),
`HJO.Mellit.RhsSumsAgree` (the inert realisation, which this predicate omits) and
`HJO.Mellit.MellitInput` (`HJO.shuffleAbove` consumes `HJO.gessel_reverse_sum`).

One of them concerns the parameters, and it would be a falsehood: quantified over *all*
`q u : L`, three of the four clauses of `HJO.Mellit.MellitInput` are jointly contradictory.
`HJO.Mellit.not_mellitInput_unrestricted`, in the module `HJO.Shuffle.MellitAtZero`, is the
witness. The parameters are therefore generic, as the standing coefficient field `ℚ(q, u)` makes
them.
-/

@[expose] public section

open Finset

namespace HJO.Mellit

open ParkingFunctions Paths

/-! ### Admissible levels and the separating property -/

/-- **Admissible level.** `HJO.Mellit.IsAdmissibleLevel`: a half-integer, that is an
element of `ℤ + 1/2`. A level must be allowed to be a half-integer rather than an integer because
integers do not separate adjacent above-diagonal ranks. -/
@[hjo "def_colouring_level"]
def IsAdmissibleLevel (η : ℚ) : Prop := ∃ n : ℤ, η = n + 1 / 2

/-- The separating property of a level that
`HJO.Mellit.isAdmissibleColouring_and_sum_sweepChar_eq_smul_dsc` and
`HJO.Mellit.mellitInduction_sweepWitness` require: among the lattice points of the `aN × bN`
rectangle weakly above the diagonal, the ones whose above-diagonal rank exceeds `η` are exactly the
ones strictly above it. -/
def SeparatesDiagonal (a b N : ℕ) (η : ℚ) : Prop :=
  ∀ x y : ℕ, x ≤ a * N → y ≤ b * N → (b : ℤ) * x ≤ (a : ℤ) * y →
    (η < (abovePointRank a b N x y : ℚ) ↔ (b : ℤ) * x < (a : ℤ) * y)

/-- The level `η := aN + 1/2` that the proof of `HJO.shuffleAbove` uses. -/
def sepLevel (a N : ℕ) : ℚ := (a : ℚ) * (N : ℚ) + 1 / 2

/-- **`η := aN + 1/2` is an admissible level.** -/
theorem isAdmissibleLevel_sepLevel (a N : ℕ) : IsAdmissibleLevel (sepLevel a N) :=
  ⟨a * N, by simp only [sepLevel]; push_cast; ring⟩

/-- **`η := aN + 1/2` separates the diagonal.** This is the inline step of the proof
of `HJO.shuffleAbove`: by `HJO.ParkingFunctions.abovePointRank` the above-diagonal rank of a lattice
point is `(aN+1)N(ay - bx) + x`, so a point of the region with `ay = bx` has rank `x ≤ aN < η`,
while one with `ay > bx` has `ay - bx ≥ 1` and therefore rank at least `(aN+1)N ≥ aN+1 > η`.

The middle inequality is exactly where `N ≥ 1` is used, and it is false without it: at `N = 0` the
bound `(aN+1)N = 0` is not `> η = 1/2`. The statement `HJO.shuffleAbove` assumes `N ≥ 1`, so
this is not a defect there; `HJO.Mellit.isAdmissibleColouring_and_sum_sweepChar_eq_smul_dsc` and
`HJO.Mellit.mellitInduction_sweepWitness` take the separating property as a hypothesis and so need
no such side condition of their own. -/
theorem separatesDiagonal_sepLevel {a b N : ℕ} (hN : 0 < N) :
    SeparatesDiagonal a b N (sepLevel a N) := by
  have key : ∀ z : ℤ, (sepLevel a N < (z : ℚ)) ↔ (a : ℤ) * N < z := by
    intro z
    simp only [sepLevel]
    constructor
    · intro h
      by_contra hc
      rw [not_lt] at hc
      have hc' : (z : ℚ) ≤ (a : ℚ) * (N : ℚ) := by
        have : (z : ℚ) ≤ (((a : ℤ) * N : ℤ) : ℚ) := by exact_mod_cast hc
        push_cast at this
        exact this
      linarith
    · intro h
      have h1 : (a : ℚ) * (N : ℚ) + 1 ≤ (z : ℚ) := by
        have h2 : ((((a : ℤ) * N + 1 : ℤ)) : ℚ) ≤ (z : ℚ) := by
          exact_mod_cast (by omega : (a : ℤ) * N + 1 ≤ z)
        push_cast at h2
        exact h2
      linarith
  intro x y hx _ hxy
  have hx' : (x : ℤ) ≤ (a : ℤ) * N := by
    have : (x : ℤ) ≤ ((a * N : ℕ) : ℤ) := by exact_mod_cast hx
    push_cast at this
    exact this
  have hN' : (1 : ℤ) ≤ (N : ℤ) := by exact_mod_cast hN
  have hx0 : (0 : ℤ) ≤ (x : ℤ) := Int.natCast_nonneg x
  have hA0 : (0 : ℤ) ≤ (a : ℤ) * N := by positivity
  rw [abovePointRank, key]
  have hd0 : (0 : ℤ) ≤ (a : ℤ) * y - (b : ℤ) * x := sub_nonneg.2 hxy
  constructor
  · intro h
    rcases hd0.lt_or_eq with h0 | h0
    · omega
    · exfalso
      rw [← h0] at h
      simp only [mul_zero, zero_add] at h
      omega
  · intro h
    have hd1 : (1 : ℤ) ≤ (a : ℤ) * y - (b : ℤ) * x := by omega
    have hAN : (0 : ℤ) ≤ ((a : ℤ) * N + 1) * N := by nlinarith
    have s1 : ((a : ℤ) * N + 1) * N * 1
        ≤ ((a : ℤ) * N + 1) * N * ((a : ℤ) * y - (b : ℤ) * x) :=
      mul_le_mul_of_nonneg_left hd1 hAN
    have s2 : ((a : ℤ) * N + 1) * 1 ≤ ((a : ℤ) * N + 1) * N :=
      mul_le_mul_of_nonneg_left hN' (by linarith)
    linarith

/-! ### The colouring of a composition -/

/-- **The colouring of a composition.** `HJO.Mellit.compColouring`: writing
`A_0 = 0` and `A_i = α_1 + ⋯ + α_i`,
`c_α = {(aA_{i-1}, bA_{i-1}) : 1 ≤ i ≤ ℓ} ∪ {(aA_i - 1, bA_i) : 1 ≤ i ≤ ℓ}`.

The first family lists the feet of the north steps leaving the diagonal touch points, the second
the feet of the east steps arriving at them. -/
@[hjo "def_mellit_comp_colouring"]
def compColouring (a b : ℕ) (α : List ℕ) : Finset (ℕ × ℕ) :=
  ((range α.length).image fun i => (a * (α.take i).sum, b * (α.take i).sum)) ∪
    ((range α.length).image fun i => (a * (α.take (i + 1)).sum - 1, b * (α.take (i + 1)).sum))

/-- The above-diagonal `(aN, bN)`-paths whose return composition is `α`, the index set of the
left-hand sums of `HJO.Mellit.isAdmissibleColouring_and_sum_sweepChar_eq_smul_dsc` and
`HJO.Mellit.sum_sweepChar_eq_sum_gessel`. -/
def aboveReturnPaths (a b N : ℕ) (α : List ℕ) : Finset (Paths.Heights a b N) :=
  univ.filter fun y => Paths.IsAboveDiagonal y ∧ Paths.HasAboveReturns α y

/-! ### The Carlsson–Mellit substrate, as data -/

universe w

/-- **The Carlsson–Mellit sweep substrate, carried as data.** The graded module
`V_k = Λ ⊗ 𝕜[y_1, …, y_k]` of `HJO.Sweep.piece` inside one total space `W`, together with
exactly the operators the top layer of Mellit's Section 6 names:

* `vac` — the vacuum `1 ∈ V_0`;
* `proj` — the reading of `V_0 = Λ` back in `Λ`, which is where `d_-^ℓ` lands;
* `dminus` — the lowering operator `d_-` of `HJO.Sweep.dminus`;
* `dplusStar` — the conjugate raising operator `d^*_+` of `HJO.Sweep.dplusStar`;
* `y1`, `z1` — multiplication by `y_1` and the conjugate commuting operator of `HJO.Sweep.zop`;
* `trainDown k`, `trainUp k` — the braid trains `T_{k↘1}` and `T_{1↗k}`;
* `chi` — the characteristic function `χ` of `HJO.Paths.sweepChar`, an element of `𝒫`;
* `D` — the colouring invariant `D_{η,c}` of `HJO.Mellit.dsc`.

No *relation* among them is asserted: this is the vocabulary the interface predicates are written
in, not a claim about it. In particular the structure exhibits no `SweepSystem`; the concrete one
is `HJO.Mellit.sweepWitness`, and showing that it satisfies the interface is the substance of the
proof.

What *is* asserted is the three **gradings** — `shape_dplusStar`, `shape_z1`, `shape_y1` — of the
last three fields. These are not relations and they are not lemmas: they are the domains and
codomains written into the definitions of the operators themselves, so every faithful sweep system
satisfies them by construction. They are recorded here because
`HJO.Mellit.exists_isReplicationFamily` needs them and nothing weaker will do: the shape clauses of
`HJO.Mellit.IsReplicationFamily` are those of the definition, and a composite of maps with no
declared grading has no grading. See each field's docstring for the grading it records. -/
structure SweepSystem (L : Type w) [Field L] [Algebra ℚ L] (q u : L) where
  /-- The total space `V_* = ⋃_k V_k`. -/
  W : Type w
  /-- The additive structure of `W`. -/
  [addCommGroup : AddCommGroup W]
  /-- The `L`-module structure of `W`. -/
  [modL : Module L W]
  /-- The graded pieces `V_k` of `HJO.Sweep.piece`. -/
  V : ℕ → Submodule L W
  /-- The vacuum `1 ∈ V_0`. -/
  vac : W
  /-- Reading an element of `V_0 = Λ` back in `Λ`. -/
  proj : W →ₗ[L] Sym.Lambda L
  /-- The lowering operator `d_-` of `HJO.Sweep.dminus`. -/
  dminus : W →ₗ[L] W
  /-- The conjugate raising operator `d^*_+` of `HJO.Sweep.dplusStar`. -/
  dplusStar : W →ₗ[L] W
  /-- Multiplication by `y_1`. -/
  y1 : W →ₗ[L] W
  /-- The conjugate commuting operator `z_1` of `HJO.Sweep.zop`. -/
  z1 : W →ₗ[L] W
  /-- The descending braid train `T_{k↘1}`. -/
  trainDown : ℕ → (W →ₗ[L] W)
  /-- The ascending braid train `T_{1↗k}`. -/
  trainUp : ℕ → (W →ₗ[L] W)
  /-- The characteristic function `χ` of a path, `HJO.Paths.sweepChar`. -/
  chi : ∀ a b N : ℕ, Paths.Heights a b N → Sym.AlphabetSeries L
  /-- The colouring invariant `D_{η,c}` of `HJO.Mellit.dsc`. -/
  D : ℚ → Finset (ℕ × ℕ) → W
  /-- **The grading of `d^*_+`.** The definition of `d^*_+` (`HJO.Sweep.dplusStar`) reads "For
  `k ≥ 0`, `d^*_+` is the `𝕜`-linear map from `V_k` to `V_{k+1}` with
  `d^*_+ F = cy_{k+1}(τ_{k+1,k+1}(F))`": the source of
  `d^*_+` is `V_k` and its target is `V_{k+1}`, for every `k ≥ 0`. -/
  shape_dplusStar : ∀ k : ℕ, (V k).map dplusStar ≤ V (k + 1)
  /-- **The grading of `z_1`.** `HJO.Sweep.zop` reads "For `k ≥ 1`, `z_1` is the `𝕜`-linear
  endomorphism `q^k/(1-q) (d^*_+ d_- - d_- d^*_+) T^{-1}_{k↘1}` of `V_k`": `z_1` is an endomorphism
  of `V_k`, for every `k ≥ 1`. -/
  shape_z1 : ∀ k : ℕ, (V (k + 1)).map z1 ≤ V (k + 1)
  /-- **The grading of multiplication by `y_1`.** `HJO.Sweep.piece` reads
  "For `k ≥ 0`, `V_k := Λ ⊗_𝕜 𝕜[y_1, …, y_k]`", so for `k ≥ 1` the variable `y_1` is one of the
  ring's own generators and multiplication by it is an endomorphism of `V_k`. This is the shape
  `HJO.Mellit.IsReplicationFamily` declares of its own third base value — "`Ω(j;m,n)` from `V_k` to
  `V_k` for `j ∈ {2,3}` and every `k ≥ 1` … `Ω(3;0,1) = y_1`, `y_1` meaning multiplication by `y_1`"
  — and the proof of `HJO.Mellit.exists_isReplicationFamily` cites `HJO.Sweep.piece` for it. -/
  shape_y1 : ∀ k : ℕ, (V (k + 1)).map y1 ≤ V (k + 1)

attribute [instance] SweepSystem.addCommGroup SweepSystem.modL

variable {L : Type w} [Field L] [Algebra ℚ L] {q u : L}

/-- The Stern–Brocot parent relation: `(m₁, n₁)` is *the* pair with `0 ≤ m₁ ≤ m`, `0 ≤ n₁ ≤ n` and
`m n₁ - n m₁ = 1`, whose uniqueness is `HJO.Mellit.existsUnique_isSBParent`. Carrying it as a
relation rather than as a function is what lets `IsReplicationFamily` be stated without that
lemma. -/
def IsSBParent (m n m₁ n₁ : ℕ) : Prop :=
  m₁ ≤ m ∧ n₁ ≤ n ∧ (m : ℤ) * n₁ - (n : ℤ) * m₁ = 1

/-- **The Stern–Brocot parent pair is unique.** The uniqueness half of
`HJO.Mellit.existsUnique_isSBParent`, which needs only `m ≥ 1`: if `m n₁ - n m₁ = m n₁' - n m₁' = 1`
then `m ∣ m₁ - m₁'`, and `0 ≤ m₁, m₁' ≤ m` leaves `m₁ = m₁'` or `{m₁, m₁'} = {0, m}`; the latter
forces `m(n₁ - n) = 1`, hence `m = 1` and `n₁ = n + 1 > n`, out of range. -/
theorem isSBParent_unique {m n m₁ n₁ m₁' n₁' : ℕ} (hmn : Nat.Coprime m n) (hm : 1 ≤ m)
    (h : IsSBParent m n m₁ n₁) (h' : IsSBParent m n m₁' n₁') : m₁ = m₁' ∧ n₁ = n₁' := by
  obtain ⟨hm1, hn1, he⟩ := h
  obtain ⟨hm1', hn1', he'⟩ := h'
  have hdvd : (m : ℤ) ∣ ((m₁ : ℤ) - m₁') := by
    have hc : IsCoprime (m : ℤ) (n : ℤ) := Nat.isCoprime_iff_coprime.mpr hmn
    have hd : (m : ℤ) ∣ (n : ℤ) * ((m₁ : ℤ) - m₁') := ⟨(n₁ : ℤ) - n₁', by linarith⟩
    exact hc.dvd_of_dvd_mul_left hd
  have hmpos : (0 : ℤ) < m := by exact_mod_cast hm
  have hmm : (m₁ : ℤ) = m₁' := by
    rcases hdvd with ⟨c, hc⟩
    have hb1 : (m₁ : ℤ) ≤ m := by exact_mod_cast hm1
    have hb2 : (m₁' : ℤ) ≤ m := by exact_mod_cast hm1'
    have hb3 : (0 : ℤ) ≤ m₁ := Int.natCast_nonneg _
    have hb4 : (0 : ℤ) ≤ m₁' := Int.natCast_nonneg _
    have hcc : c = -1 ∨ c = 0 ∨ c = 1 := by
      rcases lt_trichotomy c 0 with h1 | h1 | h1
      · left
        by_contra hne
        have : c ≤ -2 := by omega
        nlinarith
      · exact Or.inr (Or.inl h1)
      · refine Or.inr (Or.inr ?_)
        by_contra hne
        have : 2 ≤ c := by omega
        nlinarith
    rcases hcc with rfl | rfl | rfl
    · exfalso
      have h1 : (m₁' : ℤ) = m := by linarith
      rw [h1] at he'
      have hone : (m : ℤ) * ((n₁' : ℤ) - n) = 1 := by linarith
      have hm' : (m : ℤ) = 1 := Int.eq_one_of_mul_eq_one_right (le_of_lt hmpos) hone
      rw [hm'] at hone
      have : (n₁' : ℤ) ≤ n := by exact_mod_cast hn1'
      linarith
    · linarith
    · exfalso
      have h1 : (m₁ : ℤ) = m := by linarith
      rw [h1] at he
      have hone : (m : ℤ) * ((n₁ : ℤ) - n) = 1 := by linarith
      have hm' : (m : ℤ) = 1 := Int.eq_one_of_mul_eq_one_right (le_of_lt hmpos) hone
      rw [hm'] at hone
      have : (n₁ : ℤ) ≤ n := by exact_mod_cast hn1
      linarith
  have hnn : (n₁ : ℤ) = n₁' := by
    have hz : (m : ℤ) * ((n₁ : ℤ) - n₁') = 0 := by rw [hmm] at he; linarith
    rcases mul_eq_zero.mp hz with h1 | h1
    · linarith
    · linarith
  exact ⟨by exact_mod_cast hmm, by exact_mod_cast hnn⟩

/-- **A Stern–Brocot parent pair exists.** The existence half of
`HJO.Mellit.existsUnique_isSBParent`: Bézout gives `m A + n B = 1`; reducing `-B` modulo `m`
replaces `(−B, A)` by a pair `(m₁, n₁)` with `0 ≤ m₁ ≤ m - 1`, and then `m n₁ = 1 + n m₁` is between
`1` and `nm`, so `0 ≤ n₁ ≤ n`. -/
theorem exists_isSBParent {m n : ℕ} (hmn : Nat.Coprime m n) (hm : 1 ≤ m) (hn : 1 ≤ n) :
    ∃ m₁ n₁ : ℕ, IsSBParent m n m₁ n₁ := by
  have hmpos : (0 : ℤ) < m := by exact_mod_cast hm
  have hnpos : (0 : ℤ) < n := by exact_mod_cast hn
  have hb : (m : ℤ) * Nat.gcdA m n + (n : ℤ) * Nat.gcdB m n = 1 := by
    have h := Nat.gcd_eq_gcd_ab m n
    rw [Nat.Coprime.gcd_eq_one hmn] at h
    push_cast at h
    linarith
  set A := Nat.gcdA m n with hA
  set B := Nat.gcdB m n with hB
  set M1 : ℤ := (-B) % (m : ℤ) with hM1def
  set κ : ℤ := (-B) / (m : ℤ) with hκdef
  have hsplit : M1 + (m : ℤ) * κ = -B := Int.emod_add_mul_ediv _ _
  have h0 : 0 ≤ M1 := Int.emod_nonneg _ (by positivity)
  have h1 : M1 < m := Int.emod_lt_of_pos _ hmpos
  set N1 : ℤ := A - (n : ℤ) * κ with hN1def
  have hkey : (m : ℤ) * N1 - (n : ℤ) * M1 = 1 := by
    have hM : M1 = -B - (m : ℤ) * κ := by linarith
    rw [hN1def, hM]
    ring_nf
    linarith
  have hN1pos : 0 ≤ N1 := by
    by_contra hcon
    have hle : N1 ≤ 0 := by linarith [not_lt.mp (fun h => hcon (le_of_lt h))]
    nlinarith
  have hN1le : N1 ≤ n := by
    by_contra hcon
    have h2 : (n : ℤ) + 1 ≤ N1 := by omega
    nlinarith
  refine ⟨M1.toNat, N1.toNat, ?_, ?_, ?_⟩
  · have hc : (M1.toNat : ℤ) ≤ (m : ℤ) := by rw [Int.toNat_of_nonneg h0]; linarith
    exact_mod_cast hc
  · have hc : (N1.toNat : ℤ) ≤ (n : ℤ) := by rw [Int.toNat_of_nonneg hN1pos]; linarith
    exact_mod_cast hc
  · rw [Int.toNat_of_nonneg h0, Int.toNat_of_nonneg hN1pos]
    exact hkey

/-- **The Stern–Brocot parent pair is unique.** `HJO.Mellit.existsUnique_isSBParent`: for
coprime `m, n ≥ 1` there is exactly one pair `(m₁, n₁)` with `0 ≤ m₁ ≤ m`, `0 ≤ n₁ ≤ n` and
`m n₁ - n m₁ = 1`. This is what makes the three rules of `HJO.Mellit.IsReplicationFamily` a
definition rather than a family of constraints, and it is what
`HJO.Mellit.exists_isReplicationFamily` recurses on. -/
@[hjo "lem_mellit_repl_parents"]
theorem existsUnique_isSBParent {m n : ℕ} (hmn : Nat.Coprime m n) (hm : 1 ≤ m) (hn : 1 ≤ n) :
    ∃! p : ℕ × ℕ, IsSBParent m n p.1 p.2 := by
  obtain ⟨m₁, n₁, h⟩ := exists_isSBParent hmn hm hn
  refine ⟨(m₁, n₁), h, fun p hp => ?_⟩
  obtain ⟨e1, e2⟩ := isSBParent_unique hmn hm hp h
  exact Prod.ext e1 e2

/-- **A replication family.** `HJO.Mellit.IsReplicationFamily`, read on a `SweepSystem`:
an assignment `Ω(j; m, n)` for `j ∈ {1, 2, 3}` and coprime `(m, n)` with `m + n ≥ 1`, pinned at
the three base values `Ω(1;1,0) = d^*_+`, `Ω(2;1,0) = z_1`, `Ω(3;0,1) = y_1` and satisfying the
three Stern–Brocot recursions.

The shape conditions — `Ω(1; m, n)` raising `V_k` into `V_{k+1}` and the other two preserving
`V_{k+1}` — are included, since the definition carries them; nothing below uses
them.

**Why this is the intended definition.** The definition is read relative to a `SweepSystem` rather
than written out on one fixed module, and the concrete objects are an instance of it:
`HJO.Mellit.sweepWitness` is a `SweepSystem` whose `V_k` is `HJO.Sweep.piece`,
whose `dplusStar` is `HJO.Sweep.dplusStar`, whose `z1` is
`HJO.Sweep.zopOneStar` of `HJO.Sweep.zop` and whose `y1` is multiplication by `HJO.Sweep.auxVar 1`.
So `IsReplicationFamily (sweepWitness q u a b)` *is* `HJO.Mellit.IsReplicationFamily` on the
concrete operators, and the generality over `S` is the same generality `HJO.Braid.trainUp` and
`HJO.Braid.IsBraidSystem` are already stated at in `HJO.Shuffle.BraidTrain`.

Two Lean conventions the definition does not fix, neither of which introduces a falsehood.
`(qu)⁻¹` is `0` at `qu = 0`, where the coefficient field has `q` and `u` algebraically
independent; at that corner `rule_three` reads `Ω(3;m,n) = 0`, and a family still exists
(`HJO.Mellit.exists_isReplicationFamily`). And the three `shape_*` fields are quantified over all
`(m, n)` rather than only the coprime pairs with `m + n ≥ 1`, which is more than the definition asks
and is satisfied by the family built below. -/
@[hjo "def_mellit_repl_family"]
structure IsReplicationFamily (S : SweepSystem L q u)
    (Ω : ℕ → ℕ → ℕ → (S.W →ₗ[L] S.W)) : Prop where
  /-- `Ω(1; m, n)` raises the grading by one. -/
  shape_one : ∀ m n k : ℕ, (S.V k).map (Ω 1 m n) ≤ S.V (k + 1)
  /-- `Ω(2; m, n)` preserves the grading. -/
  shape_two : ∀ m n k : ℕ, (S.V (k + 1)).map (Ω 2 m n) ≤ S.V (k + 1)
  /-- `Ω(3; m, n)` preserves the grading. -/
  shape_three : ∀ m n k : ℕ, (S.V (k + 1)).map (Ω 3 m n) ≤ S.V (k + 1)
  /-- `Ω(1; 1, 0) = d^*_+`. -/
  base_one : Ω 1 1 0 = S.dplusStar
  /-- `Ω(2; 1, 0) = z_1`. -/
  base_two : Ω 2 1 0 = S.z1
  /-- `Ω(3; 0, 1) = y_1`. -/
  base_three : Ω 3 0 1 = S.y1
  /-- `Ω(1; m, n) = -Ω(3; m₁, n₁) Ω(1; m₂, n₂)`. -/
  rule_one : ∀ m n m₁ n₁ : ℕ, Nat.Coprime m n → 1 ≤ m → 1 ≤ n → IsSBParent m n m₁ n₁ →
    Ω 1 m n = -(Ω 3 m₁ n₁ ∘ₗ Ω 1 (m - m₁) (n - n₁))
  /-- `Ω(2; m, n) = -Ω(3; m₁, n₁) Ω(2; m₂, n₂)`. -/
  rule_two : ∀ m n m₁ n₁ : ℕ, Nat.Coprime m n → 1 ≤ m → 1 ≤ n → IsSBParent m n m₁ n₁ →
    Ω 2 m n = -(Ω 3 m₁ n₁ ∘ₗ Ω 2 (m - m₁) (n - n₁))
  /-- `Ω(3; m, n) = -(qu)^{-1} Ω(2; m₂, n₂) Ω(3; m₁, n₁)`. -/
  rule_three : ∀ m n m₁ n₁ : ℕ, Nat.Coprime m n → 1 ≤ m → 1 ≤ n → IsSBParent m n m₁ n₁ →
    Ω 3 m n = -((q * u)⁻¹ • (Ω 2 (m - m₁) (n - n₁) ∘ₗ Ω 3 m₁ n₁))

/-! ### A replication family exists

`HJO.Mellit.exists_isReplicationFamily`, proved rather than assumed. The recursion of
`HJO.Mellit.IsReplicationFamily` is structural on the index sum `m + n`, so it is run here on a fuel
parameter and the family is read off at fuel `m + n`; the grading conditions come from the three
`shape_*` fields of `SweepSystem`, which are the ones written into the definitions of
`d^*_+`, `z_1` and `y_1`.

This statement is load-bearing rather than bookkeeping: every statement below
it is of the form "let `Ω` be a replication family", so with no instance exhibited each of them
would be vacuously true and the whole chain would prove nothing. -/

/-! #### Gradings of composites -/

section Shapes

variable {S : SweepSystem L q u}

/-- The zero map lands inside every graded piece. -/
private theorem map_zero_le {p r : Submodule L S.W} :
    p.map (0 : S.W →ₗ[L] S.W) ≤ r := by
  intro x hx
  obtain ⟨y, hy, rfl⟩ := hx
  simp

/-- Negation does not change where a map lands. -/
private theorem map_neg_le {p r : Submodule L S.W} {f : S.W →ₗ[L] S.W} (h : p.map f ≤ r) :
    p.map (-f) ≤ r := by
  intro x hx
  obtain ⟨y, hy, rfl⟩ := hx
  rw [LinearMap.neg_apply]
  exact neg_mem (h ⟨y, hy, rfl⟩)

/-- Scaling does not change where a map lands. -/
private theorem map_smul_le {p r : Submodule L S.W} {f : S.W →ₗ[L] S.W} (c : L)
    (h : p.map f ≤ r) : p.map (c • f) ≤ r := by
  intro x hx
  obtain ⟨y, hy, rfl⟩ := hx
  rw [LinearMap.smul_apply]
  exact r.smul_mem c (h ⟨y, hy, rfl⟩)

/-- A composite lands where the outer map sends the intermediate piece. -/
private theorem map_comp_le {p r s : Submodule L S.W} {f g : S.W →ₗ[L] S.W}
    (hf : p.map f ≤ s) (hg : s.map g ≤ r) : p.map (g ∘ₗ f) ≤ r := by
  rw [Submodule.map_comp]
  exact le_trans (Submodule.map_mono hf) hg

end Shapes

/-! #### The Stern–Brocot recursion descends -/

/-- **The Stern–Brocot parent pair descends.** For `m, n ≥ 1` a parent pair `(m₁, n₁)` and its
complement `(m₂, n₂) = (m - m₁, n - n₁)` both have index sum strictly below `m + n`: neither is
`(0,0)`, since `m·0 - n·0 = 0 ≠ 1`, nor is `(m₁, n₁) = (m, n)`, since `m·n - n·m = 0 ≠ 1`, and the
two sums add to `m + n`. This is what makes the recursion of `HJO.Mellit.IsReplicationFamily` a
definition. -/
theorem isSBParent_sum_lt {m n m₁ n₁ : ℕ} (hm : 1 ≤ m) (hn : 1 ≤ n)
    (h : IsSBParent m n m₁ n₁) :
    m₁ + n₁ < m + n ∧ (m - m₁) + (n - n₁) < m + n := by
  obtain ⟨h1, h2, h3⟩ := h
  have hA : ¬(m₁ = 0 ∧ n₁ = 0) := by
    rintro ⟨rfl, rfl⟩
    simp at h3
  have hB : ¬(m₁ = m ∧ n₁ = n) := by
    rintro ⟨rfl, rfl⟩
    have : (0 : ℤ) = 1 := by linear_combination h3
    exact absurd this (by norm_num)
  omega

/-- A pair that is a Stern–Brocot parent pair of `(m, n)` whenever `(m, n)` has one. Stated this
way so that `sbParent` is total without a decidability instance. -/
theorem exists_sbParent (m n : ℕ) :
    ∃ p : ℕ × ℕ, Nat.Coprime m n → 1 ≤ m → 1 ≤ n → IsSBParent m n p.1 p.2 := by
  by_cases h : Nat.Coprime m n ∧ 1 ≤ m ∧ 1 ≤ n
  · obtain ⟨m₁, n₁, hp⟩ := exists_isSBParent h.1 h.2.1 h.2.2
    exact ⟨(m₁, n₁), fun _ _ _ => hp⟩
  · exact ⟨(0, 0), fun h1 h2 h3 => absurd ⟨h1, h2, h3⟩ h⟩

/-- **The Stern–Brocot parent pair, as a function.** For coprime `m, n ≥ 1` this is the unique pair
of `existsUnique_isSBParent`; off that range it is arbitrary, and the recursion never reads it
there. -/
noncomputable def sbParent (m n : ℕ) : ℕ × ℕ := (exists_sbParent m n).choose

/-- **`sbParent` is a Stern–Brocot parent pair.** -/
theorem isSBParent_sbParent {m n : ℕ} (hmn : Nat.Coprime m n) (hm : 1 ≤ m) (hn : 1 ≤ n) :
    IsSBParent m n (sbParent m n).1 (sbParent m n).2 :=
  (exists_sbParent m n).choose_spec hmn hm hn

/-- **`sbParent` is *the* Stern–Brocot parent pair.** Any pair satisfying `IsSBParent` is this
one, by the uniqueness half of `HJO.Mellit.existsUnique_isSBParent`. -/
theorem sbParent_eq {m n m₁ n₁ : ℕ} (hmn : Nat.Coprime m n) (hm : 1 ≤ m) (hn : 1 ≤ n)
    (h : IsSBParent m n m₁ n₁) : sbParent m n = (m₁, n₁) := by
  obtain ⟨e1, e2⟩ := isSBParent_unique hmn hm (isSBParent_sbParent hmn hm hn) h
  exact Prod.ext e1 e2

/-! #### One step of the recursion -/

/-- **One step of the recursion of `HJO.Mellit.IsReplicationFamily`.** Given the values of the
family at every smaller index sum, as `g`, this is the value at `(j; m, n)`: the three base values
at `m + n = 1`, the three displayed rules at coprime `(m, n)` with `m, n ≥ 1`, and zero at the
triples the definition imposes nothing on. -/
noncomputable def omegaStep (S : SweepSystem L q u)
    (g : ℕ → ℕ → ℕ → (S.W →ₗ[L] S.W)) (j m n : ℕ) : S.W →ₗ[L] S.W :=
  if j = 1 ∧ m = 1 ∧ n = 0 then S.dplusStar
  else if j = 2 ∧ m = 1 ∧ n = 0 then S.z1
  else if j = 3 ∧ m = 0 ∧ n = 1 then S.y1
  else if 1 ≤ m ∧ 1 ≤ n ∧ Nat.Coprime m n then
    if j = 1 then
      -(g 3 (sbParent m n).1 (sbParent m n).2 ∘ₗ
        g 1 (m - (sbParent m n).1) (n - (sbParent m n).2))
    else if j = 2 then
      -(g 3 (sbParent m n).1 (sbParent m n).2 ∘ₗ
        g 2 (m - (sbParent m n).1) (n - (sbParent m n).2))
    else if j = 3 then
      -((q * u)⁻¹ • (g 2 (m - (sbParent m n).1) (n - (sbParent m n).2) ∘ₗ
        g 3 (sbParent m n).1 (sbParent m n).2))
    else 0
  else 0

/-- **The step reads `g` only below the index sum.** Two candidate families agreeing at every index
sum below `m + n` give the same value at `(j; m, n)`, because the only calls the step makes are at
a Stern–Brocot parent pair and its complement, both of which descend by
`isSBParent_sum_lt`. -/
theorem omegaStep_congr (S : SweepSystem L q u) (g g' : ℕ → ℕ → ℕ → (S.W →ₗ[L] S.W))
    (j m n : ℕ) (h : ∀ j' m' n', m' + n' < m + n → g j' m' n' = g' j' m' n') :
    omegaStep S g j m n = omegaStep S g' j m n := by
  rw [omegaStep, omegaStep]
  by_cases hrec : 1 ≤ m ∧ 1 ≤ n ∧ Nat.Coprime m n
  · obtain ⟨hm, hn, hmn⟩ := hrec
    obtain ⟨hlt1, hlt2⟩ := isSBParent_sum_lt hm hn (isSBParent_sbParent hmn hm hn)
    rw [h 3 _ _ hlt1, h 1 _ _ hlt2, h 2 _ _ hlt2]
  · rw [ite_eq_right hrec, ite_eq_right hrec]

/-- **The step at `j = 1`.** -/
theorem omegaStep_one (S : SweepSystem L q u) (g : ℕ → ℕ → ℕ → (S.W →ₗ[L] S.W)) (m n : ℕ) :
    omegaStep S g 1 m n =
      if m = 1 ∧ n = 0 then S.dplusStar
      else if 1 ≤ m ∧ 1 ≤ n ∧ Nat.Coprime m n then
        -(g 3 (sbParent m n).1 (sbParent m n).2 ∘ₗ
          g 1 (m - (sbParent m n).1) (n - (sbParent m n).2))
      else 0 := by
  rw [omegaStep]
  norm_num

/-- **The step at `j = 2`.** -/
theorem omegaStep_two (S : SweepSystem L q u) (g : ℕ → ℕ → ℕ → (S.W →ₗ[L] S.W)) (m n : ℕ) :
    omegaStep S g 2 m n =
      if m = 1 ∧ n = 0 then S.z1
      else if 1 ≤ m ∧ 1 ≤ n ∧ Nat.Coprime m n then
        -(g 3 (sbParent m n).1 (sbParent m n).2 ∘ₗ
          g 2 (m - (sbParent m n).1) (n - (sbParent m n).2))
      else 0 := by
  rw [omegaStep]
  norm_num

/-- **The step at `j = 3`.** -/
theorem omegaStep_three (S : SweepSystem L q u) (g : ℕ → ℕ → ℕ → (S.W →ₗ[L] S.W)) (m n : ℕ) :
    omegaStep S g 3 m n =
      if m = 0 ∧ n = 1 then S.y1
      else if 1 ≤ m ∧ 1 ≤ n ∧ Nat.Coprime m n then
        -((q * u)⁻¹ • (g 2 (m - (sbParent m n).1) (n - (sbParent m n).2) ∘ₗ
          g 3 (sbParent m n).1 (sbParent m n).2))
      else 0 := by
  rw [omegaStep]
  norm_num

/-! #### The family, by fuelled recursion -/

/-- **The recursion of `HJO.Mellit.IsReplicationFamily`, run on a fuel parameter.** `omegaAux S f`
is `f` iterations of `omegaStep`, starting from the zero family. Fuel `m + n` is enough to compute
the value at `(j; m, n)`, which is what `replFamily` takes. -/
noncomputable def omegaAux (S : SweepSystem L q u) : ℕ → ℕ → ℕ → ℕ → (S.W →ₗ[L] S.W)
  | 0 => fun _ _ _ => 0
  | f + 1 => omegaStep S (omegaAux S f)

/-- **With no fuel the family is zero.** -/
theorem omegaAux_zero (S : SweepSystem L q u) (j m n : ℕ) : omegaAux S 0 j m n = 0 := rfl

/-- **Unfolding `omegaAux` by one unit of fuel.** -/
theorem omegaAux_succ_eq (S : SweepSystem L q u) (f : ℕ) :
    omegaAux S (f + 1) = omegaStep S (omegaAux S f) := rfl

/-- **Spare fuel is inert.** Once the fuel reaches `m + n`, one more unit changes nothing. -/
theorem omegaAux_succ (S : SweepSystem L q u) :
    ∀ f j m n : ℕ, m + n ≤ f → omegaAux S f j m n = omegaAux S (f + 1) j m n := by
  intro f
  induction f with
  | zero =>
    intro j m n h
    have hm : m = 0 := by omega
    have hn : n = 0 := by omega
    subst hm; subst hn
    rw [omegaAux_zero, omegaAux_succ_eq, omegaStep]
    norm_num
  | succ f ih =>
    intro j m n _
    rw [omegaAux_succ_eq, omegaAux_succ_eq]
    exact omegaStep_congr S _ _ j m n fun j' m' n' hlt => ih j' m' n' (by omega)

/-- **Any sufficient fuel gives the same value.** -/
theorem omegaAux_eq_of_le (S : SweepSystem L q u) {f g j m n : ℕ} (hf : m + n ≤ f)
    (hfg : f ≤ g) : omegaAux S f j m n = omegaAux S g j m n := by
  induction g, hfg using Nat.le_induction with
  | base => rfl
  | succ g hg ih => exact ih.trans (omegaAux_succ S g j m n (hf.trans hg))

/-- **The replication family built here.** `Ω(j; m, n)` is the value the recursion of
`HJO.Mellit.IsReplicationFamily` gives, computed with fuel `m + n`. -/
noncomputable def replFamily (S : SweepSystem L q u) (j m n : ℕ) : S.W →ₗ[L] S.W :=
  omegaAux S (m + n) j m n

/-- **Unfolding `replFamily`.** -/
theorem replFamily_eq (S : SweepSystem L q u) (j m n : ℕ) :
    replFamily S j m n = omegaAux S (m + n) j m n := rfl

/-- **Every value of `omegaAux` has the grading `HJO.Mellit.IsReplicationFamily` demands.** By
induction on the fuel: the base values have it by the three `shape_*` fields of `SweepSystem`, and a
composite inherits it — `Ω(3; ·)` applied after `Ω(1; ·) : V_k → V_{k+1}` is applied on `V_{k+1}`,
where `k + 1 ≥ 1`, and for `j ∈ {2, 3}` every factor is an endomorphism of `V_{k+1}`. -/
theorem omegaAux_shape (S : SweepSystem L q u) (f : ℕ) :
    (∀ m n k : ℕ, (S.V k).map (omegaAux S f 1 m n) ≤ S.V (k + 1)) ∧
      (∀ m n k : ℕ, (S.V (k + 1)).map (omegaAux S f 2 m n) ≤ S.V (k + 1)) ∧
      (∀ m n k : ℕ, (S.V (k + 1)).map (omegaAux S f 3 m n) ≤ S.V (k + 1)) := by
  induction f with
  | zero => exact ⟨fun _ _ _ => map_zero_le, fun _ _ _ => map_zero_le, fun _ _ _ => map_zero_le⟩
  | succ f ih =>
    obtain ⟨ih1, ih2, ih3⟩ := ih
    refine ⟨fun m n k => ?_, fun m n k => ?_, fun m n k => ?_⟩
    · rw [omegaAux_succ_eq, omegaStep_one]
      split_ifs
      · exact S.shape_dplusStar k
      · exact map_neg_le (map_comp_le (ih1 _ _ k) (ih3 _ _ k))
      · exact map_zero_le
    · rw [omegaAux_succ_eq, omegaStep_two]
      split_ifs
      · exact S.shape_z1 k
      · exact map_neg_le (map_comp_le (ih2 _ _ k) (ih3 _ _ k))
      · exact map_zero_le
    · rw [omegaAux_succ_eq, omegaStep_three]
      split_ifs
      · exact S.shape_y1 k
      · exact map_neg_le (map_smul_le _ (map_comp_le (ih3 _ _ k) (ih2 _ _ k)))
      · exact map_zero_le

/-- **A replication family exists.** `HJO.Mellit.exists_isReplicationFamily`, on any
`SweepSystem`: `replFamily S` satisfies `IsReplicationFamily S`.

The three base values are read off at fuel `1`. Each of the three rules holds because, by
`sbParent_eq`, the pair `(m₁, n₁)` the rule is stated at is `sbParent m n`, and by
`isSBParent_sum_lt` both it and its complement have index sum at most `m + n - 1` — so
`omegaAux_eq_of_le` identifies the value the step computed at that fuel with the family's own
value. The gradings are `omegaAux_shape`.

This is what discharges `HJO.Mellit.ReplExists`, which is all the interface needs of it. It is the
intended existence statement for the reason recorded on `HJO.Mellit.IsReplicationFamily`: the
substrate is built and `HJO.Mellit.sweepWitness` is a `SweepSystem` assembled from the concrete
operators, so "every `SweepSystem` carries a replication family" includes the concrete one. -/
@[hjo "lem_mellit_repl_exists"]
theorem exists_isReplicationFamily (S : SweepSystem L q u) :
    ∃ Ω, IsReplicationFamily S Ω := by
  refine ⟨replFamily S, fun m n k => (omegaAux_shape S (m + n)).1 m n k,
    fun m n k => (omegaAux_shape S (m + n)).2.1 m n k,
    fun m n k => (omegaAux_shape S (m + n)).2.2 m n k, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · change omegaStep S (omegaAux S 0) 1 1 0 = S.dplusStar
    rw [omegaStep_one]
    norm_num
  · change omegaStep S (omegaAux S 0) 2 1 0 = S.z1
    rw [omegaStep_two]
    norm_num
  · change omegaStep S (omegaAux S 0) 3 0 1 = S.y1
    rw [omegaStep_three]
    norm_num
  all_goals
    intro m n m₁ n₁ hmn hm hn hp
    obtain ⟨hlt1, hlt2⟩ := isSBParent_sum_lt hm hn hp
    have hpar : sbParent m n = (m₁, n₁) := sbParent_eq hmn hm hn hp
    have hp1 : (sbParent m n).1 = m₁ := by rw [hpar]
    have hp2 : (sbParent m n).2 = n₁ := by rw [hpar]
    obtain ⟨f, hf⟩ : ∃ f, m + n = f + 1 := ⟨m + n - 1, by omega⟩
    have e3 : omegaAux S f 3 m₁ n₁ = replFamily S 3 m₁ n₁ := by
      rw [replFamily_eq]; exact (omegaAux_eq_of_le S le_rfl (by omega)).symm
    have e1 : omegaAux S f 1 (m - m₁) (n - n₁) = replFamily S 1 (m - m₁) (n - n₁) := by
      rw [replFamily_eq]; exact (omegaAux_eq_of_le S le_rfl (by omega)).symm
    have e2 : omegaAux S f 2 (m - m₁) (n - n₁) = replFamily S 2 (m - m₁) (n - n₁) := by
      rw [replFamily_eq]; exact (omegaAux_eq_of_le S le_rfl (by omega)).symm
    rw [replFamily_eq, hf, omegaAux_succ_eq]
  · rw [omegaStep_one, ite_eq_right (show ¬(m = 1 ∧ n = 0) by omega),
      ite_eq_left (⟨hm, hn, hmn⟩ : 1 ≤ m ∧ 1 ≤ n ∧ Nat.Coprime m n), hp1, hp2, e3, e1]
  · rw [omegaStep_two, ite_eq_right (show ¬(m = 1 ∧ n = 0) by omega),
      ite_eq_left (⟨hm, hn, hmn⟩ : 1 ≤ m ∧ 1 ≤ n ∧ Nat.Coprime m n), hp1, hp2, e3, e2]
  · rw [omegaStep_three, ite_eq_right (show ¬(m = 0 ∧ n = 1) by omega),
      ite_eq_left (⟨hm, hn, hmn⟩ : 1 ≤ m ∧ 1 ≤ n ∧ Nat.Coprime m n), hp1, hp2, e3, e2]

/-- **The replicated letter at the last index.** `HJO.Mellit.replicatedLetter`:
`Z^{(k+1)}_{m,n} = q^{-k} T_{k+1↘1} Ω(2; m, n) T_{1↗k+1}` on `V_{k+1}`.

The two trains are taken in the stated order: `T_{k+1↘1}` is the outermost factor
and `T_{1↗k+1}` the innermost, which is "the order in which they are written" read as composition.
On `HJO.Mellit.sweepWitness` they are `HJO.Sweep.trainDownEnd q (k+1) 1` and
`HJO.Sweep.trainUpEnd q 1 (k+1)` of `HJO.Braid.trainDown` and `HJO.Braid.trainUp`, in the braid
operators of `HJO.Sweep.braid`, so this is the definition on the concrete objects — see
`HJO.Mellit.IsReplicationFamily`. `q ^ (-(k : ℤ))` is `0` at `q = 0`, a corner the definition
excludes and nothing below reads. -/
@[hjo "def_mellit_zk"]
def replicatedLetter (S : SweepSystem L q u) (Ω : ℕ → ℕ → ℕ → (S.W →ₗ[L] S.W))
    (m n k : ℕ) : S.W →ₗ[L] S.W :=
  (q ^ (-(k : ℤ))) • (S.trainDown (k + 1) ∘ₗ Ω 2 m n ∘ₗ S.trainUp (k + 1))

/-- **The stage of a part.** `HJO.Mellit.stage`:
`G_{k+1,A} = (Z^{(k+1)}_{a,b})^{A-1} T_{k+1↘1} Ω(1; a, b)`, a map `V_k → V_{k+1}`. The truncated
`A - 1` is harmless: the stage is only used at `A ≥ 1`.

The stage is usually written `G_{k,A} : V_{k-1} → V_k` for `k ≥ 1`; the argument `k` here is that
`k - 1`, so that the source and target gradings are `k` and `k + 1` and no truncated
subtraction appears in the index. The slope pair `(a, b)`, which that notation leaves standing, is
an explicit argument. Read on `HJO.Mellit.sweepWitness` this is the stage on the concrete
operators — see `HJO.Mellit.IsReplicationFamily`. -/
@[hjo "def_mellit_stage"]
def stage (S : SweepSystem L q u) (Ω : ℕ → ℕ → ℕ → (S.W →ₗ[L] S.W)) (a b k A : ℕ) :
    S.W →ₗ[L] S.W :=
  ((replicatedLetter S Ω a b k) ^ (A - 1)) ∘ₗ S.trainDown (k + 1) ∘ₗ Ω 1 a b

/-- The composite `G_{k+ℓ,α_ℓ} ⋯ G_{k+1,α_1}` applied to `v ∈ V_k`. -/
def stageFrom (S : SweepSystem L q u) (Ω : ℕ → ℕ → ℕ → (S.W →ₗ[L] S.W)) (a b : ℕ) :
    ℕ → S.W → List ℕ → S.W
  | _, v, [] => v
  | k, v, A :: α => stageFrom S Ω a b (k + 1) (stage S Ω a b k A v) α

/-- `G_{ℓ,α_ℓ} G_{ℓ-1,α_{ℓ-1}} ⋯ G_{1,α_1}(1)`, the element of `V_ℓ` that
`HJO.Mellit.lhsRewrite_sweepWitness` and `HJO.Mellit.mellitInduction_sweepWitness` both name. -/
def stageWord (S : SweepSystem L q u) (Ω : ℕ → ℕ → ℕ → (S.W →ₗ[L] S.W)) (a b : ℕ)
    (α : List ℕ) : S.W :=
  stageFrom S Ω a b 0 S.vac α

/-! ### The six interface statements

Each is a `Prop`-valued predicate in the style of `HJO.ShuffleAbove`: the proof asserts the
statement outright, and here it is a hypothesis. -/

section Interface

variable (S : SweepSystem L q u) (a b : ℕ)

/-- **`HJO.Mellit.exists_isReplicationFamily`: a replication family exists.** This statement is
load-bearing rather than bookkeeping: every statement below is of the form "let `Ω` be a
replication family", and a hypothesis with no exhibited instance makes each of them vacuously
true.

This is the one of the six that is **not** a hypothesis: `HJO.Mellit.replExists` proves it for every
`SweepSystem`, so it is no longer a conjunct of `HJO.Mellit.MellitInput`. -/
def ReplExists : Prop := ∃ Ω, IsReplicationFamily S Ω

/-- **`HJO.Mellit.exists_isReplicationFamily`, proved.** Every `SweepSystem` carries a replication
family, namely `HJO.Mellit.replFamily`. -/
theorem replExists : ReplExists S := exists_isReplicationFamily S

/-- **`HJO.Mellit.IsReplicationFamily.eq_index_one`: a replication family is determined off three
unreached values.** Two replication families agree at every `(j; m, n)` with `j ∈ {1, 2, 3}`,
`(m, n)` coprime and `m + n ≥ 1`, except possibly at `(1;0,1)`, `(2;0,1)` and `(3;1,0)`. -/
def ReplUnique : Prop :=
  ∀ Ω Ω', IsReplicationFamily S Ω → IsReplicationFamily S Ω' →
    ∀ j m n : ℕ, 1 ≤ j → j ≤ 3 → Nat.Coprime m n → 1 ≤ m + n →
      (j, m, n) ≠ (1, 0, 1) → (j, m, n) ≠ (2, 0, 1) → (j, m, n) ≠ (3, 1, 0) →
      Ω j m n = Ω' j m n

/-- **`HJO.Mellit.lhsRewrite_sweepWitness`: Mellit's Section 3.7, the rewriting of the left-hand
side.** `(-1)^{N(b+1)} ι(Θ(C_α 1) 1) = (-1)^{(a-1)N} q^{ℓ-N} ι(d_-^ℓ G_{ℓ,α_ℓ} ⋯ G_{1,α_1}(1))`. -/
def LhsRewrite : Prop :=
  ∀ (ι : Sym.Lambda L →ₐ[L] Sym.AlphabetSeries L), Sym.IsRealisation ι →
    ∀ Θ : Sym.Lambda L →ₐ[L] Module.End L (Sym.Lambda L), Sym.IsSlopeHom a b q u Θ →
      ∀ Ω, IsReplicationFamily S Ω →
        ∀ N : ℕ, 0 < N → ∀ α : List ℕ, (∀ x ∈ α, 0 < x) → α.sum = N →
          (-1 : L) ^ (N * (b + 1)) • ι (Θ (Sym.CopComp q α 1) 1)
            = ((-1 : L) ^ ((a - 1) * N) * q ^ ((α.length : ℤ) - (N : ℤ))) •
                ι (S.proj ((S.dminus ^ α.length) (stageWord S Ω a b α)))

/-- **`HJO.Mellit.mellitInduction_sweepWitness`: the closed form of the invariant of a
composition.** `D_{η,c_α} = (-1)^{(a-1)N} (qu)^{ℓ-N} G_{ℓ,α_ℓ} ⋯ G_{1,α_1}(1)`. -/
def MellitInduction : Prop :=
  ∀ Ω, IsReplicationFamily S Ω →
    ∀ (N : ℕ) (η : ℚ), IsAdmissibleLevel η → SeparatesDiagonal a b N η →
      ∀ α : List ℕ, (∀ x ∈ α, 0 < x) → α.sum = N →
        S.D η (compColouring a b α)
          = ((-1 : L) ^ ((a - 1) * N) * (q * u) ^ ((α.length : ℤ) - (N : ℤ))) •
              stageWord S Ω a b α

/-- **`HJO.Mellit.isAdmissibleColouring_and_sum_sweepChar_eq_smul_dsc`: Mellit's Remark 4.1, the
composition sum as an invariant.**
`∑_{P̂} u^{ârea(P̂)} q^{ĥ(P̂) - max t̂dinv(P̂)} χ(P̂) = u^{N-ℓ} d_-^ℓ D_{η,c_α}`, the sum over the
above-diagonal `(aN, bN)`-paths of return composition `α`.

**A typing defect.** As written the identity does not typecheck: by `HJO.Paths.sweepChar` the
left-hand side is an element of `𝒫`, while by `HJO.Sweep.piece` and `HJO.Sweep.dminus` the right
is an element of `V_0 = Λ`. The two are different objects and nothing supplies an inclusion
`Λ ↪ 𝒫` — the passage between them is exactly a realisation. So the statement needs a realisation
`ι`, and it belongs here rather than in `HJO.Mellit.sum_sweepChar_eq_sum_gessel`, where it would
occur nowhere in the statement. It is supplied here. -/
def Rem41 : Prop :=
  ∀ (ι : Sym.Lambda L →ₐ[L] Sym.AlphabetSeries L), Sym.IsRealisation ι →
    ∀ (N : ℕ) (η : ℚ), IsAdmissibleLevel η → SeparatesDiagonal a b N η →
      ∀ α : List ℕ, (∀ x ∈ α, 0 < x) → α.sum = N →
        ∑ y ∈ aboveReturnPaths a b N α,
            (u ^ Paths.aboveArea y *
                q ^ ((Paths.aboveHookCount y : ℤ) - (aboveMaxTdinv y : ℤ))) • S.chi a b N y
          = (u ^ ((N : ℤ) - (α.length : ℤ))) •
              ι (S.proj ((S.dminus ^ α.length) (S.D η (compColouring a b α))))

/-- **`HJO.Mellit.sum_sweepChar_eq_sum_gessel`: the two forms of the right-hand side agree.**
`∑_{P̂} u^{ârea(P̂)} q^{ĥ(P̂) - max t̂dinv(P̂)} χ(P̂)
  = ∑_{π̂ ∈ PF̂^α_{aN,bN}} q^{d̂inv(π̂)} u^{ârea(P̂_π̂)} F_{bN, îdes(π̂)^{∨bN}}`.

No realisation occurs, and the statement carries none: both sides are elements of `𝒫`, `χ` by
`HJO.Paths.sweepChar` and `F` by `HJO.ParkingFunctions.gessel`. An inert hypothesis declaring a
realisation `ι` that occurs nowhere in the statement is therefore not included. The two readings are
equivalent — a realisation always exists, `HJO.PhiMul.isRealisation_realise` — so nothing about the
strength of `HJO.Mellit.MellitInput` turns on the choice. -/
def RhsSumsAgree : Prop :=
  ∀ N : ℕ, 0 < N → ∀ α : List ℕ, (∀ x ∈ α, 0 < x) → α.sum = N →
    ∑ y ∈ aboveReturnPaths a b N α,
        (u ^ Paths.aboveArea y *
            q ^ ((Paths.aboveHookCount y : ℤ) - (aboveMaxTdinv y : ℤ))) • S.chi a b N y
      = ∑ π ∈ aboveWithReturns α a b N,
          (q ^ aboveDinv π * u ^ Paths.aboveArea (abovePath π)) •
            gessel L (b * N) (descentReverse (b * N) (aboveIdes π))

end Interface


/-! ### The assembly: `ShuffleAbove` from the interface -/

/-- **The residual Mellit interface.** For every parameter set there is a Carlsson–Mellit sweep
system satisfying the six statements of Mellit's Sections 4–6 that the proof of
`HJO.shuffleAbove` consumes. This is the whole of what `HJO.ShuffleAbove` needs from those
sections.

Note that it is *not* the whole of what the proof of `HJO.shuffleAbove` cites: that
proof also consumes `HJO.gessel_reverse_sum`, to turn each `F_{bN, îdes(π̂)^{∨bN}}` into
`F_{bN, îdes(π̂)}`. So `ShuffleAbove` is not independent of `HJO.GesselReverseSum`. No new
hypothesis follows:
`HJO.shuffle_of_above` already takes `GesselReverseSum`, so `HJO.External.Shuffle` still follows
from `GesselReverseSum` together with this interface.

`HJO.Mellit.ReplUnique` is deliberately **not** a conjunct, and that is a redundancy in the
argument as usually given: it cites `HJO.Mellit.IsReplicationFamily.eq_index_one` to
argue that "nothing below depends on which one", but it uses nothing from it.
`HJO.Mellit.lhsRewrite_sweepWitness` and `HJO.Mellit.mellitInduction_sweepWitness` are each stated
for an arbitrary replication family, so fixing one family and using it in both is enough — which is
exactly what `HJO.Mellit.aboveIdentity_of_mellit` does. Uniqueness is reassurance about the
decomposition, not a step in the argument. The predicate is still stated above, because it is one of
the inputs the argument names.


`HJO.Mellit.ReplExists` is not a conjunct either, and for the opposite reason: it is a **theorem**,
`HJO.Mellit.replExists`, holding of every `SweepSystem`. The recursion of
`HJO.Mellit.IsReplicationFamily` is on the index sum `m + n`, its base values are three operators
the substrate already carries, and `HJO.Mellit.existsUnique_isSBParent` supplies the parent pair the
recursion branches on — so a family can be built rather than assumed. What the construction needs of
the substrate is the three gradings `SweepSystem.shape_dplusStar`, `SweepSystem.shape_z1` and
`SweepSystem.shape_y1`, which are the domains and codomains written into the definitions of `d^*_+`,
`HJO.Sweep.zop` and `HJO.Sweep.piece`, not claims about the operators. So the residual is four
statements, not five.

**The parameters are generic, and that is necessary, not decoration.** Quantified over *all*
`q u : L`, this definition would be **false** — not merely
unprovable. `HJO.Mellit.not_mellitInput_unrestricted` is the witness: at `q = 0`, `u = 1`,
`(a, b) = (2, 3)`, `N = 2` and `α = (2)`, the factor `(qu)^{ℓ-N}` of `MellitInduction` vanishes, so
`D_{η,c_α} = 0`; `Rem41` then forces the path sum to be `0`; and `RhsSumsAgree` equates that with
the parking-function sum, whose coefficient on the squarefree monomial `x_1 ⋯ x_6` counts the
above-diagonal parking functions of `dinv = 0` and so is a positive integer. Three of the four
clauses are therefore jointly contradictory there, with no reference to the substrate at all.

The clauses are never meant at `q = 0`: the standing coefficient field is `𝕜 = ℚ(q, u)` with
`q, u` indeterminates, and the conditions `q, u` invertible,
`qu ≠ 1`, no power of `u` equal to `1` and `(1-q)(1-u) ≠ 0` are all load-bearing below. So once
the field is generalised, the genericity must be stated explicitly. The
hypothesis carried here is the standing genericity and the one both consumers already carry:
`HJO.ShuffleAbove` and `HJO.External.Shuffle` are each stated at `AlgebraicIndependent ℤ ![q, u]`,
so `HJO.Mellit.shuffleAbove_of_mellit` supplies it from what it is given and the reduction is
unchanged. A bare `q ≠ 0` would kill this particular witness while leaving the other three standing
hypotheses unstated. -/
def MellitInput (L : Type w) [Field L] [Algebra ℚ L] : Prop :=
  ∀ q u : L, AlgebraicIndependent ℤ ![q, u] → ∀ a b : ℕ, Nat.Coprime a b → 1 < a → a < b →
    ∃ S : SweepSystem L q u,
      LhsRewrite S a b ∧ MellitInduction S a b ∧ Rem41 S a b ∧ RhsSumsAgree S a b

/-- **The above-diagonal identity with the inverse descent sets still reflected.** The chain of the
proof of `HJO.shuffleAbove`, up to but excluding its final appeal to
`HJO.gessel_reverse_sum`.

Fix a replication family (`replExists`, a theorem; `ReplUnique` says nothing below depends on
which), put `η := aN + 1/2`, which is admissible and separating by `separatesDiagonal_sepLevel`.
Then `LhsRewrite` rewrites the left side as `(-1)^{(a-1)N} q^{ℓ-N} ι(d_-^ℓ G_ℓ ⋯ G_1(1))`,
`MellitInduction` identifies `G_ℓ ⋯ G_1(1)` with `(-1)^{(a-1)N}(qu)^{N-ℓ} D_{η,c_α}` — the two
signs cancelling and `q^{ℓ-N}(qu)^{N-ℓ}` collapsing to `u^{N-ℓ}` — and then `Rem41` and
`RhsSumsAgree` carry `u^{N-ℓ} d_-^ℓ D_{η,c_α}` to the sum over above-diagonal parking functions.

Only `u ≠ 0` is needed of the parameters; `q ≠ 0` is not. -/
theorem aboveIdentity_of_mellit {a b : ℕ} {q u : L} (S : SweepSystem L q u)
    (hlhs : LhsRewrite S a b) (hind : MellitInduction S a b)
    (hrem : Rem41 S a b) (hrhs : RhsSumsAgree S a b) (hu : u ≠ 0)
    (ι : Sym.Lambda L →ₐ[L] Sym.AlphabetSeries L) (hι : Sym.IsRealisation ι)
    (Θ : Sym.Lambda L →ₐ[L] Module.End L (Sym.Lambda L)) (hΘ : Sym.IsSlopeHom a b q u Θ)
    (N : ℕ) (hN : 0 < N) (α : List ℕ) (hαpos : ∀ x ∈ α, 0 < x) (hαN : α.sum = N) :
    (-1 : L) ^ (N * (b + 1)) • ι (Θ (Sym.CopComp q α 1) 1)
      = ∑ π ∈ aboveWithReturns α a b N,
          (q ^ aboveDinv π * u ^ aboveArea (abovePath π)) •
            gessel L (b * N) (descentReverse (b * N) (aboveIdes π)) := by
  obtain ⟨Ω, hΩ⟩ := replExists S
  have hlevel : IsAdmissibleLevel (sepLevel a N) := isAdmissibleLevel_sepLevel a N
  have hsep : SeparatesDiagonal a b N (sepLevel a N) := separatesDiagonal_sepLevel hN
  have h1 := hlhs ι hι Θ hΘ Ω hΩ N hN α hαpos hαN
  have h2 := hind Ω hΩ N (sepLevel a N) hlevel hsep α hαpos hαN
  have h3 := hrem ι hι N (sepLevel a N) hlevel hsep α hαpos hαN
  have h4 := hrhs N hN α hαpos hαN
  have hX : ι (S.proj ((S.dminus ^ α.length) (S.D (sepLevel a N) (compColouring a b α))))
      = ((-1 : L) ^ ((a - 1) * N) * (q * u) ^ ((α.length : ℤ) - (N : ℤ))) •
          ι (S.proj ((S.dminus ^ α.length) (stageWord S Ω a b α))) := by
    rw [h2, map_smul, map_smul, map_smul]
  have hscal : ((-1 : L) ^ ((a - 1) * N) * q ^ ((α.length : ℤ) - (N : ℤ)))
      = u ^ ((N : ℤ) - (α.length : ℤ)) *
          ((-1 : L) ^ ((a - 1) * N) * (q * u) ^ ((α.length : ℤ) - (N : ℤ))) := by
    have hu1 : u ^ ((N : ℤ) - (α.length : ℤ)) * u ^ ((α.length : ℤ) - (N : ℤ)) = 1 := by
      rw [← zpow_add₀ hu]
      simp
    rw [mul_zpow]
    calc (-1 : L) ^ ((a - 1) * N) * q ^ ((α.length : ℤ) - (N : ℤ))
        = ((-1 : L) ^ ((a - 1) * N) * q ^ ((α.length : ℤ) - (N : ℤ)))
            * (u ^ ((N : ℤ) - (α.length : ℤ)) * u ^ ((α.length : ℤ) - (N : ℤ))) := by
          rw [hu1, mul_one]
      _ = _ := by ring
  rw [h1, hscal, ← smul_smul, ← hX, ← h3, h4]

/-- **The above-diagonal compositional rational shuffle identity from the Mellit interface.**
`HJO.ShuffleAbove` — `HJO.shuffleAbove` — follows from `HJO.GesselReverseSum`
together with `HJO.Mellit.MellitInput`, and from nothing else.

Composed with `HJO.shuffle_of_above`, this reduces the whole shuffle side to
`GesselReverseSum` and `MellitInput`: see `HJO.Mellit.shuffle_of_mellit`. -/
theorem shuffleAbove_of_mellit (hrev : GesselReverseSum L) (h : MellitInput L) :
    ShuffleAbove L := by
  intro a b hab ha hb q u hqu ι hι Θ hΘ N hN α hαpos hαN
  obtain ⟨S, hl, hi, hr, hs⟩ := h q u hqu a b hab ha hb
  have hu : u ≠ 0 := fun h0 => by
    have hz : (MvPolynomial.X 1 : MvPolynomial (Fin 2) ℤ) = 0 :=
      PhiPoly.eq_of_aeval_eq hqu (by simp [h0])
    have hz' := congrArg (MvPolynomial.aeval ![(1 : ℤ), 1]) hz
    simp at hz'
  have hmain := aboveIdentity_of_mellit S hl hi hr hs hu ι hι Θ hΘ N hN α hαpos hαN
  have hS : ∀ π ∈ aboveWithReturns α a b N,
      descentReverse (b * N) (aboveIdes π) ⊆ Ico 1 (b * N) :=
    fun π _ => descentReverse_subset_Ico (aboveIdes_subset π)
  have hf : ι ((-1 : L) ^ (N * (b + 1)) • Θ (Sym.CopComp q α 1) 1)
      = ∑ π ∈ aboveWithReturns α a b N,
          (q ^ aboveDinv π * u ^ aboveArea (abovePath π)) •
            gessel L (b * N) (descentReverse (b * N) (aboveIdes π)) := by
    rw [map_smul]
    exact hmain
  have hres := hrev ι hι (b * N) (AboveParkingFunction a b N) (aboveWithReturns α a b N)
    (fun π => q ^ aboveDinv π * u ^ aboveArea (abovePath π))
    (fun π => descentReverse (b * N) (aboveIdes π)) hS _ hf
  rw [map_smul] at hres
  rw [hres]
  refine Finset.sum_congr rfl fun π _ => ?_
  rw [descentReverse_descentReverse ((aboveIdes_subset π).trans Finset.Ico_subset_Iic_self)]

/-- **The whole shuffle side, reduced to `GesselReverseSum` and the Mellit
interface.** The two-clause assumption `HJO.External.Shuffle` follows from `HJO.GesselReverseSum`
and `HJO.Mellit.MellitInput` alone. -/
theorem shuffle_of_mellit (hrev : GesselReverseSum L) (h : MellitInput L) :
    HJO.External.Shuffle L :=
  shuffle_of_above hrev (shuffleAbove_of_mellit hrev h)

end HJO.Mellit
