/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.Shuffle.MellitAtZero

/-! # `HJO.Mellit.mellitInduction_sweepWitness`: the induction on the number of parts, carried out

`HJO.Mellit.MellitInduction` is one of the four conjuncts of `HJO.Mellit.MellitInput`, the
hypothesis on which the shuffle side rests. The proof of `HJO.Mellit.mellitInduction_sweepWitness`
is an induction on the number `ℓ` of parts of the composition, and it cites exactly three inputs:
`HJO.Mellit.braidValueColouring_eq_dsc_floor` and
`HJO.Mellit.invFin_eq_invIni_of_separatesDiagonal`, which together read `D_{η,c_α}` as
`π_ℓ(B_{s,v,α^{br}}) d_+^ℓ(1)` with no `q`-power correction, and
`HJO.Mellit.braidRep_specialBraid_dplusIter`, which peels the last part off that braid value.

This file carries out that induction, and nothing else is needed: the result is an *equivalence*
between `HJO.Mellit.MellitInduction` and one named `Prop`, `HJO.Mellit.BraidClosedForm` — see
`HJO.Mellit.mellitInduction_iff_braidClosedForm`. So the clause is **reduced, not closed**, and what
remains of it is precisely the three cited results.

## What is proved here

* `HJO.Mellit.stageWord_append` — `G_{ℓ,α_ℓ} ⋯ G_{1,α_1}(1)` really does peel from the right:
  appending a part to `α` post-composes one further stage at index `α.length`. This is the
  compatibility of `HJO.Mellit.stage` with the indexing `k = ℓ - 1`.
* `HJO.Mellit.eq_inductionScalar_smul_stageWord` — the induction itself, including all of the
  scalar bookkeeping.
* `HJO.Mellit.replUnique` — `HJO.Mellit.IsReplicationFamily.eq_index_one`, **proved** (relative to a
  sweep system) rather than assumed, by strong induction on the index sum; and
  `HJO.Mellit.stageWord_congr`, the consequence the reduction needs, that
  `G_{ℓ,α_ℓ} ⋯ G_{1,α_1}(1)` does not depend on which replication family is used.
* `HJO.Mellit.mellitInduction_iff_braidClosedForm` — the reduction, as an equivalence.
* `HJO.Mellit.d_empty_eq_vac_of_mellitInduction` — the corner check: the clause forces
  `D_{η,∅} = 1`, which is `HJO.Mellit.isAdmissibleColouring_empty_and_dsc_eq_one`.
* `HJO.Mellit.sum_eq_of_compColouring_eq` — `c_α` determines `N`, which is what makes the top
  layer's `N`-free `HJO.Mellit.SweepSystem.D` a faithful reading of `HJO.Mellit.dsc`.

## Where genericity is spent: nowhere

`HJO.Mellit.MellitInput` carries `AlgebraicIndependent ℤ ![q, u]` because three of its four clauses
are jointly contradictory without it (`HJO.Mellit.not_mellitInput_unrestricted`), and the witness
runs through this very clause: the factor `(qu)^{ℓ-N}` with `ℓ < N` is `0^{-1} = 0` at `q = 0`. So
one would expect the induction to need `qu ≠ 0`, the scalars being multiplied by
`zpow_add₀`.

It does not, and the reason is structural rather than lucky. The two exponents combined at each step
are `1 - A` and `ℓ' - N'`, and both are **nonpositive**: `A ≥ 1` because a composition's parts are
positive, and `ℓ' ≤ N'` for the same reason (`HJO.Mellit.length_le_sum_of_forall_pos`). For
nonpositive exponents `c^{m+n} = c^m c^n` holds in any field with no hypothesis on `c`, because both
sides are inverses of powers and `(xy)⁻¹ = x⁻¹y⁻¹` is unconditional — this is
`HJO.Mellit.zpow_add_of_nonpos`, and `HJO.Mellit.zpow_add_of_nonpos_sharp` records that the
nonpositivity really is what makes it work. So the reduction holds verbatim at `q = 0`, and
`HJO.Mellit.not_braidClosedForm_of_clauses_at_zero` transports the `q = 0` refutation through it
unchanged. Genericity is spent below this statement, in
`HJO.Mellit.braidRep_specialBraid_dplusIter`: the third Stern–Brocot rule of
`HJO.Mellit.IsReplicationFamily` divides by `qu`.

This matches `HJO.Mellit.euclid`, which also needs none of the genericity its proof on paper
assumes.

## What this file does not do

The braid value `π_ℓ(B_{s,v,α^{br}}) d_+^ℓ(1)` is carried here as a function of the composition:
`HJO.Mellit.braidRep_specialBraid_dplusIter` needs `HJO.Sweep.braidRep`, which is not statable in
the vocabulary of this layer, so the value cannot be written down directly.

## Implementation notes

As explained at `HJO.Mellit.exists_isReplicationFamily`, the statements here are read relative to a
`HJO.Mellit.SweepSystem`, not on the actual `V_k` with the actual `d^*_+`, `z_1` and `y_1`. In
particular `HJO.Mellit.replUnique` is a proof of `HJO.Mellit.IsReplicationFamily.eq_index_one` in
that relative sense only.

The only import is `HJO.Shuffle.MellitAtZero`, which publicly re-exports
`HJO.Shuffle.Mellit`; naming the latter as well is redundant. `MellitAtZero` is imported for
`HJO.Mellit.false_of_clauses_at_zero`, the refutation the last corner check transports.

## References

This file concerns `HJO.Mellit.mellitInduction_sweepWitness` and the results it cites:
`HJO.Mellit.braidValueColouring_eq_dsc_floor`, `HJO.Mellit.invFin_eq_invIni_of_separatesDiagonal`,
`HJO.Mellit.braidRep_specialBraid_dplusIter`, `HJO.Mellit.braidDataOfColouring`,
`HJO.Sweep.braidRep`, `HJO.Mellit.replicatedLetter`, `HJO.Mellit.stage`,
`HJO.Mellit.IsReplicationFamily`, `HJO.Mellit.IsReplicationFamily.eq_index_one`,
`HJO.Mellit.existsUnique_isSBParent`, `HJO.Mellit.isAdmissibleColouring_empty_and_dsc_eq_one`,
`HJO.Mellit.compColouring`.
-/

@[expose] public section

open Finset

namespace HJO.Mellit

open ParkingFunctions

universe w

/-! ### Two pieces of arithmetic

The whole of the scalar bookkeeping of the induction, isolated so that the question "where is
genericity spent" has a syntactic answer: the hypotheses of these two lemmas. Stated over a bare
field: none of them sees the `ℚ`-algebra structure the rest of the file carries. -/

section Arithmetic

variable {L : Type w} [Field L]

/-- **`c^{m+n} = c^m c^n` for nonpositive exponents, with no hypothesis on `c`.** Both sides are
inverses of natural-number powers, and `(xy)⁻¹ = x⁻¹y⁻¹` holds in a field however `x` and `y`
vanish. This is what lets the induction below run at `q u = 0`, where `zpow_add₀` is
unavailable. -/
theorem zpow_add_of_nonpos (c : L) {m n : ℤ} (hm : m ≤ 0) (hn : n ≤ 0) :
    c ^ (m + n) = c ^ m * c ^ n := by
  obtain ⟨j, rfl⟩ : ∃ j : ℕ, m = -(j : ℤ) := ⟨(-m).toNat, by omega⟩
  obtain ⟨k, rfl⟩ : ∃ k : ℕ, n = -(k : ℤ) := ⟨(-n).toNat, by omega⟩
  rw [← neg_add, ← Nat.cast_add, zpow_neg, zpow_neg, zpow_neg, zpow_natCast, zpow_natCast,
    zpow_natCast, pow_add, mul_inv]

/-- **The nonpositivity in `HJO.Mellit.zpow_add_of_nonpos` is not decoration.** At `c = 0` and
exponents `-1` and `1`, whose sum is `0`, the two sides are `0` and `1`. The induction below stays
inside the nonpositive range because a composition's parts are positive, and that is the only
reason it needs no genericity. -/
theorem zpow_add_of_nonpos_sharp :
    (0 : ℚ) ^ (-1 + 1 : ℤ) ≠ (0 : ℚ) ^ (-1 : ℤ) * (0 : ℚ) ^ (1 : ℤ) := by
  norm_num

/-- **A list of positive naturals is no longer than its sum.** The `ℓ ≤ N`, which is
why the exponent `ℓ - N` of `HJO.Mellit.mellitInduction_sweepWitness` is nonpositive. -/
theorem length_le_sum_of_forall_pos {α : List ℕ} (h : ∀ x ∈ α, 0 < x) : α.length ≤ α.sum := by
  induction α with
  | nil => exact le_rfl
  | cons x xs ih =>
    have hx : 0 < x := h x (List.mem_cons_self ..)
    have hxs := ih fun y hy => h y (List.mem_cons_of_mem _ hy)
    simp only [List.length_cons, List.sum_cons]
    omega

/-! ### The scalar of the closed form -/

/-- **The scalar of `HJO.Mellit.mellitInduction_sweepWitness`**, `(-1)^{(a-1)N}(qu)^{ℓ-N}`, read off
the composition: `N` is its sum and `ℓ` its number of parts. -/
def inductionScalar (q u : L) (a : ℕ) (α : List ℕ) : L :=
  (-1 : L) ^ ((a - 1) * α.sum) * (q * u) ^ ((α.length : ℤ) - (α.sum : ℤ))

/-- **The scalar at the empty composition is `1`**, which is the `ℓ = 0` base of the
induction. -/
theorem inductionScalar_nil (q u : L) (a : ℕ) : inductionScalar q u a [] = 1 := by
  simp only [inductionScalar, List.sum_nil, List.length_nil, Nat.mul_zero, pow_zero,
    Nat.cast_zero, sub_zero, zpow_zero, mul_one]

/-- **The scalar multiplies as the induction says.** The sign is
`(-1)^{(a-1)A}(-1)^{(a-1)N'} = (-1)^{(a-1)N}` and the power of `qu` is
`(qu)^{1-A}(qu)^{ℓ'-N'} = (qu)^{ℓ-N}`. **No hypothesis on `q` or `u`**: both exponents are
nonpositive, by `0 < A` and by `HJO.Mellit.length_le_sum_of_forall_pos`, so
`HJO.Mellit.zpow_add_of_nonpos` applies. -/
theorem inductionScalar_append (q u : L) {a : ℕ} {α : List ℕ} {A : ℕ} (hα : ∀ x ∈ α, 0 < x)
    (hA : 0 < A) : inductionScalar q u a (α ++ [A]) =
      ((-1 : L) ^ ((a - 1) * A) * (q * u) ^ (1 - (A : ℤ))) * inductionScalar q u a α := by
  have hlen : α.length ≤ α.sum := length_le_sum_of_forall_pos hα
  have hs : (α ++ [A]).sum = α.sum + A := by
    simp only [List.sum_append, List.sum_cons, List.sum_nil, Nat.add_zero]
  have hl : (α ++ [A]).length = α.length + 1 := by
    simp only [List.length_append, List.length_cons, List.length_nil, Nat.zero_add]
  have hsign : (-1 : L) ^ ((a - 1) * (α.sum + A))
      = (-1 : L) ^ ((a - 1) * A) * (-1 : L) ^ ((a - 1) * α.sum) := by
    rw [← pow_add]; congr 1; ring
  have hexp : ((α.length + 1 : ℕ) : ℤ) - ((α.sum + A : ℕ) : ℤ)
      = (1 - (A : ℤ)) + (((α.length : ℕ) : ℤ) - ((α.sum : ℕ) : ℤ)) := by push_cast; ring
  rw [inductionScalar, inductionScalar, hs, hl, hsign, hexp,
    zpow_add_of_nonpos (q * u) (by omega) (by omega)]
  ring

end Arithmetic

variable {L : Type w} [Field L] [Algebra ℚ L] {q u : L}

/-! ### The stage word peels from the right

`HJO.Mellit.stageWord` is written as a left fold from the vacuum, so that
`G_{ℓ,α_ℓ} ⋯ G_{1,α_1}(1)` applies `G_{1,α_1}` first. The induction removes
`G_{ℓ,α_ℓ}`, that is the *last* part of `α`, and at index `k = ℓ - 1`. -/

/-- **Appending a part post-composes one stage.** For every starting grading `k` and vector `v`,
`stageFrom` along `α ++ [A]` is one further `HJO.Mellit.stage` at index `k + |α|` applied to
`stageFrom` along `α`. -/
theorem stageFrom_append (S : SweepSystem L q u) (Ω : ℕ → ℕ → ℕ → (S.W →ₗ[L] S.W)) (a b : ℕ)
    (α : List ℕ) (A : ℕ) : ∀ (k : ℕ) (v : S.W), stageFrom S Ω a b k v (α ++ [A]) =
      stage S Ω a b (k + α.length) A (stageFrom S Ω a b k v α) := by
  induction α with
  | nil => intro k v; simp only [List.nil_append, stageFrom, List.length_nil, Nat.add_zero]
  | cons C β ih =>
    intro k v
    have hk : k + 1 + β.length = k + (β.length + 1) := by omega
    rw [List.cons_append]
    simp only [stageFrom, List.length_cons]
    rw [ih (k + 1) (stage S Ω a b k C v), hk]

/-- **`G_{ℓ,α_ℓ} ⋯ G_{1,α_1}(1)` at `α ++ [A]`.** The inductive step reads
`G_{ℓ,α_ℓ} = (Z^{(ℓ)}_{a,b})^{α_ℓ-1} T_{ℓ↘1} Ω(1;a,b)`, which is `HJO.Mellit.stage` at
`k = ℓ - 1 = |α|`. -/
theorem stageWord_append (S : SweepSystem L q u) (Ω : ℕ → ℕ → ℕ → (S.W →ₗ[L] S.W)) (a b : ℕ)
    (α : List ℕ) (A : ℕ) : stageWord S Ω a b (α ++ [A]) =
      stage S Ω a b α.length A (stageWord S Ω a b α) := by
  rw [stageWord, stageWord, stageFrom_append, Nat.zero_add]

/-! ### The braid side, as data

`HJO.Mellit.braidValueColouring_eq_dsc_floor` and `HJO.Mellit.braidRep_specialBraid_dplusIter` are
both statements about `π_k(B_{s,v,α}) d_+^k(1)` — the image of the special braid of a colouring
under the representation `HJO.Sweep.braidRep`, applied to `d_+^k(1)`. None of `𝔹⁺_k(𝕋_0)`, the
special-braid data or `π_k` is in the top layer's vocabulary, so that value is carried here as an
unspecified function of the composition, exactly as `HJO.Mellit.SweepSystem` carries the operators
it names. -/

/-- **The two properties of the braid value that the induction uses.** Writing
`B(α) := π_ℓ(B_{s,v,α^{br}}) d_+^ℓ(1)`:

* `nil` is the `ℓ = 0` base, "the braid is the identity of `𝔹⁺_0(𝕋_0)`, `d_+^0(1) = 1`";
* `append` is `HJO.Mellit.braidRep_specialBraid_dplusIter` at `k = ℓ - 1` and `A = α_ℓ`, together
  with the inline appeal to `HJO.Mellit.braidDataOfColouring` that identifies the special-braid data
  of `c_α` with that of `c_{α'}` extended by one entry — the step argued from
  `HJO.Mellit.compColouring`.

The operator standing to the left of the last factor in
`HJO.Mellit.braidRep_specialBraid_dplusIter`'s conclusion is `G_{ℓ,α_ℓ}`, which by definition is
`HJO.Mellit.stage`; that is why it is written here as `HJO.Mellit.stage`. -/
structure IsBraidValue (S : SweepSystem L q u) (Ω : ℕ → ℕ → ℕ → (S.W →ₗ[L] S.W)) (a b : ℕ)
    (B : List ℕ → S.W) : Prop where
  /-- `B(∅) = 1`, the `ℓ = 0` base of the induction. -/
  nil : B [] = S.vac
  /-- `HJO.Mellit.braidRep_specialBraid_dplusIter`: peeling the last part multiplies by
  `(-1)^{(a-1)A}(qu)^{1-A}` and post-composes `G_{ℓ,A}`. -/
  append : ∀ (α : List ℕ) (A : ℕ), (∀ x ∈ α, 0 < x) → 0 < A →
    B (α ++ [A]) = ((-1 : L) ^ ((a - 1) * A) * (q * u) ^ (1 - (A : ℤ))) •
      stage S Ω a b α.length A (B α)

/-- **`HJO.Mellit.braidValueColouring_eq_dsc_floor` together with
`HJO.Mellit.invFin_eq_invIni_of_separatesDiagonal`.** The first reads `D_{η,c}` as
`q^{(inv_fin - inv_ini)/2} π_k(B_{s,v,α}) d_+^k(1)` and the second says the exponent vanishes at
`c = c_α`, so at a separating admissible level the invariant of `c_α` *is* the braid value. The
number `k` of components of `c_α` is the number of parts of `α` by `HJO.Mellit.compColouring`, so no
separate index appears. -/
def IsColouringValue (S : SweepSystem L q u) (a b : ℕ) (B : List ℕ → S.W) : Prop :=
  ∀ (N : ℕ) (η : ℚ), IsAdmissibleLevel η → SeparatesDiagonal a b N η →
    ∀ α : List ℕ, (∀ x ∈ α, 0 < x) → α.sum = N → S.D η (compColouring a b α) = B α

/-- **What `HJO.Mellit.MellitInduction` reduces to.** There is a replication family and a braid
value for it satisfying the two properties above. By
`HJO.Mellit.mellitInduction_iff_braidClosedForm` this is *equivalent* to the clause, so it is a
reformulation and not a weakening; and by that same equivalence it is exactly the
three cited results, with the braid representation abstracted. -/
def BraidClosedForm (S : SweepSystem L q u) (a b : ℕ) : Prop :=
  ∃ (Ω : ℕ → ℕ → ℕ → (S.W →ₗ[L] S.W)) (B : List ℕ → S.W),
    IsReplicationFamily S Ω ∧ IsBraidValue S Ω a b B ∧ IsColouringValue S a b B

/-! ### The induction -/

/-- **The induction on the number of parts.** From the two properties of the braid
value, `B(α) = (-1)^{(a-1)N}(qu)^{ℓ-N} G_{ℓ,α_ℓ} ⋯ G_{1,α_1}(1)` for every composition with
positive parts. The base is `B(∅) = 1`; the step is `HJO.Mellit.braidRep_specialBraid_dplusIter`
followed by `HJO.Mellit.stageWord_append` and `HJO.Mellit.inductionScalar_append`, the scalars being
multiplied by linearity of `HJO.Mellit.stage`. -/
theorem eq_inductionScalar_smul_stageWord {S : SweepSystem L q u}
    {Ω : ℕ → ℕ → ℕ → (S.W →ₗ[L] S.W)} {a b : ℕ} {B : List ℕ → S.W}
    (hB : IsBraidValue S Ω a b B) : ∀ α : List ℕ, (∀ x ∈ α, 0 < x) →
      B α = inductionScalar q u a α • stageWord S Ω a b α := by
  intro α
  induction α using List.reverseRecOn with
  | nil =>
    intro _
    rw [hB.nil, inductionScalar_nil, one_smul, stageWord]
    simp only [stageFrom]
  | append_singleton β A ih =>
    intro hpos
    have hβ : ∀ x ∈ β, 0 < x := fun x hx => hpos x (List.mem_append_left _ hx)
    have hA : 0 < A := hpos A (List.mem_append_right _ (List.mem_singleton_self A))
    rw [hB.append β A hβ hA, ih hβ, map_smul, smul_smul, stageWord_append,
      inductionScalar_append q u hβ hA]

/-! ### `HJO.Mellit.IsReplicationFamily.eq_index_one`, proved

`HJO.Mellit.IsReplicationFamily.eq_index_one`: a replication family is determined at every
`(j; m, n)` with `j ∈ {1,2,3}`, `(m,n)` coprime and `m + n ≥ 1`, except at the three triples where
`HJO.Mellit.IsReplicationFamily` pins nothing — `(1;0,1)`, `(2;0,1)` and `(3;1,0)`. The proof is
strong induction on the index sum, on the same fuel as `HJO.Mellit.exists_isReplicationFamily`.

This is not decoration here. `HJO.Mellit.MellitInduction` quantifies over *every* replication
family, so on the face of it it asks the same closed form of every one of them; uniqueness is what
says that is one demand and not many, and it is what lets the reduction above, stated for one
family, discharge the clause. -/

/-- A Stern–Brocot parent pair is coprime: `m n₁ - n m₁ = 1` is a Bézout identity
for the pair. -/
theorem coprime_of_isSBParent {m n m₁ n₁ : ℕ} (h : IsSBParent m n m₁ n₁) : Nat.Coprime m₁ n₁ :=
  Nat.isCoprime_iff_coprime.1 ⟨-(n : ℤ), (m : ℤ), by linear_combination h.2.2⟩

/-- The complement of a Stern–Brocot parent pair is coprime: `n m₂ - m n₂ = 1`. -/
theorem coprime_compl_of_isSBParent {m n m₁ n₁ : ℕ} (h : IsSBParent m n m₁ n₁) :
    Nat.Coprime (m - m₁) (n - n₁) := by
  obtain ⟨h1, h2, h3⟩ := h
  refine Nat.isCoprime_iff_coprime.1 ⟨(n : ℤ), -(m : ℤ), ?_⟩
  rw [Nat.cast_sub h1, Nat.cast_sub h2]
  linear_combination h3

/-- A Stern–Brocot parent pair of `(m, n)` is not `(0, 0)`, since `m·0 - n·0 = 0 ≠ 1`. -/
theorem one_le_add_of_isSBParent {m n m₁ n₁ : ℕ} (h : IsSBParent m n m₁ n₁) : 1 ≤ m₁ + n₁ := by
  obtain ⟨-, -, h3⟩ := h
  by_contra hc
  have e1 : m₁ = 0 := by omega
  have e2 : n₁ = 0 := by omega
  rw [e1, e2] at h3
  norm_num at h3

/-- The complement of a Stern–Brocot parent pair of `(m, n)` is not `(0, 0)`, since that would make
the pair `(m, n)` itself and `m n - n m = 0 ≠ 1`. -/
theorem one_le_compl_of_isSBParent {m n m₁ n₁ : ℕ} (h : IsSBParent m n m₁ n₁) :
    1 ≤ (m - m₁) + (n - n₁) := by
  obtain ⟨h1, h2, h3⟩ := h
  by_contra hc
  have e1 : m₁ = m := by omega
  have e2 : n₁ = n := by omega
  rw [e1, e2] at h3
  have : (0 : ℤ) = 1 := by linear_combination h3
  norm_num at this

/-- **A Stern–Brocot parent pair of `(m, n)` with `n ≥ 1` is not `(1, 0)`.** So the recursion of
`HJO.Mellit.IsReplicationFamily` never reads `Ω(3; 1, 0)`, the one triple at which the definition
pins nothing for `j = 3`. -/
theorem isSBParent_ne_one_zero {m n m₁ n₁ : ℕ} (hn : 1 ≤ n) (h : IsSBParent m n m₁ n₁) :
    ¬(m₁ = 1 ∧ n₁ = 0) := by
  rintro ⟨rfl, rfl⟩
  have h3 := h.2.2
  push_cast at h3
  omega

/-- **The complement of a Stern–Brocot parent pair of `(m, n)` with `m ≥ 1` is not `(0, 1)`.** So
the recursion never reads `Ω(1; 0, 1)` or `Ω(2; 0, 1)`, the two triples at which the definition
pins nothing for `j ∈ {1, 2}`: were the complement `(0, 1)` the pair would be `(m, n-1)` and
`m(n-1) - nm = -m` would have to be `1`. -/
theorem isSBParent_compl_ne_zero_one {m n m₁ n₁ : ℕ} (hm : 1 ≤ m) (h : IsSBParent m n m₁ n₁) :
    ¬(m - m₁ = 0 ∧ n - n₁ = 1) := by
  obtain ⟨h1, h2, h3⟩ := h
  rintro ⟨e1, e2⟩
  have hm1 : m₁ = m := by omega
  have hn1 : (n : ℤ) = (n₁ : ℤ) + 1 := by
    have : n₁ + 1 = n := by omega
    exact_mod_cast this.symm
  rw [hm1, hn1] at h3
  have h4 : -(m : ℤ) = 1 := by linear_combination h3
  omega

/-- **`HJO.Mellit.IsReplicationFamily.eq_index_one`, on any sweep system.** Two replication families
agree at every `(j; m, n)` with `1 ≤ j ≤ 3`, `(m, n)` coprime and `m + n ≥ 1`, except possibly at
`(1;0,1)`, `(2;0,1)` and `(3;1,0)`.

Strong induction on `m + n`. At `m = 0` coprimality forces `n = 1`, where `j = 3` is the base value
`y_1` and the other two are the excluded triples; at `n = 0` it forces `m = 1`, where `j ∈ {1,2}`
are the base values `d^*_+` and `z_1` and `j = 3` is excluded. Otherwise `m, n ≥ 1` and the three
displayed rules apply at any Stern–Brocot parent pair, whose two halves descend in index sum by
`HJO.Mellit.isSBParent_sum_lt`, are coprime, are not `(0,0)`, and — this is the point of the three
exclusions — are never the pair or the complement the definition leaves unpinned. -/
theorem replUnique (S : SweepSystem L q u) : ReplUnique S := by
  intro Ω Ω' hΩ hΩ'
  suffices H : ∀ f j m n : ℕ, m + n ≤ f → 1 ≤ j → j ≤ 3 → Nat.Coprime m n → 1 ≤ m + n →
      (j, m, n) ≠ (1, 0, 1) → (j, m, n) ≠ (2, 0, 1) → (j, m, n) ≠ (3, 1, 0) →
        Ω j m n = Ω' j m n from fun j m n => H (m + n) j m n le_rfl
  intro f
  induction f with
  | zero => intro j m n hf _ _ _ h1 _ _ _; omega
  | succ f ih =>
    intro j m n hf hj1 hj3 hmn h1 e1 e2 e3
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · have hn : n = 1 := Nat.coprime_zero_left n |>.1 hmn
      subst hn
      interval_cases j
      · exact absurd rfl e1
      · exact absurd rfl e2
      · rw [hΩ.base_three, hΩ'.base_three]
    · rcases Nat.eq_zero_or_pos n with rfl | hn
      · have hm' : m = 1 := Nat.coprime_zero_right m |>.1 hmn
        subst hm'
        interval_cases j
        · rw [hΩ.base_one, hΩ'.base_one]
        · rw [hΩ.base_two, hΩ'.base_two]
        · exact absurd rfl e3
      · obtain ⟨m₁, n₁, hpar⟩ : ∃ m₁ n₁, IsSBParent m n m₁ n₁ :=
          ⟨_, _, isSBParent_sbParent hmn hm hn⟩
        obtain ⟨hlt1, hlt2⟩ := isSBParent_sum_lt hm hn hpar
        have hne1 : ¬(m₁ = 1 ∧ n₁ = 0) := isSBParent_ne_one_zero hn hpar
        have hne2 : ¬(m - m₁ = 0 ∧ n - n₁ = 1) := isSBParent_compl_ne_zero_one hm hpar
        have h3 : Ω 3 m₁ n₁ = Ω' 3 m₁ n₁ := by
          refine ih 3 m₁ n₁ (by omega) (by omega) le_rfl (coprime_of_isSBParent hpar)
            (one_le_add_of_isSBParent hpar) ?_ ?_ ?_
          · intro hh
            simp only [Prod.mk.injEq] at hh
            omega
          · intro hh
            simp only [Prod.mk.injEq] at hh
            omega
          · intro hh
            simp only [Prod.mk.injEq] at hh
            exact hne1 ⟨hh.2.1, hh.2.2⟩
        have hc : ∀ j' : ℕ, 1 ≤ j' → j' ≤ 2 →
            Ω j' (m - m₁) (n - n₁) = Ω' j' (m - m₁) (n - n₁) := by
          intro j' hj1' hj2'
          refine ih j' _ _ (by omega) hj1' (by omega) (coprime_compl_of_isSBParent hpar)
            (one_le_compl_of_isSBParent hpar) ?_ ?_ ?_
          · intro hh
            simp only [Prod.mk.injEq] at hh
            exact hne2 ⟨hh.2.1, hh.2.2⟩
          · intro hh
            simp only [Prod.mk.injEq] at hh
            exact hne2 ⟨hh.2.1, hh.2.2⟩
          · intro hh
            simp only [Prod.mk.injEq] at hh
            omega
        interval_cases j
        · rw [hΩ.rule_one m n m₁ n₁ hmn hm hn hpar, hΩ'.rule_one m n m₁ n₁ hmn hm hn hpar, h3,
            hc 1 le_rfl (by omega)]
        · rw [hΩ.rule_two m n m₁ n₁ hmn hm hn hpar, hΩ'.rule_two m n m₁ n₁ hmn hm hn hpar, h3,
            hc 2 (by omega) le_rfl]
        · rw [hΩ.rule_three m n m₁ n₁ hmn hm hn hpar, hΩ'.rule_three m n m₁ n₁ hmn hm hn hpar, h3,
            hc 2 (by omega) le_rfl]

/-- **The replicated letter does not depend on the replication family.**
`HJO.Mellit.replicatedLetter` reads `Ω(2; a, b)`, and `0 < a` puts `(2; a, b)` outside the one
triple `HJO.Mellit.IsReplicationFamily.eq_index_one` excludes for `j = 2`. -/
theorem replicatedLetter_congr {S : SweepSystem L q u} {Ω Ω' : ℕ → ℕ → ℕ → (S.W →ₗ[L] S.W)}
    (hΩ : IsReplicationFamily S Ω) (hΩ' : IsReplicationFamily S Ω') {a b : ℕ}
    (hab : Nat.Coprime a b) (ha : 0 < a) (k : ℕ) :
    replicatedLetter S Ω a b k = replicatedLetter S Ω' a b k := by
  have e2 : Ω 2 a b = Ω' 2 a b := by
    refine replUnique S Ω Ω' hΩ hΩ' 2 a b (by omega) (by omega) hab (by omega) ?_ ?_ ?_ <;>
      · intro hh
        simp only [Prod.mk.injEq] at hh
        omega
  rw [replicatedLetter, replicatedLetter, e2]

/-- **A stage does not depend on the replication family.** `HJO.Mellit.stage` reads `Ω(1; a, b)`
and the replicated letter; both are pinned by `HJO.Mellit.IsReplicationFamily.eq_index_one` once
`0 < a`. -/
theorem stage_congr {S : SweepSystem L q u} {Ω Ω' : ℕ → ℕ → ℕ → (S.W →ₗ[L] S.W)}
    (hΩ : IsReplicationFamily S Ω) (hΩ' : IsReplicationFamily S Ω') {a b : ℕ}
    (hab : Nat.Coprime a b) (ha : 0 < a) (k A : ℕ) :
    stage S Ω a b k A = stage S Ω' a b k A := by
  have e1 : Ω 1 a b = Ω' 1 a b := by
    refine replUnique S Ω Ω' hΩ hΩ' 1 a b (by omega) (by omega) hab (by omega) ?_ ?_ ?_ <;>
      · intro hh
        simp only [Prod.mk.injEq] at hh
        omega
  rw [stage, stage, replicatedLetter_congr hΩ hΩ' hab ha, e1]

/-- **`G_{ℓ,α_ℓ} ⋯ G_{1,α_1}(1)` does not depend on the replication family.** This is what makes
`HJO.Mellit.MellitInduction`, which quantifies over every replication family, follow from the
closed form for one of them. -/
theorem stageWord_congr {S : SweepSystem L q u} {Ω Ω' : ℕ → ℕ → ℕ → (S.W →ₗ[L] S.W)}
    (hΩ : IsReplicationFamily S Ω) (hΩ' : IsReplicationFamily S Ω') {a b : ℕ}
    (hab : Nat.Coprime a b) (ha : 0 < a) (α : List ℕ) :
    stageWord S Ω a b α = stageWord S Ω' a b α := by
  have hfrom : ∀ (α : List ℕ) (k : ℕ) (v : S.W),
      stageFrom S Ω a b k v α = stageFrom S Ω' a b k v α := by
    intro α
    induction α with
    | nil => intro k v; simp only [stageFrom]
    | cons A β ihβ =>
      intro k v
      simp only [stageFrom, stage_congr hΩ hΩ' hab ha]
      exact ihβ _ _
  rw [stageWord, stageWord, hfrom]

/-! ### The reduction -/

/-- **`HJO.Mellit.mellitInduction_sweepWitness` from the three citations.** Given a replication
family and a braid value for it satisfying
`HJO.Mellit.braidValueColouring_eq_dsc_floor` together with
`HJO.Mellit.invFin_eq_invIni_of_separatesDiagonal` and
`HJO.Mellit.braidRep_specialBraid_dplusIter`, the clause holds — for *every* replication family,
by `HJO.Mellit.stageWord_congr`.

The hypotheses on `a` and `b` are only what uniqueness needs; `HJO.Mellit.MellitInput` supplies
both. **No hypothesis on `q` or `u`**: see the module docstring. -/
theorem mellitInduction_of_braidClosedForm {S : SweepSystem L q u} {a b : ℕ}
    (hab : Nat.Coprime a b) (ha : 0 < a) (h : BraidClosedForm S a b) : MellitInduction S a b := by
  obtain ⟨Ω₀, B, hΩ₀, hB, hD⟩ := h
  intro Ω hΩ N η hlevel hsep α hpos hsum
  subst hsum
  rw [hD _ η hlevel hsep α hpos rfl, eq_inductionScalar_smul_stageWord hB α hpos,
    stageWord_congr hΩ₀ hΩ hab ha α, inductionScalar]

/-- **The reduction loses nothing.** Conversely the clause gives a braid value: take
`B(α)` to be its own right-hand side. So `HJO.Mellit.BraidClosedForm` is a reformulation of
`HJO.Mellit.MellitInduction` and not a weakening of it — in particular it cannot be satisfied by
fiat any more than the clause can. -/
theorem braidClosedForm_of_mellitInduction {S : SweepSystem L q u} {a b : ℕ}
    (h : MellitInduction S a b) : BraidClosedForm S a b := by
  obtain ⟨Ω, hΩ⟩ := exists_isReplicationFamily S
  refine ⟨Ω, fun α => inductionScalar q u a α • stageWord S Ω a b α, hΩ, ⟨?_, ?_⟩, ?_⟩
  · rw [inductionScalar_nil, one_smul, stageWord]
    simp only [stageFrom]
  · intro α A hα hA
    rw [inductionScalar_append q u hα hA, stageWord_append, map_smul, smul_smul]
  · intro N η hlevel hsep α hpos hsum
    subst hsum
    exact h Ω hΩ _ η hlevel hsep α hpos rfl

/-- **`HJO.Mellit.mellitInduction_sweepWitness` is exactly the three citations.** The clause is
equivalent to `HJO.Mellit.BraidClosedForm`. Read left to right this is the reduction; read right to
left it is the certificate that nothing was smuggled in or left out. -/
theorem mellitInduction_iff_braidClosedForm {S : SweepSystem L q u} {a b : ℕ}
    (hab : Nat.Coprime a b) (ha : 0 < a) : MellitInduction S a b ↔ BraidClosedForm S a b :=
  ⟨braidClosedForm_of_mellitInduction, mellitInduction_of_braidClosedForm hab ha⟩

/-! ### Corner checks -/

/-- **At `N = 0` every nonnegative level separates the diagonal.** The only lattice point in range
is the origin, whose above-diagonal rank is `0`. Needed because
`HJO.Mellit.separatesDiagonal_sepLevel` takes `0 < N`, and the corner of
`HJO.Mellit.MellitInduction` is at the empty composition. -/
theorem separatesDiagonal_zero (a b : ℕ) : SeparatesDiagonal a b 0 (1 / 2) := by
  intro x y hx hy _
  have hx0 : x = 0 := by simpa using hx
  have hy0 : y = 0 := by simpa using hy
  subst hx0
  subst hy0
  rw [abovePointRank]
  norm_num

/-- **`1/2` is an admissible level.** -/
theorem isAdmissibleLevel_half : IsAdmissibleLevel (1 / 2) := ⟨0, by norm_num⟩

/-- **The corner check: the clause forces `D_{η,∅} = 1`.** At the empty composition
`HJO.Mellit.compColouring` gives `c_∅ = ∅`, the stage word is the vacuum and the scalar is `1`, so
`HJO.Mellit.MellitInduction` *implies* `HJO.Mellit.isAdmissibleColouring_empty_and_dsc_eq_one` at
`η = 1/2`. Two things follow. The corner is consistent —
`HJO.Mellit.isAdmissibleColouring_empty_and_dsc_eq_one` is a theorem,
not a competing claim — and the clause is not vacuous: a sweep system with `D = 0` and `vac ≠ 0`
refutes it outright, which is the guard `HJO.Mellit.RhsSumsAgree` provides for the other
clauses. -/
theorem d_empty_eq_vac_of_mellitInduction {S : SweepSystem L q u} {a b : ℕ}
    (h : MellitInduction S a b) : S.D (1 / 2) ∅ = S.vac := by
  obtain ⟨Ω, hΩ⟩ := exists_isReplicationFamily S
  have hval := h Ω hΩ 0 (1 / 2) isAdmissibleLevel_half (separatesDiagonal_zero a b) []
    (List.forall_mem_nil _) rfl
  simpa [compColouring, stageWord, stageFrom] using hval

/-- **The reduction transports the `q = 0` refutation unchanged.** `HJO.Mellit.BraidClosedForm`,
`HJO.Mellit.Rem41` and `HJO.Mellit.RhsSumsAgree` are jointly contradictory at `q = 0`, `u = 1`,
`(a, b) = (2, 3)`, exactly as `HJO.Mellit.false_of_clauses_at_zero` says of the clause itself. This
is the check that the reduction did not weaken the clause at the one parameter value where the
clauses are known to be jointly false: a `BraidClosedForm` satisfiable there would have been a
reduction to nothing.

The scalar of this clause is degenerate exactly at `qu = 0`, that is at `q = 0` or at `u = 0`, so
those are the only two parameter values from which a refutation of this shape can come. The second
one does **not** yield one, and the reason is worth recording since it is why `q ≠ 0` rather than
`qu ≠ 0` is what this route forces. At `u = 0` the parking-function side of
`HJO.Mellit.sum_sweepChar_eq_sum_gessel` keeps only its terms of `ârea = 0`, and by
`HJO.Paths.aboveArea` a path of zero above-diagonal area has `ŷ_r = ⌈br/a⌉` at every `r`, hence
passes through every diagonal point `(ak, bk)` and has return composition `(1, …, 1)` — for which
`ℓ = N` and the factor `(qu)^{ℓ-N}` is `1`. So at `u = 0` the vanishing of the scalar and the
vanishing of the sum it would have to contradict happen at disjoint compositions. This paragraph is
an analysis, not a Lean statement: it would need the area-zero characterisation, which is not
formalized. -/
theorem not_braidClosedForm_of_clauses_at_zero {K : Type} [Field K] [Algebra ℚ K]
    (S : SweepSystem K 0 1) (hB : BraidClosedForm S 2 3) (hrem : Rem41 S 2 3)
    (hrhs : RhsSumsAgree S 2 3) : False :=
  false_of_clauses_at_zero S
    (mellitInduction_of_braidClosedForm (by norm_num) (by norm_num) hB) hrem hrhs

/-! ### The colouring of a composition determines its sum

`HJO.Mellit.SweepSystem.D` is a function of a level and a colouring only, where the real
`HJO.Mellit.dsc` in `HJO/Shuffle/Colouring.lean` — also takes `a`, `b`
and `N`. The parameters `a` and `b` are fixed with the system, but `N` is quantified inside
`HJO.Mellit.MellitInduction`, so the erasure is only sound if a colouring of the form `c_α`
determines `N`. It does, as soon as `0 < b`. -/

/-- Every point of `c_α` has ordinate at most `bN`: both families of
`HJO.Mellit.compColouring` have ordinates `b` times a partial sum of `α`. -/
theorem snd_le_of_mem_compColouring {a b : ℕ} {α : List ℕ} {p : ℕ × ℕ}
    (hp : p ∈ compColouring a b α) : p.2 ≤ b * α.sum := by
  have key : ∀ i : ℕ, (α.take i).sum ≤ α.sum := fun i => by
    have h : (α.take i).sum + (α.drop i).sum = α.sum := by
      rw [← List.sum_append, List.take_append_drop]
    omega
  rw [compColouring, Finset.mem_union] at hp
  rcases hp with hp | hp
  · obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hp
    exact Nat.mul_le_mul_left b (key i)
  · obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hp
    exact Nat.mul_le_mul_left b (key (i + 1))

/-- The ordinate `bN` is attained: the last member of the second family of
`HJO.Mellit.compColouring` is the foot of the east step arriving at the final touch point. -/
theorem mem_compColouring_top {a b : ℕ} {α : List ℕ} (h : α ≠ []) :
    (a * α.sum - 1, b * α.sum) ∈ compColouring a b α := by
  have hlen : 0 < α.length := List.length_pos_iff.2 h
  refine Finset.mem_union_right _ (Finset.mem_image.2 ⟨α.length - 1, Finset.mem_range.2 ?_, ?_⟩)
  · omega
  · rw [show α.length - 1 + 1 = α.length by omega, List.take_length]

/-- **A colouring of the form `c_α` determines `N`.** So the top layer's `N`-free
`HJO.Mellit.SweepSystem.D` is a faithful reading of `HJO.Mellit.dsc`: on the colourings the
interface applies it to, the `N` that `HJO.Mellit.dsc` needs is recoverable. The hypothesis `0 < b`
holds throughout the standing range `1 < a < b`. -/
theorem sum_eq_of_compColouring_eq {a b : ℕ} (hb : 0 < b) {α β : List ℕ} (hα : α ≠ [])
    (hβ : β ≠ []) (h : compColouring a b α = compColouring a b β) : α.sum = β.sum := by
  have h1 : (a * β.sum - 1, b * β.sum) ∈ compColouring a b α := by
    rw [h]; exact mem_compColouring_top hβ
  have h2 : (a * α.sum - 1, b * α.sum) ∈ compColouring a b β := by
    rw [← h]; exact mem_compColouring_top hα
  have e1 : b * β.sum ≤ b * α.sum := snd_le_of_mem_compColouring h1
  have e2 : b * α.sum ≤ b * β.sum := snd_le_of_mem_compColouring h2
  exact Nat.eq_of_mul_eq_mul_left hb (le_antisymm e2 e1)

end HJO.Mellit
