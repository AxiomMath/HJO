/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Mathlib.Combinatorics.Enumerative.Composition
public import Mathlib.RingTheory.AlgebraicIndependent.Defs
public import HJO.Symmetric.EpsilonSelection
public meta import HJO.Attr

/-! # The all-path evaluation is a symmetric polynomial in the two parameters

Summing the sign-extraction identity of a composite creation operator over the compositions of
`N` turns it into an identity for the elementary symmetric function `e_N`: the below-diagonal
`(aN, bN)`-paths are partitioned by their return composition, so the right-hand sides add up to
the generating polynomial of *all* of them by hook count and area. That polynomial, an honest
element of `ℤ[X₀, X₁]`, is what the first half of this file produces; the scalar it computes is
therefore a polynomial in the two parameters and not merely a rational function.

The second half exchanges the parameters. The displacement `f[X + M/z]` is unchanged by the
exchange, `M = (1 - q)(1 - u)` being symmetric, hence so are the basic operators, the normalised
commutators built from them and therefore the slope operators; and the axis generators only ever
see the product of the two parameters. A slope homomorphism at `(a, b)` for one order of the
parameters is thus a slope homomorphism for the other, and the same scalar is computed by the
generating polynomial with the two parameters exchanged.

The compositional rational shuffle identity, the effect of sign extraction on the fundamental
quasisymmetric functions and the expansion of `e_N` over the compositions of `N` are taken as
explicit hypotheses; none of the three is proved here.
-/

@[expose] public section

open Finset

namespace HJO.ThetaSymmetry

open Paths ParkingFunctions

/-! ### Running sums of a list of positive naturals -/

/-- The head of a running `scanl` is its initial value. -/
private theorem head?_scanl {β α : Type*} (f : β → α → β) (b : β) (l : List α) :
    (l.scanl f b).head? = some b := by
  cases l <;> simp

/-- A running sum over a list with one entry appended appends the new total. -/
private theorem scanl_add_concat : ∀ (l : List ℕ) (x c : ℕ),
    (l ++ [x]).scanl (· + ·) c = l.scanl (· + ·) c ++ [c + l.sum + x] := by
  intro l
  induction l with
  | nil => intro x c; simp
  | cons y l ih =>
    intro x c
    simp only [List.cons_append, List.scanl_cons, ih, List.sum_cons, add_assoc]

/-- Every entry of a running sum is at least the initial value. -/
private theorem le_of_mem_scanl_add' : ∀ (l : List ℕ) (c k : ℕ),
    k ∈ l.scanl (· + ·) c → c ≤ k := by
  intro l
  induction l with
  | nil => intro c k h; simp only [List.scanl_nil, List.mem_singleton] at h; omega
  | cons y l ih =>
    intro c k h
    rw [List.scanl_cons, List.mem_cons] at h
    rcases h with rfl | h
    · exact le_rfl
    · exact le_trans (Nat.le_add_right c y) (ih (c + y) k h)

/-- Every entry of a running sum is at most the initial value plus the total. -/
private theorem le_of_mem_scanl_add : ∀ (l : List ℕ) (c k : ℕ),
    k ∈ l.scanl (· + ·) c → k ≤ c + l.sum := by
  intro l
  induction l with
  | nil => intro c k h; simp only [List.scanl_nil, List.mem_singleton] at h; simp [h]
  | cons y l ih =>
    intro c k h
    rw [List.scanl_cons, List.mem_cons] at h
    rcases h with rfl | h
    · exact Nat.le_add_right _ _
    · have := ih (c + y) k h
      simp only [List.sum_cons]
      omega

/-- A running sum over positive entries is strictly increasing. -/
private theorem pairwise_scanl_add : ∀ (l : List ℕ), (∀ x ∈ l, 0 < x) → ∀ c : ℕ,
    (l.scanl (· + ·) c).Pairwise (· < ·) := by
  intro l
  induction l with
  | nil => intro _ c; simp
  | cons y l ih =>
    intro hl c
    rw [List.scanl_cons, List.pairwise_cons]
    refine ⟨fun k hk => ?_, ih (fun x hx => hl x (List.mem_cons_of_mem _ hx)) _⟩
    have h1 : c + y ≤ k := le_of_mem_scanl_add' l (c + y) k hk
    have h2 : 0 < y := hl y (by simp)
    omega

/-- A list is determined by its running sums. -/
private theorem scanl_add_injective : ∀ (l l' : List ℕ) (c : ℕ),
    l.scanl (· + ·) c = l'.scanl (· + ·) c → l = l' := by
  intro l
  induction l with
  | nil =>
    intro l' c h
    cases l' with
    | nil => rfl
    | cons y l' =>
      have hl := congrArg List.length h
      simp only [List.length_scanl, List.length_nil, List.length_cons] at hl
      omega
  | cons x l ih =>
    intro l' c h
    cases l' with
    | nil =>
      have hl := congrArg List.length h
      simp only [List.length_scanl, List.length_nil, List.length_cons] at hl
      omega
    | cons y l' =>
      rw [List.scanl_cons, List.scanl_cons] at h
      simp only [List.cons.injEq, true_and] at h
      have hxy : c + x = c + y :=
        Option.some_injective _ (by
          have := congrArg List.head? h
          rwa [head?_scanl, head?_scanl] at this)
      have hx : x = y := by omega
      subst hx
      rw [ih l' (c + x) h]

/-- Two lists of positive naturals with the same total and the same set of running sums are
equal. -/
private theorem eq_of_scanl_mem_iff {l l' : List ℕ} (hl : ∀ x ∈ l, 0 < x)
    (hl' : ∀ x ∈ l', 0 < x) (hs : l.sum = l'.sum)
    (h : ∀ k ≤ l.sum, (k ∈ l.scanl (· + ·) 0 ↔ k ∈ l'.scanl (· + ·) 0)) : l = l' := by
  refine scanl_add_injective l l' 0 (List.SortedLT.eq_of_mem_iff
    (List.sortedLT_iff_pairwise.2 (pairwise_scanl_add l hl 0))
    (List.sortedLT_iff_pairwise.2 (pairwise_scanl_add l' hl' 0)) fun k => ?_)
  by_cases hk : k ≤ l.sum
  · exact h k hk
  · exact ⟨fun hm => absurd (le_of_mem_scanl_add l 0 k hm) (by omega),
      fun hm => absurd (le_of_mem_scanl_add l' 0 k hm) (by omega)⟩

/-- A predicate holding at `0` and at `N` is the set of running sums of a list of positive
naturals summing to `N`: the parts are the gaps between successive points where it holds. -/
private theorem exists_scanl_eq (R : ℕ → Prop) : ∀ N : ℕ, R 0 → R N →
    ∃ l : List ℕ, (∀ x ∈ l, 0 < x) ∧ l.sum = N ∧ ∀ k ≤ N, (R k ↔ k ∈ l.scanl (· + ·) 0) := by
  classical
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    intro h0 hN
    rcases Nat.eq_zero_or_pos N with rfl | hNpos
    · refine ⟨[], by simp, by simp, fun k hk => ?_⟩
      have hk0 : k = 0 := Nat.le_zero.1 hk
      subst hk0
      simpa using h0
    · have hne : ((range N).filter R).Nonempty := ⟨0, mem_filter.2 ⟨mem_range.2 hNpos, h0⟩⟩
      set m := ((range N).filter R).max' hne with hmdef
      have hmmem : m ∈ (range N).filter R := ((range N).filter R).max'_mem hne
      have hmlt : m < N := mem_range.1 (mem_filter.1 hmmem).1
      have hmR : R m := (mem_filter.1 hmmem).2
      have hmmax : ∀ j, j < N → R j → j ≤ m := fun j hj hjR =>
        Finset.le_max' _ j (mem_filter.2 ⟨mem_range.2 hj, hjR⟩)
      obtain ⟨l, hpos, hsum, hmem⟩ := ih m hmlt h0 hmR
      refine ⟨l ++ [N - m], ?_, ?_, ?_⟩
      · intro x hx
        rcases List.mem_append.1 hx with hx | hx
        · exact hpos x hx
        · rw [List.mem_singleton] at hx; omega
      · rw [List.sum_append, List.sum_singleton, hsum]; omega
      · intro k hk
        rw [scanl_add_concat l (N - m) 0, hsum]
        rw [show 0 + m + (N - m) = N by omega, List.mem_append, List.mem_singleton]
        rcases le_or_gt k m with hkm | hkm
        · refine ⟨fun hR => Or.inl ((hmem k hkm).1 hR), ?_⟩
          rintro (hh | hh)
          · exact (hmem k hkm).2 hh
          · exact absurd hkm (by omega)
        · rcases eq_or_lt_of_le hk with hkN | hkN
          · exact ⟨fun _ => Or.inr hkN, fun _ => hkN ▸ hN⟩
          · refine ⟨fun hR => absurd (hmmax k hkN hR) (by omega), ?_⟩
            rintro (hh | hh)
            · exact absurd (le_of_mem_scanl_add l 0 k hh) (by omega)
            · exact absurd hh (by omega)

/-! ### The return composition of a below-diagonal path -/

section Returns

variable {a b N : ℕ}

/-- A below-diagonal path has at most one return composition. -/
theorem hasReturns_unique {α β : List ℕ} {y : Heights a b N}
    (hα : HasReturns α y) (hβ : HasReturns β y) : α = β :=
  eq_of_scanl_mem_iff hα.2.1 hβ.2.1 (hα.2.2.1.trans hβ.2.2.1.symm) fun k hk => by
    rw [hα.2.2.1] at hk
    exact (hα.2.2.2 k hk).symm.trans (hβ.2.2.2 k hk)

/-- A below-diagonal path has a return composition: the ranks at which it touches the diagonal
are the running sums of a composition of `N`. -/
theorem exists_hasReturns {y : Heights a b N} (hy : IsBelowDiagonal y) :
    ∃ c : Composition N, HasReturns c.blocks y := by
  obtain ⟨l, hpos, hsum, hmem⟩ :=
    exists_scanl_eq (fun k => ht y (a * k) = b * k) N (by simpa using hy.1) hy.2.1
  exact ⟨⟨l, fun hx => hpos _ hx, hsum⟩, hy, hpos, hsum, hmem⟩

/-- The below-diagonal `(aN, bN)`-paths are partitioned by their return composition, so a sum
over all of them may be taken one composition of `N` at a time. -/
theorem sum_composition_hasReturns {M : Type*} [AddCommMonoid M] (f : Heights a b N → M) :
    ∑ c : Composition N, ∑ y ∈ (univ : Finset (Heights a b N)) with HasReturns c.blocks y, f y
      = ∑ y ∈ (univ : Finset (Heights a b N)) with IsBelowDiagonal y, f y := by
  have hdisj : Set.PairwiseDisjoint (↑(univ : Finset (Composition N)) : Set (Composition N))
      fun c : Composition N =>
        {y ∈ (univ : Finset (Heights a b N)) | HasReturns c.blocks y} := by
    intro c _ d _ hcd
    simp only [Function.onFun, Finset.disjoint_left, mem_filter, mem_univ, true_and]
    exact fun y hy hy' => hcd (Composition.ext (hasReturns_unique hy hy'))
  rw [← Finset.sum_biUnion hdisj]
  refine Finset.sum_congr (Finset.ext fun y => ?_) fun _ _ => rfl
  rw [mem_biUnion, mem_filter]
  constructor
  · rintro ⟨c, -, hc⟩
    exact ⟨mem_univ y, (mem_filter.1 hc).2.1⟩
  · rintro ⟨-, hy⟩
    obtain ⟨c, hc⟩ := exists_hasReturns hy
    exact ⟨c, mem_univ c, mem_filter.2 ⟨mem_univ y, hc⟩⟩

/-- The same partition read through the reversal of compositions: reversing the blocks is a
bijection of the compositions of `N`, so the paths with return composition `α.reverse`, as `α`
runs over the compositions of `N`, are again all the below-diagonal paths, each once. -/
theorem sum_composition_hasReturns_reverse {M : Type*} [AddCommMonoid M]
    (f : Heights a b N → M) :
    ∑ c : Composition N,
        ∑ y ∈ (univ : Finset (Heights a b N)) with HasReturns c.blocks.reverse y, f y
      = ∑ y ∈ (univ : Finset (Heights a b N)) with IsBelowDiagonal y, f y := by
  rw [← sum_composition_hasReturns f]
  exact Fintype.sum_bijective Composition.reverse Composition.reverse_bijective _ _
    fun c => by rw [Composition.reverse_blocks]

end Returns

/-! ### The generating polynomial of all below-diagonal paths -/

/-- The generating polynomial of the below-diagonal `(aN, bN)`-paths by hook count and area: the
first variable carries the hook count and the second the area. -/
noncomputable def pathPoly (a b N : ℕ) : MvPolynomial (Fin 2) ℤ :=
  ∑ y ∈ (univ : Finset (Heights a b N)) with IsBelowDiagonal y,
    (MvPolynomial.X 0 : MvPolynomial (Fin 2) ℤ) ^ hookCount y * MvPolynomial.X 1 ^ area y

/-- `pathPoly` corrected by the sign `(-1) ^ (N (b + 1))`, the polynomial that the scalar
attached to `e_N` is a value of. -/
noncomputable def signedPathPoly (a b N : ℕ) : MvPolynomial (Fin 2) ℤ :=
  (-1) ^ (N * (b + 1)) * pathPoly a b N

/-- Evaluating `pathPoly` at a pair of ring elements gives the generating function of the
below-diagonal paths by hook count and area. -/
theorem aeval_pathPoly {L : Type*} [CommRing L] (a b N : ℕ) (q u : L) :
    MvPolynomial.aeval ![q, u] (pathPoly a b N) =
      ∑ y ∈ (univ : Finset (Heights a b N)) with IsBelowDiagonal y,
        q ^ hookCount y * u ^ area y := by
  simp [pathPoly]

/-- Evaluating `signedPathPoly` is evaluating `pathPoly` up to the sign. -/
theorem aeval_signedPathPoly {L : Type*} [CommRing L] (a b N : ℕ) (q u : L) :
    MvPolynomial.aeval ![q, u] (signedPathPoly a b N) =
      (-1) ^ (N * (b + 1)) * MvPolynomial.aeval ![q, u] (pathPoly a b N) := by
  simp [signedPathPoly]

/-! ### The exchange of the two parameters on the operator side -/

section Swap

/-- The displacement `f[X + M/z]` is unchanged by exchanging the two parameters, the factor
`M = (1 - q)(1 - u)` being symmetric in them. -/
theorem plethShift_swap {K : Type*} [CommRing K] (q u : K) :
    Sym.plethShift q u = Sym.plethShift u q :=
  congrArg MvPolynomial.aeval (funext fun i => by
    rw [mul_comm (1 - q ^ (i + 1)) (1 - u ^ (i + 1))])

variable {L : Type*} [Field L] [Algebra ℚ L]

/-- The basic operators are unchanged by exchanging the two parameters. -/
theorem Dop_swap (q u : L) (k : ℕ) : Sym.Dop q u k = Sym.Dop u q k := by
  unfold Sym.Dop
  rw [plethShift_swap q u]

/-- The fuelled slope operators are unchanged by exchanging the two parameters: the
normalisation `M⁻¹` of the commutators is symmetric, and the split of a slope does not see the
parameters at all. -/
theorem QopAux_swap (q u : L) : ∀ fuel m n : ℕ,
    Sym.QopAux q u fuel m n = Sym.QopAux u q fuel m n := by
  intro fuel
  induction fuel with
  | zero => intro m n; exact Dop_swap q u n
  | succ fuel ih =>
    intro m n
    simp only [Sym.QopAux, Dop_swap q u, ih, mul_comm (1 - q) (1 - u)]

/-- The primitive evaluator is unchanged by exchanging the two parameters. -/
theorem QopPrim_swap (q u : L) (m n : ℕ) : Sym.QopPrim q u m n = Sym.QopPrim u q m n :=
  QopAux_swap q u m m n

/-- The slope operators are unchanged by exchanging the two parameters: the dispatch of `Qop`
tests only the two slopes, and each of its three branches is symmetric in the parameters. -/
theorem Qop_swap (q u : L) (m n : ℕ) : Sym.Qop q u m n = Sym.Qop u q m n := by
  rw [Sym.Qop, Sym.Qop]
  split_ifs
  · exact Dop_swap q u n
  · exact QopPrim_swap q u m n
  · rw [QopPrim_swap q u (m - (Sym.slopeSplit m n).1) (n - (Sym.slopeSplit m n).2),
      QopPrim_swap q u (Sym.slopeSplit m n).1 (Sym.slopeSplit m n).2,
      mul_comm (1 - q) (1 - u)]

/-- A slope homomorphism at `(a, b)` for one order of the two parameters is a slope
homomorphism at `(a, b)` for the other: the axis generators see only the product of the
parameters, and the slope operators are symmetric in them. -/
theorem isSlopeHom_swap {a b : ℕ} (q u : L)
    (Θ : Sym.Lambda L →ₐ[L] Module.End L (Sym.Lambda L)) (h : Sym.IsSlopeHom a b q u Θ) :
    Sym.IsSlopeHom a b u q Θ := fun k hk => by
  rw [mul_comm u q, ← Qop_swap]
  exact h k hk

/-- Algebraic independence of the two parameters is unchanged by exchanging them: exchanging them
is the injective renaming of the two variables of the polynomials in two variables. -/
theorem algebraicIndependent_swap {R : Type*} [CommRing R] {q u : R}
    (hqu : AlgebraicIndependent ℤ ![q, u]) : AlgebraicIndependent ℤ ![u, q] := by
  have hcomp : (![q, u] ∘ ![1, 0] : Fin 2 → R) = ![u, q] := by
    funext i
    fin_cases i <;> simp
  rw [← hcomp]
  exact hqu.comp ![1, 0] (by decide)

end Swap

/-! ### The external inputs -/

/-- Sign extraction reads off the total coefficient of the fundamental quasisymmetric functions
with a full descent set, from an expansion indexed by descent sets, that is by subsets of
`{1, …, n - 1}`. This is an external input and is not proved here. -/
def GesselSelection (L : Type*) [Field L] [Algebra ℚ L] : Prop :=
  ∀ (ι : Sym.Lambda L →ₐ[L] Sym.AlphabetSeries L), Sym.IsRealisation ι →
    ∀ n : ℕ, 0 < n → ∀ (I : Type) (J : Finset I) (w : I → L) (S : I → Finset ℕ)
      (f : Sym.Lambda L), MvPolynomial.IsWeightedHomogeneous (fun i => i + 1) f n →
      (∀ i ∈ J, S i ⊆ Ico 1 n) →
      ι f = ∑ i ∈ J, w i • gessel L n (S i) →
      Sym.signExtract L f = ∑ i ∈ J with S i = Ico 1 n, w i

section Hypotheses

variable {L : Type*} [Field L] [Algebra ℚ L]

/-- The compositional rational shuffle identity at the parameters `(q, u)`: for a slope
homomorphism at `(a, b)` for those parameters, the seed of a composition `β` is the generating
function of the parking functions with return composition `β.reverse` by dinv, area and inverse
descent set, the below-diagonal convention reading the blocks of the source's composition from the
other end. This is an external input and is not proved here. -/
def ShuffleIdentity (a b : ℕ) (q u : L) : Prop :=
  ∀ (ι : Sym.Lambda L →ₐ[L] Sym.AlphabetSeries L), Sym.IsRealisation ι →
    ∀ Θ : Sym.Lambda L →ₐ[L] Module.End L (Sym.Lambda L), Sym.IsSlopeHom a b q u Θ →
      ∀ M : ℕ, 0 < M → ∀ β : List ℕ, (∀ x ∈ β, 0 < x) → β.sum = M →
        MvPolynomial.IsWeightedHomogeneous (fun i => i + 1)
            ((-1 : L) ^ (M * (b + 1)) • Θ (Sym.CopComp q β 1) 1) (b * M) ∧
          ι ((-1 : L) ^ (M * (b + 1)) • Θ (Sym.CopComp q β 1) 1) =
            ∑ π ∈ withReturns β.reverse a b M, (q ^ dinv π * u ^ area (path π)) •
              gessel L (b * M) (ides π)

/-- The expansion of `e_N` over the compositions of `N` in the composite creation seeds at the
parameter `v`. This is an external input and is not proved here. -/
def IsCreationExpansion (N : ℕ) (v : L) : Prop :=
  Sym.elemSymm L N = ∑ c : Composition N, Sym.CopComp v c.blocks 1

end Hypotheses

/-! ### The all-path evaluation -/

section Main

variable {a b N : ℕ} {L : Type*} [Field L] [Algebra ℚ L]

/-- The scalar attached to `e_N` by a slope homomorphism at `(a, b)` is the value at the two
parameters of the generating polynomial of all below-diagonal `(aN, bN)`-paths by hook count and
area, corrected by the sign `(-1) ^ (N (b + 1))`. In particular it is a polynomial in the two
parameters. -/
theorem signExtract_elemSymm_eq_aeval {q u : L} (shuffle : ShuffleIdentity a b q u)
    (gesselSelection : GesselSelection L) (ι : Sym.Lambda L →ₐ[L] Sym.AlphabetSeries L)
    (hι : Sym.IsRealisation ι) (Θ : Sym.Lambda L →ₐ[L] Module.End L (Sym.Lambda L))
    (hΘ : Sym.IsSlopeHom a b q u Θ) (ha : 0 < a) (hb : 0 < b) (hN : 0 < N)
    (hexp : IsCreationExpansion N q) :
    Sym.signExtract L (Θ (Sym.elemSymm L N) 1) =
      MvPolynomial.aeval ![q, u] (signedPathPoly a b N) := by
  have hexp' : Sym.elemSymm L N = ∑ c : Composition N, Sym.CopComp q c.blocks 1 := hexp
  have key : (-1 : L) ^ (N * (b + 1)) * Sym.signExtract L (Θ (Sym.elemSymm L N) 1) =
      MvPolynomial.aeval ![q, u] (pathPoly a b N) := by
    rw [aeval_pathPoly, ← sum_composition_hasReturns_reverse, hexp']
    simp only [map_sum, LinearMap.sum_apply, Finset.mul_sum]
    exact Finset.sum_congr rfl fun c _ =>
      EpsilonSelection.signExtract_copComp_eq_sum_paths shuffle gesselSelection ι hι Θ hΘ ha hb hN
        c.blocks (fun _ hx => c.blocks_pos hx) c.blocks_sum
  have hsq : ((-1 : L) ^ (N * (b + 1))) * ((-1 : L) ^ (N * (b + 1))) = 1 := by
    rw [← pow_add]
    exact Even.neg_one_pow ⟨_, rfl⟩
  rw [aeval_signedPathPoly, ← key, ← mul_assoc, hsq, one_mul]

/-- The value of the generating polynomial of all below-diagonal `(aN, bN)`-paths at the two
parameters is unchanged when they are exchanged: the same slope homomorphism computes the same
scalar for either order of the parameters. -/
theorem aeval_signedPathPoly_swap {q u : L} (shuffle : ShuffleIdentity a b q u)
    (shuffleSwap : ShuffleIdentity a b u q) (gesselSelection : GesselSelection L)
    (ι : Sym.Lambda L →ₐ[L] Sym.AlphabetSeries L) (hι : Sym.IsRealisation ι)
    (Θ : Sym.Lambda L →ₐ[L] Module.End L (Sym.Lambda L)) (hΘ : Sym.IsSlopeHom a b q u Θ)
    (ha : 0 < a) (hb : 0 < b) (hN : 0 < N) (hexp : IsCreationExpansion N q)
    (hexpSwap : IsCreationExpansion N u) :
    MvPolynomial.aeval ![q, u] (signedPathPoly a b N) =
      MvPolynomial.aeval ![u, q] (signedPathPoly a b N) := by
  rw [← signExtract_elemSymm_eq_aeval shuffle gesselSelection ι hι Θ hΘ ha hb hN hexp,
    signExtract_elemSymm_eq_aeval shuffleSwap gesselSelection ι hι Θ
      (isSlopeHom_swap q u Θ hΘ) ha hb hN hexpSwap]

/-- For a slope homomorphism at `(a, b)` and every `N ≥ 1`, the scalar obtained by sign
extraction from the operator attached to `e_N`, applied to `1`, is the value at the two
parameters of a two-variable integer polynomial, and that value is unchanged when the two
parameters are exchanged. -/
@[hjo "lem_theta_e_symmetry"]
theorem signExtract_elemSymm_isPoly_and_swap {q u : L} (shuffle : ShuffleIdentity a b q u)
    (shuffleSwap : ShuffleIdentity a b u q) (gesselSelection : GesselSelection L)
    (ι : Sym.Lambda L →ₐ[L] Sym.AlphabetSeries L) (hι : Sym.IsRealisation ι)
    (Θ : Sym.Lambda L →ₐ[L] Module.End L (Sym.Lambda L)) (hΘ : Sym.IsSlopeHom a b q u Θ)
    (ha : 0 < a) (hb : 0 < b) (hN : 0 < N) (hexp : IsCreationExpansion N q)
    (hexpSwap : IsCreationExpansion N u) :
    Sym.signExtract L (Θ (Sym.elemSymm L N) 1) =
        MvPolynomial.aeval ![q, u] (signedPathPoly a b N) ∧
      MvPolynomial.aeval ![q, u] (signedPathPoly a b N) =
        MvPolynomial.aeval ![u, q] (signedPathPoly a b N) :=
  ⟨signExtract_elemSymm_eq_aeval shuffle gesselSelection ι hι Θ hΘ ha hb hN hexp,
    aeval_signedPathPoly_swap shuffle shuffleSwap gesselSelection ι hι Θ hΘ ha hb hN hexp
      hexpSwap⟩

end Main

end HJO.ThetaSymmetry
