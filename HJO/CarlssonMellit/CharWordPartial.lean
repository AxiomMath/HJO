/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.CarlssonMellit.CharRaising
public import HJO.CarlssonMellit.ChiQOne
public import HJO.CarlssonMellit.ConjugationOperator
public import HJO.CarlssonMellit.EastInverseRecover
public import HJO.CarlssonMellit.InsertInjectiveBounded
public import HJO.CarlssonMellit.LowerPieces
public import HJO.CarlssonMellit.MarkedCharSeries
public import HJO.CarlssonMellit.MarkedWord
public import HJO.CarlssonMellit.NuEast
public import HJO.CarlssonMellit.NuLower
public import HJO.CarlssonMellit.PartialLevelSteps
public import HJO.CarlssonMellit.PartialStepWord
public import HJO.CarlssonMellit.PartialWordZero
public meta import HJO.Attr

/-! # A Dyck path as a word in the operators, modulo the lowering sum

Carlsson and Mellit read a Dyck path `π` of length `n` as a word `ε₁ ⋯ ε_{2n}` in two letters and
compute its characteristic series by applying one operator per letter to `1 ∈ V_0 = Λ`: their
Theorem 4.4. This file carries out the last three steps of that argument — the lowering recursion,
the induction over the steps of a partial path, and Theorem 4.4 itself — **modulo exactly one
input**, the lowering-sum identity, which is carried as the explicit hypothesis
`HJO.Dyck.IsLoweringSum`. That identity is proved as `HJO.Dyck.isLoweringSum` in
`HJO/CarlssonMellit/LoweringSumClosed.lean`, where the three results are restated with the
hypothesis discharged, Theorem 4.4 becoming `HJO.Dyck.realisation_constantCoeff_markedWordOp'`.

## Main definitions

* `HJO.Sweep.partialWordOp`: the composite `d_{ε₁} ∘ ⋯ ∘ d_{ε_M}` of the operators of a word of
  steps, each read at the level of the value it is applied to. The level argument is the level of
  the *output*: a north letter reads `V_{k+1}` and lands in `V_k`, an east letter reads `V_{k-1}`
  and lands in `V_k`. This is the shape the recursion consumes a word in, one letter at a time.
* `HJO.Dyck.IsLoweringSum`: the lowering-sum identity, quantified over the instances
  the recursion applies it at. See "The lowering-sum hypothesis" below.

## Main results

* `HJO.Dyck.isSigmaCharacter_dminusCM`: the lowering recursion — `d_-G` is an
  `Id_{k-1}`-character of `π` read in `𝔻_{k-1,N}` — granted the instance of the lowering sum
  at that path and that `G`; unconditionally `HJO.Dyck.isSigmaCharacter_dminusCM'`.
* `HJO.Dyck.mem_piece_and_isSigmaCharacter_partialWordOp`: the composite of the letters of
  `w_k(π)`, applied to `1`, lies in `V_k` and is an `Id_k`-character of `π` — granted
  `IsLoweringSum`; unconditionally `HJO.Dyck.mem_piece_and_isSigmaCharacter_partialWordOp'`.
* `HJO.Dyck.realisation_constantCoeff_markedWordOp`: Theorem 4.4, `ι(Ξ_{π,∅}(1)) = χ(π)` — granted
  `IsLoweringSum`; unconditionally `HJO.Dyck.realisation_constantCoeff_markedWordOp'`.
* `HJO.Sweep.partialWordOp_zero_stepWord`: the full word of a square Dyck path, read by
  `partialWordOp` from level `0`, is the unmarked word `Ξ_{π,∅}` of `HJO.Sweep.markedWordOp`. This
  is what makes the statement of Theorem 4.4 here the `T = ∅` case of
  `HJO.Mellit.map_constantCoeff_markedWordOp'`.

## The lowering-sum hypothesis

The lowering-sum identity is the one step of Carlsson and Mellit's Section 4 that is not carried
out in this file: its display

`Φ_{k-1}(ι_{k-1}(θ_{k-1}(d_-G))) = (q-1)^{N-k+1} ∑_{r ≥ 0} z^{(k)}_{k+r} μ_r(π)`

is derived from the three parts it rests on separately, as `HJO.Dyck.isLoweringSum`. Here it is
carried as a hypothesis, in the spelling the surrounding declarations dictate:
`HJO.Dyck.IsLoweringSum q` is that display at `k = m + 1`, with `Φ_{k-1} = HJO.Sym.insertFront`,
`θ = HJO.Sweep.theta`, `d_- = HJO.Sweep.dminusCM`, `μ_r = HJO.Dyck.lowerCharPiece` and the sum
formed as `HJO.Sym.summableSum` — that is, its right-hand side is literally the scalar
`(q-1)^{N-m}` times the right-hand side of
`HJO.Dyck.insertFront_partialCharSeries_identityTuple` (the sum being summable by
`HJO.Dyck.isSummableFamily_zvar_mul_lowerCharPiece`), which is the form in which
`HJO.Dyck.isSigmaCharacter_dminusCM` cancels the two against each other. Carlsson and Mellit index
the letters from `1` and the library from `0`, so their `z^{(k)}_{k+r}` is
`HJO.Sym.zvar K (m+1) (m+r)`; that is the same shift that makes `HJO.Dyck.lowerTuple m r` the tuple
`(1, …, k-1, k+r)`.

It is quantified over the level, the length, the path, the two realisations and `G`, because the
induction of `HJO.Dyck.mem_piece_and_isSigmaCharacter_partialWordOp` applies it at every level of
the path and, at an east step, to a shorter path: an instance at one path does not serve. Every
hypothesis of the lemma appears — `k ≥ 1` as the shape `m + 1`, `N ≥ k` and `π ∈ 𝔻_{k,N}` as
`IsPartialDyck (m+1) N x`, and `G ∈ V_k` an `Id_k`-character as the last two — so
`HJO.Dyck.isLoweringSum` proves `IsLoweringSum q` with nothing to adapt.

For that reason none of the three results here is the unconditional statement: a theorem carrying
the lowering sum as a hypothesis is only conditional on it. The unconditional statements are the
primed declarations of `HJO/CarlssonMellit/LoweringSumClosed.lean`.

## Implementation notes

*The level attached to a letter is the level of its input.* `HJO.Sweep.stepOp q ε k` reads `V_k`,
and `HJO.Sweep.markedFactor` reads position `s` at `HJO.Dyck.wordLevel x s`. `partialWordOp` is
written the other way round — recursing on the word from the left, its level argument is the level
the whole composite lands in — because that is the direction the induction runs: at a
north step the level rises by one and the word loses its leading letter. The two readings agree on
a square Dyck path, which is `HJO.Sweep.partialWordOp_zero_stepWord`, and the truncated subtraction
in the east clause of the definition never bites there.

*What `HJO.Dyck.isSigmaCharacter_dminusCM` needs beyond the proof as usually written.* The argument
as usually written cancels `Φ_{k-1}` from the two sides by injectivity of `Φ_{k-1}`, which is
**false** at the only total rendering of `Φ` (`HJO.Sym.not_injective_insertFront`); the repaired
statement is `HJO.Sym.injOn_insertFront`, injectivity on the series of bounded `x₁`-degree. So the
two arguments must be shown to lie in that set: `HJO.Dyck.boundedFrontDegree_partialCharSeries` for
`ν_σ(π)`, whose `x₁`-exponent is at most the number `N` of positions, and
`HJO.Dyck.boundedFrontDegree_apply_of_mem_piece` for `ι_k(θ_k(d_-G))`, by way of the auxiliary
`HJO.Dyck.BoundedDegree`, a bound on the *total* alphabet degree, which is what the algebra `ι_k` is
a homomorphism of. The restriction to `V_k` there is not cosmetic: `HJO.Dyck.IsAuxRealisation` says
nothing about the auxiliary variables above the level, so `ι_k` of an element outside `V_k` can be
any series at all.

*Theorem 4.4 is stated as the `T = ∅` case of `HJO.Mellit.map_constantCoeff_markedWordOp'`.* Its
composite is `HJO.Sweep.markedWordOp q x ∅` of `HJO.Sweep.markedWordOp`, which by
`HJO.Sweep.markedFactor_empty` is the `d_{ε₁} ∘ ⋯ ∘ d_{ε_{2n}}` — every position
contributing its own letter — rather than a second full-word composite; and its right-hand side is
`HJO.Dyck.pathMarkedCharSeries q x ∅`, which is `HJO.Dyck.pathCharSeries`'s `χ(π)`. The value is
read out of `V_0 = Λ` by `MvPolynomial.constantCoeff`, `V_0` being the constants.

*Three hypotheses that Theorem 4.4 as usually stated does not carry.* `q ≠ 0` comes from
`HJO.Dyck.isSigmaCharacter_cmDPlus`, whose statement needs it; `∀ r, IsUnit (q^{r+1} - 1)` comes
from `HJO.Dyck.auxZeroMap_eq_pathCharSeries_of_isSigmaCharacter` through the bijectivity of `θ`;
and `CharZero` is needed by `HJO.Dyck.auxZeroMap_eq_pathCharSeries_of_isSigmaCharacter` as well
and does not follow from `Algebra ℚ K` by instance search. The `n ≥ 1` is *not* carried: nothing
here reads it, and at `n = 0` both sides are `1`.

## References

E. Carlsson and A. Mellit, *A proof of the shuffle conjecture*, arXiv:1508.06239v3, J. Amer. Math.
Soc. **31** (2018) 661--697, Section 4: the recursion `χ_{k+1}(Eπ) = d_+χ_k(π)`,
`χ_{k-1}(Nπ) = d_-χ_k(π)` and Theorem 4.4.
-/

@[expose] public section

namespace HJO.Sweep

open Finset HJO.Dyck

variable {L : Type*} [Field L] [Algebra ℚ L]

/-! ### The composite of the letters of a word -/

/-- **The composite `d_{ε₁}(d_{ε₂}(⋯ d_{ε_M}(-)⋯))` of the operators of a word of steps**, each
factor read at the level of the value it is applied to.

The level argument is the level of the **output**: a north letter `DyckStep.U` contributes Carlsson
and Mellit's lowering operator `d_-` of `HJO.Sweep.dminusCM`, which reads `V_{k+1}` and lands in
`V_k`, and an east letter `DyckStep.D` contributes the raising operator `d_+` of
`HJO.Sweep.cmDPlus`, which reads `V_{k-1}` and lands in `V_k`. Recursing on the word from the left
is what the character recursion does — at a north step the level rises by one and the word loses its
leading letter — and the subtraction in the east clause is truncated, harmlessly: on the word of a
partial Dyck path read at its own level no east letter is ever met at output level `0`. -/
noncomputable def partialWordOp (q : L) : ℕ → List DyckStep → Module.End L (Total L)
  | _, [] => 1
  | k, DyckStep.U :: w => dminusCM q (k + 1) * partialWordOp q (k + 1) w
  | k, DyckStep.D :: w => cmDPlus q (k - 1) * partialWordOp q (k - 1) w

/-- The empty word is the identity: the composite over no letters. -/
@[simp]
theorem partialWordOp_nil (q : L) (k : ℕ) : partialWordOp q k [] = 1 := rfl

/-- One north letter: `d_-` at the level `k + 1` it reads, before the composite of the rest at the
output level `k + 1`. -/
theorem partialWordOp_U_cons (q : L) (k : ℕ) (w : List DyckStep) :
    partialWordOp q k (DyckStep.U :: w) = dminusCM q (k + 1) * partialWordOp q (k + 1) w := rfl

/-- One east letter: `d_+` at the level `k - 1` it reads, before the composite of the rest at the
output level `k - 1`. -/
theorem partialWordOp_D_cons (q : L) (k : ℕ) (w : List DyckStep) :
    partialWordOp q k (DyckStep.D :: w) = cmDPlus q (k - 1) * partialWordOp q (k - 1) w := rfl

/-- One east letter at a positive output level, where the truncated subtraction of
`HJO.Sweep.partialWordOp_D_cons` does not bite. This is the form the east step of the recursion
uses, its level being `k + 1` there. -/
theorem partialWordOp_D_cons_succ (q : L) (k : ℕ) (w : List DyckStep) :
    partialWordOp q (k + 1) (DyckStep.D :: w) = cmDPlus q k * partialWordOp q k w := rfl

/-! ### The level of the value produced by a suffix of the word -/

/-- The number of north steps of the step word of `x` at positions `< s`. -/
private def northBelow {n : ℕ} (x : Fin n → ℕ) (s : ℕ) : ℕ := #{k : Fin n | x k + (k : ℕ) < s}

/-- The level of the value produced by the positions `s, s + 1, …, 2n - 1` acting on `1 ∈ V_0`. -/
private def lvl {n : ℕ} (x : Fin n → ℕ) (s : ℕ) : ℕ := 2 * northBelow x s - s

private theorem northBelow_zero {n : ℕ} (x : Fin n → ℕ) : northBelow x 0 = 0 := by
  rw [northBelow, card_eq_zero]
  exact filter_false_of_mem fun k _ => Nat.not_lt_zero _

private theorem lvl_zero {n : ℕ} (x : Fin n → ℕ) : lvl x 0 = 0 := by
  simp only [lvl, northBelow_zero]

private theorem northBelow_succ {n : ℕ} (x : Fin n → ℕ) (s : ℕ) :
    northBelow x (s + 1) = northCount x s := by
  simp only [northBelow, northCount, Nat.lt_succ_iff]

private theorem lvl_succ {n : ℕ} (x : Fin n → ℕ) (s : ℕ) : lvl x (s + 1) = wordLevel x s := by
  simp only [lvl, northBelow_succ, wordLevel]

private theorem le_two_mul_northBelow {n : ℕ} {x : Fin n → ℕ} (h : IsSquareDyck n x) {s : ℕ}
    (hs : s ≤ 2 * n) : s ≤ 2 * northBelow x s := by
  cases s with
  | zero => exact Nat.zero_le _
  | succ t =>
    have := h.succ_le_two_mul_northCount (show t < 2 * n by omega)
    rw [northBelow_succ]
    omega

/-- At a position carrying a north step the count through `s` exceeds the count below `s` by one:
the north step at `s` belongs to the unique row `k` with `x k + k = s`. -/
private theorem northCount_eq_succ {n : ℕ} {x : Fin n → ℕ} (h : IsSquareDyck n x) {s : ℕ}
    {k₀ : Fin n} (hk₀ : x k₀ + (k₀ : ℕ) = s) : northCount x s = northBelow x s + 1 := by
  have hfilter : ({k : Fin n | x k + (k : ℕ) ≤ s} : Finset (Fin n))
      = insert k₀ ({k : Fin n | x k + (k : ℕ) < s} : Finset (Fin n)) := by
    ext k
    simp only [mem_filter_univ, mem_insert]
    refine ⟨fun hk => ?_, ?_⟩
    · rcases Nat.lt_or_ge (x k + (k : ℕ)) s with hlt | hge
      · exact Or.inr hlt
      · exact Or.inl
          (h.strictMono_add_index.injective (show x k + (k : ℕ) = x k₀ + (k₀ : ℕ) by omega))
    · rintro (rfl | hlt)
      · omega
      · omega
  have hnot : k₀ ∉ ({k : Fin n | x k + (k : ℕ) < s} : Finset (Fin n)) := by
    simp only [mem_filter_univ]
    omega
  rw [northCount, northBelow, hfilter, card_insert_of_notMem hnot]

/-- At a position carrying an east step the two counts agree. -/
private theorem northCount_eq_of_ne {n : ℕ} (x : Fin n → ℕ) {s : ℕ}
    (hs : ∀ k : Fin n, x k + (k : ℕ) ≠ s) : northCount x s = northBelow x s := by
  have hfilter : ({k : Fin n | x k + (k : ℕ) ≤ s} : Finset (Fin n))
      = ({k : Fin n | x k + (k : ℕ) < s} : Finset (Fin n)) := by
    ext k
    simp only [mem_filter_univ]
    have := hs k
    omega
  rw [northCount, northBelow, hfilter]

/-- At a north step the level of the value produced by the positions from `s` on is one less than
the level the factor of `s` reads. -/
private theorem lvl_add_one_of_U {n : ℕ} {x : Fin n → ℕ} (h : IsSquareDyck n x) {s : ℕ}
    (hs : s < 2 * n) (hlen : s < (stepWord x).length)
    (hU : (stepWord x)[s] = DyckStep.U) : lvl x s + 1 = wordLevel x s := by
  obtain ⟨k₀, hk₀⟩ := (getElem_stepWord_eq_U_iff x s hlen).1 hU
  have hc := northCount_eq_succ h hk₀
  have hle := le_two_mul_northBelow h (le_of_lt hs)
  simp only [lvl, wordLevel, hc]
  omega

/-- At an east step the level of the value produced by the positions from `s` on is one more than
the level the factor of `s` reads. -/
private theorem lvl_eq_add_one_of_D {n : ℕ} {x : Fin n → ℕ} (h : IsSquareDyck n x) {s : ℕ}
    (hs : s < 2 * n) (hlen : s < (stepWord x).length)
    (hD : (stepWord x)[s] = DyckStep.D) : lvl x s = wordLevel x s + 1 := by
  have hc := northCount_eq_of_ne x ((getElem_stepWord_eq_D_iff x s hlen).1 hD)
  have hadd := h.wordLevel_add hs
  simp only [lvl, ← hc]
  omega

/-! ### The word of a suffix -/

private theorem partialWordOp_drop (q : L) {n : ℕ} {x : Fin n → ℕ} (h : IsSquareDyck n x) :
    ∀ m s : ℕ, s + m = 2 * n →
      partialWordOp q (lvl x s) ((stepWord x).drop s)
        = (List.ofFn fun t : Fin m => markedFactor q x ∅ (s + (t : ℕ))).prod := by
  intro m
  induction m with
  | zero =>
    intro s hsm
    rw [List.drop_eq_nil_of_le (by rw [length_stepWord]; omega), partialWordOp_nil]
    simp
  | succ m ih =>
    intro s hsm
    have hs : s < 2 * n := by omega
    have hlen : s < (stepWord x).length := by rw [length_stepWord]; omega
    have hhead : markedFactor q x ∅ s = stepOp q ((stepWord x)[s]) (wordLevel x s) := by
      rw [markedFactor_empty, List.getD_eq_getElem _ _ hlen]
    have htail : (fun t : Fin m => markedFactor q x ∅ (s + ((Fin.succ t : Fin (m + 1)) : ℕ)))
        = fun t : Fin m => markedFactor q x ∅ (s + 1 + (t : ℕ)) := by
      funext t
      congr 1
      simp only [Fin.val_succ]
      omega
    rw [List.ofFn_succ, List.prod_cons, Fin.val_zero, Nat.add_zero, hhead, htail,
      ← ih (s + 1) (by omega), List.drop_eq_getElem_cons hlen]
    cases hstep : (stepWord x)[s] with
    | U => rw [partialWordOp_U_cons, stepOp_U, lvl_add_one_of_U h hs hlen hstep, lvl_succ]
    | D =>
      rw [partialWordOp_D_cons, stepOp_D, lvl_eq_add_one_of_D h hs hlen hstep,
        Nat.add_sub_cancel, lvl_succ]

/-- **The full word of a square Dyck path is the unmarked marked-word composite.** -/
theorem partialWordOp_zero_stepWord (q : L) {n : ℕ} {x : Fin n → ℕ} (h : IsSquareDyck n x) :
    partialWordOp q 0 (stepWord x) = markedWordOp q x ∅ := by
  have hd := partialWordOp_drop q h (2 * n) 0 (by omega)
  rw [lvl_zero, List.drop_zero] at hd
  rw [hd, markedWordOp_eq_prod]
  simp

end HJO.Sweep

namespace HJO.Dyck

open HJO.Sym

/-! ### The insertion cancels where the recursion applies it -/

section Bounded

variable {K : Type*} [CommRing K]

/-- The exponent of the first letter in `x₁^a·e` pushed up one letter is `a`: the pushed-up tail
`e.mapDomain Nat.succ` vanishes at `0` not being a successor. -/
private theorem single_add_mapDomain_apply_zero (a : ℕ) (e : ℕ →₀ ℕ) :
    (Finsupp.single 0 a + e.mapDomain Nat.succ : ℕ →₀ ℕ) 0 = a := by
  rw [Finsupp.add_apply, Finsupp.single_eq_same,
    Finsupp.mapDomain_of_notMem_range e 0 (by simp), add_zero]

/-- **`ν_σ(π)` has bounded `x₁`-degree**, with the bound `N` at every letter-monomial: a labelling
of `N` positions contributes at most `N` to the exponent of the first letter of its free part
(`HJO.Dyck.ztailExponent_apply_zero_le`), so above `N` the finite sum computing the coefficient
(`HJO.Dyck.coeff_partialCharSeries`) is a sum over the empty set. This is the hypothesis
`HJO.Sym.injOn_insertFront` needs at `ν_σ(π)`. -/
theorem boundedFrontDegree_partialCharSeries (q : K) (k : ℕ) {N : ℕ} (x : Fin N → ℕ)
    (σ : Fin k → ℕ) : Sym.BoundedFrontDegree (partialCharSeries q k x σ) := fun e =>
  ⟨N, fun a ha => by
    rw [coeff_partialCharSeries]
    refine Finset.sum_eq_zero fun w hw => ?_
    exfalso
    simp only [Finset.mem_filter] at hw
    have hle := ztailExponent_apply_zero_le k w
    rw [hw.2.2, single_add_mapDomain_apply_zero] at hle
    omega⟩

/-- An auxiliary boundedness notion with better closure properties than
`HJO.Sym.BoundedFrontDegree`: the coefficients of `F` vanish at every letter-monomial of total
degree above a bound. Closed under sums and products, and it implies the bound on the first
letter. -/
private def BoundedDegree {m : ℕ} (F : Sym.AuxAlphabetSeries K m) : Prop :=
  ∃ D : ℕ, ∀ α : ℕ →₀ ℕ, D < Finsupp.degree α → MvPowerSeries.coeff α F = 0

/-- A bound on the total degree bounds the degree in the first letter, the exponent of the first
letter being at most the total degree. -/
private theorem boundedFrontDegree_of_boundedDegree {m : ℕ} {F : Sym.AuxAlphabetSeries K m}
    (hF : BoundedDegree F) : Sym.BoundedFrontDegree F := by
  obtain ⟨D, hD⟩ := hF
  refine fun e => ⟨D, fun a ha => hD _ ?_⟩
  have h2 := Finsupp.le_degree (R := ℕ) 0 (Finsupp.single 0 a + e.mapDomain Nat.succ)
  rw [single_add_mapDomain_apply_zero] at h2
  omega

private theorem BoundedDegree.add {m : ℕ} {F G : Sym.AuxAlphabetSeries K m}
    (hF : BoundedDegree F) (hG : BoundedDegree G) : BoundedDegree (F + G) := by
  obtain ⟨D₁, h₁⟩ := hF
  obtain ⟨D₂, h₂⟩ := hG
  refine ⟨max D₁ D₂, fun α hα => ?_⟩
  rw [map_add, h₁ α (lt_of_le_of_lt (le_max_left _ _) hα),
    h₂ α (lt_of_le_of_lt (le_max_right _ _) hα), add_zero]

private theorem BoundedDegree.mul {m : ℕ} {F G : Sym.AuxAlphabetSeries K m}
    (hF : BoundedDegree F) (hG : BoundedDegree G) : BoundedDegree (F * G) := by
  classical
  obtain ⟨D₁, h₁⟩ := hF
  obtain ⟨D₂, h₂⟩ := hG
  refine ⟨D₁ + D₂, fun α hα => ?_⟩
  rw [MvPowerSeries.coeff_mul]
  refine Finset.sum_eq_zero fun p hp => ?_
  have hsum : Finsupp.degree p.1 + Finsupp.degree p.2 = Finsupp.degree α := by
    rw [← map_add Finsupp.degree, Finset.HasAntidiagonal.mem_antidiagonal.1 hp]
  by_cases h : D₁ < Finsupp.degree p.1
  · rw [h₁ _ h, zero_mul]
  · rw [h₂ p.2 (by omega), mul_zero]

/-- A constant has bounded total degree, with bound `0`. -/
private theorem boundedDegree_C {m : ℕ} (p : MvPolynomial (Fin m) K) :
    BoundedDegree (MvPowerSeries.C p : Sym.AuxAlphabetSeries K m) :=
  ⟨0, fun α hα => MvPowerSeries.coeff_C_of_ne_zero (fun h => by simp [h] at hα) p⟩

private theorem boundedDegree_algebraMap {m : ℕ} (c : K) :
    BoundedDegree (algebraMap K (Sym.AuxAlphabetSeries K m) c) := by
  rw [MvPowerSeries.algebraMap_apply, MvPolynomial.algebraMap_eq]
  exact boundedDegree_C _

/-- The value of `ι_k` at a power sum has bounded total degree, with bound `r + 1`: its
coefficients are supported on the monomials `x_i^{r+1}`, of total degree `r + 1`. -/
private theorem boundedDegree_apply_C_powerSum {m : ℕ}
    {ι : Sweep.Total K →ₐ[K] Sym.AuxAlphabetSeries K m} (hι : IsAuxRealisation m ι) (r : ℕ) :
    BoundedDegree (ι (MvPolynomial.C (Sym.powerSum K (r + 1)))) :=
  ⟨r + 1, fun α hα => hι.coeff_of_ne r α fun i h => by
    rw [h, Finsupp.degree_single] at hα
    omega⟩

/-- The value of `ι_k` at an element of `Λ`, read inside the total space as a constant, has bounded
total degree: `Λ` is generated by the power sums, and the bound is closed under sums and
products. -/
private theorem boundedDegree_apply_C {m : ℕ}
    {ι : Sweep.Total K →ₐ[K] Sym.AuxAlphabetSeries K m} (hι : IsAuxRealisation m ι)
    (F : Sym.Lambda K) : BoundedDegree (ι (MvPolynomial.C F)) := by
  induction F using MvPolynomial.induction_on with
  | C c =>
    rw [show (MvPolynomial.C (MvPolynomial.C c : Sym.Lambda K) : Sweep.Total K)
        = algebraMap K (Sweep.Total K) c from rfl, ι.commutes]
    exact boundedDegree_algebraMap c
  | add p q hp hq => rw [MvPolynomial.C_add, map_add]; exact hp.add hq
  | mul_X p n hp =>
    rw [MvPolynomial.C_mul, map_mul]
    refine hp.mul ?_
    rw [show (MvPolynomial.X n : Sym.Lambda K) = Sym.powerSum K (n + 1) by
      rw [Sym.powerSum, Nat.add_sub_cancel]]
    exact boundedDegree_apply_C_powerSum hι n

/-- The value of `ι_k` at an element of `V_k` has bounded total degree: `V_k` is generated over `Λ`
by the auxiliary variables below the level, whose values are constants, and the bound is closed
under sums and products. -/
private theorem boundedDegree_apply_of_mem_piece {m : ℕ}
    {ι : Sweep.Total K →ₐ[K] Sym.AuxAlphabetSeries K m} (hι : IsAuxRealisation m ι)
    {H : Sweep.Total K} (hH : H ∈ Sweep.piece K m) : BoundedDegree (ι H) := by
  rw [Sweep.piece, MvPolynomial.supported_eq_adjoin_X] at hH
  induction hH using Algebra.adjoin_induction with
  | mem y hy =>
    obtain ⟨j, hj, rfl⟩ := hy
    have hlt : j < m := hj
    have hj' : ((⟨j, hlt⟩ : Fin m) : ℕ) + 1 - 1 = j := by simp
    rw [show (MvPolynomial.X j : Sweep.Total K) = Sweep.auxVar (((⟨j, hlt⟩ : Fin m) : ℕ) + 1) by
      rw [Sweep.auxVar, hj'], hι.map_auxVar ⟨j, hlt⟩]
    exact boundedDegree_C _
  | algebraMap r => exact boundedDegree_apply_C hι r
  | add y z _ _ hy hz => rw [map_add]; exact hy.add hz
  | mul y z _ _ hy hz => rw [map_mul]; exact hy.mul hz

/-- **The values of `ι_k` on `V_k` have bounded `x₁`-degree**: they have bounded *total* degree,
`V_k` being generated over `Λ` by the auxiliary variables — constants for `ι_k` — and `Λ` by the
power sums, whose values are supported on the monomials `x_i^r`. This is the hypothesis
`HJO.Sym.injOn_insertFront` needs at a value of `ι_k∘θ_k`. -/
theorem boundedFrontDegree_apply_of_mem_piece {m : ℕ}
    {ι : Sweep.Total K →ₐ[K] Sym.AuxAlphabetSeries K m} (hι : IsAuxRealisation m ι)
    {H : Sweep.Total K} (hH : H ∈ Sweep.piece K m) : Sym.BoundedFrontDegree (ι H) :=
  boundedFrontDegree_of_boundedDegree (boundedDegree_apply_of_mem_piece hι hH)

/-- **A scalar multiple of a series of bounded `x₁`-degree has bounded `x₁`-degree**, with the same
bound: the coefficients of `c·F` are `c` times those of `F`. -/
theorem boundedFrontDegree_smul {m : ℕ} (c : K) {F : Sym.AuxAlphabetSeries K m}
    (hF : Sym.BoundedFrontDegree F) : Sym.BoundedFrontDegree (c • F) := fun e => by
  obtain ⟨M, hM⟩ := hF e
  refine ⟨M, fun a ha => ?_⟩
  rw [show c • F = MvPowerSeries.C (MvPolynomial.C c) * F by
    rw [Algebra.smul_def, MvPowerSeries.algebraMap_apply, MvPolynomial.algebraMap_eq],
    MvPowerSeries.coeff_C_mul, hM a ha, mul_zero]

end Bounded

/-! ### An ordinary realisation read at level zero -/

section Zero

variable {K : Type*} [CommRing K]

/-- **An ordinary realisation read as a realisation with no auxiliary variables**: at level `0`
there are no auxiliary variables, so the coefficients `𝕜[y_1, …, y_0]` are the scalars and a
realisation `ι : Λ → 𝒫` extends to the total space by sending every auxiliary variable to `0`. This
is the converse of `HJO.Dyck.ofAuxRealisationZero`, and is what lets a statement about an arbitrary
realisation — `HJO.Dyck.realisation_constantCoeff_markedWordOp'` — be proved from the level-indexed
machinery. -/
noncomputable def toAuxRealisationZero (ι : Sym.Lambda K →ₐ[K] Sym.AlphabetSeries K) :
    Sweep.Total K →ₐ[K] Sym.AuxAlphabetSeries K 0 :=
  MvPolynomial.aevalTower
    ((MvPowerSeries.mapAlgHom (MvPolynomial.isEmptyAlgEquiv K (Fin 0)).symm.toAlgHom).comp ι)
    fun _ => 0

/-- The coefficients of the extension on `Λ`, read off: the identification of the level-`0`
coefficients with the scalars, applied to the coefficients of `ι`. -/
private theorem coeff_toAuxRealisationZero (ι : Sym.Lambda K →ₐ[K] Sym.AlphabetSeries K)
    (F : Sym.Lambda K) (d : ℕ →₀ ℕ) :
    MvPowerSeries.coeff d (toAuxRealisationZero ι (MvPolynomial.C F)) =
      (MvPolynomial.isEmptyAlgEquiv K (Fin 0)).symm (MvPowerSeries.coeff d (ι F)) := by
  rw [toAuxRealisationZero, MvPolynomial.aevalTower_C]
  rfl

/-- **The extension of a realisation is a realisation with auxiliary variables**: the power sums are
sent to the power sums of the alphabet, the identification of the coefficients carrying `1` to `1`
and `0` to `0`; and there is no auxiliary variable to fix, the binder `∀ j : Fin 0` being
vacuous. -/
theorem isAuxRealisation_toAuxRealisationZero {ι : Sym.Lambda K →ₐ[K] Sym.AlphabetSeries K}
    (h : Sym.IsRealisation ι) : IsAuxRealisation 0 (toAuxRealisationZero ι) where
  coeff_pow r i := by rw [coeff_toAuxRealisationZero, h.coeff_pow r i, map_one]
  coeff_of_ne r d hd := by rw [coeff_toAuxRealisationZero, h.coeff_of_ne r d hd, map_zero]
  map_auxVar j := j.elim0

/-- **The two readings are inverse**: restricting the extension of `ι` back to `Λ` returns `ι`,
since the identification of the level-`0` coefficients with the scalars is undone by its inverse. -/
theorem ofAuxRealisationZero_toAuxRealisationZero (ι : Sym.Lambda K →ₐ[K] Sym.AlphabetSeries K) :
    ofAuxRealisationZero (toAuxRealisationZero ι) = ι := by
  refine AlgHom.ext fun F => MvPowerSeries.ext fun d => ?_
  rw [coeff_ofAuxRealisationZero, coeff_toAuxRealisationZero, AlgEquiv.apply_symm_apply]

/-- A family of realisations with auxiliary variables, one per level, agreeing with a given one at
level `0`: the character recursion changes level at every step, so it reads a whole family, while
`HJO.Dyck.auxZeroMap_eq_pathCharSeries_of_isSigmaCharacter` reads the level-`0` member and nothing
above it. Above level `0` the canonical `HJO.Dyck.auxRealise` will do, nothing in the recursion
distinguishing between two realisations at the same level. -/
private noncomputable def auxFamily (ι₀ : Sweep.Total K →ₐ[K] Sym.AuxAlphabetSeries K 0) :
    ∀ l : ℕ, Sweep.Total K →ₐ[K] Sym.AuxAlphabetSeries K l
  | 0 => ι₀
  | (l + 1) => auxRealise K (l + 1)

/-- Every member of the family is a realisation with auxiliary variables at its own level. -/
private theorem isAuxRealisation_auxFamily {ι₀ : Sweep.Total K →ₐ[K] Sym.AuxAlphabetSeries K 0}
    (h : IsAuxRealisation 0 ι₀) : ∀ l : ℕ, IsAuxRealisation l (auxFamily ι₀ l)
  | 0 => h
  | (l + 1) => isAuxRealisation_auxRealise K (l + 1)

end Zero

/-! ### The lowering sum, carried as a hypothesis -/

section Lowering

variable {K : Type*} [Field K] [Algebra ℚ K]

/-- **The lowering-sum identity**, the one step of Carlsson and Mellit's Section 4 that is not
carried out in this file (it is proved as `HJO.Dyck.isLoweringSum`), quantified over the instances
the character recursion applies it at: for `k = m + 1 ≥ 1`, a partial Dyck path `π ∈ 𝔻_{k,N}`,
realisations `ι_{k-1}` and `ι_k` with auxiliary variables, and `G ∈ V_k` an `Id_k`-character of
`π`,

`Φ_{k-1}(ι_{k-1}(θ_{k-1}(d_-G))) = (q-1)^{N-k+1} ∑_{r ≥ 0} z^{(k)}_{k+r} μ_r(π)`.

The right-hand side is the scalar `(q-1)^{N-m}` times the right-hand side of
`HJO.Dyck.insertFront_partialCharSeries_identityTuple` (the sum being summable by
`HJO.Dyck.isSummableFamily_zvar_mul_lowerCharPiece`), which is how
`HJO.Dyck.isSigmaCharacter_dminusCM` cancels the two; the `z^{(k)}_{k+r}` is
`HJO.Sym.zvar K (m+1) (m+r)`, letters being indexed from `1` there and from `0` here.

The quantification is over the level, the length and the path because the induction of
`HJO.Dyck.mem_piece_and_isSigmaCharacter_partialWordOp` applies this at every level of the path
and, at an east step, to a shorter path. Every hypothesis of the lemma appears, and no other, so
`HJO.Dyck.isLoweringSum` proves this predicate with nothing to adapt. -/
def IsLoweringSum (q : K) : Prop :=
  ∀ (m N : ℕ) (x : Fin N → ℕ), IsPartialDyck (m + 1) N x →
    ∀ ι : Sweep.Total K →ₐ[K] Sym.AuxAlphabetSeries K m, IsAuxRealisation m ι →
      ∀ ι' : Sweep.Total K →ₐ[K] Sym.AuxAlphabetSeries K (m + 1), IsAuxRealisation (m + 1) ι' →
        ∀ G ∈ Sweep.piece K (m + 1),
          IsSigmaCharacter q (m + 1) ι' x (identityTuple (m + 1)) G →
            Sym.insertFront K m (ι (Sweep.theta q (Sweep.dminusCM q (m + 1) G))) =
              (q - 1) ^ (N - m) • Sym.summableSum
                fun r : ℕ => Sym.zvar K (m + 1) (m + r) * lowerCharPiece q m x r


/-! ### The lowering recursion -/

/-- **The lowering recursion, granted the lowering sum at this instance** (unconditionally,
`HJO.Dyck.isSigmaCharacter_dminusCM'`). For `k = m + 1 ≥ 1`, a partial Dyck path `π ∈ 𝔻_{k,N}` and
`G ∈ V_k` an `Id_k`-character of `π`, the element `d_-G` is an `Id_{k-1}`-character of `π` read in
`𝔻_{k-1,N}` — which it is by `HJO.Dyck.IsPartialDyck.of_le_level`, and `d_-G` lies in `V_{k-1}` by
`HJO.Sweep.dminusCM_mem_piece`, so these two side conditions of the lowering recursion are proved
elsewhere and are not restated here.

The hypothesis `hsum` is the instance of the lowering-sum identity at this path and this `G`; it
is the one input not proved here. See `HJO.Dyck.IsLoweringSum` and this module's header.

The proof is Carlsson and Mellit's: `hsum` and `HJO.Dyck.isSummableFamily_zvar_mul_lowerCharPiece`
(`HJO.Dyck.insertFront_partialCharSeries_identityTuple`) make the two sides of the character
equation agree after `Φ_{k-1}`, the scalar passing `Φ_{k-1}` by `HJO.Sym.insertFront_smul`, and
`Φ_{k-1}` is then cancelled. That last step is not the injectivity of `Φ_{k-1}`, which is false
(`HJO.Sym.not_injective_insertFront`), but its repaired form `HJO.Sym.injOn_insertFront`, whose
bound is discharged here by `HJO.Dyck.boundedFrontDegree_apply_of_mem_piece` on the left —
`θ_{k-1}(d_-G) ∈ V_{k-1}` by `HJO.Sweep.theta_mem_piece`, which is what makes the value of `ι_{k-1}`
there bounded at all — and by `HJO.Dyck.boundedFrontDegree_partialCharSeries` on the right. -/
theorem isSigmaCharacter_dminusCM (q : K) {m N : ℕ} {x : Fin N → ℕ}
    (hx : IsPartialDyck (m + 1) N x)
    {ι : Sweep.Total K →ₐ[K] Sym.AuxAlphabetSeries K m} (hι : IsAuxRealisation m ι)
    {G : Sweep.Total K} (hG : G ∈ Sweep.piece K (m + 1))
    (hsum : Sym.insertFront K m (ι (Sweep.theta q (Sweep.dminusCM q (m + 1) G))) =
      (q - 1) ^ (N - m) • Sym.summableSum
        fun r : ℕ => Sym.zvar K (m + 1) (m + r) * lowerCharPiece q m x r) :
    IsSigmaCharacter q m ι x (identityTuple m) (Sweep.dminusCM q (m + 1) G) := by
  have hmem : Sweep.dminusCM q (m + 1) G ∈ Sweep.piece K m := Sweep.dminusCM_mem_piece q m hG
  have hkey : Sym.insertFront K m (ι (Sweep.theta q (Sweep.dminusCM q (m + 1) G))) =
      Sym.insertFront K m
        ((q - 1) ^ (N - m) • partialCharSeries q m x (identityTuple m)) := by
    rw [Sym.insertFront_smul, hsum, insertFront_partialCharSeries_identityTuple q hx]
  exact Sym.injOn_insertFront K m
    (boundedFrontDegree_apply_of_mem_piece hι (Sweep.theta_mem_piece q le_rfl hmem))
    (boundedFrontDegree_smul _ (boundedFrontDegree_partialCharSeries q m x _)) hkey

/-! ### The word of a partial Dyck path computes a character -/

/-- **The word of a partial Dyck path computes a character, granted the lowering sum**
(unconditionally, `HJO.Dyck.mem_piece_and_isSigmaCharacter_partialWordOp'`). For
`π ∈ 𝔻_{k,N}` with step word `w_k(π) = ε₁ ⋯ ε_M`, `M = 2N - k`, the composite
`d_{ε₁}(d_{ε₂}(⋯ d_{ε_M}(1)⋯))` of `HJO.Sweep.partialWordOp`, applied to `1 ∈ V_0`, lies in `V_k`
and is an `Id_k`-character of `π`.

The statement as usually given asserts the *existence* of such a `G`; the composite is written down
instead, which is stronger and is what `HJO.Dyck.realisation_constantCoeff_markedWordOp` reads. Its
intermediate values lie in the pieces the successive operators demand — that is the first conjunct,
at every level of the induction — and the levels the factors are read at are the ones
`HJO.Sweep.partialWordOp` prescribes.

The proof is the induction on `M = 2N - k`. The base `M = 0` forces `N = k = 0`, where
the word is empty and `1` is a character by `HJO.Dyck.isSigmaCharacter_one_of_isEmpty`. The step
splits by `HJO.Dyck.IsSquareDyck.xor_exists_apply_eq_zero_level_pos`: at a north step
`HJO.Dyck.isPartialDyck_succ_iff` raises the level of the same path,
`HJO.Dyck.partialStepWord_eq_U_cons_partialStepWord_succ` strips the leading `-` from the word, and
`HJO.Dyck.isSigmaCharacter_dminusCM` lowers the character (this is where `hsum` is spent, at the
level `k + 1` of the same path); at an east step `HJO.Dyck.isPartialDyck_eastInverse` shortens the
path, `HJO.Dyck.partialStepWord_succ_eq_D_cons_partialStepWord_eastInverse` strips the leading `+`,
`HJO.Dyck.isSigmaCharacter_cmDPlus` raises the character of `D_k(π)` and
`HJO.Dyck.prependEast_eastInverse` identifies `E_{k-1}(D_k(π))` with `π`. The memberships are
`HJO.Sweep.dminusCM_mem_piece` and `HJO.Sweep.cmDPlus_mem_piece`.

The family `ι` of realisations is indexed by the level because the induction changes level at every
step; `HJO.Dyck.auxRealise` with `HJO.Dyck.isAuxRealisation_auxRealise` is one such family, so no
hypothesis here is vacuous. The hypothesis `q ≠ 0` is `HJO.Dyck.isSigmaCharacter_cmDPlus`'s, whose
statement needs it. The result is conditional on `hsum`. -/
theorem mem_piece_and_isSigmaCharacter_partialWordOp {q : K} (hq : q ≠ 0)
    (hsum : IsLoweringSum q) (ι : ∀ l : ℕ, Sweep.Total K →ₐ[K] Sym.AuxAlphabetSeries K l)
    (hι : ∀ l : ℕ, IsAuxRealisation l (ι l)) {k N : ℕ} {x : Fin N → ℕ}
    (hx : IsPartialDyck k N x) :
    Sweep.partialWordOp q k (partialStepWord k x) 1 ∈ Sweep.piece K k ∧
      IsSigmaCharacter q k (ι k) x (identityTuple k)
        (Sweep.partialWordOp q k (partialStepWord k x) 1) := by
  suffices h : ∀ M k N : ℕ, ∀ x : Fin N → ℕ, 2 * N - k = M → IsPartialDyck k N x →
      Sweep.partialWordOp q k (partialStepWord k x) 1 ∈ Sweep.piece K k ∧
        IsSigmaCharacter q k (ι k) x (identityTuple k)
          (Sweep.partialWordOp q k (partialStepWord k x) 1) from
    h (2 * N - k) k N x rfl hx
  intro M
  induction M with
  | zero =>
    intro k N x hM hx
    have hkN : k ≤ N := hx.le_length
    have hN : N = 0 := by omega
    subst hN
    have hk : k = 0 := by omega
    subst hk
    have hw : partialStepWord 0 x = [] := by
      have hlen : (partialStepWord 0 x).length = 0 := by rw [length_partialStepWord]
      exact List.eq_nil_of_length_eq_zero hlen
    rw [hw, Sweep.partialWordOp_nil, Module.End.one_apply]
    exact isSigmaCharacter_one_of_isEmpty q (ι 0) x (identityTuple 0)
  | succ M ih =>
    intro k N x hM hx
    have hkN : k ≤ N := hx.le_length
    have hN : 0 < N := by omega
    rcases hx.toIsSquareDyck.xor_exists_apply_eq_zero_level_pos (k := k) hN with
      ⟨⟨hkn, hx0⟩, -⟩ | ⟨⟨hkpos, hxpos⟩, -⟩
    · -- The first case: the next step is north, so the level rises and the path is unchanged.
      have hx1 : IsPartialDyck (k + 1) N x := (isPartialDyck_succ_iff hkn).2 ⟨hx, hx0⟩
      obtain ⟨hmem, hchar⟩ := ih (k + 1) N x (by omega) hx1
      rw [partialStepWord_eq_U_cons_partialStepWord_succ hkn hx0, Sweep.partialWordOp_U_cons,
        Module.End.mul_apply]
      refine ⟨Sweep.dminusCM_mem_piece q k hmem, ?_⟩
      exact isSigmaCharacter_dminusCM q hx1 (hι k) hmem
        (hsum k N x hx1 (ι k) (hι k) (ι (k + 1)) (hι (k + 1)) _ hmem hchar)
    · -- The second case: the first step is east, so the level and the length both drop.
      obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
      obtain ⟨n, rfl⟩ : ∃ n, N = n + 1 := ⟨N - 1, by omega⟩
      have hk'n : k' ≤ n := by omega
      have hpos : ∀ j : Fin (n + 1), k' + 1 ≤ (j : ℕ) → 0 < x j := by
        intro j hj
        have hjn : (j : ℕ) ≤ n := by omega
        have hkn : k' + 1 < n + 1 := by omega
        have h0 : 0 < x ⟨k' + 1, hkn⟩ := hxpos hkn
        have hle : x ⟨k' + 1, hkn⟩ ≤ x j :=
          hx.toIsSquareDyck.mono (show (⟨k' + 1, hkn⟩ : Fin (n + 1)) ≤ j from Fin.le_def.2 hj)
        omega
      have hlow : ∀ p : Fin (n + 1), (p : ℕ) < k' + 1 → x p = 0 :=
        fun p hp => hx.eq_zero_of_lt_level p hp
      have hx' : IsPartialDyck k' n (eastInverse (k' + 1) x) :=
        isPartialDyck_eastInverse hx.toIsSquareDyck hk'n
      obtain ⟨hmem, hchar⟩ := ih k' n (eastInverse (k' + 1) x) (by omega) hx'
      rw [partialStepWord_succ_eq_D_cons_partialStepWord_eastInverse hk'n hpos,
        Sweep.partialWordOp_D_cons_succ, Module.End.mul_apply]
      refine ⟨Sweep.cmDPlus_mem_piece q k' hmem, ?_⟩
      have hraise := isSigmaCharacter_cmDPlus q hq hx' (hι k') (hι (k' + 1)) hmem hchar
      rwa [prependEast_eastInverse hlow hpos] at hraise

/-! ### Theorem 4.4 -/

/-- **Carlsson and Mellit's Theorem 4.4, granted the lowering sum** (unconditionally,
`HJO.Dyck.realisation_constantCoeff_markedWordOp'`). For a square Dyck path `π` of length `n` with
step word `w(π) = ε₁ ⋯ ε_{2n}` and a realisation `ι`,

`ι(d_{ε₁} ∘ d_{ε₂} ∘ ⋯ ∘ d_{ε_{2n}}(1)) = χ(π)`,

the operators being applied to `1 ∈ V_0 = Λ` from the right.

The composite is `HJO.Sweep.markedWordOp q x ∅`, the word `Ξ_{π,T}` of `HJO.Sweep.markedWordOp` at
`T = ∅`, which by `HJO.Sweep.markedFactor_empty` is exactly the word
`d_{ε₁} ∘ ⋯ ∘ d_{ε_{2n}}` — every position contributing its own letter, read at the level
`HJO.Dyck.wordLevel x s` of the piece it acts on. So this statement is the `T = ∅` case of
`HJO.Mellit.map_constantCoeff_markedWordOp'` rather than a second reading of the word. The value
lands in `V_0`, which is `Λ` read as the constants, and is taken out of it by
`MvPolynomial.constantCoeff`; the right-hand side `HJO.Dyck.pathMarkedCharSeries q x ∅` is
`HJO.Dyck.pathCharSeries`'s `χ(π)`.

The proof is the three lines. `π` lies in `𝔻_{0,n}`, no condition being imposed at level
`0`; `HJO.Dyck.partialStepWord_zero_left` identifies `w(π)` with `w_0(π)`, and
`HJO.Sweep.partialWordOp_zero_stepWord` identifies the two readings of the composite; so
`HJO.Dyck.mem_piece_and_isSigmaCharacter_partialWordOp` at `k = 0` produces an `Id_0`-character of
`π` in `V_0`, and `HJO.Dyck.auxZeroMap_eq_pathCharSeries_of_isSigmaCharacter` turns it into `χ(π)`.
The given realisation is read as a realisation with no auxiliary variables by
`HJO.Dyck.toAuxRealisationZero`, whose round trip
`HJO.Dyck.ofAuxRealisationZero_toAuxRealisationZero` is what makes the `ι` of the conclusion the `ι`
of the hypothesis.

Three hypotheses the statement does not carry: `q ≠ 0` from `HJO.Dyck.isSigmaCharacter_cmDPlus`,
whose statement needs it; `∀ r, IsUnit (q^{r+1} - 1)` from
`HJO.Dyck.auxZeroMap_eq_pathCharSeries_of_isSigmaCharacter`, through the bijectivity of `θ`; and
`CharZero`, also from `HJO.Dyck.auxZeroMap_eq_pathCharSeries_of_isSigmaCharacter`. The `n ≥ 1` is
dropped, nothing here reading it. The result is conditional on `hsum`, the lowering-sum hypothesis
`HJO.Dyck.IsLoweringSum`, which `HJO.Dyck.isLoweringSum` proves. -/
theorem realisation_constantCoeff_markedWordOp [CharZero K] (q : K) (hq0 : q ≠ 0)
    (hq : ∀ r : ℕ, IsUnit (q ^ (r + 1) - 1)) {n : ℕ} {x : Fin n → ℕ} (hx : IsSquareDyck n x)
    {ι : Sym.Lambda K →ₐ[K] Sym.AlphabetSeries K} (hι : Sym.IsRealisation ι)
    (hsum : IsLoweringSum q) :
    ι (MvPolynomial.constantCoeff (Sweep.markedWordOp q x ∅ 1)) = pathMarkedCharSeries q x ∅ := by
  have hι₀ : IsAuxRealisation 0 (toAuxRealisationZero ι) :=
    isAuxRealisation_toAuxRealisationZero hι
  have hp : IsPartialDyck 0 n x := ⟨hx, Nat.zero_le n, fun l hl => absurd hl (Nat.not_lt_zero _)⟩
  obtain ⟨hmem, hcharacter⟩ := mem_piece_and_isSigmaCharacter_partialWordOp hq0 hsum
    (auxFamily (toAuxRealisationZero ι)) (isAuxRealisation_auxFamily hι₀) hp
  rw [partialStepWord_zero_left, Sweep.partialWordOp_zero_stepWord q hx] at hmem hcharacter
  obtain ⟨g, hg⟩ := exists_C_eq_of_mem_piece_zero hmem
  have hzero := auxZeroMap_eq_pathCharSeries_of_isSigmaCharacter hι₀ hq hx hmem
    (identityTuple 0) hcharacter
  rw [← hg, auxZeroMap_apply_C, ofAuxRealisationZero_toAuxRealisationZero] at hzero
  rw [← hg]
  simpa using hzero

end Lowering

end HJO.Dyck
