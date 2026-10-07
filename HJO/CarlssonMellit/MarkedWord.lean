/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.CarlssonMellit.SquareDyck
public import HJO.CarlssonMellit.SweepCM
public import HJO.Shuffle.CMRaising
public meta import HJO.Attr

/-! # The word of a marked Dyck path

One definition, `HJO.Sweep.markedWordOp`: the operator `Ξ_{π,T}` attached to a Dyck path `π` of
length `n` and a marking `T ⊆ c(π)` of its corners. The positions `1, …, 2n` of the step word
`w(π) = ε_1 ⋯ ε_{2n}` are partitioned into the pairs `{r_j - 1, r_j}`, one for each marked corner
`(x_j - 1, j) ∈ T` with `r_j = x_j + j - 1`, together with the remaining positions taken singly;
`Ξ_{π,T}` is the composite of the factors of the blocks, the block of largest positions acting
first, a singleton `{r}` contributing `d_{ε_r}` and a pair contributing
`(d_-d_+ - d_+d_-)/(q - 1)`.

## The shape, and what forces it

`d_+` carries `V_k` to `V_{k+1}` and `d_-` carries `V_k` to `V_{k-1}`, so every factor is read at a
*level*, and the composite is only meaningful once each position is given the level its factor acts
on. That level is determined by the word: the factors to the right of a position have already
acted, so the input level at the `0`-based position `s` is the number of north steps at positions
`≤ s` less the number of east steps there, which is `HJO.Dyck.wordLevel`.

`Ξ_{π,T}` is therefore written as an ordered product over the `2n` positions rather than over the
blocks of the partition: a marked corner contributes its commutator factor `HJO.Sweep.cmCorner` at
the position `r_j` of its north step and the identity at the position `r_j - 1` below it. The two
readings agree because the pair factor preserves the level, exactly as the two letters it replaces
do together — so the levels of every other position are untouched — and because the block sits, in
the ordering, where its largest position sits. `List.prod` of `List.ofFn` over the ascending
positions is the order: `a₀ * a₁ * ⋯` applied to a vector evaluates the last factor
first.

## Main definitions

* `HJO.Dyck.northCount`, `HJO.Dyck.wordLevel`: the number of north steps at positions `≤ s`, and
  the level at which the factor of position `s` acts.
* `HJO.Dyck.IsMarkedNorth`: `s` is the position of the north step of a marked corner.
* `HJO.Sweep.stepOp`: the factor of a singleton, `d_-` at a north step and `d_+` at an east step.
* `HJO.Sweep.cmCorner`: the factor of a pair, `(d_-d_+ - d_+d_-)/(q - 1)` with Carlsson and Mellit's
  own `d_±`.
* `HJO.Sweep.markedFactor`, `HJO.Sweep.markedWordOp`: the factor of one position, and `Ξ_{π,T}`.

## Main results

These are the well-definedness clauses of the definition, and the evidence that the levels are
the right ones.

* `HJO.Dyck.IsSquareDyck.succ_le_two_mul_northCount` and
  `HJO.Dyck.IsSquareDyck.wordLevel_add`: the truncated subtraction in `wordLevel` never bites on a
  path — the level is the honest difference of the two counts.
* `HJO.Dyck.IsSquareDyck.wordLevel_two_mul_sub_one`: the level at the last position is `0`, so the
  first factor to act reads `V_0`, where `1` lives.
* `HJO.Dyck.getElem_stepWord_isMarkedNorth` and
  `HJO.Dyck.IsSquareDyck.getElem_stepWord_isMarkedNorth_pred`: at a marked corner the letters are
  `ε_r = -` and `ε_{r-1} = +`, so the pair really does replace `d_+d_-`.
* `HJO.Dyck.IsSquareDyck.not_isMarkedNorth_succ`: the blocks are disjoint — no position is both the
  north step of a marked corner and the position below one — so the two branches of
  `markedFactor` are mutually exclusive and the order in which they are tested is immaterial.
* `HJO.Sweep.markedWordOp_one_zero`: `Ξ = d_- d_+` at the unique path of length `1`, and
  `HJO.Sweep.markedWordOp_one_zero_apply_one`: its value on `1` is `e_1 = p_1`, which is `χ(π)` for
  that path.

## Implementation notes

*Disjointness needs a gap of two.* That the `r_j` of distinct marked corners differ "by at least
`1`" would not suffice, as it would leave `{r-1, r}` and `{r, r+1}` overlapping. What holds, and
what `IsSquareDyck.not_isMarkedNorth_succ` proves, is that they differ by at least `2`: for corners
`j < j'` with `j' > j + 1` strict monotonicity of `j ↦ x_j + j` already gives `2`, and for
`j' = j + 1` the corner condition `x_j < x_{j+1}` gives the second unit.

*The level is a natural number and `wordLevel` subtracts.* It must be: `HJO.Sweep.cmDPlus` and
`HJO.Sweep.dminusCM` are indexed by a natural level, as are the pieces `V_k`. The truncation is
harmless and not merely asserted to be: `IsSquareDyck.wordLevel_add` proves the subtraction exact at
every position of a path.

*`cmCorner` is not `HJO.Sweep.corner`.* The latter is the same commutator built from the *sweep*
operators `d^♭_-` and the sign-carrying `d_+` of `HJO.Sweep.dminus` and `HJO.Sweep.dplus`. Carlsson
and Mellit's recipe is written in their own operators, which are `HJO.Sweep.cmDPlus` and
`HJO.Sweep.dminusCM`, so the factor here is built from `HJO.Sweep.cmDPlus` and
`HJO.Sweep.dminusCM`. The two are not equal; `HJO.Sweep.dplus_eq_neg_cmDPlus` and
`HJO.Sweep.dminusCM_eq_neg_dminus_auxVar_mul` are the bridges between the operators, and no bridge
between the two corner operators is claimed here.

*No hypothesis is imposed on `x` or on `T`.* A definition may not presuppose the lemmas about it;
being a square Dyck path and `T ⊆ c(π)` are hypotheses of the results above and of
`HJO.Mellit.map_constantCoeff_markedWordOp'`. Off that range the level is the junk value of a
truncated subtraction, and `IsMarkedNorth` is vacuous as soon as `T` meets no corner cell.

*The count of factors is not stated.* The partition into blocks has `2n - #T` blocks; here every
position carries a factor and `#T` of them are the identity, so that count is about the partition
rather than about this product, and its content — that the marked corners occupy
`2#T` distinct positions — is `IsSquareDyck.not_isMarkedNorth_succ` together with the injectivity of
`j ↦ x_j + j`.

## References

E. Carlsson and A. Mellit, *A proof of the shuffle conjecture*, Corollary 4.6, whose recipe is
`[d_-, d_+]/(q-1)` at each corner, and A. Mellit's Theorem 3.7 for a general marking. Consumed by
`HJO.Mellit.map_constantCoeff_markedWordOp'`, `ι(Ξ_{π,T}(1)) = χ(π, T)`, and through it by
`HJO.Mellit.constantCoeff_psiWord_one_mem_lambdaComp_and_map_eq_sweepChar`. -/

@[expose] public section

open Finset List DyckStep

namespace HJO.Dyck

/-! ### The level at a position of the step word -/

/-- The number of north steps of the step word of `x` at positions `≤ s`: the positions carrying a
north step are the `x k + k` by `HJO.Dyck.getElem_stepWord_eq_U_iff`, so this counts the rows `k`
with `x k + k ≤ s`. -/
def northCount {n : ℕ} (x : Fin n → ℕ) (s : ℕ) : ℕ := #{k : Fin n | x k + (k : ℕ) ≤ s}

/-- The level at which the factor of position `s` acts: the number of north steps at positions
`≤ s` less the number of east steps there, the latter being `s + 1` less the former. Reading the
composite from the right, each east step raises the level by one and each north step lowers it, so
this is the level of the piece `V_k` the factor of position `s` is applied to.

The subtraction is truncated; `IsSquareDyck.wordLevel_add` shows it is exact at every position of a
square Dyck path, and `IsSquareDyck.wordLevel_two_mul_sub_one` that the level at the last position
is `0`. -/
def wordLevel {n : ℕ} (x : Fin n → ℕ) (s : ℕ) : ℕ := 2 * northCount x s - (s + 1)

/-- At most every row contributes a north step at positions `≤ s`. -/
theorem northCount_le {n : ℕ} (x : Fin n → ℕ) (s : ℕ) : northCount x s ≤ n := by
  rw [northCount]
  calc #{k : Fin n | x k + (k : ℕ) ≤ s} ≤ #(univ : Finset (Fin n)) :=
        Finset.card_filter_le _ _
    _ = n := by rw [card_univ, Fintype.card_fin]

/-- **The truncated subtraction in `wordLevel` never bites**: at every position of the step word of
a square Dyck path there are at least as many north steps as east steps among the positions `≤ s`.
The reason is the diagonal bound `x_j ≤ j`: with `u` north steps at positions `≤ s`, either `u = n`
and `s < 2n = 2u`, or some row `k ≤ u` has its north step beyond `s`, and then
`s < x k + k ≤ 2u`. -/
theorem IsSquareDyck.succ_le_two_mul_northCount {n : ℕ} {x : Fin n → ℕ} (h : IsSquareDyck n x)
    {s : ℕ} (hs : s < 2 * n) : s + 1 ≤ 2 * northCount x s := by
  have hun := northCount_le x s
  rcases le_or_gt n (northCount x s) with hn | hn
  · omega
  have hex : ∃ k : Fin n, (k : ℕ) ≤ northCount x s ∧ s < x k + (k : ℕ) := by
    by_contra hc
    have hall : ∀ k : Fin n, (k : ℕ) ≤ northCount x s → x k + (k : ℕ) ≤ s := fun k hk => by
      by_contra hc2
      exact hc ⟨k, hk, by omega⟩
    have h2 : #(Finset.range (northCount x s + 1)) ≤
        #(Finset.image (fun k : Fin n => (k : ℕ)) {k : Fin n | x k + (k : ℕ) ≤ s}) := by
      refine Finset.card_le_card fun i hi => ?_
      rw [Finset.mem_range] at hi
      have hin : i < n := by omega
      exact Finset.mem_image.2
        ⟨⟨i, hin⟩, (mem_filter_univ _).2 (hall ⟨i, hin⟩ (Nat.le_of_lt_succ hi)), rfl⟩
    have h3 : #(Finset.image (fun k : Fin n => (k : ℕ)) {k : Fin n | x k + (k : ℕ) ≤ s})
        ≤ northCount x s := Finset.card_image_le
    rw [Finset.card_range] at h2
    omega
  obtain ⟨k, hk1, hk2⟩ := hex
  have := h.le_index k
  omega

/-- **The level is the honest difference of the two counts**: `wordLevel` plus the number of
positions `≤ s` is twice the number of north steps there. This is `succ_le_two_mul_northCount`
restated as the exactness of the subtraction. -/
theorem IsSquareDyck.wordLevel_add {n : ℕ} {x : Fin n → ℕ} (h : IsSquareDyck n x) {s : ℕ}
    (hs : s < 2 * n) : wordLevel x s + (s + 1) = 2 * northCount x s := by
  have := h.succ_le_two_mul_northCount hs
  rw [wordLevel]
  omega

/-- Every row of a square Dyck path has its north step at a position below the last one, so all `n`
of them are counted at `s = 2n - 1`. -/
theorem IsSquareDyck.northCount_two_mul_sub_one {n : ℕ} {x : Fin n → ℕ} (h : IsSquareDyck n x) :
    northCount x (2 * n - 1) = n := by
  have hall : ∀ k ∈ (univ : Finset (Fin n)), x k + (k : ℕ) ≤ 2 * n - 1 := fun k _ => by
    have := h.add_index_add_one_lt_two_mul k
    omega
  rw [northCount, Finset.filter_true_of_mem hall, card_univ, Fintype.card_fin]

/-- **The first factor to act reads `V_0`**: the level at the last position of the step word of a
square Dyck path is `0`, which is where the unit `1` of `Λ = V_0` lives. -/
theorem IsSquareDyck.wordLevel_two_mul_sub_one {n : ℕ} {x : Fin n → ℕ} (h : IsSquareDyck n x)
    (hn : 0 < n) : wordLevel x (2 * n - 1) = 0 := by
  rw [wordLevel, h.northCount_two_mul_sub_one]
  omega

/-! ### The marked positions -/

/-- `s` is the position of the north step of a corner of `x` marked by `T`: the `r_j = x_j + j - 1`
of the module docstring for a corner `(x_j - 1, j) ∈ T`, on positions indexed from `0`. The pair of
the partition belonging to that corner is `{s - 1, s}`. -/
def IsMarkedNorth {n : ℕ} (x : Fin n → ℕ) (T : Finset (ℕ × ℕ)) (s : ℕ) : Prop :=
  ∃ k : Fin n, IsCornerIndex x k ∧ (x k - 1, (k : ℕ)) ∈ T ∧ x k + (k : ℕ) = s

instance instDecidableIsMarkedNorth {n : ℕ} (x : Fin n → ℕ) (T : Finset (ℕ × ℕ)) (s : ℕ) :
    Decidable (IsMarkedNorth x T s) := by
  unfold IsMarkedNorth; infer_instance

/-- With no corner marked there is no marked position: at `T = ∅` the partition is into singletons
and `Ξ_{π,∅}` is the plain word of the path. -/
@[simp]
theorem isMarkedNorth_empty {n : ℕ} (x : Fin n → ℕ) (s : ℕ) : ¬IsMarkedNorth x ∅ s := by
  rintro ⟨k, -, hk, -⟩
  exact absurd hk (notMem_empty _)

/-- A marked position is positive, so the pair `{s - 1, s}` lies inside the word: a corner has
`0 < x_j` and `0 < j`, which read `x_j ≥ 2` and `j ≥ 2` when positions are counted from `1`. -/
theorem IsMarkedNorth.pos {n : ℕ} {x : Fin n → ℕ} {T : Finset (ℕ × ℕ)} {s : ℕ}
    (h : IsMarkedNorth x T s) : 0 < s := by
  obtain ⟨k, hk, -, hs⟩ := h
  have := hk.pos
  omega

/-- **No north step sits just below the north step of a corner**: the argument that
`ε_{r-1} = +`. Were `x_{j'} + j'` one less than `x_j + j`, strict monotonicity of `j ↦ x_j + j`
would force `j' = j - 1`, and then `x_{j-1} = x_j`, which the corner condition excludes. -/
theorem IsSquareDyck.northPos_pred_ne {n : ℕ} {x : Fin n → ℕ} (h : IsSquareDyck n x) {k : Fin n}
    (hk : IsCornerIndex x k) (k' : Fin n) : x k' + (k' : ℕ) + 1 ≠ x k + (k : ℕ) := by
  obtain ⟨l, hl, hlt⟩ := hk
  intro hc
  rcases le_or_gt (k' : ℕ) (l : ℕ) with hle | hgt
  · have := h.mono (show k' ≤ l from Fin.le_def.2 hle)
    omega
  · have := h.mono (show k ≤ k' from Fin.le_def.2 (by omega))
    omega

/-- **At a marked corner the letter is a north step**, `ε_r = -`. -/
theorem getElem_stepWord_isMarkedNorth {n : ℕ} {x : Fin n → ℕ} {T : Finset (ℕ × ℕ)} {s : ℕ}
    (hs : s < (stepWord x).length) (h : IsMarkedNorth x T s) : (stepWord x)[s] = DyckStep.U := by
  obtain ⟨k, -, -, hk⟩ := h
  exact (getElem_stepWord_eq_U_iff x s hs).2 ⟨k, hk⟩

/-- **Just below a marked corner the letter is an east step**, `ε_{r-1} = +`. -/
theorem IsSquareDyck.getElem_stepWord_isMarkedNorth_pred {n : ℕ} {x : Fin n → ℕ}
    (h : IsSquareDyck n x) {T : Finset (ℕ × ℕ)} {s : ℕ} (hs : s - 1 < (stepWord x).length)
    (hm : IsMarkedNorth x T s) : (stepWord x)[s - 1] = DyckStep.D := by
  have hpos := hm.pos
  obtain ⟨k, hk, -, hks⟩ := hm
  refine (getElem_stepWord_eq_D_iff x (s - 1) hs).2 fun k' hk' => ?_
  exact h.northPos_pred_ne hk k' (by omega)

/-- **The blocks of the partition are disjoint**: a position that is the north step of a marked
corner is not the position just below the north step of another. The `r_j` of distinct corners
differ by at least `2`, which is what makes `{r_j - 1, r_j}` pairwise disjoint — and, here, what
makes the two branches of `HJO.Sweep.markedFactor` mutually exclusive. -/
theorem IsSquareDyck.not_isMarkedNorth_succ {n : ℕ} {x : Fin n → ℕ} (h : IsSquareDyck n x)
    {T : Finset (ℕ × ℕ)} {s : ℕ} (hm : IsMarkedNorth x T s) : ¬IsMarkedNorth x T (s + 1) := by
  rintro ⟨k', hk', -, hks'⟩
  obtain ⟨k, -, -, hks⟩ := hm
  exact h.northPos_pred_ne hk' k (by omega)

end HJO.Dyck

namespace HJO.Sweep

open Dyck

variable {L : Type*} [Field L] [Algebra ℚ L]

/-! ### The factors -/

/-- The factor of a singleton block `{r}` of the partition: `d_{ε_r}`, read at the level `k` its
input lies in. A north step contributes Carlsson and Mellit's lowering operator `d_-` of
`HJO.Sweep.dminusCM`, which carries `V_k` to `V_{k-1}`; an east step contributes the raising
operator `d_+` of `HJO.Sweep.cmDPlus`, which carries `V_k` to `V_{k+1}`. -/
noncomputable def stepOp (q : L) (e : DyckStep) (k : ℕ) : Module.End L (Total L) :=
  match e with
  | .U => dminusCM q k
  | .D => cmDPlus q k

@[simp]
theorem stepOp_U (q : L) (k : ℕ) : stepOp q DyckStep.U k = dminusCM q k := rfl

@[simp]
theorem stepOp_D (q : L) (k : ℕ) : stepOp q DyckStep.D k = cmDPlus q k := rfl

/-- The factor of a pair block of the partition: `(d_-d_+ - d_+d_-)/(q - 1)` on `V_k`, built from
Carlsson and Mellit's own operators. The indices record which piece each factor is read on: `d_-d_+`
is `d_-` of index `k+1` after `d_+` of index `k`, and `d_+d_-` is `d_+` of index `k-1` after `d_-`
of index `k`, so both composites carry `V_k` to itself.

This is Carlsson and Mellit's printed recipe `[d_-, d_+]/(q-1)`. It is *not*
`HJO.Sweep.corner`, which is the same commutator in the operators of `HJO.Sweep.dminus` and
`HJO.Sweep.dplus`. -/
noncomputable def cmCorner (q : L) (k : ℕ) : Module.End L (Total L) :=
  (q - 1)⁻¹ • (dminusCM q (k + 1) * cmDPlus q k - cmDPlus q (k - 1) * dminusCM q k)

/-- The factor of the position `s` of the step word of `x`, marked by `T`: the pair factor at the
north step of a marked corner, the identity at the position just below it — the pair having already
contributed there — and the letter's own operator otherwise, each read at the level
`HJO.Dyck.wordLevel x s`.

The first two cases do not overlap, by `HJO.Dyck.IsSquareDyck.not_isMarkedNorth_succ`, so the order
in which they are tested is immaterial on a path. -/
noncomputable def markedFactor (q : L) {n : ℕ} (x : Fin n → ℕ) (T : Finset (ℕ × ℕ)) (s : ℕ) :
    Module.End L (Total L) :=
  if IsMarkedNorth x T s then cmCorner q (wordLevel x s)
  else if IsMarkedNorth x T (s + 1) then 1
  else stepOp q ((stepWord x).getD s DyckStep.D) (wordLevel x s)

/-- With nothing marked, every position contributes its own letter. -/
@[simp]
theorem markedFactor_empty (q : L) {n : ℕ} (x : Fin n → ℕ) (s : ℕ) :
    markedFactor q x ∅ s = stepOp q ((stepWord x).getD s DyckStep.D) (wordLevel x s) := by
  simp only [markedFactor, isMarkedNorth_empty, ite_false]

/-! ### The word of a marked Dyck path -/

/-- **The word `Ξ_{π,T}` of the marked Dyck path `(π, T)`**, where `π` has
coarea sequence `x` and `T` is a set of its corners: the ordered composite, over the `2n` positions
of the step word, of the factor of each position, the largest position acting first.

A marked corner is a *pair* block `{r_j - 1, r_j}` of the partition and contributes the
one factor `HJO.Sweep.cmCorner`, placed at the position `r_j` of its north step, the position below
carrying the identity; every other position is a singleton block and contributes `d_{ε_r}`. Each
factor is read at the level `HJO.Dyck.wordLevel x s` of the piece it acts on, which is what makes
the composite meaningful: `d_+` raises the level and `d_-` lowers it, while a pair preserves it, as
do the two letters it replaces. -/
@[hjo "def_cm_marked_word"]
noncomputable def markedWordOp (q : L) {n : ℕ} (x : Fin n → ℕ) (T : Finset (ℕ × ℕ)) :
    Module.End L (Total L) :=
  (List.ofFn fun s : Fin (2 * n) => markedFactor q x T (s : ℕ)).prod

/-- **The word of a marked Dyck path as a list of factors**, the form in which the composite is
read: `Ξ_{π,T} = F_0 ⋯ F_{2n-1}` with `F_s` the factor of position `s`, so that `F_{2n-1}` is
applied first. -/
theorem markedWordOp_eq_prod (q : L) {n : ℕ} (x : Fin n → ℕ) (T : Finset (ℕ × ℕ)) :
    markedWordOp q x T = (List.ofFn fun s : Fin (2 * n) => markedFactor q x T (s : ℕ)).prod :=
  rfl

/-- **The unique path of length `1` gives `Ξ = d_- d_+`**: its step word is a north step followed by
an east step, so, the largest position acting first, `d_+` reads `V_0` and `d_-` reads `V_1`. This
pins the order of the composite and the levels together. -/
theorem markedWordOp_one_zero (q : L) :
    markedWordOp q (0 : Fin 1 → ℕ) ∅ = dminusCM q 1 * cmDPlus q 0 := by
  have hword : stepWord (0 : Fin 1 → ℕ) = [DyckStep.U, DyckStep.D] := by decide
  have h0 : wordLevel (0 : Fin 1 → ℕ) 0 = 1 := by decide
  have h1 : wordLevel (0 : Fin 1 → ℕ) 1 = 0 := by decide
  rw [markedWordOp]
  simp [List.ofFn_succ, markedFactor_empty, hword, h0, h1]

/-- **The value of `Ξ` on `1` at the path of length `1`** is `e_1 = p_1`, which is `χ(π)` for that
path: the single labelling of one row has no inversions, so `χ(π) = ∑_i x_i`. So the composite is
not degenerate, and the levels are not off by one — at any other pair of levels the value would be
different. -/
theorem markedWordOp_one_zero_apply_one (q : L) :
    markedWordOp q (0 : Fin 1 → ℕ) ∅ (1 : Total L) = MvPolynomial.C (Sym.elemSymm L 1) := by
  rw [markedWordOp_one_zero]
  simpa [cmDPlus_zero] using dminusCM_one q 0

end HJO.Sweep
