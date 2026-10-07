/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.CarlssonMellit.CornerInclusion
public import HJO.CarlssonMellit.MarkedWord
public meta import HJO.Attr

/-! # A marked Dyck path as a word in the operators

The identity of `HJO.Mellit.map_constantCoeff_markedWordOp'`: for a square Dyck path `π` of length
`n`, a marking `T ⊆ c(π)` of its corners and a realisation `ι`,

`ι(Ξ_{π,T}(1)) = χ(π, T)`,

where `Ξ_{π,T}` is `HJO.Sweep.markedWordOp` and `χ(π, T)` is `HJO.Dyck.pathMarkedCharSeries`.

## What is proved here, and what is assumed

The proof is an inclusion--exclusion over the flips of the marking on top of the *unmarked*
statement `HJO.Dyck.realisation_constantCoeff_markedWordOp'`, which is proved only later, in
`HJO/CarlssonMellit/LoweringSumClosed.lean`. That unmarked statement is exactly this identity at
`T = ∅` — by `HJO.Sweep.markedFactor_empty` the operator `Ξ_{π,∅}` is the plain word
`d_{ε_1} ⋯ d_{ε_{2n}}` of the path — so it is carried here as the hypothesis `hthm44`, quantified
over the paths it is applied to, namely the `2 ^ #T` flips `π_S`. The later file discharges it and
states `HJO.Mellit.map_constantCoeff_markedWordOp'` without it.

Everything else is proved. The arithmetical half, the identity
`(1 - q)^{#T} χ(π, T) = ∑_{S ⊆ T} (-1)^{#S} χ(π_S)`, is
`HJO.Dyck.pathMarkedCharSeries_inclusion_exclusion`; the operator half is
`HJO.Sweep.sum_powerset_smul_markedWordOp_flipCorners`, proved here and mentioning no realisation at
all:

`∑_{S ⊆ T} (-1)^{#S} Ξ_{π_S,∅} = (1 - q)^{#T} Ξ_{π,T}`.

## Main results

* `HJO.Sweep.sum_powerset_smul_markedWordOp_flipCorners`: the operator identity above.
* `HJO.Sweep.map_constantCoeff_markedWordOp_one_eq_pathMarkedCharSeries`: the identity, modulo
  `hthm44`.
* `HJO.Dyck.getD_stepWord_flipCorners_of_isMarkedNorth_succ`,
  `HJO.Dyck.IsSquareDyck.getD_stepWord_flipCorners_of_isMarkedNorth` and
  `HJO.Dyck.getD_stepWord_flipCorners_of_not`: flipping a corner exchanges the two letters at the
  positions `r - 1` and `r` of its north step and changes no other letter.
* `HJO.Dyck.IsSquareDyck.wordLevel_flipCorners_pred` and
  `HJO.Dyck.wordLevel_flipCorners_of_not_isMarkedNorth`: what the exchange does to the levels the
  factors are read at — the level at `r` is unchanged, and the level at `r - 1` goes up by two.
* `HJO.Sweep.cmCorner_one_eq_zero` and `HJO.Sweep.markedWordOp_one_eq_zero_of_nonempty`: at `q = 1`
  the word of a marked path is the zero operator, which is half of the counterexample to the
  identity without the hypothesis `q ≠ 1` — see the implementation notes.

## The shape of the operator identity

Both sides are products over the `2n` positions of the step word, and they group those positions
differently: a marked corner contributes *one* factor at the position `r` of its north step on the
right, and *two* letters, at `r - 1` and `r`, on the left. So the proof factors through two facts
that have nothing to do with Dyck paths.

* `HJO.Sweep.prod_range_map_cluster` moves each pair of adjacent letters into the upper position of
  the pair, leaving the identity below it. Its hypotheses are that a marked position is positive and
  that no two marked positions are adjacent, which for a path is
  `HJO.Dyck.IsSquareDyck.not_isMarkedNorth_succ`.
* `HJO.Sweep.sum_powerset_smul_prod` is the distributive law: with `A_r`, `B_r` the clustered pair
  factors of the flipped and the unflipped corner at `r`, and `B_r - A_r = c · G_r`, the signed sum
  over `S ⊆ T` of the products with `A` at the corners of `S` and `B` at the others is `c^{#T}`
  times the product with `G` everywhere. Noncommutativity is no obstacle: the expansion is over the
  choice of one of two terms at each of finitely many *positions*, which is an induction over the
  marking and not a commutative rearrangement.

At a marked corner the letters of `π` at `r - 1` and `r` are `+` and `-`, and those of `π_S` are
`-` and `+`; reading the levels off `HJO.Dyck.wordLevel` gives `B_r = d_+d_-` at the levels
`(k - 1, k)` and `A_r = d_-d_+` at the levels `(k + 1, k)`, where `k` is the level at `r`. So
`B_r - A_r = (1 - q) · G_r` with `G_r = HJO.Sweep.cmCorner q k`, Carlsson and
Mellit's `(q-1)⁻¹ [d_-, d_+]`, and `c = 1 - q`.

## Implementation notes

*The factor convention is Carlsson and Mellit's, unadjusted.* The pair factor of
`HJO.Sweep.markedWordOp` is `(d_-d_+ - d_+d_-)/(q-1)`; a different corner convention would produce
`q/(q-1)·[d_-,d_+]` instead. What is proved here is the statement with Carlsson and Mellit's factor:
`HJO.Sweep.cmCorner q k` is `(q-1)⁻¹` times `d_-d_+ - d_+d_-`, read at the levels
`HJO.Dyck.wordLevel` assigns, with no power of `q` and no sign adjustment. The order of the
commutator is what the proof forces, and it is the reason the sign comes out right: the flipped
corner contributes `d_-d_+`, and it is the term that enters the alternating sum with a minus sign.

*A hypothesis `q ≠ 1` is needed.* At `q = 1` the factor `HJO.Sweep.cmCorner q k` is `0 • (⋯) = 0`,
since `(q-1)⁻¹ = 0⁻¹ = 0` in a field, so `Ξ_{π,T}` is the zero operator as soon as `T` marks a
corner, while `χ(π, T)` at `q = 1` is the nonzero series counting the labellings marked by `T` — and
one exists, `w_i = n - i` inverting every corner. Over a field such as `𝕜 = ℚ(q, u)`, with `q` an
indeterminate, the hypothesis is automatic; the Lean layer quantifies over an arbitrary field, so it
has to be carried. It enters at exactly one point, the identification of `B_r - A_r` with
`(1 - q) · G_r`, and again at the end to cancel the scalar `(1 - q)^{#T}`.

*Neither a hypothesis `1 ≤ n` nor `HJO.Sym.IsRealisation` is needed.*
Nothing below uses the length bound: at `n = 0` the corner set is empty, so `T = ∅` and the
conclusion *is* the hypothesis. And nothing below uses that `ι` is a realisation rather than an
arbitrary algebra map: the realisation enters through
`HJO.Dyck.realisation_constantCoeff_markedWordOp'`, which is the hypothesis, so carrying
`HJO.Sym.IsRealisation ι` here would only weaken the statement.

*The marked positions are handled as a `Finset ℕ`.* `HJO.Dyck.IsMarkedNorth x T s` is a predicate,
and the distributive law needs to erase one corner at a time from the marking; so the positions are
presented as `T.image HJO.Dyck.cornerPos`, with `HJO.Dyck.isMarkedNorth_iff_mem_image` the bridge
and `HJO.Dyck.injOn_cornerPos` the injectivity that makes the image faithful. The map is on cells
and takes no path as an argument, `(x_k - 1, k) ↦ x_k + k` being `(i, j) ↦ i + j + 1` on a corner
cell.

## References

E. Carlsson and A. Mellit, *A proof of the shuffle conjecture*, Corollary 4.6 at `T = c(π)`, and
A. Mellit's Theorem 3.7 for a general marking.
-/

@[expose] public section

open Finset List DyckStep

namespace HJO.Dyck

variable {n : ℕ} {x : Fin n → ℕ} {S T : Finset (ℕ × ℕ)}

/-! ### The marked positions as a set of positions -/

/-- The position of the north step of the corner cell `c`: the cell `(x_k - 1, k)` of the corner at
the row `k` has its north step at the position `x_k + k` of the step word, which is
`c.1 + c.2 + 1`. Read off the cell alone, so no path is needed to form it. -/
def cornerPos (c : ℕ × ℕ) : ℕ := c.1 + c.2 + 1

/-- **The marked positions are the image of the marking**: for `T ⊆ c(π)` a position is the north
step of a marked corner exactly when it is `HJO.Dyck.cornerPos` of a cell of `T`. This presents
`HJO.Dyck.IsMarkedNorth` as membership in a `Finset ℕ`, which is what lets one corner at a time be
erased from the marking. -/
theorem isMarkedNorth_iff_mem_image (hT : T ⊆ corner x) (s : ℕ) :
    IsMarkedNorth x T s ↔ s ∈ T.image cornerPos := by
  constructor
  · rintro ⟨k, hk, hkT, rfl⟩
    refine Finset.mem_image.2 ⟨(x k - 1, (k : ℕ)), hkT, ?_⟩
    have := hk.pos_apply
    simp only [cornerPos]
    omega
  · intro hs
    obtain ⟨c, hcT, rfl⟩ := Finset.mem_image.1 hs
    obtain ⟨k, hk, rfl⟩ := mem_corner.1 (hT hcT)
    refine ⟨k, hk, hcT, ?_⟩
    have := hk.pos_apply
    simp only [cornerPos]
    omega

/-- **Distinct marked corners have distinct positions**: `j ↦ x_j + j` is injective on a square
Dyck path, so `HJO.Dyck.cornerPos` is injective on any set of its corners. -/
theorem injOn_cornerPos (h : IsSquareDyck n x) (hT : T ⊆ corner x) :
    Set.InjOn cornerPos (T : Set (ℕ × ℕ)) := by
  intro a ha b hb hab
  obtain ⟨k, hk, rfl⟩ := mem_corner.1 (hT (Finset.mem_coe.1 ha))
  obtain ⟨l, hl, rfl⟩ := mem_corner.1 (hT (Finset.mem_coe.1 hb))
  have h1 := hk.pos_apply
  have h2 := hl.pos_apply
  obtain rfl : k = l :=
    h.strictMono_add_index.injective (show x k + (k : ℕ) = x l + (l : ℕ) by
      simp only [cornerPos] at hab
      omega)
  rfl

/-! ### The north steps of a flip -/

/-- **Away from the position below a flipped corner the north steps are unchanged**: flipping moves
the north step of a marked row from `r` to `r - 1`, so the positions `≤ t` carry the same number of
north steps before and after the flip unless `t + 1` is such an `r`. -/
theorem northCount_flipCorners_of_not_isMarkedNorth (hS : S ⊆ corner x) {t : ℕ}
    (h : ¬IsMarkedNorth x S (t + 1)) :
    northCount (flipCorners x S) t = northCount x t :=
  congrArg Finset.card (Finset.filter_congr fun k _ => by
    by_cases hk : (x k - 1, (k : ℕ)) ∈ S
    · have hck : IsCornerIndex x k := isCornerIndex_of_mem_of_subset_corner hS hk
      have hpos := hck.pos_apply
      have hne : x k + (k : ℕ) ≠ t + 1 := fun he => h ⟨k, hck, hk, he⟩
      rw [flipCorners_of_mem hk]
      constructor <;> intro hle <;> omega
    · rw [flipCorners_of_notMem hk])

/-- **At the position below a flipped corner the flip has one north step more**: the north step of
the flipped row has moved down to that position, and no other row moves. -/
theorem IsSquareDyck.northCount_flipCorners_of_isMarkedNorth (h : IsSquareDyck n x)
    (hS : S ⊆ corner x) {k : Fin n} (hk : (x k - 1, (k : ℕ)) ∈ S) {t : ℕ}
    (ht : x k + (k : ℕ) = t + 1) :
    northCount (HJO.Dyck.flipCorners x S) t = northCount x t + 1 := by
  have hck : IsCornerIndex x k := isCornerIndex_of_mem_of_subset_corner hS hk
  have hpos := hck.pos_apply
  have hins :
      Finset.filter (fun j : Fin n => HJO.Dyck.flipCorners x S j + (j : ℕ) ≤ t) Finset.univ
        = insert k (Finset.filter (fun j : Fin n => x j + (j : ℕ) ≤ t) Finset.univ) := by
    ext j
    simp only [mem_filter_univ, Finset.mem_insert]
    by_cases hj : (x j - 1, (j : ℕ)) ∈ S
    · have hcj : IsCornerIndex x j := isCornerIndex_of_mem_of_subset_corner hS hj
      have hposj := hcj.pos_apply
      rw [flipCorners_of_mem hj]
      constructor
      · intro hle
        rcases Nat.lt_or_ge (x j + (j : ℕ)) (t + 1) with h1 | h1
        · exact Or.inr (by omega)
        · exact Or.inl
            (h.strictMono_add_index.injective (show x j + (j : ℕ) = x k + (k : ℕ) by omega))
      · rintro (rfl | hle) <;> omega
    · rw [flipCorners_of_notMem hj]
      refine ⟨Or.inr, ?_⟩
      rintro (rfl | hle)
      · exact absurd hk hj
      · exact hle
  exact (congrArg Finset.card hins).trans
    (Finset.card_insert_of_notMem (by simp only [mem_filter_univ]; omega))

/-- **The north steps at and below a corner**: the positions `≤ r` of a square Dyck path carry one
north step more than the positions `≤ r - 1`, when `r` is the position of a north step. -/
theorem IsSquareDyck.northCount_succ_of_add_index_eq (h : IsSquareDyck n x) {k : Fin n} {t : ℕ}
    (ht : x k + (k : ℕ) = t + 1) : northCount x (t + 1) = northCount x t + 1 := by
  have hins : Finset.filter (fun j : Fin n => x j + (j : ℕ) ≤ t + 1) Finset.univ
      = insert k (Finset.filter (fun j : Fin n => x j + (j : ℕ) ≤ t) Finset.univ) := by
    ext j
    simp only [mem_filter_univ, Finset.mem_insert]
    constructor
    · intro hle
      rcases Nat.lt_or_ge (x j + (j : ℕ)) (t + 1) with h1 | h1
      · exact Or.inr (by omega)
      · exact Or.inl
          (h.strictMono_add_index.injective (show x j + (j : ℕ) = x k + (k : ℕ) by omega))
    · rintro (rfl | hle) <;> omega
  exact (congrArg Finset.card hins).trans
    (Finset.card_insert_of_notMem (by simp only [mem_filter_univ]; omega))

/-! ### The levels of a flip -/

/-- **The level rises by one at the north step of a corner**: the factor at the position `r` of a
north step is read one level above the factor at `r - 1`, the east step below it having raised the
level. -/
theorem IsSquareDyck.wordLevel_pred_of_add_index_eq (h : IsSquareDyck n x) {k : Fin n} {s : ℕ}
    (hks : x k + (k : ℕ) = s) (hpos : 0 < s) : wordLevel x s = wordLevel x (s - 1) + 1 := by
  obtain ⟨t, rfl⟩ : ∃ t, s = t + 1 := ⟨s - 1, by omega⟩
  have hlt : t + 1 < 2 * n := by
    have := h.add_index_add_one_lt_two_mul k
    omega
  have h1 := h.wordLevel_add hlt
  have h2 := h.wordLevel_add (show t < 2 * n by omega)
  have h3 := h.northCount_succ_of_add_index_eq hks
  simp only [Nat.add_sub_cancel]
  omega

/-- **Away from the position below a flipped corner the levels are unchanged.** -/
theorem wordLevel_flipCorners_of_not_isMarkedNorth (hS : S ⊆ corner x) {t : ℕ}
    (h : ¬IsMarkedNorth x S (t + 1)) : wordLevel (flipCorners x S) t = wordLevel x t := by
  rw [wordLevel, wordLevel, northCount_flipCorners_of_not_isMarkedNorth hS h]

/-- **Below a flipped corner the flip reads two levels higher**: the flipped path has a north step
at the position `r - 1` where `π` has an east step, so the level there rises by two — one level
above the level `π` reads at `r` itself. This is what makes the pair factor of a flipped corner
`d_-d_+` read at the levels `(k + 1, k)`, with `k` the level of `π` at `r`. -/
theorem IsSquareDyck.wordLevel_flipCorners_pred (h : IsSquareDyck n x) (hS : S ⊆ corner x)
    {k : Fin n} (hk : (x k - 1, (k : ℕ)) ∈ S) {s : ℕ} (hks : x k + (k : ℕ) = s) :
    wordLevel (HJO.Dyck.flipCorners x S) (s - 1) = wordLevel x s + 1 := by
  have hck : IsCornerIndex x k := isCornerIndex_of_mem_of_subset_corner hS hk
  have hcpos := hck.pos_apply
  have hpos : 0 < s := by omega
  obtain ⟨t, rfl⟩ : ∃ t, s = t + 1 := ⟨s - 1, by omega⟩
  have hlt : t + 1 < 2 * n := by
    have := h.add_index_add_one_lt_two_mul k
    omega
  have h1 := (h.flipCorners hS).wordLevel_add (show t < 2 * n by omega)
  have h2 := h.wordLevel_add hlt
  have h3 := h.northCount_flipCorners_of_isMarkedNorth hS hk (t := t) hks
  have h4 := h.northCount_succ_of_add_index_eq hks
  simp only [Nat.add_sub_cancel]
  omega

/-! ### The letters of a flip -/

/-- **Below a flipped corner the flip reads a north step**, where `π` reads an east step: the north
step of the flipped row has moved there. -/
theorem getD_stepWord_flipCorners_of_isMarkedNorth_succ {t : ℕ}
    (h : IsMarkedNorth x S (t + 1)) (ht : t < 2 * n) :
    (stepWord (flipCorners x S)).getD t DyckStep.D = DyckStep.U := by
  have hlen : t < (stepWord (flipCorners x S)).length := by rw [length_stepWord]; exact ht
  rw [List.getD_eq_getElem _ _ hlen]
  obtain ⟨k, hk, hkS, hks⟩ := h
  refine (getElem_stepWord_eq_U_iff _ _ hlen).2 ⟨k, ?_⟩
  have := hk.pos_apply
  rw [flipCorners_of_mem hkS]
  omega

/-- **At a flipped corner the flip reads an east step**, where `π` reads a north step: the north
step of that row has moved below it, and no other row can supply one. -/
theorem IsSquareDyck.getD_stepWord_flipCorners_of_isMarkedNorth (h : IsSquareDyck n x)
    (hS : S ⊆ corner x) {t : ℕ} (hm : IsMarkedNorth x S t) (ht : t < 2 * n) :
    (stepWord (HJO.Dyck.flipCorners x S)).getD t DyckStep.D = DyckStep.D := by
  have hlen : t < (stepWord (HJO.Dyck.flipCorners x S)).length := by
    rw [length_stepWord]; exact ht
  rw [List.getD_eq_getElem _ _ hlen]
  obtain ⟨k₀, hk₀, hk₀S, hk₀s⟩ := hm
  refine (getElem_stepWord_eq_D_iff _ _ hlen).2 fun j hj => ?_
  by_cases hjS : (x j - 1, (j : ℕ)) ∈ S
  · have hcj : IsCornerIndex x j := isCornerIndex_of_mem_of_subset_corner hS hjS
    have hposj := hcj.pos_apply
    rw [flipCorners_of_mem hjS] at hj
    exact h.northPos_pred_ne hcj k₀ (by omega)
  · rw [flipCorners_of_notMem hjS] at hj
    obtain rfl : j = k₀ := h.strictMono_add_index.injective (by omega)
    exact hjS hk₀S

/-- **Every other letter is unchanged by a flip**: a position that is neither a flipped corner nor
the position below one reads the same letter in `π` and in `π_S`. -/
theorem getD_stepWord_flipCorners_of_not (hS : S ⊆ corner x) {t : ℕ}
    (h1 : ¬IsMarkedNorth x S t) (h2 : ¬IsMarkedNorth x S (t + 1)) (ht : t < 2 * n) :
    (stepWord (flipCorners x S)).getD t DyckStep.D = (stepWord x).getD t DyckStep.D := by
  have hlen : t < (stepWord (flipCorners x S)).length := by rw [length_stepWord]; exact ht
  have hlen' : t < (stepWord x).length := by rw [length_stepWord]; exact ht
  rw [List.getD_eq_getElem _ _ hlen, List.getD_eq_getElem _ _ hlen',
    getElem_stepWord _ _ hlen, getElem_stepWord _ _ hlen']
  refine if_congr (Iff.intro ?_ ?_) rfl rfl
  · rintro ⟨j, hj⟩
    by_cases hjS : (x j - 1, (j : ℕ)) ∈ S
    · have hcj : IsCornerIndex x j := isCornerIndex_of_mem_of_subset_corner hS hjS
      have hposj := hcj.pos_apply
      rw [flipCorners_of_mem hjS] at hj
      exact absurd ⟨j, hcj, hjS, by omega⟩ h2
    · exact ⟨j, by rwa [flipCorners_of_notMem hjS] at hj⟩
  · rintro ⟨j, hj⟩
    by_cases hjS : (x j - 1, (j : ℕ)) ∈ S
    · exact absurd ⟨j, isCornerIndex_of_mem_of_subset_corner hS hjS, hjS, hj⟩ h1
    · exact ⟨j, by rwa [flipCorners_of_notMem hjS]⟩

end HJO.Dyck

namespace HJO.Sweep

open Dyck

/-! ### Products over a range of positions -/

/-- A product over `Fin m` read as a product over `List.range m`: the form in which positions are
natural numbers, so that the position below a marked one is `s - 1` with no coercion. -/
theorem ofFn_val_eq_range_map {α : Type*} (m : ℕ) (g : ℕ → α) :
    (List.ofFn fun t : Fin m => g (t : ℕ)) = (List.range m).map g :=
  List.ext_getElem (by simp) fun i h1 h2 => by simp

/-- **Clustering the factors of a pair into its upper position.** If no marked position is `0` and
no two marked positions are adjacent, then the product of one factor per position equals the product
in which each marked position `s` carries the two factors of `s - 1` and `s` and the position below
it carries the identity. This is the passage between the two readings of `Ξ_{π,T}` — as
a product over the blocks of the partition and as a product over the positions — and it is
noncommutative throughout: the two factors stay in their order, and the block sits where its largest
position sits. -/
theorem prod_range_map_cluster {R : Type*} [Monoid R] (p : ℕ → Prop) [DecidablePred p]
    (hp0 : ∀ s, p s → 0 < s) (hp2 : ∀ s, p s → ¬p (s + 1)) (f : ℕ → R) :
    ∀ m : ℕ, ¬p m →
      ((List.range m).map f).prod
        = ((List.range m).map fun s =>
            if p s then f (s - 1) * f s else if p (s + 1) then 1 else f s).prod := by
  have hsplit : ∀ (g : ℕ → R) (t : ℕ),
      ((List.range (t + 1)).map g).prod = ((List.range t).map g).prod * g t := by
    intro g t
    rw [List.range_succ, List.map_append, List.prod_append, List.map_cons, List.map_nil,
      List.prod_cons, List.prod_nil, mul_one]
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    match m with
    | 0 => intro _; rfl
    | (t + 1) =>
      intro hnp
      rw [hsplit, hsplit]
      by_cases hpt : p t
      · obtain ⟨u, rfl⟩ : ∃ u, t = u + 1 := ⟨t - 1, by have := hp0 t hpt; omega⟩
        have hpu : ¬p u := fun hu => hp2 u hu hpt
        rw [hsplit, hsplit, ih u (by omega) hpu, ite_eq_left hpt, ite_eq_right hpu, ite_eq_left hpt,
          Nat.add_sub_cancel, mul_one, mul_assoc]
      · rw [ih t (by omega) hpt, ite_eq_right hpt, ite_eq_right hnp]

/-! ### The distributive law -/

/-- Two products over a list differ at one position by the difference of the factors there: if `u`
and `v` agree off `s₀`, and `w` agrees with them off `s₀` and carries `u s₀ - v s₀` at `s₀`, then
the difference of the products is the product of `w`. -/
private theorem prod_map_sub_of_eq_off {R : Type*} [Ring R] {l : List ℕ} {s₀ : ℕ} (hs : s₀ ∈ l)
    (hnd : l.Nodup) (u v w : ℕ → R) (huv : ∀ s ∈ l, s ≠ s₀ → u s = v s)
    (huw : ∀ s ∈ l, s ≠ s₀ → u s = w s) (h0 : w s₀ = u s₀ - v s₀) :
    (l.map u).prod - (l.map v).prod = (l.map w).prod := by
  obtain ⟨l₁, l₂, rfl⟩ := List.append_of_mem hs
  obtain ⟨-, hnd2, hdis⟩ := List.nodup_append.1 hnd
  have h1 : s₀ ∉ l₁ := fun hm => hdis s₀ hm s₀ (List.mem_cons_self ..) rfl
  have h2 : s₀ ∉ l₂ := (List.nodup_cons.1 hnd2).1
  have e1 : ∀ z : ℕ → R, (∀ s ∈ l₁ ++ s₀ :: l₂, s ≠ s₀ → u s = z s) →
      l₁.map u = l₁.map z ∧ l₂.map u = l₂.map z := fun z hz =>
    ⟨List.map_congr_left fun s hsm => hz s (by simp [hsm]) fun he => h1 (he ▸ hsm),
      List.map_congr_left fun s hsm => hz s (by simp [hsm]) fun he => h2 (he ▸ hsm)⟩
  obtain ⟨ev1, ev2⟩ := e1 v huv
  obtain ⟨ew1, ew2⟩ := e1 w huw
  simp only [List.map_append, List.prod_append, List.map_cons, List.prod_cons, ← ev1, ← ev2,
    ← ew1, ← ew2, h0]
  rw [sub_mul, mul_sub]

/-- Two products over a list differ at one position by a scalar: if `u` and `v` agree off `s₀` and
`u s₀ = c • v s₀`, then the product of `u` is `c` times the product of `v`. -/
private theorem prod_map_eq_smul_of_eq_off {A : Type*} [CommRing A] {R : Type*} [Ring R]
    [Algebra A R] {l : List ℕ} {s₀ : ℕ} (hs : s₀ ∈ l) (hnd : l.Nodup) (c : A) (u v : ℕ → R)
    (huv : ∀ s ∈ l, s ≠ s₀ → u s = v s) (h0 : u s₀ = c • v s₀) :
    (l.map u).prod = c • (l.map v).prod := by
  obtain ⟨l₁, l₂, rfl⟩ := List.append_of_mem hs
  obtain ⟨-, hnd2, hdis⟩ := List.nodup_append.1 hnd
  have h1 : s₀ ∉ l₁ := fun hm => hdis s₀ hm s₀ (List.mem_cons_self ..) rfl
  have h2 : s₀ ∉ l₂ := (List.nodup_cons.1 hnd2).1
  have ev1 : l₁.map u = l₁.map v :=
    List.map_congr_left fun s hsm => huv s (by simp [hsm]) fun he => h1 (he ▸ hsm)
  have ev2 : l₂.map u = l₂.map v :=
    List.map_congr_left fun s hsm => huv s (by simp [hsm]) fun he => h2 (he ▸ hsm)
  simp only [List.map_append, List.prod_append, List.map_cons, List.prod_cons, ev1, ev2, h0]
  rw [smul_mul_assoc, mul_smul_comm]

/-- **The distributive law behind the inclusion--exclusion.** Let `pos` send each element of a
marking `P` to its own position in a list `l` of distinct positions, let `aop s` and `bop s` be the
factors of a marked position in its two states, let `cop s` be the factor of every other position,
and let `bop s - aop s = c • gop s`. Then the signed sum, over the subsets `Sm ⊆ P`, of the products
carrying `aop` at the positions of `Sm` and `bop` at the remaining positions of `P` is `c ^ #P`
times the product carrying `gop` at every position of `P`.

The expansion is over the choice, at each marked position, of one of two factors, so it is an
induction over `P` — a rearrangement of *scalars*, and no commutation of factors: the two products
subtracted at each step differ in one position only, which is
`HJO.Sweep.prod_map_sub_of_eq_off`. -/
theorem sum_powerset_smul_prod {A : Type*} [CommRing A] {R : Type*} [Ring R] [Algebra A R]
    {ι : Type*} (c : A) (aop bop gop : ℕ → R) (pos : ι → ℕ)
    (hG : ∀ s, bop s - aop s = c • gop s) (l : List ℕ) (hnd : l.Nodup) :
    ∀ P : Finset ι, (∀ i ∈ P, pos i ∈ l) → Set.InjOn pos (P : Set ι) → ∀ cop : ℕ → R,
      ∑ Sm ∈ P.powerset, (-1 : A) ^ #Sm •
          (l.map fun s => if s ∈ Sm.image pos then aop s
            else if s ∈ P.image pos then bop s else cop s).prod
        = c ^ #P • (l.map fun s => if s ∈ P.image pos then gop s else cop s).prod := by
  classical
  intro P
  induction P using Finset.induction_on with
  | empty => intro _ _ cop; simp
  | @insert i₀ P' hi₀ ih =>
    intro hP hinj cop
    have hs₀l : pos i₀ ∈ l := hP i₀ (Finset.mem_insert_self _ _)
    have hnotP' : pos i₀ ∉ P'.image pos := by
      intro hm
      obtain ⟨i, hiP', hi⟩ := Finset.mem_image.1 hm
      exact hi₀ (hinj (Finset.mem_coe.2 (Finset.mem_insert_of_mem hiP'))
        (Finset.mem_coe.2 (Finset.mem_insert_self _ _)) hi ▸ hiP')
    have hsub : ∀ Sm ∈ P'.powerset, pos i₀ ∉ Sm.image pos := by
      intro Sm hSm hm
      obtain ⟨i, hi, hie⟩ := Finset.mem_image.1 hm
      exact hnotP' (Finset.mem_image.2 ⟨i, Finset.mem_powerset.1 hSm hi, hie⟩)
    have hmemoff : ∀ s, s ≠ pos i₀ → (s ∈ (insert i₀ P').image pos ↔ s ∈ P'.image pos) := by
      intro s hs
      rw [Finset.image_insert, Finset.mem_insert]
      exact ⟨fun hm => hm.resolve_left hs, Or.inr⟩
    have hmems₀ : pos i₀ ∈ (insert i₀ P').image pos := by
      rw [Finset.image_insert]
      exact Finset.mem_insert_self _ _
    obtain ⟨cop', hcop'₀, hcop'off⟩ :
        ∃ f : ℕ → R, f (pos i₀) = c • gop (pos i₀) ∧ ∀ s, s ≠ pos i₀ → f s = cop s :=
      ⟨fun s => if s = pos i₀ then c • gop (pos i₀) else cop s, by simp, fun s hs => by simp [hs]⟩
    have hterm : ∀ Sm ∈ P'.powerset,
        ((-1 : A) ^ #Sm • (l.map fun s => if s ∈ Sm.image pos then aop s
              else if s ∈ (insert i₀ P').image pos then bop s else cop s).prod
            + (-1 : A) ^ #(insert i₀ Sm) •
              (l.map fun s => if s ∈ (insert i₀ Sm).image pos then aop s
                else if s ∈ (insert i₀ P').image pos then bop s else cop s).prod)
          = (-1 : A) ^ #Sm • (l.map fun s => if s ∈ Sm.image pos then aop s
              else if s ∈ P'.image pos then bop s else cop' s).prod := by
      intro Sm hSm
      have hi₀Sm : i₀ ∉ Sm := fun hm => hi₀ (Finset.mem_powerset.1 hSm hm)
      have hSm₀ := hsub Sm hSm
      have hins : ∀ s, s ≠ pos i₀ → (s ∈ (insert i₀ Sm).image pos ↔ s ∈ Sm.image pos) := by
        intro s hs
        rw [Finset.image_insert, Finset.mem_insert]
        exact ⟨fun hm => hm.resolve_left hs, Or.inr⟩
      have hkey := prod_map_sub_of_eq_off hs₀l hnd
        (fun s => if s ∈ Sm.image pos then aop s
          else if s ∈ (insert i₀ P').image pos then bop s else cop s)
        (fun s => if s ∈ (insert i₀ Sm).image pos then aop s
          else if s ∈ (insert i₀ P').image pos then bop s else cop s)
        (fun s => if s ∈ Sm.image pos then aop s
          else if s ∈ P'.image pos then bop s else cop' s)
        (fun s _ hs => by simp only [hins s hs])
        (fun s _ hs => by simp only [hmemoff s hs, hcop'off s hs])
        (by
          rw [ite_eq_right hSm₀, ite_eq_left hmems₀, ite_eq_right hSm₀, ite_eq_right hnotP', hcop'₀,
            ite_eq_left (show pos i₀ ∈ (insert i₀ Sm).image pos from by
              rw [Finset.image_insert]; exact Finset.mem_insert_self _ _)]
          exact (hG _).symm)
      rw [← hkey, smul_sub, Finset.card_insert_of_notMem hi₀Sm, pow_succ, mul_neg_one, neg_smul,
        ← sub_eq_add_neg]
    rw [Finset.sum_powerset_insert hi₀, ← Finset.sum_add_distrib, Finset.sum_congr rfl hterm,
      ih (fun i hi => hP i (Finset.mem_insert_of_mem hi))
        (hinj.mono (by
          rw [Finset.coe_insert]
          exact Set.subset_insert _ _)) cop',
      prod_map_eq_smul_of_eq_off hs₀l hnd c
        (fun s => if s ∈ P'.image pos then gop s else cop' s)
        (fun s => if s ∈ (insert i₀ P').image pos then gop s else cop s)
        (fun s _ hs => by simp only [hmemoff s hs, hcop'off s hs])
        (by rw [ite_eq_right hnotP', ite_eq_left hmems₀, hcop'₀]),
      smul_smul, Finset.card_insert_of_notMem hi₀, pow_succ]

/-! ### The corner factor as a difference of pairs -/

variable {L : Type*} [Field L] [Algebra ℚ L]

/-- **The pair factors of a corner in its two states differ by the corner operator**: with `k` the
level at the north step of the corner, the unflipped pair `d_+d_-`, read at the levels `(k - 1, k)`,
less the flipped pair `d_-d_+`, read at the levels `(k + 1, k)`, is `1 - q` times
`HJO.Sweep.cmCorner q k`, the `(q-1)⁻¹ [d_-, d_+]`.

The hypothesis `q ≠ 1` is needed: at `q = 1` the corner operator is `0`, the factor `(q-1)⁻¹` in
`HJO.Sweep.cmCorner` being `0⁻¹ = 0`, while the left-hand side is not. -/
theorem sub_eq_smul_cmCorner (q : L) (hq : q ≠ 1) (k : ℕ) :
    cmDPlus q (k - 1) * dminusCM q k - dminusCM q (k + 1) * cmDPlus q k
      = (1 - q) • cmCorner q k := by
  have h1 : q - 1 ≠ 0 := sub_ne_zero.2 hq
  rw [cmCorner, smul_smul,
    show (1 - q) * (q - 1)⁻¹ = -1 from by
      rw [show (1 : L) - q = -(q - 1) from by ring, neg_mul, mul_inv_cancel₀ h1]]
  exact ((neg_one_smul L _).trans (neg_sub _ _)).symm

/-- **At `q = 1` the corner factor is zero**, the scalar `(q-1)⁻¹` of `HJO.Sweep.cmCorner` being
`0⁻¹ = 0` in a field. -/
theorem cmCorner_one_eq_zero (k : ℕ) : cmCorner (1 : L) k = 0 := by
  rw [cmCorner, sub_self, inv_zero, zero_smul]

/-! ### The word of a flip, clustered at the corners -/

variable {n : ℕ} {x : Fin n → ℕ} {S T : Finset (ℕ × ℕ)}

/-- `Ξ_{π,T}` as a product over `List.range (2n)`, the form in which the positions are natural
numbers. -/
theorem markedWordOp_eq_prod_range (q : L) (x : Fin n → ℕ) (T : Finset (ℕ × ℕ)) :
    markedWordOp q x T = ((List.range (2 * n)).map fun t => markedFactor q x T t).prod := by
  rw [markedWordOp]
  exact congrArg List.prod (ofFn_val_eq_range_map _ _)

/-- **The word of a flip, with the letters at each marked corner clustered.** For `S ⊆ T ⊆ c(π)`
the plain word `Ξ_{π_S,∅}` of the flipped path is the product over the `2n` positions in which each
corner of `T` carries, at the position `r` of its north step, the two letters of `π_S` at `r - 1`
and `r` — `d_-d_+` at the levels `(k + 1, k)` if the corner is flipped by `S`, and `d_+d_-` at the
levels `(k - 1, k)` if it is not — the position below carries the identity, and every other position
carries the factor `Ξ_{π,T}` gives it, the flip having changed neither its letter nor its level. -/
private theorem markedWordOp_flipCorners_eq_prod (q : L) (hx : IsSquareDyck n x) (hST : S ⊆ T)
    (hT : T ⊆ Dyck.corner x) :
    markedWordOp q (flipCorners x S) ∅
      = ((List.range (2 * n)).map fun t =>
          if t ∈ S.image cornerPos then
            dminusCM q (wordLevel x t + 1) * cmDPlus q (wordLevel x t)
          else if t ∈ T.image cornerPos then
            cmDPlus q (wordLevel x t - 1) * dminusCM q (wordLevel x t)
          else markedFactor q x T t).prod := by
  have hSc : S ⊆ Dyck.corner x := hST.trans hT
  have hmono : ∀ s, IsMarkedNorth x S s → IsMarkedNorth x T s := by
    rintro s ⟨k, hk, hkS, hks⟩
    exact ⟨k, hk, hST hkS, hks⟩
  have hp0 : ∀ s, IsMarkedNorth x T s → 0 < s := fun s hs => hs.pos
  have hp2 : ∀ s, IsMarkedNorth x T s → ¬IsMarkedNorth x T (s + 1) := fun s hs =>
    hx.not_isMarkedNorth_succ hs
  have hpend : ¬IsMarkedNorth x T (2 * n) := by
    rintro ⟨k, -, -, hk⟩
    have := hx.add_index_add_one_lt_two_mul k
    omega
  calc markedWordOp q (flipCorners x S) ∅
      = ((List.range (2 * n)).map fun t =>
          stepOp q ((stepWord (flipCorners x S)).getD t DyckStep.D)
            (wordLevel (flipCorners x S) t)).prod := by
        rw [markedWordOp_eq_prod_range]
        exact congrArg List.prod
          (List.map_congr_left fun t _ => markedFactor_empty q (flipCorners x S) t)
    _ = ((List.range (2 * n)).map fun t =>
          if IsMarkedNorth x T t then
            stepOp q ((stepWord (flipCorners x S)).getD (t - 1) DyckStep.D)
                (wordLevel (flipCorners x S) (t - 1))
              * stepOp q ((stepWord (flipCorners x S)).getD t DyckStep.D)
                (wordLevel (flipCorners x S) t)
          else if IsMarkedNorth x T (t + 1) then 1
          else stepOp q ((stepWord (flipCorners x S)).getD t DyckStep.D)
            (wordLevel (flipCorners x S) t)).prod :=
        prod_range_map_cluster (IsMarkedNorth x T) hp0 hp2 _ (2 * n) hpend
    _ = _ := by
        refine congrArg List.prod (List.map_congr_left fun t ht => ?_)
        have htlt : t < 2 * n := List.mem_range.1 ht
        by_cases hTt : IsMarkedNorth x T t
        · have hpos := hTt.pos
          have hsucc : t - 1 + 1 = t := by omega
          have hpred : t - 1 < 2 * n := by omega
          have htmem : t ∈ T.image cornerPos := (isMarkedNorth_iff_mem_image hT t).1 hTt
          have hTsucc : ¬IsMarkedNorth x T (t + 1) := hp2 t hTt
          have hSsucc : ¬IsMarkedNorth x S (t + 1) := fun hm => hTsucc (hmono _ hm)
          rw [ite_eq_left hTt]
          by_cases hSt : IsMarkedNorth x S t
          · obtain ⟨k, hk, hkS, hks⟩ := id hSt
            rw [ite_eq_left ((isMarkedNorth_iff_mem_image hSc t).1 hSt),
              getD_stepWord_flipCorners_of_isMarkedNorth_succ
                (show IsMarkedNorth x S (t - 1 + 1) from by rwa [hsucc]) hpred,
              hx.getD_stepWord_flipCorners_of_isMarkedNorth hSc hSt htlt,
              hx.wordLevel_flipCorners_pred hSc hkS hks,
              wordLevel_flipCorners_of_not_isMarkedNorth hSc hSsucc, stepOp_U, stepOp_D]
          · obtain ⟨k, hk, hkT, hks⟩ := id hTt
            have hSt' : ¬IsMarkedNorth x S (t - 1 + 1) := by rwa [hsucc]
            have hTpred : ¬IsMarkedNorth x T (t - 1) := fun hm => hp2 _ hm (by rwa [hsucc])
            have hSpred : ¬IsMarkedNorth x S (t - 1) := fun hm => hTpred (hmono _ hm)
            have hxD : (stepWord x).getD (t - 1) DyckStep.D = DyckStep.D := by
              have hl : t - 1 < (stepWord x).length := by rw [length_stepWord]; omega
              rw [List.getD_eq_getElem _ _ hl]
              exact hx.getElem_stepWord_isMarkedNorth_pred hl hTt
            have hxU : (stepWord x).getD t DyckStep.D = DyckStep.U := by
              have hl : t < (stepWord x).length := by rw [length_stepWord]; omega
              rw [List.getD_eq_getElem _ _ hl]
              exact getElem_stepWord_isMarkedNorth hl hTt
            have hlev : wordLevel x (t - 1) = wordLevel x t - 1 := by
              have := hx.wordLevel_pred_of_add_index_eq hks hpos
              omega
            rw [ite_eq_right (fun hm => hSt ((isMarkedNorth_iff_mem_image hSc t).2 hm)),
              ite_eq_left htmem,
              getD_stepWord_flipCorners_of_not hSc hSpred hSt' hpred,
              getD_stepWord_flipCorners_of_not hSc hSt hSsucc htlt,
              wordLevel_flipCorners_of_not_isMarkedNorth hSc hSt',
              wordLevel_flipCorners_of_not_isMarkedNorth hSc hSsucc, hxD, hxU, hlev, stepOp_D,
              stepOp_U]
        · have hSt : ¬IsMarkedNorth x S t := fun hm => hTt (hmono _ hm)
          rw [ite_eq_right hTt,
            ite_eq_right (fun hm => hSt ((isMarkedNorth_iff_mem_image hSc t).2 hm)),
            ite_eq_right (fun hm => hTt ((isMarkedNorth_iff_mem_image hT t).2 hm))]
          by_cases hTsucc : IsMarkedNorth x T (t + 1)
          · rw [ite_eq_left hTsucc]
            simp only [markedFactor, ite_eq_right hTt, ite_eq_left hTsucc]
          · have hSsucc : ¬IsMarkedNorth x S (t + 1) := fun hm => hTsucc (hmono _ hm)
            rw [ite_eq_right hTsucc, getD_stepWord_flipCorners_of_not hSc hSt hSsucc htlt,
              wordLevel_flipCorners_of_not_isMarkedNorth hSc hSsucc]
            simp only [markedFactor, ite_eq_right hTt, ite_eq_right hTsucc]

/-! ### The operator identity -/

/-- **The signed sum of the words of the flips is the word of the marked path.** For a square Dyck
path `π` of length `n` and a marking `T ⊆ c(π)`,

`∑_{S ⊆ T} (-1)^{#S} Ξ_{π_S,∅} = (1 - q)^{#T} Ξ_{π,T}`,

with `Ξ_{π_S,∅}` the plain word of the flipped path. This is the operator half of
`HJO.Mellit.map_constantCoeff_markedWordOp'`, and it carries no realisation: the step "dividing each
factor at a corner of `T` by `1 - q`" is this identity, and the inclusion--exclusion
`HJO.Dyck.pathMarkedCharSeries_inclusion_exclusion` is its counterpart on the characteristic series.

Position by position: a corner of `T` occupies the positions `r - 1` and `r` of its north step, and
the letters there are `+ -` in `π` and `- +` in `π_S` for `S` containing that corner, with the level
at `r` the same either way. So the sum expands, at each corner of `T` independently, as a choice
between `d_+d_-` and `-d_-d_+`, whose sum is `1 - q` times `HJO.Sweep.cmCorner`. -/
theorem sum_powerset_smul_markedWordOp_flipCorners (q : L) (hx : IsSquareDyck n x)
    (hT : T ⊆ Dyck.corner x) (hq : q ≠ 1) :
    ∑ S ∈ T.powerset, (-1 : L) ^ #S • markedWordOp q (flipCorners x S) ∅
      = (1 - q) ^ #T • markedWordOp q x T := by
  have hposmem : ∀ c ∈ T, cornerPos c ∈ List.range (2 * n) := by
    intro c hc
    obtain ⟨k, hk, rfl⟩ := mem_corner.1 (hT hc)
    have h1 := hk.pos_apply
    have h2 := hx.add_index_add_one_lt_two_mul k
    refine List.mem_range.2 ?_
    simp only [cornerPos]
    omega
  calc ∑ S ∈ T.powerset, (-1 : L) ^ #S • markedWordOp q (flipCorners x S) ∅
      = ∑ S ∈ T.powerset, (-1 : L) ^ #S • ((List.range (2 * n)).map fun t =>
            if t ∈ S.image cornerPos then
              dminusCM q (wordLevel x t + 1) * cmDPlus q (wordLevel x t)
            else if t ∈ T.image cornerPos then
              cmDPlus q (wordLevel x t - 1) * dminusCM q (wordLevel x t)
            else markedFactor q x T t).prod :=
        Finset.sum_congr rfl fun S hS => by
          rw [markedWordOp_flipCorners_eq_prod q hx (Finset.mem_powerset.1 hS) hT]
    _ = (1 - q) ^ #T • ((List.range (2 * n)).map fun t =>
          if t ∈ T.image cornerPos then cmCorner q (wordLevel x t)
          else markedFactor q x T t).prod :=
        sum_powerset_smul_prod (1 - q)
          (fun t => dminusCM q (wordLevel x t + 1) * cmDPlus q (wordLevel x t))
          (fun t => cmDPlus q (wordLevel x t - 1) * dminusCM q (wordLevel x t))
          (fun t => cmCorner q (wordLevel x t)) cornerPos
          (fun t => sub_eq_smul_cmCorner q hq (wordLevel x t)) (List.range (2 * n))
          List.nodup_range T hposmem (injOn_cornerPos hx hT) (markedFactor q x T)
    _ = (1 - q) ^ #T • markedWordOp q x T := by
        rw [markedWordOp_eq_prod_range]
        congr 1
        refine congrArg List.prod (List.map_congr_left fun t _ => ?_)
        by_cases h : t ∈ T.image cornerPos
        · rw [ite_eq_left h]
          simp only [markedFactor, ite_eq_left ((isMarkedNorth_iff_mem_image hT t).2 h)]
        · rw [ite_eq_right h]

/-- **At `q = 1` the word of a marked path is the zero operator as soon as one corner is marked**,
the factor of that corner being `HJO.Sweep.cmCorner 1` and so `0`.

This is why the hypothesis `q ≠ 1` of
`HJO.Sweep.map_constantCoeff_markedWordOp_one_eq_pathMarkedCharSeries` cannot be dropped: the
right-hand side `χ(π, T)` at `q = 1` is the series counting the labellings marked by `T`, and there
is one — `w_i = n - i` inverts every cell `(x_k - 1, k)` of `c(π)`, since `x_k - 1 < k`. So the two
sides do not agree there. -/
theorem markedWordOp_one_eq_zero_of_nonempty (hx : IsSquareDyck n x) (hT : T ⊆ Dyck.corner x)
    (hne : T.Nonempty) : markedWordOp (1 : L) x T = 0 := by
  obtain ⟨c, hc⟩ := hne
  obtain ⟨k, hk, rfl⟩ := mem_corner.1 (hT hc)
  have hlt : x k + (k : ℕ) < 2 * n := by
    have := hx.add_index_add_one_lt_two_mul k
    omega
  have hmark : IsMarkedNorth x T (x k + (k : ℕ)) := ⟨k, hk, hc, rfl⟩
  rw [markedWordOp]
  refine List.prod_eq_zero (List.mem_ofFn.2 ⟨⟨x k + (k : ℕ), hlt⟩, ?_⟩)
  change markedFactor (1 : L) x T (x k + (k : ℕ)) = 0
  simp only [markedFactor, ite_eq_left hmark, cmCorner_one_eq_zero]

/-! ### The marked word computes the marked characteristic series -/

/-- **`HJO.Mellit.map_constantCoeff_markedWordOp'`, modulo
`HJO.Dyck.realisation_constantCoeff_markedWordOp'`.** For a square Dyck path `π` of length `n` with
coarea sequence `x`, a marking `T ⊆ c(π)` of its corners and an algebra map `ι` from `Λ` to the
alphabet series,

`ι(Ξ_{π,T}(1)) = χ(π, T)`,

on the hypothesis `hthm44` that the same holds with *no* corner marked, for every square Dyck path
of length `n` — which is this statement at `T = ∅`, `Ξ_{π,∅}` being the plain word
`d_{ε_1} ⋯ d_{ε_{2n}}` by `HJO.Sweep.markedFactor_empty`, and which is
`HJO.Dyck.realisation_constantCoeff_markedWordOp'`.

The proof is by inclusion--exclusion. By `HJO.Sweep.sum_powerset_smul_markedWordOp_flipCorners` the
operator `(1-q)^{#T} Ξ_{π,T}` is the signed sum of the plain words of the flips `π_S`, each of which
is a square Dyck path of length `n` by `HJO.Dyck.IsSquareDyck.flipCorners`; applying `hthm44` to
each turns that into the signed sum of the unmarked series `χ(π_S)`, which is `(1-q)^{#T} χ(π, T)`
by `HJO.Dyck.pathMarkedCharSeries_inclusion_exclusion`. The scalar cancels, `q ≠ 1`.

`q ≠ 1` cannot be dropped: at `q = 1` the left-hand side is `0` for
every `T` marking a corner, the corner factor `HJO.Sweep.cmCorner` being `0⁻¹ • (⋯) = 0`, while the
right-hand side counts the labellings marked by `T`. -/
theorem map_constantCoeff_markedWordOp_one_eq_pathMarkedCharSeries (q : L) (hx : IsSquareDyck n x)
    (hT : T ⊆ Dyck.corner x) (hq : q ≠ 1) {ι : Sym.Lambda L →ₐ[L] Sym.AlphabetSeries L}
    (hthm44 : ∀ y : Fin n → ℕ, IsSquareDyck n y →
      ι (MvPolynomial.constantCoeff (markedWordOp q y ∅ (1 : Total L)))
        = pathMarkedCharSeries q y ∅) :
    ι (MvPolynomial.constantCoeff (markedWordOp q x T (1 : Total L)))
      = pathMarkedCharSeries q x T := by
  have hne : (1 - q) ^ #T ≠ 0 := pow_ne_zero _ (sub_ne_zero.2 (Ne.symm hq))
  have key : (1 - q) ^ #T • ι (MvPolynomial.constantCoeff (markedWordOp q x T (1 : Total L)))
      = (1 - q) ^ #T • pathMarkedCharSeries q x T := by
    have h1 : (1 - q) ^ #T • ι (MvPolynomial.constantCoeff (markedWordOp q x T (1 : Total L)))
        = ι (MvPolynomial.constantCoeff
            (((1 - q) ^ #T • markedWordOp q x T) (1 : Total L))) := by
      rw [LinearMap.smul_apply, MvPolynomial.constantCoeff_smul, map_smul]
    have h2 : ((1 - q) ^ #T • markedWordOp q x T) (1 : Total L)
        = ∑ S ∈ T.powerset,
            ((-1 : L) ^ #S • markedWordOp q (flipCorners x S) ∅) (1 : Total L) := by
      rw [← sum_powerset_smul_markedWordOp_flipCorners q hx hT hq, LinearMap.sum_apply]
    rw [h1, h2, map_sum, map_sum, pathMarkedCharSeries_inclusion_exclusion q hx hT]
    refine Finset.sum_congr rfl fun S hS => ?_
    rw [LinearMap.smul_apply, MvPolynomial.constantCoeff_smul, map_smul,
      hthm44 _ (hx.flipCorners ((Finset.mem_powerset.1 hS).trans hT))]
  calc ι (MvPolynomial.constantCoeff (markedWordOp q x T (1 : Total L)))
      = ((1 - q) ^ #T)⁻¹ • ((1 - q) ^ #T •
          ι (MvPolynomial.constantCoeff (markedWordOp q x T (1 : Total L)))) := by
        rw [smul_smul, inv_mul_cancel₀ hne, one_smul]
    _ = ((1 - q) ^ #T)⁻¹ • ((1 - q) ^ #T • pathMarkedCharSeries q x T) := by rw [key]
    _ = pathMarkedCharSeries q x T := by rw [smul_smul, inv_mul_cancel₀ hne, one_smul]

end HJO.Sweep
