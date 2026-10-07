/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.Shuffle.Mellit
public import HJO.Shuffle.Sweep
public meta import HJO.Attr

/-! # The standardisation bijection, and the two forms of the right-hand side

`HJO.Mellit.sum_sweepChar_eq_sum_gessel` is proved here: the sum over the above-diagonal
`(aN, bN)`-paths of return composition `α` of `u^{ârea} q^{ĥ - max t̂dinv} χ(P̂)` equals the sum
over `PF̂^α_{aN,bN}` of `q^{d̂inv} u^{ârea} F_{bN, îdes^{∨bN}}`. Both sides are elements of `𝒫`, the
left of characteristic functions of paths (`HJO.Paths.sweepChar`) and the right of fundamental
quasisymmetric functions (`HJO.ParkingFunctions.gessel`), so no realisation occurs and none is
needed.

The content is the *standardisation bijection*, the argument used inside the proof of
`HJO.Mellit.eq_sum_sweepChar_of_eq_sum_gessel`. Grouping the parking functions of the right-hand
side by their underlying path reduces the claim to one identity per path,
`HJO.ParkingFunctions.sweepChar_eq_sum_gessel`, and that identity is a bijection between the words
`HJO.Paths.sweepChar` sums over and the labellings of the path.

## The bijection

Fix an above-diagonal path `y` with `bN` north steps, indexed by the height of their feet, and let
`R` be the above-diagonal rank of a north step. `HJO.Paths.stepRank_injective` says `R` is injective
as soon as `0 < a`, so the letters of a word `w` on the north steps, ties broken by `R`, are a
strict total order `HJO.Sym.LetterLt`, and `HJO.Sym.wordLabel` -- the number of north steps
carrying a strictly larger letter -- is the bijection reversing it. That is the map
`r ↦ bN + 1 - std(w)_r`, the standardisation read `0`-based and complemented.

The tie-break is by **rank**, not by the height index. The two differ: the height indexing of this
library is not the rank-order listing, and on a pair of north steps carrying equal
letters the two standardisations disagree. Only the rank tie-break works, because the pairs the
argument must control -- `HJO.Paths.sweepAttack` and `HJO.Paths.sweepMarked` -- are rank-increasing
(`HJO.Paths.stepRank_lt_of_mem_sweepAttack`, `HJO.Paths.stepRank_lt_of_mem_sweepMarked`) and are not
index-increasing. `HJO.Paths.standardisation` breaks ties by the index and is therefore not what
appears below; that is a fact about the transport of the index set, recorded in the docstring of
`HJO.Paths.sweepAttack`, and not a defect of either definition.

Three facts carry the argument, each stated for an arbitrary injective `R`:

* `HJO.Sym.wordLabel_apply_of_step`: a listing of the north steps along which the letter decreases
  at every single step *is* the inverse of `wordLabel`. This is what turns a labelling back into a
  word.
* `HJO.Sym.eq_of_wordLabel_eq`: a word is recovered from the labelling it induces together with its
  exponent vector, because listed in decreasing order of label it is weakly increasing.
* `HJO.Sym.letterLt_iff_le`: the comparison in the form the ascending-word condition produces it.

On the path side, `HJO.ParkingFunctions.isAscendingWord_gesselWord_iff` identifies the two: the
word read off `w` in decreasing order of label is an ascending word for `îdes(π̂)^{∨bN}` exactly
when `w` induces the labelling of `π̂`. Combined with
`HJO.ParkingFunctions.coeff_gessel_eq_ite` -- a coefficient of `F_{bN,S}` is the indicator of the
exponent vectors of `S`-ascending words -- this is the bijection, coefficient by coefficient.

Two further inputs match the statistics. `HJO.ParkingFunctions.aboveTdinv_eq_card_sweepAttack` is
the opening computation of `HJO.Paths.aboveMaxTdinv_eq_card_sweepAttack`: `t̂dinv(π̂)` counts the
attacking pairs of north steps on which the label increases. And
`HJO.ParkingFunctions.card_sweepAttack_eq_aboveTdinv` turns that into the exponent of `q` in
`HJO.Paths.sweepChar`, the tie-breaking clause of `LetterLt` never firing on an attacking pair
because such a pair has its ranks in increasing order.

## What the hypotheses are

`0 < a` is what survives of the global standing hypothesis `1 < a < b`, and it is where the
injectivity of the rank comes from; without it the reading order has ties and there is no bijection.

`q ≠ 0` is spent at exactly one step, and it is not removable. Splitting
`q^{ĥ - max t̂dinv} q^{t̂dinv}` into `q^{ĥ + t̂dinv - max t̂dinv} = q^{d̂inv}` is `zpow_add₀`, and
the exponent `ĥ(P̂) - max t̂dinv(P̂)` is a genuine negative integer: by
`HJO.Paths.aboveMaxTdinv_eq_card_sweepAttack` the subtrahend is `#𝒜(P̂)`, which exceeds `ĥ(P̂)` on
every above-diagonal path of every rectangle except the one hugging the top edge, where both vanish.
So the two sides of the identity do *not* agree at `q = 0`, and the hypothesis is about the
mathematics rather than about the encoding. The standing coefficient field `𝕜 = ℚ(q,u)` supplies
it -- `q` and `u` are indeterminates, hence invertible -- and the identity as usually written
leaves it implicit.

The hypotheses `N ≥ 1` and "`α` is a composition of `N`" of the identity as usually written turn
out to be unnecessary: both index sets are cut out by `HJO.Paths.HasAboveReturns`, which already
carries them, so the identity is vacuous rather than false when they fail.
`HJO.Mellit.sum_sweepChar_eq_sum_gessel` therefore omits them.

## What is *not* proved here

`HJO.Mellit.RhsSumsAgree` is a statement about an arbitrary `HJO.Mellit.SweepSystem`, whose
characteristic function `χ` is opaque data; a system with `χ = 0` refutes it, which is exactly why
the clause is the interface's anti-vacuity guard. What is proved is
`HJO.Mellit.rhsSumsAgree_of_chi_eq_sweepChar`: the clause holds of every sweep system whose `χ` is
`HJO.Paths.sweepChar`. That is the whole content of the statement; the remaining clauses of
`HJO.Mellit.MellitInput` are `LhsRewrite`, `MellitInduction` and `Rem41`.

## References

The lemma `HJO.Mellit.sum_sweepChar_eq_sum_gessel`, which supplies the reduction used inside the
proof of `HJO.Mellit.eq_sum_sweepChar_of_eq_sum_gessel`; the definitions
`HJO.Paths.sweepChar`, `HJO.Paths.sweepAttack`, `HJO.Paths.sweepMarked`,
`HJO.Paths.standardisation`, `HJO.ParkingFunctions.gessel`,
`HJO.ParkingFunctions.AboveParkingFunction`, `HJO.ParkingFunctions.aboveDinv`,
`HJO.ParkingFunctions.aboveTdinv`, `HJO.ParkingFunctions.aboveIdes`,
`HJO.ParkingFunctions.aboveMaxTdinv`, `HJO.ParkingFunctions.descentReverse`; and the lemma
`HJO.Paths.aboveMaxTdinv_eq_card_sweepAttack`. -/

@[expose] public section

open Finset

namespace HJO.Sym

/-! ### Words ordered by letter, ties broken by a rank -/

variable {n : ℕ}

/-- The position `s` carries a smaller letter of the word `w` than the position `t` does, ties
broken by the auxiliary rank `R`. For injective `R` this is a strict total order on the
positions. -/
def LetterLt (R : Fin n → ℤ) (w : Fin n → ℕ) (s t : Fin n) : Prop :=
  w s < w t ∨ (w s = w t ∧ R s < R t)

instance instDecidableLetterLt (R : Fin n → ℤ) (w : Fin n → ℕ) (s t : Fin n) :
    Decidable (LetterLt R w s t) := by unfold LetterLt; infer_instance

variable {R : Fin n → ℤ} {w : Fin n → ℕ}

theorem letterLt_irrefl (s : Fin n) : ¬ LetterLt R w s s := by
  rintro (h | ⟨-, h⟩) <;> exact absurd h (lt_irrefl _)

theorem letterLt_trans {s t u : Fin n} (h₁ : LetterLt R w s t) (h₂ : LetterLt R w t u) :
    LetterLt R w s u := by
  rcases h₁ with h₁ | ⟨he₁, h₁⟩ <;> rcases h₂ with h₂ | ⟨he₂, h₂⟩
  · exact Or.inl (h₁.trans h₂)
  · exact Or.inl (he₂ ▸ h₁)
  · exact Or.inl (he₁ ▸ h₂)
  · exact Or.inr ⟨he₁.trans he₂, h₁.trans h₂⟩

theorem letterLt_asymm {s t : Fin n} (h : LetterLt R w s t) : ¬ LetterLt R w t s :=
  fun h' => letterLt_irrefl s (letterLt_trans h h')

theorem letterLt_total (hR : Function.Injective R) {s t : Fin n} (hst : s ≠ t) :
    LetterLt R w s t ∨ LetterLt R w t s := by
  rcases lt_trichotomy (w s) (w t) with h | h | h
  · exact Or.inl (Or.inl h)
  · rcases lt_trichotomy (R s) (R t) with h' | h' | h'
    · exact Or.inl (Or.inr ⟨h, h'⟩)
    · exact absurd (hR h') hst
    · exact Or.inr (Or.inr ⟨h.symm, h'⟩)
  · exact Or.inr (Or.inl h)

/-! ### The label of a position -/

/-- The number of positions carrying a strictly larger letter than `s` does, ties broken by `R`.
This is the `0`-based label the standardisation argument attaches to `s`: the position carrying the
largest letter gets `0`, and `HJO.Sym.wordLabel` packages it as an element of `Fin n`. -/
def labelCount (R : Fin n → ℤ) (w : Fin n → ℕ) (s : Fin n) : ℕ :=
  #{t ∈ (univ : Finset (Fin n)) | LetterLt R w s t}

theorem labelCount_lt (s : Fin n) : labelCount R w s < n := by
  have h : {t ∈ (univ : Finset (Fin n)) | LetterLt R w s t} ⊂ univ := by
    refine ⟨filter_subset _ _, fun hsub => ?_⟩
    have := (mem_filter.1 (hsub (mem_univ s))).2
    exact letterLt_irrefl s this
  simpa [labelCount] using card_lt_card h

/-- The `0`-based label of the position `s`: the number of positions carrying a strictly larger
letter, ties broken by `R`. It reverses the order `HJO.Sym.LetterLt`. -/
def wordLabel (R : Fin n → ℤ) (w : Fin n → ℕ) (s : Fin n) : Fin n :=
  ⟨labelCount R w s, labelCount_lt s⟩

theorem wordLabel_lt_iff {s t : Fin n} :
    wordLabel R w s < wordLabel R w t ↔ labelCount R w s < labelCount R w t := Iff.rfl

theorem labelCount_lt_labelCount_of_letterLt {s t : Fin n} (h : LetterLt R w t s) :
    labelCount R w s < labelCount R w t := by
  refine card_lt_card ⟨fun u hu => ?_, fun hsub => ?_⟩
  · rw [mem_filter] at hu ⊢
    exact ⟨mem_univ u, letterLt_trans h hu.2⟩
  · have := (mem_filter.1 (hsub (mem_filter.2 ⟨mem_univ s, h⟩))).2
    exact letterLt_irrefl s this

theorem wordLabel_lt_wordLabel_iff (hR : Function.Injective R) {s t : Fin n} :
    wordLabel R w s < wordLabel R w t ↔ LetterLt R w t s := by
  rw [wordLabel_lt_iff]
  refine ⟨fun h => ?_, fun h => labelCount_lt_labelCount_of_letterLt h⟩
  by_cases hst : s = t
  · exact absurd (hst ▸ h) (lt_irrefl _)
  rcases letterLt_total (w := w) hR (Ne.symm hst) with h' | h'
  · exact h'
  · exact absurd (labelCount_lt_labelCount_of_letterLt h') (by omega)

theorem wordLabel_injective (hR : Function.Injective R) :
    Function.Injective (wordLabel R w) := by
  intro s t hst
  have hst' : labelCount R w s = labelCount R w t := congrArg Fin.val hst
  by_cases h : s = t
  · exact h
  rcases letterLt_total (w := w) hR h with h' | h'
  · exact absurd (labelCount_lt_labelCount_of_letterLt h') (by omega)
  · exact absurd (labelCount_lt_labelCount_of_letterLt h') (by omega)

theorem wordLabel_bijective (hR : Function.Injective R) :
    Function.Bijective (wordLabel R w) :=
  (Finite.injective_iff_bijective).1 (wordLabel_injective hR)

/-- The comparison `HJO.Sym.LetterLt` in the form the ascending-word condition produces it: a weak
inequality between the letters, made strict where the rank disagrees. The two positions must be
distinct, `LetterLt` being irreflexive where the right-hand side is not. -/
theorem letterLt_iff_le (hR : Function.Injective R) {s t : Fin n} (hst : t ≠ s) :
    LetterLt R w t s ↔ w t ≤ w s ∧ (R s < R t → w t < w s) := by
  refine ⟨fun h => ?_, fun ⟨hle, himp⟩ => ?_⟩
  · rcases h with h | ⟨he, h⟩
    · exact ⟨le_of_lt h, fun _ => h⟩
    · exact ⟨le_of_eq he, fun h' => absurd (h.trans h') (lt_irrefl _)⟩
  · rcases lt_or_eq_of_le hle with h | h
    · exact Or.inl h
    · refine Or.inr ⟨h, ?_⟩
      have h1 : ¬ R s < R t := fun h' => absurd (himp h') (by omega)
      have h2 : R t ≠ R s := fun h' => hst (hR h')
      omega

/-- Reading the letters of a word in another order does not change its exponent vector. -/
theorem wordExponent_comp_bijective {w : Fin n → ℕ} {e : Fin n → Fin n}
    (he : Function.Bijective e) : wordExponent (w ∘ e) = wordExponent w :=
  Fintype.sum_bijective e he _ _ fun _ => rfl

/-! ### The label is the only order-reversing listing -/

/-- A listing of the positions along which the letter decreases at every single step decreases
along every step: this is transitivity of `HJO.Sym.LetterLt` run along the listing. -/
theorem letterLt_of_lt_of_step {g : Fin n → Fin n}
    (hstep : ∀ k l : Fin n, (k : ℕ) + 1 = (l : ℕ) → LetterLt R w (g l) (g k))
    {k l : Fin n} (hkl : k < l) : LetterLt R w (g l) (g k) := by
  have key : ∀ d : ℕ, ∀ k l : Fin n, (l : ℕ) = (k : ℕ) + d + 1 → LetterLt R w (g l) (g k) := by
    intro d
    induction d with
    | zero => intro k l hl; exact hstep k l (by omega)
    | succ d ih =>
      intro k l hl
      have hm : (k : ℕ) + d + 1 < n := by omega
      exact letterLt_trans (hstep ⟨(k : ℕ) + d + 1, hm⟩ l (by simp only; omega))
        (ih k ⟨(k : ℕ) + d + 1, hm⟩ (by simp only))
  exact key ((l : ℕ) - (k : ℕ) - 1) k l (by omega)

/-- **The order-reversing listing is the labelling.** If `g` lists the positions so that the
letter of `w` decreases at every single step, then `g` is inverse to `HJO.Sym.wordLabel`: the
position `g k` carries the label `k`. This is the uniqueness half of the standardisation argument,
and it is what lets a labelling of a path be turned back into a word. -/
theorem wordLabel_apply_of_step {g : Fin n → Fin n}
    (hg : Function.Injective g)
    (hstep : ∀ k l : Fin n, (k : ℕ) + 1 = (l : ℕ) → LetterLt R w (g l) (g k)) (k : Fin n) :
    wordLabel R w (g k) = k := by
  have hbij : Function.Bijective g := (Finite.injective_iff_bijective).1 hg
  have hset : {t ∈ (univ : Finset (Fin n)) | LetterLt R w (g k) t}
      = ({j ∈ (univ : Finset (Fin n)) | j < k}).image g := by
    ext t
    simp only [mem_filter, mem_univ, true_and, mem_image]
    refine ⟨fun ht => ?_, ?_⟩
    · obtain ⟨j, rfl⟩ := hbij.2 t
      refine ⟨j, ?_, rfl⟩
      rcases lt_trichotomy j k with h | h | h
      · exact h
      · exact absurd (h ▸ ht) (letterLt_irrefl _)
      · exact absurd ht (letterLt_asymm (letterLt_of_lt_of_step hstep h))
    · rintro ⟨j, hj, rfl⟩
      exact letterLt_of_lt_of_step hstep hj
  have hcard : labelCount R w (g k) = (k : ℕ) := by
    rw [labelCount, hset, card_image_of_injective _ hg,
      show {j ∈ (univ : Finset (Fin n)) | j < k} = Iio k by ext j; simp, Fin.card_Iio]
  exact Fin.ext hcard

/-- **A word is recovered from the labelling it induces together with its exponent vector.** Listed
in decreasing order of label a word is weakly increasing, and a weakly increasing word is determined
by its exponent vector. This is the injectivity half of the standardisation bijection. -/
theorem eq_of_wordLabel_eq (hR : Function.Injective R) {w w' : Fin n → ℕ}
    (hlab : wordLabel R w = wordLabel R w') (hd : wordExponent w = wordExponent w') : w = w' := by
  set g := Fintype.bijInv (wordLabel_bijective (w := w) hR) with hg
  have hgw : ∀ k, wordLabel R w (g k) = k := Fintype.rightInverse_bijInv _
  have hgw' : ∀ k, wordLabel R w' (g k) = k := fun k => by rw [← hlab]; exact hgw k
  have hgbij : Function.Bijective g :=
    Fintype.bijective_bijInv (wordLabel_bijective (w := w) hR)
  have hmono : ∀ v : Fin n → ℕ, (∀ k, wordLabel R v (g k) = k) →
      Monotone fun k => v (g (Fin.rev k)) := by
    intro v hv
    refine monotone_of_le_succ fun K L hKL => ?_
    have hrev : ((Fin.rev L : Fin n) : ℕ) + 1 = ((Fin.rev K : Fin n) : ℕ) := by
      have := L.2
      rw [Fin.val_rev, Fin.val_rev]
      omega
    have hlt : wordLabel R v (g (Fin.rev L)) < wordLabel R v (g (Fin.rev K)) := by
      rw [hv, hv]
      exact Fin.lt_def.2 (by omega)
    rcases (wordLabel_lt_wordLabel_iff hR).1 hlt with h | ⟨h, -⟩
    · exact le_of_lt h
    · exact le_of_eq h
  have hcomp : (fun k => w (g (Fin.rev k))) = fun k => w' (g (Fin.rev k)) := by
    refine eq_of_monotone_of_wordExponent_eq (hmono w hgw) (hmono w' hgw') ?_
    have hbij : Function.Bijective fun k : Fin n => g (Fin.rev k) :=
      hgbij.comp Fin.rev_bijective
    have h1 : wordExponent (fun k => w (g (Fin.rev k))) = wordExponent w :=
      wordExponent_comp_bijective hbij
    have h2 : wordExponent (fun k => w' (g (Fin.rev k))) = wordExponent w' :=
      wordExponent_comp_bijective hbij
    rw [h1, h2, hd]
  funext s
  obtain ⟨k, hk⟩ := (hgbij.comp Fin.rev_bijective).2 s
  rw [Function.comp_apply] at hk
  have hck := congrFun hcomp k
  rw [hk] at hck
  exact hck

end HJO.Sym

namespace HJO.Paths

open ParkingFunctions

variable {a b N : ℕ}

/-! ### The column of a north step, and the injectivity of its rank -/

/-- The abscissa `Â_j` at which the path is last below the height `j` grows with `j`: the
condition `ŷ_r < j` it maximises over gets weaker as `j` grows. -/
theorem lastBelow_mono (y : Heights a b N) : Monotone (lastBelow y) :=
  fun _ _ h => Nat.findGreatest_mono (fun _ hr => lt_of_lt_of_le hr h) le_rfl

/-- The column of the north step at height `i` grows with `i`: a north step higher up is weakly
further to the right. -/
theorem aboveColumn_mono (y : Heights a b N) : Monotone (aboveColumn y) :=
  fun _ _ h => lastBelow_mono y (Nat.succ_le_succ h)

/-- The north steps of one column occupy an interval of heights: a step between two steps of the
same column is in that column too. -/
theorem aboveColumn_eq_of_between {y : Heights a b N} {i j k : ℕ} (hik : i ≤ k) (hkj : k ≤ j)
    (h : aboveColumn y i = aboveColumn y j) : aboveColumn y k = aboveColumn y i :=
  le_antisymm (h ▸ aboveColumn_mono y hkj) (aboveColumn_mono y hik)

/-- Membership in the attack set: the two ranks lie within the window of each other, the lower
index of the pair carrying the smaller rank. -/
@[simp]
theorem mem_sweepAttack {y : Heights a b N} {p : Fin (b * N) × Fin (b * N)} :
    p ∈ sweepAttack y ↔ stepRank y p.1 < stepRank y p.2 ∧
      stepRank y p.2 < stepRank y p.1 + attackWindow a N := by
  rw [sweepAttack, mem_filter]
  exact and_iff_right (mem_univ p)

/-- Membership in the marked pairs: the two feet share a column and are vertically adjacent. -/
@[simp]
theorem mem_sweepMarked {y : Heights a b N} {p : Fin (b * N) × Fin (b * N)} :
    p ∈ sweepMarked y ↔ aboveColumn y (p.2 : ℕ) = aboveColumn y (p.1 : ℕ) ∧
      (p.2 : ℕ) = (p.1 : ℕ) + 1 := by
  rw [sweepMarked, mem_filter]
  exact and_iff_right (mem_univ p)

/-- **The above-diagonal ranks of distinct north steps differ.** This is
`HJO.ParkingFunctions.stepRank_injective` on the above-diagonal side, read on the height indexing:
the rank `(aN+1)N(ai - bx) + x` of the step at height `i` in the column `x` determines `x` modulo
`(aN+1)N`, which exceeds `aN ≥ x`, and then determines `i` because `a > 0`.

No above-diagonality is used: the only fact about the column needed is
`HJO.ParkingFunctions.aboveColumn_le`, and `0 < N` comes free from the index type being
inhabited. -/
theorem stepRank_injective (ha : 0 < a) (y : Heights a b N) :
    Function.Injective (stepRank y) := by
  intro i j hij
  have hbN : 0 < b * N := i.pos
  have hN : 0 < N := Nat.pos_of_ne_zero fun h0 => by simp [h0] at hbN
  set W : ℤ := ((a : ℤ) * N + 1) * N with hW
  have hWpos : (0 : ℤ) < W := by
    have : (0 : ℤ) < (N : ℤ) := by exact_mod_cast hN
    positivity
  have hWgt : (a : ℤ) * N < W := by
    have h1 : (1 : ℤ) ≤ (N : ℤ) := by exact_mod_cast hN
    have h2 : (0 : ℤ) ≤ (a : ℤ) * N := by positivity
    nlinarith
  have hxi : ((aboveColumn y (i : ℕ) : ℕ) : ℤ) ≤ (a : ℤ) * N := by
    have := aboveColumn_le y (i : ℕ)
    have h' : ((aboveColumn y (i : ℕ) : ℕ) : ℤ) ≤ ((a * N : ℕ) : ℤ) := by exact_mod_cast this
    push_cast at h'
    exact h'
  have hxj : ((aboveColumn y (j : ℕ) : ℕ) : ℤ) ≤ (a : ℤ) * N := by
    have := aboveColumn_le y (j : ℕ)
    have h' : ((aboveColumn y (j : ℕ) : ℕ) : ℤ) ≤ ((a * N : ℕ) : ℤ) := by exact_mod_cast this
    push_cast at h'
    exact h'
  have h0i : (0 : ℤ) ≤ ((aboveColumn y (i : ℕ) : ℕ) : ℤ) := Int.natCast_nonneg _
  have h0j : (0 : ℤ) ≤ ((aboveColumn y (j : ℕ) : ℕ) : ℤ) := Int.natCast_nonneg _
  simp only [stepRank, abovePointRank] at hij
  set xi : ℤ := ((aboveColumn y (i : ℕ) : ℕ) : ℤ) with hxidef
  set xj : ℤ := ((aboveColumn y (j : ℕ) : ℕ) : ℤ) with hxjdef
  set u : ℤ := (a : ℤ) * (i : ℕ) - (b : ℤ) * xi with hu
  set v : ℤ := (a : ℤ) * (j : ℕ) - (b : ℤ) * xj with hv
  have hkey : W * u + xi = W * v + xj := hij
  have huv : u = v := by
    rcases lt_trichotomy u v with h | h | h
    · exfalso
      have h1 : u + 1 ≤ v := by omega
      nlinarith
    · exact h
    · exfalso
      have h1 : v + 1 ≤ u := by omega
      nlinarith
  have hx : xi = xj := by rw [huv] at hkey; omega
  have hai : (a : ℤ) * (i : ℕ) = (a : ℤ) * (j : ℕ) := by
    rw [hu, hv, hx] at huv; omega
  have hapos : (0 : ℤ) < (a : ℤ) := by exact_mod_cast ha
  have : ((i : ℕ) : ℤ) = ((j : ℕ) : ℤ) := by
    rcases mul_left_cancel₀ (ne_of_gt hapos) hai with h
    exact h
  exact Fin.ext (by exact_mod_cast this)

end HJO.Paths

namespace HJO.ParkingFunctions

open Paths

variable {a b N : ℕ}

/-! ### The reading order of an arbitrary above-diagonal parking function -/

/-- The rank of a north step of a parking function is the rank of that step of its path. -/
theorem aboveStepRank_eq_stepRank (π : AboveParkingFunction a b N) (i : Fin (b * N)) :
    aboveStepRank π i = Paths.stepRank (abovePath π) i := rfl

/-- The rank function of a parking function is that of its path. -/
theorem aboveStepRank_eq (π : AboveParkingFunction a b N) :
    aboveStepRank π = Paths.stepRank (abovePath π) := rfl

/-- **The ranks of distinct north steps of an above-diagonal parking function differ.** -/
theorem aboveStepRank_injective (ha : 0 < a) (π : AboveParkingFunction a b N) :
    Function.Injective (aboveStepRank π) :=
  Paths.stepRank_injective ha (abovePath π)

/-- For `0 < a` the tie-breaking clause of `AboveReadBefore` never fires: the step with the larger
above-diagonal rank is read first, full stop. This is the general form of
`HJO.ParkingFunctions.readBefore_iff`, which is stated for a half turn. -/
theorem aboveReadBefore_iff' (ha : 0 < a) (π : AboveParkingFunction a b N) (s t : Fin (b * N)) :
    AboveReadBefore π s t ↔ aboveStepRank π t < aboveStepRank π s := by
  refine ⟨fun h => h.elim id fun ⟨h1, h2⟩ => ?_, Or.inl⟩
  exact absurd (aboveStepRank_injective ha π h1) (ne_of_lt h2)

theorem aboveReadBefore_irrefl' (ha : 0 < a) (π : AboveParkingFunction a b N) (s : Fin (b * N)) :
    ¬ AboveReadBefore π s s := by rw [aboveReadBefore_iff' ha]; exact lt_irrefl _

theorem aboveReadBefore_trans' (ha : 0 < a) (π : AboveParkingFunction a b N)
    (s t u : Fin (b * N)) :
    AboveReadBefore π s t → AboveReadBefore π t u → AboveReadBefore π s u := by
  rw [aboveReadBefore_iff' ha, aboveReadBefore_iff' ha, aboveReadBefore_iff' ha]
  exact fun h1 h2 => h2.trans h1

theorem aboveReadBefore_total' (ha : 0 < a) (π : AboveParkingFunction a b N) (s t : Fin (b * N))
    (hst : s ≠ t) : AboveReadBefore π s t ∨ AboveReadBefore π t s := by
  rw [aboveReadBefore_iff' ha, aboveReadBefore_iff' ha]
  rcases lt_trichotomy (aboveStepRank π s) (aboveStepRank π t) with h | h | h
  · exact Or.inr h
  · exact absurd (aboveStepRank_injective ha π h) hst
  · exact Or.inl h

/-- **Membership in `ideŝ` for an arbitrary above-diagonal parking function.** For `1 ≤ i < bN`,
the index `i` is an inverse descent of `π̂` exactly when the north step carrying the label `i + 1`
is read before the one carrying the label `i`. This is
`HJO.ParkingFunctions.mem_aboveIdes_iff` with the half turn removed. -/
theorem mem_aboveIdes_iff' (ha : 0 < a) (π : AboveParkingFunction a b N) {i : ℕ} (hi1 : 1 ≤ i)
    (hi2 : i < b * N) :
    i ∈ aboveIdes π ↔
      AboveReadBefore π (aboveLabelStep π ⟨i, hi2⟩) (aboveLabelStep π ⟨i - 1, by omega⟩) := by
  have hne : aboveLabelStep π ⟨i, hi2⟩ ≠ aboveLabelStep π ⟨i - 1, by omega⟩ := by
    intro h
    have h2 : (⟨i, hi2⟩ : Fin (b * N)) = ⟨i - 1, by omega⟩ := by
      rw [← aboveLabel_aboveLabelStep π ⟨i, hi2⟩, ← aboveLabel_aboveLabelStep π ⟨i - 1, by omega⟩,
        h]
    have h3 : i = i - 1 := by simpa using congrArg Fin.val h2
    omega
  have e1 : (aboveLabel π (aboveLabelStep π ⟨i, hi2⟩) : ℕ) + 1 = i + 1 := by
    rw [aboveLabel_aboveLabelStep]
  have e2 : (aboveLabel π (aboveLabelStep π ⟨i - 1, by omega⟩) : ℕ) + 1 = i := by
    rw [aboveLabel_aboveLabelStep]; simp only; omega
  rw [aboveIdes, mem_filter, mem_Ico, aboveReadingWord,
    ← List.idxOf_lt_idxOf_map_mergeSort_iff (AboveReadBefore π)
      (injective_aboveReadingLetter π) (aboveReadBefore_irrefl' ha π)
      (aboveReadBefore_trans' ha π) (aboveReadBefore_total' ha π) hne, e1, e2]
  exact and_iff_right ⟨hi1, hi2⟩

/-- **The inverse descent set as a rank comparison.** For `1 ≤ i < bN`, the index `i` is an
inverse descent of `π̂` exactly when the step carrying the label `i` has the smaller rank of the
two steps carrying the labels `i` and `i + 1`. -/
theorem mem_aboveIdes_iff_stepRank (ha : 0 < a) (π : AboveParkingFunction a b N) {i : ℕ}
    (hi1 : 1 ≤ i) (hi2 : i < b * N) :
    i ∈ aboveIdes π ↔ aboveStepRank π (aboveLabelStep π ⟨i - 1, by omega⟩) <
      aboveStepRank π (aboveLabelStep π ⟨i, hi2⟩) := by
  rw [mem_aboveIdes_iff' ha π hi1 hi2, aboveReadBefore_iff' ha]

/-! ### `tdinv̂` counts the attacking pairs on which the label increases -/

/-- **`tdinv̂(π̂)` is the number of attacking pairs of north steps whose labels increase.** The
proof of `HJO.Paths.aboveMaxTdinv_eq_card_sweepAttack` opens with exactly this computation:
indexing the pairs of labels `(i, j)` by the pairs of north steps `(s, t)` they mark, the middle
inequality of `HJO.ParkingFunctions.aboveTdinv` becomes the attacking condition of
`HJO.Paths.sweepAttack` and the condition `i < j` becomes the increase of the label. -/
theorem aboveTdinv_eq_card_sweepAttack (π : AboveParkingFunction a b N) :
    aboveTdinv π =
      #{p ∈ Paths.sweepAttack (abovePath π) | aboveLabel π p.1 < aboveLabel π p.2} := by
  have hmem : ∀ p : Fin (b * N) × Fin (b * N),
      p ∈ {p ∈ (univ : Finset (Fin (b * N) × Fin (b * N))) | p.1 < p.2 ∧
          aboveLabelRank π p.1 < aboveLabelRank π p.2 ∧
          aboveLabelRank π p.2 < aboveLabelRank π p.1 + (a * N + 1) * (a * N)} ↔
        p.1 < p.2 ∧ aboveLabelRank π p.1 < aboveLabelRank π p.2 ∧
          aboveLabelRank π p.2 < aboveLabelRank π p.1 + (a * N + 1) * (a * N) :=
    fun p => by rw [mem_filter]; exact and_iff_right (mem_univ p)
  have hmem' : ∀ p : Fin (b * N) × Fin (b * N),
      p ∈ {p ∈ Paths.sweepAttack (abovePath π) | aboveLabel π p.1 < aboveLabel π p.2} ↔
        (aboveStepRank π p.1 < aboveStepRank π p.2 ∧
            aboveStepRank π p.2 < aboveStepRank π p.1 + (a * N + 1) * (a * N)) ∧
          aboveLabel π p.1 < aboveLabel π p.2 := by
    intro p
    rw [mem_filter, Paths.mem_sweepAttack, ← aboveStepRank_eq_stepRank,
      ← aboveStepRank_eq_stepRank, Paths.cast_attackWindow]
  rw [aboveTdinv]
  refine card_nbij' (fun p => (aboveLabelStep π p.1, aboveLabelStep π p.2))
    (fun p => (aboveLabel π p.1, aboveLabel π p.2)) (fun p hp => ?_) (fun p hp => ?_)
    (fun p _ => by simp) (fun p _ => by simp)
  · rw [Finset.mem_coe, hmem] at hp
    rw [Finset.mem_coe, hmem']
    simp only [aboveLabelRank] at hp
    exact ⟨⟨hp.2.1, hp.2.2⟩, by
      rw [aboveLabel_aboveLabelStep, aboveLabel_aboveLabelStep]; exact hp.1⟩
  · rw [Finset.mem_coe, hmem'] at hp
    rw [Finset.mem_coe, hmem]
    simp only [aboveLabelRank, aboveLabelStep_aboveLabel]
    exact ⟨hp.2, hp.1.1, hp.1.2⟩

/-! ### The labelling a word induces -/

/-- The word `w` on the north steps of `y` is *admissible*: its letters strictly decrease along
every marked pair, which is the condition `HJO.Paths.sweepChar` sums over. -/
def IsSweepAdmissible {a b N : ℕ} (y : Paths.Heights a b N) (w : Fin (b * N) → ℕ) : Prop :=
  ∀ p ∈ Paths.sweepMarked y, w p.2 < w p.1

/-- Along a column the letters of an admissible word decrease, so the label
`HJO.Sym.wordLabel` increases: this is the condition
`HJO.ParkingFunctions.IsAboveParkingLabelling` asks of a labelling. -/
theorem wordLabel_lt_wordLabel_of_aboveColumn_eq {a b N : ℕ} (ha : 0 < a)
    {y : Paths.Heights a b N} {w : Fin (b * N) → ℕ} (hw : IsSweepAdmissible y w)
    {s t : Fin (b * N)} (hst : s < t) (hcol : aboveColumn y (s : ℕ) = aboveColumn y (t : ℕ)) :
    Sym.wordLabel (Paths.stepRank y) w s < Sym.wordLabel (Paths.stepRank y) w t := by
  have hstep : ∀ u v : Fin (b * N), (u : ℕ) + 1 = (v : ℕ) → (s : ℕ) ≤ (u : ℕ) →
      (v : ℕ) ≤ (t : ℕ) → Sym.wordLabel (Paths.stepRank y) w u <
        Sym.wordLabel (Paths.stepRank y) w v := by
    intro u v huv hsu hvt
    have hcu : aboveColumn y (u : ℕ) = aboveColumn y (s : ℕ) :=
      Paths.aboveColumn_eq_of_between hsu (by omega) hcol
    have hcv : aboveColumn y (v : ℕ) = aboveColumn y (s : ℕ) :=
      Paths.aboveColumn_eq_of_between (by omega) hvt hcol
    have hmark : (u, v) ∈ Paths.sweepMarked y :=
      Paths.mem_sweepMarked.2 ⟨by rw [hcu, hcv], huv.symm⟩
    exact (Sym.wordLabel_lt_wordLabel_iff (w := w) (Paths.stepRank_injective ha y)).2
      (Or.inl (hw _ hmark))
  have key : ∀ d : ℕ, ∀ u v : Fin (b * N), (v : ℕ) = (u : ℕ) + d + 1 → (s : ℕ) ≤ (u : ℕ) →
      (v : ℕ) ≤ (t : ℕ) → Sym.wordLabel (Paths.stepRank y) w u <
        Sym.wordLabel (Paths.stepRank y) w v := by
    intro d
    induction d with
    | zero => intro u v hv hsu hvt; exact hstep u v (by omega) hsu hvt
    | succ d ih =>
      intro u v hv hsu hvt
      have hm : (u : ℕ) + d + 1 < b * N := by omega
      exact (ih u ⟨(u : ℕ) + d + 1, hm⟩ (by simp only) hsu (by simp only; omega)).trans
        (hstep ⟨(u : ℕ) + d + 1, hm⟩ v (by simp only; omega) (by simp only; omega) hvt)
  exact key ((t : ℕ) - (s : ℕ) - 1) s t (by omega) le_rfl le_rfl

/-- The labelling of the north steps of `y` an admissible word induces is an above-diagonal
parking labelling: it is a bijection by `HJO.Sym.wordLabel_bijective`, and it increases upwards
along each column because the letters decrease there. -/
theorem isAboveParkingLabelling_wordLabel {a b N : ℕ} (ha : 0 < a) {y : Paths.Heights a b N}
    {w : Fin (b * N) → ℕ} (hw : IsSweepAdmissible y w) :
    IsAboveParkingLabelling y (Sym.wordLabel (Paths.stepRank y) w) :=
  ⟨Sym.wordLabel_bijective (Paths.stepRank_injective ha y),
    fun _ _ hst hcol => wordLabel_lt_wordLabel_of_aboveColumn_eq ha hw hst hcol⟩

/-- **The above-diagonal parking function an admissible word labels the path with.** Its path is
`y` and its labelling is `HJO.Sym.wordLabel`: the north step carrying the largest letter gets the
label `1`. -/
def pfOfWord {a b N : ℕ} (ha : 0 < a) {y : Paths.Heights a b N} (hy : Paths.IsAboveDiagonal y)
    {w : Fin (b * N) → ℕ} (hw : IsSweepAdmissible y w) : AboveParkingFunction a b N :=
  ⟨(y, Sym.wordLabel (Paths.stepRank y) w), hy, isAboveParkingLabelling_wordLabel ha hw⟩

@[simp]
theorem abovePath_pfOfWord {a b N : ℕ} (ha : 0 < a) {y : Paths.Heights a b N}
    (hy : Paths.IsAboveDiagonal y) {w : Fin (b * N) → ℕ} (hw : IsSweepAdmissible y w) :
    abovePath (pfOfWord ha hy hw) = y := rfl

@[simp]
theorem aboveLabel_pfOfWord {a b N : ℕ} (ha : 0 < a) {y : Paths.Heights a b N}
    (hy : Paths.IsAboveDiagonal y) {w : Fin (b * N) → ℕ} (hw : IsSweepAdmissible y w) :
    aboveLabel (pfOfWord ha hy hw) = Sym.wordLabel (Paths.stepRank y) w := rfl

/-! ### The word a labelling reads, and the ascending-word condition -/

variable {a b N : ℕ}

theorem injective_aboveLabelStep (π : AboveParkingFunction a b N) :
    Function.Injective (aboveLabelStep π) :=
  Function.LeftInverse.injective (aboveLabel_aboveLabelStep π)

/-- **The word read in decreasing order of label.** The letters of `w` listed as the label runs
from `bN` down to `1`, which is the order the Gessel sequence of the standardisation argument reads
them in. -/
def gesselWord (π : AboveParkingFunction a b N) (w : Fin (b * N) → ℕ) (k : Fin (b * N)) : ℕ :=
  w (aboveLabelStep π (Fin.rev k))

/-- Reading the letters in another order does not change the exponent vector. -/
theorem wordExponent_gesselWord (π : AboveParkingFunction a b N) (w : Fin (b * N) → ℕ) :
    Sym.wordExponent (gesselWord π w) = Sym.wordExponent w := by
  simp only [Sym.wordExponent, gesselWord]
  exact Fintype.sum_bijective (fun k => aboveLabelStep π (Fin.rev k))
    (((injective_aboveLabelStep π).comp Fin.rev_injective).bijective_of_finite) _ _ fun _ => rfl

/-- The listing of the north steps by decreasing label runs down the letters of `w`, in the sense
of `HJO.Sym.LetterLt`. -/
def IsLabelDescending (π : AboveParkingFunction a b N) (w : Fin (b * N) → ℕ) : Prop :=
  ∀ k l : Fin (b * N), (k : ℕ) + 1 = (l : ℕ) →
    Sym.LetterLt (aboveStepRank π) w (aboveLabelStep π l) (aboveLabelStep π k)

/-- **The labelling `w` induces is `π̂`'s exactly when the letters run down the labels.** -/
theorem isLabelDescending_iff (ha : 0 < a) (π : AboveParkingFunction a b N)
    (w : Fin (b * N) → ℕ) :
    IsLabelDescending π w ↔
      aboveLabel π = Sym.wordLabel (aboveStepRank π) w := by
  refine ⟨fun h => ?_, fun h k l hkl => ?_⟩
  · funext s
    have hs := Sym.wordLabel_apply_of_step (w := w) (injective_aboveLabelStep π) h
      (aboveLabel π s)
    rw [aboveLabelStep_aboveLabel] at hs
    exact hs.symm
  · rw [← Sym.wordLabel_lt_wordLabel_iff (aboveStepRank_injective ha π), ← h,
      aboveLabel_aboveLabelStep, aboveLabel_aboveLabelStep]
    exact Fin.lt_def.2 (by omega)

/-- The descent set the Gessel sequence must respect, read as a rank comparison between the two
north steps the two consecutive labels mark. -/
theorem mem_descentReverse_aboveIdes_iff (ha : 0 < a) (π : AboveParkingFunction a b N)
    {K L : Fin (b * N)} (hKL : (K : ℕ) + 1 = (L : ℕ)) :
    (L : ℕ) ∈ descentReverse (b * N) (aboveIdes π) ↔
      aboveStepRank π (aboveLabelStep π (Fin.rev L)) <
        aboveStepRank π (aboveLabelStep π (Fin.rev K)) := by
  have hL := L.2
  have hrK : ((Fin.rev K : Fin (b * N)) : ℕ) = b * N - (K : ℕ) - 1 := by
    rw [Fin.val_rev]; omega
  have hrL : ((Fin.rev L : Fin (b * N)) : ℕ) = b * N - (L : ℕ) - 1 := by
    rw [Fin.val_rev]; omega
  have hi1 : 1 ≤ b * N - (L : ℕ) := by omega
  have hi2 : b * N - (L : ℕ) < b * N := by omega
  have hmem : (L : ℕ) ∈ descentReverse (b * N) (aboveIdes π) ↔ b * N - (L : ℕ) ∈ aboveIdes π := by
    rw [mem_descentReverse]
    refine ⟨fun ⟨j, hj, hji⟩ => ?_, fun h => ⟨b * N - (L : ℕ), h, by omega⟩⟩
    have := mem_Ico.1 (aboveIdes_subset π hj)
    have : j = b * N - (L : ℕ) := by omega
    rwa [this] at hj
  rw [hmem, mem_aboveIdes_iff_stepRank ha π hi1 hi2]
  have e1 : (⟨b * N - (L : ℕ), hi2⟩ : Fin (b * N)) = Fin.rev K :=
    Fin.ext (show b * N - (L : ℕ) = ((Fin.rev K : Fin (b * N)) : ℕ) by rw [hrK]; omega)
  have e2 : (⟨b * N - (L : ℕ) - 1, by omega⟩ : Fin (b * N)) = Fin.rev L :=
    Fin.ext (show b * N - (L : ℕ) - 1 = ((Fin.rev L : Fin (b * N)) : ℕ) by rw [hrL])
  rw [e1, e2]

/-- **The standardisation bijection, at one path.** The word read off `w` in decreasing order of
label is an ascending word for the reversed inverse descent set of `π̂` exactly when `w` induces
the labelling of `π̂`. This is the "the bijections `σ` with `σ_i > σ_j` for every
`(i,j) ∈ S(P̂)` are exactly the maps `r ↦ bN + 1 - ℓ(r)` for `ℓ` a labelling", together with its
identification of the descent set of a fixed standardisation. -/
theorem isAscendingWord_gesselWord_iff (ha : 0 < a) (π : AboveParkingFunction a b N)
    (w : Fin (b * N) → ℕ) :
    Sym.IsAscendingWord (b * N) (descentReverse (b * N) (aboveIdes π)) (gesselWord π w) ↔
      IsLabelDescending π w := by
  have hrev : ∀ K L : Fin (b * N), (K : ℕ) + 1 = (L : ℕ) →
      ((Fin.rev L : Fin (b * N)) : ℕ) + 1 = ((Fin.rev K : Fin (b * N)) : ℕ) := by
    intro K L hKL
    have := L.2
    rw [Fin.val_rev, Fin.val_rev]
    omega
  have hne : ∀ K L : Fin (b * N), (K : ℕ) + 1 = (L : ℕ) →
      aboveLabelStep π (Fin.rev K) ≠ aboveLabelStep π (Fin.rev L) := by
    intro K L hKL h
    have h' := congrArg Fin.val (Fin.rev_injective (injective_aboveLabelStep π h))
    have := hrev K L hKL
    omega
  have hpair : ∀ K L : Fin (b * N), (K : ℕ) + 1 = (L : ℕ) →
      ((gesselWord π w K ≤ gesselWord π w L ∧
          ((L : ℕ) ∈ descentReverse (b * N) (aboveIdes π) →
            gesselWord π w K < gesselWord π w L)) ↔
        Sym.LetterLt (aboveStepRank π) w (aboveLabelStep π (Fin.rev K))
          (aboveLabelStep π (Fin.rev L))) := by
    intro K L hKL
    rw [Sym.letterLt_iff_le (aboveStepRank_injective ha π) (hne K L hKL),
      mem_descentReverse_aboveIdes_iff ha π hKL]
    rfl
  refine ⟨fun hasc => ?_, fun hdesc => ?_⟩
  · intro k l hkl
    have hl := l.2
    have hKL : ((Fin.rev l : Fin (b * N)) : ℕ) + 1 = ((Fin.rev k : Fin (b * N)) : ℕ) := by
      rw [Fin.val_rev, Fin.val_rev]; omega
    have h := (hpair _ _ hKL).1 ⟨hasc.monotone (Fin.le_def.2 (by omega)),
      fun hmem => hasc.lt_of_mem _ _ hKL hmem⟩
    rwa [Fin.rev_rev, Fin.rev_rev] at h
  · refine ⟨Sym.monotone_of_le_succ fun K L hKL => ?_, fun K L hKL hmem => ?_⟩
    · exact ((hpair K L hKL).2 (hdesc _ _ (hrev K L hKL))).1
    · exact ((hpair K L hKL).2 (hdesc _ _ (hrev K L hKL))).2 hmem

/-! ### What the labelling equation gives back -/

/-- A word inducing the labelling of `π̂` is admissible for its path: along a marked pair the label
increases, so the letter decreases. -/
theorem isSweepAdmissible_of_aboveLabel_eq (ha : 0 < a) (π : AboveParkingFunction a b N)
    (w : Fin (b * N) → ℕ) (h : aboveLabel π = Sym.wordLabel (aboveStepRank π) w) :
    IsSweepAdmissible (abovePath π) w := by
  intro p hp
  have hp' : (p.1, p.2) ∈ Paths.sweepMarked (abovePath π) := hp
  have hpm := Paths.mem_sweepMarked.1 hp
  have hlt : p.1 < p.2 := Fin.lt_def.2 (by omega)
  have hlab : aboveLabel π p.1 < aboveLabel π p.2 := π.2.2.2 p.1 p.2 hlt hpm.1.symm
  rw [h, Sym.wordLabel_lt_wordLabel_iff (aboveStepRank_injective ha π)] at hlab
  rcases hlab with hlab | ⟨-, hlab⟩
  · exact hlab
  · have hrk : aboveStepRank π p.1 < aboveStepRank π p.2 :=
      Paths.stepRank_lt_of_mem_sweepMarked ha hp'
    exact absurd hlab (by omega)

/-- **The exponent of `q` in `HJO.Paths.sweepChar` is `tdinv̂`.** The attacking pairs on which the
letter decreases are exactly those on which the label increases, because an attacking pair has its
ranks in increasing order and the tie-breaking clause of `HJO.Sym.LetterLt` therefore never
fires. -/
theorem card_sweepAttack_eq_aboveTdinv (ha : 0 < a) (π : AboveParkingFunction a b N)
    (w : Fin (b * N) → ℕ) (h : aboveLabel π = Sym.wordLabel (aboveStepRank π) w) :
    #{p ∈ Paths.sweepAttack (abovePath π) | w p.2 < w p.1} = aboveTdinv π := by
  rw [aboveTdinv_eq_card_sweepAttack]
  refine congrArg _ (filter_congr fun p hp => ?_)
  have hrk : aboveStepRank π p.1 < aboveStepRank π p.2 := (Paths.mem_sweepAttack.1 hp).1
  rw [h, Sym.wordLabel_lt_wordLabel_iff (aboveStepRank_injective ha π)]
  refine ⟨fun hlt => Or.inl hlt, fun hlt => ?_⟩
  rcases hlt with hlt | ⟨-, hlt⟩
  · exact hlt
  · exact absurd hlt (by omega)

/-- `HJO.ParkingFunctions.card_sweepAttack_eq_aboveTdinv` at the labelling a word induces. -/
theorem card_sweepAttack_eq_aboveTdinv_pfOfWord (ha : 0 < a) {y : Paths.Heights a b N}
    (hy : Paths.IsAboveDiagonal y) {w : Fin (b * N) → ℕ} (hw : IsSweepAdmissible y w) :
    #{p ∈ Paths.sweepAttack y | w p.2 < w p.1} = aboveTdinv (pfOfWord ha hy hw) :=
  card_sweepAttack_eq_aboveTdinv ha (pfOfWord ha hy hw) w rfl

/-- Two words inducing the same labelling read the same letters in the same order. -/
theorem eq_of_gesselWord_eq (π : AboveParkingFunction a b N) {w w' : Fin (b * N) → ℕ}
    (h : gesselWord π w = gesselWord π w') : w = w' := by
  funext s
  have hs := congrFun h (Fin.rev (aboveLabel π s))
  rwa [gesselWord, gesselWord, Fin.rev_rev, aboveLabelStep_aboveLabel] at hs

/-! ### The per-path identity -/

/-- The labellings of a path: the above-diagonal parking functions whose path is `y`. -/
def aboveLabellings (y : Paths.Heights a b N) : Finset (AboveParkingFunction a b N) :=
  {π ∈ (univ : Finset (AboveParkingFunction a b N)) | abovePath π = y}

theorem mem_aboveLabellings {y : Paths.Heights a b N} {π : AboveParkingFunction a b N} :
    π ∈ aboveLabellings y ↔ abovePath π = y := by
  rw [aboveLabellings, mem_filter]
  exact and_iff_right (mem_univ π)

/-- The words on the north steps of `y` that `HJO.Paths.sweepChar` sums over at the exponent vector
`d`: admissible, and with `d` for exponent vector. -/
noncomputable def sweepWords (y : Paths.Heights a b N) (d : ℕ →₀ ℕ) :
    Finset (Fin (b * N) → ℕ) :=
  {w ∈ Fintype.piFinset fun _ : Fin (b * N) => d.support |
    (∀ p ∈ Paths.sweepMarked y, w p.2 < w p.1) ∧ ∑ i, Finsupp.single (w i) 1 = d}

theorem mem_sweepWords {y : Paths.Heights a b N} {d : ℕ →₀ ℕ} {w : Fin (b * N) → ℕ} :
    w ∈ sweepWords y d ↔
      (∀ i, w i ∈ d.support) ∧ IsSweepAdmissible y w ∧ Sym.wordExponent w = d := by
  rw [sweepWords, mem_filter, Fintype.mem_piFinset]
  exact ⟨fun h => ⟨h.1, h.2.1, h.2.2⟩, fun h => ⟨h.1, h.2.1, h.2.2⟩⟩

/-- A coefficient of the characteristic function of a path is the `q`-count of the admissible words
with that exponent vector. This is `HJO.Paths.sweepChar` read off its definition. -/
theorem coeff_sweepChar (K : Type*) [CommRing K] (q : K) (y : Paths.Heights a b N) (d : ℕ →₀ ℕ) :
    MvPowerSeries.coeff d (Paths.sweepChar q y)
      = ∑ w ∈ sweepWords y d, q ^ #{p ∈ Paths.sweepAttack y | w p.2 < w p.1} := by
  rw [MvPowerSeries.coeff_apply]
  simp only [Paths.sweepChar, sweepWords]
  refine Finset.sum_congr (Finset.ext fun w => ?_) fun _ _ => rfl
  simp only [mem_filter]

/-- The coefficients of a fundamental quasisymmetric function are the indicator of the exponent
vectors of its ascending words. -/
theorem coeff_gessel_eq_ite (K : Type*) [CommRing K] {n : ℕ} {S : Finset ℕ} (hS : S ⊆ Ico 1 n)
    (d : ℕ →₀ ℕ)
    [Decidable (∃ v : Fin n → ℕ, Sym.IsAscendingWord n S v ∧ d = Sym.wordExponent v)] :
    MvPowerSeries.coeff d (gessel K n S)
      = if ∃ v : Fin n → ℕ, Sym.IsAscendingWord n S v ∧ d = Sym.wordExponent v then 1 else 0 := by
  split
  · next h =>
      obtain ⟨v, hv, rfl⟩ := h
      exact coeff_wordExponent_gessel K hS hv
  · next h => exact coeff_gessel_eq_zero_of_forall_ne K fun v hv hd => h ⟨v, hv, hd⟩

/-- **The characteristic function of a path is the labelling sum of fundamentals.** This is the
per-path identity behind the proof of `HJO.Mellit.eq_sum_sweepChar_of_eq_sum_gessel`, reached
through `HJO.Mellit.sum_sweepChar_eq_sum_gessel`: for every above-diagonal `(aN, bN)`-path `P̂`,
`χ(P̂) = ∑_{π̂} q^{t̂dinv(π̂)} F_{bN, îdeŝ(π̂)^{∨bN}}`, the sum over the labellings of `P̂`.

The proof is the standardisation bijection. At a fixed exponent vector `d`, a word admissible for
`P̂` is sent to the labelling `HJO.Sym.wordLabel` it induces; the labelling determines the word back
from `d`, which is injectivity, and a labelling whose reversed inverse descent set admits an
ascending word of exponent `d` receives one, which is surjectivity. The exponent of `q` matches by
`HJO.ParkingFunctions.card_sweepAttack_eq_aboveTdinv`. -/
theorem sweepChar_eq_sum_gessel (K : Type*) [CommRing K] (q : K) (ha : 0 < a)
    {y : Paths.Heights a b N} (hy : Paths.IsAboveDiagonal y) :
    Paths.sweepChar q y = ∑ π ∈ aboveLabellings y,
      q ^ aboveTdinv π • gessel K (b * N) (descentReverse (b * N) (aboveIdes π)) := by
  classical
  refine MvPowerSeries.ext fun d => ?_
  set P : AboveParkingFunction a b N → Prop := fun π => ∃ v : Fin (b * N) → ℕ,
    Sym.IsAscendingWord (b * N) (descentReverse (b * N) (aboveIdes π)) v ∧
      d = Sym.wordExponent v with hP
  have hR : ∀ π : AboveParkingFunction a b N,
      MvPowerSeries.coeff d
          (q ^ aboveTdinv π • gessel K (b * N) (descentReverse (b * N) (aboveIdes π)))
        = if P π then q ^ aboveTdinv π else 0 := by
    intro π
    rw [map_smul, smul_eq_mul,
      coeff_gessel_eq_ite K (descentReverse_subset_Ico (aboveIdes_subset π)) d]
    split <;> simp
  rw [map_sum, Finset.sum_congr rfl fun π _ => hR π, ← Finset.sum_filter,
    coeff_sweepChar K q y d]
  refine Finset.sum_bij
    (fun w hw => pfOfWord ha hy (show IsSweepAdmissible y w from (mem_sweepWords.1 hw).2.1))
    (fun w hw => ?_) (fun w₁ hw₁ w₂ hw₂ heq => ?_) (fun π hπ => ?_) (fun w hw => ?_)
  -- the labelling a word induces has path `y` and an ascending word of exponent `d`
  · rw [mem_filter, mem_aboveLabellings]
    refine ⟨rfl, _, (isAscendingWord_gesselWord_iff ha _ w).2
      ((isLabelDescending_iff ha _ w).2 rfl), ?_⟩
    rw [wordExponent_gesselWord, (mem_sweepWords.1 hw).2.2]
  -- injectivity: the word is recovered from the labelling and the exponent vector
  · refine Sym.eq_of_wordLabel_eq (Paths.stepRank_injective ha y) ?_ ?_
    · have h := congrArg aboveLabel heq
      rwa [aboveLabel_pfOfWord, aboveLabel_pfOfWord] at h
    · rw [(mem_sweepWords.1 hw₁).2.2, (mem_sweepWords.1 hw₂).2.2]
  -- surjectivity: an ascending word of exponent `d` is read off as an admissible word
  · rw [mem_filter, mem_aboveLabellings] at hπ
    obtain ⟨hpath, v, hv, hdv⟩ := hπ
    have hgw : gesselWord π (fun t => v (Fin.rev (aboveLabel π t))) = v := by
      funext k
      rw [gesselWord, aboveLabel_aboveLabelStep, Fin.rev_rev]
    have hexp : Sym.wordExponent (fun t => v (Fin.rev (aboveLabel π t))) = d := by
      rw [← wordExponent_gesselWord π, hgw, hdv]
    have hlab : aboveLabel π = Sym.wordLabel (aboveStepRank π)
        (fun t => v (Fin.rev (aboveLabel π t))) :=
      (isLabelDescending_iff ha π _).1
        ((isAscendingWord_gesselWord_iff ha π _).1 (by rw [hgw]; exact hv))
    have hadm : IsSweepAdmissible y (fun t => v (Fin.rev (aboveLabel π t))) := by
      have h := isSweepAdmissible_of_aboveLabel_eq ha π _ hlab
      rwa [hpath] at h
    refine ⟨fun t => v (Fin.rev (aboveLabel π t)), mem_sweepWords.2 ⟨fun i => ?_, hadm, hexp⟩, ?_⟩
    · rw [← hexp]
      exact (Sym.mem_support_wordExponent _ _).2 ⟨i, rfl⟩
    · rw [aboveStepRank_eq, hpath] at hlab
      exact Subtype.ext (Prod.ext_iff.2 ⟨hpath.symm, hlab.symm⟩)
  -- the two exponents of `q` agree
  · exact congrArg (q ^ ·) (card_sweepAttack_eq_aboveTdinv_pfOfWord ha hy
      (show IsSweepAdmissible y w from (mem_sweepWords.1 hw).2.1))

end HJO.ParkingFunctions

namespace HJO.Mellit

open ParkingFunctions Paths

/-! ### `HJO.Mellit.sum_sweepChar_eq_sum_gessel` -/

/-- Membership in `PF̂^α_{aN,bN}`: the underlying path has return composition `α`. -/
theorem mem_aboveWithReturns' {a b N : ℕ} {α : List ℕ} {π : AboveParkingFunction a b N} :
    π ∈ aboveWithReturns α a b N ↔ Paths.HasAboveReturns α (abovePath π) := by
  rw [aboveWithReturns, mem_filter]
  exact and_iff_right (mem_univ π)

/-- **The two forms of the right-hand side agree.**
`∑_{P̂} u^{ârea(P̂)} q^{ĥ(P̂) - max t̂dinv(P̂)} χ(P̂)
  = ∑_{π̂ ∈ PF̂^α_{aN,bN}} q^{d̂inv(π̂)} u^{ârea(P̂_π̂)} F_{bN, îdes(π̂)^{∨bN}}`,
the first sum over the above-diagonal `(aN, bN)`-paths of return composition `α`. Both sides are
elements of `𝒫`; no realisation occurs, as the statement involves none.

The proof is the standard one: group the parking functions of the right-hand side by their
underlying path -- the members of `PF̂^α_{aN,bN}` over `P̂` are all the labellings of `P̂` when the
return composition of `P̂` is `α` and none otherwise -- write
`d̂inv(π̂) = ĥ(P̂) + t̂dinv(π̂) - max t̂dinv(P̂)`, and appeal to the per-path identity
`HJO.ParkingFunctions.sweepChar_eq_sum_gessel`, which is the standardisation bijection.

**`q ≠ 0` is spent, and it is not removable**; `0 < a` is what survives of the standing
`1 < a < b`. The module
docstring says where each goes, and why the exponent `ĥ(P̂) - max t̂dinv(P̂)` being negative makes
the first of them a statement about the mathematics rather than about the encoding.

The hypotheses `N ≥ 1` and "`α` is a composition of `N`" of the identity as usually written are
omitted: both index sets are cut out by `HJO.Paths.HasAboveReturns`, which carries those
conditions itself, so nothing is assumed by dropping them. -/
@[hjo "lem_mellit_rhs_sums_agree"]
theorem sum_sweepChar_eq_sum_gessel {L : Type*} [Field L] {a b : ℕ} {q u : L} (ha : 0 < a)
    (hq : q ≠ 0) (N : ℕ) (α : List ℕ) :
    ∑ y ∈ aboveReturnPaths a b N α,
        (u ^ Paths.aboveArea y *
            q ^ ((Paths.aboveHookCount y : ℤ) - (aboveMaxTdinv y : ℤ))) • Paths.sweepChar q y
      = ∑ π ∈ aboveWithReturns α a b N,
          (q ^ aboveDinv π * u ^ Paths.aboveArea (abovePath π)) •
            gessel L (b * N) (descentReverse (b * N) (aboveIdes π)) := by
  classical
  have hmaps : ∀ π ∈ aboveWithReturns α a b N, abovePath π ∈ aboveReturnPaths a b N α := by
    intro π hπ
    have h := mem_aboveWithReturns'.1 hπ
    rw [aboveReturnPaths, mem_filter]
    exact ⟨mem_univ _, h.1, h⟩
  rw [← Finset.sum_fiberwise_of_maps_to hmaps]
  refine Finset.sum_congr rfl fun y hyy => ?_
  rw [aboveReturnPaths, mem_filter] at hyy
  obtain ⟨-, hy1, hy2⟩ := hyy
  have hsets : {π ∈ aboveWithReturns α a b N | abovePath π = y} = aboveLabellings y := by
    ext π
    rw [mem_filter, mem_aboveWithReturns', mem_aboveLabellings]
    exact ⟨fun h => h.2, fun h => ⟨h ▸ hy2, h⟩⟩
  rw [hsets, sweepChar_eq_sum_gessel L q ha hy1, Finset.smul_sum]
  refine Finset.sum_congr rfl fun π hπ => ?_
  have hp : abovePath π = y := mem_aboveLabellings.1 hπ
  rw [smul_smul]
  refine congrArg (fun c : L => c • gessel L (b * N) (descentReverse (b * N) (aboveIdes π))) ?_
  have h1 : q ^ ((Paths.aboveHookCount y : ℤ) - (aboveMaxTdinv y : ℤ)) * q ^ (aboveTdinv π : ℤ)
      = q ^ ((Paths.aboveHookCount y : ℤ) + (aboveTdinv π : ℤ) - (aboveMaxTdinv y : ℤ)) := by
    rw [← zpow_add₀ hq]
    congr 1
    ring
  rw [aboveDinv, hp, ← zpow_natCast q (aboveTdinv π), mul_assoc, h1,
    mul_comm (u ^ Paths.aboveArea y)]

/-- **`HJO.Mellit.RhsSumsAgree` for every sweep system whose characteristic function is
`HJO.Paths.sweepChar`.** The clause is not provable of an arbitrary `HJO.Mellit.SweepSystem` -- that
is the point of its being the interface's anti-vacuity guard, since a system with `χ = 0` refutes it
-- so what discharges it is that hypothesis on `χ`, which every faithful system satisfies by
definition. Together with `HJO.Mellit.sum_sweepChar_eq_sum_gessel` this leaves
`HJO.Mellit.MellitInput` owing only `LhsRewrite`, `MellitInduction` and `Rem41`. -/
theorem rhsSumsAgree_of_chi_eq_sweepChar {L : Type*} [Field L] [Algebra ℚ L] {q u : L} {a b : ℕ}
    (S : SweepSystem L q u) (ha : 0 < a) (hq : q ≠ 0)
    (hchi : ∀ (a' b' N' : ℕ) (y : Paths.Heights a' b' N'), S.chi a' b' N' y = Paths.sweepChar q y) :
    RhsSumsAgree S a b := by
  intro N _ α _ _
  simp only [hchi]
  exact sum_sweepChar_eq_sum_gessel ha hq N α

end HJO.Mellit
