/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Mathlib.Data.Fin.Tuple.Sort
public import Mathlib.Data.Int.ConditionallyCompleteOrder
public import HJO.Paths.Basic
public import HJO.Symmetric.SymmetricFunctions
public import HJO.Defs
public meta import HJO.Attr

/-! # Sign extraction on the parking-function expansion

For a below-diagonal `(aN, bN)`-path this file builds the labelling of its north steps obtained by
ordering the steps by the rank of their feet, and shows that it is the unique parking labelling of
that path with a full inverse descent set. Its temporary dinv is maximal among the labellings of
the path, and a labelling whose temporary dinv is maximal has rational dinv the hook count of the
path. Taking the compositional rational shuffle identity and the effect of sign extraction on the
fundamental quasisymmetric functions as hypotheses, sign extraction of a composite creation
operator is therefore the generating function of the paths with a prescribed return composition by
hook count and area.
-/

@[expose] public section

open Finset

namespace HJO.ParkingFunctions

variable {a b N : ℕ}

/-- `ides(π)` is a descent set on degree `bN`: it is a subset of `1, …, bN - 1`. -/
theorem ides_subset (π : ParkingFunction a b N) : ides π ⊆ Ico 1 (b * N) :=
  filter_subset _ _

end HJO.ParkingFunctions

namespace HJO.EpsilonSelection

open ParkingFunctions Paths

variable {a b N : ℕ}

/-! ### The rank of a north step -/

/-- The rank of the foot of the north step of the path `y` whose foot is at height `s`. -/
def stepRankOf (y : Heights a b N) (s : Fin (b * N)) : ℤ :=
  pointRank a b N (column y (s : ℕ)) (s : ℕ)

/-- The rank of a north step of a parking function only depends on the underlying path. -/
theorem stepRank_eq_stepRankOf (π : ParkingFunction a b N) (s : Fin (b * N)) :
    stepRank π s = stepRankOf (path π) s := rfl

/-- Moving up a fixed column raises the rank: the integral rank of `(x, y)` increases by `a` for
each unit increase of `y`, and the perturbation by the horizontal position is the same at both
points. -/
theorem pointRank_lt_pointRank_of_lt (ha : 0 < a) (x : ℕ) {s t : ℕ} (hst : s < t) :
    pointRank a b N x s < pointRank a b N x t := by
  have h : (a : ℤ) * s < (a : ℤ) * t :=
    mul_lt_mul_of_pos_left (by exact_mod_cast hst) (by exact_mod_cast ha)
  have hscale : (0 : ℤ) < (a : ℤ) * N + 1 := by positivity
  have h' := mul_lt_mul_of_pos_left (show (a : ℤ) * s - b * x < (a : ℤ) * t - b * x by linarith)
    hscale
  simp only [pointRank]
  linarith

/-- Two north steps in the same column: the higher one has the larger rank. -/
theorem stepRankOf_lt_stepRankOf (ha : 0 < a) (y : Heights a b N) {s t : Fin (b * N)}
    (hst : s < t) (hcol : column y (s : ℕ) = column y (t : ℕ)) :
    stepRankOf y s < stepRankOf y t := by
  simp only [stepRankOf, hcol]
  exact pointRank_lt_pointRank_of_lt ha _ hst

/-! ### The two orders on the north steps -/

/-- The key ordering the north steps of `y` by increasing label: the rank of the foot, ties broken
by the height of the foot. -/
def labelKey (y : Heights a b N) (s : Fin (b * N)) : ℤ ×ₗ Fin (b * N) :=
  toLex (stepRankOf y s, s)

/-- Distinct north steps get distinct keys, the height of the foot being one of the entries. -/
theorem labelKey_injective (y : Heights a b N) : Function.Injective (labelKey y) := by
  intro s t h
  simpa [labelKey] using congrArg (fun p => (ofLex p).2) h

/-- The key ordering the north steps of `y` by the reading order: the negated rank of the foot,
ties broken by reading a column downwards. -/
def readKey (y : Heights a b N) (s : Fin (b * N)) : ℤ ×ₗ Fin (b * N) :=
  toLex (-stepRankOf y s, Fin.rev s)

/-- Distinct north steps get distinct reading keys. -/
theorem readKey_injective (y : Heights a b N) : Function.Injective (readKey y) := by
  intro s t h
  exact Fin.rev_injective (by simpa [readKey] using congrArg (fun p => (ofLex p).2) h)

/-- The label order is the reverse of the reading order. -/
theorem labelKey_lt_iff_readKey_lt (y : Heights a b N) {s t : Fin (b * N)} :
    labelKey y s < labelKey y t ↔ readKey y t < readKey y s := by
  simp only [labelKey, readKey, Prod.Lex.toLex_lt_toLex, neg_lt_neg_iff, neg_inj, Fin.rev_lt_rev]
  constructor
  · rintro (h | ⟨h₁, h₂⟩)
    · exact Or.inl h
    · exact Or.inr ⟨h₁.symm, h₂⟩
  · rintro (h | ⟨h₁, h₂⟩)
    · exact Or.inl h
    · exact Or.inr ⟨h₁.symm, h₂⟩

/-! ### The rank-ordered labelling -/

/-- The labelling of the north steps of `y` that puts them in increasing order of `labelKey`. -/
def canonLabel (y : Heights a b N) (s : Fin (b * N)) : Fin (b * N) :=
  (Tuple.sort (labelKey y)).symm s

/-- The labelling `canonLabel` increases exactly along increasing `labelKey`. -/
theorem canonLabel_lt_canonLabel_iff (y : Heights a b N) {s t : Fin (b * N)} :
    canonLabel y s < canonLabel y t ↔ labelKey y s < labelKey y t := by
  have hsm : StrictMono (labelKey y ∘ (Tuple.sort (labelKey y))) :=
    (Tuple.monotone_sort (labelKey y)).strictMono_of_injective
      ((labelKey_injective y).comp (Equiv.injective _))
  have h : ∀ r : Fin (b * N),
      labelKey y r = (labelKey y ∘ (Tuple.sort (labelKey y))) (canonLabel y r) := by
    intro r; simp [canonLabel]
  rw [h s, h t, hsm.lt_iff_lt]

/-- `canonLabel y` is injective. -/
theorem canonLabel_injective (y : Heights a b N) : Function.Injective (canonLabel y) :=
  (Tuple.sort (labelKey y)).symm.injective

/-- `canonLabel y` is a legal parking labelling: it is bijective, and along a column it increases
upwards because the rank increases upwards. -/
theorem isParkingLabelling_canonLabel (ha : 0 < a) (y : Heights a b N) :
    IsParkingLabelling y (canonLabel y) := by
  refine ⟨(Tuple.sort (labelKey y)).symm.bijective, fun s t hst hcol => ?_⟩
  rw [canonLabel_lt_canonLabel_iff, labelKey, labelKey, Prod.Lex.toLex_lt_toLex]
  exact Or.inl (stepRankOf_lt_stepRankOf ha y hst hcol)

/-- The parking function on a below-diagonal path given by the rank-ordered labelling. -/
def canonPF (ha : 0 < a) {y : Heights a b N} (hy : IsBelowDiagonal y) : ParkingFunction a b N :=
  ⟨(y, canonLabel y), hy, isParkingLabelling_canonLabel ha y⟩

/-- The path underlying `canonPF` is the path it was built from. -/
@[simp] theorem path_canonPF (ha : 0 < a) {y : Heights a b N} (hy : IsBelowDiagonal y) :
    path (canonPF ha hy) = y := rfl

/-- The labelling of `canonPF` is the rank-ordered labelling. -/
@[simp] theorem label_canonPF (ha : 0 < a) {y : Heights a b N} (hy : IsBelowDiagonal y)
    (s : Fin (b * N)) : label (canonPF ha hy) s = canonLabel y s := rfl

/-! ### Labels against north steps -/

/-- The north step carrying the label of a step is that step. -/
theorem labelStep_label (π : ParkingFunction a b N) (s : Fin (b * N)) :
    labelStep π (label π s) = s :=
  Fintype.leftInverse_bijInv (bijective_label π) s

/-- The label of the north step carrying a label is that label. -/
theorem label_labelStep (π : ParkingFunction a b N) (i : Fin (b * N)) :
    label π (labelStep π i) = i :=
  Fintype.rightInverse_bijInv (bijective_label π) i

/-- Distinct labels mark distinct north steps. -/
theorem labelStep_injective (π : ParkingFunction a b N) : Function.Injective (labelStep π) :=
  Function.LeftInverse.injective (label_labelStep π)

/-- The rank of a label is the rank of the north step it marks. -/
theorem labelRank_eq (π : ParkingFunction a b N) (i : Fin (b * N)) :
    labelRank π i = stepRankOf (path π) (labelStep π i) := rfl

/-- The rank of the label of a north step is the rank of that step. -/
theorem labelRank_label (π : ParkingFunction a b N) (s : Fin (b * N)) :
    labelRank π (label π s) = stepRankOf (path π) s := by
  rw [labelRank_eq, labelStep_label]

/-- Under the rank-ordered labelling the rank of the label of a north step is the rank of that
step. -/
theorem labelRank_canonPF (ha : 0 < a) {y : Heights a b N} (hy : IsBelowDiagonal y)
    (s : Fin (b * N)) : labelRank (canonPF ha hy) (canonLabel y s) = stepRankOf y s := by
  rw [← label_canonPF ha hy s, labelRank_label, path_canonPF]

/-! ### The maximal temporary dinv -/

/-- The temporary dinv of a parking function is at most the maximal temporary dinv of its path. -/
theorem tdinv_le_maxTdinv (π : ParkingFunction a b N) : tdinv π ≤ maxTdinv (path π) :=
  Finset.le_sup (f := tdinv) (mem_filter.2 ⟨mem_univ _, rfl⟩)

/-- The rank-ordered labelling realises every pair of north steps that the temporary dinv admits,
so no labelling of the path beats it. -/
theorem tdinv_le_tdinv_canonPF (ha : 0 < a) {y : Heights a b N} (hy : IsBelowDiagonal y)
    (π : ParkingFunction a b N) (hp : path π = y) : tdinv π ≤ tdinv (canonPF ha hy) := by
  refine Finset.card_le_card_of_injOn
    (fun p => (canonLabel y (labelStep π p.1), canonLabel y (labelStep π p.2))) ?_ ?_
  · intro p hp'
    simp only [mem_coe, mem_filter, mem_univ, true_and] at hp' ⊢
    obtain ⟨-, h₁, h₂⟩ := hp'
    rw [labelRank_eq, labelRank_eq, hp] at h₁ h₂
    refine ⟨(canonLabel_lt_canonLabel_iff y).2 (Prod.Lex.toLex_lt_toLex.2 (Or.inl h₁)), ?_, ?_⟩
    · rw [labelRank_canonPF, labelRank_canonPF]
      exact h₁
    · rw [labelRank_canonPF, labelRank_canonPF]
      exact h₂
  · intro p _ r _ h
    have h₁ := labelStep_injective π (canonLabel_injective y (congrArg Prod.fst h))
    have h₂ := labelStep_injective π (canonLabel_injective y (congrArg Prod.snd h))
    exact Prod.ext h₁ h₂

/-- The rank-ordered labelling attains the maximal temporary dinv of its path. -/
theorem tdinv_canonPF_eq_maxTdinv (ha : 0 < a) {y : Heights a b N} (hy : IsBelowDiagonal y) :
    tdinv (canonPF ha hy) = maxTdinv y :=
  le_antisymm (tdinv_le_maxTdinv _)
    (Finset.sup_le fun π hπ => tdinv_le_tdinv_canonPF ha hy π (mem_filter.1 hπ).2)

/-! ### The dinv of a parking function against the hook count of its path -/

/-- The rational dinv equals the hook count of the path exactly when the temporary dinv is
maximal. -/
theorem dinv_eq_hookCount_iff (π : ParkingFunction a b N) :
    dinv π = (hookCount (path π) : ℤ) ↔ tdinv π = maxTdinv (path π) := by
  simp only [dinv]
  omega

/-- A maximal temporary dinv collapses the rational dinv to the hook count of the path. -/
theorem dinv_eq_hookCount (π : ParkingFunction a b N) (h : tdinv π = maxTdinv (path π)) :
    dinv π = (hookCount (path π) : ℤ) :=
  (dinv_eq_hookCount_iff π).2 h

/-- The rational dinv never exceeds the hook count of the path. -/
theorem dinv_le_hookCount (π : ParkingFunction a b N) : dinv π ≤ (hookCount (path π) : ℤ) := by
  have := tdinv_le_maxTdinv π
  simp only [dinv]
  omega

/-! ### The reading order -/

/-- A north step is read before another exactly when its reading key is smaller. -/
theorem readBefore_iff_readKey_lt (π : ParkingFunction a b N) {s t : Fin (b * N)} :
    ReadBefore π s t ↔ readKey (path π) s < readKey (path π) t := by
  simp only [ReadBefore, readKey, Prod.Lex.toLex_lt_toLex, neg_lt_neg_iff, neg_inj,
    Fin.rev_lt_rev, stepRank_eq_stepRankOf]

/-- No north step is read before itself. -/
theorem not_readBefore_self (π : ParkingFunction a b N) (s : Fin (b * N)) :
    ¬ ReadBefore π s s := by
  rw [readBefore_iff_readKey_lt]
  exact lt_irrefl _

/-- A north step has the larger label exactly when it is read later. -/
theorem labelKey_lt_iff_readBefore (π : ParkingFunction a b N) {s t : Fin (b * N)} :
    labelKey (path π) s < labelKey (path π) t ↔ ReadBefore π t s :=
  (labelKey_lt_iff_readKey_lt _).trans (readBefore_iff_readKey_lt π).symm

/-- The north steps of `π` listed in reading order. -/
def sortedSteps (π : ParkingFunction a b N) : List (Fin (b * N)) :=
  (List.finRange (b * N)).mergeSort fun s t => !decide (ReadBefore π t s)

/-- The reading word is the list of labels of the north steps taken in reading order. -/
theorem readingWord_eq_map (π : ParkingFunction a b N) :
    readingWord π = (sortedSteps π).map fun s => (label π s : ℕ) + 1 := rfl

/-- The comparison used to sort the north steps is transitive. -/
private theorem sortedSteps_trans (π : ParkingFunction a b N) (s t r : Fin (b * N))
    (h₁ : (!decide (ReadBefore π t s)) = true) (h₂ : (!decide (ReadBefore π r t)) = true) :
    (!decide (ReadBefore π r s)) = true := by
  simp only [Bool.not_eq_true', decide_eq_false_iff_not, readBefore_iff_readKey_lt,
    not_lt] at h₁ h₂ ⊢
  exact h₁.trans h₂

/-- The comparison used to sort the north steps is total. -/
private theorem sortedSteps_total (π : ParkingFunction a b N) (s t : Fin (b * N)) :
    ((!decide (ReadBefore π t s)) || (!decide (ReadBefore π s t))) = true := by
  simp only [Bool.or_eq_true, Bool.not_eq_true', decide_eq_false_iff_not,
    readBefore_iff_readKey_lt, not_lt]
  exact le_total _ _

/-- A north step occurring later in the reading order is not read before an earlier one. -/
theorem pairwise_sortedSteps (π : ParkingFunction a b N) :
    List.Pairwise (fun s t => ¬ ReadBefore π t s) (sortedSteps π) :=
  (List.pairwise_mergeSort (sortedSteps_trans π) (sortedSteps_total π) _).imp
    (by simp only [Bool.not_eq_true', decide_eq_false_iff_not]; exact id)

/-- Every north step occurs in the reading order. -/
theorem mem_sortedSteps (π : ParkingFunction a b N) (s : Fin (b * N)) : s ∈ sortedSteps π :=
  ((List.mergeSort_perm _ _).mem_iff).2 (List.mem_finRange s)

/-- A north step read before another occupies an earlier position in the reading order. -/
theorem idxOf_lt_idxOf_of_readBefore (π : ParkingFunction a b N) {s t : Fin (b * N)}
    (h : ReadBefore π s t) : (sortedSteps π).idxOf s < (sortedSteps π).idxOf t := by
  have hs : (sortedSteps π).idxOf s < (sortedSteps π).length :=
    List.idxOf_lt_length_iff.2 (mem_sortedSteps π s)
  have ht : (sortedSteps π).idxOf t < (sortedSteps π).length :=
    List.idxOf_lt_length_iff.2 (mem_sortedSteps π t)
  rcases lt_trichotomy ((sortedSteps π).idxOf s) ((sortedSteps π).idxOf t) with h₁ | h₁ | h₁
  · exact h₁
  · exfalso
    have hst : s = t := by
      rw [← List.getElem_idxOf hs, ← List.getElem_idxOf ht]
      simp [h₁]
    exact not_readBefore_self π s (hst ▸ h)
  · exfalso
    have := List.pairwise_iff_getElem.1 (pairwise_sortedSteps π) _ _ ht hs h₁
    rw [List.getElem_idxOf, List.getElem_idxOf] at this
    exact this h

/-- A north step occupying an earlier position in the reading order is read before the other. -/
theorem readBefore_of_idxOf_lt (π : ParkingFunction a b N) {s t : Fin (b * N)}
    (h : (sortedSteps π).idxOf s < (sortedSteps π).idxOf t) : ReadBefore π s t := by
  rcases lt_trichotomy (readKey (path π) s) (readKey (path π) t) with h₁ | h₁ | h₁
  · exact (readBefore_iff_readKey_lt π).2 h₁
  · exfalso
    rw [readKey_injective _ h₁] at h
    exact absurd h (lt_irrefl _)
  · exact absurd (idxOf_lt_idxOf_of_readBefore π ((readBefore_iff_readKey_lt π).2 h₁))
      (by omega)

/-- Positions in a list are unchanged by an injective relabelling of its entries. -/
private theorem idxOf_map_of_injective {α β : Type*} [DecidableEq α] [DecidableEq β] {f : α → β}
    (hf : Function.Injective f) (l : List α) (x : α) : (l.map f).idxOf (f x) = l.idxOf x := by
  induction l with
  | nil => simp
  | cons y l ih =>
    by_cases hxy : x = y
    · subst hxy; simp
    · rw [List.map_cons, List.idxOf_cons_ne _ (fun h => hxy (hf h).symm),
        List.idxOf_cons_ne _ (Ne.symm hxy), ih]

/-- The position of the label of a north step in the reading word is the position of the step in
the reading order. -/
theorem idxOf_readingWord (π : ParkingFunction a b N) (s : Fin (b * N)) :
    (readingWord π).idxOf ((label π s : ℕ) + 1) = (sortedSteps π).idxOf s := by
  have hinj : Function.Injective fun r : Fin (b * N) => (label π r : ℕ) + 1 := by
    intro x y h
    simp only [Nat.add_right_cancel_iff] at h
    exact (bijective_label π).1 (Fin.val_injective h)
  rw [readingWord_eq_map]
  exact idxOf_map_of_injective hinj _ _

/-! ### The labelling with a full inverse descent set -/

/-- If every label is preceded by its successor then the positions in the reading word decrease
as the label increases. -/
theorem idxOf_lt_idxOf_of_lt (π : ParkingFunction a b N) (h : ides π = Ico 1 (b * N)) {u : ℕ}
    (hu : 1 ≤ u) : ∀ v : ℕ, u < v → v ≤ b * N →
      (readingWord π).idxOf v < (readingWord π).idxOf u := by
  intro v
  induction v with
  | zero => intro h₁; omega
  | succ w ih =>
    intro h₁ h₂
    have hstep : (readingWord π).idxOf (w + 1) < (readingWord π).idxOf w := by
      have hw : w ∈ ides π := by rw [h]; simp only [mem_Ico]; omega
      exact (mem_filter.1 hw).2
    rcases eq_or_lt_of_le (Nat.succ_le_of_lt h₁) with heq | hlt
    · have : u = w := by omega
      exact this ▸ hstep
    · exact hstep.trans (ih (by omega) (by omega))

/-- A full inverse descent set makes the label order the reverse of the reading order. -/
theorem readBefore_of_label_lt (π : ParkingFunction a b N) (h : ides π = Ico 1 (b * N))
    {s t : Fin (b * N)} (hlt : label π s < label π t) : ReadBefore π t s := by
  have hlt' : (label π s : ℕ) < (label π t : ℕ) := hlt
  have hbd : (label π t : ℕ) < b * N := (label π t).isLt
  have hidx := idxOf_lt_idxOf_of_lt π h (u := (label π s : ℕ) + 1) (by omega)
    ((label π t : ℕ) + 1) (by omega) (by omega)
  rw [idxOf_readingWord, idxOf_readingWord] at hidx
  exact readBefore_of_idxOf_lt π hidx

/-- The rank-ordered labelling has a full inverse descent set: its labels decrease along the
reading order. -/
theorem ides_canonPF (ha : 0 < a) {y : Heights a b N} (hy : IsBelowDiagonal y) :
    ides (canonPF ha hy) = Ico 1 (b * N) := by
  unfold ides
  refine filter_eq_self.2 fun i hi => ?_
  rw [mem_Ico] at hi
  have h₁ : i - 1 < b * N := by omega
  have hstep : label (canonPF ha hy) (labelStep (canonPF ha hy) ⟨i - 1, h₁⟩) <
      label (canonPF ha hy) (labelStep (canonPF ha hy) ⟨i, hi.2⟩) := by
    rw [label_labelStep, label_labelStep]
    exact Fin.mk_lt_mk.2 (by omega)
  have hrb : ReadBefore (canonPF ha hy) (labelStep (canonPF ha hy) ⟨i, hi.2⟩)
      (labelStep (canonPF ha hy) ⟨i - 1, h₁⟩) := by
    rw [← labelKey_lt_iff_readBefore, path_canonPF, ← canonLabel_lt_canonLabel_iff]
    simpa using hstep
  have hidx := idxOf_lt_idxOf_of_readBefore (canonPF ha hy) hrb
  rw [← idxOf_readingWord, ← idxOf_readingWord, label_labelStep, label_labelStep] at hidx
  simpa [Nat.sub_add_cancel hi.1] using hidx

/-- The rank-ordered labelling is the only labelling of its path with a full inverse descent
set. -/
theorem label_eq_canonLabel_of_ides (π : ParkingFunction a b N) (h : ides π = Ico 1 (b * N)) :
    label π = canonLabel (path π) := by
  set E := Equiv.ofBijective (label π) (bijective_label π) with hE
  have hval : ∀ s : Fin (b * N), E s = label π s := fun s => rfl
  have hsymm : ∀ i : Fin (b * N), label π (E.symm i) = i := fun i => by
    rw [← hval]; exact E.apply_symm_apply i
  have hsort : E.symm = Tuple.sort (labelKey (path π)) := by
    rw [Tuple.eq_sort_iff]
    refine ⟨fun i j hij => ?_, fun i j hij heq => ?_⟩
    · rcases eq_or_lt_of_le hij with rfl | hlt
      · exact le_rfl
      · refine le_of_lt ((labelKey_lt_iff_readBefore π).2 (readBefore_of_label_lt π h ?_))
        rw [hsymm, hsymm]
        exact hlt
    · exact absurd (E.symm.injective (labelKey_injective _ heq)) (by simpa using hij.ne)
  funext s
  rw [canonLabel, ← hsort, hE]
  simp

/-- A parking function with a full inverse descent set is the rank-ordered labelling of its
path. -/
theorem eq_canonPF_of_ides (ha : 0 < a) (π : ParkingFunction a b N)
    (h : ides π = Ico 1 (b * N)) : π = canonPF ha π.2.1 :=
  Subtype.ext (Prod.ext rfl (label_eq_canonLabel_of_ides π h))

/-- A full inverse descent set forces the temporary dinv to be maximal. -/
theorem tdinv_eq_maxTdinv_of_ides (ha : 0 < a) (π : ParkingFunction a b N)
    (h : ides π = Ico 1 (b * N)) : tdinv π = maxTdinv (path π) := by
  rw [congrArg tdinv (eq_canonPF_of_ides ha π h)]
  exact tdinv_canonPF_eq_maxTdinv ha π.2.1

/-- A full inverse descent set collapses the rational dinv to the hook count of the path. -/
theorem dinv_eq_hookCount_of_ides (ha : 0 < a) (π : ParkingFunction a b N)
    (h : ides π = Ico 1 (b * N)) : dinv π = (hookCount (path π) : ℤ) :=
  dinv_eq_hookCount π (tdinv_eq_maxTdinv_of_ides ha π h)

/-! ### Sign extraction against the parking-function expansion -/

section SignExtraction

variable {L : Type*} [Field L] [Algebra ℚ L]

/-- Sign extraction applied to the parking-function expansion of a composite creation operator
keeps precisely the parking functions with a full inverse descent set. The expansion itself and
the behaviour of sign extraction on the fundamental quasisymmetric functions are taken as
hypotheses `shuffle` and `signExtract_gessel`; neither is proved here. The seed of a composition
`β` expands over the parking functions of return composition `β.reverse`, the below-diagonal
convention reading the blocks of the source's composition from the other end. -/
theorem signExtract_copComp_eq_sum_full_ides {q u : L}
    (shuffle : ∀ (ι : Sym.Lambda L →ₐ[L] Sym.AlphabetSeries L), Sym.IsRealisation ι →
      ∀ Θ : Sym.Lambda L →ₐ[L] Module.End L (Sym.Lambda L), Sym.IsSlopeHom a b q u Θ →
      ∀ M : ℕ, 0 < M → ∀ β : List ℕ, (∀ x ∈ β, 0 < x) → β.sum = M →
        MvPolynomial.IsWeightedHomogeneous (fun i => i + 1)
            ((-1 : L) ^ (M * (b + 1)) • Θ (Sym.CopComp q β 1) 1) (b * M) ∧
          ι ((-1 : L) ^ (M * (b + 1)) • Θ (Sym.CopComp q β 1) 1) =
            ∑ π ∈ withReturns β.reverse a b M, (q ^ dinv π * u ^ area (path π)) •
              gessel L (b * M) (ides π))
    (signExtract_gessel : ∀ (ι : Sym.Lambda L →ₐ[L] Sym.AlphabetSeries L), Sym.IsRealisation ι →
      ∀ n : ℕ, 0 < n → ∀ (I : Type) (J : Finset I) (w : I → L) (S : I → Finset ℕ)
        (f : Sym.Lambda L), MvPolynomial.IsWeightedHomogeneous (fun i => i + 1) f n →
        (∀ i ∈ J, S i ⊆ Ico 1 n) →
        ι f = ∑ i ∈ J, w i • gessel L n (S i) →
        Sym.signExtract L f = ∑ i ∈ J with S i = Ico 1 n, w i)
    (ι : Sym.Lambda L →ₐ[L] Sym.AlphabetSeries L) (hι : Sym.IsRealisation ι)
    (Θ : Sym.Lambda L →ₐ[L] Module.End L (Sym.Lambda L)) (hΘ : Sym.IsSlopeHom a b q u Θ)
    (hb : 0 < b) (hN : 0 < N) (α : List ℕ) (hαpos : ∀ x ∈ α, 0 < x) (hα : α.sum = N) :
    (-1 : L) ^ (N * (b + 1)) * Sym.signExtract L (Θ (Sym.CopComp q α 1) 1) =
      ∑ π ∈ withReturns α.reverse a b N with ides π = Ico 1 (b * N),
        q ^ dinv π * u ^ area (path π) := by
  obtain ⟨hhom, hexp⟩ := shuffle ι hι Θ hΘ N hN α hαpos hα
  have h := signExtract_gessel ι hι (b * N) (Nat.mul_pos hb hN) (ParkingFunction a b N)
    (withReturns α.reverse a b N) (fun π => q ^ dinv π * u ^ area (path π)) ides _ hhom
    (fun π _ => ides_subset π) hexp
  rwa [map_smul, smul_eq_mul] at h

/-- Sign extraction of a composite creation operator, applied to `1` and corrected by the sign
`(-1) ^ (N (b + 1))`, is the generating function of the below-diagonal `(aN, bN)`-paths with
return composition `α.reverse` by hook count and area, the below-diagonal convention reading the
blocks of the source's composition from the other end. The compositional rational shuffle identity
and the effect of sign extraction on the fundamental quasisymmetric functions are the hypotheses
`shuffle` and `signExtract_gessel`; neither is proved here. -/
@[hjo "lem_epsilon_selection"]
theorem signExtract_copComp_eq_sum_paths {q u : L}
    (shuffle : ∀ (ι : Sym.Lambda L →ₐ[L] Sym.AlphabetSeries L), Sym.IsRealisation ι →
      ∀ Θ : Sym.Lambda L →ₐ[L] Module.End L (Sym.Lambda L), Sym.IsSlopeHom a b q u Θ →
      ∀ M : ℕ, 0 < M → ∀ β : List ℕ, (∀ x ∈ β, 0 < x) → β.sum = M →
        MvPolynomial.IsWeightedHomogeneous (fun i => i + 1)
            ((-1 : L) ^ (M * (b + 1)) • Θ (Sym.CopComp q β 1) 1) (b * M) ∧
          ι ((-1 : L) ^ (M * (b + 1)) • Θ (Sym.CopComp q β 1) 1) =
            ∑ π ∈ withReturns β.reverse a b M, (q ^ dinv π * u ^ area (path π)) •
              gessel L (b * M) (ides π))
    (signExtract_gessel : ∀ (ι : Sym.Lambda L →ₐ[L] Sym.AlphabetSeries L), Sym.IsRealisation ι →
      ∀ n : ℕ, 0 < n → ∀ (I : Type) (J : Finset I) (w : I → L) (S : I → Finset ℕ)
        (f : Sym.Lambda L), MvPolynomial.IsWeightedHomogeneous (fun i => i + 1) f n →
        (∀ i ∈ J, S i ⊆ Ico 1 n) →
        ι f = ∑ i ∈ J, w i • gessel L n (S i) →
        Sym.signExtract L f = ∑ i ∈ J with S i = Ico 1 n, w i)
    (ι : Sym.Lambda L →ₐ[L] Sym.AlphabetSeries L) (hι : Sym.IsRealisation ι)
    (Θ : Sym.Lambda L →ₐ[L] Module.End L (Sym.Lambda L)) (hΘ : Sym.IsSlopeHom a b q u Θ)
    (ha : 0 < a) (hb : 0 < b) (hN : 0 < N) (α : List ℕ) (hαpos : ∀ x ∈ α, 0 < x)
    (hα : α.sum = N) :
    (-1 : L) ^ (N * (b + 1)) * Sym.signExtract L (Θ (Sym.CopComp q α 1) 1) =
      ∑ y ∈ (univ : Finset (Heights a b N)) with HasReturns α.reverse y,
        q ^ hookCount y * u ^ area y := by
  rw [signExtract_copComp_eq_sum_full_ides shuffle signExtract_gessel ι hι Θ hΘ hb hN α hαpos hα]
  refine Finset.sum_bij' (fun π _ => path π) (fun y hy => canonPF ha (mem_filter.1 hy).2.1)
    (fun π hπ => ?_) (fun y hy => ?_) (fun π hπ => ?_) (fun y hy => ?_) (fun π hπ => ?_)
  · exact mem_filter.2 ⟨mem_univ _, (mem_filter.1 (mem_filter.1 hπ).1).2⟩
  · refine mem_filter.2 ⟨mem_filter.2 ⟨mem_univ _, ?_⟩, ides_canonPF ha _⟩
    rw [path_canonPF]
    exact (mem_filter.1 hy).2
  · exact (eq_canonPF_of_ides ha π (mem_filter.1 hπ).2).symm
  · exact path_canonPF ha _
  · rw [dinv_eq_hookCount_of_ides ha π (mem_filter.1 hπ).2, zpow_natCast]

end SignExtraction

end HJO.EpsilonSelection
