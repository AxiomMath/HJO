/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.Shuffle.BraidRelations
public import HJO.Shuffle.SweepWitness
public import HJO.Shuffle.SweepWordV0
public meta import HJO.Attr

/-! # The raising operator of the Dyck path algebra

`HJO/Shuffle/BraidRelations.lean` defines the ascending braid word `T_{[a,b]}`
(`HJO.Sweep.cmAscWord`) and proves the two relations it is built out of,
the `S_3` relation `HJO.Sweep.braid_braid` and far commutation `HJO.Sweep.braid_comm`. This file is
the word algebra those two relations buy — splitting a word, and pushing a single letter through the
word `T_{[1,k]}` — and the operator the Dyck path algebra defines from that word,
`d_+ = T_{[1,k]}τ_{k+1,k+1}`.

## Main definitions

* `HJO.Sweep.cmDPlus`,
  `d_+F = T_1(T_2(⋯T_k(τ_{k+1,k+1}(F))⋯))`.
* `HJO.Sweep.dplusIter` — `d_+^m(1)`, the unit raised `m` times by `HJO.Sweep.dplus`.

## Main results

* `HJO.Sweep.braid_of_swapAux_eq` — `T_i` fixes what `s_i` fixes.
* `HJO.Sweep.cmAscWord_split` — `T_{[a,b]} = T_{[a,c]}T_{[c+1,b]}`.
* `HJO.Sweep.cmAscWord_mul_braidEnd` — `T_{[1,k]}T_i = T_{i+1}T_{[1,k]}` for `1 ≤ i ≤ k-1`.
* `HJO.Sweep.cmAscWord_word_shift` — `T_{[1,r+1]}T_{[1,r]} = T_{[2,r+1]}T_{[1,r+1]}`.
* `HJO.Sweep.cmDPlus_apply` — `d_+F = T_{[1,k]}(τ_{k+1,k+1}(F))`.
* `HJO.Sweep.cmDPlus_braid` — `d_+(T_iF) = T_{i+1}(d_+F)`.
* `HJO.Sweep.swapAux_qshift_qshift` — `s_{k+1}` fixes the doubly shifted `V_k`.
* `HJO.Sweep.braid_one_cmDPlus_cmDPlus` — `T_1(d_+(d_+F)) = d_+(d_+F)`.
* `HJO.Sweep.braid_dplusIter` — `T_i d_+^j(1) = d_+^j(1)` for `1 ≤ i ≤ j-1`. Its two
  ingredients are the previous two results transported to
  `HJO.Sweep.dplus`, `HJO.Sweep.dplus_braid` and `HJO.Sweep.braid_one_dplus_dplus`.
* `HJO.Sweep.unitShiftTotal_braid` — the unit shift `ϑ` of `HJO.Sweep.unitShiftTotal` commutes with
  every braid operator, `HJO.Sweep.unitShiftTotal_braid`.

## The two raising operators

`HJO.Sweep.cmDPlus` here and `HJO.Sweep.dplus` are **different operators**, and
naming them apart is not a bookkeeping choice: the sweep process's raising operator carries a sign
and an extra letter,
`d_+^{sweep}F = -T_1 ⋯ T_k(y_{k+1}τ_{k+1,k+1}(F))`, where the Dyck path algebra's is
`T_1 ⋯ T_k(τ_{k+1,k+1}(F))`. `HJO.Sweep.dplus_eq_neg_cmDPlus` is the bridge,
`d_+^{sweep} = -d_+ ∘ (y_{k+1} ·)`, which holds because `τ_{k+1,k+1}` is an algebra homomorphism
fixing every auxiliary variable, so the extra letter can be moved out through it.

## Index conventions

The relations are stated for `F ∈ V_k` with `1 ≤ i ≤ k-1`, `T_i` and `T_{[a,b]}` being
maps from `V_k` to `V_k` and `d_+` a map from `V_k` to `V_{k+1}`. Here, in the house style of
`HJO.Sweep`, all of them are single endomorphisms of the total space whose restrictions are those
maps: `HJO.Sweep.cmDPlus_mem_piece` is the codomain statement `d_+(V_k) ⊆ V_{k+1}`, and
the distance hypotheses `1 ≤ i` and `i + 1 ≤ k` — the `1 ≤ i ≤ k-1` without truncated
subtraction — are the ones that carry content, being what the relations of the braid system are read
at.
-/

@[expose] public section

namespace HJO.Sweep

section Field

variable {L : Type*} [Field L]

/-! ### A braid operator fixes a symmetric element -/

/-- **`T_i` fixes what `s_i` fixes**, `HJO.Sweep.braid_of_swapAux_eq`: if `s_iF = F`
then `∂_iF = 0` by the uniqueness of the divided difference, so `T_iF = s_iF + (q-1)y_i·0 = F`.

The `1 ≤ i` is not needed: at the unread index `0` the transposition and the braid
operator are both the identity. -/
@[hjo "lem_cm_braid_symmetric_fix"]
theorem braid_of_swapAux_eq (q : L) {i : ℕ} {F : Total L} (hF : swapAux L i F = F) :
    braid q i F = F := by
  rcases Nat.eq_zero_or_pos i with rfl | hi
  · exact braid_zero_index q F
  have h0 : dividedDiff i F = 0 :=
    (dividedDiff_unique hi (G := 0) (by rw [mul_zero, hF, sub_self])).symm
  rw [braid_apply, h0, mul_zero, add_zero, hF]

/-- **`T_i` is linear over what `s_i` fixes**: `T_i(PF) = P·T_iF` whenever `s_iP = P`. The divided
difference has that property (`HJO.Sweep.dividedDiff_mul_of_swapAux_eq`) and `s_i` is a ring
homomorphism, so `T_i = s_i + (q-1)y_i∂_i` has it too. -/
theorem braid_mul_of_swapAux_eq (q : L) {i : ℕ} {P : Total L} (hP : swapAux L i P = P)
    (F : Total L) : braid q i (P * F) = P * braid q i F := by
  rw [braid_apply, braid_apply, map_mul, hP, dividedDiff_mul_of_swapAux_eq hP]
  ring

/-! ### The ascending word splits -/

/-- `T_{[a,b]}` is the ascending word in the braid operators from `a` to `b` inclusive, the train
`T_{a↗b+1}` on its ascending branch. -/
theorem cmAscWord_eq_ascendingWord (q : L) {a b : ℕ} (hab : a ≤ b + 1) :
    cmAscWord q a b = Braid.ascendingWord (braidEnd q) a (b + 1) :=
  trainUpEnd_eq_ascendingWord q hab

/-- **The ascending word splits**, `HJO.Sweep.cmAscWord_split`:
`T_{[a,b]} = T_{[a,c]}T_{[c+1,b]}` for `a - 1 ≤ c ≤ b`.

The lower bound `a - 1 ≤ c` is written `a ≤ c + 1`, avoiding truncated subtraction; its
two degenerate cases `c = a-1` and `c = b`, where one factor is the empty word, need no separate
treatment here because `HJO.Braid.ascendingWord` is a product over a `List.range'` whose length may
be zero. No relation of the braid system is read: this is the concatenation of two adjacent index
ranges, `HJO.Braid.ascendingWord_mul`. -/
@[hjo "lem_cm_ascword_split"]
theorem cmAscWord_split (q : L) {a b c : ℕ} (hac : a ≤ c + 1) (hcb : c ≤ b) :
    cmAscWord q a b = cmAscWord q a c * cmAscWord q (c + 1) b := by
  rw [cmAscWord_eq_ascendingWord q (by omega), cmAscWord_eq_ascendingWord q (by omega),
    cmAscWord_eq_ascendingWord q (by omega),
    Braid.ascendingWord_mul (braidEnd q) hac (by omega)]

/-! ### The ascending word absorbs a braid operator -/

/-- **The ascending word `T_{[1,k]}` absorbs a braid operator and shifts it**:
`T_{[1,k]}T_i = T_{i+1}T_{[1,k]}` for `1 ≤ i ≤ k-1`.

This is `HJO.Braid.ascendingWord_mul_gen` at `a = 1`, `b = k + 1`, whose three hypotheses are the
`S_3` relation at `i` and the two far commutations — `HJO.Sweep.braidEnd_braid` and
`HJO.Sweep.braidEnd_comm`, both of which hold for **every** `q`. So no invertibility hypothesis
appears, which is why the word-level lemma was stated with its relations loose rather than read off
a `HJO.Braid.IsBraidSystem`: the braid operators form a braid system only for `q ≠ 0`
(`HJO.Sweep.isBraidSystem_braidEnd`), and this statement does not need that. -/
@[hjo "lem_cm_word_braid_shift"]
theorem cmAscWord_mul_braidEnd (q : L) {k i : ℕ} (hi : 1 ≤ i) (hik : i + 1 ≤ k) :
    cmAscWord q 1 k * braidEnd q i = braidEnd q (i + 1) * cmAscWord q 1 k := by
  rw [cmAscWord_eq_ascendingWord q (by omega)]
  exact Braid.ascendingWord_mul_gen hi (by omega) (braidEnd_braid q hi)
    (fun _ hj _ => braidEnd_comm q hi hj) (fun _ hj hj2 => (braidEnd_comm q hj hj2).symm)

/-- **`T_{[1,k]}(T_iF) = T_{i+1}(T_{[1,k]}F)`**, the applied form of
`HJO.Sweep.cmAscWord_mul_braidEnd`. -/
theorem cmAscWord_braid (q : L) {k i : ℕ} (hi : 1 ≤ i) (hik : i + 1 ≤ k) (F : Total L) :
    cmAscWord q 1 k (braid q i F) = braid q (i + 1) (cmAscWord q 1 k F) :=
  LinearMap.congr_fun (cmAscWord_mul_braidEnd q hi hik) F

/-! ### The word shift -/

/-- **The word shift**, `HJO.Sweep.cmAscWord_word_shift`:
`T_{[1,r+1]}T_{[1,r]} = T_{[2,r+1]}T_{[1,r+1]}`.

The long factor `T_{[1,r+1]}` shifts each letter of the short word up by one
(`HJO.Sweep.cmAscWord_mul_braidEnd`), and the shifted word is `T_{[2,r+1]}` because shifting an
index range by one is `HJO.Braid.map_range'_succ`; both steps at once are
`HJO.Braid.mul_ascendingWord`. The induction on `r`, with the `S_3` relation applied
once per step, is what that lemma performs in the general setting.

The upper bound `r ≤ m-2` keeps every letter inside `V_m` and carries no content on the
total space. -/
@[hjo "lem_cm_word_shift"]
theorem cmAscWord_word_shift (q : L) (r : ℕ) :
    cmAscWord q 1 (r + 1) * cmAscWord q 1 r = cmAscWord q 2 (r + 1) * cmAscWord q 1 (r + 1) := by
  rw [cmAscWord_eq_ascendingWord q (a := 1) (b := r) (by omega),
    cmAscWord_eq_ascendingWord q (a := 2) (b := r + 1) (by omega)]
  exact Braid.mul_ascendingWord (by omega) fun _ hj hj2 =>
    cmAscWord_mul_braidEnd q hj (by omega)

/-- **`T_{[1,r+1]}(T_{[1,r]}F) = T_{[2,r+1]}(T_{[1,r+1]}F)`**, the applied form of
`HJO.Sweep.cmAscWord_word_shift`. -/
theorem cmAscWord_word_shift_apply (q : L) (r : ℕ) (F : Total L) :
    cmAscWord q 1 (r + 1) (cmAscWord q 1 r F)
      = cmAscWord q 2 (r + 1) (cmAscWord q 1 (r + 1) F) :=
  LinearMap.congr_fun (cmAscWord_word_shift q r) F

/-! ### The substitution passes through a distant word -/

/-- **`τ_{k,m}` commutes with an ascending word all of whose letters are distant from `y_m`.** Every
letter `T_j` of `T_{[a,b]}` has `j ≤ b < m - 1`, so `HJO.Sweep.qshift_braid` applies to it, and an
element commuting with every letter commutes with the product
(`HJO.Braid.mul_prod_comm`). -/
theorem qshift_mul_cmAscWord (q : L) {a b m : ℕ} (hab : a ≤ b + 1) (hm : b + 2 ≤ m) :
    (qshift q m).toLinearMap * cmAscWord q a b
      = cmAscWord q a b * (qshift q m).toLinearMap := by
  rw [cmAscWord_eq_ascendingWord q hab, Braid.ascendingWord]
  refine Braid.mul_prod_comm fun y hy => ?_
  obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hy
  rw [List.mem_range'_1] at hj
  exact LinearMap.ext fun F => qshift_braid q (by omega) (by omega) (by omega) F

/-- **`τ_{k,m}(T_{[a,b]}F) = T_{[a,b]}(τ_{k,m}F)`** for a word whose letters are all distant from
`y_m`. -/
theorem qshift_cmAscWord (q : L) {a b m : ℕ} (hab : a ≤ b + 1) (hm : b + 2 ≤ m) (F : Total L) :
    qshift q m (cmAscWord q a b F) = cmAscWord q a b (qshift q m F) :=
  LinearMap.congr_fun (qshift_mul_cmAscWord q hab hm) F

/-- **A word is linear over what every one of its letters fixes**: `T_{[a,b]}(PF) = P·T_{[a,b]}F`
when `s_jP = P` for each letter index `j`, by `HJO.Sweep.braid_mul_of_swapAux_eq` letter by
letter. -/
theorem cmAscWord_mul_of_swapAux_eq (q : L) {a b : ℕ} (hab : a ≤ b + 1) {P : Total L}
    (hP : ∀ j, a ≤ j → j ≤ b → swapAux L j P = P) (F : Total L) :
    cmAscWord q a b (P * F) = P * cmAscWord q a b F := by
  have key : LinearMap.mulLeft L P * cmAscWord q a b
      = cmAscWord q a b * LinearMap.mulLeft L P := by
    rw [cmAscWord_eq_ascendingWord q hab, Braid.ascendingWord]
    refine Braid.mul_prod_comm fun y hy => ?_
    obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hy
    rw [List.mem_range'_1] at hj
    exact LinearMap.ext fun G =>
      (braid_mul_of_swapAux_eq q (hP j (by omega) (by omega)) G).symm
  exact (LinearMap.congr_fun key F).symm

/-! ### The raising operator -/

/-- **The raising operator `d_+` of the Dyck path algebra.** `HJO.Sweep.cmDPlus`: for
`k ≥ 0`, the `𝕜`-linear map from `V_k` to `V_{k+1}` with
`d_+F = T_1(T_2(⋯T_k(τ_{k+1,k+1}(F))⋯))`, the composite of `T_1, …, T_k` being the identity at
`k = 0` and `T_1` alone at `k = 1`.

That composite is the ascending word `T_{[1,k]}` of `HJO.Sweep.cmAscWord`, so the definition is
written as the word rather than as a second recursion — `HJO.Sweep.cmDPlus_zero` and
`HJO.Sweep.cmDPlus_one` are the two boundary conventions, which come out of
`HJO.Sweep.cmAscWord` with nothing to prove.

**This is not `HJO.Sweep.dplus`**, the raising operator of the sweep process (`HJO.Sweep.dplus`),
which carries a sign and a factor of `y_{k+1}`; `HJO.Sweep.dplus_eq_neg_cmDPlus` is the bridge. -/
@[hjo "def_cm_dplus"]
noncomputable def cmDPlus (q : L) (k : ℕ) : Module.End L (Total L) :=
  cmAscWord q 1 k * (qshift q (k + 1)).toLinearMap

/-- **The raising operator as a word**, `HJO.Sweep.cmDPlus_apply`:
`d_+F = T_{[1,k]}(τ_{k+1,k+1}(F))`, the word being read on `V_{k+1}`.

It holds by definition, `HJO.Sweep.cmDPlus` being written as that word; what the statement
asserts, and what carries content, is that the word form agrees with the iterated composite
`T_1(T_2(⋯T_k(-)⋯))` of `HJO.Sweep.cmDPlus` — which is `HJO.Sweep.cmAscWord_apply_succ_left`
unwound, and at the two boundary indices is `HJO.Sweep.cmDPlus_zero` and `HJO.Sweep.cmDPlus_one`. -/
@[hjo "lem_cm_dplus_word"]
theorem cmDPlus_apply (q : L) (k : ℕ) (F : Total L) :
    cmDPlus q k F = cmAscWord q 1 k (qshift q (k + 1) F) := rfl

/-- **The empty composite at `k = 0`**: `d_+F = τ_{1,1}(F)`, the convention that
`T_1 ⋯ T_k` is the identity when `k = 0`. -/
theorem cmDPlus_zero (q : L) (F : Total L) : cmDPlus q 0 F = qshift q 1 F := by
  rw [cmDPlus_apply, cmAscWord_self_pred]
  rfl

/-- **One letter at `k = 1`**: `d_+F = T_1(τ_{2,2}(F))`, the convention that
`T_1 ⋯ T_k` is `T_1` alone when `k = 1`. -/
theorem cmDPlus_one (q : L) (F : Total L) : cmDPlus q 1 F = braid q 1 (qshift q 2 F) := by
  rw [cmDPlus_apply, cmAscWord_self]
  rfl

/-- **The head letter of the composite**: `d_+F = T_1(T_{[2,k]}(τ_{k+1,k+1}(F)))` for `k ≥ 1`, one
step of the display `d_+F = T_1(T_2(⋯T_k(τ_{k+1,k+1}(F))⋯))`. Iterating it strips the
word one letter at a time down to `HJO.Sweep.cmDPlus_one`. -/
theorem cmDPlus_apply_succ_left (q : L) {k : ℕ} (hk : 1 ≤ k) (F : Total L) :
    cmDPlus q k F = braid q 1 (cmAscWord q 2 k (qshift q (k + 1) F)) := by
  rw [cmDPlus_apply, cmAscWord_apply_succ_left q hk]

/-- **`d_+` carries `V_k` into `V_{k+1}`**, the codomain `HJO.Sweep.cmDPlus` gives it: `τ_{k+1,k+1}`
lands in `V_{k+1}` because the letter it adds is `(q-1)y_{k+1}`, and the word `T_{[1,k]}` reads only
braid letters of index at most `k + 1`. -/
theorem cmDPlus_mem_piece (q : L) (k : ℕ) {F : Total L} (hF : F ∈ piece L k) :
    cmDPlus q k F ∈ piece L (k + 1) := by
  rw [cmDPlus_apply, cmAscWord]
  exact trainUpEnd_mem_piece q (by omega) le_rfl
    (qshift_mem_piece q (i := k + 1) (k := k) (m := k + 1) (by omega) (by omega) hF)

/-! ### The raising operator shifts the braid operators -/

/-- **`d_+` shifts the braid operators**, `HJO.Sweep.cmDPlus_braid`:
`d_+(T_iF) = T_{i+1}(d_+F)` for `1 ≤ i ≤ k-1`.

Two steps. The substitution `τ_{k+1,k+1}` commutes with `T_i` because its letter `y_{k+1}` is
distant from `y_i, y_{i+1}` — `HJO.Sweep.qshift_braid`, where `k + 1 ∉ {i, i+1}` is exactly
`i + 1 ≤ k`. Then the word absorbs the letter and shifts it,
`HJO.Sweep.cmAscWord_mul_braidEnd`. -/
@[hjo "lem_cm_rel_dplus_braid"]
theorem cmDPlus_braid (q : L) {k i : ℕ} (hi : 1 ≤ i) (hik : i + 1 ≤ k) (F : Total L) :
    cmDPlus q k (braid q i F) = braid q (i + 1) (cmDPlus q k F) := by
  rw [cmDPlus_apply, cmDPlus_apply, qshift_braid q (by omega) (by omega) (by omega),
    cmAscWord_braid q hi hik]

/-- `HJO.Sweep.cmDPlus_braid` in the endomorphism monoid, `d_+T_i = T_{i+1}d_+`. -/
theorem cmDPlus_mul_braidEnd (q : L) {k i : ℕ} (hi : 1 ≤ i) (hik : i + 1 ≤ k) :
    cmDPlus q k * braidEnd q i = braidEnd q (i + 1) * cmDPlus q k :=
  LinearMap.ext fun F => cmDPlus_braid q hi hik F

/-! ### `T_1` fixes `d_+d_+` -/

/-- **Two `𝕜`-algebra maps agreeing on the constants and on `y_1, …, y_k` agree on `V_k`.** The
membership counterpart is `HJO.Sweep.mem_piece_of_algHom`, and the argument is the same: `V_k` is
spanned over `Λ` by the `y`-monomials supported below `k`, and an algebra map is determined on a
monomial by its values on the factors. -/
theorem algHom_eq_of_mem_piece {k : ℕ} {f g : Total L →ₐ[L] Total L}
    (hC : ∀ c : Sym.Lambda L, f (MvPolynomial.C c) = g (MvPolynomial.C c))
    (hX : ∀ j < k, f (MvPolynomial.X j) = g (MvPolynomial.X j))
    {F : Total L} (hF : F ∈ piece L k) : f F = g F := by
  rw [piece, MvPolynomial.mem_supported] at hF
  rw [MvPolynomial.as_sum F, map_sum, map_sum]
  refine Finset.sum_congr rfl fun d hd => ?_
  have hdk : ∀ j ∈ d.support, j < k := fun j hj =>
    hF (MvPolynomial.mem_vars_iff_mem_support j |>.2 ⟨d, hd, hj⟩)
  rw [MvPolynomial.monomial_eq, map_mul, map_mul, hC, Finsupp.prod, map_prod, map_prod]
  refine congrArg _ (Finset.prod_congr rfl fun j hj => ?_)
  rw [map_pow, map_pow, hX j (hdk j hj)]

/-- **`s_{k+1}` fixes `τ_{k+2,k+2}(τ_{k+2,k+1}(F))` for `F ∈ V_k`**.

The composite substitution sends `p_r` to `p_r + (q^r-1)(y_{k+1}^r + y_{k+2}^r)` and fixes
`y_1, …, y_k`, and `s_{k+1}` fixes each of those: the two letters it interchanges occur only in the
symmetric combination `y_{k+1}^r + y_{k+2}^r`. `F ∈ V_k` is what makes that a complete list of
generators, and it is not decoration — at `F = y_{k+1}` the statement is false. -/
@[hjo "lem_cm_qshift_pair_symmetric"]
theorem swapAux_qshift_qshift (q : L) {k : ℕ} {F : Total L} (hF : F ∈ piece L k) :
    swapAux L (k + 1) (qshift q (k + 2) (qshift q (k + 1) F))
      = qshift q (k + 2) (qshift q (k + 1) F) := by
  set A : Total L →ₐ[L] Total L := (swapAux L (k + 1)).toAlgHom.restrictScalars L with hA
  set φ : Total L →ₐ[L] Total L := (qshift q (k + 2)).comp (qshift q (k + 1)) with hφ
  have hAapp : ∀ G : Total L, A G = swapAux L (k + 1) G := fun _ => rfl
  have hφapp : ∀ G : Total L, φ G = qshift q (k + 2) (qshift q (k + 1) G) := fun _ => rfl
  have hs1 : swapAux L (k + 1) (auxVar (k + 1) : Total L) = auxVar (k + 2) :=
    swapAux_auxVar_self (by omega)
  have hs2 : swapAux L (k + 1) (auxVar (k + 2) : Total L) = auxVar (k + 1) := by
    rw [← hs1, swapAux_swapAux]
  have hps : ∀ j : ℕ, Sym.powerSum L (j + 1) = (MvPolynomial.X j : Sym.Lambda L) := fun j => by
    rw [Sym.powerSum, Nat.add_sub_cancel]
  have hpow : ∀ r : ℕ, A (φ (MvPolynomial.C (Sym.powerSum L (r + 1))))
      = φ (MvPolynomial.C (Sym.powerSum L (r + 1))) := by
    intro r
    have h1 : φ (MvPolynomial.C (Sym.powerSum L (r + 1)))
        = MvPolynomial.C (Sym.powerSum L (r + 1))
          + scal (q ^ (r + 1) - 1) * auxVar (k + 2) ^ (r + 1)
          + scal (q ^ (r + 1) - 1) * auxVar (k + 1) ^ (r + 1) := by
      rw [hφapp, qshift_powerSum, map_add, qshift_powerSum, map_mul, qshift_scal, map_pow,
        qshift_auxVar_apply]
    rw [h1, hAapp]
    simp only [map_add, map_mul, map_pow, swapAux_C, swapAux_scal, hs1, hs2]
    ring
  have hAφ : ∀ c : Sym.Lambda L, A (φ (MvPolynomial.C c)) = φ (MvPolynomial.C c) := by
    intro c
    induction c using MvPolynomial.induction_on with
    | C x =>
      have hx : (MvPolynomial.C (MvPolynomial.C x : Sym.Lambda L) : Total L) = scal x := rfl
      simp only [hx, hAapp, hφapp, qshift_scal, swapAux_scal]
    | add p r hp hr => rw [map_add, map_add, map_add, hp, hr]
    | mul_X p j hp => rw [map_mul, map_mul, map_mul, hp, ← hps j, hpow j]
  suffices h : (A.comp φ) F = φ F by exact h
  refine algHom_eq_of_mem_piece (f := A.comp φ) (g := φ) (k := k) (fun c => ?_)
    (fun j hj => ?_) hF
  · rw [AlgHom.comp_apply]
    exact hAφ c
  · rw [AlgHom.comp_apply, hφapp, qshift_auxVar, qshift_auxVar, hAapp,
      swapAux_X_of_ne_of_ne (by omega) (by omega)]

/-- **`T_1` fixes `T_{[1,k+1]}T_{[1,k]}G` whenever `s_{k+1}` fixes `G`.** Two steps: the word shift
rewrites the double word as `T_{[2,k+1]}(T_{[1,k+1]}(G))`, and the last letter of `T_{[1,k+1]}` acts
trivially on `G`, since `HJO.Sweep.braid_of_swapAux_eq` turns the hypothesis into
`T_{k+1}(G) = G`; so the double word is `T_{[2,k+1]}(T_{[1,k]}(G))`, and applying `T_1` puts the
head letter back, `T_1T_{[2,k+1]} = T_{[1,k+1]}`.

This is the common core of `HJO.Sweep.braid_one_cmDPlus_cmDPlus` and
`HJO.Sweep.braid_one_dplus_dplus`: the two raising operators feed it two different `G`, and the
hypothesis on `G` is all either argument reads. -/
theorem braid_one_cmAscWord_cmAscWord (q : L) {k : ℕ} {G : Total L}
    (hG : swapAux L (k + 1) G = G) :
    braid q 1 (cmAscWord q 1 (k + 1) (cmAscWord q 1 k G))
      = cmAscWord q 1 (k + 1) (cmAscWord q 1 k G) := by
  have hfix : cmAscWord q 1 (k + 1) G = cmAscWord q 1 k G := by
    rw [cmAscWord_split q (c := k) (by omega) (by omega)]
    change cmAscWord q 1 k (cmAscWord q (k + 1) (k + 1) G) = _
    rw [cmAscWord_self]
    change cmAscWord q 1 k (braid q (k + 1) G) = _
    rw [braid_of_swapAux_eq q hG]
  have hshift : cmAscWord q 1 (k + 1) (cmAscWord q 1 k G)
      = cmAscWord q 2 (k + 1) (cmAscWord q 1 k G) := by
    rw [cmAscWord_word_shift_apply, hfix]
  rw [hshift, ← cmAscWord_apply_succ_left q (show (1 : ℕ) ≤ k + 1 by omega)]
  exact hshift

/-- **`T_1` fixes `d_+d_+`**, `HJO.Sweep.braid_one_cmDPlus_cmDPlus`: `T_1(d_+(d_+F)) = d_+(d_+F)`.

On `d_+(d_+F) = T_{[1,k+1]}(τ_{k+2,k+2}(T_{[1,k]}(τ_{k+1,k+1}(F))))` the outer substitution passes
through the inner word, every letter of `T_{[1,k]}` being distant from `y_{k+2}`
(`HJO.Sweep.qshift_cmAscWord`). That leaves `T_{[1,k+1]}(T_{[1,k]}(G))` with
`G = τ_{k+2,k+2}(τ_{k+2,k+1}(F))`, which `HJO.Sweep.swapAux_qshift_qshift` says is fixed by
`s_{k+1}` — so `HJO.Sweep.braid_one_cmAscWord_cmAscWord` applies. -/
@[hjo "lem_cm_rel_dplus_sq"]
theorem braid_one_cmDPlus_cmDPlus (q : L) {k : ℕ} {F : Total L} (hF : F ∈ piece L k) :
    braid q 1 (cmDPlus q (k + 1) (cmDPlus q k F)) = cmDPlus q (k + 1) (cmDPlus q k F) := by
  have key : cmDPlus q (k + 1) (cmDPlus q k F)
      = cmAscWord q 1 (k + 1) (cmAscWord q 1 k (qshift q (k + 2) (qshift q (k + 1) F))) := by
    rw [cmDPlus_apply, cmDPlus_apply, qshift_cmAscWord q (by omega) (by omega)]
  rw [key]
  exact braid_one_cmAscWord_cmAscWord q (swapAux_qshift_qshift q hF)

/-! ### The bridge to the sweep process's raising operator -/

/-- **The sweep process's raising operator in terms of the Dyck path algebra's**:
`d_+^{sweep} = -d_+ ∘ (y_{k+1} ·)`.

The two operators of `HJO.Sweep.dplus` and `HJO.Sweep.cmDPlus` differ by the sign and the factor of
`y_{k+1}` that the sweep process's carries, and the factor can be moved to the outside of
`τ_{k+1,k+1}` because that substitution is an algebra homomorphism fixing every auxiliary variable
(`HJO.Sweep.qshift_auxVar_apply`). Nothing identifies the two operators, and nothing should: this
equation is the only statement relating them. -/
theorem dplus_eq_neg_cmDPlus (q : L) (k : ℕ) :
    dplus q k = -(cmDPlus q k ∘ₗ LinearMap.mulLeft L (auxVar (k + 1) : Total L)) := by
  refine LinearMap.ext fun F => ?_
  have h : qshift q (k + 1) ((auxVar (k + 1) : Total L) * F)
      = auxVar (k + 1) * qshift q (k + 1) F := by
    rw [map_mul, qshift_auxVar_apply]
  rw [dplus_apply, LinearMap.neg_apply, LinearMap.coe_comp, Function.comp_apply,
    LinearMap.mulLeft_apply, cmDPlus_apply, h]
  rfl

/-- **`d_+^{sweep}` shifts the braid operators too**, `d_+^{sweep}(T_iF) = T_{i+1}(d_+^{sweep}F)`
for `1 ≤ i ≤ k-1`. The extra letter `y_{k+1}` is `s_i`-symmetric for those indices, so it passes
through `T_i` (`HJO.Sweep.braid_mul_of_swapAux_eq`) and the statement reduces to
`HJO.Sweep.cmDPlus_braid`. This is the second of the two relations
`HJO.Sweep.braid_dplusIter` cites, in the reading — `HJO.Sweep.dplus` — that it is applied
to. -/
theorem dplus_braid (q : L) {k i : ℕ} (hi : 1 ≤ i) (hik : i + 1 ≤ k) (F : Total L) :
    dplus q k (braid q i F) = braid q (i + 1) (dplus q k F) := by
  have hy : swapAux L i (auxVar (k + 1) : Total L) = auxVar (k + 1) :=
    swapAux_auxVar_of_ne (by omega) (by omega) (by omega)
  have hd : ∀ G : Total L, dplus q k G = -cmDPlus q k (auxVar (k + 1) * G) := by
    intro G
    rw [dplus_eq_neg_cmDPlus]
    rfl
  rw [hd, hd, ← braid_mul_of_swapAux_eq q hy, cmDPlus_braid q hi hik, map_neg]

/-- **`T_1` fixes `d_+^{sweep}d_+^{sweep}`**, the first of the two relations
`HJO.Sweep.braid_dplusIter` cites, for `HJO.Sweep.dplus` rather than `HJO.Sweep.cmDPlus`.

The two extra letters collect: `τ_{k+2,k+2}` fixes `y_{k+1}`, and `y_{k+2}` is `s_j`-symmetric for
every letter index `j ≤ k` of the inner word, so the double raising operator is
`T_{[1,k+1]}(T_{[1,k]}(y_{k+2}y_{k+1}G))` with the same `G` as in
`HJO.Sweep.braid_one_cmDPlus_cmDPlus` — and `s_{k+1}` fixes `y_{k+2}y_{k+1}G` because it
interchanges the two letters and fixes `G`. So `HJO.Sweep.braid_one_cmAscWord_cmAscWord` applies to
this reading too, with no second argument. -/
theorem braid_one_dplus_dplus (q : L) {k : ℕ} {F : Total L} (hF : F ∈ piece L k) :
    braid q 1 (dplus q (k + 1) (dplus q k F)) = dplus q (k + 1) (dplus q k F) := by
  set G : Total L := qshift q (k + 2) (qshift q (k + 1) F) with hG
  have hs1 : swapAux L (k + 1) (auxVar (k + 1) : Total L) = auxVar (k + 2) :=
    swapAux_auxVar_self (by omega)
  have hs2 : swapAux L (k + 1) (auxVar (k + 2) : Total L) = auxVar (k + 1) := by
    rw [← hs1, swapAux_swapAux]
  have hd0 : dplus q k F = -cmAscWord q 1 k (auxVar (k + 1) * qshift q (k + 1) F) := rfl
  have hd1 : dplus q (k + 1) (dplus q k F)
      = -cmAscWord q 1 (k + 1) (auxVar (k + 2) * qshift q (k + 2) (dplus q k F)) := rfl
  have e1 : qshift q (k + 2) (dplus q k F) = -cmAscWord q 1 k (auxVar (k + 1) * G) := by
    rw [hd0, map_neg, qshift_cmAscWord q (by omega) (by omega), map_mul, qshift_auxVar_apply, hG]
  have e2 : auxVar (k + 2) * cmAscWord q 1 k (auxVar (k + 1) * G)
      = cmAscWord q 1 k (auxVar (k + 2) * (auxVar (k + 1) * G)) :=
    (cmAscWord_mul_of_swapAux_eq q (by omega)
      (fun _ _ _ => swapAux_auxVar_of_ne (by omega) (by omega) (by omega)) _).symm
  have key : dplus q (k + 1) (dplus q k F)
      = cmAscWord q 1 (k + 1) (cmAscWord q 1 k (auxVar (k + 2) * (auxVar (k + 1) * G))) := by
    rw [hd1, e1, mul_neg, map_neg, neg_neg, e2]
  have hsym : swapAux L (k + 1) (auxVar (k + 2) * (auxVar (k + 1) * G))
      = auxVar (k + 2) * (auxVar (k + 1) * G) := by
    rw [map_mul, map_mul, hs1, hs2, swapAux_qshift_qshift q hF, ← hG]
    ring
  rw [key]
  exact braid_one_cmAscWord_cmAscWord q hsym

/-! ### `d_+^j(1)` and the braid operators that fix it -/

/-- **`d_+^m(1)`**, the element Mellit's Section 3 reads every operator identity at: the unit of
`V_0` raised `m` times by `HJO.Sweep.dplus`, the grading of each factor being the index of the piece
it starts from. It is written `d_+^{\,m}(1)` there and never named, the raising operators at
the different gradings being one symbol there. -/
noncomputable def dplusIter (q : L) : ℕ → Total L
  | 0 => 1
  | m + 1 => dplus q m (dplusIter q m)

/-- **`d_+^m(1) ∈ V_m`**, `d_+` raising the grading by one at each step from `1 ∈ V_0`. -/
theorem dplusIter_mem_piece (q : L) (m : ℕ) : dplusIter q m ∈ piece L m := by
  induction m with
  | zero => exact one_mem _
  | succ m ih => exact dplus_mem_piece q m ih

/-- **Every braid operator below the top fixes `d_+^j(1)`**: `T_i d_+^j(1) = d_+^j(1)` for
`1 ≤ i ≤ j-1`.

Induction on `i`. At `i = 1` the two outermost raising operators
are `HJO.Sweep.braid_one_dplus_dplus`. At `i + 1`, the relation `d_+T_i = T_{i+1}d_+`
(`HJO.Sweep.dplus_braid`) moves `T_{i+1}` inside one raising operator as `T_i`, where the inductive
hypothesis applies — its index condition `i + 1 ≤ j - 1` being what `i + 2 ≤ j` gives. -/
@[hjo "lem_mellit_braid_fixes_dplus"]
theorem braid_dplusIter (q : L) {i j : ℕ} (hi : 1 ≤ i) (hij : i + 1 ≤ j) :
    braid q i (dplusIter q j) = dplusIter q j := by
  have main : ∀ i, 1 ≤ i → ∀ j, i + 1 ≤ j → braid q i (dplusIter q j) = dplusIter q j := by
    intro i
    induction i with
    | zero => intro h; omega
    | succ i ih =>
      intro _ j hj
      rcases Nat.eq_zero_or_pos i with rfl | hi'
      · obtain ⟨n, rfl⟩ : ∃ n, j = n + 2 := ⟨j - 2, by omega⟩
        exact braid_one_dplus_dplus q (dplusIter_mem_piece q n)
      · obtain ⟨n, rfl⟩ : ∃ n, j = n + 1 := ⟨j - 1, by omega⟩
        change braid q (i + 1) (dplus q n (dplusIter q n)) = dplus q n (dplusIter q n)
        rw [← dplus_braid q hi' (by omega), ih hi' n (by omega)]
  exact main i hi j hij

/-! ### The unit shift of the alphabet -/

/-- **The unit shift `ϑ`**, `HJO.Sweep.unitShiftTotal`: the `𝕜[y]`-algebra endomorphism of
`V_k` sending `p_r` to `p_r + 1` for every `r ≥ 1`, the addition of the single letter `1` to the
alphabet.

On the total space the definition does not depend on `k`, exactly as for `HJO.Sweep.qshift`: the
operator `ϑ_k` is the restriction of this one endomorphism to `V_k`. It is the total-space form
of `HJO.Sym.unitShift`, which does the same on `Λ` itself. -/
@[hjo "def_vmod_tau"]
noncomputable def unitShiftTotal (L : Type*) [Field L] : Total L →ₐ[L] Total L :=
  MvPolynomial.aevalTower
    (MvPolynomial.aeval fun j : ℕ => (MvPolynomial.C (MvPolynomial.X j) + 1 : Total L))
    MvPolynomial.X

@[simp]
theorem unitShiftTotal_X (j : ℕ) :
    unitShiftTotal L (MvPolynomial.X j : Total L) = MvPolynomial.X j := by
  simp [unitShiftTotal]

/-- `ϑ` fixes every auxiliary variable, being a `𝕜[y]`-algebra map. -/
@[simp]
theorem unitShiftTotal_auxVar (j : ℕ) :
    unitShiftTotal L (auxVar j : Total L) = auxVar j :=
  unitShiftTotal_X (j - 1)

/-- `ϑ` fixes a scalar of `𝕜`, being an `𝕜`-algebra map. -/
@[simp]
theorem unitShiftTotal_scal (x : L) : unitShiftTotal L (scal x : Total L) = scal x := by
  rw [scal_eq_algebraMap, AlgHom.commutes]

/-- **`ϑ(p_r) = p_r + 1`**, the prescription read on the total space. -/
theorem unitShiftTotal_powerSum (r : ℕ) :
    unitShiftTotal L (MvPolynomial.C (Sym.powerSum L (r + 1)))
      = MvPolynomial.C (Sym.powerSum L (r + 1)) + 1 := by
  simp [unitShiftTotal, Sym.powerSum]

/-- **`ϑ` commutes with every transposition.** Both composites are `𝕜`-algebra endomorphisms of
`Total L = MvPolynomial ℕ Λ`, so `MvPolynomial.algHom_ext'` reduces the claim to the auxiliary
variables, which `ϑ` fixes, and to the power sums, which `s_i` fixes and `ϑ` moves by the constant
`1` — a constant `s_i` fixes at every index, so no distance hypothesis appears, unlike for
`HJO.Sweep.qshift_swapAux`. -/
theorem unitShiftTotal_swapAux (i : ℕ) (F : Total L) :
    unitShiftTotal L (swapAux L i F) = swapAux L i (unitShiftTotal L F) := by
  set A : Total L →ₐ[L] Total L := (swapAux L i).toAlgHom.restrictScalars L with hA
  have hAapp : ∀ G : Total L, A G = swapAux L i G := fun _ => rfl
  have key : (unitShiftTotal L).comp A = A.comp (unitShiftTotal L) := by
    refine MvPolynomial.algHom_ext' ?_ fun n => ?_
    · refine MvPolynomial.algHom_ext fun r => ?_
      have hC : (algebraMap (Sym.Lambda L) (Total L)) (MvPolynomial.X r)
          = MvPolynomial.C (Sym.powerSum L (r + 1)) := by
        simp [Sym.powerSum]
      simp only [AlgHom.comp_apply, IsScalarTower.coe_toAlgHom', hC, hAapp, swapAux_C,
        unitShiftTotal_powerSum, map_add, map_one]
    · simp only [AlgHom.comp_apply, hAapp, swapAux_X, unitShiftTotal_X]
  exact congrArg (fun f : Total L →ₐ[L] Total L => f F) key

/-- **`ϑ` commutes with every divided difference.** Off the uniqueness of `∂_i`: `ϑ` commutes with
`s_i` and fixes `y_i` and `y_{i+1}`, so applying it to the defining equation
`(y_{i+1}-y_i)∂_iF = F - s_iF` exhibits `ϑ(∂_iF)` as the divided difference of `ϑF`. -/
theorem unitShiftTotal_dividedDiff {i : ℕ} (hi : 1 ≤ i) (F : Total L) :
    unitShiftTotal L (dividedDiff i F) = dividedDiff i (unitShiftTotal L F) := by
  refine dividedDiff_unique hi ?_
  have h := congrArg (unitShiftTotal L) (dividedDiff_spec i F)
  rw [map_mul, map_sub, unitShiftTotal_X, unitShiftTotal_X, map_sub, unitShiftTotal_swapAux] at h
  exact h

/-- **`ϑ` commutes with the braid operators**, `HJO.Sweep.unitShiftTotal_braid`:
`ϑ(T_iF) = T_i(ϑF)`. `T_i = s_i + (q-1)y_i∂_i` is built from `s_i` and `∂_i`, both of which commute
with `ϑ`, and from multiplication by `(q-1)y_i`, which `ϑ` passes because it is a `𝕜[y]`-algebra
map.

The `1 ≤ i ≤ k-1` carries no content here: at the unread index `0` both operators are
the identity. -/
@[hjo "lem_vmod_tau_demazure_commute"]
theorem unitShiftTotal_braid (q : L) (i : ℕ) (F : Total L) :
    unitShiftTotal L (braid q i F) = braid q i (unitShiftTotal L F) := by
  rcases Nat.eq_zero_or_pos i with rfl | hi
  · rw [braid_zero_index, braid_zero_index]
  rw [braid_apply, braid_apply, map_add, map_mul, map_mul, unitShiftTotal_scal,
    unitShiftTotal_auxVar, unitShiftTotal_dividedDiff hi, unitShiftTotal_swapAux]

end Field

end HJO.Sweep

end
