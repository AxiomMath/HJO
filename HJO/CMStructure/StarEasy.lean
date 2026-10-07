/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.Shuffle.CMRaising
public import HJO.Shuffle.MellitShiftLoc
public meta import HJO.Attr

/-! # The starred raising operator against the braid and corner elements

Two results about `d^*_+` that are easy and are usually stated without proof.

* `HJO.Sweep.dplusStar_braidInv`: `d^*_+T_i^{-1} = T_{i+1}^{-1}d^*_+`,
  `T_1^{-1}d^{*2}_+ = d^{*2}_+`, and `d^*_+y_i = y_{i+1}d^*_+`.
* `HJO.Sweep.cmDPlusPow_map_one`: `d_+^m(1) = 1` and `d^*_+(d_+^m(1)) = d_+^{m+1}(1)`.

## What `HJO.Sweep.dplusStar_braidInv` costs, and what it teaches

The usual proof reads `d^*_+ = cy_{k+1}∘τ_{k+1,k+1}` and says the substitution is distant from
`T_i` while the cyclic shift raises every index by one. The second half is the one with content, and
it is a *conjugation*, proved here once for the transposition and once for the divided difference:

* `HJO.Sweep.cycleShift_swapAux`: `cy_{k+1}s_i = s_{i+1}cy_{k+1}` for `1 ≤ i < k`.
* `HJO.Sweep.cycleShift_dividedDiff`: `cy_{k+1}∂_i = ∂_{i+1}cy_{k+1}`, from `dividedDiff_unique`.
* `HJO.Sweep.cycleShift_braid`: the two together on `T_i = s_i + (q-1)y_i∂_i`.

So what this file establishes between the starred arrow and the braid endomorphisms is the
**uninverted** relation `d^*_+T_i = T_{i+1}d^*_+` (`HJO.Sweep.dplusStar_braid`), of which the
inverted clause is the consequence obtained by conjugating with `T_i^{-1}` and
`T_{i+1}^{-1}` (`HJO.Sweep.dplusStar_braidInv`, the clause that needs `q ≠ 0`). The uninverted form
is the stronger statement, holds for every `q`, and is what a proof wanting a relation between
the starred arrow and the braid letters should use.

The index range is `1 ≤ i < k` on `V_k` in the first two clauses, and it is not slack: `cy_{k+1}`
sends `y_k` to `y_{k+1}` but `y_{k+1}` to `uy_1`, so at `i = k` the conjugation `s_i ↦ s_{i+1}`
fails on the wrapped letter. The phrase "the admissible indices" means exactly this range, and for
the third clause it is the wider `1 ≤ i ≤ k`, the wrapped letter never being reached there.

The third clause is nearly free here, because `d^*_+` is *multiplicative*: it is the composite of
two algebra maps, and `HJO.Sweep.cycleShift_auxVar` already says that `cy_{k+1}` sends `y_i` to
`y_{i+1}`.

## The second clause is where `F ∈ V_k` is load-bearing

`T_1^{-1}d^{*2}_+ = d^{*2}_+` is `s_1` fixing `d^*_+(d^*_+F)`, by
`HJO.Sweep.braid_of_swapAux_eq`. Applying `d^*_+` twice carries `F`'s own letters `y_1, …, y_k` to
`y_3, …, y_{k+2}`, and adds the alphabet `(q-1)u(y_1 + y_2)` — the letter `(q-1)y_{k+1}` of the
first substitution being wrapped to `(q-1)uy_1` and then shifted to `(q-1)uy_2`, and the letter
`(q-1)y_{k+2}` of the second being wrapped to `(q-1)uy_1`. Both are `s_1`-symmetric. **At `F = y_k`
the statement is false**, `y_k` being carried to `y_2` alone, so the hypothesis `F ∈ V_k` is not
decoration; this is the same phenomenon `HJO.Sweep.swapAux_qshift_qshift` records for the unstarred
pair, and the proof is the same `HJO.Sweep.algHom_eq_of_mem_piece` argument.

## `HJO.Sweep.cmDPlusPow_map_one` is two unit computations

Every factor of `d_+` of `HJO.Sweep.cmDPlus` — the substitution `τ_{k+1,k+1}` and each braid letter
— fixes `1`: the first is an algebra map, and `T_i(1) = 1` because `s_i` fixes `1` and the divided
difference of a constant vanishes (`HJO.Sweep.braid_of_swapAux_eq`). So `d_+^m(1) = 1` at every
vertex and `d^*_+(1) = 1`, and both sides of the second identity are `1`.

The iterate `d_+^m` needs the vertex to advance, so it is a named recursion,
`HJO.Sweep.cmDPlusPow`: the `d_+^m` is `d_+` of index `m-1` after … after `d_+` of index
`0`, and writing it as a power of a single endomorphism would read the same index at every step.

## Main results

* `HJO.Sweep.dplusStar_braid`, `HJO.Sweep.dplusStar_braidInv`, `HJO.Sweep.dplusStar_auxVar_mul`,
  `HJO.Sweep.swapAux_one_dplusStar_dplusStar`, `HJO.Sweep.braidInv_one_dplusStar_dplusStar`:
  `HJO.Sweep.dplusStar_braidInv`.
* `HJO.Sweep.cmDPlusPow_map_one`, `HJO.Sweep.dplusStar_cmDPlusPow_one`:
  `HJO.Sweep.cmDPlusPow_map_one`.

## References

The lemmas `HJO.Sweep.dplusStar_braidInv` and `HJO.Sweep.cmDPlusPow_map_one`, on the starred
relations and the kernel of the extended action; definitions `HJO.Sweep.dplusStar`,
`HJO.Sweep.cycleShift`, `HJO.Sweep.cmDPlus`, `HJO.Dyck.Aq.yElt`. Transcribing A. Mellit, *Toric
braids and `(m,n)`-parking functions*, §3.6.
-/

@[expose] public section

namespace HJO.Sweep

section Field

variable {L : Type*} [Field L]

/-! ### The braid operators and the ascending words fix the unit -/

/-- **`T_i(1) = 1`**: the transposition fixes `1`, being an algebra map, so
`HJO.Sweep.braid_of_swapAux_eq` applies. -/
@[simp]
theorem braid_map_one (q : L) (i : ℕ) : braid q i (1 : Total L) = 1 :=
  braid_of_swapAux_eq q (map_one (swapAux L i))

/-- A word in the braid operators fixes `1`, letter by letter. -/
theorem prod_map_braidEnd_apply_one (q : L) (l : List ℕ) :
    ((l.map (braidEnd q)).prod) (1 : Total L) = 1 := by
  induction l with
  | nil => simp
  | cons i t ih =>
    rw [List.map_cons, List.prod_cons]
    change braidEnd q i (((t.map (braidEnd q)).prod) (1 : Total L)) = 1
    rw [ih]
    exact braid_map_one q i

/-- **`T_{[a,b]}(1) = 1`** for `a ≤ b + 1`, the ascending word being a product of braid letters. -/
theorem cmAscWord_map_one (q : L) {a b : ℕ} (hab : a ≤ b + 1) :
    cmAscWord q a b (1 : Total L) = 1 := by
  rw [cmAscWord_eq_ascendingWord q hab, Braid.ascendingWord]
  exact prod_map_braidEnd_apply_one q _

/-- **`d_+(1) = 1`** at every vertex, with `d_+` the raising operator of `HJO.Sweep.cmDPlus`: the
substitution fixes `1` and so does the word. -/
@[simp]
theorem cmDPlus_map_one (q : L) (k : ℕ) : cmDPlus q k (1 : Total L) = 1 := by
  rw [cmDPlus_apply, map_one, cmAscWord_map_one q (by omega)]

/-! ### The iterated raising operator, and the unit -/

/-- The word `d_+^m` of raising arrows out of the vertex `0`, with `d_+` the operator of
`HJO.Sweep.cmDPlus`. The vertex advances at every step, so this is a recursion and not a power of
one endomorphism: the outermost factor is `d_+` read on `V_{m-1}`. -/
noncomputable def cmDPlusPow (q : L) : ℕ → Module.End L (Total L)
  | 0 => 1
  | m + 1 => cmDPlus q m * cmDPlusPow q m

@[simp] theorem cmDPlusPow_zero (q : L) : cmDPlusPow q 0 = 1 := rfl

theorem cmDPlusPow_succ (q : L) (m : ℕ) :
    cmDPlusPow q (m + 1) = cmDPlus q m * cmDPlusPow q m := rfl

/-- **`d_+^m(1) = 1`**, the first clause of `HJO.Sweep.cmDPlusPow_map_one`: induction on
`m` from `HJO.Sweep.cmDPlus_map_one`. -/
@[hjo "lem_cm_dplus_star_unit", simp]
theorem cmDPlusPow_map_one (q : L) (m : ℕ) : cmDPlusPow q m (1 : Total L) = 1 := by
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [cmDPlusPow_succ]
    change cmDPlus q m (cmDPlusPow q m (1 : Total L)) = 1
    rw [ih, cmDPlus_map_one]

/-- **`d_+^m(1)` lies in `V_m`**, the codomain the first clause names: the value is `1`,
which lies in every graded piece. -/
theorem cmDPlusPow_map_one_mem_piece (q : L) (m : ℕ) :
    cmDPlusPow q m (1 : Total L) ∈ piece L m := by
  rw [cmDPlusPow_map_one]
  exact one_mem _

/-! ### The cyclic shift on the auxiliary variables -/

/-- `cy_{k+1}` raises the index of an auxiliary variable it reads. -/
theorem cycleShift_X_of_lt (u : L) {k j : ℕ} (hj : j < k) :
    cycleShift u k (MvPolynomial.X j : Total L) = MvPolynomial.X (j + 1) := by
  rw [cycleShift, MvPolynomial.aeval_X]
  simp [hj]

/-- `cy_{k+1}` fixes an auxiliary variable beyond the one that wraps. -/
theorem cycleShift_X_of_gt (u : L) {k j : ℕ} (hj : k < j) :
    cycleShift u k (MvPolynomial.X j : Total L) = MvPolynomial.X j := by
  rw [cycleShift, MvPolynomial.aeval_X]
  simp [show ¬ j < k by omega, show ¬ j = k by omega]

/-- `cy_{k+1}` fixes a scalar of `𝕜`, being a `Λ`-algebra map. -/
@[simp]
theorem cycleShift_scal (u : L) (k : ℕ) (x : L) :
    cycleShift u k (scal x : Total L) = scal x :=
  AlgHom.commutes (cycleShift u k) (MvPolynomial.C x)

/-- `cy_{k+1}` fixes a coefficient from `Λ`, being a `Λ`-algebra map. -/
@[simp]
theorem cycleShift_C (u : L) (k : ℕ) (a : Sym.Lambda L) :
    cycleShift u k (MvPolynomial.C a : Total L) = MvPolynomial.C a :=
  AlgHom.commutes (cycleShift u k) a

/-! ### The cyclic shift conjugates the braid operators -/

/-- **`cy_{k+1}s_i = s_{i+1}cy_{k+1}`** for `1 ≤ i < k`. Both composites are `Λ`-algebra maps, so
it is enough to compare them on the auxiliary variables: `s_i` moves `y_i, y_{i+1}` and `cy_{k+1}`
raises both indices by one, while every other letter is either raised past the pair
`y_{i+1}, y_{i+2}` or is the wrapped letter `uy_1`, which `s_{i+1}` fixes because `i ≥ 1`.

The hypothesis `i < k` is what keeps the pair inside the range where `cy_{k+1}` is a shift: at
`i = k` the letter `y_{k+1}` wraps and the conjugation fails. -/
theorem cycleShift_swapAux (u : L) {i k : ℕ} (hi : 1 ≤ i) (hik : i < k) (F : Total L) :
    cycleShift u k (swapAux L i F) = swapAux L (i + 1) (cycleShift u k F) := by
  have hsucc : i + 1 - 1 = i := by omega
  have hpred : i - 1 + 1 = i := by omega
  have key : (cycleShift u k).comp (swapAux L i).toAlgHom
      = ((swapAux L (i + 1)).toAlgHom).comp (cycleShift u k) := by
    refine MvPolynomial.algHom_ext fun j => ?_
    simp only [AlgHom.comp_apply, AlgEquiv.coe_toAlgHom]
    rcases eq_or_ne j (i - 1) with rfl | hj1
    · rw [swapAux_X, Equiv.swap_apply_left, cycleShift_X_of_lt u hik,
        cycleShift_X_of_lt u (show i - 1 < k by omega), hpred, swapAux_X, hsucc,
        Equiv.swap_apply_left]
    rcases eq_or_ne j i with heq | hj2
    · rw [heq, swapAux_X, Equiv.swap_apply_right, cycleShift_X_of_lt u hik,
        cycleShift_X_of_lt u (show i - 1 < k by omega), hpred, swapAux_X, hsucc,
        Equiv.swap_apply_right]
    rw [swapAux_X, Equiv.swap_apply_of_ne_of_ne hj1 hj2]
    by_cases hjk : j < k
    · rw [cycleShift_X_of_lt u hjk, swapAux_X_of_ne_of_ne (by omega) (by omega)]
    by_cases hje : j = k
    · have hXk : (MvPolynomial.X j : Total L) = MvPolynomial.X k := by rw [hje]
      have hwrap : cycleShift u k (MvPolynomial.X j : Total L) = scal u * auxVar 1 := by
        rw [hXk, show (MvPolynomial.X k : Total L) = auxVar (k + 1) from by
          rw [auxVar, Nat.add_sub_cancel], cycleShift_auxVar_last]
      rw [hwrap, map_mul, swapAux_scal, swapAux_auxVar_of_ne (by omega) (by omega) (by omega)]
    · rw [cycleShift_X_of_gt u (show k < j by omega),
        swapAux_X_of_ne_of_ne (by omega) (by omega)]
  exact congrArg (fun f : Total L →ₐ[Sym.Lambda L] Total L => f F) key

/-- **`cy_{k+1}∂_i = ∂_{i+1}cy_{k+1}`** for `1 ≤ i < k`: apply `cy_{k+1}` to the defining equation
`(y_{i+1} - y_i)∂_iF = F - s_iF`, which it carries to the defining equation of `∂_{i+1}` at
`cy_{k+1}F` by `HJO.Sweep.cycleShift_swapAux`, and use that `y_{i+2} - y_{i+1}` is a
nonzerodivisor. -/
theorem cycleShift_dividedDiff (u : L) {i k : ℕ} (hi : 1 ≤ i) (hik : i < k) (F : Total L) :
    cycleShift u k (dividedDiff i F) = dividedDiff (i + 1) (cycleShift u k F) := by
  refine dividedDiff_unique (by omega) ?_
  have h := congrArg (cycleShift u k) (dividedDiff_spec i F)
  have h1 : cycleShift u k (MvPolynomial.X i : Total L) = MvPolynomial.X (i + 1) :=
    cycleShift_X_of_lt u hik
  have h2 : cycleShift u k (MvPolynomial.X (i - 1) : Total L)
      = MvPolynomial.X (i + 1 - 1) := by
    rw [cycleShift_X_of_lt u (show i - 1 < k by omega)]
    congr 1
    omega
  rw [map_mul, map_sub, h1, h2, map_sub, cycleShift_swapAux u hi hik] at h
  exact h

/-- **`cy_{k+1}T_i = T_{i+1}cy_{k+1}`** for `1 ≤ i < k`: the transposition, the variable and the
divided difference all move up by one, and the scalar is fixed. -/
theorem cycleShift_braid (q u : L) {i k : ℕ} (hi : 1 ≤ i) (hik : i < k) (F : Total L) :
    cycleShift u k (braid q i F) = braid q (i + 1) (cycleShift u k F) := by
  have hy : cycleShift u k (auxVar i : Total L) = auxVar (i + 1) :=
    cycleShift_auxVar u hi hik.le
  rw [braid_apply, braid_apply, map_add, map_mul, map_mul, cycleShift_scal, hy,
    cycleShift_dividedDiff u hi hik, cycleShift_swapAux u hi hik]

/-! ### The three clauses of `HJO.Sweep.dplusStar_braidInv`, and the starred unit -/

/-- **`d^*_+(1) = 1`**, both factors of `d^*_+` being algebra maps.

This is also `HJO.Sweep.dplusStar_map_one`, "the starred raising operator fixes the
unit": for every `k ≥ 0` the unit of `V_k` is sent to the unit of `V_{k+1}`, and the proof is the
usual one — `τ_{k+1,k+1}` and `cy_{k+1}` are `𝕜`-algebra homomorphisms, so each sends `1`
to `1`. It is the first of the two halves of `HJO.Sweep.dminus_dplusStar_map_one`. -/
@[hjo "lem_vmod_dplus_star_unit", simp]
theorem dplusStar_map_one (q u : L) (k : ℕ) : dplusStar q u k (1 : Total L) = 1 := by
  rw [dplusStar_apply, map_one, map_one]

/-- **`d^*_+(d_+^m(1)) = d_+^{m+1}(1)`**, the second clause of
`HJO.Sweep.cmDPlusPow_map_one`: by the first clause both sides are `1`. -/
@[hjo "lem_cm_dplus_star_unit"]
theorem dplusStar_cmDPlusPow_one (q u : L) (m : ℕ) :
    dplusStar q u m (cmDPlusPow q m (1 : Total L)) = cmDPlusPow q (m + 1) (1 : Total L) := by
  rw [cmDPlusPow_map_one, dplusStar_map_one, cmDPlusPow_map_one]

/-- **`d^*_+T_i = T_{i+1}d^*_+`** for `1 ≤ i < k`, the uninverted form of the first clause of
`HJO.Sweep.dplusStar_braidInv` and the stronger statement: it holds for every `q`, whereas the
inverted clause needs `T_i` to be invertible.

Two steps. The substitution `τ_{k+1,k+1}` commutes with `T_i` because its letter `y_{k+1}` is
distant from `y_i, y_{i+1}` (`HJO.Sweep.qshift_braid`, whose side condition `k + 1 ∉ {i, i+1}` is
`i < k`), and the cyclic shift conjugates `T_i` into `T_{i+1}`
(`HJO.Sweep.cycleShift_braid`). -/
theorem dplusStar_braid (q u : L) {i k : ℕ} (hi : 1 ≤ i) (hik : i < k) (F : Total L) :
    dplusStar q u k (braid q i F) = braid q (i + 1) (dplusStar q u k F) := by
  rw [dplusStar_apply, dplusStar_apply, qshift_braid q (by omega) (by omega) (by omega),
    cycleShift_braid q u hi hik]

/-- **`d^*_+T_i^{-1} = T_{i+1}^{-1}d^*_+`** for `1 ≤ i < k`, the first clause of
`HJO.Sweep.dplusStar_braidInv`. It is `HJO.Sweep.dplusStar_braid` conjugated on both sides, which is
why `q ≠ 0` appears here and not there. -/
@[hjo "lem_cm_star_easy"]
theorem dplusStar_braidInv (q u : L) (hq : q ≠ 0) {i k : ℕ} (hi : 1 ≤ i) (hik : i < k)
    (F : Total L) :
    dplusStar q u k (braidInv q i F) = braidInv q (i + 1) (dplusStar q u k F) := by
  refine (braidInv_braid q hq (i + 1) _).symm.trans ?_
  rw [← dplusStar_braid q u hi hik, braid_braidInv q hq i F]

/-- **`d^*_+y_i = y_{i+1}d^*_+`** for `1 ≤ i ≤ k`, the third clause of
`HJO.Sweep.dplusStar_braidInv`: both factors of `d^*_+` are algebra maps, `τ_{k+1,k+1}` fixes `y_i`
and `cy_{k+1}` raises its index. -/
@[hjo "lem_cm_star_easy"]
theorem dplusStar_auxVar_mul (q u : L) {i k : ℕ} (hi : 1 ≤ i) (hik : i ≤ k) (F : Total L) :
    dplusStar q u k ((auxVar i : Total L) * F) = auxVar (i + 1) * dplusStar q u k F := by
  rw [dplusStar_apply, dplusStar_apply, map_mul, qshift_auxVar_apply, map_mul,
    cycleShift_auxVar u hi hik]

/-- `d^*_+` raises the index of an auxiliary variable it reads, as an algebra map. -/
theorem dplusStarAlg_X_of_lt (q u : L) {j k : ℕ} (hj : j < k) :
    dplusStarAlg q u k (MvPolynomial.X j : Total L) = MvPolynomial.X (j + 1) := by
  rw [dplusStarAlg_apply, qshift_auxVar, cycleShift_X_of_lt u hj]

/-- `d^*_+` fixes a scalar of `𝕜`. -/
@[simp]
theorem dplusStarAlg_scal (q u : L) (k : ℕ) (x : L) :
    dplusStarAlg q u k (scal x : Total L) = scal x := by
  rw [scal_eq_algebraMap, AlgHom.commutes]

/-- **`d^*_+` adds the letter `(q-1)y_{k+1}` to the alphabet and wraps it to `(q-1)uy_1`**: the
value of `d^*_+` on the power sum `p_{r+1}`. -/
theorem dplusStarAlg_C_powerSum (q u : L) (k r : ℕ) :
    dplusStarAlg q u k (MvPolynomial.C (Sym.powerSum L (r + 1)))
      = MvPolynomial.C (Sym.powerSum L (r + 1))
        + scal (q ^ (r + 1) - 1) * (scal u * auxVar 1 : Total L) ^ (r + 1) := by
  rw [dplusStarAlg_apply, qshift_powerSum, map_add, map_mul, map_pow, cycleShift_C,
    cycleShift_scal, cycleShift_auxVar_last]

/-- **`s_1` fixes `d^*_+(d^*_+F)` for `F ∈ V_k`.** Applying `d^*_+` twice carries the letters
`y_1, …, y_k` of `F` to `y_3, …, y_{k+2}` and adds the alphabet `(q-1)u(y_1 + y_2)`, which is
symmetric in the two letters `s_1` interchanges.

`F ∈ V_k` is load-bearing: at `F = y_k` the double image is `uy_2` alone and the claim is false. -/
theorem swapAux_one_dplusStar_dplusStar (q u : L) {k : ℕ} {F : Total L} (hF : F ∈ piece L k) :
    swapAux L 1 (dplusStar q u (k + 1) (dplusStar q u k F))
      = dplusStar q u (k + 1) (dplusStar q u k F) := by
  set A : Total L →ₐ[L] Total L := (swapAux L 1).toAlgHom.restrictScalars L with hA
  set φ : Total L →ₐ[L] Total L :=
    (dplusStarAlg q u (k + 1)).comp (dplusStarAlg q u k) with hφ
  have hAapp : ∀ G : Total L, A G = swapAux L 1 G := fun _ => rfl
  have hps : ∀ j : ℕ, Sym.powerSum L (j + 1) = (MvPolynomial.X j : Sym.Lambda L) := fun j => by
    rw [Sym.powerSum, Nat.add_sub_cancel]
  have hs12 : swapAux L 1 (auxVar 1 : Total L) = auxVar 2 := swapAux_auxVar_self (by omega)
  have hs21 : swapAux L 1 (auxVar 2 : Total L) = auxVar 1 := by
    rw [← hs12, swapAux_swapAux]
  -- the two wrapped letters are `(q-1)uy_1` and `(q-1)uy_2`, and `s_1` interchanges them
  have hpow : ∀ r : ℕ, A (φ (MvPolynomial.C (Sym.powerSum L (r + 1))))
      = φ (MvPolynomial.C (Sym.powerSum L (r + 1))) := by
    intro r
    have hval : φ (MvPolynomial.C (Sym.powerSum L (r + 1)))
        = MvPolynomial.C (Sym.powerSum L (r + 1))
          + scal (q ^ (r + 1) - 1) * (scal u * auxVar 1 : Total L) ^ (r + 1)
          + scal (q ^ (r + 1) - 1) * (scal u * auxVar 2 : Total L) ^ (r + 1) := by
      have h1 : (auxVar 1 : Total L) = MvPolynomial.X 0 := rfl
      have h2 : (auxVar 2 : Total L) = MvPolynomial.X 1 := rfl
      rw [hφ, AlgHom.comp_apply, dplusStarAlg_C_powerSum, map_add, dplusStarAlg_C_powerSum,
        map_mul, map_pow, map_mul, dplusStarAlg_scal, dplusStarAlg_scal, h1, h2,
        dplusStarAlg_X_of_lt q u (show 0 < k + 1 by omega)]
    rw [hval, hAapp]
    simp only [map_add, map_mul, map_pow, swapAux_C, swapAux_scal, hs12, hs21]
    ring
  have hφscal : ∀ x : L, φ (scal x : Total L) = scal x := fun x => by
    rw [scal_eq_algebraMap, AlgHom.commutes]
  have hAφ : ∀ c : Sym.Lambda L, A (φ (MvPolynomial.C c)) = φ (MvPolynomial.C c) := by
    intro c
    induction c using MvPolynomial.induction_on with
    | C x =>
      have hx : (MvPolynomial.C (MvPolynomial.C x : Sym.Lambda L) : Total L) = scal x := rfl
      rw [hx, hφscal, hAapp, swapAux_scal]
    | add p r hp hr => rw [map_add, map_add, map_add, hp, hr]
    | mul_X p j hp => rw [map_mul, map_mul, map_mul, hp, ← hps j, hpow j]
  suffices h : (A.comp φ) F = φ F by exact h
  refine algHom_eq_of_mem_piece (f := A.comp φ) (g := φ) (k := k) (fun c => ?_)
    (fun j hj => ?_) hF
  · rw [AlgHom.comp_apply]
    exact hAφ c
  · rw [AlgHom.comp_apply, hφ, AlgHom.comp_apply, dplusStarAlg_X_of_lt q u hj,
      dplusStarAlg_X_of_lt q u (show j + 1 < k + 1 by omega), hAapp,
      swapAux_X_of_ne_of_ne (by omega) (by omega)]

/-- **`T_1^{-1}d^{*2}_+ = d^{*2}_+` on `V_k`**, the second clause of `HJO.Sweep.dplusStar_braidInv`:
`HJO.Sweep.swapAux_one_dplusStar_dplusStar` makes the double image `s_1`-symmetric, so `T_1` fixes
it by `HJO.Sweep.braid_of_swapAux_eq`, and therefore so does `T_1^{-1}`. -/
@[hjo "lem_cm_star_easy"]
theorem braidInv_one_dplusStar_dplusStar (q u : L) (hq : q ≠ 0) {k : ℕ} {F : Total L}
    (hF : F ∈ piece L k) :
    braidInv q 1 (dplusStar q u (k + 1) (dplusStar q u k F))
      = dplusStar q u (k + 1) (dplusStar q u k F) := by
  have h := braid_of_swapAux_eq q (swapAux_one_dplusStar_dplusStar q u hF)
  calc braidInv q 1 (dplusStar q u (k + 1) (dplusStar q u k F))
      = braidInv q 1 (braid q 1 (dplusStar q u (k + 1) (dplusStar q u k F))) := by rw [h]
    _ = dplusStar q u (k + 1) (dplusStar q u k F) := braidInv_braid q hq 1 _

end Field

end HJO.Sweep
